#!/usr/bin/env python3
"""
Self-written CDCL SAT solver with RUP proof logging (no external solver).

Instance: "is there a 4-colouring of {1, ..., 45} with no monochromatic
a + b = c?"  encoded as CNF.  Optionally the two symmetry-breaking units
x(1,0), x(2,1) are added (justified in Lean by `exists_good_first_two`).

Every learned clause is emitted together with a *hint list*: clause indices such
that unit propagation starting from the negation of the learned clause makes the
hinted clauses unit one after another and finally falsifies the last one.  That
is a RUP certificate; a chain of RUP steps ending in the empty clause is a
refutation.

Implementation notes
--------------------
* MiniSat-style two-watched-literal propagation.
* 1UIP conflict analysis; the hint list is read off the analysis chain
  (reason clauses in trail order, then the conflict clause).
* VSIDS activity, phase saving, Luby restarts.
* No clause deletion, so the certificate is a monotone sequence of additions.

Usage:
    python3 cdcl45.py --out proof45.rup [--sym] [--stats]
"""

import argparse
import sys
import time

N = 45
COLORS = 4


def var(i, c):
    return (i - 1) * COLORS + c + 1


def dedupe(clauses):
    """Remove repeated literals inside each clause (a duplicate-free clause is
    logically equivalent, and both the solver's propagation and the Lean
    checker are simpler and complete without duplicates)."""
    out = []
    for cl in clauses:
        seen = set()
        new = []
        for l in cl:
            if l not in seen:
                seen.add(l)
                new.append(l)
        out.append(new)
    return out


def build_cnf_s3():
    """3-colouring of {1, ..., 14} with no monochromatic a + b = c (S(3) = 13)."""
    n, k = 14, 3
    def v(i, c):
        return (i - 1) * k + c + 1
    clauses = []
    for i in range(1, n + 1):
        clauses.append([v(i, c) for c in range(k)])
        for c in range(k):
            for d in range(c + 1, k):
                clauses.append([-v(i, c), -v(i, d)])
    for a in range(1, n):
        for b in range(a, n - a + 1):
            s = a + b
            for c in range(k):
                clauses.append([-v(a, c), -v(b, c), -v(s, c)])
    return dedupe(clauses), n * k


def build_cnf(symmetry_break):
    clauses = []
    for i in range(1, N + 1):
        clauses.append([var(i, c) for c in range(COLORS)])
    for i in range(1, N + 1):
        for c in range(COLORS):
            for d in range(c + 1, COLORS):
                clauses.append([-var(i, c), -var(i, d)])
    for a in range(1, N):
        for b in range(a, N - a + 1):
            s = a + b
            for c in range(COLORS):
                clauses.append([-var(a, c), -var(b, c), -var(s, c)])
    if symmetry_break:
        # x(1,0) and x(2,1): sound by `Schur.exists_good_first_two`
        clauses.append([var(1, 0)])
        clauses.append([var(2, 1)])
    return dedupe(clauses)


class Solver:
    def __init__(self, clauses, nvars=None, seed=1, order="positional", colors=4):
        self.clauses = [list(c) for c in clauses]
        self.nvars = nvars if nvars is not None else N * COLORS
        self.order = order
        self.colors = colors
        self.npos = (self.nvars + colors - 1) // colors
        self.watches = [[] for _ in range(2 * self.nvars + 2)]

        self.value = [0] * (self.nvars + 1)      # 0 unknown, 1 true, -1 false
        self.level = [0] * (self.nvars + 1)
        self.reason = [-1] * (self.nvars + 1)
        self.trail = []
        self.trail_lim = []
        self.qhead = 0
        self.activity = [0.0] * (self.nvars + 1)
        self.var_inc = 1.0
        self.phase = [1] * (self.nvars + 1)
        self.proof = []
        self.deleted = set()
        self.base_len = len(self.clauses)
        self.debug = False
        self.stats = dict(conflicts=0, decisions=0, propagations=0, restarts=0,
                          learned=0, learned_lits=0, deleted=0,
                          fast_hints=0, fallback_hints=0)

        for ci, cl in enumerate(self.clauses):
            if len(cl) == 1:
                self.enqueue(cl[0], ci)
            else:
                self.watches[self.widx(cl[0])].append(ci)
                self.watches[self.widx(cl[1])].append(ci)
        # occurrence lists, used only to generate RUP hints
        self.occ = {}
        for idx, cl in enumerate(self.clauses):
            for l in cl:
                self.occ.setdefault(l, []).append(idx)
        # unit clauses, in the order they were added: they seed the trail in the
        # checker semantics.  Deletions are ignored here on purpose: the
        # certificate checker sees the database without deletions, so hints may
        # refer to clauses that the solver has already deleted.
        self.units = [idx for idx, cl in enumerate(self.clauses) if len(cl) == 1]
        # their assignment, precomputed: the checker seeds the trail with it
        self.unit_assign = {}
        for ci in self.units:
            l = self.clauses[ci][0]
            self.unit_assign[abs(l)] = l > 0

    # -- helpers ------------------------------------------------------------
    def widx(self, lit):
        return 2 * abs(lit) + (0 if lit > 0 else 1)

    def lit_value(self, lit):
        v = self.value[abs(lit)]
        if v == 0:
            return 0
        return v if lit > 0 else -v

    def enqueue(self, lit, reason):
        v = abs(lit)
        self.value[v] = 1 if lit > 0 else -1
        self.level[v] = len(self.trail_lim)
        self.reason[v] = reason
        self.trail.append(lit)

    # -- propagation --------------------------------------------------------
    def propagate(self):
        while self.qhead < len(self.trail):
            p = self.trail[self.qhead]
            self.qhead += 1
            self.stats["propagations"] += 1
            ws = self.watches[self.widx(-p)]
            i = 0
            while i < len(ws):
                ci = ws[i]
                if ci in self.deleted:
                    ws[i] = ws[-1]
                    ws.pop()
                    continue
                cl = self.clauses[ci]
                if cl[0] == -p:
                    cl[0], cl[1] = cl[1], cl[0]
                # now cl[1] == -p is the false watched literal
                if cl[1] != -p:                     # stale watch (should not happen)
                    i += 1
                    continue
                first = cl[0]
                if self.lit_value(first) == 1:
                    i += 1
                    continue
                # try to find a replacement watch
                replaced = False
                for k in range(2, len(cl)):
                    if self.lit_value(cl[k]) != -1:
                        cl[1], cl[k] = cl[k], cl[1]
                        ws[i] = ws[-1]
                        ws.pop()
                        self.watches[self.widx(cl[1])].append(ci)
                        replaced = True
                        break
                if replaced:
                    continue
                if self.lit_value(first) == -1:
                    self.qhead = len(self.trail)
                    return ci
                self.enqueue(first, ci)
                i += 1
        return None

    # -- conflict analysis --------------------------------------------------
    def analyze(self, conflict):
        """1UIP conflict analysis.

        Returns the learned clause (asserting literal first), the backtrack
        level, and nothing else: the RUP hints are generated separately by
        `rup_hints`, so the certificate does not depend on this analysis.
        """
        cur_level = len(self.trail_lim)
        learned = [0]
        seen = set()
        counter = 0
        cur = conflict
        p = 0
        idx = len(self.trail) - 1
        chain = []                    # reason clauses resolved on, trail order
        while True:
            cl = self.clauses[cur]
            for q in cl:
                if q == p:
                    continue
                v = abs(q)
                if v not in seen and self.level[v] > 0:
                    seen.add(v)
                    self.bump(v)
                    if self.level[v] == cur_level:
                        counter += 1
                    else:
                        learned.append(q)
            # next pivot: the last trail literal of the current level in `seen`
            while idx >= 0 and not (abs(self.trail[idx]) in seen
                                    and self.level[abs(self.trail[idx])] == cur_level):
                idx -= 1
            if idx < 0:
                raise RuntimeError("conflict analysis ran off the trail")
            p = self.trail[idx]
            idx -= 1
            seen.discard(abs(p))
            counter -= 1
            if counter == 0:
                break
            cur = self.reason[abs(p)]
            if cur < 0:
                raise RuntimeError("pivot literal has no reason")
            chain.append(cur)
        learned[0] = -p
        # drop duplicates (keep the asserting literal first)
        out = [learned[0]]
        for l in learned[1:]:
            if abs(l) != abs(learned[0]) and not any(abs(l) == abs(x) for x in out):
                out.append(l)
        if len(out) == 1:
            back = 0
        else:
            back = max(self.level[abs(l)] for l in out[1:])
        return out, back, chain

    def bump(self, v):
        self.activity[v] += self.var_inc
        if self.activity[v] > 1e100:
            for i in range(1, self.nvars + 1):
                self.activity[i] *= 1e-100
            self.var_inc *= 1e-100

    def backtrack(self, level):
        while len(self.trail_lim) > level:
            lim = self.trail_lim.pop()
            for lit in reversed(self.trail[lim:]):
                v = abs(lit)
                self.phase[v] = self.value[v]
                self.value[v] = 0
                self.reason[v] = -1
            del self.trail[lim:]
        self.qhead = len(self.trail)

    def pick_branch(self):
        """Decision heuristic.

        `positional`: decide the colours of the integers in order, trying
        colours 0,1,2,… in turn.  This mirrors the branching order of the
        verified search elsewhere in this repository, which is far better suited
        to Schur instances than activity-based branching: a blocked colour is
        refuted immediately by unit propagation, and the learned clause then
        rules out that prefix for good.

        `vsids`: standard activity-based branching.
        """
        if self.order == "positional":
            for i in range(1, self.npos + 1):
                for c in range(self.colors):
                    v = (i - 1) * self.colors + c + 1
                    if v <= self.nvars and self.value[v] == 0:
                        return v
            for v in range(1, self.nvars + 1):      # safety net
                if self.value[v] == 0:
                    return v
            return None
        best, best_act = 0, -1.0
        for v in range(1, self.nvars + 1):
            if self.value[v] == 0 and self.activity[v] > best_act:
                best, best_act = v, self.activity[v]
        return best or None

    def reduce_db(self):
        """Delete every other long learned clause (keeps indices valid: deleted
        clauses are kept in the database, so the certificate stays monotone)."""
        if len(self.clauses) < 30000:
            return
        kept = 0
        for ci in range(self.base_len, len(self.clauses)):
            if ci in self.deleted or len(self.clauses[ci]) <= 4:
                continue
            kept += 1
            if kept % 2 == 0:
                self.deleted.add(ci)
                self.stats["deleted"] += 1

    # -- main loop ----------------------------------------------------------
    def solve(self, budget):
        self._t0 = time.time()
        luby = [1, 1, 2, 1, 1, 2, 4]
        restart_at = 100
        conflicts_since_restart = 0
        while True:
            conflict = self.propagate()
            if conflict is not None:
                self.stats["conflicts"] += 1
                conflicts_since_restart += 1
                if len(self.trail_lim) == 0:
                    self.conflict = -1
                    final = self.rup_hints([])
                    if final is None:
                        # fall back: hints from the trail for the empty clause
                        final = self.trail_hints([])
                    if final is None:
                        raise RuntimeError("could not derive the empty clause")
                    self.proof.append(([], final))
                    return False
                learned, back, chain = self.analyze(conflict)
                self.conflict = conflict
                hints = self.chain_hints(chain, learned, conflict)
                if hints is not None and self.replay(learned, hints):
                    self.stats["fast_hints"] += 1
                else:
                    self.stats["fallback_hints"] += 1
                    hints = self.rup_hints(learned)
                    if hints is None:
                        raise RuntimeError("RUP hint generation failed for a learned clause")
                if self.debug:
                    if not self.replay(learned, hints):
                        raise SystemExit(f"BAD STEP at conflict {self.stats['conflicts']}")
                if len(learned) > 1:
                    # the two watched literals must be the first two
                    pass
                ci = len(self.clauses)
                self.clauses.append(learned)
                if len(learned) == 1:
                    self.units.append(ci)
                    self.unit_assign[abs(learned[0])] = learned[0] > 0
                for l in learned:
                    self.occ.setdefault(l, []).append(ci)
                if len(learned) == 1:
                    self.backtrack(0)
                    self.enqueue(learned[0], ci)
                else:
                    self.watches[self.widx(learned[0])].append(ci)
                    self.watches[self.widx(learned[1])].append(ci)
                    self.backtrack(back)
                    self.enqueue(learned[0], ci)
                self.proof.append((learned, hints))
                self.stats["learned"] += 1
                self.stats["learned_lits"] += len(learned)
                self.var_inc /= 0.95
                if conflicts_since_restart >= restart_at:
                    self.backtrack(0)
                    conflicts_since_restart = 0
                    self.stats["restarts"] += 1
                    restart_at = 100 * luby[self.stats["restarts"] % len(luby)]
                    self.reduce_db()
                if self.stats["conflicts"] > budget:
                    raise RuntimeError("conflict budget exhausted")
                if self.stats["conflicts"] % 10000 == 0 and self.stats["conflicts"] > 0:
                    print(f"  [cdcl] conflicts={self.stats['conflicts']} "
                          f"decisions={self.stats['decisions']} "
                          f"props={self.stats['propagations']} "
                          f"db={len(self.clauses)} "
                          f"t={time.time() - self._t0:.0f}s", file=sys.stderr)
                    sys.stderr.flush()
            else:
                v = self.pick_branch()
                if v is None:
                    return True
                self.stats["decisions"] += 1
                self.trail_lim.append(len(self.trail))
                self.enqueue(v if self.phase[v] > 0 else -v, -1)

    def rup_hints(self, clause):
        """Hints for a RUP step: unit propagation over the current database
        starting from the assignment that makes every literal of `clause` false.
        The returned clauses, *in the order used*, are a valid hint list."""
        assign = {}
        for l in clause:
            v, val = abs(l), l < 0
            if v in assign and assign[v] != val:
                return None                       # tautological clause
            assign[v] = val
        hints = []
        # unit clauses of the database are available to unit propagation: seed them
        for ci in self.units:
            cl = self.clauses[ci]
            l = cl[0]
            v, val = abs(l), l > 0
            if v in assign:
                if assign[v] != val:
                    return None            # contradicts the clause's negation
            else:
                assign[v] = val
        queue = [v if val else -v for v, val in assign.items()]
        head = 0
        while head < len(queue):
            lit = queue[head]
            head += 1
            for ci in self.occ.get(-lit, ()):
                if ci in self.deleted:
                    continue
                cl = self.clauses[ci]
                unassigned, unit, sat = 0, 0, False
                for l in cl:
                    a = assign.get(abs(l))
                    if a is None:
                        unassigned += 1
                        unit = l
                        if unassigned > 1:
                            break
                    elif a == (l > 0):
                        sat = True
                        break
                if sat or unassigned > 1:
                    continue
                if unassigned == 0:
                    hints.append(ci)
                    return hints
                assign[abs(unit)] = unit > 0
                queue.append(unit)
                hints.append(ci)
        return None

    def fast_assign(self, clause):
        """Assignments reached by the occurrence-list propagation (debug)."""
        assign = {}
        for l in clause:
            v, val = abs(l), l < 0
            if v in assign and assign[v] != val:
                return assign
            assign[v] = val
        queue = [v if val else -v for v, val in assign.items()]
        head = 0
        while head < len(queue):
            lit = queue[head]
            head += 1
            for ci in self.occ.get(-lit, ()):
                if ci in self.deleted:
                    continue
                cl = self.clauses[ci]
                unassigned, unit, sat = 0, 0, False
                for l in cl:
                    a = assign.get(abs(l))
                    if a is None:
                        unassigned += 1
                        unit = l
                        if unassigned > 1:
                            break
                    elif a == (l > 0):
                        sat = True
                        break
                if sat or unassigned > 1:
                    continue
                if unassigned == 0:
                    return assign
                assign[abs(unit)] = unit > 0
                queue.append(unit)
        return assign

    def slow_assign(self, clause):
        """Assignments reached by full scans until fixpoint (debug)."""
        assign = {}
        for l in clause:
            v, val = abs(l), l < 0
            if v in assign and assign[v] != val:
                return assign
            assign[v] = val
        while True:
            progress = False
            for ci, cl in enumerate(self.clauses):
                if ci in self.deleted:
                    continue
                unassigned, unit, sat = 0, 0, False
                for l in cl:
                    a = assign.get(abs(l))
                    if a is None:
                        unassigned += 1
                        unit = l
                        if unassigned > 1:
                            break
                    elif a == (l > 0):
                        sat = True
                        break
                if sat or unassigned > 1:
                    continue
                if unassigned == 0:
                    return assign
                assign[abs(unit)] = unit > 0
                progress = True
            if not progress:
                return assign

    def slow_rup(self, clause):
        """Reference RUP check: full scans until fixpoint (debug aid)."""
        assign = {}
        for l in clause:
            v, val = abs(l), l < 0
            if v in assign and assign[v] != val:
                return None
            assign[v] = val
        while True:
            progress = False
            for ci, cl in enumerate(self.clauses):
                if ci in self.deleted:
                    continue
                unassigned, unit, sat = 0, 0, False
                for l in cl:
                    a = assign.get(abs(l))
                    if a is None:
                        unassigned += 1
                        unit = l
                        if unassigned > 1:
                            break
                    elif a == (l > 0):
                        sat = True
                        break
                if sat or unassigned > 1:
                    continue
                if unassigned == 0:
                    return []
                assign[abs(unit)] = unit > 0
                progress = True
            if not progress:
                return None

    def replay(self, clause, hints):
        """Local copy of the checker semantics (unit clauses seed the trail, then
        the hints must be unit in order, the last one falsified).  Used to accept
        the cheap trail-based hints and to fall back to a full propagation."""
        assign = dict(self.unit_assign)         # unit clauses seed the trail
        for l in clause:
            v, val = abs(l), l < 0
            if v in assign:
                if assign[v] != val:
                    return True                 # already a conflict
            else:
                assign[v] = val
        for h in hints:
            cl = self.clauses[h]
            un, unit, sat = 0, 0, False
            for l in cl:
                a = assign.get(abs(l))
                if a is None:
                    un += 1
                    unit = l
                    if un > 1:
                        break
                elif a == (l > 0):
                    sat = True
                    break
            if sat or un > 1:
                return False
            if un == 0:
                return True
            assign[abs(unit)] = unit > 0
        return False

    def chain_hints(self, chain, clause, conflict):
        """Hints from the conflict-analysis resolution chain.

        The chain holds the reason clauses resolved on, latest trail literal
        first; forward propagation order is the reverse.  Reasons of level-0
        implications that are not unit clauses are prepended (they are not part
        of the chain, because the analysis skips level 0), and the conflicting
        clause closes the list.  `replay` decides whether the result is usable.
        """
        if chain is None:
            return None
        covered = {}
        for l in clause:
            v, val = abs(l), l < 0
            if v in covered and covered[v] != val:
                return None
            covered[v] = val
        n0 = self.trail_lim[0] if self.trail_lim else len(self.trail)
        level0 = []
        for lit in self.trail[:n0]:
            v = abs(lit)
            if v in covered:
                continue
            r = self.reason[v]
            if r >= 0 and len(self.clauses[r]) != 1 and r not in level0:
                level0.append(r)
        return level0 + list(reversed(chain)) + [conflict]

    def trail_hints(self, clause):
        """Hints read off the solver's own trail: the reason of every trail
        literal not already fixed by the negation of `clause`, in trail order,
        followed by the conflicting clause.  Cheap (O(trail)); the result is
        accepted only if `replay` confirms it, otherwise `rup_hints` is used."""
        covered = {}
        for l in clause:
            v, val = abs(l), l < 0
            if v in covered and covered[v] != val:
                return None
            covered[v] = val
        hints = []
        for lit in self.trail:
            v = abs(lit)
            val = lit > 0
            if v in covered:
                if covered[v] != val:
                    return None
                continue
            r = self.reason[v]
            if r < 0:
                return None
            if len(self.clauses[r]) == 1:
                continue                        # already seeded by the checker
            hints.append(r)
        hints.append(self.conflict)
        return hints


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="proof45.rup")
    ap.add_argument("--problem", choices=["s3", "s4"], default="s4")
    ap.add_argument("--sym", action="store_true", help="add symmetry-breaking units")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--budget", type=int, default=2_000_000)
    ap.add_argument("--stats", action="store_true")
    ap.add_argument("--order", choices=["positional", "vsids"], default="positional",
                    help="decision heuristic (default: colours of 1,2,3,... in order)")
    args = ap.parse_args()

    if args.problem == "s3":
        base, nvars = build_cnf_s3()
        colors = 3
    else:
        base, nvars = build_cnf(args.sym), N * COLORS
        colors = COLORS
    print(f"CNF: {nvars} vars, {len(base)} clauses, problem={args.problem}, "
          f"symmetry units: {args.sym if args.problem == 's4' else False}",
          file=sys.stderr)
    t0 = time.time()
    s = Solver(base, nvars=nvars, seed=args.seed, order=args.order, colors=colors)
    sat = s.solve(args.budget)
    dt = time.time() - t0
    print(f"result: {'SAT' if sat else 'UNSAT'} in {dt:.1f}s", file=sys.stderr)
    print("stats:", s.stats, file=sys.stderr)
    if sat:
        sys.exit("unexpectedly satisfiable")
    hints_total = sum(len(h) for _, h in s.proof)
    print(f"proof: {len(s.proof)} steps, {hints_total} hints", file=sys.stderr)
    with open(args.out, "w") as f:
        for clause, hints in s.proof:
            f.write(" ".join(map(str, clause)) + " 0 "
                    + str(len(hints)) + " " + " ".join(map(str, hints)) + "\n")
    print(f"wrote {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
