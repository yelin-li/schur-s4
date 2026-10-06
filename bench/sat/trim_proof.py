#!/usr/bin/env python3
"""
Trims a RUP certificate to the clauses that the refutation actually needs.

Every derived clause is marked backwards from the empty clause through its hint
list; unmarked clauses are dropped and the hint indices are renumbered.  All unit
clauses are kept, because they are part of unit propagation in the checker (they
seed the trail) even when nothing refers to them explicitly.

Usage:
    python3 trim_proof.py --proof proof45.rup --problem s4 --sym --out proof45_trim.rup
"""
import argparse
import sys

import cdcl45
import expand_resolution as ex


def trim(base, proof):
    n = len(base)
    marked = set()
    # the empty clause is the root; every unit clause is a root as well, because
    # unit clauses seed unit propagation in the checker even when no hint list
    # mentions them explicitly
    stack = [len(proof) - 1]
    stack += [i for i, (c, _) in enumerate(proof) if len(c) == 1]
    while stack:
        i = stack.pop()
        if i in marked:
            continue
        marked.add(i)
        for h in proof[i][1]:
            if h >= n:
                stack.append(h - n)
    # renumber: base keeps its indices, kept derived clauses shift down
    new_index = {}
    for j in range(n):
        new_index[j] = j
    kept = []
    for i in range(len(proof)):
        if i in marked:
            new_index[n + i] = n + len(kept)
            kept.append(i)
    out = []
    for i in kept:
        clause, hints = proof[i]
        out.append((clause, [new_index[h] for h in hints]))
    return out


def verify(base, proof):
    """independent re-check of the trimmed proof (RUP semantics)"""
    db = [list(c) for c in base]
    units = [i for i, c in enumerate(db) if len(c) == 1]
    for k, (clause, hints) in enumerate(proof):
        assign = dict()
        for i in units:
            l = db[i][0]
            assign[abs(l)] = l > 0
        for l in clause:
            v, val = abs(l), l < 0
            if v in assign and assign[v] != val:
                assign = None
                break
            assign[v] = val
        if assign is None:
            db.append(list(clause))
            if len(clause) == 1:
                units.append(len(db) - 1)
            continue
        closed = False
        for h in hints:
            if not (0 <= h < len(db)):
                return f"step {k}: hint {h} out of range"
            cl = db[h]
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
                return f"step {k}: hint {h} is not unit"
            if un == 0:
                closed = True
                break
            assign[abs(unit)] = unit > 0
        if not closed:
            return f"step {k}: hints do not reach a conflict"
        db.append(list(clause))
        if len(clause) == 1:
            units.append(len(db) - 1)
    if db[-1] != []:
        return "the trimmed proof does not end with the empty clause"
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proof", required=True)
    ap.add_argument("--problem", choices=["s3", "s4"], default="s4")
    ap.add_argument("--sym", action="store_true")
    ap.add_argument("--out")
    args = ap.parse_args()

    base = cdcl45.build_cnf_s3()[0] if args.problem == "s3" else cdcl45.build_cnf(args.sym)
    proof = ex.read_proof(args.proof)
    print(f"original: {len(proof)} steps", file=sys.stderr)
    trimmed = trim(base, proof)
    print(f"trimmed:  {len(trimmed)} steps "
          f"({100.0 * len(trimmed) / max(1, len(proof)):.1f}%)", file=sys.stderr)
    err = verify(base, trimmed)
    if err:
        sys.exit("trimmed proof FAILED verification: " + err)
    print("trimmed proof verified", file=sys.stderr)
    if args.out:
        with open(args.out, "w") as f:
            for clause, hints in trimmed:
                f.write(" ".join(map(str, clause)) + " 0 " + str(len(hints)) + " "
                        + " ".join(map(str, hints)) + "\n")
        print(f"wrote {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
