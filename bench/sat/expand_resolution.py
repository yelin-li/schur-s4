#!/usr/bin/env python3
"""
Expands a RUP certificate (cdcl45.py) into an explicit resolution derivation
checked by `lean/Resolution.lean`.

For every RUP step the hints describe a unit-propagation derivation of a conflict
from the negated clause.  Read backwards, that derivation is a chain of
resolution steps; the chain's result is a sub-clause of the clause, which is
then obtained by weakening.  Every produced step is verified locally here, so
the Lean checker only has to re-check what this script has already checked with
an independent implementation.

Usage:
    python3 expand_resolution.py --proof proof_s3.rup --problem s3 --out cert_s3.txt
    python3 expand_resolution.py --proof proof_s3.rup --problem s3 --lean ../lean/CertificateS3.lean
"""
import argparse
import sys

import cdcl45


def read_proof(path):
    steps = []
    for line in open(path):
        if not line.strip():
            continue
        toks = line.split()
        i = toks.index("0")
        clause = [int(x) for x in toks[:i]]
        rest = toks[i + 1:]
        n = int(rest[0])
        hints = [int(x) for x in rest[1:1 + n]]
        steps.append((clause, hints))
    return steps


def resolve(c1, c2, v):
    """Resolvent exactly as `Resolution.resolventOf` computes it: `c1` is the
    parent containing the positive pivot `v`, `c2` the one containing `-v`;
    the two pivot literals are removed and duplicates dropped."""
    out = []
    for l in c1:
        if l != v and l not in out:
            out.append(l)
    for l in c2:
        if l != -v and l not in out:
            out.append(l)
    return out


def expand(base, proof):
    """returns a list of (clause, justification) with indices into base ++ derived

    Two databases are maintained: `certDb` mirrors the RUP certificate (base
    clauses followed by the derived clauses, so the hint indices are the
    certificate's), while `deriv` is the actual resolution derivation (which also
    contains the intermediate resolvents).  `certToDeriv` maps certificate
    indices to derivation indices.
    """
    certDb = [list(c) for c in base]
    deriv = [list(c) for c in base]
    certToDeriv = list(range(len(base)))
    out = []
    for step_no, (C, hints) in enumerate(proof):
        # --- replay the RUP step to obtain the trail -----------------------
        assign = {}
        for l in C:
            assign[abs(l)] = (l < 0)              # make literal l false
        for cl in certDb:
            if len(cl) == 1:
                l = cl[0]
                if abs(l) in assign and assign[abs(l)] != (l > 0):
                    return None, f"step {step_no}: unit clause contradicts the negated clause"
                assign[abs(l)] = (l > 0)
        units = []                                 # (certificate index, unit literal)
        # the unit clauses of the database seed the trail; they are reasons too
        for ci, cl in enumerate(certDb):
            if len(cl) == 1:
                units.append((ci, cl[0]))
        conflict = None
        for h in hints:
            cl = certDb[h]
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
                return None, f"step {step_no}: hint {h} is not unit"
            if un == 0:
                conflict = h
                break
            assign[abs(unit)] = unit > 0
            units.append((h, unit))
        if conflict is None:
            return None, f"step {step_no}: hints do not reach a conflict"

        # --- resolution chain (backwards through the trail) ----------------
        res = list(deriv[certToDeriv[conflict]])
        cur = certToDeriv[conflict]
        for (h, unit) in reversed(units):
            if -unit not in res:
                continue
            v = abs(unit)
            other = deriv[certToDeriv[h]]
            if unit not in other:
                return None, f"step {step_no}: hint {h} lacks its unit literal"
            # `Resolution.resolve` wants the parent with the *positive* pivot first
            if unit > 0:
                i, j = certToDeriv[h], cur
            else:
                i, j = cur, certToDeriv[h]
            r = resolve(deriv[i], deriv[j], v)
            deriv.append(r)
            out.append((r, ("resolve", i, j, v)))
            cur = len(deriv) - 1
            res = r

        # --- weaken to the clause itself if necessary ----------------------
        if set(res) != set(C):
            if not set(res) <= set(C):
                return None, f"step {step_no}: resolvent is not a sub-clause"
            deriv.append(list(C))
            out.append((C, ("weaken", cur)))
            cur = len(deriv) - 1
        certDb.append(list(C))
        certToDeriv.append(cur)
    return out, None


def verify(base, expanded):
    """independent local check of the produced derivation"""
    db = [list(c) for c in base]
    for i, (C, j) in enumerate(expanded):
        if j[0] == "resolve":
            _, a, b, v = j
            if v not in db[a]:
                return f"step {i}: positive pivot {v} missing in the first parent"
            if -v not in db[b]:
                return f"step {i}: negative pivot {-v} missing in the second parent"
            r = resolve(db[a], db[b], v)
            if set(r) != set(C):
                return f"step {i}: clause is not the resolvent"
        elif j[0] == "weaken":
            _, a = j
            if not set(db[a]) <= set(C):
                return f"step {i}: not a weakening"
        else:
            return f"step {i}: unknown justification"
        db.append(list(C))
    if not db or db[-1] != []:
        return "the derivation does not end with the empty clause"
    return None


def lit_lean(l):
    return f"({abs(l)}, {'true' if l > 0 else 'false'})"


def clause_lean(c):
    return "[" + ", ".join(lit_lean(l) for l in c) + "]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proof", required=True)
    ap.add_argument("--problem", choices=["s3", "s4"], default="s3")
    ap.add_argument("--sym", action="store_true")
    ap.add_argument("--out")
    ap.add_argument("--lean")
    ap.add_argument("--name", default="certS3")
    args = ap.parse_args()

    if args.problem == "s3":
        base, _ = cdcl45.build_cnf_s3()
    else:
        base = cdcl45.build_cnf(args.sym)
    proof = read_proof(args.proof)
    print(f"RUP proof: {len(proof)} steps", file=sys.stderr)

    expanded, err = expand(base, proof)
    if err:
        sys.exit("expansion FAILED: " + err)
    print(f"expanded to {len(expanded)} resolution/weakening steps", file=sys.stderr)

    err = verify(base, expanded)
    if err:
        sys.exit("independent verification FAILED: " + err)
    print("independent verification of the expansion: OK", file=sys.stderr)

    if args.out:
        with open(args.out, "w") as f:
            for C, j in expanded:
                if j[0] == "resolve":
                    _, a, b, v = j
                    f.write(f"{' '.join(map(str, C))} 0 resolve {a} {b} {v}\n")
                else:
                    _, a = j
                    f.write(f"{' '.join(map(str, C))} 0 weaken {a}\n")
        print(f"wrote {args.out}", file=sys.stderr)

    if args.lean:
        with open(args.lean, "w", encoding="utf-8") as f:
            f.write("import Resolution\n\n")
            f.write("/-! Generated by `bench/sat/expand_resolution.py` — do not edit. -/\n\n")
            f.write("namespace Resolution\n\n")
            f.write(f"def {args.name}Steps : List (Clause × Justify) :=\n  [\n")
            lines = []
            for C, j in expanded:
                if j[0] == "resolve":
                    _, a, b, v = j
                    lines.append(f"    ({clause_lean(C)}, .resolve {a} {b} {v})")
                else:
                    _, a = j
                    lines.append(f"    ({clause_lean(C)}, .weaken {a})")
            f.write(",\n".join(lines))
            f.write("\n  ]\n\nend Resolution\n")
        print(f"wrote {args.lean}", file=sys.stderr)


if __name__ == "__main__":
    main()
