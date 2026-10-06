#!/usr/bin/env python3
"""
Independent RUP certificate checker (separate implementation from the solver).

Reads a certificate produced by cdcl45.py and the same CNF, and replays every
step: for the step's clause C, the assignment is built by negating C, and each
hint clause must be either unit (in which case its unit literal is assigned) or
falsified (which closes the step).  The last step must derive the empty clause.

This is deliberately written without any of the solver's data structures, so a
mistake in the solver's own propagation cannot hide here.

Usage: python3 verify_rup.py --proof proof45.rup [--problem s4] [--sym]
"""
import argparse
import sys

import cdcl45


def check(base, proof_path, verbose=True):
    db = [list(c) for c in base]
    occ = {}
    for idx, cl in enumerate(db):
        for l in cl:
            occ.setdefault(l, []).append(idx)
    units = [idx for idx, cl in enumerate(db) if len(cl) == 1]
    checked = 0
    with open(proof_path) as f:
        for lineno, line in enumerate(f, 1):
            if not line.strip():
                continue
            toks = line.split()
            if "0" not in toks:
                return f"line {lineno}: missing 0 separator"
            i = toks.index("0")
            clause = [int(x) for x in toks[:i]]
            rest = toks[i + 1:]
            if not rest:
                return f"line {lineno}: missing hint count"
            nhints = int(rest[0])
            hints = [int(x) for x in rest[1:1 + nhints]]
            if len(hints) != nhints:
                return f"line {lineno}: expected {nhints} hints, got {len(hints)}"
            assign = {}
            for l in clause:
                v, val = abs(l), l < 0
                if v in assign and assign[v] != val:
                    return f"line {lineno}: tautological clause"
                assign[v] = val
            # unit clauses of the database are part of unit propagation; the
            # list is maintained incrementally (scanning the database per step
            # would be quadratic)
            unit_assign = {}
            for ci in units:
                l = db[ci][0]
                unit_assign[abs(l)] = l > 0
            for v, val in unit_assign.items():
                if v in assign and assign[v] != val:
                    return f"line {lineno}: clause contradicts a unit clause"
                assign[v] = val
            queue = [v if val else -v for v, val in assign.items()]
            head = 0
            conflict = False
            for h in hints:
                if not (0 <= h < len(db)):
                    return f"line {lineno}: hint {h} out of range"
                cl = db[h]
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
                    return f"line {lineno}: hint clause {h} is neither unit nor falsified"
                if unassigned == 0:
                    conflict = True
                    break
                assign[abs(unit)] = unit > 0
            if not conflict:
                return f"line {lineno}: hints do not end in a conflict"
            ci = len(db)
            db.append(clause)
            if len(clause) == 1:
                units.append(ci)
            for l in clause:
                occ.setdefault(l, []).append(ci)
            checked += 1
    if not db or db[-1] != []:
        return "the last derived clause is not the empty clause"
    if verbose:
        print(f"RUP verification OK: {checked} steps checked, "
              f"database grew to {len(db)} clauses")
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proof", required=True)
    ap.add_argument("--problem", choices=["s3", "s4"], default="s4")
    ap.add_argument("--sym", action="store_true")
    args = ap.parse_args()
    if args.problem == "s3":
        base, _ = cdcl45.build_cnf_s3()
    else:
        base = cdcl45.build_cnf(args.sym)
    err = check(base, args.proof)
    if err:
        sys.exit("RUP verification FAILED: " + err)


if __name__ == "__main__":
    main()
