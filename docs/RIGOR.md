# Rigor: what is proved, what is trusted, what is not

This document is an honest audit of the formalisation.  It separates three
things that are easy to conflate: (i) what the kernel checks, (ii) what the
proof *trusts* beyond the kernel, and (iii) what has only been cross-checked.

## 1. The claim

```lean
-- Statement.lean
theorem S4_statement :
    (∃ l : List (Fin 4), l.length = 44 ∧ Good l) ∧
      (∀ l : List (Fin 4), l.length = 45 → ¬ Good l)
```

A list of length `N` with entries in `Fin 4` is a colouring of `{1, …, N}`
(entry `i` colours the integer `i + 1`), and `Good l` says that no colour class
contains `a`, `b` and `a + b`.  So the statement is: *`{1, …, 44}` has such a
colouring and `{1, …, 45}` does not*, i.e. `S(4) = 44` and the least forcing
number is `45`.

## 2. What the kernel checks

`#print axioms` (see `Verify.lean`) gives, for every ingredient:

| theorem | axioms | meaning |
|---|---|---|
| `checkGood_sound`, `checkGood_complete` | propext, Quot.sound | the computable test is equivalent to the specification |
| `extendOk_iff`, `good_append`, `extendOk_of_good_cons` | propext, Quot.sound | the incremental feasibility check is exactly the right one |
| `searchB_spec` | propext, Classical.choice, Quot.sound | **the search is correct: it succeeds exactly on the good colourings** |
| `ok23_disj`, `exists_good_first_two`, `exists_good_first_two_ok23` | propext, Quot.sound | both symmetry reductions |
| `searchB_false_of_three` | propext | the three branch verdicts combine correctly |
| `c4_44_good_kernel` | propext, Quot.sound | the explicit `[1, 44]` colouring is good (by `decide`) |
| `S4_all_shorter` | propext, Quot.sound | every shorter length is colour-able |

None of these depends on anything beyond Lean's standard axioms.  In particular
the *algorithm* has no trust footprint: `searchB_spec` is a theorem, not a test.

## 3. The one trust boundary

```
'Schur.S4_statement' depends on axioms: [propext, Classical.choice, Quot.sound,
    branchB0._native.native_decide.ax_1_1,
    branchB1._native.native_decide.ax_1_1,
    branchB2._native.native_decide.ax_1_1]
```

Those three `native_decide` axioms record that "the compiled program
`searchB 42 (…)` returned `false`" for the three sub-trees.  Concretely, the
trusted statement is:

> Lean's compiler evaluates the closed term `searchB 42 ([(0:Fin 4),1] ++ [c])`
> faithfully.

What this does and does not cover:

* **Not** the algorithm — `searchB_spec` reduces the evaluation to an ordinary
  mathematical statement, so a bug in the *design* of the search would show up as
  a failed proof, not as a wrong result.
* **Not** the modelling of the problem — that is `Good`, checked by
  `checkGood_sound`/`checkGood_complete` and by the readable restatement.
* **Only** the compiler/`ofReduceBool` mechanism.  The term is closed (no inputs,
  no environment, no IO, no `unsafe`), the function is total and pure, and the
  computation is deterministic, so the failure mode would be a miscompilation or
  a bug in the native evaluator, not nondeterminism or adversarial input.

This is the standard `native_decide` trade-off, and it is the same choice large
verification projects make.  It is, however, a real trust boundary, and a referee
is entitled to point at it.  Section 6 lists the ways to remove it.

## 4. Evidence that is *not* proof

Three independent implementations agree:

| what | implementation | result |
|---|---|---|
| the search tree sizes | `bench/measure.js` (JavaScript) | 5 300 623 637 / 1 325 155 910 / 441 718 638 / **220 859 322** |
| the branch sizes | `bench/branches.js` | 47 033 043 / 95 553 318 / 78 272 958 |
| `S(4) = 44` | `bench/reference_search.js` | 273 colourings of `[1,44]` (canonical), 0 of `[1,45]` |
| the `[1,44]` colouring | `bench/verify_coloring.py` | no monochromatic triple among all 484 ordered pairs |
| the published count | literature (Eliahou 2016) | 273 |

This is strong *evidence*: the deepest non-empty level of the verified tree has
exactly 273 states, and 273 is the number published in the literature, so the
Lean evaluation, the JavaScript search and the literature agree on a number that
would be extremely sensitive to an off-by-one or a wrong pruning rule.

It is not a proof: the JavaScript and Python programs share my understanding of
the problem, and they are not verified.  Only the kernel (plus the three
evaluations) is a proof.

## 5. Known weaknesses, ranked

1. **No certificate for the three evaluations** (the trust boundary above).
   The three statements are opaque `Bool` equalities of ~2·10⁸ steps; a reader
   cannot inspect *why* they are false.  This is the main gap.
2. **The headline statement is list-based (with a readable length-form
   restatement).**  A restatement in the form
   `Coloring N r := Fin N → Fin r` with `SumFree` would remove any doubt about
   the encoding; the bridge is routine but has not been written yet
   (`Statement.lean` currently proves the length-form restatement and the
   "all shorter lengths" form, both with the same trust base).
3. **No second formalisation** in a different proof assistant or a different
   encoding (e.g. a SAT-style encoding), which would catch a systematic
   misunderstanding.
4. **Scope creep in the data module.**  `SchurData.lean` also contains explicit
   colourings for `r = 5` and `r = 6` from the same tooling; they are not used
   by the `S(4)` proof (the README says so).
5. **Performance, not correctness.**  The list-based search is ~190× slower per
   state than the JavaScript version (see `docs/OPTIMIZATION.md`); this is why
   the three branches take ~20 minutes instead of ~1 minute.  It has no effect on
   the trust base.

## 6. What would make it airtight

In increasing order of effort:

1. **Certificate + verified checker.**  Emit, for each branch, a *refutation
   certificate* — e.g. a partition of the branch into cubes each refuted by unit
   propagation (RUP), or a resolution/DRAT derivation — and check it with a small
   verified checker in Lean.  The trust then becomes "a ~50-line checker is
   correct and the compiler runs it faithfully on explicit data", which is much
   narrower than trusting a compiler run of the search itself.  This is exactly
   the approach used by the 2026 work on covering codes that checks CNF + LRAT
   refutations inside Lean; it needs a clause-generation front end (a small
   CDCL/lookahead solver, which this environment does not provide) and a
   verified RUP/LRAT checker (~200–400 lines).
2. **Kernel `decide`.**  Replace `native_decide` by `decide`.  Sound by
   construction, but the kernel would have to reduce ~2.6·10⁸ search states;
   this is far beyond practical kernel evaluation times.
3. **Function-based restatement.**  Write the `Fin N → Fin 4` bridge (weakness 2).
   Cheap, and it addresses *encoding* doubt rather than *evaluation* doubt.
4. **Second formalisation**, e.g. re-derive the upper bound from a verified
   SAT-style encoding with a different search order, ideally in another system.

## 7. Readability: current state and what was improved

Good:

* the README states the theorem first, in Lean, with the conventions explained;
* `docs/PROOF.md` walks from `Good` to `S4_statement`, lemma by lemma;
* every file and most lemmas carry doc comments; the figures summarise the
  pipeline, the search profile, the reductions, the branches and the trust base;
* a Chinese README is included.

Weak (and what to do):

| weakness | status |
|---|---|
| headline was only in `Forcing` form | **fixed**: `S4_statement` states it with explicit lengths |
| no explicit audit document | **fixed**: this file |
| no theorem index | **fixed**: `Verify.lean` now prints the statements and their axioms; README has a table |
| one very dense proof (`searchB_spec`) | acceptable, but a paragraph of prose in `PROOF.md` §6 explains the induction; a comment block inside the file would help further |
| figures use small type at default zoom | known; the SVGs scale, but the pipeline figure could use larger labels |

## 8. Status of the certificate route (added later)

The recipe in §6.1 is now **implemented and proved**, and demonstrated end to end
on the `S(3)` instance; the `S(4)` instance itself is refuted *with a
certificate*, but that certificate has not yet been checked by the proved Lean
checker.

* `bench/sat/cdcl45.js` (and the earlier `cdcl45.py`) — a CDCL solver written
  from scratch (no external SAT solver) emits a RUP proof;
* `bench/sat/verify_rup.py` — an independent RUP checker;
  `trim_proof.py` trims; `expand_resolution.py` expands RUP into explicit
  resolution steps and verifies each step locally;
* `Resolution.lean` — a ~250-line checker with **only** `resolve` and `weaken`
  and a complete soundness proof,
  `checkProof_sound : checkProof cert = true → ¬ ∃ a, ∀ c ∈ base, Sat a c`
  (no `sorry`, standard axioms only);
* `CertificateS3.lean` + `CertCheckS3.lean` + `Encoding.lean` — the generated
  `S(3)` certificate is accepted by the proved checker, and the encoding lemma
  turns it into the mathematical statement `Schur.Forcing 3 14`
  (`forcing_three_certified`), whose trust base is `propext`, `Quot.sound` and
  two `native_decide` evaluations (of the checker on explicit data, and of the
  agreement between the generated CNF and its structural definition).

Measured results:

| instance | solver | certificate | independent checks | Lean |
|---|---|---|---|---|
| `S(3)` = 13 | UNSAT, 128 conflicts | 128 RUP steps (7.9 KB) | RUP + expansion OK | **accepted**, `Forcing 3 14` proved |
| `S(4)` = 44 | UNSAT, 214 490 conflicts (≈ 12 s) | 214 490 RUP steps (34 MB) | RUP + trimming OK | not checked: ≈ 4.6 M resolution steps |

So the remaining gap for `S(4)` is quantitative (`≈ 400 MB` of generated data and
hours of checking through the resolution route), and the way to close it is a
proved **RUP** checker in Lean (34 MB, single pass), whose only missing piece is
the soundness proof (the trail invariant).  Until then the trust base of
`S4_statement` is exactly the one in §3.  Details and reproduction commands:
`docs/CERTIFICATES.md`.
