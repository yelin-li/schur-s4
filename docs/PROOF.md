# Proof process, step by step

**TL;DR.**  `Good l` says that the colouring `l` of `{1, …, l.length}` has no
monochromatic `a + b = c`.  A backtracking search `searchB` is written down, and
proved correct (`searchB_spec`: it succeeds exactly on the good colourings that
also satisfy the symmetry condition `Ok23`).  Two *proved* symmetry reductions
shrink the search from 5 300 623 637 to 220 859 322 states.  The remaining tree
below the prefix `[0, 1]` is split into three independent files, each verified by
one `native_decide`.  A proved combination lemma turns the three verdicts into
“no good colouring of length 45 exists”; one explicit colouring of length 44
gives the other inequality.  Trust: the standard axioms plus those three
evaluations — see [`RIGOR.md`](RIGOR.md).

This document explains *how* the Lean proof of `S(4) = 44` is organised: which
lemma plays which role, why each step is sound, and how the exhaustive part is
kept as small as possible.  Every statement quoted below is a real theorem in
this repository, in the file named next to it.

*Notation.*  A colouring of `{1, …, N}` with 4 colours is a `List (Fin 4)` of
length `N`: entry `i` is the colour of `i + 1`.  The pattern to be avoided is a
monochromatic solution of `a + b = c` with `a, b, c ∈ {1, …, N}`.

---

## 1. The property to avoid (`Schur.lean`)

```lean
def Good {r : Nat} (l : List (Fin r)) : Prop :=
  ∀ i j : Nat, i < l.length → j < l.length → i + j + 1 < l.length →
    l[i]? = l[j]? → l[i + j + 1]? ≠ l[i]?
```

Indices are 0-based, so the triple `a + b = c` becomes
`(i, j, i + j + 1)`.  Requiring `i + j + 1 < l.length` restricts attention to
triples that fit inside the coloured interval.

Two remarks make this definition convenient:

* the same number may be used twice (`i = j`), which is exactly the case
  `a = b` of `a + b = c`, i.e. the doubling constraint `2a ≠ c`;
* nothing is said about triples that stick out of `{1, …, N}`.

## 2. A computable test, proved equivalent (`Schur.lean`)

```lean
def checkGood {r : Nat} (l : List (Fin r)) : Bool :=
  (List.range l.length).all fun i =>
    (List.range l.length).all fun j =>
      if l[i]? = l[j]? then !(decide (l[i + j + 1]? = l[i]?)) else true

theorem checkGood_sound    (h : checkGood l = true) : Good l
theorem checkGood_complete (h : Good l) : checkGood l = true
```

The test never indexes out of range: if `i + j + 1 ≥ l.length` then
`l[i + j + 1]? = none ≠ some _`, so the implication is discharged
automatically.  Both directions are needed later: soundness to *certify*
explicit colourings, completeness to feed the search specification.

## 3. Incremental feasibility (`Schur.lean`)

```lean
def extendOk {r : Nat} (l : List (Fin r)) (x : Fin r) : Bool :=
  (List.range l.length).all fun i =>
    if l[i]? = some x then !(decide (l[l.length - 1 - i]? = some x)) else true

theorem good_append (hl : Good l) (hx : extendOk l x = true) : Good (l ++ [x])
```

`extendOk l x` answers: may the *next* integer (position `l.length + 1`) receive
colour `x`?  The only new triples are those whose largest element is that
position, i.e. pairs `a + b = l.length + 1`; the loop enumerates them
(`a = i + 1`, `b = l.length - i`) and fails exactly when both are already
coloured `x`.  `good_append` turns this local check into a global statement, and
the converse `extendOk_of_good_cons` recovers the local check from a global
hypothesis — both are used in the search specification below.

## 4. The search and its specification (`Schur.lean`)

```lean
def search (r : Nat) : (n : Nat) → List (Fin r) → Bool
  | 0, l => checkGood l
  | n + 1, l => (List.finRange r).any fun x => extendOk l x && search r n (l ++ [x])

theorem search_spec (n : Nat) (l : List (Fin r)) :
    search r n l = true ↔ ∃ t : List (Fin r), t.length = n ∧ Good (l ++ t)
```

The proof is an induction on `n` in which the prefix `l` is generalised.  The
interesting direction is "a good colouring exists ⟹ the search finds one": if
`Good (l ++ (x :: t'))` holds, then by `extendOk_of_good_cons` the colour `x` is
admissible, and by the induction hypothesis the search continues successfully
below `l ++ [x]`.  Soundness is the mirror image, using `good_append` (and
`checkGood_complete` for the base case).

Because `search` returns a `Bool` and `search_spec` is a theorem, *the algorithm
carries its own correctness proof*: everything that follows only has to evaluate
it on closed inputs.

```lean
def Forcing (r N : Nat) : Prop := ¬ ∃ t : List (Fin r), t.length = N ∧ Good t
theorem forcing_iff_search : Forcing r N ↔ search r N [] = false
theorem forcing_mono (hNN' : N ≤ N') (h : Forcing r N) : Forcing r N'
```

The small values are decided here as well:
`one_color_exact` (`S(1) = 1`), `two_colors_exact` (`S(2) = 4`),
`three_colors_exact` (`S(3) = 13`).

## 5. First symmetry reduction: 12-fold (`Symmetry.lean`)

In a good colouring `1 + 1 = 2` forces `c(1) ≠ c(2)`.  Hence *some* permutation
of the four colours sends the pair `(c(1), c(2))` to `(0, 1)`.

```lean
theorem good_map_iff (hf : Function.Injective f) : Good (l.map f) ↔ Good l

def perms12 : List (Fin 4 → Fin 4)          -- twelve explicit permutations
def findPerm (a b : Fin 4) : Option (Fin 4 → Fin 4) :=
  perms12.find? fun π => decide (π a = 0) && decide (π b = 1) && Inj4 π

theorem lookup_ok : … = true := by decide    -- checked by the kernel, not native_decide
theorem exists_good_first_two (hg : Good t) (h2 : 2 ≤ t.length) :
    ∃ u, u.length = t.length ∧ Good u ∧ u[0]? = some 0 ∧ u[1]? = some 1
```

Why this is sound: `Good` only compares colours for equality, so relabelling by
an injective map cannot create or destroy a monochromatic triple
(`good_map_iff`).  Why the table is complete: that is the finite check
`lookup_ok`, discharged by `decide`, i.e. by the kernel — no compiler trust is
involved in the symmetry step.

## 6. Second symmetry reduction: another 12-fold (`RuleB.lean`)

After step 5 the colours `0` and `1` are pinned, but `2` and `3` are still
interchangeable, by the transposition

```lean
def swap23 : Fin 4 → Fin 4 := fun x => if x = 2 then 3 else if x = 3 then 2 else x
theorem swap23_injective : Function.Injective swap23
```

So we may assume that colour `3` is never used before colour `2`:

```lean
def Ok23 (l : List (Fin 4)) : Prop :=
  ∀ i, l[i]? = some 3 → ∃ j, j < i ∧ l[j]? = some 2

theorem ok23_disj (l : List (Fin 4)) : Ok23 l ∨ Ok23 (l.map swap23)
```

`ok23_disj` is proved by induction on the list: a leading `0` or `1` is
irrelevant (`ok23_cons_of_ne`), a leading `2` makes `Ok23` hold immediately
(`ok23_cons_two`), and a leading `3` is repaired by the transposition (which
turns it into a leading `2`).

The restricted search and its specification:

```lean
-- Fin4.lean: every element of Fin 4 is one of 0, 1, 2, 3
theorem fin4_cases (x : Fin 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3

def searchB : (n : Nat) → List (Fin 4) → Bool
  | 0, l => checkGood l
  | n + 1, l =>
      (extendOk l 0 && searchB n (l ++ [0])) ||
      ((extendOk l 1 && searchB n (l ++ [1])) ||
      ((extendOk l 2 && searchB n (l ++ [2])) ||
      (hasTwo l && (extendOk l 3 && searchB n (l ++ [3])))))

theorem searchB_spec (hl : Ok23 l) :
    searchB n l = true ↔ ∃ t, t.length = n ∧ Good (l ++ t) ∧ Ok23 (l ++ t)
```

The only difference from `search` is the extra conjunct `hasTwo l` on the
colour-`3` branch: colour `3` is tried only if colour `2` already occurs.  The
specification has to carry the `Ok23` invariant, which is why the induction
threads it through every branch
(`ok23_append_singleton_of_ne`, `ok23_append_three`, `ok23_of_append`).

Putting the two reductions together:

```lean
theorem exists_good_first_two_ok23 (hg : Good t) (h2 : 2 ≤ t.length) :
    ∃ u, u.length = t.length ∧ Good u ∧ u[0]? = some 0 ∧ u[1]? = some 1 ∧ Ok23 u
```

## 7. Splitting the remaining tree into three branches

The prefix `[0, 1]` contains no `2`, hence

```lean
theorem hasTwo_pair : hasTwo [(0 : Fin 4), (1 : Fin 4)] = false
```

so at position 3 the search may only try colours `0`, `1`, `2`
(`searchB_succ_iff` exposes the four-way case split).  The tree below `[0, 1]`
has 220 859 322 states; it is partitioned into three disjoint subtrees, one per
colour of the third integer.  Each subtree is verified in its own file:

```lean
-- BranchB0.lean
theorem branchB0 : searchB 42 ([(0 : Fin 4), 1] ++ [(0 : Fin 4)]) = false := by native_decide
-- BranchB1.lean
theorem branchB1 : searchB 42 ([(0 : Fin 4), 1] ++ [(1 : Fin 4)]) = false := by native_decide
-- BranchB2.lean
theorem branchB2 : searchB 42 ([(0 : Fin 4), 1] ++ [(2 : Fin 4)]) = false := by native_decide
```

and the three verdicts are combined by a *proved* lemma:

```lean
theorem searchB_false_of_three (hnot : hasTwo l = false)
    (h0 : searchB n (l ++ [0]) = false) (h1 : … [1] …) (h2 : … [2] …) :
    searchB (n + 1) l = false
```

Splitting has two advantages: the three evaluations are independent (and can be
run in parallel), and the combination step adds no further trust — it is an
ordinary kernel-checked proof about a `Bool`-valued function.

## 8. Assembly (`S4.lean`)

```lean
theorem searchB_prefix_43 : searchB 43 [(0 : Fin 4), (1 : Fin 4)] = false

theorem no_good_four_45 : ¬ ∃ t : List (Fin 4), t.length = 45 ∧ Good t
theorem four_colors_exact :
    (∃ t : List (Fin 4), t.length = 44 ∧ Good t) ∧ Forcing 4 45
```

The proof of `no_good_four_45` is now five lines of logic: take a hypothetical
good colouring of length 45, relabel it with
`exists_good_first_two_ok23`, observe that it must start with `0, 1`, and feed
the remainder into `searchB_spec`; the result contradicts `searchB_prefix_43`.

The lower bound is the explicit colouring of `{1, …, 44}` (Baumert–Golomb), whose
`Good`-ness is re-checked by the kernel:

```lean
theorem c4_44_good_kernel : Good c4_44 := checkGood_sound (by decide)
```

## 9. Trust base and audit

`Verify.lean` prints

```
'Schur.four_colors_exact' depends on axioms: [propext, Classical.choice, Quot.sound,
    branchB0._native.native_decide.ax_1_1,
    branchB1._native.native_decide.ax_1_1,
    branchB2._native.native_decide.ax_1_1]
```

So the audit has exactly two parts.

1. **Logic.** `propext`, `Classical.choice` and `Quot.sound` are Lean's standard
   axioms.  Everything in the `good_map_iff`/`search_spec`/`searchB_spec`/
   `searchB_false_of_three` chain is proved from them.
2. **Evaluation.** The three `native_decide` axioms say "the compiled program
   `searchB 42 (…)` returned `false`".  The program's *specification* is
   `searchB_spec`; the closed propositions evaluated are of the shape
   `searchB 42 prefix = false`, so the trusted statement is only "Lean's
   compiler evaluates this closed `Bool` faithfully".

Independently of Lean, the same search is implemented twice more in this
repository (`bench/measure.js`, `bench/reference_search.js`) and agrees on every
number, including the two numbers that can be compared with the literature:

* the deepest non-empty level of the verified tree has **273** states — the
  published number of 4-colourings of `{1, …, 44}` without a monochromatic sum
  (Eliahou 2016);
* the independent search finds **0** colourings of `{1, …, 45}`.

## 10. Figures

| figure | what it shows |
|---|---|
| `docs/figures/pipeline.svg` | which file proves what, and where the two trust boundaries are |
| `docs/figures/tree_profile.svg` | states visited per depth in the verified search, with the 273-state level marked |
| `docs/figures/reductions.svg` | size of the search tree before and after each symmetry reduction |
| `docs/figures/branches.svg` | the three verified branches and their sizes |
| `docs/figures/trust_base.svg` | kernel-checked items versus evaluated items |

They are regenerated by `python3 scripts/make_figures.py`, which reads the
measured data in `bench/out_AB.json` (produced by `bench/measure.js`).
