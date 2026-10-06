import Schur
import Symmetry
import RuleB
import BranchB0
import BranchB1
import BranchB2

/-!
# `S(4) = 44`

* **Lower bound.** `Schur.exists_four_coloring_44` exhibits an explicit
  4-colouring of `{1, …, 44}` with no monochromatic `a + b = c`
  (Baumert–Golomb 1965).  Here it is re-checked by the *kernel* (`decide`).

* **Upper bound.** `no_good_four_45` proves that **every** 4-colouring of
  `{1, …, 45}` contains a monochromatic solution of `a + b = c`, i.e.
  `Forcing 4 45`.  The proof is a verified exhaustive search:

  1. `Symmetry.exists_good_first_two` — any good colouring can be relabelled so
     that its first two colours are `0` and `1` (12-fold reduction, kernel
     checked);
  2. `RuleB.exists_good_first_two_ok23` — after that, the transposition `(2 3)`
     lets us assume colour `3` never occurs before colour `2` (24-fold
     reduction, kernel checked);
  3. `RuleB.searchB_spec` — the restricted search is *specified by a theorem*:
     it succeeds exactly on the good colourings satisfying the order condition;
  4. the remaining tree below the prefix `[0, 1]` has **220 859 322** nodes; it
     is split into three disjoint branches (the colour of the third integer,
     which can only be `0`, `1` or `2`), each verified by `native_decide` in
     `BranchB0/1/2.lean`, and the three verdicts are combined by the *proved*
     lemma `RuleB.searchB_false_of_three`.

`#print axioms Schur.four_colors_exact` shows that the only non-kernel
assumptions are the three `native_decide` evaluations of the branches.
-/

namespace Schur

/-- The exhaustive search below the prefix `[0, 1]` has no leaf. -/
theorem searchB_prefix_43 : searchB 43 ([(0 : Fin 4), (1 : Fin 4)]) = false :=
  searchB_false_of_three [(0 : Fin 4), (1 : Fin 4)] 42 hasTwo_pair
    branchB0 branchB1 branchB2

/-- **Upper bound for `S(4)`.**  No 4-colouring of `{1, …, 45}` is sum-free. -/
theorem no_good_four_45 : ¬ ∃ t : List (Fin 4), t.length = 45 ∧ Good t := by
  rintro ⟨t, ht, hg⟩
  -- relabel: first two colours are 0, 1 and colour 3 comes after colour 2
  obtain ⟨u, hul, hug, hu0, hu1, hok⟩ := exists_good_first_two_ok23 hg (by omega)
  obtain ⟨t', ht'⟩ : ∃ t', u = (0 : Fin 4) :: (1 : Fin 4) :: t' := by
    cases u with
    | nil => simp at hu0
    | cons x xs =>
        cases xs with
        | nil => simp at hu1
        | cons y ys =>
            refine ⟨ys, ?_⟩
            have hx : x = 0 := by simpa using hu0
            have hy : y = 1 := by simpa using hu1
            rw [hx, hy]
  rw [ht'] at hul hug hok
  have ht'len : t'.length = 43 := by
    rw [List.length_cons, List.length_cons] at hul
    omega
  have hsearch : searchB 43 [(0 : Fin 4), (1 : Fin 4)] = true :=
    (searchB_spec 43 [(0 : Fin 4), (1 : Fin 4)] ok23_pair).mpr
      ⟨t', ht'len, by simpa using hug, by simpa using hok⟩
  rw [searchB_prefix_43] at hsearch
  cases hsearch

/-- The lower bound, re-checked by the kernel. -/
theorem c4_44_good_kernel : Good c4_44 := checkGood_sound (by decide)

theorem exists_four_coloring_44_kernel :
    ∃ t : List (Fin 4), t.length = 44 ∧ Good t :=
  ⟨c4_44, by decide, c4_44_good_kernel⟩

/-- **`S(4) = 44`**, in both conventions: `{1, …, 44}` has a sum-free
4-colouring, and `{1, …, 45}` has none. -/
theorem four_colors_exact :
    (∃ t : List (Fin 4), t.length = 44 ∧ Good t) ∧ Forcing 4 45 :=
  ⟨exists_four_coloring_44_kernel, no_good_four_45⟩

end Schur
