import Schur
import Symmetry
import Fin4

/-!
# Second symmetry reduction: the transposition `(2 3)`

`Symmetry.lean` reduces the search for a sum-free 4-colouring of `{1, …, 45}` to
those colourings whose first two colours are `0` and `1`.  The colours `2` and
`3` are then still interchangeable, because the transposition

`swap23 = (2 3)`

is a bijection of `Fin 4` that fixes `0` and `1`.  Hence we may additionally
assume

`Ok23 l`  :  colour `3` never occurs before colour `2`.

This file proves that reduction and defines the restricted search `searchB`,
whose specification is again a theorem:

`searchB n l = true ↔ ∃ t, t.length = n ∧ Good (l ++ t) ∧ Ok23 (l ++ t)`.

Effect on the exhaustive search below the prefix `[0, 1]`: the tree shrinks from
441 718 638 nodes to 220 859 322 nodes (both numbers are reproduced
independently by the JavaScript program `bench/prune_measure.js`).
-/

namespace Schur

/-! ## The transposition of colours `2` and `3` -/

/-- The transposition `(2 3)` of `Fin 4`, fixing `0` and `1`. -/
def swap23 : Fin 4 → Fin 4 := fun x => if x = 2 then 3 else if x = 3 then 2 else x

theorem swap23_injective : Function.Injective swap23 := inj4_sound (by decide)

theorem swap23_zero : swap23 0 = (0 : Fin 4) := by decide
theorem swap23_one : swap23 1 = (1 : Fin 4) := by decide
theorem swap23_two : swap23 2 = (3 : Fin 4) := by decide
theorem swap23_three : swap23 3 = (2 : Fin 4) := by decide

/-! ## The order condition `Ok23` -/

/-- `Ok23 l`: in the colouring `l`, colour `3` never occurs before colour `2`. -/
def Ok23 (l : List (Fin 4)) : Prop :=
  ∀ i : Nat, l[i]? = some (3 : Fin 4) → ∃ j : Nat, j < i ∧ l[j]? = some (2 : Fin 4)

theorem ok23_nil : Ok23 ([] : List (Fin 4)) := by
  intro i h; simp at h

/-- `(l ++ t)[i]? = l[i]?` for `i < l.length`. -/
theorem getElem?_append_of_lt' {α : Type} {l t : List α} {i : Nat}
    (h : i < l.length) : (l ++ t)[i]? = l[i]? := by
  rw [List.getElem?_append]
  simp [h]

/-- `Ok23` is inherited by prefixes. -/
theorem ok23_of_append {l t : List (Fin 4)} (h : Ok23 (l ++ t)) : Ok23 l := by
  intro i hi
  obtain ⟨hi_lt, _⟩ := List.getElem?_eq_some_iff.mp hi
  have hi' : (l ++ t)[i]? = some (3 : Fin 4) := by
    rw [getElem?_append_of_lt' hi_lt]; exact hi
  obtain ⟨j, hj, hj2⟩ := h i hi'
  have hj_lt : j < l.length := Nat.lt_trans hj hi_lt
  refine ⟨j, hj, ?_⟩
  rw [← getElem?_append_of_lt' (t := t) hj_lt]
  exact hj2

/-- Prepending a colour that is neither `2` nor `3` preserves `Ok23`. -/
theorem ok23_cons_of_ne {x : Fin 4} (hx2 : x ≠ 2) (hx3 : x ≠ 3) {l : List (Fin 4)} :
    Ok23 (x :: l) ↔ Ok23 l := by
  constructor
  · intro h i hi
    have h1 : (x :: l)[i + 1]? = some (3 : Fin 4) := by simpa using hi
    obtain ⟨j, hj, hj2⟩ := h (i + 1) h1
    cases j with
    | zero => simp at hj2; exact absurd hj2 hx2
    | succ j' => exact ⟨j', by omega, by simpa using hj2⟩
  · intro h i hi
    cases i with
    | zero => simp at hi; exact absurd hi hx3
    | succ i' =>
        have h3 : l[i']? = some (3 : Fin 4) := by simpa using hi
        obtain ⟨j', hj', hj'2⟩ := h i' h3
        exact ⟨j' + 1, by omega, by simpa using hj'2⟩

/-- A list beginning with colour `2` satisfies `Ok23`. -/
theorem ok23_cons_two {l : List (Fin 4)} : Ok23 ((2 : Fin 4) :: l) := by
  intro i hi
  cases i with
  | zero => simp at hi
  | succ i' => exact ⟨0, by omega, by simp⟩

/-- Appending a colour different from `3` preserves `Ok23`. -/
theorem ok23_append_singleton_of_ne {l : List (Fin 4)} {x : Fin 4}
    (hx : x ≠ 3) (h : Ok23 l) : Ok23 (l ++ [x]) := by
  intro i hi
  by_cases hi' : i < l.length
  · have h1 : (l ++ [x])[i]? = l[i]? := getElem?_append_singleton_of_lt hi'
    rw [h1] at hi
    obtain ⟨j, hj, hj2⟩ := h i hi
    refine ⟨j, hj, ?_⟩
    rw [getElem?_append_singleton_of_lt (Nat.lt_trans hj hi')]
    exact hj2
  · obtain ⟨hi_lt, _⟩ := List.getElem?_eq_some_iff.mp hi
    have heq : i = l.length := by
      rw [List.length_append, List.length_singleton] at hi_lt
      omega
    rw [heq, List.getElem?_append] at hi
    simp at hi
    exact absurd hi hx

/-- The list contains colour `2`. -/
def hasTwo (l : List (Fin 4)) : Bool := l.any fun x => decide (x = (2 : Fin 4))

theorem hasTwo_iff {l : List (Fin 4)} : hasTwo l = true ↔ (2 : Fin 4) ∈ l := by
  rw [hasTwo, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    rw [decide_eq_true_eq] at h
    subst h
    exact hx
  · intro h; exact ⟨2, h, by simp⟩

/-- Appending colour `3` is compatible with `Ok23` exactly when colour `2`
already occurs. -/
theorem ok23_append_three {l : List (Fin 4)} (h : Ok23 l) :
    Ok23 (l ++ [(3 : Fin 4)]) ↔ hasTwo l = true := by
  constructor
  · intro h3
    have hlast : (l ++ [(3 : Fin 4)])[l.length]? = some (3 : Fin 4) := by
      rw [List.getElem?_append]; simp
    obtain ⟨j, hj, hj2⟩ := h3 l.length hlast
    have hj' : j < l.length := hj
    have hmem : l[j]? = some (2 : Fin 4) := by
      rw [← getElem?_append_of_lt' (t := [(3 : Fin 4)]) hj']
      exact hj2
    rw [hasTwo_iff]
    exact List.mem_iff_getElem?.mpr ⟨j, hmem⟩
  · intro h2
    rw [hasTwo_iff] at h2
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h2
    obtain ⟨hj_lt, _⟩ := List.getElem?_eq_some_iff.mp hj
    intro i hi
    by_cases hi' : i < l.length
    · have h1 : (l ++ [(3 : Fin 4)])[i]? = l[i]? := getElem?_append_singleton_of_lt hi'
      rw [h1] at hi
      obtain ⟨j', hj', hj'2⟩ := h i hi
      refine ⟨j', hj', ?_⟩
      rw [getElem?_append_singleton_of_lt (Nat.lt_trans hj' hi')]
      exact hj'2
    · refine ⟨j, by omega, ?_⟩
      rw [getElem?_append_singleton_of_lt hj_lt]
      exact hj

/-- **Disjunction.**  For every colouring, either it or its `(2 3)`-image
satisfies `Ok23`. -/
theorem ok23_disj (l : List (Fin 4)) : Ok23 l ∨ Ok23 (l.map swap23) := by
  induction l with
  | nil => exact Or.inl ok23_nil
  | cons x t ih =>
      rcases fin4_cases x with h | h | h | h
      · subst h
        rw [ok23_cons_of_ne (x := (0 : Fin 4)) (by decide) (by decide)]
        rw [List.map_cons, swap23_zero,
          ok23_cons_of_ne (x := (0 : Fin 4)) (by decide) (by decide)]
        exact ih
      · subst h
        rw [ok23_cons_of_ne (x := (1 : Fin 4)) (by decide) (by decide)]
        rw [List.map_cons, swap23_one,
          ok23_cons_of_ne (x := (1 : Fin 4)) (by decide) (by decide)]
        exact ih
      · subst h
        exact Or.inl ok23_cons_two
      · subst h
        rw [List.map_cons, swap23_three]
        exact Or.inr ok23_cons_two

/-! ## The reduced search -/

/-- Restricted search: as `Schur.search`, but colour `3` may be used only after
colour `2` has appeared. -/
def searchB : (n : Nat) → List (Fin 4) → Bool
  | 0, l => checkGood l
  | n + 1, l =>
      (extendOk l 0 && searchB n (l ++ [0])) ||
      ((extendOk l 1 && searchB n (l ++ [1])) ||
      ((extendOk l 2 && searchB n (l ++ [2])) ||
      (hasTwo l && (extendOk l 3 && searchB n (l ++ [3])))))

theorem searchB_succ_iff (l : List (Fin 4)) (n : Nat) :
    searchB (n + 1) l = true ↔
      (extendOk l 0 = true ∧ searchB n (l ++ [0]) = true) ∨
      ((extendOk l 1 = true ∧ searchB n (l ++ [1]) = true) ∨
      ((extendOk l 2 = true ∧ searchB n (l ++ [2]) = true) ∨
      (hasTwo l = true ∧ extendOk l 3 = true ∧ searchB n (l ++ [3]) = true))) := by
  rw [searchB]
  simp only [Bool.or_eq_true, Bool.and_eq_true]

/-- Specification of the restricted search. -/
theorem searchB_spec (n : Nat) (l : List (Fin 4)) (hl : Ok23 l) :
    searchB n l = true ↔
      ∃ t : List (Fin 4), t.length = n ∧ Good (l ++ t) ∧ Ok23 (l ++ t) := by
  induction n generalizing l with
  | zero =>
      constructor
      · intro h
        exact ⟨[], rfl, by simpa [searchB] using checkGood_sound h, by simpa using hl⟩
      · rintro ⟨t, ht, hg, _⟩
        cases t with
        | nil => simpa [searchB] using checkGood_complete (by simpa using hg)
        | cons y ys => simp at ht
  | succ n ih =>
      rw [searchB_succ_iff]
      constructor
      · rintro (⟨h0, hs0⟩ | ⟨h1, hs1⟩ | ⟨h2, hs2⟩ | ⟨h3a, h3b, hs3⟩)
        · obtain ⟨t, ht, hg, hok⟩ :=
            (ih (l ++ [0]) (ok23_append_singleton_of_ne (by decide) hl)).mp hs0
          exact ⟨0 :: t, by simp [ht],
            by simpa [List.singleton_append, List.append_assoc] using hg,
            by simpa [List.singleton_append, List.append_assoc] using hok⟩
        · obtain ⟨t, ht, hg, hok⟩ :=
            (ih (l ++ [1]) (ok23_append_singleton_of_ne (by decide) hl)).mp hs1
          exact ⟨1 :: t, by simp [ht],
            by simpa [List.singleton_append, List.append_assoc] using hg,
            by simpa [List.singleton_append, List.append_assoc] using hok⟩
        · obtain ⟨t, ht, hg, hok⟩ :=
            (ih (l ++ [2]) (ok23_append_singleton_of_ne (by decide) hl)).mp hs2
          exact ⟨2 :: t, by simp [ht],
            by simpa [List.singleton_append, List.append_assoc] using hg,
            by simpa [List.singleton_append, List.append_assoc] using hok⟩
        · have hok3 : Ok23 (l ++ [(3 : Fin 4)]) := (ok23_append_three hl).mpr h3a
          obtain ⟨t, ht, hg, hok⟩ := (ih (l ++ [(3 : Fin 4)]) hok3).mp hs3
          exact ⟨3 :: t, by simp [ht],
            by simpa [List.singleton_append, List.append_assoc] using hg,
            by simpa [List.singleton_append, List.append_assoc] using hok⟩
      · rintro ⟨t, ht, hg, hok⟩
        cases t with
        | nil => simp at ht
        | cons x t' =>
            have hg' : Good ((l ++ [x]) ++ t') := by
              simpa [List.singleton_append, List.append_assoc] using hg
            have hok' : Ok23 ((l ++ [x]) ++ t') := by
              simpa [List.singleton_append, List.append_assoc] using hok
            have hx3 : extendOk l x = true :=
              extendOk_of_good_cons (l := l) (t := t')
                (by simpa [List.singleton_append, List.append_assoc] using hg)
            have hokx : Ok23 (l ++ [x]) := ok23_of_append hok'
            have hlen : t'.length = n := by
              simp at ht
              omega
            rcases fin4_cases x with h | h | h | h
            · subst h
              exact Or.inl ⟨hx3, (ih (l ++ [0]) (by simpa using hokx)).mpr ⟨t', hlen, hg', hok'⟩⟩
            · subst h
              exact Or.inr (Or.inl ⟨hx3,
                (ih (l ++ [1]) (by simpa using hokx)).mpr ⟨t', hlen, hg', hok'⟩⟩)
            · subst h
              exact Or.inr (Or.inr (Or.inl ⟨hx3,
                (ih (l ++ [2]) (by simpa using hokx)).mpr ⟨t', hlen, hg', hok'⟩⟩))
            · subst h
              have hh2 : hasTwo l = true := (ok23_append_three hl).mp (by simpa using hokx)
              exact Or.inr (Or.inr (Or.inr ⟨hh2, hx3,
                (ih (l ++ [(3 : Fin 4)]) (by simpa using hokx)).mpr ⟨t', hlen, hg', hok'⟩⟩))

/-- **Symmetry reduction.**  Any good 4-colouring of length `≥ 2` can be
relabelled so that its first two colours are `0` and `1` and, in addition,
colour `3` never occurs before colour `2`. -/
theorem exists_good_first_two_ok23 {t : List (Fin 4)} (hg : Good t) (h2 : 2 ≤ t.length) :
    ∃ u : List (Fin 4), u.length = t.length ∧ Good u ∧
      u[0]? = some (0 : Fin 4) ∧ u[1]? = some (1 : Fin 4) ∧ Ok23 u := by
  obtain ⟨u, hul, hug, hu0, hu1⟩ := exists_good_first_two hg h2
  rcases ok23_disj u with hok | hok
  · exact ⟨u, hul, hug, hu0, hu1, hok⟩
  · refine ⟨u.map swap23, by simp [hul], (good_map_iff swap23_injective u).mpr hug, ?_, ?_, hok⟩
    · rw [List.getElem?_map, hu0]; simp [swap23_zero]
    · rw [List.getElem?_map, hu1]; simp [swap23_one]

/-- The initial prefix `[0, 1]` satisfies the order condition. -/
theorem ok23_pair : Ok23 ([(0 : Fin 4), (1 : Fin 4)]) := by
  rw [ok23_cons_of_ne (x := (0 : Fin 4)) (by decide) (by decide)]
  rw [ok23_cons_of_ne (x := (1 : Fin 4)) (by decide) (by decide)]
  exact ok23_nil

/-- The prefix `[0, 1]` does not yet contain colour `2`, so colour `3` is not
admissible at position 3 and the third branch of the search is empty. -/
theorem hasTwo_pair : hasTwo ([(0 : Fin 4), (1 : Fin 4)]) = false := by decide

/-- Three branch verdicts (colours `0`, `1`, `2` at position `l.length + 1`)
suffice when colour `2` has not occurred yet. -/
theorem searchB_false_of_three (l : List (Fin 4)) (n : Nat) (hnot : hasTwo l = false)
    (h0 : searchB n (l ++ [(0 : Fin 4)]) = false)
    (h1 : searchB n (l ++ [(1 : Fin 4)]) = false)
    (h2 : searchB n (l ++ [(2 : Fin 4)]) = false) :
    searchB (n + 1) l = false := by
  cases hb : searchB (n + 1) l with
  | false => rfl
  | true =>
      rw [searchB_succ_iff] at hb
      rcases hb with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨hh2, _, hx⟩
      · rw [h0] at hx; cases hx
      · rw [h1] at hx; cases hx
      · rw [h2] at hx; cases hx
      · rw [hnot] at hh2; cases hh2

/-- Four branch verdicts for the restricted search give the verdict at the
parent node. -/
theorem searchB_false_of_four (l : List (Fin 4)) (n : Nat)
    (h0 : searchB n (l ++ [(0 : Fin 4)]) = false)
    (h1 : searchB n (l ++ [(1 : Fin 4)]) = false)
    (h2 : searchB n (l ++ [(2 : Fin 4)]) = false)
    (h3 : searchB n (l ++ [(3 : Fin 4)]) = false) :
    searchB (n + 1) l = false := by
  cases hb : searchB (n + 1) l with
  | false => rfl
  | true =>
      rw [searchB_succ_iff] at hb
      rcases hb with ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, hx⟩ | ⟨_, _, hx⟩
      · rw [h0] at hx; cases hx
      · rw [h1] at hx; cases hx
      · rw [h2] at hx; cases hx
      · rw [h3] at hx; cases hx

end Schur
