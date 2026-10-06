import Std
import SchurData

/-!
# Schur numbers: machine-checked lower bounds, and the two conventions

Colour each positive integer with one of `r` colours.  Schur's theorem (1916)
says that some colour class must then contain `x, y, z` with `x + y = z`.
Two conventions are in use for the associated number:

* `S(r)`  = the largest `N` such that `{1, …, N}` admits an `r`-colouring with
  no monochromatic solution of `a + b = c`            (OEIS A045652);
* `S'(r)` = the least `N` such that *every* `r`-colouring of `{1, …, N}` has
  one, i.e. the number in the "a monochromatic solution is guaranteed"
  convention                                       (OEIS A030126).

A list of length `N` of colours *is* a colouring of `{1, …, N}`: entry `i` is
the colour of `i + 1`.
-/

namespace Schur

/-! ## The sum-free property -/

/-- `Good l` says: the list `l` lists the colours of `1, 2, …, l.length`, and no
colour class contains `a`, `b`, `a + b`.

Indices are 0-based: `l[i]?` is the colour of `i + 1`, so a solution
`a + b = c` of `{1, …, l.length}` corresponds to indices `i, j, i + j + 1`
with `i + j + 1 < l.length`. -/
def Good {r : Nat} (l : List (Fin r)) : Prop :=
  ∀ i j : Nat, i < l.length → j < l.length → i + j + 1 < l.length →
    l[i]? = l[j]? → l[i + j + 1]? ≠ l[i]?

/-- Computable decision procedure for `Good`. -/
def checkGood {r : Nat} (l : List (Fin r)) : Bool :=
  (List.range l.length).all fun i =>
    (List.range l.length).all fun j =>
      if l[i]? = l[j]? then !(decide (l[i + j + 1]? = l[i]?)) else true

/-- Soundness: a successful test proves `Good`. -/
theorem checkGood_sound {r : Nat} {l : List (Fin r)} (h : checkGood l = true) :
    Good l := by
  intro i j hi hj hij hcol
  rw [checkGood, List.all_eq_true] at h
  have hi' : i ∈ List.range l.length := by simpa [List.mem_range] using hi
  have hj' : j ∈ List.range l.length := by simpa [List.mem_range] using hj
  have h1 := h i hi'
  rw [List.all_eq_true] at h1
  have h2 := h1 j hj'
  rw [if_pos hcol] at h2
  intro hcontra
  rw [hcontra] at h2
  simp at h2

/-- Completeness: `Good` implies a successful test. -/
theorem checkGood_complete {r : Nat} {l : List (Fin r)} (h : Good l) :
    checkGood l = true := by
  rw [checkGood, List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have hi' : i < l.length := by simpa [List.mem_range] using hi
  have hj' : j < l.length := by simpa [List.mem_range] using hj
  by_cases hcol : l[i]? = l[j]?
  · rw [if_pos hcol]
    by_cases hlt : i + j + 1 < l.length
    · have hne : l[i + j + 1]? ≠ l[i]? := h i j hi' hj' hlt hcol
      simp [hne]
    · have hnone : l[i + j + 1]? = none := List.getElem?_eq_none (by omega)
      have hsome : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
      rw [hnone, hsome]
      simp
  · simp [hcol]

theorem checkGood_iff {r : Nat} (l : List (Fin r)) : checkGood l = true ↔ Good l :=
  ⟨checkGood_sound, checkGood_complete⟩

/-! ## The explicit colourings (data verified before being emitted) -/

theorem c1_1_good : Good c1_1 := checkGood_sound (by native_decide)
theorem c2_4_good : Good c2_4 := checkGood_sound (by native_decide)
theorem c3_13_good : Good c3_13 := checkGood_sound (by native_decide)
theorem c4_44_good : Good c4_44 := checkGood_sound (by native_decide)
theorem c5_160_good : Good c5_160 := checkGood_sound (by native_decide)
theorem c6_536_good : Good c6_536 := checkGood_sound (by native_decide)

/-- `{1, …, 536}` admits a 6-colouring with no monochromatic `a + b = c`.
This is the known lower bound `S(6) ≥ 536` (Fredricksen–Sweet 2000), here
re-verified from an explicit colouring. -/
theorem exists_six_coloring_536 :
    ∃ t : List (Fin 6), t.length = 536 ∧ Good t :=
  ⟨c6_536, c6_536_length, c6_536_good⟩

/-- `S(5) ≥ 160`: a 5-colouring of `{1, …, 160}` (Exoo 1994). -/
theorem exists_five_coloring_160 :
    ∃ t : List (Fin 5), t.length = 160 ∧ Good t :=
  ⟨c5_160, c5_160_length, c5_160_good⟩

/-- `S(4) ≥ 44`: a 4-colouring of `{1, …, 44}` (Baumert–Golomb 1965). -/
theorem exists_four_coloring_44 :
    ∃ t : List (Fin 4), t.length = 44 ∧ Good t :=
  ⟨c4_44, c4_44_length, c4_44_good⟩

/-- `S(3) ≥ 13`. -/
theorem exists_three_coloring_13 :
    ∃ t : List (Fin 3), t.length = 13 ∧ Good t :=
  ⟨c3_13, c3_13_length, c3_13_good⟩

/-- `S(2) ≥ 4`. -/
theorem exists_two_coloring_4 :
    ∃ t : List (Fin 2), t.length = 4 ∧ Good t :=
  ⟨c2_4, c2_4_length, c2_4_good⟩

/-- `S(1) ≥ 1`. -/
theorem exists_one_coloring_1 :
    ∃ t : List (Fin 1), t.length = 1 ∧ Good t :=
  ⟨c1_1, c1_1_length, c1_1_good⟩

/-! ## Exhaustive search: the upper bounds -/

/-- `extendOk l x`: giving the integer `l.length + 1` the colour `x` creates no
monochromatic triple, i.e. there is no `a + b = l.length + 1` with `a` and `b`
both of colour `x`. -/
def extendOk {r : Nat} (l : List (Fin r)) (x : Fin r) : Bool :=
  (List.range l.length).all fun i =>
    if l[i]? = some x then !(decide (l[l.length - 1 - i]? = some x)) else true

theorem extendOk_iff {r : Nat} {l : List (Fin r)} {x : Fin r} :
    extendOk l x = true ↔
      ∀ i, i < l.length → l[i]? = some x → l[l.length - 1 - i]? ≠ some x := by
  rw [extendOk, List.all_eq_true]
  constructor
  · intro h i hi hx
    have hh := h i (by simpa [List.mem_range] using hi)
    rw [if_pos hx] at hh
    intro hcontra
    rw [hcontra] at hh
    simp at hh
  · intro h i hi
    rw [List.mem_range] at hi
    by_cases hx : l[i]? = some x
    · rw [if_pos hx]
      have hne := h i hi hx
      simp [hne]
    · rw [if_neg hx]

/-- `(l ++ [x])[i]? = l[i]?` for `i < l.length`. -/
theorem getElem?_append_singleton_of_lt {α : Type} {l : List α} {x : α} {i : Nat}
    (h : i < l.length) : (l ++ [x])[i]? = l[i]? := by
  rw [List.getElem?_append]
  simp [h]

/-- Appending a colour keeps a good list good, provided no new monochromatic
triple is created. -/
theorem good_append {r : Nat} {l : List (Fin r)} {x : Fin r}
    (hl : Good l) (hx : extendOk l x = true) : Good (l ++ [x]) := by
  intro i j hi hj hij hcol
  have hij' : i + j + 1 ≤ l.length := by simp at hi hj hij; omega
  rcases Nat.lt_or_ge (i + j + 1) l.length with hlt | hge
  · have h1 : (l ++ [x])[i]? = l[i]? := getElem?_append_singleton_of_lt (by omega)
    have h2 : (l ++ [x])[j]? = l[j]? := getElem?_append_singleton_of_lt (by omega)
    have h3 : (l ++ [x])[i + j + 1]? = l[i + j + 1]? :=
      getElem?_append_singleton_of_lt hlt
    rw [h1, h2] at hcol
    rw [h1, h3]
    exact hl i j (by omega) (by omega) hlt hcol
  · have heq : i + j + 1 = l.length := by omega
    have hlast : (l ++ [x])[i + j + 1]? = some x := by
      rw [heq, List.getElem?_append]
      simp
    have hi'' : i < l.length := by omega
    have hj'' : j < l.length := by omega
    have hlt : j = l.length - 1 - i := by omega
    intro hcontra
    have happ_i : (l ++ [x])[i]? = some x := by rw [← hcontra]; exact hlast
    have hli := getElem?_append_singleton_of_lt (l := l) (x := x) hi''
    have hxi : l[i]? = some x := by rw [hli] at happ_i; exact happ_i
    have happ_j : (l ++ [x])[j]? = some x := by rw [← hcol]; exact happ_i
    have hlj := getElem?_append_singleton_of_lt (l := l) (x := x) hj''
    have hxj : l[j]? = some x := by rw [hlj] at happ_j; exact happ_j
    have hne := (extendOk_iff.mp hx) i hi'' hxi
    rw [hlt] at hxj
    exact hne hxj

/-- Restricting a good list to a prefix keeps it good. -/
theorem good_of_append {r : Nat} {l t : List (Fin r)} (h : Good (l ++ t)) : Good l := by
  intro i j hi hj hij hcol
  have hi' : i < (l ++ t).length := by simp; omega
  have hj' : j < (l ++ t).length := by simp; omega
  have hij' : i + j + 1 < (l ++ t).length := by simp; omega
  have h1 : (l ++ t)[i]? = l[i]? := by
    rw [List.getElem?_append]; simp [hi]
  have h2 : (l ++ t)[j]? = l[j]? := by
    rw [List.getElem?_append]; simp [hj]
  have h3 : (l ++ t)[i + j + 1]? = l[i + j + 1]? := by
    rw [List.getElem?_append]; simp [hij]
  have hcol' : (l ++ t)[i]? = (l ++ t)[j]? := by rw [h1, h2]; exact hcol
  have hne := h i j hi' hj' hij' hcol'
  rw [h3, h1] at hne
  exact hne

/-- If a good list can be extended by `x` followed by `t`, then `x` was a
permitted colour at position `l.length + 1`. -/
theorem extendOk_of_good_cons {r : Nat} {l t : List (Fin r)} {x : Fin r}
    (h : Good (l ++ (x :: t))) : extendOk l x = true := by
  rw [extendOk_iff]
  intro i hi hxi
  intro hxj
  have hlast : (l ++ (x :: t))[l.length]? = some x := by
    rw [List.getElem?_append]
    simp
  have h1 : (l ++ (x :: t))[i]? = l[i]? := by
    rw [List.getElem?_append]; simp [hi]
  have hj : l.length - 1 - i < l.length := by omega
  have h2 : (l ++ (x :: t))[l.length - 1 - i]? = l[l.length - 1 - i]? := by
    rw [List.getElem?_append]; simp [hj]
  have hsum : i + (l.length - 1 - i) + 1 = l.length := by omega
  have hcol : (l ++ (x :: t))[i]? = (l ++ (x :: t))[l.length - 1 - i]? := by
    rw [h1, h2, hxi, hxj]
  have hthird : (l ++ (x :: t))[i + (l.length - 1 - i) + 1]? = (l ++ (x :: t))[i]? := by
    rw [hsum, hlast, h1, hxi]
  have hlen : (l ++ (x :: t)).length = l.length + 1 + t.length := by
    rw [List.length_append, List.length_cons]; omega
  exact (h i (l.length - 1 - i) (by omega) (by omega) (by omega) hcol) hthird

/-- `search r n l`: can `l` be extended by `n` further colours to a good list? -/
def search (r : Nat) : (n : Nat) → List (Fin r) → Bool
  | 0, l => checkGood l
  | n + 1, l => (List.finRange r).any fun x => extendOk l x && search r n (l ++ [x])

/-- Specification of the search. -/
theorem search_spec {r : Nat} (n : Nat) (l : List (Fin r)) :
    search r n l = true ↔ ∃ t : List (Fin r), t.length = n ∧ Good (l ++ t) := by
  induction n generalizing l with
  | zero =>
      constructor
      · intro h
        exact ⟨[], rfl, by simpa using checkGood_sound h⟩
      · rintro ⟨t, ht, hg⟩
        cases t with
        | nil => simpa [search] using checkGood_complete (by simpa using hg)
        | cons y ys => simp at ht
  | succ n ih =>
      rw [search, List.any_eq_true]
      constructor
      · rintro ⟨x, _hxmem, hx⟩
        rw [Bool.and_eq_true] at hx
        obtain ⟨hxo, hxs⟩ := hx
        obtain ⟨t, ht, hg⟩ := (ih (l ++ [x])).mp hxs
        refine ⟨x :: t, by simp [ht], ?_⟩
        simpa [List.singleton_append, List.append_assoc] using hg
      · rintro ⟨t, ht, hg⟩
        cases t with
        | nil => simp at ht
        | cons x t' =>
            refine ⟨x, List.mem_finRange x, ?_⟩
            rw [Bool.and_eq_true]
            refine ⟨?_, ?_⟩
            · exact extendOk_of_good_cons (l := l) (t := t')
                (by simpa [List.singleton_append, List.append_assoc] using hg)
            · refine (ih (l ++ [x])).mpr ⟨t', by simpa using ht, ?_⟩
              simpa [List.singleton_append, List.append_assoc] using hg

/-! ## The two conventions, and the exact small values -/

/-- `Forcing r N`: every `r`-colouring of `{1, …, N}` contains a monochromatic
solution of `a + b = c`.  The least such `N` is the Schur number in the
"guaranteed solution" convention, `S'(r) = S(r) + 1`. -/
def Forcing (r N : Nat) : Prop := ¬ ∃ t : List (Fin r), t.length = N ∧ Good t

theorem forcing_iff_search {r N : Nat} : Forcing r N ↔ search r N [] = false := by
  have h := search_spec (r := r) N ([] : List (Fin r))
  simp only [List.nil_append] at h
  unfold Forcing
  by_cases hs : search r N [] = true
  · have hex : ∃ t : List (Fin r), t.length = N ∧ Good t := h.mp hs
    constructor
    · intro hf; exact absurd hex hf
    · intro hf; rw [hs] at hf; exact Bool.noConfusion hf
  · have hfalse : search r N [] = false := by
      cases hv : search r N [] <;> simp_all
    constructor
    · intro _; exact hfalse
    · intro _ hex; exact absurd (h.mpr hex) hs

/-- `Forcing` is monotone: a longer interval forces at least as much. -/
theorem forcing_mono {r N N' : Nat} (hNN' : N ≤ N') (h : Forcing r N) : Forcing r N' := by
  rintro ⟨t, ht, hg⟩
  refine h ⟨t.take N, ?_, ?_⟩
  · rw [List.length_take, ht]; omega
  · have hsplit : t.take N ++ t.drop N = t := List.take_append_drop N t
    exact good_of_append (l := t.take N) (t := t.drop N) (by rw [hsplit]; exact hg)

/-- `S(1) = 1`, i.e. `S'(1) = 2`: `{1}` can be 1-coloured, `{1,2}` cannot. -/
theorem one_color_exact :
    (∃ t : List (Fin 1), t.length = 1 ∧ Good t) ∧ Forcing 1 2 :=
  ⟨exists_one_coloring_1, forcing_iff_search.mpr (by native_decide)⟩

/-- `S(2) = 4`, i.e. `S'(2) = 5`. -/
theorem two_colors_exact :
    (∃ t : List (Fin 2), t.length = 4 ∧ Good t) ∧ Forcing 2 5 :=
  ⟨exists_two_coloring_4, forcing_iff_search.mpr (by native_decide)⟩

/-- `S(3) = 13`, i.e. `S'(3) = 14`. -/
theorem three_colors_exact :
    (∃ t : List (Fin 3), t.length = 13 ∧ Good t) ∧ Forcing 3 14 :=
  ⟨exists_three_coloring_13, forcing_iff_search.mpr (by native_decide)⟩

/-- `S(6) ≥ 536`, in the forcing convention: `536` is *not* a forcing number,
so the least forcing number is at least `537`. -/
theorem not_forcing_six_536 : ¬ Forcing 6 536 :=
  fun h => h exists_six_coloring_536

end Schur
