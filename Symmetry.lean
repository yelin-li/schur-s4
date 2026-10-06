import Schur

/-!
# Symmetry breaking for the four-colour Schur problem

To prove that `{1, …, 45}` cannot be 4-coloured without a monochromatic
`a + b = c`, we want to avoid searching all `4^45` colourings.  Two independent
reductions are used, both purely combinatorial (no SAT solver):

* the colours of the first two integers differ (because `1 + 1 = 2`), so some
  relabelling of the four colours sends them to `0` and `1`.  This is a `12`-fold
  reduction, and it is justified below by *listing* twelve permutations and
  checking finitely that one of them always works.

All finite checks are performed inside Lean; the reduction theorem
`exists_good_first_two` is a proven statement about arbitrary lists, so the
final exhaustive search only has to consider colourings starting with `0, 1`.
-/

namespace Schur

/-! ## Relabelling invariance -/

/-- Computable injectivity test for maps `Fin 4 → Fin 4`. -/
def Inj4 (f : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all fun x => (List.finRange 4).all fun y =>
    if f x = f y then decide (x = y) else true

theorem inj4_sound {f : Fin 4 → Fin 4} (h : Inj4 f = true) : Function.Injective f := by
  intro x y hxy
  rw [Inj4, List.all_eq_true] at h
  have hx := h x (List.mem_finRange x)
  rw [List.all_eq_true] at hx
  have hy := hx y (List.mem_finRange y)
  rw [if_pos hxy] at hy
  exact of_decide_eq_true hy

/-- Relabelling the colours by an injective map preserves the sum-free property. -/
theorem good_map_iff {r : Nat} {f : Fin r → Fin r} (hf : Function.Injective f)
    (l : List (Fin r)) : Good (l.map f) ↔ Good l := by
  have hlen : (l.map f).length = l.length := List.length_map f
  constructor
  · intro h i j hi hj hij hcol
    have hcol' : (l.map f)[i]? = (l.map f)[j]? := by
      rw [List.getElem?_map, List.getElem?_map, hcol]
    have hne := h i j (by omega) (by omega) (by omega) hcol'
    intro hcontra
    exact hne (by rw [List.getElem?_map, List.getElem?_map, hcontra])
  · intro h i j hi hj hij hcol
    rw [List.getElem?_map, List.getElem?_map] at hcol
    have hcol2 : l[i]? = l[j]? := Option.map_injective hf hcol
    have hne := h i j (by omega) (by omega) (by omega) hcol2
    intro hcontra
    apply hne
    have hstep : (l.map f)[i + j + 1]? = (l.map f)[i]? := hcontra
    rw [List.getElem?_map, List.getElem?_map] at hstep
    exact Option.map_injective hf hstep

/-! ## Twelve permutations that cover all ordered pairs of distinct colours -/

/-- Twelve permutations of `Fin 4`.  Between them they send every ordered pair
of distinct colours to the pair `(0, 1)`, which is what the search needs. -/
def perms12 : List (Fin 4 → Fin 4) :=
  [ fun x => match x.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3,
    fun x => match x.val with | 0 => 0 | 1 => 2 | 2 => 1 | _ => 3,
    fun x => match x.val with | 0 => 0 | 1 => 2 | 2 => 3 | _ => 1,
    fun x => match x.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3,
    fun x => match x.val with | 0 => 2 | 1 => 0 | 2 => 1 | _ => 3,
    fun x => match x.val with | 0 => 2 | 1 => 0 | 2 => 3 | _ => 1,
    fun x => match x.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3,
    fun x => match x.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3,
    fun x => match x.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1,
    fun x => match x.val with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0,
    fun x => match x.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 0,
    fun x => match x.val with | 0 => 2 | 1 => 3 | 2 => 1 | _ => 0 ]

/-- Look for a permutation sending `a ↦ 0`, `b ↦ 1`; it is also required to be
injective, which is checked computationally. -/
def findPerm (a b : Fin 4) : Option (Fin 4 → Fin 4) :=
  perms12.find? fun π => decide (π a = 0) && decide (π b = 1) && Inj4 π

/-- Finite check (done by the kernel, no compiler trust): the lookup succeeds
for every ordered pair of distinct colours. -/
theorem lookup_ok :
    ((List.finRange 4).all fun a => (List.finRange 4).all fun b =>
      if a = b then true else (findPerm a b).isSome) = true := by
  decide

theorem findPerm_isSome {a b : Fin 4} (hab : a ≠ b) : (findPerm a b).isSome = true := by
  have h1 := List.all_eq_true.mp lookup_ok a (List.mem_finRange a)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_finRange b)
  rw [if_neg hab] at h2
  exact h2

theorem findPerm_spec {a b : Fin 4} {π : Fin 4 → Fin 4} (h : findPerm a b = some π) :
    π a = 0 ∧ π b = 1 ∧ Function.Injective π := by
  have hp := List.find?_some h
  rw [Bool.and_eq_true, Bool.and_eq_true] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, inj4_sound h3⟩

/-- **Symmetry breaking.**  Any good 4-colouring of `{1, …, n}` with `n ≥ 2` can
be relabelled so that its first two colours are `0` and `1`. -/
theorem exists_good_first_two {t : List (Fin 4)} (hg : Good t) (h2 : 2 ≤ t.length) :
    ∃ u : List (Fin 4), u.length = t.length ∧ Good u ∧
      u[0]? = some (0 : Fin 4) ∧ u[1]? = some (1 : Fin 4) := by
  obtain ⟨a, ha⟩ : ∃ a, t[0]? = some a := by
    cases ht : t[0]? with
    | none => rw [List.getElem?_eq_none_iff] at ht; omega
    | some a => exact ⟨a, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, t[1]? = some b := by
    cases ht : t[1]? with
    | none => rw [List.getElem?_eq_none_iff] at ht; omega
    | some b => exact ⟨b, rfl⟩
  have hab : a ≠ b := by
    intro heq
    have hne := hg 0 0 (by omega) (by omega) (by omega) (rfl : t[0]? = t[0]?)
    rw [ha, hb] at hne
    exact hne (by rw [heq])
  obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.mp (findPerm_isSome hab)
  obtain ⟨hπ0, hπ1, hπinj⟩ := findPerm_spec hπ
  refine ⟨t.map π, by simp, (good_map_iff hπinj t).mpr hg, ?_, ?_⟩
  · rw [List.getElem?_map, ha]; simp [hπ0]
  · rw [List.getElem?_map, hb]; simp [hπ1]

end Schur
