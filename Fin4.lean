import Std

/-!
# A basic fact about `Fin 4`

`Fin 4` has exactly four elements.  This is used by the search in `RuleB.lean`
to turn "some colour `x : Fin 4` is admissible" into the explicit four-way case
split `x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3`.
-/

namespace Schur

/-- Every element of `Fin 4` is one of `0, 1, 2, 3`. -/
theorem fin4_cases (x : Fin 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  match x with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr (Or.inl rfl))
  | ⟨3, _⟩ => exact Or.inr (Or.inr (Or.inr rfl))
  | ⟨n + 4, h⟩ => exact absurd h (by omega)

end Schur
