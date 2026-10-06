import RuleB

/-!
Branch `2` of the verified exhaustive search: below the prefix `[0, 1]`, the
third integer is coloured `2`.
-/

namespace Schur

theorem branchB2 : searchB 42 ([(0 : Fin 4), 1] ++ [(2 : Fin 4)]) = false := by
  native_decide

end Schur
