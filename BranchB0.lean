import RuleB

/-!
Branch `0` of the verified exhaustive search: below the prefix `[0, 1]`, the
third integer is coloured `0`.
-/

namespace Schur

theorem branchB0 : searchB 42 ([(0 : Fin 4), 1] ++ [(0 : Fin 4)]) = false := by
  native_decide

end Schur
