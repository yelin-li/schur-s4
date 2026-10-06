import RuleB

/-!
Branch `1` of the verified exhaustive search: below the prefix `[0, 1]`, the
third integer is coloured `1`.
-/

namespace Schur

theorem branchB1 : searchB 42 ([(0 : Fin 4), 1] ++ [(1 : Fin 4)]) = false := by
  native_decide

end Schur
