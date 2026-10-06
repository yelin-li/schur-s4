import S4

/-!
# The result in a more readable form

`Schur.lean` and `S4.lean` work with lists of colours, because that is what the
search manipulates.  A list of length `N` of elements of `Fin 4` *is* a
colouring of `{1, …, N}`: entry `i` is the colour of the integer `i + 1`.  This
file restates the result without the `Forcing` abbreviation, so that the
statement can be read off directly:

> `{1, …, 44}` has a 4-colouring with no monochromatic `x + y = z`,
> and `{1, …, 45}` has none.

(The companion formulation with colourings as functions `Fin N → Fin 4` is
discussed in `docs/RIGOR.md`; it is not needed for the proof, and the list
formulation is the one the search is specified against.)
-/

namespace Schur

/-- **`S(4) = 44`, stated with explicit lengths.** -/
theorem S4_statement :
    (∃ l : List (Fin 4), l.length = 44 ∧ Good l) ∧
      (∀ l : List (Fin 4), l.length = 45 → ¬ Good l) :=
  ⟨exists_four_coloring_44_kernel, fun l hl hg => no_good_four_45 ⟨l, hl, hg⟩⟩

/-- The same statement for every smaller length: truncating a good colouring
gives a good colouring, so `44` is the *largest* such length. -/
theorem S4_all_shorter :
    ∀ N, N ≤ 44 → ∃ l : List (Fin 4), l.length = N ∧ Good l := by
  obtain ⟨l, hl, hg⟩ := exists_four_coloring_44_kernel
  intro N hN
  refine ⟨l.take N, by simp [List.length_take, hl, hN], ?_⟩
  exact good_of_append (l := l.take N) (t := l.drop N)
    (by rw [List.take_append_drop]; exact hg)

end Schur
