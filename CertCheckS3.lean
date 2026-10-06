import CertificateS3

/-! The certificate for the `S(3)` instance is checked *inside Lean* by the
proved checker `Resolution.checkProof_sound`. -/

open Resolution

/-- The generated certificate is accepted by the verified checker. -/
theorem cert3_checks : Resolution.checkProof Resolution.cert3 = true := by
  native_decide

/-- Consequently the (generated) base CNF is unsatisfiable — a statement whose
only non-kernel ingredient is the evaluation of the checker, via
`Resolution.checkProof_sound`. -/
theorem cert3_unsat : ¬ ∃ a : Resolution.Assign, ∀ c ∈ Resolution.base3, Resolution.Sat a c :=
  Resolution.checkProof_sound cert3_checks

#print axioms cert3_unsat
