import Std

/-!
# A verified resolution checker

A certificate checker for propositional refutations, with a proof that it is
sound: if the checker accepts a certificate, the CNF is unsatisfiable.

Certificates in this format are produced by `bench/sat/expand_resolution.py`,
which turns the RUP proof emitted by the from-scratch CDCL solver
`bench/sat/cdcl45.py` into an explicit resolution derivation.  Nothing about the
solver is trusted: every step is checked here, and only two inference rules are
allowed.

* `input`   — the clause is one of the base clauses;
* `resolve` — the clause is the resolvent of two earlier clauses on a variable;
* `weaken`  — the clause is a superset of an earlier clause.

Resolution and weakening preserve satisfiability, which is all the soundness
proof needs; the last derived clause must be empty.
-/

namespace Resolution

/-- A literal: variable and sign (`true` = positive). -/
abbrev Lit := Nat × Bool

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assign := Nat → Bool

/-- The negation of a literal. -/
def Lit.neg (l : Lit) : Lit := (l.1, !l.2)

/-- Truth value of a literal under an assignment. -/
def evalLit (a : Assign) (l : Lit) : Bool := if l.2 then a l.1 else !(a l.1)

@[simp] theorem evalLit_neg (a : Assign) (l : Lit) : evalLit a l.neg = !(evalLit a l) := by
  unfold evalLit Lit.neg
  cases l.2 <;> simp

/-- The assignment satisfies the clause. -/
def Sat (a : Assign) (c : Clause) : Prop := ∃ l ∈ c, evalLit a l = true

/-- `Entails base c`: every assignment satisfying `base` satisfies `c`. -/
def Entails (base : CNF) (c : Clause) : Prop :=
  ∀ a : Assign, (∀ d ∈ base, Sat a d) → Sat a c

/-! ## The checker -/

/-- All literals of `a` occur in `b`. -/
def Subset (a b : Clause) : Bool := a.all (fun l => decide (l ∈ b))

/-- `a` and `b` have the same literals (multiplicities ignored). -/
def SameSet (a b : Clause) : Bool := Subset a b && Subset b a

/-- The resolvent of `c1` and `c2` on the variable `v`. -/
def resolventOf (c1 c2 : Clause) (v : Nat) : Clause :=
  c1.filter (fun l => l != (v, true)) ++ c2.filter (fun l => l != (v, false))

/-- How a clause is justified in a certificate. -/
inductive Justify where
  | input
  | resolve (i j v : Nat)
  | weaken (i : Nat)

/-- Check one step against the database `db` (base clauses first). -/
def checkOne (base db : CNF) (C : Clause) : Justify → Bool
  | .input => decide (C ∈ base)
  | .resolve i j v =>
      match db[i]?, db[j]? with
      | some c1, some c2 =>
          decide ((v, true) ∈ c1) && decide ((v, false) ∈ c2) &&
            SameSet C (resolventOf c1 c2 v)
      | _, _ => false
  | .weaken i =>
      match db[i]? with
      | some c => Subset c C
      | none => false

/-- Check a whole derivation; the last clause must be empty. -/
def checkGo (base : CNF) : CNF → List (Clause × Justify) → Bool
  | _, [] => false
  | db, [(C, j)] => checkOne base db C j && C.isEmpty
  | db, (C, j) :: rest => checkOne base db C j && checkGo base (db ++ [C]) rest

/-- A certificate: base clauses and a derivation. -/
structure Cert where
  base : CNF
  steps : List (Clause × Justify)

def checkProof (cert : Cert) : Bool := checkGo cert.base cert.base cert.steps

/-! ## Soundness -/

theorem subset_mem {a b : Clause} {l : Lit} (h : Subset a b = true) (hl : l ∈ a) : l ∈ b := by
  have := List.all_eq_true.mp h l hl
  simpa using this

theorem sameSet_mem {a b : Clause} {l : Lit} (h : SameSet a b = true) (hl : l ∈ a) : l ∈ b := by
  have h' : Subset a b = true := by
    have := h
    rw [SameSet, Bool.and_eq_true] at this
    exact this.1
  exact subset_mem h' hl

theorem sameSet_mem' {a b : Clause} {l : Lit} (h : SameSet a b = true) (hl : l ∈ b) : l ∈ a := by
  have h' : Subset b a = true := by
    have := h
    rw [SameSet, Bool.and_eq_true] at this
    exact this.2
  exact subset_mem h' hl

theorem subset_sound {base : CNF} {a b : Clause} (ha : Entails base a)
    (h : Subset a b = true) : Entails base b := by
  intro x hx
  obtain ⟨l, hl, hlt⟩ := ha x hx
  exact ⟨l, subset_mem h hl, hlt⟩

/-- Membership in the resolvent of two clauses. -/
theorem mem_resolventOf {c1 c2 : Clause} {v : Nat} {l : Lit} :
    l ∈ resolventOf c1 c2 v ↔
      (l ∈ c1 ∧ l ≠ (v, true)) ∨ (l ∈ c2 ∧ l ≠ (v, false)) := by
  unfold resolventOf
  rw [List.mem_append, List.mem_filter, List.mem_filter]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, by simpa using h2⟩
    · exact Or.inr ⟨h1, by simpa using h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, by simp [h2]⟩
    · exact Or.inr ⟨h1, by simp [h2]⟩

/-- Resolution preserves satisfaction. -/
theorem sat_resolvent {a : Assign} {c1 c2 r : Clause} {v : Nat}
    (h1 : Sat a c1) (h2 : Sat a c2)
    (_hv1 : (v, true) ∈ c1) (_hv2 : (v, false) ∈ c2)
    (hr : SameSet r (resolventOf c1 c2 v) = true) : Sat a r := by
  obtain ⟨l, hl, hlt⟩ := h1
  by_cases hlpos : l = (v, true)
  · -- `l` is the pivot: use the witness of the second clause
    subst hlpos
    obtain ⟨k, hk, hkt⟩ := h2
    have hkne : k ≠ (v, false) := by
      intro hkf
      subst hkf
      have : (v, false) = Lit.neg (v, true) := rfl
      rw [this, evalLit_neg] at hkt
      rw [hlt] at hkt
      exact Bool.noConfusion hkt
    exact ⟨k, sameSet_mem' hr (mem_resolventOf.mpr (Or.inr ⟨hk, hkne⟩)), hkt⟩
  · exact ⟨l, sameSet_mem' hr (mem_resolventOf.mpr (Or.inl ⟨hl, hlpos⟩)), hlt⟩

/-- A resolution step is entailed by its parents (needs both parents to be
double-negation free, i.e. variables are compared literally). -/
theorem resolve_sound {base : CNF} {c1 c2 r : Clause} {v : Nat}
    (h1 : Entails base c1) (h2 : Entails base c2)
    (hv1 : (v, true) ∈ c1) (hv2 : (v, false) ∈ c2)
    (hr : SameSet r (resolventOf c1 c2 v) = true) : Entails base r := by
  intro a ha
  exact sat_resolvent (h1 a ha) (h2 a ha) hv1 hv2 hr

/-- One step preserves the invariant "every clause of the database is entailed
by the base". -/
theorem checkOne_sound {base db : CNF} {C : Clause} {j : Justify}
    (hdb : ∀ c ∈ db, Entails base c) (h : checkOne base db C j = true) :
    Entails base C := by
  unfold checkOne at h
  split at h
  · exact fun a ha => ha C (of_decide_eq_true h)
  · split at h
    · rename_i c1 c2 h1 h2
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      obtain ⟨⟨hv1, hv2⟩, hr⟩ := h
      have hc1 : c1 ∈ db := List.mem_iff_getElem?.mpr ⟨_, h1⟩
      have hc2 : c2 ∈ db := List.mem_iff_getElem?.mpr ⟨_, h2⟩
      exact resolve_sound (hdb c1 hc1) (hdb c2 hc2) (of_decide_eq_true hv1)
        (of_decide_eq_true hv2) hr
    · exact Bool.noConfusion h
  · split at h
    · rename_i c hc
      have hcm : c ∈ db := List.mem_iff_getElem?.mpr ⟨_, hc⟩
      exact subset_sound (hdb c hcm) h
    · exact Bool.noConfusion h

theorem entails_nil_unsat {base : CNF} (h : Entails base []) :
    ¬ ∃ a : Assign, ∀ c ∈ base, Sat a c := by
  rintro ⟨a, ha⟩
  have := h a ha
  simpa [Sat] using this

/-- **Soundness of the checker.** -/
theorem checkGo_sound {base : CNF} :
    ∀ (db : CNF) (steps : List (Clause × Justify)),
      (∀ c ∈ db, Entails base c) → checkGo base db steps = true →
      ¬ ∃ a : Assign, ∀ c ∈ base, Sat a c := by
  intro db steps
  induction steps generalizing db with
  | nil => intro _ h; exact Bool.noConfusion h
  | cons step rest ih =>
      obtain ⟨C, j⟩ := step
      intro hdb h
      cases rest with
      | nil =>
          simp only [checkGo] at h
          rw [Bool.and_eq_true] at h
          obtain ⟨hstep, hempty⟩ := h
          rw [List.isEmpty_iff] at hempty
          have hC : Entails base C := checkOne_sound hdb hstep
          rw [hempty] at hC
          exact entails_nil_unsat hC
      | cons step2 rest2 =>
          simp only [checkGo] at h
          rw [Bool.and_eq_true] at h
          obtain ⟨hstep, hrest⟩ := h
          exact ih (db ++ [C]) (by
            intro c hc
            rcases List.mem_append.mp hc with hin | hin
            · exact hdb c hin
            · have : c = C := by simpa using hin
              subst this
              exact checkOne_sound hdb hstep) hrest

/-- **Soundness of the checker.** -/
theorem checkCert_sound {base : CNF} {steps : List (Clause × Justify)}
    (h : checkGo base base steps = true) :
    ¬ ∃ a : Assign, ∀ c ∈ base, Sat a c :=
  checkGo_sound base steps (by intro c hc a ha; exact ha c hc) h

theorem checkProof_sound {cert : Cert} (h : checkProof cert = true) :
    ¬ ∃ a : Assign, ∀ c ∈ cert.base, Sat a c :=
  checkCert_sound (base := cert.base) (steps := cert.steps) h

end Resolution
