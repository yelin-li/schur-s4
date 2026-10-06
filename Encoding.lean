import CertificateS3
import CertCheckS3
import Schur

set_option maxRecDepth 1000000

/-!
# The structural `S(3)` encoding, and the completeness direction

`CertificateS3.lean` contains a *generated literal* CNF `Resolution.base3` (203
clauses) together with a resolution refutation of it, checked inside Lean by the
proved checker `Resolution.checkProof_sound`.  That gives

  `Resolution.cert3_unsat : ¬ ∃ a, ∀ c ∈ base3, Sat a c`

i.e. "this concrete list of clauses is unsatisfiable".

This file defines the same CNF *structurally*, as a function of the parameters,
and proves that every good 3-colouring of `{1, …, 14}` yields a satisfying
assignment.  Composing the two directions (`Forcing3Certified.lean`) turns the
certificate into `Schur.Forcing 3 14`.

## The encoding

A signed integer literal `l` (a Python `int`) becomes `(l.natAbs, 0 < l)`, so the
encoding of "integer `i` (1-based) has colour `c` (0-based)" is the
propositional variable

  `atom i c = (i - 1) * 3 + c + 1`     (a positive literal),

and its negation is `Lit.neg (atom i c)`.  This mirrors `bench/sat/cdcl45.py`
(`build_cnf_s3`), whose clauses are, in this order:

1. for each `i = 1..14`: the **ALO** clause `[x(i,0), x(i,1), x(i,2)]` followed by
   the **AMO** clauses `[¬x(i,c), ¬x(i,d)]` for `c < d` in `0..2`
   (`units` below, 14 * 4 = 56 clauses);
2. the **triples**: for `a = 1..13`, `b = a..14-a` and `c = 0..2` the clause
   `[¬x(a,c), ¬x(b,c), ¬x(a+b,c)]` (`triples` below, 21 * 7 = 147 clauses).

Finally every clause has repeated literals removed, order-preserving; this only
matters for the triples with `a = b`, where the literal `¬x(a,c)` occurs twice
and the clause shrinks to `[¬x(a,c), ¬x(a+b,c)]` (7 clauses).  The clause count is
`56 + 147 = 203`, matching `Resolution.base3`; the theorem `base3_eq` below checks
the agreement by computation (`#eval cnf3 == base3` evaluates to `true`).
-/

namespace Resolution

/-! ## Literals and clauses -/

/-- The propositional variable of "integer `i` (1-based) has colour `c` (0-based)",
matching `var(i, c) = (i - 1) * k + c + 1` in `bench/sat/cdcl45.py` with `k = 3`. -/
def atom (i c : Nat) : Lit := ((i - 1) * 3 + c + 1, true)

/-- The clause saying that the integer `i` has at least one colour. -/
def aloClause (i : Nat) : Clause := [atom i 0, atom i 1, atom i 2]

/-- The clause saying that the integer `i` does not have both colours `c` and `d`. -/
def amoClause (i c d : Nat) : Clause := [(atom i c).neg, (atom i d).neg]

/-- The clause excluding the monochromatic solution `a + b = a + b` in colour `c`. -/
def tripleClause (a b c : Nat) : Clause :=
  [(atom a c).neg, (atom b c).neg, (atom (a + b) c).neg]

/-- Remove repeated literals from a clause, preserving the order of first
occurrences.  (`List.contains` already ignores multiplicity, so this is the
same deduplication the Python encoder performs.) -/
def dedupClause : Clause → Clause
  | [] => []
  | a :: rest =>
      if (dedupClause rest).contains a then dedupClause rest else a :: dedupClause rest

/-- Remove repeated literals from every clause, preserving the clause order. -/
def dedup (cs : CNF) : CNF := cs.map dedupClause

/-! ## The structural encoding -/

/-- The AMO clauses of one integer (rows for `c = 0, 1, 2`, flattened). -/
def amoRow (i : Nat) : CNF :=
  List.flatten ((List.range 3).map (fun c => List.flatten ((List.range 3).map (fun d =>
    if c < d then [amoClause (i + 1) c d] else []))))

/-- The ALO clause of the integer `i + 1` followed by its AMO clauses. -/
def unitRow (i : Nat) : CNF := aloClause (i + 1) :: amoRow i

/-- **The "unit" clauses**, in the order used by the encoder: for `i = 0, …, 13`
the ALO clause of `i + 1` followed by its AMO clauses. -/
def units : CNF := List.flatten ((List.range 14).map (fun i => unitRow i))

/-- The triple clauses of one pair `(a, b)`, one per colour. -/
def tripleRow (a b : Nat) : CNF := (List.range 3).map (fun c => tripleClause a b c)

/-- **The triple clauses**: `a ≤ b`, `a + b ≤ 14`, one clause per colour. -/
def triples : CNF :=
  List.flatten ((List.range 15).map (fun a0 =>
    List.flatten ((List.range 16).map (fun b =>
      if a0 + 1 ≤ b ∧ b ≤ 14 - (a0 + 1) then tripleRow (a0 + 1) b else []))))

/-- The structural `S(3)` encoding: 3 colours on `{1, …, 14}` with no
monochromatic solution of `a + b = c`, deduplicated clause by clause. -/
def cnf3 : CNF := dedup (units ++ triples)

/-- **The structural encoding agrees with the solver's CNF.** -/
theorem base3_eq : Resolution.base3 = cnf3 := by native_decide

/-! ## Reading a colouring

Throughout, `t : List (Fin 3)` is a colouring: `t[i]` is the colour of the
integer `i + 1`, exactly as in `Schur.Good`. -/

/-- The colour of the integer `i + 1`; positions outside the list get colour `0`.
(The lemmas below only use it for `i < t.length`.) -/
def col (t : List (Fin 3)) (i : Nat) : Nat := (t[i]?).getD 0

/-- `col` is always a colour. -/
theorem col_lt (t : List (Fin 3)) (i : Nat) : col t i < 3 := by
  by_cases h : i < t.length
  · rw [col, List.getElem?_eq_getElem h]; exact (t[i]).isLt
  · have h' : t[i]? = none := List.getElem?_eq_none (by omega)
    rw [col, h']
    simp

theorem col_of_lt {t : List (Fin 3)} {i : Nat} (h : i < t.length) :
    col t i = (t[i]).val := by
  rw [col, List.getElem?_eq_getElem h]
  rfl

/-- Number of the variable belonging to "integer `i + 1` has colour `c`"
(`i` is the 0-based list index used by `Schur.Good`). -/
def apos (i c : Nat) : Nat := (i + 1 - 1) * 3 + c + 1

/-- `apos i c` as a plain arithmetic expression. -/
theorem apos_pos (i c : Nat) : apos i c = i * 3 + c + 1 := by
  rw [apos]
  have h : i + 1 - 1 = i := by omega
  rw [h]

/-- Integer division of the variable number by 3 recovers the index. -/
theorem apos_div (i c : Nat) (hc : c < 3) : (apos i c - 1) / 3 = i := by
  have h : apos i c - 1 = i * 3 + c := by
    rw [apos_pos]
    omega
  rw [h, show i * 3 + c = 3 * i + c from by omega]
  rw [Nat.mul_add_div (m := 3) (by omega) i c, Nat.div_eq_of_lt hc]
  omega

/-- The remainder modulo 3 is the colour. -/
theorem apos_mod (i c : Nat) (hc : c < 3) : (apos i c - 1) % 3 = c := by
  have h : apos i c - 1 = i * 3 + c := by
    rw [apos_pos]
    omega
  rw [h]
  exact Nat.mul_add_mod_of_lt (a := i) (b := 3) hc

/-- `apos i c` never exceeds the largest variable number. -/
theorem apos_le (t : List (Fin 3)) {i c : Nat} (hi : i < t.length) (hc : c < 3) :
    apos i c ≤ 3 * t.length := by
  have hc' : apos i c ≤ (i + 1) * 3 := by
    rw [apos_pos]
    omega
  have hi' : i + 1 ≤ t.length := by omega
  have hb : (i + 1) * 3 ≤ t.length * 3 := Nat.mul_le_mul_right 3 hi'
  have hb' : t.length * 3 = 3 * t.length := Nat.mul_comm _ _
  omega

/-- `atom (i+1) c` is `apos i c` with the positive sign. -/
theorem atom_succ (i c : Nat) : Resolution.atom (i + 1) c = (apos i c, true) := by
  have h : (i + 1 - 1) * 3 + c + 1 = i * 3 + c + 1 := by omega
  rw [atom, apos, h]

/-- **The assignment induced by a colouring.**  Variable `apos i c` is true
exactly when the integer `i + 1` has colour `c`.  The variable numbers are
`1, …, 3 * t.length`, so the guard is `v ≤ 3 * t.length`. -/
def mkAssign (t : List (Fin 3)) : Resolution.Assign := fun v =>
  if h : v ≤ 3 * t.length then decide (col t ((v - 1) / 3) = (v - 1) % 3) else false

/-- `evalLit` on `atom (j+1) x` is the corresponding variable of `mkAssign`. -/
theorem evalLit_atom_succ (t : List (Fin 3)) (j x : Nat) :
    evalLit (mkAssign t) (atom (j + 1) x) = mkAssign t (apos j x) := by
  rw [atom_succ]
  unfold evalLit
  simp

/-- Distinct colours of the same integer are distinct literals. -/
theorem atom_inj {i c d : Nat} (h : Resolution.atom i c = Resolution.atom i d) : c = d := by
  have h1 : (i - 1) * 3 + c + 1 = (i - 1) * 3 + d + 1 := congrArg Prod.fst h
  omega

/-- Decoding: the variable `apos i c` is true exactly when `i` has colour `c`. -/
theorem mkAssign_atom {t : List (Fin 3)} {i c : Nat} (hi : i < t.length) (hc : c < 3) :
    mkAssign t (apos i c) = decide (c = col t i) := by
  have hb : apos i c ≤ 3 * t.length := apos_le t hi hc
  have hdiv : (apos i c - 1) / 3 = i := apos_div i c hc
  have hmod : (apos i c - 1) % 3 = c := apos_mod i c hc
  rw [mkAssign, dif_pos hb, hdiv, hmod]
  exact decide_eq_decide.mpr (eq_comm)

/-! ## The assignment satisfies each family of clauses -/

/-- **ALO**: with `t[i]` as the colour of the integer `i + 1`, that integer has a
colour, so the ALO clause is satisfied. -/
theorem aloSat (t : List (Fin 3)) {i : Nat} (hi : i < t.length) :
    Sat (mkAssign t) (aloClause (i + 1)) := by
  have hc : col t i < 3 := col_lt t i
  have hmem : atom (i + 1) (col t i) ∈ aloClause (i + 1) := by
    rw [aloClause]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases Nat.lt_or_ge (col t i) 1 with h0 | h0
    · left
      have h0' : col t i = 0 := by omega
      rw [h0']
    · rcases Nat.lt_or_ge (col t i) 2 with h1 | h1
      · right; left
        have h1' : col t i = 1 := by omega
        rw [h1']
      · right; right
        have h2 : col t i = 2 := by omega
        rw [h2]
  refine ⟨atom (i + 1) (col t i), hmem, ?_⟩
  have h := mkAssign_atom (t := t) (i := i) (c := col t i) hi hc
  rw [evalLit_atom_succ, h]
  simp

/-- **AMO**: an integer never has two different colours. -/
theorem amoSat (t : List (Fin 3)) {i c d : Nat} (hi : i < t.length) (hc : c < 3) (hd : d < 3)
    (hcd : c < d) :
    Sat (mkAssign t) (amoClause (i + 1) c d) := by
  have hmem : (atom (i + 1) d).neg ∈ amoClause (i + 1) c d := by
    rw [amoClause]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hmem2 : (atom (i + 1) c).neg ∈ amoClause (i + 1) c d := by
    rw [amoClause]; exact List.mem_cons_self ..
  by_cases htrue : mkAssign t (apos i c) = true
  · -- `i + 1` has colour `c`, hence not colour `d`
    refine ⟨(atom (i + 1) d).neg, hmem, ?_⟩
    rw [evalLit_neg, evalLit_atom_succ]
    have hcol : col t i = c := by
      have hc' := mkAssign_atom (t := t) (i := i) (c := c) hi hc
      rw [hc'] at htrue
      exact (of_decide_eq_true htrue).symm
    have hd' : mkAssign t (apos i d) = false := by
      have h := mkAssign_atom (t := t) (i := i) (c := d) hi hd
      rw [h]
      have hne : ¬ (d = col t i) := by rw [hcol]; omega
      simp [hne]
    simp [hd']
  · have hfalse : mkAssign t (apos i c) = false := by
      cases hv : mkAssign t (apos i c) <;> simp_all
    refine ⟨(atom (i + 1) c).neg, hmem2, ?_⟩
    rw [evalLit_neg, evalLit_atom_succ]
    simp [hfalse]

/-- **Triples**: the integers `a`, `b` and `a + b` never all have the same
colour, because `Schur.Good` says exactly that no colour class contains `a`,
`b`, `a + b`.  This is the mathematical content of the encoding. -/
theorem tripleSat (t : List (Fin 3)) (hlen : t.length = 14) (hgood : Schur.Good t)
    {a b c : Nat} (ha1 : 1 ≤ a) (hab : a ≤ b) (hsum : a + b ≤ 14) (hc : c < 3) :
    Sat (mkAssign t) (tripleClause a b c) := by
  have ha : a - 1 < t.length := by omega
  have hb : b - 1 < t.length := by omega
  have hs : a + b - 1 < t.length := by omega
  have hm1 : (atom a c).neg ∈ tripleClause a b c := by
    rw [tripleClause]; exact List.mem_cons_self ..
  have hm2 : (atom b c).neg ∈ tripleClause a b c := by
    rw [tripleClause]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hm3 : (atom (a + b) c).neg ∈ tripleClause a b c := by
    rw [tripleClause]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  -- `Good` says: if `a` and `b` have the same colour `x`, then `a + b` does not
  have hthird : ∀ {x : Nat}, col t (a - 1) = x → col t (b - 1) = x →
      col t (a + b - 1) ≠ x := by
    intro x hx hx' hcon
    have hval : (t[a - 1]).val = (t[b - 1]).val := by
      rw [col_of_lt ha] at hx
      rw [col_of_lt hb] at hx'
      omega
    have hfe : t[a - 1] = t[b - 1] := Fin.ext hval
    have hne := hgood (a - 1) (b - 1) ha hb (by omega) (by
      rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, hfe])
    have hidx : a - 1 + (b - 1) + 1 = a + b - 1 := by omega
    rw [hidx] at hne
    have hcol : col t (a + b - 1) = col t (a - 1) := hcon.trans hx.symm
    have hopt : t[a + b - 1]? = t[a - 1]? := by
      rw [List.getElem?_eq_getElem hs, List.getElem?_eq_getElem ha]
      congr 1
      exact Fin.ext (by
        have h1 : (t[a + b - 1]).val = col t (a + b - 1) := (col_of_lt hs).symm
        have h2 : (t[a - 1]).val = col t (a - 1) := (col_of_lt ha).symm
        omega)
    exact hne hopt
  -- the negation of `atom (i+1) c` holds when `i + 1` does not have colour `c`
  have hneg : ∀ {i : Nat}, i < t.length → col t i ≠ c →
      evalLit (mkAssign t) (atom (i + 1) c).neg = true := by
    intro i hi hne
    rw [evalLit_neg]
    have hev : evalLit (mkAssign t) (atom (i + 1) c) = mkAssign t (apos i c) :=
      evalLit_atom_succ t i c
    rw [hev, mkAssign_atom (t := t) (i := i) (c := c) hi hc]
    by_cases hceq : c = col t i
    · exact absurd hceq.symm hne
    · simp [hceq]
  by_cases hca : col t (a - 1) = c
  · by_cases hcb : col t (b - 1) = c
    · exact ⟨(atom (a + b) c).neg, hm3, hneg hs (fun h => hthird hca hcb h)⟩
    · exact ⟨(atom b c).neg, hm2, hneg hb hcb⟩
  · exact ⟨(atom a c).neg, hm1, hneg ha hca⟩

/-! ## Membership in the structural encoding -/

/-- A clause of `unitRow i` is either the ALO clause of `i + 1` or one of its AMO
clauses. -/
theorem mem_unitRow {i : Nat} {cl : Clause} (h : cl ∈ unitRow i) :
    cl = aloClause (i + 1) ∨
      ∃ c d : Nat, c < 3 ∧ d < 3 ∧ c < d ∧ cl = amoClause (i + 1) c d := by
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · right
    obtain ⟨row, hrow, hcl⟩ := List.mem_flatten.mp h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨row2, hrow2, hcl2⟩ := List.mem_flatten.mp hcl
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hrow2
    have hc3 : c < 3 := List.mem_range.mp hc
    have hd3 : d < 3 := List.mem_range.mp hd
    by_cases hlt : c < d
    · rw [if_pos hlt] at hcl2
      refine ⟨c, d, hc3, hd3, hlt, ?_⟩
      simpa using hcl2
    · rw [if_neg hlt] at hcl2
      simp at hcl2

/-- A clause of `units` is an ALO or an AMO clause. -/
theorem mem_units {cl : Clause} (h : cl ∈ units) :
    (∃ i : Nat, i < 14 ∧ cl = aloClause (i + 1)) ∨
      ∃ i c d : Nat, i < 14 ∧ c < 3 ∧ d < 3 ∧ c < d ∧ cl = amoClause (i + 1) c d := by
  obtain ⟨row, hrow, hcl⟩ := List.mem_flatten.mp h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
  simp only [List.mem_range] at hi
  rcases mem_unitRow hcl with h | ⟨c, d, hc3, hd3, hcd, hcl⟩
  · exact Or.inl ⟨i, hi, h⟩
  · exact Or.inr ⟨i, c, d, hi, hc3, hd3, hcd, hcl⟩

/-- A clause of `triples` is a triple clause. -/
theorem mem_triples {cl : Clause} (h : cl ∈ triples) :
    ∃ a b c : Nat, 1 ≤ a ∧ a ≤ b ∧ a + b ≤ 14 ∧ c < 3 ∧ cl = tripleClause a b c := by
  obtain ⟨row, hrow, hcl⟩ := List.mem_flatten.mp h
  obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp hrow
  simp only [List.mem_range] at ha0
  obtain ⟨row2, hrow2, hcl2⟩ := List.mem_flatten.mp hcl
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hrow2
  simp only [List.mem_range] at hb
  by_cases hguard : a0 + 1 ≤ b ∧ b ≤ 14 - (a0 + 1)
  · rw [if_pos hguard] at hcl2
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcl2
    simp only [List.mem_range] at hc
    exact ⟨a0 + 1, b, c, by omega, hguard.1, by omega, hc, rfl⟩
  · rw [if_neg hguard] at hcl2
    simp at hcl2

/-! ## Deduplication preserves satisfaction -/

/-- Deduplication only deletes repeated literals: nothing new appears. -/
theorem mem_dedupClause_sub {cl : Clause} {l : Lit} (h : l ∈ dedupClause cl) : l ∈ cl := by
  induction cl with
  | nil => simp [dedupClause] at h
  | cons x xs ih =>
      simp only [dedupClause] at h
      split at h
      · exact List.mem_cons_of_mem _ (ih h)
      · rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h')

/-- Every literal of a clause survives deduplication (a later duplicate may be
the one that is kept, but at least one occurrence remains). -/
theorem mem_dedupClause_of_mem {cl : Clause} {l : Lit} (h : l ∈ cl) : l ∈ dedupClause cl := by
  induction cl with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      simp only [dedupClause]
      split
      · rename_i hc
        rcases List.mem_cons.mp h with rfl | h'
        · exact List.contains_iff_mem.mp hc
        · exact ih h'
      · rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h')

/-- Satisfaction is preserved by deduplication. -/
theorem dedup_sat {a : Resolution.Assign} {cs : CNF}
    (h : ∀ c ∈ cs, Sat a c) : ∀ c ∈ dedup cs, Sat a c := by
  intro c hc
  rw [dedup, List.mem_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := hc
  obtain ⟨l, hl, hlt⟩ := h c0 hc0
  exact ⟨l, mem_dedupClause_of_mem hl, hlt⟩

/-! ## Completeness -/

/-- **Completeness of the `S(3)` encoding.**  Every good 3-colouring of
`{1, …, 14}` induces a satisfying assignment of the structural CNF `cnf3`. -/
theorem sat_of_good (t : List (Fin 3)) (hlen : t.length = 14) (hgood : Schur.Good t) :
    ∃ a : Resolution.Assign, ∀ c ∈ cnf3, Resolution.Sat a c := by
  refine ⟨mkAssign t, dedup_sat ?_⟩
  intro cl hcl
  rcases List.mem_append.mp hcl with h | h
  · rcases mem_units h with ⟨i, hi, rfl⟩ | ⟨i, c, d, hi, hc3, hd3, hcd, rfl⟩
    · exact aloSat t (i := i) (by rw [hlen]; exact hi)
    · exact amoSat t (i := i) (c := c) (d := d) (by rw [hlen]; exact hi) hc3 hd3 hcd
  · obtain ⟨a, b, c, ha1, hab, hsum, hc, rfl⟩ := mem_triples h
    exact tripleSat t hlen hgood ha1 hab hsum hc

/-! ## The mathematical conclusion -/

/-- The certificate's unsatisfiability statement, transported to the structural
encoding. -/
theorem cnf3_unsat : ¬ ∃ a : Resolution.Assign, ∀ c ∈ cnf3, Resolution.Sat a c := by
  intro h
  refine _root_.cert3_unsat ?_
  rw [base3_eq]
  exact h

/-- **`S(3) = 13`, from the certificate.**  No 3-colouring of `{1, …, 14}`
avoids a monochromatic solution of `a + b = c`.

The only non-kernel ingredients are the evaluation of the proved checker on the
generated certificate (`Resolution.cert3_checks`, checked by `native_decide`)
and the agreement `base3_eq` between the generated CNF and the structural
definition above. -/
theorem forcing_three_certified : Schur.Forcing 3 14 := by
  rintro ⟨t, hlen, hgood⟩
  exact cnf3_unsat (sat_of_good t hlen hgood)

#print axioms forcing_three_certified
#print axioms cnf3_unsat

end Resolution
