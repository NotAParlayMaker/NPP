import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_103_aux

open PEqualNP.ProofComplexity MvPolynomial

private def eN {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  match x with
  | 0 => k 0
  | n + 1 => k (n + 1)

private lemma eN_eq {α : Type} (x : ℕ) (k : ℕ → α) : eN x k = k x := by
  cases x <;> rfl

private lemma nat_land_63 (n : ℕ) : Nat.land n 63 = n % 64 :=
  Nat.and_two_pow_sub_one_eq_mod n 6

private lemma nat_shr (n k : ℕ) : Nat.shiftRight n k = n / 2 ^ k :=
  Nat.shiftRight_eq_div_pow n k

private lemma nat_testBit_xor (a b i : ℕ) :
    (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) :=
  Nat.testBit_xor a b i

private lemma nat_beq_eq_false {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := by
  intro heq; subst heq; simp at h

private lemma totalDegree_prod_le {ι V : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial V (ZMod 2)) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.sum_insert hat]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

-- =========================================================================
-- Section 1: Concrete formulas and variable encodings
-- =========================================================================

private def petEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
   (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

private def k44Edges : List (Fin 8 × Fin 8) :=
  [(0, 4), (0, 5), (0, 6), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7),
   (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7)]

private def FpSet : Set (Clause (Fin 10 ⊕ (ℕ × ℕ))) :=
  {Cep | ∃ eep ∈ petEdges, Cep = {((Sum.inl eep.1 : Fin 10 ⊕ (ℕ × ℕ)), true), ((Sum.inl eep.2 : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪
  {Cap | ∃ iap : Fin 10, iap.val + 1 < 10 ∧ Cap = {((Sum.inl iap : Fin 10 ⊕ (ℕ × ℕ)), false), ((Sum.inr (iap.val, 0) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪
  {Cbp | ∃ (ibp : Fin 10) (hbp jbp : ℕ), ibp.val = hbp + 1 ∧ ibp.val + 1 < 10 ∧ jbp < 5 ∧ Cbp = {((Sum.inr (hbp, jbp) : Fin 10 ⊕ (ℕ × ℕ)), false), ((Sum.inr (ibp.val, jbp) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪
  {Ccp | ∃ (icp : Fin 10) (hcp gcp : ℕ), icp.val = hcp + 1 ∧ icp.val + 1 < 10 ∧ gcp + 1 < 5 ∧ Ccp = {((Sum.inl icp : Fin 10 ⊕ (ℕ × ℕ)), false), ((Sum.inr (hcp, gcp) : Fin 10 ⊕ (ℕ × ℕ)), false), ((Sum.inr (icp.val, gcp + 1) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪
  {Cdp | ∃ (idp : Fin 10) (hdp : ℕ), idp.val = hdp + 1 ∧ Cdp = {((Sum.inl idp : Fin 10 ⊕ (ℕ × ℕ)), false), ((Sum.inr (hdp, 4) : Fin 10 ⊕ (ℕ × ℕ)), false)}} ∪
  {Cfp | ∃ jfp : ℕ, 1 ≤ jfp ∧ jfp < 5 ∧ Cfp = {((Sum.inr (0, jfp) : Fin 10 ⊕ (ℕ × ℕ)), false)}}

private def FkSet : Set (Clause (Fin 8 ⊕ (ℕ × ℕ))) :=
  {Cek | ∃ eek ∈ k44Edges, Cek = {((Sum.inl eek.1 : Fin 8 ⊕ (ℕ × ℕ)), true), ((Sum.inl eek.2 : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪
  {Cak | ∃ iak : Fin 8, iak.val + 1 < 8 ∧ Cak = {((Sum.inl iak : Fin 8 ⊕ (ℕ × ℕ)), false), ((Sum.inr (iak.val, 0) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪
  {Cbk | ∃ (ibk : Fin 8) (hbk jbk : ℕ), ibk.val = hbk + 1 ∧ ibk.val + 1 < 8 ∧ jbk < 3 ∧ Cbk = {((Sum.inr (hbk, jbk) : Fin 8 ⊕ (ℕ × ℕ)), false), ((Sum.inr (ibk.val, jbk) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪
  {Cck | ∃ (ick : Fin 8) (hck gck : ℕ), ick.val = hck + 1 ∧ ick.val + 1 < 8 ∧ gck + 1 < 3 ∧ Cck = {((Sum.inl ick : Fin 8 ⊕ (ℕ × ℕ)), false), ((Sum.inr (hck, gck) : Fin 8 ⊕ (ℕ × ℕ)), false), ((Sum.inr (ick.val, gck + 1) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪
  {Cdk | ∃ (idk : Fin 8) (hdk : ℕ), idk.val = hdk + 1 ∧ Cdk = {((Sum.inl idk : Fin 8 ⊕ (ℕ × ℕ)), false), ((Sum.inr (hdk, 2) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪
  {Cfk | ∃ jfk : ℕ, 1 ≤ jfk ∧ jfk < 3 ∧ Cfk = {((Sum.inr (0, jfk) : Fin 8 ⊕ (ℕ × ℕ)), false)}}

private def pVar (v : ℕ) : Fin 10 ⊕ (ℕ × ℕ) :=
  if h : v < 10 then Sum.inl ⟨v, h⟩ else Sum.inr ((v - 10) / 5, (v - 10) % 5)

private def kVar (v : ℕ) : Fin 8 ⊕ (ℕ × ℕ) :=
  if h : v < 8 then Sum.inl ⟨v, h⟩ else Sum.inr ((v - 8) / 3, (v - 8) % 3)

private lemma pVar_inj_lt : ∀ a b : ℕ, a < 55 → b < 55 → pVar a = pVar b → a = b := by
  intro a b ha hb h
  unfold pVar at h
  split_ifs at h with h1 h2 h2
  · simp only [Sum.inl.injEq, Fin.mk.injEq] at h; exact h
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; omega

private lemma kVar_inj_lt : ∀ a b : ℕ, a < 29 → b < 29 → kVar a = kVar b → a = b := by
  intro a b ha hb h
  unfold kVar at h
  split_ifs at h with h1 h2 h2
  · simp only [Sum.inl.injEq, Fin.mk.injEq] at h; exact h
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; omega

private def kVarInv : Fin 8 ⊕ (ℕ × ℕ) → Option (Fin 29)
  | Sum.inl i => some ⟨i.val, by omega⟩
  | Sum.inr (i, j) => if h : i < 7 ∧ j < 3 then some ⟨8 + 3 * i + j, by omega⟩ else none

private lemma kVarInv_kVar (i : Fin 29) : kVarInv (kVar i.val) = some i := by
  fin_cases i <;> decide

-- =========================================================================
-- Section 2: Width-2 resolution lower bounds (P2, K2) & PC-2 lower bound (P4)
-- =========================================================================

private def assign2 {n : ℕ} : Fin n ⊕ (ℕ × ℕ) → Bool
  | Sum.inl _ => true
  | Sum.inr (_, j) => decide (j = 0)

private lemma clauseSat_resolvent {V : Type} [DecidableEq V] {a : V → Bool}
    {C D R : Clause V} (hC : ClauseSat a C) (hD : ClauseSat a D) (hR : IsResolvent C D R) :
    ClauseSat a R := by
  rcases hR with ⟨v, _, _, rfl⟩
  cases hv : a v
  · rcases hC with ⟨l, hlC, hla⟩
    refine ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hlC⟩), hla⟩
    rintro rfl; simp [hv] at hla
  · rcases hD with ⟨l, hlD, hla⟩
    refine ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hlD⟩), hla⟩
    rintro rfl; simp [hv] at hla

private lemma no_width2_of_sat {V : Type} [DecidableEq V] {F : Set (Clause V)} (a : V → Bool)
    (hsat : ∀ C ∈ F, C.card ≤ 2 → ClauseSat a C) :
    ¬ ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ 2 := by
  rintro ⟨π, ⟨hder, hemp⟩, hw⟩
  have hall : ∀ π', IsDerivation F π' → (∀ D ∈ π', D.card ≤ 2) → ∀ D ∈ π', ClauseSat a D := by
    intro π' hder'
    induction hder' with
    | nil => intro _ D hD; simp at hD
    | ax _ hC ih =>
      intro hw' D hD
      rcases List.mem_cons.mp hD with rfl | hD'
      · exact hsat D hC (hw' D List.mem_cons_self)
      · exact ih (fun E hE => hw' E (List.mem_cons_of_mem _ hE)) D hD'
    | res _ hC hD hR ih =>
      intro hw' E hE
      have ih' := ih (fun X hX => hw' X (List.mem_cons_of_mem _ hX))
      rcases List.mem_cons.mp hE with rfl | hE'
      · exact clauseSat_resolvent (ih' _ hC) (ih' _ hD) hR
      · exact ih' E hE'
  rcases hall π hder hw ∅ hemp with ⟨l, hl, _⟩
  exact Finset.notMem_empty l hl

private lemma card_three_triple {α : Type} [DecidableEq α] {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : ({x, y, z} : Finset α).card = 3 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [hyz]
  · simp [hxy, hxz]

private lemma assign2_sat_Fp : ∀ C ∈ FpSet, C.card ≤ 2 → ClauseSat assign2 C := by
  intro C hC hcard
  rcases hC with (((((h | h) | h) | h) | h) | h)
  · rcases h with ⟨e, _, rfl⟩
    exact ⟨(Sum.inl e.1, true), by simp, rfl⟩
  · rcases h with ⟨i, _, rfl⟩
    exact ⟨(Sum.inr (i.val, 0), true), by simp, rfl⟩
  · rcases h with ⟨i, hi, j, _, _, _, rfl⟩
    by_cases hj : j = 0
    · subst hj; exact ⟨(Sum.inr (i.val, 0), true), by simp, rfl⟩
    · exact ⟨(Sum.inr (hi, j), false), by simp, by simp [assign2, hj]⟩
  · rcases h with ⟨i, hi, g, _, _, _, rfl⟩
    have hc : ({((Sum.inl i : Fin 10 ⊕ (ℕ × ℕ)), false),
        ((Sum.inr (hi, g) : Fin 10 ⊕ (ℕ × ℕ)), false),
        ((Sum.inr (i.val, g + 1) : Fin 10 ⊕ (ℕ × ℕ)), true)} : Clause (Fin 10 ⊕ (ℕ × ℕ))).card = 3 :=
      card_three_triple (by simp) (by simp) (by simp)
    omega
  · rcases h with ⟨i, hi, _, rfl⟩
    exact ⟨(Sum.inr (hi, 4), false), by simp, rfl⟩
  · rcases h with ⟨j, hj1, _, rfl⟩
    have hj0 : j ≠ 0 := by omega
    exact ⟨(Sum.inr (0, j), false), by simp, by simp [assign2, hj0]⟩

private lemma assign2_sat_Fk : ∀ C ∈ FkSet, C.card ≤ 2 → ClauseSat assign2 C := by
  intro C hC hcard
  rcases hC with (((((h | h) | h) | h) | h) | h)
  · rcases h with ⟨e, _, rfl⟩
    exact ⟨(Sum.inl e.1, true), by simp, rfl⟩
  · rcases h with ⟨i, _, rfl⟩
    exact ⟨(Sum.inr (i.val, 0), true), by simp, rfl⟩
  · rcases h with ⟨i, hi, j, _, _, _, rfl⟩
    by_cases hj : j = 0
    · subst hj; exact ⟨(Sum.inr (i.val, 0), true), by simp, rfl⟩
    · exact ⟨(Sum.inr (hi, j), false), by simp, by simp [assign2, hj]⟩
  · rcases h with ⟨i, hi, g, _, _, _, rfl⟩
    have hc : ({((Sum.inl i : Fin 8 ⊕ (ℕ × ℕ)), false),
        ((Sum.inr (hi, g) : Fin 8 ⊕ (ℕ × ℕ)), false),
        ((Sum.inr (i.val, g + 1) : Fin 8 ⊕ (ℕ × ℕ)), true)} : Clause (Fin 8 ⊕ (ℕ × ℕ))).card = 3 :=
      card_three_triple (by simp) (by simp) (by simp)
    omega
  · rcases h with ⟨i, hi, _, rfl⟩
    exact ⟨(Sum.inr (hi, 2), false), by simp, rfl⟩
  · rcases h with ⟨j, hj1, _, rfl⟩
    have hj0 : j ≠ 0 := by omega
    exact ⟨(Sum.inr (0, j), false), by simp, by simp [assign2, hj0]⟩

private lemma P2_no_width2 : ¬ ∃ π, IsRefutation FpSet π ∧ ∀ D ∈ π, D.card ≤ 2 :=
  no_width2_of_sat assign2 assign2_sat_Fp

private lemma K2_no_width2 : ¬ ∃ π, IsRefutation FkSet π ∧ ∀ D ∈ π, D.card ≤ 2 :=
  no_width2_of_sat assign2 assign2_sat_Fk

private lemma zmod2_sq (x : ZMod 2) : x * x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_poly_add_self {V : Type} (p : MvPolynomial V (ZMod 2)) : p + p = 0 := by
  ext m; simp [zmod2_add_self]

private lemma clausePoly_eval_zero_of_sat {V : Type} [DecidableEq V] {a : V → Bool}
    {C : Clause V} (hsat : ClauseSat a C) :
    MvPolynomial.eval (fun v => if a v then (1 : ZMod 2) else 0) (clausePoly C) = 0 := by
  rcases hsat with ⟨l, hl, ha⟩
  unfold clausePoly
  rw [map_prod]
  apply Finset.prod_eq_zero hl
  cases hl2 : l.2
  · rw [hl2] at ha; simp [ha]
  · rw [hl2] at ha; simp [ha]; decide

private lemma deg3_triple_not_le_2 {V : Type} [DecidableEq V] {v1 v2 v3 : V}
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    ¬ (clausePoly ({(v1, false), (v2, false), (v3, true)} : Clause V)).totalDegree ≤ 2 := by
  have hpoly : clausePoly ({(v1, false), (v2, false), (v3, true)} : Clause V) =
      monomial (Finsupp.single v1 1 + Finsupp.single v2 1) (1 : ZMod 2) +
      monomial (Finsupp.single v1 1 + Finsupp.single v2 1 + Finsupp.single v3 1) (1 : ZMod 2) := by
    unfold clausePoly
    rw [Finset.prod_insert (by simp [h12, h13]), Finset.prod_insert (by simp [h23]), Finset.prod_singleton]
    simp only [Bool.false_eq_true, ↓reduceIte, mul_add, mul_one, ← mul_assoc]
    simp only [MvPolynomial.X, monomial_mul_monomial, one_mul]
  rw [hpoly]
  set d : V →₀ ℕ := Finsupp.single v1 1 + Finsupp.single v2 1 + Finsupp.single v3 1
  have hne : Finsupp.single v1 1 + Finsupp.single v2 1 ≠ d := by
    intro heq
    have hval := congrArg (fun f => f v3) heq
    simp [d, h13, h23] at hval
  have hcoeff : (monomial (Finsupp.single v1 1 + Finsupp.single v2 1) (1 : ZMod 2) +
      monomial d (1 : ZMod 2)).coeff d = 1 := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial, coeff_monomial, if_neg hne, if_pos rfl, zero_add]
  have hdsum : d.sum (fun _ k => k) = 3 := by
    simp only [d]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  have hle : 3 ≤ (monomial (Finsupp.single v1 1 + Finsupp.single v2 1) (1 : ZMod 2) +
      monomial d (1 : ZMod 2)).totalDegree := by
    rw [← hdsum]
    exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr (by rw [hcoeff]; decide))
  omega

private lemma P4_no_pc2 : ¬ PCRefutable (cnfSystem FpSet) 2 := by
  intro href
  let val : Fin 10 ⊕ (ℕ × ℕ) → ZMod 2 := fun v => if assign2 v then 1 else 0
  have heval : ∀ p, PCDerivable (cnfSystem FpSet) 2 p → MvPolynomial.eval val p = 0 := by
    intro p hp
    induction hp with
    | zero => simp
    | add _ _ ih1 ih2 => simp [ih1, ih2]
    | mulX j _ _ ih => simp [ih]
    | ax hmem hdeg =>
      rcases hmem with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
      · simp [zmod2_sq]
      · rcases hC with (((((h | h) | h) | h) | h) | h)
        · exact clausePoly_eval_zero_of_sat (assign2_sat_Fp C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))) (by rcases h with ⟨e, _, rfl⟩; exact Finset.card_le_two))
        · exact clausePoly_eval_zero_of_sat (assign2_sat_Fp C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))) (by rcases h with ⟨i, _, rfl⟩; exact Finset.card_le_two))
        · exact clausePoly_eval_zero_of_sat (assign2_sat_Fp C (Or.inl (Or.inl (Or.inl (Or.inr h)))) (by rcases h with ⟨i, hi, j, _, _, _, rfl⟩; exact Finset.card_le_two))
        · rcases h with ⟨i, hi, g, _, _, _, rfl⟩
          exact absurd hdeg (deg3_triple_not_le_2 (by simp) (by simp) (by simp))
        · exact clausePoly_eval_zero_of_sat (assign2_sat_Fp C (Or.inl (Or.inr h)) (by rcases h with ⟨i, hi, _, rfl⟩; exact Finset.card_le_two))
        · exact clausePoly_eval_zero_of_sat (assign2_sat_Fp C (Or.inr h) (by rcases h with ⟨j, _, _, rfl⟩; simp))
  have h1 := heval 1 href
  simp at h1

-- =========================================================================
-- Section 3: Explicit clause lists and width-3 resolution verifier (P1, K1)
-- =========================================================================

private def fpAxList : List (List (ℕ × Bool)) :=
  petEdges.map (fun e => [(e.1.val, true), (e.2.val, true)]) ++
  (List.range 9).map (fun i => [(i, false), (10 + 5 * i, true)]) ++
  ((List.range 8).flatMap (fun h => (List.range 5).map (fun j => [(10 + 5 * h + j, false), (10 + 5 * (h + 1) + j, true)]))) ++
  ((List.range 8).flatMap (fun h => (List.range 4).map (fun g => [(h + 1, false), (10 + 5 * h + g, false), (10 + 5 * (h + 1) + g + 1, true)]))) ++
  (List.range 9).map (fun h => [(h + 1, false), (10 + 5 * h + 4, false)]) ++
  (List.range 4).map (fun j => [(10 + (j + 1), false)])

private def fkAxList : List (List (ℕ × Bool)) :=
  k44Edges.map (fun e => [(e.1.val, true), (e.2.val, true)]) ++
  (List.range 7).map (fun i => [(i, false), (8 + 3 * i, true)]) ++
  ((List.range 6).flatMap (fun h => (List.range 3).map (fun j => [(8 + 3 * h + j, false), (8 + 3 * (h + 1) + j, true)]))) ++
  ((List.range 6).flatMap (fun h => (List.range 2).map (fun g => [(h + 1, false), (8 + 3 * h + g, false), (8 + 3 * (h + 1) + g + 1, true)]))) ++
  (List.range 7).map (fun h => [(h + 1, false), (8 + 3 * h + 2, false)]) ++
  (List.range 2).map (fun j => [(8 + (j + 1), false)])

private def mkClause {V : Type} [DecidableEq V] (f : ℕ → V) (l : List (ℕ × Bool)) : Clause V :=
  (l.map (fun p => (f p.1, p.2))).toFinset

private lemma mkClause_card_le {V : Type} [DecidableEq V] (f : ℕ → V) (l : List (ℕ × Bool)) :
    (mkClause f l).card ≤ l.length := by
  simpa [mkClause] using List.toFinset_card_le (l.map (fun p => (f p.1, p.2)))

private lemma pVar_inl {i : ℕ} (hi : i < 10) : pVar i = Sum.inl ⟨i, hi⟩ := by
  simp [pVar, hi]

private lemma pVar_inr {h j : ℕ} (hj : j < 5) : pVar (10 + 5 * h + j) = Sum.inr (h, j) := by
  unfold pVar
  split_ifs with hlt
  · omega
  · congr 1; ext <;> simp <;> omega

private lemma kVar_inl {i : ℕ} (hi : i < 8) : kVar i = Sum.inl ⟨i, hi⟩ := by
  simp [kVar, hi]

private lemma kVar_inr {h j : ℕ} (hj : j < 3) : kVar (8 + 3 * h + j) = Sum.inr (h, j) := by
  unfold kVar
  split_ifs with hlt
  · omega
  · congr 1; ext <;> simp <;> omega

private lemma fpAxList_mem {c : List (ℕ × Bool)} (hc : c ∈ fpAxList) : mkClause pVar c ∈ FpSet := by
  simp only [fpAxList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hc
  rcases hc with (((((⟨e, he, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨h, hh, j, hj, rfl⟩) | ⟨h, hh, g, hg, rfl⟩) | ⟨h, hh, rfl⟩) | ⟨j, hj, rfl⟩)
  · left; left; left; left; left
    refine ⟨e, he, ?_⟩
    simp [mkClause, pVar_inl e.1.isLt, pVar_inl e.2.isLt]
  · left; left; left; left; right
    refine ⟨⟨i, by omega⟩, by simp; omega, ?_⟩
    have h1 := pVar_inr (h := i) (j := 0) (by omega)
    simp only [Nat.add_zero] at h1
    simp [mkClause, pVar_inl (show i < 10 by omega), h1]
  · left; left; left; right
    refine ⟨⟨h + 1, by omega⟩, h, j, rfl, by simp; omega, hj, ?_⟩
    simp [mkClause, pVar_inr hj]
  · left; left; right
    refine ⟨⟨h + 1, by omega⟩, h, g, rfl, by simp; omega, by omega, ?_⟩
    have h1 := pVar_inr (h := h + 1) (j := g + 1) (by omega)
    have h2 : 10 + 5 * (h + 1) + g + 1 = 10 + 5 * (h + 1) + (g + 1) := by omega
    rw [h2]
    simp [mkClause, pVar_inl (show h + 1 < 10 by omega), pVar_inr (show g < 5 by omega), h1]
  · left; right
    refine ⟨⟨h + 1, by omega⟩, h, rfl, ?_⟩
    simp [mkClause, pVar_inl (show h + 1 < 10 by omega), pVar_inr (show 4 < 5 by omega)]
  · right
    refine ⟨j + 1, by omega, by omega, ?_⟩
    have h1 := pVar_inr (h := 0) (j := j + 1) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h1
    simp [mkClause, h1]

private lemma fkAxList_mem {c : List (ℕ × Bool)} (hc : c ∈ fkAxList) : mkClause kVar c ∈ FkSet := by
  simp only [fkAxList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hc
  rcases hc with (((((⟨e, he, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨h, hh, j, hj, rfl⟩) | ⟨h, hh, g, hg, rfl⟩) | ⟨h, hh, rfl⟩) | ⟨j, hj, rfl⟩)
  · left; left; left; left; left
    refine ⟨e, he, ?_⟩
    simp [mkClause, kVar_inl e.1.isLt, kVar_inl e.2.isLt]
  · left; left; left; left; right
    refine ⟨⟨i, by omega⟩, by simp; omega, ?_⟩
    have h1 := kVar_inr (h := i) (j := 0) (by omega)
    simp only [Nat.add_zero] at h1
    simp [mkClause, kVar_inl (show i < 8 by omega), h1]
  · left; left; left; right
    refine ⟨⟨h + 1, by omega⟩, h, j, rfl, by simp; omega, hj, ?_⟩
    simp [mkClause, kVar_inr hj]
  · left; left; right
    refine ⟨⟨h + 1, by omega⟩, h, g, rfl, by simp; omega, by omega, ?_⟩
    have h1 := kVar_inr (h := h + 1) (j := g + 1) (by omega)
    have h2 : 8 + 3 * (h + 1) + g + 1 = 8 + 3 * (h + 1) + (g + 1) := by omega
    rw [h2]
    simp [mkClause, kVar_inl (show h + 1 < 8 by omega), kVar_inr (show g < 3 by omega), h1]
  · left; right
    refine ⟨⟨h + 1, by omega⟩, h, rfl, ?_⟩
    simp [mkClause, kVar_inl (show h + 1 < 8 by omega), kVar_inr (show 2 < 3 by omega)]
  · right
    refine ⟨j + 1, by omega, by omega, ?_⟩
    have h1 := kVar_inr (h := 0) (j := j + 1) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h1
    simp [mkClause, h1]

private lemma fkAxList_cover {C : Clause (Fin 8 ⊕ (ℕ × ℕ))} (hC : C ∈ FkSet) :
    ∃ c ∈ fkAxList, C = mkClause kVar c := by
  rcases hC with (((((h | h) | h) | h) | h) | h)
  · rcases h with ⟨e, he, rfl⟩
    refine ⟨[(e.1.val, true), (e.2.val, true)], ?_, ?_⟩
    · simp only [fkAxList, List.mem_append, List.mem_map]
      left; left; left; left; left; exact ⟨e, he, rfl⟩
    · simp [mkClause, kVar_inl e.1.isLt, kVar_inl e.2.isLt]
  · rcases h with ⟨i, hi, rfl⟩
    refine ⟨[(i.val, false), (8 + 3 * i.val, true)], ?_, ?_⟩
    · simp only [fkAxList, List.mem_append, List.mem_map, List.mem_range]
      left; left; left; left; right; exact ⟨i.val, by omega, rfl⟩
    · have h1 := kVar_inr (h := i.val) (j := 0) (by omega)
      simp only [Nat.add_zero] at h1
      simp [mkClause, kVar_inl i.isLt, h1]
  · rcases h with ⟨i, h0, j, hi, hlt, hj, rfl⟩
    refine ⟨[(8 + 3 * h0 + j, false), (8 + 3 * (h0 + 1) + j, true)], ?_, ?_⟩
    · simp only [fkAxList, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
      left; left; left; right; exact ⟨h0, by omega, j, hj, rfl⟩
    · simp [mkClause, kVar_inr hj, hi]
  · rcases h with ⟨i, h0, g, hi, hlt, hg, rfl⟩
    refine ⟨[(h0 + 1, false), (8 + 3 * h0 + g, false), (8 + 3 * (h0 + 1) + g + 1, true)], ?_, ?_⟩
    · simp only [fkAxList, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
      left; left; right; exact ⟨h0, by omega, g, by omega, rfl⟩
    · have h1 := kVar_inr (h := h0 + 1) (j := g + 1) (by omega)
      have h2 : 8 + 3 * (h0 + 1) + g + 1 = 8 + 3 * (h0 + 1) + (g + 1) := by omega
      rw [h2]
      have hi' : (⟨h0 + 1, by omega⟩ : Fin 8) = i := Fin.ext hi.symm
      simp [mkClause, kVar_inl (show h0 + 1 < 8 by omega), kVar_inr (show g < 3 by omega), h1, hi, hi']
  · rcases h with ⟨i, h0, hi, rfl⟩
    refine ⟨[(h0 + 1, false), (8 + 3 * h0 + 2, false)], ?_, ?_⟩
    · simp only [fkAxList, List.mem_append, List.mem_map, List.mem_range]
      left; right; exact ⟨h0, by omega, rfl⟩
    · have hi' : (⟨h0 + 1, by omega⟩ : Fin 8) = i := Fin.ext hi.symm
      simp [mkClause, kVar_inl (show h0 + 1 < 8 by omega), kVar_inr (show 2 < 3 by omega), hi']
  · rcases h with ⟨j, hj1, hj3, rfl⟩
    refine ⟨[(8 + j, false)], ?_, ?_⟩
    · simp only [fkAxList, List.mem_append, List.mem_map, List.mem_range]
      right; exact ⟨j - 1, by omega, by congr 1; simp; omega⟩
    · have h1 := kVar_inr (h := 0) (j := j) (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at h1
      simp [mkClause, h1]

private def litEq (a b : ℕ × Bool) : Bool := Nat.beq a.1 b.1 && (a.2 == b.2)

private def litMem (x : ℕ × Bool) : List (ℕ × Bool) → Bool
  | [] => false
  | y :: ys => litEq x y || litMem x ys

private def clauseAllLt (N : ℕ) : List (ℕ × Bool) → Bool
  | [] => true
  | (v, _) :: ls => Nat.blt v N && clauseAllLt N ls

private def sameClause (c1 c2 : List (ℕ × Bool)) : Bool :=
  c1.all (fun x => litMem x c2) && c2.all (fun x => litMem x c1)

private def checkResStep (N : ℕ) (cPos cNeg cOut : List (ℕ × Bool)) (v : ℕ) : Bool :=
  Nat.blt v N &&
  clauseAllLt N cPos && clauseAllLt N cNeg && clauseAllLt N cOut &&
  Nat.ble cOut.length 3 &&
  litMem (v, true) cPos && litMem (v, false) cNeg &&
  cOut.all (fun x => (!litEq x (v, true) && litMem x cPos) || (!litEq x (v, false) && litMem x cNeg)) &&
  cPos.all (fun x => litEq x (v, true) || litMem x cOut) &&
  cNeg.all (fun x => litEq x (v, false) || litMem x cOut)

private def getCl : ℕ → List (List (ℕ × Bool)) → List (ℕ × Bool)
  | _, [] => []
  | 0, x :: _ => x
  | n + 1, _ :: xs => getCl n xs

private def checkResProof (N : ℕ) (axL : List (List (ℕ × Bool))) (curLen : ℕ)
    (stRev : List (List (ℕ × Bool))) : List (ℕ × ℕ × ℕ × ℕ × List (ℕ × Bool)) → Bool
  | [] => match stRev with | [] :: _ => true | _ => false
  | (kind, a1, a2, piv, cl) :: rest =>
    if Nat.beq kind 0 then
      Nat.blt a1 axL.length && Nat.ble cl.length 3 && sameClause (getCl a1 axL) cl &&
      checkResProof N axL (curLen + 1) (cl :: stRev) rest
    else
      Nat.blt a1 curLen && Nat.blt a2 curLen &&
      checkResStep N (getCl (curLen - 1 - a1) stRev) (getCl (curLen - 1 - a2) stRev) cl piv &&
      checkResProof N axL (curLen + 1) (cl :: stRev) rest

private lemma litEq_iff (a b : ℕ × Bool) : litEq a b = true ↔ a = b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  simp [litEq, Prod.mk.injEq]

private lemma litMem_iff (x : ℕ × Bool) (l : List (ℕ × Bool)) : litMem x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [litMem]
  | cons y ys ih => simp [litMem, litEq_iff, ih]

private lemma clauseAllLt_iff (N : ℕ) (l : List (ℕ × Bool)) :
    clauseAllLt N l = true ↔ ∀ x ∈ l, x.1 < N := by
  induction l with
  | nil => simp [clauseAllLt]
  | cons x xs ih =>
    rcases x with ⟨v, s⟩
    simp [clauseAllLt, ih]

private lemma getCl_mem {l : List (List (ℕ × Bool))} {i : ℕ} (hi : i < l.length) :
    getCl i l ∈ l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [getCl]
    | succ i => exact List.mem_cons_of_mem _ (ih (by simp at hi; omega))

private lemma sameClause_mkClause {V : Type} [DecidableEq V] (f : ℕ → V) {c1 c2 : List (ℕ × Bool)}
    (h : sameClause c1 c2 = true) : mkClause f c1 = mkClause f c2 := by
  simp only [sameClause, Bool.and_eq_true, List.all_eq_true, litMem_iff] at h
  ext ⟨v, s⟩
  simp only [mkClause, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩; exact ⟨x, h.1 x hx, heq⟩
  · rintro ⟨x, hx, heq⟩; exact ⟨x, h.2 x hx, heq⟩

private lemma checkResStep_sound {V : Type} [DecidableEq V] (N : ℕ) (f : ℕ → V)
    (hinj : ∀ a b : ℕ, a < N → b < N → f a = f b → a = b)
    {cPos cNeg cOut : List (ℕ × Bool)} {v : ℕ}
    (h : checkResStep N cPos cNeg cOut v = true) :
    IsResolvent (mkClause f cPos) (mkClause f cNeg) (mkClause f cOut) := by
  simp only [checkResStep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Nat.blt_eq, Nat.ble_eq, List.all_eq_true, litMem_iff, clauseAllLt_iff] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hPosLt⟩, hNegLt⟩, hOutLt⟩, _⟩, hvPos⟩, hvNeg⟩, hOutSub⟩, hPosSub⟩, hNegSub⟩
  refine ⟨f v, ?_, ?_, ?_⟩
  · simp only [mkClause, List.mem_toFinset, List.mem_map]; exact ⟨(v, true), hvPos, rfl⟩
  · simp only [mkClause, List.mem_toFinset, List.mem_map]; exact ⟨(v, false), hvNeg, rfl⟩
  · ext ⟨u, s⟩
    simp only [Finset.mem_union, Finset.mem_erase, mkClause, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨x, hx, hfx⟩
      rcases hOutSub x hx with ⟨hne, hxp⟩ | ⟨hne, hxn⟩
      · left
        refine ⟨?_, ⟨x, hxp, hfx⟩⟩
        intro heq
        have hx1 : x.1 = v := hinj x.1 v (hOutLt x hx) hv (by
          have h1 := congrArg Prod.fst hfx; have h2 := congrArg Prod.fst heq; exact h1.trans h2)
        have hx2 : x.2 = true := by
          have h1 := congrArg Prod.snd hfx; have h2 := congrArg Prod.snd heq; exact h1.trans h2
        have hxeq : x = (v, true) := Prod.ext hx1 hx2
        rw [hxeq] at hne; simp [litEq] at hne
      · right
        refine ⟨?_, ⟨x, hxn, hfx⟩⟩
        intro heq
        have hx1 : x.1 = v := hinj x.1 v (hOutLt x hx) hv (by
          have h1 := congrArg Prod.fst hfx; have h2 := congrArg Prod.fst heq; exact h1.trans h2)
        have hx2 : x.2 = false := by
          have h1 := congrArg Prod.snd hfx; have h2 := congrArg Prod.snd heq; exact h1.trans h2
        have hxeq : x = (v, false) := Prod.ext hx1 hx2
        rw [hxeq] at hne; simp [litEq] at hne
    · rintro (⟨hne, ⟨x, hxp, hfx⟩⟩ | ⟨hne, ⟨x, hxn, hfx⟩⟩)
      · rcases hPosSub x hxp with heq | hxout
        · rw [litEq_iff] at heq; subst heq; exact absurd hfx.symm hne
        · exact ⟨x, hxout, hfx⟩
      · rcases hNegSub x hxn with heq | hxout
        · rw [litEq_iff] at heq; subst heq; exact absurd hfx.symm hne
        · exact ⟨x, hxout, hfx⟩

private lemma checkResProof_sound {V : Type} [DecidableEq V] (N : ℕ) (f : ℕ → V)
    (hinj : ∀ a b : ℕ, a < N → b < N → f a = f b → a = b)
    (F : Set (Clause V)) (axL : List (List (ℕ × Bool)))
    (hax : ∀ c ∈ axL, mkClause f c ∈ F)
    (steps : List (ℕ × ℕ × ℕ × ℕ × List (ℕ × Bool))) :
    ∀ (stRev : List (List (ℕ × Bool))),
      IsDerivation F (stRev.map (mkClause f)) →
      (∀ c ∈ stRev, c.length ≤ 3) →
      checkResProof N axL stRev.length stRev steps = true →
      ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ 3 := by
  induction steps with
  | nil =>
    intro stRev hder hlen hchk
    cases stRev with
    | nil => simp [checkResProof] at hchk
    | cons hd tl =>
      cases hd with
      | nil =>
        refine ⟨(([] :: tl).map (mkClause f)), ⟨hder, ?_⟩, ?_⟩
        · simp [mkClause]
        · intro D hD
          rw [List.mem_map] at hD
          rcases hD with ⟨c, hc, rfl⟩
          exact (mkClause_card_le f c).trans (hlen c hc)
      | cons _ _ => simp [checkResProof] at hchk
  | cons st rest ih =>
    intro stRev hder hlen hchk
    rcases st with ⟨kind, a1, a2, piv, cl⟩
    simp only [checkResProof] at hchk
    split_ifs at hchk with hk
    · simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hchk
      rcases hchk with ⟨⟨⟨ha1, hcllen⟩, hsame⟩, hrest⟩
      have hmemF : mkClause f cl ∈ F := by
        rw [← sameClause_mkClause f hsame]
        exact hax _ (getCl_mem ha1)
      have hder' : IsDerivation F ((cl :: stRev).map (mkClause f)) :=
        IsDerivation.ax hder hmemF
      have hlen' : ∀ c ∈ cl :: stRev, c.length ≤ 3 := by
        intro c hc; rcases List.mem_cons.mp hc with rfl | hc'
        · exact hcllen
        · exact hlen c hc'
      exact ih (cl :: stRev) hder' hlen' (by simpa [List.length_cons] using hrest)
    · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
      rcases hchk with ⟨⟨⟨ha1, ha2⟩, hstep⟩, hrest⟩
      have hres := checkResStep_sound N f hinj hstep
      have hcllen : cl.length ≤ 3 := by
        simp only [checkResStep, Bool.and_eq_true, Nat.ble_eq] at hstep
        exact hstep.1.1.1.1.1.2
      have h1lt : stRev.length - 1 - a1 < stRev.length := by omega
      have h2lt : stRev.length - 1 - a2 < stRev.length := by omega
      have hder' : IsDerivation F ((cl :: stRev).map (mkClause f)) :=
        IsDerivation.res hder (List.mem_map_of_mem (getCl_mem h1lt))
          (List.mem_map_of_mem (getCl_mem h2lt)) hres
      have hlen' : ∀ c ∈ cl :: stRev, c.length ≤ 3 := by
        intro c hc; rcases List.mem_cons.mp hc with rfl | hc'
        · exact hcllen
        · exact hlen c hc'
      exact ih (cl :: stRev) hder' hlen' (by simpa [List.length_cons] using hrest)

private def resPSteps : List (ℕ × ℕ × ℕ × ℕ × List (ℕ × Bool)) :=
[
  (0, 4, 0, 0, [(0, true), (4, true)]),
  (0, 15, 0, 0, [(0, false), (10, true)]),
  (1, 0, 1, 0, [(4, true), (10, true)]),
  (0, 1, 0, 0, [(1, true), (2, true)]),
  (0, 64, 0, 0, [(1, false), (10, false), (16, true)]),
  (1, 3, 4, 1, [(2, true), (10, false), (16, true)]),
  (0, 30, 0, 0, [(16, false), (21, true)]),
  (1, 5, 6, 16, [(2, true), (10, false), (21, true)]),
  (1, 2, 7, 10, [(2, true), (4, true), (21, true)]),
  (0, 0, 0, 0, [(0, true), (1, true)]),
  (0, 16, 0, 0, [(1, false), (15, true)]),
  (1, 9, 10, 1, [(0, true), (15, true)]),
  (1, 11, 1, 0, [(10, true), (15, true)]),
  (0, 24, 0, 0, [(10, false), (15, true)]),
  (1, 12, 13, 10, [(15, true)]),
  (0, 68, 0, 0, [(2, false), (15, false), (21, true)]),
  (1, 14, 15, 15, [(2, false), (21, true)]),
  (1, 8, 16, 2, [(4, true), (21, true)]),
  (0, 3, 0, 0, [(3, true), (4, true)]),
  (0, 73, 0, 0, [(3, false), (21, false), (27, true)]),
  (1, 18, 19, 3, [(4, true), (21, false), (27, true)]),
  (0, 41, 0, 0, [(27, false), (32, true)]),
  (1, 20, 21, 27, [(4, true), (21, false), (32, true)]),
  (1, 17, 22, 21, [(4, true), (32, true)]),
  (0, 2, 0, 0, [(2, true), (3, true)]),
  (1, 24, 15, 2, [(3, true), (15, false), (21, true)]),
  (1, 14, 25, 15, [(3, true), (21, true)]),
  (0, 35, 0, 0, [(21, false), (26, true)]),
  (1, 26, 27, 21, [(3, true), (26, true)]),
  (0, 29, 0, 0, [(15, false), (20, true)]),
  (1, 14, 29, 15, [(20, true)]),
  (0, 72, 0, 0, [(3, false), (20, false), (26, true)]),
  (1, 30, 31, 20, [(3, false), (26, true)]),
  (1, 28, 32, 3, [(26, true)]),
  (0, 77, 0, 0, [(4, false), (26, false), (32, true)]),
  (1, 33, 34, 26, [(4, false), (32, true)]),
  (1, 23, 35, 4, [(32, true)]),
  (0, 46, 0, 0, [(32, false), (37, true)]),
  (0, 51, 0, 0, [(37, false), (42, true)]),
  (1, 37, 38, 37, [(32, false), (42, true)]),
  (0, 10, 0, 0, [(5, true), (7, true)]),
  (0, 90, 0, 0, [(7, false), (42, false), (48, true)]),
  (1, 40, 41, 7, [(5, true), (42, false), (48, true)]),
  (1, 39, 42, 42, [(5, true), (32, false), (48, true)]),
  (1, 36, 43, 32, [(5, true), (48, true)]),
  (0, 82, 0, 0, [(5, false), (32, false), (38, true)]),
  (0, 52, 0, 0, [(38, false), (43, true)]),
  (0, 57, 0, 0, [(43, false), (48, true)]),
  (1, 46, 47, 43, [(38, false), (48, true)]),
  (0, 13, 0, 0, [(6, true), (8, true)]),
  (0, 95, 0, 0, [(8, false), (48, false), (54, true)]),
  (1, 49, 50, 8, [(6, true), (48, false), (54, true)]),
  (0, 12, 0, 0, [(6, true), (9, true)]),
  (0, 104, 0, 0, [(9, false), (54, false)]),
  (1, 52, 53, 9, [(6, true), (54, false)]),
  (1, 51, 54, 54, [(6, true), (48, false)]),
  (1, 48, 55, 48, [(6, true), (38, false)]),
  (0, 87, 0, 0, [(6, false), (38, false), (44, true)]),
  (0, 11, 0, 0, [(7, true), (9, true)]),
  (0, 102, 0, 0, [(7, false), (44, false)]),
  (1, 58, 59, 7, [(9, true), (44, false)]),
  (0, 58, 0, 0, [(44, false), (49, true)]),
  (0, 63, 0, 0, [(49, false), (54, true)]),
  (1, 61, 62, 49, [(44, false), (54, true)]),
  (1, 63, 53, 54, [(9, false), (44, false)]),
  (1, 60, 64, 9, [(44, false)]),
  (1, 57, 65, 44, [(6, false), (38, false)]),
  (1, 56, 66, 6, [(38, false)]),
  (1, 45, 67, 38, [(5, false), (32, false)]),
  (1, 36, 68, 32, [(5, false)]),
  (1, 44, 69, 5, [(48, true)]),
  (0, 86, 0, 0, [(6, false), (37, false), (43, true)]),
  (1, 37, 71, 37, [(6, false), (32, false), (43, true)]),
  (1, 55, 72, 6, [(32, false), (43, true), (48, false)]),
  (0, 91, 0, 0, [(7, false), (43, false), (49, true)]),
  (1, 40, 74, 7, [(5, true), (43, false), (49, true)]),
  (0, 14, 0, 0, [(5, true), (8, true)]),
  (0, 103, 0, 0, [(8, false), (49, false)]),
  (1, 76, 77, 8, [(5, true), (49, false)]),
  (1, 75, 78, 49, [(5, true), (43, false)]),
  (1, 73, 79, 43, [(5, true), (32, false), (48, false)]),
  (1, 36, 80, 32, [(5, true), (48, false)]),
  (1, 81, 69, 5, [(48, false)]),
  (1, 70, 82, 48, [])
]

private def resKSteps : List (ℕ × ℕ × ℕ × ℕ × List (ℕ × Bool)) :=
[
  (0, 1, 0, 0, [(0, true), (5, true)]),
  (0, 16, 0, 0, [(0, false), (8, true)]),
  (1, 0, 1, 0, [(5, true), (8, true)]),
  (0, 23, 0, 0, [(8, false), (11, true)]),
  (0, 9, 0, 0, [(2, true), (5, true)]),
  (0, 43, 0, 0, [(2, false), (11, false), (15, true)]),
  (1, 4, 5, 2, [(5, true), (11, false), (15, true)]),
  (1, 3, 6, 11, [(5, true), (8, false), (15, true)]),
  (0, 30, 0, 0, [(15, false), (18, true)]),
  (1, 7, 8, 15, [(5, true), (8, false), (18, true)]),
  (0, 33, 0, 0, [(18, false), (21, true)]),
  (1, 9, 10, 18, [(5, true), (8, false), (21, true)]),
  (0, 36, 0, 0, [(21, false), (24, true)]),
  (1, 11, 12, 21, [(5, true), (8, false), (24, true)]),
  (1, 2, 13, 8, [(5, true), (24, true)]),
  (0, 12, 0, 0, [(3, true), (4, true)]),
  (0, 20, 0, 0, [(4, false), (20, true)]),
  (1, 15, 16, 4, [(3, true), (20, true)]),
  (0, 19, 0, 0, [(3, false), (17, true)]),
  (1, 17, 18, 3, [(17, true), (20, true)]),
  (0, 32, 0, 0, [(17, false), (20, true)]),
  (1, 19, 20, 17, [(20, true)]),
  (0, 49, 0, 0, [(5, false), (20, false), (24, true)]),
  (1, 21, 22, 20, [(5, false), (24, true)]),
  (1, 14, 23, 5, [(24, true)]),
  (0, 6, 0, 0, [(1, true), (6, true)]),
  (0, 52, 0, 0, [(6, false), (24, false), (28, true)]),
  (1, 25, 26, 6, [(1, true), (24, false), (28, true)]),
  (0, 7, 0, 0, [(1, true), (7, true)]),
  (0, 59, 0, 0, [(7, false), (28, false)]),
  (1, 28, 29, 7, [(1, true), (28, false)]),
  (1, 27, 30, 28, [(1, true), (24, false)]),
  (1, 24, 31, 24, [(1, true)]),
  (0, 3, 0, 0, [(0, true), (7, true)]),
  (1, 33, 1, 0, [(7, true), (8, true)]),
  (0, 2, 0, 0, [(0, true), (6, true)]),
  (1, 35, 26, 6, [(0, true), (24, false), (28, true)]),
  (1, 36, 1, 0, [(8, true), (24, false), (28, true)]),
  (1, 37, 29, 28, [(7, false), (8, true), (24, false)]),
  (1, 34, 38, 7, [(8, true), (24, false)]),
  (1, 24, 39, 24, [(8, true)]),
  (0, 41, 0, 0, [(1, false), (8, false), (12, true)]),
  (1, 40, 41, 8, [(1, false), (12, true)]),
  (1, 32, 42, 1, [(12, true)]),
  (0, 10, 0, 0, [(2, true), (6, true)]),
  (1, 44, 26, 6, [(2, true), (24, false), (28, true)]),
  (0, 11, 0, 0, [(2, true), (7, true)]),
  (1, 46, 29, 7, [(2, true), (28, false)]),
  (1, 45, 47, 28, [(2, true), (24, false)]),
  (1, 24, 48, 24, [(2, true)]),
  (0, 44, 0, 0, [(2, false), (12, false), (16, true)]),
  (0, 31, 0, 0, [(16, false), (19, true)]),
  (0, 56, 0, 0, [(4, false), (19, false)]),
  (1, 15, 52, 4, [(3, true), (19, false)]),
  (1, 51, 53, 19, [(3, true), (16, false)]),
  (0, 55, 0, 0, [(3, false), (16, false)]),
  (1, 54, 55, 3, [(16, false)]),
  (1, 50, 56, 16, [(2, false), (12, false)]),
  (1, 49, 57, 2, [(12, false)]),
  (1, 43, 58, 12, [])
]

set_option maxHeartbeats 20000000 in
private lemma resP_ok : checkResProof 55 fpAxList 0 [] resPSteps = true := by decide +kernel

set_option maxHeartbeats 20000000 in
private lemma resK_ok : checkResProof 29 fkAxList 0 [] resKSteps = true := by decide +kernel

private lemma P1_width3 : ∃ π, IsRefutation FpSet π ∧ ∀ D ∈ π, D.card ≤ 3 :=
  checkResProof_sound 55 pVar pVar_inj_lt FpSet fpAxList (fun _ h => fpAxList_mem h)
    resPSteps [] IsDerivation.nil (by simp) resP_ok

private lemma K1_width3 : ∃ π, IsRefutation FkSet π ∧ ∀ D ∈ π, D.card ≤ 3 :=
  checkResProof_sound 29 kVar kVar_inj_lt FkSet fkAxList (fun _ h => fkAxList_mem h)
    resKSteps [] IsDerivation.nil (by simp) resK_ok

-- =========================================================================
-- Section 4: Width-3 resolution implies PC degree 4 (K3)
-- =========================================================================

private noncomputable def litPoly {V : Type} (l : Literal V) : MvPolynomial V (ZMod 2) :=
  if l.2 = true then 1 + X l.1 else X l.1

private lemma litPoly_totalDegree_le {V : Type} (l : Literal V) : (litPoly l).totalDegree ≤ 1 := by
  unfold litPoly
  split_ifs
  · exact (totalDegree_add _ _).trans (max_le (by simp) (by simp))
  · simp

private lemma clausePoly_totalDegree_le {V : Type} [DecidableEq V] (C : Clause V) :
    (clausePoly C).totalDegree ≤ C.card := by
  unfold clausePoly
  refine (totalDegree_prod_le C _).trans ?_
  calc ∑ l ∈ C, (if l.2 = true then (1 : MvPolynomial V (ZMod 2)) + X l.1 else X l.1).totalDegree
      ≤ ∑ _l ∈ C, 1 := Finset.sum_le_sum (fun l _ => litPoly_totalDegree_le l)
    _ = C.card := by simp

private lemma pc_mul_lit {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    (l : Literal V) {p : MvPolynomial V (ZMod 2)} (hp : PCDerivable F B p)
    (hdeg : p.totalDegree + 1 ≤ B) : PCDerivable F B (litPoly l * p) := by
  unfold litPoly
  have hmul : (X l.1 * p).totalDegree ≤ B := by
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
  split_ifs
  · rw [add_mul, one_mul]
    exact PCDerivable.add hp (PCDerivable.mulX l.1 hp hmul)
  · exact PCDerivable.mulX l.1 hp hmul

private lemma pc_mul_prod_lits {V : Type} [DecidableEq V] {F : Set (MvPolynomial V (ZMod 2))}
    {B : ℕ} (S : Finset (Literal V)) {p : MvPolynomial V (ZMod 2)} (hp : PCDerivable F B p)
    (hdeg : p.totalDegree + S.card ≤ B) :
    PCDerivable F B ((∏ l ∈ S, litPoly l) * p) := by
  induction S using Finset.induction_on generalizing p with
  | empty => simpa using hp
  | insert l T hlT ih =>
    rw [Finset.prod_insert hlT, mul_assoc]
    have hcard : (insert l T).card = T.card + 1 := Finset.card_insert_of_notMem hlT
    have hT : PCDerivable F B ((∏ x ∈ T, litPoly x) * p) := ih hp (by omega)
    have hTdeg : ((∏ x ∈ T, litPoly x) * p).totalDegree ≤ p.totalDegree + T.card := by
      refine (totalDegree_mul _ _).trans ?_
      have h1 : (∏ x ∈ T, litPoly x).totalDegree ≤ T.card := by
        simpa [clausePoly, litPoly] using clausePoly_totalDegree_le T
      omega
    exact pc_mul_lit l hT (by omega)

private lemma res_width3_to_pc4 {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (hπ : IsRefutation F π) (hw : ∀ D ∈ π, D.card ≤ 3) :
    PCRefutable (cnfSystem F) 4 := by
  rcases hπ with ⟨hder, hemp⟩
  have hall : ∀ π', IsDerivation F π' → (∀ D ∈ π', D.card ≤ 3) → ∀ D ∈ π', PCDerivable (cnfSystem F) 4 (clausePoly D) := by
    intro π' hder'
    induction hder' with
    | nil => intro _ D hD; simp at hD
    | ax _ hC ih =>
      intro hw' D hD
      rcases List.mem_cons.mp hD with rfl | hD'
      · exact PCDerivable.ax (Or.inr ⟨D, hC, rfl⟩)
          ((clausePoly_totalDegree_le D).trans ((hw' D List.mem_cons_self).trans (by omega)))
      · exact ih (fun E hE => hw' E (List.mem_cons_of_mem _ hE)) D hD'
    | @res π0 C0 D0 R0 _ hC hD hR ih =>
      intro hw' E hE
      have ih' := ih (fun X hX => hw' X (List.mem_cons_of_mem _ hX))
      rcases List.mem_cons.mp hE with rfl | hE'
      · rcases hR with ⟨v, hvC, hvD, rfl⟩
        set A := C0.erase (v, true)
        set B := D0.erase (v, false)
        have hCp : PCDerivable (cnfSystem F) 4 (clausePoly C0) := ih' C0 hC
        have hDp : PCDerivable (cnfSystem F) 4 (clausePoly D0) := ih' D0 hD
        have hRcard : (A ∪ B).card ≤ 3 := hw' (A ∪ B) List.mem_cons_self
        have hCeq : clausePoly C0 = (1 + X v) * clausePoly A := by
          unfold clausePoly
          rw [← Finset.insert_erase hvC, Finset.prod_insert (Finset.notMem_erase _ _)]
          simp only [↓reduceIte]
          rfl
        have hDeq : clausePoly D0 = X v * clausePoly B := by
          unfold clausePoly
          rw [← Finset.insert_erase hvD, Finset.prod_insert (Finset.notMem_erase _ _)]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rfl
        have hCdeg : (clausePoly C0).totalDegree + (B \ A).card ≤ 4 := by
          have h1 : (clausePoly C0).totalDegree ≤ 1 + A.card := by
            rw [hCeq]
            refine (totalDegree_mul _ _).trans ?_
            have h11 : ((1 : MvPolynomial V (ZMod 2)) + X v).totalDegree ≤ 1 := by
              simpa [litPoly] using litPoly_totalDegree_le (v, true)
            have h12 := clausePoly_totalDegree_le A
            omega
          have h2 : A.card + (B \ A).card = (A ∪ B).card := by
            rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint.symm, Finset.union_sdiff_self_eq_union]
          omega
        have hDdeg : (clausePoly D0).totalDegree + (A \ B).card ≤ 4 := by
          have h1 : (clausePoly D0).totalDegree ≤ 1 + B.card := by
            rw [hDeq]
            refine (totalDegree_mul _ _).trans ?_
            have h11 : (X v : MvPolynomial V (ZMod 2)).totalDegree = 1 := totalDegree_X v
            have h12 := clausePoly_totalDegree_le B
            omega
          have h2 : B.card + (A \ B).card = (A ∪ B).card := by
            rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint.symm, Finset.union_sdiff_self_eq_union, Finset.union_comm]
          omega
        have h1 := pc_mul_prod_lits (B \ A) hCp hCdeg
        have h2 := pc_mul_prod_lits (A \ B) hDp hDdeg
        have hprod1 : (∏ l ∈ B \ A, litPoly l) * clausePoly C0 = (1 + X v) * clausePoly (A ∪ B) := by
          rw [hCeq, mul_left_comm]
          congr 1
          unfold clausePoly litPoly
          rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union, Finset.union_comm]
        have hprod2 : (∏ l ∈ A \ B, litPoly l) * clausePoly D0 = X v * clausePoly (A ∪ B) := by
          rw [hDeq, mul_left_comm]
          congr 1
          unfold clausePoly litPoly
          rw [← Finset.prod_union Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union]
        rw [hprod1] at h1
        rw [hprod2] at h2
        have hsum := PCDerivable.add h1 h2
        have hcancel : (1 + X v) * clausePoly (A ∪ B) + X v * clausePoly (A ∪ B) = clausePoly (A ∪ B) := by
          rw [add_mul, one_mul, add_assoc, zmod2_poly_add_self, add_zero]
        rw [hcancel] at hsum
        exact hsum
      · exact ih' E hE'
  have h1 := hall π hder hw ∅ hemp
  simpa [PCRefutable, clausePoly] using h1

private lemma K3_pc4 : PCRefutable (cnfSystem FkSet) 4 := by
  obtain ⟨π, hπ, hw⟩ := K1_width3
  exact res_width3_to_pc4 hπ hw

-- =========================================================================
-- Section 5: PC degree-3 refutation of Fp (P3)
-- =========================================================================

private def insMon (m : ℕ) : List ℕ → List ℕ
  | [] => [m]
  | x :: xs =>
    if Nat.beq m x then xs
    else if Nat.blt m x then m :: x :: xs
    else x :: insMon m xs

private def xorPoly : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => xorPoly xs (insMon x ys)

private def mulVarMon (v m : ℕ) : ℕ :=
  let v1 := v + 1
  let c0 := Nat.land m 63
  let c1 := Nat.land (Nat.shiftRight m 6) 63
  let c2 := Nat.shiftRight m 12
  if Nat.beq c0 0 then v1
  else if Nat.beq c0 v1 then m
  else if Nat.beq c1 0 then
    if Nat.blt v1 c0 then v1 + 64 * c0 else c0 + 64 * v1
  else if Nat.beq c1 v1 then m
  else if Nat.beq c2 0 then
    if Nat.blt v1 c0 then v1 + 64 * (c0 + 64 * c1)
    else if Nat.blt v1 c1 then c0 + 64 * (v1 + 64 * c1)
    else c0 + 64 * (c1 + 64 * v1)
  else m

private def mulVarPolyAcc (v : ℕ) (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | m :: ms => mulVarPolyAcc v (insMon (mulVarMon v m) acc) ms

private def monDegLe2 (m : ℕ) : Bool :=
  Nat.beq (Nat.shiftRight m 12) 0 &&
  (!Nat.beq (Nat.land m 63) 0 || Nat.beq (Nat.land (Nat.shiftRight m 6) 63) 0)

private def allDegLe2 : List ℕ → Bool
  | [] => true
  | m :: ms => monDegLe2 m && allDegLe2 ms

private def clauseToPoly : List (ℕ × Bool) → List ℕ
  | [] => [0]
  | (v, s) :: ls =>
    let p := clauseToPoly ls
    if s then xorPoly p (mulVarPolyAcc v [] p) else mulVarPolyAcc v [] p

private def getPoly : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | 0, x :: _ => x
  | n + 1, _ :: xs => getPoly n xs

private def applyXors (curLen : ℕ) (stRev : List (List ℕ)) (p : List ℕ) : List ℕ → List ℕ
  | [] => p
  | idx :: xs => applyXors curLen stRev (xorPoly p (getPoly (curLen - 1 - idx) stRev)) xs

private def runPCSteps (axL : List (List (ℕ × Bool))) (curLen : ℕ) (stRev : List (List ℕ)) :
    List (ℕ × ℕ × ℕ × List ℕ) → Bool
  | [] => match stRev with | [0] :: _ => true | _ => false
  | (kind, a1, a2, xors) :: rest =>
    if Nat.beq kind 0 then
      if !Nat.blt a1 axL.length then false
      else
        let p1 := applyXors curLen stRev (clauseToPoly (getCl a1 axL)) xors
        match p1 with
        | [] => runPCSteps axL (curLen + 1) ([] :: stRev) rest
        | h :: t => runPCSteps axL (curLen + 1) ((h :: t) :: stRev) rest
    else
      if !Nat.blt a1 55 || !Nat.blt a2 curLen then false
      else
        let src := getPoly (curLen - 1 - a2) stRev
        if !allDegLe2 src then false
        else
          let p1 := applyXors curLen stRev (mulVarPolyAcc a1 [] src) xors
          match p1 with
          | [] => runPCSteps axL (curLen + 1) ([] :: stRev) rest
          | h :: t => runPCSteps axL (curLen + 1) ((h :: t) :: stRev) rest

private noncomputable def evalSlot (c : ℕ) : MvPolynomial (Fin 10 ⊕ (ℕ × ℕ)) (ZMod 2) :=
  if c = 0 then 1 else X (pVar (c - 1))

private noncomputable def evalMonP (m : ℕ) : MvPolynomial (Fin 10 ⊕ (ℕ × ℕ)) (ZMod 2) :=
  evalSlot (Nat.land m 63) * evalSlot (Nat.land (Nat.shiftRight m 6) 63) * evalSlot (Nat.shiftRight m 12)

private noncomputable def evalPolyP (p : List ℕ) : MvPolynomial (Fin 10 ⊕ (ℕ × ℕ)) (ZMod 2) :=
  (p.map evalMonP).sum

private lemma evalSlot_zero : evalSlot 0 = 1 := by simp [evalSlot]

private lemma evalSlot_succ (v : ℕ) : evalSlot (v + 1) = X (pVar v) := by simp [evalSlot]

private lemma evalSlot_deg_le (c : ℕ) : (evalSlot c).totalDegree ≤ 1 := by
  unfold evalSlot; split_ifs <;> simp

private lemma evalMonP_deg_le2 {m : ℕ} (h : monDegLe2 m = true) :
    (evalMonP m).totalDegree ≤ 2 := by
  simp only [monDegLe2, Bool.and_eq_true, Nat.beq_eq] at h
  unfold evalMonP
  rw [h.1, evalSlot_zero, mul_one]
  exact (totalDegree_mul _ _).trans (by have := evalSlot_deg_le (Nat.land m 63); have := evalSlot_deg_le (Nat.land (Nat.shiftRight m 6) 63); omega)

private lemma evalPolyP_deg_le2 {p : List ℕ} (h : allDegLe2 p = true) :
    (evalPolyP p).totalDegree ≤ 2 := by
  induction p with
  | nil => simp [evalPolyP]
  | cons m ms ih =>
    simp only [allDegLe2, Bool.and_eq_true] at h
    simp only [evalPolyP, List.map_cons, List.sum_cons]
    exact (totalDegree_add _ _).trans (max_le (evalMonP_deg_le2 h.1) (ih h.2))

private lemma evalPolyP_insMon (m : ℕ) (p : List ℕ) :
    evalPolyP (insMon m p) = evalMonP m + evalPolyP p := by
  induction p with
  | nil => simp [insMon, evalPolyP]
  | cons x xs ih =>
    unfold insMon
    split_ifs with h1 h2
    · rw [Nat.beq_eq] at h1; subst h1
      simp only [evalPolyP, List.map_cons, List.sum_cons, ← add_assoc, zmod2_poly_add_self, zero_add]
    · simp [evalPolyP]
    · simp only [evalPolyP, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; ring

private lemma evalPolyP_xorPoly (p q : List ℕ) :
    evalPolyP (xorPoly p q) = evalPolyP p + evalPolyP q := by
  induction p generalizing q with
  | nil => simp [xorPoly, evalPolyP]
  | cons x xs ih =>
    rw [xorPoly, ih, evalPolyP_insMon]
    simp only [evalPolyP, List.map_cons, List.sum_cons]
    ring

private lemma nat_pack_slots_2 {a b : ℕ} (ha : a < 64) (hb : b < 64) :
    Nat.land (a + 64 * b) 63 = a ∧
    Nat.land (Nat.shiftRight (a + 64 * b) 6) 63 = b ∧
    Nat.shiftRight (a + 64 * b) 12 = 0 := by
  rw [nat_land_63, nat_shr, nat_land_63, nat_shr]
  omega

private lemma nat_pack_slots_3 {a b c : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    Nat.land (a + 64 * (b + 64 * c)) 63 = a ∧
    Nat.land (Nat.shiftRight (a + 64 * (b + 64 * c)) 6) 63 = b ∧
    Nat.shiftRight (a + 64 * (b + 64 * c)) 12 = c := by
  rw [nat_land_63, nat_shr, nat_land_63, nat_shr]
  omega

private lemma pc_bool_mul_slot (v : Fin 10 ⊕ (ℕ × ℕ)) (c : ℕ) :
    PCDerivable (cnfSystem FpSet) 3 ((X v * X v + X v) * evalSlot c) := by
  have hxv : (X v : MvPolynomial (Fin 10 ⊕ (ℕ × ℕ)) (ZMod 2)).totalDegree = 1 := totalDegree_X v
  have h2 : (X v * X v + X v : MvPolynomial (Fin 10 ⊕ (ℕ × ℕ)) (ZMod 2)).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans (by omega)) (by omega))
  have hax : PCDerivable (cnfSystem FpSet) 3 (X v * X v + X v) :=
    PCDerivable.ax (Or.inl ⟨v, rfl⟩) (by omega)
  unfold evalSlot
  split_ifs with hc
  · simpa using hax
  · rw [mul_comm]
    refine PCDerivable.mulX (pVar (c - 1)) hax ?_
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (X (pVar (c - 1)) : MvPolynomial (Fin 10 ⊕ (ℕ × ℕ)) (ZMod 2)).totalDegree = 1 := totalDegree_X _
    omega

private lemma pc_mulVarMon_diff {v m : ℕ} (hv : v < 55) (hm : monDegLe2 m = true) :
    PCDerivable (cnfSystem FpSet) 3 (X (pVar v) * evalMonP m + evalMonP (mulVarMon v m)) := by
  simp only [monDegLe2, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at hm
  rcases hm with ⟨hm2, hm01⟩
  have h63 : ∀ n, Nat.land n 63 < 64 := fun n => by
    rw [nat_land_63]; exact Nat.mod_lt _ (by omega)
  set c0 := Nat.land m 63
  set c1 := Nat.land (Nat.shiftRight m 6) 63
  have hc0 : c0 < 64 := h63 m
  have hc1 : c1 < 64 := h63 (Nat.shiftRight m 6)
  have hv1 : v + 1 < 64 := by omega
  have hmon : evalMonP m = evalSlot c0 * evalSlot c1 := by
    unfold evalMonP; rw [hm2, evalSlot_zero, mul_one]
  unfold mulVarMon
  simp only [hm2, Nat.beq_eq, Nat.blt_eq]
  change PCDerivable (cnfSystem FpSet) 3 (X (pVar v) * evalMonP m + evalMonP (
    if c0 = 0 then v + 1
    else if c0 = v + 1 then m
    else if c1 = 0 then if v + 1 < c0 then (v + 1) + 64 * c0 else c0 + 64 * (v + 1)
    else if c1 = v + 1 then m
    else if v + 1 < c0 then (v + 1) + 64 * (c0 + 64 * c1)
    else if v + 1 < c1 then c0 + 64 * ((v + 1) + 64 * c1)
    else c0 + 64 * (c1 + 64 * (v + 1))))
  by_cases h0 : c0 = 0
  · simp only [h0, ↓reduceIte]
    have h1 : c1 = 0 := by
      rcases hm01 with hne | h1
      · exfalso; exact absurd (Nat.beq_eq.mpr h0) (by rw [hne]; decide)
      · exact h1
    have hs := nat_pack_slots_2 hv1 (show 0 < 64 by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at hs
    have heq : X (pVar v) * evalMonP m + evalMonP (v + 1) = 0 := by
      rw [hmon, h0, h1, evalSlot_zero, mul_one, mul_one]; unfold evalMonP
      rw [hs.1, hs.2.1, hs.2.2, evalSlot_succ, evalSlot_zero, mul_one, mul_one]
      exact zmod2_poly_add_self _
    rw [heq]; exact PCDerivable.zero
  · simp only [h0, ↓reduceIte]
    by_cases h0v : c0 = v + 1
    · simp only [h0v, ↓reduceIte]
      have heq : X (pVar v) * evalMonP m + evalMonP m = (X (pVar v) * X (pVar v) + X (pVar v)) * evalSlot c1 := by
        rw [hmon, h0v, evalSlot_succ]; ring
      rw [heq]; exact pc_bool_mul_slot (pVar v) c1
    · simp only [h0v, ↓reduceIte]
      by_cases h1 : c1 = 0
      · simp only [h1, ↓reduceIte]
        split_ifs with hlt
        · have hs := nat_pack_slots_2 hv1 hc0
          have heq : X (pVar v) * evalMonP m + evalMonP ((v + 1) + 64 * c0) = 0 := by
            rw [hmon, h1, evalSlot_zero, mul_one]; unfold evalMonP
            rw [hs.1, hs.2.1, hs.2.2, evalSlot_succ, evalSlot_zero, mul_one]
            exact zmod2_poly_add_self _
          rw [heq]; exact PCDerivable.zero
        · have hs := nat_pack_slots_2 hc0 hv1
          have heq : X (pVar v) * evalMonP m + evalMonP (c0 + 64 * (v + 1)) = 0 := by
            rw [hmon, h1, evalSlot_zero, mul_one]; unfold evalMonP
            rw [hs.1, hs.2.1, hs.2.2, evalSlot_succ, evalSlot_zero, mul_one, mul_comm (evalSlot c0)]
            exact zmod2_poly_add_self _
          rw [heq]; exact PCDerivable.zero
      · simp only [h1, ↓reduceIte]
        by_cases h1v : c1 = v + 1
        · simp only [h1v, ↓reduceIte]
          have heq : X (pVar v) * evalMonP m + evalMonP m = (X (pVar v) * X (pVar v) + X (pVar v)) * evalSlot c0 := by
            rw [hmon, h1v, evalSlot_succ]; ring
          rw [heq]; exact pc_bool_mul_slot (pVar v) c0
        · simp only [h1v, ↓reduceIte]
          split_ifs with hlt1 hlt2
          · have hs := nat_pack_slots_3 hv1 hc0 hc1
            have heq : X (pVar v) * evalMonP m + evalMonP ((v + 1) + 64 * (c0 + 64 * c1)) = 0 := by
              rw [hmon]; unfold evalMonP
              rw [hs.1, hs.2.1, hs.2.2, evalSlot_succ, mul_assoc]
              exact zmod2_poly_add_self _
            rw [heq]; exact PCDerivable.zero
          · have hs := nat_pack_slots_3 hc0 hv1 hc1
            have heq : X (pVar v) * evalMonP m + evalMonP (c0 + 64 * ((v + 1) + 64 * c1)) = 0 := by
              rw [hmon]; unfold evalMonP
              rw [hs.1, hs.2.1, hs.2.2, evalSlot_succ]
              have : X (pVar v) * (evalSlot c0 * evalSlot c1) = evalSlot c0 * X (pVar v) * evalSlot c1 := by ring
              rw [this]; exact zmod2_poly_add_self _
            rw [heq]; exact PCDerivable.zero
          · have hs := nat_pack_slots_3 hc0 hc1 hv1
            have heq : X (pVar v) * evalMonP m + evalMonP (c0 + 64 * (c1 + 64 * (v + 1))) = 0 := by
              rw [hmon]; unfold evalMonP
              rw [hs.1, hs.2.1, hs.2.2, evalSlot_succ]
              have : X (pVar v) * (evalSlot c0 * evalSlot c1) = evalSlot c0 * evalSlot c1 * X (pVar v) := by ring
              rw [this]; exact zmod2_poly_add_self _
            rw [heq]; exact PCDerivable.zero

private lemma pc_mulVarPolyAcc {v : ℕ} (hv : v < 55) (p acc : List ℕ) (hp : allDegLe2 p = true) :
    PCDerivable (cnfSystem FpSet) 3
      (evalPolyP (mulVarPolyAcc v acc p) + (evalPolyP acc + X (pVar v) * evalPolyP p)) := by
  induction p generalizing acc with
  | nil =>
    simp only [mulVarPolyAcc, evalPolyP, List.map_nil, List.sum_nil, mul_zero, add_zero, zmod2_poly_add_self]
    exact PCDerivable.zero
  | cons m ms ih =>
    simp only [allDegLe2, Bool.and_eq_true] at hp
    have h1 := ih (insMon (mulVarMon v m) acc) hp.2
    rw [evalPolyP_insMon] at h1
    have h2 := pc_mulVarMon_diff hv hp.1
    have hsum := PCDerivable.add h1 h2
    have heq : evalPolyP (mulVarPolyAcc v (insMon (mulVarMon v m) acc) ms) +
        (evalMonP (mulVarMon v m) + evalPolyP acc + X (pVar v) * evalPolyP ms) +
        (X (pVar v) * evalMonP m + evalMonP (mulVarMon v m)) =
        evalPolyP (mulVarPolyAcc v acc (m :: ms)) + (evalPolyP acc + X (pVar v) * evalPolyP (m :: ms)) := by
      simp only [mulVarPolyAcc, evalPolyP, List.map_cons, List.sum_cons, mul_add]
      have hz := zmod2_poly_add_self (evalMonP (mulVarMon v m))
      linear_combination hz
    rw [heq] at hsum
    exact hsum

private lemma pc_mulVarPoly {v : ℕ} (hv : v < 55) {p : List ℕ}
    (hp : PCDerivable (cnfSystem FpSet) 3 (evalPolyP p)) (hd : allDegLe2 p = true) :
    PCDerivable (cnfSystem FpSet) 3 (evalPolyP (mulVarPolyAcc v [] p)) := by
  have hmul : PCDerivable (cnfSystem FpSet) 3 (X (pVar v) * evalPolyP p) := by
    refine PCDerivable.mulX (pVar v) hp ?_
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (X (pVar v) : MvPolynomial (Fin 10 ⊕ (ℕ × ℕ)) (ZMod 2)).totalDegree = 1 := totalDegree_X _
    have h2 := evalPolyP_deg_le2 hd
    omega
  have hdiff := pc_mulVarPolyAcc hv p [] hd
  have hnil : evalPolyP [] = 0 := rfl
  rw [hnil, zero_add] at hdiff
  have hsum := PCDerivable.add hdiff hmul
  have heq : evalPolyP (mulVarPolyAcc v [] p) + X (pVar v) * evalPolyP p + X (pVar v) * evalPolyP p =
      evalPolyP (mulVarPolyAcc v [] p) := by
    rw [add_assoc, zmod2_poly_add_self, add_zero]
  rw [heq] at hsum
  exact hsum

private def clauseGoodP (c : List (ℕ × Bool)) : Bool :=
  Nat.ble c.length 3 && clauseAllLt 55 c &&
  (match c with
   | [] => true
   | [_] => true
   | [(v0, _), (v1, _)] => !Nat.beq v0 v1
   | [(v0, _), (v1, _), (v2, _)] => !Nat.beq v0 v1 && !Nat.beq v0 v2 && !Nat.beq v1 v2
   | _ => false) &&
  allDegLe2 (clauseToPoly c.tail)

private lemma fpAxList_good : fpAxList.all clauseGoodP = true := by decide +kernel

private lemma pc_clauseToPoly_diff_base (c : List (ℕ × Bool)) (hgood : clauseGoodP c = true) :
    PCDerivable (cnfSystem FpSet) 3 (evalPolyP (clauseToPoly c) + clausePoly (mkClause pVar c)) := by
  have hstep : ∀ (v : ℕ) (s : Bool) (tl : List (ℕ × Bool)),
      v < 55 → allDegLe2 (clauseToPoly tl) = true →
      (∀ x ∈ tl, x.1 < 55 ∧ x.1 ≠ v) →
      (clausePoly (mkClause pVar tl)).totalDegree ≤ 2 →
      PCDerivable (cnfSystem FpSet) 3 (evalPolyP (clauseToPoly tl) + clausePoly (mkClause pVar tl)) →
      PCDerivable (cnfSystem FpSet) 3
        (evalPolyP (clauseToPoly ((v, s) :: tl)) + clausePoly (mkClause pVar ((v, s) :: tl))) := by
    intro v s tl hv hdeg2 htl hcldeg ih
    have hnotmem : (pVar v, s) ∉ mkClause pVar tl := by
      simp only [mkClause, List.mem_toFinset, List.mem_map, not_exists, not_and]
      intro x hx heq
      have h1 : x.1 = v := pVar_inj_lt x.1 v (htl x hx).1 hv (congrArg Prod.fst heq)
      exact (htl x hx).2 h1
    have hcp : clausePoly (mkClause pVar ((v, s) :: tl)) = litPoly (pVar v, s) * clausePoly (mkClause pVar tl) := by
      have hmk : mkClause pVar ((v, s) :: tl) = insert (pVar v, s) (mkClause pVar tl) := by
        simp [mkClause]
      rw [hmk]; unfold clausePoly litPoly
      rw [Finset.prod_insert hnotmem]
    rw [hcp]
    have hdiff := pc_mulVarPolyAcc hv (clauseToPoly tl) [] hdeg2
    have hnil : evalPolyP [] = 0 := rfl
    rw [hnil, zero_add] at hdiff
    have hihdeg : (evalPolyP (clauseToPoly tl) + clausePoly (mkClause pVar tl)).totalDegree ≤ 2 :=
      (totalDegree_add _ _).trans (max_le (evalPolyP_deg_le2 hdeg2) hcldeg)
    have hihmul : PCDerivable (cnfSystem FpSet) 3
        (X (pVar v) * (evalPolyP (clauseToPoly tl) + clausePoly (mkClause pVar tl))) := by
      refine PCDerivable.mulX (pVar v) ih ?_
      refine (totalDegree_mul _ _).trans ?_
      have hxv : (X (pVar v) : MvPolynomial (Fin 10 ⊕ (ℕ × ℕ)) (ZMod 2)).totalDegree = 1 := totalDegree_X _
      omega
    cases s
    · simp only [clauseToPoly, Bool.false_eq_true, ↓reduceIte, litPoly]
      have hsum := PCDerivable.add hdiff hihmul
      have heq : evalPolyP (mulVarPolyAcc v [] (clauseToPoly tl)) + X (pVar v) * evalPolyP (clauseToPoly tl) +
          X (pVar v) * (evalPolyP (clauseToPoly tl) + clausePoly (mkClause pVar tl)) =
          evalPolyP (mulVarPolyAcc v [] (clauseToPoly tl)) + X (pVar v) * clausePoly (mkClause pVar tl) := by
        have hz := zmod2_poly_add_self (X (pVar v) * evalPolyP (clauseToPoly tl))
        linear_combination hz
      rw [heq] at hsum; exact hsum
    · simp only [clauseToPoly, ↓reduceIte, litPoly, evalPolyP_xorPoly]
      have hsum := PCDerivable.add (PCDerivable.add ih hdiff) hihmul
      have heq : evalPolyP (clauseToPoly tl) + clausePoly (mkClause pVar tl) +
          (evalPolyP (mulVarPolyAcc v [] (clauseToPoly tl)) + X (pVar v) * evalPolyP (clauseToPoly tl)) +
          X (pVar v) * (evalPolyP (clauseToPoly tl) + clausePoly (mkClause pVar tl)) =
          evalPolyP (clauseToPoly tl) + evalPolyP (mulVarPolyAcc v [] (clauseToPoly tl)) +
            (1 + X (pVar v)) * clausePoly (mkClause pVar tl) := by
        have hz := zmod2_poly_add_self (X (pVar v) * evalPolyP (clauseToPoly tl))
        linear_combination hz
      rw [heq] at hsum; exact hsum
  have hbase0 : PCDerivable (cnfSystem FpSet) 3 (evalPolyP (clauseToPoly []) + clausePoly (mkClause pVar [])) := by
    have heq : evalPolyP (clauseToPoly []) + clausePoly (mkClause pVar []) = 0 := by
      simp only [clauseToPoly, evalPolyP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        evalMonP, evalSlot, mkClause, List.toFinset_nil, clausePoly, Finset.prod_empty]
      simp [zmod2_poly_add_self]
    rw [heq]; exact PCDerivable.zero
  have hdeg0 : allDegLe2 (clauseToPoly []) = true := by decide
  have hdeg1 : ∀ (v : ℕ) (s : Bool), v < 55 → allDegLe2 (clauseToPoly [(v, s)]) = true := by
    have hfin : ∀ (v : Fin 55) (s : Bool), allDegLe2 (clauseToPoly [(v.val, s)]) = true := by decide
    intro v s hv
    exact hfin ⟨v, hv⟩ s
  rcases c with _ | ⟨⟨v0, s0⟩, _ | ⟨⟨v1, s1⟩, _ | ⟨⟨v2, s2⟩, _ | _⟩⟩⟩
  · exact hbase0
  · simp only [clauseGoodP, Bool.and_eq_true, clauseAllLt_iff] at hgood
    have hv0 : v0 < 55 := hgood.1.1.2 (v0, s0) (by simp)
    exact hstep v0 s0 [] hv0 hdeg0 (by simp) (by simp [mkClause, clausePoly]) hbase0
  · simp only [clauseGoodP, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, clauseAllLt_iff] at hgood
    have hv0 : v0 < 55 := hgood.1.1.2 (v0, s0) (by simp)
    have hv1 : v1 < 55 := hgood.1.1.2 (v1, s1) (by simp)
    have h01 : v1 ≠ v0 := by intro h; subst h; simp at hgood
    have h1 := hstep v1 s1 [] hv1 hdeg0 (by simp) (by simp [mkClause, clausePoly]) hbase0
    refine hstep v0 s0 [(v1, s1)] hv0 (hdeg1 v1 s1 hv1) (by simp [hv1, h01]) ?_ h1
    exact (clausePoly_totalDegree_le _).trans ((mkClause_card_le _ _).trans (by simp))
  · simp only [clauseGoodP, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, clauseAllLt_iff] at hgood
    have hv0 : v0 < 55 := hgood.1.1.2 (v0, s0) (by simp)
    have hv1 : v1 < 55 := hgood.1.1.2 (v1, s1) (by simp)
    have hv2 : v2 < 55 := hgood.1.1.2 (v2, s2) (by simp)
    have h01 : v1 ≠ v0 := by intro h; subst h; simp at hgood
    have h02 : v2 ≠ v0 := by intro h; subst h; simp at hgood
    have h12 : v2 ≠ v1 := by intro h; subst h; simp at hgood
    have h2 := hstep v2 s2 [] hv2 hdeg0 (by simp) (by simp [mkClause, clausePoly]) hbase0
    have h1 := hstep v1 s1 [(v2, s2)] hv1 (hdeg1 v2 s2 hv2) (by simp [hv2, h12])
      ((clausePoly_totalDegree_le _).trans ((mkClause_card_le _ _).trans (by simp))) h2
    refine hstep v0 s0 [(v1, s1), (v2, s2)] hv0 hgood.2 ?_ ?_ h1
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact ⟨by assumption, by assumption⟩
    · exact (clausePoly_totalDegree_le _).trans ((mkClause_card_le _ _).trans (by simp))
  · simp [clauseGoodP] at hgood

private lemma pc_fpAx_derivable {c : List (ℕ × Bool)} (hc : c ∈ fpAxList) :
    PCDerivable (cnfSystem FpSet) 3 (evalPolyP (clauseToPoly c)) := by
  have hgood : clauseGoodP c = true := List.all_eq_true.mp fpAxList_good c hc
  have hcl : PCDerivable (cnfSystem FpSet) 3 (clausePoly (mkClause pVar c)) := by
    have hlen : c.length ≤ 3 := by
      simp only [clauseGoodP, Bool.and_eq_true, Nat.ble_eq] at hgood
      exact hgood.1.1.1
    exact PCDerivable.ax (Or.inr ⟨mkClause pVar c, fpAxList_mem hc, rfl⟩)
      ((clausePoly_totalDegree_le _).trans ((mkClause_card_le _ _).trans hlen))
  have hdiff := pc_clauseToPoly_diff_base c hgood
  have hsum := PCDerivable.add hdiff hcl
  have heq : evalPolyP (clauseToPoly c) + clausePoly (mkClause pVar c) + clausePoly (mkClause pVar c) =
      evalPolyP (clauseToPoly c) := by
    rw [add_assoc, zmod2_poly_add_self, add_zero]
  rw [heq] at hsum; exact hsum

private lemma getPoly_mem_or_nil (i : ℕ) (st : List (List ℕ)) :
    getPoly i st = [] ∨ getPoly i st ∈ st := by
  induction st generalizing i with
  | nil => left; cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => right; simp [getPoly]
    | succ i =>
      rcases ih i with h | h
      · left; exact h
      · right; exact List.mem_cons_of_mem _ h

private lemma pc_applyXors (curLen : ℕ) (stRev : List (List ℕ))
    (hst : ∀ p ∈ stRev, PCDerivable (cnfSystem FpSet) 3 (evalPolyP p))
    (xors : List ℕ) :
    ∀ p, PCDerivable (cnfSystem FpSet) 3 (evalPolyP p) →
      PCDerivable (cnfSystem FpSet) 3 (evalPolyP (applyXors curLen stRev p xors)) := by
  induction xors with
  | nil => intro p hp; exact hp
  | cons idx xs ih =>
    intro p hp
    apply ih
    rw [evalPolyP_xorPoly]
    refine PCDerivable.add hp ?_
    rcases getPoly_mem_or_nil (curLen - 1 - idx) stRev with hnil | hmem
    · rw [hnil]; simp only [evalPolyP, List.map_nil, List.sum_nil]; exact PCDerivable.zero
    · exact hst _ hmem

private lemma runPCSteps_sound (steps : List (ℕ × ℕ × ℕ × List ℕ)) :
    ∀ (stRev : List (List ℕ)),
      (∀ p ∈ stRev, PCDerivable (cnfSystem FpSet) 3 (evalPolyP p)) →
      runPCSteps fpAxList stRev.length stRev steps = true →
      PCRefutable (cnfSystem FpSet) 3 := by
  induction steps with
  | nil =>
    intro stRev hst hrun
    cases stRev with
    | nil => simp [runPCSteps] at hrun
    | cons hd tl =>
      cases hd with
      | nil => simp [runPCSteps] at hrun
      | cons m ms =>
        cases m with
        | zero =>
          cases ms with
          | nil =>
            have h0 := hst [0] List.mem_cons_self
            have hev : evalPolyP [0] = 1 := by
              simp [evalPolyP, evalMonP, evalSlot]
            rw [hev] at h0; exact h0
          | cons _ _ => simp [runPCSteps] at hrun
        | succ _ => simp [runPCSteps] at hrun
  | cons st rest ih =>
    intro stRev hst hrun
    rcases st with ⟨kind, a1, a2, xors⟩
    simp only [runPCSteps] at hrun
    by_cases hk : Nat.beq kind 0 = true
    · rw [if_pos hk] at hrun
      by_cases hlt : (!Nat.blt a1 fpAxList.length) = true
      · rw [if_pos hlt] at hrun; simp at hrun
      · rw [if_neg hlt] at hrun
        have hp1 : PCDerivable (cnfSystem FpSet) 3
            (evalPolyP (applyXors stRev.length stRev (clauseToPoly (getCl a1 fpAxList)) xors)) :=
          pc_applyXors stRev.length stRev hst xors _ (pc_fpAx_derivable (getCl_mem (by
            cases hb : Nat.blt a1 fpAxList.length
            · simp [hb] at hlt
            · exact Nat.blt_eq.mp hb)))
        set p1 := applyXors stRev.length stRev (clauseToPoly (getCl a1 fpAxList)) xors
        have hst' : ∀ p ∈ p1 :: stRev, PCDerivable (cnfSystem FpSet) 3 (evalPolyP p) := by
          intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
          · exact hp1
          · exact hst p hp'
        cases hp1eq : p1 with
        | nil =>
          rw [hp1eq] at hrun hst'
          exact ih ([] :: stRev) hst' (by simpa [List.length_cons] using hrun)
        | cons h t =>
          rw [hp1eq] at hrun hst'
          exact ih ((h :: t) :: stRev) hst' (by simpa [List.length_cons] using hrun)
    · rw [if_neg hk] at hrun
      by_cases hbad : (!Nat.blt a1 55 || !Nat.blt a2 stRev.length) = true
      · rw [if_pos hbad] at hrun; simp at hrun
      · rw [if_neg hbad] at hrun
        by_cases hdeg : (!allDegLe2 (getPoly (stRev.length - 1 - a2) stRev)) = true
        · rw [if_pos hdeg] at hrun; simp at hrun
        · rw [if_neg hdeg] at hrun
          have ha1 : a1 < 55 := by
            cases hb : Nat.blt a1 55
            · simp [hb] at hbad
            · exact Nat.blt_eq.mp hb
          have hd : allDegLe2 (getPoly (stRev.length - 1 - a2) stRev) = true := by
            cases hb : allDegLe2 (getPoly (stRev.length - 1 - a2) stRev)
            · simp [hb] at hdeg
            · rfl
          have hsrc : PCDerivable (cnfSystem FpSet) 3 (evalPolyP (getPoly (stRev.length - 1 - a2) stRev)) := by
            rcases getPoly_mem_or_nil (stRev.length - 1 - a2) stRev with hnil | hmem
            · rw [hnil]; simp only [evalPolyP, List.map_nil, List.sum_nil]; exact PCDerivable.zero
            · exact hst _ hmem
          have hp1 : PCDerivable (cnfSystem FpSet) 3
              (evalPolyP (applyXors stRev.length stRev (mulVarPolyAcc a1 [] (getPoly (stRev.length - 1 - a2) stRev)) xors)) :=
            pc_applyXors stRev.length stRev hst xors _ (pc_mulVarPoly ha1 hsrc hd)
          set p1 := applyXors stRev.length stRev (mulVarPolyAcc a1 [] (getPoly (stRev.length - 1 - a2) stRev)) xors
          have hst' : ∀ p ∈ p1 :: stRev, PCDerivable (cnfSystem FpSet) 3 (evalPolyP p) := by
            intro p hp; rcases List.mem_cons.mp hp with rfl | hp'
            · exact hp1
            · exact hst p hp'
          cases hp1eq : p1 with
          | nil =>
            rw [hp1eq] at hrun hst'
            exact ih ([] :: stRev) hst' (by simpa [List.length_cons] using hrun)
          | cons h t =>
            rw [hp1eq] at hrun hst'
            exact ih ((h :: t) :: stRev) hst' (by simpa [List.length_cons] using hrun)

private def pcPSteps : List (ℕ × ℕ × ℕ × List ℕ) :=
[
  (0, 104, 0, []),
  (0, 11, 0, []),
  (1, 54, 1, []),
  (1, 7, 0, [2, 0]),
  (0, 63, 0, []),
  (1, 7, 4, []),
  (1, 49, 3, [5, 4]),
  (0, 91, 0, []),
  (1, 43, 6, [7]),
  (0, 103, 0, []),
  (0, 14, 0, []),
  (1, 49, 10, []),
  (1, 5, 9, [11, 9]),
  (1, 43, 12, []),
  (0, 10, 0, []),
  (1, 43, 14, []),
  (1, 5, 8, [13, 15, 8]),
  (0, 52, 0, []),
  (1, 5, 17, []),
  (1, 38, 16, [18, 17]),
  (0, 82, 0, []),
  (0, 29, 0, []),
  (0, 16, 0, []),
  (1, 20, 22, []),
  (0, 17, 0, []),
  (0, 1, 0, []),
  (1, 20, 25, []),
  (1, 1, 24, [26, 24]),
  (1, 1, 21, [23, 27, 22, 25]),
  (1, 4, 28, []),
  (0, 2, 0, []),
  (1, 20, 30, []),
  (1, 3, 24, [31]),
  (0, 72, 0, []),
  (1, 26, 24, []),
  (1, 26, 30, []),
  (1, 26, 32, [33, 34, 35]),
  (1, 4, 36, []),
  (0, 3, 0, []),
  (1, 26, 38, []),
  (1, 20, 38, []),
  (1, 26, 29, [37, 39, 40]),
  (0, 77, 0, []),
  (1, 26, 28, [36]),
  (1, 32, 43, []),
  (1, 32, 29, []),
  (1, 15, 25, []),
  (1, 2, 22, [46]),
  (0, 68, 0, []),
  (1, 21, 22, []),
  (1, 21, 25, []),
  (1, 21, 47, [48, 49, 50]),
  (0, 35, 0, []),
  (1, 15, 52, []),
  (1, 2, 52, []),
  (1, 26, 47, []),
  (1, 26, 22, []),
  (1, 26, 25, []),
  (0, 24, 0, []),
  (0, 15, 0, []),
  (1, 15, 59, []),
  (0, 0, 0, []),
  (1, 15, 61, []),
  (1, 0, 22, [62, 22]),
  (1, 0, 58, [60, 63, 59, 61]),
  (1, 26, 64, []),
  (1, 26, 51, [53, 54, 55, 56, 57, 52, 65]),
  (1, 2, 36, [34, 35, 31, 43, 66, 51, 24, 47, 22, 25]),
  (1, 32, 67, []),
  (1, 32, 64, []),
  (1, 32, 41, [42, 44, 45, 68, 69]),
  (1, 21, 64, [51]),
  (1, 1, 51, [49, 50, 46, 71]),
  (1, 10, 61, []),
  (1, 1, 59, [73]),
  (0, 64, 0, []),
  (1, 16, 59, []),
  (1, 16, 61, []),
  (1, 16, 74, [75, 76, 77]),
  (0, 30, 0, []),
  (1, 10, 79, []),
  (1, 1, 79, []),
  (1, 21, 74, []),
  (1, 21, 59, []),
  (1, 21, 61, []),
  (1, 21, 78, [80, 81, 82, 83, 84, 79]),
  (0, 4, 0, []),
  (1, 10, 86, []),
  (1, 4, 59, [87]),
  (1, 21, 88, []),
  (1, 4, 85, [89, 83]),
  (1, 21, 86, []),
  (1, 16, 88, []),
  (1, 4, 78, [92, 76]),
  (1, 4, 22, []),
  (1, 4, 74, []),
  (1, 4, 61, []),
  (1, 4, 72, [90, 91, 92, 76, 93, 94, 95, 87, 96, 85]),
  (1, 32, 97, []),
  (1, 32, 72, []),
  (1, 32, 78, []),
  (1, 4, 58, []),
  (1, 15, 86, []),
  (1, 15, 88, [101, 60, 102, 58]),
  (1, 32, 103, []),
  (1, 32, 22, []),
  (1, 32, 88, []),
  (1, 32, 74, []),
  (1, 32, 59, []),
  (1, 32, 61, []),
  (1, 4, 52, []),
  (1, 3, 64, []),
  (1, 3, 51, []),
  (1, 21, 30, []),
  (1, 15, 30, []),
  (1, 21, 111, [112, 113, 114]),
  (0, 73, 0, []),
  (1, 27, 71, []),
  (1, 27, 111, []),
  (1, 27, 115, [116, 117, 118]),
  (0, 41, 0, []),
  (1, 21, 120, []),
  (1, 15, 120, []),
  (1, 3, 120, []),
  (1, 32, 115, []),
  (1, 32, 71, []),
  (1, 32, 111, []),
  (1, 32, 119, [121, 122, 123, 124, 125, 126]),
  (1, 32, 38, []),
  (1, 3, 70, [128, 39, 70]),
  (1, 21, 70, [98, 99, 100, 104, 105, 106, 107, 108, 109, 110, 127, 69, 70, 129, 119, 41, 97, 115, 71, 72, 29, 32, 24, 78, 103, 111, 22, 88, 74, 59, 30, 61]),
  (1, 38, 130, []),
  (1, 38, 64, []),
  (0, 5, 0, []),
  (1, 10, 133, []),
  (1, 5, 59, [134]),
  (1, 21, 135, []),
  (1, 5, 85, [136, 83]),
  (1, 21, 133, []),
  (1, 16, 135, []),
  (1, 5, 78, [139, 76]),
  (1, 5, 22, []),
  (1, 5, 74, []),
  (1, 5, 61, []),
  (1, 5, 72, [137, 138, 139, 76, 140, 141, 142, 134, 143, 85]),
  (1, 32, 144, []),
  (1, 5, 127, [145, 99, 100, 105, 107]),
  (1, 32, 133, []),
  (1, 27, 144, []),
  (1, 27, 72, []),
  (1, 27, 78, []),
  (1, 27, 22, []),
  (1, 27, 74, []),
  (1, 5, 119, [148, 149, 150, 151, 152]),
  (1, 5, 28, []),
  (1, 5, 36, []),
  (1, 26, 154, [155]),
  (1, 5, 115, []),
  (1, 5, 58, []),
  (1, 15, 133, []),
  (1, 15, 135, [158, 60, 159, 58]),
  (1, 21, 160, []),
  (1, 5, 51, [161, 136, 83]),
  (1, 5, 32, []),
  (1, 5, 24, []),
  (1, 3, 160, []),
  (1, 3, 135, []),
  (1, 3, 59, []),
  (1, 5, 30, []),
  (1, 3, 133, []),
  (1, 5, 129, [146, 147, 109, 148, 149, 150, 151, 152, 153, 156, 157, 162, 138, 163, 164, 165, 166, 167, 168, 169, 127]),
  (1, 5, 67, []),
  (1, 32, 19, [20, 131, 132, 170, 129, 119, 171, 43, 51, 144, 115, 72, 32, 24, 78, 160, 22, 135, 74, 59, 30, 61]),
  (0, 13, 0, []),
  (1, 49, 173, []),
  (1, 6, 9, [174, 9]),
  (0, 58, 0, []),
  (1, 6, 176, []),
  (1, 44, 175, [177, 176]),
  (0, 87, 0, []),
  (1, 54, 176, []),
  (1, 44, 4, [180]),
  (1, 44, 0, []),
  (1, 9, 176, []),
  (0, 102, 0, []),
  (1, 44, 1, []),
  (1, 9, 184, [185]),
  (1, 9, 181, [182, 183, 186, 184]),
  (1, 38, 187, []),
  (1, 38, 178, [179, 188]),
  (1, 38, 173, []),
  (1, 8, 189, [190]),
  (1, 8, 130, []),
  (1, 8, 28, []),
  (1, 8, 36, []),
  (0, 8, 0, []),
  (1, 26, 195, []),
  (1, 20, 195, []),
  (1, 26, 193, [194, 196, 197]),
  (1, 8, 172, [191, 189, 192, 198, 43, 10, 172, 130]),
  (1, 48, 199, []),
  (0, 95, 0, []),
  (0, 18, 0, []),
  (1, 25, 38, []),
  (1, 4, 202, [203]),
  (0, 76, 0, []),
  (1, 31, 202, []),
  (1, 31, 38, []),
  (1, 31, 204, [205, 206, 207]),
  (0, 34, 0, []),
  (1, 25, 24, []),
  (1, 25, 30, []),
  (1, 2, 202, [211, 202]),
  (1, 2, 209, [210, 212, 24, 30]),
  (1, 31, 213, [208]),
  (0, 40, 0, []),
  (1, 20, 215, []),
  (1, 3, 215, []),
  (1, 31, 32, []),
  (1, 31, 24, []),
  (1, 31, 30, []),
  (1, 31, 28, []),
  (1, 31, 36, [216, 217, 218, 219, 220, 215, 221]),
  (1, 3, 208, [206, 207, 203, 214, 222, 36, 202, 32, 24, 30]),
  (1, 5, 223, []),
  (0, 81, 0, []),
  (1, 5, 213, []),
  (1, 37, 226, []),
  (1, 37, 154, []),
  (1, 37, 224, [225, 227, 228]),
  (1, 37, 14, []),
  (1, 31, 14, []),
  (1, 7, 229, [230, 231]),
  (0, 51, 0, []),
  (1, 7, 233, []),
  (1, 5, 233, []),
  (1, 31, 52, []),
  (1, 21, 215, [236]),
  (1, 15, 237, []),
  (1, 2, 237, []),
  (1, 31, 47, []),
  (1, 31, 22, []),
  (1, 31, 25, []),
  (1, 31, 64, []),
  (1, 31, 51, [238, 239, 240, 241, 242, 53, 54, 237, 243]),
  (0, 7, 0, []),
  (1, 31, 245, []),
  (1, 7, 52, []),
  (1, 7, 51, []),
  (1, 15, 245, []),
  (1, 7, 244, [246, 247, 248, 249]),
  (1, 42, 250, []),
  (1, 42, 224, []),
  (1, 42, 244, []),
  (1, 42, 52, []),
  (1, 42, 226, []),
  (1, 42, 51, []),
  (1, 42, 154, []),
  (1, 7, 64, []),
  (1, 42, 258, []),
  (1, 42, 64, []),
  (1, 42, 232, [234, 235, 251, 252, 253, 254, 255, 256, 257, 259, 233, 260]),
  (0, 90, 0, []),
  (1, 42, 229, [235, 252, 255, 257]),
  (1, 48, 263, []),
  (1, 48, 232, []),
  (1, 48, 229, []),
  (1, 48, 250, []),
  (1, 48, 244, []),
  (1, 48, 52, []),
  (1, 48, 51, []),
  (1, 48, 258, []),
  (1, 27, 97, []),
  (1, 27, 38, []),
  (1, 27, 86, []),
  (1, 27, 61, []),
  (1, 21, 38, []),
  (1, 4, 119, [272, 149, 150, 151, 152, 273, 274, 275, 276, 119]),
  (0, 46, 0, []),
  (1, 37, 120, []),
  (1, 27, 278, [279]),
  (1, 27, 233, []),
  (1, 42, 120, []),
  (1, 42, 280, [281, 282]),
  (1, 4, 283, []),
  (1, 42, 97, []),
  (1, 42, 72, []),
  (1, 42, 78, []),
  (1, 42, 103, []),
  (1, 42, 22, []),
  (1, 42, 88, []),
  (1, 42, 74, []),
  (1, 42, 59, []),
  (1, 42, 61, []),
  (1, 4, 280, []),
  (1, 4, 120, []),
  (1, 42, 278, []),
  (1, 32, 233, [296]),
  (1, 4, 297, []),
  (1, 42, 41, []),
  (1, 42, 43, []),
  (1, 42, 29, []),
  (1, 4, 278, []),
  (1, 42, 67, []),
  (1, 42, 70, [298, 299, 300, 301, 302, 303, 260]),
  (1, 42, 277, [284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 283, 304, 280, 120, 70, 277, 41, 43, 97, 72, 29, 78, 103, 22, 88, 74, 59, 61]),
  (1, 48, 305, []),
  (1, 48, 67, []),
  (1, 48, 261, [262, 264, 265, 266, 267, 268, 269, 270, 271, 306, 307]),
  (1, 48, 3, []),
  (1, 42, 3, []),
  (1, 54, 308, [309, 310]),
  (0, 9, 0, []),
  (1, 54, 312, []),
  (1, 4, 0, [313, 0]),
  (1, 42, 314, []),
  (1, 32, 314, []),
  (1, 54, 304, [315, 316]),
  (1, 26, 314, []),
  (1, 54, 70, [316, 318]),
  (1, 54, 67, []),
  (1, 54, 28, []),
  (1, 54, 64, []),
  (1, 37, 16, []),
  (1, 43, 224, []),
  (1, 43, 226, []),
  (1, 43, 154, []),
  (1, 43, 229, [323, 324, 325, 326]),
  (0, 86, 0, []),
  (1, 6, 16, []),
  (1, 6, 327, [328, 329]),
  (0, 12, 0, []),
  (1, 54, 331, []),
  (1, 6, 0, [332, 0]),
  (1, 43, 333, []),
  (1, 37, 333, []),
  (1, 43, 4, []),
  (1, 43, 3, []),
  (1, 54, 8, [336, 337]),
  (1, 37, 41, []),
  (1, 37, 43, []),
  (1, 37, 29, []),
  (1, 37, 67, []),
  (1, 37, 64, []),
  (1, 37, 70, [302, 339, 340, 341, 342, 343]),
  (1, 37, 314, []),
  (1, 54, 344, [345, 316]),
  (1, 43, 175, []),
  (1, 6, 8, [347]),
  (1, 6, 232, []),
  (1, 6, 229, []),
  (1, 6, 250, []),
  (1, 6, 244, []),
  (1, 6, 52, []),
  (0, 6, 0, []),
  (1, 15, 354, []),
  (1, 6, 22, [355]),
  (1, 21, 356, []),
  (1, 6, 51, [357, 49]),
  (1, 7, 356, []),
  (1, 7, 22, []),
  (1, 7, 354, []),
  (1, 7, 330, [348, 349, 350, 351, 352, 353, 357, 49, 358, 359, 360, 361, 8]),
  (1, 37, 97, []),
  (1, 37, 72, []),
  (1, 37, 78, []),
  (1, 37, 103, []),
  (1, 37, 22, []),
  (1, 37, 88, []),
  (1, 37, 74, []),
  (1, 37, 59, []),
  (1, 37, 61, []),
  (1, 37, 277, [294, 363, 364, 365, 366, 367, 368, 369, 370, 371, 295, 280, 344, 120, 70, 277, 41, 43, 97, 72, 29, 78, 103, 22, 88, 74, 59, 61]),
  (1, 6, 372, []),
  (1, 6, 67, []),
  (1, 43, 331, []),
  (1, 37, 331, []),
  (1, 9, 4, []),
  (1, 49, 0, [377]),
  (1, 43, 378, []),
  (1, 43, 1, []),
  (1, 9, 8, [379, 380]),
  (1, 32, 312, []),
  (1, 26, 312, []),
  (1, 9, 70, [382, 383]),
  (1, 9, 278, []),
  (1, 9, 67, []),
  (1, 37, 386, []),
  (1, 9, 28, []),
  (1, 37, 388, []),
  (1, 9, 64, []),
  (1, 37, 390, []),
  (1, 37, 28, []),
  (1, 37, 384, [385, 302, 387, 339, 340, 389, 341, 391, 278, 392]),
  (1, 9, 330, [375, 376, 381, 362, 330, 393, 373, 344, 384, 70, 386, 374, 388, 390, 258]),
  (1, 54, 330, [334, 335, 338, 346, 319, 320, 321, 322, 8, 362, 373, 374, 258, 394]),
  (1, 49, 17, []),
  (1, 7, 17, []),
  (1, 38, 175, []),
  (1, 49, 189, [398]),
  (1, 38, 8, [396, 397, 399]),
  (1, 21, 245, []),
  (1, 21, 258, [248, 401, 249]),
  (1, 32, 402, []),
  (1, 7, 127, [403, 125]),
  (1, 27, 402, []),
  (1, 7, 119, [405, 117]),
  (1, 20, 245, []),
  (1, 7, 24, [407]),
  (1, 26, 408, []),
  (1, 7, 36, [409, 34]),
  (1, 26, 245, []),
  (1, 7, 115, []),
  (1, 7, 32, []),
  (1, 7, 111, []),
  (1, 7, 30, []),
  (1, 7, 129, [404, 405, 117, 406, 410, 411, 412, 401, 413, 407, 414, 249, 415, 127]),
  (1, 7, 172, [400, 416, 129, 119, 36, 115, 408, 32, 24, 258, 111, 14, 30, 130, 67]),
  (0, 57, 0, []),
  (1, 48, 17, []),
  (1, 38, 418, [419]),
  (1, 48, 130, []),
  (1, 48, 64, []),
  (1, 48, 172, [420, 421, 307, 422]),
  (1, 48, 417, [308, 423, 17, 261, 263, 232, 229, 250, 244, 52, 51, 258]),
  (1, 37, 175, []),
  (1, 37, 12, []),
  (1, 31, 12, []),
  (1, 49, 229, [426, 427]),
  (1, 4, 4, []),
  (1, 49, 314, [429, 4]),
  (1, 25, 195, []),
  (1, 8, 202, [431]),
  (1, 25, 9, []),
  (1, 49, 202, []),
  (1, 49, 195, []),
  (1, 49, 432, [433, 434, 435]),
  (1, 49, 208, []),
  (1, 31, 9, []),
  (1, 31, 436, [437, 438]),
  (1, 49, 204, []),
  (1, 49, 38, []),
  (1, 31, 430, [439, 440, 434, 441]),
  (1, 32, 430, []),
  (1, 26, 430, []),
  (1, 49, 70, [443, 444]),
  (1, 49, 28, []),
  (1, 49, 64, []),
  (1, 49, 172, [399, 445, 446, 447, 12]),
  (1, 49, 330, [347, 425, 8, 428, 442, 436, 9, 430, 362, 373, 374, 258, 394, 448, 67, 28, 64]),
  (1, 54, 200, [201, 311, 317, 319, 320, 321, 322, 200, 395, 424, 305, 172, 130, 67, 28, 449, 417])
]

set_option maxHeartbeats 20000000 in
private lemma pcP_ok : runPCSteps fpAxList 0 [] pcPSteps = true := by decide +kernel

private lemma P3_pc3 : PCRefutable (cnfSystem FpSet) 3 :=
  runPCSteps_sound pcPSteps [] (by simp) pcP_ok

-- =========================================================================
-- Section 6: PC degree-3 lower bound for Fk (K4) via sparse dual quotient
-- =========================================================================

private def redB0 : ℕ → ℕ | 0 => 0x1 | 1 => 0x2 | 2 => 0x4 | 3 => 0x8 | 4 => 0x10 | 5 => 0x20 | 6 => 0x40 | 7 => 0x80 | 8 => 0x100 | 9 => 0x200 | 12 => 0x400 | 13 => 0x800 | 15 => 0x1000 | 16 => 0x2000 | 18 => 0x4000 | 19 => 0x8000 | 20 => 0x10000 | 21 => 0x1 | 22 => 0x20000 | 23 => 0x40000 | 24 => 0x1 | 25 => 0x80000 | 26 => 0x100000 | 27 => 0x1 | 28 => 0x200000 | 29 => 0x400000 | 30 => 0x800000 | 31 => 0x1000000 | 32 => 0x2000000 | 33 => 0x23 | 34 => 0x43 | 35 => 0x83 | 36 => 0x103 | 37 => 0x2 | 40 => 0x2 | 41 => 0x4000000 | 43 => 0x2 | 44 => 0x8000000 | 46 => 0x2 | 47 => 0x10000000 | 48 => 0x10000 | 49 => 0x2 | 50 => 0x20000000 | 51 => 0x40000 | 52 => 0x2 | 53 => 0x80003 | 54 => 0x100000 | 55 => 0x2 | 56 => 0x200003 | 57 => 0x400000 | 58 => 0x40000000 | 59 => 0x80000000 | 60 => 0x25 | 61 => 0x45 | 62 => 0x85 | 63 => 0x105 | _ => 0
private def redB1 : ℕ → ℕ | 0 => 0x100000000 | 3 => 0x4 | 4 => 0x200000000 | 6 => 0x4 | 7 => 0x400000000 | 9 => 0x4 | 10 => 0x800000000 | 11 => 0x10000 | 12 => 0x4 | 13 => 0x20000006 | 14 => 0x40000 | 15 => 0x4 | 16 => 0x80005 | 17 => 0x100000 | 18 => 0x4 | 19 => 0x200005 | 20 => 0x400000 | 21 => 0x1000000000 | 22 => 0x29 | 23 => 0x49 | 24 => 0x89 | 25 => 0x109 | 26 => 0x2000000000 | 29 => 0x4000000000 | 32 => 0x8 | 33 => 0x8000000000 | 35 => 0x8 | 36 => 0x10000000000 | 37 => 0x10000 | 38 => 0x8 | 39 => 0x2000000a | 40 => 0x40000 | 41 => 0x8 | 42 => 0x80009 | 43 => 0x100000 | 44 => 0x8 | 45 => 0x200009 | 46 => 0x400000 | 47 => 0x31 | 48 => 0x51 | 49 => 0x91 | 50 => 0x111 | 51 => 0x20000000000 | 54 => 0x40000000000 | 57 => 0x80000000000 | 58 => 0x100000000000 | 60 => 0x10 | 61 => 0x200000000000 | 62 => 0x10000 | 63 => 0x10 | _ => 0
private def redB2 : ℕ → ℕ | 0 => 0x20000012 | 1 => 0x40000 | 2 => 0x10 | 3 => 0x80011 | 4 => 0x100000 | 5 => 0x10 | 6 => 0x200011 | 7 => 0x400000 | 8 => 0x400000000000 | 9 => 0x800000000000 | 10 => 0x1000000000000 | 11 => 0x221 | 14 => 0x421 | 15 => 0x800 | 17 => 0x1021 | 18 => 0x100000002000 | 20 => 0x4021 | 21 => 0x2000000000000 | 23 => 0x20 | 24 => 0x20020023 | 25 => 0x4000000000000 | 26 => 0x20 | 27 => 0x20 | 28 => 0x8000000000000 | 29 => 0x20 | 30 => 0x20 | 31 => 0x10000000000000 | 32 => 0x20000000000000 | 33 => 0x40000000000000 | 34 => 0x241 | 37 => 0x441 | 38 => 0x800 | 40 => 0x1041 | 41 => 0x100000002000 | 43 => 0x4041 | 44 => 0x80000000000000 | 46 => 0x40 | 47 => 0x100000000000000 | 49 => 0x40 | 50 => 0x40 | 51 => 0x200000000000000 | 52 => 0x40 | 53 => 0x40 | 54 => 0x400000000000000 | 55 => 0x800000000000000 | 56 => 0x281 | 59 => 0x481 | 60 => 0x800 | 62 => 0x1081 | 63 => 0x100000002000 | _ => 0
private def redB3 : ℕ → ℕ | 1 => 0x4081 | 2 => 0x1000000000000000 | 4 => 0x80 | 5 => 0x2000000000000000 | 7 => 0x80 | 8 => 0x4000000000000000 | 10 => 0x80 | 11 => 0x80 | 12 => 0x8000000000000000 | 13 => 0x301 | 16 => 0x501 | 17 => 0x800 | 19 => 0x1101 | 20 => 0x100000002000 | 22 => 0x4101 | 23 => 0x10000000000000000 | 25 => 0x100 | 26 => 0x20000000000000000 | 28 => 0x100 | 29 => 0x40000000000000000 | 31 => 0x100 | 32 => 0x80000000000000000 | 36 => 0x200 | 37 => 0x100000000000000000 | 39 => 0x200 | 40 => 0x200000000000000000 | 42 => 0x200 | 43 => 0x400000000000000000 | 44 => 0x10000 | 45 => 0x200 | 46 => 0x20000202 | 47 => 0x40000 | 48 => 0x200 | 49 => 0x80201 | 50 => 0x100000 | 51 => 0x200 | 52 => 0x200201 | 53 => 0x400000 | _ => 0
private def redB4 : ℕ → ℕ | 27 => 0x800000000000000000 | 29 => 0x400 | 30 => 0x1000000000000000000 | 32 => 0x400 | 33 => 0x2000000000000000000 | 34 => 0x10000 | 35 => 0x400 | 36 => 0x20000402 | 37 => 0x40000 | 38 => 0x400 | 39 => 0x80401 | 40 => 0x100000 | 41 => 0x400 | 42 => 0x200401 | 43 => 0x400000 | 45 => 0x4000000000000000000 | 46 => 0x800 | 48 => 0x8000000000000000000 | 49 => 0x800 | 51 => 0x800 | 52 => 0x800 | 54 => 0x800 | 55 => 0x800 | 57 => 0x800 | 58 => 0x800 | _ => 0
private def redB5 : ℕ → ℕ | 11 => 0x10000000000000000000 | 13 => 0x1000 | 14 => 0x20000000000000000000 | 15 => 0x10000 | 16 => 0x1000 | 17 => 0x20001002 | 18 => 0x40000 | 19 => 0x1000 | 20 => 0x81001 | 21 => 0x100000 | 22 => 0x1000 | 23 => 0x201001 | 24 => 0x400000 | 26 => 0x40000000000000000000 | 27 => 0x2000 | 28 => 0x100000000000 | 29 => 0x2000 | 30 => 0x2000 | 31 => 0x100000000000 | 32 => 0x2000 | 33 => 0x2000 | 34 => 0x100000000000 | 35 => 0x2000 | 36 => 0x2000 | 37 => 0x100000000000 | 50 => 0x80000000000000000000 | 51 => 0x10000 | 52 => 0x4000 | 53 => 0x20004002 | 54 => 0x40000 | 55 => 0x4000 | 56 => 0x84001 | 57 => 0x100000 | 58 => 0x4000 | 59 => 0x204001 | 60 => 0x400000 | 61 => 0x100000000000000000000 | 62 => 0x8000 | 63 => 0x8000 | _ => 0
private def redB6 : ℕ → ℕ | 0 => 0x200000000000000000000 | 1 => 0x8000 | 2 => 0x8000 | 3 => 0x400000000000000000000 | 4 => 0x8000 | 5 => 0x8000 | 6 => 0x800000000000000000000 | 7 => 0x10000 | 8 => 0x1000000000000000000000 | 9 => 0x10000 | 10 => 0x10000 | 11 => 0x2000000000000000000000 | 12 => 0x10000 | 13 => 0x10000 | 14 => 0x4000000000000000000000 | 15 => 0x10000 | 16 => 0x20000 | 17 => 0x40000 | 18 => 0x1 | 19 => 0x80000 | 20 => 0x100000 | 21 => 0x1 | 22 => 0x200000 | 23 => 0x400000 | 24 => 0x8000000000000000000000 | 25 => 0x20000 | 26 => 0x20000 | 27 => 0x10000000000000000000000 | 28 => 0x20000 | 29 => 0x20000 | 30 => 0x20000000000000000000000 | 31 => 0x40000 | 32 => 0x40000000000000000000000 | 33 => 0x40000 | 34 => 0x40000 | 35 => 0x80000000000000000000000 | 36 => 0x40000 | 37 => 0x80000 | 38 => 0x100000 | 39 => 0x1 | 40 => 0x200000 | 41 => 0x400000 | 42 => 0x100000000000000000000000 | 43 => 0x80000 | 44 => 0x80000 | 45 => 0x200000000000000000000000 | 46 => 0x100000 | 47 => 0x400000000000000000000000 | 48 => 0x100000 | 49 => 0x200000 | 50 => 0x400000 | 51 => 0x800000000000000000000000 | 54 => 0x800021 | 55 => 0x800041 | 56 => 0x800081 | 57 => 0x800101 | 58 => 0x800000 | 61 => 0x800000 | _ => 0
private def redB7 : ℕ → ℕ | 0 => 0x800000 | 3 => 0x800000 | 5 => 0x10000 | 6 => 0x800000 | 7 => 0x20800002 | 8 => 0x40000 | 9 => 0x800000 | 10 => 0x880001 | 11 => 0x100000 | 12 => 0x800000 | 13 => 0xa00001 | 14 => 0x400000 | 16 => 0x1000021 | 17 => 0x1000041 | 18 => 0x1000081 | 19 => 0x1000101 | 20 => 0x1000000 | 23 => 0x1000000 | 26 => 0x1000000 | 29 => 0x1000000 | 31 => 0x10000 | 32 => 0x1000000 | 33 => 0x21000002 | 34 => 0x40000 | 35 => 0x1000000 | 36 => 0x1080001 | 37 => 0x100000 | 38 => 0x1000000 | 39 => 0x1200001 | 40 => 0x400000 | 41 => 0x2000021 | 42 => 0x2000041 | 43 => 0x2000081 | 44 => 0x2000101 | 45 => 0x2000000 | 48 => 0x2000000 | 51 => 0x2000000 | 52 => 0x100000000000 | 54 => 0x2000000 | 56 => 0x10000 | 57 => 0x2000000 | 58 => 0x22000002 | 59 => 0x40000 | 60 => 0x2000000 | 61 => 0x2080001 | 62 => 0x100000 | 63 => 0x2000000 | _ => 0
private def redB8 : ℕ → ℕ | 0 => 0x2200001 | 1 => 0x400000 | 2 => 0x400000000003 | 3 => 0x800000000003 | 4 => 0x1000000000003 | 5 => 0x23 | 8 => 0x23 | 9 => 0x4000000 | 11 => 0x23 | 12 => 0x100008000000 | 14 => 0x23 | 15 => 0x2000010008000 | 17 => 0x23 | 18 => 0x23 | 19 => 0x4000000000000 | 20 => 0x23 | 21 => 0x23 | 22 => 0x8000000000000 | 23 => 0x23 | 24 => 0x23 | 25 => 0x10000000000000 | 26 => 0x20000000000003 | 27 => 0x40000000000003 | 28 => 0x43 | 31 => 0x43 | 32 => 0x4000000 | 34 => 0x43 | 35 => 0x100008000000 | 37 => 0x43 | 38 => 0x80000010008000 | 40 => 0x43 | 41 => 0x100000020020000 | 43 => 0x43 | 44 => 0x43 | 45 => 0x200000000000000 | 46 => 0x43 | 47 => 0x43 | 48 => 0x400000000000000 | 49 => 0x800000000000003 | 50 => 0x83 | 53 => 0x83 | 54 => 0x4000000 | 56 => 0x83 | 57 => 0x100008000000 | 59 => 0x83 | 60 => 0x1000000010008000 | 62 => 0x83 | 63 => 0x2000000020020000 | _ => 0
private def redB9 : ℕ → ℕ | 1 => 0x83 | 2 => 0x4000000000000003 | 4 => 0x83 | 5 => 0x83 | 6 => 0x8000000000000000 | 7 => 0x103 | 10 => 0x103 | 11 => 0x4000000 | 13 => 0x103 | 14 => 0x100008000000 | 16 => 0x103 | 17 => 0x10000000010008000 | 19 => 0x103 | 20 => 0x20000000020020000 | 22 => 0x103 | 23 => 0x40000000000000003 | 25 => 0x103 | 26 => 0x80000000000000003 | 30 => 0x2 | 31 => 0x4000000 | 33 => 0x2 | 34 => 0x8000000 | 36 => 0x2 | 37 => 0x10000000 | 38 => 0x10000 | 39 => 0x2 | 40 => 0x20000000 | 41 => 0x40000 | 42 => 0x2 | 43 => 0x80003 | 44 => 0x100000 | 45 => 0x2 | 46 => 0x200003 | 47 => 0x400000 | _ => 0
private def redB10 : ℕ → ℕ | 21 => 0x4000000 | 23 => 0x2 | 24 => 0x8000000 | 26 => 0x2 | 27 => 0x10000000 | 28 => 0x10000 | 29 => 0x2 | 30 => 0x20000000 | 31 => 0x40000 | 32 => 0x2 | 33 => 0x80003 | 34 => 0x100000 | 35 => 0x2 | 36 => 0x200003 | 37 => 0x400000 | 39 => 0x4000000 | 40 => 0x4000000 | 42 => 0x4000000 | 43 => 0x4000000 | 45 => 0x4000000 | 46 => 0x4000000 | 48 => 0x4000000 | 49 => 0x4000000 | 51 => 0x4000000 | 52 => 0x4000000 | _ => 0
private def redB11 : ℕ → ℕ | 5 => 0x8000000 | 7 => 0x2 | 8 => 0x10000000 | 9 => 0x10000 | 10 => 0x2 | 11 => 0x20000000 | 12 => 0x40000 | 13 => 0x2 | 14 => 0x80003 | 15 => 0x100000 | 16 => 0x2 | 17 => 0x200003 | 18 => 0x400000 | 20 => 0x8000000 | 21 => 0x8000000 | 22 => 0x100000000000 | 23 => 0x8000000 | 24 => 0x8000000 | 25 => 0x100000000000 | 26 => 0x8000000 | 27 => 0x8000000 | 28 => 0x100000000000 | 29 => 0x8000000 | 30 => 0x8000000 | 31 => 0x100000000000 | 44 => 0x10000000 | 45 => 0x10000 | 46 => 0x2 | 47 => 0x20000000 | 48 => 0x40000 | 49 => 0x2 | 50 => 0x80003 | 51 => 0x100000 | 52 => 0x2 | 53 => 0x200003 | 54 => 0x400000 | 55 => 0x100000000000000000000 | 56 => 0x10000000 | 57 => 0x10000000 | 58 => 0x200000000000000000000 | 59 => 0x10000000 | 60 => 0x10000000 | 61 => 0x400000000000000000000 | 62 => 0x10000000 | 63 => 0x10000000 | _ => 0
private def redB12 : ℕ → ℕ | 0 => 0x800000000000000000000 | 1 => 0x10000 | 2 => 0x1000000000000000000000 | 3 => 0x10000 | 4 => 0x10000 | 5 => 0x2000000000000000000000 | 6 => 0x10000 | 7 => 0x10000 | 8 => 0x4000000000000000000000 | 9 => 0x10000 | 10 => 0x20000000 | 11 => 0x40000 | 12 => 0x2 | 13 => 0x80003 | 14 => 0x100000 | 15 => 0x2 | 16 => 0x200003 | 17 => 0x400000 | 18 => 0x8000000000000000000000 | 19 => 0x20000000 | 20 => 0x20000000 | 21 => 0x10000000000000000000000 | 22 => 0x20000000 | 23 => 0x20000000 | 24 => 0x20000000000000000000000 | 25 => 0x40000 | 26 => 0x40000000000000000000000 | 27 => 0x40000 | 28 => 0x40000 | 29 => 0x80000000000000000000000 | 30 => 0x40000 | 31 => 0x80003 | 32 => 0x100000 | 33 => 0x2 | 34 => 0x200003 | 35 => 0x400000 | 36 => 0x100000000000000000000000 | 37 => 0x80003 | 38 => 0x80003 | 39 => 0x200000000000000000000000 | 40 => 0x100000 | 41 => 0x400000000000000000000000 | 42 => 0x100000 | 43 => 0x200003 | 44 => 0x400000 | 45 => 0x800000000000000000000000 | 47 => 0x40000021 | 48 => 0x40000041 | 49 => 0x40000081 | 50 => 0x40000101 | 54 => 0x40000000 | 57 => 0x40000000 | 60 => 0x40000000 | 62 => 0x10000 | 63 => 0x40000000 | _ => 0
private def redB13 : ℕ → ℕ | 0 => 0x60000002 | 1 => 0x40000 | 2 => 0x40000000 | 3 => 0x40080001 | 4 => 0x100000 | 5 => 0x40000000 | 6 => 0x40200001 | 7 => 0x400000 | 8 => 0x80000021 | 9 => 0x80000041 | 10 => 0x80000081 | 11 => 0x80000101 | 15 => 0x80000000 | 18 => 0x80000000 | 19 => 0x100000000000 | 21 => 0x80000000 | 23 => 0x10000 | 24 => 0x80000000 | 25 => 0xa0000002 | 26 => 0x40000 | 27 => 0x80000000 | 28 => 0x80080001 | 29 => 0x100000 | 30 => 0x80000000 | 31 => 0x80200001 | 32 => 0x400000 | 33 => 0x400000000005 | 34 => 0x800000000005 | 35 => 0x1000000000005 | 36 => 0x100000021 | 39 => 0x25 | 40 => 0x200000000 | 42 => 0x25 | 43 => 0x100400000000 | 45 => 0x25 | 46 => 0x2000800008000 | 48 => 0x25 | 49 => 0x25 | 50 => 0x4000000000000 | 51 => 0x25 | 52 => 0x25 | 53 => 0x8000000000000 | 54 => 0x25 | 55 => 0x25 | 56 => 0x10000000000000 | 57 => 0x20000000000005 | 58 => 0x40000000000005 | 59 => 0x100000041 | 62 => 0x45 | 63 => 0x200000000 | _ => 0
private def redB14 : ℕ → ℕ | 1 => 0x45 | 2 => 0x100400000000 | 4 => 0x45 | 5 => 0x80000800008000 | 7 => 0x45 | 8 => 0x100000020020006 | 10 => 0x45 | 11 => 0x45 | 12 => 0x200000000000000 | 13 => 0x45 | 14 => 0x45 | 15 => 0x400000000000000 | 16 => 0x800000000000005 | 17 => 0x100000081 | 20 => 0x85 | 21 => 0x200000000 | 23 => 0x85 | 24 => 0x100400000000 | 26 => 0x85 | 27 => 0x1000000800008000 | 29 => 0x85 | 30 => 0x2000000020020006 | 32 => 0x85 | 33 => 0x4000000000000005 | 35 => 0x85 | 36 => 0x85 | 37 => 0x8000000000000000 | 38 => 0x100000101 | 41 => 0x105 | 42 => 0x200000000 | 44 => 0x105 | 45 => 0x100400000000 | 47 => 0x105 | 48 => 0x10000000800008000 | 50 => 0x105 | 51 => 0x20000000020020006 | 53 => 0x105 | 54 => 0x40000000000000005 | 56 => 0x105 | 57 => 0x80000000000000005 | 61 => 0x100000000 | 62 => 0x100000000 | _ => 0
private def redB15 : ℕ → ℕ | 0 => 0x100000000 | 3 => 0x100000000 | 5 => 0x10000 | 6 => 0x100000000 | 7 => 0x120000002 | 8 => 0x40000 | 9 => 0x100000000 | 10 => 0x100080001 | 11 => 0x100000 | 12 => 0x100000000 | 13 => 0x100200001 | 14 => 0x400000 | 52 => 0x200000000 | 54 => 0x4 | 55 => 0x400000000 | 57 => 0x4 | 58 => 0x800000000 | 59 => 0x10000 | 60 => 0x4 | 61 => 0x20000006 | 62 => 0x40000 | 63 => 0x4 | _ => 0
private def redB16 : ℕ → ℕ | 0 => 0x80005 | 1 => 0x100000 | 2 => 0x4 | 3 => 0x200005 | 4 => 0x400000 | 6 => 0x200000000 | 7 => 0x200000000 | 9 => 0x200000000 | 10 => 0x200000000 | 12 => 0x200000000 | 13 => 0x200000000 | 15 => 0x200000000 | 16 => 0x200000000 | 18 => 0x200000000 | 19 => 0x200000000 | 36 => 0x400000000 | 38 => 0x4 | 39 => 0x800000000 | 40 => 0x10000 | 41 => 0x4 | 42 => 0x20000006 | 43 => 0x40000 | 44 => 0x4 | 45 => 0x80005 | 46 => 0x100000 | 47 => 0x4 | 48 => 0x200005 | 49 => 0x400000 | 51 => 0x400000000 | 52 => 0x400000000 | 53 => 0x100000000000 | 54 => 0x400000000 | 55 => 0x400000000 | 56 => 0x100000000000 | 57 => 0x400000000 | 58 => 0x400000000 | 59 => 0x100000000000 | 60 => 0x400000000 | 61 => 0x400000000 | 62 => 0x100000000000 | _ => 0
private def redB17 : ℕ → ℕ | 11 => 0x800000000 | 12 => 0x10000 | 13 => 0x4 | 14 => 0x20000006 | 15 => 0x40000 | 16 => 0x4 | 17 => 0x80005 | 18 => 0x100000 | 19 => 0x4 | 20 => 0x200005 | 21 => 0x400000 | 22 => 0x100000000000000000000 | 23 => 0x800000000 | 24 => 0x800000000 | 25 => 0x200000000000000000000 | 26 => 0x800000000 | 27 => 0x800000000 | 28 => 0x400000000000000000000 | 29 => 0x800000000 | 30 => 0x800000000 | 31 => 0x800000000000000000000 | 32 => 0x10000 | 33 => 0x1000000000000000000000 | 34 => 0x10000 | 35 => 0x10000 | 36 => 0x2000000000000000000000 | 37 => 0x10000 | 38 => 0x10000 | 39 => 0x4000000000000000000000 | 40 => 0x10000 | 41 => 0x20000006 | 42 => 0x40000 | 43 => 0x4 | 44 => 0x80005 | 45 => 0x100000 | 46 => 0x4 | 47 => 0x200005 | 48 => 0x400000 | 49 => 0x8000000000000000000000 | 50 => 0x20000006 | 51 => 0x20000006 | 52 => 0x10000000000000000000000 | 53 => 0x20000006 | 54 => 0x20000006 | 55 => 0x20000000000000000000000 | 56 => 0x40000 | 57 => 0x40000000000000000000000 | 58 => 0x40000 | 59 => 0x40000 | 60 => 0x80000000000000000000000 | 61 => 0x40000 | 62 => 0x80005 | 63 => 0x100000 | _ => 0
private def redB18 : ℕ → ℕ | 0 => 0x4 | 1 => 0x200005 | 2 => 0x400000 | 3 => 0x100000000000000000000000 | 4 => 0x80005 | 5 => 0x80005 | 6 => 0x200000000000000000000000 | 7 => 0x100000 | 8 => 0x400000000000000000000000 | 9 => 0x100000 | 10 => 0x200005 | 11 => 0x400000 | 12 => 0x800000000000000000000000 | 13 => 0x1000000021 | 14 => 0x1000000041 | 15 => 0x1000000081 | 16 => 0x1000000101 | 23 => 0x1000000000 | 24 => 0x100000000000 | 26 => 0x1000000000 | 28 => 0x10000 | 29 => 0x1000000000 | 30 => 0x1020000002 | 31 => 0x40000 | 32 => 0x1000000000 | 33 => 0x1000080001 | 34 => 0x100000 | 35 => 0x1000000000 | 36 => 0x1000200001 | 37 => 0x400000 | 38 => 0x400000000009 | 39 => 0x800000000009 | 40 => 0x1000000000009 | 41 => 0x2000000021 | 44 => 0x4000000021 | 47 => 0x29 | 48 => 0x108000000000 | 50 => 0x29 | 51 => 0x2010000008000 | 53 => 0x29 | 54 => 0x29 | 55 => 0x4000000000000 | 56 => 0x29 | 57 => 0x29 | 58 => 0x8000000000000 | 59 => 0x29 | 60 => 0x29 | 61 => 0x10000000000000 | 62 => 0x20000000000009 | 63 => 0x40000000000009 | _ => 0
private def redB19 : ℕ → ℕ | 0 => 0x2000000041 | 3 => 0x4000000041 | 6 => 0x49 | 7 => 0x108000000000 | 9 => 0x49 | 10 => 0x80010000008000 | 12 => 0x49 | 13 => 0x10000002002000a | 15 => 0x49 | 16 => 0x49 | 17 => 0x200000000000000 | 18 => 0x49 | 19 => 0x49 | 20 => 0x400000000000000 | 21 => 0x800000000000009 | 22 => 0x2000000081 | 25 => 0x4000000081 | 28 => 0x89 | 29 => 0x108000000000 | 31 => 0x89 | 32 => 0x1000010000008000 | 34 => 0x89 | 35 => 0x200000002002000a | 37 => 0x89 | 38 => 0x4000000000000009 | 40 => 0x89 | 41 => 0x89 | 42 => 0x8000000000000000 | 43 => 0x2000000101 | 46 => 0x4000000101 | 49 => 0x109 | 50 => 0x108000000000 | 52 => 0x109 | 53 => 0x10000010000008000 | 55 => 0x109 | 56 => 0x2000000002002000a | 58 => 0x109 | 59 => 0x40000000000000009 | 61 => 0x109 | 62 => 0x80000000000000009 | _ => 0
private def redB20 : ℕ → ℕ | 2 => 0x2000000000 | 5 => 0x2000000000 | 8 => 0x2000000000 | 10 => 0x10000 | 11 => 0x2000000000 | 12 => 0x2020000002 | 13 => 0x40000 | 14 => 0x2000000000 | 15 => 0x2000080001 | 16 => 0x100000 | 17 => 0x2000000000 | 18 => 0x2000200001 | 19 => 0x400000 | 59 => 0x4000000000 | 60 => 0x4000000000 | 62 => 0x4000000000 | _ => 0
private def redB21 : ℕ → ℕ | 0 => 0x10000 | 1 => 0x4000000000 | 2 => 0x4020000002 | 3 => 0x40000 | 4 => 0x4000000000 | 5 => 0x4000080001 | 6 => 0x100000 | 7 => 0x4000000000 | 8 => 0x4000200001 | 9 => 0x400000 | 41 => 0x8000000000 | 43 => 0x8 | 44 => 0x10000000000 | 45 => 0x10000 | 46 => 0x8 | 47 => 0x2000000a | 48 => 0x40000 | 49 => 0x8 | 50 => 0x80009 | 51 => 0x100000 | 52 => 0x8 | 53 => 0x200009 | 54 => 0x400000 | 56 => 0x8000000000 | 57 => 0x8000000000 | 58 => 0x100000000000 | 59 => 0x8000000000 | 60 => 0x8000000000 | 61 => 0x100000000000 | 62 => 0x8000000000 | 63 => 0x8000000000 | _ => 0
private def redB22 : ℕ → ℕ | 0 => 0x100000000000 | 1 => 0x8000000000 | 2 => 0x8000000000 | 3 => 0x100000000000 | 16 => 0x10000000000 | 17 => 0x10000 | 18 => 0x8 | 19 => 0x2000000a | 20 => 0x40000 | 21 => 0x8 | 22 => 0x80009 | 23 => 0x100000 | 24 => 0x8 | 25 => 0x200009 | 26 => 0x400000 | 27 => 0x100000000000000000000 | 28 => 0x10000000000 | 29 => 0x10000000000 | 30 => 0x200000000000000000000 | 31 => 0x10000000000 | 32 => 0x10000000000 | 33 => 0x400000000000000000000 | 34 => 0x10000000000 | 35 => 0x10000000000 | 36 => 0x800000000000000000000 | 37 => 0x10000 | 38 => 0x1000000000000000000000 | 39 => 0x10000 | 40 => 0x10000 | 41 => 0x2000000000000000000000 | 42 => 0x10000 | 43 => 0x10000 | 44 => 0x4000000000000000000000 | 45 => 0x10000 | 46 => 0x2000000a | 47 => 0x40000 | 48 => 0x8 | 49 => 0x80009 | 50 => 0x100000 | 51 => 0x8 | 52 => 0x200009 | 53 => 0x400000 | 54 => 0x8000000000000000000000 | 55 => 0x2000000a | 56 => 0x2000000a | 57 => 0x10000000000000000000000 | 58 => 0x2000000a | 59 => 0x2000000a | 60 => 0x20000000000000000000000 | 61 => 0x40000 | 62 => 0x40000000000000000000000 | 63 => 0x40000 | _ => 0
private def redB23 : ℕ → ℕ | 0 => 0x40000 | 1 => 0x80000000000000000000000 | 2 => 0x40000 | 3 => 0x80009 | 4 => 0x100000 | 5 => 0x8 | 6 => 0x200009 | 7 => 0x400000 | 8 => 0x100000000000000000000000 | 9 => 0x80009 | 10 => 0x80009 | 11 => 0x200000000000000000000000 | 12 => 0x100000 | 13 => 0x400000000000000000000000 | 14 => 0x100000 | 15 => 0x200009 | 16 => 0x400000 | 17 => 0x800000000000000000000000 | 18 => 0x400000000011 | 19 => 0x800000000011 | 20 => 0x1000000000011 | 21 => 0x20000000021 | 24 => 0x40000000021 | 27 => 0x80000000021 | 30 => 0x31 | 31 => 0x2200000008000 | 33 => 0x31 | 34 => 0x31 | 35 => 0x4000000000000 | 36 => 0x31 | 37 => 0x31 | 38 => 0x8000000000000 | 39 => 0x31 | 40 => 0x31 | 41 => 0x10000000000000 | 42 => 0x20000000000011 | 43 => 0x40000000000011 | 44 => 0x20000000041 | 47 => 0x40000000041 | 50 => 0x80000000041 | 53 => 0x51 | 54 => 0x80200000008000 | 56 => 0x51 | 57 => 0x100000020020012 | 59 => 0x51 | 60 => 0x51 | 61 => 0x200000000000000 | 62 => 0x51 | 63 => 0x51 | _ => 0
private def redB24 : ℕ → ℕ | 0 => 0x400000000000000 | 1 => 0x800000000000011 | 2 => 0x20000000081 | 5 => 0x40000000081 | 8 => 0x80000000081 | 11 => 0x91 | 12 => 0x1000200000008000 | 14 => 0x91 | 15 => 0x2000000020020012 | 17 => 0x91 | 18 => 0x4000000000000011 | 20 => 0x91 | 21 => 0x91 | 22 => 0x8000000000000000 | 23 => 0x20000000101 | 26 => 0x40000000101 | 29 => 0x80000000101 | 32 => 0x111 | 33 => 0x10000200000008000 | 35 => 0x111 | 36 => 0x20000000020020012 | 38 => 0x111 | 39 => 0x40000000000000011 | 41 => 0x111 | 42 => 0x80000000000000011 | 46 => 0x20000000000 | 49 => 0x20000000000 | 50 => 0x100000000000 | 52 => 0x20000000000 | 54 => 0x10000 | 55 => 0x20000000000 | 56 => 0x20020000002 | 57 => 0x40000 | 58 => 0x20000000000 | 59 => 0x20000080001 | 60 => 0x100000 | 61 => 0x20000000000 | 62 => 0x20000200001 | 63 => 0x400000 | _ => 0
private def redB25 : ℕ → ℕ | 39 => 0x40000000000 | 40 => 0x100000000000 | 42 => 0x40000000000 | 44 => 0x10000 | 45 => 0x40000000000 | 46 => 0x40020000002 | 47 => 0x40000 | 48 => 0x40000000000 | 49 => 0x40000080001 | 50 => 0x100000 | 51 => 0x40000000000 | 52 => 0x40000200001 | 53 => 0x400000 | _ => 0
private def redB26 : ℕ → ℕ | 21 => 0x100000000000 | 23 => 0x80000000000 | 24 => 0x80000000000 | 25 => 0x10000 | 26 => 0x80000000000 | 27 => 0x80020000002 | 28 => 0x40000 | 29 => 0x80000000000 | 30 => 0x80000080001 | 31 => 0x100000 | 32 => 0x80000000000 | 33 => 0x80000200001 | 34 => 0x400000 | 36 => 0x100000000000 | 37 => 0x100000000000 | 38 => 0x100000000000 | 39 => 0x100000000000 | 40 => 0x100000000000 | 41 => 0x100000000000 | 42 => 0x100000000000 | 43 => 0x100000000000 | 44 => 0x100000000000 | 45 => 0x100000000000 | 46 => 0x100000000000 | 47 => 0x100000000000 | 60 => 0x200000000000 | 61 => 0x10000 | 62 => 0x10 | 63 => 0x20000012 | _ => 0
private def redB27 : ℕ → ℕ | 0 => 0x40000 | 1 => 0x10 | 2 => 0x80011 | 3 => 0x100000 | 4 => 0x10 | 5 => 0x200011 | 6 => 0x400000 | 7 => 0x100000000000000000000 | 8 => 0x200000000000 | 9 => 0x200000000000 | 10 => 0x200000000000000000000 | 11 => 0x200000000000 | 12 => 0x200000000000 | 13 => 0x400000000000000000000 | 14 => 0x200000000000 | 15 => 0x200000000000 | 16 => 0x800000000000000000000 | 17 => 0x10000 | 18 => 0x1000000000000000000000 | 19 => 0x10000 | 20 => 0x10000 | 21 => 0x2000000000000000000000 | 22 => 0x10000 | 23 => 0x10000 | 24 => 0x4000000000000000000000 | 25 => 0x10000 | 26 => 0x20000012 | 27 => 0x40000 | 28 => 0x10 | 29 => 0x80011 | 30 => 0x100000 | 31 => 0x10 | 32 => 0x200011 | 33 => 0x400000 | 34 => 0x8000000000000000000000 | 35 => 0x20000012 | 36 => 0x20000012 | 37 => 0x10000000000000000000000 | 38 => 0x20000012 | 39 => 0x20000012 | 40 => 0x20000000000000000000000 | 41 => 0x40000 | 42 => 0x40000000000000000000000 | 43 => 0x40000 | 44 => 0x40000 | 45 => 0x80000000000000000000000 | 46 => 0x40000 | 47 => 0x80011 | 48 => 0x100000 | 49 => 0x10 | 50 => 0x200011 | 51 => 0x400000 | 52 => 0x100000000000000000000000 | 53 => 0x80011 | 54 => 0x80011 | 55 => 0x200000000000000000000000 | 56 => 0x100000 | 57 => 0x400000000000000000000000 | 58 => 0x100000 | 59 => 0x200011 | 60 => 0x400000 | 61 => 0x800000000000000000000000 | _ => 0
private def redB28 : ℕ → ℕ | 0 => 0x400000000201 | 3 => 0x400000000401 | 4 => 0x800 | 6 => 0x400000001001 | 7 => 0x100000002000 | 9 => 0x400000004001 | 12 => 0x400000000000 | 13 => 0x400020020003 | 15 => 0x400000000000 | 16 => 0x400000000000 | 18 => 0x400000000000 | 19 => 0x400000000000 | 22 => 0x800000000201 | 25 => 0x800000000401 | 26 => 0x800 | 28 => 0x800000001001 | 29 => 0x100000002000 | 31 => 0x800000004001 | 34 => 0x800000000000 | 35 => 0x800020020003 | 37 => 0x800000000000 | 38 => 0x800000000000 | 40 => 0x800000000000 | 41 => 0x800000000000 | 43 => 0x1000000000201 | 46 => 0x1000000000401 | 47 => 0x800 | 49 => 0x1000000001001 | 50 => 0x100000002000 | 52 => 0x1000000004001 | 55 => 0x1000000000000 | 56 => 0x1000020020003 | 58 => 0x1000000000000 | 59 => 0x1000000000000 | 61 => 0x1000000000000 | 62 => 0x1000000000000 | _ => 0
private def redB29 : ℕ → ℕ | 2 => 0x221 | 3 => 0x100000000000000000 | 5 => 0x221 | 6 => 0x200000100000000000 | 8 => 0x221 | 9 => 0x400002000000008000 | 11 => 0x221 | 12 => 0x221 | 13 => 0x4000000000000 | 14 => 0x221 | 15 => 0x221 | 16 => 0x8000000000000 | 17 => 0x221 | 18 => 0x221 | 19 => 0x10000000000000 | 57 => 0x800000000000000000 | 59 => 0x421 | 60 => 0x1000000100000000000 | 62 => 0x421 | 63 => 0x2000002000000008000 | _ => 0
private def redB30 : ℕ → ℕ | 1 => 0x421 | 2 => 0x421 | 3 => 0x4000000000000 | 4 => 0x421 | 5 => 0x421 | 6 => 0x8000000000000 | 7 => 0x421 | 8 => 0x421 | 9 => 0x10000000000000 | 11 => 0x4000000000000000000 | 12 => 0x800 | 14 => 0x8000000000000000000 | 15 => 0x800 | 17 => 0x800 | 18 => 0x800 | 20 => 0x800 | 21 => 0x800 | 23 => 0x800 | 24 => 0x800 | 41 => 0x10000000100000000000 | 43 => 0x1021 | 44 => 0x20000002000000008000 | 46 => 0x1021 | 47 => 0x1021 | 48 => 0x4000000000000 | 49 => 0x1021 | 50 => 0x1021 | 51 => 0x8000000000000 | 52 => 0x1021 | 53 => 0x1021 | 54 => 0x10000000000000 | 56 => 0x40000000100000000000 | 57 => 0x100000002000 | 59 => 0x100000002000 | 60 => 0x100000002000 | 62 => 0x100000002000 | 63 => 0x100000002000 | _ => 0
private def redB31 : ℕ → ℕ | 1 => 0x100000002000 | 2 => 0x100000002000 | 16 => 0x80000002000000008000 | 18 => 0x4021 | 19 => 0x4021 | 20 => 0x4000000000000 | 21 => 0x4021 | 22 => 0x4021 | 23 => 0x8000000000000 | 24 => 0x4021 | 25 => 0x4021 | 26 => 0x10000000000000 | 28 => 0x2000000000000 | 29 => 0x2000000000000 | 30 => 0x2000000000000 | 31 => 0x2000000000000 | 32 => 0x2000000000000 | 34 => 0x2000000000000 | 35 => 0x2000000000000 | 46 => 0x20020023 | 47 => 0x4000000000000 | 48 => 0x20 | 49 => 0x20 | 50 => 0x8000000000000 | 51 => 0x20 | 52 => 0x20 | 53 => 0x10000000000000 | 54 => 0x4000000000000 | 55 => 0x20020023 | 56 => 0x20020023 | 57 => 0x8000000000000 | 58 => 0x20020023 | 59 => 0x20020023 | 60 => 0x10000000000000 | 61 => 0x4000000000000 | 62 => 0x4000000000000 | 63 => 0x4000000000000 | _ => 0
private def redB32 : ℕ → ℕ | 0 => 0x4000000000000 | 1 => 0x4000000000000 | 2 => 0x4000000000000 | 3 => 0x20 | 4 => 0x8000000000000 | 5 => 0x20 | 6 => 0x20 | 7 => 0x10000000000000 | 8 => 0x8000000000000 | 9 => 0x20 | 10 => 0x20 | 11 => 0x10000000000000 | 12 => 0x8000000000000 | 13 => 0x8000000000000 | 14 => 0x8000000000000 | 15 => 0x20 | 16 => 0x10000000000000 | 17 => 0x10000000000000 | 19 => 0x20000000000201 | 22 => 0x20000000000401 | 23 => 0x800 | 25 => 0x20000000001001 | 26 => 0x100000002000 | 28 => 0x20000000004001 | 31 => 0x20000000000000 | 34 => 0x20000000000000 | 35 => 0x20000000000000 | 37 => 0x20000000000000 | 38 => 0x20000000000000 | 40 => 0x40000000000201 | 43 => 0x40000000000401 | 44 => 0x800 | 46 => 0x40000000001001 | 47 => 0x100000002000 | 49 => 0x40000000004001 | 52 => 0x40000000000000 | 55 => 0x40000000000000 | 56 => 0x40000000000000 | 58 => 0x40000000000000 | 59 => 0x40000000000000 | 63 => 0x241 | _ => 0
private def redB33 : ℕ → ℕ | 0 => 0x100000000000000000 | 2 => 0x241 | 3 => 0x200000100000000000 | 5 => 0x241 | 6 => 0x400080000000008000 | 8 => 0x241 | 9 => 0x100000020020202 | 11 => 0x241 | 12 => 0x241 | 13 => 0x200000000000000 | 14 => 0x241 | 15 => 0x241 | 16 => 0x400000000000000 | 54 => 0x800000000000000000 | 56 => 0x441 | 57 => 0x1000000100000000000 | 59 => 0x441 | 60 => 0x2000080000000008000 | 62 => 0x441 | 63 => 0x100000020020402 | _ => 0
private def redB34 : ℕ → ℕ | 1 => 0x441 | 2 => 0x441 | 3 => 0x200000000000000 | 4 => 0x441 | 5 => 0x441 | 6 => 0x400000000000000 | 8 => 0x4000000000000000000 | 9 => 0x800 | 11 => 0x8000000000000000000 | 12 => 0x800 | 14 => 0x800 | 15 => 0x800 | 17 => 0x800 | 18 => 0x800 | 20 => 0x800 | 21 => 0x800 | 38 => 0x10000000100000000000 | 40 => 0x1041 | 41 => 0x20000080000000008000 | 43 => 0x1041 | 44 => 0x100000020021002 | 46 => 0x1041 | 47 => 0x1041 | 48 => 0x200000000000000 | 49 => 0x1041 | 50 => 0x1041 | 51 => 0x400000000000000 | 53 => 0x40000000100000000000 | 54 => 0x100000002000 | 56 => 0x100000002000 | 57 => 0x100000002000 | 59 => 0x100000002000 | 60 => 0x100000002000 | 62 => 0x100000002000 | 63 => 0x100000002000 | _ => 0
private def redB35 : ℕ → ℕ | 13 => 0x80000080000000008000 | 15 => 0x4041 | 16 => 0x100000020024002 | 18 => 0x4041 | 19 => 0x4041 | 20 => 0x200000000000000 | 21 => 0x4041 | 22 => 0x4041 | 23 => 0x400000000000000 | 25 => 0x80000000000000 | 26 => 0x80000000000000 | 28 => 0x80000000000000 | 29 => 0x80000000000000 | 31 => 0x80000000000000 | 32 => 0x80000000000000 | 43 => 0x100000000000000 | 45 => 0x40 | 46 => 0x40 | 47 => 0x200000000000000 | 48 => 0x40 | 49 => 0x40 | 50 => 0x400000000000000 | 52 => 0x100000000000000 | 53 => 0x100000000000000 | 54 => 0x100000000000000 | 55 => 0x100000000000000 | 56 => 0x100000000000000 | _ => 0
private def redB36 : ℕ → ℕ | 0 => 0x40 | 1 => 0x200000000000000 | 2 => 0x40 | 3 => 0x40 | 4 => 0x400000000000000 | 5 => 0x200000000000000 | 6 => 0x40 | 7 => 0x40 | 8 => 0x400000000000000 | 9 => 0x200000000000000 | 10 => 0x200000000000000 | 11 => 0x200000000000000 | 12 => 0x40 | 13 => 0x400000000000000 | 14 => 0x400000000000000 | 15 => 0x800000000000201 | 18 => 0x800000000000401 | 19 => 0x800 | 21 => 0x800000000001001 | 22 => 0x100000002000 | 24 => 0x800000000004001 | 27 => 0x800000000000000 | 30 => 0x800000000000000 | 33 => 0x800000000000000 | 34 => 0x800000000000000 | 38 => 0x281 | 39 => 0x100000000000000000 | 41 => 0x281 | 42 => 0x200000100000000000 | 44 => 0x281 | 45 => 0x401000000000008000 | 47 => 0x281 | 48 => 0x2000000020020202 | 50 => 0x281 | 51 => 0x4000000000000201 | 53 => 0x281 | 54 => 0x281 | 55 => 0x8000000000000000 | _ => 0
private def redB37 : ℕ → ℕ | 29 => 0x800000000000000000 | 31 => 0x481 | 32 => 0x1000000100000000000 | 34 => 0x481 | 35 => 0x2001000000000008000 | 37 => 0x481 | 38 => 0x2000000020020402 | 40 => 0x481 | 41 => 0x4000000000000401 | 43 => 0x481 | 44 => 0x481 | 45 => 0x8000000000000000 | 47 => 0x4000000000000000000 | 48 => 0x800 | 50 => 0x8000000000000000000 | 51 => 0x800 | 53 => 0x800 | 54 => 0x800 | 56 => 0x800 | 57 => 0x800 | 59 => 0x800 | 60 => 0x800 | _ => 0
private def redB38 : ℕ → ℕ | 13 => 0x10000000100000000000 | 15 => 0x1081 | 16 => 0x20001000000000008000 | 18 => 0x1081 | 19 => 0x2000000020021002 | 21 => 0x1081 | 22 => 0x4000000000001001 | 24 => 0x1081 | 25 => 0x1081 | 26 => 0x8000000000000000 | 28 => 0x40000000100000000000 | 29 => 0x100000002000 | 31 => 0x100000002000 | 32 => 0x100000002000 | 34 => 0x100000002000 | 35 => 0x100000002000 | 37 => 0x100000002000 | 38 => 0x100000002000 | 52 => 0x80001000000000008000 | 54 => 0x4081 | 55 => 0x2000000020024002 | 57 => 0x4081 | 58 => 0x4000000000004001 | 60 => 0x4081 | 61 => 0x4081 | 62 => 0x8000000000000000 | _ => 0
private def redB39 : ℕ → ℕ | 0 => 0x1000000000000000 | 1 => 0x1000000000000000 | 3 => 0x1000000000000000 | 4 => 0x1000000000000000 | 6 => 0x1000000000000000 | 7 => 0x1000000000000000 | 18 => 0x2000000000000000 | 20 => 0x80 | 21 => 0x4000000000000000 | 23 => 0x80 | 24 => 0x80 | 25 => 0x8000000000000000 | 27 => 0x2000000000000000 | 28 => 0x2000000000000000 | 30 => 0x2000000000000000 | 31 => 0x2000000000000000 | 39 => 0x4000000000000000 | 41 => 0x80 | 42 => 0x80 | 43 => 0x8000000000000000 | 45 => 0x4000000000000000 | 46 => 0x4000000000000000 | 47 => 0x4000000000000000 | 51 => 0x80 | 52 => 0x8000000000000000 | 53 => 0x8000000000000000 | 56 => 0x301 | 57 => 0x100000000000000000 | 59 => 0x301 | 60 => 0x200000100000000000 | 62 => 0x301 | 63 => 0x410000000000008000 | _ => 0
private def redB40 : ℕ → ℕ | 1 => 0x301 | 2 => 0x20000000020020202 | 4 => 0x301 | 5 => 0x40000000000000201 | 7 => 0x301 | 8 => 0x80000000000000201 | 47 => 0x800000000000000000 | 49 => 0x501 | 50 => 0x1000000100000000000 | 52 => 0x501 | 53 => 0x2010000000000008000 | 55 => 0x501 | 56 => 0x20000000020020402 | 58 => 0x501 | 59 => 0x40000000000000401 | 61 => 0x501 | 62 => 0x80000000000000401 | _ => 0
private def redB41 : ℕ → ℕ | 1 => 0x4000000000000000000 | 2 => 0x800 | 4 => 0x8000000000000000000 | 5 => 0x800 | 7 => 0x800 | 8 => 0x800 | 10 => 0x800 | 11 => 0x800 | 13 => 0x800 | 14 => 0x800 | 31 => 0x10000000100000000000 | 33 => 0x1101 | 34 => 0x20010000000000008000 | 36 => 0x1101 | 37 => 0x20000000020021002 | 39 => 0x1101 | 40 => 0x40000000000001001 | 42 => 0x1101 | 43 => 0x80000000000001001 | 46 => 0x40000000100000000000 | 47 => 0x100000002000 | 49 => 0x100000002000 | 50 => 0x100000002000 | 52 => 0x100000002000 | 53 => 0x100000002000 | 55 => 0x100000002000 | 56 => 0x100000002000 | _ => 0
private def redB42 : ℕ → ℕ | 6 => 0x80010000000000008000 | 8 => 0x4101 | 9 => 0x20000000020024002 | 11 => 0x4101 | 12 => 0x40000000000004001 | 14 => 0x4101 | 15 => 0x80000000000004001 | 18 => 0x10000000000000000 | 19 => 0x10000000000000000 | 21 => 0x10000000000000000 | 22 => 0x10000000000000000 | 24 => 0x10000000000000000 | 25 => 0x10000000000000000 | 36 => 0x20000000000000000 | 38 => 0x100 | 39 => 0x40000000000000000 | 41 => 0x100 | 42 => 0x80000000000000000 | 45 => 0x20000000000000000 | 46 => 0x20000000000000000 | 48 => 0x20000000000000000 | 49 => 0x20000000000000000 | 57 => 0x40000000000000000 | 59 => 0x100 | 60 => 0x80000000000000000 | 63 => 0x40000000000000000 | _ => 0
private def redB43 : ℕ → ℕ | 0 => 0x40000000000000000 | 5 => 0x80000000000000000 | 45 => 0x100000000000000000 | 47 => 0x200 | 48 => 0x200000000000000000 | 50 => 0x200 | 51 => 0x400000000000000000 | 52 => 0x10000 | 53 => 0x200 | 54 => 0x20000202 | 55 => 0x40000 | 56 => 0x200 | 57 => 0x80201 | 58 => 0x100000 | 59 => 0x200 | 60 => 0x200201 | 61 => 0x400000 | 63 => 0x100000000000000000 | _ => 0
private def redB44 : ℕ → ℕ | 0 => 0x100000000000000000 | 2 => 0x100000000000000000 | 3 => 0x100000000000000000 | 5 => 0x100000000000000000 | 6 => 0x100000000000000000 | 8 => 0x100000000000000000 | 9 => 0x100000000000000000 | 11 => 0x100000000000000000 | 12 => 0x100000000000000000 | 29 => 0x200000000000000000 | 31 => 0x200 | 32 => 0x400000000000000000 | 33 => 0x10000 | 34 => 0x200 | 35 => 0x20000202 | 36 => 0x40000 | 37 => 0x200 | 38 => 0x80201 | 39 => 0x100000 | 40 => 0x200 | 41 => 0x200201 | 42 => 0x400000 | 44 => 0x200000000000000000 | 45 => 0x200000000000000000 | 46 => 0x100000000000 | 47 => 0x200000000000000000 | 48 => 0x200000000000000000 | 49 => 0x100000000000 | 50 => 0x200000000000000000 | 51 => 0x200000000000000000 | 52 => 0x100000000000 | 53 => 0x200000000000000000 | 54 => 0x200000000000000000 | 55 => 0x100000000000 | _ => 0
private def redB45 : ℕ → ℕ | 4 => 0x400000000000000000 | 5 => 0x10000 | 6 => 0x200 | 7 => 0x20000202 | 8 => 0x40000 | 9 => 0x200 | 10 => 0x80201 | 11 => 0x100000 | 12 => 0x200 | 13 => 0x200201 | 14 => 0x400000 | 15 => 0x100000000000000000000 | 16 => 0x400000000000000000 | 17 => 0x400000000000000000 | 18 => 0x200000000000000000000 | 19 => 0x400000000000000000 | 20 => 0x400000000000000000 | 21 => 0x400000000000000000000 | 22 => 0x400000000000000000 | 23 => 0x400000000000000000 | 24 => 0x800000000000000000000 | 25 => 0x10000 | 26 => 0x1000000000000000000000 | 27 => 0x10000 | 28 => 0x10000 | 29 => 0x2000000000000000000000 | 30 => 0x10000 | 31 => 0x10000 | 32 => 0x4000000000000000000000 | 33 => 0x10000 | 34 => 0x20000202 | 35 => 0x40000 | 36 => 0x200 | 37 => 0x80201 | 38 => 0x100000 | 39 => 0x200 | 40 => 0x200201 | 41 => 0x400000 | 42 => 0x8000000000000000000000 | 43 => 0x20000202 | 44 => 0x20000202 | 45 => 0x10000000000000000000000 | 46 => 0x20000202 | 47 => 0x20000202 | 48 => 0x20000000000000000000000 | 49 => 0x40000 | 50 => 0x40000000000000000000000 | 51 => 0x40000 | 52 => 0x40000 | 53 => 0x80000000000000000000000 | 54 => 0x40000 | 55 => 0x80201 | 56 => 0x100000 | 57 => 0x200 | 58 => 0x200201 | 59 => 0x400000 | 60 => 0x100000000000000000000000 | 61 => 0x80201 | 62 => 0x80201 | 63 => 0x200000000000000000000000 | _ => 0
private def redB46 : ℕ → ℕ | 0 => 0x100000 | 1 => 0x400000000000000000000000 | 2 => 0x100000 | 3 => 0x200201 | 4 => 0x400000 | 5 => 0x800000000000000000000000 | _ => 0
private def redB47 (_ : ℕ) : ℕ := 0
private def redB48 (_ : ℕ) : ℕ := 0
private def redB49 (_ : ℕ) : ℕ := 0
private def redB50 (_ : ℕ) : ℕ := 0
private def redB51 : ℕ → ℕ | 11 => 0x800000000000000000 | 12 => 0x800000000000000000 | 14 => 0x800000000000000000 | 15 => 0x800000000000000000 | 17 => 0x800000000000000000 | 18 => 0x800000000000000000 | 20 => 0x800000000000000000 | 21 => 0x800000000000000000 | 23 => 0x800000000000000000 | 24 => 0x800000000000000000 | 41 => 0x1000000000000000000 | 43 => 0x400 | 44 => 0x2000000000000000000 | 45 => 0x10000 | 46 => 0x400 | 47 => 0x20000402 | 48 => 0x40000 | 49 => 0x400 | 50 => 0x80401 | 51 => 0x100000 | 52 => 0x400 | 53 => 0x200401 | 54 => 0x400000 | 56 => 0x1000000000000000000 | 57 => 0x1000000000000000000 | 58 => 0x100000000000 | 59 => 0x1000000000000000000 | 60 => 0x1000000000000000000 | 61 => 0x100000000000 | 62 => 0x1000000000000000000 | 63 => 0x1000000000000000000 | _ => 0
private def redB52 : ℕ → ℕ | 0 => 0x100000000000 | 1 => 0x1000000000000000000 | 2 => 0x1000000000000000000 | 3 => 0x100000000000 | 16 => 0x2000000000000000000 | 17 => 0x10000 | 18 => 0x400 | 19 => 0x20000402 | 20 => 0x40000 | 21 => 0x400 | 22 => 0x80401 | 23 => 0x100000 | 24 => 0x400 | 25 => 0x200401 | 26 => 0x400000 | 27 => 0x100000000000000000000 | 28 => 0x2000000000000000000 | 29 => 0x2000000000000000000 | 30 => 0x200000000000000000000 | 31 => 0x2000000000000000000 | 32 => 0x2000000000000000000 | 33 => 0x400000000000000000000 | 34 => 0x2000000000000000000 | 35 => 0x2000000000000000000 | 36 => 0x800000000000000000000 | 37 => 0x10000 | 38 => 0x1000000000000000000000 | 39 => 0x10000 | 40 => 0x10000 | 41 => 0x2000000000000000000000 | 42 => 0x10000 | 43 => 0x10000 | 44 => 0x4000000000000000000000 | 45 => 0x10000 | 46 => 0x20000402 | 47 => 0x40000 | 48 => 0x400 | 49 => 0x80401 | 50 => 0x100000 | 51 => 0x400 | 52 => 0x200401 | 53 => 0x400000 | 54 => 0x8000000000000000000000 | 55 => 0x20000402 | 56 => 0x20000402 | 57 => 0x10000000000000000000000 | 58 => 0x20000402 | 59 => 0x20000402 | 60 => 0x20000000000000000000000 | 61 => 0x40000 | 62 => 0x40000000000000000000000 | 63 => 0x40000 | _ => 0
private def redB53 : ℕ → ℕ | 0 => 0x40000 | 1 => 0x80000000000000000000000 | 2 => 0x40000 | 3 => 0x80401 | 4 => 0x100000 | 5 => 0x400 | 6 => 0x200401 | 7 => 0x400000 | 8 => 0x100000000000000000000000 | 9 => 0x80401 | 10 => 0x80401 | 11 => 0x200000000000000000000000 | 12 => 0x100000 | 13 => 0x400000000000000000000000 | 14 => 0x100000 | 15 => 0x200401 | 16 => 0x400000 | 17 => 0x800000000000000000000000 | 33 => 0x4000000000000000000 | 35 => 0x4000000000000000000 | 36 => 0x4000000000000000000 | 38 => 0x4000000000000000000 | 39 => 0x4000000000000000000 | 41 => 0x4000000000000000000 | 42 => 0x4000000000000000000 | 44 => 0x4000000000000000000 | 45 => 0x4000000000000000000 | 48 => 0x8000000000000000000 | 49 => 0x800 | 51 => 0x800 | 52 => 0x800 | 54 => 0x800 | 55 => 0x800 | 57 => 0x800 | 58 => 0x800 | _ => 0
private def redB54 : ℕ → ℕ | 8 => 0x8000000000000000000 | 10 => 0x8000000000000000000 | 11 => 0x8000000000000000000 | 13 => 0x8000000000000000000 | 14 => 0x8000000000000000000 | 16 => 0x8000000000000000000 | 17 => 0x8000000000000000000 | 20 => 0x800 | 21 => 0x800 | 23 => 0x800 | 24 => 0x800 | 26 => 0x800 | 27 => 0x800 | 38 => 0x800 | 40 => 0x800 | 41 => 0x800 | 43 => 0x800 | 44 => 0x800 | 47 => 0x800 | 48 => 0x800 | 50 => 0x800 | 51 => 0x800 | 59 => 0x800 | 61 => 0x800 | 62 => 0x800 | _ => 0
private def redB55 : ℕ → ℕ | 1 => 0x800 | 2 => 0x800 | 7 => 0x800 | _ => 0
private def redB56 : ℕ → ℕ | 52 => 0x10000000000000000000 | 53 => 0x10000000000000000000 | 54 => 0x100000000000 | 55 => 0x10000000000000000000 | 56 => 0x10000000000000000000 | 57 => 0x100000000000 | 58 => 0x10000000000000000000 | 59 => 0x10000000000000000000 | 60 => 0x100000000000 | 61 => 0x10000000000000000000 | 62 => 0x10000000000000000000 | 63 => 0x100000000000 | _ => 0
private def redB57 : ℕ → ℕ | 12 => 0x20000000000000000000 | 13 => 0x10000 | 14 => 0x1000 | 15 => 0x20001002 | 16 => 0x40000 | 17 => 0x1000 | 18 => 0x81001 | 19 => 0x100000 | 20 => 0x1000 | 21 => 0x201001 | 22 => 0x400000 | 23 => 0x100000000000000000000 | 24 => 0x20000000000000000000 | 25 => 0x20000000000000000000 | 26 => 0x200000000000000000000 | 27 => 0x20000000000000000000 | 28 => 0x20000000000000000000 | 29 => 0x400000000000000000000 | 30 => 0x20000000000000000000 | 31 => 0x20000000000000000000 | 32 => 0x800000000000000000000 | 33 => 0x10000 | 34 => 0x1000000000000000000000 | 35 => 0x10000 | 36 => 0x10000 | 37 => 0x2000000000000000000000 | 38 => 0x10000 | 39 => 0x10000 | 40 => 0x4000000000000000000000 | 41 => 0x10000 | 42 => 0x20001002 | 43 => 0x40000 | 44 => 0x1000 | 45 => 0x81001 | 46 => 0x100000 | 47 => 0x1000 | 48 => 0x201001 | 49 => 0x400000 | 50 => 0x8000000000000000000000 | 51 => 0x20001002 | 52 => 0x20001002 | 53 => 0x10000000000000000000000 | 54 => 0x20001002 | 55 => 0x20001002 | 56 => 0x20000000000000000000000 | 57 => 0x40000 | 58 => 0x40000000000000000000000 | 59 => 0x40000 | 60 => 0x40000 | 61 => 0x80000000000000000000000 | 62 => 0x40000 | 63 => 0x81001 | _ => 0
private def redB58 : ℕ → ℕ | 0 => 0x100000 | 1 => 0x1000 | 2 => 0x201001 | 3 => 0x400000 | 4 => 0x100000000000000000000000 | 5 => 0x81001 | 6 => 0x81001 | 7 => 0x200000000000000000000000 | 8 => 0x100000 | 9 => 0x400000000000000000000000 | 10 => 0x100000 | 11 => 0x201001 | 12 => 0x400000 | 13 => 0x800000000000000000000000 | 26 => 0x40000000000000000000 | 27 => 0x100000000000 | 28 => 0x40000000000000000000 | 29 => 0x40000000000000000000 | 30 => 0x100000000000 | 31 => 0x40000000000000000000 | 32 => 0x40000000000000000000 | 33 => 0x100000000000 | 34 => 0x40000000000000000000 | 35 => 0x40000000000000000000 | 36 => 0x100000000000 | 37 => 0x100000000000 | 38 => 0x2000 | 39 => 0x2000 | 40 => 0x100000000000 | 41 => 0x2000 | 42 => 0x2000 | 43 => 0x100000000000 | 44 => 0x2000 | 45 => 0x2000 | 46 => 0x100000000000 | 47 => 0x100000000000 | 48 => 0x100000000000 | 49 => 0x100000000000 | 50 => 0x100000000000 | 51 => 0x100000000000 | 52 => 0x100000000000 | 53 => 0x100000000000 | 54 => 0x100000000000 | 55 => 0x100000000000 | 56 => 0x2000 | 57 => 0x100000000000 | 58 => 0x2000 | 59 => 0x2000 | 60 => 0x100000000000 | 61 => 0x2000 | 62 => 0x2000 | 63 => 0x100000000000 | _ => 0
private def redB59 : ℕ → ℕ | 0 => 0x100000000000 | 1 => 0x2000 | 2 => 0x2000 | 3 => 0x100000000000 | 4 => 0x2000 | 5 => 0x2000 | 6 => 0x100000000000 | 7 => 0x100000000000 | 8 => 0x100000000000 | 9 => 0x100000000000 | 10 => 0x100000000000 | 11 => 0x100000000000 | 12 => 0x100000000000 | 13 => 0x2000 | 14 => 0x100000000000 | 15 => 0x2000 | 16 => 0x2000 | 17 => 0x100000000000 | 18 => 0x100000000000 | 19 => 0x2000 | 20 => 0x2000 | 21 => 0x100000000000 | 22 => 0x100000000000 | 23 => 0x100000000000 | 24 => 0x100000000000 | 25 => 0x2000 | 26 => 0x100000000000 | 27 => 0x100000000000 | _ => 0
private def redB60 : ℕ → ℕ | 30 => 0x100000000000000000000 | 31 => 0x80000000000000000000 | 32 => 0x80000000000000000000 | 33 => 0x200000000000000000000 | 34 => 0x80000000000000000000 | 35 => 0x80000000000000000000 | 36 => 0x400000000000000000000 | 37 => 0x80000000000000000000 | 38 => 0x80000000000000000000 | 39 => 0x800000000000000000000 | 40 => 0x10000 | 41 => 0x1000000000000000000000 | 42 => 0x10000 | 43 => 0x10000 | 44 => 0x2000000000000000000000 | 45 => 0x10000 | 46 => 0x10000 | 47 => 0x4000000000000000000000 | 48 => 0x10000 | 49 => 0x20004002 | 50 => 0x40000 | 51 => 0x4000 | 52 => 0x84001 | 53 => 0x100000 | 54 => 0x4000 | 55 => 0x204001 | 56 => 0x400000 | 57 => 0x8000000000000000000000 | 58 => 0x20004002 | 59 => 0x20004002 | 60 => 0x10000000000000000000000 | 61 => 0x20004002 | 62 => 0x20004002 | 63 => 0x20000000000000000000000 | _ => 0
private def redB61 : ℕ → ℕ | 0 => 0x40000 | 1 => 0x40000000000000000000000 | 2 => 0x40000 | 3 => 0x40000 | 4 => 0x80000000000000000000000 | 5 => 0x40000 | 6 => 0x84001 | 7 => 0x100000 | 8 => 0x4000 | 9 => 0x204001 | 10 => 0x400000 | 11 => 0x100000000000000000000000 | 12 => 0x84001 | 13 => 0x84001 | 14 => 0x200000000000000000000000 | 15 => 0x100000 | 16 => 0x400000000000000000000000 | 17 => 0x100000 | 18 => 0x204001 | 19 => 0x400000 | 20 => 0x800000000000000000000000 | 21 => 0x100000000000000000000 | 22 => 0x100000000000000000000 | 23 => 0x100000000000000000000 | 24 => 0x100000000000000000000 | 25 => 0x100000000000000000000 | 26 => 0x100000000000000000000 | 27 => 0x100000000000000000000 | 28 => 0x100000000000000000000 | 29 => 0x100000000000000000000 | 30 => 0x8000 | 31 => 0x200000000000000000000 | 32 => 0x8000 | 33 => 0x8000 | 34 => 0x400000000000000000000 | 35 => 0x8000 | 36 => 0x8000 | 37 => 0x800000000000000000000 | 38 => 0x200000000000000000000 | 39 => 0x8000 | 40 => 0x8000 | 41 => 0x400000000000000000000 | 42 => 0x8000 | 43 => 0x8000 | 44 => 0x800000000000000000000 | 45 => 0x200000000000000000000 | 46 => 0x200000000000000000000 | 47 => 0x200000000000000000000 | 48 => 0x200000000000000000000 | 49 => 0x200000000000000000000 | 50 => 0x200000000000000000000 | 51 => 0x8000 | 52 => 0x400000000000000000000 | 53 => 0x8000 | 54 => 0x8000 | 55 => 0x800000000000000000000 | 56 => 0x400000000000000000000 | 57 => 0x8000 | 58 => 0x8000 | 59 => 0x800000000000000000000 | 60 => 0x400000000000000000000 | 61 => 0x400000000000000000000 | 62 => 0x400000000000000000000 | 63 => 0x8000 | _ => 0
private def redB62 : ℕ → ℕ | 0 => 0x800000000000000000000 | 1 => 0x800000000000000000000 | 2 => 0x1000000000000000000000 | 3 => 0x10000 | 4 => 0x10000 | 5 => 0x2000000000000000000000 | 6 => 0x10000 | 7 => 0x10000 | 8 => 0x4000000000000000000000 | 9 => 0x10000 | 10 => 0x1000000000000000000000 | 11 => 0x1000000000000000000000 | 12 => 0x1000000000000000000000 | 13 => 0x1000000000000000000000 | 14 => 0x1000000000000000000000 | 15 => 0x1000000000000000000000 | 16 => 0x1000000000000000000000 | 17 => 0x10000 | 18 => 0x2000000000000000000000 | 19 => 0x10000 | 20 => 0x10000 | 21 => 0x4000000000000000000000 | 22 => 0x10000 | 23 => 0x2000000000000000000000 | 24 => 0x10000 | 25 => 0x10000 | 26 => 0x4000000000000000000000 | 27 => 0x10000 | 28 => 0x2000000000000000000000 | 29 => 0x2000000000000000000000 | 30 => 0x2000000000000000000000 | 31 => 0x2000000000000000000000 | 32 => 0x10000 | 33 => 0x4000000000000000000000 | 34 => 0x10000 | 35 => 0x4000000000000000000000 | 36 => 0x10000 | 37 => 0x4000000000000000000000 | 38 => 0x8000000000000000000000 | 39 => 0x20000 | 40 => 0x20000 | 41 => 0x10000000000000000000000 | 42 => 0x20000 | 43 => 0x20000 | 44 => 0x20000000000000000000000 | 45 => 0x40000 | 46 => 0x40000000000000000000000 | 47 => 0x40000 | 48 => 0x40000 | 49 => 0x80000000000000000000000 | 50 => 0x40000 | 51 => 0x80000 | 52 => 0x100000 | 53 => 0x1 | 54 => 0x200000 | 55 => 0x400000 | 56 => 0x100000000000000000000000 | 57 => 0x80000 | 58 => 0x80000 | 59 => 0x200000000000000000000000 | 60 => 0x100000 | 61 => 0x400000000000000000000000 | 62 => 0x100000 | 63 => 0x200000 | _ => 0
private def redB63 : ℕ → ℕ | 0 => 0x400000 | 1 => 0x800000000000000000000000 | 2 => 0x8000000000000000000000 | 3 => 0x8000000000000000000000 | 4 => 0x8000000000000000000000 | 5 => 0x8000000000000000000000 | 6 => 0x8000000000000000000000 | 7 => 0x8000000000000000000000 | 8 => 0x20000 | 9 => 0x10000000000000000000000 | 10 => 0x20000 | 11 => 0x20000 | 12 => 0x20000000000000000000000 | 13 => 0x10000000000000000000000 | 14 => 0x20000 | 15 => 0x20000 | 16 => 0x20000000000000000000000 | 17 => 0x10000000000000000000000 | 18 => 0x10000000000000000000000 | 19 => 0x10000000000000000000000 | 20 => 0x20000 | 21 => 0x20000000000000000000000 | 22 => 0x20000000000000000000000 | 23 => 0x40000000000000000000000 | 24 => 0x40000 | 25 => 0x40000 | 26 => 0x80000000000000000000000 | 27 => 0x40000 | 28 => 0x40000000000000000000000 | 29 => 0x40000000000000000000000 | 30 => 0x40000000000000000000000 | 31 => 0x40000000000000000000000 | 32 => 0x40000 | 33 => 0x80000000000000000000000 | 34 => 0x40000 | 35 => 0x80000000000000000000000 | 36 => 0x40000 | 37 => 0x80000000000000000000000 | 38 => 0x100000000000000000000000 | 39 => 0x80000 | 40 => 0x80000 | 41 => 0x200000000000000000000000 | 42 => 0x100000 | 43 => 0x400000000000000000000000 | 44 => 0x100000 | 45 => 0x200000 | 46 => 0x400000 | 47 => 0x800000000000000000000000 | 48 => 0x100000000000000000000000 | 49 => 0x100000000000000000000000 | 50 => 0x100000000000000000000000 | 51 => 0x80000 | 52 => 0x200000000000000000000000 | 53 => 0x200000000000000000000000 | 54 => 0x400000000000000000000000 | 55 => 0x100000 | 56 => 0x400000000000000000000000 | 57 => 0x800000000000000000000000 | _ => 0

private def redAll (i : ℕ) : ℕ :=
  match Nat.div i 64 with
  | 0 => redB0 (Nat.mod i 64)
  | 1 => redB1 (Nat.mod i 64)
  | 2 => redB2 (Nat.mod i 64)
  | 3 => redB3 (Nat.mod i 64)
  | 4 => redB4 (Nat.mod i 64)
  | 5 => redB5 (Nat.mod i 64)
  | 6 => redB6 (Nat.mod i 64)
  | 7 => redB7 (Nat.mod i 64)
  | 8 => redB8 (Nat.mod i 64)
  | 9 => redB9 (Nat.mod i 64)
  | 10 => redB10 (Nat.mod i 64)
  | 11 => redB11 (Nat.mod i 64)
  | 12 => redB12 (Nat.mod i 64)
  | 13 => redB13 (Nat.mod i 64)
  | 14 => redB14 (Nat.mod i 64)
  | 15 => redB15 (Nat.mod i 64)
  | 16 => redB16 (Nat.mod i 64)
  | 17 => redB17 (Nat.mod i 64)
  | 18 => redB18 (Nat.mod i 64)
  | 19 => redB19 (Nat.mod i 64)
  | 20 => redB20 (Nat.mod i 64)
  | 21 => redB21 (Nat.mod i 64)
  | 22 => redB22 (Nat.mod i 64)
  | 23 => redB23 (Nat.mod i 64)
  | 24 => redB24 (Nat.mod i 64)
  | 25 => redB25 (Nat.mod i 64)
  | 26 => redB26 (Nat.mod i 64)
  | 27 => redB27 (Nat.mod i 64)
  | 28 => redB28 (Nat.mod i 64)
  | 29 => redB29 (Nat.mod i 64)
  | 30 => redB30 (Nat.mod i 64)
  | 31 => redB31 (Nat.mod i 64)
  | 32 => redB32 (Nat.mod i 64)
  | 33 => redB33 (Nat.mod i 64)
  | 34 => redB34 (Nat.mod i 64)
  | 35 => redB35 (Nat.mod i 64)
  | 36 => redB36 (Nat.mod i 64)
  | 37 => redB37 (Nat.mod i 64)
  | 38 => redB38 (Nat.mod i 64)
  | 39 => redB39 (Nat.mod i 64)
  | 40 => redB40 (Nat.mod i 64)
  | 41 => redB41 (Nat.mod i 64)
  | 42 => redB42 (Nat.mod i 64)
  | 43 => redB43 (Nat.mod i 64)
  | 44 => redB44 (Nat.mod i 64)
  | 45 => redB45 (Nat.mod i 64)
  | 46 => redB46 (Nat.mod i 64)
  | 47 => redB47 (Nat.mod i 64)
  | 48 => redB48 (Nat.mod i 64)
  | 49 => redB49 (Nat.mod i 64)
  | 50 => redB50 (Nat.mod i 64)
  | 51 => redB51 (Nat.mod i 64)
  | 52 => redB52 (Nat.mod i 64)
  | 53 => redB53 (Nat.mod i 64)
  | 54 => redB54 (Nat.mod i 64)
  | 55 => redB55 (Nat.mod i 64)
  | 56 => redB56 (Nat.mod i 64)
  | 57 => redB57 (Nat.mod i 64)
  | 58 => redB58 (Nat.mod i 64)
  | 59 => redB59 (Nat.mod i 64)
  | 60 => redB60 (Nat.mod i 64)
  | 61 => redB61 (Nat.mod i 64)
  | 62 => redB62 (Nat.mod i 64)
  | 63 => redB63 (Nat.mod i 64)
  | _ => 0

private def rbB0 : ℕ → List ℕ | 0 => [0] | 1 => [1] | 2 => [2] | 3 => [3] | 4 => [4] | 5 => [5] | 6 => [6] | 7 => [7] | 8 => [8] | 9 => [9] | 12 => [10] | 13 => [11] | 15 => [12] | 16 => [13] | 18 => [14] | 19 => [15] | 20 => [16] | 21 => [0] | 22 => [17] | 23 => [18] | 24 => [0] | 25 => [19] | 26 => [20] | 27 => [0] | 28 => [21] | 29 => [22] | 30 => [23] | 31 => [24] | 32 => [25] | 33 => [0, 1, 5] | 34 => [0, 1, 6] | 35 => [0, 1, 7] | 36 => [0, 1, 8] | 37 => [1] | 40 => [1] | 41 => [26] | 43 => [1] | 44 => [27] | 46 => [1] | 47 => [28] | 48 => [16] | 49 => [1] | 50 => [29] | 51 => [18] | 52 => [1] | 53 => [0, 1, 19] | 54 => [20] | 55 => [1] | 56 => [0, 1, 21] | 57 => [22] | 58 => [30] | 59 => [31] | 60 => [0, 2, 5] | 61 => [0, 2, 6] | 62 => [0, 2, 7] | 63 => [0, 2, 8] | _ => []
private def rbB1 : ℕ → List ℕ | 0 => [32] | 3 => [2] | 4 => [33] | 6 => [2] | 7 => [34] | 9 => [2] | 10 => [35] | 11 => [16] | 12 => [2] | 13 => [1, 2, 29] | 14 => [18] | 15 => [2] | 16 => [0, 2, 19] | 17 => [20] | 18 => [2] | 19 => [0, 2, 21] | 20 => [22] | 21 => [36] | 22 => [0, 3, 5] | 23 => [0, 3, 6] | 24 => [0, 3, 7] | 25 => [0, 3, 8] | 26 => [37] | 29 => [38] | 32 => [3] | 33 => [39] | 35 => [3] | 36 => [40] | 37 => [16] | 38 => [3] | 39 => [1, 3, 29] | 40 => [18] | 41 => [3] | 42 => [0, 3, 19] | 43 => [20] | 44 => [3] | 45 => [0, 3, 21] | 46 => [22] | 47 => [0, 4, 5] | 48 => [0, 4, 6] | 49 => [0, 4, 7] | 50 => [0, 4, 8] | 51 => [41] | 54 => [42] | 57 => [43] | 58 => [44] | 60 => [4] | 61 => [45] | 62 => [16] | 63 => [4] | _ => []
private def rbB2 : ℕ → List ℕ | 0 => [1, 4, 29] | 1 => [18] | 2 => [4] | 3 => [0, 4, 19] | 4 => [20] | 5 => [4] | 6 => [0, 4, 21] | 7 => [22] | 8 => [46] | 9 => [47] | 10 => [48] | 11 => [0, 5, 9] | 14 => [0, 5, 10] | 15 => [11] | 17 => [0, 5, 12] | 18 => [13, 44] | 20 => [0, 5, 14] | 21 => [49] | 23 => [5] | 24 => [0, 1, 5, 17, 29] | 25 => [50] | 26 => [5] | 27 => [5] | 28 => [51] | 29 => [5] | 30 => [5] | 31 => [52] | 32 => [53] | 33 => [54] | 34 => [0, 6, 9] | 37 => [0, 6, 10] | 38 => [11] | 40 => [0, 6, 12] | 41 => [13, 44] | 43 => [0, 6, 14] | 44 => [55] | 46 => [6] | 47 => [56] | 49 => [6] | 50 => [6] | 51 => [57] | 52 => [6] | 53 => [6] | 54 => [58] | 55 => [59] | 56 => [0, 7, 9] | 59 => [0, 7, 10] | 60 => [11] | 62 => [0, 7, 12] | 63 => [13, 44] | _ => []
private def rbB3 : ℕ → List ℕ | 1 => [0, 7, 14] | 2 => [60] | 4 => [7] | 5 => [61] | 7 => [7] | 8 => [62] | 10 => [7] | 11 => [7] | 12 => [63] | 13 => [0, 8, 9] | 16 => [0, 8, 10] | 17 => [11] | 19 => [0, 8, 12] | 20 => [13, 44] | 22 => [0, 8, 14] | 23 => [64] | 25 => [8] | 26 => [65] | 28 => [8] | 29 => [66] | 31 => [8] | 32 => [67] | 36 => [9] | 37 => [68] | 39 => [9] | 40 => [69] | 42 => [9] | 43 => [70] | 44 => [16] | 45 => [9] | 46 => [1, 9, 29] | 47 => [18] | 48 => [9] | 49 => [0, 9, 19] | 50 => [20] | 51 => [9] | 52 => [0, 9, 21] | 53 => [22] | _ => []
private def rbB4 : ℕ → List ℕ | 27 => [71] | 29 => [10] | 30 => [72] | 32 => [10] | 33 => [73] | 34 => [16] | 35 => [10] | 36 => [1, 10, 29] | 37 => [18] | 38 => [10] | 39 => [0, 10, 19] | 40 => [20] | 41 => [10] | 42 => [0, 10, 21] | 43 => [22] | 45 => [74] | 46 => [11] | 48 => [75] | 49 => [11] | 51 => [11] | 52 => [11] | 54 => [11] | 55 => [11] | 57 => [11] | 58 => [11] | _ => []
private def rbB5 : ℕ → List ℕ | 11 => [76] | 13 => [12] | 14 => [77] | 15 => [16] | 16 => [12] | 17 => [1, 12, 29] | 18 => [18] | 19 => [12] | 20 => [0, 12, 19] | 21 => [20] | 22 => [12] | 23 => [0, 12, 21] | 24 => [22] | 26 => [78] | 27 => [13] | 28 => [44] | 29 => [13] | 30 => [13] | 31 => [44] | 32 => [13] | 33 => [13] | 34 => [44] | 35 => [13] | 36 => [13] | 37 => [44] | 50 => [79] | 51 => [16] | 52 => [14] | 53 => [1, 14, 29] | 54 => [18] | 55 => [14] | 56 => [0, 14, 19] | 57 => [20] | 58 => [14] | 59 => [0, 14, 21] | 60 => [22] | 61 => [80] | 62 => [15] | 63 => [15] | _ => []
private def rbB6 : ℕ → List ℕ | 0 => [81] | 1 => [15] | 2 => [15] | 3 => [82] | 4 => [15] | 5 => [15] | 6 => [83] | 7 => [16] | 8 => [84] | 9 => [16] | 10 => [16] | 11 => [85] | 12 => [16] | 13 => [16] | 14 => [86] | 15 => [16] | 16 => [17] | 17 => [18] | 18 => [0] | 19 => [19] | 20 => [20] | 21 => [0] | 22 => [21] | 23 => [22] | 24 => [87] | 25 => [17] | 26 => [17] | 27 => [88] | 28 => [17] | 29 => [17] | 30 => [89] | 31 => [18] | 32 => [90] | 33 => [18] | 34 => [18] | 35 => [91] | 36 => [18] | 37 => [19] | 38 => [20] | 39 => [0] | 40 => [21] | 41 => [22] | 42 => [92] | 43 => [19] | 44 => [19] | 45 => [93] | 46 => [20] | 47 => [94] | 48 => [20] | 49 => [21] | 50 => [22] | 51 => [95] | _ => []

private def redBits (i : ℕ) : List ℕ :=
  match Nat.div i 64 with
  | 0 => rbB0 (Nat.mod i 64)
  | 1 => rbB1 (Nat.mod i 64)
  | 2 => rbB2 (Nat.mod i 64)
  | 3 => rbB3 (Nat.mod i 64)
  | 4 => rbB4 (Nat.mod i 64)
  | 5 => rbB5 (Nat.mod i 64)
  | 6 => rbB6 (Nat.mod i 64)
  | _ => []

private def npSet : ℕ → List ℕ | 0 => [] | 1 => [0] | 2 => [1] | 3 => [2] | 4 => [3] | 5 => [4] | 6 => [5] | 7 => [6] | 8 => [7] | 9 => [8] | 10 => [11] | 11 => [12] | 12 => [14] | 13 => [15] | 14 => [17] | 15 => [18] | 16 => [19] | 17 => [21] | 18 => [22] | 19 => [24] | 20 => [25] | 21 => [27] | 22 => [28] | 23 => [0, 1] | 24 => [0, 2] | 25 => [0, 3] | 26 => [0, 12] | 27 => [0, 15] | 28 => [0, 18] | 29 => [0, 21] | 30 => [1, 2] | 31 => [1, 3] | 32 => [1, 8] | 33 => [1, 12] | 34 => [1, 15] | 35 => [1, 18] | 36 => [2, 3] | 37 => [2, 8] | 38 => [2, 11] | 39 => [2, 15] | 40 => [2, 18] | 41 => [3, 8] | 42 => [3, 11] | 43 => [3, 14] | 44 => [3, 15] | 45 => [3, 18] | 46 => [4, 5] | 47 => [4, 6] | 48 => [4, 7] | 49 => [4, 18] | 50 => [4, 22] | 51 => [4, 25] | 52 => [4, 28] | 53 => [5, 6] | 54 => [5, 7] | 55 => [5, 18] | 56 => [5, 21] | 57 => [5, 25] | 58 => [5, 28] | 59 => [6, 7] | 60 => [6, 18] | 61 => [6, 21] | 62 => [6, 24] | 63 => [6, 28] | 64 => [7, 18] | 65 => [7, 21] | 66 => [7, 24] | 67 => [7, 27] | 68 => [8, 12] | 69 => [8, 15] | 70 => [8, 18] | 71 => [11, 12] | 72 => [11, 15] | 73 => [11, 18] | 74 => [12, 14] | 75 => [12, 17] | 76 => [14, 15] | 77 => [14, 18] | 78 => [15, 17] | 79 => [17, 18] | 80 => [18, 19] | 81 => [18, 22] | 82 => [18, 25] | 83 => [18, 28] | 84 => [19, 21] | 85 => [19, 24] | 86 => [19, 27] | 87 => [21, 22] | 88 => [21, 25] | 89 => [21, 28] | 90 => [22, 24] | 91 => [22, 27] | 92 => [24, 25] | 93 => [24, 28] | 94 => [25, 27] | 95 => [27, 28] | _ => []

private def idx1 (a : ℕ) : ℕ := a + 1
private def idx2 (a b : ℕ) : ℕ := 30 + a * (57 - a) / 2 + (b - a - 1)
private def idx3 (a b c : ℕ) : ℕ :=
  436 + (3654 - (29 - a) * (28 - a) * (27 - a) / 6) +
    ((28 - a) * (27 - a) / 2 - (29 - b) * (28 - b) / 2) + (c - b - 1)

private def ins1 (a v : ℕ) : ℕ :=
  if Nat.beq a v then idx1 a else if Nat.blt a v then idx2 a v else idx2 v a

private def ins2 (a b v : ℕ) : ℕ :=
  if Nat.beq a v || Nat.beq b v then idx2 a b
  else if Nat.blt v a then idx3 v a b
  else if Nat.blt v b then idx3 a v b
  else idx3 a b v

private def mulSet (s : List ℕ) (v : ℕ) : ℕ :=
  match s with
  | [] => idx1 v
  | [a] => ins1 a v
  | [a, b] => ins2 a b v
  | _ => 0

private def applyTAcc (v acc : ℕ) : List ℕ → ℕ
  | [] => acc
  | c :: cs => eN (Nat.xor acc (redAll (mulSet (npSet c) v))) (fun acc' => applyTAcc v acc' cs)

private def bitsToNatAcc (acc : ℕ) : List ℕ → ℕ
  | [] => acc
  | c :: cs => eN (Nat.xor acc (Nat.shiftLeft 1 c)) (fun acc' => bitsToNatAcc acc' cs)

private def checkBitsAll : ℕ → Bool
  | 0 => true
  | i + 1 => Nat.beq (bitsToNatAcc 0 (redBits i)) (redAll i) &&
      (redBits i).all (fun c => Nat.blt c 96) && checkBitsAll i

private def checkDeg0 : ℕ → Bool
  | 0 => true
  | v + 1 => Nat.beq (redAll (idx1 v)) (applyTAcc v 0 (redBits 0)) && checkDeg0 v

private def checkDeg1V (a : ℕ) (rb : List ℕ) : ℕ → Bool
  | 0 => true
  | v + 1 => Nat.beq (redAll (ins1 a v)) (applyTAcc v 0 rb) && checkDeg1V a rb v

private def checkDeg1 : ℕ → Bool
  | 0 => true
  | a + 1 => checkDeg1V a (redBits (idx1 a)) 29 && checkDeg1 a

private def checkDeg2V (a b : ℕ) (rb : List ℕ) : ℕ → Bool
  | 0 => true
  | v + 1 => Nat.beq (redAll (ins2 a b v)) (applyTAcc v 0 rb) && checkDeg2V a b rb v

private def checkDeg2B (a : ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 =>
    (if Nat.blt a b then checkDeg2V a b (redBits (idx2 a b)) 29 else true) && checkDeg2B a b

private def checkDeg2 : ℕ → Bool
  | 0 => true
  | a + 1 => checkDeg2B a 29 && checkDeg2 a

private def sortInsNat (v : ℕ) : List ℕ → List ℕ
  | [] => [v]
  | x :: xs =>
    if Nat.beq v x then x :: xs
    else if Nat.blt v x then v :: x :: xs
    else x :: sortInsNat v xs

private def idxOfList : List ℕ → ℕ
  | [] => 0
  | [a] => idx1 a
  | [a, b] => idx2 a b
  | [a, b, c] => idx3 a b c
  | _ => 0

private def clauseXor29Acc (cur : List ℕ) : List (ℕ × Bool) → ℕ
  | [] => redAll (idxOfList cur)
  | (v, s) :: ls =>
    let r1 := clauseXor29Acc (sortInsNat v cur) ls
    if s then Nat.xor (clauseXor29Acc cur ls) r1 else r1

private def checkFkAx : Bool :=
  fkAxList.all (fun c =>
    clauseAllLt 29 c && Nat.beq (clauseXor29Acc [] c) 0 &&
    (match c with
     | [_] => true
     | [(a, _), (b, _)] => !Nat.beq a b
     | [(a, _), (b, _), (d, _)] => !Nat.beq a b && !Nat.beq a d && !Nat.beq b d
     | _ => false))

set_option maxHeartbeats 20000000 in
private lemma k4_bits : checkBitsAll 436 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
private lemma k4_d0 : checkDeg0 29 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
private lemma k4_d1 : checkDeg1 29 = true := by decide +kernel

set_option maxHeartbeats 40000000 in
private lemma k4_d2 : checkDeg2 29 = true := by decide +kernel

set_option maxHeartbeats 20000000 in
private lemma k4_ax : checkFkAx = true := by decide +kernel

private lemma k4_one : (redAll 0).testBit 0 = true := by decide +kernel

private lemma k4_redAll_lt_bound : ∀ i, i < 436 →
    bitsToNatAcc 0 (redBits i) = redAll i ∧ (∀ c ∈ redBits i, c < 96) := by
  have aux : ∀ n, checkBitsAll n = true → ∀ i < n,
      bitsToNatAcc 0 (redBits i) = redAll i ∧ (∀ c ∈ redBits i, c < 96) := by
    intro n
    induction n with
    | zero => intro _ i hi; omega
    | succ n ih =>
      intro h i hi
      simp only [checkBitsAll, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at h
      by_cases hin : i = n
      · subst hin; exact ⟨h.1.1, h.1.2⟩
      · exact ih h.2 i (by omega)
  exact aux 436 k4_bits

private lemma k4_deg0_eq : ∀ v < 29, redAll (idx1 v) = applyTAcc v 0 (redBits 0) := by
  have aux : ∀ n, checkDeg0 n = true → ∀ v < n, redAll (idx1 v) = applyTAcc v 0 (redBits 0) := by
    intro n; induction n with
    | zero => intro _ v hv; omega
    | succ n ih =>
      intro h v hv
      simp only [checkDeg0, Bool.and_eq_true, Nat.beq_eq] at h
      by_cases hvn : v = n
      · subst hvn; exact h.1
      · exact ih h.2 v (by omega)
  exact aux 29 k4_d0

private lemma k4_deg1_eq : ∀ a < 29, ∀ v < 29, redAll (ins1 a v) = applyTAcc v 0 (redBits (idx1 a)) := by
  have auxV : ∀ a rb n, checkDeg1V a rb n = true → ∀ v < n, redAll (ins1 a v) = applyTAcc v 0 rb := by
    intro a rb n; induction n with
    | zero => intro _ v hv; omega
    | succ n ih =>
      intro h v hv
      simp only [checkDeg1V, Bool.and_eq_true, Nat.beq_eq] at h
      by_cases hvn : v = n
      · subst hvn; exact h.1
      · exact ih h.2 v (by omega)
  have auxA : ∀ m, checkDeg1 m = true → ∀ a < m, ∀ v < 29, redAll (ins1 a v) = applyTAcc v 0 (redBits (idx1 a)) := by
    intro m; induction m with
    | zero => intro _ a ha; omega
    | succ m ih =>
      intro h a ha
      simp only [checkDeg1, Bool.and_eq_true] at h
      by_cases ham : a = m
      · subst ham; exact auxV a _ 29 h.1
      · exact ih h.2 a (by omega)
  exact auxA 29 k4_d1

private lemma k4_deg2_eq : ∀ a < 29, ∀ b < 29, a < b → ∀ v < 29,
    redAll (ins2 a b v) = applyTAcc v 0 (redBits (idx2 a b)) := by
  have auxV : ∀ a b rb n, checkDeg2V a b rb n = true → ∀ v < n, redAll (ins2 a b v) = applyTAcc v 0 rb := by
    intro a b rb n; induction n with
    | zero => intro _ v hv; omega
    | succ n ih =>
      intro h v hv
      simp only [checkDeg2V, Bool.and_eq_true, Nat.beq_eq] at h
      by_cases hvn : v = n
      · subst hvn; exact h.1
      · exact ih h.2 v (by omega)
  have auxB : ∀ a n, checkDeg2B a n = true → ∀ b < n, a < b → ∀ v < 29,
      redAll (ins2 a b v) = applyTAcc v 0 (redBits (idx2 a b)) := by
    intro a n; induction n with
    | zero => intro _ b hb; omega
    | succ n ih =>
      intro h b hb hab
      simp only [checkDeg2B, Bool.and_eq_true] at h
      by_cases hbn : b = n
      · subst hbn
        have hlt : Nat.blt a b = true := Nat.blt_eq.mpr hab
        rw [if_pos hlt] at h
        exact auxV a b _ 29 h.1
      · exact ih h.2 b (by omega) hab
  have auxA : ∀ m, checkDeg2 m = true → ∀ a < m, ∀ b < 29, a < b → ∀ v < 29,
      redAll (ins2 a b v) = applyTAcc v 0 (redBits (idx2 a b)) := by
    intro m; induction m with
    | zero => intro _ a ha; omega
    | succ m ih =>
      intro h a ha
      simp only [checkDeg2, Bool.and_eq_true] at h
      by_cases ham : a = m
      · subst ham; exact auxB a 29 h.1
      · exact ih h.2 a (by omega)
  exact auxA 29 k4_d2

-- Vector space F_2^96 and linear maps
private def toVec (x : ℕ) : Fin 96 → ZMod 2 :=
  fun c => if x.testBit c.val then 1 else 0

private lemma toVec_zero : toVec 0 = 0 := by
  funext c; simp [toVec]

private lemma toVec_xor (a b : ℕ) : toVec (Nat.xor a b) = toVec a + toVec b := by
  funext c
  simp only [toVec, Pi.add_apply, nat_testBit_xor]
  cases a.testBit c.val <;> cases b.testBit c.val <;> decide

private lemma toVec_shiftLeft_one {c : ℕ} (hc : c < 96) :
    toVec (Nat.shiftLeft 1 c) = Pi.single ⟨c, hc⟩ (1 : ZMod 2) := by
  have hsh : Nat.shiftLeft 1 c = 2 ^ c := by
    change 1 <<< c = 2 ^ c; rw [Nat.shiftLeft_eq, one_mul]
  rw [hsh]
  funext j
  simp only [toVec, Pi.single_apply, Nat.testBit_two_pow]
  by_cases h : j.val = c
  · have hj : j = ⟨c, hc⟩ := Fin.ext h
    simp [h, hj]
  · have hj : j ≠ ⟨c, hc⟩ := fun heq => h (congrArg Fin.val heq)
    simp [h, hj, Ne.symm h]

private lemma bitsToNatAcc_toVec (l : List ℕ) (hl : ∀ c ∈ l, c < 96) :
    ∀ acc, toVec (bitsToNatAcc acc l) = toVec acc + (l.map (fun c => if h : c < 96 then Pi.single ⟨c, h⟩ (1 : ZMod 2) else 0)).sum := by
  induction l with
  | nil => intro acc; simp [bitsToNatAcc]
  | cons c cs ih =>
    intro acc
    simp only [bitsToNatAcc, eN_eq, List.map_cons, List.sum_cons]
    have hc : c < 96 := hl c List.mem_cons_self
    rw [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)), toVec_xor, toVec_shiftLeft_one hc, dif_pos hc]
    abel

private lemma applyTAcc_toVec (v : ℕ) (l : List ℕ) :
    ∀ acc, toVec (applyTAcc v acc l) = toVec acc + (l.map (fun c => toVec (redAll (mulSet (npSet c) v)))).sum := by
  induction l with
  | nil => intro acc; simp [applyTAcc]
  | cons c cs ih =>
    intro acc
    simp only [applyTAcc, eN_eq, List.map_cons, List.sum_cons]
    rw [ih, toVec_xor]; abel

private def applyTVec (v : Fin 29) (u : Fin 96 → ZMod 2) : Fin 96 → ZMod 2 :=
  ∑ c : Fin 96, u c • toVec (redAll (mulSet (npSet c.val) v.val))

private lemma applyTVec_zero (v : Fin 29) : applyTVec v 0 = 0 := by
  simp [applyTVec]

private lemma applyTVec_add (v : Fin 29) (u1 u2 : Fin 96 → ZMod 2) :
    applyTVec v (u1 + u2) = applyTVec v u1 + applyTVec v u2 := by
  simp only [applyTVec, Pi.add_apply, add_smul, Finset.sum_add_distrib]

private lemma applyTVec_sum {ι : Type} (v : Fin 29) (S : Finset ι) (f : ι → Fin 96 → ZMod 2) :
    applyTVec v (∑ i ∈ S, f i) = ∑ i ∈ S, applyTVec v (f i) := by
  induction S using Finset.cons_induction with
  | empty => simp [applyTVec_zero]
  | cons a s ha ih => simp [applyTVec_add, ih]

private lemma applyTVec_single (v : Fin 29) (c : Fin 96) :
    applyTVec v (Pi.single c (1 : ZMod 2)) = toVec (redAll (mulSet (npSet c.val) v.val)) := by
  unfold applyTVec
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hbc; simp [Pi.single_eq_of_ne hbc]
  · intro hc; exact absurd (Finset.mem_univ c) hc

private lemma applyTVec_bitsToNat {i : ℕ} (hi : i < 436) (v : Fin 29) :
    applyTVec v (toVec (redAll i)) = toVec (applyTAcc v.val 0 (redBits i)) := by
  obtain ⟨hbits, hlt⟩ := k4_redAll_lt_bound i hi
  rw [← hbits, bitsToNatAcc_toVec _ hlt 0, toVec_zero, zero_add]
  rw [applyTAcc_toVec, toVec_zero, zero_add]
  have aux : ∀ l : List ℕ, (∀ c ∈ l, c < 96) →
      applyTVec v (l.map (fun c => if h : c < 96 then Pi.single ⟨c, h⟩ (1 : ZMod 2) else 0)).sum =
      (l.map (fun c => toVec (redAll (mulSet (npSet c) v.val)))).sum := by
    intro l
    induction l with
    | nil => intro _; simp [applyTVec_zero]
    | cons c cs ih =>
      intro hcl
      have hc : c < 96 := hcl c List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, dif_pos hc]
      rw [applyTVec_add, applyTVec_single v ⟨c, hc⟩, ih (fun x hx => hcl x (List.mem_cons_of_mem _ hx))]
  exact aux (redBits i) hlt

-- Sorted Finset indexing
private def idxOfSet (S : Finset (Fin 29)) : ℕ :=
  idxOfList ((S.sort (· ≤ ·)).map Fin.val)

private lemma sort_empty_29 : (∅ : Finset (Fin 29)).sort (· ≤ ·) = [] := by simp

private lemma sort_singleton_29 (a : Fin 29) : ({a} : Finset (Fin 29)).sort (· ≤ ·) = [a] := by simp

private lemma sort_pair_29 {a b : Fin 29} (hab : a < b) :
    ({a, b} : Finset (Fin 29)).sort (· ≤ ·) = [a, b] := by
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
    (Finset.pairwise_sort _ _) (by simp [le_of_lt hab])
  refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (by simp [ne_of_lt hab])).mpr ?_
  intro x; simp [Finset.mem_sort]

private lemma sort_triple_29 {a b c : Fin 29} (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset (Fin 29)).sort (· ≤ ·) = [a, b, c] := by
  have hac : a < c := lt_trans hab hbc
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
    (Finset.pairwise_sort _ _) (by simp [le_of_lt hab, le_of_lt hac, le_of_lt hbc])
  refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _)
    (by simp [ne_of_lt hab, ne_of_lt hac, ne_of_lt hbc])).mpr ?_
  intro x; simp [Finset.mem_sort]

private lemma idxOfSet_empty : idxOfSet ∅ = 0 := by
  simp [idxOfSet, idxOfList]

private lemma idxOfSet_singleton (a : Fin 29) : idxOfSet {a} = idx1 a.val := by
  simp [idxOfSet, idxOfList]

private lemma idxOfSet_pair {a b : Fin 29} (hab : a < b) :
    idxOfSet {a, b} = idx2 a.val b.val := by
  simp [idxOfSet, sort_pair_29 hab, idxOfList]

private lemma idxOfSet_triple {a b c : Fin 29} (hab : a < b) (hbc : b < c) :
    idxOfSet {a, b, c} = idx3 a.val b.val c.val := by
  simp [idxOfSet, sort_triple_29 hab hbc, idxOfList]

private lemma idx2_lt_436 {a b : ℕ} (ha : a < 29) (hb : b < 29) (hab : a < b) :
    idx2 a b < 436 := by
  have h : ∀ x : Fin 29, ∀ y : Fin 29, x.val < y.val → idx2 x.val y.val < 436 := by decide
  exact h ⟨a, ha⟩ ⟨b, hb⟩ hab

private lemma finset_card_le_2_cases (S : Finset (Fin 29)) (hS : S.card ≤ 2) :
    S = ∅ ∨ (∃ a : Fin 29, S = {a}) ∨ (∃ a b : Fin 29, a < b ∧ S = {a, b}) := by
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort _
  have hmem : ∀ x, x ∈ S ↔ x ∈ S.sort (· ≤ ·) := fun x => (Finset.mem_sort _).symm
  have hsort := Finset.pairwise_sort S (· ≤ ·)
  have hnd := Finset.sort_nodup S (· ≤ ·)
  rcases hl : S.sort (· ≤ ·) with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · left; ext x; rw [hmem, hl]; simp
  · right; left; refine ⟨a, ?_⟩; ext x; rw [hmem, hl]; simp
  · right; right
    rw [hl] at hsort hnd
    have hab_le : a ≤ b := by simp at hsort; exact hsort
    have hab_ne : a ≠ b := by simp at hnd; exact hnd
    refine ⟨a, b, lt_of_le_of_ne hab_le hab_ne, ?_⟩
    ext x; rw [hmem, hl]; simp
  · rw [hl] at hlen; simp at hlen; omega

private lemma redAll_insert_comm (S : Finset (Fin 29)) (hS : S.card ≤ 2) (v : Fin 29) :
    toVec (redAll (idxOfSet (insert v S))) = applyTVec v (toVec (redAll (idxOfSet S))) := by
  rcases finset_card_le_2_cases S hS with rfl | ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩
  · have hins : insert v (∅ : Finset (Fin 29)) = {v} := rfl
    rw [hins, idxOfSet_singleton, idxOfSet_empty]
    rw [applyTVec_bitsToNat (by omega) v, k4_deg0_eq v.val v.isLt]
  · rw [idxOfSet_singleton]
    have hidx : idx1 a.val < 436 := by unfold idx1; omega
    rw [applyTVec_bitsToNat hidx v, ← k4_deg1_eq a.val a.isLt v.val v.isLt]
    congr 2
    unfold ins1
    rcases lt_trichotomy a v with hav | rfl | hva
    · have hne : Nat.beq a.val v.val = false := by
        cases hb : Nat.beq a.val v.val; · rfl
        · have := Nat.beq_eq.mp hb; exact absurd (Fin.ext this) (ne_of_lt hav)
      have hlt : Nat.blt a.val v.val = true := Nat.blt_eq.mpr hav
      rw [if_neg (by simp [hne]), if_pos hlt]
      have : insert v ({a} : Finset (Fin 29)) = {a, v} := by ext x; simp [or_comm]
      rw [this, idxOfSet_pair hav]
    · simp [idxOfSet_singleton]
    · have hne : Nat.beq a.val v.val = false := by
        cases hb : Nat.beq a.val v.val; · rfl
        · have := Nat.beq_eq.mp hb; exact absurd (Fin.ext this) (ne_of_gt hva)
      have hlt : Nat.blt a.val v.val = false := by
        cases hb : Nat.blt a.val v.val; · rfl
        · have := Nat.blt_eq.mp hb; omega
      rw [if_neg (by simp [hne]), if_neg (by simp [hlt])]
      have : insert v ({a} : Finset (Fin 29)) = {v, a} := rfl
      rw [this, idxOfSet_pair hva]
  · rw [idxOfSet_pair hab]
    have hidx : idx2 a.val b.val < 436 := idx2_lt_436 a.isLt b.isLt hab
    rw [applyTVec_bitsToNat hidx v, ← k4_deg2_eq a.val a.isLt b.val b.isLt hab v.val v.isLt]
    congr 2
    unfold ins2
    by_cases hva : v = a
    · subst hva
      have heq : insert v ({v, b} : Finset (Fin 29)) = {v, b} := by ext x; simp
      rw [heq, idxOfSet_pair hab]; simp
    · by_cases hvb : v = b
      · subst hvb
        have heq : insert v ({a, v} : Finset (Fin 29)) = {a, v} := by ext x; simp
        rw [heq, idxOfSet_pair hab]; simp
      · have hne1 : Nat.beq a.val v.val = false := by
          cases hb : Nat.beq a.val v.val; · rfl
          · exact absurd (Fin.ext (Nat.beq_eq.mp hb)).symm hva
        have hne2 : Nat.beq b.val v.val = false := by
          cases hb : Nat.beq b.val v.val; · rfl
          · exact absurd (Fin.ext (Nat.beq_eq.mp hb)).symm hvb
        rw [if_neg (by simp [hne1, hne2])]
        by_cases hlt1 : v < a
        · rw [if_pos (Nat.blt_eq.mpr hlt1)]
          exact idxOfSet_triple hlt1 hab
        · rw [if_neg (by
            cases hb : Nat.blt v.val a.val; · simp
            · exact absurd (Nat.blt_eq.mp hb) hlt1)]
          have hav : a < v := lt_of_le_of_ne (not_lt.mp hlt1) (Ne.symm hva)
          by_cases hlt2 : v < b
          · rw [if_pos (Nat.blt_eq.mpr hlt2)]
            have heq : insert v ({a, b} : Finset (Fin 29)) = {a, v, b} := by ext x; simp [or_left_comm]
            rw [heq, idxOfSet_triple hav hlt2]
          · rw [if_neg (by
              cases hb : Nat.blt v.val b.val; · simp
              · exact absurd (Nat.blt_eq.mp hb) hlt2)]
            have hbv : b < v := lt_of_le_of_ne (not_lt.mp hlt2) (Ne.symm hvb)
            have heq : insert v ({a, b} : Finset (Fin 29)) = {a, b, v} := by ext x; simp [or_comm, or_left_comm]
            rw [heq, idxOfSet_triple hab hbv]

-- Linear functional Phi on MvPolynomial (Fin 29) (ZMod 2)
private def evalMon29 (m : Fin 29 →₀ ℕ) : Fin 96 → ZMod 2 :=
  if m.support.card ≤ 3 then toVec (redAll (idxOfSet m.support)) else 0

private noncomputable def phi29 (p : MvPolynomial (Fin 29) (ZMod 2)) : Fin 96 → ZMod 2 :=
  ∑ m ∈ p.support, (p.coeff m) • evalMon29 m

private lemma phi29_eq_sum_of_subset {p : MvPolynomial (Fin 29) (ZMod 2)} {S : Finset (Fin 29 →₀ ℕ)}
    (hS : p.support ⊆ S) : phi29 p = ∑ m ∈ S, (p.coeff m) • evalMon29 m := by
  unfold phi29
  refine Finset.sum_subset hS ?_
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, zero_smul]

private lemma phi29_zero : phi29 0 = 0 := by simp [phi29]

private lemma phi29_add (p q : MvPolynomial (Fin 29) (ZMod 2)) :
    phi29 (p + q) = phi29 p + phi29 q := by
  let S := p.support ∪ q.support
  have h1 : (p + q).support ⊆ S := MvPolynomial.support_add
  rw [phi29_eq_sum_of_subset h1, phi29_eq_sum_of_subset Finset.subset_union_left,
      phi29_eq_sum_of_subset Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul]

private lemma phi29_monomial (m : Fin 29 →₀ ℕ) (c : ZMod 2) :
    phi29 (monomial m c) = c • evalMon29 m := by
  by_cases hc : c = 0
  · subst hc; simp [phi29_zero]
  · unfold phi29
    rw [MvPolynomial.support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

private lemma phi29_bool (v : Fin 29) : phi29 (X v * X v + X v) = 0 := by
  rw [phi29_add]
  have h1 : (X v * X v : MvPolynomial (Fin 29) (ZMod 2)) = monomial (Finsupp.single v 2) 1 := by
    simp only [MvPolynomial.X, monomial_mul_monomial, one_mul, ← Finsupp.single_add]
  have h2 : (X v : MvPolynomial (Fin 29) (ZMod 2)) = monomial (Finsupp.single v 1) 1 := rfl
  rw [h1, h2, phi29_monomial, phi29_monomial, one_smul, one_smul]
  have hs : (Finsupp.single v 2).support = (Finsupp.single v 1).support := by
    simp [Finsupp.support_single_ne_zero]
  unfold evalMon29
  rw [hs]
  funext c
  simp only [Pi.add_apply, Pi.zero_apply]
  exact zmod2_add_self _

private lemma phi29_mulX {v : Fin 29} {p : MvPolynomial (Fin 29) (ZMod 2)}
    (hdeg : (X v * p).totalDegree ≤ 3) :
    phi29 (X v * p) = applyTVec v (phi29 p) := by
  have hp_eq : p = ∑ m ∈ p.support, monomial m (p.coeff m) := MvPolynomial.as_sum p
  have hxp : X v * p = ∑ m ∈ p.support, monomial (m + Finsupp.single v 1) (p.coeff m) := by
    conv_lhs => rw [hp_eq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    simp only [MvPolynomial.X, monomial_mul_monomial, one_mul, add_comm]
  have hphi_sum : ∀ (S : Finset (Fin 29 →₀ ℕ)) (f : (Fin 29 →₀ ℕ) → MvPolynomial (Fin 29) (ZMod 2)),
      phi29 (∑ m ∈ S, f m) = ∑ m ∈ S, phi29 (f m) := by
    intro S f
    induction S using Finset.cons_induction with
    | empty => simp [phi29_zero]
    | cons a s ha ih => rw [Finset.sum_cons, phi29_add, ih, Finset.sum_cons]
  rw [hxp, hphi_sum]
  change ∑ m ∈ p.support, phi29 (monomial (m + Finsupp.single v 1) (p.coeff m)) =
      applyTVec v (∑ m ∈ p.support, (p.coeff m) • evalMon29 m)
  rw [applyTVec_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [phi29_monomial]
  have hc_ne : p.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hc1 : p.coeff m = 1 := by
    have hz2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact hz2 (p.coeff m) hc_ne
  rw [hc1, one_smul, one_smul]
  -- Show m.support.card <= 2 from (X v * p).totalDegree <= 3
  have hcoeff_xp : (X v * p).coeff (m + Finsupp.single v 1) = p.coeff m := by
    rw [add_comm, MvPolynomial.coeff_X_mul]
  have hm_sum_le : (m + Finsupp.single v 1).sum (fun _ k => k) ≤ 3 :=
    (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr (by rw [hcoeff_xp]; exact hc_ne))).trans hdeg
  have hmsum : m.sum (fun _ k => k) + 1 ≤ 3 := by
    have hadd : (m + Finsupp.single v 1).sum (fun _ k => k) = m.sum (fun _ k => k) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    omega
  have hcard_le_sum : m.support.card ≤ m.sum (fun _ k => k) := by
    unfold Finsupp.sum
    calc m.support.card = ∑ _x ∈ m.support, 1 := by simp
      _ ≤ ∑ x ∈ m.support, m x := Finset.sum_le_sum (fun x hx => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx))
  have hm2 : m.support.card ≤ 2 := by omega
  have hsupp_ins : (m + Finsupp.single v 1).support = insert v m.support := by
    ext u
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finset.mem_insert]
    by_cases huv : v = u
    · subst huv; simp
    · simp [huv, Ne.symm huv]
  have hm3 : (m + Finsupp.single v 1).support.card ≤ 3 := by
    rw [hsupp_ins]; exact (Finset.card_insert_le _ _).trans (by omega)
  unfold evalMon29
  rw [if_pos hm3, if_pos (by omega : m.support.card ≤ 3), hsupp_ins]
  exact redAll_insert_comm m.support hm2 v

private def mkClause29 (c : List (ℕ × Bool)) : Clause (Fin 29) :=
  (c.filterMap (fun p => if h : p.1 < 29 then some (⟨p.1, h⟩, p.2) else none)).toFinset

private lemma phi29_clause_eq_zero {c : List (ℕ × Bool)} (hc : c ∈ fkAxList) :
    phi29 (clausePoly (mkClause29 c)) = 0 := by
  have hchk := List.all_eq_true.mp k4_ax c hc
  simp only [Bool.and_eq_true, Nat.beq_eq, clauseAllLt_iff] at hchk
  rcases hchk with ⟨⟨hlt, hxor0⟩, hdist⟩
  have hphi_mon_prod : ∀ (S : Finset (Fin 29)), S.card ≤ 3 →
      phi29 (∏ v ∈ S, (X v : MvPolynomial (Fin 29) (ZMod 2))) = toVec (redAll (idxOfSet S)) := by
    intro S hS
    have hprod : ∀ (T : Finset (Fin 29)), (∏ v ∈ T, (X v : MvPolynomial (Fin 29) (ZMod 2))) =
        monomial (∑ v ∈ T, Finsupp.single v 1) 1 := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | insert a T haT ih =>
        rw [Finset.prod_insert haT, Finset.sum_insert haT, ih, MvPolynomial.X, monomial_mul_monomial, one_mul]
    rw [hprod S, phi29_monomial, one_smul]
    have hfsum : ∀ (T : Finset (Fin 29)) (u : Fin 29),
        (∑ v ∈ T, Finsupp.single v 1) u = if u ∈ T then 1 else 0 := by
      intro T u
      induction T using Finset.induction_on with
      | empty => simp
      | insert a T haT ih =>
        rw [Finset.sum_insert haT, Finsupp.add_apply, ih, Finsupp.single_apply]
        by_cases hua : u = a
        · subst hua; simp [haT]
        · have hau : a ≠ u := Ne.symm hua
          simp [hua, hau]
    have hsupp : (∑ v ∈ S, Finsupp.single v 1).support = S := by
      ext u
      rw [Finsupp.mem_support_iff, hfsum]
      split_ifs with hu <;> simp [hu]
    unfold evalMon29
    rw [hsupp, if_pos hS]
  have hsort_perm : ∀ (v : Fin 29) (l : List (Fin 29)), l.Pairwise (· < ·) → v ∉ l →
      (sortInsNat v.val (l.map Fin.val)) = ((insert v l.toFinset).sort (· ≤ ·)).map Fin.val := by
    intro v l hl hv
    have h1 : ∀ (x : ℕ) (xs : List ℕ), xs.Pairwise (· < ·) → x ∉ xs →
        (sortInsNat x xs).Pairwise (· < ·) ∧ (sortInsNat x xs).Perm (x :: xs) := by
      intro x xs
      induction xs with
      | nil => intro _ _; exact ⟨by simp [sortInsNat], List.Perm.refl _⟩
      | cons y ys ih =>
        intro hys hnx
        rw [List.pairwise_cons] at hys
        simp only [List.mem_cons, not_or] at hnx
        unfold sortInsNat
        have hne : Nat.beq x y = false := by
          cases hb : Nat.beq x y; · rfl
          · exact absurd (Nat.beq_eq.mp hb) hnx.1
        rw [if_neg (by simp [hne])]
        by_cases hlt : x < y
        · rw [if_pos (Nat.blt_eq.mpr hlt)]
          refine ⟨?_, List.Perm.refl _⟩
          rw [List.pairwise_cons, List.pairwise_cons]
          exact ⟨fun z hz => by rcases List.mem_cons.mp hz with rfl | hz'; exact hlt; exact lt_trans hlt (hys.1 z hz'),
            hys.1, hys.2⟩
        · have hblt : Nat.blt x y = false := by
            cases hb : Nat.blt x y with
            | false => rfl
            | true => exact absurd (Nat.blt_eq.mp hb) hlt
          rw [if_neg (by simp [hblt])]
          have hyx : y < x := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hnx.1)
          obtain ⟨hs', hp'⟩ := ih hys.2 hnx.2
          refine ⟨?_, ?_⟩
          · rw [List.pairwise_cons]
            refine ⟨fun z hz => ?_, hs'⟩
            rcases List.mem_cons.mp (hp'.subset hz) with rfl | hz'
            · exact hyx
            · exact hys.1 z hz'
          · exact (hp'.cons y).trans (List.Perm.swap x y ys)
    have hmap_sorted : (l.map Fin.val).Pairwise (· < ·) := by
      rw [List.pairwise_map]; exact hl
    have hmap_nmem : v.val ∉ l.map Fin.val := by
      intro hm; rw [List.mem_map] at hm; rcases hm with ⟨u, hu, heq⟩
      exact hv (Fin.ext heq ▸ hu)
    obtain ⟨hs1, hp1⟩ := h1 v.val (l.map Fin.val) hmap_sorted hmap_nmem
    have hs2 : (((insert v l.toFinset).sort (· ≤ ·)).map Fin.val).Pairwise (· < ·) := by
      rw [List.pairwise_map]
      have hnd := Finset.sort_nodup (insert v l.toFinset) (· ≤ ·)
      have hle := Finset.pairwise_sort (insert v l.toFinset) (· ≤ ·)
      exact (List.pairwise_and_iff.mpr ⟨hle, hnd⟩).imp (fun h => lt_of_le_of_ne h.1 (Fin.val_ne_of_ne h.2))
    apply List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
      (hs1.imp le_of_lt) (hs2.imp le_of_lt)
    refine (List.perm_ext_iff_of_nodup (hs1.imp ne_of_lt) (hs2.imp ne_of_lt)).mpr ?_
    intro x
    rw [hp1.mem_iff]
    simp only [List.mem_cons, List.mem_map, Finset.mem_sort, Finset.mem_insert, List.mem_toFinset]
    constructor
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact ⟨v, Or.inl rfl, rfl⟩
      · exact ⟨u, Or.inr hu, rfl⟩
    · rintro ⟨u, rfl | hu, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨u, hu, rfl⟩
  have hacc : ∀ (cur : List (Fin 29)) (ls : List (ℕ × Bool)),
      cur.Pairwise (· < ·) → cur.length + ls.length ≤ 3 →
      (∀ x ∈ ls, x.1 < 29) →
      (∀ x ∈ ls, ∀ u ∈ cur, x.1 ≠ u.val) →
      (ls.map Prod.fst).Nodup →
      phi29 ((∏ u ∈ cur.toFinset, (X u : MvPolynomial (Fin 29) (ZMod 2))) *
             clausePoly (mkClause29 ls)) =
      toVec (clauseXor29Acc (cur.map Fin.val) ls) := by
    intro cur ls
    induction ls generalizing cur with
    | nil =>
      intro hcur hlen _ _ _
      simp only [mkClause29, List.filterMap_nil, List.toFinset_nil, clausePoly, Finset.prod_empty,
        mul_one, clauseXor29Acc]
      have hcard : cur.toFinset.card ≤ 3 := (List.toFinset_card_le cur).trans (by omega)
      rw [hphi_mon_prod cur.toFinset hcard]
      congr 2
      unfold idxOfSet
      congr 1
      have hsort_eq : cur.toFinset.sort (· ≤ ·) = cur := by
        apply List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
          (Finset.pairwise_sort _ _) (hcur.imp le_of_lt)
        refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (hcur.imp ne_of_lt)).mpr ?_
        intro x; simp [Finset.mem_sort]
      rw [hsort_eq]
    | cons hd tl ih =>
      intro hcur hlen hlt' hdisj hnd
      rcases hd with ⟨v, s⟩
      have hv : v < 29 := hlt' (v, s) List.mem_cons_self
      let vf : Fin 29 := ⟨v, hv⟩
      have hvf_nmem : vf ∉ cur := fun h => hdisj (v, s) List.mem_cons_self vf h rfl
      have htl_lt : ∀ x ∈ tl, x.1 < 29 := fun x hx => hlt' x (List.mem_cons_of_mem _ hx)
      have hnd_tl : v ∉ tl.map Prod.fst ∧ (tl.map Prod.fst).Nodup := by
        simpa using hnd
      have hvf_nmem_mk : (vf, s) ∉ mkClause29 tl := by
        simp only [mkClause29, List.mem_toFinset, List.mem_filterMap, not_exists, not_and]
        intro x hx hsome
        split_ifs at hsome with hlt_x
        · simp only [Option.some.injEq, Prod.mk.injEq] at hsome
          exact hnd_tl.1 (List.mem_map.mpr ⟨x, hx, congrArg Fin.val hsome.1⟩)
      have hmk_cons : mkClause29 ((v, s) :: tl) = insert (vf, s) (mkClause29 tl) := by
        simp [mkClause29, hv, vf]
      have hcp_cons : clausePoly (mkClause29 ((v, s) :: tl)) =
          litPoly (vf, s) * clausePoly (mkClause29 tl) := by
        rw [hmk_cons]; unfold clausePoly litPoly; rw [Finset.prod_insert hvf_nmem_mk]
      let cur' : List (Fin 29) := (insert vf cur.toFinset).sort (· ≤ ·)
      have hcur'_sorted : cur'.Pairwise (· < ·) := by
        have h1 := Finset.sort_nodup (insert vf cur.toFinset) (· ≤ ·)
        have h2 := Finset.pairwise_sort (insert vf cur.toFinset) (· ≤ ·)
        exact (List.pairwise_and_iff.mpr ⟨h2, h1⟩).imp (fun h => lt_of_le_of_ne h.1 h.2)
      have hcur'_toFinset : cur'.toFinset = insert vf cur.toFinset := by
        ext x; simp [cur']
      have hcur'_len : cur'.length = cur.length + 1 := by
        have hndc : cur.Nodup := hcur.imp ne_of_lt
        rw [Finset.length_sort, Finset.card_insert_of_notMem (by simpa using hvf_nmem),
            List.toFinset_card_of_nodup hndc]
      have hcur'_disj : ∀ x ∈ tl, ∀ u ∈ cur', x.1 ≠ u.val := by
        intro x hx u hu heq
        simp only [cur', Finset.mem_sort, Finset.mem_insert, List.mem_toFinset] at hu
        rcases hu with rfl | hu
        · exact hnd_tl.1 (List.mem_map.mpr ⟨x, hx, heq⟩)
        · exact hdisj x (List.mem_cons_of_mem _ hx) u hu heq
      have hcur'_map : sortInsNat v (cur.map Fin.val) = cur'.map Fin.val :=
        hsort_perm vf cur hcur hvf_nmem
      have hprod_ins : (∏ u ∈ cur.toFinset, (X u : MvPolynomial (Fin 29) (ZMod 2))) * X vf =
          ∏ u ∈ cur'.toFinset, (X u : MvPolynomial (Fin 29) (ZMod 2)) := by
        rw [hcur'_toFinset, Finset.prod_insert (by simpa using hvf_nmem), mul_comm]
      have ih1 := ih cur' hcur'_sorted (by simp at hlen; omega) htl_lt hcur'_disj hnd_tl.2
      rw [← hcur'_map] at ih1
      rw [hcp_cons]
      cases s
      · simp only [litPoly, Bool.false_eq_true, ↓reduceIte, clauseXor29Acc]
        rw [← mul_assoc, hprod_ins]; exact ih1
      · simp only [litPoly, ↓reduceIte, clauseXor29Acc, add_mul, one_mul, mul_add]
        rw [phi29_add, ← mul_assoc, hprod_ins, ih1,
            ih cur hcur (by simp at hlen; omega) htl_lt
              (fun x hx u hu => hdisj x (List.mem_cons_of_mem _ hx) u hu) hnd_tl.2,
            toVec_xor]
  have hlen3 : c.length ≤ 3 := by
    rcases c with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩ <;> simp at hdist ⊢
  have hnd : (c.map Prod.fst).Nodup := by
    rcases c with _ | ⟨⟨a, _⟩, _ | ⟨⟨b, _⟩, _ | ⟨⟨d, _⟩, _ | _⟩⟩⟩ <;>
      simp [Bool.and_eq_true] at hdist ⊢
    · exact nat_beq_eq_false hdist
    · exact ⟨⟨nat_beq_eq_false hdist.1.1, nat_beq_eq_false hdist.1.2⟩, nat_beq_eq_false hdist.2⟩
  have hres := hacc [] c (by simp) (by simpa using hlen3) hlt (by simp) hnd
  simp only [List.toFinset_nil, Finset.prod_empty, one_mul, List.map_nil] at hres
  rw [hres, hxor0, toVec_zero]

private noncomputable def projK :
    MvPolynomial (Fin 8 ⊕ (ℕ × ℕ)) (ZMod 2) →ₐ[ZMod 2] MvPolynomial (Fin 29) (ZMod 2) :=
  MvPolynomial.aeval (fun v => match kVarInv v with | some i => X i | none => 0)

private lemma totalDegree_projK_le (p : MvPolynomial (Fin 8 ⊕ (ℕ × ℕ)) (ZMod 2)) :
    (projK p).totalDegree ≤ p.totalDegree := by
  have hp : p = ∑ m ∈ p.support, monomial m (p.coeff m) := MvPolynomial.as_sum p
  conv_lhs => rw [hp]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro m hm
  have hmon : projK (monomial m (p.coeff m)) =
      C (p.coeff m) * ∏ v ∈ m.support, (match kVarInv v with | some i => (X i : MvPolynomial (Fin 29) (ZMod 2)) | none => 0) ^ (m v) := by
    rw [projK, aeval_monomial, algebraMap_eq]
    rfl
  rw [hmon]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_prod_le _ _).trans ?_
  have hsum : ∑ v ∈ m.support,
      ((match kVarInv v with | some i => (X i : MvPolynomial (Fin 29) (ZMod 2)) | none => 0) ^ (m v)).totalDegree ≤
      m.sum (fun _ k => k) := by
    unfold Finsupp.sum
    refine Finset.sum_le_sum ?_
    intro v _
    refine (totalDegree_pow _ _).trans ?_
    cases kVarInv v with
    | none => simp
    | some i => simp
  exact hsum.trans (MvPolynomial.le_totalDegree hm)

private lemma projK_clause {c : List (ℕ × Bool)} (hc : c ∈ fkAxList) :
    projK (clausePoly (mkClause kVar c)) = clausePoly (mkClause29 c) := by
  have hchk := List.all_eq_true.mp k4_ax c hc
  simp only [Bool.and_eq_true, clauseAllLt_iff] at hchk
  have hlt : ∀ x ∈ c, x.1 < 29 := hchk.1.1
  have hbij : (mkClause kVar c) = (mkClause29 c).image (fun p => (kVar p.1.val, p.2)) := by
    ext ⟨v, s⟩
    simp only [mkClause, mkClause29, Finset.mem_image, List.mem_toFinset, List.mem_map, List.mem_filterMap]
    constructor
    · rintro ⟨⟨a, sa⟩, hx, heq⟩
      have ha : a < 29 := hlt (a, sa) hx
      refine ⟨(⟨a, ha⟩, sa), ⟨(a, sa), hx, by simp [ha]⟩, heq⟩
    · rintro ⟨⟨⟨a, ha⟩, sa⟩, ⟨⟨b, sb⟩, hx, hsome⟩, heq⟩
      split_ifs at hsome with hb
      · simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at hsome
        rcases hsome with ⟨rfl, rfl⟩
        exact ⟨(b, sb), hx, heq⟩
  rw [hbij]
  unfold clausePoly
  rw [map_prod, Finset.prod_image]
  · refine Finset.prod_congr rfl ?_
    intro ⟨i, s⟩ _
    cases s
    · simp [projK, kVarInv_kVar]
    · simp [projK, kVarInv_kVar]
  · intro ⟨i1, s1⟩ _ ⟨i2, s2⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (Fin.ext (kVar_inj_lt i1.val i2.val i1.isLt i2.isLt heq.1)) heq.2

private def Fk29Set : Set (Clause (Fin 29)) :=
  {C | ∃ c ∈ fkAxList, C = mkClause29 c}

private lemma K4_no_pc3 : ¬ PCRefutable (cnfSystem FkSet) 3 := by
  intro href
  have h29 : ∀ p, PCDerivable (cnfSystem FkSet) 3 p → PCDerivable (cnfSystem Fk29Set) 3 (projK p) := by
    intro p hp
    induction hp with
    | zero => rw [map_zero]; exact PCDerivable.zero
    | add _ _ ih1 ih2 => rw [map_add]; exact PCDerivable.add ih1 ih2
    | @mulX v q _ hdeg ih =>
      rw [map_mul]
      have hdeg' : (projK (X v) * projK q).totalDegree ≤ 3 := by
        rw [← map_mul]; exact (totalDegree_projK_le _).trans hdeg
      have hv : projK (X v) = match kVarInv v with | some i => X i | none => 0 := by
        simp [projK]
      rw [hv] at hdeg' ⊢
      cases hinv : kVarInv v with
      | none => simp; exact PCDerivable.zero
      | some i =>
        rw [hinv] at hdeg'
        exact PCDerivable.mulX i ih hdeg'
    | ax hmem hdeg =>
      rcases hmem with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
      · have hdeg' : (projK (X v * X v + X v)).totalDegree ≤ 3 := (totalDegree_projK_le _).trans hdeg
        simp only [projK, map_add, map_mul, aeval_X] at hdeg' ⊢
        cases hinv : kVarInv v with
        | none => simp; exact PCDerivable.zero
        | some i =>
          rw [hinv] at hdeg'
          exact PCDerivable.ax (Or.inl ⟨i, rfl⟩) hdeg'
      · obtain ⟨c, hc, rfl⟩ := fkAxList_cover hC
        have hdeg' : (projK (clausePoly (mkClause kVar c))).totalDegree ≤ 3 := (totalDegree_projK_le _).trans hdeg
        rw [projK_clause hc] at hdeg' ⊢
        exact PCDerivable.ax (Or.inr ⟨mkClause29 c, ⟨c, hc, rfl⟩, rfl⟩) hdeg'
  have href29 : PCRefutable (cnfSystem Fk29Set) 3 := by
    have h := h29 1 href
    simpa [PCRefutable] using h
  have hphi : ∀ p, PCDerivable (cnfSystem Fk29Set) 3 p → phi29 p = 0 := by
    intro p hp
    induction hp with
    | zero => exact phi29_zero
    | add _ _ ih1 ih2 => rw [phi29_add, ih1, ih2, add_zero]
    | mulX v _ hdeg ih => rw [phi29_mulX hdeg, ih, applyTVec_zero]
    | ax hmem _ =>
      rcases hmem with ⟨v, rfl⟩ | ⟨C, ⟨c, hc, rfl⟩, rfl⟩
      · exact phi29_bool v
      · exact phi29_clause_eq_zero hc
  have h1 : phi29 1 = 0 := hphi 1 href29
  have h1_val : (phi29 1) ⟨0, by omega⟩ = 1 := by
    have hmon : (1 : MvPolynomial (Fin 29) (ZMod 2)) = monomial 0 1 := rfl
    rw [hmon, phi29_monomial, one_smul]
    unfold evalMon29
    have hs : (0 : Fin 29 →₀ ℕ).support = ∅ := Finsupp.support_zero
    rw [hs, idxOfSet_empty]
    simp only [Finset.card_empty, Nat.zero_le, ↓reduceIte, toVec, k4_one]
  rw [h1] at h1_val
  simp at h1_val

private lemma main_result : (∀ Fp : Set (PEqualNP.ProofComplexity.Clause (Fin 10 ⊕ (ℕ × ℕ))), Fp = {Cep | ∃ eep ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)), Cep = {(((Sum.inl eep.1) : Fin 10 ⊕ (ℕ × ℕ)), true), (((Sum.inl eep.2) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cap | ∃ iap : Fin 10, iap.val + 1 < 10 ∧ Cap = {(((Sum.inl iap) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iap.val, 0)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbp | ∃ (ibp : Fin 10) (hbp jbp : ℕ), ibp.val = hbp + 1 ∧ ibp.val + 1 < 10 ∧ jbp < 5 ∧ Cbp = {(((Sum.inr (hbp, jbp)) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibp.val, jbp)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Ccp | ∃ (icp : Fin 10) (hcp gcp : ℕ), icp.val = hcp + 1 ∧ icp.val + 1 < 10 ∧ gcp + 1 < 5 ∧ Ccp = {(((Sum.inl icp) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hcp, gcp)) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (icp.val, gcp + 1)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdp | ∃ (idp : Fin 10) (hdp : ℕ), idp.val = hdp + 1 ∧ Cdp = {(((Sum.inl idp) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdp, 4)) : Fin 10 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfp | ∃ jfp : ℕ, 1 ≤ jfp ∧ jfp < 5 ∧ Cfp = {(((Sum.inr (0, jfp)) : Fin 10 ⊕ (ℕ × ℕ)), false)}} → (∃ πap, PEqualNP.ProofComplexity.IsRefutation Fp πap ∧ ∀ Dap ∈ πap, Dap.card ≤ 3) ∧ (¬ ∃ πbp, PEqualNP.ProofComplexity.IsRefutation Fp πbp ∧ ∀ Dbp ∈ πbp, Dbp.card ≤ 2) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fp) 3 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fp) 2) ∧ (∀ Fk : Set (PEqualNP.ProofComplexity.Clause (Fin 8 ⊕ (ℕ × ℕ))), Fk = {Cek | ∃ eek ∈ ([(0, 4), (0, 5), (0, 6), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7)] : List (Fin 8 × Fin 8)), Cek = {(((Sum.inl eek.1) : Fin 8 ⊕ (ℕ × ℕ)), true), (((Sum.inl eek.2) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cak | ∃ iak : Fin 8, iak.val + 1 < 8 ∧ Cak = {(((Sum.inl iak) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iak.val, 0)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbk | ∃ (ibk : Fin 8) (hbk jbk : ℕ), ibk.val = hbk + 1 ∧ ibk.val + 1 < 8 ∧ jbk < 3 ∧ Cbk = {(((Sum.inr (hbk, jbk)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibk.val, jbk)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cck | ∃ (ick : Fin 8) (hck gck : ℕ), ick.val = hck + 1 ∧ ick.val + 1 < 8 ∧ gck + 1 < 3 ∧ Cck = {(((Sum.inl ick) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hck, gck)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ick.val, gck + 1)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdk | ∃ (idk : Fin 8) (hdk : ℕ), idk.val = hdk + 1 ∧ Cdk = {(((Sum.inl idk) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdk, 2)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfk | ∃ jfk : ℕ, 1 ≤ jfk ∧ jfk < 3 ∧ Cfk = {(((Sum.inr (0, jfk)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} → (∃ πak, PEqualNP.ProofComplexity.IsRefutation Fk πak ∧ ∀ Dak ∈ πak, Dak.card ≤ 3) ∧ (¬ ∃ πbk, PEqualNP.ProofComplexity.IsRefutation Fk πbk ∧ ∀ Dbk ∈ πbk, Dbk.card ≤ 2) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fk) 4 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fk) 3) := by
  refine ⟨?_, ?_⟩
  · intro Fp hFp
    have hEq : Fp = FpSet := hFp
    rw [hEq]
    exact ⟨P1_width3, P2_no_width2, P3_pc3, P4_no_pc2⟩
  · intro Fk hFk
    have hEq : Fk = FkSet := hFk
    rw [hEq]
    exact ⟨K1_width3, K2_no_width2, K3_pc4, K4_no_pc3⟩

end PEqualNP.Outside.L_pcx_103_aux

theorem PEqualNP.Outside.L_pcx_103 : (∀ Fp : Set (PEqualNP.ProofComplexity.Clause (Fin 10 ⊕ (ℕ × ℕ))), Fp = {Cep | ∃ eep ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)), Cep = {(((Sum.inl eep.1) : Fin 10 ⊕ (ℕ × ℕ)), true), (((Sum.inl eep.2) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cap | ∃ iap : Fin 10, iap.val + 1 < 10 ∧ Cap = {(((Sum.inl iap) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iap.val, 0)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbp | ∃ (ibp : Fin 10) (hbp jbp : ℕ), ibp.val = hbp + 1 ∧ ibp.val + 1 < 10 ∧ jbp < 5 ∧ Cbp = {(((Sum.inr (hbp, jbp)) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibp.val, jbp)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Ccp | ∃ (icp : Fin 10) (hcp gcp : ℕ), icp.val = hcp + 1 ∧ icp.val + 1 < 10 ∧ gcp + 1 < 5 ∧ Ccp = {(((Sum.inl icp) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hcp, gcp)) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (icp.val, gcp + 1)) : Fin 10 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdp | ∃ (idp : Fin 10) (hdp : ℕ), idp.val = hdp + 1 ∧ Cdp = {(((Sum.inl idp) : Fin 10 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdp, 4)) : Fin 10 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfp | ∃ jfp : ℕ, 1 ≤ jfp ∧ jfp < 5 ∧ Cfp = {(((Sum.inr (0, jfp)) : Fin 10 ⊕ (ℕ × ℕ)), false)}} → (∃ πap, PEqualNP.ProofComplexity.IsRefutation Fp πap ∧ ∀ Dap ∈ πap, Dap.card ≤ 3) ∧ (¬ ∃ πbp, PEqualNP.ProofComplexity.IsRefutation Fp πbp ∧ ∀ Dbp ∈ πbp, Dbp.card ≤ 2) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fp) 3 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fp) 2) ∧ (∀ Fk : Set (PEqualNP.ProofComplexity.Clause (Fin 8 ⊕ (ℕ × ℕ))), Fk = {Cek | ∃ eek ∈ ([(0, 4), (0, 5), (0, 6), (0, 7), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7)] : List (Fin 8 × Fin 8)), Cek = {(((Sum.inl eek.1) : Fin 8 ⊕ (ℕ × ℕ)), true), (((Sum.inl eek.2) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cak | ∃ iak : Fin 8, iak.val + 1 < 8 ∧ Cak = {(((Sum.inl iak) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (iak.val, 0)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cbk | ∃ (ibk : Fin 8) (hbk jbk : ℕ), ibk.val = hbk + 1 ∧ ibk.val + 1 < 8 ∧ jbk < 3 ∧ Cbk = {(((Sum.inr (hbk, jbk)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ibk.val, jbk)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cck | ∃ (ick : Fin 8) (hck gck : ℕ), ick.val = hck + 1 ∧ ick.val + 1 < 8 ∧ gck + 1 < 3 ∧ Cck = {(((Sum.inl ick) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hck, gck)) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (ick.val, gck + 1)) : Fin 8 ⊕ (ℕ × ℕ)), true)}} ∪ {Cdk | ∃ (idk : Fin 8) (hdk : ℕ), idk.val = hdk + 1 ∧ Cdk = {(((Sum.inl idk) : Fin 8 ⊕ (ℕ × ℕ)), false), (((Sum.inr (hdk, 2)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} ∪ {Cfk | ∃ jfk : ℕ, 1 ≤ jfk ∧ jfk < 3 ∧ Cfk = {(((Sum.inr (0, jfk)) : Fin 8 ⊕ (ℕ × ℕ)), false)}} → (∃ πak, PEqualNP.ProofComplexity.IsRefutation Fk πak ∧ ∀ Dak ∈ πak, Dak.card ≤ 3) ∧ (¬ ∃ πbk, PEqualNP.ProofComplexity.IsRefutation Fk πbk ∧ ∀ Dbk ∈ πbk, Dbk.card ≤ 2) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fk) 4 ∧ ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem Fk) 3) :=
  PEqualNP.Outside.L_pcx_103_aux.main_result
