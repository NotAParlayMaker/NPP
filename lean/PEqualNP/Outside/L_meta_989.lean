import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_989

section UpperBound

private def dot3 {F : Type*} [Field F] (u v : Fin 3 → F) : F :=
  ∑ t : Fin 3, u t * v t

private def cross3 {F : Type*} [Field F] (u v : Fin 3 → F) : Fin 3 → F :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

private lemma dot3_expand {F : Type*} [Field F] (u v : Fin 3 → F) :
    dot3 u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [dot3, Fin.sum_univ_three]

private lemma cross3_zero_iff_prop {F : Type*} [Field F] (u v : Fin 3 → F) (hu : u ≠ 0)
    (hcross : cross3 u v = 0) : ∃ c : F, v = c • u := by
  have h0 : u 1 * v 2 - u 2 * v 1 = 0 := by simpa [cross3] using congrFun hcross 0
  have h1 : u 2 * v 0 - u 0 * v 2 = 0 := by simpa [cross3] using congrFun hcross 1
  have h2 : u 0 * v 1 - u 1 * v 0 = 0 := by simpa [cross3] using congrFun hcross 2
  have hex : ∃ t : Fin 3, u t ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  obtain ⟨t, ht⟩ := hex
  refine ⟨v t / u t, funext fun i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases t <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at ht ⊢
  · field_simp [ht]
  · field_simp [ht]; linear_combination h2
  · field_simp [ht]; linear_combination -h1
  · field_simp [ht]; linear_combination -h2
  · field_simp [ht]
  · field_simp [ht]; linear_combination h0
  · field_simp [ht]; linear_combination h1
  · field_simp [ht]; linear_combination -h0
  · field_simp [ht]

private lemma orth_cross3_prop {F : Type*} [Field F] (p1 p2 l : Fin 3 → F)
    (hp1 : p1 ≠ 0) (hp12 : ∀ c : F, p2 ≠ c • p1)
    (h1 : dot3 p1 l = 0) (h2 : dot3 p2 l = 0) :
    ∃ c : F, l = c • cross3 p1 p2 := by
  have hwne : cross3 p1 p2 ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := cross3_zero_iff_prop p1 p2 hp1 h0
    exact hp12 c hc
  apply cross3_zero_iff_prop (cross3 p1 p2) l hwne
  rw [dot3_expand] at h1 h2
  funext i
  fin_cases i <;> simp only [cross3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply]
  · linear_combination p2 0 * h1 - p1 0 * h2
  · linear_combination p2 1 * h1 - p1 1 * h2
  · linear_combination p2 2 * h1 - p1 2 * h2

private lemma two_orth_prop {F : Type*} [Field F] (p1 p2 l1 l2 : Fin 3 → F)
    (hp1 : p1 ≠ 0) (hp12 : ∀ c : F, p2 ≠ c • p1) (hl1 : l1 ≠ 0)
    (h11 : dot3 p1 l1 = 0) (h21 : dot3 p2 l1 = 0)
    (h12 : dot3 p1 l2 = 0) (h22 : dot3 p2 l2 = 0) :
    ∃ c : F, l2 = c • l1 := by
  obtain ⟨c1, hc1⟩ := orth_cross3_prop p1 p2 l1 hp1 hp12 h11 h21
  obtain ⟨c2, hc2⟩ := orth_cross3_prop p1 p2 l2 hp1 hp12 h12 h22
  have hc1ne : c1 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc1
    exact hl1 hc1
  refine ⟨c2 / c1, ?_⟩
  rw [hc1, hc2, smul_smul, div_mul_cancel₀ c2 hc1ne]

private def monomPairs (b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (b + 1) ×ˢ Finset.range (b + 1)).filter (fun ac => ac.1 + ac.2 ≤ b)

private lemma two_mul_card_monomPairs (b : ℕ) :
    2 * (monomPairs b).card = (b + 1) * (b + 2) := by
  induction b with
  | zero => decide
  | succ b ih =>
    let diag : Finset (ℕ × ℕ) := (Finset.range (b + 2)).image (fun a => (a, b + 1 - a))
    have hsplit : monomPairs (b + 1) = monomPairs b ∪ diag := by
      ext ⟨a, c⟩
      simp only [monomPairs, diag, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, hc⟩, hle⟩
        by_cases heq : a + c = b + 1
        · right; exact ⟨a, by omega, by ext <;> dsimp <;> omega⟩
        · left; exact ⟨⟨by omega, by omega⟩, by omega⟩
      · rintro (⟨⟨ha, hc⟩, hle⟩ | ⟨k, hk, hpair⟩)
        · exact ⟨⟨by omega, by omega⟩, by omega⟩
        · have ha : k = a := congrArg Prod.fst hpair
          have hc : b + 1 - k = c := congrArg Prod.snd hpair
          exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hdisj : Disjoint (monomPairs b) diag := by
      rw [Finset.disjoint_left]
      intro ⟨a, c⟩ h1 h2
      simp only [monomPairs, Finset.mem_filter] at h1
      simp only [diag, Finset.mem_image, Finset.mem_range] at h2
      obtain ⟨k, hk, hpair⟩ := h2
      have ha : k = a := congrArg Prod.fst hpair
      have hc : b + 1 - k = c := congrArg Prod.snd hpair
      omega
    have hdiag : diag.card = b + 2 := by
      rw [Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h), Finset.card_range]
    rw [hsplit, Finset.card_union_of_disjoint hdisj, hdiag]
    nlinarith

private noncomputable def expOfPair (b : ℕ) (ac : ℕ × ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 ac.1 + Finsupp.single 1 ac.2 + Finsupp.single 2 (b - ac.1 - ac.2)

private noncomputable def monomSet (b : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  (monomPairs b).image (expOfPair b)

private lemma mem_monomSet_of_sum_eq (b : ℕ) (d : Fin 3 →₀ ℕ)
    (hd : d 0 + d 1 + d 2 = b) : d ∈ monomSet b := by
  rw [monomSet, Finset.mem_image]
  refine ⟨(d 0, d 1), ?_, ?_⟩
  · simp only [monomPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · ext i
    fin_cases i <;> simp [expOfPair, Finsupp.single_apply]
    omega

private lemma card_monomSet_le (b : ℕ) : 2 * (monomSet b).card ≤ (b + 1) * (b + 2) := by
  have h1 : (monomSet b).card ≤ (monomPairs b).card := Finset.card_image_le
  have h2 := two_mul_card_monomPairs b
  omega

private noncomputable def linForm {F : Type*} [Field F] (v : Fin 3 → F) : MvPolynomial (Fin 3) F :=
  ∑ t : Fin 3, MvPolynomial.C (v t) * MvPolynomial.X t

private lemma eval_linForm {F : Type*} [Field F] (v l : Fin 3 → F) :
    MvPolynomial.eval l (linForm v) = dot3 v l := by
  simp [linForm, dot3, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X]

private lemma single_deg_one (t : Fin 3) :
    (Finsupp.single t 1 : Fin 3 →₀ ℕ) 0 + (Finsupp.single t 1 : Fin 3 →₀ ℕ) 1 +
    (Finsupp.single t 1 : Fin 3 →₀ ℕ) 2 = 1 := by
  fin_cases t <;> simp [Finsupp.single_apply]

private lemma deg_support_linForm {F : Type*} [Field F] (v : Fin 3 → F)
    (d : Fin 3 →₀ ℕ) (hd : d ∈ (linForm v).support) :
    d 0 + d 1 + d 2 = 1 := by
  have hmem := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  obtain ⟨t, _, hdt⟩ := hmem
  have hne : (MvPolynomial.C (v t) * MvPolynomial.X t : MvPolynomial (Fin 3) F).coeff d ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hdt
  rw [MvPolynomial.coeff_C_mul] at hne
  have hxne : (MvPolynomial.X t : MvPolynomial (Fin 3) F).coeff d ≠ 0 := right_ne_zero_of_mul hne
  have hxmem : d ∈ (MvPolynomial.X t : MvPolynomial (Fin 3) F).support :=
    MvPolynomial.mem_support_iff.mpr hxne
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hxmem
  subst hxmem
  exact single_deg_one t

private lemma deg_support_mul {F : Type*} [Field F] (p q : MvPolynomial (Fin 3) F) (a b : ℕ)
    (hp : ∀ d ∈ p.support, d 0 + d 1 + d 2 = a)
    (hq : ∀ d ∈ q.support, d 0 + d 1 + d 2 = b)
    (d : Fin 3 →₀ ℕ) (hd : d ∈ (p * q).support) :
    d 0 + d 1 + d 2 = a + b := by
  have hmem := MvPolynomial.support_mul p q hd
  rw [Finset.mem_add] at hmem
  obtain ⟨d1, hd1, d2, hd2, rfl⟩ := hmem
  have h1 := hp d1 hd1
  have h2 := hq d2 hd2
  simp only [Finsupp.coe_add, Pi.add_apply]
  omega

private lemma deg_support_X_pow {F : Type*} [Field F] (t : Fin 3) (m : ℕ)
    (d : Fin 3 →₀ ℕ) (hd : d ∈ ((MvPolynomial.X t : MvPolynomial (Fin 3) F) ^ m).support) :
    d 0 + d 1 + d 2 = m := by
  induction m generalizing d with
  | zero =>
    simp only [pow_zero, MvPolynomial.support_one, Finset.mem_singleton] at hd
    subst hd; simp
  | succ m ih =>
    rw [pow_succ] at hd
    refine deg_support_mul _ _ m 1 ih ?_ d hd
    intro e he
    rw [MvPolynomial.support_X, Finset.mem_singleton] at he
    subst he
    exact single_deg_one t

private lemma deg_support_prod_linForm {F : Type*} [Field F] {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Fin 3 → F)
    (d : Fin 3 →₀ ℕ) (hd : d ∈ (∏ p ∈ s, linForm (f p)).support) :
    d 0 + d 1 + d 2 = s.card := by
  induction s using Finset.induction generalizing d with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, MvPolynomial.support_one, Finset.mem_singleton] at hd ⊢
    subst hd; simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha] at hd
    rw [Finset.card_insert_of_notMem ha]
    have h := deg_support_mul _ _ 1 s.card (deg_support_linForm (f a)) ih d hd
    omega

private lemma upper_bound (F : Type) [Field F] (n k b : ℕ)
    (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F)
    (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool)
    (hpt0 : ∀ p : Fin n, pt p ≠ 0)
    (hpt_ind : ∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p)
    (hl0 : ∀ i : Fin k, l i ≠ 0)
    (hl_ind : ∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i)
    (hy_card : ∀ i : Fin k, (y i).card ≤ b)
    (hy_off : ∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0)
    (hg_safe : ∀ (i : Fin k) (x : Fin n → Bool), g x = true →
      ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0)
    (hg_two : ∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧
      ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧
      g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧
      g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) :
    2 * k ≤ (b + 1) * (b + 2) := by
  classical
  have hhit : ∀ i j : Fin k, i ≠ j → ∃ p ∈ y i, dot3 (pt p) (l j) = 0 := by
    intro i j hij
    obtain ⟨p1, p2, hp12, hp1i, hp2i, hg1, hg2⟩ := hg_two i
    have hnotboth : ¬ (dot3 (pt p1) (l j) = 0 ∧ dot3 (pt p2) (l j) = 0) := by
      rintro ⟨hp1j, hp2j⟩
      obtain ⟨c, hc⟩ := two_orth_prop (pt p1) (pt p2) (l i) (l j) (hpt0 p1)
        (hpt_ind p1 p2 hp12) (hl0 i) hp1i hp2i hp1j hp2j
      exact hl_ind i j hij c hc
    by_cases hp1j : dot3 (pt p1) (l j) = 0
    · have hp2j : dot3 (pt p2) (l j) ≠ 0 := fun h => hnotboth ⟨hp1j, h⟩
      obtain ⟨q, hqmem, hqj⟩ := hg_safe j _ hg2
      simp only [decide_eq_true_eq] at hqmem
      rcases hqmem with hqy | rfl
      · exact ⟨q, hqy, hqj⟩
      · exact absurd hqj hp2j
    · obtain ⟨q, hqmem, hqj⟩ := hg_safe j _ hg1
      simp only [decide_eq_true_eq] at hqmem
      rcases hqmem with hqy | rfl
      · exact ⟨q, hqy, hqj⟩
      · exact absurd hqj hp1j
  have hcoord : ∀ i : Fin k, ∃ t : Fin 3, l i t ≠ 0 := fun i => by
    by_contra h
    push Not at h
    exact hl0 i (funext h)
  choose t0 ht0 using hcoord
  let P : Fin k → MvPolynomial (Fin 3) F := fun i =>
    (∏ p ∈ y i, linForm (pt p)) * (MvPolynomial.X (t0 i)) ^ (b - (y i).card)
  have hP_supp : ∀ i : Fin k, (P i).support ⊆ monomSet b := by
    intro i d hd
    apply mem_monomSet_of_sum_eq
    have hdeg := deg_support_mul _ _ (y i).card (b - (y i).card)
      (deg_support_prod_linForm (y i) pt) (deg_support_X_pow (t0 i) (b - (y i).card)) d hd
    have hle := hy_card i
    omega
  have hP_diag : ∀ i : Fin k, MvPolynomial.eval (l i) (P i) ≠ 0 := by
    intro i
    simp only [P, map_mul, map_prod, map_pow, eval_linForm, MvPolynomial.eval_X]
    refine mul_ne_zero ?_ (pow_ne_zero _ (ht0 i))
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact hy_off i p hp
  have hP_off : ∀ i j : Fin k, i ≠ j → MvPolynomial.eval (l j) (P i) = 0 := by
    intro i j hij
    obtain ⟨p, hp, hpj⟩ := hhit i j hij
    simp only [P, map_mul, map_prod, eval_linForm]
    rw [Finset.prod_eq_zero hp hpj, zero_mul]
  let vec : Fin k → (monomSet b → F) := fun i m => (P i).coeff m.val
  have hli : LinearIndependent F vec := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let Q : MvPolynomial (Fin 3) F := ∑ i : Fin k, MvPolynomial.C (c i) * P i
    have hQ_zero : Q = 0 := by
      ext d
      rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      by_cases hd : d ∈ monomSet b
      · have hcd := congrFun hc ⟨d, hd⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, vec] at hcd
        simpa [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul] using hcd
      · rw [MvPolynomial.coeff_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [MvPolynomial.coeff_C_mul]
        have hnot : d ∉ (P i).support := fun h => hd (hP_supp i h)
        rw [MvPolynomial.notMem_support_iff.mp hnot, mul_zero]
    intro j
    have hev : MvPolynomial.eval (l j) Q = 0 := by rw [hQ_zero, map_zero]
    simp only [Q, map_sum, map_mul, MvPolynomial.eval_C] at hev
    rw [Finset.sum_eq_single j] at hev
    · exact (mul_eq_zero.mp hev).resolve_right (hP_diag j)
    · intro i _ hij
      rw [hP_off i j hij, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hrank := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_pi, Fintype.card_coe] at hrank
  have hbound := card_monomSet_le b
  omega

end UpperBound

section LowerBound

private def mkPt {F : Type} [Field F] [Fintype F] (eF : Fin (Fintype.card F) ≃ F)
    (p : Fin (Fintype.card F * Fintype.card F + Fintype.card F + 1)) : Fin 3 → F :=
  if h1 : p.val < Fintype.card F * Fintype.card F then
    ![1, eF ⟨p.val / Fintype.card F, Nat.div_lt_of_lt_mul h1⟩,
         eF ⟨p.val % Fintype.card F, Nat.mod_lt p.val (Fintype.card_pos_iff.mpr ⟨0⟩)⟩]
  else if h2 : p.val < Fintype.card F * Fintype.card F + Fintype.card F then
    ![0, 1, eF ⟨p.val - Fintype.card F * Fintype.card F, by omega⟩]
  else
    ![0, 0, 1]

private lemma mkPt_ne_zero {F : Type} [Field F] [Fintype F] (eF : Fin (Fintype.card F) ≃ F)
    (p : Fin (Fintype.card F * Fintype.card F + Fintype.card F + 1)) :
    mkPt eF p ≠ 0 := by
  unfold mkPt
  split_ifs with h1 h2
  · intro h; have := congrFun h 0; simp at this
  · intro h; have := congrFun h 1; simp at this
  · intro h; have := congrFun h 2; simp at this

private lemma mkPt_indep {F : Type} [Field F] [Fintype F] (eF : Fin (Fintype.card F) ≃ F)
    (p p' : Fin (Fintype.card F * Fintype.card F + Fintype.card F + 1))
    (hne : p ≠ p') (c : F) :
    mkPt eF p' ≠ c • mkPt eF p := by
  intro heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  simp only [Pi.smul_apply, smul_eq_mul, mkPt] at h0 h1 h2
  split_ifs at h0 h1 h2 with hp'1 hp1 hp1' hp'2 hp1'' hp1''' hp2 hp2'
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_one] at h0 h1 h2
    subst h0
    simp only [one_mul] at h1 h2
    have hdiv : p'.val / Fintype.card F = p.val / Fintype.card F := by
      simpa using congrArg Fin.val (eF.injective h1)
    have hmod : p'.val % Fintype.card F = p.val % Fintype.card F := by
      simpa using congrArg Fin.val (eF.injective h2)
    apply hne
    apply Fin.ext
    rw [← Nat.div_add_mod p.val (Fintype.card F), ← Nat.div_add_mod p'.val (Fintype.card F), hdiv, hmod]
  · simp at h0
  · simp at h0
  · simp at h0
    have hc : c = 0 := h0.symm
    subst hc; simp at h1
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_one] at h1 h2
    subst h1
    simp only [one_mul] at h2
    have hsub : p'.val - Fintype.card F * Fintype.card F = p.val - Fintype.card F * Fintype.card F := by
      simpa using congrArg Fin.val (eF.injective h2)
    apply hne; apply Fin.ext; omega
  · simp at h1
  · simp at h0
    have hc : c = 0 := h0.symm
    subst hc; simp at h2
  · simp at h1
    have hc : c = 0 := h1.symm
    subst hc; simp at h2
  · apply hne; apply Fin.ext; omega

private lemma mkPt_surj {F : Type} [Field F] [Fintype F] (eF : Fin (Fintype.card F) ≃ F)
    (v : Fin 3 → F) (hv : v ≠ 0) :
    ∃ (p : Fin (Fintype.card F * Fintype.card F + Fintype.card F + 1)) (c : F),
      v = c • mkPt eF p := by
  have hqpos : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  by_cases h0 : v 0 ≠ 0
  · let a := eF.symm (v 1 / v 0)
    let d := eF.symm (v 2 / v 0)
    have hlt : a.val * Fintype.card F + d.val < Fintype.card F * Fintype.card F := by
      have ha : a.val + 1 ≤ Fintype.card F := a.isLt
      have hd : d.val < Fintype.card F := d.isLt
      nlinarith
    let p : Fin (Fintype.card F * Fintype.card F + Fintype.card F + 1) :=
      ⟨a.val * Fintype.card F + d.val, by omega⟩
    have hpval : p.val < Fintype.card F * Fintype.card F := hlt
    have hdiv : (⟨p.val / Fintype.card F, Nat.div_lt_of_lt_mul hpval⟩ : Fin (Fintype.card F)) = a := by
      apply Fin.ext
      show (a.val * Fintype.card F + d.val) / Fintype.card F = a.val
      rw [Nat.mul_comm, Nat.mul_add_div hqpos, Nat.div_eq_of_lt d.isLt, add_zero]
    have hmod : (⟨p.val % Fintype.card F, Nat.mod_lt p.val hqpos⟩ : Fin (Fintype.card F)) = d := by
      apply Fin.ext
      show (a.val * Fintype.card F + d.val) % Fintype.card F = d.val
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt d.isLt]
    have hptp : mkPt eF p = ![1, v 1 / v 0, v 2 / v 0] := by
      unfold mkPt
      rw [dite_eq_left hpval, hdiv, hmod]
      simp [a, d]
    refine ⟨p, v 0, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, hptp]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    · ring
    · field_simp [h0]
    · field_simp [h0]
  · push Not at h0
    by_cases h1 : v 1 ≠ 0
    · let d := eF.symm (v 2 / v 1)
      let p : Fin (Fintype.card F * Fintype.card F + Fintype.card F + 1) :=
        ⟨Fintype.card F * Fintype.card F + d.val, by have := d.isLt; omega⟩
      have hge : ¬ (p.val < Fintype.card F * Fintype.card F) := by
        show ¬ (Fintype.card F * Fintype.card F + d.val < Fintype.card F * Fintype.card F); omega
      have hlt : p.val < Fintype.card F * Fintype.card F + Fintype.card F := by
        show Fintype.card F * Fintype.card F + d.val < Fintype.card F * Fintype.card F + Fintype.card F
        exact Nat.add_lt_add_left d.isLt _
      have hsub : (⟨p.val - Fintype.card F * Fintype.card F, by omega⟩ : Fin (Fintype.card F)) = d := by
        apply Fin.ext
        show Fintype.card F * Fintype.card F + d.val - Fintype.card F * Fintype.card F = d.val
        omega
      have hptp : mkPt eF p = ![0, 1, v 2 / v 1] := by
        unfold mkPt
        rw [dite_eq_right hge, dite_eq_left hlt, hsub]
        simp [d]
      refine ⟨p, v 1, funext fun i => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, hptp]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      · simp [h0]
      · ring
      · field_simp [h1]
    · push Not at h1
      have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv; funext i; fin_cases i <;> assumption
      let p : Fin (Fintype.card F * Fintype.card F + Fintype.card F + 1) :=
        ⟨Fintype.card F * Fintype.card F + Fintype.card F, by omega⟩
      have hge1 : ¬ (p.val < Fintype.card F * Fintype.card F) := by
        show ¬ (Fintype.card F * Fintype.card F + Fintype.card F < Fintype.card F * Fintype.card F); omega
      have hge2 : ¬ (p.val < Fintype.card F * Fintype.card F + Fintype.card F) := by
        show ¬ (Fintype.card F * Fintype.card F + Fintype.card F < Fintype.card F * Fintype.card F + Fintype.card F); omega
      have hptp : mkPt eF p = ![0, 0, 1] := by
        unfold mkPt
        rw [dite_eq_right hge1, dite_eq_right hge2]
      refine ⟨p, v 2, funext fun i => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, hptp]
      fin_cases i <;> simp [h0, h1]

private lemma two_mul_card_pairs (m : ℕ) :
    2 * (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card + m = m * m := by
  let L := Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)
  let R := Finset.univ.filter (fun p : Fin m × Fin m => p.2 < p.1)
  let D := Finset.univ.filter (fun p : Fin m × Fin m => p.1 = p.2)
  have hLR : L.card = R.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp; simp only [L, R, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
    · intro p1 _ p2 _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro p hp; refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [L, R, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
  have hD : D.card = m := by
    have : D = Finset.univ.image (fun i : Fin m => (i, i)) := by
      ext ⟨a, c⟩
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨a, Prod.ext rfl h⟩
      · rintro ⟨i, hi⟩; exact (congrArg Prod.fst hi).symm.trans (congrArg Prod.snd hi)
    rw [this, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h), Finset.card_univ, Fintype.card_fin]
  have hunion : L ∪ R ∪ D = Finset.univ := by
    ext ⟨a, c⟩
    simp only [L, R, D, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases lt_trichotomy a c with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hd1 : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [L, R, Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hd2 : Disjoint (L ∪ R) D := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [L, R, D, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1
    · exact ne_of_lt h1.2 h2.2
    · exact ne_of_gt h1.2 h2.2
  have htot := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← hLR, hD] at htot
  linarith

private lemma lower_bound (F : Type) [Field F] [Fintype F] (b : ℕ)
    (hb : b + 1 ≤ Fintype.card F) :
    ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F)
      (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool),
      (∀ p : Fin n, pt p ≠ 0) ∧
      (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧
      (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧
      (∀ i : Fin k, l i ≠ 0) ∧
      (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧
      (∀ i : Fin k, (y i).card ≤ b) ∧
      (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧
      (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧
      (∀ (i : Fin k) (x : Fin n → Bool), g x = true →
        ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧
      (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧
        ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧
        g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧
        g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧
      2 * k = (b + 1) * (b + 2) := by
  classical
  have hqpos : 0 < Fintype.card F := by omega
  let eF : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let n : ℕ := Fintype.card F * Fintype.card F + Fintype.card F + 1
  let pt : Fin n → Fin 3 → F := mkPt eF
  let arc : Fin (b + 2) → Fin n := fun r =>
    if hr : r.val < b + 1 then
      let a : Fin (Fintype.card F) := ⟨r.val, by omega⟩
      let c : Fin (Fintype.card F) := eF.symm (eF a * eF a)
      ⟨a.val * Fintype.card F + c.val, by
        have ha : a.val + 1 ≤ Fintype.card F := a.isLt
        have hc : c.val < Fintype.card F := c.isLt
        have hlt : a.val * Fintype.card F + c.val < Fintype.card F * Fintype.card F := by nlinarith
        omega⟩
    else
      ⟨Fintype.card F * Fintype.card F + Fintype.card F, by omega⟩
  have harc_val : ∀ r : Fin (b + 2),
      (∀ hr : r.val < b + 1, pt (arc r) = ![1, eF ⟨r.val, by omega⟩, eF ⟨r.val, by omega⟩ * eF ⟨r.val, by omega⟩]) ∧
      (r.val = b + 1 → pt (arc r) = ![0, 0, 1]) := by
    intro r
    constructor
    · intro hr
      let a : Fin (Fintype.card F) := ⟨r.val, by omega⟩
      let c : Fin (Fintype.card F) := eF.symm (eF a * eF a)
      have hlt : a.val * Fintype.card F + c.val < Fintype.card F * Fintype.card F := by
        have ha : a.val + 1 ≤ Fintype.card F := a.isLt
        have hc : c.val < Fintype.card F := c.isLt
        nlinarith
      have hdiv : (⟨(a.val * Fintype.card F + c.val) / Fintype.card F, Nat.div_lt_of_lt_mul hlt⟩ : Fin (Fintype.card F)) = a := by
        apply Fin.ext
        dsimp only
        rw [Nat.mul_comm, Nat.mul_add_div hqpos, Nat.div_eq_of_lt c.isLt, add_zero]
      have hmod : (⟨(a.val * Fintype.card F + c.val) % Fintype.card F, Nat.mod_lt _ hqpos⟩ : Fin (Fintype.card F)) = c := by
        apply Fin.ext
        dsimp only
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt c.isLt]
      have harc_eq : arc r = ⟨a.val * Fintype.card F + c.val, by omega⟩ := by
        dsimp only [arc]
        rw [dite_eq_left hr]
      change mkPt eF (arc r) = _
      rw [harc_eq]
      unfold mkPt
      rw [dite_eq_left hlt, hdiv, hmod]
      simp [a, c]
    · intro hr
      have hnot : ¬ (r.val < b + 1) := by omega
      have harc_eq : arc r = ⟨Fintype.card F * Fintype.card F + Fintype.card F, by omega⟩ := by
        dsimp only [arc]
        rw [dite_eq_right hnot]
      have hge1 : ¬ (Fintype.card F * Fintype.card F + Fintype.card F < Fintype.card F * Fintype.card F) := by omega
      have hge2 : ¬ (Fintype.card F * Fintype.card F + Fintype.card F < Fintype.card F * Fintype.card F + Fintype.card F) := by omega
      change mkPt eF (arc r) = _
      rw [harc_eq]
      unfold mkPt
      rw [dite_eq_right hge1, dite_eq_right hge2]
  have heq_of_eF : ∀ {r1 r2 : Fin (b + 2)} (h1 : r1.val < b + 1) (h2 : r2.val < b + 1),
      eF ⟨r1.val, by omega⟩ = eF ⟨r2.val, by omega⟩ → r1 = r2 := by
    intro r1 r2 h1 h2 heq
    have hfin := eF.injective heq
    exact Fin.ext (by simpa using congrArg Fin.val hfin)
  have harc_inj : Function.Injective arc := by
    intro r1 r2 h
    have hpt := congrArg pt h
    by_cases h1 : r1.val < b + 1 <;> by_cases h2 : r2.val < b + 1
    · rw [(harc_val r1).1 h1, (harc_val r2).1 h2] at hpt
      have heq := congrFun hpt 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at heq
      exact heq_of_eF h1 h2 heq
    · have hr2 : r2.val = b + 1 := by omega
      rw [(harc_val r1).1 h1, (harc_val r2).2 hr2] at hpt
      have := congrFun hpt 0; simp at this
    · have hr1 : r1.val = b + 1 := by omega
      rw [(harc_val r1).2 hr1, (harc_val r2).1 h2] at hpt
      have := congrFun hpt 0; simp at this
    · exact Fin.ext (by omega)
  have harc_det : ∀ r1 r2 r3 : Fin (b + 2), r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
      dot3 (pt (arc r3)) (cross3 (pt (arc r1)) (pt (arc r2))) ≠ 0 := by
    intro r1 r2 r3 h12 h13 h23
    rw [dot3_expand]
    by_cases hr1 : r1.val < b + 1 <;> by_cases hr2 : r2.val < b + 1 <;> by_cases hr3 : r3.val < b + 1
    · rw [(harc_val r1).1 hr1, (harc_val r2).1 hr2, (harc_val r3).1 hr3]
      set t1 := eF ⟨r1.val, by omega⟩
      set t2 := eF ⟨r2.val, by omega⟩
      set t3 := eF ⟨r3.val, by omega⟩
      have ht12 : t2 - t1 ≠ 0 := sub_ne_zero.mpr fun h => h12 (heq_of_eF hr1 hr2 h.symm)
      have ht13 : t3 - t1 ≠ 0 := sub_ne_zero.mpr fun h => h13 (heq_of_eF hr1 hr3 h.symm)
      have ht23 : t3 - t2 ≠ 0 := sub_ne_zero.mpr fun h => h23 (heq_of_eF hr2 hr3 h.symm)
      have hid : (1 : F) * (cross3 ![1, t1, t1 * t1] ![1, t2, t2 * t2] 0) +
          t3 * (cross3 ![1, t1, t1 * t1] ![1, t2, t2 * t2] 1) +
          (t3 * t3) * (cross3 ![1, t1, t1 * t1] ![1, t2, t2 * t2] 2) =
          (t2 - t1) * (t3 - t1) * (t3 - t2) := by
        simp only [cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hid] using
        mul_ne_zero (mul_ne_zero ht12 ht13) ht23
    · have h3eq : r3.val = b + 1 := by omega
      rw [(harc_val r1).1 hr1, (harc_val r2).1 hr2, (harc_val r3).2 h3eq]
      set t1 := eF ⟨r1.val, by omega⟩
      set t2 := eF ⟨r2.val, by omega⟩
      have ht12 : t2 - t1 ≠ 0 := sub_ne_zero.mpr fun h => h12 (heq_of_eF hr1 hr2 h.symm)
      have hid : (0 : F) * (cross3 ![1, t1, t1 * t1] ![1, t2, t2 * t2] 0) +
          0 * (cross3 ![1, t1, t1 * t1] ![1, t2, t2 * t2] 1) +
          1 * (cross3 ![1, t1, t1 * t1] ![1, t2, t2 * t2] 2) = t2 - t1 := by
        simp only [cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hid] using ht12
    · have h2eq : r2.val = b + 1 := by omega
      rw [(harc_val r1).1 hr1, (harc_val r2).2 h2eq, (harc_val r3).1 hr3]
      set t1 := eF ⟨r1.val, by omega⟩
      set t3 := eF ⟨r3.val, by omega⟩
      have ht13 : t1 - t3 ≠ 0 := sub_ne_zero.mpr fun h => h13 (heq_of_eF hr1 hr3 h)
      have hid : (1 : F) * (cross3 ![1, t1, t1 * t1] ![0, 0, 1] 0) +
          t3 * (cross3 ![1, t1, t1 * t1] ![0, 0, 1] 1) +
          (t3 * t3) * (cross3 ![1, t1, t1 * t1] ![0, 0, 1] 2) = t1 - t3 := by
        simp only [cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hid] using ht13
    · exact absurd (Fin.ext (by omega : r2.val = r3.val)) h23
    · have h1eq : r1.val = b + 1 := by omega
      rw [(harc_val r1).2 h1eq, (harc_val r2).1 hr2, (harc_val r3).1 hr3]
      set t2 := eF ⟨r2.val, by omega⟩
      set t3 := eF ⟨r3.val, by omega⟩
      have ht23 : t3 - t2 ≠ 0 := sub_ne_zero.mpr fun h => h23 (heq_of_eF hr2 hr3 h.symm)
      have hid : (1 : F) * (cross3 ![0, 0, 1] ![1, t2, t2 * t2] 0) +
          t3 * (cross3 ![0, 0, 1] ![1, t2, t2 * t2] 1) +
          (t3 * t3) * (cross3 ![0, 0, 1] ![1, t2, t2 * t2] 2) = t3 - t2 := by
        simp only [cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hid] using ht23
    · exact absurd (Fin.ext (by omega : r1.val = r3.val)) h13
    · exact absurd (Fin.ext (by omega : r1.val = r2.val)) h12
    · exact absurd (Fin.ext (by omega : r1.val = r2.val)) h12
  let Pairs := Finset.univ.filter (fun p : Fin (b + 2) × Fin (b + 2) => p.1 < p.2)
  let k := Fintype.card Pairs
  let eP : Fin k ≃ Pairs := (Fintype.equivFin Pairs).symm
  let A : Finset (Fin n) := Finset.univ.image arc
  have hA_card : A.card = b + 2 := by
    rw [Finset.card_image_of_injective _ harc_inj, Finset.card_univ, Fintype.card_fin]
  let l : Fin k → Fin 3 → F := fun i => cross3 (pt (arc (eP i).val.1)) (pt (arc (eP i).val.2))
  let y : Fin k → Finset (Fin n) := fun i => (A.erase (arc (eP i).val.1)).erase (arc (eP i).val.2)
  let g : (Fin n → Bool) → Bool := fun x => decide (b + 1 ≤ (A.filter (fun p => x p = true)).card)
  have hdot_u : ∀ i : Fin k, dot3 (pt (arc (eP i).val.1)) (l i) = 0 := by
    intro i; simp only [l, dot3_expand, cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
  have hdot_v : ∀ i : Fin k, dot3 (pt (arc (eP i).val.2)) (l i) = 0 := by
    intro i; simp only [l, dot3_expand, cross3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
  have hpair_lt : ∀ i : Fin k, (eP i).val.1 < (eP i).val.2 := fun i =>
    (Finset.mem_filter.mp (eP i).property).2
  have hpair_ne : ∀ i : Fin k, (eP i).val.1 ≠ (eP i).val.2 := fun i => ne_of_lt (hpair_lt i)
  refine ⟨n, k, pt, l, y, g, mkPt_ne_zero eF, mkPt_indep eF, mkPt_surj eF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h0
    obtain ⟨c, hc⟩ := cross3_zero_iff_prop _ _ (mkPt_ne_zero eF _) h0
    exact mkPt_indep eF _ _ (fun h => hpair_ne i (harc_inj h)) c hc
  · intro i j hij c hc
    have hne : (eP i).val ≠ (eP j).val := fun h => hij (eP.injective (Subtype.ext h))
    have hnot_both : ¬ (((eP j).val.1 = (eP i).val.1 ∨ (eP j).val.1 = (eP i).val.2) ∧
                        ((eP j).val.2 = (eP i).val.1 ∨ (eP j).val.2 = (eP i).val.2)) := by
      rintro ⟨h1 | h1, h2 | h2⟩
      · exact hpair_ne j (h1.trans h2.symm)
      · exact hne (Prod.ext h1.symm h2.symm)
      · have hlt1 := hpair_lt i; have hlt2 := hpair_lt j; rw [h1, h2] at hlt2; exact lt_asymm hlt1 hlt2
      · exact hpair_ne j (h1.trans h2.symm)
    have horth : ∀ r : Fin (b + 2), dot3 (pt (arc r)) (l j) = 0 → dot3 (pt (arc r)) (l i) = 0 := by
      intro r hr
      have hmul : c * dot3 (pt (arc r)) (l i) = 0 := by
        have : dot3 (pt (arc r)) (c • l i) = c * dot3 (pt (arc r)) (l i) := by
          simp only [dot3_expand, Pi.smul_apply, smul_eq_mul]; ring
        rw [← this, ← hc]; exact hr
      have hcne : c ≠ 0 := by
        intro hc0; rw [hc0, zero_smul] at hc
        obtain ⟨c', hc'⟩ := cross3_zero_iff_prop _ _ (mkPt_ne_zero eF _) hc
        exact mkPt_indep eF _ _ (fun h => hpair_ne j (harc_inj h)) c' hc'
      exact (mul_eq_zero.mp hmul).resolve_left hcne
    have h1 := horth (eP j).val.1 (hdot_u j)
    have h2 := horth (eP j).val.2 (hdot_v j)
    apply hnot_both
    constructor
    · by_contra hno; push Not at hno
      exact harc_det _ _ _ (hpair_ne i) hno.1.symm hno.2.symm h1
    · by_contra hno; push Not at hno
      exact harc_det _ _ _ (hpair_ne i) hno.1.symm hno.2.symm h2
  · intro i
    have hm1 : arc (eP i).val.1 ∈ A := Finset.mem_image_of_mem arc (Finset.mem_univ _)
    have hm2 : arc (eP i).val.2 ∈ A.erase (arc (eP i).val.1) :=
      Finset.mem_erase.mpr ⟨fun h => (hpair_ne i).symm (harc_inj h),
        Finset.mem_image_of_mem arc (Finset.mem_univ _)⟩
    rw [show (y i).card = ((A.erase (arc (eP i).val.1)).erase (arc (eP i).val.2)).card from rfl,
        Finset.card_erase_of_mem hm2, Finset.card_erase_of_mem hm1, hA_card]
    omega
  · intro i p hp
    have h2 := (Finset.mem_erase.mp hp).1
    have hp' := (Finset.mem_erase.mp hp).2
    have h1 := (Finset.mem_erase.mp hp').1
    have hpA := (Finset.mem_erase.mp hp').2
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hpA
    exact harc_det _ _ _ (hpair_ne i) (fun h => h1 (congrArg arc h.symm))
      (fun h => h2 (congrArg arc h.symm))
  · intro x x' hxx' hgx
    simp only [g, decide_eq_true_eq] at hgx ⊢
    exact hgx.trans (Finset.card_le_card fun p hp =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, hxx' p (Finset.mem_filter.mp hp).2⟩)
  · intro i x hgx
    simp only [g, decide_eq_true_eq] at hgx
    by_contra hno
    push Not at hno
    have hsub : A.filter (fun p => x p = true) ⊆ y i := by
      intro p hp
      have hpA := (Finset.mem_filter.mp hp).1
      have hxp := (Finset.mem_filter.mp hp).2
      refine Finset.mem_erase.mpr ⟨fun h2 => hno p hxp (h2 ▸ hdot_v i),
        Finset.mem_erase.mpr ⟨fun h1 => hno p hxp (h1 ▸ hdot_u i), hpA⟩⟩
    have hcard := Finset.card_le_card hsub
    have hm1 : arc (eP i).val.1 ∈ A := Finset.mem_image_of_mem arc (Finset.mem_univ _)
    have hm2 : arc (eP i).val.2 ∈ A.erase (arc (eP i).val.1) :=
      Finset.mem_erase.mpr ⟨fun h => (hpair_ne i).symm (harc_inj h),
        Finset.mem_image_of_mem arc (Finset.mem_univ _)⟩
    have hyc : (y i).card = b := by
      rw [show (y i).card = ((A.erase (arc (eP i).val.1)).erase (arc (eP i).val.2)).card from rfl,
          Finset.card_erase_of_mem hm2, Finset.card_erase_of_mem hm1, hA_card]
      omega
    omega
  · intro i
    let p1 := arc (eP i).val.1
    let p2 := arc (eP i).val.2
    have hp12 : p1 ≠ p2 := fun h => hpair_ne i (harc_inj h)
    have hm1 : p1 ∈ A := Finset.mem_image_of_mem arc (Finset.mem_univ _)
    have hm2 : p2 ∈ A := Finset.mem_image_of_mem arc (Finset.mem_univ _)
    refine ⟨p1, p2, hp12, hdot_u i, hdot_v i, ?_, ?_⟩
    · simp only [g, decide_eq_true_eq]
      have hfilt : A.filter (fun v => v ∈ y i ∨ v = p1) = A.erase p2 := by
        ext v
        simp only [Finset.mem_filter, y, Finset.mem_erase]
        constructor
        · rintro ⟨hvA, ⟨hv2, _, _⟩ | rfl⟩
          · exact ⟨hv2, hvA⟩
          · exact ⟨hp12, hvA⟩
        · rintro ⟨hv2, hvA⟩
          by_cases hv1 : v = p1
          · exact ⟨hvA, Or.inr hv1⟩
          · exact ⟨hvA, Or.inl ⟨hv2, hv1, hvA⟩⟩
      rw [hfilt, Finset.card_erase_of_mem hm2, hA_card]
      omega
    · simp only [g, decide_eq_true_eq]
      have hfilt : A.filter (fun v => v ∈ y i ∨ v = p2) = A.erase p1 := by
        ext v
        simp only [Finset.mem_filter, y, Finset.mem_erase]
        constructor
        · rintro ⟨hvA, ⟨_, hv1, _⟩ | rfl⟩
          · exact ⟨hv1, hvA⟩
          · exact ⟨hp12.symm, hvA⟩
        · rintro ⟨hv1, hvA⟩
          by_cases hv2 : v = p2
          · exact ⟨hvA, Or.inr hv2⟩
          · exact ⟨hvA, Or.inl ⟨hv2, hv1, hvA⟩⟩
      rw [hfilt, Finset.card_erase_of_mem hm1, hA_card]
      omega
  · have h2 := two_mul_card_pairs (b + 2)
    have hk : k = Pairs.card := Fintype.card_coe Pairs
    rw [hk]
    change 2 * Pairs.card + (b + 2) = (b + 2) * (b + 2) at h2
    nlinarith

end LowerBound

end PEqualNP.Outside.L_meta_989

open PEqualNP.Outside.L_meta_989 in
theorem PEqualNP.Outside.L_meta_989 : (∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) → (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) → (∀ i : Fin k, l i ≠ 0) → (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) → (∀ i : Fin k, (y i).card ≤ b) → (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) → (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) → (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) → 2 * k ≤ (b + 1) * (b + 2)) ∧ (∀ (F : Type) [Field F] [Fintype F] (b : ℕ), b + 1 ≤ Fintype.card F → ∃ (n k : ℕ) (pt : Fin n → Fin 3 → F) (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool), (∀ p : Fin n, pt p ≠ 0) ∧ (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧ (∀ v : Fin 3 → F, v ≠ 0 → ∃ (p : Fin n) (c : F), v = c • pt p) ∧ (∀ i : Fin k, l i ≠ 0) ∧ (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧ (∀ i : Fin k, (y i).card ≤ b) ∧ (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧ (∀ x x' : Fin n → Bool, (∀ v : Fin n, x v = true → x' v = true) → g x = true → g x' = true) ∧ (∀ (i : Fin k) (x : Fin n → Bool), g x = true → ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧ (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧ ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧ g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧ 2 * k = (b + 1) * (b + 2)) :=
  ⟨upper_bound, lower_bound⟩
