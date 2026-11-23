import PEqualNP.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PEqualNP.Outside

private def permRestrictEquiv {n k : ℕ} (C R : Finset (Fin n))
    (hC : C.card = k) (hR : R.card = k) :
    {σ : Equiv.Perm (Fin n) // C.image σ = R} ≃
      Equiv.Perm (Fin k) × ({x : Fin n // x ∉ C} ≃ {y : Fin n // y ∉ R}) where
  toFun := fun ⟨σ, hσ⟩ =>
    let eC : Fin k ≃ {x : Fin n // x ∈ C} := (C.orderIsoOfFin hC).toEquiv
    let eR : Fin k ≃ {y : Fin n // y ∈ R} := (R.orderIsoOfFin hR).toEquiv
    let e1 : {x : Fin n // x ∈ C} ≃ {y : Fin n // y ∈ R} :=
      { toFun := fun x => ⟨σ x.1, by rw [← hσ]; exact Finset.mem_image_of_mem σ x.2⟩
        invFun := fun y =>
          ⟨σ.symm y.1, by
            have hy : y.1 ∈ C.image σ := by rw [hσ]; exact y.2
            rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
            simpa [← hxy] using hx⟩
        left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1) }
    let e2 : {x : Fin n // x ∉ C} ≃ {y : Fin n // y ∉ R} :=
      { toFun := fun x =>
          ⟨σ x.1, by
            intro hy
            have hy' : σ x.1 ∈ C.image σ := by rw [hσ]; exact hy
            rcases Finset.mem_image.mp hy' with ⟨a, ha, hax⟩
            exact x.2 (σ.injective hax ▸ ha)⟩
        invFun := fun y =>
          ⟨σ.symm y.1, by
            intro hx
            have hy : σ (σ.symm y.1) ∈ C.image σ := Finset.mem_image_of_mem σ hx
            rw [hσ, σ.apply_symm_apply] at hy
            exact y.2 hy⟩
        left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1) }
    (eC.trans (e1.trans eR.symm), e2)
  invFun := fun ⟨τ, e2⟩ =>
    let eC : Fin k ≃ {x : Fin n // x ∈ C} := (C.orderIsoOfFin hC).toEquiv
    let eR : Fin k ≃ {y : Fin n // y ∈ R} := (R.orderIsoOfFin hR).toEquiv
    let e1 : {x : Fin n // x ∈ C} ≃ {y : Fin n // y ∈ R} := eC.symm.trans (τ.trans eR)
    let σ : Equiv.Perm (Fin n) :=
      (Equiv.sumCompl (· ∈ C)).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ R)))
    ⟨σ, by
      ext y
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hval : σ x = (e1 ⟨x, hx⟩).1 := by
          simp [σ, Equiv.sumCompl_symm_apply_of_pos hx]
        rw [hval]
        exact (e1 ⟨x, hx⟩).2
      · intro hy
        refine ⟨(e1.symm ⟨y, hy⟩).1, (e1.symm ⟨y, hy⟩).2, ?_⟩
        have hval : σ (e1.symm ⟨y, hy⟩).1 = (e1 (e1.symm ⟨y, hy⟩)).1 := by
          simp [σ, Equiv.sumCompl_symm_apply_of_pos (e1.symm ⟨y, hy⟩).2]
        rw [hval, e1.apply_symm_apply]⟩
  left_inv := fun ⟨σ, hσ⟩ => by
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ C
    · simp [Equiv.sumCompl_symm_apply_of_pos hx]
    · simp [Equiv.sumCompl_symm_apply_of_neg hx]
  right_inv := fun ⟨τ, e2⟩ => by
    apply Prod.ext
    · ext b
      have hb : ((C.orderIsoOfFin hC) b).1 ∈ C := ((C.orderIsoOfFin hC) b).2
      simp [Equiv.sumCompl_symm_apply_of_pos hb]
      apply congrArg Fin.val
      convert (R.orderIsoOfFin hR).symm_apply_apply (τ b)
      exact (Finset.coe_orderIsoOfFin_apply R hR (τ b)).symm
    · ext x
      simp [Equiv.sumCompl_symm_apply_of_neg x.2]

private lemma sum_perm_prod_eq {n k : ℕ} (t : Fin n × Fin n → ℂ)
    (C : Finset (Fin n)) (hC : C.card = k) :
    (∑ σ : Equiv.Perm (Fin n), ∏ a ∈ C, t (σ a, a)) =
      ((n - k).factorial : ℂ) *
        ∑ R : Finset (Fin n),
          if hR : R.card = k then
            Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b))
          else 0 := by
  have hpart :
      (∑ σ : Equiv.Perm (Fin n), ∏ a ∈ C, t (σ a, a)) =
        ∑ R : Finset (Fin n), ∑ σ : Equiv.Perm (Fin n),
          if C.image σ = R then ∏ a ∈ C, t (σ a, a) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp
  rw [hpart, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  by_cases hR : R.card = k
  · simp only [dif_pos hR]
    have hsub :
        (∑ σ : Equiv.Perm (Fin n), if C.image σ = R then ∏ a ∈ C, t (σ a, a) else 0) =
          ∑ p : {σ : Equiv.Perm (Fin n) // C.image σ = R}, ∏ a ∈ C, t (p.1 a, a) := by
      rw [← Finset.sum_filter, ← Finset.sum_coe_sort]
      exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun σ => by simp) _ _ (fun _ => rfl)
    rw [hsub]
    rw [Fintype.sum_equiv (permRestrictEquiv C R hC hR)
      (fun p => ∏ a ∈ C, t (p.1 a, a))
      (fun q => ∏ b : Fin k, t (R.orderEmbOfFin hR (q.1 b), C.orderEmbOfFin hC b))]
    · rw [Fintype.sum_prod_type_right]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard_eq : Fintype.card {x : Fin n // x ∉ C} = n - k := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hC]
      have hcard_eqR : Fintype.card {y : Fin n // y ∉ R} = n - k := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hR]
      have hcard_equiv :
          Fintype.card ({x : Fin n // x ∉ C} ≃ {y : Fin n // y ∉ R}) = (n - k).factorial := by
        let e : {x : Fin n // x ∉ C} ≃ {y : Fin n // y ∉ R} :=
          Fintype.equivOfCardEq (hcard_eq.trans hcard_eqR.symm)
        have heq :
            Fintype.card ({x : Fin n // x ∉ C} ≃ {y : Fin n // y ∉ R}) =
              Fintype.card (Equiv.Perm {x : Fin n // x ∉ C}) :=
          Fintype.card_congr
            { toFun := fun f => f.trans e.symm
              invFun := fun g => g.trans e
              left_inv := fun f => by ext x; simp
              right_inv := fun g => by ext x; simp }
        rw [heq, Fintype.card_perm, hcard_eq]
      rw [hcard_equiv]
      rfl
    · intro ⟨σ, hσ⟩
      have hprod :
          (∏ a ∈ C, t (σ a, a)) =
            ∏ b : Fin k, t (σ (C.orderEmbOfFin hC b), C.orderEmbOfFin hC b) := by
        rw [← Finset.prod_coe_sort C (fun a => t (σ a, a))]
        exact (Fintype.prod_equiv (C.orderIsoOfFin hC).toEquiv
          (fun b => t (σ (C.orderEmbOfFin hC b), C.orderEmbOfFin hC b))
          (fun a => t (σ a.1, a.1))
          (fun b => rfl)).symm
      rw [hprod]
      refine Finset.prod_congr rfl fun b _ => ?_
      have happly :
          R.orderEmbOfFin hR ((permRestrictEquiv C R hC hR ⟨σ, hσ⟩).1 b) =
            σ (C.orderEmbOfFin hC b) := by
        change ((R.orderIsoOfFin hR)
          ((R.orderIsoOfFin hR).symm ⟨σ ((C.orderIsoOfFin hC) b).1, _⟩)).1 = _
        rw [(R.orderIsoOfFin hR).apply_symm_apply]
        rfl
      rw [happly]
  · simp only [dif_neg hR, mul_zero]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [if_neg]
    intro hσ
    apply hR
    rw [← hσ, Finset.card_image_of_injective C σ.injective, hC]

theorem L_gct_205 :
    ∀ n : ℕ, ∀ L Z : Submodule ℂ (Fin n × Fin n → ℂ),
      (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n →
        (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
          if h : R.card = k ∧ C.card = k then
            Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
          else 0) = 0) →
      (∀ z ∈ Z, Matrix.permanent (Matrix.of fun a b => z (a, b)) = 0) →
      (fun _ => (1 : ℂ)) ∉ L ⊔ Z := by
  intro n L Z hL hZ hmem
  rw [Submodule.mem_sup] at hmem
  rcases hmem with ⟨t, ht, z, hz, htz⟩
  have hz_eq : ∀ p : Fin n × Fin n, z p = (-t p) + 1 := by
    intro p
    have hp : t p + z p = 1 := congr_fun htz p
    linear_combination hp
  have hperm_zero : Matrix.permanent (Matrix.of fun a b => z (a, b)) = 0 := hZ z hz
  have hexpand :
      Matrix.permanent (Matrix.of fun a b => z (a, b)) =
        ∑ C : Finset (Fin n), (-1 : ℂ) ^ C.card *
          ∑ σ : Equiv.Perm (Fin n), ∏ a ∈ C, t (σ a, a) := by
    unfold Matrix.permanent
    simp only [Matrix.of_apply, hz_eq]
    have hstep :
        (∑ σ : Equiv.Perm (Fin n), ∏ a : Fin n, (-t (σ a, a) + 1)) =
          ∑ σ : Equiv.Perm (Fin n), ∑ C : Finset (Fin n),
            (-1 : ℂ) ^ C.card * ∏ a ∈ C, t (σ a, a) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.prod_add]
      have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
        ext S
        simp
      rw [hpow]
      refine Finset.sum_congr rfl fun C _ => ?_
      simp [Finset.prod_neg]
    rw [hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finset.mul_sum]
  have hfiber :
      (∑ C : Finset (Fin n), (-1 : ℂ) ^ C.card *
          ∑ σ : Equiv.Perm (Fin n), ∏ a ∈ C, t (σ a, a)) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ C ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun C => C.card = k),
            (-1 : ℂ) ^ C.card * ∑ σ : Equiv.Perm (Fin n), ∏ a ∈ C, t (σ a, a) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun C _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using C.card_le_univ))) _
  have hrange :
      (∑ k ∈ Finset.range (n + 1),
          ∑ C ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun C => C.card = k),
            (-1 : ℂ) ^ C.card * ∑ σ : Equiv.Perm (Fin n), ∏ a ∈ C, t (σ a, a)) =
        (n.factorial : ℂ) := by
    rw [Finset.sum_range_succ']
    have hrest :
        (∑ k ∈ Finset.range n,
          ∑ C ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun C => C.card = k + 1),
            (-1 : ℂ) ^ C.card * ∑ σ : Equiv.Perm (Fin n), ∏ a ∈ C, t (σ a, a)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have hkn : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have hterm :
          (∑ C ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun C => C.card = k + 1),
              (-1 : ℂ) ^ C.card * ∑ σ : Equiv.Perm (Fin n), ∏ a ∈ C, t (σ a, a)) =
            (-1 : ℂ) ^ (k + 1) * ((n - (k + 1)).factorial : ℂ) *
              (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
                if h : R.card = k + 1 ∧ C.card = k + 1 then
                  Matrix.permanent
                    (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
                else 0) := by
        rw [Finset.sum_comm]
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun C _ => ?_
        by_cases hC : C.card = k + 1
        · rw [if_pos hC, sum_perm_prod_eq t C hC, ← mul_assoc]
          have hpow : (-1 : ℂ) ^ C.card = (-1 : ℂ) ^ (k + 1) := by rw [hC]
          rw [hpow]
          congr 1
          refine Finset.sum_congr rfl fun R _ => ?_
          by_cases hR : R.card = k + 1
          · simp [hR, hC]
          · simp [hR]
        · rw [if_neg hC]
          symm
          rw [mul_eq_zero]
          right
          refine Finset.sum_eq_zero fun R _ => ?_
          have hnot : ¬ (R.card = k + 1 ∧ C.card = k + 1) := fun h => hC h.2
          simp [hnot]
      rw [hterm, hL t ht (k + 1) hk1 hkn, mul_zero]
    rw [hrest, zero_add]
    have hzero_filter :
        (Finset.univ : Finset (Finset (Fin n))).filter (fun C => C.card = 0) = {∅} := by
      ext C
      simp
    rw [hzero_filter, Finset.sum_singleton]
    simp [Fintype.card_perm]
  have hfact_zero : (n.factorial : ℂ) = 0 := by
    rw [← hrange, ← hfiber, ← hexpand, hperm_zero]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) hfact_zero

end PEqualNP.Outside
