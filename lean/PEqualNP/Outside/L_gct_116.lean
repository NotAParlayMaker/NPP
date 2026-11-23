import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_116_aux

lemma perm_inv {n k : ℕ} (g : Fin n → Fin n → ℂ) (π : Equiv.Perm (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ σ : (↥S ≃ ↥T), ∏ i : ↥S, g (π i.val) (σ i).val)
    = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ σ : (↥S ≃ ↥T), ∏ i : ↥S, g i.val (σ i).val := by
  refine Finset.sum_nbij' (fun S => S.map π.toEmbedding) (fun S => S.map π.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_map] at hS ⊢
    exact hS
  · intro S hS
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and, Finset.card_map] at hS ⊢
    exact hS
  · intro S _
    ext x
    simp
  · intro S _
    ext x
    simp
  · intro S _
    refine Finset.sum_congr rfl ?_
    intro T _
    let e : ↥S ≃ ↥(S.map π.toEmbedding) := π.subtypeEquiv (by intro a; simp)
    refine Fintype.sum_equiv (Equiv.equivCongr e (Equiv.refl ↥T)) _ _ ?_
    intro σ
    refine Fintype.prod_equiv e _ _ ?_
    intro i
    simp [e]

lemma pow_inj_aux (n : ℕ) (ω : ℂ) (h1 : ω ^ n = 1) (h : ∀ s : ℕ, 0 < s → s < n → ω ^ s ≠ 1)
    (s t : ℕ) (hst : s < t) (ht : t < n) (he : ω ^ s = ω ^ t) : False := by
  have hω : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have e : ω ^ t = ω ^ s * ω ^ (t - s) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e] at he
  have he' : ω ^ s * 1 = ω ^ s * ω ^ (t - s) := by rw [mul_one]; exact he
  have := mul_left_cancel₀ (pow_ne_zero s hω) he'
  exact h (t - s) (by omega) (by omega) this.symm

lemma pow_inj (n : ℕ) (ω : ℂ) (h1 : ω ^ n = 1) (h : ∀ s : ℕ, 0 < s → s < n → ω ^ s ≠ 1) :
    Function.Injective (fun s : Fin n => ω ^ s.val) := by
  intro s t he
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact pow_inj_aux n ω h1 h s.val t.val hlt t.isLt he
  · exact pow_inj_aux n ω h1 h t.val s.val hlt s.isLt he.symm

open Polynomial in
noncomputable def P (n m k : ℕ) (ω : ℂ) (c : Fin m → Fin n → ℂ) : Polynomial ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ σ : (↥S ≃ ↥T), ∏ i : ↥S, ∑ a : Fin m, ∑ b : Fin n, C (c a b * ω ^ ((a.val + 1) * i.val.val + b.val * (σ i).val.val)) * X ^ (a.val + 1)

lemma P_eval (n m k : ℕ) (ω : ℂ) (c : Fin m → Fin n → ℂ) (z : ℂ) :
    (P n m k ω c).eval z = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ σ : (↥S ≃ ↥T), ∏ i : ↥S, ∑ a : Fin m, ∑ b : Fin n, c a b * ω ^ ((a.val + 1) * i.val.val + b.val * (σ i).val.val) * z ^ (a.val + 1) := by
  unfold P
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_prod, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

lemma P_deg (n m k : ℕ) (ω : ℂ) (c : Fin m → Fin n → ℂ) : (P n m k ω c).natDegree ≤ k * m := by
  unfold P
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro S hS
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro T _
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro σ _
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have hc : (Finset.univ : Finset ↥S).card = k := by
    rw [Finset.card_univ, Fintype.card_coe]
    exact (Finset.mem_powersetCard.mp hS).2
  have hb : ∀ i ∈ (Finset.univ : Finset ↥S), (∑ a : Fin m, ∑ b : Fin n, Polynomial.C (c a b * ω ^ ((a.val + 1) * i.val.val + b.val * (σ i).val.val)) * Polynomial.X ^ (a.val + 1)).natDegree ≤ m := by
    intro i _
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro a _
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro b _
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
    have := a.isLt
    omega
  have := Finset.sum_le_card_nsmul _ _ m hb
  rw [hc, smul_eq_mul] at this
  exact this

lemma P_zero (n m k : ℕ) (ω : ℂ) (c : Fin m → Fin n → ℂ) (hk : 1 ≤ k) :
    (P n m k ω c).eval 0 = 0 := by
  rw [P_eval]
  refine Finset.sum_eq_zero ?_
  intro S hS
  refine Finset.sum_eq_zero ?_
  intro T _
  refine Finset.sum_eq_zero ?_
  intro σ _
  have hc : S.card = k := (Finset.mem_powersetCard.mp hS).2
  have hne : S.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨x, hx⟩ := hne
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨x, hx⟩ : ↥S)) ?_
  simp

lemma P_shift (n m k : ℕ) (ω : ℂ) (c : Fin m → Fin n → ℂ) (h1 : ω ^ n = 1) (s : Fin n) :
    (P n m k ω c).eval (ω ^ s.val) = (P n m k ω c).eval 1 := by
  have : NeZero n := ⟨by have := s.isLt; omega⟩
  rw [P_eval, P_eval]
  have key := perm_inv (k := k) (fun i j : Fin n => ∑ a : Fin m, ∑ b : Fin n, c a b * ω ^ ((a.val + 1) * i.val + b.val * j.val)) (Equiv.addRight s)
  beta_reduce at key
  have hper : ∀ x : ℕ, ω ^ (x % n) = ω ^ x := fun x => (pow_eq_pow_mod x h1).symm
  simp only [one_pow, mul_one]
  refine Eq.trans ?_ key
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e : ω ^ ((a.val + 1) * ((i.val.val + s.val) % n)) = ω ^ ((a.val + 1) * (i.val.val + s.val)) := by
    rw [pow_mul', hper, ← pow_mul']
  rw [Equiv.coe_addRight, Fin.val_add, mul_assoc]
  congr 1
  rw [pow_add ω ((a.val + 1) * ((i.val.val + s.val) % n)) _, e, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

end PEqualNP.Outside.L_gct_116_aux

open PEqualNP.Outside.L_gct_116_aux in
theorem PEqualNP.Outside.L_gct_116 : ∀ (n m k : ℕ) (ω : ℂ) (c : Fin m → Fin n → ℂ), ω ^ n = 1 → (∀ s : ℕ, 0 < s → s < n → ω ^ s ≠ 1) → 1 ≤ k → k * m < n → (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∑ σ : (↥S ≃ ↥T), ∏ i : ↥S, ∑ a : Fin m, ∑ b : Fin n, c a b * ω ^ ((a.val + 1) * i.val.val + b.val * (σ i).val.val)) = 0 := by
  intro n m k ω c h1 hprim hk hkm
  have hQ : (P n m k ω c - Polynomial.C ((P n m k ω c).eval 1)) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (pow_inj n ω h1 hprim) ?_ ?_
    · intro s
      rw [Polynomial.eval_sub, Polynomial.eval_C, P_shift n m k ω c h1 s, sub_self]
    · rw [Fintype.card_fin]
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
      rw [Polynomial.natDegree_C]
      have := P_deg n m k ω c
      omega
  have h0 : (P n m k ω c - Polynomial.C ((P n m k ω c).eval 1)).eval 0 = 0 := by
    rw [hQ, Polynomial.eval_zero]
  rw [Polynomial.eval_sub, Polynomial.eval_C, P_zero n m k ω c hk] at h0
  have h2 : (P n m k ω c).eval 1 = 0 := by
    simpa using h0
  rw [P_eval] at h2
  simpa only [one_pow, mul_one] using h2
