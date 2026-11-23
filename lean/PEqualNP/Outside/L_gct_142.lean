import Mathlib
import PEqualNP.Defs

open Finset

-- Adding the two product expansions cancels every odd degree.
private theorem product_pair {n : ℕ} (w : Fin n → ℂ)
    (h : ∀ j : ℕ, 1 ≤ j → ∑ S ∈ (univ : Finset (Fin n)).powersetCard (2 * j),
      ∏ i ∈ S, w i = 0) :
    (∏ i, (1 + w i)) + (∏ i, (1 + -w i)) = 2 := by
  classical
  rw [prod_one_add, prod_one_add, ← sum_add_distrib, sum_powerset]
  rw [sum_eq_single 0]
  · norm_num
  · intro k _ hk
    by_cases he : Even k
    · obtain ⟨j, hj⟩ := he
      have hk' : k = 2 * j := by omega
      have hz := h j (by omega)
      rw [← hk'] at hz
      calc
        _ = ∑ S ∈ (univ : Finset (Fin n)).powersetCard k, ((∏ i ∈ S, w i) + ∏ i ∈ S, w i) := by
          apply sum_congr rfl
          intro S hS
          rw [prod_neg, (mem_powersetCard.mp hS).2, hk', pow_mul]
          simp
        _ = 0 := by rw [sum_add_distrib, hz, add_zero]
    · apply sum_eq_zero
      intro S hS
      rw [prod_neg, (mem_powersetCard.mp hS).2, (Nat.not_even_iff_odd.mp he).neg_one_pow]
      ring
  · simp

theorem PEqualNP.Outside.L_gct_142 :
    ∀ (n : ℕ) (W : Submodule ℂ (Fin n → ℂ)), (∀ w ∈ W, ∀ j : ℕ, 1 ≤ j →
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (2 * j), ∏ i ∈ S, w i = 0) →
      Module.finrank ℂ W ≤ 1 := by
  classical
  intro n W h
  by_cases hex : ∃ (v : Fin n → ℂ), v ∈ W ∧ ∃ i, v i ≠ 0
  · obtain ⟨v, hv, i, hi⟩ := hex
    let e : W →ₗ[ℂ] ℂ := (LinearMap.proj i).comp W.subtype
    have hinj : Function.Injective e := by
      apply (injective_iff_map_eq_zero _).2
      intro w hw
      change w.val i = 0 at hw
      apply Subtype.ext
      funext j
      change w.val j = 0
      by_contra hj
      -- This linear combination has coordinates 1 and -1, killing both products.
      let a : ℂ := (v i)⁻¹
      let b : ℂ := (-1 - a * v j) / w.val j
      let u := a • v + b • w.val
      have hu : u ∈ W := W.add_mem (W.smul_mem a hv) (W.smul_mem b w.property)
      have hui : u i = 1 := by simp [u, a, hw, hi]
      have huj : u j = -1 := by
        change a * v j + ((-1 - a * v j) / w.val j) * w.val j = -1
        rw [div_mul_cancel₀ _ hj]
        ring
      have hp := product_pair u (h u hu)
      have h₁ : (∏ k, (1 + u k)) = 0 :=
        prod_eq_zero (mem_univ j) (by simp [huj])
      have h₂ : (∏ k, (1 + -u k)) = 0 :=
        prod_eq_zero (mem_univ i) (by simp [hui])
      rw [h₁, h₂] at hp
      norm_num at hp
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  · have hW : W = ⊥ := by
      apply bot_unique
      intro v hv
      change v = 0
      funext i
      exact not_ne_iff.mp (fun hvi => hex ⟨v, hv, i, hvi⟩)
    rw [hW, finrank_bot]
    decide
