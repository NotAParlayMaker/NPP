import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_108_aux

/-- A vector of length `m` as a `2 × (m + 1)` matrix: the first row is the vector followed by
minus its sum, the second row is zero. -/
noncomputable def emb (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] (Fin 2 × Fin (m + 1) → ℂ) where
  toFun v := fun p =>
    if p.1 = 0 then (if h : (p.2 : ℕ) < m then v ⟨p.2, h⟩ else -∑ k, v k) else 0
  map_add' v w := by
    funext p
    simp only [Pi.add_apply]
    split_ifs
    · rfl
    · rw [Finset.sum_add_distrib]; ring
    · simp
  map_smul' c v := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · rw [← Finset.mul_sum]; ring
    · simp

theorem emb_zero_row (m : ℕ) (v : Fin m → ℂ) (j : Fin (m + 1)) :
    emb m v (0, j) = if h : (j : ℕ) < m then v ⟨j, h⟩ else -∑ k, v k := by
  simp [emb]

theorem emb_one_row (m : ℕ) (v : Fin m → ℂ) (j : Fin (m + 1)) : emb m v (1, j) = 0 := by
  simp [emb]

theorem emb_injective (m : ℕ) : Function.Injective (emb m) := by
  intro v w h
  funext k
  have := congrFun h (0, k.castSucc)
  simpa [emb_zero_row] using this

theorem emb_sum (m : ℕ) (v : Fin m → ℂ) : ∑ j, emb m v (0, j) = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [emb_zero_row]

end PEqualNP.Outside.L_gct_108_aux

open PEqualNP.Outside.L_gct_108_aux in
theorem PEqualNP.Outside.L_gct_108 : ∀ (q : ℕ), 2 ≤ q → ∃ L : Submodule ℂ (Fin 2 × Fin q → ℂ), (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) ∧ Module.finrank ℂ L + 1 = q := by
  intro q hq
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  refine ⟨LinearMap.range (emb m), ?_, ?_⟩
  · rintro t ⟨v, rfl⟩
    constructor
    · simp only [emb_one_row, add_zero]
      exact emb_sum m v
    · simp [emb_one_row]
  · rw [LinearMap.finrank_range_of_inj (emb_injective m)]
    simp
