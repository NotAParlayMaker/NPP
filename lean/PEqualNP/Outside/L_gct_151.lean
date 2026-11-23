import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_151 : ∀ (q : ℕ) (Z : Submodule ℂ (Fin q → ℂ)) (y : Fin q → ℂ), y ∈ Z → (Finset.univ.sum fun j : Fin q => y j) ≠ 0 → (∀ y' ∈ Z, (Finset.univ.sum fun j : Fin q => y' j) ≠ 0 → (∀ j : Fin q, y j = 0 → y' j = 0) → ∀ j : Fin q, y' j = 0 → y j = 0) → ∀ x ∈ Z, (∀ j : Fin q, y j = 0 → x j = 0) → ∃ c : ℂ, x = c • y := by
  intro q Z y hy hs hmin x hx hsupp
  refine ⟨(Finset.univ.sum fun j : Fin q => x j) / (Finset.univ.sum fun j : Fin q => y j), ?_⟩
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hyj : y j = 0
  · rw [hsupp j hyj, hyj, mul_zero]
  · have key : (Finset.univ.sum fun k : Fin q => x k) = (x j / y j) * (Finset.univ.sum fun k : Fin q => y k) := by
      by_contra hne
      have hz : x - (x j / y j) • y ∈ Z := Z.sub_mem hx (Z.smul_mem _ hy)
      have hzs : (Finset.univ.sum fun k : Fin q => (x - (x j / y j) • y) k) ≠ 0 := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        exact sub_ne_zero.mpr hne
      have hzsupp : ∀ k : Fin q, y k = 0 → (x - (x j / y j) • y) k = 0 := by
        intro k hk
        simp [hsupp k hk, hk]
      have := hmin _ hz hzs hzsupp j (by simp [div_mul_cancel₀ _ hyj])
      exact hyj this
    rw [key]
    field_simp
