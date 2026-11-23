import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_683 : ∀ (F : Type) [Field F] [Fintype F] [CharP F 2],
    ∃ b : F, ∀ x : F, x ^ 2 + b * x + 1 ≠ 0 := by
  intro F _ _ _
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let g : F → F := fun x => x + x⁻¹
  have hni : ¬ Function.Injective g := by
    intro hinj
    have h : g 0 = g 1 := by
      show (0 : F) + 0⁻¹ = 1 + 1⁻¹
      rw [inv_zero, inv_one, add_zero]
      linear_combination -h2
    exact zero_ne_one (hinj h)
  have hns : ¬ Function.Surjective g := fun hs => hni (Finite.injective_iff_surjective.mpr hs)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨b, hb⟩ := hns
  refine ⟨b, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · subst h0
    simp at hx
  · have key : b * x = x ^ 2 + 1 := by linear_combination hx - (x ^ 2 + 1) * h2
    have hinv : x * x⁻¹ = 1 := mul_inv_cancel₀ h0
    exact hb x (by
      show x + x⁻¹ = b
      linear_combination (-x⁻¹) * key + (b - x) * hinv)
