import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_683_aux

theorem main (F : Type) [Field F] [Fintype F] [CharP F 2] :
    ∃ b : F, ∀ x : F, x ^ 2 + b * x + 1 ≠ 0 := by
  have h11 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hns : ¬ Function.Surjective (fun s : F => s ^ 2 + s) := by
    intro hs
    have hi := Finite.injective_iff_surjective.mpr hs
    have h := @hi 0 1 (by simp [h11])
    exact zero_ne_one h
  obtain ⟨c, hc⟩ : ∃ c, ∀ s : F, s ^ 2 + s ≠ c := by
    by_contra h
    push_neg at h
    exact hns (fun c => h c)
  have hc0 : c ≠ 0 := fun h => hc 0 (by simp [h])
  have hinj : Function.Injective (fun s : F => s ^ 2) := by
    intro a b hab
    have hab' : a ^ 2 = b ^ 2 := hab
    have h2 : (a + b) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hab']
      exact CharTwo.add_self_eq_zero _
    exact CharTwo.add_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp h2)
  obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.mp hinj c⁻¹
  have hb2 : b ^ 2 = c⁻¹ := hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    have : c⁻¹ = 0 := by rw [← hb2]; simp
    exact hc0 (inv_eq_zero.mp this)
  refine ⟨b, fun x hx => hc (x / b) ?_⟩
  have h1 : x ^ 2 + b * x = 1 := by linear_combination hx - h11
  have h3 : (x / b) ^ 2 + x / b = (x ^ 2 + b * x) / b ^ 2 := by field_simp
  rw [h3, h1, hb2]
  simp

end PEqualNP.Outside.L_meta_683_aux

theorem PEqualNP.Outside.L_meta_683 : ∀ (F : Type) [Field F] [Fintype F] [CharP F 2],
    ∃ b : F, ∀ x : F, x ^ 2 + b * x + 1 ≠ 0 := by
  intro F _ _ _
  exact PEqualNP.Outside.L_meta_683_aux.main F
