import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_683 :
    ∀ (F : Type) [Field F] [Fintype F] [CharP F 2],
    ∃ b : F, ∀ x : F, x ^ 2 + b * x + 1 ≠ 0 := by
  intro F _ _ _
  classical
  have hcard : ((Finset.univ.erase (0 : F)).image (fun x : F => -(x + x⁻¹))).card
      < Fintype.card F := by
    calc ((Finset.univ.erase (0 : F)).image (fun x : F => -(x + x⁻¹))).card
        ≤ (Finset.univ.erase (0 : F)).card := Finset.card_image_le
      _ = Fintype.card F - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      _ < Fintype.card F := Nat.sub_lt Fintype.card_pos Nat.zero_lt_one
  obtain ⟨b, hb⟩ : ∃ b : F, b ∉ (Finset.univ.erase (0 : F)).image (fun x : F => -(x + x⁻¹)) := by
    by_contra h
    push_neg at h
    rw [Finset.eq_univ_iff_forall.mpr h, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  refine ⟨b, fun x hx => hb ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have h1 : b * x = -(x ^ 2 + 1) := by linear_combination hx
  have h2 : x ^ 2 * x⁻¹ = x := by rw [pow_two, mul_assoc, hxinv, mul_one]
  have h3 : -(x + x⁻¹) = b := by
    calc -(x + x⁻¹) = -(x ^ 2 + 1) * x⁻¹ := by linear_combination h2
      _ = b * x * x⁻¹ := by rw [h1]
      _ = b := by rw [mul_assoc, hxinv, mul_one]
  exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ x⟩, h3⟩
