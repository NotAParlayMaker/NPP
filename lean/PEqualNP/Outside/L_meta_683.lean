import Mathlib

theorem PEqualNP.Outside.L_meta_683 :
    ∀ (F : Type) [Field F] [Fintype F] [CharP F 2],
      ∃ b : F, ∀ x : F, x ^ 2 + b * x + 1 ≠ 0 := by
  intro F _ _ _
  have htwo : (1 : F) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharP.cast_eq_zero F 2
  let f (s : F) := s ^ 2 + s
  have hnot : ¬ Function.Surjective f := by
    intro h
    have hi := Finite.injective_iff_surjective.mpr h
    have h01 : f 0 = f 1 := by simp [f, htwo]
    exact zero_ne_one (hi h01)
  obtain ⟨c, hc⟩ := not_forall.mp hnot
  have hc0 : c ≠ 0 := by
    intro h
    exact hc ⟨0, by simp [f, h]⟩
  have hsquare : Function.Surjective (fun x : F => x ^ 2) :=
    Finite.injective_iff_surjective.mp (frobenius F 2).injective
  obtain ⟨a, ha⟩ := hsquare c
  have ha0 : a ≠ 0 := by
    intro h
    exact hc0 (by simpa [h] using ha.symm)
  refine ⟨a⁻¹, ?_⟩
  intro x hx
  apply hc
  refine ⟨a * x, ?_⟩
  have hsum : (a * x) ^ 2 + a * x + c = 0 := by
    calc
      (a * x) ^ 2 + a * x + c = a ^ 2 * (x ^ 2 + a⁻¹ * x + 1) := by
        rw [← ha]
        field_simp
      _ = 0 := by rw [hx, mul_zero]
  have hcneg : -c = c := by
    apply neg_eq_of_add_eq_zero_left
    calc
      c + c = c * ((1 : F) + 1) := by ring
      _ = 0 := by rw [htwo, mul_zero]
  exact (eq_neg_of_add_eq_zero_left hsum).trans hcneg
