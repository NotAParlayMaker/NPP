import Mathlib

namespace PEqualNP.Outside.L_scratch_mle

theorem chi_ne_zero {m : ℕ} {F : Type} [Field F] (x : Fin m → Bool) (r : Fin m → F)
    (hr : ∀ i, r i ≠ 0 ∧ r i ≠ 1) : (∏ i, (if x i then r i else 1 - r i)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i _
  by_cases hx : x i
  · simp [hx, (hr i).1]
  · simp only [hx, Bool.false_eq_true, ite_false]
    intro h0
    exact (hr i).2 (by linear_combination -h0)

end PEqualNP.Outside.L_scratch_mle

theorem PEqualNP.Outside.L_scratch_mle :
    ∀ {m : ℕ} {F : Type} [Field F] (A B : (Fin m → Bool) → F) (r : Fin m → F),
      (∀ i, r i ≠ 0 ∧ r i ≠ 1) → ∀ (x₀ : Fin m → Bool), A x₀ ≠ B x₀ → (∀ x, x ≠ x₀ → A x = B x) →
      (∑ x, A x * ∏ i, (if x i then r i else 1 - r i)) ≠ (∑ x, B x * ∏ i, (if x i then r i else 1 - r i)) := by
  intro m F _ A B r hr x₀ hx₀ hoff h
  have hdiff : (∑ x, A x * ∏ i, (if x i then r i else 1 - r i)) - (∑ x, B x * ∏ i, (if x i then r i else 1 - r i))
      = (A x₀ - B x₀) * ∏ i, (if x₀ i then r i else 1 - r i) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single x₀]
    · ring
    · intro x _ hx
      rw [hoff x hx]; ring
    · intro hx; exact absurd (Finset.mem_univ _) hx
  rw [h, sub_self] at hdiff
  rcases mul_eq_zero.mp hdiff.symm with h1 | h2
  · exact hx₀ (sub_eq_zero.mp h1)
  · exact PEqualNP.Outside.L_scratch_mle.chi_ne_zero x₀ r hr h2
