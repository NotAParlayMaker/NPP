import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7416_aux

theorem tbf (y i : ℕ) (h : y ≤ i) : y.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_le_of_lt h (by
    have := @Nat.lt_two_pow_self i
    exact (Nat.pow_le_pow_right (by norm_num) (le_refl i)).trans_lt' this |>.trans_le (le_refl _)))

theorem mem_le (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ≤ l.sum :=
  List.le_sum_of_mem h

theorem and_mask (y N : ℕ) (hy : y < N) : y &&& (2 ^ N - 1) = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < N
  · simp [hi]
  · simp [hi, tbf y i (by omega)]

end PEqualNP.Outside.L_meta_7416_aux

open PEqualNP.Outside.L_meta_7416_aux in
theorem PEqualNP.Outside.L_meta_7416 : ∀ (x1 : List ℕ) (x2 : ℕ), ∃ (x3 : ℕ), (∀ (x4 : ℕ), ∃ (x5 : ℕ), x3.testBit x5 = Bool.true ∧ x2.testBit x5 = x2.testBit x4 ∧ ∀ x6 ∈ x1, x6.testBit x5 = x6.testBit x4) ∧ (∀ x4 ∈ x1, x4 &&& x3 = x4) ∧ x2 &&& x3 = x2 := by
  intro x1 x2
  refine ⟨2 ^ (x2 + x1.sum + 1) - 1, ?_, ?_, ?_⟩
  · intro x4
    by_cases h4 : x4 < x2 + x1.sum + 1
    · refine ⟨x4, ?_, rfl, fun _ _ => rfl⟩
      rw [Nat.testBit_two_pow_sub_one]
      simp [h4]
    · refine ⟨x2 + x1.sum, ?_, ?_, ?_⟩
      · rw [Nat.testBit_two_pow_sub_one]
        simp
      · rw [tbf x2 _ (by omega), tbf x2 _ (by omega)]
      · intro x6 hx6
        have := mem_le x1 x6 hx6
        rw [tbf x6 _ (by omega), tbf x6 _ (by omega)]
  · intro x4 hx4
    have := mem_le x1 x4 hx4
    exact and_mask x4 _ (by omega)
  · exact and_mask x2 _ (by omega)
