import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6363 : ∀ (x1 : List ℕ) (x2 : ℕ), ∃ (x3 : ℕ), x2 &&& x3 = x2 ∧ (∀ x4 ∈ x1, x4 &&& x3 = x4) ∧ ∀ (x4 : ℕ), ∃ (x5 : ℕ), x3.testBit x5 = Bool.true ∧ x2.testBit x5 = x2.testBit x4 ∧ ∀ x6 ∈ x1, x6.testBit x5 = x6.testBit x4 := by
  intro l a
  have hle : ∀ v ∈ l, v ≤ l.sum := fun v hv => List.le_sum_of_mem hv
  have hpow : ∀ v, v ≤ a + l.sum → v < 2 ^ (a + l.sum) := fun v hv =>
    lt_of_le_of_lt hv Nat.lt_two_pow_self
  have hsub : ∀ v, v ≤ a + l.sum → v &&& (2 ^ (a + l.sum + 1) - 1) = v := by
    intro v hv
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (lt_trans (hpow v hv) (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  have hz : ∀ v, v ≤ a + l.sum → ∀ p, a + l.sum ≤ p → v.testBit p = false := by
    intro v hv p hp
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hpow v hv) (Nat.pow_le_pow_right (by norm_num) hp))
  refine ⟨2 ^ (a + l.sum + 1) - 1, hsub a (by omega), fun v hv => hsub v (by have := hle v hv; omega), ?_⟩
  intro p
  by_cases hp : p < a + l.sum + 1
  · exact ⟨p, by rw [Nat.testBit_two_pow_sub_one]; simpa using hp, rfl, fun _ _ => rfl⟩
  · refine ⟨a + l.sum, by rw [Nat.testBit_two_pow_sub_one]; simp, ?_, ?_⟩
    · rw [hz a (by omega) _ le_rfl, hz a (by omega) p (by omega)]
    · intro v hv
      have := hle v hv
      rw [hz v (by omega) _ le_rfl, hz v (by omega) p (by omega)]
