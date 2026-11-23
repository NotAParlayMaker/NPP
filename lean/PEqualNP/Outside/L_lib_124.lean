import Mathlib

namespace PEqualNP.Outside.L_lib_124
lemma succ_pow_ge (p : ℕ) : ∀ n : ℕ, (n + 1) * p ^ n ≤ (p + 1) ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc (n + 1 + 1) * p ^ (n + 1)
        = (n + 1) * p ^ n * p + p ^ (n + 1) := by ring
      _ ≤ (p + 1) ^ (n + 1) * p + (p + 1) ^ (n + 1) := by gcongr <;> omega
      _ = (p + 1) ^ (n + 1 + 1) := by ring
end PEqualNP.Outside.L_lib_124

theorem my_step : ∀ p' q : ℕ, p' < q → ∀ k : ℕ, ∃ i : ℕ, 2 * k * p' ^ i ≤ q ^ i := by
  intro p' q hpq k
  refine ⟨2 * k * p' + 1, ?_⟩
  calc 2 * k * p' ^ (2 * k * p' + 1)
      = 2 * k * p' * p' ^ (2 * k * p') := by ring
    _ ≤ (2 * k * p' + 1) * p' ^ (2 * k * p') := by gcongr; omega
    _ ≤ (p' + 1) ^ (2 * k * p' + 1) := PEqualNP.Outside.L_lib_124.succ_pow_ge p' _
    _ ≤ q ^ (2 * k * p' + 1) := Nat.pow_le_pow_left hpq _
