import Mathlib

theorem PEqualNP.Outside.L_meta_1659 : ∀ (q N c5 s k : ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → c5 ≤ 300 → 18 * q * (k + 1) ≤ 2 * c5 * s + N * q → N * (q + 1) ≤ 10 * s + 2 * q * k + 9 * N → 2 * N ≤ s + 1 → N * q ≤ 100 * s := by
  intro q N c5 s k hq hN hc hQ hP hI
  have hNpos : 1 ≤ N := by omega
  have hNs : N ≤ s := by omega
  have hcs : c5 * s ≤ 300 * s := Nat.mul_le_mul_right s hc
  have hmain : 8 * N * q ≤ 690 * s + 72 * N := by nlinarith
  by_cases hsmall : q < 100
  · calc
      N * q ≤ N * 100 := Nat.mul_le_mul_left N (by omega)
      _ ≤ 100 * s := by nlinarith
  · have hlarge : 100 ≤ q := by omega
    have hmul : 100 * N ≤ N * q := by nlinarith [Nat.mul_le_mul_left N hlarge]
    nlinarith