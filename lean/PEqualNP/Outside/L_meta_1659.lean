import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1659 : ∀ (q N c5 s k : ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → c5 ≤ 300 → 18 * q * (k + 1) ≤ 2 * c5 * s + N * q → N * (q + 1) ≤ 10 * s + 2 * q * k + 9 * N → 2 * N ≤ s + 1 → N * q ≤ 100 * s := by
  intro q N c5 s k hq hN hc5 h1 h2 h3
  have hcs : 2 * c5 * s ≤ 600 * s := by nlinarith
  have h1' : 18 * (q * k) + 18 * q ≤ 600 * s + N * q := by
    have : 18 * q * (k + 1) = 18 * (q * k) + 18 * q := by ring
    linarith
  have h2' : N * q + N ≤ 10 * s + 2 * (q * k) + 9 * N := by
    have : N * (q + 1) = N * q + N := by ring
    have : 2 * q * k = 2 * (q * k) := by ring
    linarith
  linarith
