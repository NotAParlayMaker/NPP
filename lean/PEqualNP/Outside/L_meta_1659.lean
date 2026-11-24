import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1659 : ∀ (q N c5 s k : ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → c5 ≤ 300 → 18 * q * (k + 1) ≤ 2 * c5 * s + N * q → N * (q + 1) ≤ 10 * s + 2 * q * k + 9 * N → 2 * N ≤ s + 1 → N * q ≤ 100 * s := by
  intro q N c5 s k hq _ hc h1 h2 h3
  have hC : c5 * s ≤ 300 * s := Nat.mul_le_mul_right s hc
  have e1 : 18 * q * (k + 1) = 18 * (q * k) + 18 * q := by ring
  have e2 : 2 * c5 * s = 2 * (c5 * s) := by ring
  have e3 : N * (q + 1) = N * q + N := by ring
  have e4 : 2 * q * k = 2 * (q * k) := by ring
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  omega
