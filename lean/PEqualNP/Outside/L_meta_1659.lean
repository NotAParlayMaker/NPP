import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1659 : ∀ (q N c5 s k : ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → c5 ≤ 300 → 18 * q * (k + 1) ≤ 2 * c5 * s + N * q → N * (q + 1) ≤ 10 * s + 2 * q * k + 9 * N → 2 * N ≤ s + 1 → N * q ≤ 100 * s := by
  intro q N c5 s k hq _ hc price cover inputs
  have priceCap := Nat.mul_le_mul_right s hc
  nlinarith only [hq, priceCap, price, cover, inputs, Nat.zero_le s]
