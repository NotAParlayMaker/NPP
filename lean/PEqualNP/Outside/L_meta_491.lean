import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_491 : ∀ (E k u v p : ℕ), u < v → v < 3 * (E + 1) → p < 2 * k → 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p < 3 * (E + 1) + 18 * k * (E + 1) ^ 2 ∧ 3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by
  intro E k u v p huv hv hp
  let B := 3 * (E + 1)
  have hvB : v < B := hv
  have huB : u + 1 ≤ B := by omega
  have hindex : u * B + v < B ^ 2 := calc
    u * B + v < u * B + B := Nat.add_lt_add_left hvB _
    _ = (u + 1) * B := by ring
    _ ≤ B * B := Nat.mul_le_mul_right B huB
    _ = B ^ 2 := by ring
  have hscale := Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt hindex)
  have hlast : 2 * k * (u * B + v) + p < 2 * k * B ^ 2 := by
    rw [Nat.mul_succ] at hscale
    omega
  have hsize : 2 * k * B ^ 2 = 18 * k * (E + 1) ^ 2 := by dsimp [B]; ring
  rw [hsize] at hlast
  constructor
  · change B + 2 * k * (u * B + v) + p < B + 18 * k * (E + 1) ^ 2
    omega
  · exact congrArg (B + ·) hsize
