import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_491 : ∀ (E k u v p : ℕ), u < v → v < 3 * (E + 1) → p < 2 * k → 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p < 3 * (E + 1) + 18 * k * (E + 1) ^ 2 ∧ 3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by
  intro E k u v p huv hv hp
  have e : 2 * k * (3 * (E + 1)) ^ 2 = 18 * k * (E + 1) ^ 2 := by ring
  refine ⟨?_, by rw [e]⟩
  rw [← e]
  have h1 : u * (3 * (E + 1)) + v + 1 ≤ (3 * (E + 1)) * (3 * (E + 1)) := by
    have h2 : (u + 1) * (3 * (E + 1)) ≤ (3 * (E + 1)) * (3 * (E + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  have h3 := Nat.mul_le_mul_left (2 * k) h1
  rw [Nat.mul_add, Nat.mul_one] at h3
  have e2 : (3 * (E + 1)) ^ 2 = (3 * (E + 1)) * (3 * (E + 1)) := by ring
  rw [e2]
  omega
