import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_491 : ∀ (E k u v p : ℕ), u < v → v < 3 * (E + 1) → p < 2 * k → 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p < 3 * (E + 1) + 18 * k * (E + 1) ^ 2 ∧ 3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by
  intro E k u v p huv hv hp
  have hsq : 18 * k * (E + 1) ^ 2 = 2 * k * ((3 * (E + 1)) * (3 * (E + 1))) := by ring
  refine ⟨?_, by rw [hsq]; ring⟩
  rw [hsq]
  generalize 3 * (E + 1) = M at hv ⊢
  have h0 : (u + 1) * M ≤ M * M := Nat.mul_le_mul_right M (by omega)
  have h1 : u * M + v + 1 ≤ M * M := by nlinarith
  have h2 : 2 * k * (u * M + v + 1) ≤ 2 * k * (M * M) := Nat.mul_le_mul_left (2 * k) h1
  have h3 : 2 * k * (u * M + v + 1) = 2 * k * (u * M + v) + 2 * k := by ring
  omega
