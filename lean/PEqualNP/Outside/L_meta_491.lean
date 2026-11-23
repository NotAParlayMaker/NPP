import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_491 : ∀ (E k u v p : ℕ), u < v → v < 3 * (E + 1) → p < 2 * k → 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p < 3 * (E + 1) + 18 * k * (E + 1) ^ 2 ∧ 3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by
  intro E k u v p huv hv hp
  constructor
  · have hu : u < 3 * (E + 1) := lt_trans huv hv
    have hi : u * (3 * (E + 1)) + v < (3 * (E + 1)) ^ 2 := by
      calc
        u * (3 * (E + 1)) + v < u * (3 * (E + 1)) + 3 * (E + 1) :=
          Nat.add_lt_add_left hv _
        _ = (u + 1) * (3 * (E + 1)) := by ring
        _ ≤ (3 * (E + 1)) * (3 * (E + 1)) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hu)
        _ = (3 * (E + 1)) ^ 2 := by ring
    have hs := Nat.mul_le_mul_left (2 * k) (Nat.succ_le_of_lt hi)
    calc
      3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p <
          3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + 2 * k :=
        Nat.add_lt_add_left hp _
      _ = 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v + 1) := by ring
      _ ≤ 3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 := Nat.add_le_add_left hs _
      _ = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by ring
  · ring
