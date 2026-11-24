import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1977_aux

theorem core : ∀ (a b c : Fin 13), a ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → b ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → c ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → a ≠ b → a ≠ c → b ≠ c → ∀ (t : Fin 13), a - t ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → b - t ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → c - t ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → (0 - a - b - c) - t ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1977_aux

theorem PEqualNP.Outside.L_meta_1977 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 x4 x5 : Fin (13 : ℕ)), x2 ≠ x3 → x2 ≠ x4 → x3 ≠ x4 → x2 - x5 ∈ x1 → x3 - x5 ∈ x1 → x4 - x5 ∈ x1 → ∃ (x12 : Fin (13 : ℕ)), ∀ (x13 : Fin (13 : ℕ)), x2 - x13 ∉ x1 → x3 - x13 ∉ x1 → x4 - x13 ∉ x1 → x12 - x13 ∈ x1 := by
  intro x1 x2 x3 x4 x5 h23 h24 h34 h2 h3 h4
  refine ⟨x5 + x5 + x5 + x5 - x2 - x3 - x4, fun x13 g2 g3 g4 => ?_⟩
  have e2 : x2 - x13 = (x2 - x5) - (x13 - x5) := by abel
  have e3 : x3 - x13 = (x3 - x5) - (x13 - x5) := by abel
  have e4 : x4 - x13 = (x4 - x5) - (x13 - x5) := by abel
  have e : x5 + x5 + x5 + x5 - x2 - x3 - x4 - x13 = (0 - (x2 - x5) - (x3 - x5) - (x4 - x5)) - (x13 - x5) := by abel
  rw [e2] at g2
  rw [e3] at g3
  rw [e4] at g4
  rw [e]
  refine PEqualNP.Outside.L_meta_1977_aux.core _ _ _ h2 h3 h4 ?_ ?_ ?_ _ g2 g3 g4
  · intro h; exact h23 (sub_left_injective h)
  · intro h; exact h24 (sub_left_injective h)
  · intro h; exact h34 (sub_left_injective h)
