import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17140 : ∀ (x1 x2 : Fin (13 : ℕ)), x1 - x2 = (0 : Fin (13 : ℕ)) ∨ x1 - x2 = (1 : Fin (13 : ℕ)) ∨ x1 - x2 = (3 : Fin (13 : ℕ)) ∨ x1 - x2 = (9 : Fin (13 : ℕ)) ↔ x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 := by
  unfold PEqualNP.HeptadCover.singerLines3
  decide
