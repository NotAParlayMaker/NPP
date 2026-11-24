import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1296 : (∀ p p2 l l2 : Fin 7, p ≠ p2 → l ≠ l2 → ¬ (((p.val + 7 - l.val) % 7 = 0 ∨ (p.val + 7 - l.val) % 7 = 1 ∨ (p.val + 7 - l.val) % 7 = 3) ∧ ((p.val + 7 - l2.val) % 7 = 0 ∨ (p.val + 7 - l2.val) % 7 = 1 ∨ (p.val + 7 - l2.val) % 7 = 3) ∧ ((p2.val + 7 - l.val) % 7 = 0 ∨ (p2.val + 7 - l.val) % 7 = 1 ∨ (p2.val + 7 - l.val) % 7 = 3) ∧ ((p2.val + 7 - l2.val) % 7 = 0 ∨ (p2.val + 7 - l2.val) % 7 = 1 ∨ (p2.val + 7 - l2.val) % 7 = 3))) ∧ (∀ l : Fin 7, (Finset.univ.filter (fun p : Fin 7 => ((p.val + 7 - l.val) % 7 = 0 ∨ (p.val + 7 - l.val) % 7 = 1 ∨ (p.val + 7 - l.val) % 7 = 3))).card = 3) ∧ (∀ p : Fin 7, (Finset.univ.filter (fun l : Fin 7 => ((p.val + 7 - l.val) % 7 = 0 ∨ (p.val + 7 - l.val) % 7 = 1 ∨ (p.val + 7 - l.val) % 7 = 3))).card = 3) := by
  decide +kernel
