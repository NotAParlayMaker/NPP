import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1303 : (∀ p p2 l l2 : Fin 9, p ≠ p2 → l ≠ l2 → ¬ ((p.val % 3 = ((l.val / 3) * (p.val / 3) + l.val % 3) % 3) ∧ (p.val % 3 = ((l2.val / 3) * (p.val / 3) + l2.val % 3) % 3) ∧ (p2.val % 3 = ((l.val / 3) * (p2.val / 3) + l.val % 3) % 3) ∧ (p2.val % 3 = ((l2.val / 3) * (p2.val / 3) + l2.val % 3) % 3))) ∧ (∀ l : Fin 9, (Finset.univ.filter (fun p : Fin 9 => (p.val % 3 = ((l.val / 3) * (p.val / 3) + l.val % 3) % 3))).card = 3) ∧ (∀ p : Fin 9, (Finset.univ.filter (fun l : Fin 9 => (p.val % 3 = ((l.val / 3) * (p.val / 3) + l.val % 3) % 3))).card = 3) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
