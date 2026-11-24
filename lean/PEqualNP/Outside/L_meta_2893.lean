import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_2893 : ∀ (x1 : Fin (8 : ℕ)),   ∃ (x2 : Fin (8 : ℕ) → Fin (8 : ℕ)),     (x2 x1 = (0 : Fin (8 : ℕ)) ∨ x2 x1 = (1 : Fin (8 : ℕ))) ∧       ∀ (x3 : Fin (8 : ℕ) → Bool),         (have x4 : Fin (9 : ℕ) → Bool := Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false (x3 ∘ x2);           x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) =           have x4 : Fin (8 : ℕ) → Bool := x3;           x4 (0 : Fin (8 : ℕ)) && x4 (1 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (2 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (3 : Fin (8 : ℕ)) || x4 (0 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (5 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (3 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (4 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (5 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (7 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) := by
  intro x1
  fin_cases x1
  · exact ⟨![1, 0, 4, 7, 5, 2, 6, 3], by decide, by decide⟩
  · exact ⟨![1, 0, 4, 7, 5, 2, 6, 3], by decide, by decide⟩
  · exact ⟨![4, 0, 1, 2, 6, 7, 5, 3], by decide, by decide⟩
  · exact ⟨![4, 6, 2, 1, 0, 7, 3, 5], by decide, by decide⟩
  · exact ⟨![1, 5, 7, 4, 0, 2, 3, 6], by decide, by decide⟩
  · exact ⟨![2, 3, 7, 4, 6, 1, 5, 0], by decide, by decide⟩
  · exact ⟨![2, 6, 4, 7, 3, 1, 0, 5], by decide, by decide⟩
  · exact ⟨![2, 3, 7, 4, 6, 1, 5, 0], by decide, by decide⟩
