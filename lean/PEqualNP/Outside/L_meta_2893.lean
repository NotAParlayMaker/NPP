import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2893 : ∀ (x1 : Fin (8 : ℕ)),   ∃ (x2 : Fin (8 : ℕ) → Fin (8 : ℕ)),     (x2 x1 = (0 : Fin (8 : ℕ)) ∨ x2 x1 = (1 : Fin (8 : ℕ))) ∧       ∀ (x3 : Fin (8 : ℕ) → Bool),         (have x4 : Fin (9 : ℕ) → Bool := Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false (x3 ∘ x2);           x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) =           have x4 : Fin (8 : ℕ) → Bool := x3;           x4 (0 : Fin (8 : ℕ)) && x4 (1 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (2 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (3 : Fin (8 : ℕ)) || x4 (0 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (5 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (3 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (4 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (5 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (7 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) := by
  intro x1
  fin_cases x1
  all_goals first
    | refine ⟨![1,0,4,7,5,2,6,3], by decide, ?_⟩
    | refine ⟨![4,0,1,2,6,7,5,3], by decide, ?_⟩
    | refine ⟨![4,6,2,1,0,7,3,5], by decide, ?_⟩
    | refine ⟨![2,6,4,7,3,1,0,5], by decide, ?_⟩
    | refine ⟨![2,3,7,4,6,1,5,0], by decide, ?_⟩
  all_goals
    intro x3
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
        x3 = ![b0, b1, b2, b3, b4, b5, b6, b7] :=
      ⟨x3 0, x3 1, x3 2, x3 3, x3 4, x3 5, x3 6, x3 7, by funext i; fin_cases i <;> rfl⟩
    revert b0 b1 b2 b3 b4 b5 b6 b7
    decide
