import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3837_1
    (copyCase : ∀ (C : Circuit), FanInTwo C → C.size = 13 →
      ∀ (s : Fin 11) (b : Bool), b = false → s.val < 10 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 6]
        C.eval (w ++ [b != w.getD s false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5))
    (notCase : ∀ (C : Circuit), FanInTwo C → C.size = 13 →
      ∀ (s : Fin 11) (b : Bool), (b = true ∨ s.val = 10) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 || x 6]
        C.eval (w ++ [b != w.getD s false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → ∀ (x6 : Fin (11 : ℕ)) (x7 : Bool), ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval (x2 x8 ++ [x7 != (x2 x8).getD (↑x6) Bool.false]) ≠ x1 x8 := by
  dsimp only
  intro C hfan hsize s b
  by_cases h : b = false ∧ s.val < 10
  · exact copyCase C hfan hsize s b h.1 h.2
  · apply notCase C hfan hsize s b
    by_cases hb : b = false
    · right
      have : ¬ s.val < 10 := fun hs => h ⟨hb, hs⟩
      have := s.isLt
      omega
    · left
      simpa using hb
