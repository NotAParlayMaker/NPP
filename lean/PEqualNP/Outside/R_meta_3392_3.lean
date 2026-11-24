import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3392_3
    (notUnused : ∀ j ∈ ([1, 2, 3, 4, 6] : List (Fin 9)), ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ((∀ g ∈ C.gates, 9 ∉ g.inputs) ∧ C.output ≠ 9) →
      ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x j]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5))
    (orUnused : ∀ j ∈ ([1, 2, 3, 4, 6] : List (Fin 9)), ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ((∀ g ∈ C.gates, 10 ∉ g.inputs) ∧ C.output ≠ 10) →
      ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x j]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5))
    (bothUsed : ∀ j ∈ ([1, 2, 3, 4, 6] : List (Fin 9)), ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
      (((∃ g ∈ C.gates, 9 ∈ g.inputs) ∨ C.output = 9) ∧ ((∃ g ∈ C.gates, 10 ∈ g.inputs) ∨ C.output = 10)) →
      ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x j]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (4 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro j hj C hfan hsize
  by_cases h9 : (∀ g ∈ C.gates, 9 ∉ g.inputs) ∧ C.output ≠ 9
  · exact notUnused j hj C hfan hsize h9
  by_cases h10 : (∀ g ∈ C.gates, 10 ∉ g.inputs) ∧ C.output ≠ 10
  · exact orUnused j hj C hfan hsize h10
  apply bothUsed j hj C hfan hsize
  constructor
  · by_cases ho : C.output = 9
    · exact Or.inr ho
    · left
      by_contra hn
      push_neg at hn
      exact h9 ⟨hn, ho⟩
  · by_cases ho : C.output = 10
    · exact Or.inr ho
    · left
      by_contra hn
      push_neg at hn
      exact h10 ⟨hn, ho⟩
