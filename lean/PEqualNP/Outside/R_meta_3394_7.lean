import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3394_7
    (h1 :
      ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)),
        (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))],
        ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo x3 →
            x3.size - PEqualNP.NotBracket.notCount x3 ≤ (12 : ℕ) →
              ∃ (x6 : Fin (9 : ℕ) → Bool),
                x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++
                  [x6 (6 : Fin (9 : ℕ)) || x6 x1]) ≠
                  (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
                    x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
                    x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
                    x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
                    x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
                    x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
                    x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
                    x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                    x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                    x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                    x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                    x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h2 :
      ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))],
        ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 x3 →
            x3.size ≤ (13 : ℕ) →
              ∃ (x6 : Fin (9 : ℕ) → Bool),
                x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++
                  [x6 (6 : Fin (9 : ℕ)) || x6 x1]) ≠
                  (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
                    x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
                    x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
                    x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
                    x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
                    x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
                    x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
                    x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                    x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                    x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                    x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                    x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h3 :
      ∀ x1 ∈ [(2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))],
        ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 x3 →
            x3.size ≤ (13 : ℕ) →
              ∃ (x6 : Fin (9 : ℕ) → Bool),
                x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++
                  [x6 (6 : Fin (9 : ℕ)) || x6 x1]) ≠
                  (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
                    x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
                    x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
                    x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
                    x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
                    x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
                    x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
                    x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                    x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                    x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                    x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                    x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)),
      (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))],
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
          x3.size ≤ (13 : ℕ) →
            ∃ (x6 : Fin (9 : ℕ) → Bool),
              x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++
                [x6 (6 : Fin (9 : ℕ)) || x6 x1]) ≠
                (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) ||
                  x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) ||
                  x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) ||
                  x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) ||
                  x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) ||
                  x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) ||
                  x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 x3 hfan hsize
  by_cases hnot : PEqualNP.NotBracket.notCount x3 = 0
  · have hmono : PEqualNP.MetaComplexity.Monotone2 x3 := by
      intro g hg
      have hnil := List.length_eq_zero_iff.mp hnot
      have hne : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
        have hfalse := (List.filter_eq_nil_iff.mp hnil) g hg
        intro heq
        exact hfalse (by simp [heq])
      obtain ⟨hop, hlen⟩ := hfan g hg
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hne h)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx1
    rcases hx1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h2 (1 : Fin 9) (by simp) x3 hmono hsize
    · exact h3 (2 : Fin 9) (by simp) x3 hmono hsize
    · exact h3 (3 : Fin 9) (by simp) x3 hmono hsize
    · exact h3 (5 : Fin 9) (by simp) x3 hmono hsize
    · exact h2 (6 : Fin 9) (by simp) x3 hmono hsize
    · exact h3 (7 : Fin 9) (by simp) x3 hmono hsize
    · exact h2 (8 : Fin 9) (by simp) x3 hmono hsize
  · exact h1 x1 hx1 x3 hfan (by omega)
