import PEqualNP.Defs

-- Split the 22 second-AND prefixes into the 19 degenerate, vertex-0, or degree-2 cases
-- and the 3 disjoint degree-3 pairs [1, 2], [1, 5], [1, 8].
theorem PEqualNP.Outside.R_meta_2923_2
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   ∀ x2 ∈ [[], [(0 : Fin 11)], [(0 : Fin 11), (1 : Fin 11)], [(0 : Fin 11), (2 : Fin 11)], [(0 : Fin 11), (4 : Fin 11)], [(0 : Fin 11), (6 : Fin 11)], [(1 : Fin 11)], [(1 : Fin 11), (4 : Fin 11)], [(1 : Fin 11), (6 : Fin 11)], [(1 : Fin 11), (7 : Fin 11)], [(1 : Fin 11), (9 : Fin 11)], [(4 : Fin 11)], [(4 : Fin 11), (6 : Fin 11)], [(4 : Fin 11), (9 : Fin 11)], [(6 : Fin 11)], [(6 : Fin 11), (7 : Fin 11)], [(6 : Fin 11), (9 : Fin 11)], [(9 : Fin 11)], [(10 : Fin 11)]],     PEqualNP.MetaComplexity.FanInTwo x1 →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   ∀ x2 ∈ [[(1 : Fin 11), (2 : Fin 11)], [(1 : Fin 11), (5 : Fin 11)], [(1 : Fin 11), (8 : Fin 11)]],     PEqualNP.MetaComplexity.FanInTwo x1 →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   ∀ x2 ∈ [[], [(0 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (1 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (2 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (2 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(9 : Fin (11 : ℕ))], [(10 : Fin (11 : ℕ))]],     PEqualNP.MetaComplexity.FanInTwo x1 →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  intro C x2 hx2 hFan hFun
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2
  rcases hx2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h2 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h2 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h2 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
  · exact h1 C _ (by decide) hFan hFun
