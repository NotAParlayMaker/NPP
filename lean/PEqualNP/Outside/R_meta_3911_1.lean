import Mathlib
import PEqualNP.Defs

-- Cut by the pair the AND gate reads. Wire 9 is x0 OR x2.
-- pair38: the AND gate reads x3 and x8.
-- low: it reads x1 and one of x3, x4, x6, x8.
-- rest: the other eight pairs.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3911_1
  (pair38 : ∀ x1 ∈ [[(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))]],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
  (low : ∀ x1 ∈ [[(1 : Fin (11 : ℕ)), (3 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))]],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
  (rest : ∀ x1 ∈ [[(3 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))]],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
  :
  ∀ x1 ∈ [[(1 : Fin (11 : ℕ)), (3 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))]],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];           x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact low _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact low _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact low _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact low _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact rest _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact rest _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact rest _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact rest _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact pair38 _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact rest _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact rest _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact rest _ (by decide)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact rest _ (by decide)
  exact absurd hx List.not_mem_nil
