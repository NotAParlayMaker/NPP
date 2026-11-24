import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2923_1
  (h1 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x2 ∈ [[], [(0 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (1 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (2 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ))]], PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x5 : Fin (9 : ℕ) → Bool), have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]; x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size)
  (h2 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x2 ∈ [[(1 : Fin (11 : ℕ)), (2 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))]], PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x5 : Fin (9 : ℕ) → Bool), have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]; x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size)
  (h3 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x2 ∈ [[(4 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(9 : Fin (11 : ℕ))], [(10 : Fin (11 : ℕ))]], PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x5 : Fin (9 : ℕ) → Bool), have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]; x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x2 ∈ [[], [(0 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (1 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (2 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(0 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (2 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))], [(1 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))], [(4 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))], [(6 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))], [(9 : Fin (11 : ℕ))], [(10 : Fin (11 : ℕ))]], PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x5 : Fin (9 : ℕ) → Bool), have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]; x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro x1 x2 hx2 hfan heval
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2
  rcases hx2 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact h1 x1 x2 (by simp [h]) hfan heval
  · exact h1 x1 x2 (by simp [h]) hfan heval
  · exact h1 x1 x2 (by simp [h]) hfan heval
  · exact h1 x1 x2 (by simp [h]) hfan heval
  · exact h1 x1 x2 (by simp [h]) hfan heval
  · exact h1 x1 x2 (by simp [h]) hfan heval
  · exact h1 x1 x2 (by simp [h]) hfan heval
  · exact h2 x1 x2 (by simp [h]) hfan heval
  · exact h2 x1 x2 (by simp [h]) hfan heval
  · exact h2 x1 x2 (by simp [h]) hfan heval
  · exact h2 x1 x2 (by simp [h]) hfan heval
  · exact h2 x1 x2 (by simp [h]) hfan heval
  · exact h2 x1 x2 (by simp [h]) hfan heval
  · exact h2 x1 x2 (by simp [h]) hfan heval
  · exact h3 x1 x2 (by simp [h]) hfan heval
  · exact h3 x1 x2 (by simp [h]) hfan heval
  · exact h3 x1 x2 (by simp [h]) hfan heval
  · exact h3 x1 x2 (by simp [h]) hfan heval
  · exact h3 x1 x2 (by simp [h]) hfan heval
  · exact h3 x1 x2 (by simp [h]) hfan heval
  · exact h3 x1 x2 (by simp [h]) hfan heval
  · exact h3 x1 x2 (by simp [h]) hfan heval
