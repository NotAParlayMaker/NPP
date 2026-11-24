import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1932_1
    (h0 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool),
        have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];
        C.eval (x7 ++ [Bool.false]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h1 : ∀ (a : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool),
        have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];
        C.eval (x7 ++ [x7.getD a Bool.false]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (a : ℕ) (b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool),
        have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];
        C.eval (x7 ++ [x7.getD a Bool.false || x7.getD b Bool.false]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx C hm hsize
  cases x1 with
  | nil =>
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h0 C hm hsize
  | cons a t =>
      cases t with
      | nil =>
          simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h1 a C hm hsize
      | cons b t =>
          cases t with
          | nil =>
              simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h2 a b C hm hsize
          | cons c t =>
              simp at hx
