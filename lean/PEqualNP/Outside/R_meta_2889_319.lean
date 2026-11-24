import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2889_319
    (h1 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 ∧
      x1.size ≤ (12 : ℕ) ∧
      x1.gates.countP (fun g => match g.op with | PEqualNP.CircuitLowerBounds.GateOp.not => true | _ => false) = 0 ∧
      ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (0 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))))
    (h2 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 ∧
      x1.size ≤ (12 : ℕ) ∧
      x1.gates.countP (fun g => match g.op with | PEqualNP.CircuitLowerBounds.GateOp.not => true | _ => false) = 1 ∧
      ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (0 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))))
    (h3 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 ∧
      x1.size ≤ (12 : ℕ) ∧
      2 ≤ x1.gates.countP (fun g => match g.op with | PEqualNP.CircuitLowerBounds.GateOp.not => true | _ => false) ∧
      ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (0 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)))) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (0 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))) := by
  rintro ⟨x1, hfit, hsize, heval⟩
  match hc : x1.gates.countP (fun g => match g.op with | PEqualNP.CircuitLowerBounds.GateOp.not => true | _ => false) with
  | 0 => exact h1 ⟨x1, hfit, hsize, hc, heval⟩
  | 1 => exact h2 ⟨x1, hfit, hsize, hc, heval⟩
  | n + 2 => exact h3 ⟨x1, hfit, hsize, by omega, heval⟩
