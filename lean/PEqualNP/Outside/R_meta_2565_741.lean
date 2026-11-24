import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2565_741
    (hElim : ∀ C : Circuit, FanInTwo C →
      (∃ g ∈ C.gates, g.op = GateOp.and ∧ 9 ∈ g.inputs) →
      C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0)) ++ [false]) = false →
      C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0 ∨ i = 4)) ++ [false]) = true →
      C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0 ∨ i = 1)) ++ [false]) = true →
      C.eval (List.ofFn (fun _ : Fin 9 => false) ++ [false]) = false →
      HasCircuitSize 8
        (fun x => C.eval (List.ofFn (Fin.insertNth (4 : Fin 9) false x) ++ [false]))
        (C.size - 2))
    (hIdentity : ∀ x : Fin 8 → Bool,
        (fun (x4 : Fin 9 → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) (Fin.insertNth (4 : Fin 9) false x) =
        (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (9 : ℕ) ∈ x3.inputs) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) (x1.size - (2 : ℕ)) := by
  intro C hFan hAnd hEval
  have hs : C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0)) ++ [false]) = false := by
    simpa (config := { decide := true }) using hEval (fun i => decide (i = 0))
  have h04 : C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0 ∨ i = 4)) ++ [false]) = true := by
    simpa (config := { decide := true }) using hEval (fun i => decide (i = 0 ∨ i = 4))
  have h01 : C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0 ∨ i = 1)) ++ [false]) = true := by
    simpa (config := { decide := true }) using hEval (fun i => decide (i = 0 ∨ i = 1))
  have hz : C.eval (List.ofFn (fun _ : Fin 9 => false) ++ [false]) = false := by
    simpa using hEval (fun _ => false)
  obtain ⟨D, hDf, hDs, hDe⟩ := hElim C hFan hAnd hs h04 h01 hz
  refine ⟨D, hDf, hDs, fun x => ?_⟩
  let y : Fin 9 → Bool := Fin.insertNth (4 : Fin 9) false x
  refine Eq.trans (hDe x) (Eq.trans ?_ (hIdentity x))
  change C.eval (List.ofFn y ++ [false]) = _
  exact hEval y
