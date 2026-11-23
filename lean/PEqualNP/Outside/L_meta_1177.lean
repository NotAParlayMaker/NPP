import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1177

open PEqualNP.CircuitLowerBounds

def graphCircuit : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [1, 2]⟩
      , ⟨GateOp.or, [8, 3]⟩
      , ⟨GateOp.or, [9, 4]⟩
      , ⟨GateOp.and, [0, 10]⟩
      , ⟨GateOp.or, [5, 6]⟩
      , ⟨GateOp.and, [1, 12]⟩
      , ⟨GateOp.and, [5, 7]⟩
      , ⟨GateOp.or, [11, 13]⟩
      , ⟨GateOp.or, [15, 14]⟩ ]
    output := 16 }

theorem graphCircuitEval :
    ∀ a b c d e f g h : Bool,
      graphCircuit.eval [a, b, c, d, e, f, g, h] =
        ((a && b) || (a && c) || (a && d) || (a && e) ||
          (b && f) || (b && g) || (f && h)) := by
  decide

end PEqualNP.Outside.L_meta_1177

theorem PEqualNP.Outside.L_meta_1177 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1177.graphCircuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1177.graphCircuit]
  · decide
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [inputs]
    exact PEqualNP.Outside.L_meta_1177.graphCircuitEval
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
