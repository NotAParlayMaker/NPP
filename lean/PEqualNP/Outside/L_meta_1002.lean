import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1002_aux

private def circ13 : PEqualNP.CircuitLowerBounds.Circuit where
  gates := [
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 17]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩
  ]
  output := 20

private theorem circ13_fanInTwo : PEqualNP.MetaComplexity.FanInTwo circ13 := by
  intro g hg
  simp only [circ13, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

private theorem circ13_eval (x : Fin 8 → Bool) :
    circ13.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)) := by
  have hx : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      circ13.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
        ((b0 && b1) || (b1 && b2) || (b2 && b3) || (b0 && b4) ||
         (b1 && b5) || (b2 && b6) || (b3 && b7) || (b4 && b6) ||
         (b5 && b7) || (b7 && b4)) := by
    decide
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    simp [List.ofFn_succ]
  rw [hl]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

theorem witness :
    PEqualNP.MetaComplexity.HasCircuitSize 8
      (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
        (x 5 && x 7) || (x 7 && x 4)) 13 :=
  ⟨circ13, circ13_fanInTwo, le_rfl, circ13_eval⟩

end PEqualNP.Outside.L_meta_1002_aux

theorem PEqualNP.Outside.L_meta_1002 : ¬ (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13) :=
  fun h => h PEqualNP.Outside.L_meta_1002_aux.witness
