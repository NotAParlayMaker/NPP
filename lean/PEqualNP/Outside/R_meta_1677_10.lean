import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def PEqualNP.Outside.R_meta_1677_10.range10SecondGate (C : Circuit) : Prop :=
  ∃ g : Gate, C.gates[1]? = some g ∧
    (g.op = GateOp.and ∧ (g.inputs = [2, 5] ∨ g.inputs = [5, 2]) ∨
     g.op = GateOp.or ∧ (g.inputs = [2, 5] ∨ g.inputs = [5, 2]) ∨
     g.op = GateOp.and ∧ (g.inputs = [2, 6] ∨ g.inputs = [6, 2]) ∨
     g.op = GateOp.or ∧ (g.inputs = [2, 6] ∨ g.inputs = [6, 2]) ∨
     g.op = GateOp.and ∧ (g.inputs = [2, 7] ∨ g.inputs = [7, 2]))

theorem PEqualNP.Outside.R_meta_1677_10
    (range10 : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      C.size ≤ 15 → PEqualNP.Outside.R_meta_1677_10.range10SecondGate C → False)
    (outsideRange10 : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      C.size ≤ 15 → ¬PEqualNP.Outside.R_meta_1677_10.range10SecondGate C → False) :
    ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size := by
  intro C hFan hFirst hCompute
  by_contra hBound
  have hSmall : C.size ≤ 15 := by omega
  by_cases hRange : PEqualNP.Outside.R_meta_1677_10.range10SecondGate C
  · exact (range10 C hFan hFirst hCompute hSmall hRange).elim
  · exact (outsideRange10 C hFan hFirst hCompute hSmall hRange).elim
