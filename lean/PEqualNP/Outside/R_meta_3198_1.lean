import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3198_1

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def twoNot (C : Circuit) : Prop :=
  ∃ i j : Fin C.gates.length,
    i < j ∧ (i : ℕ) = 5 ∧
      (C.gates.get i).op = GateOp.not ∧
      (C.gates.get j).op = GateOp.not ∧
      ∀ k : Fin C.gates.length, (C.gates.get k).op = GateOp.not →
        k = i ∨ k = j

def selector (C : Circuit) : Prop :=
  ∀ x : Fin 9 → Bool,
    (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)

def firstGate (C : Circuit) : Prop :=
  C.gates.head? = some ⟨GateOp.or, [0, 2]⟩ ∨
    C.gates.head? = some ⟨GateOp.or, [2, 0]⟩

def edgeFunction (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
    (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

end PEqualNP.Outside.R_meta_3198_1

theorem PEqualNP.Outside.R_meta_3198_1
    (hFirst : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.Outside.R_meta_3198_1.selector C →
      PEqualNP.Outside.R_meta_3198_1.firstGate C)
    (hSignature : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.Outside.R_meta_3198_1.twoNot C →
      PEqualNP.Outside.R_meta_3198_1.firstGate C →
      (∀ x : Fin 9 → Bool,
        Fintype.card {i : Fin 9 // x i = true} ≤ 2 →
        C.eval (List.ofFn x) = PEqualNP.Outside.R_meta_3198_1.edgeFunction x) →
      16 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.Outside.R_meta_3198_1.twoNot C →
      PEqualNP.Outside.R_meta_3198_1.selector C →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        PEqualNP.Outside.R_meta_3198_1.edgeFunction →
      16 ≤ C.size := by
  intro C hFan hNot hSelector hFun
  have hGate := hFirst C hFan hSelector
  apply hSignature C hFan hNot hGate
  intro x hx
  have hEval := congrFun hFun x
  simpa [PEqualNP.MetaComplexity.circuitFun,
    PEqualNP.Outside.R_meta_3198_1.edgeFunction] using hEval
