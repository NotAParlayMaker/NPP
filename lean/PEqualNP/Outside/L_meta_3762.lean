import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3762_aux

def G0 : SimpleGraph (Fin 7) where
  Adj u v := (u, v) ∈ ([(0, 4), (0, 5), (0, 6), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)) ∨ (v, u) ∈ ([(0, 4), (0, 5), (0, 6), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7))
  symm := ⟨fun u v h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G0.Adj := fun u v => by unfold G0; infer_instance

end PEqualNP.Outside.L_meta_3762_aux

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_3762 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 16] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 7 C ∧ C.size = 11 ∧
  (∀ x : Fin 7 → Bool, PEqualNP.MetaComplexity.circuitFun 7 C x = decide (∃ e ∈ ([(0, 4), (0, 5), (0, 6), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 4), (0, 5), (0, 6), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)), PEqualNP.Core.ReadTwiceAt 7 C (C.output - 7) e.1 e.2 ↔ e ∈ ([(0, 4), (0, 5), (0, 6), (2, 5), (3, 6)] : List (Fin 7 × Fin 7))) ∧
  (∀ (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj], (∀ u v : Fin 7, G.Adj u v ↔ ((u, v) ∈ ([(0, 4), (0, 5), (0, 6), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)) ∨ (v, u) ∈ ([(0, 4), (0, 5), (0, 6), (1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)))) →
    PEqualNP.Core.IsLiftFixedPoint G C) ∧
  PEqualNP.CleanedNonEdge.OrToOutput 7 C 9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C 9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C 8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C 4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
  PEqualNP.CleanedNonEdge.OrReaches 7 C (PEqualNP.TopForm.opnd C 9 1) 8 ∧ PEqualNP.CleanedNonEdge.OrReaches 7 C (PEqualNP.TopForm.opnd C 8 1) 4 ∧
  ∀ i : Fin 2, (C.wires (List.ofFn (fun z : Fin 7 => decide (z = 0 ∨ z = 4)))).getD (PEqualNP.TopForm.opnd C 4 i) false = true ∧ (C.wires (List.ofFn (fun z : Fin 7 => decide (z = 4)))).getD (PEqualNP.TopForm.opnd C 4 i) false = false := by
  intro C hC
  subst hC
  refine ⟨by decide, rfl, by decide, by decide, ?_, by decide, rfl, rfl, rfl, by decide, by decide, by decide⟩
  have h : PEqualNP.Core.IsLiftFixedPoint PEqualNP.Outside.L_meta_3762_aux.G0 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 16] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) := by decide
  intro G inst hG
  have hE : G = PEqualNP.Outside.L_meta_3762_aux.G0 := by
    ext u v
    exact hG u v
  subst hE
  convert h
