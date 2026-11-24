import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1674_67
    (exclude : ∀ C : Circuit, FanInTwo C → C.size ≤ 15 → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → ¬(∃ (pre post : List Gate) (g : Gate) (a b : Fin 9) (op : GateOp),
      C.gates = pre ++ g :: post ∧
      ((op = .and ∧ a ≠ b) ∨ (op = .or ∧ (10 * min a.val b.val + max a.val b.val) ∈ ([1,12,23,34,4,5,16,27,38,57,68,58] : List Nat))) ∧
      ∀ x : Fin 9 → Bool, let w := (Circuit.mk pre 0).wires (List.ofFn x);
        g.op.eval (g.inputs.map fun i => w.getD i false) = op.eval [x a,x b]))
    (remaining : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      C.size ≤ 15 → (¬(∃ (pre post : List Gate) (g : Gate) (a b : Fin 9) (op : GateOp),
      C.gates = pre ++ g :: post ∧
      ((op = .and ∧ a ≠ b) ∨ (op = .or ∧ (10 * min a.val b.val + max a.val b.val) ∈ ([1,12,23,34,4,5,16,27,38,57,68,58] : List Nat))) ∧
      ∀ x : Fin 9 → Bool, let w := (Circuit.mk pre 0).wires (List.ofFn x);
        g.op.eval (g.inputs.map fun i => w.getD i false) = op.eval [x a,x b])) → circuitFun 9 C ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hf head correct
  by_contra! small
  have cap : C.size ≤ 15 := by omega
  exact remaining C hf head cap (exclude C hf cap correct) correct
