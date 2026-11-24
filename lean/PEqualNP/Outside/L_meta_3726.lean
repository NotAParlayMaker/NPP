import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3726

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.Core

def C0 : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [2, 3] },
      { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [4, 8] },
      { op := GateOp.or, inputs := [5, 9] }, { op := GateOp.and, inputs := [6, 10] }],
    output := 11 }

def edges : List (Fin 6 × Fin 6) :=
  [(0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5)]

def bad2 : List (Fin 6 × Fin 6) :=
  [(1, 2), (1, 3)]

def mkIn (b0 b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5

lemma mkIn_eq (x : Fin 6 → Bool) :
    mkIn (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) = x := by
  funext i
  fin_cases i <;> rfl

lemma h_ao2 : IsAO2 6 C0 := by decide +kernel

lemma h_size : C0.size = 6 := rfl

set_option maxRecDepth 100000 in
lemma h_eval_bool : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    circuitFun 6 C0 (mkIn b0 b1 b2 b3 b4 b5) =
      decide (∃ e ∈ edges, mkIn b0 b1 b2 b3 b4 b5 e.1 = true ∧
        mkIn b0 b1 b2 b3 b4 b5 e.2 = true) := by
  decide +kernel

lemma h_eval (x : Fin 6 → Bool) :
    circuitFun 6 C0 x = decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true) := by
  have h := h_eval_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  rwa [mkIn_eq] at h

set_option maxRecDepth 100000 in
lemma h_read : ∀ e ∈ edges, ReadTwiceAt 6 C0 (C0.output - 6) e.1 e.2 ↔ e ∈ bad2 := by
  decide +kernel

end PEqualNP.Outside.L_meta_3726

theorem PEqualNP.Outside.L_meta_3726 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 10] }], output := 11 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 6 C ∧ C.size = 6 ∧
  (∀ x : Fin 6 → Bool, PEqualNP.MetaComplexity.circuitFun 6 C x = decide (∃ e ∈ ([(0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5)] : List (Fin 6 × Fin 6)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5)] : List (Fin 6 × Fin 6)), PEqualNP.Core.ReadTwiceAt 6 C (C.output - 6) e.1 e.2 ↔ e ∈ ([(1, 2), (1, 3)] : List (Fin 6 × Fin 6))) := by
  rintro C rfl
  exact ⟨PEqualNP.Outside.L_meta_3726.h_ao2, PEqualNP.Outside.L_meta_3726.h_size,
    PEqualNP.Outside.L_meta_3726.h_eval, PEqualNP.Outside.L_meta_3726.h_read⟩
