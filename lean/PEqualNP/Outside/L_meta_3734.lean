import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3734

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.Core

def C0 : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.or, inputs := [0, 7] }, { op := GateOp.and, inputs := [3, 7] },
      { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [4, 11] },
      { op := GateOp.and, inputs := [9, 12] }],
    output := 13 }

def edges : List (Fin 7 × Fin 7) :=
  [(0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)]

def bad2 : List (Fin 7 × Fin 7) :=
  [(1, 3), (2, 3)]

def mkIn (b0 b1 b2 b3 b4 b5 b6 : Bool) : Fin 7 → Bool
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6

lemma mkIn_eq (x : Fin 7 → Bool) :
    mkIn (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) = x := by
  funext i
  fin_cases i <;> rfl

lemma h_ao2 : IsAO2 7 C0 := by decide +kernel

lemma h_size : C0.size = 7 := rfl

set_option maxRecDepth 100000 in
lemma h_eval_bool : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    circuitFun 7 C0 (mkIn b0 b1 b2 b3 b4 b5 b6) =
      decide (∃ e ∈ edges, mkIn b0 b1 b2 b3 b4 b5 b6 e.1 = true ∧
        mkIn b0 b1 b2 b3 b4 b5 b6 e.2 = true) := by
  decide +kernel

lemma h_eval (x : Fin 7 → Bool) :
    circuitFun 7 C0 x = decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true) := by
  have h := h_eval_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  rwa [mkIn_eq] at h

set_option maxRecDepth 100000 in
lemma h_read : ∀ e ∈ edges, ReadTwiceAt 7 C0 (C0.output - 7) e.1 e.2 ↔ e ∈ bad2 := by
  decide +kernel

end PEqualNP.Outside.L_meta_3734

theorem PEqualNP.Outside.L_meta_3734 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 7 C ∧ C.size = 7 ∧
  (∀ x : Fin 7 → Bool, PEqualNP.MetaComplexity.circuitFun 7 C x = decide (∃ e ∈ ([(0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), PEqualNP.Core.ReadTwiceAt 7 C (C.output - 7) e.1 e.2 ↔ e ∈ ([(1, 3), (2, 3)] : List (Fin 7 × Fin 7))) := by
  rintro C rfl
  exact ⟨PEqualNP.Outside.L_meta_3734.h_ao2, PEqualNP.Outside.L_meta_3734.h_size,
    PEqualNP.Outside.L_meta_3734.h_eval, PEqualNP.Outside.L_meta_3734.h_read⟩
