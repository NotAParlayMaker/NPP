import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3752.Proof

open PEqualNP.CircuitLowerBounds

def step (values : List Bool) (g : Gate) : List Bool :=
  values ++ [g.op.eval (g.inputs.map fun i => values.getD i false)]

theorem evalAnd (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem evalOr (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
  cases a <;> cases b <;> rfl

end PEqualNP.Outside.L_meta_3752.Proof

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3752.Proof in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_3752 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [46, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [51, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 52] }], output := 53 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 40 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  intro C hC
  subst C
  refine ⟨?_, rfl, ?_, ?_⟩
  · decide +kernel
  · intro x
    have hInput : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := rfl
    let w14 := GateOp.or.eval [x 0, x 1]
    have h14 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] ⟨.or, [0, 1]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14] := rfl
    let w15 := GateOp.or.eval [w14, x 3]
    have h15 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14] ⟨.or, [14, 3]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15] := rfl
    let w16 := GateOp.or.eval [x 7, x 8]
    have h16 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15] ⟨.or, [7, 8]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16] := rfl
    let w17 := GateOp.or.eval [w16, x 10]
    have h17 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16] ⟨.or, [16, 10]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17] := rfl
    let w18 := GateOp.and.eval [w15, w17]
    have h18 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17] ⟨.and, [15, 17]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18] := rfl
    let w19 := GateOp.and.eval [x 5, x 10]
    have h19 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18] ⟨.and, [5, 10]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19] := rfl
    let w20 := GateOp.or.eval [w18, w19]
    have h20 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19] ⟨.or, [18, 19]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20] := rfl
    let w21 := GateOp.or.eval [x 0, x 10]
    have h21 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20] ⟨.or, [0, 10]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21] := rfl
    let w22 := GateOp.or.eval [x 1, x 3]
    have h22 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21] ⟨.or, [1, 3]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22] := rfl
    let w23 := GateOp.or.eval [w22, x 5]
    have h23 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22] ⟨.or, [22, 5]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23] := rfl
    let w24 := GateOp.or.eval [w23, x 7]
    have h24 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23] ⟨.or, [23, 7]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24] := rfl
    let w25 := GateOp.and.eval [w21, w24]
    have h25 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24] ⟨.and, [21, 24]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25] := rfl
    let w26 := GateOp.and.eval [w20, w25]
    have h26 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25] ⟨.and, [20, 25]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26] := rfl
    let w27 := GateOp.and.eval [x 4, x 8]
    have h27 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26] ⟨.and, [4, 8]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27] := rfl
    let w28 := GateOp.or.eval [w18, w27]
    have h28 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27] ⟨.or, [18, 27]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28] := rfl
    let w29 := GateOp.or.eval [x 1, x 8]
    have h29 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28] ⟨.or, [1, 8]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29] := rfl
    let w30 := GateOp.or.eval [x 0, x 3]
    have h30 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29] ⟨.or, [0, 3]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] := rfl
    let w31 := GateOp.or.eval [w30, x 4]
    have h31 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] ⟨.or, [30, 4]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31] := rfl
    let w32 := GateOp.or.eval [w31, x 7]
    have h32 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31] ⟨.or, [31, 7]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32] := rfl
    let w33 := GateOp.and.eval [w29, w32]
    have h33 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32] ⟨.and, [29, 32]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33] := rfl
    let w34 := GateOp.and.eval [w28, w33]
    have h34 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33] ⟨.and, [28, 33]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34] := rfl
    let w35 := GateOp.or.eval [w26, w34]
    have h35 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34] ⟨.or, [26, 34]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35] := rfl
    let w36 := GateOp.and.eval [x 7, x 2]
    have h36 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35] ⟨.and, [7, 2]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36] := rfl
    let w37 := GateOp.or.eval [w35, w36]
    have h37 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36] ⟨.or, [35, 36]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37] := rfl
    let w38 := GateOp.or.eval [x 0, x 5]
    have h38 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37] ⟨.or, [0, 5]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38] := rfl
    let w39 := GateOp.or.eval [w38, x 6]
    have h39 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38] ⟨.or, [38, 6]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39] := rfl
    let w40 := GateOp.and.eval [w39, x 9]
    have h40 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39] ⟨.and, [39, 9]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40] := rfl
    let w41 := GateOp.or.eval [w37, w40]
    have h41 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40] ⟨.or, [37, 40]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41] := rfl
    let w42 := GateOp.or.eval [x 1, x 4]
    have h42 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41] ⟨.or, [1, 4]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42] := rfl
    let w43 := GateOp.or.eval [w42, x 6]
    have h43 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42] ⟨.or, [42, 6]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43] := rfl
    let w44 := GateOp.and.eval [w43, x 11]
    have h44 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43] ⟨.and, [43, 11]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44] := rfl
    let w45 := GateOp.or.eval [w41, w44]
    have h45 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44] ⟨.or, [41, 44]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45] := rfl
    let w46 := GateOp.or.eval [x 2, x 3]
    have h46 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45] ⟨.or, [2, 3]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46] := rfl
    let w47 := GateOp.or.eval [w46, x 6]
    have h47 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46] ⟨.or, [46, 6]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47] := rfl
    let w48 := GateOp.and.eval [w47, x 12]
    have h48 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47] ⟨.and, [47, 12]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48] := rfl
    let w49 := GateOp.or.eval [w45, w48]
    have h49 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48] ⟨.or, [45, 48]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49] := rfl
    let w50 := GateOp.or.eval [x 2, x 4]
    have h50 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49] ⟨.or, [2, 4]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50] := rfl
    let w51 := GateOp.or.eval [w50, x 5]
    have h51 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50] ⟨.or, [50, 5]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51] := rfl
    let w52 := GateOp.and.eval [w51, x 13]
    have h52 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51] ⟨.and, [51, 13]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52] := rfl
    let w53 := GateOp.or.eval [w49, w52]
    have h53 : step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52] ⟨.or, [49, 52]⟩ = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53] := rfl
    change (([⟨.or, [0, 1]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [16, 10]⟩, ⟨.and, [15, 17]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [22, 5]⟩, ⟨.or, [23, 7]⟩, ⟨.and, [21, 24]⟩, ⟨.and, [20, 25]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [18, 27]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [30, 4]⟩, ⟨.or, [31, 7]⟩, ⟨.and, [29, 32]⟩, ⟨.and, [28, 33]⟩, ⟨.or, [26, 34]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [38, 6]⟩, ⟨.and, [39, 9]⟩, ⟨.or, [37, 40]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [42, 6]⟩, ⟨.and, [43, 11]⟩, ⟨.or, [41, 44]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [46, 6]⟩, ⟨.and, [47, 12]⟩, ⟨.or, [45, 48]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [50, 5]⟩, ⟨.and, [51, 13]⟩, ⟨.or, [49, 52]⟩] : List Gate).foldl step (List.ofFn x)).getD 53 false = _
    rw [hInput]
    rw [List.foldl_cons, h14]
    rw [List.foldl_cons, h15]
    rw [List.foldl_cons, h16]
    rw [List.foldl_cons, h17]
    rw [List.foldl_cons, h18]
    rw [List.foldl_cons, h19]
    rw [List.foldl_cons, h20]
    rw [List.foldl_cons, h21]
    rw [List.foldl_cons, h22]
    rw [List.foldl_cons, h23]
    rw [List.foldl_cons, h24]
    rw [List.foldl_cons, h25]
    rw [List.foldl_cons, h26]
    rw [List.foldl_cons, h27]
    rw [List.foldl_cons, h28]
    rw [List.foldl_cons, h29]
    rw [List.foldl_cons, h30]
    rw [List.foldl_cons, h31]
    rw [List.foldl_cons, h32]
    rw [List.foldl_cons, h33]
    rw [List.foldl_cons, h34]
    rw [List.foldl_cons, h35]
    rw [List.foldl_cons, h36]
    rw [List.foldl_cons, h37]
    rw [List.foldl_cons, h38]
    rw [List.foldl_cons, h39]
    rw [List.foldl_cons, h40]
    rw [List.foldl_cons, h41]
    rw [List.foldl_cons, h42]
    rw [List.foldl_cons, h43]
    rw [List.foldl_cons, h44]
    rw [List.foldl_cons, h45]
    rw [List.foldl_cons, h46]
    rw [List.foldl_cons, h47]
    rw [List.foldl_cons, h48]
    rw [List.foldl_cons, h49]
    rw [List.foldl_cons, h50]
    rw [List.foldl_cons, h51]
    rw [List.foldl_cons, h52]
    rw [List.foldl_cons, h53]
    rw [List.foldl_nil]
    change (GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(GateOp.and.eval [(GateOp.or.eval [(GateOp.and.eval [(GateOp.or.eval [(GateOp.or.eval [(x 0), (x 1)]), (x 3)]), (GateOp.or.eval [(GateOp.or.eval [(x 7), (x 8)]), (x 10)])]), (GateOp.and.eval [(x 5), (x 10)])]), (GateOp.and.eval [(GateOp.or.eval [(x 0), (x 10)]), (GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(x 1), (x 3)]), (x 5)]), (x 7)])])]), (GateOp.and.eval [(GateOp.or.eval [(GateOp.and.eval [(GateOp.or.eval [(GateOp.or.eval [(x 0), (x 1)]), (x 3)]), (GateOp.or.eval [(GateOp.or.eval [(x 7), (x 8)]), (x 10)])]), (GateOp.and.eval [(x 4), (x 8)])]), (GateOp.and.eval [(GateOp.or.eval [(x 1), (x 8)]), (GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(x 0), (x 3)]), (x 4)]), (x 7)])])])]), (GateOp.and.eval [(x 7), (x 2)])]), (GateOp.and.eval [(GateOp.or.eval [(GateOp.or.eval [(x 0), (x 5)]), (x 6)]), (x 9)])]), (GateOp.and.eval [(GateOp.or.eval [(GateOp.or.eval [(x 1), (x 4)]), (x 6)]), (x 11)])]), (GateOp.and.eval [(GateOp.or.eval [(GateOp.or.eval [(x 2), (x 3)]), (x 6)]), (x 12)])]), (GateOp.and.eval [(GateOp.or.eval [(GateOp.or.eval [(x 2), (x 4)]), (x 5)]), (x 13)])]) = _
    simp only [evalAnd, evalOr, List.exists_mem_cons_iff, List.not_mem_nil, false_and,
      exists_false, or_false, Bool.decide_or, Bool.decide_and, Bool.decide_eq_true]
    generalize x 0 = p0
    generalize x 1 = p1
    generalize x 2 = p2
    generalize x 3 = p3
    generalize x 4 = p4
    generalize x 5 = p5
    generalize x 6 = p6
    generalize x 7 = p7
    generalize x 8 = p8
    generalize x 9 = p9
    generalize x 10 = p10
    generalize x 11 = p11
    generalize x 12 = p12
    generalize x 13 = p13
    revert p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    decide +kernel
  · decide +kernel
