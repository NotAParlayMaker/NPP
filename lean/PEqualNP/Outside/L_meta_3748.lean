import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_3748 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [41, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [48, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 50] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [52, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [56, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [57, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [60, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [61, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 62] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [64, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [65, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [73, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 74] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [76, 80] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [82, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 89] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [93, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 95] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [96, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 101] }], output := 102 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 89 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 11), (0, 13), (1, 7), (1, 8), (1, 12), (2, 8), (2, 9), (2, 13), (3, 7), (3, 9), (3, 10), (4, 8), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 11), (0, 13), (1, 7), (1, 8), (1, 12), (2, 8), (2, 9), (2, 13), (3, 7), (3, 9), (3, 10), (4, 8), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 11), (0, 13), (1, 7), (1, 8), (1, 12), (2, 8), (2, 9), (2, 13), (3, 7), (3, 9), (3, 10), (4, 8), (4, 10), (4, 11), (5, 9), (5, 11), (5, 12), (6, 10), (6, 12), (6, 13)] : List (Fin 14 × Fin 14))) := by
  rintro C rfl
  refine ⟨by decide +kernel, rfl, ?_, by decide +kernel⟩
  intro x
  have edgeTest (es : List (Fin 14 × Fin 14)) :
      decide (∃ e ∈ es, x e.1 = true ∧ x e.2 = true) = es.any (fun e => x e.1 && x e.2) := by
    apply Bool.eq_iff_iff.mpr
    simp
  rw [edgeTest]
  have table : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool, (
    let w14 := b7 || (b11 || false)
    let w15 := w14 || (b13 || false)
    let w16 := b0 && (w15 && true)
    let w17 := b7 || (b8 || false)
    let w18 := w17 || (b12 || false)
    let w19 := b1 && (w18 && true)
    let w20 := w16 || (w19 || false)
    let w21 := b8 || (b9 || false)
    let w22 := w21 || (b13 || false)
    let w23 := b2 && (w22 && true)
    let w24 := w20 || (w23 || false)
    let w25 := b7 || (b9 || false)
    let w26 := w25 || (b10 || false)
    let w27 := b3 && (w26 && true)
    let w28 := w24 || (w27 || false)
    let w29 := b8 || (b10 || false)
    let w30 := w29 || (b11 || false)
    let w31 := b4 && (w30 && true)
    let w32 := w28 || (w31 || false)
    let w33 := b9 || (b11 || false)
    let w34 := w33 || (b12 || false)
    let w35 := b5 && (w34 && true)
    let w36 := w32 || (w35 || false)
    let w37 := b10 || (b12 || false)
    let w38 := w37 || (b13 || false)
    let w39 := b6 && (w38 && true)
    let w40 := w36 || (w39 || false)
    let w41 := b2 && (b4 && true)
    let w42 := w41 && (b5 && true)
    let w43 := w42 && (b6 && true)
    let w44 := b0 && (b3 && true)
    let w45 := w44 && (b5 && true)
    let w46 := w45 && (b6 && true)
    let w47 := w43 || (w46 || false)
    let w48 := b0 && (b1 && true)
    let w49 := w48 && (b4 && true)
    let w50 := w49 && (b6 && true)
    let w51 := w47 || (w50 || false)
    let w52 := b0 && (b1 && true)
    let w53 := w52 && (b2 && true)
    let w54 := w53 && (b5 && true)
    let w55 := w51 || (w54 || false)
    let w56 := b1 && (b2 && true)
    let w57 := w56 && (b3 && true)
    let w58 := w57 && (b6 && true)
    let w59 := w55 || (w58 || false)
    let w60 := b0 && (b2 && true)
    let w61 := w60 && (b3 && true)
    let w62 := w61 && (b4 && true)
    let w63 := w59 || (w62 || false)
    let w64 := b1 && (b3 && true)
    let w65 := w64 && (b4 && true)
    let w66 := w65 && (b5 && true)
    let w67 := w63 || (w66 || false)
    let w68 := w67 || (b0 || false)
    let w69 := w68 || (b1 || false)
    let w70 := w69 || (b3 || false)
    let w71 := b7 && (w70 && true)
    let w72 := w67 || (b1 || false)
    let w73 := w72 || (b2 || false)
    let w74 := w73 || (b4 || false)
    let w75 := b8 && (w74 && true)
    let w76 := w71 || (w75 || false)
    let w77 := w67 || (b2 || false)
    let w78 := w77 || (b3 || false)
    let w79 := w78 || (b5 || false)
    let w80 := b9 && (w79 && true)
    let w81 := w76 || (w80 || false)
    let w82 := w67 || (b3 || false)
    let w83 := w82 || (b4 || false)
    let w84 := w83 || (b6 || false)
    let w85 := b10 && (w84 && true)
    let w86 := w81 || (w85 || false)
    let w87 := w67 || (b0 || false)
    let w88 := w87 || (b4 || false)
    let w89 := w88 || (b5 || false)
    let w90 := b11 && (w89 && true)
    let w91 := w86 || (w90 || false)
    let w92 := w67 || (b1 || false)
    let w93 := w92 || (b5 || false)
    let w94 := w93 || (b6 || false)
    let w95 := b12 && (w94 && true)
    let w96 := w91 || (w95 || false)
    let w97 := w67 || (b0 || false)
    let w98 := w97 || (b2 || false)
    let w99 := w98 || (b6 || false)
    let w100 := b13 && (w99 && true)
    let w101 := w96 || (w100 || false)
    let w102 := w40 && (w101 && true)
    w102) = ((b0 && b7) || ((b0 && b11) || ((b0 && b13) || ((b1 && b7) || ((b1 && b8) || ((b1 && b12) || ((b2 && b8) || ((b2 && b9) || ((b2 && b13) || ((b3 && b7) || ((b3 && b9) || ((b3 && b10) || ((b4 && b8) || ((b4 && b10) || ((b4 && b11) || ((b5 && b9) || ((b5 && b11) || ((b5 && b12) || ((b6 && b10) || ((b6 && b12) || ((b6 && b13) || false))))))))))))))))))))) := by
    decide +kernel
  have xs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := by rfl
  simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons,
    List.map_nil, xs, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
  simpa only [Bool.and_true,Bool.or_false] using table (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13)
