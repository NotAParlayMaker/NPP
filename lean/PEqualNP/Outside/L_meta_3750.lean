import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3750

lemma bool_rec_id (b : Bool) : Bool.rec false true b = b := by
  cases b <;> rfl

def specimen : PEqualNP.CircuitLowerBounds.Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [38, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [54, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [58, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 59] }], output := 60 }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma shape : PEqualNP.TopForm.IsAO2 14 specimen ∧ specimen.size = 47 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma reread : ∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)),
    PEqualNP.Core.ReadTwiceAt 14 specimen (specimen.output - 14) e.1 e.2 ↔
    e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (2, 7), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma computes (x : Fin 14 → Bool) : PEqualNP.MetaComplexity.circuitFun 14 specimen x =
    decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true) := by
  cbv
  simp only [bool_rec_id]
  change (((((((((((x 0 || x 1) || x 3) && ((x 7 || x 8) || x 10)) || (x 5 && (x 7 || x 10))) && ((x 0 || x 10) && ((x 1 || x 5) || x 7))) || (((((x 0 || x 1) || x 3) && ((x 7 || x 8) || x 10)) || (x 4 && (x 7 || x 8))) && ((x 1 || x 8) && ((x 0 || x 3) || x 4)))) || (((((x 0 || x 1) || x 3) && ((x 7 || x 8) || x 10)) || (x 2 && (x 7 || x 8))) && ((x 3 || x 7) && ((x 1 || x 2) || x 10)))) || (((x 0 || x 5) || x 6) && x 9)) || (((x 1 || x 4) || x 6) && x 11)) || (((x 2 || x 3) || x 6) && x 12)) || (((x 2 || x 4) || x 5) && x 13)) = _
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  simp only [Bool.decide_or, Bool.decide_and, Bool.decide_coe]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  generalize x 8 = b8
  generalize x 9 = b9
  generalize x 10 = b10
  generalize x 11 = b11
  generalize x 12 = b12
  generalize x 13 = b13
  clear x
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  decide +kernel

end PEqualNP.Outside.L_meta_3750

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_3750 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [38, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [54, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [58, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 59] }], output := 60 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 47 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (2, 7), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  intro C hC
  subst C
  exact ⟨PEqualNP.Outside.L_meta_3750.shape.1, PEqualNP.Outside.L_meta_3750.shape.2,
    PEqualNP.Outside.L_meta_3750.computes, PEqualNP.Outside.L_meta_3750.reread⟩
