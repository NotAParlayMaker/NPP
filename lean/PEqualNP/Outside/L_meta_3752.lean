import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3752

open PEqualNP.CircuitLowerBounds

private def specimen : Circuit :=
  { gates :=
      [{ op := GateOp.or, inputs := [0, 1] },
       { op := GateOp.or, inputs := [14, 3] },
       { op := GateOp.or, inputs := [7, 8] },
       { op := GateOp.or, inputs := [16, 10] },
       { op := GateOp.and, inputs := [15, 17] },
       { op := GateOp.and, inputs := [5, 10] },
       { op := GateOp.or, inputs := [18, 19] },
       { op := GateOp.or, inputs := [0, 10] },
       { op := GateOp.or, inputs := [1, 3] },
       { op := GateOp.or, inputs := [22, 5] },
       { op := GateOp.or, inputs := [23, 7] },
       { op := GateOp.and, inputs := [21, 24] },
       { op := GateOp.and, inputs := [20, 25] },
       { op := GateOp.and, inputs := [4, 8] },
       { op := GateOp.or, inputs := [18, 27] },
       { op := GateOp.or, inputs := [1, 8] },
       { op := GateOp.or, inputs := [0, 3] },
       { op := GateOp.or, inputs := [30, 4] },
       { op := GateOp.or, inputs := [31, 7] },
       { op := GateOp.and, inputs := [29, 32] },
       { op := GateOp.and, inputs := [28, 33] },
       { op := GateOp.or, inputs := [26, 34] },
       { op := GateOp.and, inputs := [7, 2] },
       { op := GateOp.or, inputs := [35, 36] },
       { op := GateOp.or, inputs := [0, 5] },
       { op := GateOp.or, inputs := [38, 6] },
       { op := GateOp.and, inputs := [39, 9] },
       { op := GateOp.or, inputs := [37, 40] },
       { op := GateOp.or, inputs := [1, 4] },
       { op := GateOp.or, inputs := [42, 6] },
       { op := GateOp.and, inputs := [43, 11] },
       { op := GateOp.or, inputs := [41, 44] },
       { op := GateOp.or, inputs := [2, 3] },
       { op := GateOp.or, inputs := [46, 6] },
       { op := GateOp.and, inputs := [47, 12] },
       { op := GateOp.or, inputs := [45, 48] },
       { op := GateOp.or, inputs := [2, 4] },
       { op := GateOp.or, inputs := [50, 5] },
       { op := GateOp.and, inputs := [51, 13] },
       { op := GateOp.or, inputs := [49, 52] }]
    output := 53 }

private def edges : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)]

private def rereadEdges : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)]

private lemma edgeTest (x : Fin 14 → Bool) :
    edges.any (fun e => x e.1 && x e.2) =
      decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  simp only [Bool.and_eq_true]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
private lemma computesEdgeFunction (x : Fin 14 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 14 specimen x =
      decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true) := by
  rw [← edgeTest]
  have inputs : List.ofFn x =
      [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := rfl
  rw [PEqualNP.MetaComplexity.circuitFun, inputs]
  clear inputs
  simp only [specimen, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, GateOp.eval, List.all_cons, List.all_nil, List.any_cons,
    List.any_nil, id_eq, edges, Bool.and_true, Bool.or_false]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  grind (splits := 32)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
private lemma readsExactly :
    ∀ e ∈ edges, PEqualNP.Core.ReadTwiceAt 14 specimen (specimen.output - 14) e.1 e.2 ↔
      e ∈ rereadEdges := by
  unfold edges rereadEdges
  decide +kernel

end PEqualNP.Outside.L_meta_3752

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_3752 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [46, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [51, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 52] }], output := 53 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 40 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  intro C h
  change C = PEqualNP.Outside.L_meta_3752.specimen at h
  subst C
  refine ⟨by decide +kernel, rfl, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_3752.computesEdgeFunction
  · exact PEqualNP.Outside.L_meta_3752.readsExactly
