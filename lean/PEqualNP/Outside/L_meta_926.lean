import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_1 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  refine ⟨⟨[⟨.and, [0, 1]⟩], 2⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩], 4⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_3 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩,
      ⟨.or, [4, 5]⟩], 6⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩], 6⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩,
      ⟨.or, [5, 6]⟩], 7⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_7 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩,
      ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩], 8⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [3, 4]⟩,
      ⟨.or, [6, 7]⟩], 8⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩,
      ⟨.and, [0, 7]⟩], 8⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩,
      ⟨.and, [1, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩,
      ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩,
      ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩,
      ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩], 10⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩,
      ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩,
      ⟨.or, [10, 9]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩,
      ⟨.or, [2, 3]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [6, 7]⟩,
      ⟨.or, [10, 9]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩,
      ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩,
      ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩,
      ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩,
      ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩,
      ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩,
      ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩], 10⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩,
      ⟨.and, [0, 8]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.and, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩,
      ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.or, [4, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 9]⟩,
      ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.or, [1, 5]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩,
      ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 8]⟩,
      ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 4]⟩,
      ⟨.or, [1, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 8]⟩,
      ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩,
      ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩,
      ⟨.or, [10, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩,
      ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩,
      ⟨.or, [9, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩,
      ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 5]⟩,
      ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 5]⟩,
      ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [3, 5]⟩,
      ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩,
      ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 10]⟩,
      ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.and, [1, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 10]⟩,
      ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩,
      ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.and, [4, 5]⟩,
      ⟨.or, [7, 8]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 5]⟩,
      ⟨.and, [3, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 10]⟩,
      ⟨.or, [7, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩,
      ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩,
      ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩,
      ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩,
      ⟨.and, [3, 4]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [3, 4]⟩,
      ⟨.and, [5, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [3, 4]⟩,
      ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.and, [1, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩,
      ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩,
      ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩,
      ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 4]⟩,
      ⟨.and, [2, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 10]⟩,
      ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩,
      ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [8, 9]⟩,
      ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 6]⟩,
      ⟨.or, [11, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [5, 6]⟩,
      ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩,
      ⟨.or, [10, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩,
      ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [5, 11]⟩,
      ⟨.or, [10, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [5, 6]⟩,
      ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩,
      ⟨.or, [9, 10]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 11]⟩,
      ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 6]⟩,
      ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 5]⟩,
      ⟨.and, [2, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 11]⟩,
      ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.and, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 11]⟩,
      ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [1, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [4, 11]⟩,
      ⟨.or, [9, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.and, [1, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 11]⟩,
      ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [5, 6]⟩,
      ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩,
      ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [4, 6]⟩,
      ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩,
      ⟨.or, [2, 3]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [5, 6]⟩,
      ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩,
      ⟨.and, [3, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 11]⟩,
      ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩,
      ⟨.and, [1, 2]⟩, ⟨.or, [12, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [2, 6]⟩,
      ⟨.and, [1, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 2]⟩,
      ⟨.and, [3, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩,
      ⟨.and, [1, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩,
      ⟨.and, [2, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩,
      ⟨.and, [3, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩,
      ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩,
      ⟨.and, [3, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 6]⟩,
      ⟨.and, [5, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩,
      ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩,
      ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 5]⟩,
      ⟨.and, [6, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩,
      ⟨.or, [0, 5]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [0, 6]⟩,
      ⟨.and, [3, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩,
      ⟨.and, [3, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [3, 6]⟩,
      ⟨.and, [5, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [11, 6]⟩,
      ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [2, 4]⟩,
      ⟨.and, [6, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.and, [2, 5]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [11, 6]⟩,
      ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem graph_85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩,
      ⟨.or, [1, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [2, 6]⟩,
      ⟨.and, [5, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [FanInTwo]
  · decide +kernel

end PEqualNP.Outside.L_meta_926

open PEqualNP.Outside.L_meta_926 in
theorem PEqualNP.Outside.L_meta_926 :
  (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧
  (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  exact ⟨graph_1, graph_2, graph_3, graph_4, graph_5, graph_6, graph_7, graph_8,
    graph_9, graph_10, graph_11, graph_12, graph_13, graph_14, graph_15, graph_16,
    graph_17, graph_18, graph_19, graph_20, graph_21, graph_22, graph_23, graph_24,
    graph_25, graph_26, graph_27, graph_28, graph_29, graph_30, graph_31, graph_32,
    graph_33, graph_34, graph_35, graph_36, graph_37, graph_38, graph_39, graph_40,
    graph_41, graph_42, graph_43, graph_44, graph_45, graph_46, graph_47, graph_48,
    graph_49, graph_50, graph_51, graph_52, graph_53, graph_54, graph_55, graph_56,
    graph_57, graph_58, graph_59, graph_60, graph_61, graph_62, graph_63, graph_64,
    graph_65, graph_66, graph_67, graph_68, graph_69, graph_70, graph_71, graph_72,
    graph_73, graph_74, graph_75, graph_76, graph_77, graph_78, graph_79, graph_80,
    graph_81, graph_82, graph_83, graph_84, graph_85⟩
