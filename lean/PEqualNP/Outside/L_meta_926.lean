import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row0 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) := by
  let C : Circuit := ⟨[⟨.and,[0,1]⟩], 2⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row1 : (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,3]⟩], 4⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row2 : (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,3]⟩, ⟨.and,[1,2]⟩, ⟨.or,[4,5]⟩], 6⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row3 : (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) := by
  let C : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.or,[4,5]⟩], 6⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row4 : (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[4,3]⟩, ⟨.and,[0,5]⟩], 6⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row5 : (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,4]⟩, ⟨.and,[1,3]⟩, ⟨.or,[5,6]⟩], 7⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row6 : (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[4,3]⟩, ⟨.and,[0,5]⟩, ⟨.and,[1,2]⟩, ⟨.or,[6,7]⟩], 8⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row7 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,5]⟩, ⟨.and,[3,4]⟩, ⟨.or,[6,7]⟩], 8⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row8 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[5,3]⟩, ⟨.or,[6,4]⟩, ⟨.and,[0,7]⟩], 8⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row9 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[5,3]⟩, ⟨.and,[0,6]⟩, ⟨.and,[1,4]⟩, ⟨.or,[7,8]⟩], 9⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row10 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,5]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,4]⟩, ⟨.or,[6,7]⟩, ⟨.or,[9,8]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row11 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) := by
  let C : Circuit := ⟨[⟨.or,[0,3]⟩, ⟨.and,[1,5]⟩, ⟨.or,[0,4]⟩, ⟨.and,[2,7]⟩, ⟨.or,[6,8]⟩], 9⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row12 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[5,3]⟩, ⟨.or,[6,4]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,2]⟩, ⟨.or,[8,9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row13 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[5,3]⟩, ⟨.and,[0,6]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,8]⟩, ⟨.or,[7,9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row14 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[5,3]⟩, ⟨.and,[0,6]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,4]⟩, ⟨.or,[7,8]⟩, ⟨.or,[10,9]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row15 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,5]⟩, ⟨.and,[2,4]⟩, ⟨.or,[1,4]⟩, ⟨.and,[3,8]⟩, ⟨.or,[6,7]⟩, ⟨.or,[10,9]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row16 : (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[5,3]⟩, ⟨.or,[6,4]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,4]⟩, ⟨.or,[8,9]⟩, ⟨.or,[11,10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row17 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) := by
  let C : Circuit := ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.and,[4,5]⟩, ⟨.or,[6,7]⟩, ⟨.or,[9,8]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row18 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.and,[4,5]⟩, ⟨.or,[8,9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row19 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,6]⟩, ⟨.and,[1,3]⟩, ⟨.and,[4,5]⟩, ⟨.or,[7,8]⟩, ⟨.or,[10,9]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row20 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,6]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,8]⟩, ⟨.or,[7,9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row21 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.or,[7,4]⟩, ⟨.or,[8,5]⟩, ⟨.and,[0,9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row22 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.or,[7,4]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,5]⟩, ⟨.or,[9,10]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row23 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,2]⟩, ⟨.and,[4,5]⟩, ⟨.or,[8,9]⟩, ⟨.or,[11,10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row24 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.or,[4,5]⟩, ⟨.and,[1,9]⟩, ⟨.or,[8,10]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row25 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,4]⟩, ⟨.and,[2,5]⟩, ⟨.or,[8,9]⟩, ⟨.or,[11,10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row26 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.or,[1,5]⟩, ⟨.and,[4,9]⟩, ⟨.or,[8,10]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row27 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,6]⟩, ⟨.and,[1,2]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,9]⟩, ⟨.or,[7,8]⟩, ⟨.or,[11,10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row28 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,6]⟩, ⟨.and,[2,4]⟩, ⟨.or,[1,5]⟩, ⟨.and,[3,9]⟩, ⟨.or,[7,8]⟩, ⟨.or,[11,10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row29 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.or,[7,4]⟩, ⟨.or,[8,5]⟩, ⟨.and,[0,9]⟩, ⟨.and,[1,2]⟩, ⟨.or,[10,11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row30 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.or,[7,4]⟩, ⟨.and,[0,8]⟩, ⟨.or,[2,5]⟩, ⟨.and,[1,10]⟩, ⟨.or,[9,11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row31 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.or,[7,4]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,5]⟩, ⟨.or,[9,10]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row32 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,9]⟩, ⟨.and,[2,5]⟩, ⟨.or,[8,10]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row33 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,9]⟩, ⟨.and,[3,5]⟩, ⟨.or,[8,10]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row34 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,2]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,10]⟩, ⟨.or,[8,9]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row35 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,2]⟩, ⟨.or,[3,5]⟩, ⟨.and,[4,10]⟩, ⟨.or,[8,9]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row36 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.and,[2,5]⟩, ⟨.or,[1,5]⟩, ⟨.and,[4,10]⟩, ⟨.or,[8,9]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row37 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,6]⟩, ⟨.and,[1,2]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,9]⟩, ⟨.and,[4,5]⟩, ⟨.or,[7,8]⟩, ⟨.or,[12,10]⟩, ⟨.or,[13,11]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row38 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,6]⟩, ⟨.or,[1,5]⟩, ⟨.and,[3,8]⟩, ⟨.or,[2,5]⟩, ⟨.and,[4,10]⟩, ⟨.or,[7,9]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row39 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.or,[7,4]⟩, ⟨.or,[8,5]⟩, ⟨.and,[0,9]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,4]⟩, ⟨.or,[10,11]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row40 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.or,[7,4]⟩, ⟨.and,[0,8]⟩, ⟨.or,[2,5]⟩, ⟨.and,[1,10]⟩, ⟨.and,[3,4]⟩, ⟨.or,[9,11]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row41 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,9]⟩, ⟨.or,[3,4]⟩, ⟨.and,[5,11]⟩, ⟨.or,[8,10]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row42 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,7]⟩, ⟨.and,[3,4]⟩, ⟨.and,[5,6]⟩, ⟨.or,[8,9]⟩, ⟨.or,[11,10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row43 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.and,[5,6]⟩, ⟨.or,[10,11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row44 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,4]⟩, ⟨.and,[5,6]⟩, ⟨.or,[9,10]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row45 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[5,6]⟩, ⟨.and,[4,10]⟩, ⟨.or,[9,11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row46 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,4]⟩, ⟨.and,[5,6]⟩, ⟨.or,[8,9]⟩, ⟨.or,[12,10]⟩, ⟨.or,[13,11]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row47 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) := by
  let C : Circuit := ⟨[⟨.or,[0,3]⟩, ⟨.and,[1,7]⟩, ⟨.or,[0,4]⟩, ⟨.and,[2,9]⟩, ⟨.and,[5,6]⟩, ⟨.or,[8,10]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row48 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,3]⟩, ⟨.or,[5,6]⟩, ⟨.and,[4,10]⟩, ⟨.or,[8,9]⟩, ⟨.or,[12,11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row49 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.or,[9,5]⟩, ⟨.or,[10,6]⟩, ⟨.and,[0,11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row50 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.or,[9,5]⟩, ⟨.and,[0,10]⟩, ⟨.and,[1,6]⟩, ⟨.or,[11,12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row51 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.and,[1,2]⟩, ⟨.and,[5,6]⟩, ⟨.or,[10,11]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row52 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.or,[5,6]⟩, ⟨.and,[1,11]⟩, ⟨.or,[10,12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row53 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.and,[1,5]⟩, ⟨.and,[2,6]⟩, ⟨.or,[10,11]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row54 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.or,[1,6]⟩, ⟨.and,[5,11]⟩, ⟨.or,[10,12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row55 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,10]⟩, ⟨.and,[5,6]⟩, ⟨.or,[9,11]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row56 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,4]⟩, ⟨.and,[5,6]⟩, ⟨.or,[9,10]⟩, ⟨.or,[13,11]⟩, ⟨.or,[14,12]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row57 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,2]⟩, ⟨.or,[5,6]⟩, ⟨.and,[4,11]⟩, ⟨.or,[9,10]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row58 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[4,5]⟩, ⟨.and,[1,10]⟩, ⟨.and,[2,6]⟩, ⟨.or,[9,11]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row59 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[0,4]⟩, ⟨.and,[1,7]⟩, ⟨.or,[0,5]⟩, ⟨.and,[2,9]⟩, ⟨.or,[0,6]⟩, ⟨.and,[3,11]⟩, ⟨.or,[8,10]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row60 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.and,[2,5]⟩, ⟨.or,[1,6]⟩, ⟨.and,[4,11]⟩, ⟨.or,[9,10]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row61 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[1,5]⟩, ⟨.or,[10,6]⟩, ⟨.and,[4,11]⟩, ⟨.or,[9,12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row62 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,4]⟩, ⟨.or,[4,6]⟩, ⟨.and,[5,11]⟩, ⟨.or,[9,10]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row63 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[5,6]⟩, ⟨.and,[4,10]⟩, ⟨.and,[5,6]⟩, ⟨.or,[9,11]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row64 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,7]⟩, ⟨.and,[1,2]⟩, ⟨.or,[4,5]⟩, ⟨.and,[3,10]⟩, ⟨.and,[4,6]⟩, ⟨.or,[8,9]⟩, ⟨.or,[13,11]⟩, ⟨.or,[14,12]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row65 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,7]⟩, ⟨.and,[2,4]⟩, ⟨.or,[1,4]⟩, ⟨.and,[3,10]⟩, ⟨.and,[5,6]⟩, ⟨.or,[8,9]⟩, ⟨.or,[13,11]⟩, ⟨.or,[14,12]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row66 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.and,[0,7]⟩, ⟨.or,[1,5]⟩, ⟨.and,[3,9]⟩, ⟨.or,[2,6]⟩, ⟨.and,[4,11]⟩, ⟨.or,[8,10]⟩, ⟨.or,[13,12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row67 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.or,[9,5]⟩, ⟨.or,[10,6]⟩, ⟨.and,[0,11]⟩, ⟨.and,[1,2]⟩, ⟨.or,[12,13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row68 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.or,[9,5]⟩, ⟨.and,[0,10]⟩, ⟨.or,[2,6]⟩, ⟨.and,[1,12]⟩, ⟨.or,[11,13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row69 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.or,[9,5]⟩, ⟨.and,[0,10]⟩, ⟨.and,[1,2]⟩, ⟨.and,[3,6]⟩, ⟨.or,[11,12]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row70 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.or,[2,5]⟩, ⟨.or,[11,6]⟩, ⟨.and,[1,12]⟩, ⟨.or,[10,13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row71 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.or,[2,5]⟩, ⟨.and,[1,11]⟩, ⟨.and,[2,6]⟩, ⟨.or,[10,12]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row72 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.or,[2,5]⟩, ⟨.and,[1,11]⟩, ⟨.and,[3,6]⟩, ⟨.or,[10,12]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row73 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.or,[2,5]⟩, ⟨.and,[1,11]⟩, ⟨.and,[5,6]⟩, ⟨.or,[10,12]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row74 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.and,[1,2]⟩, ⟨.or,[5,6]⟩, ⟨.and,[3,12]⟩, ⟨.or,[10,11]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row75 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.and,[1,2]⟩, ⟨.or,[3,6]⟩, ⟨.and,[5,12]⟩, ⟨.or,[10,11]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row76 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.or,[5,6]⟩, ⟨.and,[1,11]⟩, ⟨.and,[5,6]⟩, ⟨.or,[10,12]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row77 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.or,[8,4]⟩, ⟨.and,[0,9]⟩, ⟨.and,[2,6]⟩, ⟨.or,[1,6]⟩, ⟨.and,[5,12]⟩, ⟨.or,[10,11]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row78 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[0,2]⟩, ⟨.or,[7,4]⟩, ⟨.and,[1,8]⟩, ⟨.or,[0,5]⟩, ⟨.and,[2,10]⟩, ⟨.or,[0,6]⟩, ⟨.and,[3,12]⟩, ⟨.or,[9,11]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row79 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,10]⟩, ⟨.or,[5,6]⟩, ⟨.and,[3,12]⟩, ⟨.or,[9,11]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row80 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[2,4]⟩, ⟨.and,[1,10]⟩, ⟨.or,[3,6]⟩, ⟨.and,[5,12]⟩, ⟨.or,[9,11]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row81 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,2]⟩, ⟨.or,[3,5]⟩, ⟨.or,[11,6]⟩, ⟨.and,[4,12]⟩, ⟨.or,[9,10]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row82 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[4,5]⟩, ⟨.and,[1,10]⟩, ⟨.or,[2,4]⟩, ⟨.and,[6,12]⟩, ⟨.or,[9,11]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row83 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.and,[2,5]⟩, ⟨.or,[1,5]⟩, ⟨.or,[11,6]⟩, ⟨.and,[4,12]⟩, ⟨.or,[9,10]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem row84 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩, ⟨.or,[7,3]⟩, ⟨.and,[0,8]⟩, ⟨.or,[1,6]⟩, ⟨.and,[4,10]⟩, ⟨.or,[2,6]⟩, ⟨.and,[5,12]⟩, ⟨.or,[9,11]⟩, ⟨.or,[14,13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C,FanInTwo]
  · decide

end PEqualNP.Outside.L_meta_926_aux

open PEqualNP.Outside.L_meta_926_aux in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41, row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66, row67, row68, row69, row70, row71, row72, row73, row74, row75, row76, row77, row78, row79, row80, row81, row82, row83, row84⟩
