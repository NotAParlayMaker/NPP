import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit0 : Circuit :=
  ⟨[⟨GateOp.and, [1, 0]⟩], 2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result0 : HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  refine ⟨circuit0, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit0]
  · decide +kernel
  · decide +kernel

def circuit1 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 3]⟩], 4⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result1 : HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  refine ⟨circuit1, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit1]
  · decide +kernel
  · decide +kernel

def circuit2 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 3]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩], 6⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result2 : HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨circuit2, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit2]
  · decide +kernel
  · decide +kernel

def circuit3 : Circuit :=
  ⟨[⟨GateOp.and, [1, 0]⟩,
    ⟨GateOp.and, [3, 2]⟩,
    ⟨GateOp.or, [4, 5]⟩], 6⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result3 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  refine ⟨circuit3, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit3]
  · decide +kernel
  · decide +kernel

def circuit4 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [4, 3]⟩,
    ⟨GateOp.and, [0, 5]⟩], 6⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result4 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  refine ⟨circuit4, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit4]
  · decide +kernel
  · decide +kernel

def circuit5 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 4]⟩,
    ⟨GateOp.and, [3, 1]⟩,
    ⟨GateOp.or, [5, 6]⟩], 7⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result5 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  refine ⟨circuit5, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit5]
  · decide +kernel
  · decide +kernel

def circuit6 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [4, 3]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [6, 7]⟩], 8⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result6 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  refine ⟨circuit6, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit6]
  · decide +kernel
  · decide +kernel

def circuit7 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.or, [6, 7]⟩], 8⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result7 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  refine ⟨circuit7, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit7]
  · decide +kernel
  · decide +kernel

def circuit8 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [5, 3]⟩,
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.and, [0, 7]⟩], 8⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result8 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  refine ⟨circuit8, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit8]
  · decide +kernel
  · decide +kernel

def circuit9 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [5, 3]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.and, [4, 1]⟩,
    ⟨GateOp.or, [7, 8]⟩], 9⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result9 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  refine ⟨circuit9, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit9]
  · decide +kernel
  · decide +kernel

def circuit10 : Circuit :=
  ⟨[⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.or, [9, 8]⟩], 10⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result10 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  refine ⟨circuit10, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit10]
  · decide +kernel
  · decide +kernel

def circuit11 : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.and, [1, 5]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.or, [6, 8]⟩], 9⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result11 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  refine ⟨circuit11, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit11]
  · decide +kernel
  · decide +kernel

def circuit12 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [5, 3]⟩,
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [8, 9]⟩], 10⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result12 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  refine ⟨circuit12, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit12]
  · decide +kernel
  · decide +kernel

def circuit13 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [5, 3]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.or, [7, 9]⟩], 10⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result13 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  refine ⟨circuit13, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit13]
  · decide +kernel
  · decide +kernel

def circuit14 : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [10, 9]⟩], 11⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result14 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  refine ⟨circuit14, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit14]
  · decide +kernel
  · decide +kernel

def circuit15 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.and, [3, 7]⟩,
    ⟨GateOp.and, [4, 2]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [10, 9]⟩], 11⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result15 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  refine ⟨circuit15, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit15]
  · decide +kernel
  · decide +kernel

def circuit16 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [5, 3]⟩,
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result16 : HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  refine ⟨circuit16, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit16]
  · decide +kernel
  · decide +kernel

def circuit17 : Circuit :=
  ⟨[⟨GateOp.and, [1, 0]⟩,
    ⟨GateOp.and, [3, 2]⟩,
    ⟨GateOp.and, [5, 4]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [9, 8]⟩], 10⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result17 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨circuit17, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit17]
  · decide +kernel
  · decide +kernel

def circuit18 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [5, 4]⟩,
    ⟨GateOp.or, [8, 9]⟩], 10⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result18 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨circuit18, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit18]
  · decide +kernel
  · decide +kernel

def circuit19 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.and, [3, 1]⟩,
    ⟨GateOp.and, [5, 4]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [10, 9]⟩], 11⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result19 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  refine ⟨circuit19, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit19]
  · decide +kernel
  · decide +kernel

def circuit20 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [3, 8]⟩,
    ⟨GateOp.or, [7, 9]⟩], 10⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result20 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  refine ⟨circuit20, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit20]
  · decide +kernel
  · decide +kernel

def circuit21 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.or, [8, 5]⟩,
    ⟨GateOp.and, [0, 9]⟩], 10⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result21 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  refine ⟨circuit21, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit21]
  · decide +kernel
  · decide +kernel

def circuit22 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [5, 1]⟩,
    ⟨GateOp.or, [9, 10]⟩], 11⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result22 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨circuit22, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit22]
  · decide +kernel
  · decide +kernel

def circuit23 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.and, [5, 4]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result23 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  refine ⟨circuit23, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit23]
  · decide +kernel
  · decide +kernel

def circuit24 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.or, [8, 10]⟩], 11⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result24 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨circuit24, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit24]
  · decide +kernel
  · decide +kernel

def circuit25 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [4, 1]⟩,
    ⟨GateOp.and, [5, 2]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result25 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  refine ⟨circuit25, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit25]
  · decide +kernel
  · decide +kernel

def circuit26 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [4, 9]⟩,
    ⟨GateOp.or, [8, 10]⟩], 11⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result26 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  refine ⟨circuit26, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit26]
  · decide +kernel
  · decide +kernel

def circuit27 : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [3, 6]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result27 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨circuit27, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit27]
  · decide +kernel
  · decide +kernel

def circuit28 : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [2, 6]⟩,
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.and, [5, 3]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result28 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨circuit28, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit28]
  · decide +kernel
  · decide +kernel

def circuit29 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.or, [8, 5]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [10, 11]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result29 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  refine ⟨circuit29, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit29]
  · decide +kernel
  · decide +kernel

def circuit30 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.and, [1, 10]⟩,
    ⟨GateOp.or, [9, 11]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result30 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  refine ⟨circuit30, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit30]
  · decide +kernel
  · decide +kernel

def circuit31 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.and, [5, 3]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result31 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  refine ⟨circuit31, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit31]
  · decide +kernel
  · decide +kernel

def circuit32 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.and, [5, 2]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result32 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  refine ⟨circuit32, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit32]
  · decide +kernel
  · decide +kernel

def circuit33 : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.and, [1, 7]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [5, 3]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result33 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨circuit33, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit33]
  · decide +kernel
  · decide +kernel

def circuit34 : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.and, [3, 7]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result34 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨circuit34, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit34]
  · decide +kernel
  · decide +kernel

def circuit35 : Circuit :=
  ⟨[⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.and, [4, 6]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result35 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  refine ⟨circuit35, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit35]
  · decide +kernel
  · decide +kernel

def circuit36 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [4, 9]⟩,
    ⟨GateOp.and, [5, 2]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result36 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨circuit36, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit36]
  · decide +kernel
  · decide +kernel

def circuit37 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [3, 9]⟩,
    ⟨GateOp.and, [5, 4]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [12, 10]⟩,
    ⟨GateOp.or, [13, 11]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result37 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨circuit37, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit37]
  · decide +kernel
  · decide +kernel

def circuit38 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [3, 8]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result38 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨circuit38, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit38]
  · decide +kernel
  · decide +kernel

def circuit39 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.or, [8, 5]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result39 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  refine ⟨circuit39, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit39]
  · decide +kernel
  · decide +kernel

def circuit40 : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.and, [1, 7]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result40 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  refine ⟨circuit40, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit40]
  · decide +kernel
  · decide +kernel

def circuit41 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [5, 11]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result41 : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨circuit41, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit41]
  · decide +kernel
  · decide +kernel

def circuit42 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result42 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨circuit42, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit42]
  · decide +kernel
  · decide +kernel

def circuit43 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [10, 11]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result43 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨circuit43, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit43]
  · decide +kernel
  · decide +kernel

def circuit44 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [4, 1]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result44 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨circuit44, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit44]
  · decide +kernel
  · decide +kernel

def circuit45 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.or, [9, 11]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result45 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  refine ⟨circuit45, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit45]
  · decide +kernel
  · decide +kernel

def circuit46 : Circuit :=
  ⟨[⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [12, 10]⟩,
    ⟨GateOp.or, [13, 11]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result46 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨circuit46, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit46]
  · decide +kernel
  · decide +kernel

def circuit47 : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.and, [1, 7]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [2, 9]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result47 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨circuit47, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit47]
  · decide +kernel
  · decide +kernel

def circuit48 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [3, 1]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [12, 11]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result48 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨circuit48, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit48]
  · decide +kernel
  · decide +kernel

def circuit49 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [9, 5]⟩,
    ⟨GateOp.or, [10, 6]⟩,
    ⟨GateOp.and, [0, 11]⟩], 12⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result49 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  refine ⟨circuit49, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit49]
  · decide +kernel
  · decide +kernel

def circuit50 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [9, 5]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [6, 1]⟩,
    ⟨GateOp.or, [11, 12]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result50 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨circuit50, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit50]
  · decide +kernel
  · decide +kernel

def circuit51 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result51 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  refine ⟨circuit51, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit51]
  · decide +kernel
  · decide +kernel

def circuit52 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [10, 12]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result52 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨circuit52, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit52]
  · decide +kernel
  · decide +kernel

def circuit53 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [5, 1]⟩,
    ⟨GateOp.and, [6, 2]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result53 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨circuit53, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit53]
  · decide +kernel
  · decide +kernel

def circuit54 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.and, [5, 11]⟩,
    ⟨GateOp.or, [10, 12]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result54 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  refine ⟨circuit54, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit54]
  · decide +kernel
  · decide +kernel

def circuit55 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [1, 10]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result55 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨circuit55, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit55]
  · decide +kernel
  · decide +kernel

def circuit56 : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [3, 7]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [13, 11]⟩,
    ⟨GateOp.or, [14, 12]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result56 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨circuit56, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit56]
  · decide +kernel
  · decide +kernel

def circuit57 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [4, 11]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result57 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨circuit57, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit57]
  · decide +kernel
  · decide +kernel

def circuit58 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [6, 2]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result58 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨circuit58, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit58]
  · decide +kernel
  · decide +kernel

def circuit59 : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [1, 7]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.and, [2, 9]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result59 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  refine ⟨circuit59, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit59]
  · decide +kernel
  · decide +kernel

def circuit60 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.and, [5, 2]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result60 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨circuit60, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit60]
  · decide +kernel
  · decide +kernel

def circuit61 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [10, 6]⟩,
    ⟨GateOp.and, [4, 11]⟩,
    ⟨GateOp.or, [9, 12]⟩], 13⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result61 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨circuit61, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit61]
  · decide +kernel
  · decide +kernel

def circuit62 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result62 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  refine ⟨circuit62, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit62]
  · decide +kernel
  · decide +kernel

def circuit63 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result63 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  refine ⟨circuit63, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit63]
  · decide +kernel
  · decide +kernel

def circuit64 : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [3, 7]⟩,
    ⟨GateOp.and, [6, 4]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [13, 11]⟩,
    ⟨GateOp.or, [14, 12]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result64 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨circuit64, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit64]
  · decide +kernel
  · decide +kernel

def circuit65 : Circuit :=
  ⟨[⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.and, [3, 10]⟩,
    ⟨GateOp.and, [4, 2]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [13, 11]⟩,
    ⟨GateOp.or, [14, 12]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result65 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨circuit65, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit65]
  · decide +kernel
  · decide +kernel

def circuit66 : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [3, 7]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [4, 11]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [13, 12]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result66 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨circuit66, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit66]
  · decide +kernel
  · decide +kernel

def circuit67 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [9, 5]⟩,
    ⟨GateOp.or, [10, 6]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [12, 13]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result67 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  refine ⟨circuit67, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit67]
  · decide +kernel
  · decide +kernel

def circuit68 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [9, 5]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [1, 12]⟩,
    ⟨GateOp.or, [11, 13]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result68 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  refine ⟨circuit68, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit68]
  · decide +kernel
  · decide +kernel

def circuit69 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [9, 5]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.and, [6, 3]⟩,
    ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result69 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  refine ⟨circuit69, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit69]
  · decide +kernel
  · decide +kernel

def circuit70 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.or, [11, 6]⟩,
    ⟨GateOp.and, [1, 12]⟩,
    ⟨GateOp.or, [10, 13]⟩], 14⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result70 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  refine ⟨circuit70, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit70]
  · decide +kernel
  · decide +kernel

def circuit71 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.and, [6, 2]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result71 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  refine ⟨circuit71, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit71]
  · decide +kernel
  · decide +kernel

def circuit72 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.and, [6, 3]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result72 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨circuit72, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit72]
  · decide +kernel
  · decide +kernel

def circuit73 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result73 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨circuit73, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit73]
  · decide +kernel
  · decide +kernel

def circuit74 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [3, 12]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result74 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨circuit74, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit74]
  · decide +kernel
  · decide +kernel

def circuit75 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [3, 6]⟩,
    ⟨GateOp.and, [5, 12]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result75 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨circuit75, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit75]
  · decide +kernel
  · decide +kernel

def circuit76 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.and, [6, 5]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result76 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨circuit76, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit76]
  · decide +kernel
  · decide +kernel

def circuit77 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.and, [5, 11]⟩,
    ⟨GateOp.and, [6, 2]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result77 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨circuit77, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit77]
  · decide +kernel
  · decide +kernel

def circuit78 : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.and, [2, 10]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.and, [3, 12]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result78 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨circuit78, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit78]
  · decide +kernel
  · decide +kernel

def circuit79 : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [3, 12]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result79 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨circuit79, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit79]
  · decide +kernel
  · decide +kernel

def circuit80 : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [3, 6]⟩,
    ⟨GateOp.and, [5, 12]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result80 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨circuit80, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit80]
  · decide +kernel
  · decide +kernel

def circuit81 : Circuit :=
  ⟨[⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.or, [7, 6]⟩,
    ⟨GateOp.and, [4, 8]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [10, 3]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [9, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result81 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨circuit81, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit81]
  · decide +kernel
  · decide +kernel

def circuit82 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [6, 10]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [1, 12]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result82 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  refine ⟨circuit82, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit82]
  · decide +kernel
  · decide +kernel

def circuit83 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [10, 6]⟩,
    ⟨GateOp.and, [4, 11]⟩,
    ⟨GateOp.and, [5, 2]⟩,
    ⟨GateOp.or, [9, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result83 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨circuit83, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit83]
  · decide +kernel
  · decide +kernel

def circuit84 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [5, 12]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem result84 : HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨circuit84, ?_, ?_, ?_⟩
  · simp [FanInTwo, circuit84]
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_926

theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨PEqualNP.Outside.L_meta_926.result0,
   PEqualNP.Outside.L_meta_926.result1,
   PEqualNP.Outside.L_meta_926.result2,
   PEqualNP.Outside.L_meta_926.result3,
   PEqualNP.Outside.L_meta_926.result4,
   PEqualNP.Outside.L_meta_926.result5,
   PEqualNP.Outside.L_meta_926.result6,
   PEqualNP.Outside.L_meta_926.result7,
   PEqualNP.Outside.L_meta_926.result8,
   PEqualNP.Outside.L_meta_926.result9,
   PEqualNP.Outside.L_meta_926.result10,
   PEqualNP.Outside.L_meta_926.result11,
   PEqualNP.Outside.L_meta_926.result12,
   PEqualNP.Outside.L_meta_926.result13,
   PEqualNP.Outside.L_meta_926.result14,
   PEqualNP.Outside.L_meta_926.result15,
   PEqualNP.Outside.L_meta_926.result16,
   PEqualNP.Outside.L_meta_926.result17,
   PEqualNP.Outside.L_meta_926.result18,
   PEqualNP.Outside.L_meta_926.result19,
   PEqualNP.Outside.L_meta_926.result20,
   PEqualNP.Outside.L_meta_926.result21,
   PEqualNP.Outside.L_meta_926.result22,
   PEqualNP.Outside.L_meta_926.result23,
   PEqualNP.Outside.L_meta_926.result24,
   PEqualNP.Outside.L_meta_926.result25,
   PEqualNP.Outside.L_meta_926.result26,
   PEqualNP.Outside.L_meta_926.result27,
   PEqualNP.Outside.L_meta_926.result28,
   PEqualNP.Outside.L_meta_926.result29,
   PEqualNP.Outside.L_meta_926.result30,
   PEqualNP.Outside.L_meta_926.result31,
   PEqualNP.Outside.L_meta_926.result32,
   PEqualNP.Outside.L_meta_926.result33,
   PEqualNP.Outside.L_meta_926.result34,
   PEqualNP.Outside.L_meta_926.result35,
   PEqualNP.Outside.L_meta_926.result36,
   PEqualNP.Outside.L_meta_926.result37,
   PEqualNP.Outside.L_meta_926.result38,
   PEqualNP.Outside.L_meta_926.result39,
   PEqualNP.Outside.L_meta_926.result40,
   PEqualNP.Outside.L_meta_926.result41,
   PEqualNP.Outside.L_meta_926.result42,
   PEqualNP.Outside.L_meta_926.result43,
   PEqualNP.Outside.L_meta_926.result44,
   PEqualNP.Outside.L_meta_926.result45,
   PEqualNP.Outside.L_meta_926.result46,
   PEqualNP.Outside.L_meta_926.result47,
   PEqualNP.Outside.L_meta_926.result48,
   PEqualNP.Outside.L_meta_926.result49,
   PEqualNP.Outside.L_meta_926.result50,
   PEqualNP.Outside.L_meta_926.result51,
   PEqualNP.Outside.L_meta_926.result52,
   PEqualNP.Outside.L_meta_926.result53,
   PEqualNP.Outside.L_meta_926.result54,
   PEqualNP.Outside.L_meta_926.result55,
   PEqualNP.Outside.L_meta_926.result56,
   PEqualNP.Outside.L_meta_926.result57,
   PEqualNP.Outside.L_meta_926.result58,
   PEqualNP.Outside.L_meta_926.result59,
   PEqualNP.Outside.L_meta_926.result60,
   PEqualNP.Outside.L_meta_926.result61,
   PEqualNP.Outside.L_meta_926.result62,
   PEqualNP.Outside.L_meta_926.result63,
   PEqualNP.Outside.L_meta_926.result64,
   PEqualNP.Outside.L_meta_926.result65,
   PEqualNP.Outside.L_meta_926.result66,
   PEqualNP.Outside.L_meta_926.result67,
   PEqualNP.Outside.L_meta_926.result68,
   PEqualNP.Outside.L_meta_926.result69,
   PEqualNP.Outside.L_meta_926.result70,
   PEqualNP.Outside.L_meta_926.result71,
   PEqualNP.Outside.L_meta_926.result72,
   PEqualNP.Outside.L_meta_926.result73,
   PEqualNP.Outside.L_meta_926.result74,
   PEqualNP.Outside.L_meta_926.result75,
   PEqualNP.Outside.L_meta_926.result76,
   PEqualNP.Outside.L_meta_926.result77,
   PEqualNP.Outside.L_meta_926.result78,
   PEqualNP.Outside.L_meta_926.result79,
   PEqualNP.Outside.L_meta_926.result80,
   PEqualNP.Outside.L_meta_926.result81,
   PEqualNP.Outside.L_meta_926.result82,
   PEqualNP.Outside.L_meta_926.result83,
   PEqualNP.Outside.L_meta_926.result84⟩
