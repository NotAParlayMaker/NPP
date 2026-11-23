import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926_aux

open PEqualNP.CircuitLowerBounds

def c1 : Circuit where
  gates := [{ op := GateOp.and, inputs := [0, 1] }]
  output := 2

set_option maxRecDepth 400000 in
theorem h1 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  refine ⟨c1, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c1]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c1]
  · decide

def c2 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 3] }]
  output := 4

set_option maxRecDepth 400000 in
theorem h2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  refine ⟨c2, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c2]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c2]
  · decide

def c3 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [4, 5] }]
  output := 6

set_option maxRecDepth 400000 in
theorem h3 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨c3, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c3]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c3]
  · decide

def c4 : Circuit where
  gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [2, 3] }, { op := GateOp.or, inputs := [4, 5] }]
  output := 6

set_option maxRecDepth 400000 in
theorem h4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  refine ⟨c4, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c4]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c4]
  · decide

def c5 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [4, 3] }, { op := GateOp.and, inputs := [0, 5] }]
  output := 6

set_option maxRecDepth 400000 in
theorem h5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  refine ⟨c5, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c5]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c5]
  · decide

def c6 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 3] }, { op := GateOp.or, inputs := [5, 6] }]
  output := 7

set_option maxRecDepth 400000 in
theorem h6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  refine ⟨c6, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c6]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c6]
  · decide

def c7 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [4, 3] }, { op := GateOp.and, inputs := [0, 5] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 7] }]
  output := 8

set_option maxRecDepth 400000 in
theorem h7 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  refine ⟨c7, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c7]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c7]
  · decide

def c8 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 5] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [6, 7] }]
  output := 8

set_option maxRecDepth 400000 in
theorem h8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  refine ⟨c8, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c8]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c8]
  · decide

def c9 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 3] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.and, inputs := [0, 7] }]
  output := 8

set_option maxRecDepth 400000 in
theorem h9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  refine ⟨c9, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c9]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c9]
  · decide

def c10 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 3] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.or, inputs := [7, 8] }]
  output := 9

set_option maxRecDepth 400000 in
theorem h10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  refine ⟨c10, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c10]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c10]
  · decide

def c11 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 5] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [8, 9] }]
  output := 10

set_option maxRecDepth 400000 in
theorem h11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  refine ⟨c11, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c11]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c11]
  · decide

def c12 : Circuit where
  gates := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 5] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [2, 7] }, { op := GateOp.or, inputs := [6, 8] }]
  output := 9

set_option maxRecDepth 400000 in
theorem h12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  refine ⟨c12, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c12]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c12]
  · decide

def c13 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 3] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 9] }]
  output := 10

set_option maxRecDepth 400000 in
theorem h13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  refine ⟨c13, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c13]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c13]
  · decide

def c14 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 3] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [7, 9] }]
  output := 10

set_option maxRecDepth 400000 in
theorem h14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  refine ⟨c14, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c14]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c14]
  · decide

def c15 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 3] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [9, 10] }]
  output := 11

set_option maxRecDepth 400000 in
theorem h15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  refine ⟨c15, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c15]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c15]
  · decide

def c16 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 5] }, { op := GateOp.and, inputs := [1, 3] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [4, 9] }, { op := GateOp.or, inputs := [8, 10] }]
  output := 11

set_option maxRecDepth 400000 in
theorem h16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  refine ⟨c16, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c16]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c16]
  · decide

def c17 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 3] }, { op := GateOp.or, inputs := [6, 4] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [10, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  refine ⟨c17, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c17]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c17]
  · decide

def c18 : Circuit where
  gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [2, 3] }, { op := GateOp.or, inputs := [6, 7] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [8, 9] }]
  output := 10

set_option maxRecDepth 400000 in
theorem h18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨c18, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c18]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c18]
  · decide

def c19 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [8, 9] }]
  output := 10

set_option maxRecDepth 400000 in
theorem h19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨c19, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c19]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c19]
  · decide

def c20 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.and, inputs := [1, 3] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [9, 10] }]
  output := 11

set_option maxRecDepth 400000 in
theorem h20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  refine ⟨c20, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c20]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c20]
  · decide

def c21 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [3, 8] }, { op := GateOp.or, inputs := [7, 9] }]
  output := 10

set_option maxRecDepth 400000 in
theorem h21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  refine ⟨c21, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c21]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c21]
  · decide

def c22 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [0, 9] }]
  output := 10

set_option maxRecDepth 400000 in
theorem h22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  refine ⟨c22, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c22]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c22]
  · decide

def c23 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [1, 5] }, { op := GateOp.or, inputs := [9, 10] }]
  output := 11

set_option maxRecDepth 400000 in
theorem h23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨c23, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c23]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c23]
  · decide

def c24 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [10, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  refine ⟨c24, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c24]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c24]
  · decide

def c25 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [8, 10] }]
  output := 11

set_option maxRecDepth 400000 in
theorem h25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨c25, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c25]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c25]
  · decide

def c26 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.and, inputs := [2, 5] }, { op := GateOp.or, inputs := [10, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  refine ⟨c26, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c26]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c26]
  · decide

def c27 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.and, inputs := [4, 9] }, { op := GateOp.or, inputs := [8, 10] }]
  output := 11

set_option maxRecDepth 400000 in
theorem h27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  refine ⟨c27, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c27]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c27]
  · decide

def c28 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [3, 10] }, { op := GateOp.or, inputs := [9, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨c28, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c28]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c28]
  · decide

def c29 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.and, inputs := [2, 4] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.and, inputs := [3, 10] }, { op := GateOp.or, inputs := [9, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨c29, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c29]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c29]
  · decide

def c30 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [10, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  refine ⟨c30, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c30]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c30]
  · decide

def c31 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  refine ⟨c31, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c31]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c31]
  · decide

def c32 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.and, inputs := [3, 5] }, { op := GateOp.or, inputs := [11, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  refine ⟨c32, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c32]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c32]
  · decide

def c33 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.and, inputs := [2, 5] }, { op := GateOp.or, inputs := [11, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  refine ⟨c33, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c33]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c33]
  · decide

def c34 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.and, inputs := [3, 5] }, { op := GateOp.or, inputs := [11, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨c34, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c34]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c34]
  · decide

def c35 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [3, 11] }, { op := GateOp.or, inputs := [10, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨c35, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c35]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c35]
  · decide

def c36 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [10, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  refine ⟨c36, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c36]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c36]
  · decide

def c37 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [5, 11] }, { op := GateOp.or, inputs := [10, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨c37, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c37]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c37]
  · decide

def c38 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [3, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.and, inputs := [4, 5] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨c38, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c38]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c38]
  · decide

def c39 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 6] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.and, inputs := [3, 8] }, { op := GateOp.or, inputs := [7, 9] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [10, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨c39, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c39]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c39]
  · decide

def c40 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.or, inputs := [8, 5] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [10, 11] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  refine ⟨c40, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c40]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c40]
  · decide

def c41 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  refine ⟨c41, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c41]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c41]
  · decide

def c42 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [6, 3] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [1, 9] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [3, 4] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [11, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨c42, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c42]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c42]
  · decide

def c43 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [10, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨c43, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c43]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c43]
  · decide

def c44 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [10, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨c44, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c44]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c44]
  · decide

def c45 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [11, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨c45, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c45]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c45]
  · decide

def c46 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [9, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  refine ⟨c46, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c46]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c46]
  · decide

def c47 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [10, 11] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨c47, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c47]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c47]
  · decide

def c48 : Circuit where
  gates := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [2, 9] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [11, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨c48, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c48]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c48]
  · decide

def c49 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 3] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [10, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨c49, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c49]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c49]
  · decide

def c50 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.or, inputs := [10, 6] }, { op := GateOp.and, inputs := [0, 11] }]
  output := 12

set_option maxRecDepth 400000 in
theorem h50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  refine ⟨c50, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c50]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c50]
  · decide

def c51 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [0, 10] }, { op := GateOp.and, inputs := [1, 6] }, { op := GateOp.or, inputs := [11, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨c51, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c51]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c51]
  · decide

def c52 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [10, 11] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  refine ⟨c52, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c52]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c52]
  · decide

def c53 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [1, 11] }, { op := GateOp.or, inputs := [10, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨c53, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c53]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c53]
  · decide

def c54 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [1, 5] }, { op := GateOp.or, inputs := [10, 11] }, { op := GateOp.and, inputs := [2, 6] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨c54, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c54]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c54]
  · decide

def c55 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.and, inputs := [5, 11] }, { op := GateOp.or, inputs := [10, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  refine ⟨c55, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c55]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c55]
  · decide

def c56 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨c56, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c56]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c56]
  · decide

def c57 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.and, inputs := [3, 4] }, { op := GateOp.or, inputs := [11, 12] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [13, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨c57, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c57]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c57]
  · decide

def c58 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [4, 12] }, { op := GateOp.or, inputs := [11, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c58, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c58]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c58]
  · decide

def c59 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.and, inputs := [2, 6] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨c59, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c59]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c59]
  · decide

def c60 : Circuit where
  gates := [{ op := GateOp.or, inputs := [0, 4] }, { op := GateOp.and, inputs := [1, 7] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [2, 9] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [3, 12] }, { op := GateOp.or, inputs := [11, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  refine ⟨c60, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c60]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c60]
  · decide

def c61 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [2, 5] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.and, inputs := [4, 12] }, { op := GateOp.or, inputs := [11, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c61, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c61]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c61]
  · decide

def c62 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.or, inputs := [10, 6] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [9, 12] }]
  output := 13

set_option maxRecDepth 400000 in
theorem h62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨c62, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c62]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c62]
  · decide

def c63 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [1, 4] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [11, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  refine ⟨c63, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c63]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c63]
  · decide

def c64 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  refine ⟨c64, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c64]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c64]
  · decide

def c65 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [3, 11] }, { op := GateOp.or, inputs := [10, 12] }, { op := GateOp.and, inputs := [4, 6] }, { op := GateOp.or, inputs := [13, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c65, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c65]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c65]
  · decide

def c66 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.and, inputs := [1, 3] }, { op := GateOp.or, inputs := [8, 9] }, { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.and, inputs := [4, 11] }, { op := GateOp.or, inputs := [10, 12] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [13, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨c66, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c66]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c66]
  · decide

def c67 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.and, inputs := [0, 7] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.and, inputs := [3, 9] }, { op := GateOp.or, inputs := [8, 10] }, { op := GateOp.or, inputs := [2, 6] }, { op := GateOp.and, inputs := [4, 12] }, { op := GateOp.or, inputs := [11, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨c67, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c67]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c67]
  · decide

def c68 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.or, inputs := [10, 6] }, { op := GateOp.and, inputs := [0, 11] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [12, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  refine ⟨c68, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c68]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c68]
  · decide

def c69 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [0, 10] }, { op := GateOp.or, inputs := [2, 6] }, { op := GateOp.and, inputs := [1, 12] }, { op := GateOp.or, inputs := [11, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  refine ⟨c69, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c69]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c69]
  · decide

def c70 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.or, inputs := [9, 5] }, { op := GateOp.and, inputs := [0, 10] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [11, 12] }, { op := GateOp.and, inputs := [3, 6] }, { op := GateOp.or, inputs := [13, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  refine ⟨c70, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c70]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c70]
  · decide

def c71 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.or, inputs := [11, 6] }, { op := GateOp.and, inputs := [1, 12] }, { op := GateOp.or, inputs := [10, 13] }]
  output := 14

set_option maxRecDepth 400000 in
theorem h71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  refine ⟨c71, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c71]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c71]
  · decide

def c72 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [1, 11] }, { op := GateOp.or, inputs := [10, 12] }, { op := GateOp.and, inputs := [2, 6] }, { op := GateOp.or, inputs := [13, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  refine ⟨c72, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c72]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c72]
  · decide

def c73 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [1, 11] }, { op := GateOp.or, inputs := [10, 12] }, { op := GateOp.and, inputs := [3, 6] }, { op := GateOp.or, inputs := [13, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c73, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c73]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c73]
  · decide

def c74 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [1, 11] }, { op := GateOp.or, inputs := [10, 12] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [13, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c74, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c74]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c74]
  · decide

def c75 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [10, 11] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [3, 13] }, { op := GateOp.or, inputs := [12, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c75, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c75]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c75]
  · decide

def c76 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [10, 11] }, { op := GateOp.or, inputs := [3, 6] }, { op := GateOp.and, inputs := [5, 13] }, { op := GateOp.or, inputs := [12, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c76, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c76]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c76]
  · decide

def c77 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [1, 11] }, { op := GateOp.or, inputs := [10, 12] }, { op := GateOp.and, inputs := [5, 6] }, { op := GateOp.or, inputs := [13, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c77, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c77]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c77]
  · decide

def c78 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.or, inputs := [8, 4] }, { op := GateOp.and, inputs := [0, 9] }, { op := GateOp.and, inputs := [1, 5] }, { op := GateOp.or, inputs := [10, 11] }, { op := GateOp.or, inputs := [2, 5] }, { op := GateOp.and, inputs := [6, 13] }, { op := GateOp.or, inputs := [12, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c78, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c78]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c78]
  · decide

def c79 : Circuit where
  gates := [{ op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [7, 4] }, { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.and, inputs := [2, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [0, 6] }, { op := GateOp.and, inputs := [3, 13] }, { op := GateOp.or, inputs := [12, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c79, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c79]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c79]
  · decide

def c80 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [3, 13] }, { op := GateOp.or, inputs := [12, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨c80, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c80]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c80]
  · decide

def c81 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [3, 6] }, { op := GateOp.and, inputs := [5, 13] }, { op := GateOp.or, inputs := [12, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨c81, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c81]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c81]
  · decide

def c82 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [1, 2] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.or, inputs := [12, 6] }, { op := GateOp.and, inputs := [4, 13] }, { op := GateOp.or, inputs := [11, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c82, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c82]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c82]
  · decide

def c83 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [6, 13] }, { op := GateOp.or, inputs := [12, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  refine ⟨c83, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c83]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c83]
  · decide

def c84 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.and, inputs := [2, 5] }, { op := GateOp.or, inputs := [9, 10] }, { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.or, inputs := [12, 6] }, { op := GateOp.and, inputs := [4, 13] }, { op := GateOp.or, inputs := [11, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨c84, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c84]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c84]
  · decide

def c85 : Circuit where
  gates := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [7, 3] }, { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.and, inputs := [4, 10] }, { op := GateOp.or, inputs := [9, 11] }, { op := GateOp.or, inputs := [2, 6] }, { op := GateOp.and, inputs := [5, 13] }, { op := GateOp.or, inputs := [12, 14] }]
  output := 15

set_option maxRecDepth 400000 in
theorem h85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨c85, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, c85]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, c85]
  · decide

end PEqualNP.Outside.L_meta_926_aux

open PEqualNP.Outside.L_meta_926_aux in
theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85⟩
