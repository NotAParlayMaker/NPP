import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨(⟨[⟨.and, [0, 1]⟩], 2⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩], 4⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩], 6⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩], 6⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩], 8⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩], 8⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩], 8⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩], 10⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩], 11⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 9]⟩], 11⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩], 11⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩], 10⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [11, 10]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [11, 10]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩], 12⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [11, 12]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [12, 13]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [0, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
  · refine ⟨(⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩ : Circuit), ?_, by decide, ?_⟩
    · simp [FanInTwo, List.forall_mem_cons]
    · decide +kernel
