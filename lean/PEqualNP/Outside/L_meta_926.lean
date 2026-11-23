import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926

open PEqualNP.CircuitLowerBounds

-- Each edge is assigned to one endpoint in a minimum vertex cover. A star uses
-- one AND of the center and the OR of its assigned neighbors. OR the star outputs.
set_option maxRecDepth 10000 in
private theorem graph01 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  refine ⟨⟨[⟨.and, [0, 1]⟩], 2⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph02 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 3]⟩], 4⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph03 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 3]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [4, 5]⟩], 6⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph04 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  refine ⟨⟨[⟨.and, [0, 1]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [4, 5]⟩], 6⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph05 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.and, [0, 5]⟩], 6⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph06 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [5, 6]⟩], 7⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph07 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [6, 7]⟩], 8⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph08 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [6, 7]⟩], 8⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph09 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.or, [6, 4]⟩,
    ⟨.and, [0, 7]⟩], 8⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [7, 8]⟩], 9⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 8]⟩], 10⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  refine ⟨⟨[⟨.or, [0, 3]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [6, 8]⟩], 9⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.or, [6, 4]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [8, 9]⟩], 10⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [7, 9]⟩], 10⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [10, 9]⟩], 11⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.and, [2, 4]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [10, 9]⟩], 11⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.or, [6, 4]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨⟨[⟨.and, [0, 1]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 8]⟩], 10⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [8, 9]⟩], 10⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [10, 9]⟩], 11⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.or, [7, 9]⟩], 10⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.and, [0, 9]⟩], 10⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.or, [9, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [8, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.or, [8, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [2, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [10, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [9, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [12, 10]⟩,
    ⟨.or, [13, 11]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [5, 11]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 10]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [10, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.or, [9, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [12, 10]⟩,
    ⟨.or, [13, 11]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [0, 3]⟩,
    ⟨.and, [1, 7]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.and, [2, 9]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.or, [11, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [10, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [5, 11]⟩,
    ⟨.or, [10, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 11]⟩,
    ⟨.or, [14, 12]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [0, 4]⟩,
    ⟨.and, [1, 7]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.and, [2, 9]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.or, [9, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [5, 11]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.and, [4, 6]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [13, 11]⟩,
    ⟨.or, [14, 12]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [2, 4]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [13, 11]⟩,
    ⟨.or, [14, 12]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [12, 13]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [11, 13]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [11, 6]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [10, 13]⟩], 14⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [0, 2]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [11, 6]⟩,
    ⟨.and, [4, 12]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [6, 12]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [11, 6]⟩,
    ⟨.and, [4, 12]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

set_option maxRecDepth 10000 in
private theorem graph85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]

end PEqualNP.Outside.L_meta_926

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧
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
  exact ⟨PEqualNP.Outside.L_meta_926.graph01, PEqualNP.Outside.L_meta_926.graph02, PEqualNP.Outside.L_meta_926.graph03, PEqualNP.Outside.L_meta_926.graph04, PEqualNP.Outside.L_meta_926.graph05, PEqualNP.Outside.L_meta_926.graph06,
    PEqualNP.Outside.L_meta_926.graph07, PEqualNP.Outside.L_meta_926.graph08, PEqualNP.Outside.L_meta_926.graph09, PEqualNP.Outside.L_meta_926.graph10, PEqualNP.Outside.L_meta_926.graph11, PEqualNP.Outside.L_meta_926.graph12,
    PEqualNP.Outside.L_meta_926.graph13, PEqualNP.Outside.L_meta_926.graph14, PEqualNP.Outside.L_meta_926.graph15, PEqualNP.Outside.L_meta_926.graph16, PEqualNP.Outside.L_meta_926.graph17, PEqualNP.Outside.L_meta_926.graph18,
    PEqualNP.Outside.L_meta_926.graph19, PEqualNP.Outside.L_meta_926.graph20, PEqualNP.Outside.L_meta_926.graph21, PEqualNP.Outside.L_meta_926.graph22, PEqualNP.Outside.L_meta_926.graph23, PEqualNP.Outside.L_meta_926.graph24,
    PEqualNP.Outside.L_meta_926.graph25, PEqualNP.Outside.L_meta_926.graph26, PEqualNP.Outside.L_meta_926.graph27, PEqualNP.Outside.L_meta_926.graph28, PEqualNP.Outside.L_meta_926.graph29, PEqualNP.Outside.L_meta_926.graph30,
    PEqualNP.Outside.L_meta_926.graph31, PEqualNP.Outside.L_meta_926.graph32, PEqualNP.Outside.L_meta_926.graph33, PEqualNP.Outside.L_meta_926.graph34, PEqualNP.Outside.L_meta_926.graph35, PEqualNP.Outside.L_meta_926.graph36,
    PEqualNP.Outside.L_meta_926.graph37, PEqualNP.Outside.L_meta_926.graph38, PEqualNP.Outside.L_meta_926.graph39, PEqualNP.Outside.L_meta_926.graph40, PEqualNP.Outside.L_meta_926.graph41, PEqualNP.Outside.L_meta_926.graph42,
    PEqualNP.Outside.L_meta_926.graph43, PEqualNP.Outside.L_meta_926.graph44, PEqualNP.Outside.L_meta_926.graph45, PEqualNP.Outside.L_meta_926.graph46, PEqualNP.Outside.L_meta_926.graph47, PEqualNP.Outside.L_meta_926.graph48,
    PEqualNP.Outside.L_meta_926.graph49, PEqualNP.Outside.L_meta_926.graph50, PEqualNP.Outside.L_meta_926.graph51, PEqualNP.Outside.L_meta_926.graph52, PEqualNP.Outside.L_meta_926.graph53, PEqualNP.Outside.L_meta_926.graph54,
    PEqualNP.Outside.L_meta_926.graph55, PEqualNP.Outside.L_meta_926.graph56, PEqualNP.Outside.L_meta_926.graph57, PEqualNP.Outside.L_meta_926.graph58, PEqualNP.Outside.L_meta_926.graph59, PEqualNP.Outside.L_meta_926.graph60,
    PEqualNP.Outside.L_meta_926.graph61, PEqualNP.Outside.L_meta_926.graph62, PEqualNP.Outside.L_meta_926.graph63, PEqualNP.Outside.L_meta_926.graph64, PEqualNP.Outside.L_meta_926.graph65, PEqualNP.Outside.L_meta_926.graph66,
    PEqualNP.Outside.L_meta_926.graph67, PEqualNP.Outside.L_meta_926.graph68, PEqualNP.Outside.L_meta_926.graph69, PEqualNP.Outside.L_meta_926.graph70, PEqualNP.Outside.L_meta_926.graph71, PEqualNP.Outside.L_meta_926.graph72,
    PEqualNP.Outside.L_meta_926.graph73, PEqualNP.Outside.L_meta_926.graph74, PEqualNP.Outside.L_meta_926.graph75, PEqualNP.Outside.L_meta_926.graph76, PEqualNP.Outside.L_meta_926.graph77, PEqualNP.Outside.L_meta_926.graph78,
    PEqualNP.Outside.L_meta_926.graph79, PEqualNP.Outside.L_meta_926.graph80, PEqualNP.Outside.L_meta_926.graph81, PEqualNP.Outside.L_meta_926.graph82, PEqualNP.Outside.L_meta_926.graph83, PEqualNP.Outside.L_meta_926.graph84,
    PEqualNP.Outside.L_meta_926.graph85⟩
