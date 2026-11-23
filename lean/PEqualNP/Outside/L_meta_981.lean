import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

namespace PEqualNP.Outside

theorem L_meta_981 :
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) 10) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) 11) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 12) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) 12) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) 12) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) 12) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) 12) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [3, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [2, 10]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 13]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [3, 13]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [6, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [16, 12]⟩, ⟨.or, [17, 15]⟩], 18⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide
  · refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [17, 15]⟩], 18⟩, ?_, by decide, ?_⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo]
    · decide

end PEqualNP.Outside
