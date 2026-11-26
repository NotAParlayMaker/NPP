import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18169 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => decide (4 ≤ (List.ofFn x).count true)) 20 := by
  unfold PEqualNP.MetaComplexity.HasCircuitSize
  refine ⟨⟨[⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [10, 8]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [18, 16]⟩, ⟨.and, [20, 19]⟩, ⟨.and, [14, 17]⟩, ⟨.and, [15, 22]⟩, ⟨.or, [15, 22]⟩, ⟨.or, [23, 21]⟩, ⟨.and, [25, 24]⟩], 26⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
