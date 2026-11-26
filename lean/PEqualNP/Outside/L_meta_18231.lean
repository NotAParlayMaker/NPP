import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18231 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => decide (5 ≤ (List.ofFn x).count true)) 39 := by
  unfold PEqualNP.MetaComplexity.HasCircuitSize
  refine ⟨⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [6, 13]⟩, ⟨.and, [16, 10]⟩, ⟨.or, [16, 10]⟩, ⟨.and, [18, 12]⟩, ⟨.or, [18, 12]⟩, ⟨.and, [20, 14]⟩, ⟨.or, [20, 14]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [24, 26]⟩, ⟨.and, [23, 25]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [27, 19]⟩, ⟨.or, [21, 29]⟩, ⟨.and, [22, 28]⟩, ⟨.and, [32, 30]⟩, ⟨.and, [34, 33]⟩, ⟨.or, [34, 33]⟩, ⟨.or, [31, 35]⟩, ⟨.and, [37, 36]⟩], 38⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
