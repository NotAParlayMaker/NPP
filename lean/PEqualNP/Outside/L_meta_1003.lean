import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The cover circuit from the vertex cover {1, 2, 4, 7}:
x1 (x0 + x5 + x2) + x2 (x3 + x6) + x4 (x0 + x6 + x7) + x7 (x3 + x5), thirteen gates. -/
theorem PEqualNP.Outside.L_meta_1003 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 := by
  refine ⟨⟨[⟨.or, [0, 5]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [2, 11]⟩,
    ⟨.or, [0, 6]⟩, ⟨.or, [13, 7]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [7, 16]⟩,
    ⟨.or, [10, 12]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [19, 17]⟩], 20⟩, ?_, ?_, ?_⟩
  · simp [FanInTwo]
  · decide
  · decide +kernel
