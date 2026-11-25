import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_11099 :
    PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (3 ≤ ((List.ofFn x).count true))) 10 := by
  -- Wires 9 and 10 say that each pair has a true input and that some pair has
  -- two true inputs. The last four gates take their majority with input 4.
  let C : Circuit :=
    ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩,
     ⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩,
     ⟨.and, [6, 7]⟩, ⟨.or, [5, 8]⟩,
     ⟨.and, [4, 9]⟩, ⟨.or, [4, 9]⟩,
     ⟨.or, [10, 11]⟩, ⟨.and, [12, 13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp_all [C] <;> aesop
  · decide +kernel
