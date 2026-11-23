import PEqualNP.Defs

-- Mythos 6 et Codex Betelgeuse

set_option maxRecDepth 32000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_1182 :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) x := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩,
    ⟨.and, [0, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [5, 12]⟩,
    ⟨.and, [6, 7]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.Monotone2]
  · decide
