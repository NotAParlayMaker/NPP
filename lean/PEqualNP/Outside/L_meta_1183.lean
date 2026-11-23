import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1183 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 6 && x 7)) x := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 4]⟩,
      ⟨.and, [1, 11]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [10, 12]⟩,
      ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_or_distrib_left, Bool.or_assoc]
