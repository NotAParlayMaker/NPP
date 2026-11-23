import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_809 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 9 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 4), (0, 7), (1, 2), (2, 3), (3, 4), (3, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
    · exact ⟨Or.inl rfl, by decide⟩
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
    · exact ⟨Or.inl rfl, by decide⟩
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
    · exact ⟨Or.inl rfl, by decide⟩
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
  · decide
  · intro x
    revert x
    decide
