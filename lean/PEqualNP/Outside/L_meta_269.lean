import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_269 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) → (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  refine ⟨⟨?_, {0, 5, 10}, by decide, ?_⟩, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro j g hj hop
    have hl : j < 11 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j <;> simp at hj <;> subst hj <;> simp at hop ⊢
  · decide
