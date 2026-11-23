import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_272 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ (∃ A : Finset ℕ, A.card = 5 ∧ (∀ j ∈ A, j < C.size) ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ j ∈ A)) ∧ (∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) := by
  intro C hC
  subst C
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · refine ⟨{0, 1, 3, 4, 6}, by decide, ?_, ?_⟩
    · intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    · intro j g hg
      have hj : j < 7 := by
        by_contra hn
        have hnone : ([⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
            ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩] :
            List PEqualNP.CircuitLowerBounds.Gate)[j]? = none :=
          List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hn)
        simp only [hnone] at hg
        contradiction
      interval_cases j <;> simp at hg <;> subst g <;> simp
  · decide
