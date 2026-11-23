import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_272 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ (∃ A : Finset ℕ, A.card = 5 ∧ (∀ j ∈ A, j < C.size) ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ j ∈ A)) ∧ (∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ⟨{0, 1, 3, 4, 6}, rfl, ?_, ?_⟩, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    change j < 7
    omega
  · intro j g hg
    rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> simp at hg <;> subst hg <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3] := by simp [List.ofFn_succ]
    rw [hx]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide
