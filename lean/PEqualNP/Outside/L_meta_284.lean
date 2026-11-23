import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_284 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ ∀ x : Fin 6 → Bool, ((List.ofFn x).count true ≤ 2 → (C.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) ∧ (¬ (C.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ↔ (x 3 = true ∧ x 4 = true ∧ x 5 = true ∧ ¬ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  intro C hC
  subst C
  refine ⟨?_, rfl, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · intro x
    simp only [Fin.exists_fin_succ]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
      simp [List.ofFn_succ, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires,
        PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD, h0, h1, h2, h3, h4, h5]
