import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_284

def HasEdge (x : Fin 6 → Bool) : Prop := ∃ u v : Fin 6,
  (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧
  x u = true ∧ x v = true

def edgeBool (x : Fin 6 → Bool) : Bool :=
  @decide (HasEdge x) (by unfold HasEdge; infer_instance)

theorem edgeBool_iff (x : Fin 6 → Bool) : edgeBool x = true ↔ HasEdge x := by
  simp [edgeBool]

end PEqualNP.Outside.L_meta_284

open PEqualNP.Outside.L_meta_284 in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_284 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ ∀ x : Fin 6 → Bool, ((List.ofFn x).count true ≤ 2 → (C.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) ∧ (¬ (C.eval (List.ofFn x) = true ↔ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ↔ (x 3 = true ∧ x 4 = true ∧ x 5 = true ∧ ¬ (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · unfold PEqualNP.MetaComplexity.Monotone2
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    change (_ → (_ ↔ HasEdge x)) ∧ (¬ (_ ↔ HasEdge x) ↔ _ ∧ _ ∧ _ ∧ ¬ HasEdge x)
    rw [← edgeBool_iff]
    revert x
    decide +kernel
