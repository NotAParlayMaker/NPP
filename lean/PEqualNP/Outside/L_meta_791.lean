import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_791

lemma key : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool,
    (PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) [a0, a1, a2, a3, a4, a5, a6] = true ↔
      ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)] : List (ℕ × ℕ)) ∧
        ![a0, a1, a2, a3, a4, a5, a6] u = true ∧ ![a0, a1, a2, a3, a4, a5, a6] v = true) := by
  decide

lemma ofFnN (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := rfl

lemma vecN (x : Fin 7 → Bool) : ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] = x := by
  funext i
  fin_cases i <;> rfl

end PEqualNP.Outside.L_meta_791

open PEqualNP.Outside.L_meta_791 in
theorem PEqualNP.Outside.L_meta_791 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have h := key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
    rw [vecN x] at h
    rw [ofFnN x]
    exact h
