import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_277

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def circuit277 : Circuit :=
  { gates := [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [5, 9]⟩], output := 10 }

theorem circuit277_monotone : Monotone2 circuit277 := by
  simp only [Monotone2]
  intro g hg
  simp only [circuit277, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circuit277_size : circuit277.size = 6 := rfl

theorem circuit277_eval (x : Fin 5 → Bool) :
    circuit277.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5,
        (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 2), (2, 3)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true := by
  revert x
  decide +revert

end PEqualNP.Outside.L_meta_277

open PEqualNP.Outside.L_meta_277 in
theorem PEqualNP.Outside.L_meta_277 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 6 ∧ (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 2), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  exact ⟨circuit277_monotone, circuit277_size, circuit277_eval⟩
