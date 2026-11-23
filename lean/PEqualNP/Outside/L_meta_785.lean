import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_785

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def circuit785 : Circuit :=
  { gates := [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [10, 12]⟩], output := 13 }

theorem circuit785_fanInTwo : FanInTwo circuit785 := by
  simp only [FanInTwo]
  intro g hg
  simp only [circuit785, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circuit785_size : circuit785.size = 8 := rfl

theorem circuit785_eval (x : Fin 6 → Bool) :
    circuit785.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 6,
        (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (2, 3), (3, 4), (4, 5)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true := by
  revert x
  decide +revert

end PEqualNP.Outside.L_meta_785

open PEqualNP.Outside.L_meta_785 in
theorem PEqualNP.Outside.L_meta_785 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (2, 3), (3, 4), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  exact ⟨circuit785_fanInTwo, circuit785_size, circuit785_eval⟩
