import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_820

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  { gates := [⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [8, 2]⟩, ⟨GateOp.and, [1, 9]⟩,
      ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.or, [14, 4]⟩, ⟨GateOp.and, [3, 15]⟩, ⟨GateOp.or, [13, 16]⟩],
    output := 17 }

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem computes : ∀ x : Fin 8 → Bool, (circ.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (1, 7), (2, 3), (3, 4), (3, 6),
      (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_820

theorem PEqualNP.Outside.L_meta_820 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (1, 7), (2, 3), (3, 4), (3, 6), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  exact ⟨PEqualNP.Outside.L_meta_820.fanin, rfl, PEqualNP.Outside.L_meta_820.computes⟩
