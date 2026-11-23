import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_161 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∃ i j : Fin C.gates.length, i ≠ j ∧ ∀ k : Fin C.gates.length, (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ (k = i ∨ k = j)) ∧ ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)) := by
  -- Each pair of distinct inputs is separated by at least one of the two partitions.
  let C : Circuit := ⟨[
    ⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [7, 8]⟩,
    ⟨.or, [6, 9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_, ⟨2, 5, by decide, ?_⟩, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, C]
  · simp [C]
  · intro k
    change Fin 7 at k
    fin_cases k <;> simp [C, List.get]
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3] := rfl
    rw [h]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> rfl
