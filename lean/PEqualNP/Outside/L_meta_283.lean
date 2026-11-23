import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_283

private lemma allInputs (P : (Fin 6 → Bool) → Prop)
    (h : ∀ a b c d e f : Bool, P ![a, b, c, d, e, f]) (x : Fin 6 → Bool) : P x := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  exact hx ▸ h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

end PEqualNP.Outside.L_meta_283

theorem PEqualNP.Outside.L_meta_283 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 2 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  refine ⟨⟨?_, {3, 8}, by decide, ?_⟩, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · intro j g hj hop
    have hj' : j < 9 := (List.getElem?_eq_some_iff.mp hj).1
    interval_cases j <;> injection hj with hg <;> subst g <;> first | decide | cases hop
  · apply PEqualNP.Outside.L_meta_283.allInputs
    decide
