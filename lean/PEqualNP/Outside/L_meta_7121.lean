import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7121 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (1 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ))) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩], 8⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp
  · intro x
    have h0 : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    have h3 : (List.ofFn x).getD 3 false = x 3 := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    show ((List.ofFn x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
      [(List.ofFn x).getD 0 false, (List.ofFn x).getD 3 false]]).getD 8 false) = _
    rw [h0, h3, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
