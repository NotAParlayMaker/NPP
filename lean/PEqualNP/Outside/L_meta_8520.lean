import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_8520 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 : Bool) (x4 x5 : ℕ), ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x7 : List Bool), x6.eval x7 = x1.eval (x7 ++ [if x4 = (56 : ℕ) then x3 else if x3 = Bool.true then x7.getD x4 Bool.false && x7.getD x5 Bool.false else x7.getD x4 Bool.false || x7.getD x5 Bool.false]) := by
  intro x1 hm x3 x4 x5
  refine ⟨Circuit.mk ((if x4 = 56 then Gate.mk (if x3 then GateOp.and else GateOp.or) [] else Gate.mk (if x3 then GateOp.and else GateOp.or) [x4, x5]) :: x1.gates) x1.output, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with hg | hg
    · subst hg
      by_cases h : x4 = 56 <;> cases x3 <;> simp [h]
    · exact hm g hg
  · simp [Circuit.size]
  · intro x7
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons]
    congr 3
    by_cases h : x4 = 56 <;> cases x3 <;> simp [h, GateOp.eval, List.getD_eq_getElem?_getD]
