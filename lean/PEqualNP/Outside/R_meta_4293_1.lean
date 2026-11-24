import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4293_1
    (hstruct : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → PEqualNP.CircuitMoves.Lift x1 x2 x3 → PEqualNP.TopForm.IsAO2 x1 x3 ∧ x3.output < x1 + x3.gates.length ∧ x3.size = x2.size)
    (hsem : ∀ (x1 : ℕ) (x2 x3 : Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → PEqualNP.CircuitMoves.Lift x1 x2 x3 → PEqualNP.MetaComplexity.circuitFun x1 x3 = PEqualNP.MetaComplexity.circuitFun x1 x2) :
    ∀ (x1 : ℕ) (x2 x3 : Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → PEqualNP.CircuitMoves.Lift x1 x2 x3 → PEqualNP.TopForm.IsAO2 x1 x3 ∧ x3.output < x1 + x3.gates.length ∧ x3.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x3 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  intro n C C' hAO hout hLift
  obtain ⟨hs1, hs2, hs3⟩ := hstruct n C C' hAO hout hLift
  exact ⟨hs1, hs2, hs3, hsem n C C' hAO hout hLift⟩
