import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1772_317
    (hBip : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],
      x2.edgeFinset.Nonempty → x2.Colorable (2 : ℕ) →
      (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →
      PEqualNP.TopForm.NoFourCycle x2 →
      ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧
        PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
        ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11)
    (hNonBip : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],
      x2.edgeFinset.Nonempty → ¬x2.Colorable (2 : ℕ) →
      (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →
      PEqualNP.TopForm.NoFourCycle x2 →
      ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧
        PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
        ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro x1 x2 _ htri hc4
  by_cases hedge : x2.edgeFinset.Nonempty
  · by_cases hcol : x2.Colorable 2
    · exact hBip x1 x2 hedge hcol htri hc4
    · exact hNonBip x1 x2 hedge hcol htri hc4
  · refine ⟨{ gates := [], output := x1 }, ?_, ?_, ?_⟩
    · refine ⟨fun g hg => False.elim (List.not_mem_nil hg), fun D _ _ => Nat.zero_le _⟩
    · funext y
      have hno : ∀ u v : Fin x1, ¬x2.Adj u v := fun u v huv => hedge ⟨s(u, v), x2.mem_edgeFinset.mpr huv⟩
      have hlhs : (List.ofFn y).getD x1 false = false := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp)]
        rfl
      have hrhs : PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ y = false := by
        change decide ((∃ v ∈ (∅ : Finset (Fin x1)), y v = true) ∨ ∃ u v : Fin x1, x2.Adj u v ∧ y u = true ∧ y v = true) = false
        rw [decide_eq_false_iff_not]
        rintro (⟨v, hv, _⟩ | ⟨u, v, huv, _, _⟩)
        · exact Finset.notMem_empty v hv
        · exact hno u v huv
      change (List.ofFn y).getD x1 false = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ y
      rw [hlhs, hrhs]
    · intro x7 hx7
      exact False.elim (Nat.not_lt_zero x7 hx7)
