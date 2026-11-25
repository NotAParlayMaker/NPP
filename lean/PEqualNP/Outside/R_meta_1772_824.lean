import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1772_824
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let defects := fun D : Circuit => {j : ℕ | j < D.gates.length ∧
        (gateAt D j).op = GateOp.and ∧ ∀ u v, G.Adj u v → ¬Owns n D j u v}
      let lost := fun (D : Circuit) (j : ℕ) (u v : Fin n) => G.Adj u v ∧
        circuitFun n ⟨D.gates.set j ⟨GateOp.or, []⟩, D.output⟩ (pairInput u v) = false
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        (∀ D : Circuit, IsMinimalMonoCircuit n D → circuitFun n D = graphFun G ∅ →
          (defects C).ncard ≤ (defects D).ncard) ∧
        (∀ j ∈ defects C, ∃ u v a b, lost C j u v ∧ lost C j a b ∧ s(u,v) ≠ s(a,b)))
    (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let defects := fun D : Circuit => {j : ℕ | j < D.gates.length ∧
        (gateAt D j).op = GateOp.and ∧ ∀ u v, G.Adj u v → ¬Owns n D j u v}
      let lost := fun (D : Circuit) (j : ℕ) (u v : Fin n) => G.Adj u v ∧
        circuitFun n ⟨D.gates.set j ⟨GateOp.or, []⟩, D.output⟩ (pairInput u v) = false
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        (defects C).Nonempty →
        (∀ j ∈ defects C, ∃ u v a b, lost C j u v ∧ lost C j a b ∧ s(u,v) ≠ s(a,b)) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size ≤ C.size ∧ (defects D).ncard < (defects C).ncard) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G _ tri four
  classical
  obtain ⟨C, least, computes, optimal, double⟩ := normalize n G
  refine ⟨C, least, computes, ?_⟩
  intro j hj op
  by_contra empty
  obtain ⟨D, mono, correct, size, lower⟩ := exchange n G tri four C least computes
    ⟨j, hj, op, fun u v edge owns => empty ⟨u, v, edge, owns⟩⟩ double
  have minD : IsMinimalMonoCircuit n D := ⟨mono, fun A m h =>
    size.trans (least.2 A m (h.trans (correct.trans computes.symm)))⟩
  exact (Nat.not_lt_of_ge (optimal D minD correct)) lower
