import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1774_307
    (coverBudget : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v) →
      (∃ j : ℕ, ∃ u v p q : Fin n, G.Adj u v ∧ G.Adj p q ∧ Owns n C j u v ∧
        Owns n C j p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q) →
      ∃ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) ∧
        G.edgeFinset.card + T.card - 1 ≤ C.size)
    (starConstruction : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (T : Finset (Fin n)), G.IsVertexCover (T : Set (Fin n)) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ G.edgeFinset.card + T.card - 1 ∧
        ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          ∃ a b : Fin n, G.Adj a b ∧ Owns n D j a b ∧
            ∀ u v : Fin n, G.Adj u v → Owns n D j u v → u = a ∨ v = a) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8 := by
  classical
  intro n G _ triangleFree squareFree useful cost C least computes allUseful positive
  let bad (D : Circuit) : Set ℕ := {j | ∃ u v p q : Fin n, G.Adj u v ∧ G.Adj p q ∧
    Owns n D j u v ∧ Owns n D j p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q}
  have witness : (bad C).Nonempty := by
    by_contra none
    have empty : bad C = ∅ := Set.not_nonempty_iff_eq_empty.mp none
    change 0 < (bad C).ncard at positive
    simp [empty] at positive
  obtain ⟨T, covers, budget⟩ := coverBudget n G C triangleFree squareFree least computes allUseful witness
  obtain ⟨D, mono, same, bound, stars⟩ := starConstruction n G T covers
  have clean : bad D = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro j h
    obtain ⟨u,v,p,q,uv,pq,j1,j2,up,uq,vp,vq⟩ := h
    obtain ⟨a,_,_,_,atCenter⟩ := stars j j1.1 j1.2.1
    rcases atCenter u v uv j1 with hu | hv <;> rcases atCenter p q pq j2 with hp | hq
    · exact up (hu.trans hp.symm)
    · exact uq (hu.trans hq.symm)
    · exact vp (hv.trans hp.symm)
    · exact vq (hv.trans hq.symm)
  refine ⟨D,mono,same,bound.trans budget,?_,?_⟩
  · intro j hj ha
    obtain ⟨a,b,ab,owns,_⟩ := stars j hj ha
    exact ⟨a,b,ab,owns⟩
  · change (bad D).ncard < cost C
    simpa [clean] using positive
