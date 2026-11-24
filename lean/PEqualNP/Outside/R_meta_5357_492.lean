import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.NotPremium

-- The first child keeps circuit size fixed and rules out two local repairs of an ownerless AND.
-- The second seeks a vertex cover within budget or an equivalent circuit with edge ownership.
theorem PEqualNP.Outside.R_meta_5357_492
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    let rigid (D : Circuit) : Prop :=
      let fix (j : ℕ) (b : Bool) := circuitFun n ⟨replaceByConst D.gates j b,D.output⟩
      let pivot (j : ℕ) (a b : Fin n) := G.Adj a b ∧ fix j false (pairInput a b) = false
      ∀ j < D.size, (gateAt D j).op = .and → (¬ ∃ a b, G.Adj a b ∧ Owns n D j a b) →
      (∃ a b c d, pivot j a b ∧ pivot j c d ∧ s(a,b) ≠ s(c,d)) ∧
      ∀ s t : ℕ, circuitFun n ⟨D.gates.set j ⟨.or,[s,t]⟩,D.output⟩ ≠ circuitFun n D
    Monotone2 C → circuitFun n C = graphFun G ∅ →
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧ rigid D)
    (structural : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    G.CliqueFree 3 → NoFourCycle G →
    IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
    (let pivot (j : ℕ) (a b : Fin n) := G.Adj a b ∧
        circuitFun n ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩ (pairInput a b) = false
      ∀ j < C.size, (gateAt C j).op = .and → (¬ ∃ a b, G.Adj a b ∧ Owns n C j a b) →
      (∃ a b c d, pivot j a b ∧ pivot j c d ∧ s(a,b) ≠ s(c,d)) ∧
      ∀ s t : ℕ, circuitFun n ⟨C.gates.set j ⟨.or,[s,t]⟩,C.output⟩ ≠ circuitFun n C) →
    (∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧
      G.edgeSet.ncard + T.card - 1 ≤ C.size) ∨
    ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧ E.size ≤ C.size ∧
      ∀ j < E.size, (gateAt E j).op = .and → ∃ a b, G.Adj a b ∧ Owns n E j a b) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
    IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
    (∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T →
      C.size < G.edgeSet.ncard + T.card - 1) →
    ∃ E : Circuit, Monotone2 E ∧ circuitFun n E = graphFun G ∅ ∧ E.size ≤ C.size ∧
      ∀ j < E.size, (gateAt E j).op = .and → ∃ a b, G.Adj a b ∧ Owns n E j a b := by
  intro n G _ C tri four mC fC savings
  obtain ⟨D,mD,fD,sz,rigid⟩ := normalize n G C mC.1 fC
  have best : IsMinimalMonoCircuit n D := ⟨mD,fun E hm he => sz.trans_le
    (mC.2 E hm (he.trans (fD.trans fC.symm)))⟩
  have triangle : G.CliqueFree 3 := by
    intro S h
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp h
    exact tri a b c hab hbc hac.symm
  rcases structural n G D triangle four best fD rigid with ⟨T,cover,bound⟩ | ⟨E,mE,fE,small,owned⟩
  · exact ((savings T cover).not_ge (bound.trans_eq sz)).elim
  · exact ⟨E,mE,fE,small.trans_eq sz,owned⟩
