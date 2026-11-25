import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Removing an edge inside S and losing an outside neighbor take distinct uncovered edges.
theorem PEqualNP.Outside.R_meta_5182_528
    (fewEdges :
      let base := edgeGraph 11
        (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map fun e => (e / 11,e % 11))
      let S : Finset (Fin 11) := {3,8,9,10}
      let M : Finset (Fin 11 × Fin 11) := {(1,4),(2,5),(6,7)}
      let forced (H : SimpleGraph (Fin 11)) [DecidableRel H.Adj] :=
        (Finset.univ \ S).filter fun v => ∃ u∈S, H.Adj u v
      let cost (H : SimpleGraph (Fin 11)) [DecidableRel H.Adj] :=
        (forced H).card +
          (M.filter fun e => H.Adj e.1 e.2 ∧ e.1 ∉ forced H ∧ e.2 ∉ forced H).card
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (U : Finset (Sym2 (Fin 11))),
        G = base → U.card ≤ 2 → (∀ a∈S, ∀ b∈S, ¬ (G.deleteEdges ↑U).Adj a b) →
        5+U.card ≤ cost (G.deleteEdges ↑U)+1)
    (positiveOverhead :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
        IsLeastAO G C → (∃ a b, G.Adj a b) → (junk G C).Nonempty →
        1 ≤ 2*(centreless G C).card+(orN G C \ lam G C).card)
    (remaining :
      let base := edgeGraph 11
        (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map fun e => (e / 11,e % 11))
      let S : Finset (Fin 11) := {3,8,9,10}
      let M : Finset (Fin 11 × Fin 11) := {(1,4),(2,5),(6,7)}
      let forced (H : SimpleGraph (Fin 11)) [DecidableRel H.Adj] :=
        (Finset.univ \ S).filter fun v => ∃ u∈S, H.Adj u v
      let cost (H : SimpleGraph (Fin 11)) [DecidableRel H.Adj] :=
        (forced H).card +
          (M.filter fun e => H.Adj e.1 e.2 ∧ e.1 ∉ forced H ∧ e.2 ∉ forced H).card
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
        G = base → IsLeastAO G C → TopForm G C → C.size < 22 →
        (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
        let U := Ustar G C
        let H := G.deleteEdges ↑U
        (∀ a∈S, ∀ b∈S, ¬ H.Adj a b) → 3 ≤ U.card → cost H+1 < 5+U.card →
        5+U.card ≤ cost H + 2*(centreless G C).card + (orN G C \ lam G C).card) :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               x13 = ∅ →                 (∀ x16 ∈ x11 \ x13, ∀ x18 ∈ x11 \ x13, ¬x10.Adj x16 x18) →                   have x17 : Finset (Fin (11 : ℕ)) := {x17 ∈ Finset.univ \ x11 | ∃ x18 ∈ x11 \ x13, x10.Adj x18 x17};                   have x18 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x18 ∈ x12 | x10.Adj x18.1 x18.2 ∧ x18.1 ∉ x17 ∧ x18.2 ∉ x17};                   (5 : ℕ) + x9.card ≤ x13.card + x17.card + x18.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  intro G inst C graph least top short chain
  dsimp only
  intro selected sub empty independent
  subst selected
  rw [Finset.sdiff_empty] at independent
  rw [Finset.sdiff_empty,Finset.card_empty,zero_add]
  let base := edgeGraph 11
    (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map fun e => (e / 11,e % 11))
  let S : Finset (Fin 11) := {3,8,9,10}
  let M : Finset (Fin 11 × Fin 11) := {(1,4),(2,5),(6,7)}
  let forced (H : SimpleGraph (Fin 11)) [DecidableRel H.Adj] :=
    (Finset.univ \ S).filter fun v => ∃ u∈S, H.Adj u v
  let cost (H : SimpleGraph (Fin 11)) [DecidableRel H.Adj] :=
    (forced H).card +
      (M.filter fun e => H.Adj e.1 e.2 ∧ e.1 ∉ forced H ∧ e.2 ∉ forced H).card
  let U := Ustar G C
  let H := G.deleteEdges (U : Set _)
  change (∀ a∈S, ∀ b∈S, ¬ H.Adj a b) at independent
  change 5+U.card ≤ cost H + 2*(centreless G C).card+(orN G C \ lam G C).card
  have graphEq : G = base := graph
  have someEdge : ∃ a b, G.Adj a b := by
    rw [graph]
    exact ⟨8,9,by decide +kernel⟩
  have someJunk : (junk G C).Nonempty := by
    obtain ⟨i,j,eq,_⟩ := chain
    rw [eq]
    exact ⟨i,by simp⟩
  have paid := positiveOverhead 11 G C least someEdge someJunk
  by_cases count : U.card ≤ 2
  · have easy := fewEdges G U graphEq count independent
    change 5+U.card ≤ cost H+1 at easy
    omega
  · by_cases charge : 5+U.card ≤ cost H+1
    · omega
    · have high : 3 ≤ U.card := by omega
      have deficit : cost H+1 < 5+U.card := by omega
      exact remaining G C graphEq least top short chain independent high deficit
