import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.Core

-- Price the accepted core edges first. Only a closed residual left neighborhood
-- whose old cover exceeds that remaining budget needs a different full cover.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2962_319 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsAO2 n C →
      circuitFun n C = NestedCover.graphFun G ∅ → IsLiftFixedPoint G C →
      let M := maximalCores G C
      let D := M.biUnion (gammaE G C)
      let cap := (M.biUnion (coneSet n C)).card + M.card
      cap < 2 * D.card → D.card ≤ cap) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsAO2 n C →
      circuitFun n C = NestedCover.graphFun G ∅ → IsLiftFixedPoint G C →
      let M := maximalCores G C
      let D := M.biUnion (gammaE G C)
      let b := (M.biUnion (coneSet n C)).card + M.card - D.card
      let R := G.deleteEdges (D : Set (Sym2 (Fin n)))
      let L := Finset.univ.filter (fun v => s v = false)
      let full := fun X : Finset (Fin n) => (L \ X) ∪ X.biUnion (fun i => G.neighborFinset i)
      let res := fun X : Finset (Fin n) => (L \ X) ∪ X.biUnion (fun i => R.neighborFinset i)
      (M.biUnion (coneSet n C)).card + M.card < 2 * D.card →
      ∀ X ⊆ L, (∀ w ∈ L, R.neighborFinset w ⊆ X.biUnion (fun i => R.neighborFinset i) → w ∈ X) →
        (res X).card + b < (full X).card →
        ∃ Y ⊆ L, (full Y).card ≤ (res X).card + b) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card := by
  intro edge exchange n G inst C s T V sides square ao computes fixed cover residual
  let M := maximalCores G C
  let D := M.biUnion (gammaE G C)
  let U := M.biUnion (coneSet n C)
  let R := G.deleteEdges (D : Set (Sym2 (Fin n)))
  let L := Finset.univ.filter (fun v => s v = false)
  let full := fun X : Finset (Fin n) => (L \ X) ∪ X.biUnion (fun i => G.neighborFinset i)
  let res := fun X : Finset (Fin n) => (L \ X) ∪ X.biUnion (fun i => R.neighborFinset i)
  let b := U.card + M.card - D.card
  change NestedCover.IsMinCover R V at residual
  change D.card + T.card ≤ U.card + M.card + V.card
  by_cases easy : 2 * D.card ≤ U.card + M.card
  · let ends := D.image (fun e => e.out.1)
    have extended : G.IsVertexCover (↑(V ∪ ends) : Set (Fin n)) := by
      intro u v uv
      by_cases gone : s(u,v) ∈ D
      · have picked : (s(u,v)).out.1 ∈ ends := Finset.mem_image.mpr ⟨s(u,v),gone,rfl⟩
        rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(u,v)) with p | p
        · exact Or.inl (Finset.mem_union_right _ (p ▸ picked))
        · exact Or.inr (Finset.mem_union_right _ (p ▸ picked))
      · have present : R.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨uv,gone⟩
        exact (residual.1 present).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    have c := cover.2 (V ∪ ends) extended
    have u := Finset.card_union_le V ends
    have e : ends.card ≤ D.card := Finset.card_image_le
    omega
  have dense : U.card + M.card < 2 * D.card := Nat.lt_of_not_ge easy
  have ec : D.card ≤ U.card + M.card := edge n G C s sides square ao computes fixed dense
  have ex : ∀ X ⊆ L, (∀ w ∈ L, R.neighborFinset w ⊆ X.biUnion (fun i => R.neighborFinset i) → w ∈ X) →
      (res X).card + b < (full X).card → ∃ Y ⊆ L, (full Y).card ≤ (res X).card + b :=
    exchange n G C s sides square ao computes fixed dense
  let X := L \ V
  have xl : X ⊆ L := Finset.sdiff_subset
  have neighbors : X.biUnion (fun i => R.neighborFinset i) ⊆ V := by
    intro w hw
    obtain ⟨v,hv,hvw⟩ := Finset.mem_biUnion.mp hw
    have hnv : v ∉ V := (Finset.mem_sdiff.mp hv).2
    exact (residual.1 ((R.mem_neighborFinset v w).mp hvw)).resolve_left hnv
  have small : res X ⊆ V := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · by_contra no
      exact (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h).1,no⟩)
    · exact neighbors h
  have closed : ∀ w ∈ L, R.neighborFinset w ⊆ X.biUnion (fun i => R.neighborFinset i) → w ∈ X := by
    intro w wl whole
    apply Finset.mem_sdiff.mpr
    refine ⟨wl,?_⟩
    intro member
    have canErase : R.IsVertexCover (↑(V.erase w) : Set (Fin n)) := by
      intro u v huv
      by_cases uw : u = w
      · subst u
        exact Or.inr (Finset.mem_erase.mpr ⟨huv.ne.symm,neighbors (whole ((R.mem_neighborFinset w v).mpr huv))⟩)
      by_cases vw : v = w
      · subst v
        exact Or.inl (Finset.mem_erase.mpr ⟨uw,neighbors (whole ((R.mem_neighborFinset w u).mpr huv.symm))⟩)
      rcases residual.1 huv with hu | hv
      · exact Or.inl (Finset.mem_erase.mpr ⟨uw,hu⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨vw,hv⟩)
    exact (Nat.not_lt_of_ge (residual.2 _ canErase)) (Finset.card_erase_lt_of_mem member)
  have covers (Y : Finset (Fin n)) : G.IsVertexCover (↑(full Y) : Set (Fin n)) := by
    intro u v uv
    have side (a d : Fin n) (ad : G.Adj a d) (al : a ∈ L) : a ∈ full Y ∨ d ∈ full Y := by
      by_cases ay : a ∈ Y
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a,ay,(G.mem_neighborFinset a d).mpr ad⟩))
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨al,ay⟩))
    have color := sides u v uv
    by_cases ul : s u = false
    · exact side u v uv (Finset.mem_filter.mpr ⟨Finset.mem_univ u,ul⟩)
    · have vl : s v = false := by
        cases hu : s u with
        | false => exact False.elim (ul hu)
        | true =>
          cases hv : s v with
          | false => rfl
          | true => exact False.elim (color (hu.trans hv.symm))
      exact (side v u uv.symm (Finset.mem_filter.mpr ⟨Finset.mem_univ v,vl⟩)).symm
  have step : T.card ≤ (res X).card + b := by
    by_cases ok : (full X).card ≤ (res X).card + b
    · exact (cover.2 _ (covers X)).trans ok
    · obtain ⟨Y,_,price⟩ := ex X xl closed (Nat.lt_of_not_ge ok)
      exact (cover.2 _ (covers Y)).trans price
  have rv := Finset.card_le_card small
  dsimp only [b] at step
  omega
