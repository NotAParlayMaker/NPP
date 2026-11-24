import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2962_417
    (hOr : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card ≤
        {j | j ∈ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C) ∧
          (gateAt C j).op = GateOp.or}.ncard + (PEqualNP.Core.maximalCores G C).card)
    (hAnd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      ∃ S : Finset (Fin n),
        (∀ e ∈ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C), ∃ v ∈ S, v ∈ e) ∧
        S.card ≤ {j | j ∈ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C) ∧
          (gateAt C j).op = GateOp.and}.ncard) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card := by
  classical
  intro n G _ C s T T' hbip h4 hao hfun hfix hT hT'
  have h1 := hOr n G C s hbip h4 hao hfun hfix
  obtain ⟨S, hS, h2⟩ := hAnd n G C s hbip h4 hao hfun hfix
  set M := PEqualNP.Core.maximalCores G C
  set D := M.biUnion (PEqualNP.TopForm.gammaE G C)
  set U := M.biUnion (PEqualNP.Core.coneSet n C)
  have h3 : {j | j ∈ U ∧ (gateAt C j).op = GateOp.or}.ncard +
      {j | j ∈ U ∧ (gateAt C j).op = GateOp.and}.ncard ≤ U.card := by
    have hdisj : Disjoint {j | j ∈ U ∧ (gateAt C j).op = GateOp.or}
        {j | j ∈ U ∧ (gateAt C j).op = GateOp.and} := by
      rw [Set.disjoint_left]
      rintro j ⟨_, ha⟩ ⟨_, hb⟩
      rw [ha] at hb
      cases hb
    have hfo : {j | j ∈ U ∧ (gateAt C j).op = GateOp.or}.Finite :=
      (Finset.finite_toSet U).subset fun j hj => hj.1
    have hfa : {j | j ∈ U ∧ (gateAt C j).op = GateOp.and}.Finite :=
      (Finset.finite_toSet U).subset fun j hj => hj.1
    rw [← Set.ncard_union_eq hdisj hfo hfa, ← Set.ncard_coe_finset U]
    apply Set.ncard_le_ncard _ (Finset.finite_toSet U)
    rintro j (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
  have hcov : G.IsVertexCover ((T' ∪ S : Finset (Fin n)) : Set (Fin n)) := by
    intro u v huv
    by_cases hD : s(u, v) ∈ D
    · obtain ⟨w, hw, hwe⟩ := hS _ hD
      rcases Sym2.mem_iff.mp hwe with rfl | rfl
      · left; simp [hw]
      · right; simp [hw]
    · have hadj : (G.deleteEdges ((D : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv, by simpa using hD⟩
      rcases hT'.1 hadj with h | h
      · left; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at h ⊢; exact Or.inl h
      · right; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at h ⊢; exact Or.inl h
  have hTle := hT.2 _ hcov
  have hu := Finset.card_union_le T' S
  omega
