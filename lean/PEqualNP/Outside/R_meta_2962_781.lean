import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2962_781
  (single : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → ∀ g ∈ PEqualNP.Core.maximalCores G C, ∃ S : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.gammaE G C g, ∃ v ∈ S, v ∈ e) ∧ (PEqualNP.TopForm.gammaE G C g).card + S.card ≤ (PEqualNP.Core.coneSet n C g).card + 1)
  (shared : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∃ g ∈ PEqualNP.Core.maximalCores G C, ∃ h ∈ PEqualNP.Core.maximalCores G C, g ≠ h ∧ (PEqualNP.Core.coneSet n C g ∩ PEqualNP.Core.coneSet n C h).Nonempty) → ∃ S : Finset (Fin n), (∀ e ∈ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C), ∃ v ∈ S, v ∈ e) ∧ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + S.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card) :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := by
  intro n G _ C s T T' hs hC4 hAO hF hfix hT hT'
  classical
  obtain ⟨S, hScov, hScard⟩ : ∃ S : Finset (Fin n),
      (∀ e ∈ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C), ∃ v ∈ S, v ∈ e) ∧
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + S.card ≤
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card +
          (PEqualNP.Core.maximalCores G C).card := by
    by_cases hsh : ∃ g ∈ PEqualNP.Core.maximalCores G C, ∃ h ∈ PEqualNP.Core.maximalCores G C,
        g ≠ h ∧ (PEqualNP.Core.coneSet n C g ∩ PEqualNP.Core.coneSet n C h).Nonempty
    · exact shared n G C s hs hC4 hAO hF hfix hsh
    · have hdisj : ((PEqualNP.Core.maximalCores G C : Finset ℕ) : Set ℕ).PairwiseDisjoint
          (PEqualNP.Core.coneSet n C) := by
        intro g hg h hh hne
        rw [Function.onFun, Finset.disjoint_iff_inter_eq_empty]
        by_contra hne'
        exact hsh ⟨g, hg, h, hh, hne, Finset.nonempty_iff_ne_empty.mpr hne'⟩
      have hU := Finset.card_biUnion hdisj
      let Sf : ℕ → Finset (Fin n) := fun g =>
        if hg : g ∈ PEqualNP.Core.maximalCores G C then
          Classical.choose (single n G C s hs hC4 hAO hF hfix g hg) else ∅
      have hSf : ∀ g ∈ PEqualNP.Core.maximalCores G C,
          (∀ e ∈ PEqualNP.TopForm.gammaE G C g, ∃ v ∈ Sf g, v ∈ e) ∧
            (PEqualNP.TopForm.gammaE G C g).card + (Sf g).card ≤
              (PEqualNP.Core.coneSet n C g).card + 1 := by
        intro g hg
        simp only [Sf, hg, ↓reduceDIte]
        exact Classical.choose_spec (single n G C s hs hC4 hAO hF hfix g hg)
      refine ⟨(PEqualNP.Core.maximalCores G C).biUnion Sf, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_biUnion] at he
        obtain ⟨g, hg, heg⟩ := he
        obtain ⟨v, hv, hve⟩ := (hSf g hg).1 e heg
        exact ⟨v, Finset.mem_biUnion.2 ⟨g, hg, hv⟩, hve⟩
      · have h1 := Finset.card_biUnion_le (s := PEqualNP.Core.maximalCores G C)
          (t := PEqualNP.TopForm.gammaE G C)
        have h2 := Finset.card_biUnion_le (s := PEqualNP.Core.maximalCores G C) (t := Sf)
        have h3 : ∑ g ∈ PEqualNP.Core.maximalCores G C,
            ((PEqualNP.TopForm.gammaE G C g).card + (Sf g).card) ≤
            ∑ g ∈ PEqualNP.Core.maximalCores G C, ((PEqualNP.Core.coneSet n C g).card + 1) :=
          Finset.sum_le_sum fun g hg => (hSf g hg).2
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
          mul_one] at h3
        omega
  have hcov : G.IsVertexCover ((T' ∪ S : Finset (Fin n)) : Set (Fin n)) := by
    intro u v huv
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    by_cases hD : s(u, v) ∈ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)
    · obtain ⟨w, hw, hwe⟩ := hScov _ hD
      rcases Sym2.mem_iff.1 hwe with rfl | rfl
      · exact Or.inl (Or.inr hw)
      · exact Or.inr (Or.inr hw)
    · have hadj : (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion
          (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj, Finset.mem_coe]
        exact ⟨huv, hD⟩
      rcases hT'.1 hadj with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
  have hTle := hT.2 _ hcov
  have hun := Finset.card_union_le T' S
  omega
