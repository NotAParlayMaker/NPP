import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_612_17
    (hnorm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (D : PEqualNP.CircuitLowerBounds.Circuit),
      G.edgeFinset.Nonempty →
      PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧ C.size ≤ D.size)
    (h0 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin n)),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = ∅ →
      G.edgeFinset.card + K.card ≤ C.size + 1)
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin n)) (g : ℕ),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = {g} →
      G.edgeFinset.card + K.card ≤ C.size + 1)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin n)),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      G.edgeFinset.card + K.card ≤ C.size + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G D hedge hno4 hcov hmin hmono heval
  have hne : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := hedge
    exact ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv⟩
  have hfour : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    refine Finset.card_le_one.mpr ?_
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨ha₁, hb₁⟩ := (Finset.mem_filter.mp hw₁).2
    obtain ⟨ha₂, hb₂⟩ := (Finset.mem_filter.mp hw₂).2
    by_contra hne12
    exact hno4 a w₁ b w₂ (G.ne_of_adj ha₁) hab (G.ne_of_adj ha₂) (G.ne_of_adj hb₁).symm
      hne12 (G.ne_of_adj hb₂) ha₁ hb₁.symm hb₂ ha₂.symm
  obtain ⟨K, hKcov, hKcard⟩ := hcov
  have hKmin : PEqualNP.MetaComplexity.NestedCover.IsMinCover G K := by
    refine ⟨?_, ?_⟩
    · intro u v huv
      exact hKcov u v huv
    · intro S hS
      rw [hKcard]
      exact hmin S (fun u v huv => hS huv)
  have hfun : PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change D.eval (List.ofFn x) = true ↔
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    rw [heval x]
    simp
  obtain ⟨C, hleast, htop, hle⟩ := hnorm n G D hne hmono hfun
  have hbound : G.edgeFinset.card + K.card ≤ C.size + 1 := by
    rcases hj : (PEqualNP.TopForm.junk G C).card with _ | _ | k
    · exact h0 n G C K hfour hne hKmin hleast htop (Finset.card_eq_zero.mp hj)
    · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hj
      exact h1 n G C K g hfour hne hKmin hleast htop hg
    · exact h2 n G C K hfour hne hKmin hleast htop (by omega)
  have hedg : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset G, Set.ncard_coe_finset]
  omega
