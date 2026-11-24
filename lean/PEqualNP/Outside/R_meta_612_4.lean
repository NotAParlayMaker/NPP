import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_612_4
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G.edgeFinset.Nonempty →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n C' ∧
        PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        C'.size ≤ C.size)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C' ∧
        PEqualNP.TopForm.TopForm G C' ∧
        PEqualNP.TopForm.junk G C' = ∅)
    (h3 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin n)),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = ∅ →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
      G.edgeFinset.card + K.card ≤ C.size + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G C hedge hfour hSc hmin hmono heval
  obtain ⟨u0, v0, huv0⟩ := hedge
  obtain ⟨S, hS, hSt⟩ := hSc
  have hne : G.edgeFinset.Nonempty := ⟨s(u0, v0), by simp [SimpleGraph.mem_edgeFinset, huv0]⟩
  have h4 : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    by_contra hgt
    have htwo : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card := Nat.lt_of_not_ge hgt
    obtain ⟨w1, hw1, w2, hw2, hw12⟩ := Finset.one_lt_card.mp htwo
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    have haw1 : a ≠ w1 := G.ne_of_adj hw1.1
    have hbw1 : b ≠ w1 := G.ne_of_adj hw1.2
    have haw2 : a ≠ w2 := G.ne_of_adj hw2.1
    have hbw2 : b ≠ w2 := G.ne_of_adj hw2.2
    exact hfour a w1 b w2 haw1 hab haw2 hbw1.symm hw12 hbw2
      hw1.1 hw1.2.symm hw2.2 hw2.1.symm
  have hfun : PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    change C.eval (List.ofFn x) = true ↔
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact heval x
  obtain ⟨C1, hAO1, hfun1, hle1⟩ := h1 n G C hne hmono hfun
  have hex : ∃ m : ℕ, ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C' ∧
      PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      C'.size = m := ⟨C1.size, C1, hAO1, hfun1, rfl⟩
  let m0 := Nat.find hex
  obtain ⟨Cmin, hAOmin, hfunmin, hszmin⟩ := Nat.find_spec hex
  have hleast : PEqualNP.TopForm.IsLeastAO G Cmin := by
    refine ⟨hAOmin, hfunmin, ?_⟩
    intro C' hAO' hfun'
    rw [hszmin]
    exact Nat.find_min' hex ⟨C', hAO', hfun', rfl⟩
  have hmin_le : Cmin.size ≤ C.size := le_trans (hleast.2.2 C1 hAO1 hfun1) hle1
  obtain ⟨C', hleast', htf', hjunk'⟩ := h2 n G Cmin h4 hne hleast
  have hC'_le : C'.size ≤ Cmin.size := hleast'.2.2 Cmin hAOmin hfunmin
  have hminS : PEqualNP.MetaComplexity.NestedCover.IsMinCover G S := by
    refine ⟨?_, ?_⟩
    · intro u v huv
      exact hS u v huv
    · intro T' hT'
      rw [hSt]
      exact hmin T' (fun u v huv => hT' huv)
  have hbd := h3 n G C' S h4 hne hleast' htf' hjunk' hminS
  have hcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset G, Set.ncard_coe_finset]
  omega
