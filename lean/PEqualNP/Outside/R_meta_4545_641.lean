import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Reserve the endpoints of the matched uncovered edges, then trim the star cover.
-- When its size still exceeds the budget, replace a subset by vertices covering its neighbors.
theorem PEqualNP.Outside.R_meta_4545_641
    (starEstimate : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (residualCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      (∀ D : Circuit, IsLeastAO G D → TopForm G D → (Ustar G C).card ≤ (Ustar G D).card) →
      (∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) →
      (∀ u, (G.neighborSet u).ncard ≠ 1) →
      let U := Ustar G C
      let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      ∀ R : Finset (Sym2 (Fin n)), R ⊆ U →
        (∀ e ∈ R, ∀ f ∈ R, ∀ v ∈ e, v ∈ f → e = f) →
        let H := G.deleteEdges {d | d ∈ U ∨ ∃ e ∈ R, ∃ v ∈ e, v ∈ d}
        ∀ K : Finset (Fin n), H.IsVertexCover ↑K → K.card ≤ (tops G C \ centreless G C).card →
          let budget := (tops G C \ centreless G C).card + B
          budget < U.card + R.card + K.card →
          ∃ S ⊆ K, ∃ X : Finset (Fin n),
            (∀ u ∈ S, ∀ v, H.Adj u v → v ∈ K \ S ∨ v ∈ X) ∧
            U.card + R.card + K.card + X.card ≤ budget + S.card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x1 × Fin x1)), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x10 → PEqualNP.TopForm.TopForm x2 x10 → (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.Ustar x2 x10).card) → (∃ (x11 : Fin x1 → Bool), ∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x11 x12 ≠ x11 x13) → (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard ≠ (1 : ℕ)) → (∀ x13 ∈ x5, x2.Adj x13.1 x13.2) → (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) → (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) → (∀ x16 ∈ x5, ∀ x18 ∈ x5, x16.1 ≠ x18.2) → (PEqualNP.TopForm.Ustar x2 x4).card + x5.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  classical
  intro n G _ C T h4 hne hleast htop hmin hcolor hdeg hadj hleft hright hcross
  let edge := fun p : Fin n × Fin n => s(p.1, p.2)
  let M := T.image edge
  let U := Ustar G C
  let R := M ∩ U
  let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  have endpoint : ∀ p ∈ T, ∀ q ∈ T, ∀ v ∈ edge p, v ∈ edge q → p = q := by
    intro p hp q hq v hv hw
    rcases Sym2.mem_iff.mp hv with hv | hv <;> rcases Sym2.mem_iff.mp hw with hw | hw
    · exact hleft _ hp _ hq (hv.symm.trans hw)
    · exact (hcross _ hp _ hq (hv.symm.trans hw)).elim
    · exact (hcross _ hq _ hp (hw.symm.trans hv)).elim
    · exact hright _ hp _ hq (hv.symm.trans hw)
  have hcard : M.card = T.card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq he
    exact endpoint p hp q hq p.1 (Sym2.mem_mk_left ..) (he ▸ Sym2.mem_mk_left ..)
  have matching : ∀ e ∈ M, ∀ f ∈ M, ∀ v ∈ e, v ∈ f → e = f := by
    intro e he f hf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
    intro v hv hw
    exact congrArg edge (endpoint p hp q hq v hv hw)
  have hRM : R ⊆ M := Finset.inter_subset_left
  have hRU : R ⊆ U := Finset.inter_subset_right
  obtain ⟨K, hcover, hbudget⟩ : ∃ K : Finset (Fin n),
      (∀ u v, (G.deleteEdges ↑U).Adj u v → (∀ e ∈ R, u ∉ e ∧ v ∉ e) → u ∈ K ∨ v ∈ K) ∧
      U.card + R.card + K.card ≤ (tops G C \ centreless G C).card + B := by
    let H := G.deleteEdges {d | d ∈ U ∨ ∃ e ∈ R, ∃ v ∈ e, v ∈ d}
    have haiff (u v : Fin n) : H.Adj u v ↔
        (G.deleteEdges ↑U).Adj u v ∧ ∀ e ∈ R, u ∉ e ∧ v ∉ e := by
      constructor
      · intro ha
        obtain ⟨had, hdel⟩ := SimpleGraph.deleteEdges_adj.mp ha
        refine ⟨SimpleGraph.deleteEdges_adj.mpr ⟨had, fun hu => hdel (Or.inl hu)⟩, ?_⟩
        intro e he
        exact ⟨fun hu => hdel (Or.inr ⟨e, he, u, hu, Sym2.mem_mk_left ..⟩),
          fun hv => hdel (Or.inr ⟨e, he, v, hv, Sym2.mem_mk_right ..⟩)⟩
      · rintro ⟨ha, free⟩
        obtain ⟨had, hout⟩ := SimpleGraph.deleteEdges_adj.mp ha
        refine SimpleGraph.deleteEdges_adj.mpr ⟨had, ?_⟩
        rintro (hu | ⟨e, he, w, hw, hwuv⟩)
        · exact hout hu
        · rcases Sym2.mem_iff.mp hwuv with rfl | rfl
          · exact (free e he).1 hw
          · exact (free e he).2 hw
    let H₀ := G.deleteEdges ↑U
    let P := fun k : ℕ => ∃ K : Finset (Fin n), H₀.IsVertexCover ↑K ∧ K.card = k
    have hex : ∃ k, P k := ⟨_, Finset.univ, by simp, rfl⟩
    obtain ⟨K₀, hK₀, hcard₀⟩ := Nat.find_spec hex
    have hleast₀ : PEqualNP.MetaComplexity.NestedCover.IsMinCover H₀ K₀ :=
      ⟨hK₀, fun S hS => hcard₀ ▸ Nat.find_min' hex ⟨S, hS, rfl⟩⟩
    have hk₀ := (starEstimate n G C h4 hne hleast htop).2 K₀ hleast₀
    let K := K₀.filter fun v => ∀ e ∈ R, v ∉ e
    have hk : K.card ≤ (tops G C \ centreless G C).card :=
      (Finset.card_le_card (Finset.filter_subset ..)).trans hk₀
    have hK : H.IsVertexCover ↑K := by
      intro u v ha
      obtain ⟨ha', free⟩ := (haiff u v).mp ha
      rcases hK₀ ha' with hu | hv
      · exact Or.inl (Finset.mem_filter.mpr ⟨hu, fun e he => (free e he).1⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hv, fun e he => (free e he).2⟩)
    by_cases hpay : U.card + R.card + K.card ≤ (tops G C \ centreless G C).card + B
    · exact ⟨K, fun u v ha free => hK ((haiff u v).mpr ⟨ha, free⟩), hpay⟩
    · obtain ⟨S, hSK, X, hreplace, hsize⟩ :=
        residualCover n G C h4 hne hleast htop hmin hcolor hdeg R hRU
          (fun e he f hf => matching e (hRM he) f (hRM hf)) K hK hk (Nat.lt_of_not_ge hpay)
      refine ⟨(K \ S) ∪ X, ?_, ?_⟩
      · intro u v ha free
        have hh := (haiff u v).mpr ⟨ha, free⟩
        rcases hK hh with hu | hv
        · by_cases hs : u ∈ S
          · exact Or.inr (Finset.mem_union.mpr (hreplace u hs v hh))
          · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu, hs⟩))
        · by_cases hs : v ∈ S
          · exact Or.inl (Finset.mem_union.mpr (hreplace v hs u hh.symm))
          · exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hs⟩))
      · have hunion := Finset.card_union_le (K \ S) X
        have hdiff := Finset.card_sdiff_add_card_eq_card hSK
        change U.card + R.card + K.card + X.card ≤ (tops G C \ centreless G C).card + B + S.card at hsize
        omega
  have hit : ∀ e ∈ M \ R, ∃ v ∈ K, v ∈ e := by
    intro e he
    obtain ⟨hem, her⟩ := Finset.mem_sdiff.mp he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hem
    have hout : edge p ∉ U := fun hu => her (Finset.mem_inter.mpr ⟨hem, hu⟩)
    have free : ∀ f ∈ R, p.1 ∉ f ∧ p.2 ∉ f := by
      intro f hf
      constructor
      · intro hv
        exact her ((matching _ hem _ (hRM hf) _ (Sym2.mem_mk_left ..) hv).symm ▸ hf)
      · intro hv
        exact her ((matching _ hem _ (hRM hf) _ (Sym2.mem_mk_right ..) hv).symm ▸ hf)
    rcases hcover p.1 p.2 (SimpleGraph.deleteEdges_adj.mpr ⟨hadj p hp, hout⟩) free with h | h
    · exact ⟨p.1, h, Sym2.mem_mk_left ..⟩
    · exact ⟨p.2, h, Sym2.mem_mk_right ..⟩
  choose pick hK hmem using hit
  have hbound : (M \ R).card ≤ K.card := by
    let select : ↥(M \ R) → ↥K := fun e => ⟨pick e.val e.property, hK e.val e.property⟩
    apply Finset.card_le_card_of_injective (f := select)
    intro e f heq
    have hv : pick e.val e.property = pick f.val f.property := congrArg Subtype.val heq
    apply Subtype.ext
    exact matching _ (Finset.mem_sdiff.mp e.property).1 _ (Finset.mem_sdiff.mp f.property).1 _
      (hmem e.val e.property) (hv ▸ hmem f.val f.property)
  have hsum := Finset.card_sdiff_add_card_eq_card hRM
  change U.card + T.card ≤ _
  dsimp only [B] at hbudget
  omega
