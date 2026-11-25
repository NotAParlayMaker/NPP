import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- At most two uncovered edges: the residual cover bound and the trace lemma close it.
-- Three or more: split by whether some junk AND lies in the cone of another junk AND.
-- If none does, every junk AND is read by a centreless top or an OR gate outside Lambda
-- (the reader lemma), and fan-in two gives at most two junk ANDs per such reader.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2258_654
    (hTrace : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      (∀ g ∈ D.gates, g.inputs.length = 2) →
      ∀ a ∈ tops G D, ∀ b : Fin 2, ∀ h ∈ junk G D,
        OrReaches n D (opnd D a b) h →
          a ∈ centreless G D ∨ (orN G D \ lam G D).Nonempty)
    (hReader : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      0 < n → IsLeastAO G D →
      ∀ h ∈ junk G D, ∃ k < D.gates.length, n + h ∈ (gateAt D k).inputs ∧ InCone n D h k ∧
        (gateAt D k).inputs.length = 2 ∧
        (k ∈ junk G D ∨ k ∈ centreless G D ∨ k ∈ orN G D \ lam G D))
    (hNested : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 11 ([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97].map
        fun e => (e / 11, e % 11)) →
      IsLeastAO G D → TopForm G D →
      let T := tops G D
      let V := centreless G D
      let J := junk G D
      let U := Ustar G D
      let R := orN G D \ lam G D
      (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side D a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J,
        gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) h ∧
        gateVal 11 D h (pairInput u v) = true) →
      15 + (T \ V).card + 2 * V.card + J.card + R.card ≤ D.size + U.card →
      (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ V).card) →
      3 ≤ U.card → 3 ≤ J.card →
      (∃ h1 ∈ J, ∃ h2 ∈ J, InCone 11 D h1 h2) → 22 ≤ D.size)
    (hFlat : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 11 ([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97].map
        fun e => (e / 11, e % 11)) →
      IsLeastAO G D → TopForm G D →
      let T := tops G D
      let V := centreless G D
      let J := junk G D
      let U := Ustar G D
      let R := orN G D \ lam G D
      (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side D a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J,
        gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) h ∧
        gateVal 11 D h (pairInput u v) = true) →
      15 + (T \ V).card + 2 * V.card + J.card + R.card ≤ D.size + U.card →
      (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ V).card) →
      3 ≤ U.card → 3 ≤ J.card →
      (∀ h1 ∈ J, ∀ h2 ∈ J, ¬ InCone 11 D h1 h2) → J.card ≤ 2 * (V ∪ R).card →
      22 ≤ D.size) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x7 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x8 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;         have x10 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x11 ∈ x7,             have x13 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x11;             (∀ x14 ∈ x13 (0 : Fin (2 : ℕ)), ∀ x16 ∈ x13 (1 : Fin (2 : ℕ)), x1.Adj x14 x16) ∧ ((x13 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x13 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x12 x13 : Fin (11 : ℕ)), s(x12, x13) ∈ x10 → ∃ x15 ∈ x7, ∃ (x16 : Fin (2 : ℕ)), ∃ x17 ∈ x9, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x15 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x15 x16) x17 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true) → (15 : ℕ) + (x7 \ x8).card + (2 : ℕ) * x8.card + x9.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x10.card → (∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x14 → x14.card ≤ (x7 \ x8).card) → (3 : ℕ) ≤ x9.card → (22 : ℕ) ≤ x3.size := by
  intro G _ D hG hLeast hTop
  dsimp only
  intro hStars hOff hCount hCoverBound hJunk
  let rawPairs : List (ℕ × ℕ) :=
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let edgePairs : Finset (Fin 11 × Fin 11) :=
    {(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)}
  have hPairsAdj : ∀ p ∈ edgePairs, (edgeGraph 11 rawPairs).Adj p.1 p.2 := by decide
  have hPairsLt : ∀ p ∈ edgePairs, p.1 < p.2 := by decide
  have hCheckAll : ∀ K : Finset (Fin 11),
      7 ≤ K.card + (edgePairs.filter (fun p => p.1 ∉ K ∧ p.2 ∉ K)).card := by
    decide
  classical
  let U := Ustar G D
  let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
  let covers : Finset (Finset (Fin 11)) :=
    Finset.univ.filter (fun K : Finset (Fin 11) => H.IsVertexCover (↑K : Set (Fin 11)))
  have hCovers : covers.Nonempty := by
    refine ⟨(Finset.univ : Finset (Fin 11)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro u _ _
    exact Or.inl (Finset.mem_univ u)
  exact Exists.elim (Finset.exists_min_image covers Finset.card hCovers) fun K hK_rest => by
    have hKMin : IsMinCover H K :=
      ⟨(Finset.mem_filter.mp hK_rest.1).2, fun A hA =>
        hK_rest.2 A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)⟩
    have hKT : K.card ≤ (tops G D \ centreless G D).card := hCoverBound K hKMin
    let missed : Finset (Fin 11 × Fin 11) := edgePairs.filter (fun p => p.1 ∉ K ∧ p.2 ∉ K)
    let toSym : Fin 11 × Fin 11 → Sym2 (Fin 11) := fun p => s(p.1, p.2)
    have hSubU : missed.image toSym ⊆ U := by
      intro e he
      exact Exists.elim (Finset.mem_image.mp he) fun p hp => by
        rw [← hp.2]
        have hp_mem := (Finset.mem_filter.mp hp.1).1
        have hp_not := (Finset.mem_filter.mp hp.1).2
        have hadjG : G.Adj p.1 p.2 := by rw [hG]; exact hPairsAdj p hp_mem
        by_contra hnotU
        have hadjH : H.Adj p.1 p.2 := SimpleGraph.deleteEdges_adj.mpr ⟨hadjG, hnotU⟩
        exact (hKMin.1 hadjH).elim hp_not.1 hp_not.2
    have hInjSym : Set.InjOn toSym ↑missed := by
      intro p1 h1 p2 h2 heq
      have lt1 := hPairsLt p1 (Finset.mem_filter.mp h1).1
      have lt2 := hPairsLt p2 (Finset.mem_filter.mp h2).1
      exact (Sym2.eq_iff.mp heq).elim
        (fun h => Prod.ext h.1 h.2)
        (fun h => absurd (lt_trans (h.1 ▸ lt1) (h.2 ▸ lt2)) (lt_irrefl _))
    have hMissedLeU : missed.card ≤ U.card := by
      rw [← Finset.card_image_of_injOn hInjSym]
      exact Finset.card_le_card hSubU
    have hChk := hCheckAll K
    rw [Finset.filter_congr_decidable] at hChk
    have h7 : 7 ≤ K.card + U.card := by
      have h7m : 7 ≤ K.card + missed.card := hChk
      omega
    change 15 + (tops G D \ centreless G D).card + 2 * (centreless G D).card + (junk G D).card +
      (orN G D \ lam G D).card ≤ D.size + U.card at hCount
    change 3 ≤ (junk G D).card at hJunk
    have hG' : G = edgeGraph 11 ([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97].map
        fun e => (e / 11, e % 11)) := by
      rw [hG]
      rfl
    have hFan : ∀ g ∈ D.gates, g.inputs.length = 2 := hLeast.1.2.2
    have hTr : U.Nonempty → 1 ≤ 2 * (centreless G D).card + (orN G D \ lam G D).card := by
      intro hne
      obtain ⟨e, he⟩ := hne
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨a, ha, b, h, hh, _, hr, _⟩ := hOff u v he
        rcases hTrace 11 G D hFan a ha b h hh hr with hc | ho
        · have := Finset.card_pos.mpr ⟨a, hc⟩
          omega
        · have := Finset.card_pos.mpr ho
          omega
    by_cases hle1 : U.card ≤ 1
    · omega
    · by_cases heq2 : U.card = 2
      · have hne : U.Nonempty := Finset.card_pos.mp (by omega)
        have := hTr hne
        by_contra hlt
        omega
      · have hge3 : 3 ≤ U.card := by omega
        by_cases hnest : ∃ h1 ∈ junk G D, ∃ h2 ∈ junk G D, InCone 11 D h1 h2
        · exact hNested G D hG' hLeast hTop hStars hOff hCount hCoverBound hge3 hJunk hnest
        · have hflat : ∀ h1 ∈ junk G D, ∀ h2 ∈ junk G D, ¬ InCone 11 D h1 h2 := by
            intro h1 hh1 h2 hh2 hin
            exact hnest ⟨h1, hh1, h2, hh2, hin⟩
          let J := junk G D
          let W := centreless G D ∪ (orN G D \ lam G D)
          let f : ℕ → ℕ := fun h =>
            if hh : h ∈ J then Classical.choose (hReader 11 G D (by norm_num) hLeast h hh) else 0
          have hspec : ∀ h (hh : h ∈ J), 11 + h ∈ (gateAt D (f h)).inputs ∧
              (gateAt D (f h)).inputs.length = 2 ∧ f h ∈ W := by
            intro h hh
            have hs := Classical.choose_spec (hReader 11 G D (by norm_num) hLeast h hh)
            have hf : f h = Classical.choose (hReader 11 G D (by norm_num) hLeast h hh) :=
              dite_eq_left hh
            rw [hf]
            obtain ⟨_, hin, hcone, hlen, hcls⟩ := hs
            refine ⟨hin, hlen, ?_⟩
            rcases hcls with hj | hc | ho
            · exact absurd hcone (hflat h hh _ hj)
            · exact Finset.mem_union_left _ hc
            · exact Finset.mem_union_right _ ho
          have hmaps : ∀ h ∈ J, f h ∈ W := fun h hh => (hspec h hh).2.2
          have hfib : ∀ k ∈ W, (J.filter (fun h => f h = k)).card ≤ 2 := by
            intro k _
            let S := J.filter (fun h => f h = k)
            by_cases hS : S.Nonempty
            · obtain ⟨h0, hh0⟩ := hS
              have hh0J := (Finset.mem_filter.mp hh0).1
              have hk0 := (Finset.mem_filter.mp hh0).2
              have hlen : (gateAt D k).inputs.length = 2 := by
                have := (hspec h0 hh0J).2.1
                rw [hk0] at this
                exact this
              have hsub : S.image (fun h => 11 + h) ⊆ (gateAt D k).inputs.toFinset := by
                intro w hw
                obtain ⟨h, hhS, rfl⟩ := Finset.mem_image.mp hw
                have hhJ := (Finset.mem_filter.mp hhS).1
                have hk := (Finset.mem_filter.mp hhS).2
                have := (hspec h hhJ).1
                rw [hk] at this
                exact List.mem_toFinset.mpr this
              have hinj : Set.InjOn (fun h : ℕ => 11 + h) ↑S := by
                intro a _ b _ hab
                simp only at hab
                omega
              have h1 := Finset.card_image_of_injOn hinj
              have h2 := Finset.card_le_card hsub
              have h3 := List.toFinset_card_le (gateAt D k).inputs
              change S.card ≤ 2
              omega
            · rw [Finset.not_nonempty_iff_eq_empty] at hS
              change S.card ≤ 2
              rw [hS]
              simp
          have hbound : J.card ≤ 2 * W.card :=
            Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfib
          exact hFlat G D hG' hLeast hTop hStars hOff hCount hCoverBound hge3 hJunk hflat hbound
