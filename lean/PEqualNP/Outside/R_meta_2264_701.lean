import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2264_701
    (routing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → PEqualNP.TopForm.junk G C = {i,j} → ¬ PEqualNP.EdgeOwnership.InCone n C i j → ¬ PEqualNP.EdgeOwnership.InCone n C j i → ∀ h ∈ PEqualNP.TopForm.junk G C, ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h)
    (path_cost : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ i j : ℕ, i ∈ PEqualNP.TopForm.junk G C → j ∈ PEqualNP.TopForm.junk G C → (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) i) → (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) j) → (∀ a ∈ PEqualNP.TopForm.tops G C, PEqualNP.EdgeOwnership.InCone n C i a → ¬ PEqualNP.EdgeOwnership.InCone n C j a) → 2 ≤ 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)
    (charge : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → i < j → PEqualNP.TopForm.junk G C = {i,j} → ¬ PEqualNP.EdgeOwnership.InCone 11 C i j → ¬ PEqualNP.EdgeOwnership.InCone 11 C j i → (∀ a ∈ PEqualNP.TopForm.tops G C, PEqualNP.EdgeOwnership.InCone 11 C i a → ¬ PEqualNP.EdgeOwnership.InCone 11 C j a) → C.size ≤ 21 → let U := PEqualNP.TopForm.Ustar G C; 3 ≤ U.card → ∃ K A : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧ (∀ u v : Fin 11, s(u,v) ∈ U → u ∈ K ∪ A ∨ v ∈ K ∪ A) ∧ A.card + U.card ≤ 2 * (PEqualNP.TopForm.centreless G C).card + 2 + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by

  intro G inst C i j hG hLeast hTop
  dsimp only
  intro hStars hSource hCount hCover hij hJ hnoij hnoji hApart
  classical
  let U := PEqualNP.TopForm.Ustar G C
  let V := PEqualNP.TopForm.centreless G C
  let R := PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C
  let t := (PEqualNP.TopForm.tops G C \ V).card
  change 17 + t + 2 * V.card + R.card ≤ C.size + U.card at hCount
  have h7 : ∀ K : Finset (Fin 11), G.IsVertexCover (K : Set (Fin 11)) → 7 ≤ K.card := by
    subst G
    let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    intro K hK
    classical
    let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
    have ew (u v : Fin 11) (he : G.Adj u v) : 1 ≤ w u + w v := by
      rcases hK he with hu | hv
      · change u ∈ K at hu
        simp [w, hu]
      · change v ∈ K at hv
        simp [w, hv]
    have e0 := ew 1 4 (by
      change (1 : Fin 11) ≠ 4 ∧ ((1,4) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (4,1) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e1 := ew 4 8 (by
      change (4 : Fin 11) ≠ 8 ∧ ((4,8) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (8,4) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e2 := ew 8 1 (by
      change (8 : Fin 11) ≠ 1 ∧ ((8,1) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (1,8) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e3 := ew 3 6 (by
      change (3 : Fin 11) ≠ 6 ∧ ((3,6) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (6,3) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e4 := ew 6 7 (by
      change (6 : Fin 11) ≠ 7 ∧ ((6,7) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (7,6) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e5 := ew 7 3 (by
      change (7 : Fin 11) ≠ 3 ∧ ((7,3) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (3,7) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e6 := ew 0 9 (by
      change (0 : Fin 11) ≠ 9 ∧ ((0,9) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (9,0) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e7 := ew 9 5 (by
      change (9 : Fin 11) ≠ 5 ∧ ((9,5) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (5,9) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e8 := ew 5 2 (by
      change (5 : Fin 11) ≠ 2 ∧ ((5,2) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (2,5) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e9 := ew 2 10 (by
      change (2 : Fin 11) ≠ 10 ∧ ((2,10) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (10,2) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have e10 := ew 10 0 (by
      change (10 : Fin 11) ≠ 0 ∧ ((10,0) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∨ (0,10) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)))
      decide +kernel)
    have hw : ∑ i, w i = K.card := by
      simp [w]
    rw [Fin.sum_univ_succ] at hw
    simp [Fin.sum_univ_succ] at hw
    omega

  have residual (K : Finset (Fin 11))
      (hK : (G.deleteEdges (↑U)).IsVertexCover (↑K : Set (Fin 11))) :
      7 ≤ K.card + U.card := by
    let X := U.image (fun e => e.out.1)
    have hx : X.card ≤ U.card := Finset.card_image_le
    have hfull : G.IsVertexCover (↑(K ∪ X)) := by
      intro u v huv
      by_cases eh : s(u,v) ∈ U
      · have hvx : s(u,v).out.1 ∈ X := Finset.mem_image_of_mem _ eh
        have hh := Sym2.out_fst_mem s(u,v)
        rw [Sym2.mem_iff] at hh
        rcases hh with h | h
        · exact Or.inl (Finset.mem_union_right _ (h ▸ hvx))
        · exact Or.inr (Finset.mem_union_right _ (h ▸ hvx))
      · have hh : (G.deleteEdges (↑U)).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, eh⟩
        rcases hK hh with h | h
        · exact Or.inl (Finset.mem_union_left X h)
        · exact Or.inr (Finset.mem_union_left X h)
    have score := h7 _ hfull
    have card := Finset.card_union_le K X
    omega
  by_contra hShort
  have hSize : C.size ≤ 21 := by omega
  have routes := routing 11 G C i j hLeast hTop hJ hnoij hnoji
  have hi : i ∈ PEqualNP.TopForm.junk G C := by rw [hJ]; simp
  have hj : j ∈ PEqualNP.TopForm.junk G C := by rw [hJ]; simp
  have budget := path_cost 11 G C hLeast.1 i j hi hj (routes i hi) (routes j hj) hApart
  change 2 ≤ 2 * V.card + R.card at budget
  have large : 3 ≤ U.card := by
    let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
    let P := fun k : ℕ => ∃ K : Finset (Fin 11), H.IsVertexCover (↑K : Set _) ∧ K.card = k
    have ex : ∃ k, P k := ⟨11, Finset.univ, by simp [SimpleGraph.IsVertexCover], by simp⟩
    obtain ⟨K, covers, hk⟩ := Nat.find_spec ex
    have hMin : PEqualNP.MetaComplexity.NestedCover.IsMinCover H K := by
      refine ⟨covers, ?_⟩
      intro A ha
      rw [hk]
      exact Nat.find_min' ex (show P A.card from ⟨A, ha, rfl⟩)
    have hK := hCover K hMin
    change K.card ≤ t at hK
    have hRes := residual K covers
    omega
  have lift : ∃ K A : Finset (Fin 11),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K ∧
      (∀ u v : Fin 11, s(u,v) ∈ U → u ∈ K ∪ A ∨ v ∈ K ∪ A) ∧
      A.card + U.card ≤ 2 * V.card + 2 + R.card := by
    exact charge G C i j hG hLeast hTop hij hJ hnoij hnoji hApart hSize large
  obtain ⟨K, A, hMin, hA, hCost⟩ := lift
  have hFull : G.IsVertexCover (↑(K ∪ A) : Set (Fin 11)) := by
    intro u v hadj
    by_cases hDel : s(u,v) ∈ U
    · exact hA u v hDel
    · have he : (G.deleteEdges ↑U).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hDel⟩
      exact (hMin.1 he).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
  have hFullBound := h7 _ hFull
  have hUnion := Finset.card_union_le K A
  have hK := hCover K hMin
  change K.card ≤ t at hK
  omega
