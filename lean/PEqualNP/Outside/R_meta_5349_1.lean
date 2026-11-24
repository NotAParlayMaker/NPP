import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

-- The finite peeling argument adapts the checked reduction by You can call me Glenn,
-- R_meta_1768_417 at commit 6d432048194b883713b4b8fa32fd41862824ebe8.
-- The shallow-gate bound is proved separately by localizing Adrian Gonzalez's
-- L_meta_3805 at commit b8c7d50c23775b2c057b3057b7512e7aed12c42b.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5349_1
    (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), IsLeastAO G C → G.support.ncard ≤ C.size+1)
    (shallow : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsLeastAO G C → TopForm G C →
      {e ∈ Ustar G C | ∃ u v : Fin n, e = s(u,v) ∧ ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
        (∀ h ∈ junk G C, ¬ InCone n C h g) ∧ u ∈ side C a b ∧
        OrReaches n C (opnd C a (1-b)) g ∧ gateVal n C g (pairInput u v) = true}.card ≤ 54*(C.size+1))
    (deep : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → ∀ (x9 : Finset (Sym2 (Fin x2))) (x10 x11 : Sym2 (Fin x2) → Fin x2) (x12 x13 : Sym2 (Fin x2) → ℕ) (x14 : Sym2 (Fin x2) → Fin (2 : ℕ)), (∀ x15 ∈ x9, x15 ∈ PEqualNP.TopForm.Ustar x3 x5 ∧ x15 = s(x10 x15, x11 x15) ∧ x12 x15 ∈ PEqualNP.TopForm.tops x3 x5 ∧ x13 x15 ∈ PEqualNP.TopForm.junk x3 x5 ∧ (∃ h ∈ PEqualNP.TopForm.junk x3 x5, PEqualNP.EdgeOwnership.InCone x2 x5 h (x13 x15)) ∧ x10 x15 ∈ PEqualNP.TopForm.side x5 (x12 x15) (x14 x15) ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 (x12 x15) ((1 : Fin (2 : ℕ)) - x14 x15)) (x13 x15) ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 (x13 x15) (PEqualNP.EdgeOwnership.pairInput (x10 x15) (x11 x15)) = Bool.true) → (∀ x16 ∈ x9, ∀ x18 ∈ [fun (x19 : Sym2 (Fin x2)) => ↑(x10 x19), fun (x19 : Sym2 (Fin x2)) => ↑(x11 x19), fun (x19 : Sym2 (Fin x2)) => (2 : ℕ) * x12 x19 + ↑(x14 x19), x13], (3 : ℕ) ≤ {x20 ∈ x9 | x18 x20 = x18 x16}.card) → (∀ (x17 : Fin x2), ∀ x18 ∈ x9, ∀ x20 ∈ x9, x11 x18 = x11 x20 → x17 ∈ PEqualNP.TopForm.side x5 (x12 x18) ((1 : Fin (2 : ℕ)) - x14 x18) → x17 ∈ PEqualNP.TopForm.side x5 (x12 x20) ((1 : Fin (2 : ℕ)) - x14 x20) → x18 = x20) → x9.card ≤ x1 * (x5.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → ∀ (x9 : Finset (Sym2 (Fin x2))) (x10 x11 : Sym2 (Fin x2) → Fin x2) (x12 x13 : Sym2 (Fin x2) → ℕ) (x14 : Sym2 (Fin x2) → Fin (2 : ℕ)), (∀ x15 ∈ x9, x15 ∈ PEqualNP.TopForm.Ustar x3 x5 ∧ x15 = s(x10 x15, x11 x15) ∧ x12 x15 ∈ PEqualNP.TopForm.tops x3 x5 ∧ x13 x15 ∈ PEqualNP.TopForm.junk x3 x5 ∧ x10 x15 ∈ PEqualNP.TopForm.side x5 (x12 x15) (x14 x15) ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 (x12 x15) ((1 : Fin (2 : ℕ)) - x14 x15)) (x13 x15) ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 (x13 x15) (PEqualNP.EdgeOwnership.pairInput (x10 x15) (x11 x15)) = Bool.true) → (∀ x16 ∈ x9, ∀ x18 ∈ [fun (x19 : Sym2 (Fin x2)) => ↑(x10 x19), fun (x19 : Sym2 (Fin x2)) => ↑(x11 x19), fun (x19 : Sym2 (Fin x2)) => (2 : ℕ) * x12 x19 + ↑(x14 x19), x13], (3 : ℕ) ≤ {x20 ∈ x9 | x18 x20 = x18 x16}.card) → (∀ (x17 : Fin x2), ∀ x18 ∈ x9, ∀ x20 ∈ x9, x11 x18 = x11 x20 → x17 ∈ PEqualNP.TopForm.side x5 (x12 x18) ((1 : Fin (2 : ℕ)) - x14 x18) → x17 ∈ PEqualNP.TopForm.side x5 (x12 x20) ((1 : Fin (2 : ℕ)) - x14 x20) → x18 = x20) → x9.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  classical
  obtain ⟨k,hcore⟩ := deep
  refine ⟨k+64,?_⟩
  intro n G inst C hcy hleast htop T u v a g b hw hrich hthin
  let S := T
  let F := S.filter fun e => ∀ h ∈ junk G C, ¬ InCone n C h (g e)
  let A := S \ F
  have hF : F.card ≤ 54*(C.size+1) := by
    apply le_trans (Finset.card_le_card ?_) (shallow n G C hcy hleast htop)
    intro e he
    obtain ⟨heS,hflat⟩ := Finset.mem_filter.mp he
    obtain ⟨hU,heq,ha,hg,hu,hr,hv⟩ := hw e heS
    exact Finset.mem_filter.mpr ⟨hU,u e,v e,heq,a e,ha,b e,g e,hg,hflat,hu,hr,hv⟩
  let label : Fin 4 → Sym2 (Fin n) → ℕ :=
    ![fun e => (u e).val,fun e => (v e).val,fun e => 2*a e+(b e).val,g]
  let V := G.support.toFinset.image Fin.val
  let ranges : Fin 4 → Finset ℕ := ![V,V,Finset.range (2*C.size),Finset.range C.size]
  let R := (Finset.univ : Finset (Fin 4)).sigma ranges
  have cap : R.card ≤ 5*(C.size+1) := by
    have hV : V.card ≤ C.size+1 := by
      apply Finset.card_image_le.trans
      have he := (Set.ncard_eq_toFinset_card' G.support).symm
      rw [he]
      exact support n G C hleast
    change ((Finset.univ : Finset (Fin 4)).sigma ranges).card ≤ _
    rw [Finset.card_sigma,Fin.sum_univ_four]
    change V.card + V.card + (Finset.range (2*C.size)).card + (Finset.range C.size).card ≤ _
    simp only [Finset.card_range]
    omega
  have allowed (e) (he : e ∈ S) (j : Fin 4) : (⟨j,label j e⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ R := by
    obtain ⟨hu,heq,ht,hj,_,_,_⟩ := hw e he
    have hAdj : G.Adj (u e) (v e) := by
      have hm := (Finset.mem_sdiff.mp hu).1
      rw [heq] at hm
      exact G.mem_edgeFinset.mp hm
    have hU : (u e).val ∈ V := Finset.mem_image.mpr ⟨u e,by simpa using (show u e ∈ G.support from ⟨_,hAdj⟩),rfl⟩
    have hV : (v e).val ∈ V := Finset.mem_image.mpr ⟨v e,by simpa using (show v e ∈ G.support from ⟨_,hAdj.symm⟩),rfl⟩
    have index {P : ℕ → Prop} {dec : DecidablePred P} {i : ℕ}
        (h : i ∈ @gatesWhere C P dec) : i < C.size := by
      exact Finset.mem_range.mp (Finset.mem_filter.mp (show i ∈ (Finset.range C.size).filter P from h)).1
    have hA : a e < C.size := index ht
    have hG : g e < C.size := index hj
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    fin_cases j
    · exact hU
    · exact hV
    · apply Finset.mem_range.mpr
      change 2*a e + (b e).val < 2*C.size
      have := (b e).isLt
      omega
    · exact Finset.mem_range.mpr hG
  have peel (m : ℕ) : ∀ (P : Finset (Sigma (fun _ : Fin 4 => ℕ))) (A : Finset (Sym2 (Fin n))),
      P.card = m → (∀ e ∈ A, ∀ j, (⟨j,label j e⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ P) →
      ∃ T ⊆ A, (∀ e ∈ T, ∀ j, 3 ≤ (T.filter fun z => label j z = label j e).card) ∧
        A.card ≤ T.card + 2*P.card := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro P A hm hp
      by_cases h : ∀ e ∈ A, ∀ j, 3 ≤ (A.filter fun z => label j z = label j e).card
      · exact ⟨A,Finset.Subset.rfl,h,by omega⟩
      · push Not at h
        obtain ⟨e,he,j,hfew⟩ := h
        let B := A.filter fun z => label j z = label j e
        let r : Sigma (fun _ : Fin 4 => ℕ) := ⟨j,label j e⟩
        have hr : r ∈ P := hp e he j
        have hlt : (P.erase r).card < m := hm ▸ Finset.card_erase_lt_of_mem hr
        have rem (z) (hz : z ∈ A \ B) (i) : (⟨i,label i z⟩ : Sigma (fun _ : Fin 4 => ℕ)) ∈ P.erase r := by
          obtain ⟨hza,hzb⟩ := Finset.mem_sdiff.mp hz
          apply Finset.mem_erase.mpr
          refine ⟨?_,hp z hza i⟩
          intro eq
          have ij : i = j := congrArg Sigma.fst eq
          subst i
          have same : label j z = label j e := congrArg (fun p : Sigma (fun _ : Fin 4 => ℕ) => p.2) eq
          exact hzb (Finset.mem_filter.mpr ⟨hza,same⟩)
        obtain ⟨T,hTA,hT,hsize⟩ := ih _ hlt _ _ rfl rem
        refine ⟨T,hTA.trans Finset.sdiff_subset,hT,?_⟩
        have hsum := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun z => label j z = label j e) A)
        change (A \ B).card + B.card = A.card at hsum
        change B.card < 3 at hfew
        omega

  obtain ⟨W,hW,hRich,hpay⟩ := peel R.card R A rfl (fun e he j => allowed e (Finset.mem_sdiff.mp he).1 j)
  have hWA : W ⊆ S := hW.trans Finset.sdiff_subset
  have hBound := hcore n G C hcy hleast htop W u v a g b (by
    intro e he
    obtain ⟨hU,heq,ha,hg,hu,hr,hv⟩ := hw e (hWA he)
    refine ⟨hU,heq,ha,hg,?_,hu,hr,hv⟩
    by_contra hn
    have hflat : ∀ h ∈ junk G C, ¬ InCone n C h (g e) := fun h hh hc => hn ⟨h,hh,hc⟩
    exact (Finset.mem_sdiff.mp (hW he)).2 (Finset.mem_filter.mpr ⟨hWA he,hflat⟩)) (by
    intro e he f hf
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact hRich e he 0
    · exact hRich e he 1
    · exact hRich e he 2
    · exact hRich e he 3) (by
    intro w e he d hd hmate hw1 hw2
    exact hthin w e (hWA he) d (hWA hd) hmate hw1 hw2)
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun e => ∀ h ∈ junk G C, ¬ InCone n C h (g e)) S)
  change A.card + F.card = T.card at hsum
  rw [Nat.add_mul]
  omega
