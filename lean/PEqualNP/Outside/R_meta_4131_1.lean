import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

-- The masks name three sets of four vertices. Every seven-cover has all its
-- internal edges incident to one of these sets. For a chosen mask, fix the
-- vertices dropped inside it. All remaining eligible vertices can be dropped
-- together because they form an independent set, even before any edges are deleted.
theorem PEqualNP.Outside.R_meta_4131_1
    (pivots : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ T : Finset (Fin 11), T.card = 7 → G.IsVertexCover ↑T →
        ∃ p ∈ ([432,848,1416] : List ℕ), G.IsIndepSet ↑(T \ T.filter (fun v => p.testBit v.val)))
    (budget : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        U.card ≤ B → B < 2 * U.card →
        ∀ T : Finset (Fin 11), T.card = 7 → G.IsVertexCover ↑T →
        ∀ p ∈ ([432,848,1416] : List ℕ),
          let P := T.filter (fun v => p.testBit v.val)
          G.IsIndepSet ↑(T \ P) →
          ∀ S ⊆ P, (G.deleteEdges ↑U).IsVertexCover ↑(T \ S) →
            S.card + ((T \ P).filter (fun v => ∀ w : Fin 11,
              (G.deleteEdges ↑U).Adj v w → w ∈ T \ S)).card ≤ B - U.card) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) x1; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x2 x3 →       PEqualNP.TopForm.TopForm x2 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → ∀ (x12 x13 : Finset (Fin (11 : ℕ))), x12.card = (7 : ℕ) → x2.IsVertexCover ↑x12 → x13 ⊆ x12 → (x2.deleteEdges ↑x8).IsVertexCover ↑(x12 \ x13) → x13.card ≤ x9 - x8.card := by
  dsimp only
  intro C short least top junkCount lo hi T X seven cover subset residual
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let H := G.deleteEdges ↑(Ustar G C)
  obtain ⟨p, hp, independent⟩ := pivots T seven cover
  let P := T.filter (fun v => p.testBit v.val)
  let S := X ∩ P
  let F := (T \ P).filter (fun v => ∀ w : Fin 11, H.Adj v w → w ∈ T \ S)
  have seedSubset : S ⊆ P := Finset.inter_subset_right
  have seedCover : H.IsVertexCover ↑(T \ S) := by
    apply residual.subset
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, fun hs =>
      (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hs).1⟩
  have limit := budget C short least top junkCount lo hi T seven cover p hp independent S seedSubset seedCover
  have remaining : X \ S ⊆ F := by
    intro v hv
    obtain ⟨vx, vs⟩ := Finset.mem_sdiff.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨subset vx, fun vp => vs (Finset.mem_inter.mpr ⟨vx,vp⟩)⟩, ?_⟩
    intro w adj
    rcases residual adj with h | h
    · exact False.elim ((Finset.mem_sdiff.mp h).2 vx)
    · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h).1, fun hs =>
        (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hs).1⟩
  have split := Finset.card_sdiff_add_card_eq_card (show S ⊆ X from Finset.inter_subset_left)
  change S.card + F.card ≤ _ at limit
  calc
    X.card = (X \ S).card + S.card := split.symm
    _ ≤ F.card + S.card := Nat.add_le_add_right (Finset.card_le_card remaining) _
    _ = S.card + F.card := Nat.add_comm _ _
    _ ≤ _ := limit
