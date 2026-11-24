import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_2264_2
  (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j k : ℕ),
    (∃ u v, G.Adj u v) →
    IsLeastAO G C → PEqualNP.TopForm.TopForm G C → j < k →
    junk G C = {j,k} → ¬ InCone n C j k → ¬ InCone n C k j →
    (∀ a ∈ tops G C, InCone n C j a → ¬ InCone n C k a) →
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card)
  (large : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (j k : ℕ),
    G = edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7),
      (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)] →
    IsLeastAO G C → PEqualNP.TopForm.TopForm G C → j < k →
    junk G C = {j,k} → ¬ InCone 11 C j k → ¬ InCone 11 C k j →
    (∀ a ∈ tops G C, InCone 11 C j a → ¬ InCone 11 C k a) →
    3 ≤ (Ustar G C).card →
    17 + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
      (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card →
    (∀ T : Finset (Fin 11), IsMinCover (G.deleteEdges ↑(Ustar G C)) T →
      T.card ≤ (tops G C \ centreless G C).card) →
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card →
    22 ≤ C.size) :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
  x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
    [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
     ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
     ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
     ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
  PEqualNP.TopForm.IsLeastAO x1 x3 →
  PEqualNP.TopForm.TopForm x1 x3 →
  have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;
  have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;
  have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
  have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;
  (∀ x13 ∈ x9,
     have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;
     (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧
       ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →
  (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9,
    ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧
    PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧
    PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧
    PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) →
  (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card +
    (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card →
  (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover
    (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) →
  x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 →
  (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  have g11Miss (T : Finset (Fin 11)) (h : T.card < 7) :
      ∃ e ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
        (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)),
        e.1 ∉ T ∧ e.2 ∉ T ∧ e.1 ≠ e.2 :=
    (show ∀ T : Finset (Fin 11), T.card < 7 →
      ∃ e ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
        (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)),
        e.1 ∉ T ∧ e.2 ∉ T ∧ e.1 ≠ e.2 from by decide +kernel) T h

  have g11Cover (G : SimpleGraph (Fin 11)) (hG : G = edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
       (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)])
      (T : Finset (Fin 11)) (hT : G.IsVertexCover ↑T) : 7 ≤ T.card := by
    by_contra! lt
    obtain ⟨⟨v,w⟩, he, hv, hw, hvw⟩ := g11Miss T lt
    have hE : G.Adj v w := by
      rw [hG]
      change v ≠ w ∧ _
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at he
      refine ⟨hvw, Or.inl ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      rcases he with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> decide
    exact (hT hE).elim hv hw

  have addDeletedEdges (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
      (U : Finset (Sym2 (Fin 11))) (hG : G = edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
       (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)])
      (K : Finset (Fin 11)) (hK : (G.deleteEdges ↑U).IsVertexCover ↑K) :
      7 ≤ K.card + U.card := by
    classical
    have pick : ∀ e : Sym2 (Fin 11), ∃ v, v ∈ e := by
      intro e
      induction e using Sym2.ind with
      | h a b => exact ⟨a, by simp⟩
    choose endpt hEnd using pick
    let enlarged := K ∪ U.image endpt
    have hBig : G.IsVertexCover (↑enlarged : Set (Fin 11)) := by
      intro v w h
      by_cases hu : s(v,w) ∈ U
      · have hm := hEnd s(v,w)
        rw [Sym2.mem_iff] at hm
        have hm' : endpt s(v,w) ∈ enlarged := by
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)
        rcases hm with ee | ee
        · left
          simpa only [ee, Finset.mem_coe] using hm'
        · right
          simpa only [ee, Finset.mem_coe] using hm'
      · have hd : (G.deleteEdges ↑U).Adj v w :=
          SimpleGraph.deleteEdges_adj.mpr ⟨h, hu⟩
        rcases hK hd with hl | hr
        · left
          exact Finset.mem_union_left _ hl
        · right
          exact Finset.mem_union_left _ hr
    exact (g11Cover G hG enlarged hBig).trans <| (Finset.card_union_le _ _).trans <|
      Nat.add_le_add_left Finset.card_image_le _

  have numFinish (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
      (U : Finset (Sym2 (Fin 11))) (hG : G = edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
       (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)])
      (t a sz : ℕ)
      (hk : ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ t)
      (hcount : 17 + t + a ≤ sz + U.card)
      (hsmall : 2 * U.card ≤ a + 2) : 22 ≤ sz := by
    classical
    let H := G.deleteEdges ↑U
    let covs : Finset (Finset (Fin 11)) :=
      Finset.filter (fun K : Finset (Fin 11) => H.IsVertexCover (↑K : Set (Fin 11))) Finset.univ
    have hNE : covs.Nonempty := ⟨Finset.univ, by
      simp [covs, SimpleGraph.isVertexCover_univ]⟩
    obtain ⟨K, hK, min⟩ := Finset.exists_min_image covs Finset.card hNE
    have hKcover : H.IsVertexCover (↑K : Set (Fin 11)) := (Finset.mem_filter.mp hK).2
    have hKmin : IsMinCover H K :=
      ⟨hKcover, fun L hL => min L (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL⟩)⟩
    have first := addDeletedEdges G U hG K hKcover
    have inter := hk K hKmin
    omega

  intro G dec C j k same least shape
  dsimp only
  intro _ _ budget minCover order junkEq noJK noKJ separate
  have edge : ∃ u v, G.Adj u v := by
    rw [same]
    exact ⟨0,9,by decide⟩
  have paid := charge 11 G C j k edge least shape order junkEq noJK noKJ separate
  by_cases few : (Ustar G C).card ≤ 2
  · apply numFinish G (Ustar G C) same (tops G C \ centreless G C).card
      (2 * (centreless G C).card + (orN G C \ lam G C).card) _ minCover
    · omega
    · omega
  · exact large G C j k same least shape order junkEq noJK noKJ separate
      (by omega) budget minCover paid
