import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

-- Eliminate at most one uncovered edge directly via the cover number 7 of G11.
-- Separate the disjoint-cone structural side lemma from the remaining cover-charging bound.
theorem PEqualNP.Outside.R_meta_2264_1
    (hDisjointSide :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (j1 j2 : ℕ),
        IsLeastAO G C → TopForm G C → junk G C = {j1, j2} →
        (∀ a ∈ tops G C, InCone n C j1 a → ¬ InCone n C j2 a) →
        ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ h ∈ junk G C,
          OrReaches n C (opnd C a b) h →
          (a ∈ centreless G C ∨ (orN G C \ lam G C).Nonempty) ∧
          (∀ u v : Fin n, gateVal n C a (pairInput u v) = true →
            u ∈ side C a (1 - b) ∨ v ∈ side C a (1 - b)))
    (hCharge :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (j1 j2 : ℕ),
        let U := Ustar G C
        let V := centreless G C
        let R := orN G C \ lam G C
        let T := tops G C
        let J := junk G C
        (G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
          (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] ∧
        IsLeastAO G C ∧ TopForm G C ∧ j1 < j2 ∧ J = {j1, j2} ∧
        ¬ InCone 11 C j1 j2 ∧ ¬ InCone 11 C j2 j1 ∧
        (∀ a ∈ T, InCone 11 C j1 a → ¬ InCone 11 C j2 a) ∧
        2 ≤ U.card ∧ C.size ≤ 21 ∧ (V.Nonempty ∨ R.Nonempty) ∧
        (∀ u v : Fin 11, s(u, v) ∈ U →
          ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J,
            OrReaches 11 C (opnd C a b) h ∧
            gateVal 11 C h (pairInput u v) = true ∧
            (u ∈ side C a (1 - b) ∨ v ∈ side C a (1 - b)))) →
        ∃ K A : Finset (Fin 11),
          IsMinCover (G.deleteEdges ↑U) K ∧
          (∀ u v : Fin 11, s(u, v) ∈ U → u ∈ K ∪ A ∨ v ∈ K ∪ A) ∧
          A.card + U.card ≤ 2 + 2 * V.card + R.card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  classical
  intro G _ C j1 j2 hG hLeast hTop
  dsimp only
  intro _ hOff hCount hCoverBound hlt hjunk hnc1 hnc2 hdisj
  have hAdj : ∀ u v : Fin 11,
      (u, v) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)) →
      G.Adj u v := by
    intro u v huv
    rw [hG]
    revert u v huv
    decide
  have hCover7 : ∀ S : Finset (Fin 11), G.IsVertexCover (↑S : Set (Fin 11)) → 7 ≤ S.card := by
    intro S hS
    let b : Fin 11 → ℕ := fun i => if i ∈ S then 1 else 0
    have hb : ∀ x y : Fin 11, x ∈ S ∨ y ∈ S → 1 ≤ b x + b y := by
      intro x y h
      rcases h with hx | hy
      · simp only [b, hx, ↓reduceIte]; omega
      · simp only [b, hy, ↓reduceIte]; omega
    have e14 := hb 1 4 (hS (hAdj 1 4 (by decide)))
    have e18 := hb 1 8 (hS (hAdj 1 8 (by decide)))
    have e48 := hb 4 8 (hS (hAdj 4 8 (by decide)))
    have e36 := hb 3 6 (hS (hAdj 3 6 (by decide)))
    have e37 := hb 3 7 (hS (hAdj 3 7 (by decide)))
    have e67 := hb 6 7 (hS (hAdj 6 7 (by decide)))
    have e09 := hb 0 9 (hS (hAdj 0 9 (by decide)))
    have e010 := hb 0 10 (hS (hAdj 0 10 (by decide)))
    have e210 := hb 2 10 (hS (hAdj 2 10 (by decide)))
    have e25 := hb 2 5 (hS (hAdj 2 5 (by decide)))
    have e59 := hb 5 9 (hS (hAdj 5 9 (by decide)))
    have hsum : S.card = ∑ i : Fin 11, b i := by
      simp [b]
    rw [hsum, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    change 7 ≤ b 0 + (b 1 + (b 2 + (b 3 + (b 4 + (b 5 + (b 6 + (b 7 + (b 8 + (b 9 + b 10)))))))))
    omega
  have hResidual : ∀ (W : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11)),
      (G.deleteEdges ↑W).IsVertexCover (↑K : Set (Fin 11)) → 7 ≤ K.card + W.card := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      intro K hK
      have hGcov : G.IsVertexCover (↑K : Set (Fin 11)) := by
        intro u v huv
        exact hK (SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simp⟩)
      simpa using hCover7 K hGcov
    | @insert e W he ih =>
      intro K hK
      induction e using Sym2.ind with
      | _ a b =>
        have hK' : (G.deleteEdges ↑W).IsVertexCover (↑(insert a K) : Set (Fin 11)) := by
          intro u v huv
          by_cases heq : s(u, v) = s(a, b)
          · rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl (Finset.mem_insert_self u K)
            · exact Or.inr (Finset.mem_insert_self v K)
          · have hdel : (G.deleteEdges ↑(insert s(a, b) W)).Adj u v := by
              rw [SimpleGraph.deleteEdges_adj]
              refine ⟨(SimpleGraph.deleteEdges_adj.mp huv).1, ?_⟩
              simp [heq, (SimpleGraph.deleteEdges_adj.mp huv).2]
            exact (hK hdel).imp (Finset.mem_insert_of_mem) (Finset.mem_insert_of_mem)
        have h1 := ih (insert a K) hK'
        have h2 := Finset.card_insert_le a K
        rw [Finset.card_insert_of_notMem he]
        omega
  by_contra hShort
  have hSize : C.size ≤ 21 := by omega
  let U := Ustar G C
  let V := centreless G C
  let T := tops G C
  let R := orN G C \ lam G C
  change 17 + (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card at hCount
  by_cases hLarge : 2 ≤ U.card
  · have hUNonempty : U.Nonempty := Finset.card_pos.mp (by omega)
    have hVR : V.Nonempty ∨ R.Nonempty := by
      obtain ⟨e, he⟩ := hUNonempty
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨a, ha, b, h, hh, _, hr, _⟩ := hOff u v he
        have hhJ : h ∈ junk G C := by rw [hjunk]; simp [hh]
        rcases (hDisjointSide 11 G C j1 j2 hLeast hTop hjunk hdisj a ha b h hhJ hr).1 with haV | hR
        · exact Or.inl ⟨a, haV⟩
        · exact Or.inr hR
    have hSideOff : ∀ u v : Fin 11, s(u, v) ∈ U →
        ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ junk G C,
          OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true ∧
          (u ∈ side C a (1 - b) ∨ v ∈ side C a (1 - b)) := by
      intro u v huv
      obtain ⟨a, ha, b, h, hh, hta, hr, hth⟩ := hOff u v huv
      have hhJ : h ∈ junk G C := by rw [hjunk]; simp [hh]
      have hsd := (hDisjointSide 11 G C j1 j2 hLeast hTop hjunk hdisj a ha b h hhJ hr).2 u v hta
      exact ⟨a, ha, b, h, hhJ, hr, hth, hsd⟩
    obtain ⟨K, A, hKMin, hA, hACharge⟩ :=
      hCharge G C j1 j2 ⟨hG, hLeast, hTop, hlt, hjunk, hnc1, hnc2, hdisj, hLarge, hSize, hVR, hSideOff⟩
    have hKT : K.card ≤ (T \ V).card := hCoverBound K hKMin
    have hFull : G.IsVertexCover (↑(K ∪ A) : Set (Fin 11)) := by
      intro u v hadj
      by_cases hDel : s(u, v) ∈ U
      · exact hA u v hDel
      · have he : (G.deleteEdges ↑U).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hDel⟩
        exact (hKMin.1 he).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    have hFull7 := hCover7 (K ∪ A) hFull
    have hUnion := Finset.card_union_le K A
    change A.card + U.card ≤ 2 + 2 * V.card + R.card at hACharge
    omega
  · let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
    let covers : Finset (Finset (Fin 11)) :=
      Finset.univ.filter (fun (K : Finset (Fin 11)) => H.IsVertexCover (↑K : Set (Fin 11)))
    have hCovers : covers.Nonempty := by
      refine ⟨(Finset.univ : Finset (Fin 11)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      intro u v _
      exact Or.inl (Finset.mem_univ u)
    obtain ⟨K, hK, hMin⟩ := Finset.exists_min_image covers Finset.card hCovers
    have hKMin : IsMinCover H K :=
      ⟨(Finset.mem_filter.mp hK).2, fun A hA =>
        hMin A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)⟩
    have hKT : K.card ≤ (T \ V).card := hCoverBound K hKMin
    have hKBound := hResidual U K hKMin.1
    omega
