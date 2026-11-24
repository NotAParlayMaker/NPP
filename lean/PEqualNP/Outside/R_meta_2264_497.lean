import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_2264_497
    (profile : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj],
      G = edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7),
        (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)] →
      ∀ K : Finset (Fin 11),
        ([7,6,5,4,4,3,3,3,2,2,2,2,1,1,1,1] : List ℕ).getD
          (G.edgeFinset.filter fun e => ∀ v : Fin 11, v ∈ e → v ∉ K).card 0 ≤ K.card)
    (price : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (a b : ℕ),
      G = edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7),
        (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)] →
      IsLeastAO G C → TopForm G C → C.size < 22 →
      (∀ u v : Fin 11, s(u,v) ∈ Ustar G C → ∃ t ∈ tops G C, ∃ side : Fin 2, ∃ j : ℕ,
        (j = a ∨ j = b) ∧ gateVal 11 C t (pairInput u v) = true ∧
        OrReaches 11 C (opnd C t side) j ∧ gateVal 11 C j (pairInput u v) = true) →
      a < b → junk G C = {a,b} → ¬InCone 11 C a b → ¬InCone 11 C b a →
      (∀ t ∈ tops G C, InCone 11 C a t → ¬InCone 11 C b t) →
      5 + (Ustar G C).card ≤
        ([7,6,5,4,4,3,3,3,2,2,2,2,1,1,1,1] : List ℕ).getD (Ustar G C).card 0 +
        2 * (centreless G C).card + (orN G C \ lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  classical
  intro G dec C a b graph least top
  dsimp only
  intro _ off gateCount coverBound ab two noAB noBA separate
  by_contra! small
  let U := Ustar G C
  let H := G.deleteEdges (U : Set (Sym2 (Fin 11)))
  let rank (k : ℕ) := ([7,6,5,4,4,3,3,3,2,2,2,2,1,1,1,1] : List ℕ).getD k 0
  have decline : Antitone rank := by
    apply antitone_nat_of_succ_le
    intro n
    by_cases h : n < 16
    · interval_cases n <;> decide
    · have h0 : rank n = 0 := List.getD_eq_default _ _ (by simp; omega)
      have h1 : rank (n + 1) = 0 := List.getD_eq_default _ _ (by simp; omega)
      rw [h0, h1]
  let covers : Finset (Finset (Fin 11)) :=
    Finset.univ.filter fun K : Finset (Fin 11) => H.IsVertexCover (K : Set (Fin 11))
  have hCovers : covers.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro u v _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨K, hK, hMin⟩ := Finset.exists_min_image covers Finset.card hCovers
  have hKMin : IsMinCover H K :=
    ⟨(Finset.mem_filter.mp hK).2, fun A hA =>
      hMin A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)⟩
  let outside := G.edgeFinset.filter fun e => ∀ v : Fin 11, v ∈ e → v ∉ K
  have hsub : outside ⊆ U := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨heG, heK⟩ := Finset.mem_filter.mp he
      by_contra hnot
      have ha : G.Adj u v := SimpleGraph.mem_edgeFinset.mp heG
      have hh : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨ha, hnot⟩
      rcases hKMin.1 hh with hu | hv
      · exact heK u (by simp) hu
      · exact heK v (by simp) hv
  have hRank : rank U.card ≤ K.card :=
    (decline (Finset.card_le_card hsub)).trans (profile G graph K)
  have hCover := coverBound K hKMin
  have hPrice := price G C a b graph least top small off ab two noAB noBA separate
  change 5 + U.card ≤ rank U.card + 2 * (centreless G C).card + (orN G C \ lam G C).card at hPrice
  change 17 + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
    (orN G C \ lam G C).card ≤ C.size + U.card at gateCount
  omega
