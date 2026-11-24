import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

-- Two junk ANDs, neither inside the other, no top over both.
-- hShape is the normal form: each junk AND is an AND of two ORs of inputs, and a top that reaches
-- a junk AND through ORs is (OR of inputs, or that junk AND) AND (OR of inputs).
-- hCharge is the count that is left, stated for circuits already in that normal form,
-- with one unit for each junk AND.
-- hGraph is the cover number of the graph.
theorem PEqualNP.Outside.R_meta_2264_1
    (hGraph :
      let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11)),
        (G.deleteEdges ↑U).IsVertexCover (↑K : Set (Fin 11)) → 7 ≤ K.card + U.card)
    (hShape :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit) (i j : ℕ),
        IsAO2 n D → TopForm G D → junk G D = {i, j} →
        ¬ InCone n D i j → ¬ InCone n D j i →
        (∀ a ∈ tops G D, InCone n D i a → ¬ InCone n D j a) →
        (∀ h : ℕ, h = i ∨ h = j → ∀ x : Fin n → Bool,
          gateVal n D h x =
            (decide (∃ u ∈ side (n := n) D h 0, x u = true) &&
              decide (∃ u ∈ side (n := n) D h 1, x u = true))) ∧
        (∀ a ∈ tops G D, ∀ b : Fin 2, ∀ h : ℕ, h = i ∨ h = j →
          OrReaches n D (opnd D a b) h → ∀ x : Fin n → Bool,
          gateVal n D a x =
            ((decide (∃ u ∈ side (n := n) D a b, x u = true) || gateVal n D h x) &&
              decide (∃ u ∈ side (n := n) D a (1 - b), x u = true))))
    (hCharge :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
        G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
        IsLeastAO G D → TopForm G D → D.size ≤ 21 →
        (∀ a ∈ tops G D, ∀ b : Fin 2, ∀ h ∈ junk G D,
          OrReaches 11 D (opnd D a b) h → ∀ x : Fin 11 → Bool,
          gateVal 11 D a x =
            ((decide (∃ u ∈ side (n := 11) D a b, x u = true) ||
                (decide (∃ u ∈ side (n := 11) D h 0, x u = true) &&
                  decide (∃ u ∈ side (n := 11) D h 1, x u = true))) &&
              decide (∃ u ∈ side (n := 11) D a (1 - b), x u = true))) →
        ∃ K A : Finset (Fin 11),
          IsMinCover (G.deleteEdges ↑(Ustar G D)) K ∧
          (∀ e ∈ Ustar G D, ∃ u ∈ K ∪ A, u ∈ e) ∧
          A.card + (Ustar G D).card ≤
            2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card)
    : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  intro G _ D i j hG hLeast hTop
  dsimp only
  intro hStars hOff hCount hCoverBound hij hJunk hNot1 hNot2 hBoth
  by_contra hShort
  have hSize : D.size ≤ 21 := by omega
  let U := Ustar G D
  let V := centreless G D
  let T := tops G D
  let R := orN G D \ lam G D
  change 17 + (T \ V).card + 2 * V.card + R.card ≤ D.size + U.card at hCount
  classical
  let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
  obtain ⟨hP1, hP2⟩ := hShape 11 G D i j hLeast.1 hTop hJunk hNot1 hNot2 hBoth
  obtain ⟨K, A, hKMin, hA, hACharge⟩ :=
    hCharge G D hG hLeast hTop hSize
      (fun a ha b h hh => by
        have hh' : h = i ∨ h = j := by rw [hJunk] at hh; simpa using hh
        intro hr x
        rw [hP2 a ha b h hh' hr x, hP1 h hh' x])
  have hJc : (junk G D).card = 2 := by rw [hJunk]; exact Finset.card_pair (Nat.ne_of_lt hij)
  have hKT : K.card ≤ (T \ V).card := hCoverBound K hKMin
  rw [hJc] at hACharge
  change A.card + U.card ≤ 2 * V.card + 2 + R.card at hACharge
  have hFull : G.IsVertexCover (↑(K ∪ A) : Set (Fin 11)) := by
    intro u v hadj
    by_cases hDel : s(u, v) ∈ U
    · obtain ⟨w, hw, hwe⟩ := hA _ hDel
      rcases Sym2.mem_iff.mp hwe with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr hw
    · have he : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hDel⟩
      exact (hKMin.1 he).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
  have hFullDeleted : (G.deleteEdges (↑(∅ : Finset (Sym2 (Fin 11))) : Set (Sym2 (Fin 11)))).IsVertexCover
      (↑(K ∪ A) : Set (Fin 11)) := by
    intro u v hadj
    exact hFull (SimpleGraph.deleteEdges_adj.mp hadj).1
  have hFullBound : 7 ≤ (K ∪ A).card + (∅ : Finset (Sym2 (Fin 11))).card := by
    rw [hG] at hFullDeleted
    exact hGraph ∅ (K ∪ A) hFullDeleted
  have hUnion := Finset.card_union_le K A
  rw [Finset.card_empty, Nat.add_zero] at hFullBound
  omega
