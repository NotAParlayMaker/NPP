import Mathlib.Data.Nat.BitIndices
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4715_421
    (packing : ∀ (v : Fin (11 : ℕ)) (blocks : List ℕ),
      blocks.Pairwise (fun a b => a &&& b = 0) →
      (∀ b ∈ blocks, b ∈ [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)] ∧ b.testBit v.val = false) →
      (blocks.map (fun b => (b.bitIndices.length + 1) / 2)).sum ≤ 6)
    (remaining : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card < (7 : ℕ) → ¬ (x9 - x8.card = 6 ∧ ∃ u v : Fin 11, (x1.deleteEdges ↑x8).Adj u v) → ∃ (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x13 ∧ ∀ (x14 : List ℕ), List.Pairwise (fun (x15 x16 : ℕ) => x15 &&& x16 = (0 : ℕ)) x14 → (∀ x16 ∈ x14, x16 ∈ x2 ∧ ∀ x18 ∈ x13, x16.testBit ↑x18 = Bool.false) → (List.map (fun (x17 : ℕ) => (x17.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x14).sum ≤ x9 - x8.card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card < (7 : ℕ) → ∃ (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x13 ∧ ∀ (x14 : List ℕ), List.Pairwise (fun (x15 x16 : ℕ) => x15 &&& x16 = (0 : ℕ)) x14 → (∀ x16 ∈ x14, x16 ∈ x2 ∧ ∀ x18 ∈ x13, x16.testBit ↑x18 = Bool.false) → (List.map (fun (x17 : ℕ) => (x17.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x14).sum ≤ x9 - x8.card := by
  intro G catalogue C hsize hleast htop hjunk missed budget hlo hhi hlt
  classical
  let H : SimpleGraph (Fin 11) := G.deleteEdges (missed : Set (Sym2 (Fin 11)))
  by_cases hb : budget - missed.card = 6 ∧ ∃ u v : Fin 11, H.Adj u v
  · let covers : Finset (Finset (Fin 11)) :=
      Finset.univ.filter fun T => H.IsVertexCover (T : Set (Fin 11))
    have full : H.IsVertexCover ((Finset.univ : Finset (Fin 11)) : Set (Fin 11)) := by
      intro u v h
      exact Or.inl (by simp)
    have hn : covers.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, full⟩⟩
    obtain ⟨T,hT,hmin⟩ := Finset.exists_min_image covers Finset.card hn
    have hc : H.IsVertexCover (T : Set (Fin 11)) := (Finset.mem_filter.mp hT).2
    have hminimum : PEqualNP.MetaComplexity.NestedCover.IsMinCover H T := by
      exact ⟨hc, fun S hs => hmin S (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)⟩
    obtain ⟨u,v,hedge⟩ := hb.2
    have ht : T.Nonempty := by
      rcases (@hc u v hedge) with h | h
      · exact ⟨u,h⟩
      · exact ⟨v,h⟩
    obtain ⟨w,hw⟩ := ht
    refine ⟨T,hminimum,?_⟩
    intro blocks hd hx
    rw [hb.1]
    exact packing w blocks hd (fun b h => ⟨(hx b h).1, (hx b h).2 w hw⟩)
  · exact remaining C hsize hleast htop hjunk hlo hhi hlt hb

