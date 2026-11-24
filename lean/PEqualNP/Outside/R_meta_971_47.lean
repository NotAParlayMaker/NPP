import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Prove the cubic Heawood residual vertex-cover inequality 21 <= 3 * K.card + U.card
-- inside the reduction, discharging U.card <= 2 completely and splitting 3 <= U.card <= 5
-- (where 6 <= (tops \ centreless).card) from 6 <= U.card.
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_971_47 :
    (∀ (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 14 [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
        (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10),
        (5, 12), (6, 8), (6, 9), (6, 11)] →
      Monotone2 C → circuitFun 14 C = graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size ≤ C.size ∧
        20 + (tops G D \ centreless G D).card + 2 * (centreless G D).card + (junk G D).card +
          (orN G D \ lam G D).card ≤ D.size + (Ustar G D).card ∧
        (∀ K : Finset (Fin 14), IsMinCover (G.deleteEdges ↑(Ustar G D)) K →
          K.card ≤ (tops G D \ centreless G D).card) ∧
        ((Ustar G D).Nonempty →
          (junk G D).Nonempty ∧ ((centreless G D).Nonempty ∨ (orN G D \ lam G D).Nonempty))) →
    (∀ (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 14 [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
        (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10),
        (5, 12), (6, 8), (6, 9), (6, 11)] →
      IsLeastAO G D → TopForm G D →
      let T := tops G D
      let V := centreless G D
      let J := junk G D
      let U := Ustar G D
      20 + (T \ V).card + 2 * V.card + J.card + (orN G D \ lam G D).card ≤ D.size + U.card →
      3 ≤ U.card → U.card ≤ 5 → 6 ≤ (T \ V).card → 1 ≤ J.card →
      1 ≤ 2 * V.card + (orN G D \ lam G D).card → 27 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 14 [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
        (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10),
        (5, 12), (6, 8), (6, 9), (6, 11)] →
      IsLeastAO G D → TopForm G D →
      let T := tops G D
      let V := centreless G D
      let J := junk G D
      let U := Ustar G D
      20 + (T \ V).card + 2 * V.card + J.card + (orN G D \ lam G D).card ≤ D.size + U.card →
      (∀ K : Finset (Fin 14), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ V).card) →
      6 ≤ U.card → 21 ≤ 3 * (T \ V).card + U.card → 1 ≤ J.card → 27 ≤ D.size) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  intro hNorm hMed hLarge C hMono hEval
  let rawPairs : List (ℕ × ℕ) :=
    [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
     (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
     (6, 8), (6, 9), (6, 11)]
  let G : SimpleGraph (Fin 14) := edgeGraph 14 rawPairs
  let E21 : Finset (Fin 14 × Fin 14) :=
    {(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
     (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
     (6, 8), (6, 9), (6, 11)}
  have hCard21 : E21.card = 21 := by decide
  have hPairsAdj : ∀ p ∈ E21, G.Adj p.1 p.2 := by decide
  have hPairsLt : ∀ p ∈ E21, p.1 < p.2 := by decide
  have hDeg3 : ∀ w : Fin 14, (E21.filter (fun p => p.1 = w ∨ p.2 = w)).card ≤ 3 := by decide
  have hMemDistinct : ∀ u v : Fin 14, (u.val, v.val) ∈ rawPairs → u ≠ v := by decide
  have hFun : circuitFun 14 C = graphFun G ∅ := by
    funext x
    change C.eval (List.ofFn x) =
      (decide (∃ a ∈ (∅ : Finset (Fin 14)), x a = true) ||
        decide (∃ u v : Fin 14, G.Adj u v ∧ x u = true ∧ x v = true))
    have hempty : decide (∃ a ∈ (∅ : Finset (Fin 14)), x a = true) = false := by simp
    rw [hempty, Bool.false_or]
    have hiff : (∃ u v : Fin 14, (u.val, v.val) ∈ rawPairs ∧ x u = true ∧ x v = true) ↔
        (∃ u v : Fin 14, G.Adj u v ∧ x u = true ∧ x v = true) := by
      constructor
      · intro h
        exact Exists.elim h fun u hu => Exists.elim hu fun v huv =>
          ⟨u, v, ⟨hMemDistinct u v huv.1, Or.inl huv.1⟩, huv.2⟩
      · intro h
        exact Exists.elim h fun u hu => Exists.elim hu fun v huv =>
          huv.1.2.elim
            (fun h1 => ⟨u, v, h1, huv.2⟩)
            (fun h2 => ⟨v, u, h2, huv.2.2, huv.2.1⟩)
    by_cases hx : ∃ u v : Fin 14, G.Adj u v ∧ x u = true ∧ x v = true
    · rw [(hEval x).mpr (hiff.mpr hx), decide_eq_true hx]
    · have hcf : C.eval (List.ofFn x) = false :=
        Bool.eq_false_iff.mpr fun ht => hx (hiff.mp ((hEval x).mp ht))
      rw [hcf, decide_eq_false hx]
  exact Exists.elim (hNorm G C rfl hMono hFun) fun D hD => by
    have hLeast := hD.1
    have hTop := hD.2.1
    have hSizeLe := hD.2.2.1
    have hCount := hD.2.2.2.1
    have hCoverBound := hD.2.2.2.2.1
    have hNonemptyProps := hD.2.2.2.2.2
    classical
    let U := Ustar G D
    let H := G.deleteEdges (↑U : Set (Sym2 (Fin 14)))
    let covers : Finset (Finset (Fin 14)) :=
      Finset.univ.filter (fun K : Finset (Fin 14) => H.IsVertexCover (↑K : Set (Fin 14)))
    have hCovers : covers.Nonempty := by
      refine ⟨(Finset.univ : Finset (Fin 14)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      intro u _ _
      exact Or.inl (Finset.mem_univ u)
    exact Exists.elim (Finset.exists_min_image covers Finset.card hCovers) fun K hK_rest => by
      have hKMin : IsMinCover H K :=
        ⟨(Finset.mem_filter.mp hK_rest.1).2, fun A hA =>
          hK_rest.2 A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)⟩
      have hKT : K.card ≤ (tops G D \ centreless G D).card := hCoverBound K hKMin
      let hit : Finset (Fin 14 × Fin 14) := E21.filter (fun p => p.1 ∈ K ∨ p.2 ∈ K)
      let miss : Finset (Fin 14 × Fin 14) := E21.filter (fun p => ¬ (p.1 ∈ K ∨ p.2 ∈ K))
      have hHM_disj : Disjoint hit miss :=
        Finset.disjoint_left.mpr fun p h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hHM_uni : hit ∪ miss = E21 := by
        ext p
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        exact ⟨fun h => h.elim (fun x => x.1) (fun x => x.1),
          fun hp => if hc : p.1 ∈ K ∨ p.2 ∈ K then Or.inl ⟨hp, hc⟩ else Or.inr ⟨hp, hc⟩⟩
      have hHM_sum : hit.card + miss.card = 21 := by
        rw [← Finset.card_union_of_disjoint hHM_disj, hHM_uni, hCard21]
      let incAt : Fin 14 → Finset (Fin 14 × Fin 14) := fun w => E21.filter (fun p => p.1 = w ∨ p.2 = w)
      have hHitSub : hit ⊆ K.biUnion incAt := by
        intro p hp
        have hm := Finset.mem_filter.mp hp
        rw [Finset.mem_biUnion]
        exact hm.2.elim
          (fun h1 => ⟨p.1, h1, Finset.mem_filter.mpr ⟨hm.1, Or.inl rfl⟩⟩)
          (fun h2 => ⟨p.2, h2, Finset.mem_filter.mpr ⟨hm.1, Or.inr rfl⟩⟩)
      have hIncCard : ∀ w ∈ K, (incAt w).card ≤ 3 := by
        intro w _
        dsimp only [incAt]
        rw [Finset.filter_congr_decidable]
        exact hDeg3 w
      have hHitLe : hit.card ≤ K.card * 3 :=
        (Finset.card_le_card hHitSub).trans (Finset.card_biUnion_le_card_mul K incAt 3 hIncCard)
      let toSym : Fin 14 × Fin 14 → Sym2 (Fin 14) := fun p => s(p.1, p.2)
      have hMissSubU : miss.image toSym ⊆ U := by
        intro e he
        exact Exists.elim (Finset.mem_image.mp he) fun p hp => by
          rw [← hp.2]
          have hm := Finset.mem_filter.mp hp.1
          have hadjG : G.Adj p.1 p.2 := hPairsAdj p hm.1
          by_contra hnotU
          have hadjH : H.Adj p.1 p.2 := SimpleGraph.deleteEdges_adj.mpr ⟨hadjG, hnotU⟩
          exact hm.2 (hKMin.1 hadjH)
      have hInjSym : Set.InjOn toSym ↑miss := by
        intro p1 h1 p2 h2 heq
        have lt1 := hPairsLt p1 (Finset.mem_filter.mp h1).1
        have lt2 := hPairsLt p2 (Finset.mem_filter.mp h2).1
        exact (Sym2.eq_iff.mp heq).elim
          (fun h => Prod.ext h.1 h.2)
          (fun h => absurd (lt_trans (h.1 ▸ lt1) (h.2 ▸ lt2)) (lt_irrefl _))
      have hMissLeU : miss.card ≤ U.card := by
        rw [← Finset.card_image_of_injOn hInjSym]
        exact Finset.card_le_card hMissSubU
      have hCubicBound : 21 ≤ 3 * (tops G D \ centreless G D).card + U.card := by omega
      change 20 + (tops G D \ centreless G D).card + 2 * (centreless G D).card + (junk G D).card +
        (orN G D \ lam G D).card ≤ D.size + U.card at hCount
      by_cases hU0 : U.card = 0
      · omega
      · have hUNe : U.Nonempty := Finset.card_pos.mp (by omega)
        have hNP := hNonemptyProps hUNe
        have hJ1 : 1 ≤ (junk G D).card := Finset.card_pos.mpr hNP.1
        have hVR1 : 1 ≤ 2 * (centreless G D).card + (orN G D \ lam G D).card :=
          hNP.2.elim
            (fun hV => by have hv := Finset.card_pos.mpr hV; omega)
            (fun hR => by have hr := Finset.card_pos.mpr hR; omega)
        by_cases hU2 : U.card ≤ 2
        · omega
        · by_cases hU5 : U.card ≤ 5
          · have h3 : 3 ≤ U.card := by omega
            have hTV6 : 6 ≤ (tops G D \ centreless G D).card := by omega
            have hD27 := hMed G D rfl hLeast hTop hCount h3 hU5 hTV6 hJ1 hVR1
            omega
          · have h6 : 6 ≤ U.card := by omega
            have hD27 := hLarge G D rfl hLeast hTop hCount hCoverBound h6 hCubicBound hJ1
            omega
