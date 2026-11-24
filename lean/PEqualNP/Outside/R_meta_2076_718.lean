import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- A large bipartite cut followed by degree-two peeling leaves a bipartite core.
-- Only the residual subgraph is required to be bipartite. The ambient graph is unchanged.
theorem PEqualNP.Outside.R_meta_2076_718
    (largeCut : ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
      ∃ (B : SimpleGraph (Fin n)) (color : Fin n → Bool), B ≤ F ∧
        (∀ u v, B.Adj u v → color u ≠ color v) ∧ F.edgeSet.ncard ≤ 2 * B.edgeSet.ncard) :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1) →
    (∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ (C : Circuit) (H : SimpleGraph (Fin n)),
      IsLeastAO G C → TopForm G C → H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
      (∃ color : Fin n → Bool, ∀ u v, H.Adj u v → color u ≠ color v) →
      H.edgeSet.ncard ≤ c * (C.size + 1)) →
∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  intro essential core
  obtain ⟨c,hCore⟩ := core
  refine ⟨2 * (c + 2),?_⟩
  intro n G _ hGirth hEdge C H hLeast hTop hH _hMin
  classical
  have edgeCount (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
      F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have peel (p : ℕ) : ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      F.support.ncard = p →
      ∃ H : SimpleGraph (Fin n), H ≤ F ∧
        (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) ∧
        F.edgeSet.ncard ≤ H.edgeSet.ncard + 2 * p := by
    induction p using Nat.strong_induction_on with
    | ind p smaller =>
      intro F _ hF
      by_cases h : ∀ v : Fin n, (F.neighborSet v).ncard = 0 ∨ 3 ≤ (F.neighborSet v).ncard
      · exact ⟨F,le_rfl,h,by omega⟩
      · push Not at h
        obtain ⟨v,hv0,hv2⟩ := h
        have hDeg := F.ncard_neighborSet v
        have hvPos : 0 < F.degree v := by omega
        have hv : v ∈ F.support := by
          by_contra hn
          have hz : F.neighborSet v = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro w hw
            exact hn ⟨w,hw⟩
          exact hv0 (by rw [hz,Set.ncard_empty])
        have hPpos : 0 < F.support.ncard := by
          rw [← Set.fintypeCard_eq_ncard]
          exact Fintype.card_pos_iff.mpr ⟨⟨v,hv⟩⟩
        let R := F.deleteIncidenceSet v
        have hDrop : R.support.ncard ≤ F.support.ncard - 1 := by
          simpa only [Set.fintypeCard_eq_ncard] using F.card_support_deleteIncidenceSet hv
        obtain ⟨H,hHR,hMin,hH⟩ := smaller R.support.ncard (by omega) R rfl
        refine ⟨H,hHR.trans (F.deleteIncidenceSet_le v),hMin,?_⟩
        have hRemoved : R.edgeFinset.card = F.edgeFinset.card - F.degree v :=
          F.card_edgeFinset_deleteIncidenceSet v
        have hLe : F.degree v ≤ F.edgeFinset.card := by
          rw [← F.card_incidenceFinset_eq_degree v]
          exact Finset.card_le_card (F.incidenceFinset_subset v)
        rw [edgeCount R] at hH
        rw [edgeCount F]
        omega

  obtain ⟨B,color,hBH,hColor,hHalf⟩ := largeCut n H
  obtain ⟨K,hKB,hMin,hPeel⟩ := peel B.support.ncard B rfl
  have hK := hCore n G hGirth hEdge C K hLeast hTop ((hKB.trans hBH).trans hH) hMin
    ⟨color, fun u v huv => hColor u v (hKB huv)⟩
  have sub : B.support ⊆ G.support := by
    rintro u ⟨v,huv⟩
    exact ⟨v,(G.deleteEdges_le _) (hH (hBH huv))⟩
  have sizeBound := (Set.ncard_le_ncard sub).trans (essential n G C hLeast)
  calc H.edgeSet.ncard ≤ 2 * B.edgeSet.ncard := hHalf
    _ ≤ 2 * (K.edgeSet.ncard + 2 * B.support.ncard) := Nat.mul_le_mul_left _ hPeel
    _ ≤ 2 * (c * (C.size+1) + 2 * (C.size+1)) := by omega
    _ = 2 * (c + 2) * (C.size+1) := by ring
