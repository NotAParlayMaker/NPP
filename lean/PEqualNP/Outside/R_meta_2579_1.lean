import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2579_1 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1) →
    (∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ (C : Circuit) (H : SimpleGraph (Fin n)),
      IsLeastAO G C → TopForm G C →
      H.edgeSet ⊆ (↑({e ∈ Ustar G C | ¬ ∃ u v : Fin n, e = s(u, v) ∧
        ∃ j < C.gates.length, ∃ b : Fin 2,
          2 ≤ (orIn n C (n + j)).card ∧
          (∀ x ∈ orIn n C (n + j), G.Adj u x) ∧
          orIn n C (opnd C j b) = {v}} : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
      H.edgeSet.ncard ≤ c * (C.size + 1)) →
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  intro essential core
  obtain ⟨c,hCore⟩ := core
  refine ⟨c+2,?_⟩
  intro n G _ hGirth hEdge C hLeast hTop
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
  let U : Finset (Sym2 (Fin n)) := {e ∈ Ustar G C | ¬ ∃ u v : Fin n, e = s(u, v) ∧
        ∃ j < C.gates.length, ∃ b : Fin 2,
          2 ≤ (orIn n C (n + j)).card ∧
          (∀ x ∈ orIn n C (n + j), G.Adj u x) ∧
          orIn n C (opnd C j b) = {v}}
  let D := G.deleteEdges {e | e ∉ U}
  have hEdgeSet : D.edgeSet = (U : Set (Sym2 (Fin n))) := by
    ext e
    change e ∈ (G.deleteEdges {e | e ∉ U}).edgeSet ↔ e ∈ U
    rw [SimpleGraph.edgeSet_deleteEdges]
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, not_not]
    refine ⟨And.right, fun he => ⟨?_, he⟩⟩
    have he' := (Finset.mem_filter.mp he).1
    exact (G.coe_edgeFinset ▸ (show e ∈ (G.edgeFinset : Set _) from
      (Finset.mem_sdiff.mp he').1))
  obtain ⟨H, hHD, hMin, hPeel⟩ := peel D.support.ncard D rfl
  have hDSupport : D.support ⊆ G.support := by
    rintro v ⟨w, hw⟩
    exact ⟨w, (G.deleteEdges_le _) hw⟩
  have hSubset : H.edgeSet ⊆ (U : Set (Sym2 (Fin n))) := by
    rw [← hEdgeSet]
    exact SimpleGraph.edgeSet_subset_edgeSet.mpr hHD
  have hBound := hCore n G hGirth hEdge C H hLeast hTop hSubset hMin
  have hSupport := (Set.ncard_le_ncard hDSupport).trans (essential n G C hLeast)
  rw [hEdgeSet, Set.ncard_coe_finset] at hPeel
  change U.card ≤ (c + 2) * (C.size + 1)
  rw [Nat.add_mul]
  omega
