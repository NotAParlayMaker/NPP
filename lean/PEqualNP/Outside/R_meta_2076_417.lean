import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2076_417
    (essential : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (atMostOne : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (junk G C).card ≤ 1 →
        (Ustar G C).card ≤ c * (C.size + 1))
    (nonbranching :
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit) (H : SimpleGraph (Fin n)), IsLeastAO G C → TopForm G C →
      H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 4 ≤ (H.neighborSet v).ncard) →
      2 ≤ (junk G C).card →
      let next := fun (i j : ℕ) => i ∈ junk G C ∧ j ∈ junk G C ∧ InCone n C i j ∧
        ¬ ∃ k ∈ junk G C, InCone n C i k ∧ InCone n C k j
      (¬ ∃ i j k, j ≠ k ∧ next i j ∧ next i k) → H.edgeSet.ncard ≤ c * (C.size + 1))
    (branching :
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → G.edgeFinset.Nonempty →
      ∀ (C : Circuit) (H : SimpleGraph (Fin n)), IsLeastAO G C → TopForm G C →
      H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 4 ≤ (H.neighborSet v).ncard) →
      2 ≤ (junk G C).card →
      let next := fun (i j : ℕ) => i ∈ junk G C ∧ j ∈ junk G C ∧ InCone n C i j ∧
        ¬ ∃ k ∈ junk G C, InCone n C i k ∧ InCone n C k j
      (∃ i j k, j ≠ k ∧ next i j ∧ next i k) → H.edgeSet.ncard ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨small, smallBound⟩ := atMostOne
  obtain ⟨chainCost, chainBound⟩ := nonbranching
  obtain ⟨forkCost, forkBound⟩ := branching
  refine ⟨max small (max chainCost forkCost + 3), ?_⟩
  intro n G _ girth edge C H least top inside _
  classical
  have edgeCount (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
      F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  by_cases one : (junk G C).card ≤ 1
  · have covered : H.edgeFinset ⊆ Ustar G C := by
      have sub := SimpleGraph.edgeFinset_mono inside
      rw [SimpleGraph.edgeFinset_deleteEdges] at sub
      exact sub
    rw [edgeCount H]
    exact (Finset.card_le_card covered).trans ((smallBound n G girth edge C least top one).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)))
  have peel (p : ℕ) : ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      F.support.ncard = p →
      ∃ H : SimpleGraph (Fin n), H ≤ F ∧
        (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 4 ≤ (H.neighborSet v).ncard) ∧
        F.edgeSet.ncard ≤ H.edgeSet.ncard + 3 * p := by
    induction p using Nat.strong_induction_on with
    | ind p smaller =>
      intro F _ hF
      by_cases h : ∀ v : Fin n, (F.neighborSet v).ncard = 0 ∨ 4 ≤ (F.neighborSet v).ncard
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
  obtain ⟨K, inH, degrees, cost⟩ := peel H.support.ncard H rfl
  have together := inH.trans inside
  have supportG : H.support ⊆ G.support := by
    intro v hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, (G.deleteEdges_le _) (inside hw)⟩
  have support : H.support.ncard ≤ C.size + 1 :=
    (Set.ncard_le_ncard supportG).trans (essential n G C least)
  let next (i j : ℕ) := i ∈ junk G C ∧ j ∈ junk G C ∧ InCone n C i j ∧
    ¬ ∃ k ∈ junk G C, InCone n C i k ∧ InCone n C k j
  have coreCost : K.edgeSet.ncard ≤ max chainCost forkCost * (C.size + 1) := by
    by_cases forks : ∃ i j k, j ≠ k ∧ next i j ∧ next i k
    · exact (forkBound n G girth edge C K least top together degrees (by omega) forks).trans
        (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
    · exact (chainBound n G girth edge C K least top together degrees (by omega) forks).trans
        (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  calc
    H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * H.support.ncard := cost
    _ ≤ max chainCost forkCost * (C.size + 1) + 3 * (C.size + 1) :=
      Nat.add_le_add coreCost (Nat.mul_le_mul_left _ support)
    _ = (max chainCost forkCost + 3) * (C.size + 1) := by rw [Nat.add_mul]
    _ ≤ max small (max chainCost forkCost + 3) * (C.size + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_max_right _ _)
