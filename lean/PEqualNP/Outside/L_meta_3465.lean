import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3465

lemma three (n : ℕ) (U F : Finset ℕ) :
    (U.filter (fun w => w < n)).card + (U.filter (fun w => n ≤ w ∧ w - n ∉ F)).card
      + (F.filter (fun g => n + g ∈ U)).card ≤ U.card := by
  have h3 : (F.filter (fun g => n + g ∈ U)).card
      ≤ (U.filter (fun w => n ≤ w ∧ w - n ∈ F)).card := by
    apply Finset.card_le_card_of_injOn (fun g => n + g)
    · intro g hg
      rw [Finset.mem_coe, Finset.mem_filter] at hg
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨hg.2, Nat.le_add_right n g, ?_⟩
      have e : n + g - n = g := by omega
      show n + g - n ∈ F
      rw [e]
      exact hg.1
    · intro a _ b _ h
      exact Nat.add_left_cancel h
  have d1 : Disjoint (U.filter (fun w => w < n)) (U.filter (fun w => n ≤ w ∧ w - n ∉ F)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have a1 := (Finset.mem_filter.mp h1).2
    have a2 := (Finset.mem_filter.mp h2).2.1
    omega
  have d2 : Disjoint (U.filter (fun w => w < n) ∪ U.filter (fun w => n ≤ w ∧ w - n ∉ F))
      (U.filter (fun w => n ≤ w ∧ w - n ∈ F)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have a2 := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h | h
    · have a1 := (Finset.mem_filter.mp h).2
      omega
    · exact (Finset.mem_filter.mp h).2.2 a2.2
  have hs : (U.filter (fun w => w < n) ∪ U.filter (fun w => n ≤ w ∧ w - n ∉ F))
      ∪ U.filter (fun w => n ≤ w ∧ w - n ∈ F) ⊆ U :=
    Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1] at hc
  omega

end PEqualNP.Outside.L_meta_3465

open PEqualNP.Outside.L_meta_3465 in
theorem PEqualNP.Outside.L_meta_3465 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hC hF
  refine (three n _ F).trans ?_
  have h : (F.biUnion (fun g =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).card ≤ F.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro g hg
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt C g = C.gates[g]'(hF g hg) :=
      List.getD_eq_getElem _ _ (hF g hg)
    have l : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length = 2 := by
      rw [e]
      exact hC.2.2 _ (List.getElem_mem _)
    exact l ▸ List.toFinset_card_le _
  omega
