import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F h hF
  set R := F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset) with hR
  have h3 : (F.filter (fun g => n + g ∈ R)).card = (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card := by
    apply Finset.card_nbij' (fun g => n + g) (fun w => w - n)
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
      refine ⟨ha.2, by omega, ?_⟩
      simpa using ha.1
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
      refine ⟨ha.2.2, ?_⟩
      have : n + (a - n) = a := by omega
      rw [this]; exact ha.1
    · intro a ha
      simp
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
      show n + (a - n) = a
      omega
  have hp1 := Finset.card_filter_add_card_filter_not (s := R) (fun w => w < n)
  have hp2 := Finset.card_filter_add_card_filter_not (s := R.filter (fun w => ¬ w < n)) (fun w => w - n ∈ F)
  rw [Finset.filter_filter, Finset.filter_filter] at hp2
  have e1 : R.filter (fun w => ¬ w < n ∧ w - n ∈ F) = R.filter (fun w => n ≤ w ∧ w - n ∈ F) := by
    apply Finset.filter_congr; intro x _; constructor <;> intro hx <;> exact ⟨by omega, hx.2⟩
  have e2 : R.filter (fun w => ¬ w < n ∧ ¬ w - n ∈ F) = R.filter (fun w => n ≤ w ∧ w - n ∉ F) := by
    apply Finset.filter_congr; intro x _; constructor <;> intro hx <;> exact ⟨by omega, hx.2⟩
  rw [e1, e2] at hp2
  have hle : R.card ≤ 2 * F.card := by
    calc R.card ≤ ∑ g ∈ F, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ g ∈ F, 2 := by
        apply Finset.sum_le_sum
        intro g hg
        have hm : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          rw [List.getD_eq_getElem _ _ (hF g hg)]
          exact List.getElem_mem _
        exact (List.toFinset_card_le _).trans (h.2.2 _ hm).le
    _ = 2 * F.card := by simp [mul_comm]
  omega
