import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hC hF
  unfold PEqualNP.TopForm.IsAO2 at hC
  obtain ⟨_, _, h2⟩ := hC
  set R := F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset) with hR
  have hlen : ∀ g ∈ F, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset).card ≤ 2 := by
    intro g hg
    have hlt := hF g hg
    have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    calc ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset).card
        ≤ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length := List.toFinset_card_le _
      _ = 2 := h2 _ hmem
  have h1 : (F.filter (fun g => n + g ∈ R)).card ≤ (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card := by
    rw [← Finset.card_image_of_injective (F.filter (fun g => n + g ∈ R)) (add_right_injective n)]
    apply Finset.card_le_card
    intro w hw
    simp only [Finset.mem_image, Finset.mem_filter] at hw ⊢
    obtain ⟨g, ⟨hgF, hgR⟩, rfl⟩ := hw
    exact ⟨hgR, Nat.le_add_right n g, by simpa using hgF⟩
  have h3 : (R.filter (fun w => w < n)).card + (R.filter (fun w => n ≤ w ∧ w - n ∉ F)).card
      + (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card ≤ R.card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : w < n
    · have hw' : ¬ n ≤ w := by omega
      simp [hw, hw']
    · have hw' : n ≤ w := by omega
      by_cases hm : w - n ∈ F
      · simp [hw, hw', hm]
      · simp [hw, hw', hm]
  have h4 : R.card ≤ 2 * F.card := by
    calc R.card ≤ ∑ g ∈ F, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _g ∈ F, 2 := Finset.sum_le_sum hlen
      _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega
