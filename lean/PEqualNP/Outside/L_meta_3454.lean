import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3454

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem card_inputs_le (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) (g : ℕ)
    (hg : g < C.gates.length) : (gateAt C g).inputs.toFinset.card ≤ 2 := by
  have hmem : gateAt C g ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hg]
    exact List.getElem_mem hg
  have hl := h.2.2 _ hmem
  calc (gateAt C g).inputs.toFinset.card ≤ (gateAt C g).inputs.length := List.toFinset_card_le _
    _ = 2 := hl

end PEqualNP.Outside.L_meta_3454

theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F h hF
  set R := F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset) with hR
  have hRcard : R.card ≤ 2 * F.card := by
    calc R.card ≤ ∑ g ∈ F, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _g ∈ F, 2 := Finset.sum_le_sum (fun g hg =>
          PEqualNP.Outside.L_meta_3454.card_inputs_le n C h g (hF g hg))
      _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h3 : (F.filter (fun g => n + g ∈ R)).card ≤ (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card := by
    apply Finset.card_le_card_of_injOn (fun g => n + g)
    · intro g hg
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hg ⊢
      refine ⟨hg.2, by omega, ?_⟩
      simpa using hg.1
    · intro a _ b _ hab
      simpa using hab
  have hsplit : (R.filter (fun w => w < n)).card + (R.filter (fun w => n ≤ w ∧ w - n ∉ F)).card
      + (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card = R.card := by
    rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
    · congr 1
      ext w
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨h1, _⟩ | ⟨h1, _⟩) | ⟨h1, _⟩) <;> exact h1
      · intro hw
        by_cases h1 : w < n
        · exact Or.inl (Or.inl ⟨hw, h1⟩)
        · by_cases h2 : w - n ∈ F
          · exact Or.inr ⟨hw, by omega, h2⟩
          · exact Or.inl (Or.inr ⟨hw, by omega, h2⟩)
    · rw [Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_union, Finset.mem_filter] at hw1 hw2
      rcases hw1 with ⟨_, h1⟩ | ⟨_, h1, h2⟩
      · omega
      · exact h2 hw2.2.2
    · rw [Finset.disjoint_left]
      intro w hw1 hw2
      simp only [Finset.mem_filter] at hw1 hw2
      omega
  omega
