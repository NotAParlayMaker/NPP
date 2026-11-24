import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3454

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma inputs_len_two (n : ℕ) (C : Circuit) (F : Finset ℕ) (hAO : IsAO2 n C)
    (hF : ∀ g ∈ F, g < C.gates.length) (g : ℕ) (hg : g ∈ F) :
    (gateAt C g).inputs.length = 2 := by
  have hglt := hF g hg
  have h2 : (C.gates[g]).inputs.length = 2 := hAO.2.2 _ (List.getElem_mem hglt)
  rw [gateAt, List.getD_eq_getElem _ _ hglt]
  exact h2

end PEqualNP.Outside.L_meta_3454

open PEqualNP.Outside.L_meta_3454 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm


theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hAO hF
  set R : Finset ℕ := F.biUnion (fun g => (gateAt C g).inputs.toFinset)
  have hRle : R.card ≤ 2 * F.card := by
    have hb := Finset.card_biUnion_le (s := F) (t := fun g => (gateAt C g).inputs.toFinset)
    calc R.card ≤ ∑ g ∈ F, (gateAt C g).inputs.toFinset.card := hb
      _ ≤ ∑ _g ∈ F, 2 := by
          apply Finset.sum_le_sum
          intro g hg
          have h1 := List.toFinset_card_le (l := (gateAt C g).inputs)
          exact h1.trans (le_of_eq (inputs_len_two n C F hAO hF g hg))
      _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hdisj12 : Disjoint (R.filter (fun w => w < n)) (R.filter (fun w => n ≤ w ∧ w - n ∉ F)) := by
    rw [Finset.disjoint_filter]
    intro w _ h1 h2
    obtain ⟨h2a, _⟩ := h2
    omega
  have hdisj1i : Disjoint (R.filter (fun w => w < n))
      ((F.filter (fun g => n + g ∈ R)).image (fun g => n + g)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [Finset.mem_filter] at hw1
    simp only [Finset.mem_image] at hw2
    obtain ⟨g, _hg, rfl⟩ := hw2
    omega
  have hdisj2i : Disjoint (R.filter (fun w => n ≤ w ∧ w - n ∉ F))
      ((F.filter (fun g => n + g ∈ R)).image (fun g => n + g)) := by
    rw [Finset.disjoint_left]
    intro w hw2 hwi
    simp only [Finset.mem_filter] at hw2
    simp only [Finset.mem_image] at hwi
    obtain ⟨g, hg, rfl⟩ := hwi
    have hgF : g ∈ F := (Finset.mem_filter.mp hg).1
    have hsub : (n + g) - n = g := by omega
    exact hw2.2.2 (hsub.symm ▸ hgF)
  have hunion : R.filter (fun w => w < n) ∪ R.filter (fun w => n ≤ w ∧ w - n ∉ F)
        ∪ (F.filter (fun g => n + g ∈ R)).image (fun g => n + g) = R := by
    ext w
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ((⟨hw, _⟩ | ⟨hw, _⟩) | ⟨g, hg, rfl⟩)
      · exact hw
      · exact hw
      · exact hg.2
    · intro hwR
      by_cases hlt : w < n
      · exact Or.inl (Or.inl ⟨hwR, hlt⟩)
      · have hge : n ≤ w := Nat.le_of_not_lt hlt
        by_cases hmem : w - n ∈ F
        · refine Or.inr ⟨w - n, ⟨hmem, ?_⟩, ?_⟩
          · have hw2 : n + (w - n) = w := by omega
            rw [hw2]
            exact hwR
          · omega
        · exact Or.inl (Or.inr ⟨hwR, hge, hmem⟩)
  have hcard : (R.filter (fun w => w < n) ∪ R.filter (fun w => n ≤ w ∧ w - n ∉ F)
        ∪ (F.filter (fun g => n + g ∈ R)).image (fun g => n + g)).card
      = (R.filter (fun w => w < n)).card + (R.filter (fun w => n ≤ w ∧ w - n ∉ F)).card
        + (F.filter (fun g => n + g ∈ R)).card := by
    have hdisjU : Disjoint ((R.filter (fun w => w < n)) ∪ (R.filter (fun w => n ≤ w ∧ w - n ∉ F)))
        ((F.filter (fun g => n + g ∈ R)).image (fun g => n + g)) :=
      Finset.disjoint_union_left.mpr ⟨hdisj1i, hdisj2i⟩
    rw [Finset.card_union_of_disjoint hdisjU, Finset.card_union_of_disjoint hdisj12,
      Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)]
  rw [hunion] at hcard
  rw [← hcard]
  exact hRle

