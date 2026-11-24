import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3454

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem card_reads_le (C : Circuit) (F : Finset ℕ)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hF : ∀ g ∈ F, g < C.gates.length) :
    (F.biUnion (fun g => (NestedCover.gateAt C g).inputs.toFinset)).card ≤ 2 * F.card := by
  have hle : ∀ g ∈ F, ((NestedCover.gateAt C g).inputs.toFinset).card ≤ 2 := by
    intro g hg
    have hlt : g < C.gates.length := hF g hg
    have hmem : NestedCover.gateAt C g ∈ C.gates := by
      unfold NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    calc ((NestedCover.gateAt C g).inputs.toFinset).card
        ≤ (NestedCover.gateAt C g).inputs.length := List.toFinset_card_le _
      _ = 2 := h2 _ hmem
  calc (F.biUnion (fun g => (NestedCover.gateAt C g).inputs.toFinset)).card
      ≤ ∑ g ∈ F, ((NestedCover.gateAt C g).inputs.toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ F, 2 := Finset.sum_le_sum hle
    _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_shift (R F : Finset ℕ) (n : ℕ) :
    (F.filter (fun g => n + g ∈ R)).card = (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card := by
  apply Finset.card_bij (fun g _ => n + g)
  · intro g hg
    rw [Finset.mem_filter] at hg
    rw [Finset.mem_filter]
    refine ⟨hg.2, Nat.le_add_right n g, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact hg.1
  · intro a _ b _ h
    exact Nat.add_left_cancel h
  · intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwR, hnw, hwF⟩ := hw
    have hw' : n + (w - n) = w := Nat.add_sub_cancel' hnw
    refine ⟨w - n, ?_, hw'⟩
    rw [Finset.mem_filter]
    refine ⟨hwF, ?_⟩
    rw [hw']
    exact hwR

theorem card_split (R F : Finset ℕ) (n : ℕ) :
    (R.filter (fun w => w < n)).card + (R.filter (fun w => n ≤ w ∧ w - n ∉ F)).card
      + (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card = R.card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h1 : w < n
  · have h2 : ¬ n ≤ w := Nat.not_le.mpr h1
    simp [h1, h2]
  · have h2 : n ≤ w := Nat.not_lt.mp h1
    by_cases h3 : w - n ∈ F
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]

theorem slot_count (R F : Finset ℕ) (n : ℕ) :
    (R.filter (fun w => w < n)).card + (R.filter (fun w => n ≤ w ∧ w - n ∉ F)).card
      + (F.filter (fun g => n + g ∈ R)).card = R.card := by
  rw [card_shift R F n]
  exact card_split R F n

end PEqualNP.Outside.L_meta_3454

theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hAO hF
  rw [PEqualNP.Outside.L_meta_3454.slot_count]
  exact PEqualNP.Outside.L_meta_3454.card_reads_le C F hAO.2.2 hF
