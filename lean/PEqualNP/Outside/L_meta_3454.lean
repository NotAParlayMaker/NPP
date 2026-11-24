import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3454_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- A gate of F reads at most two distinct wires.
theorem inputs_card_le (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (g : ℕ)
    (hg : g < C.gates.length) : (gateAt C g).inputs.toFinset.card ≤ 2 := by
  have hmem : gateAt C g ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hg]
    exact List.getElem_mem hg
  calc (gateAt C g).inputs.toFinset.card ≤ (gateAt C g).inputs.length := List.toFinset_card_le _
    _ = 2 := hC.2.2 _ hmem

-- The read wires split into inputs, gates outside F and gates of F; the last part is a copy
-- of the gates of F that some gate of F reads.
theorem split (n : ℕ) (F R : Finset ℕ) :
    (R.filter (fun w => w < n)).card + (R.filter (fun w => n ≤ w ∧ w - n ∉ F)).card +
      (F.filter (fun g => n + g ∈ R)).card = R.card := by
  have e1 := Finset.card_filter_add_card_filter_not (s := R) (fun w => w < n)
  have e2 := Finset.card_filter_add_card_filter_not
    (s := R.filter (fun w => ¬ w < n)) (fun w => w - n ∉ F)
  have e3 : R.filter (fun w => n ≤ w ∧ w - n ∉ F) =
      (R.filter (fun w => ¬ w < n)).filter (fun w => w - n ∉ F) := by
    ext w
    simp only [Finset.mem_filter, not_lt]
    tauto
  have e4 : (R.filter (fun w => ¬ w < n)).filter (fun w => ¬ (w - n ∉ F)) =
      (F.filter (fun g => n + g ∈ R)).map ⟨(n + ·), add_right_injective n⟩ := by
    ext w
    simp only [Finset.mem_filter, not_lt, not_not, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨hR, hn⟩, hF⟩
      exact ⟨w - n, ⟨hF, by rwa [Nat.add_sub_cancel' hn]⟩, Nat.add_sub_cancel' hn⟩
    · rintro ⟨g, ⟨hF, hR⟩, rfl⟩
      exact ⟨⟨hR, Nat.le_add_right n g⟩, by rwa [Nat.add_sub_cancel_left]⟩
  have e5 := Finset.card_map (s := F.filter (fun g => n + g ∈ R)) ⟨(n + ·), add_right_injective n⟩
  rw [e4] at e2
  rw [e3]
  omega

end PEqualNP.Outside.L_meta_3454_aux

theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hC hF
  have hR := PEqualNP.Outside.L_meta_3454_aux.split n F
    (F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset))
  rw [hR]
  calc (F.biUnion fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset).card
      ≤ ∑ g ∈ F, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset.card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _g ∈ F, 2 := Finset.sum_le_sum fun g hg =>
        PEqualNP.Outside.L_meta_3454_aux.inputs_card_le n C hC g (hF g hg)
    _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
