import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1539 : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (P : Finset (K × K)) (a m : K) (T : Finset K), 2 * P.card < Fintype.card K → 2 * T.card ≤ Fintype.card K → ∃ b : K, (∀ pt ∈ P, pt.2 ≠ m * pt.1 + b) ∧ m * a + b ∉ T := by
  intro K _ _ _ P a m T hP hT
  have hcard : (P.image (fun pt => pt.2 - m * pt.1) ∪ T.image (fun t => t - m * a)).card
      < Fintype.card K := by
    calc (P.image (fun pt => pt.2 - m * pt.1) ∪ T.image (fun t => t - m * a)).card
        ≤ (P.image (fun pt => pt.2 - m * pt.1)).card + (T.image (fun t => t - m * a)).card :=
          Finset.card_union_le _ _
      _ ≤ P.card + T.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ < Fintype.card K := by omega
  obtain ⟨b, hb⟩ : ∃ b, b ∉ P.image (fun pt => pt.2 - m * pt.1) ∪ T.image (fun t => t - m * a) := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hsub : (Finset.univ : Finset K) ⊆
        P.image (fun pt => pt.2 - m * pt.1) ∪ T.image (fun t => t - m * a) := fun x _ => h x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    omega
  refine ⟨b, ?_, ?_⟩
  · intro pt hpt heq
    apply hb
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨pt, hpt, by rw [heq]; ring⟩
  · intro hmem
    apply hb
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨m * a + b, hmem, by ring⟩
