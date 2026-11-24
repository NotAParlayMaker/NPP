import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1539 : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (P : Finset (K × K)) (a m : K) (T : Finset K), 2 * P.card < Fintype.card K → 2 * T.card ≤ Fintype.card K → ∃ b : K, (∀ pt ∈ P, pt.2 ≠ m * pt.1 + b) ∧ m * a + b ∉ T := by
  intro K _ _ _ P a m T hP hT
  have hcard : (P.image (fun pt => pt.2 - m * pt.1) ∪ T.image (fun t => t - m * a)).card < (Finset.univ : Finset K).card := by
    have h1 := Finset.card_union_le (P.image (fun pt => pt.2 - m * pt.1)) (T.image (fun t => t - m * a))
    have h2 := Finset.card_image_le (s := P) (f := fun pt => pt.2 - m * pt.1)
    have h3 := Finset.card_image_le (s := T) (f := fun t => t - m * a)
    rw [Finset.card_univ]
    omega
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_union, not_or] at hb
  refine ⟨b, ?_, ?_⟩
  · intro pt hpt h
    exact hb.1 (Finset.mem_image.mpr ⟨pt, hpt, by rw [h]; ring⟩)
  · intro h
    exact hb.2 (Finset.mem_image.mpr ⟨m * a + b, h, by ring⟩)
