import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1539 : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (P : Finset (K × K)) (a m : K) (T : Finset K), 2 * P.card < Fintype.card K → 2 * T.card ≤ Fintype.card K → ∃ b : K, (∀ pt ∈ P, pt.2 ≠ m * pt.1 + b) ∧ m * a + b ∉ T := by
  intro K instF instT instD P a m T hP hT
  have h1 : (P.image (fun pt : K × K => pt.2 - m * pt.1)).card ≤ P.card := Finset.card_image_le
  have h2 : (T.image (fun t : K => t - m * a)).card ≤ T.card := Finset.card_image_le
  have h3 := Finset.card_union_le (P.image (fun pt : K × K => pt.2 - m * pt.1)) (T.image (fun t : K => t - m * a))
  have hcard : (P.image (fun pt : K × K => pt.2 - m * pt.1) ∪ T.image (fun t : K => t - m * a)).card < Fintype.card K := by
    omega
  have hex : ∃ b : K, b ∉ P.image (fun pt : K × K => pt.2 - m * pt.1) ∪ T.image (fun t : K => t - m * a) := by
    by_contra hno
    have hall : ∀ b : K, b ∈ P.image (fun pt : K × K => pt.2 - m * pt.1) ∪ T.image (fun t : K => t - m * a) := by
      intro b
      by_contra hb
      exact hno ⟨b, hb⟩
    have huniv := Finset.eq_univ_iff_forall.mpr hall
    rw [huniv, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨b, hb⟩ := hex
  refine ⟨b, ?_, ?_⟩
  · intro pt hpt heq
    apply hb
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨pt, hpt, ?_⟩
    rw [heq]
    ring
  · intro hmem
    apply hb
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨m * a + b, hmem, ?_⟩
    ring
