import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5337

lemma key (n d : ℕ) (E : Finset (Fin n × Fin n)) : ∀ m (A B : Finset (Fin n)),
    A.card + B.card = m →
    d * (A.card + B.card) < (E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card →
    ∃ (A' : Finset (Fin n)) (B' : Finset (Fin n)), A'.Nonempty ∧ B'.Nonempty ∧
      (∀ a ∈ A', d < {b ∈ B' | (a, b) ∈ E}.card) ∧
      ∀ b ∈ B', d < {a ∈ A' | (a, b) ∈ E}.card := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro A B hm h
  by_cases ha : ∃ a ∈ A, {b ∈ B | (a, b) ∈ E}.card ≤ d
  · obtain ⟨a, haA, hd⟩ := ha
    have hle : (E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card ≤
        (E.filter (fun p => p.1 ∈ A.erase a ∧ p.2 ∈ B)).card +
          {b ∈ B | (a, b) ∈ E}.card := by
      refine le_trans (Finset.card_le_card ?_) (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_left (Finset.card_image_le (f := fun b => (a, b))) _))
      intro p hp
      simp only [Finset.mem_filter] at hp
      by_cases hpa : p.1 = a
      · apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨p.2, ?_, ?_⟩
        · simp only [Finset.mem_filter]; refine ⟨hp.2.2, ?_⟩; rw [← hpa]; exact hp.1
        · rw [← hpa]
      · apply Finset.mem_union_left
        simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨hp.1, ⟨hpa, hp.2.1⟩, hp.2.2⟩
    have hc := Finset.card_erase_add_one haA
    exact ih _ (by omega) (A.erase a) B rfl (by
      have : d * ((A.erase a).card + B.card) + d = d * (A.card + B.card) := by
        rw [← hc]; ring
      omega)
  by_cases hb : ∃ b ∈ B, {a ∈ A | (a, b) ∈ E}.card ≤ d
  · obtain ⟨b, hbB, hd⟩ := hb
    have hle : (E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).card ≤
        (E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B.erase b)).card +
          {a ∈ A | (a, b) ∈ E}.card := by
      refine le_trans (Finset.card_le_card ?_) (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_left (Finset.card_image_le (f := fun a => (a, b))) _))
      intro p hp
      simp only [Finset.mem_filter] at hp
      by_cases hpb : p.2 = b
      · apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨p.1, ?_, ?_⟩
        · simp only [Finset.mem_filter]; refine ⟨hp.2.1, ?_⟩; rw [← hpb]; exact hp.1
        · rw [← hpb]
      · apply Finset.mem_union_left
        simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨hp.1, hp.2.1, hpb, hp.2.2⟩
    have hc := Finset.card_erase_add_one hbB
    exact ih _ (by omega) A (B.erase b) rfl (by
      have : d * (A.card + (B.erase b).card) + d = d * (A.card + B.card) := by
        rw [← hc]; ring
      omega)
  push_neg at ha hb
  obtain ⟨p, hp⟩ : (E.filter (fun p => p.1 ∈ A ∧ p.2 ∈ B)).Nonempty :=
    Finset.card_pos.mp (by omega)
  simp only [Finset.mem_filter] at hp
  exact ⟨A, B, ⟨_, hp.2.1⟩, ⟨_, hp.2.2⟩, ha, hb⟩

end PEqualNP.Outside.L_meta_5337

theorem PEqualNP.Outside.L_meta_5337 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)), x2 * (x1 + x1) < x3.card → ∃ (x5 : Finset (Fin x1)) (x6 : Finset (Fin x1)), x5.Nonempty ∧ x6.Nonempty ∧ (∀ x7 ∈ x5, x2 < {x9 ∈ x6 | (x7, x9) ∈ x3}.card) ∧ ∀ x7 ∈ x6, x2 < {x9 ∈ x5 | (x9, x7) ∈ x3}.card := by
  intro n d E h
  refine PEqualNP.Outside.L_meta_5337.key n d E _ Finset.univ Finset.univ rfl ?_
  simpa [Finset.card_univ, Fintype.card_fin] using h
