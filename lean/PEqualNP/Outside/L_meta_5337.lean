import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5337
open PEqualNP.CircuitLowerBounds



theorem splitA {N : ℕ} (S : Finset (Fin N × Fin N)) (A B : Finset (Fin N)) (a : Fin N) :
    (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B).card
      ≤ (S.filter fun p => p.1 ∈ A.erase a ∧ p.2 ∈ B).card + (B.filter fun b => (a, b) ∈ S).card := by
  have hsub : (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B)
      ⊆ (S.filter fun p => p.1 ∈ A.erase a ∧ p.2 ∈ B) ∪ (B.filter fun b => (a, b) ∈ S).image (fun b => (a, b)) := by
    intro p hp
    obtain ⟨hpS, hpA, hpB⟩ := Finset.mem_filter.1 hp
    by_cases h : p.1 = a
    · apply Finset.mem_union_right
      refine Finset.mem_image.2 ⟨p.2, Finset.mem_filter.2 ⟨hpB, ?_⟩, ?_⟩
      · rw [← h]; exact hpS
      · rw [← h]
    · apply Finset.mem_union_left
      exact Finset.mem_filter.2 ⟨hpS, Finset.mem_erase.2 ⟨h, hpA⟩, hpB⟩
  exact le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add_left Finset.card_image_le _))

theorem splitB {N : ℕ} (S : Finset (Fin N × Fin N)) (A B : Finset (Fin N)) (b : Fin N) :
    (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B).card
      ≤ (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B.erase b).card + (A.filter fun a => (a, b) ∈ S).card := by
  have hsub : (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B)
      ⊆ (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B.erase b) ∪ (A.filter fun a => (a, b) ∈ S).image (fun a => (a, b)) := by
    intro p hp
    obtain ⟨hpS, hpA, hpB⟩ := Finset.mem_filter.1 hp
    by_cases h : p.2 = b
    · apply Finset.mem_union_right
      refine Finset.mem_image.2 ⟨p.1, Finset.mem_filter.2 ⟨hpA, ?_⟩, ?_⟩
      · rw [← h]; exact hpS
      · rw [← h]
    · apply Finset.mem_union_left
      exact Finset.mem_filter.2 ⟨hpS, hpA, Finset.mem_erase.2 ⟨h, hpB⟩⟩
  exact le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add_left Finset.card_image_le _))

theorem mulpred (k a b : ℕ) (ha : 0 < a) : k * (a - 1 + b) + k = k * (a + b) := by
  obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt ha)
  rw [hc]
  simp
  ring

theorem mulpred2 (k a b : ℕ) (hb : 0 < b) : k * (a + (b - 1)) + k = k * (a + b) := by
  obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hb)
  rw [hc]
  simp
  ring

end PEqualNP.Outside.L_meta_5337

open PEqualNP.Outside.L_meta_5337 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5337 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)), x2 * (x1 + x1) < x3.card → ∃ (x5 : Finset (Fin x1)) (x6 : Finset (Fin x1)), x5.Nonempty ∧ x6.Nonempty ∧ (∀ x7 ∈ x5, x2 < {x9 ∈ x6 | (x7, x9) ∈ x3}.card) ∧ ∀ x7 ∈ x6, x2 < {x9 ∈ x5 | (x9, x7) ∈ x3}.card := by
  intro N k S h
  obtain ⟨⟨A, B⟩, _, hmin⟩ := Finite.exists_le_minimal
    (p := fun q : Finset (Fin N) × Finset (Fin N) =>
      k * (q.1.card + q.2.card) < (S.filter fun p => p.1 ∈ q.1 ∧ p.2 ∈ q.2).card)
    (a := (Finset.univ, Finset.univ)) (by simpa using h)
  have hP : k * (A.card + B.card) < (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B).card := hmin.1
  have hpos : 0 < (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B).card := lt_of_le_of_lt (Nat.zero_le _) hP
  obtain ⟨p0, hp0⟩ := Finset.card_pos.1 hpos
  obtain ⟨_, hp0A, hp0B⟩ := Finset.mem_filter.1 hp0
  refine ⟨A, B, ⟨p0.1, hp0A⟩, ⟨p0.2, hp0B⟩, ?_, ?_⟩
  · intro a ha
    by_contra hd
    have hd' : (B.filter fun b => (a, b) ∈ S).card ≤ k := Nat.le_of_not_lt hd
    have hs := splitA S A B a
    have he := mulpred k A.card B.card (Finset.card_pos.2 ⟨a, ha⟩)
    have hP' : k * ((A.erase a).card + B.card) < (S.filter fun p => p.1 ∈ A.erase a ∧ p.2 ∈ B).card := by
      rw [Finset.card_erase_of_mem ha]
      linarith
    have hle := hmin.2 (y := (A.erase a, B)) hP' ⟨Finset.erase_subset _ _, le_refl _⟩
    exact (Finset.mem_erase.1 (hle.1 ha)).1 rfl
  · intro b hb
    by_contra hd
    have hd' : (A.filter fun a => (a, b) ∈ S).card ≤ k := Nat.le_of_not_lt hd
    have hs := splitB S A B b
    have he := mulpred2 k A.card B.card (Finset.card_pos.2 ⟨b, hb⟩)
    have hP' : k * (A.card + (B.erase b).card) < (S.filter fun p => p.1 ∈ A ∧ p.2 ∈ B.erase b).card := by
      rw [Finset.card_erase_of_mem hb]
      linarith
    have hle := hmin.2 (y := (A, B.erase b)) hP' ⟨le_refl _, Finset.erase_subset _ _⟩
    exact (Finset.mem_erase.1 (hle.2 hb)).1 rfl
