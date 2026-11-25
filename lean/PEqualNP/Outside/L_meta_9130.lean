import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9130_aux

theorem sum_bound (x2 x3 c : ℕ) (h : x2 ≤ x3) :
    ∑ i ∈ Finset.range x3, (if i < x2 then c else 0) = x2 * c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range x2, (if i < x2 then c else 0) = ∑ i ∈ Finset.range x2, c := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have h2 : ∑ i ∈ Finset.range d, (if x2 + i < x2 then c else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp
  rw [h1, h2]
  simp

end PEqualNP.Outside.L_meta_9130_aux

theorem PEqualNP.Outside.L_meta_9130 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Fin x2 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x2), Fintype.card { x7 : Fin x2 // x4 x7 x6 } = x1 + (1 : ℕ)) → x2 ≤ x3 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x3 → ∃ (x9 : Fin x3 → Finset (Fin x2)) (x10 : Fin x3 → Finset (Fin x2)), (∀ (x11 : Fin x3), ∀ x12 ∈ x9 x11, ∀ x14 ∈ x10 x11, x4 x12 x14) ∧ (∀ (x11 x12 : Fin x2), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x9 x14 ∧ x12 ∈ x10 x14) ∧ ∑ x11 : Fin x3, ((x9 x11).card + (x10 x11).card) ≤ (100 : ℕ) * x3 + x2 := by
  intro x1 x2 x3 x4 x5 hc h23 h100
  refine ⟨fun k => if h : k.val < x2 then Finset.univ.filter (fun u => x4 u ⟨k.val, h⟩) else ∅,
    fun k => if h : k.val < x2 then {⟨k.val, h⟩} else ∅, ?_, ?_, ?_⟩
  · intro k a ha b hb
    by_cases h : k.val < x2
    · simp only [h, dif_pos] at ha hb
      rw [Finset.mem_singleton] at hb
      subst hb
      simpa using ha
    · simp [h] at ha
  · intro a b hab
    refine ⟨⟨b.val, lt_of_lt_of_le b.isLt h23⟩, ?_, ?_⟩
    · simp [b.isLt, hab]
    · simp [b.isLt]
  · have key : ∀ k : Fin x3, ((if h : k.val < x2 then Finset.univ.filter (fun u => x4 u ⟨k.val, h⟩) else ∅).card
        + (if h : k.val < x2 then ({⟨k.val, h⟩} : Finset (Fin x2)) else ∅).card)
        = (if k.val < x2 then x1 + 1 + 1 else 0) := by
      intro k
      by_cases h : k.val < x2
      · simp only [h, dif_pos, if_true, Finset.card_singleton]
        rw [← Fintype.card_subtype, hc]
      · simp [h]
    rw [Finset.sum_congr rfl (fun k _ => key k)]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < x2 then x1 + 1 + 1 else 0) x3]
    rw [PEqualNP.Outside.L_meta_9130_aux.sum_bound x2 x3 _ h23]
    nlinarith
