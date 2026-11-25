import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6597

-- Pigeonhole on the first index at which each element has the property.
theorem pig {α : Type} (P : ℕ → α → Prop) (a b c : ℕ) (E : Finset α) (hc : c < a + b)
    (hall : ∀ e ∈ E, P c e) (hnone : ∀ t < a, ∀ e ∈ E, ¬P t e) (hbig : 24 * b < E.card) :
    ∃ j < b, ∃ S ⊆ E, 24 < S.card ∧ ∀ e ∈ S, P (a + j) e ∧ ∀ t < a + j, ¬P t e := by
  classical
  let f : α → ℕ := fun e => if h : ∃ t, P t e then Nat.find h - a else 0
  have hf : ∀ e ∈ E, f e ∈ Finset.range b := by
    intro e he
    have h : ∃ t, P t e := ⟨c, hall e he⟩
    have h1 : Nat.find h ≤ c := Nat.find_min' h (hall e he)
    have hca : a ≤ c := by
      by_contra hlt
      exact hnone c (by omega) e he (hall e he)
    show (if h : ∃ t, P t e then Nat.find h - a else 0) ∈ Finset.range b
    rw [dif_pos h, Finset.mem_range]
    omega
  have hcard : (Finset.range b).card * 24 < E.card := by
    rw [Finset.card_range]; omega
  obtain ⟨j, hj, hjc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hcard
  refine ⟨j, Finset.mem_range.mp hj, E.filter (fun e => f e = j), Finset.filter_subset _ _, hjc, ?_⟩
  intro e he
  obtain ⟨heE, hfe⟩ := Finset.mem_filter.mp he
  have h : ∃ t, P t e := ⟨c, hall e heE⟩
  have hfe' : Nat.find h - a = j := by
    have : f e = Nat.find h - a := by
      show (if h : ∃ t, P t e then Nat.find h - a else 0) = _
      rw [dif_pos h]
    rw [← this]; exact hfe
  have hge : a ≤ Nat.find h := by
    by_contra hlt
    exact hnone (Nat.find h) (by omega) e heE (Nat.find_spec h)
  have heq : a + j = Nat.find h := by omega
  refine ⟨by rw [heq]; exact Nat.find_spec h, fun t ht => ?_⟩
  rw [heq] at ht
  exact Nat.find_min h ht

end PEqualNP.Outside.L_meta_6597

theorem PEqualNP.Outside.L_meta_6597 : ∀ (x1 x2 x3 x4 : ℕ) (x5 : Finset (Fin x1 × Fin x1)) (x6 : ℕ → Set ((Fin x1 × Fin x1) × Finset (Fin x1))),   have x7 : ℕ → Fin x1 × Fin x1 → Prop := fun (x7 : ℕ) (x8 : Fin x1 × Fin x1) => (x8, ∅) ∈ x6 x7 ∧ (x8, {x8.2}) ∈ x6 x7;   x4 < x2 + x3 → (∀ x9 ∈ x5, x7 x4 x9) → (∀ x10 < x2, ∀ x12 ∈ x5, ¬x7 x10 x12) → (24 : ℕ) * x3 < x5.card → ∃ x12 < x3, ∃ x13 ⊆ x5, (24 : ℕ) < x13.card ∧ ∀ x14 ∈ x13, x7 (x2 + x12) x14 ∧ ∀ x16 < x2 + x12, ¬x7 x16 x14 := by
  intro n a b c E F
  exact PEqualNP.Outside.L_meta_6597.pig
    (fun (t : ℕ) (e : Fin n × Fin n) => (e, ∅) ∈ F t ∧ (e, {e.2}) ∈ F t) a b c E
