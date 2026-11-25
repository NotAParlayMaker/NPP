import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7505_aux

theorem exmin {α : Type} [DecidableEq α] (x2 : Finset (Finset α)) :
    ∀ n : ℕ, ∀ x7 ∈ x2, x7.card ≤ n →
      ∃ x8 ∈ x2, x8 ⊆ x7 ∧ ∀ x9 ∈ x2, x9 ⊆ x8 → x9 = x8 := by
  intro n
  induction n with
  | zero =>
    intro x7 h7 hc
    by_cases h : ∀ x9 ∈ x2, x9 ⊆ x7 → x9 = x7
    · exact ⟨x7, h7, subset_rfl, h⟩
    · push Not at h
      obtain ⟨x9, h9, hs, hne⟩ := h
      have := Finset.card_lt_card (ssubset_of_subset_of_ne hs hne)
      omega
  | succ n ih =>
    intro x7 h7 hc
    by_cases h : ∀ x9 ∈ x2, x9 ⊆ x7 → x9 = x7
    · exact ⟨x7, h7, subset_rfl, h⟩
    · push Not at h
      obtain ⟨x9, h9, hs, hne⟩ := h
      have := Finset.card_lt_card (ssubset_of_subset_of_ne hs hne)
      obtain ⟨x8, h8, hs8, hm⟩ := ih x9 h9 (by omega)
      exact ⟨x8, h8, hs8.trans hs, hm⟩

theorem key (x1 : ℕ) (x3 : Bool) (x4 : Fin x1 → Bool) (i : ℕ)
    (h : ¬ (if x3 = Bool.true then x1 ≤ i else i < x1)) :
    (if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 Bool.false
      else List.replicate x1 Bool.false ++ List.ofFn x4).getD i Bool.false =
    (if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 Bool.true
      else List.replicate x1 Bool.true ++ List.ofFn x4).getD i Bool.false := by
  cases x3
  · simp at h
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h]
  · simp at h
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, h]

theorem nonc (x1 : ℕ) (x3 : Bool) (x4 : Fin x1 → Bool) (i : ℕ)
    (h : (if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 Bool.false
      else List.replicate x1 Bool.false ++ List.ofFn x4).getD i Bool.false = Bool.true) :
    ¬ (if x3 = Bool.true then x1 ≤ i else i < x1) := by
  intro hc
  cases x3
  · simp at hc
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hc] at h
  · simp at hc
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, hc, List.getElem?_replicate] at h
    split_ifs at h <;> simp at h

end PEqualNP.Outside.L_meta_7505_aux

theorem PEqualNP.Outside.L_meta_7505 : ∀ (x1 : ℕ) (x2 : Finset (Finset (Fin (x1 + x1)))) (x3 : Bool) (x4 : Fin x1 → Bool),   have x5 : Bool → List Bool := fun (x5 : Bool) => if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 x5 else List.replicate x1 x5 ++ List.ofFn x4;   have x6 : Bool → Prop := fun (x6 : Bool) => ∀ x7 ∈ x2, ∃ x9 ∈ x7, (x5 x6).getD (↑x9) Bool.false = Bool.true;   ¬(x6 Bool.false ↔ x6 Bool.true) → ∃ x8 ∈ x2, (∀ x9 ∈ x2, x9 ⊆ x8 → x9 = x8) ∧ ∃ x9 ∈ x8, if x3 = Bool.true then x1 ≤ ↑x9 else ↑x9 < x1 := by
  intro x1 x2 x3 x4
  dsimp only
  intro h
  have hmono : (∀ x7 ∈ x2, ∃ x9 ∈ x7, (if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 Bool.false else List.replicate x1 Bool.false ++ List.ofFn x4).getD (↑x9) Bool.false = Bool.true) → (∀ x7 ∈ x2, ∃ x9 ∈ x7, (if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 Bool.true else List.replicate x1 Bool.true ++ List.ofFn x4).getD (↑x9) Bool.false = Bool.true) := by
    intro hf x7 h7
    obtain ⟨x9, h9, hv⟩ := hf x7 h7
    refine ⟨x9, h9, ?_⟩
    rw [← PEqualNP.Outside.L_meta_7505_aux.key x1 x3 x4 x9 (PEqualNP.Outside.L_meta_7505_aux.nonc x1 x3 x4 x9 hv)]
    exact hv
  have ht : ∀ x7 ∈ x2, ∃ x9 ∈ x7, (if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 Bool.true else List.replicate x1 Bool.true ++ List.ofFn x4).getD (↑x9) Bool.false = Bool.true := by
    by_contra hn
    exact h ⟨hmono, fun a => absurd a hn⟩
  have hf : ¬ (∀ x7 ∈ x2, ∃ x9 ∈ x7, (if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 Bool.false else List.replicate x1 Bool.false ++ List.ofFn x4).getD (↑x9) Bool.false = Bool.true) := by
    intro hn
    exact h ⟨fun _ => ht, fun _ => hn⟩
  push Not at hf
  obtain ⟨x7, h7, hnot⟩ := hf
  obtain ⟨x8, h8, hs, hm⟩ := PEqualNP.Outside.L_meta_7505_aux.exmin x2 x7.card x7 h7 le_rfl
  refine ⟨x8, h8, hm, ?_⟩
  obtain ⟨x9, h9, hv⟩ := ht x8 h8
  refine ⟨x9, h9, ?_⟩
  by_contra hc
  apply hnot x9 (hs h9)
  rw [PEqualNP.Outside.L_meta_7505_aux.key x1 x3 x4 x9 hc]
  exact hv
