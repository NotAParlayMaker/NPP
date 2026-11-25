import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7608

theorem aux (α : Type) (x2 x3 : List (Set α)) (x4 : Set α) (hin : ∀ x7 ∈ x2, ¬x7 ⊆ x4)
    (hg : ∀ (x8 : Fin x3.length), ∃ x9 ∈ x2 ++ List.take x8 x3, ∃ x10 ∈ x2 ++ List.take x8 x3,
      x3.get x8 = x9 ∪ x10 ∨ x3.get x8 = x9 ∩ x10) (a : α) :
    ∀ n, ∀ i : Fin x3.length, i.val = n → x3.get i ⊆ x4 → a ∈ x3.get i →
      ∃ x11 : Fin x3.length, x3.get x11 ⊆ x4 ∧ a ∈ x3.get x11 ∧
        ∃ x12 ∈ x2 ++ List.take x11 x3, ∃ x13 ∈ x2 ++ List.take x11 x3,
          ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hsub ha
    obtain ⟨p, hp, q, hq, h⟩ := hg i
    have key : ∀ r ∈ x2 ++ List.take i x3, r ⊆ x4 → a ∈ r →
        ∃ x11 : Fin x3.length, x3.get x11 ⊆ x4 ∧ a ∈ x3.get x11 ∧
        ∃ x12 ∈ x2 ++ List.take x11 x3, ∃ x13 ∈ x2 ++ List.take x11 x3,
          ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
      intro r hr hrs har
      rcases List.mem_append.1 hr with h2 | h3
      · exact absurd hrs (hin r h2)
      · obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.1 h3
        have hk' : k < i.val ∧ k < x3.length := by
          rw [List.length_take] at hk
          omega
        rw [List.getElem_take] at hkr
        subst hkr
        exact ih k (by omega) ⟨k, hk'.2⟩ rfl hrs har
    rcases h with h | h
    · rw [h] at hsub ha
      rcases ha with ha | ha
      · exact key p hp (fun _ hx => hsub (Or.inl hx)) ha
      · exact key q hq (fun _ hx => hsub (Or.inr hx)) ha
    · have ha2 : a ∈ p ∩ q := h ▸ ha
      by_cases hps : p ⊆ x4
      · exact key p hp hps ha2.1
      by_cases hqs : q ⊆ x4
      · exact key q hq hqs ha2.2
      exact ⟨i, hsub, ha, p, hp, q, hq, hps, hqs, h⟩

theorem main (x1 : Type) (x2 x3 : List (Set x1)) (x4 : Set x1) :
    x4 ∈ x2 ++ x3 → (∀ x7 ∈ x2, ¬x7 ⊆ x4) →
    (∀ (x8 : Fin x3.length), ∃ x9 ∈ x2 ++ List.take x8 x3, ∃ x10 ∈ x2 ++ List.take x8 x3,
      x3.get x8 = x9 ∪ x10 ∨ x3.get x8 = x9 ∩ x10) →
    ∀ x9 ∈ x4, ∃ (x11 : Fin x3.length), x3.get x11 ⊆ x4 ∧ x9 ∈ x3.get x11 ∧
      ∃ x12 ∈ x2 ++ List.take x11 x3, ∃ x13 ∈ x2 ++ List.take x11 x3,
        ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
  intro hmem hin hg a ha
  rcases List.mem_append.1 hmem with h2 | h3
  · exact absurd (subset_refl x4) (hin x4 h2)
  · obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.1 h3
    subst hkr
    exact aux x1 x2 x3 _ hin hg a k ⟨k, hk⟩ rfl (subset_refl _) ha

end PEqualNP.Outside.L_meta_7608

theorem PEqualNP.Outside.L_meta_7608 : ∀ (x1 : Type) (x2 x3 : List (Set x1)) (x4 : Set x1),   have x5 : ℕ → List (Set x1) := fun (x5 : ℕ) => x2 ++ List.take x5 x3;   x4 ∈ x2 ++ x3 → (∀ x7 ∈ x2, ¬x7 ⊆ x4) → (∀ (x8 : Fin x3.length), ∃ x9 ∈ x5 ↑x8, ∃ x10 ∈ x5 ↑x8, x3.get x8 = x9 ∪ x10 ∨ x3.get x8 = x9 ∩ x10) → ∀ x9 ∈ x4, ∃ (x11 : Fin x3.length), x3.get x11 ⊆ x4 ∧ x9 ∈ x3.get x11 ∧ ∃ x12 ∈ x5 ↑x11, ∃ x13 ∈ x5 ↑x11, ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
  intro x1 x2 x3 x4
  exact PEqualNP.Outside.L_meta_7608.main x1 x2 x3 x4
