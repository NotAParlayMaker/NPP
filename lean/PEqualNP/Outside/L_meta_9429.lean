import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9429

lemma key (x1 : Finset (Finset ℕ)) (x7 : Finset ℕ)
    (h1 : ∀ A ∈ x1, ¬ A ⊆ x7 ∧ ∀ B ∈ x1, A ≠ B → (A ∩ B ∩ x7).card ≤ 1)
    (C D C' D' : Finset ℕ) (hC : C ∈ x1) (hD : D ∈ x1) (hC' : C' ∈ x1) (hD' : D' ∈ x1)
    (hT : C ∩ D ∩ (C' ∩ D') ⊆ x7) : (C ∩ D ∩ (C' ∩ D')).card ≤ 1 := by
  by_contra hcon
  have two : ∀ P ∈ x1, ∀ Q ∈ x1, C ∩ D ∩ (C' ∩ D') ⊆ P → C ∩ D ∩ (C' ∩ D') ⊆ Q → P = Q := by
    intro P hP Q hQ hTP hTQ
    by_contra hne
    apply hcon
    refine le_trans (Finset.card_le_card ?_) ((h1 P hP).2 Q hQ hne)
    intro t ht
    simp only [Finset.mem_inter]
    exact ⟨⟨hTP ht, hTQ ht⟩, hT ht⟩
  have sC : C ∩ D ∩ (C' ∩ D') ⊆ C := fun t ht => by
    simp only [Finset.mem_inter] at ht; exact ht.1.1
  have sD : C ∩ D ∩ (C' ∩ D') ⊆ D := fun t ht => by
    simp only [Finset.mem_inter] at ht; exact ht.1.2
  have sC' : C ∩ D ∩ (C' ∩ D') ⊆ C' := fun t ht => by
    simp only [Finset.mem_inter] at ht; exact ht.2.1
  have sD' : C ∩ D ∩ (C' ∩ D') ⊆ D' := fun t ht => by
    simp only [Finset.mem_inter] at ht; exact ht.2.2
  have e1 := two C hC D hD sC sD
  have e2 := two C hC C' hC' sC sC'
  have e3 := two C hC D' hD' sC sD'
  rw [← e1, ← e2, ← e3] at hT
  apply (h1 C hC).1
  intro t ht
  exact hT (by simp only [Finset.mem_inter]; exact ⟨⟨ht, ht⟩, ht, ht⟩)

lemma rep (x1 : Finset (Finset ℕ)) (x2 x3 : Finset ℕ) (x4 : Finset (Finset ℕ)) (x6 : Finset ℕ)
    (x8 x9 : ℕ) (h8 : x8 ∉ x6) (h9 : x9 ∉ x6) (h1 : ∀ A ∈ x1, A ⊆ x6)
    (h4 : x4 ⊆ insert (insert x8 x2) (insert (insert x9 x3) x1))
    (hx2 : x2 ∈ Finset.image₂ (fun a b : Finset ℕ => a ∩ b) ({a ∈ x4 | a ⊆ x6}) ({a ∈ x4 | a ⊆ x6}))
    (hx3 : x3 ∈ Finset.image₂ (fun a b : Finset ℕ => a ∩ b) ({a ∈ x4 | a ⊆ x6}) ({a ∈ x4 | a ⊆ x6})) :
    ∀ A ∈ x4, ∃ C ∈ x1, ∃ D ∈ x1, A ∩ x6 = C ∩ D := by
  have sub : ∀ A ∈ x4, A ⊆ x6 → A ∈ x1 := by
    intro A hA hs
    have h := h4 hA
    simp only [Finset.mem_insert] at h
    rcases h with h | h | h
    · rw [h] at hs
      exact (h8 (hs (Finset.mem_insert_self _ _))).elim
    · rw [h] at hs
      exact (h9 (hs (Finset.mem_insert_self _ _))).elim
    · exact h
  have r2 : ∃ C ∈ x1, ∃ D ∈ x1, x2 = C ∩ D := by
    simp only [Finset.mem_image₂, Finset.mem_filter] at hx2
    obtain ⟨C, ⟨hC, hCs⟩, D, ⟨hD, hDs⟩, e⟩ := hx2
    exact ⟨C, sub C hC hCs, D, sub D hD hDs, e.symm⟩
  have r3 : ∃ C ∈ x1, ∃ D ∈ x1, x3 = C ∩ D := by
    simp only [Finset.mem_image₂, Finset.mem_filter] at hx3
    obtain ⟨C, ⟨hC, hCs⟩, D, ⟨hD, hDs⟩, e⟩ := hx3
    exact ⟨C, sub C hC hCs, D, sub D hD hDs, e.symm⟩
  have ins : ∀ (y : ℕ) (X : Finset ℕ), y ∉ x6 → X ⊆ x6 → insert y X ∩ x6 = X := by
    intro y X hy hX
    ext t
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, h6⟩
      · rw [h] at h6
        exact (hy h6).elim
      · exact h
    · intro h
      exact ⟨Or.inr h, hX h⟩
  intro A hA
  have h := h4 hA
  simp only [Finset.mem_insert] at h
  rcases h with h | h | h
  · obtain ⟨C, hC, D, hD, e⟩ := r2
    refine ⟨C, hC, D, hD, ?_⟩
    rw [h, ← e]
    apply ins x8 x2 h8
    rw [e]
    exact fun t ht => h1 C hC (Finset.mem_inter.mp ht).1
  · obtain ⟨C, hC, D, hD, e⟩ := r3
    refine ⟨C, hC, D, hD, ?_⟩
    rw [h, ← e]
    apply ins x9 x3 h9
    rw [e]
    exact fun t ht => h1 C hC (Finset.mem_inter.mp ht).1
  · refine ⟨A, h, A, h, ?_⟩
    ext t
    simp only [Finset.mem_inter]
    exact ⟨fun hh => ⟨hh.1, hh.1⟩, fun hh => ⟨hh.1, h1 A h hh.1⟩⟩

lemma main (x1 : Finset (Finset ℕ)) (x2 x3 : Finset ℕ) (x4 x5 : Finset (Finset ℕ))
    (x6 x7 : Finset ℕ) (x8 x9 : ℕ) (h8 : x8 ∉ x6) (h9 : x9 ∉ x6) (h7 : x7 ⊆ x6)
    (h1 : ∀ A ∈ x1, A ⊆ x6 ∧ ¬ A ⊆ x7 ∧ ∀ B ∈ x1, A ≠ B → (A ∩ B ∩ x7).card ≤ 1)
    (h4 : x4 ⊆ insert (insert x8 x2) (insert (insert x9 x3) x1))
    (hx2 : x2 ∈ Finset.image₂ (fun a b : Finset ℕ => a ∩ b) ({a ∈ x4 | a ⊆ x6}) ({a ∈ x4 | a ⊆ x6}))
    (hx3 : x3 ∈ Finset.image₂ (fun a b : Finset ℕ => a ∩ b) ({a ∈ x4 | a ⊆ x6}) ({a ∈ x4 | a ⊆ x6}))
    (h5 : x5 ⊆ Finset.image₂
      (fun a b : Finset ℕ => a ∩ b ∩ x6 ∪ if {x8, x9} ⊆ a ∪ b then {x8} else ∅) x4 x4)
    (hU : x5.biUnion id = insert x8 x7) : x7.card ≤ x5.card := by
  have hrep := rep x1 x2 x3 x4 x6 x8 x9 h8 h9 (fun A hA => (h1 A hA).1) h4 hx2 hx3
  have hS : ∀ S ∈ x5, (S ∩ x7).card ≤ 1 := by
    intro S hS
    have hsub : S ⊆ insert x8 x7 := by
      rw [← hU]
      intro t ht
      exact Finset.mem_biUnion.mpr ⟨S, hS, ht⟩
    have h5S := h5 hS
    simp only [Finset.mem_image₂] at h5S
    obtain ⟨A, hA, B, hB, e⟩ := h5S
    obtain ⟨C, hC, D, hD, eA⟩ := hrep A hA
    obtain ⟨C', hC', D', hD', eB⟩ := hrep B hB
    have hSx : S ∩ x7 = C ∩ D ∩ (C' ∩ D') := by
      rw [← eA, ← eB]
      ext t
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hS', h7'⟩
        rw [← e] at hS'
        rcases Finset.mem_union.mp hS' with h | h
        · simp only [Finset.mem_inter] at h
          exact ⟨⟨h.1.1, h.2⟩, h.1.2, h.2⟩
        · exfalso
          split_ifs at h
          · rw [Finset.mem_singleton] at h
            rw [h] at h7'
            exact h8 (h7 h7')
          · simp at h
      · rintro ⟨⟨hA', h6⟩, hB', _⟩
        have htS : t ∈ S := by
          rw [← e]
          exact Finset.mem_union_left _
            (by simp only [Finset.mem_inter]; exact ⟨⟨hA', hB'⟩, h6⟩)
        have h := hsub htS
        rw [Finset.mem_insert] at h
        rcases h with h | h
        · rw [h] at h6
          exact (h8 h6).elim
        · exact ⟨htS, h⟩
    rw [hSx]
    apply key x1 x7 (fun A hA => (h1 A hA).2) C D C' D' hC hD hC' hD'
    rw [← hSx]
    exact Finset.inter_subset_right
  have hcov : x7 ⊆ x5.biUnion (fun S => S ∩ x7) := by
    intro t ht
    have h : t ∈ x5.biUnion id := by
      rw [hU]
      exact Finset.mem_insert_of_mem ht
    obtain ⟨S, hS', htS⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨S, hS', Finset.mem_inter.mpr ⟨htS, ht⟩⟩
  calc x7.card ≤ (x5.biUnion (fun S => S ∩ x7)).card := Finset.card_le_card hcov
    _ ≤ ∑ S ∈ x5, (S ∩ x7).card := Finset.card_biUnion_le
    _ ≤ ∑ S ∈ x5, 1 := Finset.sum_le_sum hS
    _ = x5.card := by simp

end PEqualNP.Outside.L_meta_9429

theorem PEqualNP.Outside.L_meta_9429 : ∀ (x1 : Finset (Finset ℕ)) (x2 x3 : Finset ℕ) (x4 x5 : Finset (Finset ℕ)) (x6 x7 : Finset ℕ) (x8 x9 : ℕ), x8 ∉ x6 → x9 ∉ x6 → x7 ⊆ x6 → (∀ x13 ∈ x1, x13 ⊆ x6 ∧ ¬x13 ⊆ x7 ∧ ∀ x15 ∈ x1, x13 ≠ x15 → (x13 ∩ x15 ∩ x7).card ≤ (1 : ℕ)) → x4 ⊆ Insert.insert (Insert.insert x8 x2) (Insert.insert (Insert.insert x9 x3) x1) → x2 ∈ Finset.image₂ (fun (x15 x16 : Finset ℕ) => x15 ∩ x16) ({x15 ∈ x4 | x15 ⊆ x6}) ({x15 ∈ x4 | x15 ⊆ x6}) → x3 ∈ Finset.image₂ (fun (x16 x17 : Finset ℕ) => x16 ∩ x17) ({x16 ∈ x4 | x16 ⊆ x6}) ({x16 ∈ x4 | x16 ⊆ x6}) → x5 ⊆ Finset.image₂ (fun (x17 x18 : Finset ℕ) => x17 ∩ x18 ∩ x6 ∪ if {x8, x9} ⊆ x17 ∪ x18 then {x8} else ∅) x4 x4 → x5.biUnion id = Insert.insert x8 x7 → x7.card ≤ x5.card := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 h8 h9 h7 h1 h4 hx2 hx3 h5 hU
  exact PEqualNP.Outside.L_meta_9429.main x1 x2 x3 x4 x5 x6 x7 x8 x9 h8 h9 h7 h1 h4 hx2 hx3 h5 hU
