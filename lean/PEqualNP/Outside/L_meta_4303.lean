import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4303

lemma main_proof : ∀ (x1 x2 : Type) (x3 x4 x5 : ℕ) (x6 : ℕ → Set (x1 × x2)),   have x7 : (ℕ → Set (x1 × x2)) → x1 × x2 → Prop := fun (x7 : ℕ → Set (x1 × x2)) (x8 : x1 × x2) => ∃ x9 < x4, x7 (x3 + x9) ⊆ x7 x5 ∧ x8 ∈ x7 (x3 + x9) ∧ ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x3 + x9 ∧ x7 (x3 + x9) = x7 x10 ∩ x7 x11 ∧ ∃ (x12 : Set x1) (x13 : Set x2), x7 x10 = x12 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x13;   (0 : ℕ) < x3 → (∀ x9 < x3, x6 x9 ≠ ∅) → x6 x5 ≠ ∅ → ¬x6 (0 : ℕ) ⊆ x6 x5 → (∀ x12 < x4, ∃ (x14 : ℕ) (x15 : ℕ), Max.max x14 x15 < x3 + x12 ∧ x6 (x3 + x12) ∈ [x6 x14 ∪ x6 x15, x6 x14, ∅, x6 x14 ∩ x6 x15]) → ∃ (x13 : ℕ → Set (x1 × x2)), (∀ x14 < x3, x13 x14 = x6 x14) ∧ x13 x5 = x6 x5 ∧ (∀ (x14 : ℕ), x13 x14 ≠ ∅) ∧ (∀ x14 < x4, ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < x3 + x14 ∧ (x13 (x3 + x14) = x13 x16 ∪ x13 x17 ∨ x13 (x3 + x14) = x13 x16 ∩ x13 x17)) ∧ ∀ (x14 : x1 × x2), x7 x13 x14 → x7 x6 x14 := by
  classical
  intro X1 X2 m s o W x7 hm hraw ho hnot hsteps
  let W' : ℕ → Set (X1 × X2) := fun w => if W w = ∅ then W 0 else W w
  have hW0 : W 0 ≠ ∅ := hraw 0 hm
  refine ⟨W', ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [W', hraw i hi]
  · simp [W', ho]
  · intro w
    dsimp [W']
    split_ifs <;> assumption
  · intro i hi
    obtain ⟨a, b, hab, hmem⟩ := hsteps i hi
    have ha : a < m + i := (max_lt_iff.mp hab).1
    have hb : b < m + i := (max_lt_iff.mp hab).2
    have h0 : 0 < m + i := by omega
    by_cases hWi : W (m + i) = ∅
    · refine ⟨0, 0, max_lt_iff.mpr ⟨h0, h0⟩, Or.inl ?_⟩
      simp [W', hWi]
    · have hW'i : W' (m + i) = W (m + i) := by simp [W', hWi]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hunion | hcopy | hempty | hinter
      · by_cases hae : W a = ∅
        · by_cases hbe : W b = ∅
          · exfalso
            apply hWi
            rw [hunion, hae, hbe, Set.union_empty]
          · have hW'b : W' b = W b := by simp [W', hbe]
            refine ⟨b, b, max_lt_iff.mpr ⟨hb, hb⟩, Or.inl ?_⟩
            rw [hW'i, hW'b, hunion, hae, Set.empty_union, Set.union_self]
        · have hW'a : W' a = W a := by simp [W', hae]
          by_cases hbe : W b = ∅
          · refine ⟨a, a, max_lt_iff.mpr ⟨ha, ha⟩, Or.inl ?_⟩
            rw [hW'i, hW'a, hunion, hbe, Set.union_empty, Set.union_self]
          · have hW'b : W' b = W b := by simp [W', hbe]
            refine ⟨a, b, hab, Or.inl ?_⟩
            rw [hW'i, hW'a, hW'b, hunion]
      · have hae : W a ≠ ∅ := by
          intro h
          apply hWi
          rw [hcopy, h]
        have hW'a : W' a = W a := by simp [W', hae]
        refine ⟨a, a, max_lt_iff.mpr ⟨ha, ha⟩, Or.inl ?_⟩
        rw [hW'i, hW'a, hcopy, Set.union_self]
      · exact False.elim (hWi hempty)
      · have hae : W a ≠ ∅ := by
          intro h
          apply hWi
          rw [hinter, h, Set.empty_inter]
        have hbe : W b ≠ ∅ := by
          intro h
          apply hWi
          rw [hinter, h, Set.inter_empty]
        have hW'a : W' a = W a := by simp [W', hae]
        have hW'b : W' b = W b := by simp [W', hbe]
        refine ⟨a, b, hab, Or.inr ?_⟩
        rw [hW'i, hW'a, hW'b, hinter]
  · intro z hz
    rcases hz with ⟨i, hi, hsub, hzmem, a, b, hab, hinter, A, B, hA, hB⟩
    have hWo : W' o = W o := by simp [W', ho]
    have hWi : W (m + i) ≠ ∅ := by
      intro h
      apply hnot
      have h1 : W' (m + i) = W 0 := by simp [W', h]
      rw [h1, hWo] at hsub
      exact hsub
    have hW'i : W' (m + i) = W (m + i) := by simp [W', hWi]
    rw [hW'i] at hzmem
    have hsub' : W (m + i) ⊆ W o := by
      rw [← hW'i, ← hWo]
      exact hsub
    by_cases hae : W a = ∅
    · have hW'a : W' a = W 0 := by simp [W', hae]
      by_cases hbe : W b = ∅
      · have hW'b : W' b = W 0 := by simp [W', hbe]
        have hW'i_eq : W (m + i) = W 0 := by
          rw [← hW'i, hinter, hW'a, hW'b, Set.inter_self]
        exfalso
        apply hnot
        rw [← hW'i_eq]
        exact hsub'
      · have hW'b : W' b = W b := by simp [W', hbe]
        have h0_lt : 0 < m + i := by omega
        have hb_lt : b < m + i := (max_lt_iff.mp hab).2
        refine ⟨i, hi, hsub', hzmem, 0, b, max_lt_iff.mpr ⟨h0_lt, hb_lt⟩, ?_, A, B, ?_, ?_⟩
        · rw [← hW'i, hinter, hW'a, hW'b]
        · rw [← hW'a, hA]
        · rw [← hW'b, hB]
    · have hW'a : W' a = W a := by simp [W', hae]
      by_cases hbe : W b = ∅
      · have hW'b : W' b = W 0 := by simp [W', hbe]
        have ha_lt : a < m + i := (max_lt_iff.mp hab).1
        have h0_lt : 0 < m + i := by omega
        refine ⟨i, hi, hsub', hzmem, a, 0, max_lt_iff.mpr ⟨ha_lt, h0_lt⟩, ?_, A, B, ?_, ?_⟩
        · rw [← hW'i, hinter, hW'a, hW'b]
        · rw [← hW'a, hA]
        · rw [← hW'b, hB]
      · have hW'b : W' b = W b := by simp [W', hbe]
        refine ⟨i, hi, hsub', hzmem, a, b, hab, ?_, A, B, ?_, ?_⟩
        · rw [← hW'i, hinter, hW'a, hW'b]
        · rw [← hW'a, hA]
        · rw [← hW'b, hB]

end PEqualNP.Outside.L_meta_4303

theorem PEqualNP.Outside.L_meta_4303 : ∀ (x1 x2 : Type) (x3 x4 x5 : ℕ) (x6 : ℕ → Set (x1 × x2)),   have x7 : (ℕ → Set (x1 × x2)) → x1 × x2 → Prop := fun (x7 : ℕ → Set (x1 × x2)) (x8 : x1 × x2) => ∃ x9 < x4, x7 (x3 + x9) ⊆ x7 x5 ∧ x8 ∈ x7 (x3 + x9) ∧ ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x3 + x9 ∧ x7 (x3 + x9) = x7 x10 ∩ x7 x11 ∧ ∃ (x12 : Set x1) (x13 : Set x2), x7 x10 = x12 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x13;   (0 : ℕ) < x3 → (∀ x9 < x3, x6 x9 ≠ ∅) → x6 x5 ≠ ∅ → ¬x6 (0 : ℕ) ⊆ x6 x5 → (∀ x12 < x4, ∃ (x14 : ℕ) (x15 : ℕ), Max.max x14 x15 < x3 + x12 ∧ x6 (x3 + x12) ∈ [x6 x14 ∪ x6 x15, x6 x14, ∅, x6 x14 ∩ x6 x15]) → ∃ (x13 : ℕ → Set (x1 × x2)), (∀ x14 < x3, x13 x14 = x6 x14) ∧ x13 x5 = x6 x5 ∧ (∀ (x14 : ℕ), x13 x14 ≠ ∅) ∧ (∀ x14 < x4, ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < x3 + x14 ∧ (x13 (x3 + x14) = x13 x16 ∪ x13 x17 ∨ x13 (x3 + x14) = x13 x16 ∩ x13 x17)) ∧ ∀ (x14 : x1 × x2), x7 x13 x14 → x7 x6 x14 :=
  PEqualNP.Outside.L_meta_4303.main_proof
