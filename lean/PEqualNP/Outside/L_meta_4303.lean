import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4303 : ∀ (x1 x2 : Type) (x3 x4 x5 : ℕ) (x6 : ℕ → Set (x1 × x2)),   have x7 : (ℕ → Set (x1 × x2)) → x1 × x2 → Prop := fun (x7 : ℕ → Set (x1 × x2)) (x8 : x1 × x2) => ∃ x9 < x4, x7 (x3 + x9) ⊆ x7 x5 ∧ x8 ∈ x7 (x3 + x9) ∧ ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x3 + x9 ∧ x7 (x3 + x9) = x7 x10 ∩ x7 x11 ∧ ∃ (x12 : Set x1) (x13 : Set x2), x7 x10 = x12 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x13;   (0 : ℕ) < x3 → (∀ x9 < x3, x6 x9 ≠ ∅) → x6 x5 ≠ ∅ → ¬x6 (0 : ℕ) ⊆ x6 x5 → (∀ x12 < x4, ∃ (x14 : ℕ) (x15 : ℕ), Max.max x14 x15 < x3 + x12 ∧ x6 (x3 + x12) ∈ [x6 x14 ∪ x6 x15, x6 x14, ∅, x6 x14 ∩ x6 x15]) → ∃ (x13 : ℕ → Set (x1 × x2)), (∀ x14 < x3, x13 x14 = x6 x14) ∧ x13 x5 = x6 x5 ∧ (∀ (x14 : ℕ), x13 x14 ≠ ∅) ∧ (∀ x14 < x4, ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < x3 + x14 ∧ (x13 (x3 + x14) = x13 x16 ∪ x13 x17 ∨ x13 (x3 + x14) = x13 x16 ∩ x13 x17)) ∧ ∀ (x14 : x1 × x2), x7 x13 x14 → x7 x6 x14 := by
  intro α β n m o S
  dsimp only
  intro hn hin ho hnot hg
  classical
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Set (α × β), ∀ k, T k = if S k = ∅ then S 0 else S k :=
    ⟨_, fun _ => rfl⟩
  have T_ne : ∀ k, S k ≠ ∅ → T k = S k := by
    intro k h; simp [hT k, h]
  have T_e : ∀ k, S k = ∅ → T k = S 0 := by
    intro k h; simp [hT k, h]
  have T0 : T 0 = S 0 := T_ne 0 (hin 0 hn)
  have hTo : T o = S o := T_ne o ho
  refine ⟨T, fun i hi => T_ne i (hin i hi), hTo, ?_, ?_, ?_⟩
  · intro k
    by_cases h : S k = ∅
    · rw [T_e k h]; exact hin 0 hn
    · rw [T_ne k h]; exact h
  · intro k hk
    obtain ⟨a, b, hab, hmem⟩ := hg k hk
    have ha : a < n + k := lt_of_le_of_lt (le_max_left a b) hab
    have hb : b < n + k := lt_of_le_of_lt (le_max_right a b) hab
    by_cases hE : S (n + k) = ∅
    · refine ⟨0, 0, ?_, Or.inl ?_⟩
      · rw [max_self]; omega
      · rw [T_e _ hE, T0, Set.union_self]
    · have hTk := T_ne _ hE
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with h | h | h | h
      · by_cases hae : S a = ∅
        · by_cases hbe : S b = ∅
          · exact absurd (by rw [h, hae, hbe, Set.union_self]) hE
          · refine ⟨b, b, by rw [max_self]; exact hb, Or.inl ?_⟩
            rw [hTk, T_ne b hbe, h, hae, Set.empty_union, Set.union_self]
        · by_cases hbe : S b = ∅
          · refine ⟨a, a, by rw [max_self]; exact ha, Or.inl ?_⟩
            rw [hTk, T_ne a hae, h, hbe, Set.union_empty, Set.union_self]
          · exact ⟨a, b, hab, Or.inl (by rw [hTk, T_ne a hae, T_ne b hbe, h])⟩
      · have hae : S a ≠ ∅ := by rw [← h]; exact hE
        refine ⟨a, a, by rw [max_self]; exact ha, Or.inl ?_⟩
        rw [hTk, T_ne a hae, h, Set.union_self]
      · exact absurd h hE
      · have hae : S a ≠ ∅ := by
          intro hae; exact hE (by rw [h, hae, Set.empty_inter])
        have hbe : S b ≠ ∅ := by
          intro hbe; exact hE (by rw [h, hbe, Set.inter_empty])
        exact ⟨a, b, hab, Or.inr (by rw [hTk, T_ne a hae, T_ne b hbe, h])⟩
  · rintro p ⟨k, hk, hsub, hpm, a, b, hab, heq, A, B, hA, hB⟩
    have ha : a < n + k := lt_of_le_of_lt (le_max_left a b) hab
    have hb : b < n + k := lt_of_le_of_lt (le_max_right a b) hab
    have hEk : S (n + k) ≠ ∅ := by
      intro hE
      apply hnot
      rw [T_e _ hE, hTo] at hsub
      exact hsub
    have hTk := T_ne _ hEk
    have h0 : 0 < n + k := by omega
    obtain ⟨a', ha', hae'⟩ : ∃ a', a' < n + k ∧ S a' = T a := by
      by_cases h : S a = ∅
      · exact ⟨0, h0, (T_e a h).symm⟩
      · exact ⟨a, ha, (T_ne a h).symm⟩
    obtain ⟨b', hb', hbe'⟩ : ∃ b', b' < n + k ∧ S b' = T b := by
      by_cases h : S b = ∅
      · exact ⟨0, h0, (T_e b h).symm⟩
      · exact ⟨b, hb, (T_ne b h).symm⟩
    refine ⟨k, hk, ?_, ?_, a', b', max_lt ha' hb', ?_, A, B, ?_, ?_⟩
    · rw [← hTk, ← hTo]; exact hsub
    · rw [← hTk]; exact hpm
    · rw [← hTk, heq, hae', hbe']
    · rw [hae']; exact hA
    · rw [hbe']; exact hB
