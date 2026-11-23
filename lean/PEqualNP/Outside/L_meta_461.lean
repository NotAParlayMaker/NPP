import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_461 :
    ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6, (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 6 × Fin 6 → ℚ, (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  rintro E rfl τ hτ c hc
  have hind : ∀ u : Fin 6, ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)),
      ¬ (f.1 ∈ ({u} : Finset (Fin 6)) ∧ f.2 ∈ ({u} : Finset (Fin 6))) := by
    intro u f hf ⟨h1, h2⟩
    simp only [Finset.mem_singleton] at h1 h2
    have hEq : f.1 = f.2 := h1.trans h2.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd hEq (by decide)
  have ht_mem : ∀ (e : Fin 6 × Fin 6) (u : Fin 6),
      e ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)) →
      (τ e {u} = e.1 ∨ τ e {u} = e.2) ∧ τ e {u} ≠ u := by
    intro e u he
    have h := hτ e he {u} (hind u)
    exact ⟨h.1, by simpa using h.2⟩
  have h0_01 : τ (0, 1) {0} = 1 := by
    have h := ht_mem (0, 1) 0 (by simp)
    rcases h.1 with h1 | h2
    · exact absurd h1 h.2
    · exact h2
  have h0_02 : τ (0, 2) {0} = 2 := by
    have h := ht_mem (0, 2) 0 (by simp)
    rcases h.1 with h1 | h2
    · exact absurd h1 h.2
    · exact h2
  have h0_03 : τ (0, 3) {0} = 3 := by
    have h := ht_mem (0, 3) 0 (by simp)
    rcases h.1 with h1 | h2
    · exact absurd h1 h.2
    · exact h2
  have h1_01 : τ (0, 1) {1} = 0 := by
    have h := ht_mem (0, 1) 1 (by simp)
    rcases h.1 with h1 | h2
    · exact h1
    · exact absurd h2 h.2
  have h1_12 : τ (1, 2) {1} = 2 := by
    have h := ht_mem (1, 2) 1 (by simp)
    rcases h.1 with h1 | h2
    · exact absurd h1 h.2
    · exact h2
  have h1_14 : τ (1, 4) {1} = 4 := by
    have h := ht_mem (1, 4) 1 (by simp)
    rcases h.1 with h1 | h2
    · exact absurd h1 h.2
    · exact h2
  have h2_02 : τ (0, 2) {2} = 0 := by
    have h := ht_mem (0, 2) 2 (by simp)
    rcases h.1 with h1 | h2
    · exact h1
    · exact absurd h2 h.2
  have h2_12 : τ (1, 2) {2} = 1 := by
    have h := ht_mem (1, 2) 2 (by simp)
    rcases h.1 with h1 | h2
    · exact h1
    · exact absurd h2 h.2
  have h2_25 : τ (2, 5) {2} = 5 := by
    have h := ht_mem (2, 5) 2 (by simp)
    rcases h.1 with h1 | h2
    · exact absurd h1 h.2
    · exact h2
  have hc03 : c (0, 3) = 0 := by
    have hsum := hc {0} (hind 0) 3
    have h12 : τ (1, 2) {0} ≠ 3 := by
      rcases (ht_mem (1, 2) 0 (by simp)).1 with h | h <;> rw [h] <;> decide
    have h14 : τ (1, 4) {0} ≠ 3 := by
      rcases (ht_mem (1, 4) 0 (by simp)).1 with h | h <;> rw [h] <;> decide
    have h25 : τ (2, 5) {0} ≠ 3 := by
      rcases (ht_mem (2, 5) 0 (by simp)).1 with h | h <;> rw [h] <;> decide
    simp [List.filter, h0_01, h0_02, h0_03, h12, h14, h25] at hsum
    exact hsum
  have hc14 : c (1, 4) = 0 := by
    have hsum := hc {1} (hind 1) 4
    have h02 : τ (0, 2) {1} ≠ 4 := by
      rcases (ht_mem (0, 2) 1 (by simp)).1 with h | h <;> rw [h] <;> decide
    have h03 : τ (0, 3) {1} ≠ 4 := by
      rcases (ht_mem (0, 3) 1 (by simp)).1 with h | h <;> rw [h] <;> decide
    have h25 : τ (2, 5) {1} ≠ 4 := by
      rcases (ht_mem (2, 5) 1 (by simp)).1 with h | h <;> rw [h] <;> decide
    simp [List.filter, h1_01, h1_12, h1_14, h02, h03, h25] at hsum
    exact hsum
  have hc25 : c (2, 5) = 0 := by
    have hsum := hc {2} (hind 2) 5
    have h01 : τ (0, 1) {2} ≠ 5 := by
      rcases (ht_mem (0, 1) 2 (by simp)).1 with h | h <;> rw [h] <;> decide
    have h03 : τ (0, 3) {2} ≠ 5 := by
      rcases (ht_mem (0, 3) 2 (by simp)).1 with h | h <;> rw [h] <;> decide
    have h14 : τ (1, 4) {2} ≠ 5 := by
      rcases (ht_mem (1, 4) 2 (by simp)).1 with h | h <;> rw [h] <;> decide
    simp [List.filter, h2_02, h2_12, h2_25, h01, h03, h14] at hsum
    exact hsum
  have heq0 : (c (0, 1) = 0 ∧ c (0, 2) + c (1, 2) = 0) ∨ (c (0, 2) = 0 ∧ c (0, 1) + c (1, 2) = 0) := by
    have hs1 := hc {0} (hind 0) 1
    have hs2 := hc {0} (hind 0) 2
    rcases (ht_mem (1, 2) 0 (by simp)).1 with h12 | h12 <;>
      rcases (ht_mem (1, 4) 0 (by simp)).1 with h14 | h14 <;>
      rcases (ht_mem (2, 5) 0 (by simp)).1 with h25 | h25 <;>
      simp [List.filter, h0_01, h0_02, h0_03, h12, h14, h25, hc03, hc14, hc25] at hs1 hs2
    all_goals first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩
  have heq1 : (c (0, 1) = 0 ∧ c (0, 2) + c (1, 2) = 0) ∨ (c (1, 2) = 0 ∧ c (0, 1) + c (0, 2) = 0) := by
    have hs0 := hc {1} (hind 1) 0
    have hs2 := hc {1} (hind 1) 2
    rcases (ht_mem (0, 2) 1 (by simp)).1 with h02 | h02 <;>
      rcases (ht_mem (0, 3) 1 (by simp)).1 with h03 | h03 <;>
      rcases (ht_mem (2, 5) 1 (by simp)).1 with h25 | h25 <;>
      simp [List.filter, h1_01, h1_12, h1_14, h02, h03, h25, hc03, hc14, hc25] at hs0 hs2
    all_goals first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩
  have heq2 : (c (0, 2) = 0 ∧ c (0, 1) + c (1, 2) = 0) ∨ (c (1, 2) = 0 ∧ c (0, 1) + c (0, 2) = 0) := by
    have hs0 := hc {2} (hind 2) 0
    have hs1 := hc {2} (hind 2) 1
    rcases (ht_mem (0, 1) 2 (by simp)).1 with h01 | h01 <;>
      rcases (ht_mem (0, 3) 2 (by simp)).1 with h03 | h03 <;>
      rcases (ht_mem (1, 4) 2 (by simp)).1 with h14 | h14 <;>
      simp [List.filter, h2_02, h2_12, h2_25, h01, h03, h14, hc03, hc14, hc25] at hs0 hs1
    all_goals first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩
  have htri : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
    rcases heq0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases heq1 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases heq2 with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
      exact ⟨by linarith, by linarith, by linarith⟩
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact htri.1
  · exact htri.2.1
  · exact htri.2.2
  · exact hc03
  · exact hc14
  · exact hc25
