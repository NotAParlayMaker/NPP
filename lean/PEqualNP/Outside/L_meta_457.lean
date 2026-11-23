import Mathlib

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_457 :
    ∀ E : List (Fin 3 × Fin 3), E = [(0, 1), (0, 2), (1, 2)] → ∀ τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3, (∀ e ∈ E, ∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 3 × Fin 3 → ℚ, (∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 3, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE
  subst E
  intro τ ht c hs
  have hi (v : Fin 3) : ∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)),
      ¬ (f.1 ∈ ({v} : Finset (Fin 3)) ∧ f.2 ∈ ({v} : Finset (Fin 3))) := by
    fin_cases v <;> decide
  have h0 : (c (0, 1) = 0 ∨ c (0, 2) = 0) ∧ c (0, 1) + c (0, 2) + c (1, 2) = 0 := by
    have h01 : τ (0, 1) {0} = 1 := by
      obtain ⟨hp, hn⟩ := ht (0, 1) (by decide) {0} (hi 0)
      rcases hp with hp | hp
      · exact False.elim (hn (by simp [hp]))
      · exact hp
    have h02 : τ (0, 2) {0} = 2 := by
      obtain ⟨hp, hn⟩ := ht (0, 2) (by decide) {0} (hi 0)
      rcases hp with hp | hp
      · exact False.elim (hn (by simp [hp]))
      · exact hp
    have s1 := hs {0} (hi 0) 1
    have s2 := hs {0} (hi 0) 2
    rcases (ht (1, 2) (by decide) {0} (hi 0)).1 with h12 | h12
    · simp +decide [h01, h02, h12] at s1 s2
      constructor
      · exact Or.inr s2
      · linarith only [s1, s2]
    · simp +decide [h01, h02, h12] at s1 s2
      constructor
      · exact Or.inl s1
      · linarith only [s1, s2]
  have h1 : c (0, 1) = 0 ∨ c (1, 2) = 0 := by
    have h01 : τ (0, 1) {1} = 0 := by
      obtain ⟨hp, hn⟩ := ht (0, 1) (by decide) {1} (hi 1)
      rcases hp with hp | hp
      · exact hp
      · exact False.elim (hn (by simp [hp]))
    have h12 : τ (1, 2) {1} = 2 := by
      obtain ⟨hp, hn⟩ := ht (1, 2) (by decide) {1} (hi 1)
      rcases hp with hp | hp
      · exact False.elim (hn (by simp [hp]))
      · exact hp
    have s0 := hs {1} (hi 1) 0
    have s2 := hs {1} (hi 1) 2
    rcases (ht (0, 2) (by decide) {1} (hi 1)).1 with h02 | h02
    · simp +decide [h01, h02, h12] at s0 s2
      exact Or.inr s2
    · simp +decide [h01, h02, h12] at s0 s2
      exact Or.inl s0
  have h2 : c (0, 2) = 0 ∨ c (1, 2) = 0 := by
    have h02 : τ (0, 2) {2} = 0 := by
      obtain ⟨hp, hn⟩ := ht (0, 2) (by decide) {2} (hi 2)
      rcases hp with hp | hp
      · exact hp
      · exact False.elim (hn (by simp [hp]))
    have h12 : τ (1, 2) {2} = 1 := by
      obtain ⟨hp, hn⟩ := ht (1, 2) (by decide) {2} (hi 2)
      rcases hp with hp | hp
      · exact hp
      · exact False.elim (hn (by simp [hp]))
    have s0 := hs {2} (hi 2) 0
    have s1 := hs {2} (hi 2) 1
    rcases (ht (0, 1) (by decide) {2} (hi 2)).1 with h01 | h01
    · simp +decide [h01, h02, h12] at s0 s1
      exact Or.inr s1
    · simp +decide [h01, h02, h12] at s0 s1
      exact Or.inl s0
  obtain ⟨h0, htotal⟩ := h0
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> first | assumption | linarith only [h0, h1, h2, htotal]
