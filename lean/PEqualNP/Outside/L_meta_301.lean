import Mathlib.Order.Interval.Finset.Nat

theorem PEqualNP.Outside.L_meta_301 : ∀ (k : ℕ) (c : ℕ → Bool), (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) → k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  classical
  intro k c hc
  let count (t : ℕ) := ((Finset.Icc 1 (2 * t)).filter (fun j => c j = true)).card
  have hstep (t : ℕ) : count (t + 1) =
      count t + (if c (2 * t + 1) = true then 1 else 0) +
        (if c (2 * t + 2) = true then 1 else 0) := by
    dsimp [count]
    have hI : Finset.Icc 1 (2 * (t + 1)) =
        insert (2 * t + 2) (insert (2 * t + 1) (Finset.Icc 1 (2 * t))) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hA : 2 * t + 1 ∉ Finset.Icc 1 (2 * t) := by
      simp only [Finset.mem_Icc, not_and]
      omega
    have hB : 2 * t + 2 ∉ Finset.Icc 1 (2 * t) := by
      simp only [Finset.mem_Icc, not_and]
      omega
    rw [hI, Finset.filter_insert, Finset.filter_insert]
    by_cases ha : c (2 * t + 1) = true
    · by_cases hb : c (2 * t + 2) = true
      · simp [ha, hb, hA, hB]
      · simp [ha, hb, hA]
    · by_cases hb : c (2 * t + 2) = true
      · simp [ha, hb, hB]
      · simp [ha, hb]
  have hind : ∀ t : ℕ,
      (∀ j : ℕ, j ≤ 2 * t → c j = true ∨ c (j + 1) = true) →
        t ≤ count t ∧
        t + 1 ≤ count t + (if c 0 = true then 1 else 0) +
          (if c (2 * t + 1) = true then 1 else 0) := by
    intro t
    induction t with
    | zero =>
      intro h
      have hedge := h 0 (by omega)
      have hz : count 0 = 0 := by simp [count]
      by_cases h0 : c 0 = true <;> by_cases h1 : c 1 = true
      all_goals simp [hz, h0, h1] at *
    | succ t ih =>
      intro h
      have hprev : ∀ j : ℕ, j ≤ 2 * t →
          c j = true ∨ c (j + 1) = true := by
        intro j hj
        exact h j (by omega)
      obtain ⟨hlo, hhi⟩ := ih hprev
      have hab : c (2 * t + 1) = true ∨ c (2 * t + 2) = true :=
        h (2 * t + 1) (by omega)
      have hbe : c (2 * t + 2) = true ∨ c (2 * t + 3) = true :=
        h (2 * t + 2) (by omega)
      have hindex : 2 * (t + 1) + 1 = 2 * t + 3 := by omega
      simp only [hstep t, hindex]
      by_cases ha : c (2 * t + 1) = true <;>
        by_cases hb : c (2 * t + 2) = true <;>
        by_cases he : c (2 * t + 3) = true
      all_goals simp [ha, hb, he] at *
      all_goals omega
  obtain ⟨hlo, hhi⟩ := hind k hc
  change k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ count k
  by_cases hb : c 0 = false ∧ c (2 * k + 1) = false
  · obtain ⟨h0, he⟩ := hb
    have hh : k + 1 ≤ count k := by simpa [h0, he] using hhi
    simpa [h0, he] using hh
  · simpa [hb] using hlo
