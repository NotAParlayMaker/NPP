import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18163_1
  (base : ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (u ≠ v)) s → 15 ≤ s)
  (shrink : ∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (n + 1) => decide (u ≠ v)) (s + 3) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) : ∀ n s : ℕ, 5 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro s h; omega
  | succ k ih =>
    intro s h rep
    by_cases eq : k = 4
    · subst k
      exact base s rep
    · have hk : 5 ≤ k := by omega
      let t := s - 3
      have cap : s ≤ t + 3 := by dsimp [t]; omega
      obtain ⟨C, hm, hc, hr⟩ := rep
      have smaller := shrink k t ⟨C, hm, hc.trans cap, hr⟩
      have step := ih t hk smaller
      dsimp [t] at step
      omega
