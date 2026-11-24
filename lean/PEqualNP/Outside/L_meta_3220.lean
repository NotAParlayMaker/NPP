import PEqualNP.Defs

/-- The recorded statement `¬∃ x1, ∀ x2, x1 ≤ x2` is false: zero bounds every natural. -/
theorem PEqualNP.Outside.L_meta_3220 :
    ¬ (¬ ∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2) := by
  intro h
  exact h ⟨0, fun x2 => Nat.zero_le x2⟩
