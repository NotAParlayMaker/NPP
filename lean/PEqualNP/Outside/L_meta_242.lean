import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_242 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasBinarySize n f s →
      PEqualNP.MetaComplexity.HasBinarySize n f (s + 1) := by
  intro n f s ⟨C, hle, heval⟩
  exact ⟨C, Nat.le_succ_of_le hle, heval⟩
