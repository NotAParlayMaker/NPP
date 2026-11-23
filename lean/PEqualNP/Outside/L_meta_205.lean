import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_205 :
    ∀ (n : ℕ) (c : Bool), PEqualNP.MetaComplexity.HasTypedRank n (fun _ => c) 0 := by
  intro n c
  let τ : (Fin n → Bool) → (Fin n → Bool) → ℕ := fun _ _ => 0
  refine ⟨τ, ?_, ?_⟩
  · intro x y hx hy
    cases c <;> simp_all
  · have hz (i : Fin n) (b : Bool) : typedMatrix n (fun _ => c) τ i b = 0 := by
      ext x y
      cases c <;> simp [typedMatrix]
    simp [hz]
