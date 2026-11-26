import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18069 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x3 : Fin (13 : ℕ) → Bool) (x4 : Fin (13 : ℕ)) => !(x3 x4 || x3 (x4 + (1 : Fin (13 : ℕ))) || x3 (x4 + (3 : Fin (13 : ℕ))) || x3 (x4 + (9 : Fin (13 : ℕ)))); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ), (∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x4 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false) → ∀ (x8 : Fin (13 : ℕ) → Bool), (∀ (x9 : Fin (13 : ℕ)), x8 x9 = Bool.false → ∃ (x11 : Fin (13 : ℕ)), x1 x9 x11 ∧ x3 x8 x11 = Bool.true) → PEqualNP.BlindGate.wireValue x4 (26 : ℕ) (Fin.append x8 (x3 x8)) (if x3 x8 (0 : Fin (13 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  dsimp only
  intro C a b h S hS
  have h13 : (13 : Fin 26) = Fin.natAdd 13 (0 : Fin 13) := rfl
  have key := h (Fin.append S (fun l => !(S l || S (l + 1) || S (l + 3) || S (l + 9)))) ?_
  · rwa [h13, Fin.append_right] at key
  refine ⟨?_, ?_⟩
  · rintro ⟨p, l, hR, h1, h2⟩
    rw [Fin.append_left] at h1
    rw [Fin.append_right] at h2
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at h2
    rcases hR with rfl | rfl | rfl | rfl <;> simp_all
  · intro y hy hxy i
    refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
    · rw [Fin.append_left]
      cases hSp : S p
      · obtain ⟨l, hR, hT⟩ := hS p hSp
        have hl := hxy (Fin.natAdd 13 l)
        rw [Fin.append_right, hT] at hl
        cases hyp : y (Fin.castAdd 13 p)
        · exact le_refl _
        · exact absurd ⟨p, l, hR, hyp, by revert hl; cases y (Fin.natAdd 13 l) <;> simp [Bool.le_iff_imp]⟩ hy
      · exact le_top
    · rw [Fin.append_right]
      cases hTl : (!(S l || S (l + 1) || S (l + 3) || S (l + 9)))
      · cases hyl : y (Fin.natAdd 13 l)
        · exact le_refl _
        · exfalso
          apply hy
          simp only [Bool.not_eq_false', Bool.or_eq_true] at hTl
          have hq : ∀ q, S q = true → q = l ∨ q = l + 1 ∨ q = l + 3 ∨ q = l + 9 → False := by
            intro q hq hR
            have hc := hxy (Fin.castAdd 13 q)
            rw [Fin.append_left, hq] at hc
            exact hy ⟨q, l, hR, by revert hc; cases y (Fin.castAdd 13 q) <;> simp [Bool.le_iff_imp], hyl⟩
          exfalso
          rcases hTl with ((h0 | h0) | h0) | h0
          · exact hq _ h0 (Or.inl rfl)
          · exact hq _ h0 (Or.inr (Or.inl rfl))
          · exact hq _ h0 (Or.inr (Or.inr (Or.inl rfl)))
          · exact hq _ h0 (Or.inr (Or.inr (Or.inr rfl)))
      · exact le_top
