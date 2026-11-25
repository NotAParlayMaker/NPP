import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5765 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : Finset (Fin x1 ⊕ Fin x2)) (x6 : Fin x1 ⊕ Fin x2 → Finset (Fin x1 × Fin x2)) (x7 x8 : ℕ), x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → (∀ x12 ∈ x3, ∃ x14 ∈ x5, x12 ∈ x6 x14) → (∀ x13 ∈ x5, ∀ x15 ∈ x6 x13, x13 = Sum.inl x15.1 ∨ x13 = Sum.inr x15.2) → ∑ x14 ∈ x5, (x6 x14).card ≤ x7 + x8 → x5.card ≤ x7 → x3.card + x4.card ≤ (2 : ℕ) * x7 + x8 := by
  intro n m E M S st a b hME hM1 hM2 hcov hstar hsum hcard
  have h1 : E.card ≤ a + b := by
    calc E.card ≤ (S.biUnion st).card := Finset.card_le_card (fun e he => by
          obtain ⟨s, hs, hes⟩ := hcov e he
          exact Finset.mem_biUnion.mpr ⟨s, hs, hes⟩)
      _ ≤ ∑ s ∈ S, (st s).card := Finset.card_biUnion_le
      _ ≤ a + b := hsum
  have h2 : M.card ≤ S.card := by
    classical
    rcases M.eq_empty_or_nonempty with h0 | ⟨e0, he0⟩
    · simp [h0]
    haveI : Nonempty (Fin n ⊕ Fin m) := ⟨Sum.inl e0.1⟩
    choose! f hf using fun e (he : e ∈ M) => hcov e (hME he)
    apply Finset.card_le_card_of_injOn f (fun e he => (hf e he).1)
    intro e he e' he' hee
    have h := hstar _ (hf e he).1 e (hf e he).2
    have h' := hstar _ (hf e' he').1 e' (hf e' he').2
    rw [← hee] at h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact hM1 e he e' he' (Sum.inl.inj (h.symm.trans h'))
    · rw [h] at h'; cases h'
    · rw [h] at h'; cases h'
    · exact hM2 e he e' he' (Sum.inr.inj (h.symm.trans h'))
  omega
