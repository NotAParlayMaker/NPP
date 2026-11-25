import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2584_1
    (h1 : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ (A : Finset (Fin P)) (B : Finset (Fin L)), (∀ p : Fin P, ∀ l : Fin L, I p l → p ∈ A ∨ l ∈ B) ∧ Fintype.card {q : Fin P × Fin L // I q.1 q.2} + A.card + B.card - 1 ≤ C.size)
    (h2 : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (A : Finset (Fin P)) (B : Finset (Fin L)), (∀ p : Fin P, ∀ l : Fin L, I p l → p ∈ A ∨ l ∈ B) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ Fintype.card {q : Fin P × Fin L // I q.1 q.2} + A.card + B.card - 1 ∧ PEqualNP.ReadK.IsReadK (P + L) D 2) :
    ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2 := by
  intro P L I _ C h4 hC hF
  obtain ⟨A, B, hcov, hle⟩ := h1 P L I C h4 hC hF
  obtain ⟨D, hD, hDF, hDs, hDr⟩ := h2 P L I A B hcov
  exact ⟨D, hD, hDF, le_trans hDs hle, hDr⟩
