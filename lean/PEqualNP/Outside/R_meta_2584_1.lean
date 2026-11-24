import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2584_1
    (hBuild : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ PEqualNP.ReadK.IsReadK (P + L) D 2 ∧ D.size ≤ C.size)
    (hSound : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C D : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → PEqualNP.TopForm.IsAO2 (P + L) D → PEqualNP.ReadK.IsReadK (P + L) D 2 → D.size ≤ C.size → ∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = Bool.true → ∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = Bool.true ∧ y (Fin.natAdd P l) = Bool.true)
    (hComplete : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C D : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → PEqualNP.TopForm.IsAO2 (P + L) D → PEqualNP.ReadK.IsReadK (P + L) D 2 → D.size ≤ C.size → ∀ y : Fin (P + L) → Bool, (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = Bool.true ∧ y (Fin.natAdd P l) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (P + L) D y = Bool.true) :
    ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2 := by
  intro P L I _ C hNo4 hAO2 hEq
  obtain ⟨D, hDAO2, hRead, hSize⟩ := hBuild P L I C hNo4 hAO2 hEq
  refine ⟨D, hDAO2, ?_, hSize, hRead⟩
  intro y
  let Q : Prop := ∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = Bool.true ∧ y (Fin.natAdd P l) = Bool.true
  have hS : Q → PEqualNP.MetaComplexity.circuitFun (P + L) D y = Bool.true := by
    intro hQ
    exact hComplete P L I C D hNo4 hAO2 hEq hDAO2 hRead hSize y hQ
  have hT : PEqualNP.MetaComplexity.circuitFun (P + L) D y = Bool.true → Q := by
    intro hTrue
    exact hSound P L I C D hNo4 hAO2 hEq hDAO2 hRead hSize y hTrue
  cases hVal : PEqualNP.MetaComplexity.circuitFun (P + L) D y with
  | false =>
      have hNotQ : ¬ Q := by
        intro hQ
        have hTrue : PEqualNP.MetaComplexity.circuitFun (P + L) D y = Bool.true := hS hQ
        have : Bool.false = Bool.true := hVal.symm.trans hTrue
        cases this
      have hDec : Decidable.decide Q = Bool.false := by
        by_cases hQ : Q
        · exact False.elim (hNotQ hQ)
        · simp [hQ]
      exact Eq.symm hDec
  | true =>
      have hQ : Q := hT hVal
      have hDec : Decidable.decide Q = Bool.true := by simp [hQ]
      exact Eq.symm hDec
