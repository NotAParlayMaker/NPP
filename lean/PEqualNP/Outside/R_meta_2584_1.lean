import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2584_1
    (least_to_read2 : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
        (E : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
          ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        PEqualNP.TopForm.IsAO2 (P + L) E →
        (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) E z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) →
        (∀ E' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) E' → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) E' z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → E.size ≤ E'.size) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) ∧ D.size ≤ E.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2)
    (exists_least : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
        (Ct : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (P + L) Ct →
        (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) Ct z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) →
        ∃ Ct' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) Ct' ∧ (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) Ct' z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) ∧ Ct'.size ≤ Ct.size ∧ (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) C' → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C' z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → Ct'.size ≤ C'.size))
    : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2 := by
  intro P L I inst C hfour hAO hcomp
  rcases exists_least P L I C hAO hcomp with ⟨Cmin, hAOmin, hcommin, hsizemin, hmin⟩
  rcases least_to_read2 P L I Cmin hfour hAOmin hcommin hmin with
    ⟨D, hAOd, hcompd, hsized, hread⟩
  exact ⟨D, hAOd, hcompd, le_trans hsized hsizemin, hread⟩
