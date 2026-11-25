import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2585_1
    (hbudget : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (p q : Fin n) (l k : Fin m), p ≠ q → l ≠ k →
        ¬((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ z, PEqualNP.MetaComplexity.circuitFun (n + m) C z =
        decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card - 1 ≤ C.size)
    (hstar : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)),
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (n + m) D ∧
        D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, PEqualNP.MetaComplexity.circuitFun (n + m) D z =
          decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        PEqualNP.ReadK.IsReadK (n + m) D 1) :
    ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (P + L) C →
      (∀ z : Fin (P + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (P + L) C z =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (P + L) D ∧
        (∀ y : Fin (P + L) → Bool,
          PEqualNP.MetaComplexity.circuitFun (P + L) D y =
            decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
              y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  intro n m I dec C noFour ao eval
  let E := Finset.univ.filter (fun e : Fin n × Fin m => I e.1 e.2)
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  have agrees (z : Fin (n + m) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (n + m) C z =
        decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) := by
    simpa only [mem] using eval z
  obtain ⟨A, B, cover, budget⟩ := hbudget n m E C (by simpa only [mem] using noFour) ao agrees
  obtain ⟨D, dao, size, deval, read⟩ := hstar n m E A B cover
  exact ⟨D, dao, fun z => by simpa only [mem] using deval z, size.trans budget, read⟩
