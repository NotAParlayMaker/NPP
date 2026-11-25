import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2872_5
    (lower : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n+m) C →
      (∀ z, PEqualNP.MetaComplexity.circuitFun (n+m) C z =
        Decidable.decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = Bool.true ∧ z (Fin.natAdd n l) = Bool.true)) →
      ∃ T : Finset (Fin (n+m)),
        (∀ (p : Fin n) (l : Fin m), (p,l) ∈ E → Fin.castAdd m p ∈ T ∨ Fin.natAdd n l ∈ T) ∧
        E.card + T.card ≤ C.size + 1)
    (koenig : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (T : Finset (Fin (n+m))),
      (∀ (p : Fin n) (l : Fin m), (p,l) ∈ E → Fin.castAdd m p ∈ T ∨ Fin.natAdd n l ∈ T) →
      M ⊆ E → (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) →
      (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) → M.card ≤ T.card) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m E M C square ao val sub rows cols
  obtain ⟨T, hcover, hbound⟩ := lower n m E C square ao val
  have hm : M.card ≤ T.card := koenig n m E M T hcover sub rows cols
  omega
