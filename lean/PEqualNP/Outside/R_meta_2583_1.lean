import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2583_1
    (existsMin : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (2 : ℕ) ≤ q → N = q ^ 2 + q + (1 : ℕ) →
        (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + (1 : ℕ)) →
          (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
            PEqualNP.TopForm.IsAO2 (N + N) C →
              (∀ z : Fin (N + N) → Bool,
                PEqualNP.MetaComplexity.circuitFun (N + N) C z =
                  decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
                    z (Fin.natAdd N l) = true)) →
                ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
                  PEqualNP.TopForm.IsAO2 (N + N) D ∧
                    (∀ y : Fin (N + N) → Bool,
                      PEqualNP.MetaComplexity.circuitFun (N + N) D y =
                        decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
                          y (Fin.natAdd N l) = true)) ∧
                      D.size ≤ C.size ∧
                        ∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
                          PEqualNP.TopForm.IsAO2 (N + N) D' →
                            (∀ y : Fin (N + N) → Bool,
                              PEqualNP.MetaComplexity.circuitFun (N + N) D' y =
                                decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
                                  y (Fin.natAdd N l) = true)) →
                              D.size ≤ D'.size)
    (minIsRead1 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (D : PEqualNP.CircuitLowerBounds.Circuit),
      (2 : ℕ) ≤ q → N = q ^ 2 + q + (1 : ℕ) →
        (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + (1 : ℕ)) →
          (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
            PEqualNP.TopForm.IsAO2 (N + N) D →
              (∀ z : Fin (N + N) → Bool,
                PEqualNP.MetaComplexity.circuitFun (N + N) D z =
                  decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
                    z (Fin.natAdd N l) = true)) →
                (∀ D' : PEqualNP.CircuitLowerBounds.Circuit,
                  PEqualNP.TopForm.IsAO2 (N + N) D' →
                    (∀ y : Fin (N + N) → Bool,
                      PEqualNP.MetaComplexity.circuitFun (N + N) D' y =
                        decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
                          y (Fin.natAdd N l) = true)) →
                      D.size ≤ D'.size) →
                  PEqualNP.ReadK.IsReadK (N + N) D (1 : ℕ)) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  intro q N I _ C hq hN hline hpair hAO hfun
  obtain ⟨D, hDAO, hDfun, hDle, hDmin⟩ := existsMin q N I C hq hN hline hpair hAO hfun
  exact ⟨D, hDAO, hDfun, hDle, minIsRead1 q N I D hq hN hline hpair hDAO hDfun hDmin⟩
