import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7447_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x4 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) → (27 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (14 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x4 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) → (27 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x4 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) → (27 : ℕ) ≤ x1.size := by
  intro x1 hmono hreads hfun
  by_cases h : x1.output < 14
  · exact h1 x1 h hmono hreads hfun
  · have hge : 14 ≤ x1.output := by omega
    exact h2 x1 hge hmono hreads hfun
