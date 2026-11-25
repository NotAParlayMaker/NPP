import PEqualNP.Defs

/-- Reduction glue for L-meta-12872 (twinned positive step: L-meta-12871).
h1: a NOT circuit of at most 10 gates (FanInTwo model) computes the target monotone six-input f.
h2: no monotone (Monotone2) circuit of at most 10 gates computes f.
Together these refute `∀ s, HasCircuitSize 6 f s → ∃ Monotone2 C ≤ s computing f`, i.e. L-meta-12872.
The counterexample witness is s = 10. -/
theorem PEqualNP.Outside.R_meta_12872_1
    (h1 : PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        Nat.testBit (4008372904 * 2 ^ 32 + 3936938664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) 10)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      C.size ≤ 10 →
      ¬∀ x : Fin 6 → Bool,
        C.eval (List.ofFn x) =
          Nat.testBit (4008372904 * 2 ^ 32 + 3936938664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) :
    ¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
        (fun x : Fin 6 → Bool =>
          Nat.testBit (4008372904 * 2 ^ 32 + 3936938664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool,
          C.eval (List.ofFn x) =
            Nat.testBit (4008372904 * 2 ^ 32 + 3936938664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro hall
  obtain ⟨C, hMono, hsz, hEq⟩ := hall 10 h1
  exact h2 C hMono hsz hEq
