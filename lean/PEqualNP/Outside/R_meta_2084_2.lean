import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2084_2 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (p : G.Walk w w), p.IsCycle → 7 ≤ p.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s →
        ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
          C.size + A.card ≤ s ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
            ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (p : G.Walk w w), p.IsCycle → 7 ≤ p.length) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeSet.ncard + k ≤ C.size + 1) →
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by
  intro noNot mono n k G A f deg girth isolated hedge cover hf s hs
  obtain ⟨C, hC, hsize, hval⟩ := noNot n G A f deg girth isolated hedge hf s hs
  have hdeg : ∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3 := by
    intro v
    by_cases h : v ∈ A
    · left
      have : G.neighborSet v = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun w hw => isolated v w hw h
      simp [this]
    · exact Or.inr (deg v h)
  have := mono n k G C hdeg girth hedge cover hC hval
  omega
