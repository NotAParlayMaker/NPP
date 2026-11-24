import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2001_3
    (h1 : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
        PEqualNP.SharedBlockCost.HasSharedBlockCost G (c * (C.size + 1)))
    (h2 : ∃ c : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PEqualNP.SharedBlockCost.HasSharedBlockCost G k →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C' ∧
        C'.size + 1 ≤ c * (k + 1) ∧
        ∀ x y : Fin n → Bool, C'.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ y v = true)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  refine ⟨c2 * (c1 + 1), ?_⟩
  intro n G _ hdeg hcyc C hM heval
  have hsbc := hc1 n G hdeg hcyc C hM heval
  obtain ⟨C', hM', hsz', heval'⟩ := hc2 n (c1 * (C.size + 1)) G hsbc
  refine ⟨C', hM', ?_, heval'⟩
  have hle : c1 * (C.size + 1) + 1 ≤ (c1 + 1) * (C.size + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) _
  exact le_trans hsz' (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left c2 hle)
