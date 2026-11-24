import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2001_2
    (normal : ∃ (a : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ v : Fin n, G.degree v = (0 : ℕ) ∨ (3 : ℕ) ≤ G.degree v) → (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (5 : ℕ) ≤ w.length) → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →  (∀ x : Fin n → Bool, C.eval (List.ofFn x) = Decidable.decide (∃ u v : Fin n, G.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true)) → ∃ (E : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 E ∧ PEqualNP.SyntacticMultilinear.IsSyntMultilinear n E ∧  (∀ x : Fin n → Bool, E.eval (List.ofFn x) = Decidable.decide (∃ u v : Fin n, G.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true)) ∧ E.size + (1 : ℕ) ≤ a * (C.size + (1 : ℕ)))
    (polar : ∃ (b : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ v : Fin n, G.degree v = (0 : ℕ) ∨ (3 : ℕ) ≤ G.degree v) → (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (5 : ℕ) ≤ w.length) → ∀ (E : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 E → PEqualNP.SyntacticMultilinear.IsSyntMultilinear n E →  (∀ x : Fin n → Bool, E.eval (List.ofFn x) = Decidable.decide (∃ u v : Fin n, G.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + (1 : ℕ) ≤ b * (E.size + (1 : ℕ)) ∧ (∀ x y : Fin n → Bool, D.eval (List.ofFn x ++ List.ofFn y) = Decidable.decide (∃ u v : Fin n, G.Adj u v ∧ x u = Bool.true ∧ y v = Bool.true))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) := by
  classical
  obtain ⟨a, hnormal⟩ := normal
  obtain ⟨b, hpolar⟩ := polar
  refine ⟨a * b, ?_⟩
  intro n G inst hdegree hgirth C hmono hfunction
  obtain ⟨E, hEmono, hEmult, hEfunc, hEsize⟩ := hnormal n G hdegree hgirth C hmono hfunction
  obtain ⟨D, hDmono, hDsize, hDfunc⟩ := hpolar n G hdegree hgirth E hEmono hEmult hEfunc
  refine ⟨D, hDmono, ?_, hDfunc⟩
  calc
    D.size + 1 ≤ b * (E.size + 1) := hDsize
    _ ≤ b * (a * (C.size + 1)) := Nat.mul_le_mul_left b hEsize
    _ = (a * b) * (C.size + 1) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
