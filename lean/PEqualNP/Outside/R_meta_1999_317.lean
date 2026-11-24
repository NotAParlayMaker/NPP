import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1999_317
    (cAndLe : ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)],
      (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) →
      (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) →
      (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) →
      ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x9 →
        (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) →
        (2 : ℕ) * (x9.gates.filter fun g => g.op.eval []).length ≤ x9.size →
        ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ)))
    (cOrLe : ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)],
      (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) →
      (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) →
      (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) →
      ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x9 →
        (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) →
        (2 : ℕ) * (x9.gates.filter fun g => !g.op.eval []).length ≤ x9.size →
        ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := cAndLe
  obtain ⟨c2, hc2⟩ := cOrLe
  refine ⟨max c1 c2, ?_⟩
  intro x2 x3 x4 _ hd1 hd2 hc4 x9 hmono hev
  have hsum : ∀ l : List PEqualNP.CircuitLowerBounds.Gate,
      (l.filter fun g => g.op.eval []).length + (l.filter fun g => !g.op.eval []).length = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons g t ih =>
      cases hge : g.op.eval [] <;> simp [List.filter_cons, hge] <;> omega
  have htot := hsum x9.gates
  by_cases ha : 2 * (x9.gates.filter fun g => g.op.eval []).length ≤ x9.size
  · exact (hc1 x2 x3 x4 hd1 hd2 hc4 x9 hmono hev ha).trans (Nat.mul_le_mul_right _ (le_max_left c1 c2))
  · have ho : 2 * (x9.gates.filter fun g => !g.op.eval []).length ≤ x9.size := by
      change 2 * (x9.gates.filter fun g => !g.op.eval []).length ≤ x9.gates.length
      change ¬ 2 * (x9.gates.filter fun g => g.op.eval []).length ≤ x9.gates.length at ha
      omega
    exact (hc2 x2 x3 x4 hd1 hd2 hc4 x9 hmono hev ho).trans (Nat.mul_le_mul_right _ (le_max_right c1 c2))
