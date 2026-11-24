import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4135_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size < (18 : ℕ) → (∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [Bool.false]) ≠ x1.eval (List.ofFn x5 ++ [Bool.false])) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size ≤ (17 : ℕ) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6 ++ [Bool.false])) ∨ ∀ (x5 : Fin (10 : ℕ) → Bool) (x6 : Bool), x1.eval (List.ofFn x5 ++ [x6]) = x1.eval (List.ofFn x5 ++ [Bool.false]))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (18 : ℕ) → (∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [Bool.false]) ≠ x1.eval (List.ofFn x5 ++ [Bool.false])) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size ≤ (17 : ℕ) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6 ++ [Bool.false])) ∨ ∀ (x5 : Fin (10 : ℕ) → Bool) (x6 : Bool), x1.eval (List.ofFn x5 ++ [x6]) = x1.eval (List.ofFn x5 ++ [Bool.false])) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [Bool.false]) ≠ x1.eval (List.ofFn x5 ++ [Bool.false])) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size ≤ (17 : ℕ) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6 ++ [Bool.false])) ∨ ∀ (x5 : Fin (10 : ℕ) → Bool) (x6 : Bool), x1.eval (List.ofFn x5 ++ [x6]) = x1.eval (List.ofFn x5 ++ [Bool.false]) := by
  intro x1 hf hs hnonconst
  rcases lt_or_eq_of_le hs with hlt | heq
  · exact h1 x1 hf hlt hnonconst
  · exact h2 x1 hf heq hnonconst
