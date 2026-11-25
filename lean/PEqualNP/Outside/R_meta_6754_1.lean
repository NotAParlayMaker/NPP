import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-6754`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_6754_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (15 : ℕ) → x1.output = (23 : ℕ) → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → (∀ x6 < (14 : ℕ), ∃ (x8 : Fin x1.gates.length), x6 < ↑x8 ∧ (9 : ℕ) + x6 ∈ (x1.gates.get x8).inputs) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (15 : ℕ) → x1.output = (23 : ℕ) → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → (∀ x6 < (14 : ℕ), ∃ (x8 : Fin x1.gates.length), x6 < ↑x8 ∧ (9 : ℕ) + x6 ∈ (x1.gates.get x8).inputs) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (15 : ℕ) → x1.output = (23 : ℕ) → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → (∀ x6 < (14 : ℕ), ∃ (x8 : Fin x1.gates.length), x6 < ↑x8 ∧ (9 : ℕ) + x6 ∈ (x1.gates.get x8).inputs) → ∃ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
