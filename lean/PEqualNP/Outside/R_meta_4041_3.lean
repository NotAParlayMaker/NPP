import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-4041`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_4041_3 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (42 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → x2.card ≤ (2 : ℕ) → (∀ x6 ∈ x2, ↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → (∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x9 : Fin (42 : ℕ)) => Decidable.decide (x9 ∈ x2))).getD ((42 : ℕ) + x7) Bool.false = Bool.true) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x8 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (42 : ℕ)) (x10 : Fin (42 : ℕ)), (↑x9 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x10 ∧ (↑x10 + (21 : ℕ) - ↑x9) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (42 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → x2.card ≤ (2 : ℕ) → (∀ x6 ∈ x2, ↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → (∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x9 : Fin (42 : ℕ)) => Decidable.decide (x9 ∈ x2))).getD ((42 : ℕ) + x7) Bool.false = Bool.true) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x8 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (42 : ℕ)) (x10 : Fin (42 : ℕ)), (↑x9 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x10 ∧ (↑x10 + (21 : ℕ) - ↑x9) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (42 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → x2.card ≤ (2 : ℕ) → (∀ x6 ∈ x2, ↑x6 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]) → (∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x9 : Fin (42 : ℕ)) => Decidable.decide (x9 ∈ x2))).getD ((42 : ℕ) + x7) Bool.false = Bool.true) → ∃ (x8 : Fin (42 : ℕ) → Bool), ¬(x1.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (42 : ℕ)) (x10 : Fin (42 : ℕ)), (↑x9 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x10 ∧ (↑x10 + (21 : ℕ) - ↑x9) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) := by
  classical
  intro h1 h2 x1 x2
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
