import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-7387`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_7387_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (26 : ℕ) ≤ (Finset.image (fun (x4 : Fin ((11 : ℕ) + x1.size)) (x5 : Fin (9 : ℕ) → Bool) => (x1.wires [Bool.false, x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)), x5 (1 : Fin (9 : ℕ)), x5 (6 : Fin (9 : ℕ)), x5 (7 : Fin (9 : ℕ)), x5 (3 : Fin (9 : ℕ)), x5 (5 : Fin (9 : ℕ)), x5 (2 : Fin (9 : ℕ)), x5 (8 : Fin (9 : ℕ)), Bool.true]).getD (↑x4) Bool.false) Finset.univ).card → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (26 : ℕ) ≤ (Finset.image (fun (x4 : Fin ((11 : ℕ) + x1.size)) (x5 : Fin (9 : ℕ) → Bool) => (x1.wires [Bool.false, x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)), x5 (1 : Fin (9 : ℕ)), x5 (6 : Fin (9 : ℕ)), x5 (7 : Fin (9 : ℕ)), x5 (3 : Fin (9 : ℕ)), x5 (5 : Fin (9 : ℕ)), x5 (2 : Fin (9 : ℕ)), x5 (8 : Fin (9 : ℕ)), Bool.true]).getD (↑x4) Bool.false) Finset.univ).card → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (26 : ℕ) ≤ (Finset.image (fun (x4 : Fin ((11 : ℕ) + x1.size)) (x5 : Fin (9 : ℕ) → Bool) => (x1.wires [Bool.false, x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)), x5 (1 : Fin (9 : ℕ)), x5 (6 : Fin (9 : ℕ)), x5 (7 : Fin (9 : ℕ)), x5 (3 : Fin (9 : ℕ)), x5 (5 : Fin (9 : ℕ)), x5 (2 : Fin (9 : ℕ)), x5 (8 : Fin (9 : ℕ)), Bool.true]).getD (↑x4) Bool.false) Finset.univ).card → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x6 x7 = Bool.true ∧ x6 x8 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8 = Bool.true)) x5) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
