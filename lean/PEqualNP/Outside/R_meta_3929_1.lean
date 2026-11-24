import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-3929`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_3929_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∃ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x6 ≥ (9 : ℕ), x5.inputs = [(0 : ℕ), x6] ∨ x5.inputs = [x6, (0 : ℕ)]) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then !x6 (0 : Fin (9 : ℕ)) else x6 x7) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (9 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (9 : ℕ) (x7 % (10 : ℕ)))) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → False) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∃ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x6 ≥ (9 : ℕ), x5.inputs = [(0 : ℕ), x6] ∨ x5.inputs = [x6, (0 : ℕ)]) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then !x6 (0 : Fin (9 : ℕ)) else x6 x7) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (9 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (9 : ℕ) (x7 % (10 : ℕ)))) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → False) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∃ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ x6 ≥ (9 : ℕ), x5.inputs = [(0 : ℕ), x6] ∨ x5.inputs = [x6, (0 : ℕ)]) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then !x6 (0 : Fin (9 : ℕ)) else x6 x7) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (9 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (9 : ℕ) (x7 % (10 : ℕ)))) → False) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
