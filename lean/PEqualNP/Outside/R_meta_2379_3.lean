import Mathlib
import PEqualNP.Defs

-- L-meta-2379 cut by the number of OR gates: at most 103 OR gates is one case,
-- at least 104 OR gates is the other.  Both cases still have to show the 21 AND
-- gates, but the counting argument splits cleanly at the known 104 OR bound.
theorem PEqualNP.Outside.R_meta_2379_3
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → ({x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ≤ (103 : ℕ)) → (21 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → ((104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) → (21 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (21 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro C hm hf
  by_cases h : ({i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ≤ (103 : ℕ))
  · exact h1 C hm hf h
  · exact h2 C hm hf (by omega)
