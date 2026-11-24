import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2377_3
    (hT1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ((x1.size ≤ 12) →  PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard))
    (hT2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (( ¬ x1.size ≤ 12) →  PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  classical
  intro v1
  by_cases h : (v1.size ≤ 12)
  · exact @hT1 v1 h
  · exact @hT2 v1 h
