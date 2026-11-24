import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4710

theorem PEqualNP.Outside.L_meta_4710 :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset ℕ),
    (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x14 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x14 ∧ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 → ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) → (∀ x16 ∈ x6, x16 < x5.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x16).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x17 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x17 = Bool.true ↔ ∃ x18 ∈ x6, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x18 x17 = Bool.true) → (∀ (x18 x19 : Fin x2), x3 x18 x19 → ∃ x21 ∈ x6, (PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x21 fun (x22 : Fin (x2 + x2)) => Decidable.decide (x22 = Fin.castAdd x2 x18 ∨ x22 = Fin.natAdd x2 x19)) = Bool.true) → (∀ (x19 : Fin (x2 + x2) → Bool), Fintype.card { x20 : Fin x2 // x19 (Fin.natAdd x2 x20) = Bool.true } ≤ x1 → (¬∃ (x21 : Fin x2) (x22 : Fin x2), x3 x21 x22 ∧ x19 (Fin.castAdd x2 x21) = Bool.true ∧ x19 (Fin.natAdd x2 x22) = Bool.true) → ∀ x22 ∈ x6, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 x22 x19 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  sorry

end PEqualNP.Outside.L_meta_4710