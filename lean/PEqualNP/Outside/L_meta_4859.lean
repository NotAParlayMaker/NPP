import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4859

theorem PEqualNP.Outside.L_meta_4859 :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 x8 : Fin x6 ↪ Fin x1),
    Odd x6 →
    (∀ (x10 : Fin x6), x2.Adj (x7 x10) (x8 x10) ∧ x8 x10 ∉ Set.range ⇑x7) →
    (∀ (x11 x12 : Fin x6), x2.Adj (x7 x11) (x7 x12) ↔ (↑x11 + (1 : ℕ)) % x6 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x6 = ↑x11) →
    (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard = if x12 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →
    (7 : ℕ∞) ≤ x2.egirth →
    PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
    PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
    ∃ (x16 : Fin x6) (x17 : Fin x6),
      x2.Adj (x7 x16) (x7 x17) ∧
      ∃ (x18 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo (x18 (0 : ℕ)) ∧
        (x18 (0 : ℕ)).size ≤ x5.size ∧
        PEqualNP.MetaComplexity.circuitFun x1 (x18 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧
        ∀ x19 < (7 : ℕ),
          ∃ (x21 : ℕ) (x22 : ℕ),
            x21 < (x18 x19).size ∧
            (x22 < x1 + x21 ∨ x1 + (x18 x19).size ≤ x22) ∧
            x18 (x19 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x18 x19) x21 x22 ∧
            ((∀ (x23 : Fin x1 → Bool),
              (have x24 : List Bool := (x18 x19).wires (List.ofFn (Function.update (Function.update x23 (x7 x16) Bool.false) (x7 x17) Bool.false));
               x24.getD (x1 + x21) Bool.false = x24.getD x22 Bool.false)) ∨
             (x18 x19).output ≠ x1 + x21 ∧ ∀ x23 ∈ List.drop (x21 + (1 : ℕ)) (x18 x19).gates, x1 + x21 ∉ x23.inputs)) := by
  sorry

end PEqualNP.Outside.L_meta_4859