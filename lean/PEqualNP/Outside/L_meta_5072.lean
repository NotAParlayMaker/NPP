import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5072

theorem PEqualNP.Outside.L_meta_5072 :
  (have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)));
   have x2 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => x2.op.eval [Bool.false] && !x2.op.eval [Bool.true];
   have x3 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 : ℕ) => Decidable.decide (x3.inputs[(0 : ℕ)]? = Option.some x4) || !x2 x3 && x3.inputs.contains x4;
   ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
     PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) →
     (x4.output ≤ (24 : ℕ) ∧ ∀ x7 ∈ x4.gates, ∀ x9 ∈ x7.inputs, x9 ≤ (24 : ℕ)) →
     (∀ x8 < (24 : ℕ), x8 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) →
     (9 : ℕ) + (List.filter x2 x4.gates).length + ∑ x9 ∈ Finset.range (24 : ℕ), (List.count x9 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ (14 : ℕ) →
     (1 : ℕ) ≤ (List.filter x2 x4.gates).length →
     (2 : ℕ) ≤ List.count (9 : ℕ) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) →
     (∀ (x12 : Fin (9 : ℕ)), ∃ (x13 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x13 ++ [x13 x12]) ≠ x1 x13) →
     List.countP (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x3 x13 (0 : ℕ)) x4.gates ≤ (2 : ℕ) →
     List.countP (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => x3 x14 (3 : ℕ)) x4.gates ≤ (2 : ℕ) →
     ∃ (x15 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x15 ++ [x15 (0 : Fin (9 : ℕ)) || x15 (3 : Fin (9 : ℕ))]) ≠ x1 x15) := by
  sorry

end PEqualNP.Outside.L_meta_5072