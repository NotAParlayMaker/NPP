import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4787

theorem PEqualNP.Outside.L_meta_4787 :
  (let x1 : Type := Fin (13 : ℕ);
   have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)};
   let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5;
   let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5;
   let x5 : Type := Fin (26 : ℕ) → Bool;
   have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7);
   have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9);
   have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10);
   ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
     PEqualNP.MetaComplexity.Monotone2 x9 →
     x9.size ≤ (60 : ℕ) →
     (have x12 : ℕ → x5 → Bool := fun (x12 : ℕ) (x13 : x5) => (x9.wires (List.ofFn x13 ++ [Bool.true, Bool.false])).getD x12 Bool.false;
      have x13 : (x5 → Bool) → Prop := fun (x13 : x5 → Bool) => ∀ (x14 x15 : x1), x3 x14 x15 → x13 (x6 x14 x15) = Bool.true;
      ∀ (x14 x15 : ℕ), (x13 fun (x16 : x5) => x12 x14 x16 || x12 x15 x16) → ¬x13 (x12 x14) → ¬x13 (x12 x15) → (∀ (x19 : Finset x1), x8 x19 → ¬(x12 x14 (x7 x19) || x12 x15 (x7 x19)) = Bool.true) → False)) := by
  sorry

end PEqualNP.Outside.L_meta_4787