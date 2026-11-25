import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17531

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_17531

theorem PEqualNP.Outside.L_meta_17531 : ∀ (x1 : List Bool) (x2 : ℕ), (List.foldr Nat.bit (0 : ℕ) x1).testBit x2 = x1.getD x2 Bool.false := by
  intro x1
  induction x1 with
  | nil => intro x2; simp
  | cons b l ih =>
    intro x2
    cases x2 with
    | zero => simp [List.foldr, Nat.testBit_bit_zero]
    | succ k => simp [List.foldr, Nat.testBit_bit_succ, ih]
