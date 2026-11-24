import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4951 : ∀ (x1 x2 : Fin (9 : ℕ)),   ∃ (x3 : Fin (9 : ℕ) → Bool),     have x4 : (Fin (9 : ℕ) → Bool) → Bool := fun (x4 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x5 : ℕ) => x4 (Fin.ofNat (9 : ℕ) (x5 / (10 : ℕ))) && x4 (Fin.ofNat (9 : ℕ) (x5 % (10 : ℕ)));     x4 x3 = Bool.false ∧ (x4 fun (x5 : Fin (9 : ℕ)) => Decidable.decide (x5 = x1) || x3 x5) = Bool.true ∧ (x4 fun (x5 : Fin (9 : ℕ)) => Decidable.decide (x5 = x2) || x3 x5) = Bool.true := by
  set_option maxRecDepth 100000 in
  decide
