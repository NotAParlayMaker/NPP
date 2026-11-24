import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_4875 :
    have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); ∀ (x2 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x2) ≤ (3 : ℕ) ∨ List.count Bool.true (List.ofFn (x1 x2)) ≤ (3 : ℕ) := by
  decide
