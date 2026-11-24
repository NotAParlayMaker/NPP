import Mathlib
import PEqualNP.Defs

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_4209 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ∃ x3 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].toFinset, x1 = x2 + x3; ∀ (x2 : ℕ) (x3 : Fin (13 : ℕ)),   x2 ∈ [(8191 : ℕ), (7668 : ℕ), (6624 : ℕ), (5584 : ℕ), (3492 : ℕ), (1408 : ℕ), (7492 : ℕ), (7316 : ℕ), (6272 : ℕ), (7472 : ℕ), (4176 : ℕ), (2084 : ℕ), (6144 : ℕ), (5120 : ℕ), (4160 : ℕ), (2304 : ℕ), (2052 : ℕ), (4112 : ℕ), (4096 : ℕ), (0 : ℕ)].toFinset →     have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x2.testBit ↑(x5 - x3) = Bool.true};     have x6 : Fin (13 : ℕ) → Prop := fun (x6 : Fin (13 : ℕ)) => ∀ x7 ∈ x5, ¬x1 x7 x6;     (∀ x7 ∉ x5, ∃ (x9 : Fin (13 : ℕ)), x6 x9 ∧ x1 x7 x9) ∧ ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x1 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x6 x8 → x1 x7 x8) := by
  dsimp only
  intro x2 x3 hx2
  rw [List.mem_toFinset] at hx2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_cons,
    or_and_right, exists_or, exists_eq_left, List.not_mem_nil, or_false]
  revert x3
  revert hx2
  revert x2
  decide +kernel
