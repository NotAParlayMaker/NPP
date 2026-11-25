import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8329 : have x1 : Finset (Fin (7 : ℕ) × Fin (7 : ℕ)) := {x1 : Fin (7 : ℕ) × Fin (7 : ℕ) | x1.1 = x1.2 ∨ x1.1 = x1.2 + (1 : Fin (7 : ℕ)) ∨ x1.1 = x1.2 + (3 : Fin (7 : ℕ))}; have x2 : Finset (Fin (7 : ℕ) × Fin (7 : ℕ)) := {x2 : Fin (7 : ℕ) × Fin (7 : ℕ) | x2.1 = x2.2}; x2 ⊆ x1 ∧ (∀ x3 ∈ x2, ∀ x5 ∈ x2, x3.1 = x5.1 → x3 = x5) ∧ (∀ x3 ∈ x2, ∀ x5 ∈ x2, x3.2 = x5.2 → x3 = x5) ∧ (∀ (x3 x4 x5 x6 : Fin (7 : ℕ)), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x1 ∧ (x3, x6) ∈ x1 ∧ (x4, x5) ∈ x1 ∧ (x4, x6) ∈ x1)) ∧ x1.card = (21 : ℕ) ∧ x2.card = (7 : ℕ) := by
  set_option maxHeartbeats 8000000 in
  set_option maxRecDepth 100000 in
  (intros
   try subst_vars
   repeat' apply And.intro
   all_goals first
     | decide +kernel
     | simp [PEqualNP.MetaComplexity.Monotone2]
     | (simp [PEqualNP.MetaComplexity.Monotone2]; decide))
