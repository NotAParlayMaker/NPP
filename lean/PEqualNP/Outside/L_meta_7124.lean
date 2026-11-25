import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_970
import PEqualNP.Outside.L_meta_7121
import PEqualNP.Outside.R_meta_969_1

theorem PEqualNP.Outside.L_meta_7124 : ¬ (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (10 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (8 : ℕ)) (x4 : Fin (8 : ℕ)), (↑x3, ↑x4) ∈ [((0 : ℕ), (1 : ℕ)), ((0 : ℕ), (2 : ℕ)), ((0 : ℕ), (4 : ℕ)), ((1 : ℕ), (3 : ℕ)), ((1 : ℕ), (5 : ℕ)), ((2 : ℕ), (3 : ℕ)), ((2 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (5 : ℕ)), ((4 : ℕ), (6 : ℕ)), ((5 : ℕ), (7 : ℕ)), ((6 : ℕ), (7 : ℕ))] ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true) := by
  intro h2
  obtain ⟨C, hmono, hsize, heval⟩ := PEqualNP.Outside.R_meta_969_1 PEqualNP.Outside.L_meta_7121 h2
  have h12 := PEqualNP.Outside.L_meta_970 C hmono heval
  omega
