import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2195_1
    (h : ∃ n : ℕ, ∀ m : ℕ, n ≤ m)
    (hn : ¬ ∃ n : ℕ, ∀ m : ℕ, n ≤ m) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : Fin (13 : ℕ)),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ (x5 : Fin x1.length), ∀ x6 ∈ (x1.get x5).inputs, x6 < (10 : ℕ) + ↑x5) →         (∀ (x6 : Fin (9 : ℕ)), ∃ x7 ∈ x1, ↑x6 ∈ x7.inputs) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ))]);             (x8.getD ((10 : ℕ) + ↑x2) Bool.false || x8.getD (22 : ℕ) Bool.false) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  exact absurd h hn
