import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17209_aux

def S0 : Fin 13 → Finset (Fin 13) :=
  ![{2, 4, 5, 6}, {2, 4, 5, 6}, {2, 4, 5, 6}, {2, 4, 5, 6}, {2, 4, 5, 6}, {2, 4, 5, 6},
    {2, 4, 5, 6}, {2, 4, 7, 8}, {2, 4, 5, 8}, {2, 4, 5, 6}, {2, 5, 6, 10}, {2, 4, 6, 11},
    {2, 4, 5, 12}]

def W (x2 x3 : Fin 13) : Finset (Fin 13) := (S0 (x2 - x3)).image (fun y => y + x3)

theorem key : ∀ (x2 x3 : Fin 13), x2 - x3 ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
    (W x2 x3).card = 4 ∧ (∀ (x6 : Fin 13), {x7 ∈ W x2 x3 | x7 - x6 ∈ ({0, 1, 3, 9} : Finset (Fin 13))}.card ≤ 2) ∧
    x2 ∈ W x2 x3 ∧ ∀ x6 ∈ W x2 x3, x6 - x3 ∉ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_17209_aux

open PEqualNP.Outside.L_meta_17209_aux in
theorem PEqualNP.Outside.L_meta_17209 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Fin (13 : ℕ)), x2 - x3 ∉ x1 → ∃ (x5 : Finset (Fin (13 : ℕ))), x5.card = (4 : ℕ) ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) ∧ x2 ∈ x5 ∧ ∀ x6 ∈ x5, x6 - x3 ∉ x1 := by
  intro x1 x2 x3 h
  exact ⟨W x2 x3, key x2 x3 h⟩
