import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17209

open PEqualNP.CircuitLowerBounds

def base (p : Fin 13) : Finset (Fin 13) :=
  match p.val with
  | 2 => {(2 : Fin 13), (4 : Fin 13), (5 : Fin 13), (6 : Fin 13)}
  | 4 => {(2 : Fin 13), (4 : Fin 13), (5 : Fin 13), (6 : Fin 13)}
  | 5 => {(2 : Fin 13), (4 : Fin 13), (5 : Fin 13), (6 : Fin 13)}
  | 6 => {(2 : Fin 13), (4 : Fin 13), (5 : Fin 13), (6 : Fin 13)}
  | 7 => {(2 : Fin 13), (4 : Fin 13), (7 : Fin 13), (8 : Fin 13)}
  | 8 => {(2 : Fin 13), (4 : Fin 13), (5 : Fin 13), (8 : Fin 13)}
  | 10 => {(2 : Fin 13), (5 : Fin 13), (6 : Fin 13), (10 : Fin 13)}
  | 11 => {(2 : Fin 13), (4 : Fin 13), (6 : Fin 13), (11 : Fin 13)}
  | 12 => {(2 : Fin 13), (4 : Fin 13), (5 : Fin 13), (12 : Fin 13)}
  | _ => ∅

def wit (p l : Fin 13) : Finset (Fin 13) := (base (p - l)).image (· + l)

theorem key : ∀ x2 x3 : Fin 13, x2 - x3 ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
    (wit x2 x3).card = 4 ∧ (∀ x6 : Fin 13, ((wit x2 x3).filter (fun x7 => x7 - x6 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    x2 ∈ wit x2 x3 ∧ ∀ x6 ∈ wit x2 x3, x6 - x3 ∉ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  decide +kernel

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_17209

theorem PEqualNP.Outside.L_meta_17209 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Fin (13 : ℕ)), x2 - x3 ∉ x1 → ∃ (x5 : Finset (Fin (13 : ℕ))), x5.card = (4 : ℕ) ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x7 - x6 ∈ x1}.card ≤ (2 : ℕ)) ∧ x2 ∈ x5 ∧ ∀ x6 ∈ x5, x6 - x3 ∉ x1 := by
  intro x1 x2 x3 h
  exact ⟨L_meta_17209.wit x2 x3, L_meta_17209.key x2 x3 h⟩
