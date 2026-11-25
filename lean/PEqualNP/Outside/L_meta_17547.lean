import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17547

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem pre (x2 : List (Bool × Fin 32 × Fin 32)) (x3 : List ℕ → Bool × Fin 32 × Fin 32 → ℕ) :
    ∀ (x1 : List ℕ) (i : ℕ), i < x1.length →
      (List.foldl (fun x5 x6 => x5 ++ [x3 x5 x6]) x1 x2).getD i 0 = x1.getD i 0 := by
  induction x2 with
  | nil => intro x1 i _; rfl
  | cons a t ih =>
    intro x1 i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_17547

theorem PEqualNP.Outside.L_meta_17547 : ∀ (x1 : List ℕ) (x2 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x3 : List ℕ → Bool × Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ) (x4 : Fin x1.length), (List.foldl (fun (x5 : List ℕ) (x6 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x5 ++ [x3 x5 x6]) x1 x2).getD ↑x4 (0 : ℕ) = x1.getD ↑x4 (0 : ℕ) := by
  intro x1 x2 x3 x4
  exact L_meta_17547.pre x2 x3 x1 x4 x4.2
