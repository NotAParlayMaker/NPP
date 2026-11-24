import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2901

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 }

def or2 (u v : Bool) : Bool := u || (v || false)

def and2 (u v : Bool) : Bool := u && (v && true)

def F (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  let w14 := or2 a3 b2
  let w15 := or2 a5 b1
  let w16 := and2 w14 w15
  let w17 := or2 a3 a5
  let w18 := and2 w16 w17
  let w19 := or2 w18 a0
  let w20 := or2 w19 a4
  let w21 := and2 w20 b1
  let w22 := or2 w19 a6
  let w23 := and2 w22 b2
  let w24 := or2 a0 a1
  let w25 := or2 w24 a2
  let w26 := and2 w25 b0
  let w27 := or2 a1 a3
  let w28 := or2 w27 a5
  let w29 := and2 w28 b3
  let w30 := or2 a1 a4
  let w31 := or2 w30 a6
  let w32 := and2 w31 b4
  let w33 := or2 a2 a3
  let w34 := or2 w33 a6
  let w35 := and2 w34 b5
  let w36 := or2 a2 a4
  let w37 := or2 w36 a5
  let w38 := and2 w37 b6
  let w39 := or2 w21 w23
  let w40 := or2 w39 w26
  let w41 := or2 w40 w29
  let w42 := or2 w41 w32
  let w43 := or2 w42 w35
  or2 w43 w38

def G (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  (a0 && b0) || (a1 && b0) || (a2 && b0) || (a0 && b1) || (a3 && b1) || (a4 && b1) || (a0 && b2) || (a5 && b2) || (a6 && b2) || (a1 && b3) || (a3 && b3) || (a5 && b3) || (a1 && b4) || (a4 && b4) || (a6 && b4) || (a2 && b5) || (a3 && b5) || (a6 && b5) || (a2 && b6) || (a4 && b6) || (a5 && b6)

theorem lhs (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) :
    C0.eval [a0, a1, a2, a3, a4, a5, a6, b0, b1, b2, b3, b4, b5, b6] = F a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 := by
  simp only [C0, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, GateOp.eval,
    List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id,
    List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, F, or2, and2]

theorem tab : ∀ a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool, F a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 = G a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem ofFn7 (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := rfl

theorem rhs (x y : Fin 7 → Bool) :
    decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true)
      = G (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨p, l, hm, hx, hy⟩
    fin_cases p <;> fin_cases l <;> simp_all [G]
  · intro h
    simp only [G, Bool.or_eq_true, Bool.and_eq_true, or_assoc] at h
    rcases h with ⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩ <;>
      exact ⟨_, _, by decide, h1, h2⟩

theorem main (x y : Fin 7 → Bool) :
    C0.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  rw [rhs x y, ofFn7 x, ofFn7 y]
  exact (lhs (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)).trans (tab (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6))

end PEqualNP.Outside.L_meta_2901

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_2901 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 31 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ x y : Fin 7 → Bool, C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true)) ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a : Fin 7 => decide (a ∈ ({3} : Finset (Fin 7)))) ++ List.ofFn (fun b : Fin 7 => decide (b ∈ ({1} : Finset (Fin 7))))) = false ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a2 : Fin 7 => decide (a2 ∈ ({5} : Finset (Fin 7)))) ++ List.ofFn (fun b2 : Fin 7 => decide (b2 ∈ ({2} : Finset (Fin 7))))) = false := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_, PEqualNP.Outside.L_meta_2901.main, ?_, ?_⟩
  · simp [Monotone2]
  · decide +kernel
  · decide +kernel
  · decide +kernel
