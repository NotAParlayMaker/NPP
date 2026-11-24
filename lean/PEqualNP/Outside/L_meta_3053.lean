import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3053

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 28] }], output := 44 }

def or2 (u v : Bool) : Bool := u || (v || false)

def and2 (u v : Bool) : Bool := u && (v && true)

def F (a0 a1 a2 a3 a4 a5 _a6 b0 b1 b2 b3 b4 b5 _b6 : Bool) : Bool :=
  let w14 := or2 a1 a2
  let w15 := or2 w14 a0
  let w16 := or2 w15 a3
  let w17 := and2 w14 b0
  let w18 := and2 w16 b0
  let w19 := or2 b0 b4
  let w20 := and2 a0 w19
  let w21 := or2 a1 a4
  let w22 := and2 w21 b3
  let w23 := or2 b3 b2
  let w24 := and2 a1 w23
  let w25 := or2 a2 a5
  let w26 := and2 w25 b5
  let w27 := or2 b5 b1
  let w28 := and2 a2 w27
  let w29 := and2 w17 w18
  let w30 := or2 w17 w18
  let w31 := and2 w30 w20
  let w32 := or2 w29 w31
  let w33 := or2 w30 w20
  let w34 := and2 w33 w22
  let w35 := or2 w32 w34
  let w36 := or2 w33 w22
  let w37 := and2 w36 w24
  let w38 := or2 w35 w37
  let w39 := or2 w36 w24
  let w40 := and2 w39 w26
  let w41 := or2 w38 w40
  let w42 := or2 w39 w26
  let w43 := and2 w42 w28
  or2 w41 w43

def G (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  (a0 && b0) || (a1 && b0) || (a2 && b0) || (a0 && b1) || (a3 && b1) || (a4 && b1) || (a0 && b2) || (a5 && b2) || (a6 && b2) || (a1 && b3) || (a3 && b3) || (a5 && b3) || (a1 && b4) || (a4 && b4) || (a6 && b4) || (a2 && b5) || (a3 && b5) || (a6 && b5) || (a2 && b6) || (a4 && b6) || (a5 && b6)

theorem lhs (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) :
    C0.eval [a0, a1, a2, a3, a4, a5, a6, b0, b1, b2, b3, b4, b5, b6] = F a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 := by
  simp only [C0, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, GateOp.eval,
    List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id,
    List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero, F, or2, and2]

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
    C0.eval (List.ofFn x ++ List.ofFn y) = F (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) := by
  rw [ofFn7 x, ofFn7 y]
  exact lhs (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)

theorem noinc (x y : Fin 7 → Bool) :
    (∃ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) ↔ G (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) = true := by
  rw [← rhs x y, decide_eq_true_iff]

theorem flags : ∀ p l : Fin 7, F (decide ((0 : Fin 7) = p)) (decide ((1 : Fin 7) = p)) (decide ((2 : Fin 7) = p)) (decide ((3 : Fin 7) = p)) (decide ((4 : Fin 7) = p)) (decide ((5 : Fin 7) = p)) (decide ((6 : Fin 7) = p)) (decide ((0 : Fin 7) = l)) (decide ((1 : Fin 7) = l)) (decide ((2 : Fin 7) = l)) (decide ((3 : Fin 7) = l)) (decide ((4 : Fin 7) = l)) (decide ((5 : Fin 7) = l)) (decide ((6 : Fin 7) = l)) = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (1, 3), (2, 5)] : List (ℕ × ℕ))) := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem key5 : ∀ a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool, ¬ (G a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 = true) →
    (F a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 = true ↔ ((a0 = false ∧ a1 = true ∧ a2 = true ∧ a3 = false ∧ a4 = false ∧ a5 = false ∧ a6 = false) ∧ (b0 = false ∧ b1 = true ∧ b2 = true ∧ b3 = false ∧ b4 = false ∧ b5 = false ∧ b6 = false)) ∨ ((a0 = true ∧ a1 = false ∧ a2 = false ∧ a3 = false ∧ a4 = false ∧ a5 = true ∧ a6 = false) ∧ (b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false ∧ b4 = true ∧ b5 = true ∧ b6 = false))) := by
  decide +kernel

theorem v12 (x : Fin 7 → Bool) :
    (∀ i : Fin 7, x i = decide (i ∈ ({1, 2} : Finset (Fin 7)))) ↔ (x 0 = false ∧ x 1 = true ∧ x 2 = true ∧ x 3 = false ∧ x 4 = false ∧ x 5 = false ∧ x 6 = false) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2, by simpa using h 3, by simpa using h 4, by simpa using h 5, by simpa using h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    fin_cases i <;> simp_all

theorem v05 (x : Fin 7 → Bool) :
    (∀ i : Fin 7, x i = decide (i ∈ ({0, 5} : Finset (Fin 7)))) ↔ (x 0 = true ∧ x 1 = false ∧ x 2 = false ∧ x 3 = false ∧ x 4 = false ∧ x 5 = true ∧ x 6 = false) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2, by simpa using h 3, by simpa using h 4, by simpa using h 5, by simpa using h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    fin_cases i <;> simp_all

theorem v45 (x : Fin 7 → Bool) :
    (∀ i : Fin 7, x i = decide (i ∈ ({4, 5} : Finset (Fin 7)))) ↔ (x 0 = false ∧ x 1 = false ∧ x 2 = false ∧ x 3 = false ∧ x 4 = true ∧ x 5 = true ∧ x 6 = false) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2, by simpa using h 3, by simpa using h 4, by simpa using h 5, by simpa using h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    fin_cases i <;> simp_all

end PEqualNP.Outside.L_meta_3053

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_3053 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 28] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 32 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ (p l : Fin 7), ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) → PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn (fun a : Fin 7 => decide (a = p)) ++ List.ofFn (fun b : Fin 7 => decide (b = l))) = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (1, 3), (2, 5)] : List (ℕ × ℕ)))) ∧
  (∀ x y : Fin 7 → Bool, (¬ ∃ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn x ++ List.ofFn y) = true ↔ ((∀ i : Fin 7, x i = decide (i ∈ ({1, 2} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({1, 2} : Finset (Fin 7)))) ∨ ((∀ i : Fin 7, x i = decide (i ∈ ({0, 5} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({4, 5} : Finset (Fin 7)))))) := by
  intro C hC
  have hC0 : C = PEqualNP.Outside.L_meta_3053.C0 := hC
  subst hC0
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [Monotone2, PEqualNP.Outside.L_meta_3053.C0]
  · decide +kernel
  · intro p l _
    rw [PEqualNP.Outside.L_meta_3053.main]
    exact PEqualNP.Outside.L_meta_3053.flags p l
  · intro x y h
    rw [PEqualNP.Outside.L_meta_3053.noinc] at h
    rw [PEqualNP.Outside.L_meta_3053.main, PEqualNP.Outside.L_meta_3053.v12 x, PEqualNP.Outside.L_meta_3053.v12 y, PEqualNP.Outside.L_meta_3053.v05 x, PEqualNP.Outside.L_meta_3053.v45 y]
    exact PEqualNP.Outside.L_meta_3053.key5 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) h
