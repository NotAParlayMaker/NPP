import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3053

open PEqualNP.CircuitLowerBounds

def fanoCircuit : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [14, 0]⟩, ⟨GateOp.or, [15, 3]⟩, ⟨GateOp.and, [14, 7]⟩, ⟨GateOp.and, [16, 7]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.and, [0, 19]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [21, 10]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [1, 23]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [25, 12]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.and, [2, 27]⟩, ⟨GateOp.and, [17, 18]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.and, [30, 20]⟩, ⟨GateOp.or, [29, 31]⟩, ⟨GateOp.or, [30, 20]⟩, ⟨GateOp.and, [33, 22]⟩, ⟨GateOp.or, [32, 34]⟩, ⟨GateOp.or, [33, 22]⟩, ⟨GateOp.and, [36, 24]⟩, ⟨GateOp.or, [35, 37]⟩, ⟨GateOp.or, [36, 24]⟩, ⟨GateOp.and, [39, 26]⟩, ⟨GateOp.or, [38, 40]⟩, ⟨GateOp.or, [39, 26]⟩, ⟨GateOp.and, [42, 28]⟩, ⟨GateOp.or, [41, 43]⟩, ⟨GateOp.or, [42, 28]⟩], 44⟩

def flagAt (x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : Bool) : Bool :=
  (x0 && y0) || (x1 && y0) || (x2 && y0) || (x0 && y1) || (x3 && y1) || (x4 && y1) || (x0 && y2) || (x5 && y2) || (x6 && y2) || (x1 && y3) || (x3 && y3) || (x5 && y3) || (x1 && y4) || (x4 && y4) || (x6 && y4) || (x2 && y5) || (x3 && y5) || (x6 && y5) || (x2 && y6) || (x4 && y6) || (x5 && y6)

def firstInput (x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : Bool) : Bool :=
  !x0 && x1 && x2 && !x3 && !x4 && !x5 && !x6 && !y0 && y1 && y2 && !y3 && !y4 && !y5 && !y6

def secondInput (x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : Bool) : Bool :=
  x0 && !x1 && !x2 && !x3 && !x4 && x5 && !x6 && !y0 && !y1 && !y2 && !y3 && y4 && y5 && !y6

theorem eval_all : ∀ x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : Bool,
    (flagAt x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 || (fanoCircuit.eval [x0, x1, x2, x3, x4, x5, x6, y0, y1, y2, y3, y4, y5, y6] == (firstInput x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 || secondInput x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6))) = true := by
  decide +kernel

theorem listOf (x y : Fin 7 → Bool) : List.ofFn x ++ List.ofFn y =
    [x 0, x 1, x 2, x 3, x 4, x 5, x 6, y 0, y 1, y 2, y 3, y 4, y 5, y 6] := by
  simp [List.ofFn_succ]

theorem set12 (x : Fin 7 → Bool) : (∀ i : Fin 7, x i = decide (i ∈ ({1, 2} : Finset (Fin 7)))) ↔
    (x 0 = false ∧ x 1 = true ∧ x 2 = true ∧ x 3 = false ∧ x 4 = false ∧ x 5 = false ∧ x 6 = false) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    fin_cases i
    exacts [h0, h1, h2, h3, h4, h5, h6]

theorem set05 (x : Fin 7 → Bool) : (∀ i : Fin 7, x i = decide (i ∈ ({0, 5} : Finset (Fin 7)))) ↔
    (x 0 = true ∧ x 1 = false ∧ x 2 = false ∧ x 3 = false ∧ x 4 = false ∧ x 5 = true ∧ x 6 = false) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    fin_cases i
    exacts [h0, h1, h2, h3, h4, h5, h6]

theorem set45 (x : Fin 7 → Bool) : (∀ i : Fin 7, x i = decide (i ∈ ({4, 5} : Finset (Fin 7)))) ↔
    (x 0 = false ∧ x 1 = false ∧ x 2 = false ∧ x 3 = false ∧ x 4 = true ∧ x 5 = true ∧ x 6 = false) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    fin_cases i
    exacts [h0, h1, h2, h3, h4, h5, h6]

theorem freeRows (x y : Fin 7 → Bool)
    (hb : ∀ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) → (x p && y l) = false) :
    (fanoCircuit.eval (List.ofFn x ++ List.ofFn y) = true ↔
      ((∀ i : Fin 7, x i = decide (i ∈ ({1, 2} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({1, 2} : Finset (Fin 7)))) ∨
      ((∀ i : Fin 7, x i = decide (i ∈ ({0, 5} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({4, 5} : Finset (Fin 7))))) := by
  have hf : flagAt (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) = false := by
    have f00 : (x 0 && y 0) = false := hb 0 0 (by decide)
    have f10 : (x 1 && y 0) = false := hb 1 0 (by decide)
    have f20 : (x 2 && y 0) = false := hb 2 0 (by decide)
    have f01 : (x 0 && y 1) = false := hb 0 1 (by decide)
    have f31 : (x 3 && y 1) = false := hb 3 1 (by decide)
    have f41 : (x 4 && y 1) = false := hb 4 1 (by decide)
    have f02 : (x 0 && y 2) = false := hb 0 2 (by decide)
    have f52 : (x 5 && y 2) = false := hb 5 2 (by decide)
    have f62 : (x 6 && y 2) = false := hb 6 2 (by decide)
    have f13 : (x 1 && y 3) = false := hb 1 3 (by decide)
    have f33 : (x 3 && y 3) = false := hb 3 3 (by decide)
    have f53 : (x 5 && y 3) = false := hb 5 3 (by decide)
    have f14 : (x 1 && y 4) = false := hb 1 4 (by decide)
    have f44 : (x 4 && y 4) = false := hb 4 4 (by decide)
    have f64 : (x 6 && y 4) = false := hb 6 4 (by decide)
    have f25 : (x 2 && y 5) = false := hb 2 5 (by decide)
    have f35 : (x 3 && y 5) = false := hb 3 5 (by decide)
    have f65 : (x 6 && y 5) = false := hb 6 5 (by decide)
    have f26 : (x 2 && y 6) = false := hb 2 6 (by decide)
    have f46 : (x 4 && y 6) = false := hb 4 6 (by decide)
    have f56 : (x 5 && y 6) = false := hb 5 6 (by decide)
    simp only [flagAt, f00, f10, f20, f01, f31, f41, f02, f52, f62, f13, f33, f53, f14, f44, f64, f25, f35, f65, f26, f46, f56, Bool.or_false]
  have h := eval_all (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)
  rw [hf, Bool.false_or, beq_iff_eq] at h
  rw [listOf, h, set12, set12, set05, set45]
  simp only [firstInput, secondInput, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', and_assoc]

end PEqualNP.Outside.L_meta_3053

theorem PEqualNP.Outside.L_meta_3053 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 28] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 32 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ (p l : Fin 7), ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) → PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn (fun a : Fin 7 => decide (a = p)) ++ List.ofFn (fun b : Fin 7 => decide (b = l))) = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (1, 3), (2, 5)] : List (ℕ × ℕ)))) ∧
  (∀ x y : Fin 7 → Bool, (¬ ∃ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn x ++ List.ofFn y) = true ↔ ((∀ i : Fin 7, x i = decide (i ∈ ({1, 2} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({1, 2} : Finset (Fin 7)))) ∨ ((∀ i : Fin 7, x i = decide (i ∈ ({0, 5} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({4, 5} : Finset (Fin 7)))))) := by
  intro C hC
  have hC' : C = PEqualNP.Outside.L_meta_3053.fanoCircuit := hC
  clear hC
  subst hC'
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_3053.fanoCircuit]
  · decide
  · decide +kernel
  · intro x y hno
    apply PEqualNP.Outside.L_meta_3053.freeRows
    intro p l hpl
    by_contra hne
    apply hno
    have ht : (x p && y l) = true := by simpa using hne
    rw [Bool.and_eq_true] at ht
    exact ⟨p, l, hpl, ht.1, ht.2⟩
