import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3053

def Cc : PEqualNP.CircuitLowerBounds.Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 28] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit)

def Q (x y : Fin 7 → Bool) : Prop := (¬ ∃ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.Outside.L_meta_3053.Cc (List.ofFn x ++ List.ofFn y) = true ↔ ((∀ i : Fin 7, x i = decide (i ∈ ({1, 2} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({1, 2} : Finset (Fin 7)))) ∨ ((∀ i : Fin 7, x i = decide (i ∈ ({0, 5} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({4, 5} : Finset (Fin 7)))))

def hf (x y : Fin 7 → Bool) : Bool := x 0 && y 0 || x 1 && y 0 || x 2 && y 0 || x 0 && y 1 || x 3 && y 1 || x 4 && y 1 || x 0 && y 2 || x 5 && y 2 || x 6 && y 2 || x 1 && y 3 || x 3 && y 3 || x 5 && y 3 || x 1 && y 4 || x 4 && y 4 || x 6 && y 4 || x 2 && y 5 || x 3 && y 5 || x 6 && y 5 || x 2 && y 6 || x 4 && y 6 || x 5 && y 6

theorem hf_of (x y : Fin 7 → Bool) (h : hf x y = true) : ∃ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true := by
  by_contra hn
  have e : ∀ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) → (x p && y l) = false := by
    intro p l hm
    cases hx : x p <;> cases hy : y l
    · rfl
    · rfl
    · rfl
    · exact absurd ⟨p, l, hm, hx, hy⟩ hn
  simp only [hf, e 0 0 (by decide), e 1 0 (by decide), e 2 0 (by decide), e 0 1 (by decide), e 3 1 (by decide), e 4 1 (by decide), e 0 2 (by decide), e 5 2 (by decide), e 6 2 (by decide), e 1 3 (by decide), e 3 3 (by decide), e 5 3 (by decide), e 1 4 (by decide), e 4 4 (by decide), e 6 4 (by decide), e 2 5 (by decide), e 3 5 (by decide), e 6 5 (by decide), e 2 6 (by decide), e 4 6 (by decide), e 5 6 (by decide)] at h
  simp at h



theorem flags : ∀ (p l : Fin 7), ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) → PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.Outside.L_meta_3053.Cc (List.ofFn (fun a : Fin 7 => decide (a = p)) ++ List.ofFn (fun b : Fin 7 => decide (b = l))) = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (1, 3), (2, 5)] : List (ℕ × ℕ))) := by
  decide +kernel

def eqv (x v : Fin 7 → Bool) : Bool := (x 0 == v 0) && (x 1 == v 1) && (x 2 == v 2) && (x 3 == v 3) && (x 4 == v 4) && (x 5 == v 5) && (x 6 == v 6)

theorem eqv_iff (x v : Fin 7 → Bool) : eqv x v = true ↔ ∀ i, x i = v i := by
  constructor
  · intro h i
    simp only [eqv, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
  · intro h
    simp only [eqv, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩, h 4⟩, h 5⟩, h 6⟩

def chk (x y : Fin 7 → Bool) : Bool := hf x y || (Cc.eval (List.ofFn x ++ List.ofFn y) == (eqv x ![false, true, true, false, false, false, false] && eqv y ![false, true, true, false, false, false, false] || eqv x ![true, false, false, false, false, true, false] && eqv y ![false, false, false, false, true, true, false]))

theorem k0000000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, false, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0000001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, false, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0000010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, false, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0000011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, false, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0000100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, false, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0000101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, false, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0000110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, false, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0000111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, false, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0001000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, true, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0001001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, true, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0001010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, true, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0001011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, true, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0001100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, true, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0001101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, true, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0001110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, true, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0001111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, false, true, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0010000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, false, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0010001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, false, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0010010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, false, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0010011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, false, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0010100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, false, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0010101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, false, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0010110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, false, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0010111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, false, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0011000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, true, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0011001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, true, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0011010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, true, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0011011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, true, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0011100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, true, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0011101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, true, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0011110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, true, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0011111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, false, true, true, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0100000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, false, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0100001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, false, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0100010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, false, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0100011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, false, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0100100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, false, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0100101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, false, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0100110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, false, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0100111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, false, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0101000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, true, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0101001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, true, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0101010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, true, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0101011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, true, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0101100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, true, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0101101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, true, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0101110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, true, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0101111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, false, true, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0110000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, false, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0110001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, false, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0110010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, false, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0110011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, false, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0110100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, false, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0110101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, false, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0110110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, false, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0110111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, false, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0111000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, true, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0111001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, true, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0111010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, true, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0111011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, true, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0111100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, true, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0111101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, true, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0111110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, true, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k0111111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![false, true, true, true, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1000000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, false, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1000001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, false, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1000010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, false, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1000011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, false, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1000100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, false, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1000101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, false, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1000110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, false, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1000111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, false, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1001000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, true, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1001001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, true, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1001010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, true, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1001011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, true, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1001100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, true, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1001101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, true, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1001110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, true, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1001111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, false, true, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1010000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, false, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1010001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, false, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1010010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, false, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1010011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, false, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1010100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, false, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1010101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, false, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1010110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, false, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1010111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, false, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1011000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, true, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1011001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, true, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1011010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, true, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1011011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, true, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1011100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, true, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1011101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, true, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1011110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, true, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1011111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, false, true, true, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1100000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, false, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1100001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, false, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1100010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, false, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1100011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, false, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1100100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, false, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1100101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, false, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1100110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, false, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1100111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, false, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1101000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, true, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1101001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, true, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1101010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, true, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1101011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, true, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1101100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, true, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1101101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, true, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1101110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, true, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1101111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, false, true, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1110000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, false, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1110001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, false, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1110010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, false, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1110011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, false, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1110100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, false, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1110101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, false, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1110110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, false, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1110111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, false, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1111000 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, true, false, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1111001 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, true, false, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1111010 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, true, false, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1111011 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, true, false, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1111100 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, true, true, false, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1111101 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, true, true, false, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1111110 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, true, true, true, false] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem k1111111 : ∀ c0 c1 c2 c3 c4 c5 c6 : Bool, chk ![true, true, true, true, true, true, true] ![c0, c1, c2, c3, c4, c5, c6] = true := by
  decide +kernel

theorem key (x y : Fin 7 → Bool) : Q x y := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    funext i
    fin_cases i <;> rfl
  have hy : y = ![y 0, y 1, y 2, y 3, y 4, y 5, y 6] := by
    funext i
    fin_cases i <;> rfl
  have hc : chk x y = true := by
    rw [hx, hy]
    generalize x 0 = a0
    generalize x 1 = a1
    generalize x 2 = a2
    generalize x 3 = a3
    generalize x 4 = a4
    generalize x 5 = a5
    generalize x 6 = a6
    cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6
    · exact k0000000 _ _ _ _ _ _ _
    · exact k0000001 _ _ _ _ _ _ _
    · exact k0000010 _ _ _ _ _ _ _
    · exact k0000011 _ _ _ _ _ _ _
    · exact k0000100 _ _ _ _ _ _ _
    · exact k0000101 _ _ _ _ _ _ _
    · exact k0000110 _ _ _ _ _ _ _
    · exact k0000111 _ _ _ _ _ _ _
    · exact k0001000 _ _ _ _ _ _ _
    · exact k0001001 _ _ _ _ _ _ _
    · exact k0001010 _ _ _ _ _ _ _
    · exact k0001011 _ _ _ _ _ _ _
    · exact k0001100 _ _ _ _ _ _ _
    · exact k0001101 _ _ _ _ _ _ _
    · exact k0001110 _ _ _ _ _ _ _
    · exact k0001111 _ _ _ _ _ _ _
    · exact k0010000 _ _ _ _ _ _ _
    · exact k0010001 _ _ _ _ _ _ _
    · exact k0010010 _ _ _ _ _ _ _
    · exact k0010011 _ _ _ _ _ _ _
    · exact k0010100 _ _ _ _ _ _ _
    · exact k0010101 _ _ _ _ _ _ _
    · exact k0010110 _ _ _ _ _ _ _
    · exact k0010111 _ _ _ _ _ _ _
    · exact k0011000 _ _ _ _ _ _ _
    · exact k0011001 _ _ _ _ _ _ _
    · exact k0011010 _ _ _ _ _ _ _
    · exact k0011011 _ _ _ _ _ _ _
    · exact k0011100 _ _ _ _ _ _ _
    · exact k0011101 _ _ _ _ _ _ _
    · exact k0011110 _ _ _ _ _ _ _
    · exact k0011111 _ _ _ _ _ _ _
    · exact k0100000 _ _ _ _ _ _ _
    · exact k0100001 _ _ _ _ _ _ _
    · exact k0100010 _ _ _ _ _ _ _
    · exact k0100011 _ _ _ _ _ _ _
    · exact k0100100 _ _ _ _ _ _ _
    · exact k0100101 _ _ _ _ _ _ _
    · exact k0100110 _ _ _ _ _ _ _
    · exact k0100111 _ _ _ _ _ _ _
    · exact k0101000 _ _ _ _ _ _ _
    · exact k0101001 _ _ _ _ _ _ _
    · exact k0101010 _ _ _ _ _ _ _
    · exact k0101011 _ _ _ _ _ _ _
    · exact k0101100 _ _ _ _ _ _ _
    · exact k0101101 _ _ _ _ _ _ _
    · exact k0101110 _ _ _ _ _ _ _
    · exact k0101111 _ _ _ _ _ _ _
    · exact k0110000 _ _ _ _ _ _ _
    · exact k0110001 _ _ _ _ _ _ _
    · exact k0110010 _ _ _ _ _ _ _
    · exact k0110011 _ _ _ _ _ _ _
    · exact k0110100 _ _ _ _ _ _ _
    · exact k0110101 _ _ _ _ _ _ _
    · exact k0110110 _ _ _ _ _ _ _
    · exact k0110111 _ _ _ _ _ _ _
    · exact k0111000 _ _ _ _ _ _ _
    · exact k0111001 _ _ _ _ _ _ _
    · exact k0111010 _ _ _ _ _ _ _
    · exact k0111011 _ _ _ _ _ _ _
    · exact k0111100 _ _ _ _ _ _ _
    · exact k0111101 _ _ _ _ _ _ _
    · exact k0111110 _ _ _ _ _ _ _
    · exact k0111111 _ _ _ _ _ _ _
    · exact k1000000 _ _ _ _ _ _ _
    · exact k1000001 _ _ _ _ _ _ _
    · exact k1000010 _ _ _ _ _ _ _
    · exact k1000011 _ _ _ _ _ _ _
    · exact k1000100 _ _ _ _ _ _ _
    · exact k1000101 _ _ _ _ _ _ _
    · exact k1000110 _ _ _ _ _ _ _
    · exact k1000111 _ _ _ _ _ _ _
    · exact k1001000 _ _ _ _ _ _ _
    · exact k1001001 _ _ _ _ _ _ _
    · exact k1001010 _ _ _ _ _ _ _
    · exact k1001011 _ _ _ _ _ _ _
    · exact k1001100 _ _ _ _ _ _ _
    · exact k1001101 _ _ _ _ _ _ _
    · exact k1001110 _ _ _ _ _ _ _
    · exact k1001111 _ _ _ _ _ _ _
    · exact k1010000 _ _ _ _ _ _ _
    · exact k1010001 _ _ _ _ _ _ _
    · exact k1010010 _ _ _ _ _ _ _
    · exact k1010011 _ _ _ _ _ _ _
    · exact k1010100 _ _ _ _ _ _ _
    · exact k1010101 _ _ _ _ _ _ _
    · exact k1010110 _ _ _ _ _ _ _
    · exact k1010111 _ _ _ _ _ _ _
    · exact k1011000 _ _ _ _ _ _ _
    · exact k1011001 _ _ _ _ _ _ _
    · exact k1011010 _ _ _ _ _ _ _
    · exact k1011011 _ _ _ _ _ _ _
    · exact k1011100 _ _ _ _ _ _ _
    · exact k1011101 _ _ _ _ _ _ _
    · exact k1011110 _ _ _ _ _ _ _
    · exact k1011111 _ _ _ _ _ _ _
    · exact k1100000 _ _ _ _ _ _ _
    · exact k1100001 _ _ _ _ _ _ _
    · exact k1100010 _ _ _ _ _ _ _
    · exact k1100011 _ _ _ _ _ _ _
    · exact k1100100 _ _ _ _ _ _ _
    · exact k1100101 _ _ _ _ _ _ _
    · exact k1100110 _ _ _ _ _ _ _
    · exact k1100111 _ _ _ _ _ _ _
    · exact k1101000 _ _ _ _ _ _ _
    · exact k1101001 _ _ _ _ _ _ _
    · exact k1101010 _ _ _ _ _ _ _
    · exact k1101011 _ _ _ _ _ _ _
    · exact k1101100 _ _ _ _ _ _ _
    · exact k1101101 _ _ _ _ _ _ _
    · exact k1101110 _ _ _ _ _ _ _
    · exact k1101111 _ _ _ _ _ _ _
    · exact k1110000 _ _ _ _ _ _ _
    · exact k1110001 _ _ _ _ _ _ _
    · exact k1110010 _ _ _ _ _ _ _
    · exact k1110011 _ _ _ _ _ _ _
    · exact k1110100 _ _ _ _ _ _ _
    · exact k1110101 _ _ _ _ _ _ _
    · exact k1110110 _ _ _ _ _ _ _
    · exact k1110111 _ _ _ _ _ _ _
    · exact k1111000 _ _ _ _ _ _ _
    · exact k1111001 _ _ _ _ _ _ _
    · exact k1111010 _ _ _ _ _ _ _
    · exact k1111011 _ _ _ _ _ _ _
    · exact k1111100 _ _ _ _ _ _ _
    · exact k1111101 _ _ _ _ _ _ _
    · exact k1111110 _ _ _ _ _ _ _
    · exact k1111111 _ _ _ _ _ _ _
  intro hn
  have hfx : hf x y = false := by
    cases hb : hf x y
    · rfl
    · exact absurd (hf_of x y hb) hn
  simp only [chk, hfx, Bool.false_or, beq_iff_eq] at hc
  rw [hc]
  have e1 : ∀ (z v : Fin 7 → Bool), eqv z v = true ↔ ∀ i, z i = v i := eqv_iff
  simp only [Bool.or_eq_true, Bool.and_eq_true, e1]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      exact ⟨fun i => by rw [h1 i]; fin_cases i <;> rfl, fun i => by rw [h2 i]; fin_cases i <;> rfl⟩
    · right
      exact ⟨fun i => by rw [h1 i]; fin_cases i <;> rfl, fun i => by rw [h2 i]; fin_cases i <;> rfl⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      exact ⟨fun i => by rw [h1 i]; fin_cases i <;> rfl, fun i => by rw [h2 i]; fin_cases i <;> rfl⟩
    · right
      exact ⟨fun i => by rw [h1 i]; fin_cases i <;> rfl, fun i => by rw [h2 i]; fin_cases i <;> rfl⟩

end PEqualNP.Outside.L_meta_3053

theorem PEqualNP.Outside.L_meta_3053 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 28] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 32 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ (p l : Fin 7), ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) → PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn (fun a : Fin 7 => decide (a = p)) ++ List.ofFn (fun b : Fin 7 => decide (b = l))) = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (1, 3), (2, 5)] : List (ℕ × ℕ)))) ∧
  (∀ x y : Fin 7 → Bool, (¬ ∃ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn x ++ List.ofFn y) = true ↔ ((∀ i : Fin 7, x i = decide (i ∈ ({1, 2} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({1, 2} : Finset (Fin 7)))) ∨ ((∀ i : Fin 7, x i = decide (i ∈ ({0, 5} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({4, 5} : Finset (Fin 7)))))) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_, PEqualNP.Outside.L_meta_3053.flags, fun x y => PEqualNP.Outside.L_meta_3053.key x y⟩
  · unfold PEqualNP.MetaComplexity.Monotone2
    simp
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
    decide
