import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5396

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_last (w : List Bool) (v : Bool) :
    (w ++ [v]).getD w.length false = v := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp [List.getD]

lemma getD_earlier (w : List Bool) (v : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  induction w generalizing i with
  | nil => cases hi
  | cons a w ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp [List.getD, List.getElem?_cons_succ]
          exact ih i (Nat.lt_of_succ_lt_succ hi)

lemma getD_at {w : List Bool} {v : Bool} {i : ℕ} (hi : w.length = i) :
    (w ++ [v]).getD i false = v :=
  hi ▸ getD_last w v

lemma map_two (w : List Bool) (a b : ℕ) :
    ([a, b].map fun i => w.getD i false) = [w.getD a false, w.getD b false] := by
  simp

lemma or_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  simp [GateOp.eval]

lemma and_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  simp [GateOp.eval]

def L0 (x : Fin 16 → Bool) : List Bool := List.ofFn x

def L1 (x : Fin 16 → Bool) : List Bool := step (L0 x) ⟨GateOp.or, [1, 2]⟩

def L2 (x : Fin 16 → Bool) : List Bool := step (L1 x) ⟨GateOp.or, [0, 3]⟩

def L3 (x : Fin 16 → Bool) : List Bool := step (L2 x) ⟨GateOp.and, [16, 17]⟩

def L4 (x : Fin 16 → Bool) : List Bool := step (L3 x) ⟨GateOp.or, [4, 18]⟩

def L5 (x : Fin 16 → Bool) : List Bool := step (L4 x) ⟨GateOp.or, [0, 5]⟩

def L6 (x : Fin 16 → Bool) : List Bool := step (L5 x) ⟨GateOp.and, [19, 20]⟩

def L7 (x : Fin 16 → Bool) : List Bool := step (L6 x) ⟨GateOp.or, [6, 18]⟩

def L8 (x : Fin 16 → Bool) : List Bool := step (L7 x) ⟨GateOp.or, [2, 7]⟩

def L9 (x : Fin 16 → Bool) : List Bool := step (L8 x) ⟨GateOp.and, [22, 23]⟩

def L10 (x : Fin 16 → Bool) : List Bool := step (L9 x) ⟨GateOp.or, [8, 18]⟩

def L11 (x : Fin 16 → Bool) : List Bool := step (L10 x) ⟨GateOp.or, [12, 21]⟩

def L12 (x : Fin 16 → Bool) : List Bool := step (L11 x) ⟨GateOp.and, [25, 26]⟩

def L13 (x : Fin 16 → Bool) : List Bool := step (L12 x) ⟨GateOp.or, [9, 21]⟩

def L14 (x : Fin 16 → Bool) : List Bool := step (L13 x) ⟨GateOp.or, [5, 13]⟩

def L15 (x : Fin 16 → Bool) : List Bool := step (L14 x) ⟨GateOp.and, [28, 29]⟩

def L16 (x : Fin 16 → Bool) : List Bool := step (L15 x) ⟨GateOp.or, [10, 18]⟩

def L17 (x : Fin 16 → Bool) : List Bool := step (L16 x) ⟨GateOp.or, [14, 24]⟩

def L18 (x : Fin 16 → Bool) : List Bool := step (L17 x) ⟨GateOp.and, [31, 32]⟩

def L19 (x : Fin 16 → Bool) : List Bool := step (L18 x) ⟨GateOp.or, [11, 24]⟩

def L20 (x : Fin 16 → Bool) : List Bool := step (L19 x) ⟨GateOp.or, [7, 15]⟩

def L21 (x : Fin 16 → Bool) : List Bool := step (L20 x) ⟨GateOp.and, [34, 35]⟩

def L22 (x : Fin 16 → Bool) : List Bool := step (L21 x) ⟨GateOp.or, [27, 30]⟩

def L23 (x : Fin 16 → Bool) : List Bool := step (L22 x) ⟨GateOp.or, [33, 37]⟩

def L24 (x : Fin 16 → Bool) : List Bool := step (L23 x) ⟨GateOp.or, [36, 38]⟩

lemma len0 (x : Fin 16 → Bool) : (L0 x).length = 16 := by
  simp [L0]

lemma len1 (x : Fin 16 → Bool) : (L1 x).length = 17 := by
  simp [L1, step, len0]

lemma len2 (x : Fin 16 → Bool) : (L2 x).length = 18 := by
  simp [L2, step, len1]

lemma len3 (x : Fin 16 → Bool) : (L3 x).length = 19 := by
  simp [L3, step, len2]

lemma len4 (x : Fin 16 → Bool) : (L4 x).length = 20 := by
  simp [L4, step, len3]

lemma len5 (x : Fin 16 → Bool) : (L5 x).length = 21 := by
  simp [L5, step, len4]

lemma len6 (x : Fin 16 → Bool) : (L6 x).length = 22 := by
  simp [L6, step, len5]

lemma len7 (x : Fin 16 → Bool) : (L7 x).length = 23 := by
  simp [L7, step, len6]

lemma len8 (x : Fin 16 → Bool) : (L8 x).length = 24 := by
  simp [L8, step, len7]

lemma len9 (x : Fin 16 → Bool) : (L9 x).length = 25 := by
  simp [L9, step, len8]

lemma len10 (x : Fin 16 → Bool) : (L10 x).length = 26 := by
  simp [L10, step, len9]

lemma len11 (x : Fin 16 → Bool) : (L11 x).length = 27 := by
  simp [L11, step, len10]

lemma len12 (x : Fin 16 → Bool) : (L12 x).length = 28 := by
  simp [L12, step, len11]

lemma len13 (x : Fin 16 → Bool) : (L13 x).length = 29 := by
  simp [L13, step, len12]

lemma len14 (x : Fin 16 → Bool) : (L14 x).length = 30 := by
  simp [L14, step, len13]

lemma len15 (x : Fin 16 → Bool) : (L15 x).length = 31 := by
  simp [L15, step, len14]

lemma len16 (x : Fin 16 → Bool) : (L16 x).length = 32 := by
  simp [L16, step, len15]

lemma len17 (x : Fin 16 → Bool) : (L17 x).length = 33 := by
  simp [L17, step, len16]

lemma len18 (x : Fin 16 → Bool) : (L18 x).length = 34 := by
  simp [L18, step, len17]

lemma len19 (x : Fin 16 → Bool) : (L19 x).length = 35 := by
  simp [L19, step, len18]

lemma len20 (x : Fin 16 → Bool) : (L20 x).length = 36 := by
  simp [L20, step, len19]

lemma len21 (x : Fin 16 → Bool) : (L21 x).length = 37 := by
  simp [L21, step, len20]

lemma len22 (x : Fin 16 → Bool) : (L22 x).length = 38 := by
  simp [L22, step, len21]

lemma len23 (x : Fin 16 → Bool) : (L23 x).length = 39 := by
  simp [L23, step, len22]

lemma len24 (x : Fin 16 → Bool) : (L24 x).length = 40 := by
  simp [L24, step, len23]

lemma keep0 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L0 x).length) :
    (L1 x).getD i false = (L0 x).getD i false := by
  rw [L1, step]
  exact getD_earlier _ _ i hi

lemma keep1 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L1 x).length) :
    (L2 x).getD i false = (L1 x).getD i false := by
  rw [L2, step]
  exact getD_earlier _ _ i hi

lemma keep2 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L2 x).length) :
    (L3 x).getD i false = (L2 x).getD i false := by
  rw [L3, step]
  exact getD_earlier _ _ i hi

lemma keep3 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L3 x).length) :
    (L4 x).getD i false = (L3 x).getD i false := by
  rw [L4, step]
  exact getD_earlier _ _ i hi

lemma keep4 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L4 x).length) :
    (L5 x).getD i false = (L4 x).getD i false := by
  rw [L5, step]
  exact getD_earlier _ _ i hi

lemma keep5 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L5 x).length) :
    (L6 x).getD i false = (L5 x).getD i false := by
  rw [L6, step]
  exact getD_earlier _ _ i hi

lemma keep6 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L6 x).length) :
    (L7 x).getD i false = (L6 x).getD i false := by
  rw [L7, step]
  exact getD_earlier _ _ i hi

lemma keep7 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L7 x).length) :
    (L8 x).getD i false = (L7 x).getD i false := by
  rw [L8, step]
  exact getD_earlier _ _ i hi

lemma keep8 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L8 x).length) :
    (L9 x).getD i false = (L8 x).getD i false := by
  rw [L9, step]
  exact getD_earlier _ _ i hi

lemma keep9 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L9 x).length) :
    (L10 x).getD i false = (L9 x).getD i false := by
  rw [L10, step]
  exact getD_earlier _ _ i hi

lemma keep10 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L10 x).length) :
    (L11 x).getD i false = (L10 x).getD i false := by
  rw [L11, step]
  exact getD_earlier _ _ i hi

lemma keep11 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L11 x).length) :
    (L12 x).getD i false = (L11 x).getD i false := by
  rw [L12, step]
  exact getD_earlier _ _ i hi

lemma keep12 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L12 x).length) :
    (L13 x).getD i false = (L12 x).getD i false := by
  rw [L13, step]
  exact getD_earlier _ _ i hi

lemma keep13 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L13 x).length) :
    (L14 x).getD i false = (L13 x).getD i false := by
  rw [L14, step]
  exact getD_earlier _ _ i hi

lemma keep14 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L14 x).length) :
    (L15 x).getD i false = (L14 x).getD i false := by
  rw [L15, step]
  exact getD_earlier _ _ i hi

lemma keep15 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L15 x).length) :
    (L16 x).getD i false = (L15 x).getD i false := by
  rw [L16, step]
  exact getD_earlier _ _ i hi

lemma keep16 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L16 x).length) :
    (L17 x).getD i false = (L16 x).getD i false := by
  rw [L17, step]
  exact getD_earlier _ _ i hi

lemma keep17 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L17 x).length) :
    (L18 x).getD i false = (L17 x).getD i false := by
  rw [L18, step]
  exact getD_earlier _ _ i hi

lemma keep18 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L18 x).length) :
    (L19 x).getD i false = (L18 x).getD i false := by
  rw [L19, step]
  exact getD_earlier _ _ i hi

lemma keep19 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L19 x).length) :
    (L20 x).getD i false = (L19 x).getD i false := by
  rw [L20, step]
  exact getD_earlier _ _ i hi

lemma keep20 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L20 x).length) :
    (L21 x).getD i false = (L20 x).getD i false := by
  rw [L21, step]
  exact getD_earlier _ _ i hi

lemma keep21 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L21 x).length) :
    (L22 x).getD i false = (L21 x).getD i false := by
  rw [L22, step]
  exact getD_earlier _ _ i hi

lemma keep22 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L22 x).length) :
    (L23 x).getD i false = (L22 x).getD i false := by
  rw [L23, step]
  exact getD_earlier _ _ i hi

lemma keep23 (x : Fin 16 → Bool) (i : ℕ) (hi : i < (L23 x).length) :
    (L24 x).getD i false = (L23 x).getD i false := by
  rw [L24, step]
  exact getD_earlier _ _ i hi

lemma w0 (x : Fin 16 → Bool) : (L1 x).getD 16 false = ((x 1) || (x 2)) := by
  have hlen := len0 x
  rw [L1, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L0 x).getD 1 false = x 1 by
    simp [L0]]
  rw [show (L0 x).getD 2 false = x 2 by
    simp [L0]]

lemma w1 (x : Fin 16 → Bool) : (L2 x).getD 17 false = ((x 0) || (x 3)) := by
  have hlen := len1 x
  rw [L2, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L1 x).getD 0 false = x 0 by
    rw [keep0 x 0 (by rw [len0]; decide)]
    simp [L0]]
  rw [show (L1 x).getD 3 false = x 3 by
    rw [keep0 x 3 (by rw [len0]; decide)]
    simp [L0]]

lemma w2 (x : Fin 16 → Bool) : (L3 x).getD 18 false = (((x 1) || (x 2)) && ((x 0) || (x 3))) := by
  have hlen := len2 x
  rw [L3, step]
  rw [getD_at hlen]
  rw [map_two, and_two]
  rw [keep1 x 16 (by rw [len1]; decide)]
  rw [w0]
  rw [w1]

lemma w3 (x : Fin 16 → Bool) : (L4 x).getD 19 false = ((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) := by
  have hlen := len3 x
  rw [L4, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L3 x).getD 4 false = x 4 by
    rw [keep2 x 4 (by rw [len2]; decide), keep1 x 4 (by rw [len1]; decide), keep0 x 4 (by rw [len0]; decide)]
    simp [L0]]
  rw [w2]

lemma w4 (x : Fin 16 → Bool) : (L5 x).getD 20 false = ((x 0) || (x 5)) := by
  have hlen := len4 x
  rw [L5, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L4 x).getD 0 false = x 0 by
    rw [keep3 x 0 (by rw [len3]; decide), keep2 x 0 (by rw [len2]; decide), keep1 x 0 (by rw [len1]; decide), keep0 x 0 (by rw [len0]; decide)]
    simp [L0]]
  rw [show (L4 x).getD 5 false = x 5 by
    rw [keep3 x 5 (by rw [len3]; decide), keep2 x 5 (by rw [len2]; decide), keep1 x 5 (by rw [len1]; decide), keep0 x 5 (by rw [len0]; decide)]
    simp [L0]]

lemma w5 (x : Fin 16 → Bool) : (L6 x).getD 21 false = (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5))) := by
  have hlen := len5 x
  rw [L6, step]
  rw [getD_at hlen]
  rw [map_two, and_two]
  rw [keep4 x 19 (by rw [len4]; decide)]
  rw [w3]
  rw [w4]

lemma w6 (x : Fin 16 → Bool) : (L7 x).getD 22 false = ((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) := by
  have hlen := len6 x
  rw [L7, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L6 x).getD 6 false = x 6 by
    rw [keep5 x 6 (by rw [len5]; decide), keep4 x 6 (by rw [len4]; decide), keep3 x 6 (by rw [len3]; decide), keep2 x 6 (by rw [len2]; decide), keep1 x 6 (by rw [len1]; decide), keep0 x 6 (by rw [len0]; decide)]
    simp [L0]]
  rw [keep5 x 18 (by rw [len5]; decide), keep4 x 18 (by rw [len4]; decide), keep3 x 18 (by rw [len3]; decide)]
  rw [w2]

lemma w7 (x : Fin 16 → Bool) : (L8 x).getD 23 false = ((x 2) || (x 7)) := by
  have hlen := len7 x
  rw [L8, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L7 x).getD 2 false = x 2 by
    rw [keep6 x 2 (by rw [len6]; decide), keep5 x 2 (by rw [len5]; decide), keep4 x 2 (by rw [len4]; decide), keep3 x 2 (by rw [len3]; decide), keep2 x 2 (by rw [len2]; decide), keep1 x 2 (by rw [len1]; decide), keep0 x 2 (by rw [len0]; decide)]
    simp [L0]]
  rw [show (L7 x).getD 7 false = x 7 by
    rw [keep6 x 7 (by rw [len6]; decide), keep5 x 7 (by rw [len5]; decide), keep4 x 7 (by rw [len4]; decide), keep3 x 7 (by rw [len3]; decide), keep2 x 7 (by rw [len2]; decide), keep1 x 7 (by rw [len1]; decide), keep0 x 7 (by rw [len0]; decide)]
    simp [L0]]

lemma w8 (x : Fin 16 → Bool) : (L9 x).getD 24 false = (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7))) := by
  have hlen := len8 x
  rw [L9, step]
  rw [getD_at hlen]
  rw [map_two, and_two]
  rw [keep7 x 22 (by rw [len7]; decide)]
  rw [w6]
  rw [w7]

lemma w9 (x : Fin 16 → Bool) : (L10 x).getD 25 false = ((x 8) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) := by
  have hlen := len9 x
  rw [L10, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L9 x).getD 8 false = x 8 by
    rw [keep8 x 8 (by rw [len8]; decide), keep7 x 8 (by rw [len7]; decide), keep6 x 8 (by rw [len6]; decide), keep5 x 8 (by rw [len5]; decide), keep4 x 8 (by rw [len4]; decide), keep3 x 8 (by rw [len3]; decide), keep2 x 8 (by rw [len2]; decide), keep1 x 8 (by rw [len1]; decide), keep0 x 8 (by rw [len0]; decide)]
    simp [L0]]
  rw [keep8 x 18 (by rw [len8]; decide), keep7 x 18 (by rw [len7]; decide), keep6 x 18 (by rw [len6]; decide), keep5 x 18 (by rw [len5]; decide), keep4 x 18 (by rw [len4]; decide), keep3 x 18 (by rw [len3]; decide)]
  rw [w2]

lemma w10 (x : Fin 16 → Bool) : (L11 x).getD 26 false = ((x 12) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5)))) := by
  have hlen := len10 x
  rw [L11, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L10 x).getD 12 false = x 12 by
    rw [keep9 x 12 (by rw [len9]; decide), keep8 x 12 (by rw [len8]; decide), keep7 x 12 (by rw [len7]; decide), keep6 x 12 (by rw [len6]; decide), keep5 x 12 (by rw [len5]; decide), keep4 x 12 (by rw [len4]; decide), keep3 x 12 (by rw [len3]; decide), keep2 x 12 (by rw [len2]; decide), keep1 x 12 (by rw [len1]; decide), keep0 x 12 (by rw [len0]; decide)]
    simp [L0]]
  rw [keep9 x 21 (by rw [len9]; decide), keep8 x 21 (by rw [len8]; decide), keep7 x 21 (by rw [len7]; decide), keep6 x 21 (by rw [len6]; decide)]
  rw [w5]

lemma w11 (x : Fin 16 → Bool) : (L12 x).getD 27 false = (((x 8) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 12) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5))))) := by
  have hlen := len11 x
  rw [L12, step]
  rw [getD_at hlen]
  rw [map_two, and_two]
  rw [keep10 x 25 (by rw [len10]; decide)]
  rw [w9]
  rw [w10]

lemma w12 (x : Fin 16 → Bool) : (L13 x).getD 28 false = ((x 9) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5)))) := by
  have hlen := len12 x
  rw [L13, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L12 x).getD 9 false = x 9 by
    rw [keep11 x 9 (by rw [len11]; decide), keep10 x 9 (by rw [len10]; decide), keep9 x 9 (by rw [len9]; decide), keep8 x 9 (by rw [len8]; decide), keep7 x 9 (by rw [len7]; decide), keep6 x 9 (by rw [len6]; decide), keep5 x 9 (by rw [len5]; decide), keep4 x 9 (by rw [len4]; decide), keep3 x 9 (by rw [len3]; decide), keep2 x 9 (by rw [len2]; decide), keep1 x 9 (by rw [len1]; decide), keep0 x 9 (by rw [len0]; decide)]
    simp [L0]]
  rw [keep11 x 21 (by rw [len11]; decide), keep10 x 21 (by rw [len10]; decide), keep9 x 21 (by rw [len9]; decide), keep8 x 21 (by rw [len8]; decide), keep7 x 21 (by rw [len7]; decide), keep6 x 21 (by rw [len6]; decide)]
  rw [w5]

lemma w13 (x : Fin 16 → Bool) : (L14 x).getD 29 false = ((x 5) || (x 13)) := by
  have hlen := len13 x
  rw [L14, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L13 x).getD 5 false = x 5 by
    rw [keep12 x 5 (by rw [len12]; decide), keep11 x 5 (by rw [len11]; decide), keep10 x 5 (by rw [len10]; decide), keep9 x 5 (by rw [len9]; decide), keep8 x 5 (by rw [len8]; decide), keep7 x 5 (by rw [len7]; decide), keep6 x 5 (by rw [len6]; decide), keep5 x 5 (by rw [len5]; decide), keep4 x 5 (by rw [len4]; decide), keep3 x 5 (by rw [len3]; decide), keep2 x 5 (by rw [len2]; decide), keep1 x 5 (by rw [len1]; decide), keep0 x 5 (by rw [len0]; decide)]
    simp [L0]]
  rw [show (L13 x).getD 13 false = x 13 by
    rw [keep12 x 13 (by rw [len12]; decide), keep11 x 13 (by rw [len11]; decide), keep10 x 13 (by rw [len10]; decide), keep9 x 13 (by rw [len9]; decide), keep8 x 13 (by rw [len8]; decide), keep7 x 13 (by rw [len7]; decide), keep6 x 13 (by rw [len6]; decide), keep5 x 13 (by rw [len5]; decide), keep4 x 13 (by rw [len4]; decide), keep3 x 13 (by rw [len3]; decide), keep2 x 13 (by rw [len2]; decide), keep1 x 13 (by rw [len1]; decide), keep0 x 13 (by rw [len0]; decide)]
    simp [L0]]

lemma w14 (x : Fin 16 → Bool) : (L15 x).getD 30 false = (((x 9) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5)))) && ((x 5) || (x 13))) := by
  have hlen := len14 x
  rw [L15, step]
  rw [getD_at hlen]
  rw [map_two, and_two]
  rw [keep13 x 28 (by rw [len13]; decide)]
  rw [w12]
  rw [w13]

lemma w15 (x : Fin 16 → Bool) : (L16 x).getD 31 false = ((x 10) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) := by
  have hlen := len15 x
  rw [L16, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L15 x).getD 10 false = x 10 by
    rw [keep14 x 10 (by rw [len14]; decide), keep13 x 10 (by rw [len13]; decide), keep12 x 10 (by rw [len12]; decide), keep11 x 10 (by rw [len11]; decide), keep10 x 10 (by rw [len10]; decide), keep9 x 10 (by rw [len9]; decide), keep8 x 10 (by rw [len8]; decide), keep7 x 10 (by rw [len7]; decide), keep6 x 10 (by rw [len6]; decide), keep5 x 10 (by rw [len5]; decide), keep4 x 10 (by rw [len4]; decide), keep3 x 10 (by rw [len3]; decide), keep2 x 10 (by rw [len2]; decide), keep1 x 10 (by rw [len1]; decide), keep0 x 10 (by rw [len0]; decide)]
    simp [L0]]
  rw [keep14 x 18 (by rw [len14]; decide), keep13 x 18 (by rw [len13]; decide), keep12 x 18 (by rw [len12]; decide), keep11 x 18 (by rw [len11]; decide), keep10 x 18 (by rw [len10]; decide), keep9 x 18 (by rw [len9]; decide), keep8 x 18 (by rw [len8]; decide), keep7 x 18 (by rw [len7]; decide), keep6 x 18 (by rw [len6]; decide), keep5 x 18 (by rw [len5]; decide), keep4 x 18 (by rw [len4]; decide), keep3 x 18 (by rw [len3]; decide)]
  rw [w2]

lemma w16 (x : Fin 16 → Bool) : (L17 x).getD 32 false = ((x 14) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7)))) := by
  have hlen := len16 x
  rw [L17, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L16 x).getD 14 false = x 14 by
    rw [keep15 x 14 (by rw [len15]; decide), keep14 x 14 (by rw [len14]; decide), keep13 x 14 (by rw [len13]; decide), keep12 x 14 (by rw [len12]; decide), keep11 x 14 (by rw [len11]; decide), keep10 x 14 (by rw [len10]; decide), keep9 x 14 (by rw [len9]; decide), keep8 x 14 (by rw [len8]; decide), keep7 x 14 (by rw [len7]; decide), keep6 x 14 (by rw [len6]; decide), keep5 x 14 (by rw [len5]; decide), keep4 x 14 (by rw [len4]; decide), keep3 x 14 (by rw [len3]; decide), keep2 x 14 (by rw [len2]; decide), keep1 x 14 (by rw [len1]; decide), keep0 x 14 (by rw [len0]; decide)]
    simp [L0]]
  rw [keep15 x 24 (by rw [len15]; decide), keep14 x 24 (by rw [len14]; decide), keep13 x 24 (by rw [len13]; decide), keep12 x 24 (by rw [len12]; decide), keep11 x 24 (by rw [len11]; decide), keep10 x 24 (by rw [len10]; decide), keep9 x 24 (by rw [len9]; decide)]
  rw [w8]

lemma w17 (x : Fin 16 → Bool) : (L18 x).getD 33 false = (((x 10) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 14) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7))))) := by
  have hlen := len17 x
  rw [L18, step]
  rw [getD_at hlen]
  rw [map_two, and_two]
  rw [keep16 x 31 (by rw [len16]; decide)]
  rw [w15]
  rw [w16]

lemma w18 (x : Fin 16 → Bool) : (L19 x).getD 34 false = ((x 11) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7)))) := by
  have hlen := len18 x
  rw [L19, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L18 x).getD 11 false = x 11 by
    rw [keep17 x 11 (by rw [len17]; decide), keep16 x 11 (by rw [len16]; decide), keep15 x 11 (by rw [len15]; decide), keep14 x 11 (by rw [len14]; decide), keep13 x 11 (by rw [len13]; decide), keep12 x 11 (by rw [len12]; decide), keep11 x 11 (by rw [len11]; decide), keep10 x 11 (by rw [len10]; decide), keep9 x 11 (by rw [len9]; decide), keep8 x 11 (by rw [len8]; decide), keep7 x 11 (by rw [len7]; decide), keep6 x 11 (by rw [len6]; decide), keep5 x 11 (by rw [len5]; decide), keep4 x 11 (by rw [len4]; decide), keep3 x 11 (by rw [len3]; decide), keep2 x 11 (by rw [len2]; decide), keep1 x 11 (by rw [len1]; decide), keep0 x 11 (by rw [len0]; decide)]
    simp [L0]]
  rw [keep17 x 24 (by rw [len17]; decide), keep16 x 24 (by rw [len16]; decide), keep15 x 24 (by rw [len15]; decide), keep14 x 24 (by rw [len14]; decide), keep13 x 24 (by rw [len13]; decide), keep12 x 24 (by rw [len12]; decide), keep11 x 24 (by rw [len11]; decide), keep10 x 24 (by rw [len10]; decide), keep9 x 24 (by rw [len9]; decide)]
  rw [w8]

lemma w19 (x : Fin 16 → Bool) : (L20 x).getD 35 false = ((x 7) || (x 15)) := by
  have hlen := len19 x
  rw [L20, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [show (L19 x).getD 7 false = x 7 by
    rw [keep18 x 7 (by rw [len18]; decide), keep17 x 7 (by rw [len17]; decide), keep16 x 7 (by rw [len16]; decide), keep15 x 7 (by rw [len15]; decide), keep14 x 7 (by rw [len14]; decide), keep13 x 7 (by rw [len13]; decide), keep12 x 7 (by rw [len12]; decide), keep11 x 7 (by rw [len11]; decide), keep10 x 7 (by rw [len10]; decide), keep9 x 7 (by rw [len9]; decide), keep8 x 7 (by rw [len8]; decide), keep7 x 7 (by rw [len7]; decide), keep6 x 7 (by rw [len6]; decide), keep5 x 7 (by rw [len5]; decide), keep4 x 7 (by rw [len4]; decide), keep3 x 7 (by rw [len3]; decide), keep2 x 7 (by rw [len2]; decide), keep1 x 7 (by rw [len1]; decide), keep0 x 7 (by rw [len0]; decide)]
    simp [L0]]
  rw [show (L19 x).getD 15 false = x 15 by
    rw [keep18 x 15 (by rw [len18]; decide), keep17 x 15 (by rw [len17]; decide), keep16 x 15 (by rw [len16]; decide), keep15 x 15 (by rw [len15]; decide), keep14 x 15 (by rw [len14]; decide), keep13 x 15 (by rw [len13]; decide), keep12 x 15 (by rw [len12]; decide), keep11 x 15 (by rw [len11]; decide), keep10 x 15 (by rw [len10]; decide), keep9 x 15 (by rw [len9]; decide), keep8 x 15 (by rw [len8]; decide), keep7 x 15 (by rw [len7]; decide), keep6 x 15 (by rw [len6]; decide), keep5 x 15 (by rw [len5]; decide), keep4 x 15 (by rw [len4]; decide), keep3 x 15 (by rw [len3]; decide), keep2 x 15 (by rw [len2]; decide), keep1 x 15 (by rw [len1]; decide), keep0 x 15 (by rw [len0]; decide)]
    simp [L0]]

lemma w20 (x : Fin 16 → Bool) : (L21 x).getD 36 false = (((x 11) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7)))) && ((x 7) || (x 15))) := by
  have hlen := len20 x
  rw [L21, step]
  rw [getD_at hlen]
  rw [map_two, and_two]
  rw [keep19 x 34 (by rw [len19]; decide)]
  rw [w18]
  rw [w19]

lemma w21 (x : Fin 16 → Bool) : (L22 x).getD 37 false = ((((x 8) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 12) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5))))) || (((x 9) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5)))) && ((x 5) || (x 13)))) := by
  have hlen := len21 x
  rw [L22, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [keep20 x 27 (by rw [len20]; decide), keep19 x 27 (by rw [len19]; decide), keep18 x 27 (by rw [len18]; decide), keep17 x 27 (by rw [len17]; decide), keep16 x 27 (by rw [len16]; decide), keep15 x 27 (by rw [len15]; decide), keep14 x 27 (by rw [len14]; decide), keep13 x 27 (by rw [len13]; decide), keep12 x 27 (by rw [len12]; decide)]
  rw [w11]
  rw [keep20 x 30 (by rw [len20]; decide), keep19 x 30 (by rw [len19]; decide), keep18 x 30 (by rw [len18]; decide), keep17 x 30 (by rw [len17]; decide), keep16 x 30 (by rw [len16]; decide), keep15 x 30 (by rw [len15]; decide)]
  rw [w14]

lemma w22 (x : Fin 16 → Bool) : (L23 x).getD 38 false = ((((x 10) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 14) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7))))) || ((((x 8) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 12) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5))))) || (((x 9) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5)))) && ((x 5) || (x 13))))) := by
  have hlen := len22 x
  rw [L23, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [keep21 x 33 (by rw [len21]; decide), keep20 x 33 (by rw [len20]; decide), keep19 x 33 (by rw [len19]; decide), keep18 x 33 (by rw [len18]; decide)]
  rw [w17]
  rw [w21]

lemma w23 (x : Fin 16 → Bool) : (L24 x).getD 39 false = ((((x 11) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7)))) && ((x 7) || (x 15))) || ((((x 10) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 14) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7))))) || ((((x 8) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 12) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5))))) || (((x 9) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5)))) && ((x 5) || (x 13)))))) := by
  have hlen := len23 x
  rw [L24, step]
  rw [getD_at hlen]
  rw [map_two, or_two]
  rw [keep22 x 36 (by rw [len22]; decide), keep21 x 36 (by rw [len21]; decide)]
  rw [w20]
  rw [w22]

def sem (x : Fin 16 → Bool) : Bool := ((((x 11) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7)))) && ((x 7) || (x 15))) || ((((x 10) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 14) || (((x 6) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 2) || (x 7))))) || ((((x 8) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 12) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5))))) || (((x 9) || (((x 4) || (((x 1) || (x 2)) && ((x 0) || (x 3)))) && ((x 0) || (x 5)))) && ((x 5) || (x 13))))))

def matchEdges : List (Fin 16 × Fin 16) := [(0, 1), (2, 3), (4, 5), (6, 7), (8, 12), (9, 13), (10, 14), (11, 15)]

def allEdges : List (Fin 16 × Fin 16) := [(0, 1), (2, 3), (4, 5), (6, 7), (8, 12), (9, 13), (10, 14), (11, 15), (0, 2), (3, 5), (1, 7), (1, 12), (4, 8), (5, 9), (0, 13), (3, 14), (6, 10), (7, 11), (2, 15)]

lemma low (x : Fin 16 → Bool)
    (h : ∃ e ∈ matchEdges, x e.1 = true ∧ x e.2 = true) : sem x = true := by
  rcases h with ⟨e, he, h1, h2⟩
  simp only [matchEdges, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [sem, h1, h2]

lemma high (x : Fin 16 → Bool) (h : sem x = true) :
    ∃ e ∈ allEdges, x e.1 = true ∧ x e.2 = true := by
  unfold sem at h
  rcases Bool.or_eq_true_iff.mp h with h1 | h2
  rcases Bool.and_eq_true_iff.mp h1 with ⟨h3, h4⟩
  rcases Bool.or_eq_true_iff.mp h3 with h5 | h6
  rcases Bool.or_eq_true_iff.mp h4 with h7 | h8
  exact ⟨(7, 11), by decide, h7, h5⟩
  exact ⟨(11, 15), by decide, h5, h8⟩
  rcases Bool.and_eq_true_iff.mp h6 with ⟨h9, h10⟩
  rcases Bool.or_eq_true_iff.mp h9 with h11 | h12
  rcases Bool.or_eq_true_iff.mp h10 with h13 | h14
  rcases Bool.or_eq_true_iff.mp h4 with h15 | h16
  exact ⟨(6, 7), by decide, h11, h15⟩
  exact ⟨(2, 15), by decide, h13, h16⟩
  rcases Bool.or_eq_true_iff.mp h4 with h17 | h18
  exact ⟨(6, 7), by decide, h11, h14⟩
  exact ⟨(6, 7), by decide, h11, h14⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨h19, h20⟩
  rcases Bool.or_eq_true_iff.mp h19 with h21 | h22
  rcases Bool.or_eq_true_iff.mp h20 with h23 | h24
  rcases Bool.or_eq_true_iff.mp h10 with h25 | h26
  rcases Bool.or_eq_true_iff.mp h4 with h27 | h28
  exact ⟨(0, 1), by decide, h23, h21⟩
  exact ⟨(0, 1), by decide, h23, h21⟩
  rcases Bool.or_eq_true_iff.mp h4 with h29 | h30
  exact ⟨(0, 1), by decide, h23, h21⟩
  exact ⟨(0, 1), by decide, h23, h21⟩
  rcases Bool.or_eq_true_iff.mp h10 with h31 | h32
  rcases Bool.or_eq_true_iff.mp h4 with h33 | h34
  exact ⟨(2, 3), by decide, h31, h24⟩
  exact ⟨(2, 3), by decide, h31, h24⟩
  rcases Bool.or_eq_true_iff.mp h4 with h35 | h36
  exact ⟨(1, 7), by decide, h21, h32⟩
  exact ⟨(1, 7), by decide, h21, h32⟩
  rcases Bool.or_eq_true_iff.mp h20 with h37 | h38
  rcases Bool.or_eq_true_iff.mp h10 with h39 | h40
  rcases Bool.or_eq_true_iff.mp h4 with h41 | h42
  exact ⟨(0, 2), by decide, h37, h22⟩
  exact ⟨(0, 2), by decide, h37, h22⟩
  rcases Bool.or_eq_true_iff.mp h4 with h43 | h44
  exact ⟨(0, 2), by decide, h37, h22⟩
  exact ⟨(0, 2), by decide, h37, h22⟩
  rcases Bool.or_eq_true_iff.mp h10 with h45 | h46
  rcases Bool.or_eq_true_iff.mp h4 with h47 | h48
  exact ⟨(2, 3), by decide, h22, h38⟩
  exact ⟨(2, 3), by decide, h22, h38⟩
  rcases Bool.or_eq_true_iff.mp h4 with h49 | h50
  exact ⟨(2, 3), by decide, h22, h38⟩
  exact ⟨(2, 3), by decide, h22, h38⟩
  rcases Bool.or_eq_true_iff.mp h2 with h51 | h52
  rcases Bool.and_eq_true_iff.mp h51 with ⟨h53, h54⟩
  rcases Bool.or_eq_true_iff.mp h53 with h55 | h56
  rcases Bool.or_eq_true_iff.mp h54 with h57 | h58
  exact ⟨(10, 14), by decide, h55, h57⟩
  rcases Bool.and_eq_true_iff.mp h58 with ⟨h59, h60⟩
  rcases Bool.or_eq_true_iff.mp h59 with h61 | h62
  rcases Bool.or_eq_true_iff.mp h60 with h63 | h64
  exact ⟨(6, 10), by decide, h61, h55⟩
  exact ⟨(6, 7), by decide, h61, h64⟩
  rcases Bool.and_eq_true_iff.mp h62 with ⟨h65, h66⟩
  rcases Bool.or_eq_true_iff.mp h65 with h67 | h68
  rcases Bool.or_eq_true_iff.mp h66 with h69 | h70
  rcases Bool.or_eq_true_iff.mp h60 with h71 | h72
  exact ⟨(0, 1), by decide, h69, h67⟩
  exact ⟨(0, 1), by decide, h69, h67⟩
  rcases Bool.or_eq_true_iff.mp h60 with h73 | h74
  exact ⟨(2, 3), by decide, h73, h70⟩
  exact ⟨(1, 7), by decide, h67, h74⟩
  rcases Bool.or_eq_true_iff.mp h66 with h75 | h76
  rcases Bool.or_eq_true_iff.mp h60 with h77 | h78
  exact ⟨(0, 2), by decide, h75, h68⟩
  exact ⟨(0, 2), by decide, h75, h68⟩
  rcases Bool.or_eq_true_iff.mp h60 with h79 | h80
  exact ⟨(2, 3), by decide, h68, h76⟩
  exact ⟨(2, 3), by decide, h68, h76⟩
  rcases Bool.and_eq_true_iff.mp h56 with ⟨h81, h82⟩
  rcases Bool.or_eq_true_iff.mp h81 with h83 | h84
  rcases Bool.or_eq_true_iff.mp h82 with h85 | h86
  rcases Bool.or_eq_true_iff.mp h54 with h87 | h88
  exact ⟨(0, 1), by decide, h85, h83⟩
  rcases Bool.and_eq_true_iff.mp h88 with ⟨h89, h90⟩
  rcases Bool.or_eq_true_iff.mp h89 with h91 | h92
  rcases Bool.or_eq_true_iff.mp h90 with h93 | h94
  exact ⟨(0, 1), by decide, h85, h83⟩
  exact ⟨(0, 1), by decide, h85, h83⟩
  rcases Bool.and_eq_true_iff.mp h92 with ⟨h95, h96⟩
  rcases Bool.or_eq_true_iff.mp h95 with h97 | h98
  rcases Bool.or_eq_true_iff.mp h96 with h99 | h100
  rcases Bool.or_eq_true_iff.mp h90 with h101 | h102
  exact ⟨(0, 1), by decide, h85, h83⟩
  exact ⟨(0, 1), by decide, h85, h83⟩
  rcases Bool.or_eq_true_iff.mp h90 with h103 | h104
  exact ⟨(0, 1), by decide, h85, h83⟩
  exact ⟨(0, 1), by decide, h85, h83⟩
  rcases Bool.or_eq_true_iff.mp h96 with h105 | h106
  rcases Bool.or_eq_true_iff.mp h90 with h107 | h108
  exact ⟨(0, 1), by decide, h85, h83⟩
  exact ⟨(0, 1), by decide, h85, h83⟩
  rcases Bool.or_eq_true_iff.mp h90 with h109 | h110
  exact ⟨(0, 1), by decide, h85, h83⟩
  exact ⟨(0, 1), by decide, h85, h83⟩
  rcases Bool.or_eq_true_iff.mp h54 with h111 | h112
  exact ⟨(3, 14), by decide, h86, h111⟩
  rcases Bool.and_eq_true_iff.mp h112 with ⟨h113, h114⟩
  rcases Bool.or_eq_true_iff.mp h113 with h115 | h116
  rcases Bool.or_eq_true_iff.mp h114 with h117 | h118
  exact ⟨(2, 3), by decide, h117, h86⟩
  exact ⟨(6, 7), by decide, h115, h118⟩
  rcases Bool.and_eq_true_iff.mp h116 with ⟨h119, h120⟩
  rcases Bool.or_eq_true_iff.mp h119 with h121 | h122
  rcases Bool.or_eq_true_iff.mp h120 with h123 | h124
  rcases Bool.or_eq_true_iff.mp h114 with h125 | h126
  exact ⟨(0, 1), by decide, h123, h83⟩
  exact ⟨(0, 1), by decide, h123, h83⟩
  rcases Bool.or_eq_true_iff.mp h114 with h127 | h128
  exact ⟨(2, 3), by decide, h127, h86⟩
  exact ⟨(1, 7), by decide, h83, h128⟩
  rcases Bool.or_eq_true_iff.mp h120 with h129 | h130
  rcases Bool.or_eq_true_iff.mp h114 with h131 | h132
  exact ⟨(0, 1), by decide, h129, h83⟩
  exact ⟨(0, 1), by decide, h129, h83⟩
  rcases Bool.or_eq_true_iff.mp h114 with h133 | h134
  exact ⟨(2, 3), by decide, h122, h86⟩
  exact ⟨(2, 3), by decide, h122, h86⟩
  rcases Bool.or_eq_true_iff.mp h82 with h135 | h136
  rcases Bool.or_eq_true_iff.mp h54 with h137 | h138
  exact ⟨(0, 2), by decide, h135, h84⟩
  rcases Bool.and_eq_true_iff.mp h138 with ⟨h139, h140⟩
  rcases Bool.or_eq_true_iff.mp h139 with h141 | h142
  rcases Bool.or_eq_true_iff.mp h140 with h143 | h144
  exact ⟨(0, 2), by decide, h135, h84⟩
  exact ⟨(6, 7), by decide, h141, h144⟩
  rcases Bool.and_eq_true_iff.mp h142 with ⟨h145, h146⟩
  rcases Bool.or_eq_true_iff.mp h145 with h147 | h148
  rcases Bool.or_eq_true_iff.mp h146 with h149 | h150
  rcases Bool.or_eq_true_iff.mp h140 with h151 | h152
  exact ⟨(0, 1), by decide, h135, h147⟩
  exact ⟨(0, 1), by decide, h135, h147⟩
  rcases Bool.or_eq_true_iff.mp h140 with h153 | h154
  exact ⟨(0, 1), by decide, h135, h147⟩
  exact ⟨(0, 1), by decide, h135, h147⟩
  rcases Bool.or_eq_true_iff.mp h146 with h155 | h156
  rcases Bool.or_eq_true_iff.mp h140 with h157 | h158
  exact ⟨(0, 2), by decide, h135, h84⟩
  exact ⟨(0, 2), by decide, h135, h84⟩
  rcases Bool.or_eq_true_iff.mp h140 with h159 | h160
  exact ⟨(2, 3), by decide, h84, h156⟩
  exact ⟨(2, 3), by decide, h84, h156⟩
  rcases Bool.or_eq_true_iff.mp h54 with h161 | h162
  exact ⟨(2, 3), by decide, h84, h136⟩
  rcases Bool.and_eq_true_iff.mp h162 with ⟨h163, h164⟩
  rcases Bool.or_eq_true_iff.mp h163 with h165 | h166
  rcases Bool.or_eq_true_iff.mp h164 with h167 | h168
  exact ⟨(2, 3), by decide, h84, h136⟩
  exact ⟨(2, 3), by decide, h84, h136⟩
  rcases Bool.and_eq_true_iff.mp h166 with ⟨h169, h170⟩
  rcases Bool.or_eq_true_iff.mp h169 with h171 | h172
  rcases Bool.or_eq_true_iff.mp h170 with h173 | h174
  rcases Bool.or_eq_true_iff.mp h164 with h175 | h176
  exact ⟨(0, 1), by decide, h173, h171⟩
  exact ⟨(0, 1), by decide, h173, h171⟩
  rcases Bool.or_eq_true_iff.mp h164 with h177 | h178
  exact ⟨(2, 3), by decide, h84, h136⟩
  exact ⟨(2, 3), by decide, h84, h136⟩
  rcases Bool.or_eq_true_iff.mp h170 with h179 | h180
  rcases Bool.or_eq_true_iff.mp h164 with h181 | h182
  exact ⟨(2, 3), by decide, h84, h136⟩
  exact ⟨(2, 3), by decide, h84, h136⟩
  rcases Bool.or_eq_true_iff.mp h164 with h183 | h184
  exact ⟨(2, 3), by decide, h84, h136⟩
  exact ⟨(2, 3), by decide, h84, h136⟩
  rcases Bool.or_eq_true_iff.mp h52 with h185 | h186
  rcases Bool.and_eq_true_iff.mp h185 with ⟨h187, h188⟩
  rcases Bool.or_eq_true_iff.mp h187 with h189 | h190
  rcases Bool.or_eq_true_iff.mp h188 with h191 | h192
  exact ⟨(8, 12), by decide, h189, h191⟩
  rcases Bool.and_eq_true_iff.mp h192 with ⟨h193, h194⟩
  rcases Bool.or_eq_true_iff.mp h193 with h195 | h196
  rcases Bool.or_eq_true_iff.mp h194 with h197 | h198
  exact ⟨(4, 8), by decide, h195, h189⟩
  exact ⟨(4, 5), by decide, h195, h198⟩
  rcases Bool.and_eq_true_iff.mp h196 with ⟨h199, h200⟩
  rcases Bool.or_eq_true_iff.mp h199 with h201 | h202
  rcases Bool.or_eq_true_iff.mp h200 with h203 | h204
  rcases Bool.or_eq_true_iff.mp h194 with h205 | h206
  exact ⟨(0, 1), by decide, h203, h201⟩
  exact ⟨(0, 1), by decide, h203, h201⟩
  rcases Bool.or_eq_true_iff.mp h194 with h207 | h208
  exact ⟨(0, 1), by decide, h207, h201⟩
  exact ⟨(3, 5), by decide, h204, h208⟩
  rcases Bool.or_eq_true_iff.mp h200 with h209 | h210
  rcases Bool.or_eq_true_iff.mp h194 with h211 | h212
  exact ⟨(0, 2), by decide, h209, h202⟩
  exact ⟨(0, 2), by decide, h209, h202⟩
  rcases Bool.or_eq_true_iff.mp h194 with h213 | h214
  exact ⟨(2, 3), by decide, h202, h210⟩
  exact ⟨(2, 3), by decide, h202, h210⟩
  rcases Bool.and_eq_true_iff.mp h190 with ⟨h215, h216⟩
  rcases Bool.or_eq_true_iff.mp h215 with h217 | h218
  rcases Bool.or_eq_true_iff.mp h216 with h219 | h220
  rcases Bool.or_eq_true_iff.mp h188 with h221 | h222
  exact ⟨(0, 1), by decide, h219, h217⟩
  rcases Bool.and_eq_true_iff.mp h222 with ⟨h223, h224⟩
  rcases Bool.or_eq_true_iff.mp h223 with h225 | h226
  rcases Bool.or_eq_true_iff.mp h224 with h227 | h228
  exact ⟨(0, 1), by decide, h219, h217⟩
  exact ⟨(0, 1), by decide, h219, h217⟩
  rcases Bool.and_eq_true_iff.mp h226 with ⟨h229, h230⟩
  rcases Bool.or_eq_true_iff.mp h229 with h231 | h232
  rcases Bool.or_eq_true_iff.mp h230 with h233 | h234
  rcases Bool.or_eq_true_iff.mp h224 with h235 | h236
  exact ⟨(0, 1), by decide, h219, h217⟩
  exact ⟨(0, 1), by decide, h219, h217⟩
  rcases Bool.or_eq_true_iff.mp h224 with h237 | h238
  exact ⟨(0, 1), by decide, h219, h217⟩
  exact ⟨(0, 1), by decide, h219, h217⟩
  rcases Bool.or_eq_true_iff.mp h230 with h239 | h240
  rcases Bool.or_eq_true_iff.mp h224 with h241 | h242
  exact ⟨(0, 1), by decide, h219, h217⟩
  exact ⟨(0, 1), by decide, h219, h217⟩
  rcases Bool.or_eq_true_iff.mp h224 with h243 | h244
  exact ⟨(0, 1), by decide, h219, h217⟩
  exact ⟨(0, 1), by decide, h219, h217⟩
  rcases Bool.or_eq_true_iff.mp h188 with h245 | h246
  exact ⟨(1, 12), by decide, h217, h245⟩
  rcases Bool.and_eq_true_iff.mp h246 with ⟨h247, h248⟩
  rcases Bool.or_eq_true_iff.mp h247 with h249 | h250
  rcases Bool.or_eq_true_iff.mp h248 with h251 | h252
  exact ⟨(0, 1), by decide, h251, h217⟩
  exact ⟨(4, 5), by decide, h249, h252⟩
  rcases Bool.and_eq_true_iff.mp h250 with ⟨h253, h254⟩
  rcases Bool.or_eq_true_iff.mp h253 with h255 | h256
  rcases Bool.or_eq_true_iff.mp h254 with h257 | h258
  rcases Bool.or_eq_true_iff.mp h248 with h259 | h260
  exact ⟨(0, 1), by decide, h257, h217⟩
  exact ⟨(0, 1), by decide, h257, h217⟩
  rcases Bool.or_eq_true_iff.mp h248 with h261 | h262
  exact ⟨(0, 1), by decide, h261, h217⟩
  exact ⟨(3, 5), by decide, h220, h262⟩
  rcases Bool.or_eq_true_iff.mp h254 with h263 | h264
  rcases Bool.or_eq_true_iff.mp h248 with h265 | h266
  exact ⟨(0, 1), by decide, h263, h217⟩
  exact ⟨(0, 1), by decide, h263, h217⟩
  rcases Bool.or_eq_true_iff.mp h248 with h267 | h268
  exact ⟨(0, 1), by decide, h267, h217⟩
  exact ⟨(2, 3), by decide, h256, h220⟩
  rcases Bool.or_eq_true_iff.mp h216 with h269 | h270
  rcases Bool.or_eq_true_iff.mp h188 with h271 | h272
  exact ⟨(0, 2), by decide, h269, h218⟩
  rcases Bool.and_eq_true_iff.mp h272 with ⟨h273, h274⟩
  rcases Bool.or_eq_true_iff.mp h273 with h275 | h276
  rcases Bool.or_eq_true_iff.mp h274 with h277 | h278
  exact ⟨(0, 2), by decide, h269, h218⟩
  exact ⟨(4, 5), by decide, h275, h278⟩
  rcases Bool.and_eq_true_iff.mp h276 with ⟨h279, h280⟩
  rcases Bool.or_eq_true_iff.mp h279 with h281 | h282
  rcases Bool.or_eq_true_iff.mp h280 with h283 | h284
  rcases Bool.or_eq_true_iff.mp h274 with h285 | h286
  exact ⟨(0, 1), by decide, h269, h281⟩
  exact ⟨(0, 1), by decide, h269, h281⟩
  rcases Bool.or_eq_true_iff.mp h274 with h287 | h288
  exact ⟨(0, 1), by decide, h269, h281⟩
  exact ⟨(0, 1), by decide, h269, h281⟩
  rcases Bool.or_eq_true_iff.mp h280 with h289 | h290
  rcases Bool.or_eq_true_iff.mp h274 with h291 | h292
  exact ⟨(0, 2), by decide, h269, h218⟩
  exact ⟨(0, 2), by decide, h269, h218⟩
  rcases Bool.or_eq_true_iff.mp h274 with h293 | h294
  exact ⟨(2, 3), by decide, h218, h290⟩
  exact ⟨(2, 3), by decide, h218, h290⟩
  rcases Bool.or_eq_true_iff.mp h188 with h295 | h296
  exact ⟨(2, 3), by decide, h218, h270⟩
  rcases Bool.and_eq_true_iff.mp h296 with ⟨h297, h298⟩
  rcases Bool.or_eq_true_iff.mp h297 with h299 | h300
  rcases Bool.or_eq_true_iff.mp h298 with h301 | h302
  exact ⟨(2, 3), by decide, h218, h270⟩
  exact ⟨(2, 3), by decide, h218, h270⟩
  rcases Bool.and_eq_true_iff.mp h300 with ⟨h303, h304⟩
  rcases Bool.or_eq_true_iff.mp h303 with h305 | h306
  rcases Bool.or_eq_true_iff.mp h304 with h307 | h308
  rcases Bool.or_eq_true_iff.mp h298 with h309 | h310
  exact ⟨(0, 1), by decide, h307, h305⟩
  exact ⟨(0, 1), by decide, h307, h305⟩
  rcases Bool.or_eq_true_iff.mp h298 with h311 | h312
  exact ⟨(0, 1), by decide, h311, h305⟩
  exact ⟨(2, 3), by decide, h218, h270⟩
  rcases Bool.or_eq_true_iff.mp h304 with h313 | h314
  rcases Bool.or_eq_true_iff.mp h298 with h315 | h316
  exact ⟨(2, 3), by decide, h218, h270⟩
  exact ⟨(2, 3), by decide, h218, h270⟩
  rcases Bool.or_eq_true_iff.mp h298 with h317 | h318
  exact ⟨(2, 3), by decide, h218, h270⟩
  exact ⟨(2, 3), by decide, h218, h270⟩
  rcases Bool.and_eq_true_iff.mp h186 with ⟨h319, h320⟩
  rcases Bool.or_eq_true_iff.mp h319 with h321 | h322
  rcases Bool.or_eq_true_iff.mp h320 with h323 | h324
  exact ⟨(5, 9), by decide, h323, h321⟩
  exact ⟨(9, 13), by decide, h321, h324⟩
  rcases Bool.and_eq_true_iff.mp h322 with ⟨h325, h326⟩
  rcases Bool.or_eq_true_iff.mp h325 with h327 | h328
  rcases Bool.or_eq_true_iff.mp h326 with h329 | h330
  rcases Bool.or_eq_true_iff.mp h320 with h331 | h332
  exact ⟨(4, 5), by decide, h327, h331⟩
  exact ⟨(0, 13), by decide, h329, h332⟩
  rcases Bool.or_eq_true_iff.mp h320 with h333 | h334
  exact ⟨(4, 5), by decide, h327, h330⟩
  exact ⟨(4, 5), by decide, h327, h330⟩
  rcases Bool.and_eq_true_iff.mp h328 with ⟨h335, h336⟩
  rcases Bool.or_eq_true_iff.mp h335 with h337 | h338
  rcases Bool.or_eq_true_iff.mp h336 with h339 | h340
  rcases Bool.or_eq_true_iff.mp h326 with h341 | h342
  rcases Bool.or_eq_true_iff.mp h320 with h343 | h344
  exact ⟨(0, 1), by decide, h339, h337⟩
  exact ⟨(0, 1), by decide, h339, h337⟩
  rcases Bool.or_eq_true_iff.mp h320 with h345 | h346
  exact ⟨(0, 1), by decide, h339, h337⟩
  exact ⟨(0, 1), by decide, h339, h337⟩
  rcases Bool.or_eq_true_iff.mp h326 with h347 | h348
  rcases Bool.or_eq_true_iff.mp h320 with h349 | h350
  exact ⟨(0, 1), by decide, h347, h337⟩
  exact ⟨(0, 1), by decide, h347, h337⟩
  rcases Bool.or_eq_true_iff.mp h320 with h351 | h352
  exact ⟨(3, 5), by decide, h340, h348⟩
  exact ⟨(3, 5), by decide, h340, h348⟩
  rcases Bool.or_eq_true_iff.mp h336 with h353 | h354
  rcases Bool.or_eq_true_iff.mp h326 with h355 | h356
  rcases Bool.or_eq_true_iff.mp h320 with h357 | h358
  exact ⟨(0, 2), by decide, h353, h338⟩
  exact ⟨(0, 2), by decide, h353, h338⟩
  rcases Bool.or_eq_true_iff.mp h320 with h359 | h360
  exact ⟨(0, 2), by decide, h353, h338⟩
  exact ⟨(0, 2), by decide, h353, h338⟩
  rcases Bool.or_eq_true_iff.mp h326 with h361 | h362
  rcases Bool.or_eq_true_iff.mp h320 with h363 | h364
  exact ⟨(2, 3), by decide, h338, h354⟩
  exact ⟨(2, 3), by decide, h338, h354⟩
  rcases Bool.or_eq_true_iff.mp h320 with h365 | h366
  exact ⟨(2, 3), by decide, h338, h354⟩
  exact ⟨(2, 3), by decide, h338, h354⟩

abbrev C0 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [4, 18]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [19, 20]⟩, ⟨GateOp.or, [6, 18]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [22, 23]⟩, ⟨GateOp.or, [8, 18]⟩, ⟨GateOp.or, [12, 21]⟩, ⟨GateOp.and, [25, 26]⟩, ⟨GateOp.or, [9, 21]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.and, [28, 29]⟩, ⟨GateOp.or, [10, 18]⟩, ⟨GateOp.or, [14, 24]⟩, ⟨GateOp.and, [31, 32]⟩, ⟨GateOp.or, [11, 24]⟩, ⟨GateOp.or, [7, 15]⟩, ⟨GateOp.and, [34, 35]⟩, ⟨GateOp.or, [27, 30]⟩, ⟨GateOp.or, [33, 37]⟩, ⟨GateOp.or, [36, 38]⟩], output := 39 }

lemma wires_eq (x : Fin 16 → Bool) : C0.wires (List.ofFn x) = L24 x := by
  simp only [Circuit.wires, L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, L12, L13, L14, L15, L16, L17, L18, L19, L20, L21, L22, L23, L24, step]
  rfl

lemma out_eq (x : Fin 16 → Bool) : PEqualNP.MetaComplexity.circuitFun 16 C0 x = sem x := by
  rw [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, wires_eq]
  rw [show C0.output = 39 by rfl]
  rw [w23]
  unfold sem
  rfl

end PEqualNP.Outside.L_meta_5396

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_5396 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 38] }], output := 39 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 16 C ∧ C.size = 24 ∧
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ k ∈ ([2, 5, 8, 11, 14, 17, 20] : List ℕ)) ∧
  ∀ x : Fin 16 → Bool,
    ((∃ e ∈ ([(0, 1), (2, 3), (4, 5), (6, 7), (8, 12), (9, 13), (10, 14), (11, 15)] : List (Fin 16 × Fin 16)), x e.1 = true ∧ x e.2 = true) → PEqualNP.MetaComplexity.circuitFun 16 C x = true) ∧
    (PEqualNP.MetaComplexity.circuitFun 16 C x = true → ∃ e ∈ ([(0, 1), (2, 3), (4, 5), (6, 7), (8, 12), (9, 13), (10, 14), (11, 15), (0, 2), (3, 5), (1, 7), (1, 12), (4, 8), (5, 9), (0, 13), (3, 14), (6, 10), (7, 11), (2, 15)] : List (Fin 16 × Fin 16)), x e.1 = true ∧ x e.2 = true) := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro k hk
    have hk24 : k < 24 := by simpa using hk
    interval_cases k <;> simp [PEqualNP.MetaComplexity.NestedCover.gateAt]
  · intro x
    rw [PEqualNP.Outside.L_meta_5396.out_eq x]
    constructor
    · intro h
      exact PEqualNP.Outside.L_meta_5396.low x h
    · intro h
      exact PEqualNP.Outside.L_meta_5396.high x h
