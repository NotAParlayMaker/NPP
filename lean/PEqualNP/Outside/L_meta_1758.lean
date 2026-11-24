import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1758

open PEqualNP.CircuitLowerBounds

def enc : List Bool → ℕ
  | [] => 0
  | b :: t => Nat.bit b (enc t)

theorem enc_testBit (w : List Bool) (i : ℕ) : (enc w).testBit i = w.getD i false := by
  induction w generalizing i with
  | nil => simp [enc]
  | cons b t ih =>
    cases i with
    | zero => simp [enc]
    | succ i => simp [enc, Nat.testBit_bit_succ, ih]

def run : List Gate → ℕ → ℕ → ℕ
  | [], _, W => W
  | g :: gs, k, W =>
    run gs (k + 1) (W ||| (bif g.op.eval (g.inputs.map fun i => W.testBit i) then 2 ^ k else 0))

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = (w.getD i false || (b && decide (w.length = i))) := by
  rcases lt_trichotomy i w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h.ne']
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨d, rfl⟩ : ∃ d, i = w.length + (d + 1) := ⟨i - w.length - 1, by omega⟩
    simp [List.getD_eq_getElem?_getD]

theorem run_rep (gs : List Gate) (w : List Bool) (W : ℕ)
    (h : ∀ i, W.testBit i = w.getD i false) (i : ℕ) :
    (run gs w.length W).testBit i =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs generalizing w W i with
  | nil => simpa [run] using h i
  | cons g gs ih =>
    have hv : (g.inputs.map fun i => W.testBit i) = (g.inputs.map fun i => w.getD i false) := by
      congr 1
      funext j
      exact h j
    have hrep : ∀ j, (W ||| (bif g.op.eval (g.inputs.map fun i => w.getD i false) then 2 ^ w.length
        else 0)).testBit j
        = (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD j false := by
      intro j
      rw [getD_snoc, Nat.testBit_lor, h j]
      cases g.op.eval (g.inputs.map fun i => w.getD i false) <;> simp [Nat.testBit_two_pow]
    have key := ih _ _ hrep i
    simp only [List.length_append, List.length_singleton] at key
    simp only [run, List.foldl_cons, hv]
    exact key

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (run C.gates x.length (enc x)).testBit C.output := by
  unfold Circuit.eval Circuit.wires
  exact (run_rep C.gates x (enc x) (enc_testBit x) C.output).symm

theorem wire_eq (C : Circuit) (x : List Bool) (i : ℕ) :
    (C.wires x).getD i false = (run C.gates x.length (enc x)).testBit i := by
  unfold Circuit.wires
  exact (run_rep C.gates x (enc x) (enc_testBit x) i).symm

theorem fin16 (P : Fin 16 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) (h14 : P 14) (h15 : P 15) : ∀ a, P a := by
  intro a
  fin_cases a
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

end PEqualNP.Outside.L_meta_1758

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1758 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [56, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [59, 60]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [47, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [50, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [62, 63]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [47, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [50, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [65, 66]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [58, 67]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [58, 64]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [72, 73]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [46, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [49, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [75, 76]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [47, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [50, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [78, 79]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [47, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [50, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [81, 82]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [80, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [83, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [84, 85]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [80, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [83, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [87, 88]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [77, 89]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [74, 89]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [77, 86]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [74, 86]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [58, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [94, 95]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [58, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [61, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [97, 98]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [99, 83]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [96, 83]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [99, 80]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [96, 80]⟩], 103⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 88 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 16 + p.2) ∧ (∀ i j : Fin 16, (C.wires (List.ofFn fun k : Fin 16 => decide (k = i))).getD ([52, 53, 54, 55, 68, 69, 70, 71, 90, 91, 92, 93, 100, 101, 102, 103].getD j.val 0) false = decide (j.val % 4 = (([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]].getD (i.val / 4) []).getD (j.val / 4) 0 ^^^ i.val % 4))) ∧ (C.wires (List.ofFn fun k : Fin 16 => decide (k.val = 0 ∨ k.val = 3))).getD 53 false = true ∧ ¬ (1 = (([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]].getD 0 []).getD 0 0 ^^^ 0)) ∧ ¬ (1 = (([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]].getD 0 []).getD 0 0 ^^^ 3)) := by
  intro C
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i j
    refine (PEqualNP.Outside.L_meta_1758.wire_eq _ _ _).trans ?_
    revert i j
    refine PEqualNP.Outside.L_meta_1758.fin16 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · refine (PEqualNP.Outside.L_meta_1758.wire_eq _ _ _).trans ?_
    decide +kernel
  · decide
  · decide
