import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1757

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

end PEqualNP.Outside.L_meta_1757

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1757 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 29]⟩], 40⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 27 ∧ C.output = 40 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 14 + p.2) ∧ ∀ p l : Fin 7, (p.val = (l.val) % 7 ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) → (C.eval (List.ofFn fun i : Fin 14 => decide (i.val = p.val ∨ i.val = 7 + l.val)) = false ↔ ((p.val = 2 ∧ l.val = 2) ∨ (p.val = 5 ∧ l.val = 2))) := by
  intro C
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro p l h
    rw [PEqualNP.Outside.L_meta_1757.eval_eq]
    revert p l
    decide +kernel
