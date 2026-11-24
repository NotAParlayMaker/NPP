import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1756

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

theorem red (G : List Gate) (o : ℕ) (x : Fin 14 → Bool) (r : Bool)
    (h : (run G 14 (enc (List.ofFn x))).testBit o = r) :
    Circuit.eval ⟨G, o⟩ (List.ofFn x) = r := by
  rw [eval_eq, List.length_ofFn]
  exact h

theorem fin14 (P : Fin 14 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) : ∀ a, P a := by
  intro a
  fin_cases a
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

end PEqualNP.Outside.L_meta_1756

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1756 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 29]⟩], 42⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 29 ∧ C.output = 42 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 14 + p.2) ∧ let F : (Fin 14 → Bool) → Bool := fun x => (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 4 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 5 && x 9) || (x 3 && x 10) || (x 4 && x 10) || (x 6 && x 10) || (x 0 && x 11) || (x 4 && x 11) || (x 5 && x 11) || (x 1 && x 12) || (x 5 && x 12) || (x 6 && x 12) || (x 0 && x 13) || (x 2 && x 13) || (x 6 && x 13); C.eval (List.replicate 14 false) = false ∧ ∀ a b c : Fin 14, a ≤ b → b ≤ c → C.eval (List.ofFn (fun k : Fin 14 => decide (k = a ∨ k = b ∨ k = c))) = F (fun k : Fin 14 => decide (k = a ∨ k = b ∨ k = c)) := by
  dsimp only
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro a b c hab hbc
    refine PEqualNP.Outside.L_meta_1756.red _ _ _ _ ?_
    revert a b c
    refine PEqualNP.Outside.L_meta_1756.fin14 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
