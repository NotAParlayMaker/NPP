import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1731

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

def run : List PEqualNP.CircuitLowerBounds.Gate → ℕ → ℕ → ℕ
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

theorem run_rep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (W : ℕ)
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

theorem eval_eq (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) :
    C.eval x = (run C.gates x.length (enc x)).testBit C.output := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  exact (run_rep C.gates x (enc x) (enc_testBit x) C.output).symm

def isAO : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.and => true
  | PEqualNP.CircuitLowerBounds.GateOp.or => true
  | _ => false

theorem isAO_iff (o : PEqualNP.CircuitLowerBounds.GateOp) (h : isAO o = true) :
    o = PEqualNP.CircuitLowerBounds.GateOp.and ∨ o = PEqualNP.CircuitLowerBounds.GateOp.or := by
  cases o <;> simp [isAO] at h ⊢

theorem mono2_of (C : PEqualNP.CircuitLowerBounds.Circuit)
    (h : C.gates.all (fun g => isAO g.op && decide (g.inputs.length ≤ 2)) = true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨?_, h1.2⟩
  rcases isAO_iff _ h1.1 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr h2

end PEqualNP.Outside.L_meta_1731

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1731 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 50]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 51]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [44, 52]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [45, 53]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [46, 54]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [47, 55]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [48, 56]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [49, 57]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [50, 58]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [51, 59]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [52, 60]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [53, 61]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [54, 62]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [55, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [56, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [57, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [58, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [59, 46]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [60, 47]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [61, 48]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [62, 49]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [63, 97]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [64, 98]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [65, 99]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [66, 100]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [67, 101]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [68, 102]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [69, 103]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [70, 104]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [71, 84]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [72, 85]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [73, 86]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [74, 87]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [75, 88]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [76, 89]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [77, 90]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [78, 91]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [79, 92]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [80, 93]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [81, 94]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [82, 95]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [83, 96]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [105, 106]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [126, 107]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [127, 108]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [128, 109]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [129, 110]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [130, 111]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [131, 112]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [132, 113]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [133, 114]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [134, 115]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [135, 116]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [136, 117]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [137, 118]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [138, 119]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [139, 120]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [140, 121]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [141, 122]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [142, 123]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [143, 124]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [144, 125]⟩], output := 145 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 104 ∧ (∀ p l : Fin 21, (p.val + l.val) % 21 ∈ ([0, 1, 4, 14, 16] : List ℕ) → C.eval (List.ofFn (fun i : Fin 42 => decide (i.val = p.val ∨ i.val = 21 + l.val))) = true) ∧ (∀ p l : Fin 21, (p.val + l.val) % 21 ∈ ([0, 1, 4, 14, 16] : List ℕ) → ¬ (Nat.testBit 8892411 p.val = true ∧ Nat.testBit 8892411 (21 + l.val) = true)) ∧ C.eval (List.ofFn (fun j : Fin 42 => Nat.testBit 8892411 j.val)) = true := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_1731.mono2_of _ (by decide +kernel)
  · decide +kernel
  · intro p l h
    refine (PEqualNP.Outside.L_meta_1731.eval_eq _ _).trans ?_
    revert p l
    decide +kernel
  · decide +kernel
  · refine (PEqualNP.Outside.L_meta_1731.eval_eq _ _).trans ?_
    decide +kernel
