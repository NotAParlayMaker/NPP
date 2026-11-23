import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1101_aux

open PEqualNP.CircuitLowerBounds

-- The wires after running a list of gates on a starting list of wires.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem getD_left (l m : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ m).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at_length (l : List Bool) (b : Bool) (m : List Bool) :
    (l ++ b :: m).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

-- Wire holding the OR of the first k + 1 inputs.
def pIdx (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => n + 3 * k + 3

-- Wire holding threshold two of the first k + 1 inputs.
def tIdx (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => n + 3 * k + 2

-- The three gates that take input k + 1 into account.
def step (n k : ℕ) : List Gate :=
  [⟨GateOp.and, [pIdx n k, k + 1]⟩, ⟨GateOp.or, [tIdx n k, n + 3 * k + 1]⟩,
    ⟨GateOp.or, [pIdx n k, k + 1]⟩]

def gatesUpTo (n : ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.or, []⟩]
  | k + 1 => gatesUpTo n k ++ step n k

theorem length_gatesUpTo (n k : ℕ) : (gatesUpTo n k).length = 3 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [gatesUpTo, step, ih]; omega

theorem gate_ok (n k : ℕ) : ∀ g ∈ gatesUpTo n k,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero =>
    intro g hg
    simp [gatesUpTo] at hg
    subst hg
    simp
  | succ k ih =>
    intro g hg
    simp only [gatesUpTo, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · simp [step] at hg
      rcases hg with rfl | rfl | rfl <;> simp

theorem idx_lt (n k : ℕ) (hn : 1 ≤ n) :
    pIdx n k < n + 3 * k + 1 ∧ tIdx n k < n + 3 * k + 1 := by
  cases k with
  | zero => simp only [pIdx, tIdx]; omega
  | succ k => simp only [pIdx, tIdx]; omega

theorem wiresFrom_step (n k : ℕ) (W : List Bool) (hW : W.length = n + 3 * k + 1)
    (hp : pIdx n k < W.length) (ht : tIdx n k < W.length) (hk : k + 1 < W.length) :
    wiresFrom (step n k) W = W ++ [W.getD (pIdx n k) false && W.getD (k + 1) false,
      W.getD (tIdx n k) false || (W.getD (pIdx n k) false && W.getD (k + 1) false),
      W.getD (pIdx n k) false || W.getD (k + 1) false] := by
  simp only [step, wiresFrom_cons, wiresFrom_nil, List.map_cons, List.map_nil]
  generalize hA : GateOp.eval GateOp.and [W.getD (pIdx n k) false, W.getD (k + 1) false] = A
  have q1 : (W ++ [A]).getD (tIdx n k) false = W.getD (tIdx n k) false := getD_left W _ _ ht
  have q2 : (W ++ [A]).getD (n + 3 * k + 1) false = A := by
    rw [← hW]; exact getD_at_length W A []
  rw [q1, q2]
  generalize hB : GateOp.eval GateOp.or [W.getD (tIdx n k) false, A] = B
  have hl : (W ++ [A]).length = W.length + 1 := by simp
  have q3 : (W ++ [A] ++ [B]).getD (pIdx n k) false = W.getD (pIdx n k) false := by
    rw [getD_left (W ++ [A]) _ _ (by omega), getD_left W _ _ hp]
  have q4 : (W ++ [A] ++ [B]).getD (k + 1) false = W.getD (k + 1) false := by
    rw [getD_left (W ++ [A]) _ _ (by omega), getD_left W _ _ hk]
  rw [q3, q4]
  subst hA hB
  simp [GateOp.eval]

theorem count_take_succ (x : List Bool) (k : ℕ) (hk : k < x.length) :
    (x.take (k + 1)).count true
      = (x.take k).count true + (if x.getD k false then 1 else 0) := by
  rw [List.take_add_one, List.count_append, List.getElem?_eq_getElem hk]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  cases x[k] <;> simp

theorem upd_p (c : ℕ) (b : Bool) :
    (decide (1 ≤ c) || b) = decide (1 ≤ c + (if b then 1 else 0)) := by
  cases b <;> by_cases h : 1 ≤ c <;> simp [h]

theorem upd_t (c : ℕ) (b : Bool) :
    (decide (2 ≤ c) || (decide (1 ≤ c) && b)) = decide (2 ≤ c + (if b then 1 else 0)) := by
  cases b <;> by_cases h : 1 ≤ c <;> by_cases h2 : 2 ≤ c <;> simp [h, h2] <;> omega

theorem invariant (n : ℕ) (x : List Bool) (hx : x.length = n) :
    ∀ k, k + 1 ≤ n →
      (wiresFrom (gatesUpTo n k) x).length = n + 3 * k + 1 ∧
      (∀ i, i < n → (wiresFrom (gatesUpTo n k) x).getD i false = x.getD i false) ∧
      (wiresFrom (gatesUpTo n k) x).getD (pIdx n k) false
        = decide (1 ≤ (x.take (k + 1)).count true) ∧
      (wiresFrom (gatesUpTo n k) x).getD (tIdx n k) false
        = decide (2 ≤ (x.take (k + 1)).count true) := by
  intro k
  induction k with
  | zero =>
    intro hn
    have hw : wiresFrom (gatesUpTo n 0) x = x ++ [false] := by
      simp [gatesUpTo, wiresFrom_cons, wiresFrom_nil, GateOp.eval]
    rw [hw]
    refine ⟨by simp [hx], ?_, ?_, ?_⟩
    · intro i hi
      exact getD_left x _ i (by omega)
    · rw [show pIdx n 0 = 0 from rfl, getD_left x _ 0 (by omega)]
      have := count_take_succ x 0 (by omega)
      rw [this]
      cases x.getD 0 false <;> simp
    · rw [show tIdx n 0 = n from rfl, ← hx, getD_at_length x false []]
      have := count_take_succ x 0 (by omega)
      rw [this]
      cases x.getD 0 false <;> simp
  | succ k ih =>
    intro hk
    obtain ⟨hlen, hin, hp, ht⟩ := ih (by omega)
    have hlt := idx_lt n k (by omega)
    have hW : wiresFrom (gatesUpTo n (k + 1)) x
        = wiresFrom (gatesUpTo n k) x ++
          [(wiresFrom (gatesUpTo n k) x).getD (pIdx n k) false
              && (wiresFrom (gatesUpTo n k) x).getD (k + 1) false,
            (wiresFrom (gatesUpTo n k) x).getD (tIdx n k) false
              || ((wiresFrom (gatesUpTo n k) x).getD (pIdx n k) false
                && (wiresFrom (gatesUpTo n k) x).getD (k + 1) false),
            (wiresFrom (gatesUpTo n k) x).getD (pIdx n k) false
              || (wiresFrom (gatesUpTo n k) x).getD (k + 1) false] := by
      rw [show gatesUpTo n (k + 1) = gatesUpTo n k ++ step n k from rfl, wiresFrom_append]
      exact wiresFrom_step n k _ hlen (by omega) (by omega) (by omega)
    have hxk : (wiresFrom (gatesUpTo n k) x).getD (k + 1) false = x.getD (k + 1) false :=
      hin (k + 1) (by omega)
    rw [hxk, hp, ht] at hW
    have hc := count_take_succ x (k + 1) (by omega)
    refine ⟨by rw [hW]; simp [hlen]; omega, ?_, ?_, ?_⟩
    · intro i hi
      rw [hW, getD_left _ _ i (by omega)]
      exact hin i hi
    · rw [hW, hc, ← upd_p]
      have e : pIdx n (k + 1) = (wiresFrom (gatesUpTo n k) x).length + 2 := by
        rw [hlen]; simp [pIdx]
      rw [e]
      simp [List.getD_eq_getElem?_getD]
    · rw [hW, hc, ← upd_t]
      have e : tIdx n (k + 1) = (wiresFrom (gatesUpTo n k) x).length + 1 := by
        rw [hlen]; simp [tIdx]
      rw [e]
      simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_1101_aux

open PEqualNP.Outside.L_meta_1101_aux

theorem PEqualNP.Outside.L_meta_1101 : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.size ≤ 3 * n ∧ ∀ x : List Bool, x.length = n → (C.eval x = true ↔ 2 ≤ x.count true) := by
  intro n hn
  refine ⟨⟨gatesUpTo n (n - 1), tIdx n (n - 1)⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact (gate_ok n (n - 1) g hg).1
  · intro g hg
    exact (gate_ok n (n - 1) g hg).2
  · show (gatesUpTo n (n - 1)).length ≤ 3 * n
    rw [length_gatesUpTo]
    omega
  · intro x hx
    have h := (invariant n x hx (n - 1) (by omega)).2.2.2
    have htake : x.take (n - 1 + 1) = x := List.take_of_length_le (by omega)
    rw [htake] at h
    show (wiresFrom (gatesUpTo n (n - 1)) x).getD (tIdx n (n - 1)) false = true ↔ _
    rw [h]
    simp
