import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2901

open PEqualNP.CircuitLowerBounds

-- Bitset evaluation: all wires of a circuit in one natural number.

def gv (g : Gate) (W : ℕ) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [i, j] => W.testBit i && W.testBit j
  | GateOp.or, [i, j] => W.testBit i || W.testBit j
  | _, _ => false

def evN : List Gate → ℕ → ℕ → ℕ
  | [], W, _ => W
  | g :: gs, W, k => evN gs (if gv g W = true then W ||| 2 ^ k else W) (k + 1)

def Rel (w : List Bool) (W : ℕ) : Prop := ∀ i : ℕ, W.testBit i = w.getD i false

def Ok2 (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem testBit_or_pow (W k i : ℕ) : (W ||| 2 ^ k).testBit i = (W.testBit i || decide (i = k)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h : i = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem gv_eq (g : Gate) (hg : Ok2 g) (w : List Bool) (W : ℕ) (hr : Rel w W) :
    gv g W = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨hop, hlen⟩ := hg
  match h : g.inputs, hlen with
  | [i, j], _ =>
    rcases hop with hop | hop
    · simp [gv, hop, h, GateOp.eval, hr i, hr j]
    · simp [gv, hop, h, GateOp.eval, hr i, hr j]

theorem rel_step (g : Gate) (hg : Ok2 g) (w : List Bool) (W : ℕ) (hr : Rel w W) :
    Rel (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (if gv g W = true then W ||| 2 ^ w.length else W) := by
  intro i
  rw [← gv_eq g hg w W hr]
  rcases Nat.lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi, ← hr i]
    split_ifs
    · rw [testBit_or_pow]; simp [Nat.ne_of_lt hi]
    · rfl
  · subst hi
    have h0 : W.testBit w.length = false := by rw [hr]; simp
    simp only [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
    split_ifs with h
    · rw [testBit_or_pow]; simp [h]
    · rw [h0]; simpa using h
  · have h0 : W.testBit i = false := by rw [hr]; exact List.getD_eq_default _ _ (by omega)
    rw [List.getD_eq_default _ _ (by simp; omega)]
    split_ifs
    · rw [testBit_or_pow, h0]; simp; omega
    · exact h0

theorem rel_wires : ∀ (gs : List Gate) (w : List Bool) (W : ℕ), (∀ g ∈ gs, Ok2 g) → Rel w W →
    Rel (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      (evN gs W w.length) := by
  intro gs
  induction gs with
  | nil => intro w W _ hr; exact hr
  | cons g gs ih =>
    intro w W hok hr
    have h1 := rel_step g (hok g List.mem_cons_self) w W hr
    have h2 := ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) h1
    simp only [List.foldl_cons, evN]
    simpa using h2

def encL : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (encL bs)

theorem rel_encL : ∀ w : List Bool, Rel w (encL w) := by
  intro w
  induction w with
  | nil => intro i; simp [encL]
  | cons b bs ih =>
    intro i
    cases i with
    | zero => simp [encL]
    | succ i => simp [encL, Nat.testBit_bit_succ, ih i]

theorem eval_evN (C : Circuit) (hok : ∀ g ∈ C.gates, Ok2 g) (w : List Bool) :
    C.eval w = (evN C.gates (encL w) w.length).testBit C.output := by
  unfold Circuit.eval Circuit.wires
  rw [rel_wires C.gates w (encL w) hok (rel_encL w)]

def gG (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  ((a0 && b0) || ((a1 && b0) || ((a2 && b0) || ((a0 && b1) || ((a3 && b1) || ((a4 && b1) || ((a0 && b2) || ((a5 && b2) || ((a6 && b2) || ((a1 && b3) || ((a3 && b3) || ((a5 && b3) || ((a1 && b4) || ((a4 && b4) || ((a6 && b4) || ((a2 && b5) || ((a3 && b5) || ((a6 && b5) || ((a2 && b6) || ((a4 && b6) || (a5 && b6)))))))))))))))))))))

def C0 : Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit)

theorem C0_ok : ∀ g ∈ C0.gates, Ok2 g := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Ok2]

theorem bits_eq_0 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, false, false, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false false false false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_1 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, false, false, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false false false false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_2 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, false, false, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false false false true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_3 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, false, false, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false false false true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_4 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, false, true, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false false true false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_5 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, false, true, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false false true false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_6 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, false, true, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false false true true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_7 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, false, true, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false false true true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_8 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, true, false, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false true false false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_9 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, true, false, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false true false false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_10 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, true, false, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false true false true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_11 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, true, false, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false true false true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_12 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, true, true, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false true true false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_13 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, true, true, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false true true false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_14 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, true, true, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false true true true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_15 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, false, true, true, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false false true true true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_16 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, false, false, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true false false false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_17 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, false, false, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true false false false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_18 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, false, false, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true false false true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_19 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, false, false, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true false false true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_20 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, false, true, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true false true false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_21 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, false, true, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true false true false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_22 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, false, true, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true false true true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_23 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, false, true, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true false true true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_24 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, true, false, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true true false false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_25 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, true, false, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true true false false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_26 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, true, false, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true true false true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_27 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, true, false, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true true false true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_28 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, true, true, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true true true false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_29 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, true, true, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true true true false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_30 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, true, true, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true true true true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_31 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [false, true, true, true, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG false true true true true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_32 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, false, false, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false false false false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_33 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, false, false, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false false false false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_34 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, false, false, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false false false true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_35 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, false, false, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false false false true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_36 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, false, true, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false false true false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_37 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, false, true, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false false true false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_38 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, false, true, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false false true true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_39 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, false, true, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false false true true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_40 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, true, false, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false true false false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_41 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, true, false, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false true false false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_42 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, true, false, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false true false true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_43 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, true, false, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false true false true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_44 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, true, true, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false true true false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_45 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, true, true, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false true true false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_46 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, true, true, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false true true true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_47 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, false, true, true, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true false true true true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_48 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, false, false, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true false false false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_49 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, false, false, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true false false false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_50 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, false, false, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true false false true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_51 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, false, false, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true false false true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_52 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, false, true, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true false true false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_53 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, false, true, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true false true false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_54 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, false, true, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true false true true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_55 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, false, true, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true false true true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_56 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, true, false, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true true false false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_57 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, true, false, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true true false false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_58 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, true, false, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true true false true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_59 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, true, false, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true true false true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_60 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, true, true, false, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true true true false false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_61 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, true, true, false, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true true true false true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_62 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, true, true, true, false, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true true true true false a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq_63 : ∀ a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [true, true, true, true, true, true, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG true true true true true true a6 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem bits_eq : ∀ a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool,
    (evN C0.gates (encL [a0, a1, a2, a3, a4, a5, a6, b0, b1, b2, b3, b4, b5, b6]) 14).testBit 44 = gG a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 := by
  intro a0 a1 a2 a3 a4 a5
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5
  · exact bits_eq_0
  · exact bits_eq_1
  · exact bits_eq_2
  · exact bits_eq_3
  · exact bits_eq_4
  · exact bits_eq_5
  · exact bits_eq_6
  · exact bits_eq_7
  · exact bits_eq_8
  · exact bits_eq_9
  · exact bits_eq_10
  · exact bits_eq_11
  · exact bits_eq_12
  · exact bits_eq_13
  · exact bits_eq_14
  · exact bits_eq_15
  · exact bits_eq_16
  · exact bits_eq_17
  · exact bits_eq_18
  · exact bits_eq_19
  · exact bits_eq_20
  · exact bits_eq_21
  · exact bits_eq_22
  · exact bits_eq_23
  · exact bits_eq_24
  · exact bits_eq_25
  · exact bits_eq_26
  · exact bits_eq_27
  · exact bits_eq_28
  · exact bits_eq_29
  · exact bits_eq_30
  · exact bits_eq_31
  · exact bits_eq_32
  · exact bits_eq_33
  · exact bits_eq_34
  · exact bits_eq_35
  · exact bits_eq_36
  · exact bits_eq_37
  · exact bits_eq_38
  · exact bits_eq_39
  · exact bits_eq_40
  · exact bits_eq_41
  · exact bits_eq_42
  · exact bits_eq_43
  · exact bits_eq_44
  · exact bits_eq_45
  · exact bits_eq_46
  · exact bits_eq_47
  · exact bits_eq_48
  · exact bits_eq_49
  · exact bits_eq_50
  · exact bits_eq_51
  · exact bits_eq_52
  · exact bits_eq_53
  · exact bits_eq_54
  · exact bits_eq_55
  · exact bits_eq_56
  · exact bits_eq_57
  · exact bits_eq_58
  · exact bits_eq_59
  · exact bits_eq_60
  · exact bits_eq_61
  · exact bits_eq_62
  · exact bits_eq_63

theorem ofFn_xy (x y : Fin 7 → Bool) :
    List.ofFn x ++ List.ofFn y = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, y 0, y 1, y 2, y 3, y 4, y 5, y 6] := by
  simp [List.ofFn_succ]

theorem eval_eq (x y : Fin 7 → Bool) :
    Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn x ++ List.ofFn y) =
      gG (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) := by
  rw [ofFn_xy]
  change Circuit.eval C0 _ = _
  rw [eval_evN C0 C0_ok]
  exact bits_eq (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)

theorem rhs_eq (x y : Fin 7 → Bool) :
    decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) =
      gG (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨p, l, hm, hp, hl⟩
    fin_cases p <;> fin_cases l <;> simp_all [gG]
  · intro h
    simp only [gG, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨0, 0, by decide, h1, h2⟩
    · exact ⟨1, 0, by decide, h1, h2⟩
    · exact ⟨2, 0, by decide, h1, h2⟩
    · exact ⟨0, 1, by decide, h1, h2⟩
    · exact ⟨3, 1, by decide, h1, h2⟩
    · exact ⟨4, 1, by decide, h1, h2⟩
    · exact ⟨0, 2, by decide, h1, h2⟩
    · exact ⟨5, 2, by decide, h1, h2⟩
    · exact ⟨6, 2, by decide, h1, h2⟩
    · exact ⟨1, 3, by decide, h1, h2⟩
    · exact ⟨3, 3, by decide, h1, h2⟩
    · exact ⟨5, 3, by decide, h1, h2⟩
    · exact ⟨1, 4, by decide, h1, h2⟩
    · exact ⟨4, 4, by decide, h1, h2⟩
    · exact ⟨6, 4, by decide, h1, h2⟩
    · exact ⟨2, 5, by decide, h1, h2⟩
    · exact ⟨3, 5, by decide, h1, h2⟩
    · exact ⟨6, 5, by decide, h1, h2⟩
    · exact ⟨2, 6, by decide, h1, h2⟩
    · exact ⟨4, 6, by decide, h1, h2⟩
    · exact ⟨5, 6, by decide, h1, h2⟩

end PEqualNP.Outside.L_meta_2901

theorem PEqualNP.Outside.L_meta_2901 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 31 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ x y : Fin 7 → Bool, C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true)) ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a : Fin 7 => decide (a ∈ ({3} : Finset (Fin 7)))) ++ List.ofFn (fun b : Fin 7 => decide (b ∈ ({1} : Finset (Fin 7))))) = false ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a2 : Fin 7 => decide (a2 ∈ ({5} : Finset (Fin 7)))) ++ List.ofFn (fun b2 : Fin 7 => decide (b2 ∈ ({2} : Finset (Fin 7))))) = false := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rfl
  · decide
  · intro x y
    rw [PEqualNP.Outside.L_meta_2901.eval_eq, PEqualNP.Outside.L_meta_2901.rhs_eq]
  · decide
  · decide
