import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1755

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

def G : List (Bool × ℕ × ℕ) := [(false, 9, 5), (false, 0, 9), (false, 0, 6), (false, 7, 3), (true, 1, 12), (false, 6, 5), (false, 11, 3), (false, 13, 1), (false, 14, 2), (true, 12, 15), (true, 4, 16), (true, 19, 11), (false, 7, 21), (true, 18, 17), (false, 20, 23), (false, 3, 15), (true, 25, 8), (true, 22, 10), (false, 27, 26), (false, 24, 28)]

def Ed : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def toGate (g : Bool × ℕ × ℕ) : Gate := ⟨cond g.1 GateOp.and GateOp.or, [g.2.1, g.2.2]⟩

def C0 : Circuit := ⟨G.map toGate, 29⟩

def stpG (fa fo : ℕ → ℕ → ℕ) (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ :=
  w ++ [cond g.1 (fa (w.getD g.2.1 0) (w.getD g.2.2 0)) (fo (w.getD g.2.1 0) (w.getD g.2.2 0))]

def rd (n : ℕ) (r : List ℕ) (a : ℕ) : ℕ := if a < n then r.getD (n - 1 - a) 0 else 0

def evR (fa fo : ℕ → ℕ → ℕ) : List (Bool × ℕ × ℕ) → ℕ → List ℕ → List ℕ
  | [], _, r => r
  | g :: gs, n, r =>
    evR fa fo gs (n + 1)
      (cond g.1 (fa (rd n r g.2.1) (rd n r g.2.2)) (fo (rd n r g.2.1) (rd n r g.2.2)) :: r)

theorem rd_eq (w : List ℕ) (a : ℕ) : rd w.length w.reverse a = w.getD a 0 := by
  unfold rd
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega)]
    congr 2
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem evR_eq (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    evR fa fo gs w.length w.reverse = (gs.foldl (stpG fa fo) w).reverse := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ← ih, evR, rd_eq, rd_eq]
    simp [stpG]

theorem length_fold (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    (gs.foldl (stpG fa fo) w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stpG]
    omega

theorem fold_getD (fa fo : ℕ → ℕ → ℕ) (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) (a : ℕ) :
    (gs.foldl (stpG fa fo) w).getD a 0
      = rd (w.length + gs.length) (evR fa fo gs w.length w.reverse) a := by
  rw [evR_eq, ← length_fold fa fo, rd_eq]

def stpN (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ := stpG (fun a b => a &&& b) (fun a b => a ||| b) w g

theorem getD_tb (k : ℕ) (W : List ℕ) (i : ℕ) :
    (W.map fun v => v.testBit k).getD i false = (W.getD i 0).testBit k := by
  have h := List.getD_map (f := fun v : ℕ => v.testBit k) (l := W) (d := 0) (n := i)
  simpa using h

theorem bridge (k : ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (W : List ℕ),
    (gs.map toGate).foldl stp (W.map fun v => v.testBit k)
      = (gs.foldl stpN W).map fun v => v.testBit k := by
  intro gs
  induction gs with
  | nil => intro W; rfl
  | cons g gs ih =>
    intro W
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    obtain ⟨b, i, j⟩ := g
    have hi := getD_tb k W i
    have hj := getD_tb k W j
    cases b
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_lor]
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_land]

def tab : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, p => if p = n then (2 ^ 2 ^ n - 1) <<< 2 ^ n else tab n p ||| (tab n p <<< 2 ^ n)

theorem tab_bit : ∀ n p k, p < n →
    (tab n p).testBit k = (decide (k < 2 ^ n) && k.testBit p) := by
  intro n
  induction n with
  | zero => intro p k h; omega
  | succ n ih =>
    intro p k hp
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [tab]
    split_ifs with hpn
    · subst hpn
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hk : k < 2 ^ p
      · rw [Nat.testBit_lt_two_pow hk]
        simp
        omega
      · have hb : k.testBit p = !((k - 2 ^ p).testBit p) := by
          rw [← Nat.testBit_two_pow_add_eq]
          congr 1
          omega
        by_cases hk2 : k - 2 ^ p < 2 ^ p
        · have e0 : decide (k ≥ 2 ^ p) = true := by
            simp only [decide_eq_true_eq]
            omega
          have e1 : decide (k - 2 ^ p < 2 ^ p) = true := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = true := by
            simp only [decide_eq_true_eq]
            omega
          rw [hb, Nat.testBit_lt_two_pow hk2, e0, e1, e2]
          rfl
        · have e1 : decide (k - 2 ^ p < 2 ^ p) = false := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = false := by
            simp only [decide_eq_false_iff_not]
            omega
          rw [e1, e2]
          simp
    · have hp' : p < n := by omega
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft, ih p k hp', ih p (k - 2 ^ n) hp']
      by_cases hk : k < 2 ^ n
      · have e1 : decide (k < 2 ^ n) = true := by simpa using hk
        have e2 : decide (k < 2 ^ (n + 1)) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e3 : decide (k ≥ 2 ^ n) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        rw [e1, e2, e3]
        simp
      · have hb : (k - 2 ^ n).testBit p = k.testBit p := by
          rw [← Nat.testBit_two_pow_add_gt hp' (k - 2 ^ n)]
          congr 1
          omega
        have e1 : decide (k < 2 ^ n) = false := by simpa using hk
        have e3 : decide (k ≥ 2 ^ n) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e4 : decide (k - 2 ^ n < 2 ^ n) = decide (k < 2 ^ (n + 1)) := by
          apply decide_eq_decide.mpr
          omega
        rw [e1, e3, e4, hb]
        simp

def W : List ℕ := (List.range 10).map (tab 10)

theorem W_getD (i : ℕ) : W.getD i 0 = if i < 10 then tab 10 i else 0 := by
  unfold W
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem W_len : W.length = 10 := by simp [W]

theorem G_len : G.length = 20 := by decide +kernel

def E : ℕ := Ed.foldr (fun q acc => (tab 10 q.1 &&& tab 10 q.2) ||| acc) 0

set_option maxRecDepth 100000 in
theorem out0 :
    rd 30 (evR (fun a b => a &&& b) (fun a b => a ||| b) G 10 W.reverse) 29 = E := by
  decide +kernel

theorem out_eq : (G.foldl stpN W).getD 29 0 = E := by
  have h := fold_getD (fun a b => a &&& b) (fun a b => a ||| b) G W 29
  rw [W_len, G_len] at h
  exact h.trans out0

theorem any_bit (k : ℕ) (hk : k < 2 ^ 10) : ∀ L : List (ℕ × ℕ), (∀ q ∈ L, q.1 < 10 ∧ q.2 < 10) →
    (L.foldr (fun q acc => (tab 10 q.1 &&& tab 10 q.2) ||| acc) 0).testBit k
      = L.any (fun q => k.testBit q.1 && k.testBit q.2) := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons q L ih =>
    intro hL
    have hq := hL q List.mem_cons_self
    rw [List.foldr_cons, List.any_cons, Nat.testBit_lor, Nat.testBit_land,
      tab_bit 10 q.1 k (by omega), tab_bit 10 q.2 k (by omega),
      ih (fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')), decide_eq_true hk]
    simp

theorem Ed_lt : ∀ q ∈ Ed, q.1 < 10 ∧ q.2 < 10 := by decide +kernel

theorem len : C0.gates.length = 20 := by
  show (G.map toGate).length = 20
  rw [List.length_map, G_len]

set_option maxRecDepth 100000 in
theorem gatesOK : ∀ p ∈ C0.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 10 + p.2 := by
  decide +kernel

theorem main : ∀ x : Fin 10 → Bool, C0.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
  intro x
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, k < 2 ^ 10 ∧ ∀ (i : ℕ) (h : i < 10), k.testBit i = x ⟨i, h⟩ :=
    ⟨Nat.ofBits x, Nat.ofBits_lt_two_pow x, fun i hi => Nat.testBit_ofBits_lt x i hi⟩
  have hin : List.ofFn x = W.map (fun v => v.testBit k) := by
    refine List.ext_getElem (by simp [W]) (fun i h1 h2 => ?_)
    have h10 : i < 10 := by simpa using h1
    rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2, ofFn_getD, getD_tb,
      W_getD, if_pos h10, tab_bit 10 i k h10, decide_eq_true hk1, Bool.true_and, dif_pos h10,
      hk2 i h10]
  have h0 : k.testBit 0 = x 0 := hk2 0 (by omega)
  have h1 : k.testBit 1 = x 1 := hk2 1 (by omega)
  have h2 : k.testBit 2 = x 2 := hk2 2 (by omega)
  have h3 : k.testBit 3 = x 3 := hk2 3 (by omega)
  have h4 : k.testBit 4 = x 4 := hk2 4 (by omega)
  have h5 : k.testBit 5 = x 5 := hk2 5 (by omega)
  have h6 : k.testBit 6 = x 6 := hk2 6 (by omega)
  have h7 : k.testBit 7 = x 7 := hk2 7 (by omega)
  have h8 : k.testBit 8 = x 8 := hk2 8 (by omega)
  have h9 : k.testBit 9 = x 9 := hk2 9 (by omega)
  rw [eval_eq, hin]
  show ((G.map toGate).foldl stp (W.map fun v => v.testBit k)).getD 29 false = _
  rw [bridge, getD_tb, out_eq]
  show (Ed.foldr (fun q acc => (tab 10 q.1 &&& tab 10 q.2) ||| acc) 0).testBit k = _
  rw [any_bit k hk1 Ed Ed_lt]
  simp only [Ed, List.any_cons, List.any_nil, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    Bool.or_false, Bool.or_assoc]

set_option maxRecDepth 100000 in
theorem full : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], 29⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 20 ∧ C.output = 29 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 10 + p.2) ∧ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
  intro C
  exact ⟨len, rfl, gatesOK, main⟩

end PEqualNP.Outside.L_meta_1755

theorem PEqualNP.Outside.L_meta_1755 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], 29⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 20 ∧ C.output = 29 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 10 + p.2) ∧ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
  exact PEqualNP.Outside.L_meta_1755.full
