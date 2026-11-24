import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4029_aux

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem stepW_length (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

theorem stepW_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (stepW w g).getD i false = w.getD i false := by
  unfold stepW
  rw [List.getD_append _ _ _ _ h]

theorem stepW_eq (w : List Bool) (g : Gate) (i : ℕ) (h : i = w.length) :
    (stepW w g).getD i false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold stepW
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [h]

theorem foldl_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [List.foldl_cons, ih, stepW_length]; omega

theorem foldl_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ _ (by rw [stepW_length]; omega), stepW_lt _ _ _ h]

theorem wires_length (C : Circuit) (x : Fin 26 → Bool) :
    (C.wires (List.ofFn x)).length = 26 + C.size := by
  rw [wires_eq, foldl_length]; simp [Circuit.size]

theorem wires_input (C : Circuit) (x : Fin 26 → Bool) (i : Fin 26) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  rw [wires_eq, foldl_prefix _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem or_shuffle (o a b c d : Bool) :
    (a || b || c || d || o) = (o || a || b || c || d) := by
  revert o a b c d; decide

theorem or_eval (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  simp [GateOp.eval]

theorem and_eval (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  simp [GateOp.eval]

theorem prefix_get (w : List Bool) (g : Gate) (i len : ℕ) (hlen : w.length = len)
    (h : i < len) (W : List Bool) (hW : W = stepW w g) :
    W.getD i false = w.getD i false := by
  rw [hW, stepW_lt _ _ _ (by omega)]

theorem new_get (w : List Bool) (g : Gate) (i len : ℕ) (hlen : w.length = len)
    (h : i = len) (W : List Bool) (hW : W = stepW w g) :
    W.getD i false = g.op.eval (g.inputs.map fun j => w.getD j false) := by
  rw [hW, stepW_eq _ _ _ (by omega)]

theorem getElem?_cons_succ {α : Type} (a : α) (l : List α) (n : ℕ) :
    (a :: l)[n + 1]? = l[n]? := rfl

theorem getElem?_cons_zero {α : Type} (a : α) (l : List α) :
    (a :: l)[0]? = some a := rfl

theorem main : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → (26 : ℕ) ≤ x2 → x2 < (26 : ℕ) + x1.size → (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x8.inputs = [x10, x11] ∧ x10 ≠ x11 ∧ x10 < (26 : ℕ) + x7 ∧ x11 < (26 : ℕ) + x7) → (∀ (x8 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x8)).getD x2 Bool.false = (x8 (1 : Fin (26 : ℕ)) || x8 (2 : Fin (26 : ℕ)))) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x9.size ≤ x1.size + (5 : ℕ) ∧ (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x9.gates[x13]? = Option.some x14 → (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 ≠ x17 ∧ x16 < (26 : ℕ) + x13 ∧ x17 < (26 : ℕ) + x13) ∧ x9.output = (26 : ℕ) + x10 ∧ x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x11, x12] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x13 : Fin (26 : ℕ) → Bool), have x14 : List Bool := x9.wires (List.ofFn x13); have x15 : Bool := x1.eval (List.ofFn x13); x14.getD x11 Bool.false = (x15 || x13 (14 : Fin (26 : ℕ))) ∧ x14.getD x12 Bool.false = (x15 || x13 (1 : Fin (26 : ℕ)) || x13 (2 : Fin (26 : ℕ)) || x13 (4 : Fin (26 : ℕ)) || x13 (10 : Fin (26 : ℕ))) ∧ x9.eval (List.ofFn x13) = (x14.getD x11 Bool.false && x14.getD x12 Bool.false) := by
  intro C x2 ho1 ho2 h21 h22 hok hx2
  set n := C.size with hn
  set o := C.output with ho
  let g0 : Gate := ⟨GateOp.or, [x2, 4]⟩
  let g1 : Gate := ⟨GateOp.or, [26 + n, 10]⟩
  let g2 : Gate := ⟨GateOp.or, [26 + n + 1, o]⟩
  let g3 : Gate := ⟨GateOp.or, [o, 14]⟩
  let g4 : Gate := ⟨GateOp.and, [26 + n + 3, 26 + n + 2]⟩
  let extra : List Gate := [g0, g1, g2, g3, g4]
  have hlen : C.gates.length = n := rfl
  have hx24 : x2 ≠ 4 := by omega
  have hn10 : 26 + n ≠ 10 := by omega
  have hn1o : 26 + n + 1 ≠ o := by omega
  have ho14 : o ≠ 14 := by omega
  have h32 : 26 + n + 3 ≠ 26 + n + 2 := by omega
  refine ⟨⟨C.gates ++ extra, 26 + (n + 4)⟩, n + 4, 26 + n + 3, 26 + n + 2,
    ?_, ?_, rfl, ?_, ?_⟩
  · show (C.gates ++ extra).length ≤ n + 5
    simp [extra, hlen]
  · intro j g hg
    by_cases hj : j < n
    · rw [List.getElem?_append_left (by omega)] at hg
      exact hok j g hg
    · rw [List.getElem?_append_right (by omega), hlen] at hg
      obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
      rw [Nat.add_sub_cancel_left] at hg
      unfold extra at hg
      match k with
      | 0 =>
        rw [getElem?_cons_zero] at hg
        cases hg
        exact ⟨Or.inr rfl, x2, 4, rfl, hx24, by omega, by omega⟩
      | 1 =>
        rw [getElem?_cons_succ, getElem?_cons_zero] at hg
        cases hg
        exact ⟨Or.inr rfl, 26 + n, 10, rfl, hn10, by omega, by omega⟩
      | 2 =>
        rw [getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_zero] at hg
        cases hg
        exact ⟨Or.inr rfl, 26 + n + 1, o, rfl, hn1o, by omega, by omega⟩
      | 3 =>
        rw [getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_zero] at hg
        cases hg
        exact ⟨Or.inr rfl, o, 14, rfl, ho14, by omega, by omega⟩
      | 4 =>
        rw [getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_succ,
          getElem?_cons_zero] at hg
        cases hg
        exact ⟨Or.inl rfl, 26 + n + 3, 26 + n + 2, rfl, h32, by omega, by omega⟩
      | k + 5 =>
        rw [getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_succ,
          getElem?_cons_succ] at hg
        cases hg
  · show (C.gates ++ extra)[n + 4]? = some ⟨GateOp.and, [26 + n + 3, 26 + n + 2]⟩
    have hnle : n ≤ n + 4 := by omega
    rw [List.getElem?_append_right hnle, hlen, Nat.add_sub_cancel_left]
    unfold extra
    rw [getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_succ, getElem?_cons_succ,
      getElem?_cons_zero]
  · intro x
    set W0 := C.wires (List.ofFn x) with hW0
    set W1 := stepW W0 g0 with hW1
    set W2 := stepW W1 g1 with hW2
    set W3 := stepW W2 g2 with hW3
    set W4 := stepW W3 g3 with hW4
    set W5 := stepW W4 g4 with hW5
    have hw : Circuit.wires ⟨C.gates ++ extra, 26 + (n + 4)⟩ (List.ofFn x) = W5 := by
      change (C.gates ++ extra).foldl stepW (List.ofFn x) = W5
      rw [List.foldl_append]
      change extra.foldl stepW W0 = W5
      simp [extra, W1, W2, W3, W4, W5]
    have L0 : W0.length = 26 + n := by
      rw [hW0, wires_length]
    have L1 : W1.length = 26 + n + 1 := by
      rw [hW1, stepW_length, L0]
    have L2 : W2.length = 26 + n + 2 := by
      rw [hW2, stepW_length, L1]
    have L3 : W3.length = 26 + n + 3 := by
      rw [hW3, stepW_length, L2]
    have L4 : W4.length = 26 + n + 4 := by
      rw [hW4, stepW_length, L3]
    have L5 : W5.length = 26 + n + 5 := by
      rw [hW5, stepW_length, L4]
    have i4 : W0.getD 4 false = x 4 := by
      rw [hW0]; exact wires_input C x 4
    have i10 : W0.getD 10 false = x 10 := by
      rw [hW0]; exact wires_input C x 10
    have i14 : W0.getD 14 false = x 14 := by
      rw [hW0]; exact wires_input C x 14
    have hev : C.eval (List.ofFn x) = W0.getD o false := by
      rw [hW0]; rfl
    have hx : W0.getD x2 false = (x 1 || x 2) := by
      rw [hW0]; exact hx2 x
    have v0 : W1.getD (26 + n) false = (W0.getD x2 false || x 4) := by
      rw [new_get W0 g0 (26 + n) (26 + n) L0 rfl W1 hW1]
      simp only [g0, List.map_cons, List.map_nil]
      rw [or_eval, i4]
    have v1 : W2.getD (26 + n + 1) false = ((W0.getD x2 false || x 4) || x 10) := by
      rw [new_get W1 g1 (26 + n + 1) (26 + n + 1) L1 rfl W2 hW2]
      simp only [g1, List.map_cons, List.map_nil]
      rw [or_eval]
      have hlt : 10 < 26 + n := by omega
      rw [prefix_get W0 g0 10 (26 + n) L0 hlt W1 hW1, v0, i10]
    have v2 : W3.getD (26 + n + 2) false
        = (((W0.getD x2 false || x 4) || x 10) || W0.getD o false) := by
      rw [new_get W2 g2 (26 + n + 2) (26 + n + 2) L2 rfl W3 hW3]
      simp only [g2, List.map_cons, List.map_nil]
      rw [or_eval, v1]
      have hlt : o < 26 + n := by omega
      rw [prefix_get W1 g1 o (26 + n + 1) L1 (by omega) W2 hW2,
        prefix_get W0 g0 o (26 + n) L0 hlt W1 hW1]
    have v3 : W4.getD (26 + n + 3) false = (W0.getD o false || x 14) := by
      rw [new_get W3 g3 (26 + n + 3) (26 + n + 3) L3 rfl W4 hW4]
      simp only [g3, List.map_cons, List.map_nil]
      rw [or_eval]
      have ho' : o < 26 + n := by omega
      have h14 : 14 < 26 + n := by omega
      rw [prefix_get W2 g2 o (26 + n + 2) L2 (by omega) W3 hW3,
        prefix_get W1 g1 o (26 + n + 1) L1 (by omega) W2 hW2,
        prefix_get W0 g0 o (26 + n) L0 ho' W1 hW1]
      rw [prefix_get W2 g2 14 (26 + n + 2) L2 (by omega) W3 hW3,
        prefix_get W1 g1 14 (26 + n + 1) L1 (by omega) W2 hW2,
        prefix_get W0 g0 14 (26 + n) L0 h14 W1 hW1, i14]
    have w3 : W5.getD (26 + n + 3) false = (W0.getD o false || x 14) := by
      rw [prefix_get W4 g4 (26 + n + 3) (26 + n + 4) L4 (by omega) W5 hW5]
      exact v3
    have w2 : W5.getD (26 + n + 2) false
        = (((W0.getD x2 false || x 4) || x 10) || W0.getD o false) := by
      rw [prefix_get W4 g4 (26 + n + 2) (26 + n + 4) L4 (by omega) W5 hW5,
        prefix_get W3 g3 (26 + n + 2) (26 + n + 3) L3 (by omega) W4 hW4]
      exact v2
    have w4 : W5.getD (26 + (n + 4)) false
        = ((W0.getD o false || x 14) &&
            (((W0.getD x2 false || x 4) || x 10) || W0.getD o false)) := by
      rw [new_get W4 g4 (26 + (n + 4)) (26 + n + 4) L4 (by omega) W5 hW5]
      simp only [g4, List.map_cons, List.map_nil]
      rw [and_eval, v3]
      rw [prefix_get W3 g3 (26 + n + 2) (26 + n + 3) L3 (by omega) W4 hW4, v2]
    refine ⟨?_, ?_, ?_⟩
    · show (Circuit.wires ⟨C.gates ++ extra, 26 + (n + 4)⟩ (List.ofFn x)).getD (26 + n + 3) false
        = (C.eval (List.ofFn x) || x 14)
      rw [hw, w3, hev]
    · show (Circuit.wires ⟨C.gates ++ extra, 26 + (n + 4)⟩ (List.ofFn x)).getD (26 + n + 2) false
        = (C.eval (List.ofFn x) || x 1 || x 2 || x 4 || x 10)
      rw [hw, w2, hev, hx]
      exact or_shuffle _ _ _ _ _
    · show Circuit.eval ⟨C.gates ++ extra, 26 + (n + 4)⟩ (List.ofFn x)
        = ((Circuit.wires ⟨C.gates ++ extra, 26 + (n + 4)⟩ (List.ofFn x)).getD (26 + n + 3) false &&
            (Circuit.wires ⟨C.gates ++ extra, 26 + (n + 4)⟩ (List.ofFn x)).getD (26 + n + 2) false)
      unfold Circuit.eval
      rw [hw, w4, w3, w2]

end PEqualNP.Outside.L_meta_4029_aux

theorem PEqualNP.Outside.L_meta_4029 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → (26 : ℕ) ≤ x2 → x2 < (26 : ℕ) + x1.size → (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x8.inputs = [x10, x11] ∧ x10 ≠ x11 ∧ x10 < (26 : ℕ) + x7 ∧ x11 < (26 : ℕ) + x7) → (∀ (x8 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x8)).getD x2 Bool.false = (x8 (1 : Fin (26 : ℕ)) || x8 (2 : Fin (26 : ℕ)))) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x9.size ≤ x1.size + (5 : ℕ) ∧ (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x9.gates[x13]? = Option.some x14 → (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 ≠ x17 ∧ x16 < (26 : ℕ) + x13 ∧ x17 < (26 : ℕ) + x13) ∧ x9.output = (26 : ℕ) + x10 ∧ x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x11, x12] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x13 : Fin (26 : ℕ) → Bool), have x14 : List Bool := x9.wires (List.ofFn x13); have x15 : Bool := x1.eval (List.ofFn x13); x14.getD x11 Bool.false = (x15 || x13 (14 : Fin (26 : ℕ))) ∧ x14.getD x12 Bool.false = (x15 || x13 (1 : Fin (26 : ℕ)) || x13 (2 : Fin (26 : ℕ)) || x13 (4 : Fin (26 : ℕ)) || x13 (10 : Fin (26 : ℕ))) ∧ x9.eval (List.ofFn x13) = (x14.getD x11 Bool.false && x14.getD x12 Bool.false) :=
  PEqualNP.Outside.L_meta_4029_aux.main
