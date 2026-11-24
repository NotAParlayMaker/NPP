import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3388_1

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def targetFun (x6 : Fin 9 → Bool) : Bool :=
  x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
    x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 ||
    x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5

private lemma targetFun_of_one_two (f : Fin 9 → Bool) (h1 : f 1 = Bool.true) (h2 : f 2 = Bool.true) :
    targetFun f = Bool.true := by
  simp [targetFun, h1, h2]

private lemma wires_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun i => acc[i]?.getD false))]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

private lemma wires_getD_lt (gs : List Gate) (init : List Bool)
    (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map (fun j => acc.getD j false))]) init).getD i false =
      init.getD i false := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (init ++ [_]) (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_triple_agree (x1 : ℕ) (hx1 : x1 = 0 ∨ 9 ≤ x1) (i : ℕ) (hi : i < 11) :
    let y0 : Fin 9 → Bool := fun _ => Bool.false
    let y1' : Fin 9 → Bool :=
      if h9 : i < 9 then (fun v => decide (v ≠ ⟨i, h9⟩)) else (fun v => decide (v ≠ (0 : Fin 9)))
    let t0 := List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false]]
    let t1 := List.ofFn y1' ++ [!y1' 0] ++ [GateOp.not.eval [(List.ofFn y1' ++ [!y1' 0]).getD x1 false]]
    t0.getD i false = t1.getD i false := by
  intro y0 y1' t0 t1
  have hy0 : ∀ v : Fin 9, y0 v = false := fun _ => rfl
  by_cases hi9 : i < 9
  · have hy1' : y1' ⟨i, hi9⟩ = false := by simp [y1', hi9]
    have hlt : i < (List.ofFn y0 ++ [!y0 0]).length := by simp; omega
    have hlt1 : i < (List.ofFn y1' ++ [!y1' 0]).length := by simp; omega
    dsimp only [t0, t1]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_append_left hlt1,
      List.getElem?_append_left (by simp [hi9] : i < (List.ofFn y0).length),
      List.getElem?_append_left (by simp [hi9] : i < (List.ofFn y1').length),
      List.getElem?_ofFn, dif_pos hi9, Option.getD_some]
    rw [hy0 ⟨i, hi9⟩, hy1']
  · have hi_cases : i = 9 ∨ i = 10 := by omega
    have hy1'0 : y1' 0 = false := by simp [y1', hi9]
    rcases hi_cases with rfl | rfl
    · dsimp only [t0, t1]
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp : 9 < (List.ofFn y0 ++ [!y0 0]).length),
        List.getElem?_append_left (by simp : 9 < (List.ofFn y1' ++ [!y1' 0]).length),
        List.getElem?_append_right (by simp : (List.ofFn y0).length ≤ 9),
        List.getElem?_append_right (by simp : (List.ofFn y1').length ≤ 9),
        List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hy0 0, hy1'0]
    · dsimp only [t0, t1]
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp : (List.ofFn y0 ++ [!y0 0]).length ≤ 10),
        List.getElem?_append_right (by simp : (List.ofFn y1' ++ [!y1' 0]).length ≤ 10),
        List.length_append, List.length_ofFn, List.length_singleton, Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      rcases hx1 with rfl | h9
      · simp only [List.getElem?_append_left (by simp : 0 < (List.ofFn y0).length),
          List.getElem?_append_left (by simp : 0 < (List.ofFn y1').length),
          List.getElem?_ofFn, dif_pos (by omega : 0 < 9), Option.getD_some]
        change GateOp.not.eval [y0 0] = GateOp.not.eval [y1' 0]
        rw [hy0 0, hy1'0]
      · by_cases hx9 : x1 = 9
        · subst hx9
          simp only [List.getElem?_append_right (by simp : (List.ofFn y0).length ≤ 9),
            List.getElem?_append_right (by simp : (List.ofFn y1').length ≤ 9),
            List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [hy0 0, hy1'0]
        · have hx10 : 10 ≤ x1 := by omega
          simp only [List.getElem?_append_right (by simp; omega : (List.ofFn y0).length ≤ x1),
            List.getElem?_append_right (by simp; omega : (List.ofFn y1').length ≤ x1),
            List.length_ofFn]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem main
    (h0 : ∀ (x3 : Circuit), FanInTwo x3 → x3.size ≤ 13 → 11 ≤ x3.output → x3.output < 11 + x3.gates.length →
      ∃ (x6 : Fin 9 → Bool),
        have x7 : List Bool := List.ofFn x6 ++ [!x6 0]
        x3.eval (x7 ++ [GateOp.not.eval [x7.getD 0 false]]) ≠ targetFun x6)
    (h9 : ∀ (x3 : Circuit), FanInTwo x3 → x3.size ≤ 13 → 11 ≤ x3.output → x3.output < 11 + x3.gates.length →
      ∃ (x6 : Fin 9 → Bool),
        have x7 : List Bool := List.ofFn x6 ++ [!x6 0]
        x3.eval (x7 ++ [GateOp.not.eval [x7.getD 9 false]]) ≠ targetFun x6)
    (h10 : ∀ (x1 : ℕ), 10 ≤ x1 → ∀ (x3 : Circuit), FanInTwo x3 → x3.size ≤ 13 → 11 ≤ x3.output → x3.output < 11 + x3.gates.length →
      ∃ (x6 : Fin 9 → Bool),
        have x7 : List Bool := List.ofFn x6 ++ [!x6 0]
        x3.eval (x7 ++ [GateOp.not.eval [x7.getD x1 false]]) ≠ targetFun x6) :
    ∀ (x1 : ℕ), x1 = (0 : ℕ) ∨ (9 : ℕ) ≤ x1 → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))]; x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval [x7.getD x1 Bool.false]]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 x3 hfan hsz
  by_cases hout11 : x3.output < 11
  · let y0 : Fin 9 → Bool := fun _ => Bool.false
    let y1 : Fin 9 → Bool :=
      if h9 : x3.output < 9 then (fun v => decide (v ≠ ⟨x3.output, h9⟩)) else (fun v => decide (v ≠ 0))
    have heval : x3.eval (List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false]]) =
        x3.eval (List.ofFn y1 ++ [!y1 0] ++ [GateOp.not.eval [(List.ofFn y1 ++ [!y1 0]).getD x1 false]]) := by
      simp only [Circuit.eval, Circuit.wires]
      rw [wires_getD_lt x3.gates _ x3.output (by simp; omega),
          wires_getD_lt x3.gates _ x3.output (by simp; omega)]
      exact getD_triple_agree x1 hx1 x3.output hout11
    by_cases hy0 : x3.eval (List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false]]) = Bool.false
    · by_cases h12 : x3.output = 1 ∨ x3.output = 2
      · let y2 : Fin 9 → Bool := fun v => decide (v = 0 ∨ v = 3)
        -- Actually if output is 1 or 2, take y_alt where 1,2 are false? No! y0 already has 1,2 false!
        -- Wait: if output = 1, y0 has y0 1 = false, and take y_23 where y 1 = false, y 2 = true, y 3 = true!
        -- Better: in ALL cases where output < 11, pick y_cov : {0..8} \ {x3.output} is a vertex? No!
        -- Pick y2 = fun v => decide (v ≠ ⟨x3.output, ...⟩) ONLY if output ≠ 1 and output ≠ 2!
        -- If output = 1: pick y2 = fun v => decide (v = 2 ∨ v = 3), then y2 1 = false = y0 1, and y2 2 = true, y2 3 = true -> targetFun y2 = true!
        -- If output = 2: pick y2 = fun v => decide (v = 0 ∨ v = 1), then y2 2 = false = y0 2, and y2 0 = true, y2 1 = true -> targetFun y2 = true!
        rcases h12 with h1 | h2
        · let y2 : Fin 9 → Bool := fun v => decide (v = 2 ∨ v = 3)
          refine ⟨y2, ?_⟩
          dsimp only
          change _ ≠ targetFun y2
          have heval2 : x3.eval (List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false]]) =
              x3.eval (List.ofFn y2 ++ [!y2 0] ++ [GateOp.not.eval [(List.ofFn y2 ++ [!y2 0]).getD x1 false]]) := by
            simp only [Circuit.eval, Circuit.wires]
            rw [wires_getD_lt x3.gates _ x3.output (by simp; omega),
                wires_getD_lt x3.gates _ x3.output (by simp; omega), h1]
            simp [List.getD_eq_getElem?_getD, y0, y2]
          rw [← heval2, hy0]
          simp [targetFun, y2]
        · let y2 : Fin 9 → Bool := fun v => decide (v = 0 ∨ v = 1)
          refine ⟨y2, ?_⟩
          dsimp only
          change _ ≠ targetFun y2
          have heval2 : x3.eval (List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false]]) =
              x3.eval (List.ofFn y2 ++ [!y2 0] ++ [GateOp.not.eval [(List.ofFn y2 ++ [!y2 0]).getD x1 false]]) := by
            simp only [Circuit.eval, Circuit.wires]
            rw [wires_getD_lt x3.gates _ x3.output (by simp; omega),
                wires_getD_lt x3.gates _ x3.output (by simp; omega), h2]
            simp [List.getD_eq_getElem?_getD, y0, y2]
          rw [← heval2, hy0]
          simp [targetFun, y2]
      · refine ⟨y1, ?_⟩
        dsimp only
        change _ ≠ targetFun y1
        have hy1_1 : y1 1 = Bool.true := by
          dsimp [y1]
          split_ifs with h9
          · simp only [decide_eq_true_eq, ne_eq, Fin.ext_iff]
            omega
          · decide
        have hy1_2 : y1 2 = Bool.true := by
          dsimp [y1]
          split_ifs with h9
          · simp only [decide_eq_true_eq, ne_eq, Fin.ext_iff]
            omega
          · decide
        rw [← heval, hy0, targetFun_of_one_two y1 hy1_1 hy1_2]
        decide
    · refine ⟨y0, ?_⟩
      dsimp only
      change _ ≠ targetFun y0
      have hfalse : targetFun y0 = Bool.false := by simp [targetFun, y0]
      rw [hfalse]
      exact hy0
  · by_cases hout_hi : 11 + x3.gates.length ≤ x3.output
    · refine ⟨fun _ => Bool.true, ?_⟩
      dsimp only
      change _ ≠ targetFun (fun _ => Bool.true)
      have heval_false : x3.eval (List.ofFn (fun _ : Fin 9 => Bool.true) ++ [!Bool.true] ++
          [GateOp.not.eval [(List.ofFn (fun _ : Fin 9 => Bool.true) ++ [!Bool.true]).getD x1 false]]) = Bool.false := by
        simp only [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none]
        · rfl
        · rw [wires_length]
          simp only [List.length_append, List.length_ofFn, List.length_singleton]
          omega
      rw [heval_false]
      decide
    · have hout_ge : 11 ≤ x3.output := by omega
      have hout_lt : x3.output < 11 + x3.gates.length := by omega
      rcases hx1 with rfl | hge9
      · exact h0 x3 hfan hsz hout_ge hout_lt
      · by_cases hx9 : x1 = 9
        · subst hx9
          exact h9 x3 hfan hsz hout_ge hout_lt
        · exact h10 x1 (by omega) x3 hfan hsz hout_ge hout_lt

end PEqualNP.Outside.R_meta_3388_1
