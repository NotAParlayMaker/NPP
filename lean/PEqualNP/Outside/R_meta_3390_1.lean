import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3390_1

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def targetFun (x7 : Fin 9 → Bool) : Bool :=
  x7 0 && x7 1 || x7 1 && x7 2 || x7 2 && x7 3 || x7 3 && x7 4 || x7 4 && x7 0 ||
    x7 0 && x7 5 || x7 1 && x7 6 || x7 2 && x7 7 || x7 3 && x7 8 ||
    x7 5 && x7 7 || x7 6 && x7 8 || x7 8 && x7 5

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

private lemma getD_triple_agree (x1 x2 : ℕ) (hx1 : x1 = 0 ∨ 9 ≤ x1) (i : ℕ) (hi : i < 11) :
    let y0 : Fin 9 → Bool := fun _ => Bool.false
    let y1' : Fin 9 → Bool :=
      if h9 : i < 9 then (fun v => decide (v ≠ ⟨i, h9⟩)) else (fun v => decide (v ≠ (0 : Fin 9)))
    let t0 := List.ofFn y0 ++ [!y0 0] ++
      [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false, (List.ofFn y0 ++ [!y0 0]).getD x2 false]]
    let t1 := List.ofFn y1' ++ [!y1' 0] ++
      [GateOp.not.eval [(List.ofFn y1' ++ [!y1' 0]).getD x1 false, (List.ofFn y1' ++ [!y1' 0]).getD x2 false]]
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
        change GateOp.not.eval [y0 0, _] = GateOp.not.eval [y1' 0, _]
        simp [GateOp.eval, hy0 0, hy1'0]
      · by_cases hx9 : x1 = 9
        · subst hx9
          simp only [List.getElem?_append_right (by simp : (List.ofFn y0).length ≤ 9),
            List.getElem?_append_right (by simp : (List.ofFn y1').length ≤ 9),
            List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          simp [GateOp.eval, hy0 0, hy1'0]
        · have hx10 : 10 ≤ x1 := by omega
          simp only [List.getElem?_append_right (by simp; omega : (List.ofFn y0).length ≤ x1),
            List.getElem?_append_right (by simp; omega : (List.ofFn y1').length ≤ x1),
            List.length_ofFn]
          simp [GateOp.eval, hy0 0, hy1'0]

theorem main
    (h0 : ∀ (x2 : ℕ) (x4 : Circuit), FanInTwo x4 → x4.size ≤ 13 → 11 ≤ x4.output → x4.output < 11 + x4.gates.length →
      ∃ (x7 : Fin 9 → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [!x7 0]
        x4.eval (x8 ++ [GateOp.not.eval [x8.getD 0 false, x8.getD x2 false]]) ≠ targetFun x7)
    (h9 : ∀ (x2 : ℕ) (x4 : Circuit), FanInTwo x4 → x4.size ≤ 13 → 11 ≤ x4.output → x4.output < 11 + x4.gates.length →
      ∃ (x7 : Fin 9 → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [!x7 0]
        x4.eval (x8 ++ [GateOp.not.eval [x8.getD 9 false, x8.getD x2 false]]) ≠ targetFun x7)
    (h10 : ∀ (x1 x2 : ℕ), 10 ≤ x1 → ∀ (x4 : Circuit), FanInTwo x4 → x4.size ≤ 13 → 11 ≤ x4.output → x4.output < 11 + x4.gates.length →
      ∃ (x7 : Fin 9 → Bool),
        have x8 : List Bool := List.ofFn x7 ++ [!x7 0]
        x4.eval (x8 ++ [GateOp.not.eval [x8.getD x1 false, x8.getD x2 false]]) ≠ targetFun x7) :
    ∀ (x1 x2 : ℕ), x1 = (0 : ℕ) ∨ (9 : ℕ) ≤ x1 → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]; x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval [x8.getD x1 Bool.false, x8.getD x2 Bool.false]]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 hx1 x4 hfan hsz
  by_cases hout11 : x4.output < 11
  · let y0 : Fin 9 → Bool := fun _ => Bool.false
    let y1 : Fin 9 → Bool :=
      if h9 : x4.output < 9 then (fun v => decide (v ≠ ⟨x4.output, h9⟩)) else (fun v => decide (v ≠ 0))
    have heval : x4.eval (List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false, (List.ofFn y0 ++ [!y0 0]).getD x2 false]]) =
        x4.eval (List.ofFn y1 ++ [!y1 0] ++ [GateOp.not.eval [(List.ofFn y1 ++ [!y1 0]).getD x1 false, (List.ofFn y1 ++ [!y1 0]).getD x2 false]]) := by
      simp only [Circuit.eval, Circuit.wires]
      rw [wires_getD_lt x4.gates _ x4.output (by simp; omega),
          wires_getD_lt x4.gates _ x4.output (by simp; omega)]
      exact getD_triple_agree x1 x2 hx1 x4.output hout11
    by_cases hy0 : x4.eval (List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false, (List.ofFn y0 ++ [!y0 0]).getD x2 false]]) = Bool.false
    · by_cases h12 : x4.output = 1 ∨ x4.output = 2
      · rcases h12 with h1 | h2
        · let y2 : Fin 9 → Bool := fun v => decide (v = 2 ∨ v = 3)
          refine ⟨y2, ?_⟩
          dsimp only
          change _ ≠ targetFun y2
          have heval2 : x4.eval (List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false, (List.ofFn y0 ++ [!y0 0]).getD x2 false]]) =
              x4.eval (List.ofFn y2 ++ [!y2 0] ++ [GateOp.not.eval [(List.ofFn y2 ++ [!y2 0]).getD x1 false, (List.ofFn y2 ++ [!y2 0]).getD x2 false]]) := by
            simp only [Circuit.eval, Circuit.wires]
            rw [wires_getD_lt x4.gates _ x4.output (by simp; omega),
                wires_getD_lt x4.gates _ x4.output (by simp; omega), h1]
            simp [List.getD_eq_getElem?_getD, y0, y2]
          rw [← heval2, hy0]
          simp [targetFun, y2]
        · let y2 : Fin 9 → Bool := fun v => decide (v = 0 ∨ v = 1)
          refine ⟨y2, ?_⟩
          dsimp only
          change _ ≠ targetFun y2
          have heval2 : x4.eval (List.ofFn y0 ++ [!y0 0] ++ [GateOp.not.eval [(List.ofFn y0 ++ [!y0 0]).getD x1 false, (List.ofFn y0 ++ [!y0 0]).getD x2 false]]) =
              x4.eval (List.ofFn y2 ++ [!y2 0] ++ [GateOp.not.eval [(List.ofFn y2 ++ [!y2 0]).getD x1 false, (List.ofFn y2 ++ [!y2 0]).getD x2 false]]) := by
            simp only [Circuit.eval, Circuit.wires]
            rw [wires_getD_lt x4.gates _ x4.output (by simp; omega),
                wires_getD_lt x4.gates _ x4.output (by simp; omega), h2]
            simp [List.getD_eq_getElem?_getD, y0, y2]
          rw [← heval2, hy0]
          simp [targetFun, y2]
      · refine ⟨y1, ?_⟩
        dsimp only
        change _ ≠ targetFun y1
        have hy1_1 : y1 1 = Bool.true := by
          dsimp [y1]
          split_ifs with h9
          · simp only [decide_eq_true_eq, Fin.ext_iff]; omega
          · decide
        have hy1_2 : y1 2 = Bool.true := by
          dsimp [y1]
          split_ifs with h9
          · simp only [decide_eq_true_eq, Fin.ext_iff]; omega
          · decide
        rw [← heval, hy0, targetFun_of_one_two y1 hy1_1 hy1_2]
        decide
    · refine ⟨y0, ?_⟩
      dsimp only
      change _ ≠ targetFun y0
      have hfalse : targetFun y0 = Bool.false := by simp [targetFun, y0]
      rw [hfalse]
      exact hy0
  · by_cases hout_hi : 11 + x4.gates.length ≤ x4.output
    · refine ⟨fun _ => Bool.true, ?_⟩
      dsimp only
      change _ ≠ targetFun (fun _ => Bool.true)
      have heval_false : x4.eval (List.ofFn (fun _ : Fin 9 => Bool.true) ++ [!Bool.true] ++
          [GateOp.not.eval [(List.ofFn (fun _ : Fin 9 => Bool.true) ++ [!Bool.true]).getD x1 false,
            (List.ofFn (fun _ : Fin 9 => Bool.true) ++ [!Bool.true]).getD x2 false]]) = Bool.false := by
        simp only [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none]
        · rfl
        · rw [wires_length]
          simp only [List.length_append, List.length_ofFn, List.length_singleton]
          omega
      rw [heval_false]
      decide
    · have hout_ge : 11 ≤ x4.output := by omega
      have hout_lt : x4.output < 11 + x4.gates.length := by omega
      rcases hx1 with rfl | hge9
      · exact h0 x2 x4 hfan hsz hout_ge hout_lt
      · by_cases hx9 : x1 = 9
        · subst hx9
          exact h9 x2 x4 hfan hsz hout_ge hout_lt
        · exact h10 x1 x2 (by omega) x4 hfan hsz hout_ge hout_lt

end PEqualNP.Outside.R_meta_3390_1
