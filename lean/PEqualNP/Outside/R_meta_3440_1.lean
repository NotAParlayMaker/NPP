import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3440_1

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def targetFun (x7 : Fin 9 → Bool) : Bool :=
  x7 0 && x7 1 || x7 1 && x7 2 || x7 2 && x7 3 || x7 3 && x7 4 || x7 4 && x7 0 ||
    x7 0 && x7 5 || x7 1 && x7 6 || x7 2 && x7 7 || x7 3 && x7 8 ||
    x7 5 && x7 7 || x7 6 && x7 8 || x7 8 && x7 5

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

theorem main
    (h_adj : ∀ (x1 : Fin 9), (↑x1 = 1 ∨ ↑x1 = 4) → ∀ (x4 : Circuit), Monotone2 x4 → x4.size = 13 →
      11 ≤ x4.output → x4.output < 24 →
      ∃ (x7 : Fin 9 → Bool), x4.eval (List.ofFn x7 ++ [!x7 0, !x7 x1]) ≠ targetFun x7)
    (h_nonadj : ∀ (x1 : Fin 9), (↑x1 = 2 ∨ ↑x1 = 3) → ∀ (x4 : Circuit), Monotone2 x4 → x4.size = 13 →
      11 ≤ x4.output → x4.output < 24 →
      ∃ (x7 : Fin 9 → Bool), x4.eval (List.ofFn x7 ++ [!x7 0, !x7 x1]) ≠ targetFun x7) :
    ∀ (x1 : Fin (9 : ℕ)), (1 : ℕ) ≤ ↑x1 → ↑x1 ≤ (4 : ℕ) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.size = (13 : ℕ) → ∃ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ)), !x7 x1]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1_lo hx1_hi x4 hmon hsz
  by_cases hout11 : x4.output < 11
  · let y0 : Fin 9 → Bool := fun _ => Bool.false
    by_cases hy0 : x4.eval (List.ofFn y0 ++ [!y0 0, !y0 x1]) = Bool.false
    · by_cases h578 : x4.output = 5 ∨ x4.output = 8
      · let y1 : Fin 9 → Bool := fun v => decide (v = 1 ∨ v = 2)
        refine ⟨y1, ?_⟩
        change _ ≠ targetFun y1
        have heval : x4.eval (List.ofFn y0 ++ [!y0 0, !y0 x1]) =
            x4.eval (List.ofFn y1 ++ [!y1 0, !y1 x1]) := by
          simp only [Circuit.eval, Circuit.wires]
          rw [wires_getD_lt x4.gates _ x4.output (by simp [hout11]),
              wires_getD_lt x4.gates _ x4.output (by simp [hout11])]
          rcases h578 with h5 | h8
          · rw [h5]; simp [List.getD_eq_getElem?_getD, y0, y1]
          · rw [h8]; simp [List.getD_eq_getElem?_getD, y0, y1]
        rw [← heval, hy0]
        simp [targetFun, y1]
      · let y1 : Fin 9 → Bool := fun v => decide (v = 5 ∨ v = 8)
        refine ⟨y1, ?_⟩
        change _ ≠ targetFun y1
        have heval : x4.eval (List.ofFn y0 ++ [!y0 0, !y0 x1]) =
            x4.eval (List.ofFn y1 ++ [!y1 0, !y1 x1]) := by
          simp only [Circuit.eval, Circuit.wires]
          rw [wires_getD_lt x4.gates _ x4.output (by simp [hout11]),
              wires_getD_lt x4.gates _ x4.output (by simp [hout11])]
          by_cases h9 : x4.output < 9
          · simp only [List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simp [h9] : x4.output < (List.ofFn y0).length),
              List.getElem?_append_left (by simp [h9] : x4.output < (List.ofFn y1).length),
              List.getElem?_ofFn, dif_pos h9, Option.getD_some]
            simp only [y0, y1]
            rw [decide_eq_false (by simp only [Fin.ext_iff]; exact h578)]
          · have h910 : x4.output = 9 ∨ x4.output = 10 := by omega
            rcases h910 with h9' | h10'
            · rw [h9']
              simp [List.getD_eq_getElem?_getD, y0, y1]
            · rw [h10']
              simp only [List.getD_eq_getElem?_getD,
                List.getElem?_append_right (by simp : (List.ofFn y0).length ≤ 10),
                List.getElem?_append_right (by simp : (List.ofFn y1).length ≤ 10),
                List.length_ofFn, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
              have hy1x : y1 x1 = Bool.false := by
                simp only [y1, decide_eq_false_iff_not, Fin.ext_iff]
                omega
              rw [hy1x]
        rw [← heval, hy0]
        simp [targetFun, y1]
    · refine ⟨y0, ?_⟩
      change _ ≠ targetFun y0
      have hfalse : targetFun y0 = Bool.false := by simp [targetFun, y0]
      rw [hfalse]
      exact hy0
  · by_cases hout_hi : 24 ≤ x4.output
    · refine ⟨fun _ => Bool.true, ?_⟩
      change _ ≠ targetFun (fun _ => Bool.true)
      have heval_false : x4.eval (List.ofFn (fun _ : Fin 9 => Bool.true) ++ [!Bool.true, !Bool.true]) = Bool.false := by
        simp only [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none]
        · rfl
        · rw [wires_length]
          have hglen : x4.gates.length = 13 := hsz
          simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
          omega
      rw [heval_false]
      decide
    · have hout_ge : 11 ≤ x4.output := by omega
      have hout_lt : x4.output < 24 := by omega
      have hcases : (↑x1 = 1 ∨ ↑x1 = 4) ∨ (↑x1 = 2 ∨ ↑x1 = 3) := by omega
      rcases hcases with hadj | hnonadj
      · exact h_adj x1 hadj x4 hmon hsz hout_ge hout_lt
      · exact h_nonadj x1 hnonadj x4 hmon hsz hout_ge hout_lt

end PEqualNP.Outside.R_meta_3440_1
