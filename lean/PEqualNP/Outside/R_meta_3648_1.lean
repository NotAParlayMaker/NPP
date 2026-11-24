import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3648_1
    (gateCase : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit), x1.size = (13 : ℕ) → x1.output < (24 : ℕ) → (∀ (x4 : ℕ) (x5 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[x4]? = Option.some x5 → x5.left < (11 : ℕ) + x4 ∧ x5.right < (11 : ℕ) + x4 ∧ ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) → (11 : ℕ) ≤ x1.output → ∃ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Bool.false]) != Bool.false) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))))
    : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit), x1.size = (13 : ℕ) → x1.output < (24 : ℕ) → (∀ (x4 : ℕ) (x5 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[x4]? = Option.some x5 → x5.left < (11 : ℕ) + x4 ∧ x5.right < (11 : ℕ) + x4 ∧ ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) → ∃ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Bool.false]) != Bool.false) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro D hsize hout hgate
  by_cases h : D.output < 11
  · have key : ∀ (gs : List BinaryGate) (w : List Bool) (i : ℕ), i < w.length →
        (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w).getD i false
          = w.getD i false := by
      intro gs
      induction gs with
      | nil => intro w i hi; rfl
      | cons g gs ih =>
        intro w i hi
        have hstep : (w ++ [g.op (w.getD g.left false) (w.getD g.right false)]).length
            = w.length + 1 := by simp
        have h1 := ih (w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) i (by omega)
        have h2 : (w ++ [g.op (w.getD g.left false) (w.getD g.right false)]).getD i false
            = w.getD i false := List.getD_append _ _ _ _ hi
        rw [List.foldl_cons]
        exact h1.trans h2
    have eval_seed : ∀ (w : List Bool), D.output < w.length → D.eval w = w.getD D.output false := by
      intro w hw
      have h2 := key D.gates w D.output hw
      exact h2
    interval_cases D.output
    · refine ⟨fun j : Fin 9 => decide (j.val = 0), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 0)) ++ [(fun j : Fin 9 => decide (j.val = 0)) 0 || (fun j : Fin 9 => decide (j.val = 0)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 1), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 1)) ++ [(fun j : Fin 9 => decide (j.val = 1)) 0 || (fun j : Fin 9 => decide (j.val = 1)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 2), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 2)) ++ [(fun j : Fin 9 => decide (j.val = 2)) 0 || (fun j : Fin 9 => decide (j.val = 2)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 3), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 3)) ++ [(fun j : Fin 9 => decide (j.val = 3)) 0 || (fun j : Fin 9 => decide (j.val = 3)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 4), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 4)) ++ [(fun j : Fin 9 => decide (j.val = 4)) 0 || (fun j : Fin 9 => decide (j.val = 4)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 5), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 5)) ++ [(fun j : Fin 9 => decide (j.val = 5)) 0 || (fun j : Fin 9 => decide (j.val = 5)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 6), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 6)) ++ [(fun j : Fin 9 => decide (j.val = 6)) 0 || (fun j : Fin 9 => decide (j.val = 6)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 7), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 7)) ++ [(fun j : Fin 9 => decide (j.val = 7)) 0 || (fun j : Fin 9 => decide (j.val = 7)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 8), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 8)) ++ [(fun j : Fin 9 => decide (j.val = 8)) 0 || (fun j : Fin 9 => decide (j.val = 8)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 0), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 0)) ++ [(fun j : Fin 9 => decide (j.val = 0)) 0 || (fun j : Fin 9 => decide (j.val = 0)) 4, false]) (by simp)
      rw [es]
      decide
    · refine ⟨fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1), ?_⟩
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1)) ++ [(fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1)) 0 || (fun j : Fin 9 => decide (j.val = 0 ∨ j.val = 1)) 4, false]) (by simp)
      rw [es]
      decide
  · exact gateCase D hsize hout hgate (by omega)
