import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A cut of L-meta-1676 by output wire: seed vs gate. -/
theorem PEqualNP.Outside.R_meta_1676_9
    (gateOut : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 9 ≤ C.output → 16 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hFan hFirst hFun
  have key : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD i false
          = w.getD i false := by
      intro gs
      induction gs with
      | nil => intro w i hi; rfl
      | cons g gs ih =>
        intro w i hi
        have hstep : (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length
            = w.length + 1 := by simp
        have h1 := ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) i (by omega)
        have h2 : (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD i false
            = w.getD i false := List.getD_append _ _ _ _ hi
        rw [List.foldl_cons]
        exact h1.trans h2
  have eval_seed : ∀ (w : List Bool), C.output < w.length →
      C.eval w = w.getD C.output false := by
    intro w hw
    have h2 := key C.gates w C.output hw
    exact h2
  by_cases h : C.output < 9
  · interval_cases C.output
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 0))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 0)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 0))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 0)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 0)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 0))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 1))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 1)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 1))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 1)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 1)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 1))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 2))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 2)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 2))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 2)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 2)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 2))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 3))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 3)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 3))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 3)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 3)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 3))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 4))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 4)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 4))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 4)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 4)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 4))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 5))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 5)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 5))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 5)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 5)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 5))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 6))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 6)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 6))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 6)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 6)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 6))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 7))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 7)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 7))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 7)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 7)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 7))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
    · exfalso
      have es := eval_seed (List.ofFn (fun j : Fin 9 => decide (j.val = 8))) (by simp)
      have hval : circuitFun 9 C (fun j : Fin 9 => decide (j.val = 8)) = true := by
        show C.eval (List.ofFn (fun j : Fin 9 => decide (j.val = 8))) = true
        rw [es]
        decide
      have hfalse : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 8)) = false := by decide
      have hcontra : (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j : Fin 9 => decide (j.val = 8)) = true := by
        have htmp := congrFun hFun (fun j : Fin 9 => decide (j.val = 8))
        rw [hval] at htmp
        exact htmp.symm
      rw [hcontra] at hfalse
      exact Bool.noConfusion hfalse
  · exact gateOut C hFan hFirst hFun (by omega)
