import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3413_1
    (lower : ¬ HasCircuitSize 9
      (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5) 14)
    (normalize : ∀ (C : Circuit) (b : Bool), FanInTwo C → C.output ≠ 0 →
      (List.filter (fun g : Gate => g.inputs.contains 0) C.gates).length = 1 →
      (∃ g ∈ C.gates, 0 ∈ g.inputs ∧ g.op = GateOp.not) →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
        ∀ x : Fin 9 → Bool, circuitFun 9 D x = circuitFun 9 C
          (fun i : Fin 9 => if i = 0 then b != x 0 else x i)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → (∃ x6 ∈ x1.gates, (0 : ℕ) ∈ x6.inputs ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro C b hfan hsize hunique hnot
  by_contra hcon
  push Not at hcon
  have hout : C.output ≠ 0 := by
    intro ho
    have hhead : ∀ (gs : List Gate) (w : List Bool), w ≠ [] →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD 0 false
          = w.getD 0 false := by
      intro gs
      induction gs with
      | nil => intro w hw; simp
      | cons g gs ih =>
        intro w hw
        calc
          _ = (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD 0 false :=
            ih _ (by simp)
          _ = w.getD 0 false := List.getD_append _ _ _ _ (by cases w <;> simp_all)
    let x : Fin 9 → Bool := fun i => if i = 0 then !b else false
    have hx := hcon x
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn (fun i : Fin 9 => if i = 0 then b != x 0 else x i))).getD C.output false = _ at hx
    rw [ho, hhead C.gates _ (by simp)] at hx
    cases b <;> simp [x] at hx
  obtain ⟨D, hDfan, hDsize, hDeq⟩ := normalize C b hfan hout hunique hnot
  apply lower
  refine ⟨D, hDfan, hDsize.trans hsize, ?_⟩
  intro x
  exact (hDeq x).trans (hcon x)
