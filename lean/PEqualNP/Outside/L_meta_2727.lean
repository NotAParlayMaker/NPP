import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2727_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma length_foldl_step (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [step]
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega

lemma getD_step (w : List Bool) (g : Gate) {i : ℕ} (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  exact List.getD_append w _ false i hi

lemma getD_foldl_step (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons]
      rw [ih (step w g) (by simp [step]; omega)]
      exact getD_step w g hi

lemma and_eval_eq_left {a b : Bool} (h : a = true → b = true) :
    GateOp.and.eval [a, b] = a := by
  cases a <;> cases b <;> simp_all [GateOp.eval]

lemma or_eval_single (a : Bool) : GateOp.or.eval [a] = a := by
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_2727_aux

open PEqualNP.Outside.L_meta_2727_aux
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_2727 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
      j < C.gates.length →
      C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u, t] } →
      u < n + j → t < n + j →
      (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD u false = true →
          (C.wires (List.ofFn x)).getD t false = true) →
      ∀ x : Fin n → Bool,
        ({ gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] },
           output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) =
        C.wires (List.ofFn x) := by
  intro n C j u t hj hgate hu ht himp x
  let g : Gate := { op := GateOp.and, inputs := [u, t] }
  let g' : Gate := { op := GateOp.or, inputs := [u] }
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hgate
  have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
    simp [List.append_assoc, g]
  have hset : C.gates.set j g' = C.gates.take j ++ g' :: C.gates.drop (j + 1) := by
    exact List.set_eq_take_cons_drop g' hb
  let w := (C.gates.take j).foldl step (List.ofFn x)
  have hw : w.length = n + j := by
    simp [w, length_foldl_step, List.length_take, Nat.min_eq_left hj.le]
  have hC : C.wires (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step w g) := by
    rw [wires_eq, hsplit, List.foldl_append, List.foldl_cons]
    simp [w, List.drop_append, List.drop_take, Nat.min_eq_left hj.le]
  have hC' : ({ gates := C.gates.set j g', output := C.output } : Circuit).wires (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step w g') := by
    rw [wires_eq, hset, List.foldl_append, List.foldl_cons]
  rw [hC, hC']
  have hstep : step w g = step w g' := by
    have hval : w.getD u false = true → w.getD t false = true := by
      intro hvu
      have hfull_u : (C.wires (List.ofFn x)).getD u false = true := by
        rw [hC]
        rw [getD_foldl_step _ _ (by simp [step]; omega)]
        rw [getD_step _ _ (by omega)]
        exact hvu
      have hfull_t := himp x hfull_u
      rw [hC] at hfull_t
      rw [getD_foldl_step _ _ (by simp [step]; omega)] at hfull_t
      rwa [getD_step _ _ (by omega)] at hfull_t
    have h1 : GateOp.and.eval [w.getD u false, w.getD t false] = w.getD u false :=
      and_eval_eq_left hval
    have h2 : GateOp.or.eval [w.getD u false] = w.getD u false :=
      or_eval_single _
    simp [step, g, g']
    change GateOp.and.eval [w.getD u false, w.getD t false] = GateOp.or.eval [w.getD u false]
    rw [h1, h2]
  rw [hstep]
