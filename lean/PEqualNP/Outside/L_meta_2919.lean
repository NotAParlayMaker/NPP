import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2919_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma and_const : GateOp.and.eval [] = true := rfl

lemma or_const : GateOp.or.eval [] = false := rfl

lemma and_two (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by
  simp [GateOp.eval]

lemma or_two (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by
  simp [GateOp.eval]

lemma or_one (p : Bool) : GateOp.or.eval [p] = p := by
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_2919_aux

open PEqualNP.Outside.L_meta_2919_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_2919 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j a b : ℕ)
      (op : PEqualNP.CircuitLowerBounds.GateOp),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      C.gates[j]? = some (Gate.mk op [a, b]) →
      a < n + j →
      (∀ x : Fin n → Bool,
          (C.wires (List.ofFn x)).getD a false =
            PEqualNP.CircuitLowerBounds.GateOp.eval op [] →
          PEqualNP.MetaComplexity.circuitFun n
              { gates := C.gates.set j (Gate.mk op []), output := C.output } x =
            PEqualNP.MetaComplexity.circuitFun n C x) →
      PEqualNP.MetaComplexity.circuitFun n
          { gates := C.gates.set j
              { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] },
            output := C.output } =
        PEqualNP.MetaComplexity.circuitFun n C ∧
      (C.gates.set j
        { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] }).length =
        C.gates.length := by
  intro n C j a b op hop hgate ha hdrop
  refine ⟨?_, List.length_set ..⟩
  funext x
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hgate
  have hsplit : C.gates =
      C.gates.take j ++ (Gate.mk op [a, b]) :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
    simp
  have hsetc : C.gates.set j (Gate.mk op []) =
      C.gates.take j ++ (Gate.mk op []) :: C.gates.drop (j + 1) :=
    List.set_eq_take_cons_drop _ hb
  have hsetr : C.gates.set j (Gate.mk GateOp.or [a]) =
      C.gates.take j ++ (Gate.mk GateOp.or [a]) :: C.gates.drop (j + 1) :=
    List.set_eq_take_cons_drop _ hb
  let w := (C.gates.take j).foldl step (List.ofFn x)
  have hw : w.length = n + j := by
    simp [w, length_foldl_step, List.length_take, Nat.min_eq_left hb.le]
  have hC : C.wires (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step w (Gate.mk op [a, b])) := by
    rw [wires_eq, hsplit, List.foldl_append, List.foldl_cons]
    simp [w, List.drop_append, List.drop_take, Nat.min_eq_left hb.le]
  have hCc : (Circuit.mk (C.gates.set j (Gate.mk op [])) C.output).wires
        (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step w (Gate.mk op [])) := by
    rw [wires_eq, hsetc, List.foldl_append, List.foldl_cons]
  have hCr : (Circuit.mk (C.gates.set j (Gate.mk GateOp.or [a])) C.output).wires
        (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step w (Gate.mk GateOp.or [a])) := by
    rw [wires_eq, hsetr, List.foldl_append, List.foldl_cons]
  have hprefix : (C.wires (List.ofFn x)).getD a false = w.getD a false := by
    rw [hC]
    rw [getD_foldl_step _ _ (by simp [step]; omega)]
    rw [getD_step _ _ (by omega)]
  have hdrop' : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD a false = GateOp.eval op [] →
      (Circuit.mk (C.gates.set j (Gate.mk op [])) C.output).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
    intro x hx
    exact hdrop x hx
  change ((Circuit.mk (C.gates.set j (Gate.mk GateOp.or [a])) C.output).wires
      (List.ofFn x)).getD C.output false =
    ((C.wires (List.ofFn x)).getD C.output false)
  rw [hC, hCr]
  rcases hop with rfl | rfl
  · by_cases hv : w.getD a false
    · have hstep : step w (Gate.mk GateOp.or [a]) =
          step w (Gate.mk GateOp.and []) := by
        dsimp only [step]
        simp only [List.map_cons, List.map_nil]
        rw [or_one, and_const, hv]
      have hfull : (C.wires (List.ofFn x)).getD a false = GateOp.and.eval [] := by
        rw [hprefix, hv]
        rfl
      have hd := hdrop' x hfull
      change ((Circuit.mk (C.gates.set j (Gate.mk GateOp.and [])) C.output).wires
          (List.ofFn x)).getD C.output false =
        ((C.wires (List.ofFn x)).getD C.output false) at hd
      rw [hCc, hC] at hd
      rw [hstep]
      exact hd
    · have hv' : w.getD a false = false := by
        cases h : w.getD a false
        · rfl
        · exact absurd h hv
      have hstep : step w (Gate.mk GateOp.or [a]) =
          step w (Gate.mk GateOp.and [a, b]) := by
        dsimp only [step]
        simp only [List.map_cons, List.map_nil]
        rw [or_one, and_two, hv']
        simp only [Bool.false_and]
      rw [hstep]
  · by_cases hv : w.getD a false
    · have hstep : step w (Gate.mk GateOp.or [a]) =
          step w (Gate.mk GateOp.or [a, b]) := by
        dsimp only [step]
        simp only [List.map_cons, List.map_nil]
        rw [or_one, or_two, hv]
        simp only [Bool.true_or]
      rw [hstep]
    · have hv' : w.getD a false = false := by
        cases h : w.getD a false
        · rfl
        · exact absurd h hv
      have hstep : step w (Gate.mk GateOp.or [a]) =
          step w (Gate.mk GateOp.or []) := by
        dsimp only [step]
        simp only [List.map_cons, List.map_nil]
        rw [or_one, or_const, hv']
      have hfull : (C.wires (List.ofFn x)).getD a false = GateOp.or.eval [] := by
        rw [hprefix, hv']
        rfl
      have hd := hdrop' x hfull
      change ((Circuit.mk (C.gates.set j (Gate.mk GateOp.or [])) C.output).wires
          (List.ofFn x)).getD C.output false =
        ((C.wires (List.ofFn x)).getD C.output false) at hd
      rw [hCc, hC] at hd
      rw [hstep]
      exact hd
