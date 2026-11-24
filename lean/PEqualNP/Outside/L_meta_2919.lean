import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2919

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [step, ih]; omega

lemma read_old_wire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i false = w.getD i false
    rw [ih _ (by simpa [step] using Nat.lt_succ_of_lt hi)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma replace_same_eval (gs : List Gate) (w : List Bool) (j : ℕ) (g h : Gate)
    (same : step ((gs.take j).foldl step w) g = step ((gs.take j).foldl step w) h) :
    (gs.set j g).foldl step w = (gs.set j h).foldl step w := by
  induction gs generalizing w j with
  | nil => simp
  | cons k gs ih =>
    cases j with
    | zero =>
      simpa using congrArg (gs.foldl step) same
    | succ j =>
      simpa using ih (step w k) j (by simpa using same)

end PEqualNP.Outside.L_meta_2919

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2919 in
theorem PEqualNP.Outside.L_meta_2919 :
∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j a b : ℕ) (op : PEqualNP.CircuitLowerBounds.GateOp),
  (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  C.gates[j]? = some { op := op, inputs := [a, b] } →
  a < n + j →
  (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD a false = PEqualNP.CircuitLowerBounds.GateOp.eval op [] →
      PEqualNP.MetaComplexity.circuitFun n
          { gates := C.gates.set j { op := op, inputs := [] }, output := C.output } x =
        PEqualNP.MetaComplexity.circuitFun n C x) →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a] }).length =
    C.gates.length
    := by
  intro n C j a b op hop hgate ha hforce
  refine ⟨?_, by simp⟩
  funext x
  let w := List.ofFn x
  let pre := (C.gates.take j).foldl step w
  let copy : Gate := ⟨.or, [a]⟩
  let force : Gate := ⟨op, []⟩
  let old : Gate := ⟨op, [a, b]⟩
  have hj : j < C.gates.length := by
    rcases Nat.lt_or_ge j C.gates.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hgate
      contradiction
  have haPre : a < pre.length := by
    simp [pre, fold_length, w, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), ha]
  have hread : (C.wires w).getD a false = pre.getD a false := by
    change (C.gates.foldl step w).getD a false = pre.getD a false
    have hsplit : C.gates.foldl step w = (C.gates.drop j).foldl step pre := by
      change C.gates.foldl step w = (C.gates.drop j).foldl step ((C.gates.take j).foldl step w)
      rw [← List.foldl_append, List.take_append_drop]
    rw [hsplit]
    exact read_old_wire _ pre a haPre
  have hcopy (g : Gate) (he : step pre copy = step pre g) :
      circuitFun n ⟨C.gates.set j copy, C.output⟩ x =
        circuitFun n ⟨C.gates.set j g, C.output⟩ x := by
    change ((C.gates.set j copy).foldl step w).getD C.output false =
      ((C.gates.set j g).foldl step w).getD C.output false
    rw [replace_same_eval C.gates w j copy g he]
  have cases_of_copy : step pre copy = step pre old ∨
      (step pre copy = step pre force ∧ pre.getD a false = op.eval []) := by
    rcases hop with rfl | rfl <;> cases hv : pre[a]?.getD false <;>
      simp [copy, old, force, step, GateOp.eval, List.getD_eq_getElem?_getD, hv]
  rcases cases_of_copy with hs | ⟨hs, hv⟩
  · calc
      _ = circuitFun n ⟨C.gates.set j old, C.output⟩ x := hcopy old hs
      _ = _ := by
        have hOld : C.gates[j] = old :=
          Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hgate)
        rw [← hOld, List.set_getElem_self]
  · exact (hcopy force hs).trans (hforce x (hread.trans hv))
