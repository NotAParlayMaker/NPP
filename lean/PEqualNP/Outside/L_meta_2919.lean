import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2919

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, step]; omega

lemma foldl_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl step w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨_ :: t, by rw [List.foldl_cons, ht, step, List.append_assoc, List.singleton_append]⟩

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma set_eq (gs : List Gate) (j : ℕ) (x : List Bool) (g1 g2 : Gate) (hj : j < gs.length)
    (h : step ((gs.take j).foldl step x) g1 = step ((gs.take j).foldl step x) g2) :
    (gs.set j g1).foldl step x = (gs.set j g2).foldl step x := by
  rw [List.set_eq_take_append_cons_drop, List.set_eq_take_append_cons_drop]
  simp only [hj, ite_true, List.foldl_append, List.foldl_cons, h]

end PEqualNP.Outside.L_meta_2919

theorem PEqualNP.Outside.L_meta_2919 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j a b : ℕ) (op : PEqualNP.CircuitLowerBounds.GateOp),
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
    C.gates.length := by
  intro n C j a b op hop hg ha hyp
  open PEqualNP.Outside.L_meta_2919 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
  refine ⟨?_, by simp⟩
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  have hC : C.gates.set j { op := op, inputs := [a, b] } = C.gates := by
    rw [← hgj]; exact List.set_getElem_self hj
  funext x
  set w0 := (C.gates.take j).foldl step (List.ofFn x) with hw0
  have hlen : w0.length = n + j := by
    rw [hw0, foldl_length]; simp; omega
  have hwa : (C.wires (List.ofFn x)).getD a false = w0.getD a false := by
    rw [wires_eq]
    have e : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j _).symm
    rw [e, List.foldl_append]
    obtain ⟨t, ht⟩ := foldl_prefix (C.gates.drop j) w0
    rw [← hw0, ht]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  have key : ∀ g1 g2 : Gate,
      step w0 g1 = step w0 g2 →
      circuitFun n { gates := C.gates.set j g1, output := C.output } x =
        circuitFun n { gates := C.gates.set j g2, output := C.output } x := by
    intro g1 g2 h
    simp only [circuitFun, Circuit.eval, wires_eq]
    rw [set_eq C.gates j (List.ofFn x) g1 g2 hj h]
  have hCx : circuitFun n C x =
      circuitFun n { gates := C.gates.set j { op := op, inputs := [a, b] }, output := C.output } x := by
    rw [hC]
  rcases hop with rfl | rfl
  · cases hv : w0.getD a false
    · rw [hCx]; apply key; simp only [List.getD_eq_getElem?_getD] at hv; simp [step, hv, GateOp.eval]
    · rw [← hyp x (by rw [hwa, hv]; rfl)]
      apply key; simp only [List.getD_eq_getElem?_getD] at hv; simp [step, hv, GateOp.eval]
  · cases hv : w0.getD a false
    · rw [← hyp x (by rw [hwa, hv]; rfl)]
      apply key; simp only [List.getD_eq_getElem?_getD] at hv; simp [step, hv, GateOp.eval]
    · rw [hCx]; apply key; simp only [List.getD_eq_getElem?_getD] at hv; simp [step, hv, GateOp.eval]
