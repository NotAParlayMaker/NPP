import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_196

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_def (w : List Bool) (g : Gate) :
    step w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

private lemma step_length (w : List Bool) (g : Gate) :
    (step w g).length = w.length + 1 := by
  simp [step]

private lemma foldl_length : ∀ (l : List Gate) (w : List Bool),
    (l.foldl step w).length = w.length + l.length
  | [], w => by simp
  | g :: t, w => by
      rw [List.foldl_cons, foldl_length t (step w g), step_length]
      simp
      omega

private lemma foldl_getD_lt : ∀ (l : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (l.foldl step w).getD i false = w.getD i false
  | [], w, i, _ => rfl
  | g :: t, w, i, hi => by
      rw [List.foldl_cons]
      rw [foldl_getD_lt t (step w g) i (by rw [step_length]; omega)]
      rw [step_def]
      exact List.getD_append w _ false i hi

private lemma foldl_getD_stable (l₁ l₂ : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < (l₁.foldl step w).length) :
    ((l₁ ++ l₂).foldl step w).getD i false = (l₁.foldl step w).getD i false := by
  rw [List.foldl_append]
  exact foldl_getD_lt l₂ (l₁.foldl step w) i hi

private lemma foldl_set_eq : ∀ (l : List Gate) (j : ℕ) (g g' : Gate) (w : List Bool),
    l[j]? = some g →
    step ((l.take j).foldl step w) g = step ((l.take j).foldl step w) g' →
    (l.set j g').foldl step w = l.foldl step w
  | [], j, g, g', w, hj, _ => by simp at hj
  | g0 :: t, 0, g, g', w, hj, hval => by
      rw [List.getElem?_cons_zero] at hj
      injection hj with hgeq
      subst hgeq
      simp only [List.take_zero, List.foldl_nil] at hval
      simp only [List.set_cons_zero, List.foldl_cons, List.foldl_nil]
      rw [hval]
  | g0 :: t, j + 1, g, g', w, hj, hval => by
      rw [List.getElem?_cons_succ] at hj
      have ih := foldl_set_eq t j g g' (step w g0) hj (by
        simpa [List.take_succ_cons, List.foldl_cons] using hval)
      rw [List.set_cons_succ, List.foldl_cons, List.foldl_cons]
      exact ih

private lemma getD_set_lt : ∀ (l : List Gate) (j i : ℕ) (g g' : Gate) (w : List Bool),
    l[j]? = some g → i < w.length + j →
    ((l.set j g').foldl step w).getD i false = (l.foldl step w).getD i false
  | [], j, i, g, g', w, hj, _ => by simp at hj
  | g0 :: t, 0, i, g, g', w, hj, hi => by
      rw [List.getElem?_cons_zero] at hj
      injection hj with hgeq
      subst hgeq
      rw [List.set_cons_zero, List.foldl_cons, List.foldl_cons]
      rw [foldl_getD_lt t (step w g') i (by rw [step_length]; omega)]
      rw [foldl_getD_lt t (step w g0) i (by rw [step_length]; omega)]
      rw [step_def, step_def]
      rw [List.getD_append w _ false i (by simpa using hi)]
      rw [List.getD_append w _ false i (by simpa using hi)]
  | g0 :: t, j + 1, i, g, g', w, hj, hi => by
      rw [List.getElem?_cons_succ] at hj
      rw [List.set_cons_succ, List.foldl_cons, List.foldl_cons]
      exact getD_set_lt t j i g g' (step w g0) hj (by rw [step_length]; omega)

private lemma or_eval_two (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by
  show [p, q].any id = (p || q)
  simp

private lemma or_eval_one (p : Bool) : GateOp.or.eval [p] = p := by
  show [p].any id = p
  simp

private lemma step_or_of_getD (w : List Bool) (a h : ℕ) (hh : w.getD h false = false) :
    step w ⟨GateOp.or, [a, h]⟩ = step w ⟨GateOp.or, [a]⟩ := by
  show w ++ [GateOp.or.eval [w.getD a false, w.getD h false]] =
    w ++ [GateOp.or.eval [w.getD a false]]
  rw [or_eval_two, or_eval_one, hh]
  simp

private lemma or_gate_val_true (w : List Bool) (o h : ℕ) (hh : w.getD h false = true) :
    (⟨GateOp.or, [o, h]⟩ : Gate).op.eval
      ((⟨GateOp.or, [o, h]⟩ : Gate).inputs.map fun i => w.getD i false) = true := by
  show GateOp.or.eval [w.getD o false, w.getD h false] = true
  rw [or_eval_two, hh]
  simp

private lemma or_gate_val_false (w : List Bool) (o h : ℕ) (hh : w.getD h false = false) :
    (⟨GateOp.or, [o, h]⟩ : Gate).op.eval
      ((⟨GateOp.or, [o, h]⟩ : Gate).inputs.map fun i => w.getD i false) = w.getD o false := by
  show GateOp.or.eval [w.getD o false, w.getD h false] = w.getD o false
  rw [or_eval_two, hh]
  simp

private lemma wires_length (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.size := by
  show (C.gates.foldl step w).length = w.length + C.gates.length
  rw [foldl_length]

end PEqualNP.Outside.L_meta_196

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_196 :
    ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool),
      C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ →
      h < n + j →
      ∀ x : Fin n → Bool,
        PEqualNP.MetaComplexity.circuitFun n
          { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++
              [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x →
        PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨
          ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hj hh x hne
  let w : List Bool := List.ofFn x
  have hw : w.length = n := List.length_ofFn
  let gj : Gate := ⟨GateOp.or, [a, h]⟩
  let g0 : Gate := ⟨GateOp.or, [a]⟩
  let g1 : Gate := ⟨GateOp.or, [C.output, h]⟩
  let C' : Circuit := { gates := C.gates.set j g0 ++ [g1], output := n + C.size }
  have hC'def : C' = { gates := C.gates.set j g0 ++ [g1], output := n + C.size } := rfl
  have hj' : C.gates[j]? = some gj := hj
  obtain ⟨hjlt, hjget⟩ := List.getElem?_eq_some_iff.mp hj'
  by_cases hh1 : (C.wires w).getD h false = true
  · right
    refine ⟨hh1, ?_⟩
    have hpref : ((C.gates.set j g0).foldl PEqualNP.Outside.L_meta_196.step w).getD h false = true := by
      rw [PEqualNP.Outside.L_meta_196.getD_set_lt C.gates j h gj g0 w hj' (by rw [hw]; exact hh)]
      exact hh1
    have hval : PEqualNP.MetaComplexity.circuitFun n C' x = true := by
      show (C'.wires w).getD (n + C.size) false = true
      have hsetlen : ((C.gates.set j g0).foldl PEqualNP.Outside.L_meta_196.step w).length =
          n + C.size := by
        rw [PEqualNP.Outside.L_meta_196.foldl_length, hw]
        simp [PEqualNP.CircuitLowerBounds.Circuit.size]
      have hwires' : C'.wires w =
          (C.gates.set j g0).foldl PEqualNP.Outside.L_meta_196.step w ++
            [(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩ : Gate).op.eval
              ((⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩ : Gate).inputs.map fun i =>
                ((C.gates.set j g0).foldl PEqualNP.Outside.L_meta_196.step w).getD i false)] := by
        rw [hC'def]
        show (C.gates.set j g0 ++ [g1]).foldl PEqualNP.Outside.L_meta_196.step w =
          (C.gates.set j g0).foldl PEqualNP.Outside.L_meta_196.step w ++
            [g1.op.eval (g1.inputs.map fun i =>
              ((C.gates.set j g0).foldl PEqualNP.Outside.L_meta_196.step w).getD i false)]
        rw [List.foldl_append]
        rfl
      rw [hwires', List.getD_append_right _ _ _ _ (by rw [hsetlen])]
      rw [show n + C.size - ((C.gates.set j g0).foldl PEqualNP.Outside.L_meta_196.step w).length = 0
        by omega]
      simp only [List.getD_cons_zero, List.getD_nil]
      exact PEqualNP.Outside.L_meta_196.or_gate_val_true _ C.output h hpref
    cases hfx : f x with
    | false => rfl
    | true =>
        exfalso
        exact hne (by rw [hval, hfx])
  · left
    have hfalse : (C.wires w).getD h false = false := by
      cases hv : (C.wires w).getD h false with
      | false => rfl
      | true => exact absurd hv hh1
    have hpref_len : ((C.gates.take j).foldl PEqualNP.Outside.L_meta_196.step w).length = n + j := by
      rw [PEqualNP.Outside.L_meta_196.foldl_length, List.length_take, hw,
        Nat.min_eq_left (Nat.le_of_lt hjlt)]
    have hpref_h : ((C.gates.take j).foldl PEqualNP.Outside.L_meta_196.step w).getD h false = false := by
      have hs := PEqualNP.Outside.L_meta_196.foldl_getD_stable (C.gates.take j) (C.gates.drop j) w h
        (by rw [hpref_len]; omega)
      rw [List.take_append_drop] at hs
      exact hs.symm.trans hfalse
    have hseteq : (C.gates.set j g0).foldl PEqualNP.Outside.L_meta_196.step w =
        C.gates.foldl PEqualNP.Outside.L_meta_196.step w := by
      refine PEqualNP.Outside.L_meta_196.foldl_set_eq C.gates j gj g0 w hj' ?_
      exact PEqualNP.Outside.L_meta_196.step_or_of_getD _ a h hpref_h
    have hC'w : C'.wires w = C.wires w ++ [PEqualNP.MetaComplexity.circuitFun n C x] := by
      rw [hC'def]
      show (C.gates.set j g0 ++ [g1]).foldl PEqualNP.Outside.L_meta_196.step w =
        C.wires w ++ [PEqualNP.MetaComplexity.circuitFun n C x]
      rw [List.foldl_append, hseteq]
      show (C.gates.foldl PEqualNP.Outside.L_meta_196.step w) ++
          [g1.op.eval (g1.inputs.map fun i =>
            (C.gates.foldl PEqualNP.Outside.L_meta_196.step w).getD i false)] =
        C.wires w ++ [PEqualNP.MetaComplexity.circuitFun n C x]
      rw [show g1.op.eval (g1.inputs.map fun i =>
            (C.gates.foldl PEqualNP.Outside.L_meta_196.step w).getD i false) =
          PEqualNP.MetaComplexity.circuitFun n C x from
        PEqualNP.Outside.L_meta_196.or_gate_val_false (C.wires w) C.output h hfalse]
      rfl
    have hC'eq : PEqualNP.MetaComplexity.circuitFun n C' x =
        PEqualNP.MetaComplexity.circuitFun n C x := by
      show (C'.wires w).getD (n + C.size) false = (C.wires w).getD C.output false
      rw [hC'w]
      have hlen : (C.wires w).length = n + C.size := by
        rw [PEqualNP.Outside.L_meta_196.wires_length, hw]
      rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
      rw [show n + C.size - (C.wires w).length = 0 by omega]
      simp only [List.getD_cons_zero]
      show PEqualNP.MetaComplexity.circuitFun n C x = (C.wires w).getD C.output false
      rfl
    intro hcontra
    exact hne (hC'eq.trans hcontra)
