import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2919_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem pre (B : List Gate) : ∀ W : List Bool, ∃ T : List Bool, B.foldl step W = W ++ T := by
  induction B with
  | nil => intro W; exact ⟨[], by simp⟩
  | cons g B ih =>
    intro W
    obtain ⟨T, h⟩ := ih (step W g)
    exact ⟨[g.op.eval (g.inputs.map fun i => W.getD i false)] ++ T, by
      rw [List.foldl_cons, h]; simp [step]⟩

theorem pre2 (B : List Gate) (W : List Bool) (g : Gate) :
    ∃ T : List Bool, B.foldl step (step W g) = W ++ T := by
  obtain ⟨T, h⟩ := pre B (step W g)
  exact ⟨[g.op.eval (g.inputs.map fun i => W.getD i false)] ++ T, by rw [h]; simp [step]⟩

theorem swap (A B : List Gate) (g1 g2 : Gate) (x : List Bool)
    (h : g1.op.eval (g1.inputs.map fun i => (A.foldl step x).getD i false) =
      g2.op.eval (g2.inputs.map fun i => (A.foldl step x).getD i false)) :
    (A ++ g1 :: B).foldl step x = (A ++ g2 :: B).foldl step x := by
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  congr 1
  simp only [step]
  rw [h]

end PEqualNP.Outside.L_meta_2919_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2919_aux in
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
  rintro n ⟨gs, out⟩ j a b op hop hg ha hyp
  replace hg : gs[j]? = some ⟨op, [a, b]⟩ := hg
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  refine ⟨?_, by simp⟩
  funext x
  have hdec : gs = gs.take j ++ ⟨op, [a, b]⟩ :: gs.drop (j + 1) := by
    rw [← hgj, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hset : ∀ g : Gate, gs.set j g = gs.take j ++ g :: gs.drop (j + 1) := by
    intro g
    rw [List.set_eq_take_append_cons_drop, if_pos hj]
  have hW : ((gs.take j).foldl step (List.ofFn x)).length = n + j := by
    rw [fold_len]
    simp
    omega
  have hfold : gs.foldl step (List.ofFn x) =
      (gs.take j ++ ⟨op, [a, b]⟩ :: gs.drop (j + 1)).foldl step (List.ofFn x) :=
    congrArg (fun l => l.foldl step (List.ofFn x)) hdec
  have hwa : (gs.foldl step (List.ofFn x)).getD a false =
      ((gs.take j).foldl step (List.ofFn x)).getD a false := by
    obtain ⟨T, hT⟩ := pre2 (gs.drop (j + 1)) ((gs.take j).foldl step (List.ofFn x)) ⟨op, [a, b]⟩
    rw [hfold, List.foldl_append, List.foldl_cons, hT, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  show ((gs.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x)).getD out false =
    (gs.foldl step (List.ofFn x)).getD out false
  by_cases hc : ((gs.take j).foldl step (List.ofFn x)).getD a false = op.eval []
  · have h1 : ((gs.set j ⟨op, []⟩).foldl step (List.ofFn x)).getD out false =
        (gs.foldl step (List.ofFn x)).getD out false :=
      hyp x (by
        show (gs.foldl step (List.ofFn x)).getD a false = _
        rw [hwa]
        exact hc)
    rw [← h1, hset, hset]
    congr 1
    apply swap
    simpa [GateOp.eval] using hc
  · rw [hset, hfold]
    congr 1
    apply swap
    clear hdec hset hfold hwa hyp hg hgj
    rcases hop with rfl | rfl
    · cases h : ((gs.take j).foldl step (List.ofFn x)).getD a false <;>
        simp_all [GateOp.eval]
    · cases h : ((gs.take j).foldl step (List.ofFn x)).getD a false <;>
        simp_all [GateOp.eval]
