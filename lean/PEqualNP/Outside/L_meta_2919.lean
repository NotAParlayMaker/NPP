import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2919_aux

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

theorem run_append (p s : List Gate) (w : List Bool) : run (p ++ s) w = run s (run p w) := by
  simp only [run, Circuit.wires, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp
    omega

theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem wires_set (gs : List Gate) (j : ℕ) (g' : Gate) (hj : j < gs.length) (out : ℕ)
    (w : List Bool) :
    (Circuit.mk (gs.set j g') out).wires w = run (gs.drop (j + 1))
      (run (gs.take j) w ++ [g'.op.eval (g'.inputs.map fun i => (run (gs.take j) w).getD i false)]) := by
  rw [List.set_eq_take_cons_drop _ hj]
  change run _ w = _
  rw [run_append, run_cons]

theorem wires_self (C : Circuit) (j : ℕ) (g : Gate) (h : C.gates[j]? = some g)
    (w : List Bool) :
    C.wires w = run (C.gates.drop (j + 1))
      (run (C.gates.take j) w ++ [g.op.eval (g.inputs.map fun i => (run (C.gates.take j) w).getD i false)]) := by
  obtain ⟨hj, hg⟩ := List.getElem?_eq_some_iff.1 h
  rw [← wires_set C.gates j g hj C.output w]
  rw [← hg, List.set_getElem_self]

end PEqualNP.Outside.L_meta_2919_aux

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
    C.gates.length := by
  intro n C j a b op hop hg ha hyp
  refine ⟨?_, List.length_set⟩
  funext x
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 hg
  have hW : (L_meta_2919_aux.run (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [L_meta_2919_aux.run_length, List.length_take, List.length_ofFn]
    omega
  have hA : (C.wires (List.ofFn x)).getD a false =
      (L_meta_2919_aux.run (C.gates.take j) (List.ofFn x)).getD a false := by
    rw [L_meta_2919_aux.wires_self C j _ hg, L_meta_2919_aux.run_preserves _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by omega)]
  have h1 : circuitFun n (Circuit.mk (C.gates.set j (Gate.mk GateOp.or [a])) C.output) x = (L_meta_2919_aux.run (C.gates.drop (j + 1))
        (L_meta_2919_aux.run (C.gates.take j) (List.ofFn x) ++
          [(L_meta_2919_aux.run (C.gates.take j) (List.ofFn x)).getD a false])).getD C.output false := by
    unfold circuitFun Circuit.eval
    rw [L_meta_2919_aux.wires_set _ _ _ hj]
    simp [GateOp.eval]
  have h0 : circuitFun n (Circuit.mk (C.gates.set j (Gate.mk op [])) C.output) x = (L_meta_2919_aux.run (C.gates.drop (j + 1))
        (L_meta_2919_aux.run (C.gates.take j) (List.ofFn x) ++
          [op.eval []])).getD C.output false := by
    unfold circuitFun Circuit.eval
    rw [L_meta_2919_aux.wires_set _ _ _ hj]
    simp
  have hc : circuitFun n C x = (L_meta_2919_aux.run (C.gates.drop (j + 1))
        (L_meta_2919_aux.run (C.gates.take j) (List.ofFn x) ++
          [op.eval [(L_meta_2919_aux.run (C.gates.take j) (List.ofFn x)).getD a false,
            (L_meta_2919_aux.run (C.gates.take j) (List.ofFn x)).getD b false]])).getD C.output false := by
    unfold circuitFun Circuit.eval
    rw [L_meta_2919_aux.wires_self C j _ hg]
    simp
  have key := hyp x
  rw [hA] at key
  rw [h0, hc] at key
  rw [h1, hc]
  generalize (L_meta_2919_aux.run (C.gates.take j) (List.ofFn x)).getD a false = va at key ⊢
  rcases hop with rfl | rfl <;> cases va <;> simp_all [GateOp.eval]
