import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_196

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

lemma getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

lemma step_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_196

open PEqualNP.Outside.L_meta_196 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hg hh x hne
  have hj : j < C.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg
    exact absurd hg (by simp)
  obtain ⟨pre, post, hsplit, hpre⟩ : ∃ pre post : List Gate,
      C.gates = pre ++ ⟨GateOp.or, [a, h]⟩ :: post ∧ pre.length = j := by
    refine ⟨C.gates.take j, C.gates.drop (j + 1), ?_, by simp; omega⟩
    have e : C.gates[j] = ⟨GateOp.or, [a, h]⟩ := by
      rw [List.getElem?_eq_getElem hj] at hg; exact Option.some.inj hg
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj, e]
  have hset : C.gates.set j ⟨GateOp.or, [a]⟩ = pre ++ ⟨GateOp.or, [a]⟩ :: post := by
    rw [hsplit, ← hpre, List.set_append_right _ _ (le_refl _)]
    simp
  set W := pre.foldl step (List.ofFn x) with hW
  have hWlen : W.length = n + j := by rw [hW, foldl_length]; simp; omega
  have hL : (List.foldl step (List.ofFn x) pre).length = n + j := hWlen
  -- the value of wire h, read before gate j
  have hhC : (C.wires (List.ofFn x)).getD h false = W.getD h false := by
    rw [wires_eq, hsplit, List.foldl_append, List.foldl_cons, foldl_prefix _ _ _ (by
      simp [step, hL]; omega)]
    exact getD_append_lt _ _ _ (by rw [hL]; omega)
  -- the wires of the aliased circuit, before the appended gate
  set W' := (C.gates.set j ⟨GateOp.or, [a]⟩).foldl step (List.ofFn x) with hW'
  have hW'len : W'.length = n + C.size := by
    rw [hW', foldl_length]; simp [Circuit.size]
  have hval : circuitFun n { gates := C.gates.set j ⟨GateOp.or, [a]⟩ ++
      [⟨GateOp.or, [C.output, h]⟩], output := n + C.size } x =
      (W'.getD C.output false || W'.getD h false) := by
    show (Circuit.wires _ (List.ofFn x)).getD (n + C.size) false = _
    rw [wires_eq]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← hW', ← hW'len, step_last]
    simp [GateOp.eval]
  have hhW' : W'.getD h false = W.getD h false := by
    rw [hW', hset, List.foldl_append, List.foldl_cons, foldl_prefix _ _ _ (by
      simp [step, hL]; omega)]
    exact getD_append_lt _ _ _ (by rw [hL]; omega)
  cases hb : W.getD h false
  ·
    left
    have hsame : W' = C.wires (List.ofFn x) := by
      rw [hW', wires_eq, hset, hsplit, List.foldl_append, List.foldl_append, List.foldl_cons,
        List.foldl_cons]
      congr 1
      have hb' : (List.foldl step (List.ofFn x) pre).getD h false = false := hb
      simp only [step, List.map_cons, List.map_nil, hb']
      simp [GateOp.eval]
    intro hC
    apply hne
    rw [hval, hhW', hb, Bool.or_false, hsame]
    exact hC
  · right
    refine ⟨by rw [hhC, hb], ?_⟩
    rw [hval, hhW', hb, Bool.or_true] at hne
    cases hf : f x
    · rfl
    · exact absurd hf.symm hne
