import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_196

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl step w = w ++ t ∧ (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]
      simp [step]
    · rw [List.foldl_cons, hl]
      simp [step]
      omega

lemma getD_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, -⟩ := foldl_step_prefix gs w
  rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

lemma getD_step_prefix (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  rw [step, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

lemma getD_last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp

end PEqualNP.Outside.L_meta_196

theorem PEqualNP.Outside.L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hj hh x hne
  obtain ⟨hjlt, hjg⟩ := List.getElem?_eq_some_iff.1 hj
  set pre := C.gates.take j with hpre
  set suf := C.gates.drop (j + 1) with hsuf
  have hsplit : C.gates = pre ++ ⟨GateOp.or, [a, h]⟩ :: suf := by
    rw [hpre, hsuf, ← hjg, ← List.drop_eq_getElem_cons hjlt, List.take_append_drop]
  have hset : C.gates.set j ⟨GateOp.or, [a]⟩ = pre ++ ⟨GateOp.or, [a]⟩ :: suf := by
    rw [List.set_eq_take_append_cons_drop]
    simp only [hjlt, ↓reduceIte]
    rfl
  have hprelen : pre.length = j := by
    rw [hpre, List.length_take]; omega
  set W0 := pre.foldl PEqualNP.Outside.L_meta_196.step (List.ofFn x) with hW0
  have hW0len : W0.length = n + j := by
    obtain ⟨_, _, hl⟩ := PEqualNP.Outside.L_meta_196.foldl_step_prefix pre (List.ofFn x)
    rw [hW0, hl, List.length_ofFn, hprelen]
  have hCw : C.wires (List.ofFn x) =
      suf.foldl PEqualNP.Outside.L_meta_196.step
        (PEqualNP.Outside.L_meta_196.step W0 ⟨GateOp.or, [a, h]⟩) := by
    rw [PEqualNP.Outside.L_meta_196.wires_eq, hsplit, List.foldl_append, List.foldl_cons]
  set Cw := C.wires (List.ofFn x) with hCwdef
  set W' := suf.foldl PEqualNP.Outside.L_meta_196.step
      (PEqualNP.Outside.L_meta_196.step W0 ⟨GateOp.or, [a]⟩) with hW'
  have hCwlen : Cw.length = n + C.size := by
    obtain ⟨_, _, hl⟩ := PEqualNP.Outside.L_meta_196.foldl_step_prefix C.gates (List.ofFn x)
    rw [hCwdef, PEqualNP.Outside.L_meta_196.wires_eq, hl, List.length_ofFn]
    rfl
  have hhW0 : h < W0.length := by omega
  have hCwh : Cw.getD h false = W0.getD h false := by
    rw [hCw, PEqualNP.Outside.L_meta_196.getD_prefix _ _ _ (by simp [PEqualNP.Outside.L_meta_196.step]; omega),
      PEqualNP.Outside.L_meta_196.getD_step_prefix _ _ _ hhW0]
  have hW'h : W'.getD h false = W0.getD h false := by
    rw [hW', PEqualNP.Outside.L_meta_196.getD_prefix _ _ _ (by simp [PEqualNP.Outside.L_meta_196.step]; omega),
      PEqualNP.Outside.L_meta_196.getD_step_prefix _ _ _ hhW0]
  have hW'len : W'.length = n + C.size := by
    obtain ⟨_, _, hl⟩ := PEqualNP.Outside.L_meta_196.foldl_step_prefix suf
      (PEqualNP.Outside.L_meta_196.step W0 ⟨GateOp.or, [a]⟩)
    obtain ⟨_, _, hl2⟩ := PEqualNP.Outside.L_meta_196.foldl_step_prefix suf
      (PEqualNP.Outside.L_meta_196.step W0 ⟨GateOp.or, [a, h]⟩)
    rw [hW', hl, ← hCwlen, hCw, hl2]
    simp [PEqualNP.Outside.L_meta_196.step]
  have hnew : PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨GateOp.or, [a]⟩ ++ [⟨GateOp.or, [C.output, h]⟩], output := n + C.size } x =
(W'.getD C.output false || W'.getD h false) := by
    show (Circuit.wires _ (List.ofFn x)).getD (n + C.size) false = _
    rw [PEqualNP.Outside.L_meta_196.wires_eq]
    simp only
    rw [hset, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, ← hW']
    rw [PEqualNP.Outside.L_meta_196.step, ← hW'len, PEqualNP.Outside.L_meta_196.getD_last]
    simp [GateOp.eval]
  have hold : PEqualNP.MetaComplexity.circuitFun n C x = Cw.getD C.output false := rfl
  rw [hnew] at hne
  rw [hold, hCwh]
  cases hb : W0.getD h false with
  | false =>
    left
    have hsame : PEqualNP.Outside.L_meta_196.step W0 ⟨GateOp.or, [a]⟩ =
        PEqualNP.Outside.L_meta_196.step W0 ⟨GateOp.or, [a, h]⟩ := by
      have hb' : W0[h]?.getD false = false := by rw [← List.getD_eq_getElem?_getD]; exact hb
      simp [PEqualNP.Outside.L_meta_196.step, GateOp.eval, hb']
    have : W' = Cw := by rw [hW', hsame, hCw]
    rw [hW'h, hb, this] at hne
    simpa using hne
  | true =>
    right
    refine ⟨rfl, ?_⟩
    rw [hW'h, hb, Bool.or_true] at hne
    cases hf : f x
    · rfl
    · exact absurd hf.symm hne
