import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2919
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

end PEqualNP.Outside.L_meta_2919

open PEqualNP.Outside.L_meta_2919 PEqualNP.CircuitLowerBounds in
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
  intro n C j a b op hop hg ha hdc
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  refine ⟨?_, by simp⟩
  funext x
  have h2 : ∀ g : Gate, C.gates.set j g = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    intro g
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  have h1 : C.gates = C.gates.take j ++ ⟨op, [a, b]⟩ :: C.gates.drop (j + 1) := by
    rw [← h2, ← hgj]
    exact (List.set_getElem_self _).symm
  have hWlen : (wf (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hj)]
  have eS : ∀ g : Gate, wf (C.gates.set j g) (List.ofFn x) = wf (C.gates.drop (j + 1))
      (wf (C.gates.take j) (List.ofFn x) ++ [g.op.eval (g.inputs.map fun i => (wf (C.gates.take j) (List.ofFn x)).getD i false)]) := by
    intro g
    rw [h2, wf_append, wf_cons]
  have eC : wf C.gates (List.ofFn x) = wf (C.gates.drop (j + 1))
      (wf (C.gates.take j) (List.ofFn x) ++ [op.eval ([a, b].map fun i => (wf (C.gates.take j) (List.ofFn x)).getD i false)]) := by
    conv_lhs => rw [h1]
    rw [wf_append, wf_cons]
  have hx : (wf C.gates (List.ofFn x)).getD a false = op.eval [] →
      (wf (C.gates.set j ⟨op, []⟩) (List.ofFn x)).getD C.output false
        = (wf C.gates (List.ofFn x)).getD C.output false := hdc x
  show (wf (C.gates.set j ⟨GateOp.or, [a]⟩) (List.ofFn x)).getD C.output false
    = (wf C.gates (List.ofFn x)).getD C.output false
  have hka : (wf C.gates (List.ofFn x)).getD a false = (wf (C.gates.take j) (List.ofFn x)).getD a false := by
    rw [eC, wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)]
  rw [hka, eS] at hx
  rw [eS]
  rw [eC] at hx ⊢
  generalize wf (C.gates.take j) (List.ofFn x) = W at *
  simp only [List.map_cons, List.map_nil] at hx ⊢
  have e1 : GateOp.eval GateOp.or [W.getD a false] = W.getD a false := by simp [GateOp.eval]
  rw [e1]
  rcases hop with h | h <;> subst h
  · cases hva : W.getD a false
    · simp [GateOp.eval]
    · rw [hva] at hx
      have := hx (by simp [GateOp.eval])
      simpa [GateOp.eval] using this
  · cases hva : W.getD a false
    · rw [hva] at hx
      have := hx (by simp [GateOp.eval])
      simpa [GateOp.eval] using this
    · simp [GateOp.eval]
