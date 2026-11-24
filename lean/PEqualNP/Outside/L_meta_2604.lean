import Mathlib
import PEqualNP.Defs

-- The wire lemmas below are those of the merged file L_meta_1004.lean of this repository,
-- with only the namespace changed.

namespace PEqualNP.Outside.L_meta_2604

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

end PEqualNP.Outside.L_meta_2604

open PEqualNP.Outside.L_meta_2604 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2604 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n C j u t _ hj hg ht himp
  funext x
  have hgj : C.gates[j] = ⟨GateOp.or, [u, t]⟩ := by
    obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.mp hg
    exact e
  have h2 : ∀ a : Gate, C.gates.set j a = C.gates.take j ++ a :: C.gates.drop (j + 1) := by
    intro a
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  have h1 : C.gates = C.gates.take j ++ ⟨GateOp.or, [u, t]⟩ :: C.gates.drop (j + 1) := by
    rw [← h2, ← hgj]
    exact (List.set_getElem_self _).symm
  set X := List.ofFn x with hX
  set W := wiresFrom (C.gates.take j) X with hW
  have hWlen : W.length = n + j := by
    rw [hW, length_wiresFrom, hX]
    simp
    omega
  have hw : C.wires X = wiresFrom (C.gates.drop (j + 1)) (W ++ [W.getD u false || W.getD t false]) := by
    rw [wires_eq]
    conv_lhs => rw [h1]
    rw [wiresFrom_append]
    show wiresFrom (C.gates.drop (j + 1)) (W ++ [GateOp.eval GateOp.or ([u, t].map fun i => W.getD i false)]) = _
    simp [GateOp.eval]
  have hw' : wiresFrom (C.gates.set j ⟨GateOp.or, [u]⟩) X
      = wiresFrom (C.gates.drop (j + 1)) (W ++ [W.getD u false]) := by
    rw [h2, wiresFrom_append]
    show wiresFrom (C.gates.drop (j + 1)) (W ++ [GateOp.eval GateOp.or ([u].map fun i => W.getD i false)]) = _
    simp [GateOp.eval]
  have hlen' : (wiresFrom (C.gates.set j ⟨GateOp.or, [u]⟩) X).length = n + C.gates.length := by
    rw [length_wiresFrom, hX]
    simp
  have hval : PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j { op := GateOp.or, inputs := [u] } ++ [{ op := GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } x
      = ((wiresFrom (C.gates.set j ⟨GateOp.or, [u]⟩) X).getD C.output false
        || (wiresFrom (C.gates.set j ⟨GateOp.or, [u]⟩) X).getD t false) := by
    show ((Circuit.wires _ X).getD (n + C.gates.length) false) = _
    rw [wires_eq, wiresFrom_append]
    show ((wiresFrom (C.gates.set j ⟨GateOp.or, [u]⟩) X) ++ [GateOp.eval GateOp.or ([C.output, t].map fun i => (wiresFrom (C.gates.set j ⟨GateOp.or, [u]⟩) X).getD i false)]).getD (n + C.gates.length) false = _
    rw [← hlen', getD_snoc_eq]
    simp [GateOp.eval]
  have htW : ∀ v : Bool, (wiresFrom (C.gates.drop (j + 1)) (W ++ [v])).getD t false = W.getD t false := by
    intro v
    rw [getD_wiresFrom _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
  rw [hval, hw']
  show _ = (C.wires X).getD C.output false
  cases hc : W.getD t false
  · rw [hw, htW, hc]
    simp
  · have ht1 : (C.wires (List.ofFn x)).getD t false = true := by
      rw [← hX, hw, htW, hc]
    have := himp x ht1
    have e : (C.wires X).getD C.output false = true := this
    rw [e, htW, hc]
    simp
