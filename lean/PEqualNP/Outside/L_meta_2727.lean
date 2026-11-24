import Mathlib
import PEqualNP.Defs

-- The wire lemmas below are those of the merged file L_meta_1004.lean of this repository,
-- with only the namespace changed.

namespace PEqualNP.Outside.L_meta_2727

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

end PEqualNP.Outside.L_meta_2727

open PEqualNP.Outside.L_meta_2727 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2727 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
  j < C.gates.length →
  C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u, t] } →
  u < n + j → t < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD u false = true →
      (C.wires (List.ofFn x)).getD t false = true) →
  ∀ x : Fin n → Bool,
    ({ gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] },
       output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) =
    C.wires (List.ofFn x) := by
  intro n C j u t hj hg hu ht himp x
  have hgj : C.gates[j] = ⟨GateOp.and, [u, t]⟩ := by
    obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.mp hg
    exact e
  have h2 : ∀ a : Gate, C.gates.set j a = C.gates.take j ++ a :: C.gates.drop (j + 1) := by
    intro a
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  have h1 : C.gates = C.gates.take j ++ ⟨GateOp.and, [u, t]⟩ :: C.gates.drop (j + 1) := by
    rw [← h2, ← hgj]
    exact (List.set_getElem_self _).symm
  set X := List.ofFn x with hX
  set W := wiresFrom (C.gates.take j) X with hW
  have hWlen : W.length = n + j := by
    rw [hW, length_wiresFrom, hX]
    simp
    omega
  have hw : C.wires X = wiresFrom (C.gates.drop (j + 1)) (W ++ [W.getD u false && W.getD t false]) := by
    rw [wires_eq]
    conv_lhs => rw [h1]
    rw [wiresFrom_append]
    show wiresFrom (C.gates.drop (j + 1)) (W ++ [GateOp.eval GateOp.and ([u, t].map fun i => W.getD i false)]) = _
    simp [GateOp.eval]
  have hw' : wiresFrom (C.gates.set j ⟨GateOp.or, [u]⟩) X
      = wiresFrom (C.gates.drop (j + 1)) (W ++ [W.getD u false]) := by
    rw [h2, wiresFrom_append]
    show wiresFrom (C.gates.drop (j + 1)) (W ++ [GateOp.eval GateOp.or ([u].map fun i => W.getD i false)]) = _
    simp [GateOp.eval]
  have hk : ∀ (v : Bool) (a : ℕ), a < n + j →
      (wiresFrom (C.gates.drop (j + 1)) (W ++ [v])).getD a false = W.getD a false := by
    intro v a ha
    rw [getD_wiresFrom _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
  show wiresFrom (C.gates.set j ⟨GateOp.or, [u]⟩) X = C.wires X
  rw [hw', hw]
  have key : (W.getD u false && W.getD t false) = W.getD u false := by
    cases hc : W.getD u false
    · rfl
    · have h := himp x (by rw [← hX, hw, hk _ u hu]; exact hc)
      rw [← hX, hw, hk _ t ht] at h
      rw [h]
      rfl
  rw [key]
