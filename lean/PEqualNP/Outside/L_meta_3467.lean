import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3467

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

private def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem preserveInput (gates : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (gates.foldl appendGate w).getD i false = w.getD i false := by
  induction gates generalizing w with
  | nil => rfl
  | cons g gates ih =>
    change (gates.foldl appendGate (appendGate w g)).getD i false = w.getD i false
    rw [ih (appendGate w g) (by simp [appendGate]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem evalInput (C : Circuit) {n : ℕ} (X Y : Finset (Fin n))
    (h : C.output < n + n) :
    C.eval (incidenceInput X Y) = (incidenceInput X Y).getD C.output false := by
  unfold Circuit.eval Circuit.wires
  exact preserveInput C.gates (incidenceInput X Y) C.output (by simpa [incidenceInput] using h)

theorem readPoint (C : Circuit) {n : ℕ} (h : C.output < n) :
    C.eval (incidenceInput ({⟨C.output, h⟩} : Finset (Fin n)) (∅ : Finset (Fin n))) = true := by
  rw [evalInput C _ _ (by omega)]
  unfold incidenceInput
  rw [List.getD_append _ _ _ _ (by simpa using h)]
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  simp

theorem readLine (C : Circuit) {n : ℕ} (h : n ≤ C.output) (h' : C.output < n + n) :
    C.eval (incidenceInput (∅ : Finset (Fin n))
      ({⟨C.output - n, by omega⟩} : Finset (Fin n))) = true := by
  rw [evalInput C _ _ h']
  unfold incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simpa using h), List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp

end PEqualNP.Outside.L_meta_3467

open PEqualNP.GenericRejection PEqualNP.Outside.L_meta_3467

theorem PEqualNP.Outside.L_meta_3467 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq _ _ _ _ hout _ hreject
  by_cases hpoint : C.output < n
  · let p : Fin n := ⟨C.output, hpoint⟩
    have hfalse : IsFalseInput S {p} (∅ : Finset (Fin n)) := by simp [IsFalseInput]
    have hzero := hreject {p} ∅ (by simp) hfalse
    have hone := readPoint C hpoint
    change C.eval (incidenceInput {p} (∅ : Finset (Fin n))) = true at hone
    rw [hzero] at hone
    contradiction
  · have hline : n ≤ C.output := Nat.le_of_not_gt hpoint
    let l : Fin n := ⟨C.output - n, by omega⟩
    have hfalse : IsFalseInput S (∅ : Finset (Fin n)) {l} := by simp [IsFalseInput]
    have hcard : ({l} : Finset (Fin n)).card ≤ q := by simpa using (show 1 ≤ q by omega)
    have hzero := hreject ∅ {l} hcard hfalse
    have hone := readLine C hline hout
    change C.eval (incidenceInput (∅ : Finset (Fin n)) {l}) = true at hone
    rw [hzero] at hone
    contradiction
