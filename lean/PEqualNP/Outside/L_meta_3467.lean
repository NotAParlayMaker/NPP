import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3467

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun j => acc.getD j false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih _ hlen]
    exact List.getD_append _ _ _ _ hi

lemma eval_input_lt (C : Circuit) (w : List Bool) (ho : C.output < w.length) :
    C.eval w = w.getD C.output false :=
  foldl_getD_lt C.gates w C.output ho

lemma incidenceInput_len {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    (incidenceInput X Y).length = n + m := by
  simp [incidenceInput]

lemma incidenceInput_point {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m))
    (k : ℕ) (hk : k < n) :
    (incidenceInput X Y).getD k false = decide (⟨k, hk⟩ ∈ X) := by
  unfold incidenceInput
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  simp [List.getD_eq_getElem?_getD, hk]

lemma incidenceInput_line {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m))
    (k : ℕ) (hge : n ≤ k) (hlt : k < n + m) :
    (incidenceInput X Y).getD k false = decide (⟨k - n, by omega⟩ ∈ Y) := by
  unfold incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp [hge])]
  simp only [List.length_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hsub : k - n < m := by omega
  simp [hsub]

lemma main_proof
    (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : Circuit)
    (hx1 : 200 ≤ x1)
    (hout : x4.output < x2 + x2)
    (hfalse : ∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 →
      IsFalseInput x3 x12 x13 → x4.eval (incidenceInput x12 x13) = false) :
    x2 * x1 ≤ 100 * x4.size := by
  exfalso
  by_cases hlt : x4.output < x2
  · let p0 : Fin x2 := ⟨x4.output, hlt⟩
    have hf : x4.eval (incidenceInput {p0} (∅ : Finset (Fin x2))) = false :=
      hfalse {p0} ∅ (by simp) (by intro l hl; simp at hl)
    have hev : x4.eval (incidenceInput {p0} (∅ : Finset (Fin x2))) = true := by
      rw [eval_input_lt x4 _ (by rw [incidenceInput_len]; exact hout)]
      rw [incidenceInput_point _ _ x4.output hlt]
      simp [p0]
    rw [hev] at hf
    cases hf
  · have hge : x2 ≤ x4.output := by omega
    let l0 : Fin x2 := ⟨x4.output - x2, by omega⟩
    have hf : x4.eval (incidenceInput (∅ : Finset (Fin x2)) {l0}) = false :=
      hfalse ∅ {l0} (by simp; omega) (by intro l _; exact Finset.disjoint_empty_right _)
    have hev : x4.eval (incidenceInput (∅ : Finset (Fin x2)) {l0}) = true := by
      rw [eval_input_lt x4 _ (by rw [incidenceInput_len]; exact hout)]
      rw [incidenceInput_line _ _ x4.output hge hout]
      simp [l0]
    rw [hev] at hf
    cases hf

end PEqualNP.Outside.L_meta_3467

theorem PEqualNP.Outside.L_meta_3467 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 hx1 _ _ _ _ hout _ hfalse
  exact PEqualNP.Outside.L_meta_3467.main_proof x1 x2 x3 x4 hx1 hout hfalse
