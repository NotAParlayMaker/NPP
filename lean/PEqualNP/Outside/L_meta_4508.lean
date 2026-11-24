import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4508

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

private lemma foldl_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]) w).getD
      i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private lemma incidence_eval_input {n : ℕ} (C : Circuit) (h : C.output < n + n)
    (X Y : Finset (Fin n)) :
    C.eval (incidenceInput X Y) = (incidenceInput X Y).getD C.output false := by
  exact foldl_getD C.gates _ _ (by simpa [incidenceInput] using h)

end PEqualNP.Outside.L_meta_4508

theorem PEqualNP.Outside.L_meta_4508 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2))
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 →
        ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) →
        PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 →
        x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →
      x2 + x2 + x2 ≤ x4.size + (1 : ℕ) := by
  open PEqualNP.GenericRejection PEqualNP.Outside.L_meta_4508 in
  intro q n S C _ hn hcard _ _ hout hright hreject
  let l : Fin n := ⟨0, by omega⟩
  have hpos : 0 < (S l).card := by rw [hcard]; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hpair := hright l p hp
  exfalso
  by_cases hpoint : C.output < n
  · have hfalse : IsFalseInput S ({p} : Finset (Fin n)) ∅ := by
      simp [IsFalseInput]
    have hsingle := hreject {p} ∅ (by simp) hfalse
    rw [incidence_eval_input C hout] at hpair hsingle
    have hleft : C.output <
        (List.ofFn fun i : Fin n => decide (i ∈ ({p} : Finset (Fin n)))).length := by
      simpa using hpoint
    simp only [incidenceInput, List.getD_eq_getElem?_getD, List.getElem?_append_left hleft]
      at hpair hsingle
    exact Bool.noConfusion (hpair.symm.trans hsingle)
  · have hfalse : IsFalseInput S ∅ ({l} : Finset (Fin n)) := by
      simp [IsFalseInput]
    have hsingle := hreject ∅ {l} (by simp) hfalse
    rw [incidence_eval_input C hout] at hpair hsingle
    have hline : n ≤ C.output := Nat.le_of_not_gt hpoint
    have hrightAppend (f : Fin n → Bool) (ys : List Bool) :
        (List.ofFn f ++ ys)[C.output]? = ys[C.output - n]? := by
      have hlength : (List.ofFn f).length ≤ C.output := by simpa using hline
      rw [List.getElem?_append_right hlength, List.length_ofFn]
    simp only [incidenceInput, List.getD_eq_getElem?_getD, hrightAppend] at hpair hsingle
    exact Bool.noConfusion (hpair.symm.trans hsingle)
