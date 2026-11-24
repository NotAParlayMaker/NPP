import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3467

open PEqualNP.CircuitLowerBounds

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_input (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  unfold Circuit.eval Circuit.wires
  exact fold_pre _ _ _ h

end PEqualNP.Outside.L_meta_3467

theorem PEqualNP.Outside.L_meta_3467 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq _ _ _ _ hout _ hfalse
  exfalso
  by_cases hp : C.output < N
  · have h1 := hfalse {⟨C.output, hp⟩} ∅ (by simp) (by intro l hl; simp at hl)
    rw [PEqualNP.Outside.L_meta_3467.eval_input C _
      (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at h1
    simp only [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD] at h1
    rw [List.getElem?_append_left (by simp; omega)] at h1
    simp [hp] at h1
  · have hl : C.output - N < N := by omega
    have h1 := hfalse ∅ {⟨C.output - N, hl⟩} (by simp; omega) (by intro l _; simp)
    rw [PEqualNP.Outside.L_meta_3467.eval_input C _
      (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at h1
    simp only [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD] at h1
    rw [List.getElem?_append_right (by simp; omega)] at h1
    simp [hl] at h1
