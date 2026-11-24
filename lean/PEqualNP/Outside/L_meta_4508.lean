import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4508

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

private lemma foldl_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ),
    i < w.length →
    (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)]) w).getD i false =
      w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    change (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)])
      (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])).getD i false = w.getD i false
    rw [ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]

private lemma eval_of_output_lt (C : Circuit) (w : List Bool) (h : C.output < w.length) :
    C.eval w = w.getD C.output false :=
  foldl_getD_lt C.gates w C.output h

private lemma main_contra (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hout : C.output < N + N)
    (hfalse : ∀ (X Y : Finset (Fin N)),
      X.card + Y.card ≤ 3 → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) :
    False := by
  by_cases hlt : C.output < N
  · let p : Fin N := ⟨C.output, hlt⟩
    have hf := hfalse {p} ∅ (by simp) (fun l hl => by simp at hl)
    have hev := eval_of_output_lt C (incidenceInput ({p} : Finset (Fin N)) (∅ : Finset (Fin N)))
      (by simp [incidenceInput, hout])
    rw [hev] at hf
    have htrue : (incidenceInput ({p} : Finset (Fin N)) (∅ : Finset (Fin N))).getD C.output false = true := by
      unfold incidenceInput
      rw [List.getD_append _ _ _ _ (by simp [hlt]),
          List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
      simp [p]
    rw [htrue] at hf
    cases hf
  · let l : Fin N := ⟨C.output - N, by omega⟩
    have hf := hfalse ∅ {l} (by simp) (fun _ _ => Finset.disjoint_empty_right _)
    have hev := eval_of_output_lt C (incidenceInput (∅ : Finset (Fin N)) ({l} : Finset (Fin N)))
      (by simp [incidenceInput, hout])
    rw [hev] at hf
    have htrue : (incidenceInput (∅ : Finset (Fin N)) ({l} : Finset (Fin N))).getD C.output false = true := by
      unfold incidenceInput
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      simp [l]
    rw [htrue] at hf
    cases hf

end PEqualNP.Outside.L_meta_4508

theorem PEqualNP.Outside.L_meta_4508 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 + x2 + x2 ≤ x4.size + (1 : ℕ) := by
  intro q N S C _ _ _ _ _ hout _ hfalse
  exact False.elim (PEqualNP.Outside.L_meta_4508.main_contra N S C hout hfalse)
