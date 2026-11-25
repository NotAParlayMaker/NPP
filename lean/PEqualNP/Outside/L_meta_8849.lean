import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8849_aux

open PEqualNP.CircuitLowerBounds

theorem all_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    (l.map f).all id ≤ (l.map g).all id := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a
    simp only [List.map_cons, List.all_cons, id] at ih ⊢
    revert ih ha
    cases f a <;> cases g a <;> cases (t.map f).all id <;> cases (t.map g).all id <;> decide

theorem any_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    (l.map f).any id ≤ (l.map g).any id := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a
    simp only [List.map_cons, List.any_cons, id] at ih ⊢
    revert ih ha
    cases f a <;> cases g a <;> cases (t.map f).any id <;> cases (t.map g).any id <;> decide

theorem step (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool) (hl : w.length = w'.length)
    (hw : ∀ i, w.getD i false ≤ w'.getD i false) :
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false ≤
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD i false := by
  induction gs generalizing w w' with
  | nil => simpa using hw
  | cons g t ih =>
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · have hop := hg g (List.mem_cons_self)
      have hb : g.op.eval (g.inputs.map fun i => w.getD i false) ≤
          g.op.eval (g.inputs.map fun i => w'.getD i false) := by
        rcases hop with h | h
        · rw [h]; simp only [GateOp.eval]; exact all_mono _ _ _ hw
        · rw [h]; simp only [GateOp.eval]; exact any_mono _ _ _ hw
      intro i
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
        exact hw i
      · rw [not_lt] at hi
        rw [List.getD_append_right _ _ _ _ hi, List.getD_append_right _ _ _ _ (hl ▸ hi), hl]
        rcases Nat.eq_zero_or_pos (i - w'.length) with h0 | h0
        · rw [h0]; simpa using hb
        · obtain ⟨k, hk⟩ : ∃ k, i - w'.length = k + 1 := ⟨i - w'.length - 1, by omega⟩
          rw [hk]; simp

end PEqualNP.Outside.L_meta_8849_aux

open PEqualNP.Outside.L_meta_8849_aux in
theorem PEqualNP.Outside.L_meta_8849 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → ∀ (x4 x5 x6 x7 : Finset (Fin x1)), x4 ⊆ x6 → x5 ⊆ x7 → x2.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.true → x2.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true := by
  intro n C hC A B A' B' hA hB h
  have hm := step C.gates hC.1 (PEqualNP.GenericRejection.incidenceInput A B)
    (PEqualNP.GenericRejection.incidenceInput A' B')
    (by simp [PEqualNP.GenericRejection.incidenceInput]) (by
      intro i
      simp only [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD]
      by_cases hi : i < n
      · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_append_left (by simpa using hi)]
        simp only [List.getElem?_ofFn, hi]
        simp
        intro hx; simpa using hA (of_decide_eq_true hx)
      · rw [not_lt] at hi
        rw [List.getElem?_append_right (by simpa using hi), List.getElem?_append_right (by simpa using hi)]
        simp only [List.length_ofFn, List.getElem?_ofFn]
        by_cases hj : i - n < n
        · simp [hj]; intro hx; simpa using hB (of_decide_eq_true hx)
        · simp [hj]) C.output
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at h ⊢
  rw [h] at hm
  revert hm; generalize List.getD _ C.output false = b; cases b <;> simp

