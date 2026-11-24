import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3481

open PEqualNP.CircuitLowerBounds

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_input (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  unfold Circuit.eval Circuit.wires
  exact fold_pre _ _ _ h

theorem eval_out (C : Circuit) (x : List Bool) (h : x.length + C.size ≤ C.output) :
    C.eval x = false := by
  unfold Circuit.eval Circuit.wires
  apply List.getD_eq_default
  rw [fold_len]
  exact h

end PEqualNP.Outside.L_meta_3481

theorem PEqualNP.Outside.L_meta_3481 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 ∨ x1 + x4.size ≤ x4.output → (∀ (x12 x13 : Fin x1), x4.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x12 ∨ x14 = x13)) = Bool.true ↔ x3.Adj x12 x13) → x1 + x2 ≤ x4.size + (1 : ℕ) := by
  intro n k G C hdeg _ _ hcov _ _ hout hiff
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨S, _, hS⟩ := hcov
    have h1 := S.card_le_univ
    simp only [Fintype.card_fin] at h1
    omega
  · exfalso
    rcases hout with h | h
    · have h2 := hiff ⟨C.output, h⟩ ⟨C.output, h⟩
      rw [PEqualNP.Outside.L_meta_3481.eval_input C _ (by simpa using h)] at h2
      have h3 : (List.ofFn fun (i : Fin n) => decide (i = ⟨C.output, h⟩ ∨ i = ⟨C.output, h⟩)).getD C.output false = true := by
        simp [List.getD_eq_getElem?_getD, h]
      rw [h3] at h2
      exact G.irrefl (h2.mp rfl)
    · obtain ⟨w, hw⟩ := hdeg ⟨0, hn⟩
      have h2 := hiff ⟨0, hn⟩ w
      rw [PEqualNP.Outside.L_meta_3481.eval_out C _ (by simpa using h)] at h2
      exact absurd (h2.mpr hw) (by simp)
