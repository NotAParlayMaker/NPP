import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3481

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stp w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stp]; omega

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stp]; omega), stp, List.getD_append _ _ _ _ hi]

theorem eval_input (C : Circuit) (y : List Bool) (h : C.output < y.length) :
    C.eval y = y.getD C.output false :=
  fold_getD_lt C.gates y C.output h

theorem eval_big (C : Circuit) (y : List Bool) (h : y.length + C.size ≤ C.output) :
    C.eval y = false := by
  show (C.gates.foldl stp y).getD C.output false = false
  rw [List.getD_eq_default _ _ (by rw [fold_length]; exact h)]

end PEqualNP.Outside.L_meta_3481

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3481

theorem PEqualNP.Outside.L_meta_3481 : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < x1 ∨ x1 + x4.size ≤ x4.output → (∀ (x12 x13 : Fin x1), x4.eval (List.ofFn fun (x14 : Fin x1) => Decidable.decide (x14 = x12 ∨ x14 = x13)) = Bool.true ↔ x3.Adj x12 x13) → x1 + x2 ≤ x4.size + (1 : ℕ) := by
  intro n t G C hdeg _ _ hcov hmin _ hout hpair
  by_cases hn : n = 0
  · subst hn
    have := hmin ∅ (fun u => Fin.elim0 u)
    simp at this
    omega
  exfalso
  obtain ⟨w, hvw⟩ := hdeg ⟨0, by omega⟩
  rcases hout with ho | ho
  · let i : Fin n := ⟨C.output, ho⟩
    have h := (hpair i i).mp (by
      rw [eval_input C _ (by simpa using ho)]
      simp [List.getD_eq_getElem?_getD, ho, i])
    exact G.irrefl h
  · have h := (hpair ⟨0, by omega⟩ w).mpr hvw
    rw [eval_big C _ (by simpa using ho)] at h
    exact absurd h (by simp)
