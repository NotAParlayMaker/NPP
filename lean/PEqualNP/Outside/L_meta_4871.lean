import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4871_aux
open PEqualNP.CircuitLowerBounds

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ h; simpa using h
  | cons g gs ih =>
    intro w1 w2 hl h
    simp only [List.foldl_cons]
    apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    · simp [hl]
    · have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
          g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
        rcases hgs g (List.mem_cons_self) with ho | ho <;> rw [ho] <;> simp only [GateOp.eval]
        · simp only [List.all_eq_true, List.mem_map, id]
          rintro hall _ ⟨a, ha, rfl⟩
          exact h a (hall _ ⟨a, ha, rfl⟩)
        · simp only [List.any_eq_true, List.mem_map, id]
          rintro ⟨_, ⟨a, ha, rfl⟩, hb⟩
          exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩
      intro i hi
      rcases Nat.lt_trichotomy i w1.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h i hi
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp at hi ⊢
        exact hv hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi (by simp)

end PEqualNP.Outside.L_meta_4871_aux

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4871 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → Monotone fun (x3 : Fin (14 : ℕ) → Bool) => x1.eval (List.ofFn x3) := by
  intro C hC x y hxy
  have hxy' : ∀ i, x i = true → y i = true := by
    intro i hi
    have := hxy i
    revert this hi
    cases x i <;> cases y i <;> simp
  show C.eval (List.ofFn x) ≤ C.eval (List.ofFn y)
  have key : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    intro hx
    unfold Circuit.eval Circuit.wires at *
    refine L_meta_4871_aux.fold_mono C.gates hC.1 _ _ (by simp) ?_ _ hx
    intro i hi
    by_cases h : i < 14
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy' _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)
  revert key
  cases C.eval (List.ofFn x) <;> cases C.eval (List.ofFn y) <;> simp
