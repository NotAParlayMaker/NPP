import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7676

open PEqualNP.CircuitLowerBounds

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

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

end PEqualNP.Outside.L_meta_7676

theorem PEqualNP.Outside.L_meta_7676 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (21 : ℕ) x1 → ∀ (x3 x4 : Fin (21 : ℕ) → Bool), (∀ (x5 : Fin (21 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true := by
  intro C hC x3 x4 hle k hk
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires at hk ⊢
  refine PEqualNP.Outside.L_meta_7676.fold_mono C.gates hC.1 (List.ofFn x3) (List.ofFn x4) (by simp) ?_ k hk
  intro i hi
  by_cases h : i < 21
  · rw [PEqualNP.Outside.L_meta_7676.ofFn_getD_lt _ _ h] at hi ⊢
    exact hle ⟨i, h⟩ hi
  · rw [PEqualNP.Outside.L_meta_7676.getD_ge_len _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)
