import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1082

lemma eval_mono (op : PEqualNP.CircuitLowerBounds.GateOp)
    (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma fold_mono (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hgs : ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD
          i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).getD
          i false = true := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    have hl' : (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]).length =
        (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]).length := by
      simp [hl]
    have key : ∀ i, (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]).getD i false = true →
        (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]).getD i false = true := by
      intro i hi
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ hl' key

end PEqualNP.Outside.L_meta_1082

theorem PEqualNP.Outside.L_meta_1082 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ x y : List Bool, x.length = n → y.length = n → (∀ i < n, x.getD i false = true → y.getD i false = true) → C.eval x = true → C.eval y = true := by
  intro n C hC x y hx hy hxy h
  have hle : ∀ i, x.getD i false = true → y.getD i false = true := by
    intro i hi
    by_cases hin : i < n
    · exact hxy i hin hi
    · rw [List.getD_eq_default _ _ (by omega)] at hi
      simp at hi
  exact PEqualNP.Outside.L_meta_1082.fold_mono C.gates hC x y (by omega) hle C.output h
