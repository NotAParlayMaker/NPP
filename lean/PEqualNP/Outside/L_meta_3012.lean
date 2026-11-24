import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_3012 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : (Fin x1 → Bool) → Bool), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ (x5 : Fin x1 → Bool), x3 x5 = Bool.true → (∀ x7 ≤ x5, x3 x7 = Bool.true → x7 = x5) → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), x3 x6 = Bool.false → (∀ (x8 : Fin x1 → Bool), x6 ≤ x8 → x3 x8 = Bool.false → x8 = x6) → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = x3 x7 := by
  intro n C f ao onMin onMax
  have orderBool (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by cases a <;> cases b <;> decide
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have run (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (a b : List Bool) (ln : a.length = b.length)
      (le : ∀ i, a.getD i false = true → b.getD i false = true) :
      ∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
    induction gs generalizing a b with
    | nil => exact le
    | cons g gs ih =>
      let v := fun w : List Bool => g.op.eval (g.inputs.map fun i => w.getD i false)
      have gate : v a = true → v b = true := by
        rcases ops g List.mem_cons_self with h | h
        · dsimp only [v]
          rw [h]
          change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
          rw [List.all_map, List.all_map]
          intro ha
          exact List.all_eq_true.mpr (fun i hi => le i (List.all_eq_true.mp ha i hi))
        · dsimp only [v]
          rw [h]
          change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
          rw [List.any_map, List.any_map]
          rintro ha
          obtain ⟨i, hi, hv⟩ := List.any_eq_true.mp ha
          exact List.any_eq_true.mpr ⟨i,hi,le i hv⟩
      apply ih (fun q hq => ops q (List.mem_cons_of_mem _ hq)) (step a g) (step b g)
      · simp only [step, List.length_append, List.length_singleton, ln]
      · intro i
        change (a ++ [v a]).getD i false = true → (b ++ [v b]).getD i false = true
        by_cases h : i < a.length
        · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (ln ▸ h)]
          exact le i
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ← ln]
          cases i - a.length with
          | zero => exact gate
          | succ k => simp
  have mono : Monotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
    intro x y h
    apply (orderBool _ _).mpr
    apply run C.gates ao.1 (List.ofFn x) (List.ofFn y) (by simp) _ C.output
    intro i
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_ofFn]
      exact (orderBool _ _).mp (h ⟨i,hi⟩)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
      simp
  intro x
  cases hx : f x with
  | true =>
    obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT (fun y => f y = true) x hx
    have hit := onMin y hy.1 (fun z hzy hz => le_antisymm hzy (hy.2 hz hzy))
    exact (orderBool _ _).mp (mono hyx) hit
  | false =>
    obtain ⟨y, hxy, hy⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => f y = false) x hx
    have miss := onMax y hy.1 (fun z hyz hz => le_antisymm (hy.2 hz hyz) hyz)
    have bound := mono hxy
    change C.eval (List.ofFn x) ≤ C.eval (List.ofFn y) at bound
    rw [miss] at bound
    exact Bool.eq_false_of_le_false bound
