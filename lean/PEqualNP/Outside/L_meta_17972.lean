import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_17972 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.getD x6 Bool.false = Bool.true → x4.getD x6 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true := by
  intro C hC x y hl hp he
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let precedes (u v : List Bool) : Prop :=
    u.length = v.length ∧ ∀ i, u.getD i false = true → v.getD i false = true
  have move (gs : List Gate) (ok : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (huv : precedes u v) :
      precedes (gs.foldl step u) (gs.foldl step v) := by
    induction gs generalizing u v with
    | nil => exact huv
    | cons g gs ih =>
      apply ih (fun g' hg' => ok g' (List.mem_cons_of_mem _ hg'))
      have hgo := ok g (List.mem_cons_self)
      have evalStep :
          g.op.eval (g.inputs.map fun i => u.getD i false) = true →
          g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
        rcases hgo with ho | ho
        · rw [ho]
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
          intro h b hb
          obtain ⟨i, hi, rfl⟩ := hb
          exact huv.2 i (h _ ⟨i, hi, rfl⟩)
        · rw [ho]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          rintro ⟨b, ⟨i, hi, rfl⟩, h⟩
          exact ⟨_, ⟨i, hi, rfl⟩, huv.2 i h⟩
      refine ⟨by simp [step, huv.1], ?_⟩
      intro i hi
      by_cases h : i < u.length
      · have h' : i < v.length := by simpa only [← huv.1] using h
        rw [List.getD_append _ _ _ _ h] at hi
        rw [List.getD_append _ _ _ _ h']
        exact huv.2 i hi
      · have h' : v.length ≤ i := by simpa only [← huv.1] using Nat.le_of_not_gt h
        rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h)] at hi
        rw [List.getD_append_right _ _ _ _ h', ← huv.1]
        generalize i - u.length = index at hi ⊢
        cases index with
        | zero => exact evalStep hi
        | succ index => simp at hi
  exact (move C.gates hC x y ⟨hl, hp⟩).2 C.output he
