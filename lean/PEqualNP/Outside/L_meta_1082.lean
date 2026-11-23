import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1082

open PEqualNP.CircuitLowerBounds

def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem op_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg]
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro H b ⟨i, hi, rfl⟩
    exact h i (H _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hb⟩

theorem step_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, Le w w' →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
         (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    refine ⟨by simp [hl], ?_⟩
    intro i hx
    by_cases hlt : i < w.length
    · rw [List.getD_append _ _ _ _ hlt] at hx
      rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
      exact hi i hx
    · by_cases heq : i = w.length
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hx
        rw [List.getD_append_right _ _ _ _ (le_of_eq hl.symm), ← hl]
        simp only [Nat.sub_self, List.getD_cons_zero] at hx ⊢
        exact op_mono g (hm g (List.mem_cons_self)) w w' hi hx
      · have h1 : w.length < i := by omega
        rw [List.getD_append_right _ _ _ _ (le_of_lt h1)] at hx
        obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
        rw [hk] at hx
        simp at hx

end PEqualNP.Outside.L_meta_1082

theorem PEqualNP.Outside.L_meta_1082 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ x y : List Bool, x.length = n →
      y.length = n → (∀ i < n, x.getD i false = true → y.getD i false = true) →
      C.eval x = true → C.eval y = true := by
  intro n C hC x y hx hy hxy hxe
  have hxy' : ∀ i, x.getD i false = true → y.getD i false = true := by
    intro i hi
    by_cases hlt : i < n
    · exact hxy i hlt hi
    · rw [List.getD_eq_default _ _ (by omega)] at hi
      exact absurd hi (by simp)
  have key := PEqualNP.Outside.L_meta_1082.step_mono C.gates hC x y ⟨by omega, hxy'⟩
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at *
  exact key.2 C.output hxe
