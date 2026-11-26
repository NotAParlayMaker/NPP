import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18430_aux

open PEqualNP.CircuitLowerBounds

def R (a b : List Bool) : Prop :=
  a.length = b.length ∧ 14 ≤ a.length ∧ ∀ i, i ≠ 2 → a.getD i false = true → b.getD i false = true

theorem step (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (h2 : 2 ∉ g.inputs)
    (a b : List Bool) (h : R a b) :
    R (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  obtain ⟨hl, h14, hv⟩ := h
  have hne : ∀ j ∈ g.inputs, j ≠ 2 := by
    intro j hj e; subst e; exact h2 hj
  have hev : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    rcases hg with hg | hg <;> rw [hg] <;> simp [GateOp.eval]
    · intro H j hj; exact hv _ (hne j hj) (H j hj)
    · intro j hj H; exact ⟨j, hj, hv _ (hne j hj) H⟩
  refine ⟨by simp [hl], by simp; omega, fun i hi2 hi => ?_⟩
  rcases lt_trichotomy i a.length with h1 | h1 | h1
  · rw [List.getD_append _ _ _ _ h1] at hi
    rw [List.getD_append _ _ _ _ (hl ▸ h1)]
    exact hv _ hi2 hi
  · subst h1
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
    simp at hi ⊢
    exact hev hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    simp at hi

theorem fold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : ∀ g ∈ gs, 2 ∉ g.inputs) :
    ∀ a b : List Bool, R a b →
      R (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hg g' (by simp [hg'])) (fun g' hg' => h2 g' (by simp [hg'])) _ _
      (step g (hg g (by simp)) (h2 g (by simp)) a b h)

end PEqualNP.Outside.L_meta_18430_aux

open PEqualNP.Outside.L_meta_18430_aux in
theorem PEqualNP.Outside.L_meta_18430 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x3 ∈ x1.gates, (2 : ℕ) ∉ x3.inputs) → ∀ (x4 : ℕ), x4 ≠ (2 : ℕ) → ∀ (x6 x7 : Fin (14 : ℕ) → Bool), (∀ (x8 : Fin (14 : ℕ)), x8 ≠ (2 : Fin (14 : ℕ)) → x6 x8 = Bool.true → x7 x8 = Bool.true) → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x6 x4 = Bool.true → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x7 x4 = Bool.true := by
  intro C hC h2 w hw x y hxy hx
  have h0 : R (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, by simp, fun i hi2 hi => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    rcases Nat.lt_or_ge i 14 with h | h
    · rw [dif_pos h] at hi ⊢
      exact hxy _ (fun e => hi2 (by simpa using congrArg Fin.val e)) hi
    · rw [dif_neg (by omega)] at hi
      simp at hi
  exact (fold C.gates hC.1 h2 _ _ h0).2.2 w hw hx
