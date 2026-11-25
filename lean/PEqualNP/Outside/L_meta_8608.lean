import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8608_aux

open PEqualNP.CircuitLowerBounds

theorem step (x1 : List Gate) (x2 : List Bool) (x3 : ℕ → Bool)
    (h1 : ∀ (x4 : Fin x2.length), x2.get x4 = x3 ↑x4)
    (h2 : ∀ (x5 : Fin x1.length), (∀ x6 ∈ (x1.get x5).inputs, x6 < x2.length + ↑x5) ∧
      (x1.get x5).op.eval (List.map x3 (x1.get x5).inputs) = x3 (x2.length + ↑x5)) :
    ∀ k, k ≤ x1.length →
      ((x1.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x2).length
        = x2.length + k ∧
      ∀ i, i < x2.length + k →
        ((x1.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x2).getD i false
          = x3 i := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i hi
    simp only [List.take_zero, List.foldl_nil, Nat.add_zero] at hi ⊢
    rw [List.getD_eq_getElem _ _ hi]
    exact h1 ⟨i, hi⟩
  | succ k ih =>
    intro hk
    obtain ⟨hl, hv⟩ := ih (by omega)
    have hk' : k < x1.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    set w := (x1.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x2
    obtain ⟨hin, hev⟩ := h2 ⟨k, hk'⟩
    simp only [List.get_eq_getElem] at hin hev
    have hmap : (x1[k].inputs.map fun i => w.getD i false) = x1[k].inputs.map x3 := by
      apply List.map_congr_left
      intro a ha
      exact hv a (hin a ha)
    rw [hmap, hev]
    refine ⟨by simp [hl]; omega, ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i w.length with h | h
    · rw [List.getD_append _ _ _ _ h]
      exact hv i (by omega)
    · have : i = w.length := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp [hl]

end PEqualNP.Outside.L_meta_8608_aux

theorem PEqualNP.Outside.L_meta_8608 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List Bool) (x3 : ℕ → Bool), (∀ (x4 : Fin x2.length), x2.get x4 = x3 ↑x4) → (∀ (x5 : Fin x1.length), (∀ x6 ∈ (x1.get x5).inputs, x6 < x2.length + ↑x5) ∧ (x1.get x5).op.eval (List.map x3 (x1.get x5).inputs) = x3 (x2.length + ↑x5)) → ∀ (x6 : Fin (x2.length + x1.length)), ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x2).getD (↑x6) Bool.false = x3 ↑x6 := by
  intro x1 x2 x3 h1 h2 x6
  have := (PEqualNP.Outside.L_meta_8608_aux.step x1 x2 x3 h1 h2 x1.length le_rfl).2 x6 x6.isLt
  rw [List.take_length] at this
  exact this
