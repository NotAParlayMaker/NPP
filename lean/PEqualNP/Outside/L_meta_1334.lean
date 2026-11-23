import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1334_aux

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_agree (T : ℕ) : ∀ (gs : List Gate) (A B : List Bool), A.length = B.length →
    (∀ i, i ≠ T → A.getD i false = B.getD i false) → (∀ g ∈ gs, T ∉ g.inputs) →
    (gs.foldl stp A).length = (gs.foldl stp B).length ∧
      ∀ i, i ≠ T → (gs.foldl stp A).getD i false = (gs.foldl stp B).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro A B hl h _
    exact ⟨hl, h⟩
  | cons g rest ih =>
    intro A B hl h hT
    rw [List.foldl_cons, List.foldl_cons]
    have hmap : (g.inputs.map fun j => A.getD j false) = (g.inputs.map fun j => B.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact h j (fun e => hT g (by simp) (e ▸ hj))
    apply ih
    · simp [stp, hl]
    · intro i hi
      simp only [stp, hmap]
      by_cases hlt : i < A.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h i hi
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]
    · intro g2 hg2
      exact hT g2 (List.mem_cons_of_mem _ hg2)

theorem set_agree : ∀ (gs : List Gate) (q : ℕ) (A : List Bool) (g' : Gate) (T : ℕ),
    T = A.length + q → (∀ g ∈ gs, T ∉ g.inputs) →
    ((gs.set q g').foldl stp A).length = (gs.foldl stp A).length ∧
      ∀ i, i ≠ T → ((gs.set q g').foldl stp A).getD i false = (gs.foldl stp A).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro q A g' T _ _
    simp
  | cons g rest ih =>
    intro q A g' T hTq hT
    cases q with
    | zero =>
      rw [List.set_cons_zero, List.foldl_cons, List.foldl_cons]
      apply fold_agree T rest
      · simp [stp]
      · intro i hi
        by_cases hlt : i < A.length
        · simp only [stp]
          rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
        · simp only [stp, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      · intro g2 hg2
        exact hT g2 (List.mem_cons_of_mem _ hg2)
    | succ q =>
      rw [List.set_cons_succ, List.foldl_cons, List.foldl_cons]
      apply ih q (stp A g) g' T
      · simp [stp]
        omega
      · intro g2 hg2
        exact hT g2 (List.mem_cons_of_mem _ hg2)

end PEqualNP.Outside.L_meta_1334_aux

theorem PEqualNP.Outside.L_meta_1334 : ∀ (n q w : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g' : PEqualNP.CircuitLowerBounds.Gate), (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gates[k]? = some g → n + q ∉ g.inputs) → w ≠ n + q → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set q g', w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) := by
  intro n q w gates g' h hw x
  have hT : ∀ g ∈ gates, n + q ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
    exact h k g hk
  exact (PEqualNP.Outside.L_meta_1334_aux.set_agree gates q (List.ofFn x) g' (n + q) (by simp) hT).2 w hw
