import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1331_aux

open PEqualNP.CircuitLowerBounds

theorem getD_eq_of_drop (n : ℕ) (a b : List Bool) (h : a.drop n = b.drop n) (i : ℕ) (hi : n ≤ i) :
    a.getD i false = b.getD i false := by
  have ha : a.getD i false = (a.drop n).getD (i - n) false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    omega
  have hb : b.getD i false = (b.drop n).getD (i - n) false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    omega
  rw [ha, hb, h]

theorem fold_drop (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, ∀ u ∈ g.inputs, n ≤ u) :
    ∀ a b : List Bool, n ≤ a.length → n ≤ b.length → a.drop n = b.drop n →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).drop n =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).drop n := by
  induction gs with
  | nil => intro a b _ _ h; simpa using h
  | cons g gs ih =>
    intro a b ha hb h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp; omega
    · simp; omega
    · have hm : (g.inputs.map fun i => a.getD i false) = (g.inputs.map fun i => b.getD i false) := by
        apply List.map_congr_left
        intro u hu
        exact getD_eq_of_drop n a b h u (hg g List.mem_cons_self u hu)
      rw [List.drop_append_of_le_length ha, List.drop_append_of_le_length hb, h, hm]

end PEqualNP.Outside.L_meta_1331_aux

open PEqualNP.Outside.L_meta_1331_aux in
theorem PEqualNP.Outside.L_meta_1331 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G : Finset (Fin gates.length)), (∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u) → ∀ k ∈ G, (∀ i ∈ G, k ≤ i) → ∀ w ∈ (gates.get k).inputs, n ≤ w → ∀ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn y) := by
  intro n gates G hG k hk hmin w _ hw x y
  have hpre : ∀ g ∈ gates.take k.val, ∀ u ∈ g.inputs, n ≤ u := by
    intro g hg u hu
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hjk : j < k.val := by simp at hj; omega
    have hjl : j < gates.length := by simp at hj; omega
    have hnot : (⟨j, hjl⟩ : Fin gates.length) ∉ G := by
      intro hin
      have := hmin _ hin
      rw [Fin.le_def] at this
      simp at this
      omega
    have := hG _ hnot u
    simp only [List.get_eq_getElem] at this
    rw [List.getElem_take] at hu
    exact this hu
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  apply getD_eq_of_drop n _ _ _ w hw
  refine fold_drop n _ hpre _ _ (by simp) (by simp) ?_
  rw [List.drop_eq_nil_of_le (by simp), List.drop_eq_nil_of_le (by simp)]
