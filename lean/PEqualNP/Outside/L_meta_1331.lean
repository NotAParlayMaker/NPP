import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1331

open PEqualNP.CircuitLowerBounds

lemma tail_exists (n : ℕ) (L : List Gate) (h : ∀ g ∈ L, ∀ u ∈ g.inputs, n ≤ u) :
    ∃ T : List Bool, ∀ (o : ℕ) (x : List Bool), x.length = n →
      Circuit.wires ⟨L, o⟩ x = x ++ T := by
  induction L using List.reverseRec with
  | nil => exact ⟨[], fun o x _ => by simp [Circuit.wires]⟩
  | append_singleton L g ih =>
    obtain ⟨T, hT⟩ := ih (fun g' hg' => h g' (by simp [hg']))
    refine ⟨T ++ [g.op.eval (g.inputs.map fun i => T.getD (i - n) false)], fun o x hx => ?_⟩
    have h1 := hT o x hx
    simp only [Circuit.wires] at h1 ⊢
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, h1, List.append_assoc]
    congr 4
    apply List.map_congr_left
    intro u hu
    have hnu : n ≤ u := h g (by simp) u hu
    rw [List.getD_append_right _ _ _ _ (by omega), hx]

end PEqualNP.Outside.L_meta_1331

theorem PEqualNP.Outside.L_meta_1331 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G : Finset (Fin gates.length)), (∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u) → ∀ k ∈ G, (∀ i ∈ G, k ≤ i) → ∀ w ∈ (gates.get k).inputs, n ≤ w → ∀ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn y) := by
  intro n gates G hG k _ hmin w _ _ x y
  have hL : ∀ g ∈ gates.take k.val, ∀ u ∈ g.inputs, n ≤ u := by
    intro g hg u hu
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [List.length_take] at hj
    have hjk : j < k.val := by omega
    have hjl : j < gates.length := by omega
    rw [List.getElem_take] at hu
    refine hG ⟨j, hjl⟩ (fun hmem => ?_) u hu
    have := hmin _ hmem
    exact absurd (Fin.le_def.mp this) (by simpa using hjk)
  obtain ⟨T, hT⟩ := PEqualNP.Outside.L_meta_1331.tail_exists n (gates.take k.val) hL
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
  rw [hT w (List.ofFn x) (by simp), hT w (List.ofFn y) (by simp)]
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
  simp
