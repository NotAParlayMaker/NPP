import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1331

open PEqualNP.CircuitLowerBounds

theorem foldl_inv (n : ℕ) : ∀ (gs : List Gate) (a b : List Bool),
    (∀ g ∈ gs, ∀ u ∈ g.inputs, n ≤ u) → a.length = b.length →
    (∀ i, n ≤ i → a[i]? = b[i]?) →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).length =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).length ∧
    ∀ i, n ≤ i →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)[i]? =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b)[i]? := by
  intro gs
  induction gs with
  | nil =>
    intro a b _ hl h
    exact ⟨hl, h⟩
  | cons g gs ih =>
    intro a b hgs hl h
    simp only [List.foldl_cons]
    have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu' := h u (hgs g List.mem_cons_self u hu)
      simp only [List.getD_eq_getElem?_getD, hu']
    apply ih
    · intro g' hg'
      exact hgs g' (List.mem_cons_of_mem _ hg')
    · simp [hl]
    · intro i hi
      rw [hv, List.getElem?_append, List.getElem?_append, hl]
      split
      · exact h i hi
      · rfl

end PEqualNP.Outside.L_meta_1331

theorem PEqualNP.Outside.L_meta_1331 :
    ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G : Finset (Fin gates.length)),
      (∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u) →
        ∀ k ∈ G, (∀ i ∈ G, k ≤ i) →
          ∀ w ∈ (gates.get k).inputs, n ≤ w →
            ∀ x y : Fin n → Bool,
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn x) =
                PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn y) := by
  intro n gates G hG k _ hmin w _ hnw x y
  have hall : ∀ g ∈ gates.take k.val, ∀ u ∈ g.inputs, n ≤ u := by
    intro g hg u hu
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    have hjk : j < k.val := by
      simp only [List.length_take] at hj
      omega
    have hjlen : j < gates.length := by
      simp only [List.length_take] at hj
      omega
    have hnot : (⟨j, hjlen⟩ : Fin gates.length) ∉ G := by
      intro hm
      have := hmin _ hm
      rw [Fin.le_def] at this
      simp only at this
      omega
    have := hG ⟨j, hjlen⟩ hnot u
    rw [List.getElem_take] at hu
    exact this (by simpa using hu)
  obtain ⟨_, h⟩ := PEqualNP.Outside.L_meta_1331.foldl_inv n (gates.take k.val)
    (List.ofFn x) (List.ofFn y) hall (by simp) (by
      intro i hi
      rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by simpa using hi)])
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h w hnw]
