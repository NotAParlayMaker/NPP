import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1088

lemma dep (gs : List PEqualNP.CircuitLowerBounds.Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ (n : ℕ) (O : Finset ℕ), ∃ F : Finset ℕ, F.card ≤ O.card + gs.length ∧
      ∀ x x' : List Bool, x.length = n → x'.length = n →
        (∀ j ∈ F, x.getD j false = x'.getD j false) →
        ∀ o ∈ O,
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD
              o false =
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x').getD
              o false := by
  induction gs with
  | nil =>
    intro n O
    exact ⟨O, by simp, fun x x' _ _ h o ho => h o ho⟩
  | cons g hs ih =>
    intro n O
    classical
    obtain ⟨F1, hF1, hdep⟩ := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (n + 1) O
    refine ⟨F1.erase n ∪ (if n ∈ F1 then g.inputs.toFinset else ∅), ?_, ?_⟩
    · calc (F1.erase n ∪ (if n ∈ F1 then g.inputs.toFinset else ∅)).card
          ≤ (F1.erase n).card + (if n ∈ F1 then g.inputs.toFinset else ∅).card :=
            Finset.card_union_le _ _
        _ ≤ O.card + (g :: hs).length := by
          by_cases hn : n ∈ F1
          · rw [if_pos hn, Finset.card_erase_of_mem hn]
            have h1 := List.toFinset_card_le g.inputs
            have h2 := hgs g List.mem_cons_self
            have h3 : 0 < F1.card := Finset.card_pos.mpr ⟨n, hn⟩
            simp only [List.length_cons]
            omega
          · rw [if_neg hn]
            have h1 := Finset.card_erase_le (s := F1) (a := n)
            simp only [Finset.card_empty, List.length_cons]
            omega
    · intro x x' hx hx' hagree o ho
      show (hs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).getD o false =
        (hs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (x' ++ [g.op.eval (g.inputs.map fun i => x'.getD i false)])).getD o false
      apply hdep _ _ (by simp [hx]) (by simp [hx']) _ o ho
      intro j hj
      by_cases h1 : j < n
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hagree j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hj⟩))
      · by_cases h2 : j = n
        · have hnF : n ∈ F1 := h2 ▸ hj
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          have e1 : j - x.length = 0 := by omega
          have e2 : j - x'.length = 0 := by omega
          rw [e1, e2]
          simp only [List.getD_cons_zero]
          congr 1
          apply List.map_congr_left
          intro i hi
          apply hagree i
          apply Finset.mem_union_right
          rw [if_pos hnF]
          exact List.mem_toFinset.mpr hi
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_1088

theorem PEqualNP.Outside.L_meta_1088 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ i < n, ∃ x : List Bool, x.length = n ∧ C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) → n ≤ C.size + 1 := by
  intro n C hfan hrel
  obtain ⟨F, hF, hdep⟩ := PEqualNP.Outside.L_meta_1088.dep C.gates hfan n {C.output}
  have hsub : Finset.range n ⊆ F := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_contra hiF
    obtain ⟨x, hx, hne⟩ := hrel i hi
    apply hne
    have hlen : (x.set i (!(x.getD i false))).length = n := by simp [hx]
    refine hdep x _ hx hlen ?_ C.output (Finset.mem_singleton_self _)
    intro j hj
    have hij : i ≠ j := fun h => hiF (h ▸ hj)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_range, Finset.card_singleton] at hc hF
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega
