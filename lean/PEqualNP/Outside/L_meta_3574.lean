import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3574

def G {n : ℕ} (L : List (Finset (Fin n))) (i : Fin L.length) (T : Finset (Fin n)) :
    Finset (Fin L.length) :=
  Finset.univ.filter (fun j => j ≤ i ∧ 1 < (L.get j).card ∧ L.get j ⊆ L.get i ∧ ¬ L.get j ⊆ T)

theorem key {n : ℕ} (L : List (Finset (Fin n)))
    (hL : ∀ (x3 : ℕ) (x4 : Finset (Fin n)), L[x3]? = some x4 → ∃ (x6 x7 : Finset (Fin n)),
      x4 = x6 ∪ x7 ∧ (x6.card ≤ 1 ∨ x6 ∈ List.take x3 L) ∧ (x7.card ≤ 1 ∨ x7 ∈ List.take x3 L)) :
    ∀ m, ∀ i : Fin L.length, i.val = m → ∀ T : Finset (Fin n),
      ((L.get i) \ T).card ≤ (G L i T).card + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi T
    -- piece bound
    have piece : ∀ (P : Finset (Fin n)), (P.card ≤ 1 ∨ P ∈ List.take i.val L) → ∀ U : Finset (Fin n),
        ∃ K : Finset (Fin L.length), (∀ j ∈ K, j < i ∧ 1 < (L.get j).card ∧ L.get j ⊆ P ∧ ¬ L.get j ⊆ U) ∧
          (P \ U).card ≤ K.card + 1 := by
      intro P hP U
      rcases hP with hP | hP
      · refine ⟨∅, by simp, ?_⟩
        have := Finset.card_le_card (Finset.sdiff_subset (s := P) (t := U))
        simp only [Finset.card_empty]
        omega
      · obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hP
        rw [List.length_take] at ha
        have ha' : a < L.length := by omega
        have hai : a < i.val := by omega
        let ia : Fin L.length := ⟨a, ha'⟩
        have hget : (List.take i.val L)[a] = L.get ia := by simp [ia]
        refine ⟨G L ia U, ?_, ?_⟩
        · intro j hj
          simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          refine ⟨?_, hj.2.1, ?_, hj.2.2.2⟩
          · exact lt_of_le_of_lt hj.1 (by simp only [Fin.lt_def, ia]; omega)
          · rw [hget]; exact hj.2.2.1
        · rw [hget]
          exact ih a (by omega) ia rfl U
    obtain ⟨A, B, hS, hA, hB⟩ := hL i.val (L.get i) (by simp)
    by_cases hsmall : ((L.get i) \ T).card ≤ 1
    · omega
    obtain ⟨KA, hKA, hcA⟩ := piece A hA T
    obtain ⟨KB, hKB, hcB⟩ := piece B hB (T ∪ A)
    have hAS : A ⊆ L.get i := by rw [hS]; exact Finset.subset_union_left
    have hBS : B ⊆ L.get i := by rw [hS]; exact Finset.subset_union_right
    have hiG : i ∈ G L i T := by
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨le_refl _, ?_, subset_refl _, ?_⟩
      · have := Finset.card_le_card (Finset.sdiff_subset (s := L.get i) (t := T))
        omega
      · intro hsub
        rw [Finset.sdiff_eq_empty_iff_subset.2 hsub] at hsmall
        simp at hsmall
    have hsub : insert i (KA ∪ KB) ⊆ G L i T := by
      intro j hj
      rw [Finset.mem_insert, Finset.mem_union] at hj
      rcases hj with rfl | hj | hj
      · exact hiG
      · obtain ⟨h1, h2, h3, h4⟩ := hKA j hj
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨le_of_lt h1, h2, h3.trans hAS, h4⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hKB j hj
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨le_of_lt h1, h2, h3.trans hBS, fun h => h4 (h.trans Finset.subset_union_left)⟩
    have hdisj : Disjoint KA KB := by
      rw [Finset.disjoint_left]
      intro j hjA hjB
      exact (hKB j hjB).2.2.2 ((hKA j hjA).2.2.1.trans Finset.subset_union_right)
    have hinot : i ∉ KA ∪ KB := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact lt_irrefl _ (hKA i h).1
      · exact lt_irrefl _ (hKB i h).1
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hinot, Finset.card_union_of_disjoint hdisj] at hc1
    have hsplit : (L.get i) \ T ⊆ (A \ T) ∪ (B \ (T ∪ A)) := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [hS, Finset.mem_union] at hx
      rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_union]
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, hx.2⟩
      · rcases hx.1 with h | h
        · exact absurd h hxA
        · exact Or.inr ⟨h, by tauto⟩
    have hc2 := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
    omega

end PEqualNP.Outside.L_meta_3574

theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro n L hL S hS
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hS
  have h := PEqualNP.Outside.L_meta_3574.key L hL i.val i rfl ∅
  rw [Finset.sdiff_empty] at h
  rw [Fintype.card_subtype]
  refine h.trans (Nat.add_le_add_right (Finset.card_le_card ?_) 1)
  intro j hj
  simp only [PEqualNP.Outside.L_meta_3574.G, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hj.2.1, hj.2.2.1⟩
