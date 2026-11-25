import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7606

theorem sorted_take (l : List ℕ) (h : l.Pairwise (· < ·)) (k : ℕ) (hk : k < l.length) :
    (∀ y ∈ l.take k, y < l[k]) ∧ (∀ y ∈ l, y < l[k] → y ∈ l.take k) := by
  rw [List.pairwise_iff_getElem] at h
  constructor
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    have hi' : i < k := by
      have h2 := hi
      simp only [List.length_take] at h2
      omega
    rw [List.getElem_take]
    exact h i k (by omega) hk hi'
  · intro y hy hlt
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    have hik : i < k := by
      by_contra hc
      rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hc) with e | e
      · subst e
        exact lt_irrefl _ hlt
      · exact lt_asymm hlt (h k i hk hi e)
    have hm : (l.take k)[i]'(by rw [List.length_take]; omega) ∈ l.take k := List.getElem_mem _
    rwa [List.getElem_take] at hm

theorem main (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1) (h4 : x4 < x2 + x3) (hne : x5 x4 ≠ ∅)
    (H : ∀ x8 < x3, ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x2 + x8 ∧ x5 (x2 + x8) ∈ [x5 x10 ∪ x5 x11, x5 x10, ∅, x5 x10 ∩ x5 x11]) :
    ∃ (x9 : List ℕ), x9.length ≤ x3 ∧ (∀ x10 ∈ x9, x2 ≤ x10 ∧ x10 < x2 + x3) ∧ x5 x4 ∈ List.map x5 (List.range x2 ++ x9) ∧
      ∀ (x10 : Fin x9.length), (∀ x13 ∈ List.range x2 ++ List.take (↑x10) x9, x13 < x9.get x10) ∧ x5 (x9.get x10) ≠ ∅ ∧ x5 (x9.get x10) ∉ List.map x5 (List.range x2 ++ List.take (↑x10) x9) ∧ ∃ x13 ∈ List.map x5 (List.range x2 ++ List.take (↑x10) x9), ∃ x14 ∈ List.map x5 (List.range x2 ++ List.take (↑x10) x9), ¬x13 ⊆ x14 ∧ ¬x14 ⊆ x13 ∧ (x5 (x9.get x10) = x13 ∪ x14 ∨ x5 (x9.get x10) = x13 ∩ x14) := by
  classical
  have hmem : ∀ j, j ∈ (List.range' x2 x3).filter (fun j => decide (x5 j ≠ ∅ ∧ ∀ i < j, x5 i ≠ x5 j)) ↔ (x2 ≤ j ∧ j < x2 + x3) ∧ (x5 j ≠ ∅ ∧ ∀ i < j, x5 i ≠ x5 j) := by
    intro j
    simp only [List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  have hsort : ((List.range' x2 x3).filter (fun j => decide (x5 j ≠ ∅ ∧ ∀ i < j, x5 i ≠ x5 j))).Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range'
  have hlen : ((List.range' x2 x3).filter (fun j => decide (x5 j ≠ ∅ ∧ ∀ i < j, x5 i ≠ x5 j))).length ≤ x3 := by
    have h1 := List.length_filter_le (fun j => decide (x5 j ≠ ∅ ∧ ∀ i < j, x5 i ≠ x5 j)) (List.range' x2 x3)
    simpa using h1
  generalize (List.range' x2 x3).filter (fun j => decide (x5 j ≠ ∅ ∧ ∀ i < j, x5 i ≠ x5 j)) = L at hmem hsort hlen
  have key : ∀ i, i < x2 + x3 → x5 i ≠ ∅ → ∃ i' ≤ i, x5 i' = x5 i ∧ i' ∈ List.range x2 ++ L := by
    intro i hi hi0
    have hex : ∃ n, x5 n = x5 i := ⟨i, rfl⟩
    have hle : Nat.find hex ≤ i := Nat.find_min' hex rfl
    refine ⟨Nat.find hex, hle, Nat.find_spec hex, ?_⟩
    by_cases hlt : Nat.find hex < x2
    · exact List.mem_append_left _ (List.mem_range.mpr hlt)
    · refine List.mem_append_right _ ((hmem _).mpr ⟨⟨by omega, by omega⟩, ?_, ?_⟩)
      · rw [Nat.find_spec hex]
        exact hi0
      · intro a ha hEq
        exact Nat.find_min hex ha (hEq.trans (Nat.find_spec hex))
  refine ⟨L, hlen, fun j hj => ((hmem j).mp hj).1, ?_, ?_⟩
  · obtain ⟨i', _, he, hm⟩ := key x4 h4 hne
    exact List.mem_map.mpr ⟨i', hm, he⟩
  · intro k
    have hk := sorted_take L hsort k.1 k.2
    have hjL : L.get k ∈ L := List.get_mem L k
    rw [← List.get_eq_getElem] at hk
    generalize L.get k = j at hk hjL ⊢
    obtain ⟨⟨hj2, hj3⟩, hj0, hjnew⟩ := (hmem j).mp hjL
    have hprev : ∀ y ∈ List.range x2 ++ List.take (↑k) L, y < j := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · have := List.mem_range.mp h
        omega
      · exact hk.1 y h
    have hin : ∀ a, a < j → x5 a ≠ ∅ → x5 a ∈ List.map x5 (List.range x2 ++ List.take (↑k) L) := by
      intro a ha ha0
      obtain ⟨a', hle, he, hm⟩ := key a (by omega) ha0
      refine List.mem_map.mpr ⟨a', ?_, he⟩
      rcases List.mem_append.mp hm with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (hk.2 a' h (by omega))
    refine ⟨hprev, hj0, ?_, ?_⟩
    · intro hc
      obtain ⟨y, hy, hye⟩ := List.mem_map.mp hc
      exact hjnew y (hprev y hy) hye
    · obtain ⟨a, b, hab, hcase⟩ := H (j - x2) (by omega)
      have hjx : x2 + (j - x2) = j := by omega
      rw [hjx] at hab hcase
      have ha : a < j := lt_of_le_of_lt (le_max_left a b) hab
      have hb : b < j := lt_of_le_of_lt (le_max_right a b) hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcase
      have hnab : ¬ x5 a ⊆ x5 b := by
        intro hs
        rcases hcase with h | h | h | h
        · rw [Set.union_eq_self_of_subset_left hs] at h
          exact hjnew b hb h.symm
        · exact hjnew a ha h.symm
        · exact hj0 h
        · rw [Set.inter_eq_self_of_subset_left hs] at h
          exact hjnew a ha h.symm
      have hnba : ¬ x5 b ⊆ x5 a := by
        intro hs
        rcases hcase with h | h | h | h
        · rw [Set.union_eq_self_of_subset_right hs] at h
          exact hjnew a ha h.symm
        · exact hjnew a ha h.symm
        · exact hj0 h
        · rw [Set.inter_eq_self_of_subset_right hs] at h
          exact hjnew b hb h.symm
      have ha0 : x5 a ≠ ∅ := by
        intro h
        apply hnab
        rw [h]
        exact Set.empty_subset _
      have hb0 : x5 b ≠ ∅ := by
        intro h
        apply hnba
        rw [h]
        exact Set.empty_subset _
      refine ⟨x5 a, hin a ha ha0, x5 b, hin b hb hb0, hnab, hnba, ?_⟩
      rcases hcase with h | h | h | h
      · exact Or.inl h
      · exact absurd h.symm (hjnew a ha)
      · exact absurd h hj0
      · exact Or.inr h

end PEqualNP.Outside.L_meta_7606

theorem PEqualNP.Outside.L_meta_7606 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1),   x4 < x2 + x3 →     x5 x4 ≠ ∅ →       (∀ x8 < x3, ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x2 + x8 ∧ x5 (x2 + x8) ∈ [x5 x10 ∪ x5 x11, x5 x10, ∅, x5 x10 ∩ x5 x11]) →         ∃ (x9 : List ℕ),           x9.length ≤ x3 ∧             (∀ x10 ∈ x9, x2 ≤ x10 ∧ x10 < x2 + x3) ∧               x5 x4 ∈ List.map x5 (List.range x2 ++ x9) ∧                 ∀ (x10 : Fin x9.length),                   have x11 : List ℕ := List.range x2 ++ List.take (↑x10) x9;                   have x12 : Set x1 := x5 (x9.get x10);                   (∀ x13 ∈ x11, x13 < x9.get x10) ∧ x12 ≠ ∅ ∧ x12 ∉ List.map x5 x11 ∧ ∃ x13 ∈ List.map x5 x11, ∃ x14 ∈ List.map x5 x11, ¬x13 ⊆ x14 ∧ ¬x14 ⊆ x13 ∧ (x12 = x13 ∪ x14 ∨ x12 = x13 ∩ x14) := by
  intro x1 x2 x3 x4 x5 h4 hne H
  exact PEqualNP.Outside.L_meta_7606.main x1 x2 x3 x4 x5 h4 hne H
