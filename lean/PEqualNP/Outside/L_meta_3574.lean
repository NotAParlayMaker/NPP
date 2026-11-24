import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3574_aux

def cnt {n : ℕ} (l : List (Finset (Fin n))) (X C : Finset (Fin n)) : Finset ℕ :=
  (Finset.range l.length).filter
    (fun j => 1 < (l.getD j ∅).card ∧ l.getD j ∅ ⊆ X ∧ ¬ l.getD j ∅ ⊆ C)

theorem small {n : ℕ} (l : List (Finset (Fin n))) (X C : Finset (Fin n)) (h : X.card ≤ 1) :
    (X \ C).card ≤ (cnt l X C).card + (if Disjoint X C then 1 else 0) := by
  by_cases hd : Disjoint X C
  · have h1 := Finset.card_le_card (Finset.sdiff_subset (s := X) (t := C))
    simp only [hd, ite_true]
    omega
  · obtain ⟨a, ha, haC⟩ := Finset.not_disjoint_iff.mp hd
    have hXC : X ⊆ C := by
      intro b hb
      have hba : b = a := Finset.card_le_one.mp h b hb a ha
      rw [hba]
      exact haC
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hXC]
    simp

theorem main {n : ℕ} (l : List (Finset (Fin n)))
    (hl : ∀ (i : ℕ) (X : Finset (Fin n)), l[i]? = Option.some X →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin n)), X = A ∪ B ∧
        (A.card ≤ (1 : ℕ) ∨ A ∈ List.take i l) ∧ (B.card ≤ (1 : ℕ) ∨ B ∈ List.take i l)) :
    ∀ (i : ℕ) (X : Finset (Fin n)),
      (X.card ≤ 1 ∨ ∃ j, j < i ∧ j < l.length ∧ l.getD j ∅ = X) →
      ∀ C : Finset (Fin n),
        (X \ C).card ≤ (cnt l X C).card + (if Disjoint X C then 1 else 0) := by
  intro i
  induction i with
  | zero =>
    intro X hX C
    rcases hX with h | ⟨j, hj, _⟩
    · exact small l X C h
    · omega
  | succ i ih =>
    intro X hX C
    rcases hX with h | ⟨j, hj, hjl, hjX⟩
    · exact small l X C h
    · by_cases hji : j < i
      · exact ih X (Or.inr ⟨j, hji, hjl, hjX⟩) C
      · have hje : j = i := by omega
        subst hje
        have hget : l[j]? = Option.some X := by
          rw [List.getElem?_eq_getElem hjl, ← hjX, List.getD_eq_getElem _ _ hjl]
        obtain ⟨A, B, hAB, hA, hB⟩ := hl j X hget
        have conv : ∀ Y : Finset (Fin n), (Y.card ≤ 1 ∨ Y ∈ List.take j l) →
            (Y.card ≤ 1 ∨ ∃ k, k < j ∧ k < l.length ∧ l.getD k ∅ = Y) := by
          intro Y hY
          rcases hY with h | h
          · exact Or.inl h
          · right
            obtain ⟨k, hk, hkY⟩ := List.mem_iff_getElem.mp h
            have hk2 := hk
            rw [List.length_take] at hk2
            refine ⟨k, by omega, by omega, ?_⟩
            rw [List.getD_eq_getElem _ _ (by omega), ← hkY, List.getElem_take]
        have ihA := ih A (conv A hA)
        have ihB := ih B (conv B hB)
        by_cases hXs : X.card ≤ 1
        · exact small l X C hXs
        by_cases hAX : A = X
        · rw [← hAX]
          exact ihA C
        by_cases hBX : B = X
        · rw [← hBX]
          exact ihB C
        by_cases hXC : X ⊆ C
        · rw [Finset.sdiff_eq_empty_iff_subset.mpr hXC]
          simp
        have h1 := ihA C
        have h2 := ihB (C ∪ A)
        have hsub : X \ C ⊆ A \ C ∪ B \ (C ∪ A) := by
          intro a ha
          rw [hAB] at ha
          simp only [Finset.mem_sdiff, Finset.mem_union] at ha ⊢
          tauto
        have h3 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hAsub : A ⊆ X := by
          rw [hAB]
          exact Finset.subset_union_left
        have hBsub : B ⊆ X := by
          rw [hAB]
          exact Finset.subset_union_right
        have hnA : ¬ X ⊆ A := fun h => hAX (Finset.Subset.antisymm hAsub h)
        have hnB : ¬ X ⊆ B := fun h => hBX (Finset.Subset.antisymm hBsub h)
        have hdisj : Disjoint (cnt l A C) (cnt l B (C ∪ A)) := by
          rw [Finset.disjoint_left]
          intro k hk1 hk2
          simp only [cnt, Finset.mem_filter] at hk1 hk2
          exact hk2.2.2.2 (hk1.2.2.1.trans Finset.subset_union_right)
        have hjn : j ∉ cnt l A C ∪ cnt l B (C ∪ A) := by
          simp only [cnt, Finset.mem_union, Finset.mem_filter, hjX]
          rintro (h | h)
          · exact hnA h.2.2.1
          · exact hnB h.2.2.1
        have hins : insert j (cnt l A C ∪ cnt l B (C ∪ A)) ⊆ cnt l X C := by
          intro k hk
          rw [Finset.mem_insert] at hk
          rcases hk with hk | hk
          · rw [hk]
            simp only [cnt, Finset.mem_filter, Finset.mem_range, hjX]
            exact ⟨hjl, by omega, subset_rfl, hXC⟩
          · rw [Finset.mem_union] at hk
            simp only [cnt, Finset.mem_filter] at hk ⊢
            rcases hk with h | h
            · exact ⟨h.1, h.2.1, h.2.2.1.trans hAsub, h.2.2.2⟩
            · exact ⟨h.1, h.2.1, h.2.2.1.trans hBsub,
                fun hc => h.2.2.2 (hc.trans Finset.subset_union_left)⟩
        have h4 := Finset.card_le_card hins
        rw [Finset.card_insert_of_notMem hjn, Finset.card_union_of_disjoint hdisj] at h4
        have d3 : Disjoint A C → Disjoint B (C ∪ A) → Disjoint X C := by
          intro d1 d2
          rw [hAB]
          exact Finset.disjoint_union_left.mpr ⟨d1, (Finset.disjoint_union_right.mp d2).1⟩
        have h5 : (if Disjoint A C then 1 else 0) + (if Disjoint B (C ∪ A) then 1 else 0)
            ≤ 1 + (if Disjoint X C then 1 else 0) := by
          split_ifs with a b c <;> first | omega | exact absurd (d3 a b) c
        omega

end PEqualNP.Outside.L_meta_3574_aux

theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro x1 x2 h X hX
  obtain ⟨i, hi, hiX⟩ := List.mem_iff_getElem.mp hX
  have m := PEqualNP.Outside.L_meta_3574_aux.main x2 h (i + 1) X
    (Or.inr ⟨i, by omega, hi, by rw [List.getD_eq_getElem _ _ hi]; exact hiX⟩) ∅
  simp only [Finset.sdiff_empty, Finset.disjoint_empty_right, ite_true] at m
  have hc : (PEqualNP.Outside.L_meta_3574_aux.cnt x2 X ∅).card ≤
      Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ X } := by
    rw [Fintype.card_subtype, ← Finset.card_map Fin.valEmbedding]
    apply Finset.card_le_card
    intro k hk
    simp only [PEqualNP.Outside.L_meta_3574_aux.cnt, Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_map]
    refine ⟨⟨k, hk.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    have hk1 : k < x2.length := hk.1
    have e : x2.getD k ∅ = x2.get ⟨k, hk1⟩ := by
      rw [List.getD_eq_getElem _ _ hk1]
      rfl
    rw [← e]
    exact ⟨Finset.mem_univ _, hk.2.1, hk.2.2.1⟩
  omega
