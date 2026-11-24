import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4534 : ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro x1 x2 x3 x4 x5 h12 hsub h34 i
  simp only [x5] at h12 h34 ⊢
  by_cases hi : (i : ℕ) < x2.length
  · obtain ⟨a, ha, b, hb, h⟩ := h12 ⟨i, hi⟩
    have ht : List.take (↑i) (x2 ++ x4) = List.take (↑i) x2 := by
      rw [List.take_append_of_le_length (le_of_lt hi)]
    have hg : (x2 ++ x4).get i = x2.get ⟨i, hi⟩ := by
      simp [List.getElem_append_left hi]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact h
  · have hle : x2.length ≤ (i : ℕ) := Nat.le_of_not_lt hi
    have hj : (i : ℕ) - x2.length < x4.length := by
      have := i.isLt
      simp only [List.length_append] at this
      omega
    obtain ⟨a, ha, b, hb, h⟩ := h34 ⟨(i : ℕ) - x2.length, hj⟩
    have ht : List.take (↑i) (x2 ++ x4) = x2 ++ List.take ((i : ℕ) - x2.length) x4 := by
      rw [List.take_append, List.take_of_length_le hle]
    have hg : (x2 ++ x4).get i = x4.get ⟨(i : ℕ) - x2.length, hj⟩ := by
      simp [List.getElem_append_right hle]
    have hmem : ∀ c, c ∈ x3 ++ List.take ((i : ℕ) - x2.length) x4 →
        c ∈ x1 ++ List.take (↑i) (x2 ++ x4) := by
      intro c hc
      rw [ht]
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp (hsub c hc) with h1 | h2
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_append_left _ h2)
      · exact List.mem_append_right _ (List.mem_append_right _ hc)
    refine ⟨a, hmem a ha, b, hmem b hb, ?_⟩
    rw [hg]; exact h
