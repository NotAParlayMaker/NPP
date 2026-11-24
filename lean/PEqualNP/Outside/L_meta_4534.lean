import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4534 : ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro x1 x2 x3 x4
  dsimp only
  intro h12 h3 h34 x7
  have hlen : (x7 : ℕ) < x2.length + x4.length := by
    simpa [List.length_append] using x7.isLt
  by_cases hi : (x7 : ℕ) < x2.length
  · obtain ⟨a, ha, b, hb, h⟩ := h12 ⟨x7, hi⟩
    have ht : List.take (x7 : ℕ) (x2 ++ x4) = List.take (x7 : ℕ) x2 :=
      List.take_append_of_le_length (Nat.le_of_lt hi)
    have hg : (x2 ++ x4).get x7 = x2.get ⟨x7, hi⟩ := by
      simp [List.getElem_append_left hi]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [ht]; exact ha
    · rw [ht]; exact hb
    · rw [hg]; exact h
  · have hle : x2.length ≤ (x7 : ℕ) := Nat.le_of_not_lt hi
    have hj : (x7 : ℕ) - x2.length < x4.length := by omega
    obtain ⟨a, ha, b, hb, h⟩ := h34 ⟨(x7 : ℕ) - x2.length, hj⟩
    have ht : List.take (x7 : ℕ) (x2 ++ x4)
        = x2 ++ List.take ((x7 : ℕ) - x2.length) x4 := by
      rw [List.take_append, List.take_of_length_le hle]
    have hg : (x2 ++ x4).get x7 = x4.get ⟨(x7 : ℕ) - x2.length, hj⟩ := by
      simp [List.getElem_append_right hle]
    have hmem : ∀ y, y ∈ x3 ++ List.take ((x7 : ℕ) - x2.length) x4 →
        y ∈ x1 ++ List.take (x7 : ℕ) (x2 ++ x4) := by
      intro y hy
      rw [ht]
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_append.mp (h3 y hy) with hy' | hy'
        · exact List.mem_append_left _ hy'
        · exact List.mem_append_right _ (List.mem_append_left _ hy')
      · exact List.mem_append_right _ (List.mem_append_right _ hy)
    refine ⟨a, hmem a ha, b, hmem b hb, ?_⟩
    rw [hg]; exact h
