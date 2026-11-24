import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4534 : ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro x1 x2 x3 x4
  dsimp only
  intro h12 h3 h34 i
  by_cases hi : i.val < x2.length
  · obtain ⟨a, ha, b, hb, hab⟩ := h12 ⟨i, hi⟩
    have htake : List.take i (x2 ++ x4) = List.take i x2 :=
      List.take_append_of_le_length (le_of_lt hi)
    have hget : (x2 ++ x4).get i = x2.get ⟨i, hi⟩ := by
      simp [List.getElem_append_left hi]
    refine ⟨a, by rw [htake]; exact ha, b, by rw [htake]; exact hb, by rw [hget]; exact hab⟩
  · have hlen : i.val < x2.length + x4.length := by simpa using i.isLt
    have hj : i.val - x2.length < x4.length := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := h34 ⟨i - x2.length, hj⟩
    have htake : List.take i (x2 ++ x4) = x2 ++ List.take (i - x2.length) x4 := by
      rw [List.take_append, List.take_of_length_le (by omega)]
    have hget : (x2 ++ x4).get i = x4.get ⟨i - x2.length, hj⟩ := by
      simp [List.getElem_append_right (not_lt.1 hi)]
    have mem : ∀ c, c ∈ x3 ++ List.take (i - x2.length) x4 →
        c ∈ x1 ++ (x2 ++ List.take (i - x2.length) x4) := by
      intro c hc
      rcases List.mem_append.1 hc with h | h
      · have h' := h3 c h
        simp only [List.mem_append] at h' ⊢
        tauto
      · simp only [List.mem_append]
        tauto
    refine ⟨a, by rw [htake]; exact mem a ha, b, by rw [htake]; exact mem b hb, by rw [hget]; exact hab⟩
