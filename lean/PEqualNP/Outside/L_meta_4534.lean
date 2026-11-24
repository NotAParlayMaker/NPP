import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4534 : ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro x1 x2 x3 x4 x5 h12 hsub h34 i
  by_cases hi : (i : ℕ) < x2.length
  · obtain ⟨a, ha, b, hb, hab⟩ := h12 ⟨(i : ℕ), hi⟩
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
      exact ha
    · rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
      exact hb
    · rw [List.get_eq_getElem] at hab
      rw [List.get_eq_getElem, List.getElem_append_left hi]
      exact hab
  · have hi' : x2.length ≤ (i : ℕ) := Nat.not_lt.mp hi
    have hjlt : (i : ℕ) - x2.length < x4.length := by
      have hlt : (i : ℕ) < (x2 ++ x4).length := i.isLt
      have hlen : (x2 ++ x4).length = x2.length + x4.length := List.length_append
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := h34 ⟨(i : ℕ) - x2.length, hjlt⟩
    have htake : List.take (i : ℕ) (x2 ++ x4) = x2 ++ List.take ((i : ℕ) - x2.length) x4 := by
      rw [List.take_append, List.take_of_length_le hi']
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [htake]
      rcases List.mem_append.mp ha with ha3 | ha4
      · have hmem := hsub a ha3
        rw [List.mem_append] at hmem ⊢
        rcases hmem with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (List.mem_append_left _ h2)
      · exact List.mem_append_right _ (List.mem_append_right _ ha4)
    · rw [htake]
      rcases List.mem_append.mp hb with hb3 | hb4
      · have hmem := hsub b hb3
        rw [List.mem_append] at hmem ⊢
        rcases hmem with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (List.mem_append_left _ h2)
      · exact List.mem_append_right _ (List.mem_append_right _ hb4)
    · rw [List.get_eq_getElem] at hab
      rw [List.get_eq_getElem, List.getElem_append_right hi']
      exact hab
