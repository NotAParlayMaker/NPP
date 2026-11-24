import Mathlib.Data.Nat.Notation

theorem PEqualNP.Outside.L_meta_4534 :
    ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro x1 x2 x3 x4
  dsimp only
  intro hx2 hsub hx4 idx
  by_cases hlt : idx.val < x2.length
  · have ⟨a, ha, b, hb, hval⟩ := hx2 ⟨idx.val, hlt⟩
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact ha
    · rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hb
    · rw [List.get_eq_getElem, List.getElem_append_left hlt]
      simpa [List.get_eq_getElem] using hval
  · have hge : x2.length ≤ idx.val := Nat.le_of_not_lt hlt
    have hidx4 : idx.val - x2.length < x4.length := by
      have hlen : idx.val < x2.length + x4.length := by
        simpa [List.length_append] using idx.isLt
      omega
    have ⟨a, ha, b, hb, hval⟩ := hx4 ⟨idx.val - x2.length, hidx4⟩
    have hmem : ∀ z, z ∈ x3 ++ List.take (idx.val - x2.length) x4 → z ∈ x1 ++ List.take idx.val (x2 ++ x4) := by
      intro z hz
      rw [List.take_append, List.take_of_length_le hge, ← List.append_assoc]
      rw [List.mem_append] at hz ⊢
      rcases hz with hz3 | hz4
      · exact Or.inl (hsub z hz3)
      · exact Or.inr hz4
    refine ⟨a, hmem a ha, b, hmem b hb, ?_⟩
    rw [List.get_eq_getElem, List.getElem_append_right hge]
    simpa [List.get_eq_getElem] using hval
