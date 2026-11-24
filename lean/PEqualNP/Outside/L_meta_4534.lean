import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4534 :
∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro inputs first sources second
  dsimp only
  intro hFirst hSources hSecond i
  by_cases h : i.val < first.length
  · obtain ⟨a, ha, b, hb, hgate⟩ := hFirst ⟨i.val, h⟩
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rwa [List.take_append_of_le_length h.le]
    · rwa [List.take_append_of_le_length h.le]
    · simpa only [List.get_eq_getElem, List.getElem_append_left h] using hgate
  · have hle : first.length ≤ i.val := Nat.le_of_not_gt h
    have hindex : i.val - first.length < second.length := by
      have hi : i.val < first.length + second.length := by
        simpa only [List.length_append] using i.isLt
      omega
    let j : Fin second.length := ⟨i.val - first.length, hindex⟩
    obtain ⟨a, ha, b, hb, hgate⟩ := hSecond j
    have transfer (v : ℕ) (hv : v ∈ sources ++ second.take j.val) :
        v ∈ inputs ++ (first ++ second).take i.val := by
      rw [List.take_append, List.take_of_length_le hle, ← List.append_assoc]
      rcases List.mem_append.mp hv with hv | hv
      · exact List.mem_append_left _ (hSources v hv)
      · exact List.mem_append_right _ hv
    refine ⟨a, transfer a ha, b, transfer b hb, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_append_right hle, j] using hgate
