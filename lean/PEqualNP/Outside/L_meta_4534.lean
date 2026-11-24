import Mathlib.Data.Nat.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4534 : ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro initial first available second
  dsimp only
  intro hfirst hsub hsecond k
  by_cases hk : k.val < first.length
  · let i : Fin first.length := ⟨k.val, hk⟩
    obtain ⟨a, ha, b, hb, hv⟩ := hfirst i
    have ht : (first ++ second).take k.val = first.take k.val := by
      simp [List.take_append, Nat.sub_eq_zero_of_le (Nat.le_of_lt hk)]
    have he : (first ++ second).get k = first.get i := by
      simp only [List.get_eq_getElem]
      exact List.getElem_append_left hk
    rw [ht, he]
    exact ⟨a, ha, b, hb, hv⟩
  · have hlarge : first.length ≤ k.val := Nat.le_of_not_lt hk
    have hbound := k.isLt
    simp only [List.length_append] at hbound
    let i : Fin second.length := ⟨k.val - first.length, by omega⟩
    obtain ⟨a, ha, b, hb, hv⟩ := hsecond i
    have ht : (first ++ second).take k.val = first ++ second.take i.val := by
      rw [List.take_append, List.take_of_length_le hlarge]
    have he : (first ++ second).get k = second.get i := by
      simp only [List.get_eq_getElem]
      exact List.getElem_append_right hlarge
    have liftMem (w : ℕ) (hw : w ∈ available ++ second.take i.val) :
        w ∈ initial ++ (first ++ second).take k.val := by
      rw [ht, ← List.append_assoc]
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_append_left _ (hsub w h)
      · exact List.mem_append_right _ h
    exact ⟨a, liftMem a ha, b, liftMem b hb, by rwa [he]⟩
