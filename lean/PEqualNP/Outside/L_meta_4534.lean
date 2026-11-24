import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4534

theorem key (x1 x2 x3 x4 : List ℕ)
    (h12 : ∀ i : Fin x2.length, ∃ u ∈ x1 ++ List.take (↑i) x2, ∃ w ∈ x1 ++ List.take (↑i) x2,
      x2.get i = u &&& w ∨ x2.get i = u ||| w)
    (h3 : ∀ z ∈ x3, z ∈ x1 ++ x2)
    (h34 : ∀ i : Fin x4.length, ∃ u ∈ x3 ++ List.take (↑i) x4, ∃ w ∈ x3 ++ List.take (↑i) x4,
      x4.get i = u &&& w ∨ x4.get i = u ||| w) :
    ∀ i : Fin (x2 ++ x4).length, ∃ u ∈ x1 ++ List.take (↑i) (x2 ++ x4),
      ∃ w ∈ x1 ++ List.take (↑i) (x2 ++ x4),
      (x2 ++ x4).get i = u &&& w ∨ (x2 ++ x4).get i = u ||| w := by
  intro ⟨i, hi⟩
  have hlen : i < x2.length + x4.length := by simpa using hi
  by_cases hlt : i < x2.length
  · obtain ⟨u, hu, w, hw, h⟩ := h12 ⟨i, hlt⟩
    have htake : List.take i (x2 ++ x4) = List.take i x2 :=
      List.take_append_of_le_length (by omega)
    have hget : (x2 ++ x4).get ⟨i, hi⟩ = x2.get ⟨i, hlt⟩ := by
      simp only [List.get_eq_getElem]
      exact List.getElem_append_left hlt
    refine ⟨u, ?_, w, ?_, ?_⟩
    · simpa only [htake] using hu
    · simpa only [htake] using hw
    · rw [hget]; exact h
  · have hle : x2.length ≤ i := by omega
    have hj : i - x2.length < x4.length := by omega
    obtain ⟨u, hu, w, hw, h⟩ := h34 ⟨i - x2.length, hj⟩
    have htake : List.take i (x2 ++ x4) = x2 ++ List.take (i - x2.length) x4 := by
      rw [List.take_append, List.take_of_length_le hle]
    have hsub : ∀ z ∈ x3 ++ List.take (i - x2.length) x4,
        z ∈ x1 ++ List.take i (x2 ++ x4) := by
      intro z hz
      rw [htake]
      rcases List.mem_append.mp hz with hz | hz
      · have hz' := h3 z hz
        rcases List.mem_append.mp hz' with hz' | hz'
        · exact List.mem_append_left _ hz'
        · exact List.mem_append_right _ (List.mem_append_left _ hz')
      · exact List.mem_append_right _ (List.mem_append_right _ hz)
    have hget : (x2 ++ x4).get ⟨i, hi⟩ = x4.get ⟨i - x2.length, hj⟩ := by
      simp only [List.get_eq_getElem]
      exact List.getElem_append_right hle
    refine ⟨u, hsub u hu, w, hsub w hw, ?_⟩
    rw [hget]; exact h

end PEqualNP.Outside.L_meta_4534

theorem PEqualNP.Outside.L_meta_4534 : ∀ (x1 x2 x3 x4 : List ℕ),   have x5 : List ℕ → List ℕ → Prop := fun (x5 x6 : List ℕ) => ∀ (x7 : Fin x6.length), ∃ x8 ∈ x5 ++ List.take (↑x7) x6, ∃ x9 ∈ x5 ++ List.take (↑x7) x6, x6.get x7 = x8 &&& x9 ∨ x6.get x7 = x8 ||| x9;   x5 x1 x2 → (∀ x7 ∈ x3, x7 ∈ x1 ++ x2) → x5 x3 x4 → x5 x1 (x2 ++ x4) := by
  intro x1 x2 x3 x4
  dsimp only
  intro h12 h3 h34
  exact PEqualNP.Outside.L_meta_4534.key x1 x2 x3 x4 h12 h3 h34
