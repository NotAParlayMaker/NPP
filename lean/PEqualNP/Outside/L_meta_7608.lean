import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7608

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7608

theorem PEqualNP.Outside.L_meta_7608 : ∀ (x1 : Type) (x2 x3 : List (Set x1)) (x4 : Set x1),   have x5 : ℕ → List (Set x1) := fun (x5 : ℕ) => x2 ++ List.take x5 x3;   x4 ∈ x2 ++ x3 → (∀ x7 ∈ x2, ¬x7 ⊆ x4) → (∀ (x8 : Fin x3.length), ∃ x9 ∈ x5 ↑x8, ∃ x10 ∈ x5 ↑x8, x3.get x8 = x9 ∪ x10 ∨ x3.get x8 = x9 ∩ x10) → ∀ x9 ∈ x4, ∃ (x11 : Fin x3.length), x3.get x11 ⊆ x4 ∧ x9 ∈ x3.get x11 ∧ ∃ x12 ∈ x5 ↑x11, ∃ x13 ∈ x5 ↑x11, ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
  intro α B G Z take hZ hB hG x hx
  classical
  -- a gate inside `Z` containing `x`, of least index
  have base : ∃ i, ∃ h : i < G.length, G[i] ⊆ Z ∧ x ∈ G[i] := by
    rcases List.mem_append.1 hZ with h | h
    · exact absurd (subset_refl Z) (hB Z h)
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
      exact ⟨i, hi, by rw [e], by rw [e]; exact hx⟩
  obtain ⟨hi, h1, h2⟩ := Nat.find_spec base
  set i := Nat.find base with hidef
  have least : ∀ j, j < i → ∀ h : j < G.length, G[j] ⊆ Z → x ∉ G[j] := by
    intro j hj h a b
    exact Nat.find_min base hj ⟨h, a, b⟩
  have small : ∀ A ∈ take i, A ⊆ Z → x ∈ A → False := by
    intro A hA hAZ hxA
    rcases List.mem_append.1 hA with h | h
    · exact hB A h hAZ
    · obtain ⟨j, hj, e⟩ := List.getElem_of_mem h
      rw [List.length_take] at hj
      rw [List.getElem_take] at e
      exact least j (by omega) (by omega) (by rw [e]; exact hAZ) (by rw [e]; exact hxA)
  obtain ⟨A, hA, D, hD, hval⟩ := hG ⟨i, hi⟩
  simp only [List.get_eq_getElem] at hA hD hval
  refine ⟨⟨i, hi⟩, h1, h2, A, hA, D, hD, ?_⟩
  rcases hval with hval | hval
  · exfalso
    rw [hval] at h1 h2
    rcases h2 with h | h
    · exact small A hA (fun y hy => h1 (Or.inl hy)) h
    · exact small D hD (fun y hy => h1 (Or.inr hy)) h
  · rw [hval] at h1 h2
    exact ⟨fun h => small A hA h h2.1, fun h => small D hD h h2.2, hval⟩
