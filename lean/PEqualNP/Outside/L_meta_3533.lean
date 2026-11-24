import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3533
open PEqualNP.CircuitLowerBounds



def SL (a l : List ℕ) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), ∃ p ∈ a ++ l.take i, ∃ q ∈ a ++ l.take i, l[i] = p &&& q ∨ l[i] = p ||| q

theorem sl_main (a : List ℕ) : ∀ l : List ℕ, SL a l →
    ∃ r : List ℕ, r.length ≤ l.length ∧ r.Nodup ∧ (∀ y ∈ r, y ∉ a) ∧ (∀ y ∈ l, y ∈ a ∨ y ∈ r) ∧ SL a r := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], le_refl _, List.nodup_nil, ?_, ?_, ?_⟩
    · intro y hy; cases hy
    · intro y hy; cases hy
    · intro i h; cases h
  | append_singleton l x ih =>
    intro hS
    have hl : SL a l := by
      intro i h
      have h2 : i < (l ++ [x]).length := by rw [List.length_append]; exact Nat.lt_add_right _ h
      have h3 := hS i h2
      rw [List.take_append_of_le_length (Nat.le_of_lt h), List.getElem_append_left h] at h3
      exact h3
    obtain ⟨r, hr1, hr2, hr3, hr4, hr5⟩ := ih hl
    have hlast : ∃ p ∈ a ++ l, ∃ q ∈ a ++ l, x = p &&& q ∨ x = p ||| q := by
      have h2 : l.length < (l ++ [x]).length := by rw [List.length_append]; exact Nat.lt_succ_self _
      have h3 := hS l.length h2
      rw [List.take_left, List.getElem_append_right (le_refl _)] at h3
      simpa using h3
    by_cases hx : x ∈ a ∨ x ∈ r
    · refine ⟨r, ?_, hr2, hr3, ?_, hr5⟩
      · rw [List.length_append]; exact Nat.le_succ_of_le hr1
      · intro y hy
        rcases List.mem_append.1 hy with h | h
        · exact hr4 y h
        · rw [List.mem_singleton] at h; rw [h]; exact hx
    · have hxa : x ∉ a := fun h => hx (Or.inl h)
      have hxr : x ∉ r := fun h => hx (Or.inr h)
      refine ⟨r ++ [x], ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_append]; exact Nat.succ_le_succ hr1
      · rw [List.nodup_append]
        refine ⟨hr2, List.nodup_singleton x, ?_⟩
        intro u hu v hv
        rw [List.mem_singleton] at hv
        intro huv
        rw [hv] at huv
        rw [huv] at hu
        exact hxr hu
      · intro y hy
        rcases List.mem_append.1 hy with h | h
        · exact hr3 y h
        · rw [List.mem_singleton] at h; rw [h]; exact hxa
      · intro y hy
        rcases List.mem_append.1 hy with h | h
        · rcases hr4 y h with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (List.mem_append.2 (Or.inl h1))
        · exact Or.inr (List.mem_append.2 (Or.inr h))
      · intro i h
        rw [List.length_append] at h
        rcases Nat.lt_or_ge i r.length with h1 | h1
        · have h3 := hr5 i h1
          rw [List.take_append_of_le_length (Nat.le_of_lt h1), List.getElem_append_left h1]
          exact h3
        · have h4 : i = r.length := Nat.le_antisymm (Nat.le_of_lt_succ h) h1
          subst h4
          obtain ⟨p, hp, q, hq, hpq⟩ := hlast
          have conv : ∀ z, z ∈ a ++ l → z ∈ a ++ r := by
            intro z hz
            rcases List.mem_append.1 hz with h5 | h5
            · exact List.mem_append.2 (Or.inl h5)
            · rcases hr4 z h5 with h6 | h6
              · exact List.mem_append.2 (Or.inl h6)
              · exact List.mem_append.2 (Or.inr h6)
          rw [List.take_left, List.getElem_append_right (le_refl _)]
          refine ⟨p, conv p hp, q, conv q hq, ?_⟩
          simpa using hpq

end PEqualNP.Outside.L_meta_3533

open PEqualNP.Outside.L_meta_3533 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3533 : ∀ (x1 x2 : List ℕ), ∀ x3 ∉ x1, x3 ∈ x2 → (∀ (x6 : Fin x2.length), ∃ x7 ∈ x1 ++ List.take (↑x6) x2, ∃ x8 ∈ x1 ++ List.take (↑x6) x2, x2.get x6 = x7 &&& x8 ∨ x2.get x6 = x7 ||| x8) → ∃ (x7 : List ℕ), x7.length ≤ x2.length ∧ x7.Nodup ∧ (∀ x8 ∈ x7, x8 ∉ x1) ∧ x3 ∈ x7 ∧ ∀ (x8 : Fin x7.length), ∃ x9 ∈ x1 ++ List.take (↑x8) x7, ∃ x10 ∈ x1 ++ List.take (↑x8) x7, x7.get x8 = x9 &&& x10 ∨ x7.get x8 = x9 ||| x10 := by
  intro x1 x2 x3 h3 h4 h5
  have hS : SL x1 x2 := fun i h => h5 ⟨i, h⟩
  obtain ⟨r, hr1, hr2, hr3, hr4, hr5⟩ := sl_main x1 x2 hS
  refine ⟨r, hr1, hr2, hr3, ?_, fun i => hr5 i.1 i.2⟩
  rcases hr4 x3 h4 with h | h
  · exact absurd h h3
  · exact h
