import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8809_aux

def Ctrl {α : Type} (f : ℕ → Set α) (S : Finset ℕ) (w : ℕ) : Prop :=
  ∀ a b : α, (∀ i ∈ S, a ∈ f i → b ∈ f i) → a ∈ f w → b ∈ f w

theorem gen (α : Type) (n m : ℕ) (f : ℕ → Set α)
    (h : ∀ x7 < m, ∃ x9 < n + x7, ∃ x10 < n + x7, f (n + x7) = f x9 ∪ f x10 ∨ f (n + x7) = f x9 ∨ f (n + x7) = ∅ ∨ f (n + x7) = f x9 ∩ f x10) :
    ∀ k ≤ m, ∀ T : Finset ℕ, T ⊆ Finset.range (n + k) →
      ∃ S ⊆ Finset.range n, S.card ≤ k + T.card ∧ ∀ w ∈ T, Ctrl f S w := by
  intro k
  induction k with
  | zero =>
    intro _ T hT
    refine ⟨T, by simpa using hT, by omega, ?_⟩
    intro w hw a b hab ha
    exact hab w hw ha
  | succ k ih =>
    intro hk T hT
    by_cases hg : n + k ∈ T
    · obtain ⟨x9, h9, x10, h10, hc⟩ := h k (by omega)
      set T' := (T.erase (n + k)) ∪ {x9, x10} with hT'
      have hsub : T' ⊆ Finset.range (n + k) := by
        intro x hx
        rw [hT', Finset.mem_union, Finset.mem_erase] at hx
        simp only [Finset.mem_range]
        rcases hx with ⟨hne, hx⟩ | hx
        · have := hT hx
          simp only [Finset.mem_range] at this
          omega
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          omega
      have hcard : T'.card ≤ T.card + 1 := by
        rw [hT']
        have h1 := Finset.card_union_le (T.erase (n + k)) {x9, x10}
        have h2 := Finset.card_erase_of_mem hg
        have h3 : ({x9, x10} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        have h4 : 0 < T.card := Finset.card_pos.mpr ⟨_, hg⟩
        omega
      obtain ⟨S, hS, hSc, hSw⟩ := ih (by omega) T' hsub
      refine ⟨S, hS, by omega, ?_⟩
      intro w hw
      by_cases hwg : w = n + k
      · subst hwg
        have c9 := hSw x9 (by rw [hT']; simp)
        have c10 := hSw x10 (by rw [hT']; simp)
        intro a b hab ha
        rcases hc with e | e | e | e <;> rw [e] at ha ⊢
        · rcases ha with ha | ha
          · exact Or.inl (c9 a b hab ha)
          · exact Or.inr (c10 a b hab ha)
        · exact c9 a b hab ha
        · exact ha.elim
        · exact ⟨c9 a b hab ha.1, c10 a b hab ha.2⟩
      · exact hSw w (by rw [hT']; simp [hwg, hw])
    · have hsub : T ⊆ Finset.range (n + k) := by
        intro x hx
        have := hT hx
        simp only [Finset.mem_range] at this ⊢
        have : x ≠ n + k := fun e => hg (e ▸ hx)
        omega
      obtain ⟨S, hS, hSc, hSw⟩ := ih (by omega) T hsub
      exact ⟨S, hS, by omega, hSw⟩

end PEqualNP.Outside.L_meta_8809_aux

open PEqualNP.Outside.L_meta_8809_aux in
theorem PEqualNP.Outside.L_meta_8809 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1), x4 < x2 + x3 → (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x5 (x2 + x7) = x5 x9 ∪ x5 x10 ∨ x5 (x2 + x7) = x5 x9 ∨ x5 (x2 + x7) = ∅ ∨ x5 (x2 + x7) = x5 x9 ∩ x5 x10) → ∃ x8 ⊆ Finset.range x2, x8.card ≤ x3 + (1 : ℕ) ∧ ∀ (x9 x10 : x1), (∀ x11 ∈ x8, x9 ∈ x5 x11 → x10 ∈ x5 x11) → x9 ∈ x5 x4 → x10 ∈ x5 x4 := by
  intro x1 x2 x3 x4 x5 h4 h
  obtain ⟨S, hS, hc, hw⟩ := gen x1 x2 x3 x5 h x3 le_rfl {x4} (by simpa using h4)
  refine ⟨S, hS, by simpa using hc, ?_⟩
  exact hw x4 (by simp)
