import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

theorem PEqualNP.Outside.L_meta_302 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ T' ∨ y ∈ T' := by
  intro m k H Q S hk hQ hS T T' hT hT' x y hxy
  obtain ⟨u, v, huv, hadj, p, hp, hcase⟩ := (hS x y).mp hxy
  suffices h : ∀ a b : Fin (m + 2 * k * (m * m)), Q u v p a → Q u v (p + 1) b → a ∈ T' ∨ b ∈ T' by
    rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact h x y ha hb
    · exact (h y x ha hb).symm
  intro a b ha hb
  have ha' := (hQ u v p a).mp ha
  have hb' := (hQ u v (p + 1) b).mp hb
  by_cases hp0 : p = 0
  · subst hp0
    have hax : a.val = u.val := by
      rcases ha' with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _, _⟩
      · exact h
      · omega
      · omega
    have hby : b.val = m + 2 * k * (u.val * m + v.val) + 0 := by
      rcases hb' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩
      · omega
      · omega
      · omega
    by_cases hu : u ∈ T
    · left
      exact (hT' a).mpr (Or.inl ⟨u, hu, hax⟩)
    · right
      refine (hT' b).mpr (Or.inr ⟨u, v, 0, by omega, huv, hadj, hby, ?_⟩)
      simp [hu]
  · by_cases hp2k : p = 2 * k
    · subst hp2k
      have hax : a.val = m + 2 * k * (u.val * m + v.val) + (2 * k - 1) := by
        rcases ha' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩
        · omega
        · omega
        · omega
      have hby : b.val = v.val := by
        rcases hb' with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h, _⟩
        · omega
        · exact h
        · omega
      rcases hT u v hadj with hu | hv
      · left
        refine (hT' a).mpr (Or.inr ⟨u, v, 2 * k - 1, by omega, huv, hadj, hax, ?_⟩)
        constructor
        · intro _; exact hu
        · intro _; omega
      · right
        exact (hT' b).mpr (Or.inl ⟨v, hv, hby⟩)
    · have hax : a.val = m + 2 * k * (u.val * m + v.val) + (p - 1) := by
        rcases ha' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩
        · omega
        · omega
        · omega
      have hby : b.val = m + 2 * k * (u.val * m + v.val) + p := by
        rcases hb' with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h⟩
        · omega
        · omega
        · omega
      by_cases hpar : (p - 1) % 2 = 1 ↔ u ∈ T
      · left
        exact (hT' a).mpr (Or.inr ⟨u, v, p - 1, by omega, huv, hadj, hax, hpar⟩)
      · right
        refine (hT' b).mpr (Or.inr ⟨u, v, p, by omega, huv, hadj, hby, ?_⟩)
        by_cases hu : u ∈ T
        · have hne : (p - 1) % 2 ≠ 1 := fun h => hpar (iff_of_true h hu)
          exact iff_of_true (by omega) hu
        · have heq : (p - 1) % 2 = 1 := by
            by_contra hne
            exact hpar (iff_of_false hne hu)
          exact iff_of_false (by omega) hu
