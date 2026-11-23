import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_467 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ T' ∨ y ∈ T' := by
  intro m k H Q S hk hQ hS T T' hcov hT' x y hxy
  rw [hS] at hxy
  obtain ⟨u, v, huv, hadj, p, hp, h⟩ := hxy
  have sel : ∀ (q : ℕ) (z : Fin (m + 2 * k * (m * m))), Q u v q z →
      (q % 2 = 0 ↔ u ∈ T) → z ∈ T' := by
    intro q z hq hpar
    rw [hT']
    rw [hQ] at hq
    rcases hq with ⟨rfl, hz⟩ | ⟨rfl, hz⟩ | ⟨h1, h2, hz⟩
    · exact Or.inl ⟨u, hpar.mp rfl, hz⟩
    · have hu : u ∉ T := fun hu => by
        have := hpar.mpr hu
        omega
      exact Or.inl ⟨v, (hcov u v hadj).resolve_left hu, hz⟩
    · refine Or.inr ⟨u, v, q - 1, by omega, huv, hadj, ?_, ?_⟩
      · generalize 2 * k * (u.val * m + v.val) = w at hz ⊢
        omega
      · rw [← hpar]
        constructor <;> intro h <;> omega
  have flip : ∀ q : ℕ, ¬ (q % 2 = 0 ↔ u ∈ T) → ((q + 1) % 2 = 0 ↔ u ∈ T) := by
    intro q hc
    by_cases hu : u ∈ T <;> simp only [hu, iff_true, iff_false] at hc ⊢ <;> omega
  rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · by_cases hc : (p % 2 = 0 ↔ u ∈ T)
    · exact Or.inl (sel p x hx hc)
    · exact Or.inr (sel (p + 1) y hy (flip p hc))
  · by_cases hc : (p % 2 = 0 ↔ u ∈ T)
    · exact Or.inr (sel p y hy hc)
    · exact Or.inl (sel (p + 1) x hx (flip p hc))
