import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_467 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ T' ∨ y ∈ T' := by
  intro m k H Q S hk hQ hS T T' hT hT' x y hxy
  have original (z : Fin (m + 2 * k * (m * m))) (u : Fin m)
      (hu : u ∈ T) (hz : z.val = u.val) : z ∈ T' :=
    (hT' z).2 (Or.inl ⟨u, hu, hz⟩)
  have interior (z : Fin (m + 2 * k * (m * m))) (u v : Fin m) (i : ℕ)
      (hi : i < 2 * k) (huv : u < v) (he : H.Adj u v)
      (hz : z.val = m + 2 * k * (u.val * m + v.val) + i)
      (hpar : i % 2 = 1 ↔ u ∈ T) : z ∈ T' :=
    (hT' z).2 (Or.inr ⟨u, v, i, hi, huv, he, hz, hpar⟩)
  have path (u v : Fin m) (p : ℕ) (a b : Fin (m + 2 * k * (m * m)))
      (huv : u < v) (he : H.Adj u v) (hp : p ≤ 2 * k)
      (ha : Q u v p a) (hb : Q u v (p + 1) b) : a ∈ T' ∨ b ∈ T' := by
    have ha' := (hQ u v p a).1 ha
    have hb' := (hQ u v (p + 1) b).1 hb
    by_cases hzero : p = 0
    · have hav : a.val = u.val := by
        rcases ha' with h | h | h <;> omega
      by_cases hu : u ∈ T
      · exact Or.inl (original a u hu hav)
      · right
        apply interior b u v 0 (by omega) huv he
        · rcases hb' with h | h | h <;> omega
        · simp [hu]
    · by_cases hlast : p = 2 * k
      · have hbv : b.val = v.val := by
          rcases hb' with h | h | h <;> omega
        by_cases hu : u ∈ T
        · left
          apply interior a u v (p - 1) (by omega) huv he
          · rcases ha' with h | h | h <;> omega
          · simp only [hu, iff_true]
            omega
        · exact Or.inr (original b v ((hT u v he).resolve_left hu) hbv)
      · have hav : a.val = m + 2 * k * (u.val * m + v.val) + (p - 1) := by
          rcases ha' with h | h | h <;> omega
        have hbv : b.val = m + 2 * k * (u.val * m + v.val) + p := by
          rcases hb' with h | h | h <;> omega
        by_cases hpar : (p - 1) % 2 = 1 ↔ u ∈ T
        · exact Or.inl (interior a u v (p - 1) (by omega) huv he hav hpar)
        · right
          apply interior b u v p (by omega) huv he hbv
          by_cases hu : u ∈ T
          · simp only [hu, iff_true] at hpar ⊢
            omega
          · simp only [hu, iff_false, not_not] at hpar ⊢
            omega
  rcases (hS x y).1 hxy with ⟨u, v, huv, he, p, hp, h | h⟩
  · exact path u v p x y huv he hp h.1 h.2
  · exact (path u v p y x huv he hp h.1 h.2).symm
