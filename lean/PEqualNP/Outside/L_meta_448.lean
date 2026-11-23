import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_448 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  let R : Fin (m + 2 * k * (m * m)) → Fin (m + 2 * k * (m * m)) → Prop := fun x y =>
    ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))
  have hsymm : ∀ x y, R x y → R y x := by
    rintro x y ⟨u, v, huv, hadj, p, hp, h⟩
    exact ⟨u, v, huv, hadj, p, hp, h.symm⟩
  have hne : ∀ x y, R x y → x ≠ y := by
    rintro x y ⟨u, v, _, _, p, hp, h⟩ rfl
    have key : ¬ (Q u v p x ∧ Q u v (p + 1) x) := by
      rintro ⟨h1, h2⟩
      rw [hQ] at h1 h2
      have hu := u.isLt
      have hv := v.isLt
      generalize 2 * k * (u.val * m + v.val) = w at h1 h2
      omega
    rcases h with h | h
    · exact key h
    · exact key h
  refine ⟨SimpleGraph.fromRel R, fun x y => ?_⟩
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact hsymm _ _ h
  · intro h
    exact ⟨hne x y h, Or.inl h⟩
