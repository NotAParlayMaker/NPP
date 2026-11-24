import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_448 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  refine ⟨{ Adj := fun x y => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))
            symm := ?_
            loopless := ?_ }, fun x y => Iff.rfl⟩
  · constructor
    intro x y h
    obtain ⟨u, v, huv, hadj, p, hp, h⟩ := h
    exact ⟨u, v, huv, hadj, p, hp, h.symm⟩
  · constructor
    intro x h
    obtain ⟨u, v, _, _, p, hp, h⟩ := h
    have h' : Q u v p x ∧ Q u v (p + 1) x := by
      rcases h with h | h <;> exact h
    rw [hQ, hQ] at h'
    have hu := u.isLt
    have hv := v.isLt
    generalize 2 * k * (u.val * m + v.val) = A at h'
    omega
