import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_448

def adj (m k : ℕ) (H : SimpleGraph (Fin m))
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (x y : Fin (m + 2 * k * (m * m))) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
    ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))

theorem not_Q_and_Q_succ
    (m k : ℕ)
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hk : 1 ≤ k)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔
        (p = 0 ∧ x.val = u.val) ∨
        (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k) (x : Fin (m + 2 * k * (m * m)))
    (hx1 : Q u v p x) (hx2 : Q u v (p + 1) x) : False := by
  rw [hQ u v p x] at hx1
  rw [hQ u v (p + 1) x] at hx2
  have hu : u.val < m := u.isLt
  have hv : v.val < m := v.isLt
  generalize 2 * k * (u.val * m + v.val) = off at hx1 hx2
  rcases hx1 with ⟨hp0, hxu⟩ | ⟨hp1, _⟩ | ⟨hp_lo, _, hxo⟩
  · rcases hx2 with ⟨hp2, _⟩ | ⟨hp2, _⟩ | ⟨_, _, hxo2⟩
    · omega
    · omega
    · omega
  · omega
  · rcases hx2 with ⟨hp2, _⟩ | ⟨_, hxv⟩ | ⟨_, _, hxo2⟩
    · omega
    · omega
    · omega

def subdivGraph (m k : ℕ) (H : SimpleGraph (Fin m))
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hk : 1 ≤ k)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔
        (p = 0 ∧ x.val = u.val) ∨
        (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) :
    SimpleGraph (Fin (m + 2 * k * (m * m))) where
  Adj := adj m k H Q
  symm := by
    constructor
    intro x y h
    dsimp only [adj] at h ⊢
    rcases h with ⟨u, v, huv, hadj, p, hp, hq⟩
    exact ⟨u, v, huv, hadj, p, hp, Or.elim hq Or.inr Or.inl⟩
  loopless := by
    constructor
    intro x h
    dsimp only [adj] at h
    rcases h with ⟨u, v, _, _, p, hp, hq⟩
    rcases hq with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · exact not_Q_and_Q_succ m k Q hk hQ u v p hp x hx1 hx2
    · exact not_Q_and_Q_succ m k Q hk hQ u v p hp x hx1 hx2

end PEqualNP.Outside.L_meta_448

theorem PEqualNP.Outside.L_meta_448 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  refine ⟨PEqualNP.Outside.L_meta_448.subdivGraph m k H Q hk hQ, ?_⟩
  intro x y
  exact Iff.rfl
