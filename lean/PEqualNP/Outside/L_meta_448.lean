import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_448 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  let Adj : Fin (m + 2 * k * (m * m)) → Fin (m + 2 * k * (m * m)) → Prop :=
    fun x y => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))
  refine ⟨{ Adj := Adj, symm := ⟨?_⟩, loopless := ⟨?_⟩ }, ?_⟩
  · intro x y h
    rcases h with ⟨u, v, huv, hH, p, hp, h | h⟩
    · exact ⟨u, v, huv, hH, p, hp, Or.inr h⟩
    · exact ⟨u, v, huv, hH, p, hp, Or.inl h⟩
  · intro x h
    rcases h with ⟨u, v, huv, hH, p, hp, h | h⟩
    · rcases h with ⟨h1, h2⟩
      have h1' := (hQ u v p x).1 h1
      have h2' := (hQ u v (p + 1) x).1 h2
      rcases h1' with ⟨hp0, hx⟩ | ⟨hpk, hx⟩ | ⟨hp1, hpk, hx⟩ <;>
      rcases h2' with ⟨hp0', hx'⟩ | ⟨hpk', hx'⟩ | ⟨hp1', hpk', hx'⟩ <;>
      omega
    · rcases h with ⟨h1, h2⟩
      have h1' := (hQ u v p x).1 h1
      have h2' := (hQ u v (p + 1) x).1 h2
      rcases h1' with ⟨hp0, hx⟩ | ⟨hpk, hx⟩ | ⟨hp1, hpk, hx⟩ <;>
      rcases h2' with ⟨hp0', hx'⟩ | ⟨hpk', hx'⟩ | ⟨hp1', hpk', hx'⟩ <;>
      omega
  · intro x y
    rfl
