import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_448_aux

theorem no_self {m k : ℕ} {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hk : 1 ≤ k) {u v : Fin m} (huv : u < v) {p : ℕ} (hp : p ≤ 2 * k)
    {x : Fin (m + 2 * k * (m * m))} (h1 : Q u v p x) (h2 : Q u v (p + 1) x) : False := by
  have h1' := (hQ u v p x).mp h1
  have h2' := (hQ u v (p + 1) x).mp h2
  have hu : u.val < m := u.isLt
  have hv : v.val < m := v.isLt
  have huv' : u.val < v.val := huv
  have hA : (0 : ℕ) ≤ 2 * k * (u.val * m + v.val) := Nat.zero_le _
  rcases h1' with ⟨e1, f1⟩ | ⟨e1, f1⟩ | ⟨e1, f1⟩ <;>
    rcases h2' with ⟨e2, f2⟩ | ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
    omega

end PEqualNP.Outside.L_meta_448_aux

theorem PEqualNP.Outside.L_meta_448 :
∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  refine ⟨⟨fun x y => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)), ?_, ?_⟩, ?_⟩
  · refine ⟨fun x y h => ?_⟩
    obtain ⟨u, v, huv, hH, p, hp, hpq⟩ := h
    exact ⟨u, v, huv, hH, p, hp, hpq.elim (fun hh => Or.inr hh) (fun hh => Or.inl hh)⟩
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨u, v, huv, hH, p, hp, hpq⟩ := hx
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact PEqualNP.Outside.L_meta_448_aux.no_self hQ hk huv hp h1 h2
    · exact PEqualNP.Outside.L_meta_448_aux.no_self hQ hk huv hp h1 h2
  · intro x y
    rfl
