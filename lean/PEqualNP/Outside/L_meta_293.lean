import Mathlib.Combinatorics.SimpleGraph.Basic

theorem PEqualNP.Outside.L_meta_293 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop),
      1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
          (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))),
        (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
            ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  refine ⟨{
    Adj := fun x y => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
      ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))
    symm := ⟨by
      rintro x y ⟨u, v, huv, hadj, p, hp, h⟩
      exact ⟨u, v, huv, hadj, p, hp, h.symm⟩⟩
    loopless := ⟨by
      intro x ⟨u, v, huv, _, p, hp, h⟩
      have hboth : Q u v p x ∧ Q u v (p + 1) x := h.elim id id
      have h1 := (hQ u v p x).mp hboth.1
      have h2 := (hQ u v (p + 1) x).mp hboth.2
      have hu : u.val < m := u.isLt
      have hv : v.val < m := v.isLt
      rcases h1 with ⟨hp0, hxu⟩ | ⟨hp1, hxv⟩ | ⟨hp_lo, hp_hi, hxp⟩ <;>
        rcases h2 with ⟨hq0, hxu'⟩ | ⟨hq1, hxv'⟩ | ⟨hq_lo, hq_hi, hxp'⟩ <;>
        omega⟩
  }, fun _ _ => Iff.rfl⟩
