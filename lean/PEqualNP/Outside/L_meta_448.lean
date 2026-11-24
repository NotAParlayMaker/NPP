import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_448 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop),
      1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
          Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
            (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))),
        (∀ x y : Fin (m + 2 * k * (m * m)),
          S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
            ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  refine ⟨{ Adj := fun x y => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
              ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)),
            symm := ?_, loopless := ?_ }, ?_⟩
  · exact ⟨by
      rintro x y ⟨u, v, huv, hH, p, hp, h⟩
      exact ⟨u, v, huv, hH, p, hp, h.symm⟩⟩
  · exact ⟨by
      rintro x ⟨u, v, huv, hH, p, hp, h⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h1' := (hQ u v p x).mp h1
        have h2' := (hQ u v (p + 1) x).mp h2
        have hu : u.val < m := u.isLt
        omega
      · have h1' := (hQ u v p x).mp h1
        have h2' := (hQ u v (p + 1) x).mp h2
        have hu : u.val < m := u.isLt
        omega⟩
  · intro x y
    exact Iff.rfl
