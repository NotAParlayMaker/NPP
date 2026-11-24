import Mathlib.Combinatorics.SimpleGraph.Basic

theorem PEqualNP.Outside.L_meta_448 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop),
      1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
          (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))),
        ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
            ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)) := by
  intro m k H Q hk hQ
  let A := fun (x y : Fin (m + 2 * k * (m * m))) =>
    ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))
  have hsym : Std.Symm A := by
    constructor
    rintro x y ⟨u, v, huv, he, p, hp, hxy⟩
    exact ⟨u, v, huv, he, p, hp, hxy.symm⟩
  have hloop : ∀ x, ¬ A x x := by
    rintro x ⟨u, v, huv, _, p, hp, hxx⟩
    obtain ⟨ha, hb⟩ := hxx.elim id id
    have ha := (hQ u v p x).mp ha
    have hb := (hQ u v (p + 1) x).mp hb
    have hu := u.isLt
    have hv := v.isLt
    change u.val < v.val at huv
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega
  exact ⟨⟨A, hsym, ⟨hloop⟩⟩, fun _ _ => Iff.rfl⟩
