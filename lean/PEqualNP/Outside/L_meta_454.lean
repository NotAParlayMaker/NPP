import Mathlib
import PEqualNP.Defs

theorem L454_bound (m k a b : ℕ) (ha : a < m) (hb : b < m) :
    m + 2 * k * (a * m + b) + (2 * k - 1) < m + 2 * k * (m * m) ∨ k = 0 := by
  rcases Nat.eq_zero_or_pos k with h | h
  · exact Or.inr h
  · left
    have h1 : a * m + b + 1 ≤ m * m := by nlinarith
    have h2 : 2 * k * (a * m + b + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h1
    have h3 : 2 * k * (a * m + b + 1) = 2 * k * (a * m + b) + 2 * k := by ring
    omega

theorem L454_mixed (k A B : ℕ) (hk : 1 ≤ k) (h : 2 * k * A = 2 * k * B + (2 * k - 1)) : False := by
  rcases Nat.lt_or_ge B A with hBA | hAB
  · have h2 : 2 * k * (B + 1) ≤ 2 * k * A := Nat.mul_le_mul_left _ hBA
    have h3 : 2 * k * (B + 1) = 2 * k * B + 2 * k := by ring
    omega
  · have h2 : 2 * k * A ≤ 2 * k * B := Nat.mul_le_mul_left _ hAB
    omega

theorem L454_cancel (k A B : ℕ) (hk : 1 ≤ k) (h : 2 * k * A = 2 * k * B) : A = B := by
  have : 0 < 2 * k := by omega
  exact Nat.eq_of_mul_eq_mul_left this h

theorem PEqualNP.Outside.L_meta_454 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ u : Fin m, (S.neighborSet (Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) u)).ncard = (H.neighborSet u).ncard := by
  intro m k H Q S hk hQ hS u
  have hu : u.val < m := u.isLt
  let f : Fin m → Fin (m + 2 * k * (m * m)) := fun b =>
    ⟨if u < b then m + 2 * k * (u.val * m + b.val) else m + 2 * k * (b.val * m + u.val) + (2 * k - 1), by
      have h1 := L454_bound m k u.val b.val hu b.isLt
      have h2 := L454_bound m k b.val u.val b.isLt hu
      split_ifs <;> omega⟩
  have hinj : Function.Injective f := by
    intro b c hbc
    have hv := congrArg Fin.val hbc
    simp only [f] at hv
    by_cases hb : u < b <;> by_cases hc : u < c <;> simp only [hb, hc, ite_true, ite_false] at hv
    · have := L454_cancel k _ _ hk (by omega : 2 * k * (u.val * m + b.val) = 2 * k * (u.val * m + c.val))
      exact Fin.ext (by omega)
    · exact (L454_mixed k _ _ hk (by omega : 2 * k * (u.val * m + b.val) = 2 * k * (c.val * m + u.val) + (2 * k - 1))).elim
    · exact (L454_mixed k _ _ hk (by omega : 2 * k * (u.val * m + c.val) = 2 * k * (b.val * m + u.val) + (2 * k - 1))).elim
    · have := L454_cancel k _ _ hk (by omega : 2 * k * (b.val * m + u.val) = 2 * k * (c.val * m + u.val))
      have hm : 0 < m := by omega
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right hm (by omega))
  have key : S.neighborSet (Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) u) = f '' H.neighborSet u := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_image]
    rw [hS]
    simp only [hQ, Fin.val_castLE]
    constructor
    · rintro ⟨a, b, hab, hadj, p, hp, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
      · rcases h1 with ⟨rfl, hua⟩ | ⟨hp', _⟩ | ⟨hp1, _, hc⟩
        · have hua' : u = a := Fin.ext hua
          subst hua'
          rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, hy⟩
          · omega
          · omega
          · refine ⟨b, hadj, ?_⟩
            apply Fin.ext
            simp only [f, hab, ite_true]
            omega
        · omega
        · omega
      · rcases h2 with ⟨h, _⟩ | ⟨h, hub⟩ | ⟨_, _, hc⟩
        · omega
        · have hub' : u = b := Fin.ext hub
          subst hub'
          have hp2 : p = 2 * k := by omega
          subst hp2
          rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, hy⟩
          · omega
          · omega
          · refine ⟨a, hadj.symm, ?_⟩
            apply Fin.ext
            have hna : ¬ u < a := not_lt.mpr hab.le
            simp only [f, hna, ite_false]
            omega
        · omega
    · rintro ⟨b, hb, rfl⟩
      by_cases hub : u < b
      · refine ⟨u, b, hub, hb, 0, by omega, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr ⟨le_rfl, by omega, ?_⟩)⟩⟩
        simp only [f, hub, ite_true]
      · have hne : b ≠ u := (H.ne_of_adj hb).symm
        have hbu : b < u := lt_of_le_of_ne (not_lt.mp hub) hne
        refine ⟨b, u, hbu, hb.symm, 2 * k, le_rfl, Or.inr ⟨Or.inr (Or.inr ⟨by omega, le_rfl, ?_⟩), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩⟩
        simp only [f, hub, ite_false]
        omega
  rw [key, Set.ncard_image_of_injective _ hinj]
