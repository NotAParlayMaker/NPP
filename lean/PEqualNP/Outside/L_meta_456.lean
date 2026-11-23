import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_456 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hx hy hxy w
  let φ : Fin (m + 2 * k * (m * m)) → ℕ := fun z =>
    if z.val < m then (if z.val = x.val then 0 else 2 * k + 1)
    else if (z.val - m) / (2 * k) / m = x.val then (z.val - m) % (2 * k) + 1
    else if (z.val - m) / (2 * k) % m = x.val then 2 * k - (z.val - m) % (2 * k)
    else 2 * k + 1
  have hφ0 : ∀ z : Fin (m + 2 * k * (m * m)), z.val < m → φ z = if z.val = x.val then 0 else 2 * k + 1 := by
    intro z hz
    simp only [φ, ite_eq_left hz]
  have hφ1 : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))), 1 ≤ p → p ≤ 2 * k → z.val + 1 = m + 2 * k * (u.val * m + v.val) + p → φ z = if u.val = x.val then p else if v.val = x.val then 2 * k + 1 - p else 2 * k + 1 := by
    intro u v p z h1 h2 h3
    have hvm := v.isLt
    have hz : ¬ z.val < m := by omega
    have ht : z.val - m = 2 * k * (u.val * m + v.val) + (p - 1) := by omega
    have hb : (z.val - m) / (2 * k) = u.val * m + v.val := by
      rw [ht, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
      simp
    have hr : (z.val - m) % (2 * k) = p - 1 := by
      rw [ht, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hu : (u.val * m + v.val) / m = u.val := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hvm]
      simp
    have hv : (u.val * m + v.val) % m = v.val := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hvm]
    simp only [φ, ite_eq_right hz, hb, hr, hu, hv]
    split_ifs <;> omega
  have hL : ∀ a b : Fin (m + 2 * k * (m * m)), S.Adj a b → φ b ≤ φ a + 1 ∧ φ a ≤ φ b + 1 := by
    intro a b hab
    rcases (hS a b).1 hab with ⟨u, v, huv, hadj, p, hp, h⟩
    have huv' : u.val < v.val := huv
    have key : ∀ a b : Fin (m + 2 * k * (m * m)), Q u v p a → Q u v (p + 1) b → φ b ≤ φ a + 1 ∧ φ a ≤ φ b + 1 := by
      intro a b ha hb
      rw [hQ] at ha hb
      have hu := u.isLt
      have hv := v.isLt
      rcases ha with ⟨hp0, ha⟩ | ⟨hp0, ha⟩ | ⟨ha1, ha2, ha⟩
      · have ea := hφ0 a (by omega)
        rcases hb with ⟨hq, hb⟩ | ⟨hq, hb⟩ | ⟨hb1, hb2, hb⟩
        · omega
        · omega
        · have eb := hφ1 u v (p + 1) b hb1 hb2 hb
          rw [ea, eb]
          split_ifs <;> omega
      · omega
      · have ea := hφ1 u v p a ha1 ha2 ha
        rcases hb with ⟨hq, hb⟩ | ⟨hq, hb⟩ | ⟨hb1, hb2, hb⟩
        · omega
        · have eb := hφ0 b (by omega)
          rw [ea, eb]
          split_ifs <;> omega
        · have eb := hφ1 u v (p + 1) b hb1 hb2 hb
          rw [ea, eb]
          split_ifs <;> omega
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact key a b h1 h2
    · exact (key b a h1 h2).symm
  have hW : ∀ (a b : Fin (m + 2 * k * (m * m))) (q : S.Walk a b), φ b ≤ φ a + q.length := by
    intro a b q
    induction q with
    | nil => simp
    | cons h q ih =>
      have h1 := (hL _ _ h).1
      rw [SimpleGraph.Walk.length_cons]
      omega
  have h0 := hW x y w
  have e0 := hφ0 x hx
  have e1 := hφ0 y hy
  have hne : ¬ y.val = x.val := fun e => hxy (Fin.ext e.symm)
  rw [ite_eq_left rfl] at e0
  rw [ite_eq_right hne] at e1
  omega
