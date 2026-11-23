import Mathlib
import PEqualNP.Defs

theorem L451_divuniq (d a b r s : ℕ) (hr : r < d) (hs : s < d)
    (h : d * a + r = d * b + s) : a = b ∧ r = s := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have h1 : d * (a + 1) ≤ d * b := Nat.mul_le_mul (le_refl d) hab
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  · subst hab
    omega
  · have h1 : d * (b + 1) ≤ d * a := Nat.mul_le_mul (le_refl d) hab
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega

theorem PEqualNP.Outside.L_meta_451 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x → (S.neighborSet x).ncard = 2 := by
  intro m k H Q S hk hQ hS u v p x huv hadj hp1 hp2 hx
  have hu := u.isLt
  have hv := v.isLt
  have hxN := x.isLt
  have hxv : x.val + 1 = m + 2 * k * (u.val * m + v.val) + p := by
    rcases (hQ u v p x).1 hx with h | h | h <;> omega
  have hA : u.val * m + v.val + 1 ≤ m * m := by
    have h1 : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul (Nat.succ_le_of_lt hu) (le_refl m)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  have hB : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
    Nat.mul_le_mul (le_refl _) hA
  rw [Nat.mul_add, Nat.mul_one] at hB
  have huniq : ∀ (u' v' : Fin m) (q : ℕ), 1 ≤ q → q ≤ 2 * k →
      x.val + 1 = m + 2 * k * (u'.val * m + v'.val) + q → u' = u ∧ v' = v ∧ q = p := by
    intro u' v' q hq1 hq2 h
    have e : 2 * k * (u'.val * m + v'.val) + (q - 1) = 2 * k * (u.val * m + v.val) + (p - 1) := by
      omega
    obtain ⟨e1, e2⟩ := L451_divuniq (2 * k) _ _ _ _ (by omega) (by omega) e
    have e3 : m * u'.val + v'.val = m * u.val + v.val := by
      rw [Nat.mul_comm m u'.val, Nat.mul_comm m u.val]
      exact e1
    obtain ⟨e4, e5⟩ := L451_divuniq m _ _ _ _ v'.isLt v.isLt e3
    exact ⟨Fin.ext e4, Fin.ext e5, by omega⟩
  obtain ⟨y1, hy1⟩ : ∃ y : Fin (m + 2 * k * (m * m)),
      y.val = if p = 1 then u.val else x.val - 1 :=
    ⟨⟨if p = 1 then u.val else x.val - 1, by split_ifs <;> omega⟩, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y : Fin (m + 2 * k * (m * m)),
      y.val = if p = 2 * k then v.val else x.val + 1 :=
    ⟨⟨if p = 2 * k then v.val else x.val + 1, by split_ifs <;> omega⟩, rfl⟩
  have hset : S.neighborSet x = {y1, y2} := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff, hS]
    constructor
    · rintro ⟨u', v', -, -, q, hq, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
      · have hu' := u'.isLt
        have hv' := v'.isLt
        rw [hQ] at h1 h2
        rcases h1 with h1 | h1 | h1
        · omega
        · omega
        · obtain ⟨e1, e2, e3⟩ := huniq u' v' q h1.1 h1.2.1 h1.2.2
          subst e1 e2 e3
          right
          apply Fin.ext
          rw [hy2]
          split_ifs with hc <;> rcases h2 with h2 | h2 | h2 <;> omega
      · have hu' := u'.isLt
        have hv' := v'.isLt
        rw [hQ] at h1 h2
        rcases h2 with h2 | h2 | h2
        · omega
        · omega
        · obtain ⟨e1, e2, e3⟩ := huniq u' v' (q + 1) h2.1 h2.2.1 h2.2.2
          subst e1 e2 e3
          left
          apply Fin.ext
          rw [hy1]
          split_ifs with hc <;> rcases h1 with h1 | h1 | h1 <;> omega
    · rintro (rfl | rfl)
      · refine ⟨u, v, huv, hadj, p - 1, by omega, Or.inr ⟨?_, ?_⟩⟩
        · rw [hQ, hy1]
          split_ifs with hc <;> omega
        · have e : p - 1 + 1 = p := by omega
          rw [e]
          exact hx
      · refine ⟨u, v, huv, hadj, p, hp2, Or.inl ⟨hx, ?_⟩⟩
        rw [hQ, hy2]
        split_ifs with hc <;> omega
  rw [hset]
  apply Set.ncard_pair
  intro h
  have e := congrArg Fin.val h
  rw [hy1, hy2] at e
  split_ifs at e <;> omega
