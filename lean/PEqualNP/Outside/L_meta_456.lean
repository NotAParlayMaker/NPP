import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

theorem PEqualNP.Outside.L_meta_456 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk position edge x y hx hy different path
  let D := 2 * k + 1
  -- The height rises along threads leaving x and falls along threads entering x.
  let profile (u v p : ℕ) := if u = x.val then p else if v = x.val then D - p else D
  let height (z : Fin (m + 2 * k * (m * m))) :=
    if z.val < m then (if z.val = x.val then 0 else D)
    else
      let offset := z.val - m
      let block := offset / (2 * k)
      profile (block / m) (block % m) (offset % (2 * k) + 1)
  have value {u v : Fin m} (uv : u < v) {p z} (onThread : Q u v p z) :
      height z = profile u.val v.val p := by
    rcases (position u v p z).mp onThread with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨lo, hi, h⟩
    · simp [height, h, profile]
    · have hne : u.val ≠ v.val := Nat.ne_of_lt uv
      simp only [height, h, v.isLt, ite_true, profile, D]
      split_ifs <;> omega
    · let block := u.val * m + v.val
      have hoff : z.val - m = (p - 1) + (2 * k) * block := by
        dsimp [block]
        omega
      have hz : ¬ z.val < m := by omega
      have remLt : p - 1 < 2 * k := by omega
      have blockDiv : block / m = u.val := by
        dsimp [block]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < m),
          Nat.div_eq_of_lt v.isLt, Nat.zero_add]
      have blockMod : block % m = v.val := by
        dsimp [block]
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]
      simp only [height, hz, ite_false, hoff, Nat.add_mul_div_left _ _ (by omega : 0 < 2 * k),
        Nat.div_eq_of_lt remLt, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt remLt,
        blockDiv, blockMod, Nat.sub_add_cancel lo]
  have adjacent {a b} (h : S.Adj a b) : height b ≤ height a + 1 := by
    obtain ⟨u, v, uv, _, p, _, forward | backward⟩ := (edge a b).mp h
    · rw [value uv forward.1, value uv forward.2]
      simp only [profile]
      split_ifs <;> omega
    · rw [value uv backward.1, value uv backward.2]
      simp only [profile]
      split_ifs <;> omega
  have walkBound {a b} (w : S.Walk a b) : height b ≤ height a + w.length := by
    induction w with
    | nil => simp
    | cons h w ih =>
      have step := adjacent h
      rw [SimpleGraph.Walk.length_cons]
      omega
  have hxy : y.val ≠ x.val := fun h => different (Fin.ext h.symm)
  simpa [height, hx, hy, hxy, D] using walkBound path
