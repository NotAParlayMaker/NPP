import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

theorem PEqualNP.Outside.L_meta_451 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x → (S.neighborSet x).ncard = 2 := by
  intro m k H Q S hk hQ hS u v p x huv hH hp1 hp2 hx
  have hx_eq : x.val + 1 = m + 2 * k * (u.val * m + v.val) + p := by
    have h := (hQ u v p x).mp hx
    rcases h with ⟨hp0, _⟩ | ⟨hp2k, _⟩ | ⟨_, _, heq⟩
    · omega
    · omega
    · exact heq
  have hQ_unique_val : ∀ (u' v' : Fin m) (r : ℕ) (y₁ y₂ : Fin (m + 2 * k * (m * m))),
      Q u' v' r y₁ → Q u' v' r y₂ → y₁ = y₂ := by
    intro u' v' r y₁ y₂ h1 h2
    have h1' := (hQ u' v' r y₁).mp h1
    have h2' := (hQ u' v' r y₂).mp h2
    apply Fin.ext
    rcases h1' with ⟨hr0, heq1⟩ | ⟨hr2k, heq1⟩ | ⟨hr1, hr2, heq1⟩ <;>
      rcases h2' with ⟨hr0', heq2⟩ | ⟨hr2k', heq2⟩ | ⟨hr1', hr2', heq2⟩ <;>
      omega
  have hQ_unique_idx : ∀ (u' v' : Fin m) (r : ℕ),
      Q u' v' r x → u' = u ∧ v' = v ∧ r = p := by
    intro u' v' r hxr
    have hxr' := (hQ u' v' r x).mp hxr
    have hu' := u'.isLt
    have hv' := v'.isLt
    have hu := u.isLt
    have hv := v.isLt
    rcases hxr' with ⟨hr0, heq⟩ | ⟨hr2k, heq⟩ | ⟨hr1, hr2, heq⟩
    · omega
    · omega
    · have hab : u'.val * m + v'.val = u.val * m + v.val := by
        rcases lt_trichotomy (u'.val * m + v'.val) (u.val * m + v.val) with hlt | heq' | hgt
        · have hle : 2 * k * (u'.val * m + v'.val + 1) ≤ 2 * k * (u.val * m + v.val) :=
            Nat.mul_le_mul_left (2 * k) hlt
          rw [Nat.mul_add, Nat.mul_one] at hle
          omega
        · exact heq'
        · have hle : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (u'.val * m + v'.val) :=
            Nat.mul_le_mul_left (2 * k) hgt
          rw [Nat.mul_add, Nat.mul_one] at hle
          omega
      have hrp : r = p := by
        rw [hab] at heq
        omega
      have hu_eq : u'.val = u.val := by
        rcases lt_trichotomy u'.val u.val with hlt | heq' | hgt
        · have hle : (u'.val + 1) * m ≤ u.val * m := Nat.mul_le_mul_right m hlt
          rw [Nat.add_mul, Nat.one_mul] at hle
          omega
        · exact heq'
        · have hle : (u.val + 1) * m ≤ u'.val * m := Nat.mul_le_mul_right m hgt
          rw [Nat.add_mul, Nat.one_mul] at hle
          omega
      have hv_eq : v'.val = v.val := by
        rw [hu_eq] at hab
        omega
      exact ⟨Fin.ext hu_eq, Fin.ext hv_eq, hrp⟩
  let y_prev : Fin (m + 2 * k * (m * m)) :=
    if hp : p = 1 then
      ⟨u.val, by have := u.isLt; omega⟩
    else
      ⟨x.val - 1, by have := x.isLt; omega⟩
  have hy_prev : Q u v (p - 1) y_prev := by
    apply (hQ u v (p - 1) y_prev).mpr
    dsimp [y_prev]
    split_ifs with hp
    · exact Or.inl ⟨by omega, rfl⟩
    · exact Or.inr (Or.inr ⟨by omega, by omega, by dsimp only; omega⟩)
  have hnext_lt : p < 2 * k → x.val + 1 < m + 2 * k * (m * m) := by
    intro hplt
    have h1 : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m u.isLt
    rw [Nat.add_mul, Nat.one_mul] at h1
    have h2 : u.val * m + v.val + 1 ≤ m * m := by
      have hv := v.isLt
      omega
    have h3 : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
      Nat.mul_le_mul_left (2 * k) h2
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega
  let y_next : Fin (m + 2 * k * (m * m)) :=
    if hp : p = 2 * k then
      ⟨v.val, by have := v.isLt; omega⟩
    else
      ⟨x.val + 1, hnext_lt (by omega)⟩
  have hy_next : Q u v (p + 1) y_next := by
    apply (hQ u v (p + 1) y_next).mpr
    dsimp [y_next]
    split_ifs with hp
    · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega, by dsimp only; omega⟩)
  have hne : y_prev ≠ y_next := by
    intro heq
    have hval : y_prev.val = y_next.val := congrArg Fin.val heq
    have hu := u.isLt
    have hv := v.isLt
    have h1 : y_prev.val = if p = 1 then u.val else x.val - 1 := by
      dsimp [y_prev]
      split_ifs <;> rfl
    have h2 : y_next.val = if p = 2 * k then v.val else x.val + 1 := by
      dsimp [y_next]
      split_ifs <;> rfl
    rw [h1, h2] at hval
    split_ifs at hval <;> omega
  have hset : S.neighborSet x = {y_prev, y_next} := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hadj
      obtain ⟨u', v', _, _, q, _, hcases⟩ := (hS x y).mp hadj
      rcases hcases with ⟨hqx, hqy⟩ | ⟨hqy, hqx⟩
      · obtain ⟨hu', hv', hq⟩ := hQ_unique_idx u' v' q hqx
        rw [hu', hv', hq] at hqy
        exact Or.inr (hQ_unique_val u v (p + 1) y y_next hqy hy_next)
      · obtain ⟨hu', hv', hqeq⟩ := hQ_unique_idx u' v' (q + 1) hqx
        have hq : q = p - 1 := by omega
        rw [hu', hv', hq] at hqy
        exact Or.inl (hQ_unique_val u v (p - 1) y y_prev hqy hy_prev)
    · rintro (rfl | rfl)
      · exact (hS x y_prev).mpr ⟨u, v, huv, hH, p - 1, by omega,
          Or.inr ⟨hy_prev, by rwa [Nat.sub_add_cancel hp1]⟩⟩
      · exact (hS x y_next).mpr ⟨u, v, huv, hH, p, hp2,
          Or.inl ⟨hx, hy_next⟩⟩
  rw [hset, Set.ncard_pair hne]
