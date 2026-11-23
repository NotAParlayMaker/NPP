import Mathlib
import PEqualNP.Defs

lemma PEqualNP.Outside.L_meta_451_div (c A B a b : ℕ) (ha : a < c) (hb : b < c)
    (h : c * A + a = c * B + b) : A = B ∧ a = b := by
  rcases lt_trichotomy A B with hAB | hAB | hAB
  · have : c * (A + 1) ≤ c * B := Nat.mul_le_mul_left c hAB
    nlinarith
  · subst hAB
    omega
  · have : c * (B + 1) ≤ c * A := Nat.mul_le_mul_left c hAB
    nlinarith

theorem PEqualNP.Outside.L_meta_451 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x → (S.neighborSet x).ncard = 2 := by
  intro m k H Q S hk hQ hS u v p x huv hHuv hp1 hp2 hx
  have hum : u.val < m := u.isLt
  have hvm : v.val < m := v.isLt
  have hxv : x.val + 1 = m + 2 * k * (u.val * m + v.val) + p := by
    rcases (hQ u v p x).1 hx with h | h | h
    · omega
    · omega
    · exact h.2.2
  have hbd : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) := by
    apply Nat.mul_le_mul_left
    nlinarith
  have hxN : x.val < m + 2 * k * (m * m) := x.isLt
  have hmx : m ≤ x.val := by
    have : 0 ≤ 2 * k * (u.val * m + v.val) := Nat.zero_le _
    omega
  have dec : ∀ (u' v' : Fin m) (q : ℕ), q ≤ 2 * k + 1 → Q u' v' q x →
      u' = u ∧ v' = v ∧ q = p := by
    intro u' v' q hq h
    have hu'm : u'.val < m := u'.isLt
    have hv'm : v'.val < m := v'.isLt
    rcases (hQ u' v' q x).1 h with h | h | h
    · omega
    · omega
    · obtain ⟨hq1, hq2, h⟩ := h
      have h1 := PEqualNP.Outside.L_meta_451_div (2 * k) (u'.val * m + v'.val)
        (u.val * m + v.val) (q - 1) (p - 1) (by omega) (by omega) (by omega)
      have h2 := PEqualNP.Outside.L_meta_451_div m u'.val u.val v'.val v.val hv'm hvm
        (by linarith [h1.1, mul_comm u'.val m, mul_comm u.val m])
      exact ⟨Fin.ext h2.1, Fin.ext h2.2, by omega⟩
  have haN : (if p = 1 then u.val else x.val - 1) < m + 2 * k * (m * m) := by
    split_ifs <;> omega
  have hbN : (if p = 2 * k then v.val else x.val + 1) < m + 2 * k * (m * m) := by
    split_ifs with h
    · omega
    · have : p < 2 * k := by omega
      have e1 : 2 * k * (u.val * m + v.val + 1) = 2 * k * (u.val * m + v.val) + 2 * k := by ring
      omega
  set a : Fin (m + 2 * k * (m * m)) := ⟨if p = 1 then u.val else x.val - 1, haN⟩ with ha
  set b : Fin (m + 2 * k * (m * m)) := ⟨if p = 2 * k then v.val else x.val + 1, hbN⟩ with hb
  have hQa : Q u v (p - 1) a := by
    rw [hQ]
    by_cases h : p = 1
    · left
      exact ⟨by omega, by simp [ha, h]⟩
    · right
      right
      refine ⟨by omega, by omega, ?_⟩
      simp only [ha, h, if_false]
      omega
  have hQb : Q u v (p + 1) b := by
    rw [hQ]
    by_cases h : p = 2 * k
    · right
      left
      exact ⟨by omega, by simp [hb, h]⟩
    · right
      right
      refine ⟨by omega, by omega, ?_⟩
      simp only [hb, h, if_false]
      omega
  have hset : S.neighborSet x = {a, b} := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, hS, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u', v', -, -, q, hq, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · obtain ⟨rfl, rfl, rfl⟩ := dec u' v' q (by omega) h1
        right
        apply Fin.ext
        rcases (hQ u' v' (q + 1) y).1 h2 with h | h | h
        · omega
        · simp only [hb]
          rw [if_pos (by omega)]
          exact h.2
        · simp only [hb]
          rw [if_neg (by omega)]
          omega
      · obtain ⟨rfl, rfl, hqp⟩ := dec u' v' (q + 1) (by omega) h2
        left
        apply Fin.ext
        rcases (hQ u' v' q y).1 h1 with h | h | h
        · simp only [ha]
          rw [if_pos (by omega)]
          exact h.2
        · omega
        · simp only [ha]
          rw [if_neg (by omega)]
          omega
    · rintro (rfl | rfl)
      · refine ⟨u, v, huv, hHuv, p - 1, by omega, Or.inr ⟨hQa, ?_⟩⟩
        rw [show p - 1 + 1 = p by omega]
        exact hx
      · exact ⟨u, v, huv, hHuv, p, hp2, Or.inl ⟨hx, hQb⟩⟩
  rw [hset]
  apply Set.ncard_pair
  intro h
  have h' := congrArg Fin.val h
  simp only [ha, hb] at h'
  have huv' : u.val < v.val := huv
  split_ifs at h' <;> omega
