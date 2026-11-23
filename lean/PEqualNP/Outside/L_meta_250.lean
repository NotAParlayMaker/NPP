import Mathlib
import PEqualNP.Defs

lemma PEqualNP.Outside.L_meta_250_sum_cases {m x y : ℕ} (hx : x < m) (hy : y < m)
    (h : (x + y) % m = 0) : x + y = 0 ∨ x + y = m := by
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
  rcases c with _ | _ | c
  · left; simpa using hc
  · right; simpa using hc
  · exfalso; nlinarith

lemma PEqualNP.Outside.L_meta_250_succ_cases {m p : ℕ} (hp : p < m) :
    ((p + 1) % m = p + 1 ∧ p + 1 < m) ∨ ((p + 1) % m = 0 ∧ p + 1 = m) := by
  rcases Nat.lt_or_ge (p + 1) m with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have e : p + 1 = m := by omega
    exact Or.inr ⟨by rw [e, Nat.mod_self], e⟩

theorem PEqualNP.Outside.L_meta_250 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos pos' : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ v : Fin N, pos' v ≤ 2 * k ∧ (pos v + pos' v) % (2 * k + 1) = 0) → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos' u ≠ 0 ∨ pos' v ≠ 0) ∧ ∀ v : Fin N, pos' v ≠ 0 → pos' v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos' a + 1 = pos' v ∧ pos' b = (pos' v + 1) % (2 * k + 1)) := by
  intro N k E pos pos' hk hlab hp'
  obtain ⟨hsym, hedge, hv⟩ := hlab
  have key : ∀ w : Fin N, pos w < 2 * k + 1 →
      pos w + pos' w = 0 ∨ pos w + pos' w = 2 * k + 1 := by
    intro w hw
    have h1 := (hp' w).1
    exact PEqualNP.Outside.L_meta_250_sum_cases hw (by omega) (hp' w).2
  have zero_iff : ∀ w : Fin N, pos' w ≠ 0 ↔ pos w ≠ 0 := by
    intro w
    have h1 := (hp' w).1
    by_cases h0 : pos w = 0
    · rcases key w (by omega) with h | h
      · constructor <;> intro <;> omega
      · constructor <;> intro <;> omega
    · have h2 := (hv w h0).1
      rcases key w (by omega) with h | h
      · constructor <;> intro <;> omega
      · constructor <;> intro <;> omega
  refine ⟨hsym, ?_, ?_⟩
  · intro u v huv
    rcases hedge u v huv with h | h
    · exact Or.inl ((zero_iff u).2 h)
    · exact Or.inr ((zero_iff v).2 h)
  · intro v hv'
    have hpv : pos v ≠ 0 := (zero_iff v).1 hv'
    obtain ⟨hle, a, b, hnb, ha, hb⟩ := hv v hpv
    have hv'le := (hp' v).1
    have kv := key v (by omega)
    refine ⟨hv'le, b, a, ?_, ?_, ?_⟩
    · intro w
      rw [hnb w]
      exact Or.comm
    · have hbm : pos b < 2 * k + 1 := by
        rw [hb]
        exact Nat.mod_lt _ (by omega)
      have kb := key b hbm
      have hb'le := (hp' b).1
      rcases PEqualNP.Outside.L_meta_250_succ_cases (m := 2 * k + 1) (p := pos v) (by omega)
        with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hb
        omega
      · rw [h1] at hb
        omega
    · have ka := key a (by omega)
      have ha'le := (hp' a).1
      rcases PEqualNP.Outside.L_meta_250_succ_cases (m := 2 * k + 1) (p := pos' v) (by omega)
        with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]
        omega
      · rw [h1]
        omega
