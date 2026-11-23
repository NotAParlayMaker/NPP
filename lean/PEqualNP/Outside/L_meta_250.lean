import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_250 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos pos' : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ v : Fin N, pos' v ≤ 2 * k ∧ (pos v + pos' v) % (2 * k + 1) = 0) → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos' u ≠ 0 ∨ pos' v ≠ 0) ∧ ∀ v : Fin N, pos' v ≠ 0 → pos' v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos' a + 1 = pos' v ∧ pos' b = (pos' v + 1) % (2 * k + 1)) := by
  intro N k E pos pos' hk h hp'
  obtain ⟨hsym, hne, hthr⟩ := h
  have key : ∀ p p' : ℕ, p ≤ 2 * k → p' ≤ 2 * k → (p + p') % (2 * k + 1) = 0 →
      p + p' = 0 ∨ p + p' = 2 * k + 1 := by
    intro p p' h1 h2 h3
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h3
    have hc2 : c < 2 := by
      by_contra hcc
      have h4 : 2 ≤ c := by omega
      have h5 : (2 * k + 1) * 2 ≤ (2 * k + 1) * c := Nat.mul_le_mul_left _ h4
      omega
    interval_cases c <;> omega
  have modm : ∀ q : ℕ, q ≤ 2 * k + 1 →
      (q % (2 * k + 1) = q ∧ q < 2 * k + 1) ∨ (q % (2 * k + 1) = 0 ∧ q = 2 * k + 1) := by
    intro q hq
    rcases Nat.lt_or_ge q (2 * k + 1) with h | h
    · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
    · have h6 : q = 2 * k + 1 := by omega
      exact Or.inr ⟨by rw [h6, Nat.mod_self], h6⟩
  have sum : ∀ v : Fin N, pos v ≤ 2 * k → pos v + pos' v = 0 ∨ pos v + pos' v = 2 * k + 1 :=
    fun v hv => key (pos v) (pos' v) hv (hp' v).1 (hp' v).2
  have nz : ∀ v : Fin N, pos v ≠ 0 → pos' v ≠ 0 := by
    intro v hv h0
    have h1 := sum v (hthr v hv).1
    have h2 := (hthr v hv).1
    omega
  have nz' : ∀ v : Fin N, pos' v ≠ 0 → pos v ≠ 0 := by
    intro v hv h0
    have h1 := sum v (by omega)
    have h2 := (hp' v).1
    omega
  refine ⟨hsym, ?_, ?_⟩
  · intro u v huv
    rcases hne u v huv with h | h
    · exact Or.inl (nz u h)
    · exact Or.inr (nz v h)
  · intro v hv'
    have hv := nz' v hv'
    obtain ⟨hle, a, b, hnb, ha, hb⟩ := hthr v hv
    have sv := sum v hle
    have pa := (hp' a).1
    have pb := (hp' b).1
    have pv := (hp' v).1
    have sa := sum a (by omega)
    refine ⟨pv, b, a, fun w => by rw [hnb w]; exact or_comm, ?_, ?_⟩
    · rcases modm (pos v + 1) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hb
        have sb := sum b (by omega)
        omega
      · rw [h1] at hb
        have sb := sum b (by omega)
        omega
    · rcases modm (pos' v + 1) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]
        omega
      · rw [h1]
        omega
