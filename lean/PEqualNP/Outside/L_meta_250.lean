import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L250

theorem mod_zero_small (a n : ℕ) (hn : 0 < n) (ha : a < 2 * n) (h : a % n = 0) : a = 0 ∨ a = n := by
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
  rcases c with _ | _ | c
  · left; simpa using hc
  · right; simpa using hc
  · exfalso
    rw [hc] at ha
    nlinarith

end PEqualNP.Outside.L250

theorem PEqualNP.Outside.L_meta_250 :
    ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos pos' : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ v : Fin N, pos' v ≤ 2 * k ∧ (pos v + pos' v) % (2 * k + 1) = 0) → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos' u ≠ 0 ∨ pos' v ≠ 0) ∧ ∀ v : Fin N, pos' v ≠ 0 → pos' v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos' a + 1 = pos' v ∧ pos' b = (pos' v + 1) % (2 * k + 1)) := by
  intro N k E pos pos' hk hTL hpos'
  obtain ⟨hsym, hedge, hthread⟩ := hTL
  have key : ∀ v, (pos v = 0 ∧ pos' v = 0) ∨ (1 ≤ pos v ∧ pos v ≤ 2 * k ∧ pos' v = 2 * k + 1 - pos v) := by
    intro v
    obtain ⟨hle, hmod⟩ := hpos' v
    by_cases h0 : pos v = 0
    · left
      refine ⟨h0, ?_⟩
      rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hmod
      exact hmod
    · right
      have hb := (hthread v h0).1
      refine ⟨by omega, hb, ?_⟩
      rcases PEqualNP.Outside.L250.mod_zero_small _ _ (by omega) (by omega) hmod with h | h
      · omega
      · omega
  refine ⟨hsym, ?_, ?_⟩
  · intro u v huv
    rcases hedge u v huv with h | h
    · left
      rcases key u with ⟨h1, _⟩ | ⟨h1, h2, h3⟩ <;> omega
    · right
      rcases key v with ⟨h1, _⟩ | ⟨h1, h2, h3⟩ <;> omega
  · intro v hv'
    rcases key v with ⟨_, h2⟩ | ⟨h1, h2, h3⟩
    · exact absurd h2 hv'
    · obtain ⟨_, a, b, hnb, ha, hb⟩ := hthread v (by omega)
      refine ⟨(hpos' v).1, b, a, fun w => by rw [hnb]; exact or_comm, ?_, ?_⟩
      · rcases Nat.lt_or_ge (pos v + 1) (2 * k + 1) with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at hb
          rcases key b with ⟨hb1, _⟩ | ⟨hb1, hb2, hb3⟩ <;> omega
        · have hv2k : pos v + 1 = 2 * k + 1 := by omega
          rw [hv2k, Nat.mod_self] at hb
          rcases key b with ⟨hb1, hb2⟩ | ⟨hb1, hb2, hb3⟩ <;> omega
      · rcases key a with ⟨ha1, ha2⟩ | ⟨ha1, ha2, ha3⟩
        · have hv1 : pos v = 1 := by omega
          rw [ha2, h3, hv1, show 2 * k + 1 - 1 + 1 = 2 * k + 1 by omega, Nat.mod_self]
        · rw [ha3, h3, Nat.mod_eq_of_lt (by omega)]
          omega
