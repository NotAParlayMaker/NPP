import PEqualNP.Defs

namespace PEqualNP.Outside

theorem L_meta_250 :
    ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos pos' : Fin N → ℕ),
      1 ≤ k →
      ((∀ u v : Fin N, E u v → E v u) ∧
        (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧
        ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧
          ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧
            pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) →
      (∀ v : Fin N, pos' v ≤ 2 * k ∧ (pos v + pos' v) % (2 * k + 1) = 0) →
      ((∀ u v : Fin N, E u v → E v u) ∧
        (∀ u v : Fin N, E u v → pos' u ≠ 0 ∨ pos' v ≠ 0) ∧
        ∀ v : Fin N, pos' v ≠ 0 → pos' v ≤ 2 * k ∧
          ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧
            pos' a + 1 = pos' v ∧ pos' b = (pos' v + 1) % (2 * k + 1)) := by
  intro N k E pos pos' hk ⟨hsym, hnz, hpos⟩ hpos'
  have hzero_iff : ∀ v : Fin N, pos' v = 0 ↔ pos v = 0 := by
    intro v
    have ⟨hle', hmod⟩ := hpos' v
    constructor
    · intro h0'
      by_contra h0
      have hle : pos v ≤ 2 * k := (hpos v h0).1
      rw [h0', Nat.add_zero] at hmod
      have : pos v % (2 * k + 1) = pos v := Nat.mod_eq_of_lt (by omega)
      omega
    · intro h0
      rw [h0, Nat.zero_add] at hmod
      have : pos' v % (2 * k + 1) = pos' v := Nat.mod_eq_of_lt (by omega)
      omega
  have hsum_eq : ∀ v : Fin N, pos v ≠ 0 → pos v + pos' v = 2 * k + 1 := by
    intro v hv
    have hle : pos v ≤ 2 * k := (hpos v hv).1
    have ⟨hle', hmod⟩ := hpos' v
    have hv' : pos' v ≠ 0 := mt (hzero_iff v).mp hv
    have hlt : pos v + pos' v < 2 * (2 * k + 1) := by omega
    have hgt : 0 < pos v + pos' v := by omega
    have hdvd : (2 * k + 1) ∣ (pos v + pos' v) := Nat.dvd_of_mod_eq_zero hmod
    rcases hdvd with ⟨q, hq⟩
    have hq1 : q = 1 := by
      rcases q with _ | _ | q'
      · simp at hq; omega
      · rfl
      · rw [Nat.mul_succ, Nat.mul_succ] at hq
        omega
    rw [hq1, Nat.mul_one] at hq
    omega
  refine ⟨hsym, ?_, ?_⟩
  · intro u v huv
    rcases hnz u v huv with hu | hv
    · exact Or.inl (mt (hzero_iff u).mp hu)
    · exact Or.inr (mt (hzero_iff v).mp hv)
  · intro v hv'
    have hv : pos v ≠ 0 := mt (hzero_iff v).mpr hv'
    have hle' : pos' v ≤ 2 * k := (hpos' v).1
    have ⟨hle, a, b, hnb, ha, hb⟩ := hpos v hv
    have hvv' : pos v + pos' v = 2 * k + 1 := hsum_eq v hv
    refine ⟨hle', b, a, ?_, ?_, ?_⟩
    · intro w
      rw [hnb w, or_comm]
    · by_cases htop : pos v = 2 * k
      · have hposb : pos b = 0 := by
          rw [hb, htop]
          exact Nat.mod_self (2 * k + 1)
        have hpos'b : pos' b = 0 := (hzero_iff b).mpr hposb
        omega
      · have hlt : pos v + 1 < 2 * k + 1 := by omega
        have hposb : pos b = pos v + 1 := by
          rw [hb, Nat.mod_eq_of_lt hlt]
        have hb_nz : pos b ≠ 0 := by omega
        have hbb' : pos b + pos' b = 2 * k + 1 := hsum_eq b hb_nz
        omega
    · by_cases hbot : pos v = 1
      · have hposa : pos a = 0 := by omega
        have hpos'a : pos' a = 0 := (hzero_iff a).mpr hposa
        have hpos'v : pos' v = 2 * k := by omega
        rw [hpos'a, hpos'v, Nat.mod_self]
      · have ha_nz : pos a ≠ 0 := by omega
        have haa' : pos a + pos' a = 2 * k + 1 := hsum_eq a ha_nz
        have hlt : pos' v + 1 < 2 * k + 1 := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega

end PEqualNP.Outside
