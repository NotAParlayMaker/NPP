import Mathlib.Data.Fin.Basic

theorem PEqualNP.Outside.L_meta_250 :
    ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos pos' : Fin N → ℕ),
      1 ≤ k →
      ((∀ u v : Fin N, E u v → E v u) ∧
        (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧
        ∀ v : Fin N, pos v ≠ 0 →
          pos v ≤ 2 * k ∧
          ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧
            pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) →
      (∀ v : Fin N, pos' v ≤ 2 * k ∧ (pos v + pos' v) % (2 * k + 1) = 0) →
      ((∀ u v : Fin N, E u v → E v u) ∧
        (∀ u v : Fin N, E u v → pos' u ≠ 0 ∨ pos' v ≠ 0) ∧
        ∀ v : Fin N, pos' v ≠ 0 →
          pos' v ≤ 2 * k ∧
          ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧
            pos' a + 1 = pos' v ∧ pos' b = (pos' v + 1) % (2 * k + 1)) := by
  intro N k E pos pos' hk ⟨hsym, hedge, hpos⟩ hrefl
  have hle : ∀ v : Fin N, pos v ≤ 2 * k := fun v => by
    by_cases hv : pos v = 0
    · omega
    · exact (hpos v hv).1
  have hcases : ∀ v : Fin N,
      (pos v = 0 ∧ pos' v = 0) ∨ (pos v ≠ 0 ∧ pos' v ≠ 0 ∧ pos v + pos' v = 2 * k + 1) := by
    intro v
    have h1 := hle v
    have ⟨h2, hmod⟩ := hrefl v
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
    rcases q with _ | _ | q
    · left; omega
    · right; omega
    · have hge : (2 * k + 1) * 2 ≤ (2 * k + 1) * (q + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
  have hzero_iff : ∀ v : Fin N, pos v = 0 ↔ pos' v = 0 := fun v => by
    rcases hcases v with ⟨h1, h2⟩ | ⟨h1, h2, _⟩ <;> simp [h1, h2]
  have hsum_nz : ∀ v : Fin N, pos v ≠ 0 → pos v + pos' v = 2 * k + 1 := fun v hv => by
    rcases hcases v with ⟨h1, _⟩ | ⟨_, _, hsum⟩
    · exact absurd h1 hv
    · exact hsum
  refine ⟨hsym, ?_, ?_⟩
  · intro u v huv
    rcases hedge u v huv with hu | hv
    · exact Or.inl fun h => hu ((hzero_iff u).mpr h)
    · exact Or.inr fun h => hv ((hzero_iff v).mpr h)
  · intro v hv'
    have hv : pos v ≠ 0 := fun h => hv' ((hzero_iff v).mp h)
    refine ⟨(hrefl v).1, ?_⟩
    obtain ⟨hle_v, a, b, hnb, ha, hb⟩ := hpos v hv
    have hsum_v := hsum_nz v hv
    refine ⟨b, a, ?_, ?_, ?_⟩
    · intro w
      rw [hnb w, or_comm]
    · by_cases htop : pos v = 2 * k
      · rw [htop, Nat.mod_self] at hb
        have hpb' : pos' b = 0 := (hzero_iff b).mp hb
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hb
        have hsum_b := hsum_nz b (by omega)
        omega
    · by_cases hbot : pos v = 1
      · have hpa' : pos' a = 0 := (hzero_iff a).mp (by omega)
        have hpv' : pos' v = 2 * k := by omega
        rw [hpa', hpv', Nat.mod_self]
      · have hsum_a := hsum_nz a (by omega)
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
