import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_1844 : (∀ (qlv18 Nlv18 klv18 mlv18 alv18 clv18 : ℕ) (Ilv18 : Fin Nlv18 → Fin Nlv18 → Prop) [DecidableRel Ilv18] (Clv18 : PEqualNP.CircuitLowerBounds.Circuit) (Rlv18 : ℕ → ℕ), 2 ≤ qlv18 → Nlv18 = qlv18 ^ 2 + qlv18 + 1 → (∀ llv18 : Fin Nlv18, (Finset.univ.filter (fun plv18 => Ilv18 plv18 llv18)).card = qlv18 + 1) → (∀ palv18 pblv18 : Fin Nlv18, palv18 ≠ pblv18 → ∃! lblv18 : Fin Nlv18, Ilv18 palv18 lblv18 ∧ Ilv18 pblv18 lblv18) → 1 ≤ klv18 → klv18 ≤ qlv18 → ((∀ glv18 ∈ Clv18.gates, (glv18.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv18.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv18.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv18 + Nlv18) Clv18) → Set.ncard {jlv18 : ℕ | jlv18 < Clv18.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv18x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.Ico Nlv18 (Nlv18 + Nlv18))).getD ilv18x3 0 = 0) ∨ (∀ hlv18 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18 jlv18).inputs, (Clv18.lineDegrees (Nlv18 + Nlv18) (Finset.range Nlv18)).getD hlv18 0 = 0))} ≤ mlv18 → (∀ plv18x1 llv18x1 : Fin Nlv18, Ilv18 plv18x1 llv18x1 → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 (fun klv18x1 => decide (klv18x1 = Fin.castAdd Nlv18 plv18x1 ∨ klv18x1 = Fin.natAdd Nlv18 llv18x1)) = true) → (∀ zlv18 : Fin (Nlv18 + Nlv18) → Bool, (Finset.univ.filter (fun llv18x2 : Fin Nlv18 => zlv18 (Fin.natAdd Nlv18 llv18x2) = true)).card ≤ klv18 → (¬ ∃ plv18x2 llv18x3 : Fin Nlv18, Ilv18 plv18x2 llv18x3 ∧ zlv18 (Fin.castAdd Nlv18 plv18x2) = true ∧ zlv18 (Fin.natAdd Nlv18 llv18x3) = true) → PEqualNP.MetaComplexity.circuitFun (Nlv18 + Nlv18) Clv18 zlv18 = false) → (∀ dlv18 < mlv18, 1 ≤ Rlv18 dlv18 ∧ Rlv18 dlv18 ≤ qlv18) → (∀ dlv18x1 elv18x1 : ℕ, dlv18x1 + elv18x1 = mlv18 → 2 ^ elv18x1 + dlv18x1 ≤ klv18 ∧ ∑ ilv18 ∈ Finset.range dlv18x1, (1 + Rlv18 ilv18 * (qlv18 + 1)) < Nlv18) → (∀ dlv18x2 elv18x2 : ℕ, dlv18x2 + elv18x2 + 1 = mlv18 → (alv18 : ℤ) * max ((Rlv18 dlv18x2 : ℤ) * max (2 * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1))) ≤ (clv18 : ℤ) * ((Rlv18 dlv18x2 : ℤ) * ((klv18 : ℤ) + 1 - (dlv18x2 : ℤ) - 2 ^ (elv18x2 + 1)) * ((Nlv18 : ℤ) - ∑ ilv18x1 ∈ Finset.range dlv18x2, (1 + (Rlv18 ilv18x1 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (dlv18x2 : ℤ)))) → (alv18 : ℤ) * max ((qlv18 : ℤ) * max (2 * ((klv18 : ℤ) - (mlv18 : ℤ))) ((qlv18 : ℤ) + 1)) (3 * (qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ))) ≤ (clv18 : ℤ) * ((qlv18 : ℤ) * ((klv18 : ℤ) - (mlv18 : ℤ)) * ((Nlv18 : ℤ) - ∑ ilv18x2 ∈ Finset.range mlv18, (1 + (Rlv18 ilv18x2 : ℤ) * ((qlv18 : ℤ) + 1))) * ((qlv18 : ℤ) - (mlv18 : ℤ))) → alv18 ≤ clv18 * Clv18.size) → (∀ (N112 km112 : ℕ) (C112 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C112 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) C112 → Set.ncard {j112 : ℕ | j112 < C112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112 0 = 0) ∨ (∀ h112 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C112 j112).inputs, (C112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112 0 = 0))} ≤ km112 → (∃ z112 z112a : Fin (N112 + N112) → Bool, PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112 ≠ PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112 z112a) → ∃ D112 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g112 ∈ D112.gates, (g112.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g112.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g112.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N112 + N112) D112) ∧ Set.ncard {j112a : ℕ | j112a < D112.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ i112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.Ico N112 (N112 + N112))).getD i112a 0 = 0) ∨ (∀ h112a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D112 j112a).inputs, (D112.lineDegrees (N112 + N112) (Finset.range N112)).getD h112a 0 = 0))} ≤ km112 ∧ D112.size ≤ C112.size ∧ PEqualNP.MetaComplexity.circuitFun (N112 + N112) D112 = PEqualNP.MetaComplexity.circuitFun (N112 + N112) C112) → ∀ (qlv18g Nlv18g : ℕ) (Ilv18g : Fin Nlv18g → Fin Nlv18g → Prop) [DecidableRel Ilv18g] (Clv18g : PEqualNP.CircuitLowerBounds.Circuit) (mlv18g : ℕ), 2 ≤ qlv18g → Nlv18g = qlv18g ^ 2 + qlv18g + 1 → (∀ llv18g : Fin Nlv18g, (Finset.univ.filter (fun plv18g => Ilv18g plv18g llv18g)).card = qlv18g + 1) → (∀ palv18g pblv18g : Fin Nlv18g, palv18g ≠ pblv18g → ∃! lblv18g : Fin Nlv18g, Ilv18g palv18g lblv18g ∧ Ilv18g pblv18g lblv18g) → PEqualNP.MetaComplexity.Monotone2 Clv18g → PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv18g + Nlv18g) Clv18g → Set.ncard {jlv18g : ℕ | jlv18g < Clv18g.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18g jlv18g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv18g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18g jlv18g).inputs, (Clv18g.lineDegrees (Nlv18g + Nlv18g) (Finset.Ico Nlv18g (Nlv18g + Nlv18g))).getD ilv18g 0 = 0) ∨ (∀ hlv18g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv18g jlv18g).inputs, (Clv18g.lineDegrees (Nlv18g + Nlv18g) (Finset.range Nlv18g)).getD hlv18g 0 = 0))} ≤ mlv18g → 1 ≤ mlv18g → 4 * mlv18g ≤ qlv18g → 2 ^ (mlv18g + 1) ≤ qlv18g + 1 → (∀ plv18gx1 llv18gx1 : Fin Nlv18g, Ilv18g plv18gx1 llv18gx1 → PEqualNP.MetaComplexity.circuitFun (Nlv18g + Nlv18g) Clv18g (fun klv18g => decide (klv18g = Fin.castAdd Nlv18g plv18gx1 ∨ klv18g = Fin.natAdd Nlv18g llv18gx1)) = true) → (∀ zlv18g : Fin (Nlv18g + Nlv18g) → Bool, (Finset.univ.filter (fun llv18gx2 : Fin Nlv18g => zlv18g (Fin.natAdd Nlv18g llv18gx2) = true)).card ≤ qlv18g → (¬ ∃ plv18gx2 llv18gx3 : Fin Nlv18g, Ilv18g plv18gx2 llv18gx3 ∧ zlv18g (Fin.castAdd Nlv18g plv18gx2) = true ∧ zlv18g (Fin.natAdd Nlv18g llv18gx3) = true) → PEqualNP.MetaComplexity.circuitFun (Nlv18g + Nlv18g) Clv18g zlv18g = false) → ((3 : ℤ) * (Nlv18g : ℤ) - 4 * (mlv18g : ℤ)) * ((qlv18g : ℤ) - (mlv18g : ℤ)) * ((qlv18g : ℤ) - 4 * (mlv18g : ℤ)) ≤ 48 * (mlv18g : ℤ) * (qlv18g : ℤ) * (Clv18g.size : ℤ) := by
  intro LV Norm q N I _ C m hq hN hline huniq hMon hRB hcross hm1 h4m hpow hinc hsound
  -- an incident pair, to see that the circuit is not constant
  have hNpos : 0 < N := by rw [hN]; positivity
  obtain ⟨p0, hp0⟩ : ∃ p, I p ⟨0, hNpos⟩ := by
    have hc := hline ⟨0, hNpos⟩
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hc]; omega)
    exact ⟨p, (Finset.mem_filter.mp hp).2⟩
  have hnc : ∃ z za : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z ≠
      PEqualNP.MetaComplexity.circuitFun (N + N) C za := by
    refine ⟨fun k => decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N ⟨0, hNpos⟩),
      fun _ => false, ?_⟩
    rw [hinc p0 ⟨0, hNpos⟩ hp0, hsound (fun _ => false) (by simp) (by simp)]
    simp
  obtain ⟨D, ⟨hD1, hD2⟩, hDc, hDs, hDf⟩ := Norm N m C hMon hRB hcross hnc
  -- the reference-set size used at every step
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = q / (4 * m) := ⟨_, rfl⟩
  have hR1 : 4 * m * R ≤ q := by rw [hRdef]; exact Nat.mul_div_le q (4 * m)
  have hR2 : q < 4 * m * R + 4 * m := by
    have h1 := Nat.div_add_mod q (4 * m)
    have h2 := Nat.mod_lt q (show 4 * m > 0 by omega)
    rw [← hRdef] at h1
    omega
  have hRpos : 1 ≤ R := by rw [hRdef]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hRq : R ≤ q := by rw [hRdef]; exact Nat.div_le_self _ _
  have h4R : 4 * R ≤ q := le_trans (Nat.mul_le_mul_right R (by omega)) hR1
  have h2m : 2 * 2 ^ m ≤ q + 1 := by rw [pow_succ] at hpow; omega
  -- integer facts
  have zq : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have zm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm1
  have z4m : 4 * (m : ℤ) ≤ q := by exact_mod_cast h4m
  have zR1 : 4 * (m : ℤ) * R ≤ q := by exact_mod_cast hR1
  have zR2 : (q : ℤ) < 4 * m * R + 4 * m := by exact_mod_cast hR2
  have zRpos : (1 : ℤ) ≤ R := by exact_mod_cast hRpos
  have zRq : (R : ℤ) ≤ q := by exact_mod_cast hRq
  have z4R : 4 * (R : ℤ) ≤ q := by exact_mod_cast h4R
  have zN : (N : ℤ) = q ^ 2 + q + 1 := by rw [hN]; push_cast; ring
  -- the core estimate, for every prefix length d at most m
  have core : ∀ d : ℕ, d ≤ m → 3 * (3 * (N : ℤ) - 4 * m) * ((q : ℤ) - 4 * m) ≤
      48 * (m : ℤ) * R * ((N : ℤ) - (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1))) := by
    intro d hd
    have zd : (d : ℤ) ≤ m := by exact_mod_cast hd
    have zd0 : (0 : ℤ) ≤ d := by positivity
    have hS : 4 * ((N : ℤ) - (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1))) ≥ 3 * N - 4 * m + 1 := by
      have e1 : (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1)) ≤ (m : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1)) :=
        mul_le_mul_of_nonneg_right zd (by positivity)
      have e2 : 4 * (m : ℤ) * R * ((q : ℤ) + 1) ≤ (q : ℤ) * ((q : ℤ) + 1) :=
        mul_le_mul_of_nonneg_right zR1 (by positivity)
      nlinarith
    have hA : (q : ℤ) - 4 * m ≤ 4 * m * R := by linarith
    have hB : 0 ≤ 3 * (N : ℤ) - 4 * m := by nlinarith
    have hC : (0 : ℤ) ≤ 4 * m * R := by positivity
    have key := mul_le_mul hA (show 3 * (N : ℤ) - 4 * m ≤
      4 * ((N : ℤ) - (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1))) by linarith) hB hC
    nlinarith
  have hSpos : ∀ d : ℕ, d ≤ m →
      0 ≤ (N : ℤ) - (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1)) := by
    intro d hd
    have zd : (d : ℤ) ≤ m := by exact_mod_cast hd
    have e1 : (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1)) ≤ (m : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1)) :=
      mul_le_mul_of_nonneg_right zd (by positivity)
    have e2 : 4 * (m : ℤ) * R * ((q : ℤ) + 1) ≤ (q : ℤ) * ((q : ℤ) + 1) :=
      mul_le_mul_of_nonneg_right zR1 (by positivity)
    nlinarith
  -- the constants
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = (3 * (N : ℤ) - 4 * (m : ℤ)) * ((q : ℤ) - (m : ℤ)) * ((q : ℤ) - 4 * (m : ℤ)) :=
    ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    have a1 : 0 ≤ 3 * (N : ℤ) - 4 * (m : ℤ) := by nlinarith
    have a2 : 0 ≤ (q : ℤ) - (m : ℤ) := by linarith
    have a3 : 0 ≤ (q : ℤ) - 4 * (m : ℤ) := by linarith
    rw [hX]
    exact mul_nonneg (mul_nonneg a1 a2) a3
  have ha : ((X.toNat : ℕ) : ℤ) = X := Int.toNat_of_nonneg hX0
  have hc : (((48 * m * q : ℕ)) : ℤ) = 48 * (m : ℤ) * q := by push_cast; ring
  have hRb : ∀ d < m, 1 ≤ (fun _ : ℕ => R) d ∧ (fun _ : ℕ => R) d ≤ q :=
    fun _ _ => ⟨hRpos, hRq⟩
  have hde : ∀ d e : ℕ, d + e = m → 2 ^ e + d ≤ q ∧
      ∑ i ∈ Finset.range d, (1 + (fun _ : ℕ => R) i * (q + 1)) < N := by
    intro d e hde
    have hpe : 2 ^ e ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have e1 : d * (1 + R * (q + 1)) ≤ m * (1 + R * (q + 1)) := Nat.mul_le_mul_right _ (by omega)
    have e2 : 4 * m * R * (q + 1) ≤ q * (q + 1) := Nat.mul_le_mul_right _ hR1
    have e5 : q * (q + 1) + 4 * m < 4 * (q ^ 2 + q + 1) := by nlinarith
    rw [hN]
    linarith
  have hstep : ∀ d e : ℕ, d + e + 1 = m →
      ((X.toNat : ℕ) : ℤ) * max (((fun _ : ℕ => R) d : ℤ) * max (2 * ((q : ℤ) + 1 - (d : ℤ) -
        2 ^ (e + 1))) ((q : ℤ) + 1)) (3 * (q : ℤ) * ((q : ℤ) + 1 - (d : ℤ) - 2 ^ (e + 1))) ≤
      (((48 * m * q : ℕ)) : ℤ) * (((fun _ : ℕ => R) d : ℤ) * ((q : ℤ) + 1 - (d : ℤ) - 2 ^ (e + 1)) *
        ((N : ℤ) - ∑ i ∈ Finset.range d, (1 + ((fun _ : ℕ => R) i : ℤ) * ((q : ℤ) + 1))) *
        ((q : ℤ) - (d : ℤ))) := by
    intro d e hde
    simp only []
    rw [ha, hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hdm : d ≤ m := by omega
    have zd : (d : ℤ) + 1 ≤ m := by exact_mod_cast (show d + 1 ≤ m by omega)
    have hpe : 2 ^ (e + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have zpe : (2 : ℤ) * 2 ^ (e + 1) ≤ q + 1 := by
      have : 2 * 2 ^ (e + 1) ≤ q + 1 := by omega
      exact_mod_cast this
    set t : ℤ := (q : ℤ) + 1 - (d : ℤ) - 2 ^ (e + 1) with ht
    have ht4 : (q : ℤ) + 6 ≤ 4 * t := by rw [ht]; linarith
    have ht0 : 0 ≤ t := by linarith
    have hle : (R : ℤ) * max (2 * t) ((q : ℤ) + 1) ≤ 3 * q * t := by
      rcases le_total (2 * t) ((q : ℤ) + 1) with h | h
      · rw [max_eq_right h]
        nlinarith [mul_le_mul_of_nonneg_right z4R (show (0 : ℤ) ≤ (q : ℤ) + 1 by linarith),
          mul_le_mul_of_nonneg_left ht4 (show (0 : ℤ) ≤ q by linarith)]
      · rw [max_eq_left h]
        nlinarith [mul_le_mul_of_nonneg_right (show 2 * (R : ℤ) ≤ 3 * q by linarith) ht0]
    rw [max_eq_right hle]
    have A := core d hdm
    have S0 := hSpos d hdm
    calc X * (3 * q * t) = (3 * (3 * (N : ℤ) - 4 * m) * ((q : ℤ) - 4 * m)) *
          ((q : ℤ) * t * ((q : ℤ) - m)) := by rw [hX]; ring
      _ ≤ (48 * (m : ℤ) * R * ((N : ℤ) - (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1)))) *
          ((q : ℤ) * t * ((q : ℤ) - m)) :=
          mul_le_mul_of_nonneg_right A (mul_nonneg (mul_nonneg (by linarith) ht0) (by linarith))
      _ ≤ (48 * (m : ℤ) * R * ((N : ℤ) - (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1)))) *
          ((q : ℤ) * t * ((q : ℤ) - d)) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left (by linarith)
            exact mul_nonneg (by linarith) ht0
          · positivity
      _ = 48 * (m : ℤ) * q * ((R : ℤ) * t * ((N : ℤ) - (d : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1))) *
          ((q : ℤ) - d)) := by ring
  have hfin : ((X.toNat : ℕ) : ℤ) * max ((q : ℤ) * max (2 * ((q : ℤ) - (m : ℤ))) ((q : ℤ) + 1))
      (3 * (q : ℤ) * ((q : ℤ) - (m : ℤ))) ≤ (((48 * m * q : ℕ)) : ℤ) * ((q : ℤ) * ((q : ℤ) - (m : ℤ)) *
      ((N : ℤ) - ∑ i ∈ Finset.range m, (1 + ((fun _ : ℕ => R) i : ℤ) * ((q : ℤ) + 1))) *
      ((q : ℤ) - (m : ℤ))) := by
    simp only []
    rw [ha, hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hle : (q : ℤ) * max (2 * ((q : ℤ) - (m : ℤ))) ((q : ℤ) + 1) ≤ 3 * q * ((q : ℤ) - m) := by
      rcases le_total (2 * ((q : ℤ) - (m : ℤ))) ((q : ℤ) + 1) with h | h
      · rw [max_eq_right h]
        nlinarith
      · rw [max_eq_left h]
        nlinarith
    rw [max_eq_right hle]
    have A := core m le_rfl
    have S0 := hSpos m le_rfl
    have A2 : 3 * (3 * (N : ℤ) - 4 * m) * ((q : ℤ) - 4 * m) ≤
        48 * (m : ℤ) * q * ((N : ℤ) - (m : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1))) := by
      refine le_trans A ?_
      apply mul_le_mul_of_nonneg_right _ S0
      apply mul_le_mul_of_nonneg_left zRq
      positivity
    calc X * (3 * q * ((q : ℤ) - m)) = (3 * (3 * (N : ℤ) - 4 * m) * ((q : ℤ) - 4 * m)) *
          ((q : ℤ) * ((q : ℤ) - m) * ((q : ℤ) - m)) := by rw [hX]; ring
      _ ≤ (48 * (m : ℤ) * q * ((N : ℤ) - (m : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1)))) *
          ((q : ℤ) * ((q : ℤ) - m) * ((q : ℤ) - m)) :=
          mul_le_mul_of_nonneg_right A2 (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
      _ = 48 * (m : ℤ) * q * ((q : ℤ) * ((q : ℤ) - m) *
          ((N : ℤ) - (m : ℤ) * (1 + (R : ℤ) * ((q : ℤ) + 1))) * ((q : ℤ) - m)) := by ring
  have hmain := LV q N q m X.toNat (48 * m * q) I D (fun _ => R) hq hN hline huniq (by omega)
    le_rfl ⟨hD1, hD2⟩ hDc
    (fun p l h => by rw [hDf]; exact hinc p l h)
    (fun z hz hno => by rw [hDf]; exact hsound z hz hno)
    hRb hde hstep hfin
  have zmain : ((X.toNat : ℕ) : ℤ) ≤ (((48 * m * q : ℕ)) : ℤ) * (D.size : ℤ) := by
    exact_mod_cast hmain
  rw [ha, hc] at zmain
  have zs : (D.size : ℤ) ≤ C.size := by exact_mod_cast hDs
  rw [← hX]
  calc X ≤ 48 * (m : ℤ) * q * (D.size : ℤ) := zmain
    _ ≤ 48 * (m : ℤ) * q * (C.size : ℤ) :=
        mul_le_mul_of_nonneg_left zs (by positivity)
