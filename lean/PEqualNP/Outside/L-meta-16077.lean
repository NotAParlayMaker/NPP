import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16077_aux

-- two times x is at most 4 e times (x / e), when 1 <= e <= x
lemma two_mul_le (e x : ℕ) (he : 1 ≤ e) (hx : e ≤ x) : 2 * x ≤ 4 * e * (x / e) := by
  have he0 : 0 < e := he
  have hq : 1 ≤ x / e := Nat.div_pos hx he0
  have hs : x % e < e := Nat.mod_lt x he0
  have hd : x = e * (x / e) + x % e := (Nat.div_add_mod x e).symm
  have hle : x % e ≤ e * (x / e) := by
    have h1 : e ≤ e * (x / e) := Nat.le_mul_of_pos_right e (by omega)
    omega
  nlinarith [hd, hle]

-- (2 * a) / d <= 2 * (a / d) + 1
lemma div_two_mul (a d : ℕ) (hd : 1 ≤ d) : 2 * a / d ≤ 2 * (a / d) + 1 := by
  have hd0 : 0 < d := hd
  rw [Nat.div_le_iff_le_mul hd0]
  have h := Nat.div_add_mod a d
  have hm := Nat.mod_lt a hd0
  have ha : a < (a / d + 1) * d := by nlinarith [h, hm]
  have h2 : 2 * a < 2 * ((a / d + 1) * d) := by nlinarith [ha]
  have h3 : 2 * a < (2 * (a / d) + 1) * d + d := by
    calc 2 * a < 2 * ((a / d + 1) * d) := h2
      _ = (2 * (a / d) + 1) * d + d := by ring
  omega

end PEqualNP.Outside.L_meta_16077_aux

theorem PEqualNP.Outside.L_meta_16077 :
    ∀ (r : ℕ → ℕ) (K e : ℕ), 1 ≤ e → (∀ k : ℕ, K ≤ k → 2 * r k + 2 ^ k / e ≤ r (k + 1)) → ∀ d : ℕ, 1 ≤ d → ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k → 4 * 2 ^ k + 2 ^ k / d < r k := by
  classical
  intro r K e he hstep d hd
  -- K0 with K <= K0 and e <= 2^K0
  obtain ⟨K0, hKK0, hK0e⟩ : ∃ K0 : ℕ, K ≤ K0 ∧ e ≤ 2 ^ K0 := by
    refine ⟨K + e, Nat.le_add_right K e, ?_⟩
    have h1 : 2 ^ e ≤ 2 ^ (K + e) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left e K)
    have h2 : e + 1 ≤ 2 ^ e := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := e))
    omega
  -- growth: 4*e*r(K0+m) >= m * 2^(K0+m)
  have growth : ∀ m : ℕ, m * 2 ^ (K0 + m) ≤ 4 * e * r (K0 + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hstepm : 2 * r (K0 + m) + 2 ^ (K0 + m) / e ≤ r (K0 + m + 1) := by
          refine hstep (K0 + m) (by omega)
        have hmono : e ≤ 2 ^ (K0 + m) := by
          have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_add_right K0 m)
          omega
        have hdiv : 2 * 2 ^ (K0 + m) ≤ 4 * e * (2 ^ (K0 + m) / e) :=
          PEqualNP.Outside.L_meta_16077_aux.two_mul_le e (2 ^ (K0 + m)) he hmono
        have hpow : (2 : ℕ) ^ (K0 + m + 1) = 2 * 2 ^ (K0 + m) := by
          rw [Nat.pow_succ]
          ring
        calc (m + 1) * 2 ^ (K0 + m + 1)
            = 2 * m * 2 ^ (K0 + m) + 2 * 2 ^ (K0 + m) := by rw [hpow]; ring
          _ ≤ 2 * m * 2 ^ (K0 + m) + 4 * e * (2 ^ (K0 + m) / e) := by omega
          _ ≤ 2 * (4 * e * r (K0 + m)) + 4 * e * (2 ^ (K0 + m) / e) := by
                have : m * 2 ^ (K0 + m) ≤ 4 * e * r (K0 + m) := ih
                nlinarith [this]
          _ = 4 * e * (2 * r (K0 + m) + 2 ^ (K0 + m) / e) := by ring
          _ ≤ 4 * e * r (K0 + m + 1) := by
                have : 0 < 4 * e := by omega
                exact Nat.mul_le_mul_left (4 * e) hstepm
  -- the threshold function
  set T : ℕ → ℕ := fun k => 4 * 2 ^ k + 2 ^ k / d with hT
  have hTle : ∀ k, T k ≤ 5 * 2 ^ k := by
    intro k
    have : 2 ^ k / d ≤ 2 ^ k := Nat.div_le_self _ _
    simp only [hT]
    omega
  have hTsucc : ∀ k, T (k + 1) ≤ 2 * T k + 1 := by
    intro k
    have hd2 : 2 * 2 ^ k / d ≤ 2 * (2 ^ k / d) + 1 :=
      PEqualNP.Outside.L_meta_16077_aux.div_two_mul (2 ^ k) d hd
    have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
    simp only [hT]
    rw [hp]
    omega
  -- it gets above
  set m : ℕ := 20 * e + 1 with hm
  have habove : T (K0 + m) < r (K0 + m) := by
    have hg : m * 2 ^ (K0 + m) ≤ 4 * e * r (K0 + m) := growth m
    have hTe : 4 * e * T (K0 + m) < m * 2 ^ (K0 + m) := by
      have h1 : T (K0 + m) ≤ 5 * 2 ^ (K0 + m) := hTle _
      have h2 : 4 * e * T (K0 + m) ≤ 4 * e * (5 * 2 ^ (K0 + m)) := Nat.mul_le_mul_left _ h1
      have h3 : 4 * e * (5 * 2 ^ (K0 + m)) = 20 * e * 2 ^ (K0 + m) := by ring
      have h4 : 20 * e * 2 ^ (K0 + m) < m * 2 ^ (K0 + m) := by
        have h5 : 20 * e < m := by omega
        have h6 : 0 < 2 ^ (K0 + m) := by positivity
        exact Nat.mul_lt_mul_of_pos_right h5 h6
      omega
    have hlt : 4 * e * T (K0 + m) < 4 * e * r (K0 + m) := lt_of_lt_of_le hTe hg
    exact Nat.lt_of_mul_lt_mul_left hlt
  -- and stays above
  have stepup : ∀ k : ℕ, K ≤ k → T k < r k → T (k + 1) < r (k + 1) := by
    intro k hKk hlt
    have h1 : T (k + 1) ≤ 2 * T k + 1 := hTsucc k
    have h2 : 2 * T k + 2 ≤ 2 * r k := by
      have hlt' : T k + 1 ≤ r k := hlt
      omega
    have h3 : 2 * r k ≤ r (k + 1) :=
      le_trans (Nat.le_add_right (2 * r k) (2 ^ k / e)) (hstep k hKk)
    calc T (k + 1) ≤ 2 * T k + 1 := h1
      _ < 2 * r k := by omega
      _ ≤ r (k + 1) := h3
  refine ⟨K0 + m, ?_⟩
  intro k hk
  have hmain : ∀ j : ℕ, T (K0 + m + j) < r (K0 + m + j) := by
    intro j
    induction j with
    | zero => simpa using habove
    | succ j ih =>
        have h1 : T (K0 + m + j + 1) < r (K0 + m + j + 1) :=
          stepup (K0 + m + j) (by omega) ih
        simpa [Nat.add_assoc] using h1
  have hkj : K0 + m + (k - (K0 + m)) = k := Nat.add_sub_cancel' hk
  have := hmain (k - (K0 + m))
  rwa [hkj] at this
