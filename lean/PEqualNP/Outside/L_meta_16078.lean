import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16078_aux

lemma two_mul_le (e x : ℕ) (he : 1 ≤ e) (hx : e ≤ x) : 2 * x ≤ 4 * e * (x / e) := by
  have he0 : 0 < e := he
  have hq : 1 ≤ x / e := Nat.div_pos hx he0
  have hs : x % e < e := Nat.mod_lt x he0
  have hd : x = e * (x / e) + x % e := (Nat.div_add_mod x e).symm
  have hle : x % e ≤ e * (x / e) := by
    have h1 : e ≤ e * (x / e) := Nat.le_mul_of_pos_right e (by omega)
    omega
  nlinarith [hd, hle]

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

end PEqualNP.Outside.L_meta_16078_aux

theorem PEqualNP.Outside.L_meta_16078 :
    ∀ (r : ℕ → ℕ) (K e d : ℕ), 1 ≤ e → 1 ≤ d → (∀ k : ℕ, K ≤ k → (r k ≤ 4 * 2 ^ k + 2 ^ k / d → 2 * r k + 2 ^ k / e ≤ r (k + 1)) ∧ (4 * 2 ^ k + 2 ^ k / d < r k → 2 * r k ≤ r (k + 1))) → ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k → 4 * 2 ^ k + 2 ^ k / d < r k := by
  intro r K e d he hd hstep
  obtain ⟨K0, hKK0, hK0e⟩ : ∃ K0 : ℕ, K ≤ K0 ∧ e ≤ 2 ^ K0 := by
    refine ⟨K + e, Nat.le_add_right K e, ?_⟩
    have h1 : 2 ^ e ≤ 2 ^ (K + e) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left e K)
    have h2 : e + 1 ≤ 2 ^ e := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := e))
    omega
  set T : ℕ → ℕ := fun k => 4 * 2 ^ k + 2 ^ k / d with hT
  have hTle : ∀ k, T k ≤ 5 * 2 ^ k := by
    intro k
    have : 2 ^ k / d ≤ 2 ^ k := Nat.div_le_self _ _
    simp only [hT]
    omega
  have hTsucc : ∀ k, T (k + 1) ≤ 2 * T k + 1 := by
    intro k
    have hd2 : 2 * 2 ^ k / d ≤ 2 * (2 ^ k / d) + 1 :=
      PEqualNP.Outside.L_meta_16078_aux.div_two_mul (2 ^ k) d hd
    have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
    simp only [hT]
    rw [hp]
    omega
  have stepup : ∀ k : ℕ, K ≤ k → T k < r k → T (k + 1) < r (k + 1) := by
    intro k hKk hlt
    have h2 : 2 * r k ≤ r (k + 1) := (hstep k hKk).2 hlt
    have h1 : T (k + 1) ≤ 2 * T k + 1 := hTsucc k
    calc T (k + 1) ≤ 2 * T k + 1 := h1
      _ < 2 * r k := by omega
      _ ≤ r (k + 1) := h2
  set m : ℕ := 20 * e + 1 with hm
  by_cases hup : T (K0 + m) < r (K0 + m)
  · refine ⟨K0 + m, ?_⟩
    intro k hk
    have hmain : ∀ j : ℕ, T (K0 + m + j) < r (K0 + m + j) := by
      intro j
      induction j with
      | zero => simpa using hup
      | succ j ih =>
          have h1 : T (K0 + m + j + 1) < r (K0 + m + j + 1) :=
            stepup (K0 + m + j) (by omega) ih
          simpa [Nat.add_assoc] using h1
    have hkj : K0 + m + (k - (K0 + m)) = k := Nat.add_sub_cancel' hk
    have := hmain (k - (K0 + m))
    rwa [hkj] at this
  · push_neg at hup
    exfalso
    have hbel : ∀ i : ℕ, i ≤ m → r (K0 + i) ≤ T (K0 + i) := by
      intro i hi
      by_contra hcon
      push_neg at hcon
      have hmain : ∀ j : ℕ, T (K0 + i + j) < r (K0 + i + j) := by
        intro j
        induction j with
        | zero => simpa using hcon
        | succ j ih =>
            have h1 : T (K0 + i + j + 1) < r (K0 + i + j + 1) :=
              stepup (K0 + i + j) (by omega) ih
            simpa [Nat.add_assoc] using h1
      have hjm : K0 + i + (m - i) = K0 + m := by omega
      have hfin := hmain (m - i)
      rw [hjm] at hfin
      omega
    have growth : ∀ j : ℕ, j ≤ m → j * 2 ^ (K0 + j) ≤ 4 * e * r (K0 + j) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
          intro hj
          have hj' : j ≤ m := by omega
          have hgain : 2 * r (K0 + j) + 2 ^ (K0 + j) / e ≤ r (K0 + j + 1) :=
            (hstep (K0 + j) (by omega)).1 (hbel j hj')
          have hmono : e ≤ 2 ^ (K0 + j) := by
            have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_add_right K0 j)
            omega
          have hdiv : 2 * 2 ^ (K0 + j) ≤ 4 * e * (2 ^ (K0 + j) / e) :=
            PEqualNP.Outside.L_meta_16078_aux.two_mul_le e (2 ^ (K0 + j)) he hmono
          have hpow : (2 : ℕ) ^ (K0 + j + 1) = 2 * 2 ^ (K0 + j) := by rw [Nat.pow_succ]; ring
          calc (j + 1) * 2 ^ (K0 + j + 1)
              = 2 * j * 2 ^ (K0 + j) + 2 * 2 ^ (K0 + j) := by rw [hpow]; ring
            _ ≤ 2 * j * 2 ^ (K0 + j) + 4 * e * (2 ^ (K0 + j) / e) := by omega
            _ ≤ 2 * (4 * e * r (K0 + j)) + 4 * e * (2 ^ (K0 + j) / e) := by
                  have hih : j * 2 ^ (K0 + j) ≤ 4 * e * r (K0 + j) := ih hj'
                  nlinarith [hih]
            _ = 4 * e * (2 * r (K0 + j) + 2 ^ (K0 + j) / e) := by ring
            _ ≤ 4 * e * r (K0 + j + 1) := by
                  have h4e : 0 < 4 * e := by omega
                  exact Nat.mul_le_mul_left (4 * e) hgain
    have hg : m * 2 ^ (K0 + m) ≤ 4 * e * r (K0 + m) := growth m (le_refl m)
    have hb : r (K0 + m) ≤ T (K0 + m) := hbel m (le_refl m)
    have hTle' : T (K0 + m) ≤ 5 * 2 ^ (K0 + m) := hTle _
    have h2 : 4 * e * r (K0 + m) ≤ 4 * e * (5 * 2 ^ (K0 + m)) := by nlinarith [hb, hTle']
    have h3 : 4 * e * (5 * 2 ^ (K0 + m)) = 20 * e * 2 ^ (K0 + m) := by ring
    have h4 : 20 * e * 2 ^ (K0 + m) < m * 2 ^ (K0 + m) := by
      have h5 : 20 * e < m := by omega
      have h6 : 0 < 2 ^ (K0 + m) := by positivity
      exact Nat.mul_lt_mul_of_pos_right h5 h6
    omega
