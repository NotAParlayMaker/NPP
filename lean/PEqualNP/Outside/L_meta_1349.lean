import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

def miss (h j : ℕ) : ℕ :=
  if j = 0 then 2 ^ h * 2 ^ h + 2 ^ h + 1
  else if j = h + 2 then 0
  else 2 ^ h * (2 ^ h + 1) / 2 ^ (j - 1) - 2 ^ h

def charge (h j : ℕ) : ℕ :=
  if j = h + 2 then 2 ^ h else 2 ^ (j - 1) - 1

def cost (h : ℕ) (uv : ℕ × ℕ) : ℕ :=
  (miss h uv.1 - miss h uv.2) * charge h uv.2

def window (h : ℕ) (P : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
    (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))

def score (h : ℕ) (P : Finset ℕ) : ℕ :=
  (window h P).sup (cost h)

def fence (m : ℕ) (cuts : List ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if h : i < cuts.length then cuts[i] else m

lemma two_dvd_pow (n : ℕ) (hn : 1 ≤ n) : 2 ∣ 2 ^ n := by
  have hdv : 2 ^ 1 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn
  simpa using hdv

lemma two_pow_pred_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ (n - 1) ≤ 2 ^ n - 1 := by
  have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have hn' : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hsplit : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    conv_lhs => rw [← hn', Nat.pow_succ, Nat.mul_comm, Nat.two_mul]
  have : 2 ^ (n - 1) + 1 ≤ 2 ^ n := by
    calc
      2 ^ (n - 1) + 1 ≤ 2 ^ (n - 1) + 2 ^ (n - 1) := Nat.add_le_add_left hpos _
      _ = 2 ^ n := hsplit.symm
  exact Nat.le_sub_of_add_le this

lemma two_mul_pred_le (k : ℕ) (hk : 1 ≤ k) :
    2 * (2 ^ (k - 1) - 1) ≤ 2 ^ k - 1 := by
  have hk' : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have hsplit : 2 ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [← hk', Nat.pow_succ, Nat.mul_comm]
  calc
    2 * (2 ^ (k - 1) - 1) = 2 * 2 ^ (k - 1) - 2 := by rw [Nat.mul_sub, Nat.mul_one]
    _ = 2 ^ k - 2 := by rw [← hsplit]
    _ ≤ 2 ^ k - 1 := Nat.sub_le_sub_left (by decide : 1 ≤ 2) _

lemma div_mul_pow_pred (h e : ℕ) (he : 1 ≤ e) (heh : e ≤ h) :
    2 ^ h / 2 ^ e * 2 ^ (e - 1) = 2 ^ h / 2 := by
  have hdvd : 2 ^ e ∣ 2 ^ h := Nat.pow_dvd_pow 2 heh
  have h2 : 2 ∣ 2 ^ e := two_dvd_pow e he
  calc
    2 ^ h / 2 ^ e * 2 ^ (e - 1)
        = 2 ^ h / 2 ^ e * (2 ^ e / 2) := by rw [← Nat.pow_div he (by decide : 0 < 2)]
    _ = (2 ^ h / 2 ^ e * 2 ^ e) / 2 := (Nat.mul_div_assoc (2 ^ h / 2 ^ e) h2).symm
    _ = 2 ^ h / 2 := by rw [Nat.div_mul_cancel hdvd]

lemma miss_last (h : ℕ) : miss h (h + 2) = 0 := by
  unfold miss
  rw [ite_eq_right (by omega : h + 2 ≠ 0), ite_eq_left rfl]

lemma miss_zero (h : ℕ) : miss h 0 = 2 ^ h * 2 ^ h + 2 ^ h + 1 := by
  unfold miss
  rw [ite_eq_left rfl]

lemma miss_factor (h j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ h + 1) :
    miss h j = (2 ^ h / 2 ^ (j - 1)) * (2 ^ h + 1 - 2 ^ (j - 1)) := by
  have hne0 : j ≠ 0 := by omega
  have hnel : j ≠ h + 2 := by omega
  set d := 2 ^ (j - 1)
  have hdvd : d ∣ 2 ^ h := Nat.pow_dvd_pow 2 (by omega : j - 1 ≤ h)
  have hsplit : 2 ^ h * (2 ^ h + 1) / d = (2 ^ h / d) * (2 ^ h + 1) := by
    calc
      2 ^ h * (2 ^ h + 1) / d = (2 ^ h + 1) * 2 ^ h / d := by rw [Nat.mul_comm]
      _ = (2 ^ h + 1) * (2 ^ h / d) := Nat.mul_div_assoc (2 ^ h + 1) hdvd
      _ = (2 ^ h / d) * (2 ^ h + 1) := Nat.mul_comm _ _
  have hq : 2 ^ h = (2 ^ h / d) * d := (Nat.div_mul_cancel hdvd).symm
  have hdle : d ≤ 2 ^ h + 1 := by
    have : d ≤ 2 ^ h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    omega
  unfold miss
  rw [ite_eq_right hne0, ite_eq_right hnel]
  calc
    2 ^ h * (2 ^ h + 1) / d - 2 ^ h
        = (2 ^ h / d) * (2 ^ h + 1) - 2 ^ h := by rw [hsplit]
    _ = (2 ^ h / d) * (2 ^ h + 1) - (2 ^ h / d) * d := by rw [← hq]
    _ = (2 ^ h / d) * (2 ^ h + 1 - d) := (Nat.mul_sub (2 ^ h / d) (2 ^ h + 1) d).symm

lemma miss_diff (h a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ h + 1) :
    miss h a - miss h b =
      (2 ^ h / 2 ^ (b - 1)) * (2 ^ h + 1) * (2 ^ (b - a) - 1) := by
  set q := 2 ^ h
  set da := 2 ^ (a - 1)
  set db := 2 ^ (b - 1)
  set k := 2 ^ (b - a)
  have hma := miss_factor h a ha (hab.trans hb)
  have hmb := miss_factor h b (by omega) hb
  have hk : db = da * k := by
    simp only [db, da, k]
    rw [show b - 1 = (a - 1) + (b - a) by omega, Nat.pow_add]
  have hdbq : db ∣ q := Nat.pow_dvd_pow 2 (by omega : b - 1 ≤ h)
  set sb := q / db
  have hsb : q = db * sb := (Nat.mul_div_cancel' hdbq).symm
  have hs : q / da = k * sb := by
    have hq' : q = da * (k * sb) := by rw [hsb, hk, Nat.mul_assoc]
    have hda_pos : 0 < da := Nat.two_pow_pos _
    calc
      q / da = da * (k * sb) / da := by rw [hq']
      _ = k * sb := Nat.mul_div_cancel_left (k * sb) hda_pos
  have hdb_le : db ≤ q + 1 := by
    have : db ≤ q := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    omega
  have hkda : k * da ≤ q + 1 := by
    rw [Nat.mul_comm, ← hk]
    exact hdb_le
  have hkq : q + 1 ≤ k * (q + 1) := Nat.le_mul_of_pos_left (q + 1) (Nat.two_pow_pos _)
  have hmul : k * (q + 1 - da) = k * (q + 1) - k * da := Nat.mul_sub k (q + 1) da
  have hcancel :
      (q + 1 - k * da) + (k * (q + 1) - (q + 1)) = k * (q + 1) - k * da := by
    rw [Nat.add_comm]
    exact Nat.sub_add_sub_cancel hkq hkda
  have htail : k * (q + 1) - (q + 1) = (k - 1) * (q + 1) := by
    rw [Nat.mul_comm k (q + 1), Nat.mul_comm (k - 1) (q + 1)]
    exact (Nat.mul_sub_one (q + 1) k).symm
  have hsum : k * (q + 1 - da) = (q + 1 - db) + (k - 1) * (q + 1) := by
    calc
      k * (q + 1 - da) = k * (q + 1) - k * da := hmul
      _ = (q + 1 - k * da) + (k * (q + 1) - (q + 1)) := hcancel.symm
      _ = (q + 1 - db) + (k - 1) * (q + 1) := by
        rw [show k * da = db by rw [hk, Nat.mul_comm], htail]
  have hma' : miss h a = sb * (k * (q + 1 - da)) := by
    rw [hma, hs]
    calc
      (k * sb) * (q + 1 - da) = k * (sb * (q + 1 - da)) := Nat.mul_assoc _ _ _
      _ = sb * (k * (q + 1 - da)) := Nat.mul_left_comm _ _ _
  have hmb' : miss h b = sb * (q + 1 - db) := by
    simpa [q, db] using hmb
  have hjoin : miss h a = miss h b + sb * ((k - 1) * (q + 1)) := by
    rw [hma', hmb', hsum, Nat.mul_add]
  calc
    miss h a - miss h b = sb * ((k - 1) * (q + 1)) := by
      rw [hjoin, Nat.add_sub_cancel_left]
    _ = sb * (q + 1) * (k - 1) := by
      rw [Nat.mul_assoc, Nat.mul_comm (k - 1) (q + 1), ← Nat.mul_assoc]

lemma sq_div_two_le_zero_gap (h b : ℕ) (hh : 1 ≤ h) (hb1 : 2 ≤ b) (hb2 : b ≤ h + 1) :
    2 ^ h * 2 ^ h / 2 ≤ miss h 0 - miss h b := by
  set q := 2 ^ h
  set d := 2 ^ (b - 1)
  have hfac := miss_factor h b (by omega) hb2
  have hr : q / d ≤ q / 2 := by
    have hbh : b - 1 ≤ h := by omega
    rw [show q = 2 ^ h by rfl, Nat.pow_div hbh (by decide : 0 < 2),
      Nat.pow_div (by omega : 1 ≤ h) (by decide : 0 < 2)]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hsub : q + 1 - d ≤ q - 1 := by
    have hd : 2 ≤ d := by
      have : 2 ^ 1 ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ b - 1)
      simpa [d] using this
    omega
  have hmissb : miss h b ≤ (q / 2) * (q - 1) := by
    calc
      miss h b = (q / d) * (q + 1 - d) := by simpa [q, d] using hfac
      _ ≤ (q / 2) * (q + 1 - d) := Nat.mul_le_mul_right _ hr
      _ ≤ (q / 2) * (q - 1) := Nat.mul_le_mul_left _ hsub
  have h2q : 2 ∣ q := by
    have : 2 ^ 1 ∣ 2 ^ h := Nat.pow_dvd_pow 2 hh
    simpa [q] using this
  have hsq : q ^ 2 / 2 = q / 2 * q := by
    calc
      q ^ 2 / 2 = q * q / 2 := by rw [Nat.pow_two]
      _ = q * (q / 2) := Nat.mul_div_assoc q h2q
      _ = q / 2 * q := Nat.mul_comm _ _
  have hsum : q ^ 2 / 2 + (q / 2) * (q - 1) = (q / 2) * (2 * q - 1) := by
    have hadd : q + (q - 1) = 2 * q - 1 := by
      have hq1 : 1 ≤ q := by simpa [q] using (Nat.one_le_two_pow : 1 ≤ 2 ^ h)
      calc
        q + (q - 1) = q + q - 1 := (Nat.add_sub_assoc hq1 q).symm
        _ = 2 * q - 1 := by rw [Nat.two_mul]
    calc
      q ^ 2 / 2 + (q / 2) * (q - 1) = q / 2 * q + (q / 2) * (q - 1) := by rw [hsq]
      _ = (q / 2) * (q + (q - 1)) := by rw [← Nat.mul_add]
      _ = (q / 2) * (2 * q - 1) := by rw [hadd]
  have hpoly : (q / 2) * (2 * q - 1) ≤ q * q + q + 1 := by
    have hmul : 2 * ((q / 2) * (2 * q - 1)) = q * (2 * q - 1) := by
      rw [← Nat.mul_assoc, Nat.mul_div_cancel' h2q]
    have hexp : q * (2 * q - 1) = 2 * q * q - q := by
      calc
        q * (2 * q - 1) = q * (2 * q) - q := by rw [Nat.mul_sub, Nat.mul_one]
        _ = 2 * q * q - q := by rw [← Nat.mul_assoc, Nat.mul_comm q 2]
    have hle : 2 * q * q - q ≤ 2 * (q * q) + 2 * q + 2 := by
      calc
        2 * q * q - q ≤ 2 * q * q := Nat.sub_le _ _
        _ = 2 * (q * q) := by rw [Nat.mul_assoc]
        _ ≤ 2 * (q * q) + (2 * q + 2) := Nat.le_add_right _ _
        _ = 2 * (q * q) + 2 * q + 2 := by rw [← Nat.add_assoc]
    have htwo : 2 * ((q / 2) * (2 * q - 1)) ≤ 2 * (q * q + q + 1) := by
      rw [hmul, hexp]
      calc
        2 * q * q - q ≤ 2 * (q * q) + 2 * q + 2 := hle
        _ = 2 * (q * q + q + 1) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    exact Nat.le_of_mul_le_mul_left htwo (by decide : 0 < 2)
  have hupper : (q / 2) * (q - 1) ≤ miss h 0 := by
    rw [miss_zero]
    calc
      (q / 2) * (q - 1) ≤ q ^ 2 / 2 + (q / 2) * (q - 1) := Nat.le_add_left _ _
      _ = (q / 2) * (2 * q - 1) := hsum
      _ ≤ q * q + q + 1 := hpoly
  have hbase : q ^ 2 / 2 ≤ miss h 0 - (q / 2) * (q - 1) :=
    (Nat.le_sub_iff_add_le hupper).2 (by
      rw [miss_zero, hsum]
      simpa [Nat.pow_two] using hpoly)
  have hpow : q * q / 2 = q ^ 2 / 2 := by rw [Nat.pow_two]
  rw [hpow]
  exact hbase.trans (Nat.sub_le_sub_left hmissb _)

lemma cost_interior (h a b : ℕ) (hh : 1 ≤ h) (ha : 1 ≤ a) (hgap : a + 2 ≤ b) (hb : b ≤ h + 1) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (b - a - 1) - 1) ≤ cost h (a, b) := by
  have hdiff := miss_diff h a b ha (by omega) hb
  have hch : charge h b = 2 ^ (b - 1) - 1 := by
    rw [charge, ite_eq_right (by omega : b ≠ h + 2)]
  set q := 2 ^ h
  set e := b - 1
  set t := 2 ^ (b - a - 1) - 1
  have he : 1 ≤ e := by omega
  have heh : e ≤ h := by omega
  have hk : 1 ≤ b - a := by omega
  have hcost : cost h (a, b) =
      (q / 2 ^ e) * (q + 1) * (2 ^ (b - a) - 1) * (2 ^ e - 1) := by
    rw [cost, hdiff, hch]
  have hge_pow : 2 ^ (e - 1) ≤ 2 ^ e - 1 := two_pow_pred_le e he
  have hdiv : q / 2 ^ e * 2 ^ (e - 1) = q / 2 := by
    simpa [q] using div_mul_pow_pred h e he heh
  have htwo : 2 * t ≤ 2 ^ (b - a) - 1 := by
    simpa [t] using two_mul_pred_le (b - a) hk
  have h2q : 2 ∣ q := by
    have : 2 ^ 1 ∣ 2 ^ h := Nat.pow_dvd_pow 2 hh
    simpa [q] using this
  have hassoc : (q / 2) * (q + 1) * (2 * t) = q * (q + 1) * t := by
    have hcancel : q / 2 * 2 = q := Nat.div_mul_cancel h2q
    calc
      (q / 2) * (q + 1) * (2 * t) = (q / 2) * ((q + 1) * (2 * t)) := by rw [Nat.mul_assoc]
      _ = (q / 2) * (2 * ((q + 1) * t)) := by
        conv_lhs => arg 2; rw [Nat.mul_left_comm (q + 1) 2 t]
      _ = ((q / 2) * 2) * ((q + 1) * t) := by rw [← Nat.mul_assoc]
      _ = q * ((q + 1) * t) := by rw [hcancel]
      _ = q * (q + 1) * t := by rw [Nat.mul_assoc]
  have hmove : (q / 2) * (q + 1) * (2 ^ (b - a) - 1) =
      (q / 2 ^ e) * (q + 1) * (2 ^ (b - a) - 1) * 2 ^ (e - 1) := by
    rw [← hdiv]
    ac_rfl
  calc
    (q * q / 2) * t ≤ q * q * t := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    _ ≤ q * (q + 1) * t :=
      Nat.mul_le_mul_right t (Nat.mul_le_mul_left q (Nat.le_succ q))
    _ = (q / 2) * (q + 1) * (2 * t) := hassoc.symm
    _ ≤ (q / 2) * (q + 1) * (2 ^ (b - a) - 1) := Nat.mul_le_mul_left _ htwo
    _ = (q / 2 ^ e) * (q + 1) * (2 ^ (b - a) - 1) * 2 ^ (e - 1) := hmove
    _ ≤ (q / 2 ^ e) * (q + 1) * (2 ^ (b - a) - 1) * (2 ^ e - 1) :=
      Nat.mul_le_mul_left _ hge_pow
    _ = cost h (a, b) := hcost.symm

lemma cost_suffix (h a : ℕ) (_hh : 1 ≤ h) (ha1 : 1 ≤ a) (ha2 : a ≤ h) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (h + 1 - a) - 1) ≤ cost h (a, h + 2) := by
  set q := 2 ^ h
  set da := 2 ^ (a - 1)
  have hfac := miss_factor h a ha1 (by omega)
  have hdvd : da ∣ q := Nat.pow_dvd_pow 2 (by omega : a - 1 ≤ h)
  have hquot : q / da = 2 ^ (h - (a - 1)) := Nat.pow_div (by omega) (by decide : 0 < 2)
  have hsub : q - da = da * (q / da - 1) := by
    have hqeq : da * (q / da) = q := Nat.mul_div_cancel' hdvd
    calc
      q - da = da * (q / da) - da := by conv_lhs => rw [← hqeq]
      _ = da * (q / da) - da * 1 := by rw [Nat.mul_one]
      _ = da * (q / da - 1) := (Nat.mul_sub da (q / da) 1).symm
  have hsplit : q + 1 - da = (q - da) + 1 := by
    have hda_le : da ≤ q := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    omega
  have hprod : ((q / da) * (q + 1 - da)) * q = (q ^ 2 / da) * (q + 1 - da) := by
    calc
      ((q / da) * (q + 1 - da)) * q = (q / da) * q * (q + 1 - da) := by rw [Nat.mul_right_comm]
      _ = (q * (q / da)) * (q + 1 - da) := by rw [Nat.mul_comm (q / da) q]
      _ = (q * q / da) * (q + 1 - da) := by rw [Nat.mul_div_assoc q hdvd]
      _ = (q ^ 2 / da) * (q + 1 - da) := by rw [← Nat.pow_two]
  have hpiece : (q ^ 2 / da) * (q - da) = q ^ 2 * (q / da - 1) := by
    have hdvd2 : da ∣ q ^ 2 := by
      rw [Nat.pow_two]
      exact Nat.dvd_mul_right_of_dvd hdvd q
    calc
      (q ^ 2 / da) * (q - da) = (q ^ 2 / da) * (da * (q / da - 1)) := by rw [hsub]
      _ = ((q ^ 2 / da) * da) * (q / da - 1) := by rw [Nat.mul_assoc]
      _ = q ^ 2 * (q / da - 1) := by rw [Nat.div_mul_cancel hdvd2]
  have hcost : cost h (a, h + 2) = q ^ 2 * (q / da - 1) + q ^ 2 / da := by
    simp only [cost, miss_last, Nat.sub_zero, charge]
    rw [hfac]
    calc
      ((q / da) * (q + 1 - da)) * q = (q ^ 2 / da) * (q + 1 - da) := hprod
      _ = (q ^ 2 / da) * ((q - da) + 1) := by rw [hsplit]
      _ = (q ^ 2 / da) * (q - da) + q ^ 2 / da := by rw [Nat.mul_add, Nat.mul_one]
      _ = q ^ 2 * (q / da - 1) + q ^ 2 / da := by rw [hpiece]
  have hexp : 2 ^ (h + 1 - a) = q / da := by
    rw [hquot]
    congr 1
    omega
  calc
    (q * q / 2) * (2 ^ (h + 1 - a) - 1) ≤ q * q * (2 ^ (h + 1 - a) - 1) :=
      Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    _ = q ^ 2 * (q / da - 1) := by rw [← Nat.pow_two, hexp]
    _ ≤ q ^ 2 * (q / da - 1) + q ^ 2 / da := Nat.le_add_right _ _
    _ = cost h (a, h + 2) := hcost.symm

lemma cost_full (h : ℕ) (hh : 1 ≤ h) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (h + 1) - 1) ≤ cost h (0, h + 2) := by
  set q := 2 ^ h
  have h2q : 2 ∣ q := by
    have : 2 ^ 1 ∣ 2 ^ h := Nat.pow_dvd_pow 2 hh
    simpa [q] using this
  have h2sq : 2 ∣ q ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.dvd_mul_right_of_dvd h2q q
  have hpow : 2 ^ (h + 1) = 2 * q := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hcost : cost h (0, h + 2) = (q * q + q + 1) * q := by
    simp only [cost, miss_zero, miss_last, Nat.sub_zero, charge, q, ite_true]
  calc
    (q * q / 2) * (2 ^ (h + 1) - 1) ≤ (q * q / 2) * 2 ^ (h + 1) :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = (q * q / 2) * (2 * q) := by rw [hpow]
    _ = (q * q / 2 * 2) * q := by rw [← Nat.mul_assoc]
    _ = q * q * q := by rw [Nat.div_mul_cancel (by simpa [Nat.pow_two] using h2sq)]
    _ ≤ (q * q + q + 1) * q := Nat.mul_le_mul_right q (Nat.le_add_right (q * q) (q + 1))
    _ = cost h (0, h + 2) := hcost.symm

lemma cost_ge (h a L : ℕ) (hh : 1 ≤ h) (hL : 1 ≤ L) (hb : a + L ≤ h + 3) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (L - 2) - 1) ≤ cost h (a, a + L - 1) := by
  by_cases hsmall : L ≤ 2
  · have hzero : L - 2 = 0 := by omega
    rw [hzero]
    simp
  · have hL3 : 3 ≤ L := by omega
    set b := a + L - 1
    by_cases hlast : b = h + 2
    · have hlen : a + L = h + 3 := by omega
      by_cases ha0 : a = 0
      · have hL' : L = h + 3 := by omega
        have hexp : L - 2 = h + 1 := by omega
        rw [ha0, hlast, hexp]
        exact cost_full h hh
      · have ha1 : 1 ≤ a := by omega
        have ha2 : a ≤ h := by omega
        have hexp : L - 2 = h + 1 - a := by omega
        rw [hlast, hexp]
        exact cost_suffix h a hh ha1 ha2
    · have hb_mid : b ≤ h + 1 := by omega
      by_cases ha0 : a = 0
      · have hexp : L - 2 = b - 1 := by omega
        have hb2 : 2 ≤ b := by omega
        have hdiff := sq_div_two_le_zero_gap h b hh hb2 hb_mid
        have hch : charge h b = 2 ^ (b - 1) - 1 := by
          rw [charge, ite_eq_right (by omega : b ≠ h + 2)]
        calc
          (2 ^ h * 2 ^ h / 2) * (2 ^ (L - 2) - 1)
              = (2 ^ h * 2 ^ h / 2) * charge h b := by rw [hexp, hch]
          _ ≤ (miss h 0 - miss h b) * charge h b := Nat.mul_le_mul_right _ hdiff
          _ = cost h (a, b) := by rw [cost, ha0]
      · have ha1 : 1 ≤ a := by omega
        have hgap : a + 2 ≤ b := by omega
        have hexp : L - 2 = b - a - 1 := by omega
        rw [hexp]
        exact cost_interior h a b hh ha1 hgap hb_mid

lemma exists_clear_window (h t : ℕ) (hh : 1 ≤ h) (P : Finset ℕ)
    (hP : P ⊆ Finset.range (h + 3)) (hcard : P.card + 1 ≤ 2 ^ t) :
    let C := (h + 3 + 2 ^ t - 1) / 2 ^ t
    ∃ a, a + C ≤ h + 3 ∧ ∀ w ∈ P, ¬ (a < w ∧ w ≤ a + C - 1) := by
  intro C
  let m := h + 3
  let R := 2 ^ t
  let cuts := (P.filter (fun j => 0 < j)).sort
  have hsort : cuts.SortedLT := Finset.sortedLT_sort _
  have hlen : cuts.length + 1 ≤ R := by
    rw [Finset.length_sort]
    exact (Nat.add_le_add_right (Finset.card_filter_le P (fun j => 0 < j)) 1).trans hcard
  have hcut_lt : ∀ j (hj : j < cuts.length), cuts[j] < m := by
    intro j hj
    have hmem : cuts[j] ∈ cuts := List.mem_iff_getElem.mpr ⟨j, hj, rfl⟩
    rw [Finset.mem_sort] at hmem
    exact Finset.mem_range.mp (hP (Finset.mem_filter.mp hmem).1)
  have hmono : Monotone (fence m cuts) := by
    refine monotone_nat_of_le_succ ?_
    intro i
    cases i with
    | zero =>
        simp only [fence]
        split <;> exact Nat.zero_le _
    | succ i =>
        simp only [fence]
        split_ifs with h1 h2
        · exact le_of_lt (hsort.getElem_lt_getElem_of_lt (by omega : i < i + 1))
        · exact le_of_lt (hcut_lt i h1)
        · omega
        · exact le_rfl
  have hsum : ∑ i ∈ Finset.range (cuts.length + 1),
      (fence m cuts (i + 1) - fence m cuts i) = m := by
    rw [Finset.sum_range_tsub hmono]
    have h0 : fence m cuts 0 = 0 := by simp [fence]
    have hN : fence m cuts (cuts.length + 1) = m := by
      simp only [fence, dite_eq_right (by simp : ¬ cuts.length < cuts.length)]
    rw [h0, hN, Nat.sub_zero]
  have hR : 0 < R := Nat.two_pow_pos _
  have hCpos : 1 ≤ C := by
    change 1 ≤ (m + R - 1) / R
    rw [Nat.le_div_iff_mul_le hR, Nat.one_mul]
    omega
  have hmul : (C - 1) * R ≤ m - 1 := by
    have hCRle : C * R ≤ m + R - 1 := by
      change ((m + R - 1) / R) * R ≤ m + R - 1
      exact Nat.div_mul_le_self _ _
    calc
      (C - 1) * R = C * R - R := by rw [Nat.sub_one_mul]
      _ ≤ (m + R - 1) - R := Nat.sub_le_sub_right hCRle _
      _ = m - 1 := by omega
  have hex : ∃ i ∈ Finset.range (cuts.length + 1), C ≤ fence m cuts (i + 1) - fence m cuts i := by
    by_contra hno
    push Not at hno
    have hsmall : ∀ i ∈ Finset.range (cuts.length + 1),
        fence m cuts (i + 1) - fence m cuts i ≤ C - 1 := by
      intro i hi
      have : fence m cuts (i + 1) - fence m cuts i < C := hno i hi
      omega
    have hle : m ≤ (cuts.length + 1) * (C - 1) := by
      calc
        m = ∑ i ∈ Finset.range (cuts.length + 1),
            (fence m cuts (i + 1) - fence m cuts i) := hsum.symm
        _ ≤ ∑ i ∈ Finset.range (cuts.length + 1), (C - 1) := Finset.sum_le_sum hsmall
        _ = (cuts.length + 1) * (C - 1) := by
          simp [Finset.sum_const, Finset.card_range]
    have : m ≤ m - 1 := by
      calc
        m ≤ (cuts.length + 1) * (C - 1) := hle
        _ ≤ R * (C - 1) := Nat.mul_le_mul_right _ hlen
        _ = (C - 1) * R := Nat.mul_comm _ _
        _ ≤ m - 1 := hmul
    omega
  obtain ⟨i, hi, hgap⟩ := hex
  refine ⟨fence m cuts i, ?_, ?_⟩
  · have hle : fence m cuts i ≤ fence m cuts (i + 1) := hmono (Nat.le_succ i)
    have hadd : fence m cuts i + C ≤ fence m cuts (i + 1) := by
      have hsumC : C + fence m cuts i ≤ fence m cuts (i + 1) :=
        (Nat.le_sub_iff_add_le hle).1 hgap
      rwa [Nat.add_comm] at hsumC
    have hend : fence m cuts (i + 1) ≤ m := by
      have hi' : i ≤ cuts.length := by
        have : i < cuts.length + 1 := Finset.mem_range.mp hi
        omega
      by_cases hlt : i < cuts.length
      · have heq : fence m cuts (i + 1) = cuts[i] := by
          simp [fence, dite_eq_left hlt]
        rw [heq]
        exact le_of_lt (hcut_lt i hlt)
      · have heqi : i = cuts.length := by omega
        have hm : fence m cuts (i + 1) = m := by
          simp [fence, heqi]
        simp [hm]
    exact hadd.trans hend
  · intro w hw hbad
    have hw0 : 0 < w := by omega
    have hmem : w ∈ cuts := by
      rw [Finset.mem_sort]
      exact Finset.mem_filter.mpr ⟨hw, hw0⟩
    obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp hmem
    have hwfen : fence m cuts (j + 1) = w := by
      simp [fence, dite_eq_left hj, hjw]
    have hle : fence m cuts i ≤ fence m cuts (i + 1) := hmono (Nat.le_succ i)
    have hadd : fence m cuts i + C ≤ fence m cuts (i + 1) := by
      have hsumC : C + fence m cuts i ≤ fence m cuts (i + 1) :=
        (Nat.le_sub_iff_add_le hle).1 hgap
      rwa [Nat.add_comm] at hsumC
    rcases Nat.lt_or_ge (j + 1) (i + 1) with hlt | hge
    · have : fence m cuts (j + 1) ≤ fence m cuts i := hmono (Nat.le_of_lt_succ hlt)
      rw [hwfen] at this
      omega
    · have : fence m cuts (i + 1) ≤ fence m cuts (j + 1) := hmono hge
      rw [hwfen] at this
      have : fence m cuts i + C ≤ w := hadd.trans this
      omega

lemma score_ge_pair (h : ℕ) (P : Finset ℕ) (u v : ℕ)
    (hu : u ∈ Finset.range (h + 3)) (hv : v ∈ Finset.range (h + 3))
    (huv : u ≤ v) (hclear : ∀ w ∈ P, ¬ (u < w ∧ w ≤ v)) :
    cost h (u, v) ≤ score h P := by
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, ⟨huv, hclear⟩⟩

lemma target_le_score (h t : ℕ) (hh : 1 ≤ h) (P : Finset ℕ)
    (hP : P ⊆ Finset.range (h + 3)) (hcard : P.card + 1 ≤ 2 ^ t) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ score h P := by
  let C := (h + 3 + 2 ^ t - 1) / 2 ^ t
  obtain ⟨a, ha, hclear⟩ := exists_clear_window h t hh P hP hcard
  have hC : 1 ≤ C := by
    have hR : 0 < 2 ^ t := Nat.two_pow_pos _
    change 1 ≤ (h + 3 + 2 ^ t - 1) / 2 ^ t
    rw [Nat.le_div_iff_mul_le hR, Nat.one_mul]
    omega
  have hexp : (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1 = C - 2 := by
    simp [C]
  have hcost := cost_ge h a C hh hC ha
  have hu : a ∈ Finset.range (h + 3) := Finset.mem_range.mpr (by omega)
  have hv : a + C - 1 ∈ Finset.range (h + 3) := Finset.mem_range.mpr (by omega)
  have huv : a ≤ a + C - 1 := by omega
  calc
    (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1)
        = (2 ^ h * 2 ^ h / 2) * (2 ^ (C - 2) - 1) := by rw [hexp]
    _ ≤ cost h (a, a + C - 1) := hcost
    _ ≤ score h P := score_ge_pair h P a (a + C - 1) hu hv huv hclear

lemma target_le_min (h t : ℕ) (hh : 1 ≤ h) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤
      WithTop.untopD 0
        (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image
          (score h)).min := by
  let feasible := (Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)
  let img := feasible.image (score h)
  have hempty : ∅ ∈ feasible := by
    refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩
    simpa using (Nat.one_le_two_pow : 1 ≤ 2 ^ t)
  have hne : img.Nonempty := ⟨score h ∅, Finset.mem_image_of_mem _ hempty⟩
  have hle : ∀ s ∈ img,
      (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ s := by
    intro s hs
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hP
    exact target_le_score h t hh P (Finset.mem_powerset.mp hsub) hcard
  have hmin : (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤
      img.min' hne := Finset.le_min' img hne _ hle
  rw [← Finset.coe_min' hne, WithTop.untopD_coe]
  exact hmin

end PEqualNP.Outside.L_meta_1349

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  have hmin := PEqualNP.Outside.L_meta_1349.target_le_min h t hh
  unfold PEqualNP.Outside.L_meta_1349.score PEqualNP.Outside.L_meta_1349.window
    PEqualNP.Outside.L_meta_1349.cost PEqualNP.Outside.L_meta_1349.miss
    PEqualNP.Outside.L_meta_1349.charge at hmin
  exact hmin
