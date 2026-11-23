import Mathlib
import PEqualNP.Defs

namespace PEqualNP.MetaComplexity.L1349Aux

def lev (h i : ℕ) : ℕ :=
  if i = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if i = h + 2 then 0 else
    2 ^ h * (2 ^ h + 1) / 2 ^ (i - 1) - 2 ^ h

def wid (h v : ℕ) : ℕ := if v = h + 2 then 2 ^ h else 2 ^ (v - 1) - 1

theorem lev_zero (h : ℕ) : lev h 0 = 2 ^ h * 2 ^ h + 2 ^ h + 1 := by simp [lev]

theorem lev_top (h : ℕ) : lev h (h + 2) = 0 := by simp [lev]

theorem lev_mid (h i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ h + 1) :
    lev h i = 2 ^ (h + 1 - i) * (2 ^ h + 1) - 2 ^ h := by
  have hi0 : i ≠ 0 := by omega
  have hi2 : i ≠ h + 2 := by omega
  have key : 2 ^ h * (2 ^ h + 1) = 2 ^ (i - 1) * (2 ^ (h + 1 - i) * (2 ^ h + 1)) := by
    rw [← Nat.mul_assoc, ← pow_add, show i - 1 + (h + 1 - i) = h by omega]
  simp only [lev, hi0, hi2, if_false]
  rw [key, Nat.mul_div_cancel_left _ (by positivity)]

theorem wid_top (h : ℕ) : wid h (h + 2) = 2 ^ h := by simp [wid]

theorem wid_mid (h v : ℕ) (hv : v ≠ h + 2) : wid h v = 2 ^ (v - 1) - 1 := by simp [wid, hv]

theorem alg1 (q : ℕ) : (q * q / 2) * (q * 2 - 1) ≤ (q * q + q + 1 - 0) * q := by
  have h1 : (q * q / 2) * (q * 2 - 1) ≤ (q * q / 2) * (q * 2) :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : (q * q / 2) * 2 ≤ q * q := Nat.div_mul_le_self _ _
  have h3 : (q * q / 2) * (q * 2) = ((q * q / 2) * 2) * q := by ring
  have h4 : ((q * q / 2) * 2) * q ≤ (q * q) * q := Nat.mul_le_mul_right _ h2
  have h5 : (q * q) * q ≤ (q * q + q + 1 - 0) * q := Nat.mul_le_mul_right _ (by omega)
  calc (q * q / 2) * (q * 2 - 1) ≤ (q * q / 2) * (q * 2) := h1
    _ = ((q * q / 2) * 2) * q := h3
    _ ≤ (q * q) * q := h4
    _ ≤ (q * q + q + 1 - 0) * q := h5

theorem alg2 (q E B : ℕ) (hEB : E * B = q) (hB : 2 ≤ B) :
    (q * q / 2) * (B - 1) ≤ (q * q + q + 1 - (E * (q + 1) - q)) * (B - 1) := by
  apply Nat.mul_le_mul_right
  have h0 : E * 2 ≤ E * B := Nat.mul_le_mul_left E hB
  have h1 : 2 * E ≤ q := by rw [← hEB]; linarith
  have h2 : 2 * E * (q + 1) ≤ q * (q + 1) := Nat.mul_le_mul_right _ h1
  have h3 : 2 * (E * (q + 1)) ≤ q * q + q := by nlinarith
  omega

theorem alg3 (q M : ℕ) (hM : 1 ≤ M) : (q * q / 2) * (M - 1) ≤ (M * (q + 1) - q - 0) * q := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have e0 : (m + 1) * (q + 1) = m * q + m + q + 1 := by ring
  have e : (m + 1) * (q + 1) - q - 0 = m * q + m + 1 := by omega
  rw [e, show m + 1 - 1 = m by omega]
  have hd : q * q / 2 ≤ q * q := Nat.div_le_self _ _
  have e2 : q * q * m + (m * q + q) = (m * q + m + 1) * q := by ring
  calc q * q / 2 * m ≤ q * q * m := Nat.mul_le_mul_right _ hd
    _ ≤ (m * q + m + 1) * q := Nat.le.intro e2

theorem alg4 (q E B M : ℕ) (hEB : E * B = q) (hB : 2 ≤ B) (hE : 1 ≤ E) (hM : 1 ≤ M) :
    (q * q / 2) * (M - 1) ≤ (2 * E * M * (q + 1) - q - (E * (q + 1) - q)) * (B - 1) := by
  subst hEB
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, B = c + 2 := ⟨B - 2, by omega⟩
  have hEE : E * (c + 2) ≤ E * (E * (c + 2)) := Nat.le_mul_of_pos_left _ (by omega)
  have eX : E * (E * (c + 2) + 1) = E * (E * (c + 2)) + E := by ring
  have e1 : 2 * E * (m + 1) * (E * (c + 2) + 1) =
      (2 * m + 1) * (E * (E * (c + 2) + 1)) + E * (E * (c + 2) + 1) := by ring
  have e2 : 2 * E * (m + 1) * (E * (c + 2) + 1) - E * (c + 2) -
      (E * (E * (c + 2) + 1) - E * (c + 2)) = (2 * m + 1) * (E * (E * (c + 2) + 1)) := by
    omega
  rw [e2, show m + 1 - 1 = m by omega, show c + 2 - 1 = c + 1 by omega]
  have hd : E * (c + 2) * (E * (c + 2)) / 2 ≤ E * (c + 2) * (E * (c + 2)) := Nat.div_le_self _ _
  have e3 : E * (c + 2) * (E * (c + 2)) * m + (E * E * (c + 2) * (m * c + c + 1) +
      (2 * m + 1) * E * (c + 1)) = (2 * m + 1) * (E * (E * (c + 2) + 1)) * (c + 1) := by ring
  calc E * (c + 2) * (E * (c + 2)) / 2 * m ≤ E * (c + 2) * (E * (c + 2)) * m :=
        Nat.mul_le_mul_right _ hd
    _ ≤ (2 * m + 1) * (E * (E * (c + 2) + 1)) * (c + 1) := Nat.le.intro e3

theorem lemA (h a L : ℕ) (hh : 1 ≤ h) (hL : 2 ≤ L) (hb : a + L ≤ h + 2) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (L - 1) - 1) ≤ (lev h a - lev h (a + L)) * wid h (a + L) := by
  have hM : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
  rcases Nat.lt_or_ge (a + L) (h + 2) with hlt | hge
  · have hv : a + L ≠ h + 2 := by omega
    have hEB : 2 ^ (h + 1 - (a + L)) * 2 ^ (a + L - 1) = 2 ^ h := by
      rw [← pow_add, show h + 1 - (a + L) + (a + L - 1) = h by omega]
    have hB : 2 ≤ 2 ^ (a + L - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a + L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [wid_mid h (a + L) hv, lev_mid h (a + L) (by omega) (by omega)]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [Nat.zero_add] at hEB hB ⊢
      rw [lev_zero]
      exact alg2 (2 ^ h) _ _ hEB hB
    · have hpow : 2 ^ (h + 1 - a) = 2 * 2 ^ (h + 1 - (a + L)) * 2 ^ (L - 1) := by
        rw [show h + 1 - a = (h + 1 - (a + L)) + (L - 1) + 1 by omega, pow_succ, pow_add]
        ring
      rw [lev_mid h a ha (by omega), hpow]
      exact alg4 (2 ^ h) _ _ _ hEB hB Nat.one_le_two_pow hM
  · rw [show a + L = h + 2 by omega, lev_top, wid_top]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [lev_zero, show L - 1 = h + 1 by omega, pow_succ]
      exact alg1 (2 ^ h)
    · rw [lev_mid h a ha (by omega), show h + 1 - a = L - 1 by omega]
      exact alg3 (2 ^ h) _ hM

theorem window (h t L : ℕ) (P : Finset ℕ) (hP : P.card + 1 ≤ 2 ^ t) (hL : 1 ≤ L)
    (hLT : L * 2 ^ t ≤ h + 2) : ∃ a, a + L ≤ h + 2 ∧ ∀ w ∈ P, ¬ (a < w ∧ w ≤ a + L) := by
  have hcard : (P.image (fun w => (w - 1) / L)).card < (Finset.range (2 ^ t)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Finset.card_image_le (by omega)
  obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hjT : j + 1 ≤ 2 ^ t := Finset.mem_range.mp hj
  refine ⟨j * L, ?_, ?_⟩
  · have h1 : (j + 1) * L ≤ 2 ^ t * L := Nat.mul_le_mul_right _ hjT
    have h2 : (j + 1) * L = j * L + L := by ring
    have h3 : 2 ^ t * L = L * 2 ^ t := by ring
    omega
  · rintro w hw ⟨h1, h2⟩
    apply hjn
    refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
    have h3 : (j + 1) * L = j * L + L := by ring
    apply Nat.div_eq_of_lt_le
    · omega
    · omega

theorem le_untopD_min (s : Finset ℕ) (b : ℕ) (hs : s.Nonempty) (hb : ∀ y ∈ s, b ≤ y) :
    b ≤ WithTop.untopD 0 s.min := by
  rw [← Finset.coe_min' hs, WithTop.untopD_coe]
  exact hb _ (Finset.min'_mem s hs)

end PEqualNP.MetaComplexity.L1349Aux

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  have hT : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  by_cases hL : (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 ≤ 1
  · have h0 : (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1 = 0 := by omega
    rw [h0]
    simp
  · push_neg at hL
    set L := (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 with hLdef
    have hLT : L * 2 ^ t ≤ h + 2 := by
      have hd := Nat.div_mul_le_self (h + 3 + 2 ^ t - 1) (2 ^ t)
      rw [hLdef, Nat.sub_one_mul]
      omega
    apply PEqualNP.MetaComplexity.L1349Aux.le_untopD_min
    · exact ⟨_, Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simpa using hT⟩)⟩
    · intro y hy
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨_, hPcard⟩ := Finset.mem_filter.mp hP
      obtain ⟨a, haL, hcut⟩ :=
        PEqualNP.MetaComplexity.L1349Aux.window h t L P hPcard (by omega) hLT
      have hmem : (a, a + L) ∈ (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
          (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩, by omega, hcut⟩
      refine le_trans ?_ (Finset.le_sup hmem)
      exact PEqualNP.MetaComplexity.L1349Aux.lemA h a L hh (by omega) haL
