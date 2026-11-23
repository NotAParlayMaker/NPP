import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

-- The value of a level, as in the posted statement.
def V (h i : ℕ) : ℕ :=
  if i = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if i = h + 2 then 0
  else 2 ^ h * (2 ^ h + 1) / 2 ^ (i - 1) - 2 ^ h

-- The weight of a level, as in the posted statement.
def W (h j : ℕ) : ℕ := if j = h + 2 then 2 ^ h else 2 ^ (j - 1) - 1

theorem V_zero (h : ℕ) : V h 0 = 2 ^ h * 2 ^ h + 2 ^ h + 1 := by
  unfold V
  rw [ite_eq_left rfl]

theorem V_top (h : ℕ) : V h (h + 2) = 0 := by
  unfold V
  rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem W_top (h : ℕ) : W h (h + 2) = 2 ^ h := by
  unfold W
  rw [ite_eq_left rfl]

theorem W_mid (h j : ℕ) (hj : j ≠ h + 2) : W h j = 2 ^ (j - 1) - 1 := by
  unfold W
  rw [ite_eq_right hj]

theorem pow_div_eq (h m : ℕ) (hm : m ≤ h) :
    2 ^ h * (2 ^ h + 1) / 2 ^ m = (2 ^ h + 1) * 2 ^ (h - m) := by
  have h1 : 2 ^ h * (2 ^ h + 1) = (2 ^ h + 1) * 2 ^ (h - m) * 2 ^ m := by
    calc 2 ^ h * (2 ^ h + 1) = 2 ^ (h - m) * 2 ^ m * (2 ^ h + 1) := by
          rw [← pow_add, Nat.sub_add_cancel hm]
      _ = (2 ^ h + 1) * 2 ^ (h - m) * 2 ^ m := by ring
  rw [h1, Nat.mul_div_cancel _ (by positivity)]

theorem V_mid (h i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ h + 1) :
    V h i = (2 ^ h + 1) * 2 ^ (h + 1 - i) - 2 ^ h := by
  unfold V
  rw [ite_eq_right (by omega), ite_eq_right (by omega), pow_div_eq h (i - 1) (by omega)]
  have h3 : h - (i - 1) = h + 1 - i := by omega
  rw [h3]

theorem two_le_pow (n : ℕ) (hn : 1 ≤ n) : 2 ≤ 2 ^ n := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

-- Pigeonhole: fewer than k cut points cannot meet every window of length g in 0 .. M.
theorem window (M g k : ℕ) (P : Finset ℕ) (hk : P.card < k) (hM : g * k ≤ M) :
    ∃ a, a + g ≤ M ∧ ∀ w ∈ P, ¬ (a < w ∧ w ≤ a + g) := by
  by_contra hcon
  push Not at hcon
  have hsub : Finset.range k ⊆ P.image (fun w => (w - 1) / g) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hle : i * g + g ≤ M := by
      have h1 : (i + 1) * g ≤ k * g := Nat.mul_le_mul (by omega) (le_refl _)
      have h2 : (i + 1) * g = i * g + g := by ring
      have h3 : k * g = g * k := by ring
      omega
    obtain ⟨w, hwP, hw1, hw2⟩ := hcon (i * g) hle
    rw [Finset.mem_image]
    refine ⟨w, hwP, ?_⟩
    apply Nat.div_eq_of_lt_le
    · omega
    · calc w - 1 < w := by omega
        _ ≤ i * g + g := hw2
        _ = (i + 1) * g := by ring
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := P) (f := fun w => (w - 1) / g)
  rw [Finset.card_range] at h1
  omega

-- The pair (a, a + G) pays at least the posted amount.
theorem value (h G a : ℕ) (hh : 1 ≤ h) (hG : 2 ≤ G) (ha : a + G ≤ h + 2) :
    2 ^ h * 2 ^ h / 2 * (2 ^ (G - 1) - 1) ≤ (V h a - V h (a + G)) * W h (a + G) := by
  have hE : 2 ^ h * 2 ^ h / 2 * 2 ≤ 2 ^ h * 2 ^ h := Nat.div_mul_le_self _ _
  have hX2 : 2 ≤ 2 ^ (G - 1) := two_le_pow _ (by omega)
  have hXG : 2 ^ G = 2 * 2 ^ (G - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  by_cases hv : a + G = h + 2
  · rw [hv, V_top, W_top, Nat.sub_zero]
    by_cases ha0 : a = 0
    · subst ha0
      have hGh : G = h + 2 := by omega
      subst hGh
      rw [V_zero]
      have hX : 2 ^ (h + 2 - 1) = 2 * 2 ^ h := by
        rw [show h + 2 - 1 = h + 1 by omega, pow_succ']
      rw [hX]
      generalize 2 ^ h = q at *
      calc q * q / 2 * (2 * q - 1) ≤ q * q / 2 * (2 * q) :=
            Nat.mul_le_mul (le_refl _) (Nat.sub_le _ _)
        _ = q * q / 2 * 2 * q := by ring
        _ ≤ q * q * q := Nat.mul_le_mul hE (le_refl _)
        _ ≤ (q * q + q + 1) * q := Nat.mul_le_mul (by omega) (le_refl _)
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      rw [V_mid h a ha1 (by omega)]
      have hexp : h + 1 - a = G - 1 := by omega
      rw [hexp]
      generalize 2 ^ (G - 1) = X at *
      generalize 2 ^ h = q at *
      obtain ⟨Y, rfl⟩ : ∃ Y, X = Y + 1 := ⟨X - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have h1 : (q + 1) * (Y + 1) - q = q * Y + Y + 1 := by
        have : (q + 1) * (Y + 1) = q * Y + Y + 1 + q := by ring
        omega
      rw [h1]
      calc q * q / 2 * Y ≤ q * q * Y := Nat.mul_le_mul (by omega) (le_refl _)
        _ ≤ (q * Y + Y + 1) * q := by
          have : (q * Y + Y + 1) * q = q * q * Y + (q * Y + q) := by ring
          rw [this]
          exact Nat.le_add_right _ _
  · have hv1 : a + G ≤ h + 1 := by omega
    rw [W_mid h (a + G) hv, V_mid h (a + G) (by omega) hv1]
    have hZY : 2 ^ (h + 1 - (a + G)) * 2 ^ (a + G - 1) = 2 ^ h := by
      rw [← pow_add]
      congr 1
      omega
    have hY2 : 2 ≤ 2 ^ (a + G - 1) := two_le_pow _ (by omega)
    have hZ1 : 1 ≤ 2 ^ (h + 1 - (a + G)) := Nat.one_le_two_pow
    by_cases ha0 : a = 0
    · subst ha0
      rw [V_zero]
      rw [Nat.zero_add] at hZY hY2 hZ1 ⊢
      refine Nat.mul_le_mul ?_ (le_refl _)
      generalize 2 ^ (G - 1) = X at *
      generalize 2 ^ (h + 1 - G) = Z at *
      generalize 2 ^ h = q at *
      have h2Z : 2 * Z ≤ q := by
        calc 2 * Z = Z * 2 := by ring
          _ ≤ Z * X := Nat.mul_le_mul (le_refl _) hY2
          _ = q := hZY
      have h2qZ : 2 * (q * Z) ≤ q * q := by
        calc 2 * (q * Z) = q * (2 * Z) := by ring
          _ ≤ q * q := Nat.mul_le_mul (le_refl _) h2Z
      rw [show (q + 1) * Z = q * Z + Z by ring]
      omega
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      rw [V_mid h a ha1 (by omega)]
      have hexp : 2 ^ (h + 1 - a) = 2 ^ (h + 1 - (a + G)) * 2 ^ G := by
        rw [← pow_add]
        congr 1
        omega
      rw [hexp, hXG]
      generalize 2 ^ (a + G - 1) = Yv at *
      generalize 2 ^ (h + 1 - (a + G)) = Z at *
      generalize 2 ^ (G - 1) = X at *
      generalize 2 ^ h = q at *
      obtain ⟨X', rfl⟩ : ∃ X', X = X' + 1 := ⟨X - 1, by omega⟩
      obtain ⟨Y', rfl⟩ : ∃ Y', Yv = Y' + 2 := ⟨Yv - 2, by omega⟩
      have hB : q ≤ (q + 1) * Z := by
        calc q ≤ q + 1 := Nat.le_succ q
          _ = (q + 1) * 1 := (mul_one _).symm
          _ ≤ (q + 1) * Z := Nat.mul_le_mul (le_refl _) hZ1
      have hT : (q + 1) * (Z * (2 * (X' + 1))) = (q + 1) * Z * (2 * X' + 1) + (q + 1) * Z := by
        ring
      have hD : (q + 1) * (Z * (2 * (X' + 1))) - q - ((q + 1) * Z - q)
          = (q + 1) * Z * (2 * X' + 1) := by
        omega
      rw [hD, Nat.add_sub_cancel, show Y' + 2 - 1 = Y' + 1 by omega]
      have key : (Y' + 2) * X' ≤ (2 * X' + 1) * (Y' + 1) := by
        have : (2 * X' + 1) * (Y' + 1) = (Y' + 2) * X' + (X' * Y' + Y' + 1) := by ring
        rw [this]
        exact Nat.le_add_right _ _
      calc q * q / 2 * X' ≤ q * q * X' := Nat.mul_le_mul (Nat.div_le_self _ _) (le_refl _)
        _ = q * Z * ((Y' + 2) * X') := by
          rw [← hZY]
          ring
        _ ≤ (q + 1) * Z * ((2 * X' + 1) * (Y' + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ q) (le_refl _)) key
        _ = (q + 1) * Z * (2 * X' + 1) * (Y' + 1) := by ring

theorem le_untopD_min (s : Finset ℕ) (a : ℕ) (hs : s.Nonempty) (h : ∀ x ∈ s, a ≤ x) :
    a ≤ WithTop.untopD 0 s.min := by
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hs
  rw [hm, WithTop.untopD_coe]
  exact h m (Finset.mem_of_min hm)

end PEqualNP.Outside.L_meta_1349

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  have ht : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hc : (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1 = (h + 2) / 2 ^ t - 1 := by
    have h1 : h + 3 + 2 ^ t - 1 = (h + 2) + 2 ^ t := by omega
    rw [h1, Nat.add_div_right _ (by positivity)]
    omega
  rw [hc]
  have hGm : (h + 2) / 2 ^ t * 2 ^ t ≤ h + 2 := Nat.div_mul_le_self _ _
  generalize (h + 2) / 2 ^ t = G at hGm ⊢
  apply PEqualNP.Outside.L_meta_1349.le_untopD_min
  · have h0 : (∅ : Finset ℕ) ∈ (Finset.range (h + 3)).powerset.filter
        (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t) := by
      rw [Finset.mem_filter, Finset.card_empty]
      exact ⟨Finset.empty_mem_powerset _, by omega⟩
    exact ⟨_, Finset.mem_image_of_mem _ h0⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    rw [Finset.mem_filter] at hP
    obtain ⟨_, hPcard⟩ := hP
    by_cases hG2 : G < 2
    · have h1 : G - 1 = 0 := by omega
      rw [h1]
      simp
    · have hG2' : 2 ≤ G := by omega
      obtain ⟨a, ha, hwin⟩ :=
        PEqualNP.Outside.L_meta_1349.window (h + 2) G (2 ^ t) P (by omega) hGm
      have hval := PEqualNP.Outside.L_meta_1349.value h G a hh hG2' ha
      have hmem : (a, a + G) ∈ (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
          (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)) := by
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, by omega, hwin⟩
      exact le_trans hval (Finset.le_sup (f := fun uv : ℕ × ℕ =>
        (PEqualNP.Outside.L_meta_1349.V h uv.1 - PEqualNP.Outside.L_meta_1349.V h uv.2) *
          PEqualNP.Outside.L_meta_1349.W h uv.2) hmem)
