import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

-- The value of level x in the ladder game for q = 2 ^ h.
def lv (h x : ℕ) : ℕ :=
  if x = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if x = h + 2 then 0
  else 2 ^ h * (2 ^ h + 1) / 2 ^ (x - 1) - 2 ^ h

-- The multiplier of level v in the ladder game.
def mv (h v : ℕ) : ℕ := if v = h + 2 then 2 ^ h else 2 ^ (v - 1) - 1

theorem lv_mid (h x : ℕ) (h1 : 1 ≤ x) (h2 : x ≤ h + 1) :
    lv h x + 2 ^ h = 2 ^ (h + 1 - x) * (2 ^ h + 1) := by
  unfold lv
  have h0 : x ≠ 0 := by omega
  have h3 : x ≠ h + 2 := by omega
  simp only [h0, h3, ↓reduceIte]
  have e : 2 ^ h * (2 ^ h + 1) / 2 ^ (x - 1) = 2 ^ (h + 1 - x) * (2 ^ h + 1) := by
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    rw [mul_right_comm, ← pow_add, show h + 1 - x + (x - 1) = h by omega]
  rw [e]
  have : 2 ^ h ≤ 2 ^ (h + 1 - x) * (2 ^ h + 1) := by
    calc 2 ^ h ≤ 1 * (2 ^ h + 1) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ Nat.one_le_two_pow
  omega

theorem lv_top (h : ℕ) : lv h (h + 2) = 0 := by
  unfold lv
  simp

theorem mv_top (h : ℕ) : mv h (h + 2) = 2 ^ h := by
  unfold mv
  simp

theorem mv_mid (h v : ℕ) (hv : v ≤ h + 1) : mv h v = 2 ^ (v - 1) - 1 := by
  unfold mv
  have h3 : v ≠ h + 2 := by omega
  simp only [h3, ↓reduceIte]

theorem div_helper (A Y Z : ℕ) (H : A * Y ≤ 2 * Z) : A / 2 * Y ≤ Z := by
  have h1 : A / 2 * 2 ≤ A := Nat.div_mul_le_self A 2
  have h2 : A / 2 * 2 * Y ≤ A * Y := Nat.mul_le_mul_right Y h1
  nlinarith

theorem le_untopD_min (s : Finset ℕ) (c : ℕ) (hs : s.Nonempty) (H : ∀ x ∈ s, c ≤ x) :
    c ≤ WithTop.untopD 0 s.min := by
  rw [← Finset.coe_min' hs, WithTop.untopD_coe]
  exact Finset.le_min' s hs c H

-- Pigeonhole: fewer than 2 ^ t cuts miss one of the 2 ^ t windows of width g.
theorem window (P : Finset ℕ) (t g : ℕ) (_hg : 1 ≤ g) (hP : P.card + 1 ≤ 2 ^ t) :
    ∃ k < 2 ^ t, ∀ w ∈ P, ¬ (k * g < w ∧ w ≤ k * g + g) := by
  by_contra H
  simp only [not_exists, not_and, not_forall, not_not] at H
  have hsub : Finset.range (2 ^ t) ⊆ P.image (fun w => (w - 1) / g) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨w, hw, h1, h2⟩ := H k hk
    rw [Finset.mem_image]
    refine ⟨w, hw, ?_⟩
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [add_mul, one_mul]
      omega
  have c1 := Finset.card_le_card hsub
  rw [Finset.card_range] at c1
  have c2 := Finset.card_image_le (s := P) (f := fun w => (w - 1) / g)
  omega

-- A cut-free window of width g starting at a holds a pair of large cost.
theorem cost (h g a : ℕ) (hh : 1 ≤ h) (hg : 2 ≤ g) (hb : a + g ≤ h + 2) :
    ∃ u v, a ≤ u ∧ u ≤ v ∧ v ≤ a + g ∧
      2 ^ h * 2 ^ h / 2 * (2 ^ (g - 1) - 1) ≤ (lv h u - lv h v) * mv h v := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    refine ⟨1, g, by omega, by omega, by omega, ?_⟩
    apply div_helper
    have hL1 := lv_mid h 1 le_rfl (by omega)
    rw [show h + 1 - 1 = h by omega] at hL1
    rcases Nat.lt_or_ge g (h + 2) with hgl | hgl
    · have hLg := lv_mid h g (by omega) (by omega)
      rw [mv_mid h g (by omega)]
      have hq : 2 ^ h = 2 ^ (h + 1 - g) * 2 ^ (g - 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hG : 2 ≤ 2 ^ (g - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (g - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      generalize lv h 1 = L1 at hL1 ⊢
      generalize lv h g = Lg at hLg ⊢
      generalize 2 ^ (h + 1 - g) = p at hLg hq
      generalize 2 ^ (g - 1) = G at hq hG ⊢
      generalize 2 ^ h = q at hL1 hLg hq ⊢
      have f1 : 2 * (p * q) ≤ q * q := by
        calc 2 * (p * q) = p * q * 2 := by ring
          _ ≤ p * q * G := Nat.mul_le_mul_left _ hG
          _ = q * q := by rw [hq]; ring
      have f2 : p ≤ q := by
        rw [hq]
        exact Nat.le_mul_of_pos_right p (by omega)
      have e1 : L1 = q * q := by
        have : q * (q + 1) = q * q + q := by ring
        omega
      have e2 : Lg + q = p * q + p := by
        rw [hLg]
        ring
      have f3 : q * q ≤ 2 * (L1 - Lg) := by omega
      calc q * q * (G - 1) ≤ 2 * (L1 - Lg) * (G - 1) := Nat.mul_le_mul_right _ f3
        _ = 2 * ((L1 - Lg) * (G - 1)) := by ring
    · obtain rfl : g = h + 2 := by omega
      rw [lv_top, mv_top, show h + 2 - 1 = h + 1 by omega, pow_succ]
      generalize lv h 1 = L1 at hL1 ⊢
      generalize 2 ^ h = q at hL1 ⊢
      have e1 : L1 = q * q := by
        have : q * (q + 1) = q * q + q := by ring
        omega
      rw [e1, Nat.sub_zero]
      calc q * q * (q * 2 - 1) ≤ q * q * (q * 2) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = 2 * (q * q * q) := by ring
  · refine ⟨a, a + g, le_rfl, by omega, le_rfl, ?_⟩
    apply div_helper
    have hLa := lv_mid h a ha (by omega)
    rcases Nat.lt_or_ge (a + g) (h + 2) with hgl | hgl
    · have hLb := lv_mid h (a + g) (by omega) (by omega)
      rw [mv_mid h (a + g) (by omega)]
      have hr : 2 ^ (h + 1 - a) = 2 ^ (h + 1 - (a + g)) * (2 * 2 ^ (g - 1)) := by
        rw [show h + 1 - a = (h + 1 - (a + g)) + (g - 1) + 1 by omega, pow_succ, pow_add]
        ring
      have hq : 2 ^ h = 2 ^ (h + 1 - (a + g)) * 2 ^ (a + g - 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hs : 2 ≤ 2 ^ (a + g - 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (a + g - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hG : 1 ≤ 2 ^ (g - 1) := Nat.one_le_two_pow
      rw [hr] at hLa
      generalize lv h a = La at hLa ⊢
      generalize lv h (a + g) = Lb at hLb ⊢
      generalize 2 ^ (h + 1 - (a + g)) = p at hLa hLb hq
      generalize 2 ^ (a + g - 1) = s at hq hs ⊢
      generalize 2 ^ (g - 1) = G at hLa hG ⊢
      generalize 2 ^ h = q at hLa hLb hq ⊢
      have key1 : p * G * q ≤ La - Lb := by
        have eA : p * (2 * G) * (q + 1) = 2 * (p * G * q) + 2 * (p * G) := by ring
        have eB : p * (q + 1) = p * q + p := by ring
        have i1 : p * q ≤ p * G * q := by
          calc p * q = p * q * 1 := (mul_one _).symm
            _ ≤ p * q * G := Nat.mul_le_mul_left _ hG
            _ = p * G * q := by ring
        have i2 : p ≤ p * G := Nat.le_mul_of_pos_right p hG
        omega
      calc q * q * (G - 1) ≤ q * q * G := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = p * G * q * s := by rw [hq]; ring
        _ ≤ p * G * q * (2 * (s - 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (p * G * q * (s - 1)) := by ring
        _ ≤ 2 * ((La - Lb) * (s - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ key1)
    · obtain hag : a + g = h + 2 := by omega
      rw [hag, lv_top, mv_top, Nat.sub_zero]
      rw [show h + 1 - a = g - 1 by omega] at hLa
      generalize lv h a = La at hLa ⊢
      generalize 2 ^ (g - 1) = G at hLa ⊢
      generalize 2 ^ h = q at hLa ⊢
      have f : q * (G - 1) ≤ La := by
        rw [Nat.mul_sub_one]
        have : G * (q + 1) = q * G + G := by ring
        omega
      calc q * q * (G - 1) = q * (G - 1) * q := by ring
        _ ≤ La * q := Nat.mul_le_mul_right _ f
        _ ≤ 2 * (La * q) := by omega

end PEqualNP.Outside.L_meta_1349

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  rcases Nat.lt_or_ge ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1) 2 with hg | hg
  · rw [show (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1 = 0 by omega]
    simp
  generalize hgd : (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 = g at hg ⊢
  have hgt : 2 ^ t * g ≤ h + 2 := by
    have h1 := Nat.div_mul_le_self (h + 3 + 2 ^ t - 1) (2 ^ t)
    have h2 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    rw [← hgd, Nat.mul_comm, Nat.sub_mul, one_mul]
    omega
  apply PEqualNP.Outside.L_meta_1349.le_untopD_min
  · apply Finset.Nonempty.image
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.card_empty, zero_add]
    exact ⟨Finset.empty_subset _, Nat.one_le_two_pow⟩
  · intro x hx
    obtain ⟨P, hPmem, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter, Finset.mem_powerset] at hPmem
    obtain ⟨k, hk, hwin⟩ := PEqualNP.Outside.L_meta_1349.window P t g (by omega) hPmem.2
    have hkg : k * g + g ≤ h + 2 := by
      have : (k + 1) * g ≤ 2 ^ t * g := Nat.mul_le_mul_right _ hk
      rw [add_mul, one_mul] at this
      omega
    obtain ⟨u, v, hau, huv, hvb, hc⟩ := PEqualNP.Outside.L_meta_1349.cost h g (k * g) hh hg hkg
    have hmem : (u, v) ∈ (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
        (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)) := by
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      refine ⟨⟨by omega, by omega⟩, huv, fun w hw hw2 => hwin w hw ⟨by omega, by omega⟩⟩
    exact le_trans hc (Finset.le_sup (f := fun uv : ℕ × ℕ => (PEqualNP.Outside.L_meta_1349.lv h uv.1 - PEqualNP.Outside.L_meta_1349.lv h uv.2) * PEqualNP.Outside.L_meta_1349.mv h uv.2) hmem)
