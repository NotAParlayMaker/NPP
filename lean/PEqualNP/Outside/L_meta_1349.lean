import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

lemma exists_long_interval_of_mul_lt (N R g : ℕ) (P : Finset ℕ)
    (hcount : P.card + 1 ≤ R) (hmul : R * g < N) :
    ∃ a b : ℕ, a < N ∧ b < N ∧ a ≤ b ∧
      (∀ w ∈ P, ¬ (a < w ∧ w ≤ b)) ∧ g ≤ b - a := by
  classical
  let f : ℕ → ℕ := fun i => (P.filter fun w => w ≤ i).card
  have hmap : ∀ i ∈ Finset.range N, f i ∈ Finset.range R := by
    intro i _
    apply Finset.mem_range.mpr
    have hle := Finset.card_filter_le P (fun w => w ≤ i)
    dsimp [f]
    omega
  obtain ⟨y, _, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.range N) (t := Finset.range R) (f := f) (n := g) hmap
    (by simpa using hmul)
  let A := (Finset.range N).filter fun i => f i = y
  have hAcard : g < A.card := hy
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  let a := A.min' hA
  let b := A.max' hA
  have hamem : a ∈ A := Finset.min'_mem A hA
  have hbmem : b ∈ A := Finset.max'_mem A hA
  have haN : a < N := Finset.mem_range.mp (Finset.mem_filter.mp hamem).1
  have hbN : b < N := Finset.mem_range.mp (Finset.mem_filter.mp hbmem).1
  have hab : a ≤ b := Finset.min'_le_max' A hA
  have haf : f a = y := (Finset.mem_filter.mp hamem).2
  have hbf : f b = y := (Finset.mem_filter.mp hbmem).2
  have hfilters : P.filter (fun w => w ≤ a) = P.filter (fun w => w ≤ b) := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨hwP, hwa⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hwP, hwa.trans hab⟩
    · change f b ≤ f a
      rw [haf, hbf]
  have huncut : ∀ w ∈ P, ¬ (a < w ∧ w ≤ b) := by
    intro w hwP ⟨haw, hwb⟩
    have hw : w ∈ P.filter (fun u => u ≤ b) := Finset.mem_filter.mpr ⟨hwP, hwb⟩
    rw [← hfilters] at hw
    have hwa := (Finset.mem_filter.mp hw).2
    omega
  have hsub : A ⊆ Finset.Icc a b := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le A i hi, Finset.le_max' A i hi⟩
  have hbound := Finset.card_le_card hsub
  have hsize : A.card ≤ b + 1 - a := by simpa using hbound
  exact ⟨a, b, haN, hbN, hab, huncut, by omega⟩

lemma exists_long_interval (N R : ℕ) (P : Finset ℕ) (hN : 0 < N) (hR : 0 < R)
    (_hP : P ⊆ Finset.range N) (hcount : P.card + 1 ≤ R) :
    ∃ a b : ℕ, a < N ∧ b < N ∧ a ≤ b ∧
      (∀ w ∈ P, ¬ (a < w ∧ w ≤ b)) ∧ (N + R - 1) / R - 1 ≤ b - a := by
  have hdiv : (N + R - 1) / R - 1 = (N - 1) / R := by
    have hrewrite : N + R - 1 = (N - 1) + R := by omega
    rw [hrewrite, Nat.add_div_right _ hR]
    simp
  rw [hdiv]
  apply exists_long_interval_of_mul_lt N R ((N - 1) / R) P hcount
  have hmul := Nat.mul_div_le (N - 1) R
  omega

def level (h i : ℕ) : ℕ :=
  if i = 0 then 2^h*2^h+2^h+1 else if i = h+2 then 0
  else 2^h*(2^h+1)/2^(i-1)-2^h

def intervalCost (h a b : ℕ) : ℕ :=
  (level h a-level h b)*(if b=h+2 then 2^h else 2^(b-1)-1)

lemma pow_factor {h i : ℕ} (hi : i ≤ h) :
    2^h = 2^(h-i)*2^i := by
  rw [← pow_add]
  congr 1
  omega

lemma quotient (h i : ℕ) (hi : i ≤ h) :
    2^h*(2^h+1)/2^i = 2^(h-i)*(2^h+1) := by
  have he : 2^h*(2^h+1) = (2^(h-i)*(2^h+1))*2^i := by
    calc
      _ = (2^(h-i)*2^i)*(2^h+1) := by rw [← pow_factor hi]
      _ = _ := by ring
  rw [he, Nat.mul_div_cancel]
  exact pow_pos (by decide) _

lemma level_inner (h i : ℕ) (hi : 1 ≤ i) (hil : i ≤ h+1) :
    level h i = 2^(h-(i-1))*(2^h+1)-2^h := by
  simp only [level, ite_eq_right (by omega : i ≠ 0), ite_eq_right (by omega : i ≠ h+2)]
  rw [quotient h (i-1) (by omega)]

lemma level_inner_add (h i : ℕ) (hi : 1 ≤ i) (hil : i ≤ h+1) :
    level h i + 2^h = 2^(h-(i-1))*(2^h+1) := by
  rw [level_inner h i hi hil]
  have hp : 1 ≤ 2^(h-(i-1)) := Nat.one_le_pow _ _ (by decide)
  have hl : 2^h ≤ 2^(h-(i-1))*(2^h+1) := by
    have := Nat.mul_le_mul_right (2^h+1) hp
    omega
  omega

lemma interval_small (h a b : ℕ) (hd : b-a ≤ 1) :
    (2^h*2^h/2)*(2^(b-a-1)-1) ≤ intervalCost h a b := by
  have he : b-a-1 = 0 := by omega
  simp [he]

lemma interval_inner (h a b : ℕ) (ha : 1 ≤ a) (hab : a+2 ≤ b)
    (hb : b ≤ h+1) :
    (2^h*2^h/2)*(2^(b-a-1)-1) ≤ intervalCost h a b := by
  let q := 2^h
  let p := 2^(h-(b-1))
  let B := 2^(b-1)
  let r := 2^(b-a)
  let u := 2^(b-a-1)
  have hp : 1 ≤ p := Nat.one_le_pow _ _ (by decide)
  have hu : 1 ≤ u := Nat.one_le_pow _ _ (by decide)
  have hr : r = 2*u := by
    dsimp [r,u]
    calc
      2^(b-a) = 2^((b-a-1)+1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; omega
  have hBr : r ≤ B := by
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hr1 : 1 ≤ r := by omega
  have hB1 : 1 ≤ B := by omega
  have hq : q = p*B := pow_factor (by omega)
  have hpa : 2^(h-(a-1)) = p*r := by
    dsimp [p,r]
    rw [← pow_add]
    congr 1
    omega
  have hla := level_inner_add h a ha (by omega)
  have hlb := level_inner_add h b (by omega) hb
  change level h a + q = _ at hla
  rw [hpa] at hla
  change level h a + q = p*r*(q+1) at hla
  change level h b + q = p*(q+1) at hlb
  have hsplit : p*r*(q+1) = p*(r-1)*(q+1)+p*(q+1) := by
    calc
      _ = p*((r-1)+1)*(q+1) := by rw [Nat.sub_add_cancel hr1]
      _ = _ := by ring
  have hdif : level h a-level h b = p*(r-1)*(q+1) := by omega
  have hn : B*(u-1) ≤ (r-1)*(B-1) := by
    have hsB := Nat.sub_add_cancel hB1
    have hsr := Nat.sub_add_cancel hr1
    have hsu := Nat.sub_add_cancel hu
    nlinarith
  have hmain : q*q*(u-1) ≤ p*(r-1)*(q+1)*(B-1) := by
    calc
      q*q*(u-1) = p*q*(B*(u-1)) := by rw [hq]; ring
      _ ≤ p*q*((r-1)*(B-1)) := Nat.mul_le_mul_left _ hn
      _ ≤ p*(r-1)*(q+1)*(B-1) := by nlinarith [Nat.zero_le (p*(r-1)*(B-1))]
  have hhalf : q*q/2 ≤ q*q := Nat.div_le_self _ _
  unfold intervalCost
  rw [hdif, ite_eq_right (by omega : b ≠ h+2)]
  exact (Nat.mul_le_mul_right (u-1) hhalf).trans hmain

lemma interval_from_zero (h b : ℕ) (hb2 : 2 ≤ b) (hb : b ≤ h+1) :
    (2^h*2^h/2)*(2^(b-0-1)-1) ≤ intervalCost h 0 b := by
  let q := 2^h
  let p := 2^(h-(b-1))
  let B := 2^(b-1)
  have hB : 2 ≤ B := by
    change 2^1 ≤ 2^(b-1)
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hq : q = p*B := pow_factor (by omega)
  have hp : 2*p ≤ q := by nlinarith
  have hlb := level_inner_add h b (by omega) hb
  change level h b + q = p*(q+1) at hlb
  have hbmul := Nat.mul_le_mul_right (q+1) hp
  have hsmall : 2*level h b ≤ q*q := by nlinarith
  have hhalf : (q*q/2)*2 ≤ q*q := Nat.div_mul_le_self _ _
  have hboth : q*q/2 + level h b ≤ q*q+q+1 := by omega
  have hl0 : level h 0 = q*q+q+1 := by simp [level,q]
  have hdiff : q*q/2 ≤ level h 0-level h b := by rw [hl0]; omega
  unfold intervalCost
  rw [ite_eq_right (by omega : b ≠ h+2)]
  exact Nat.mul_le_mul_right (2^(b-1)-1) hdiff

lemma interval_to_end_zero (h : ℕ) :
    (2^h*2^h/2)*(2^((h+2)-0-1)-1) ≤ intervalCost h 0 (h+2) := by
  let q := 2^h
  let H := q*q/2
  have hp : 2^((h+2)-0-1) = 2*q := by
    have he : h+2-0-1 = h+1 := by omega
    rw [he,pow_succ]
    dsimp [q]
    ring
  have hhalf : H*2 ≤ q*q := Nat.div_mul_le_self _ _
  have hl0 : level h 0 = q*q+q+1 := by simp [level,q]
  have hlend : level h (h+2) = 0 := by simp [level]
  change H*(2^((h+2)-0-1)-1) ≤ _
  rw [hp]
  unfold intervalCost
  rw [hl0,hlend]
  simp only [Nat.sub_zero]
  change H*(2*q-1) ≤ (q*q+q+1)*q
  calc
    _ ≤ H*(2*q) := Nat.mul_le_mul_left H (Nat.sub_le _ _)
    _ = (H*2)*q := by ring
    _ ≤ (q*q)*q := Nat.mul_le_mul_right q hhalf
    _ ≤ _ := Nat.mul_le_mul_right q (by omega)

lemma interval_to_end (h a : ℕ) (ha : 1 ≤ a) (hah : a ≤ h+1) :
    (2^h*2^h/2)*(2^((h+2)-a-1)-1) ≤ intervalCost h a (h+2) := by
  let q := 2^h
  let u := 2^(h-(a-1))
  have hu : 1 ≤ u := Nat.one_le_pow _ _ (by decide)
  have he : h+2-a-1 = h-(a-1) := by omega
  have hla := level_inner_add h a ha hah
  change level h a+q = u*(q+1) at hla
  have hs := Nat.sub_add_cancel hu
  have hlevel : level h a = q*(u-1)+u := by nlinarith
  have hlend : level h (h+2) = 0 := by simp [level]
  have hhalf : q*q/2 ≤ q*q := Nat.div_le_self _ _
  unfold intervalCost
  rw [hlend,hlevel]
  simp only [Nat.sub_zero]
  rw [he]
  change (q*q/2)*(u-1) ≤ (q*(u-1)+u)*q
  calc
    _ ≤ (q*q)*(u-1) := Nat.mul_le_mul_right (u-1) hhalf
    _ ≤ _ := by nlinarith [Nat.zero_le (u*q)]

lemma interval_lower (h a b : ℕ) (hh : 1 ≤ h) (hab : a ≤ b) (hb : b ≤ h+2) :
    (2^h*2^h/2)*(2^(b-a-1)-1) ≤ intervalCost h a b := by
  by_cases hd : b-a ≤ 1
  · exact interval_small h a b hd
  by_cases hbe : b = h+2
  · subst b
    by_cases ha0 : a = 0
    · subst a
      exact interval_to_end_zero h
    · exact interval_to_end h a (by omega) (by omega)
  · by_cases ha0 : a = 0
    · subst a
      exact interval_from_zero h b (by omega) (by omega)
    · exact interval_inner h a b (by omega) (by omega) (by omega)

open Classical in
lemma game_lower (N R B : ℕ) (cost : ℕ × ℕ → ℕ) (hR : 1 ≤ R)
    (hcost : ∀ P : Finset ℕ, P ⊆ Finset.range N → P.card + 1 ≤ R →
      ∃ a b : ℕ, a < N ∧ b < N ∧ a ≤ b ∧
        (∀ w ∈ P, ¬ (a < w ∧ w ≤ b)) ∧ B ≤ cost (a, b)) :
    B ≤ WithTop.untopD 0 (((Finset.range N).powerset.filter
      (fun P : Finset ℕ => P.card + 1 ≤ R)).image
      (fun P : Finset ℕ => ((Finset.range N ×ˢ Finset.range N).filter
        (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧
          ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup cost)).min := by
  let feasible := (Finset.range N).powerset.filter
    (fun P : Finset ℕ => P.card + 1 ≤ R)
  let score (P : Finset ℕ) := ((Finset.range N ×ˢ Finset.range N).filter
    (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧
      ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup cost
  change B ≤ WithTop.untopD 0 (feasible.image score).min
  have hempty : (∅ : Finset ℕ) ∈ feasible := by
    simp only [feasible, Finset.mem_filter, Finset.mem_powerset, Finset.card_empty]
    exact ⟨Finset.empty_subset _, hR⟩
  have hne : (feasible.image score).Nonempty :=
    ⟨score ∅, Finset.mem_image_of_mem score hempty⟩
  obtain ⟨v, hv⟩ := Finset.min_of_nonempty hne
  rw [hv]
  simp only [WithTop.untopD_coe]
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_min hv)
  obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hP
  obtain ⟨a, b, ha, hb, hab, hcut, hbound⟩ :=
    hcost P (Finset.mem_powerset.mp hsub) hcard
  apply hbound.trans
  apply Finset.le_sup
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩,
      hab, hcut⟩

end PEqualNP.Outside.L_meta_1349

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by

  intro h t hh
  apply PEqualNP.Outside.L_meta_1349.game_lower
    (h + 3) (2 ^ t) _
    (fun uv => PEqualNP.Outside.L_meta_1349.intervalCost h uv.1 uv.2)
    (Nat.one_le_pow _ _ (by decide))
  intro P hP hcount
  obtain ⟨a, b, ha, hb, hab, hcut, hspan⟩ :=
    PEqualNP.Outside.L_meta_1349.exists_long_interval
      (h + 3) (2 ^ t) P (by omega) (by positivity) hP hcount
  refine ⟨a, b, ha, hb, hab, hcut, ?_⟩
  apply le_trans _ (PEqualNP.Outside.L_meta_1349.interval_lower h a b hh hab (by omega))
  apply Nat.mul_le_mul_left
  apply Nat.sub_le_sub_right
  apply Nat.pow_le_pow_right (by decide)
  omega
