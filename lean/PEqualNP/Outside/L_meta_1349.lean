import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

-- the value of level u in the ladder for a plane of order 2^h
def V (h u : ℕ) : ℕ :=
  if u = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if u = h + 2 then 0
  else 2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h

-- the multiplier of the upper end u
def M (h u : ℕ) : ℕ := if u = h + 2 then 2 ^ h else 2 ^ (u - 1) - 1

-- the cost of the pair of levels uv
def cost (h : ℕ) (uv : ℕ × ℕ) : ℕ := (V h uv.1 - V h uv.2) * M h uv.2

lemma V_zero' (h : ℕ) : V h 0 = 2 ^ h * 2 ^ h + 2 ^ h + 1 := by
  unfold V; rw [if_pos rfl]

lemma V_top' (h : ℕ) : V h (h + 2) = 0 := by
  have hne : h + 2 ≠ 0 := by omega
  unfold V; rw [if_neg hne, if_pos rfl]

lemma V_mid' (h u : ℕ) (hu1 : 1 ≤ u) (hu2 : u ≤ h + 1) :
    V h u + 2 ^ h = 2 ^ (h + 1 - u) * (2 ^ h + 1) := by
  have hne0 : u ≠ 0 := by omega
  have hne : u ≠ h + 2 := by omega
  have key : 2 ^ h * (2 ^ h + 1) = 2 ^ (u - 1) * (2 ^ (h + 1 - u) * (2 ^ h + 1)) := by
    rw [← mul_assoc, ← pow_add, show u - 1 + (h + 1 - u) = h by omega]
  have hge : 2 ^ h ≤ 2 ^ (h + 1 - u) * (2 ^ h + 1) := by
    have : 0 < 2 ^ (h + 1 - u) := by positivity
    calc 2 ^ h ≤ 1 * (2 ^ h + 1) := by omega
      _ ≤ _ := Nat.mul_le_mul (by omega) le_rfl
  unfold V
  rw [if_neg hne0, if_neg hne, key, Nat.mul_div_cancel_left _ (by positivity)]
  exact Nat.sub_add_cancel hge

lemma M_top' (h : ℕ) : M h (h + 2) = 2 ^ h := by
  unfold M; rw [if_pos rfl]

lemma M_mid' (h u : ℕ) (hu : u ≤ h + 1) : M h u = 2 ^ (u - 1) - 1 := by
  have hne : u ≠ h + 2 := by omega
  unfold M; rw [if_neg hne]

lemma arA0 (Q P X : ℕ) (hP : Q = 2 * P) (hX : X + 1 ≤ 2 * Q) :
    Q * P * X ≤ (Q * Q + Q + 1) * Q := by
  calc Q * P * X ≤ Q * P * (2 * Q) := Nat.mul_le_mul le_rfl (by omega)
    _ = Q * Q * Q := by subst hP; ring
    _ ≤ (Q * Q + Q + 1) * Q := Nat.mul_le_mul (by omega) le_rfl

lemma arA1 (Q P X a V1 : ℕ) (hP : Q = 2 * P) (hV : V1 + Q = a * (Q + 1)) (hXa : X + 1 ≤ a) :
    Q * P * X ≤ V1 * Q := by
  have h1 : (X + 1) * Q ≤ a * Q := Nat.mul_le_mul hXa le_rfl
  have hV1 : X * Q ≤ V1 := by nlinarith
  calc Q * P * X = (X * P) * Q := by ring
    _ ≤ (X * Q) * Q := Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) le_rfl
    _ ≤ V1 * Q := Nat.mul_le_mul hV1 le_rfl

lemma arB0 (Q P X b c V2 : ℕ) (hQ : Q = 2 * (b * c)) (hP : P = b * c) (hc : 1 ≤ c)
    (hV2 : V2 + Q = b * (Q + 1)) (hXc : X + 1 ≤ 2 * c) :
    Q * P * X ≤ (Q * Q + Q + 1 - V2) * (2 * c - 1) := by
  subst hP
  have e1 : Q * b * 1 ≤ Q * b * c := Nat.mul_le_mul le_rfl hc
  have e2 : b * 1 ≤ b * c := Nat.mul_le_mul le_rfl hc
  have e3 : Q * Q = Q * (2 * (b * c)) := by rw [← hQ]
  have hD : Q * (b * c) ≤ Q * Q + Q + 1 - V2 := by
    have : V2 + Q * (b * c) ≤ Q * Q + Q + 1 := by nlinarith
    omega
  calc Q * (b * c) * X ≤ Q * (b * c) * (2 * c - 1) := Nat.mul_le_mul le_rfl (by omega)
    _ ≤ (Q * Q + Q + 1 - V2) * (2 * c - 1) := Nat.mul_le_mul hD le_rfl

lemma arB1 (Q P X b c t V1 V2 : ℕ) (hP : P = b * c) (hc : 1 ≤ c)
    (hV1 : V1 + Q = b * t * (Q + 1)) (hV2 : V2 + Q = b * (Q + 1)) (hXt : X + 1 ≤ t) :
    Q * P * X ≤ (V1 - V2) * (2 * c - 1) := by
  subst hP
  have h3 : b * (Q + 1) * (X + 1) ≤ b * (Q + 1) * t := Nat.mul_le_mul le_rfl hXt
  have hD : b * X * (Q + 1) ≤ V1 - V2 := by
    have : V2 + b * X * (Q + 1) ≤ V1 := by nlinarith
    omega
  calc Q * (b * c) * X = (b * X * Q) * c := by ring
    _ ≤ (b * X * (Q + 1)) * (2 * c - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) (by omega)
    _ ≤ (V1 - V2) * (2 * c - 1) := Nat.mul_le_mul hD le_rfl

theorem arith (h u1 u2 g : ℕ) (h1 : 1 ≤ h) (h12 : u1 ≤ u2) (h2 : u2 ≤ h + 2) (hg : g ≤ u2 - u1) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (g - 1) - 1) ≤ cost h (u1, u2) := by
  rcases Nat.lt_or_ge g 2 with hg2 | hg2
  · have : g - 1 = 0 := by omega
    simp [this]
  obtain ⟨P, hP⟩ : ∃ P, 2 ^ h = 2 * P :=
    ⟨2 ^ (h - 1), by rw [← pow_succ', Nat.sub_add_cancel h1]⟩
  have hQQ : 2 ^ h * 2 ^ h / 2 = 2 ^ h * P := by
    rw [hP, show 2 * P * (2 * P) = 2 * (2 * P * P) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  obtain ⟨X, hX⟩ : ∃ X, 2 ^ (g - 1) = X + 1 :=
    ⟨2 ^ (g - 1) - 1, by have : 0 < 2 ^ (g - 1) := by positivity
                         omega⟩
  rw [hQQ, hX, Nat.add_sub_cancel]
  simp only [cost]
  rcases Nat.lt_or_ge u2 (h + 2) with hu2 | hu2
  · have hu2lo : 2 ≤ u2 := by omega
    obtain ⟨b, hb⟩ : ∃ b, b = 2 ^ (h + 1 - u2) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = 2 ^ (u2 - 2) := ⟨_, rfl⟩
    have hc1 : 1 ≤ c := by
      have : 0 < 2 ^ (u2 - 2) := by positivity
      omega
    have hM : M h u2 = 2 * c - 1 := by
      rw [M_mid' h u2 (by omega), hc, ← pow_succ', show u2 - 2 + 1 = u2 - 1 by omega]
    have hQ : 2 ^ h = 2 * (b * c) := by
      rw [hb, hc, ← pow_add, ← pow_succ', show h + 1 - u2 + (u2 - 2) + 1 = h by omega]
    have hPbc : P = b * c := by omega
    have hV2 : V h u2 + 2 ^ h = b * (2 ^ h + 1) := by
      rw [hb]; exact V_mid' h u2 (by omega) (by omega)
    rw [hM]
    rcases Nat.eq_zero_or_pos u1 with hu1 | hu1
    · subst hu1
      rw [V_zero']
      have hXc : X + 1 ≤ 2 * c := by
        rw [← hX, hc, ← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact arB0 _ _ _ _ _ _ hQ hPbc hc1 hV2 hXc
    · obtain ⟨t, ht⟩ : ∃ t, t = 2 ^ (u2 - u1) := ⟨_, rfl⟩
      have hV1 : V h u1 + 2 ^ h = b * t * (2 ^ h + 1) := by
        rw [V_mid' h u1 hu1 (by omega), hb, ht, ← pow_add,
          show h + 1 - u2 + (u2 - u1) = h + 1 - u1 by omega]
      have hXt : X + 1 ≤ t := by
        rw [← hX, ht]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact arB1 _ _ _ _ _ _ _ _ hPbc hc1 hV1 hV2 hXt
  · have hu2' : u2 = h + 2 := by omega
    subst hu2'
    rw [V_top', M_top', Nat.sub_zero]
    rcases Nat.eq_zero_or_pos u1 with hu1 | hu1
    · subst hu1
      rw [V_zero']
      have hX2 : X + 1 ≤ 2 * 2 ^ h := by
        rw [← hX, ← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact arA0 _ _ _ hP hX2
    · have hV := V_mid' h u1 hu1 (by omega)
      have hXa : X + 1 ≤ 2 ^ (h + 1 - u1) := by
        rw [← hX]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact arA1 _ _ _ _ _ hP hV hXa

-- pairs of levels inside one run of the cut set P
def runs (h : ℕ) (P : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
    (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))

-- the allowed cut sets
def cuts (h t : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)

-- the start of the run holding level u: the largest cut at most u, or 0
def start (P : Finset ℕ) (u : ℕ) : ℕ := (P.filter (fun w => w ≤ u)).sup id

theorem start_mem (P : Finset ℕ) (u : ℕ) : start P u ∈ insert 0 P := by
  unfold start
  rcases (P.filter (fun w => w ≤ u)).eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  · obtain ⟨w, hw, hwe⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [hwe]
    exact Finset.mem_insert_of_mem (Finset.mem_filter.1 hw).1

theorem start_le (P : Finset ℕ) (u : ℕ) : start P u ≤ u := by
  unfold start
  apply Finset.sup_le
  intro w hw
  exact (Finset.mem_filter.1 hw).2

theorem le_start (P : Finset ℕ) (u w : ℕ) (hw : w ∈ P) (hwu : w ≤ u) : w ≤ start P u := by
  unfold start
  exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hw, hwu⟩)

-- some run spans at least g + 1 levels
theorem long_run (h t : ℕ) (P : Finset ℕ) (hP : P ∈ cuts h t) :
    ∃ u1 u2, (u1, u2) ∈ runs h P ∧ (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 ≤ u2 - u1 := by
  have hc : P.card + 1 ≤ 2 ^ t := (Finset.mem_filter.1 hP).2
  set G := (h + 3 + 2 ^ t - 1) / 2 ^ t with hGdef
  have hT : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hGT : G * 2 ^ t ≤ h + 3 + 2 ^ t - 1 := Nat.div_mul_le_self _ _
  have hcard : (insert 0 P).card ≤ 2 ^ t := (Finset.card_insert_le 0 P).trans hc
  have hlt : (insert 0 P).card * (G - 1) < (Finset.range (h + 3)).card := by
    rw [Finset.card_range]
    calc (insert 0 P).card * (G - 1) ≤ 2 ^ t * (G - 1) := Nat.mul_le_mul_right _ hcard
      _ = G * 2 ^ t - 2 ^ t := by rw [Nat.mul_sub_one, mul_comm]
      _ < h + 3 := by omega
  obtain ⟨y, _, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := start P) (fun u _ => start_mem P u) hlt
  set F := (Finset.range (h + 3)).filter (fun u => start P u = y) with hF
  have hFne : F.Nonempty := Finset.card_pos.1 (by omega)
  refine ⟨F.min' hFne, F.max' hFne, ?_, ?_⟩
  · have h1 : F.min' hFne ∈ (Finset.range (h + 3)).filter (fun u => start P u = y) :=
      Finset.min'_mem F hFne
    have h2 : F.max' hFne ∈ (Finset.range (h + 3)).filter (fun u => start P u = y) :=
      Finset.max'_mem F hFne
    rw [Finset.mem_filter] at h1 h2
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1.1, h2.1⟩, Finset.min'_le_max' F hFne, ?_⟩
    rintro w hw ⟨hw1, hw2⟩
    have a1 := le_start P _ w hw hw2
    have a2 := start_le P (F.min' hFne)
    rw [h2.2] at a1
    rw [h1.2] at a2
    omega
  · have hsub : F ⊆ Finset.Icc (F.min' hFne) (F.max' hFne) := by
      intro u hu
      exact Finset.mem_Icc.2 ⟨Finset.min'_le F u hu, Finset.le_max' F u hu⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    have hge := Finset.min'_le_max' F hFne
    omega

end PEqualNP.Outside.L_meta_1349

open PEqualNP.Outside.L_meta_1349 in
theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t h1
  change _ ≤ WithTop.untopD 0 (((cuts h t).image (fun P => (runs h P).sup (cost h))).min)
  have hne : ((cuts h t).image (fun P => (runs h P).sup (cost h))).Nonempty := by
    apply Finset.Nonempty.image
    exact ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp [Nat.one_le_two_pow]⟩⟩
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty hne
  rw [ha, WithTop.untopD_coe]
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_min ha)
  obtain ⟨u1, u2, hmem, hg⟩ := long_run h t P hP
  have hu := (Finset.mem_filter.1 hmem)
  have hu2 : u2 < h + 3 := Finset.mem_range.1 (Finset.mem_product.1 hu.1).2
  exact (arith h u1 u2 _ h1 hu.2.1 (by omega) hg).trans (Finset.le_sup (f := cost h) hmem)
