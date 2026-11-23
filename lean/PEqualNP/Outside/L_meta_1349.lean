import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

def A (h u : ℕ) : ℕ :=
  if u = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if u = h + 2 then 0
  else 2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h

def Bw (h v : ℕ) : ℕ := if v = h + 2 then 2 ^ h else 2 ^ (v - 1) - 1

lemma A_mid (h u : ℕ) (h1 : 1 ≤ u) (h2 : u ≤ h + 1) :
    A h u = 2 ^ (h + 1 - u) * (2 ^ h + 1) - 2 ^ h := by
  have h3 : u ≠ 0 := by omega
  have h4 : u ≠ h + 2 := by omega
  simp only [A, h3, h4, ↓reduceIte]
  have hp : 2 ^ (h + 1 - u) * 2 ^ (u - 1) = 2 ^ h := by
    rw [← pow_add]
    congr 1
    omega
  rw [Nat.div_eq_of_eq_mul_left (by positivity) (by rw [mul_right_comm, hp])]

-- The value of a pair at distance at least e + 1 is at least the bound.
lemma value_bound (h e u v : ℕ) (hh : 1 ≤ h) (he : 1 ≤ e) (huv : u ≤ v) (hv : v ≤ h + 2)
    (hd : e + 1 ≤ v - u) : (2 ^ h * 2 ^ h / 2) * (2 ^ e - 1) ≤ (A h u - A h v) * Bw h v := by
  set q := 2 ^ h with hq
  have hq1 : 2 ≤ q := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hh
    simpa [hq] using this
  have hhalf : q * q / 2 = 2 ^ (h - 1) * q := by
    have : q = 2 * 2 ^ (h - 1) := by
      rw [hq, ← pow_succ']
      congr 1
      omega
    rw [this]
    rw [show 2 * 2 ^ (h - 1) * (2 * 2 ^ (h - 1)) = (2 ^ (h - 1) * (2 * 2 ^ (h - 1))) * 2 by ring]
    rw [Nat.mul_div_cancel _ (by norm_num)]
  have hE1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  rw [hhalf]
  by_cases hvt : v = h + 2
  · -- the last level: weight q and value zero there
    have hBv : Bw h v = q := by simp [Bw, hvt, hq]
    have hAv : A h v = 0 := by simp [A, hvt]
    rw [hBv, hAv, Nat.sub_zero]
    have hpow : 2 ^ (h - 1) ≤ q := by
      rw [hq]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hu0 : u = 0
    · have hAu : A h u = q * q + q + 1 := by simp [A, hu0, hq]
      rw [hAu]
      have heh : e ≤ h + 1 := by omega
      have h2e : 2 ^ e ≤ 2 * q := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) heh
        rw [pow_succ] at this
        rw [hq]
        linarith
      have h2h : 2 * 2 ^ (h - 1) = q := by
        rw [hq, ← pow_succ']
        congr 1
        omega
      calc 2 ^ (h - 1) * q * (2 ^ e - 1) ≤ 2 ^ (h - 1) * q * (2 * q) := by
            gcongr
            exact (Nat.sub_le _ _).trans h2e
        _ = (2 * 2 ^ (h - 1)) * q * q := by ring
        _ = q * q * q := by rw [h2h]
        _ ≤ (q * q + q + 1) * q := by nlinarith
    · have hu1 : 1 ≤ u := by omega
      have hu2 : u ≤ h + 1 := by omega
      rw [A_mid h u hu1 hu2]
      have hs : 2 ^ e ≤ 2 ^ (h + 1 - u) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hlow : (2 ^ e - 1) * q ≤ 2 ^ (h + 1 - u) * (q + 1) - q := by
        have : 2 ^ e * q ≤ 2 ^ (h + 1 - u) * q := Nat.mul_le_mul_right _ hs
        have h3 : 2 ^ (h + 1 - u) * q ≤ 2 ^ (h + 1 - u) * (q + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.sub_mul, Nat.one_mul]
        omega
      calc 2 ^ (h - 1) * q * (2 ^ e - 1) ≤ q * ((2 ^ e - 1) * q) := by
            rw [show 2 ^ (h - 1) * q * (2 ^ e - 1) = 2 ^ (h - 1) * ((2 ^ e - 1) * q) by ring]
            gcongr
        _ ≤ q * (2 ^ (h + 1 - u) * (q + 1) - q) := by gcongr
        _ = (2 ^ (h + 1 - u) * (q + 1) - q) * q := by ring
  · have hv1 : v ≤ h + 1 := by omega
    have hv2 : 2 ≤ v := by omega
    have hBv : Bw h v = 2 ^ (v - 1) - 1 := by simp [Bw, hvt]
    rw [hBv, A_mid h v (by omega) hv1]
    set r := h + 1 - v with hr
    have hrh : r ≤ h - 1 := by omega
    -- a lower bound for the value at u, through the level max u 1
    have hAu : 2 ^ r * 2 ^ e * (q + 1) - q ≤ A h u := by
      have key : 2 ^ r * 2 ^ e ≤ 2 ^ (h + 1 - max u 1) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      by_cases hu0 : u = 0
      · have hA0 : A h u = q * q + q + 1 := by simp [A, hu0, hq]
        rw [hA0]
        have hm : h + 1 - max u 1 = h := by omega
        rw [hm] at key
        have : 2 ^ r * 2 ^ e * (q + 1) ≤ q * (q + 1) := Nat.mul_le_mul_right _ key
        have : q * (q + 1) = q * q + q := by ring
        omega
      · rw [A_mid h u (by omega) (by omega), ← hq]
        have hm : h + 1 - max u 1 = h + 1 - u := by omega
        rw [hm] at key
        have : 2 ^ r * 2 ^ e * (q + 1) ≤ 2 ^ (h + 1 - u) * (q + 1) := Nat.mul_le_mul_right _ key
        omega
    set X := 2 ^ r * (q + 1) with hX
    have hXq : q ≤ X := by
      have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      rw [hX]
      nlinarith
    have hY : 2 ^ r * 2 ^ e * (q + 1) = X * 2 ^ e := by rw [hX]; ring
    rw [hY] at hAu
    have hXY : X ≤ X * 2 ^ e := Nat.le_mul_of_pos_right _ (by positivity)
    have hdiff : X * (2 ^ e - 1) ≤ A h u - (X - q) := by
      rw [Nat.mul_sub_one]
      omega
    have hw : 2 ^ (v - 1) = 2 ^ (h - r) := by congr 1; omega
    rw [hw]
    have hsplit : 2 ^ h = 2 ^ r * 2 ^ (h - r) := by
      rw [← pow_add]
      congr 1
      omega
    have hhr : 2 ^ (h - 1) ≤ 2 ^ r * (2 ^ (h - r) - 1) := by
      rw [Nat.mul_sub_one, ← hsplit]
      have h1 : 2 ^ r ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by norm_num) hrh
      have h2 : 2 ^ h = 2 * 2 ^ (h - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    calc 2 ^ (h - 1) * q * (2 ^ e - 1) ≤ (2 ^ r * (2 ^ (h - r) - 1)) * (q + 1) * (2 ^ e - 1) := by
          gcongr
          omega
      _ = X * (2 ^ e - 1) * (2 ^ (h - r) - 1) := by rw [hX]; ring
      _ ≤ (A h u - (X - q)) * (2 ^ (h - r) - 1) := by gcongr

-- Some run between consecutive cut points is long: pigeonhole on the number of cuts so far.
lemma run_exists (N K L : ℕ) (P : Finset ℕ) (hP : P.card + 1 ≤ K) (hL : K * L < N) :
    ∃ u v, u ≤ v ∧ v < N ∧ L ≤ v - u ∧ ∀ w ∈ P, ¬ (u < w ∧ w ≤ v) := by
  classical
  let r : ℕ → ℕ := fun x => (P.filter (· ≤ x)).card
  have hmaps : ∀ x ∈ Finset.range N, r x ∈ Finset.range K := by
    intro x _
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Finset.card_filter_le _ _) (by omega)
  obtain ⟨k, _, hk⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (by simpa using hL)
  set F := (Finset.range N).filter (fun x => r x = k) with hF
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨F.min' hne, F.max' hne, Finset.min'_le _ _ (Finset.max'_mem _ _), ?_, ?_, ?_⟩
  · exact Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem F hne)).1
  · have hsub : F ⊆ Finset.Icc (F.min' hne) (F.max' hne) := fun x hx =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  · intro w hw ⟨h1, h2⟩
    have hu := (Finset.mem_filter.mp (Finset.min'_mem F hne)).2
    have hv := (Finset.mem_filter.mp (Finset.max'_mem F hne)).2
    have hsub : P.filter (· ≤ F.min' hne) ⊆ P.filter (· ≤ F.max' hne) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans (Finset.min'_le _ _ (Finset.max'_mem _ _))⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      change r (F.max' hne) ≤ r (F.min' hne)
      rw [hu, hv])
    have hwin : w ∈ P.filter (· ≤ F.max' hne) := Finset.mem_filter.mpr ⟨hw, h2⟩
    rw [← heq, Finset.mem_filter] at hwin
    omega

end PEqualNP.Outside.L_meta_1349

open PEqualNP.Outside.L_meta_1349 in
theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  set e := (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1 with he
  by_cases he0 : e = 0
  · rw [he0]
    simp
  have hK : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hL : 2 ^ t * (e + 1) < h + 3 := by
    have hc := Nat.div_mul_le_self (h + 3 + 2 ^ t - 1) (2 ^ t)
    have hce : (h + 3 + 2 ^ t - 1) / 2 ^ t = e + 2 := by omega
    rw [hce] at hc
    have : (e + 2) * 2 ^ t = 2 ^ t * (e + 1) + 2 ^ t := by ring
    omega
  set S := (Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)
  have hS : (∅ : Finset ℕ) ∈ S := by
    simp [S]
  set F := fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
    (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup
    (fun uv : ℕ × ℕ => (A h uv.1 - A h uv.2) * Bw h uv.2) with hF
  change _ ≤ WithTop.untopD 0 (S.image F).min
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty (s := S.image F) (Finset.image_nonempty.mpr ⟨_, hS⟩)
  rw [hm, WithTop.untopD_coe]
  have hle : ((2 ^ h * 2 ^ h / 2) * (2 ^ e - 1) : ℕ) ≤ ((S.image F).min : WithTop ℕ) := by
    apply Finset.le_min
    intro b hb
    obtain ⟨P, hPS, rfl⟩ := Finset.mem_image.mp hb
    have hPc := (Finset.mem_filter.mp hPS).2
    obtain ⟨u, v, huv, hvN, hd, hcut⟩ := run_exists (h + 3) (2 ^ t) (e + 1) P hPc hL
    have hmem : (u, v) ∈ (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
        (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)) := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, hvN⟩, huv, hcut⟩
    have h1 := value_bound h e u v hh (by omega) huv (by omega) hd
    have h2 := Finset.le_sup (f := fun uv : ℕ × ℕ => (A h uv.1 - A h uv.2) * Bw h uv.2) hmem
    exact WithTop.coe_le_coe.mpr (h1.trans h2)
  rw [hm] at hle
  exact WithTop.coe_le_coe.mp hle
