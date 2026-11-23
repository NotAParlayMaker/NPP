import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349

open Finset

def av (h u : ℕ) : ℕ :=
  if u = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if u = h + 2 then 0
  else 2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h

def bv (h v : ℕ) : ℕ := if v = h + 2 then 2 ^ h else 2 ^ (v - 1) - 1

def gval (h : ℕ) (P : Finset ℕ) : ℕ :=
  ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
    (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup
    (fun uv : ℕ × ℕ => (av h uv.1 - av h uv.2) * bv h uv.2)

lemma av_mid (h u : ℕ) (h1 : u ≠ 0) (h2 : u ≠ h + 2) :
    av h u = 2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h := by
  simp [av, h1, h2]

lemma av_top (h : ℕ) : av h (h + 2) = 0 := by
  simp [av]

lemma bv_top (h : ℕ) : bv h (h + 2) = 2 ^ h := by
  simp [bv]

lemma bv_mid (h v : ℕ) (h2 : v ≠ h + 2) : bv h v = 2 ^ (v - 1) - 1 := by
  simp [bv, h2]

lemma div_exact (h u : ℕ) (h1 : 1 ≤ u) (h2 : u ≤ h + 1) :
    2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) = 2 ^ (h + 1 - u) * (2 ^ h + 1) := by
  have hp : (2 : ℕ) ^ h = 2 ^ (h + 1 - u) * 2 ^ (u - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have e : 2 ^ h * (2 ^ h + 1) = 2 ^ (h + 1 - u) * (2 ^ h + 1) * 2 ^ (u - 1) := by
    nth_rewrite 1 [hp]
    ring
  rw [e]
  exact Nat.mul_div_cancel _ (by positivity)

lemma arithA (Q x y z w : ℕ) (hxz : x * z = Q) (hz : 2 ≤ z) (hwy : w ≤ y) (hw : 1 ≤ w) :
    Q * Q / 2 * (w - 1) ≤ (x * y * (Q + 1) - Q - (x * (Q + 1) - Q)) * (z - 1) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  obtain ⟨z', rfl⟩ : ∃ z', z = z' + 2 := ⟨z - 2, by omega⟩
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have hwy' : w' ≤ y' := by omega
  have h1 : Q ≤ x * (Q + 1) := by
    rcases Nat.eq_zero_or_pos x with hx | hx
    · rw [hx] at hxz
      simp at hxz
      omega
    · nlinarith
  have h2 : x * (y' + 1) * (Q + 1) = x * y' * (Q + 1) + x * (Q + 1) := by ring
  have h3 : x * (y' + 1) * (Q + 1) - Q - (x * (Q + 1) - Q) = x * y' * (Q + 1) := by omega
  rw [h3]
  simp only [Nat.add_sub_cancel]
  have h4 : Q * Q / 2 ≤ Q * x * (z' + 1) := by
    apply Nat.div_le_of_le_mul
    have : Q * Q = Q * x * (z' + 2) := by
      rw [mul_assoc, hxz]
    nlinarith
  have h5 : z' + 2 - 1 = z' + 1 := by omega
  rw [h5]
  calc Q * Q / 2 * w' ≤ Q * x * (z' + 1) * w' := Nat.mul_le_mul_right _ h4
    _ ≤ Q * x * (z' + 1) * y' := Nat.mul_le_mul_left _ hwy'
    _ ≤ x * y' * (Q + 1) * (z' + 1) := by nlinarith [Nat.zero_le (x * y' * (z' + 1))]

lemma lemA (h u v E : ℕ) (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ h + 1) (hE : E ≤ v - u) :
    2 ^ h * 2 ^ h / 2 * (2 ^ E - 1) ≤
      (2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h - (2 ^ h * (2 ^ h + 1) / 2 ^ (v - 1) - 2 ^ h)) *
        (2 ^ (v - 1) - 1) := by
  rw [div_exact h u hu (by omega), div_exact h v (by omega) hv]
  have e1 : (2 : ℕ) ^ (h + 1 - u) = 2 ^ (h + 1 - v) * 2 ^ (v - u) := by
    rw [← pow_add]
    congr 1
    omega
  have e2 : (2 : ℕ) ^ (h + 1 - v) * 2 ^ (v - 1) = 2 ^ h := by
    rw [← pow_add]
    congr 1
    omega
  have e3 : 2 ≤ (2 : ℕ) ^ (v - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (v - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e4 : (2 : ℕ) ^ E ≤ 2 ^ (v - u) := Nat.pow_le_pow_right (by norm_num) hE
  have e5 : 1 ≤ (2 : ℕ) ^ E := Nat.one_le_two_pow
  rw [e1]
  exact arithA (2 ^ h) (2 ^ (h + 1 - v)) (2 ^ (v - u)) (2 ^ (v - 1)) (2 ^ E) e2 e3 e4 e5

lemma lemB1 (h u E : ℕ) (hu : 1 ≤ u) (hu2 : u ≤ h + 1) (hE : E ≤ h + 1 - u) :
    2 ^ h * 2 ^ h / 2 * (2 ^ E - 1) ≤
      (2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h - 0) * 2 ^ h := by
  rw [div_exact h u hu hu2]
  have e4 : (2 : ℕ) ^ E ≤ 2 ^ (h + 1 - u) := Nat.pow_le_pow_right (by norm_num) hE
  have e5 : 1 ≤ (2 : ℕ) ^ E := Nat.one_le_two_pow
  generalize (2 : ℕ) ^ E = w at e4 e5
  generalize (2 : ℕ) ^ (h + 1 - u) = y at e4
  generalize (2 : ℕ) ^ h = Q
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  have h1 : (y' + 1) * (Q + 1) - Q - 0 = y' * (Q + 1) + 1 := by
    have : (y' + 1) * (Q + 1) = y' * (Q + 1) + Q + 1 := by ring
    omega
  rw [h1]
  simp only [Nat.add_sub_cancel]
  have h2 : Q * Q / 2 ≤ Q * Q := Nat.div_le_self _ _
  have h3 : w' ≤ y' := by omega
  calc Q * Q / 2 * w' ≤ Q * Q * w' := Nat.mul_le_mul_right _ h2
    _ ≤ Q * Q * y' := Nat.mul_le_mul_left _ h3
    _ ≤ (y' * (Q + 1) + 1) * Q := by nlinarith [Nat.zero_le (y' * Q)]

lemma lemB2 (h E : ℕ) (hE : E ≤ h + 1) :
    2 ^ h * 2 ^ h / 2 * (2 ^ E - 1) ≤
      (2 ^ h * (2 ^ h + 1) / 2 ^ (1 - 1) - 2 ^ h - 0) * 2 ^ h := by
  have e4 : (2 : ℕ) ^ E ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by norm_num) hE
  have e6 : (2 : ℕ) ^ (h + 1) = 2 * 2 ^ h := by ring
  rw [e6] at e4
  simp only [Nat.sub_self, pow_zero, Nat.div_one, Nat.sub_zero]
  generalize (2 : ℕ) ^ E = w at e4
  generalize (2 : ℕ) ^ h = Q at e4
  have h1 : Q * (Q + 1) - Q = Q * Q := by
    have : Q * (Q + 1) = Q * Q + Q := by ring
    omega
  rw [h1]
  have h2 : Q * Q / 2 * 2 ≤ Q * Q := Nat.div_mul_le_self _ _
  have h3 : w - 1 ≤ 2 * Q := by omega
  calc Q * Q / 2 * (w - 1) ≤ Q * Q / 2 * (2 * Q) := Nat.mul_le_mul_left _ h3
    _ = Q * Q / 2 * 2 * Q := by ring
    _ ≤ Q * Q * Q := Nat.mul_le_mul_right _ h2

lemma run (P : Finset ℕ) : ∀ k a b : ℕ, a < b →
    (P.filter (fun w => a < w ∧ w < b)).card + 1 ≤ k →
    ∃ u v : ℕ, a ≤ u ∧ u ≤ v ∧ v < b ∧ b - a ≤ (v - u + 1) * k ∧
      ∀ w ∈ P, ¬ (u < w ∧ w ≤ v) := by
  intro k
  induction k with
  | zero =>
    intro a b _ hk
    omega
  | succ k ih =>
    intro a b hab hk
    by_cases hemp : P.filter (fun w => a < w ∧ w < b) = ∅
    · refine ⟨a, b - 1, le_refl _, by omega, by omega, ?_, ?_⟩
      · have : b - a ≤ (b - 1 - a + 1) * 1 := by omega
        exact this.trans (Nat.mul_le_mul_left _ (by omega))
      · intro w hw hcon
        have : w ∈ P.filter (fun w => a < w ∧ w < b) :=
          Finset.mem_filter.mpr ⟨hw, hcon.1, by omega⟩
        rw [hemp] at this
        simp at this
    · have hne : (P.filter (fun w => a < w ∧ w < b)).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hemp
      have hmem := Finset.max'_mem _ hne
      obtain ⟨hw0P, hw0a, hw0b⟩ := Finset.mem_filter.mp hmem
      have hmax : ∀ w ∈ P, a < w → w < b →
          w ≤ (P.filter (fun w => a < w ∧ w < b)).max' hne :=
        fun w hw h1 h2 => Finset.le_max' _ w (Finset.mem_filter.mpr ⟨hw, h1, h2⟩)
      generalize (P.filter (fun w => a < w ∧ w < b)).max' hne = w0 at hw0P hw0a hw0b hmax
      by_cases hbig : b - a ≤ (b - w0) * (k + 1)
      · refine ⟨w0, b - 1, by omega, by omega, by omega, ?_, ?_⟩
        · have : b - 1 - w0 + 1 = b - w0 := by omega
          rw [this]
          exact hbig
        · intro w hw hcon
          have := hmax w hw (by omega) (by omega)
          omega
      · have hsub : P.filter (fun w => a < w ∧ w < w0) ⊆
            (P.filter (fun w => a < w ∧ w < b)).erase w0 := by
          intro w hw
          obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_filter.mpr ⟨h1, h2, by omega⟩⟩
        have hc1 := Finset.card_le_card hsub
        have hc2 : ((P.filter (fun w => a < w ∧ w < b)).erase w0).card =
            (P.filter (fun w => a < w ∧ w < b)).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hw0P, hw0a, hw0b⟩)
        have hpos : 0 < (P.filter (fun w => a < w ∧ w < b)).card :=
          Finset.card_pos.mpr ⟨w0, Finset.mem_filter.mpr ⟨hw0P, hw0a, hw0b⟩⟩
        obtain ⟨u, v, h1, h2, h3, h4, h5⟩ := ih a w0 hw0a (by omega)
        refine ⟨u, v, h1, h2, by omega, ?_, h5⟩
        have hk1 : 1 ≤ k := by omega
        have hbig' : (b - w0) * (k + 1) < b - a := by omega
        generalize hm : v - u + 1 = mm at h4
        generalize hr : b - w0 = rr at hbig'
        generalize hn : b - a = nn at hbig'
        have hn' : w0 - a = nn - rr := by omega
        rw [hn'] at h4
        have hrr : rr ≤ nn := by omega
        obtain ⟨dd, rfl⟩ : ∃ dd, nn = rr + dd := ⟨nn - rr, by omega⟩
        simp only [Nat.add_sub_cancel_left] at h4
        nlinarith

end PEqualNP.Outside.L_meta_1349

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  classical
  show _ ≤ WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter
    (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (PEqualNP.Outside.L_meta_1349.gval h)).min
  have hkey : ∀ P : Finset ℕ, P.card + 1 ≤ 2 ^ t →
      2 ^ h * 2 ^ h / 2 * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ PEqualNP.Outside.L_meta_1349.gval h P := by
    intro P hP
    have hfc : (P.filter (fun w => 0 < w ∧ w < h + 3)).card ≤ P.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    obtain ⟨u0, v0, _, huv, hvb, hlen, hcut⟩ := PEqualNP.Outside.L_meta_1349.run P (2 ^ t) 0 (h + 3) (by omega) (by omega)
    have hpos : 0 < 2 ^ t := by positivity
    have hL : (h + 3 + 2 ^ t - 1) / 2 ^ t ≤ v0 - u0 + 1 := by
      have : (h + 3 + 2 ^ t - 1) / 2 ^ t < v0 - u0 + 1 + 1 := by
        rw [Nat.div_lt_iff_lt_mul hpos]
        have : (v0 - u0 + 1 + 1) * 2 ^ t = (v0 - u0 + 1) * 2 ^ t + 2 ^ t := by ring
        omega
      omega
    generalize (h + 3 + 2 ^ t - 1) / 2 ^ t = L at hL
    by_cases hL2 : L ≤ 2
    · have : L - 1 - 1 = 0 := by omega
      rw [this]
      simp
    · have hsup : ∀ u v : ℕ, u ≤ v → v < h + 3 → (∀ w ∈ P, ¬ (u < w ∧ w ≤ v)) →
          (PEqualNP.Outside.L_meta_1349.av h u - PEqualNP.Outside.L_meta_1349.av h v) * PEqualNP.Outside.L_meta_1349.bv h v ≤ PEqualNP.Outside.L_meta_1349.gval h P := by
        intro u v h1 h2 h3
        have hm : (u, v) ∈ (Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter
            (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr h2⟩, h1, h3⟩
        unfold PEqualNP.Outside.L_meta_1349.gval
        exact Finset.le_sup (f := fun uv : ℕ × ℕ =>
          (PEqualNP.Outside.L_meta_1349.av h uv.1 - PEqualNP.Outside.L_meta_1349.av h uv.2) *
            PEqualNP.Outside.L_meta_1349.bv h uv.2) hm
      by_cases hv : v0 = h + 2
      · by_cases hu : u0 = 0
        · refine le_trans ?_ (hsup 1 (h + 2) (by omega) (by omega) (by
            intro w hw hcon
            exact hcut w hw ⟨by omega, by omega⟩))
          rw [PEqualNP.Outside.L_meta_1349.av_mid h 1 (by omega) (by omega), PEqualNP.Outside.L_meta_1349.av_top, PEqualNP.Outside.L_meta_1349.bv_top]
          exact PEqualNP.Outside.L_meta_1349.lemB2 h (L - 1 - 1) (by omega)
        · refine le_trans ?_ (hsup u0 (h + 2) (by omega) (by omega) (by
            intro w hw hcon
            exact hcut w hw ⟨by omega, by omega⟩))
          rw [PEqualNP.Outside.L_meta_1349.av_mid h u0 hu (by omega), PEqualNP.Outside.L_meta_1349.av_top, PEqualNP.Outside.L_meta_1349.bv_top]
          exact PEqualNP.Outside.L_meta_1349.lemB1 h u0 (L - 1 - 1) (by omega) (by omega) (by omega)
      · by_cases hu : u0 = 0
        · refine le_trans ?_ (hsup 1 v0 (by omega) (by omega) (by
            intro w hw hcon
            exact hcut w hw ⟨by omega, by omega⟩))
          rw [PEqualNP.Outside.L_meta_1349.av_mid h 1 (by omega) (by omega), PEqualNP.Outside.L_meta_1349.av_mid h v0 (by omega) hv,
            PEqualNP.Outside.L_meta_1349.bv_mid h v0 hv]
          exact PEqualNP.Outside.L_meta_1349.lemA h 1 v0 (L - 1 - 1) (by omega) (by omega) (by omega) (by omega)
        · refine le_trans ?_ (hsup u0 v0 huv hvb hcut)
          rw [PEqualNP.Outside.L_meta_1349.av_mid h u0 hu (by omega), PEqualNP.Outside.L_meta_1349.av_mid h v0 (by omega) hv, PEqualNP.Outside.L_meta_1349.bv_mid h v0 hv]
          exact PEqualNP.Outside.L_meta_1349.lemA h u0 v0 (L - 1 - 1) (by omega) (by omega) (by omega) (by omega)
  have hne : (((Finset.range (h + 3)).powerset.filter
      (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (PEqualNP.Outside.L_meta_1349.gval h)).Nonempty := by
    refine ⟨PEqualNP.Outside.L_meta_1349.gval h ∅, Finset.mem_image.mpr ⟨∅, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩, rfl⟩⟩
    simp only [Finset.card_empty, zero_add]
    exact Nat.one_le_two_pow
  obtain ⟨x, hx⟩ := Finset.min_of_nonempty hne
  rw [hx]
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_min hx)
  exact hkey P (Finset.mem_filter.mp hP).2
