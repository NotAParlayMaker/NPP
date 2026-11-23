import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Choose
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349_aux

lemma gap_exists {L k : ℕ} (hL : 0 < L) (hk : 1 ≤ k)
    (P : Finset ℕ) (hP : P.card + 1 ≤ k) :
    ∃ u v : ℕ, u ≤ v ∧ v < L ∧ (L + k - 1) / k - 1 ≤ v - u ∧
      ∀ w ∈ P, ¬ (u < w ∧ w ≤ v) := by
  classical
  let q := (L + k - 1) / k
  let d := q - 1
  change ∃ u v : ℕ, u ≤ v ∧ v < L ∧ d ≤ v - u ∧
    ∀ w ∈ P, ¬ (u < w ∧ w ≤ v)
  have hk0 : 0 < k := by omega
  have hq : 1 ≤ q := by
    exact (Nat.le_div_iff_mul_le hk0).2 (by simp; omega)
  have hqd : q = d + 1 := by
    dsimp [d]
    omega
  have hdiv : q * k ≤ L + k - 1 := Nat.div_mul_le_self _ _
  have hdMul : d * k ≤ L - 1 := by
    rw [hqd, Nat.add_mul, Nat.one_mul] at hdiv
    omega
  by_cases hd : d = 0
  · refine ⟨0, 0, le_rfl, hL, by simp [hd], ?_⟩
    intro w _ hw
    omega
  · have available : ∃ i : Fin k, ∀ w ∈ P,
        ¬ (i.val * d < w ∧ w ≤ (i.val + 1) * d) := by
      by_contra hnone
      have hit (i : Fin k) : ∃ w ∈ P, i.val * d < w ∧ w ≤ (i.val + 1) * d := by
        by_contra hmiss
        apply hnone
        refine ⟨i, ?_⟩
        intro w hw hwpos
        exact hmiss ⟨w, hw, hwpos⟩
      choose w hw hloc using hit
      let embed : Fin k → {z : ℕ // z ∈ P} := fun i => ⟨w i, hw i⟩
      have hinj : Function.Injective embed := by
        intro i j hembed
        have hwEq : w i = w j := congrArg Subtype.val hembed
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hmul : (i.val + 1) * d ≤ j.val * d :=
            Nat.mul_le_mul_right d (by omega)
          have hwi := (hloc i).2
          have hwj := (hloc j).1
          omega
        · have hmul : (j.val + 1) * d ≤ i.val * d :=
            Nat.mul_le_mul_right d (by omega)
          have hwi := (hloc i).1
          have hwj := (hloc j).2
          omega
      have hkCard : k ≤ P.card := by
        simpa using Fintype.card_le_of_injective embed hinj
      omega
    obtain ⟨i, hi⟩ := available
    have hiMul : (i.val + 1) * d ≤ k * d :=
      Nat.mul_le_mul_right d (by omega)
    have hbelow : (i.val + 1) * d < L := by
      rw [Nat.mul_comm k d] at hiMul
      omega
    refine ⟨i.val * d, (i.val + 1) * d, ?_, hbelow, ?_, hi⟩
    · exact Nat.mul_le_mul_right d (by omega)
    · rw [Nat.add_mul, Nat.one_mul]
      omega

def levelValue (h u : ℕ) : ℕ :=
  if u = 0 then 2 ^ h * 2 ^ h + 2 ^ h + 1
  else if u = h + 2 then 0
  else 2 ^ h * (2 ^ h + 1) / 2 ^ (u - 1) - 2 ^ h

def endWeight (h v : ℕ) : ℕ :=
  if v = h + 2 then 2 ^ h else 2 ^ (v - 1) - 1

private lemma pow_div_factor {h a : ℕ} (ha : a ≤ h) :
    2 ^ h * (2 ^ h + 1) / 2 ^ a = 2 ^ (h - a) * (2 ^ h + 1) := by
  have hp : (2 : ℕ) ^ h = 2 ^ a * 2 ^ (h - a) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le ha]
  calc
    2 ^ h * (2 ^ h + 1) / 2 ^ a =
        (2 ^ a * (2 ^ (h - a) * (2 ^ h + 1))) / 2 ^ a := by
      rw [← Nat.mul_assoc, ← hp]
    _ = _ := Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)

private lemma interior_value {h v : ℕ} (hv₀ : 0 < v) (hv₁ : v ≤ h + 1) :
    levelValue h v = 2 ^ (h - (v - 1)) * (2 ^ h + 1) - 2 ^ h := by
  have hv₂ : v ≠ h + 2 := by omega
  rw [levelValue, ite_eq_right (Nat.ne_of_gt hv₀), ite_eq_right hv₂, pow_div_factor (by omega)]

private lemma half_square {h : ℕ} (hh : 1 ≤ h) :
    2 ^ h * 2 ^ h / 2 = 2 ^ h * 2 ^ (h - 1) := by
  have hp : (2 : ℕ) ^ h = 2 * 2 ^ (h - 1) := by
    calc
      (2 : ℕ) ^ h = 2 ^ (1 + (h - 1)) := by rw [Nat.add_sub_of_le hh]
      _ = 2 * 2 ^ (h - 1) := by rw [Nat.pow_add, Nat.pow_one]
  calc
    2 ^ h * 2 ^ h / 2 = (2 * (2 ^ h * 2 ^ (h - 1))) / 2 := by
      calc
        2 ^ h * 2 ^ h / 2 = (2 ^ h * (2 * 2 ^ (h - 1))) / 2 := by
          exact congrArg (fun n : ℕ => (2 ^ h * n) / 2) hp
        _ = _ := by ac_rfl
    _ = _ := Nat.mul_div_cancel_left _ (by decide)

private lemma power_half_le_weight {b : ℕ} (hb : 1 ≤ b) :
    2 ^ (b - 1) ≤ 2 ^ b - 1 := by
  have hp : (2 : ℕ) ^ b = 2 ^ (b - 1) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hp₀ := Nat.two_pow_pos (b - 1)
  omega

lemma cost_lower {h u v : ℕ} (hh : 1 ≤ h) (huv : u ≤ v) (hv : v < h + 3) :
    (2 ^ h * 2 ^ h / 2) * (2 ^ (v - u - 1) - 1) ≤
      (levelValue h u - levelValue h v) * endWeight h v := by
  by_cases hshort : v ≤ u + 1
  · have he : v - u - 1 = 0 := by omega
    simp [he]
  by_cases hlast : v = h + 2
  · subst v
    have hl : levelValue h (h + 2) = 0 := by simp [levelValue]
    rw [hl, Nat.sub_zero, endWeight, ite_eq_left rfl]
    by_cases hu : u = 0
    · subst u
      have he : h + 2 - 0 - 1 = h + 1 := by omega
      have hp : (2 : ℕ) ^ (h - 1) * 2 ^ (h + 1) = 2 ^ h * 2 ^ h := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        congr 1
        omega
      rw [half_square hh, he, levelValue, ite_eq_left rfl]
      calc
        (2 ^ h * 2 ^ (h - 1)) * (2 ^ (h + 1) - 1) ≤
            (2 ^ h * 2 ^ (h - 1)) * 2 ^ (h + 1) :=
          Nat.mul_le_mul_left _ (Nat.sub_le ..)
        _ = (2 ^ h * 2 ^ h) * 2 ^ h := by
          rw [Nat.mul_assoc, hp, Nat.mul_comm (2 ^ h) (2 ^ h * 2 ^ h)]
        _ ≤ _ := Nat.mul_le_mul_right _ (by
          have := Nat.two_pow_pos h
          omega)
    · have hu₀ : 0 < u := Nat.pos_of_ne_zero hu
      have hu₁ : u ≤ h + 1 := by omega
      have he : h + 2 - u - 1 = h - (u - 1) := by omega
      rw [interior_value hu₀ hu₁, he]
      have hval : 2 ^ h * (2 ^ (h - (u - 1)) - 1) ≤
          2 ^ (h - (u - 1)) * (2 ^ h + 1) - 2 ^ h := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        apply Nat.sub_le_sub_right
        rw [Nat.mul_comm (2 ^ h) (2 ^ (h - (u - 1)))]
        exact Nat.mul_le_mul_left _ (Nat.le_succ _)
      calc
        (2 ^ h * 2 ^ h / 2) * (2 ^ (h - (u - 1)) - 1) ≤
            (2 ^ h * 2 ^ h) * (2 ^ (h - (u - 1)) - 1) :=
          Nat.mul_le_mul_right _ (Nat.div_le_self ..)
        _ = (2 ^ h * (2 ^ (h - (u - 1)) - 1)) * 2 ^ h := by ac_rfl
        _ ≤ _ := Nat.mul_le_mul_right _ hval
  · have hv₁ : v ≤ h + 1 := by omega
    have hv₀ : 0 < v := by omega
    have hb : 1 ≤ v - 1 := by omega
    rw [interior_value hv₀ hv₁, endWeight, ite_eq_right hlast]
    by_cases hu : u = 0
    · subst u
      rw [Nat.sub_zero, levelValue, ite_eq_left rfl]
      rw [half_square hh]
      apply Nat.mul_le_mul_right
      have hhalf : (2 : ℕ) ^ h = 2 ^ (h - 1) * 2 := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      have hvpow : (2 : ℕ) ^ (h - (v - 1)) ≤ 2 ^ (h - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hvprod : 2 ^ (h - (v - 1)) * (2 ^ h + 1) ≤
          2 ^ (h - 1) * (2 ^ h + 1) := Nat.mul_le_mul_right _ hvpow
      have hhalfprod : 2 ^ h * (2 ^ h + 1) =
          (2 ^ (h - 1) * (2 ^ h + 1)) * 2 := by
        calc
          2 ^ h * (2 ^ h + 1) = (2 ^ (h - 1) * 2) * (2 ^ h + 1) := by
            exact congrArg (fun n : ℕ => n * (2 ^ h + 1)) hhalf
          _ = _ := by ac_rfl
      have hfull : 2 ^ h * (2 ^ h + 1) = 2 ^ h * 2 ^ h + 2 ^ h := by
        rw [Nat.mul_add, Nat.mul_one]
      have hsmall : 2 ^ h * 2 ^ (h - 1) ≤ 2 ^ (h - 1) * (2 ^ h + 1) := by
        rw [Nat.mul_comm (2 ^ h) (2 ^ (h - 1))]
        exact Nat.mul_le_mul_left _ (Nat.le_succ _)
      omega
    · have hu₀ : 0 < u := Nat.pos_of_ne_zero hu
      have hu₁ : u ≤ h + 1 := by omega
      rw [interior_value hu₀ hu₁, half_square hh]
      let t := (2 : ℕ) ^ (h - (v - 1))
      let r := (2 : ℕ) ^ (v - u)
      let q := (2 : ℕ) ^ h
      have ht : 1 ≤ t := Nat.two_pow_pos _
      have hr : 1 ≤ r := Nat.two_pow_pos _
      have hpr : (2 : ℕ) ^ (h - (u - 1)) = t * r := by
        unfold t r
        rw [← Nat.pow_add]
        congr 1
        omega
      have htq : q ≤ t * (q + 1) := by
        calc
          q ≤ q + 1 := Nat.le_succ _
          _ = 1 * (q + 1) := (Nat.one_mul _).symm
          _ ≤ _ := Nat.mul_le_mul_right _ ht
      have htr : t * (q + 1) ≤ (t * (q + 1)) * r := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (t * (q + 1)) hr
      have hdifference : (t * r * (q + 1) - q) - (t * (q + 1) - q) =
          (t * (q + 1)) * (r - 1) := by
        rw [show t * r * (q + 1) = t * (q + 1) * r by ac_rfl]
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        omega
      have hweights : (2 : ℕ) ^ (h - 1) = t * 2 ^ (v - 1 - 1) := by
        unfold t
        rw [← Nat.pow_add]
        congr 1
        omega
      have hscale : q * 2 ^ (h - 1) ≤ (t * (q + 1)) * (2 ^ (v - 1) - 1) := by
        rw [hweights]
        calc
          q * (t * 2 ^ (v - 1 - 1)) = (t * q) * 2 ^ (v - 1 - 1) := by ac_rfl
          _ ≤ (t * (q + 1)) * 2 ^ (v - 1 - 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
          _ ≤ _ := Nat.mul_le_mul_left _ (power_half_le_weight hb)
      have hre : (2 : ℕ) ^ (v - u - 1) - 1 ≤ r - 1 := by
        exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega)) _
      change q * 2 ^ (h - 1) * (2 ^ (v - u - 1) - 1) ≤
        ((2 ^ (h - (u - 1)) * (q + 1) - q) - (t * (q + 1) - q)) *
          (2 ^ (v - 1) - 1)
      rw [hpr, hdifference]
      calc
        q * 2 ^ (h - 1) * (2 ^ (v - u - 1) - 1) ≤
            ((t * (q + 1)) * (2 ^ (v - 1) - 1)) * (r - 1) :=
          Nat.mul_le_mul hscale hre
        _ = _ := by ac_rfl

theorem game_lower (value weight : ℕ → ℕ) (L k d bound : ℕ)
    (hk : 1 ≤ k)
    (hgap : ∀ P : Finset ℕ, P ⊆ Finset.range L → P.card + 1 ≤ k →
      ∃ u v : ℕ, u ≤ v ∧ v < L ∧ d ≤ v - u ∧
        ∀ w ∈ P, ¬ (u < w ∧ w ≤ v))
    (hcost : ∀ u v : ℕ, u ≤ v → v < L → d ≤ v - u →
      bound ≤ (value u - value v) * weight v) :
    bound ≤ WithTop.untopD 0
      (((Finset.range L).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ k)).image
        (fun P : Finset ℕ =>
          ((Finset.range L ×ˢ Finset.range L).filter
            (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧
              ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup
            (fun uv => (value uv.1 - value uv.2) * weight uv.2))).min := by
  let placements := (Finset.range L).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ k)
  let intervals (P : Finset ℕ) :=
    (Finset.range L ×ˢ Finset.range L).filter (fun uv : ℕ × ℕ =>
      uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))
  let cost (uv : ℕ × ℕ) := (value uv.1 - value uv.2) * weight uv.2
  let score (P : Finset ℕ) := (intervals P).sup cost
  let scores := placements.image score
  have hempty : (∅ : Finset ℕ) ∈ placements := by
    simpa [placements] using (show 0 < k from hk)
  have hNonempty : scores.Nonempty :=
    ⟨score ∅, Finset.mem_image.mpr ⟨∅, hempty, rfl⟩⟩
  obtain ⟨best, hbest⟩ := Finset.min_of_nonempty hNonempty
  obtain ⟨P, hP, hscore⟩ : ∃ P ∈ placements, score P = best :=
    Finset.mem_image.mp (Finset.mem_of_min hbest)
  obtain ⟨hsub, hcard⟩ : P ⊆ Finset.range L ∧ P.card + 1 ≤ k := by
    simpa only [placements, Finset.mem_filter, Finset.mem_powerset] using hP
  obtain ⟨u, v, huv, hv, hd, hfree⟩ := hgap P hsub hcard
  have hu : u < L := huv.trans_lt hv
  have hpair : (u, v) ∈ intervals P := by
    simp only [intervals, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hu, hv⟩, huv, hfree⟩
  have hscore_lower : bound ≤ score P :=
    (hcost u v huv hv hd).trans (Finset.le_sup (f := cost) hpair)
  change bound ≤ WithTop.untopD 0 scores.min
  rw [hbest, WithTop.untopD_coe, ← hscore]
  exact hscore_lower

end PEqualNP.Outside.L_meta_1349_aux

open PEqualNP.Outside.L_meta_1349_aux

theorem PEqualNP.Outside.L_meta_1349 :
    ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  let d := (h + 3 + 2 ^ t - 1) / 2 ^ t - 1
  have hk : 1 ≤ (2 : ℕ) ^ t := Nat.one_le_pow t 2 (by decide)
  apply game_lower (levelValue h) (endWeight h) (h + 3) (2 ^ t) d _ hk
  · intro P _ hP
    exact gap_exists (by omega) hk P hP
  · intro u v huv hv hd
    have hexp : d - 1 ≤ v - u - 1 := Nat.sub_le_sub_right hd 1
    have hpow : (2 : ℕ) ^ (d - 1) ≤ 2 ^ (v - u - 1) :=
      Nat.pow_le_pow_right (by decide) hexp
    exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hpow 1)).trans
      (cost_lower hh huv hv)
