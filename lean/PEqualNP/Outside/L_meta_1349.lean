import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349_aux

lemma long_run (h t : ℕ) (P : Finset ℕ) (_hP : P ⊆ Finset.range (h + 3))
    (hcard : P.card + 1 ≤ 2 ^ t) :
    ∃ a b : ℕ, a ≤ b ∧ b < h + 3 ∧
      (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 ≤ b - a ∧
      ∀ w ∈ P, ¬ (a < w ∧ w ≤ b) := by
  classical
  let k := 2 ^ t
  let d := (h + 2) / k
  have hk : 0 < k := by dsimp [k]; positivity
  have hd : (h + 3 + 2 ^ t - 1) / 2 ^ t - 1 = d := by
    change (h + 3 + k - 1) / k - 1 = (h + 2) / k
    rw [show h + 3 + k - 1 = h + 2 + k by omega, Nat.add_div_right _ hk]
    exact Nat.add_sub_cancel _ _
  have hbound : k * d ≤ h + 2 := by
    simpa [d, Nat.mul_comm] using Nat.div_mul_le_self (h + 2) k
  by_contra noInterval
  have blocked (i : Fin k) : ∃ w ∈ P, i.val * d < w ∧ w ≤ (i.val + 1) * d := by
    by_contra noWitness
    apply noInterval
    have hi : (i.val + 1) * d ≤ k * d := Nat.mul_le_mul_right d i.isLt
    refine ⟨i.val * d, (i.val + 1) * d, ?_, by omega, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]
      omega
    · rw [hd, Nat.add_mul, Nat.one_mul]
      omega
    · intro w hw location
      exact noWitness ⟨w, hw, location⟩
  choose point hmem hloc using blocked
  let f (i : Fin k) : P := ⟨point i, hmem i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have he : point i = point j := congrArg Subtype.val hij
    have uniqueOrder (a b : Fin k) (eqPoint : point a = point b) : ¬ a.val < b.val := by
      intro hab
      have hs : (a.val + 1) * d ≤ b.val * d := Nat.mul_le_mul_right d hab
      have ha := (hloc a).2
      have hb := (hloc b).1
      omega
    apply Fin.ext
    have h₁ := uniqueOrder i j he
    have h₂ := uniqueOrder j i he.symm
    omega
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  change P.card + 1 ≤ k at hcard
  omega

def levelValue (h i : ℕ) : ℕ :=
  if i = 0 then 2 ^ h * 2 ^ h + 2 ^ h + 1
  else if i = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (i - 1) - 2 ^ h

def levelWeight (h i : ℕ) : ℕ :=
  if i = h + 2 then 2 ^ h else 2 ^ (i - 1) - 1

private lemma power_split (h x : ℕ) (hx : x ≤ h) :
    2 ^ (h-x) * 2 ^ x = (2:ℕ)^h := by
  rw [← pow_add, Nat.sub_add_cancel hx]

private lemma divided (h x : ℕ) (hx : x ≤ h) :
    2^h * (2^h+1) / 2^x = 2^(h-x) * (2^h+1) := by
  have he : 2^h * (2^h+1) = (2^(h-x) * (2^h+1)) * 2^x := by
    calc
      _ = (2^(h-x) * 2^x) * (2^h+1) := by rw [power_split h x hx]
      _ = _ := by ring
  rw [he, Nat.mul_div_cancel _ (by positivity)]

private lemma value_floor (h i : ℕ) (hi : i ≤ h+1) :
    2^(h-(i-1)) * (2^h+1) - 2^h ≤ levelValue h i := by
  by_cases hz : i = 0
  · subst i
    simp only [levelValue, ↓reduceIte, Nat.zero_sub, Nat.sub_zero]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
    exact Nat.le_succ_of_le (Nat.le_add_right _ _)
  · simp [levelValue, hz, show i ≠ h+2 by omega, divided h (i-1) (by omega)]

private lemma interior_interval (h a b : ℕ) (gap : a+2 ≤ b) (hb : b ≤ h+1) :
    (2^h*2^h/2) * (2^(b-a-1)-1) ≤
      (levelValue h a - levelValue h b) * levelWeight h b := by
  let q : ℕ := 2 ^ h
  let B : ℕ := 2 ^ (b-1)
  let K : ℕ := 2 ^ (h-(b-1))
  let R : ℕ := 2 ^ ((b-1)-(a-1))
  have hKB : K*B=q := power_split h (b-1) (by omega)
  have hk : 1 ≤ K := Nat.one_le_pow _ _ (by decide)
  have hb2 : 2 ≤ B := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ b-1 by omega)
  have hr : 1 ≤ R := Nat.one_le_pow _ _ (by decide)
  have hC : q ≤ K*(q+1) := by nlinarith
  have hrExp : K*R = 2^(h-(a-1)) := by
    dsimp [K,R]
    rw [← pow_add]
    congr 1
    omega
  have hva : K*(q+1)*R-q ≤ levelValue h a := by
    have eq : K*(q+1)*R=2^(h-(a-1))*(q+1) := by rw [← hrExp]; ring
    rw [eq]
    exact value_floor h a (by omega)
  have hvb : levelValue h b=K*(q+1)-q := by
    simp [levelValue, show b ≠ 0 by omega, show b ≠ h+2 by omega,
      divided h (b-1) (by omega), K, q]
  have hdiff : K*(q+1)*(R-1) ≤ levelValue h a - levelValue h b := by
    have add := Nat.add_sub_of_le hC
    have prod : K*(q+1) ≤ K*(q+1)*R := by
      simpa using Nat.mul_le_mul_left (K*(q+1)) hr
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, hvb]
    omega
  have hw : levelWeight h b=B-1 := by simp [levelWeight, B, show b ≠ h+2 by omega]
  have hhalf : q*q/2 ≤ K*(q+1)*(B-1) := by
    have htwice : q*q ≤ 2*(K*(q+1)*(B-1)) := by
      calc
        q*q = (K*q)*B := by calc
          _ = (K*B)*q := by rw [hKB]
          _ = _ := by ring
        _ ≤ (K*q)*(2*(B-1)) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 2*(K*(q+1)*(B-1)) := by nlinarith
    omega
  have hsmall : 2^(b-a-1) ≤ R := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show b-a-1 ≤ (b-1)-(a-1) by omega)
  change (q*q/2)*(2^(b-a-1)-1) ≤ _
  rw [hw]
  calc
    _ ≤ (K*(q+1)*(B-1))*(R-1) := Nat.mul_le_mul hhalf (Nat.sub_le_sub_right hsmall 1)
    _ = (K*(q+1)*(R-1))*(B-1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hdiff

lemma interval_lower (h a b : ℕ) (hh : 1 ≤ h) (hab : a ≤ b) (hb : b ≤ h+2) :
    (2^h*2^h/2) * (2^(b-a-1)-1) ≤
      (levelValue h a - levelValue h b) * levelWeight h b := by
  by_cases gap : a+2 ≤ b
  · by_cases top : b = h+2
    · subst b
      let q : ℕ := 2^h
      have ht : levelValue h (h+2) = 0 := by simp [levelValue]
      rw [ht, Nat.sub_zero, show levelWeight h (h+2) = q by simp [levelWeight,q]]
      by_cases hz : a = 0
      · subst a
        simp only [Nat.sub_zero]
        rw [show h+2-1=h+1 by omega, pow_succ, show levelValue h 0=q*q+q+1 by simp [levelValue,q]]
        change (q*q/2)*(q*2-1) ≤ (q*q+q+1)*q
        calc
          _ ≤ (q*q/2)*(q*2) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = (q*q/2*2)*q := by ring
          _ ≤ (q*q)*q := Nat.mul_le_mul_right q (Nat.div_mul_le_self _ _)
          _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ_of_le (Nat.le_add_right _ _))
      · let K : ℕ := 2^(h-(a-1))
        have he : h+2-a-1=h-(a-1) := by omega
        rw [he]
        change (q*q/2)*(K-1) ≤ levelValue h a * q
        have hval := value_floor h a (by omega)
        have hmul : q*(K-1) ≤ levelValue h a := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          change K*(q+1)-q ≤ levelValue h a at hval
          have : q*K ≤ K*(q+1) := by nlinarith
          omega
        calc
          _ ≤ (q*q)*(K-1) := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
          _ = (q*(K-1))*q := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ hmul
    · exact interior_interval h a b gap (by omega)
  · simp [show b-a-1=0 by omega]

end PEqualNP.Outside.L_meta_1349_aux

open PEqualNP.Outside.L_meta_1349_aux

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t hh
  let cuts := (Finset.range (h + 3)).powerset.filter fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t
  let runs (P : Finset ℕ) := (Finset.range (h+3) ×ˢ Finset.range (h+3)).filter
    fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)
  let payoff (uv : ℕ × ℕ) := (levelValue h uv.1 - levelValue h uv.2) * levelWeight h uv.2
  let scores := cuts.image fun P => (runs P).sup payoff
  change _ ≤ WithTop.untopD 0 scores.min
  have he : (∅ : Finset ℕ) ∈ cuts := by simp [cuts]
  have hne : scores.Nonempty := ⟨(runs ∅).sup payoff, Finset.mem_image.mpr ⟨∅, he, rfl⟩⟩
  obtain ⟨v, hv⟩ := Finset.min_of_nonempty hne
  rw [hv, WithTop.untopD_coe]
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_min hv)
  obtain ⟨hsub, hcard⟩ := Finset.mem_filter.mp hP
  obtain ⟨a, b, hab, hb, hlong, hclear⟩ :=
    long_run h t P (Finset.mem_powerset.mp hsub) hcard
  have hmem : (a,b) ∈ runs P := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt hab hb), Finset.mem_range.mpr hb⟩, hab, hclear⟩
  have hpow : (2 : ℕ)^((h+3+2^t-1)/2^t-1-1) ≤ 2^(b-a-1) :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hlong 1)
  exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hpow 1)).trans
    ((interval_lower h a b hh hab (by omega)).trans (Finset.le_sup (f := payoff) hmem))
