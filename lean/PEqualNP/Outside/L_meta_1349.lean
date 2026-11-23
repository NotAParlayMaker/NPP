import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1349_aux

-- Classify each level by the number of cuts at or before it.
-- Equal classes have no cut strictly after the first endpoint and at or
-- before the second. The largest class contains the required long interval.
theorem interval (M K : ℕ) (pos : 0 < M) (P : Finset ℕ)
    (budget : P.card+1 ≤ K) :
    ∃ u v, u < M ∧ v < M ∧ u ≤ v ∧ (M-1)/K ≤ v-u ∧
      ∀ w ∈ P, ¬(u < w ∧ w ≤ v) := by
  let cutsThrough (i : ℕ) := P.filter (· ≤ i)
  let label (i : ℕ) := (cutsThrough i).card
  have maps (i) (_ : i ∈ Finset.range M) : label i ∈ Finset.range K := by
    have h := Finset.card_filter_le P (· ≤ i)
    change (P.filter (· ≤ i)).card ∈ Finset.range K
    exact Finset.mem_range.mpr (by omega)
  have cap : (Finset.range K).card * ((M-1)/K) < (Finset.range M).card := by
    simp only [Finset.card_range]
    have h := Nat.div_mul_le_self (M-1) K
    rw [Nat.mul_comm] at h
    omega
  obtain ⟨j,_,large⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to maps cap
  let F := (Finset.range M).filter (fun i => label i = j)
  change (M-1)/K < F.card at large
  have nonempty : F.Nonempty := Finset.card_pos.mp ((Nat.zero_le _).trans_lt large)
  let u := F.min' nonempty
  let v := F.max' nonempty
  have hu : u ∈ F := F.min'_mem nonempty
  have hv : v ∈ F := F.max'_mem nonempty
  have a := Finset.mem_filter.mp hu
  have b := Finset.mem_filter.mp hv
  have uv : u ≤ v := F.min'_le v hv
  have sub : F ⊆ Finset.Icc u v := fun i hi => Finset.mem_Icc.mpr ⟨F.min'_le i hi,F.le_max' i hi⟩
  have count := Finset.card_le_card sub
  rw [Nat.card_Icc] at count
  refine ⟨u,v,Finset.mem_range.mp a.1,Finset.mem_range.mp b.1,uv,by omega,?_⟩
  rintro w hw ⟨uw,wv⟩
  have incl : cutsThrough u ⊆ cutsThrough v := fun i hi =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,((Finset.mem_filter.mp hi).2).trans uv⟩
  have strict : cutsThrough u ⊂ cutsThrough v := (Finset.ssubset_iff_of_subset incl).mpr
    ⟨w,Finset.mem_filter.mpr ⟨hw,wv⟩,fun h => (Nat.not_le_of_gt uw) (Finset.mem_filter.mp h).2⟩
  exact (Finset.card_lt_card strict).ne (a.2.trans b.2.symm)

def level (h i : ℕ) : ℕ :=
  if i = 0 then 2^h*2^h+2^h+1 else if i = h+2 then 0 else 2^h*(2^h+1)/2^(i-1)-2^h

def weight (h i : ℕ) : ℕ := if i = h+2 then 2^h else 2^(i-1)-1

def score (h : ℕ) (uv : ℕ × ℕ) : ℕ := (level h uv.1 - level h uv.2) * weight h uv.2

theorem factor (h j : ℕ) (hj : j ≤ h) :
    2^h*(2^h+1)/2^j = 2^(h-j)*(2^h+1) := by
  have eq : (2^(h-j)*(2^h+1))*2^j = 2^h*(2^h+1) := by
    calc
      _ = (2^(h-j)*2^j)*(2^h+1) := by ring
      _ = _ := by rw [Nat.pow_sub_mul_pow 2 hj]
  rw [← eq,Nat.mul_div_cancel _ (by positivity)]

theorem first_bound (h u : ℕ) (hu : u ≤ h+1) :
    2^(h-(u-1))*(2^h+1)-2^h ≤ level h u := by
  by_cases hz : u = 0
  · subst u
    change 2^(h-(0-1))*(2^h+1)-2^h ≤ 2^h*2^h+2^h+1
    simp only [Nat.zero_sub,Nat.sub_zero]
    calc
      _ ≤ 2^h*(2^h+1) := Nat.sub_le _ _
      _ = 2^h*2^h+2^h := by ring
      _ ≤ _ := Nat.le_succ _
  · simp [level,hz,show u ≠ h+2 by omega,factor h (u-1) (by omega)]

-- Inside the ladder, raising the level divides its height term by two
-- while doubling the multiplier. We keep the exact factors until the
-- final inequality so natural subtraction and division introduce no error.
theorem interior (h u v : ℕ) (uv : u ≤ v) (vh : v ≤ h+1) (big : 1 < v-u) :
    2^h*2^h/2 * (2^(v-u-1)-1) ≤ score h (u,v) := by
  let q := 2^h
  let a := u-1
  let b := v-1
  let X := 2^(h-b)*(q+1)
  let B := 2^b
  let K := 2^(b-a)
  have ab : a ≤ b := by dsimp [a,b]; omega
  have bh : b ≤ h := by dsimp [b]; omega
  have xpos : 1 ≤ 2^(h-b) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have kpos : 1 ≤ K := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have qx : q ≤ X := by
    have z := Nat.mul_le_mul_right (q+1) xpos
    simpa [X] using (show q ≤ 2^(h-b)*(q+1) by omega)
  have hx : K*X = 2^(h-a)*(q+1) := by
    dsimp [K,X]
    rw [← Nat.mul_assoc,← pow_add,show b-a+(h-b) = h-a by omega]
  have lo : K*X-q ≤ level h u := by rw [hx]; exact first_bound h u (by omega)
  have lv : level h v = X-q := by
    simp [level,show v ≠ 0 by omega,show v ≠ h+2 by omega,X,b,q,factor h (v-1) (by omega)]
  have mx : X ≤ K*X := by simpa using Nat.mul_le_mul_right X kpos
  have diff : (K-1)*X ≤ level h u - level h v := by
    rw [lv,Nat.sub_mul,Nat.one_mul]
    omega
  have prod : X*B = q*(q+1) := by
    calc
      _ = (2^(h-b)*2^b)*(q+1) := by dsimp [X,B]; ring
      _ = _ := by rw [Nat.pow_sub_mul_pow 2 bh]
  have bbig : 2 ≤ B := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ b by dsimp [b]; omega)
  have qb : q*q/2 ≤ X*(B-1) := by
    have qle : q*q ≤ X*B := by rw [prod]; exact Nat.mul_le_mul_left _ (by omega)
    have z := Nat.mul_le_mul_left X (show B ≤ 2*(B-1) by omega)
    rw [show X*(2*(B-1)) = 2*(X*(B-1)) by ring] at z
    omega
  have ex : 2^(v-u-1)-1 ≤ K-1 := Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (by decide) (show v-u-1 ≤ b-a by dsimp [a,b]; omega)) 1
  have w : weight h v = B-1 := by simp [weight,B,b,show v ≠ h+2 by omega]
  calc
    _ ≤ (X*(B-1))*(K-1) := Nat.mul_le_mul qb ex
    _ = ((K-1)*X)*(B-1) := by ring
    _ ≤ score h (u,v) := by
      change _ ≤ (level h u - level h v)*weight h v
      rw [w]
      exact Nat.mul_le_mul_right _ diff

theorem terminal (h u : ℕ) (hu : u ≤ h+1) :
    2^h*2^h/2 * (2^(h+2-u-1)-1) ≤ score h (u,h+2) := by
  let q := 2^h
  have last : level h (h+2) = 0 := by simp [level]
  change q*q/2 * (2^(h+2-u-1)-1) ≤ (level h u-level h (h+2))*weight h (h+2)
  rw [last,Nat.sub_zero,show weight h (h+2) = q by simp [weight,q]]
  by_cases uz : u = 0
  · subst u
    have ex : 2^(h+2-0-1) = 2*q := by rw [show h+2-0-1 = h+1 by omega,pow_succ]; exact Nat.mul_comm _ _
    rw [ex,show level h 0 = q*q+q+1 by simp [level,q]]
    calc
      _ ≤ (q*q/2)*(2*q) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = ((q*q/2)*2)*q := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by have z := Nat.div_mul_le_self (q*q) 2; omega)
  · let A := 2^(h-(u-1))
    have ap : 1 ≤ A := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have ex : h+2-u-1 = h-(u-1) := by omega
    have lo : A*(q+1)-q ≤ level h u := first_bound h u hu
    have saving : q*(A-1) ≤ level h u := by
      rw [Nat.mul_sub,Nat.mul_one]
      have eq : A*(q+1) = q*A+A := by ring
      omega
    rw [ex]
    calc
      _ ≤ (q*q)*(A-1) := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
      _ = (q*(A-1))*q := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ saving

theorem span (h u v : ℕ) (uv : u ≤ v) (vh : v < h+3) :
    2^h*2^h/2 * (2^(v-u-1)-1) ≤ score h (u,v) := by
  by_cases small : v-u ≤ 1
  · simp [show v-u-1=0 by omega]
  by_cases last : v = h+2
  · subst v
    exact terminal h u (by omega)
  exact interior h u v uv (by omega) (by omega)

def runs (h : ℕ) (P : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (h+3)) ×ˢ (Finset.range (h+3))).filter fun uv =>
    uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬(uv.1 < w ∧ w ≤ uv.2)

def boards (h K : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (h+3)).powerset.filter fun P => P.card+1 ≤ K

theorem game (h t : ℕ) :
    (2^h*2^h/2)*(2^((h+3+2^t-1)/2^t-1-1)-1) ≤
      WithTop.untopD 0 (((boards h (2^t)).image (fun P => (runs h P).sup (score h))).min) := by
  let K := 2^t
  have hk : 0 < K := by dsimp [K]; positivity
  have bnon : (boards h K).Nonempty := ⟨∅,by simp [boards]; omega⟩
  let values := (boards h K).image (fun P => (runs h P).sup (score h))
  have non : values.Nonempty := bnon.image _
  change _ ≤ WithTop.untopD 0 values.min
  rw [← Finset.coe_min' non,WithTop.untopD_coe]
  obtain ⟨P,hP,eq⟩ := Finset.mem_image.mp (values.min'_mem non)
  rw [← eq]
  have budget := (Finset.mem_filter.mp hP).2
  obtain ⟨u,v,hu,hv,ord,gap,good⟩ := interval (h+3) K (by omega) P budget
  have inside : (u,v) ∈ runs h P := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hu,Finset.mem_range.mpr hv⟩,ord,good⟩
  have ceil : (h+3+K-1)/K-1 = (h+3-1)/K := by
    rw [show h+3+K-1 = (h+3-1)+K by omega,Nat.add_div_right _ hk]
    exact Nat.add_sub_cancel _ _
  change (2^h*2^h/2)*(2^((h+3+K-1)/K-1-1)-1) ≤ _
  rw [ceil]
  have ep := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le_sub_right gap 1)
  exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right ep 1)).trans
    ((span h u v ord hv).trans (Finset.le_sup (f := score h) inside))

end PEqualNP.Outside.L_meta_1349_aux

theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min) := by
  intro h t _
  exact PEqualNP.Outside.L_meta_1349_aux.game h t
