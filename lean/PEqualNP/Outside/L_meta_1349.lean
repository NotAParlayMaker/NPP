import Mathlib
import PEqualNP.Defs
namespace Ladder1349
open Finset
theorem wide (n r k : ℕ) (P : Finset ℕ) (hp : P.card < r) (hk : r*k<n) :
    ∃ u v : ℕ, u ≤ v ∧ v<n ∧ k≤v-u ∧ ∀ w∈P, ¬(u<w ∧ w≤v) := by
  classical
  let f := fun x : ℕ => (P.filter (·≤x)).card
  have hf : ∀ x∈range n, f x ∈ range r := fun x _ => mem_range.mpr
    (lt_of_le_of_lt (card_filter_le _ _) hp)
  obtain ⟨y,_,hy⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf
    (by simpa using hk : (range r).card*k < (range n).card)
  let S := (range n).filter (fun i => f i = y)
  change k < S.card at hy
  have hs : S.Nonempty := card_pos.mp (by omega)
  let u := S.min' hs
  let v := S.max' hs
  have hu : u∈S := min'_mem _ _
  have hv : v∈S := max'_mem _ _
  have huv : u≤v := min'_le _ _ hv
  have sub : S ⊆ Icc u v := fun x hx => mem_Icc.mpr ⟨min'_le _ _ hx, le_max' _ _ hx⟩
  have len := card_le_card sub
  rw [Nat.card_Icc] at len
  refine ⟨u,v,huv,mem_range.mp (mem_filter.mp hv).1,by omega,?_⟩
  intro w hw hwuv
  have lt : P.filter (·≤u) ⊂ P.filter (·≤v) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨(fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1, le_trans (mem_filter.mp hx).2 huv⟩), ?_⟩
    intro eq
    have : w ∈ P.filter (·≤u) := eq ▸ mem_filter.mpr ⟨hw,hwuv.2⟩
    exact (not_lt_of_ge (mem_filter.mp this).2) hwuv.1
  have hlt : f u < f v := card_lt_card lt
  have eu := (mem_filter.mp hu).2
  have ev := (mem_filter.mp hv).2
  omega
end Ladder1349
namespace Ladder1349
def height (h v : ℕ) :=
  if v=0 then 2^h*2^h+2^h+1 else if v=h+2 then 0 else
  2^h*(2^h+1)/2^(v-1)-2^h
def weight (h v : ℕ) := if v=h+2 then 2^h else 2^(v-1)-1

theorem inner (h i j : ℕ) (ij : i ≤ j) (jh : j≤h) (hj : 1≤j) :
  (2^h*2^h/2)*(2^(j-i)-1) ≤
    ((2^h*(2^h+1)/2^i-2^h)-(2^h*(2^h+1)/2^j-2^h))*(2^j-1) := by
  let q := 2^h
  let a := 2^(h-j)
  let b := 2^j
  let c := 2^(j-i)
  have hab : a*b=q := by dsimp [a,b,q]; rw [←pow_add]; congr 1; omega
  have hbc : c*2^i=b := by dsimp [c,b]; rw [←pow_add]; congr 1; omega
  have hb : 2≤b := by exact Nat.pow_le_pow_right (by decide : 0<2) hj
  have ha : 1≤a := Nat.one_le_pow _ _ (by decide)
  have hc : 1≤c := Nat.one_le_pow _ _ (by decide)
  have divb : q*(q+1)/b=a*(q+1) := by
    conv_lhs => lhs; lhs; rw [←hab]
    rw [mul_right_comm, Nat.mul_div_cancel _ (by omega)]
  have divi : q*(q+1)/2^i=(a*(q+1))*c := by
    have e : q*(q+1)=(a*(q+1)*c)*2^i := by
      calc
        _ = (a*b)*(q+1) := by rw [hab]
        _ = _ := by rw [←hbc]; ring
    rw [e, Nat.mul_div_cancel _ (by positivity)]
  change q*q/2*(c-1) ≤ ((q*(q+1)/2^i-q)-(q*(q+1)/b-q))*(b-1)
  rw [divi,divb]
  have hl : q ≤ a*(q+1) := by nlinarith
  have sub : a*(q+1)*c-q-(a*(q+1)-q) = a*(q+1)*(c-1) := by
    rw [Nat.mul_sub, Nat.mul_one]
    omega
  rw [sub, mul_right_comm]
  apply Nat.mul_le_mul_right
  have b2 : b ≤ (b-1)*2 := by omega
  have base := Nat.mul_le_mul_left (a*(q+1)) b2
  have eq : a*(q+1)*b=q*(q+1) := by rw [mul_right_comm,hab]
  rw [eq] at base
  have two : a*(q+1)*((b-1)*2)=a*(q+1)*(b-1)*2 := by ring
  rw [two] at base
  have : q*q ≤ q*(q+1) := by nlinarith
  omega
theorem interval (h u v : ℕ) (hh : 1≤h) (huv : u≤v) (hv : v<h+3) :
    (2^h*2^h/2)*(2^(v-u-1)-1) ≤ (height h u-height h v)*weight h v := by
  by_cases near : v≤u+1
  · simp [show v-u-1=0 by omega]
  by_cases ends : u=0 ∧ v=h+2
  · obtain ⟨rfl,rfl⟩ := ends
    simp only [Nat.sub_zero, show h+2-1=h+1 by omega,pow_succ,height,weight,
      show h+2≠0 by omega,ite_false]
    have := Nat.div_mul_le_self (2^h*2^h) 2
    calc
      _ ≤ (2^h*2^h/2)*(2^h*2) := Nat.mul_le_mul_left _ (Nat.sub_le ..)
      _ = (2^h*2^h/2*2)*2^h := by ring
      _ ≤ (2^h*2^h+2^h+1)*2^h := Nat.mul_le_mul_right _ ((Nat.div_mul_le_self _ _).trans (Nat.le_add_right _ _ |>.trans (Nat.le_succ _)))
  let i := u-1
  let j := min (v-1) h
  have hj : 1≤j := by dsimp [j]; omega
  have jh : j≤h := min_le_right .. 
  have ij : i≤j := by dsimp [i,j]; omega
  have e : v-u-1≤j-i := by dsimp [i,j]; omega
  have hu : 2^h*(2^h+1)/2^i-2^h ≤ height h u := by
    unfold height
    split_ifs with hx hx
    · simp only [i,hx,Nat.zero_sub,pow_zero,Nat.div_one]; exact (Nat.sub_le ..).trans (by rw [Nat.mul_add]; simp)
    · omega
    · rfl
  have hv' : height h v ≤ 2^h*(2^h+1)/2^j-2^h := by
    by_cases last : v=h+2
    · simp [height,last]
    · have eq : j=v-1 := min_eq_left (by omega)
      simp [height,show v≠0 by omega,last,eq]
  have hw : 2^j-1≤weight h v := by
    unfold weight
    split_ifs
    · exact (Nat.sub_le ..).trans (Nat.pow_le_pow_right (by decide) jh)
    · exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (min_le_left ..)) 1
  exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) e) 1)).trans
    ((inner h i j ij jh hj).trans (Nat.mul_le_mul (tsub_le_tsub hu hv') hw))
end Ladder1349
open Finset Ladder1349
theorem PEqualNP.Outside.L_meta_1349 : ∀ h t : ℕ, 1 ≤ h → (2 ^ h * 2 ^ h / 2) * (2 ^ ((h + 3 + 2 ^ t - 1) / 2 ^ t - 1 - 1) - 1) ≤ (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.1 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.1 - 1) - 2 ^ h) - (if uv.2 = 0 then (2 ^ h * 2 ^ h + 2 ^ h + 1) else if uv.2 = h + 2 then 0 else 2 ^ h * (2 ^ h + 1) / 2 ^ (uv.2 - 1) - 2 ^ h)) * (if uv.2 = h + 2 then 2 ^ h else 2 ^ (uv.2 - 1) - 1)))).min)
 := by
  intro h t hh
  classical
  let n := h+3
  let r := 2^t
  let k := (n+r-1)/r-1
  let Ps := (range n).powerset.filter (fun P => P.card+1≤r)
  let pairs := fun P : Finset ℕ => (range n ×ˢ range n).filter
    (fun uv => uv.1≤uv.2 ∧ ∀ w∈P, ¬(uv.1<w ∧ w≤uv.2))
  let val := fun P => (pairs P).sup (fun uv => (height h uv.1-height h uv.2)*weight h uv.2)
  let A := Ps.image val
  change (2^h*2^h/2)*(2^(k-1)-1) ≤ A.min.untopD 0
  have hr : 0<r := by dsimp [r]; positivity
  have hn : 0<n := by dsimp [n]; omega
  have hemi : ∅ ∈ Ps := by simp [Ps]; omega
  have ha : A.Nonempty := ⟨_,mem_image_of_mem val hemi⟩
  rw [← coe_min' ha, WithTop.untopD_coe]
  obtain ⟨P,hP,heq⟩ := mem_image.mp (min'_mem A ha)
  rw [←heq]
  have hp := (mem_filter.mp hP).2
  have hk : r*k<n := by
    dsimp [k]
    rw [show n+r-1=n-1+r by omega, Nat.add_div_right _ hr]
    simpa using lt_of_le_of_lt (Nat.mul_div_le (n-1) r) (show n-1<n by omega)
  obtain ⟨u,v,huv,hv,hk',hcut⟩ := wide n r k P (by omega) hk
  have hm : (u,v)∈pairs P := mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_range.mpr (lt_of_le_of_lt huv hv),mem_range.mpr hv⟩,huv,hcut⟩
  exact (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide)
    (Nat.sub_le_sub_right hk' 1)) 1)).trans ((interval h u v hh huv hv).trans (le_sup (f := fun uv : ℕ × ℕ => (height h uv.1-height h uv.2)*weight h uv.2) hm))
