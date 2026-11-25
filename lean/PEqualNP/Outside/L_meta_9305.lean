import Mathlib
import PEqualNP.Defs

-- There are 117 zero cells and each zero rectangle has area at most 12. Ten rectangles could overcount at most three cells. The displayed inverse certificate shows that even these overlaps leave the coverage matrix injective.

namespace PEqualNP.Outside.L_meta_9305
open Finset
abbrev I := Fin 13
def rows : List ℕ := [5137,2083,4166,141,282,564,1128,2256,4512,833,1666,3332,6664]
def zeroCell (i j : I) : Bool := !((rows.getD i.val 0).testBit j.val)
def colSet (i : I) := Finset.univ.filter (fun j : I => zeroCell i j)
def A (i j : I) : ℕ := (zeroCell i j).toNat
def coeff (j i : I) : ℚ := if zeroCell i j then 1 else -2


def areaCheck : List I → ℕ → Finset I → Bool
  | [], k, cols => decide (k * cols.card ≤ 12)
  | i::rest, k, cols =>
    decide ((k+rest.length+1)*cols.card ≤ 12) ||
      (areaCheck rest k cols && areaCheck rest (k+1) (cols ∩ colSet i))

theorem areaSound (R C : Finset I) (ok : ∀ i ∈ R, C ⊆ colSet i) (rs : List I)
    (k : ℕ) (cols : Finset I) (sub : C ⊆ cols) (good : areaCheck rs k cols = true) :
    (k+(rs.filter fun i => i ∈ R).length)*C.card ≤ 12 := by
  induction rs generalizing k cols with
  | nil =>
    simp only [areaCheck,decide_eq_true_eq] at good
    simpa using (Nat.mul_le_mul_left k (card_le_card sub)).trans good
  | cons i rs ih =>
    simp only [areaCheck,Bool.or_eq_true,decide_eq_true_eq,Bool.and_eq_true] at good
    rcases good with done | ⟨skip,take⟩
    · have le := List.length_filter_le (fun i : I => decide (i ∈ R)) (i::rs)
      have len : (i::rs).length = rs.length+1 := rfl
      exact (Nat.mul_le_mul (by omega) (card_le_card sub)).trans done
    · by_cases hi : i ∈ R
      · have next := ih (k+1) (cols ∩ colSet i) (Finset.subset_inter sub (ok i hi)) take
        simpa [List.filter_cons,hi,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
      · simpa [List.filter_cons,hi] using ih k cols sub skip

set_option maxRecDepth 100000 in
theorem areaVerified : areaCheck (List.finRange 13) 0 univ = true := by decide +kernel

theorem area (R C : Finset I) (ok : ∀ i ∈ R, C ⊆ colSet i) : R.card*C.card ≤ 12 := by
  have valid := areaSound R C ok (List.finRange 13) 0 univ (Finset.subset_univ _) areaVerified
  let selected := (List.finRange 13).filter (fun i : I => i ∈ R)
  have same : selected.toFinset = R := by ext i; simp [selected]
  have nodup : selected.Nodup := (List.nodup_finRange 13).filter _
  rw [←same,List.toFinset_card_of_nodup nodup]
  simpa only [Nat.zero_add] using valid

set_option maxRecDepth 100000 in
theorem weight : ∑ i : I, ∑ j : I, A i j = 117 := by decide +kernel
set_option maxRecDepth 100000 in
theorem inverse : ∀ u j : I, ∑ i : I, coeff u i * (A i j : ℚ) =
    if u=j then 9 else 0 := by decide +kernel
theorem smallCoeff (u i : I) : |coeff u i| ≤ 2 := by
  unfold coeff
  split <;> norm_num
end PEqualNP.Outside.L_meta_9305

namespace PEqualNP.Outside.L_meta_9305
open Finset
theorem stable {n : ℕ} [NeZero n]
    (A E : Fin n → Fin n → ℕ) (K : Fin n → Fin n → ℚ)
    (inv : ∀ u j, ∑ i, K u i * (A i j : ℚ) = if u=j then 9 else 0)
    (coeff : ∀ u i, |K u i| ≤ 2) (err : ∑ i, ∑ j, E i j ≤ 3)
    (v : Fin n → ℚ) (ker : ∀ i, ∑ j, ((A i j : ℚ)+E i j)*v j=0) : v=0 := by
  classical
  obtain ⟨u, _, peak⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|) Finset.univ_nonempty
  have scale : (∑ i, ∑ j, (E i j : ℚ)) ≤ 3 := by exact_mod_cast err
  have hrow (i : Fin n) : ∑ j, (A i j : ℚ)*v j = -(∑ j, (E i j : ℚ)*v j) := by
    have h := ker i
    simp only [add_mul,Finset.sum_add_distrib] at h
    linarith
  have identity : (∑ i, K u i * (∑ j, (A i j : ℚ)*v j)) = 9*v u := by
    simp_rw [Finset.mul_sum,← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, inv]
    simp
  have balance : 9*v u = -(∑ i, ∑ j, K u i * (E i j : ℚ)*v j) := by
    rw [← identity]
    simp_rw [hrow,mul_neg,Finset.mul_sum,← mul_assoc,Finset.sum_neg_distrib]
  have bound : |∑ i, ∑ j, K u i * (E i j : ℚ)*v j| ≤ 6 * |v u| := by
    calc
      _ ≤ ∑ i, |∑ j, K u i * (E i j : ℚ)*v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |K u i * (E i j : ℚ)*v j| := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, (E i j : ℚ)*(2*|v u|) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : (0:ℚ) ≤ E i j)]
        have first := mul_le_mul_of_nonneg_right (coeff u i) (by positivity : (0:ℚ) ≤ E i j)
        calc
          _ ≤ (2*(E i j : ℚ))*|v u| := mul_le_mul first (peak j (Finset.mem_univ _)) (abs_nonneg _) (by positivity)
          _ = _ := by ring
      _ = (∑ i, ∑ j, (E i j : ℚ))*(2*|v u|) := by simp only [Finset.sum_mul]
      _ ≤ 3*(2*|v u|) := mul_le_mul_of_nonneg_right scale (by positivity)
      _ = _ := by ring
  have mag := congrArg abs balance
  simp only [abs_mul,abs_neg] at mag
  norm_num at mag
  have zero : |v u|=0 := by linarith [abs_nonneg (v u)]
  funext j
  exact abs_eq_zero.mp (le_antisymm ((peak j (Finset.mem_univ _)).trans zero.le) (abs_nonneg _))
end PEqualNP.Outside.L_meta_9305

namespace PEqualNP.Outside.L_meta_9305
open Finset

set_option maxHeartbeats 4000000 in
theorem no_cover (L : List (Finset I × Finset I)) (short : L.length ≤ 10)
    (pure : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, zeroCell i j = true)
    (covers : ∀ i j, zeroCell i j = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  classical
  let R (k : Fin L.length) := (L.get k).1
  let C (k : Fin L.length) := (L.get k).2
  let left (k : Fin L.length) (i : I) : ℕ := if i ∈ R k then 1 else 0
  let right (k : Fin L.length) (j : I) : ℕ := if j ∈ C k then 1 else 0
  let B (i j : I) := ∑ k, left k i * right k j
  have lsum (k : Fin L.length) : ∑ i, left k i = (R k).card := by simp [left]
  have rsum (k : Fin L.length) : ∑ j, right k j = (C k).card := by simp [right]
  have rect (k : Fin L.length) : (R k).card*(C k).card ≤ 12 := by
    apply area
    intro i hi j hj
    exact Finset.mem_filter.mpr ⟨mem_univ _,pure _ (List.get_mem L k) i hi j hj⟩
  have totalB : ∑ i, ∑ j, B i j ≤ 120 := by
    calc
      _ = ∑ i, ∑ k, left k i * (∑ j, right k j) := by
        apply sum_congr rfl
        intro i _
        unfold B
        rw [sum_comm]
        simp only [Finset.mul_sum]
      _ = ∑ k, (R k).card*(C k).card := by
        rw [sum_comm]
        simp_rw [rsum,← Finset.sum_mul,lsum]
      _ ≤ ∑ _ : Fin L.length, 12 := sum_le_sum (fun k _ => rect k)
      _ ≤ 120 := by simp; omega
  have leB (i j : I) : A i j ≤ B i j := by
    cases h : zeroCell i j with
    | false => simp [A,h]
    | true =>
      obtain ⟨r,hr,hi,hj⟩ := covers i j h
      obtain ⟨k,rfl⟩ := List.get_of_mem hr
      have h1 : i ∈ R k := hi
      have h2 : j ∈ C k := hj
      have one := Finset.single_le_sum (f := fun k => left k i * right k j) (fun _ _ => Nat.zero_le _) (mem_univ k)
      simpa [A,h,left,right,h1,h2,B] using one
  let E (i j : I) := B i j - A i j
  have sumCell (i j : I) : E i j + A i j = B i j := Nat.sub_add_cancel (leB i j)
  have totalE : ∑ i, ∑ j, E i j ≤ 3 := by
    have eq : (∑ i, ∑ j, E i j) + (∑ i, ∑ j, A i j) = ∑ i, ∑ j, B i j := by
      simp only [← Finset.sum_add_distrib,sumCell]
    rw [weight] at eq
    omega
  let F : (I → ℚ) →ₗ[ℚ] (Fin L.length → ℚ) :=
    { toFun := fun v k => ∑ j, (right k j : ℚ)*v j
      map_add' := by intro x y; ext k; simp [mul_add,Finset.sum_add_distrib]
      map_smul' := by intro r x; ext k; simp [Finset.mul_sum,mul_left_comm] }
  have inj : Function.Injective F := by
    intro x y same
    let v := x-y
    have null : F v = 0 := by simp [v,same]
    have ker (i : I) : ∑ j, ((A i j : ℚ)+E i j)*v j=0 := by
      have eq (j : I) : (A i j : ℚ)+E i j = (B i j : ℚ) := by
        exact_mod_cast ((Nat.add_comm _ _).trans (sumCell i j))
      simp_rw [eq,B,Nat.cast_sum,Nat.cast_mul,Finset.sum_mul,mul_assoc]
      rw [sum_comm]
      simp_rw [← Finset.mul_sum]
      have z (k : Fin L.length) : ∑ j, (right k j : ℚ)*v j=0 := congrFun null k
      simp [z]
    exact sub_eq_zero.mp (stable A E coeff inverse smallCoeff totalE v ker)
  have dim := LinearMap.finrank_le_finrank_of_injective (f := F) inj
  simp [I] at dim
  omega
end PEqualNP.Outside.L_meta_9305

theorem PEqualNP.Outside.L_meta_9305 : ¬ (∃ L : List (Finset (Fin 13) × Finset (Fin 13)), L.length ≤ 10 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 13) (j : Fin 13), (([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L,short,pure,covers⟩
  apply PEqualNP.Outside.L_meta_9305.no_cover L short
  · intro r hr i hi j hj
    have h := pure r hr i hi j hj
    simpa only [PEqualNP.Outside.L_meta_9305.zeroCell,PEqualNP.Outside.L_meta_9305.rows,h,Bool.not_false]
  · intro i j hz
    apply covers i j
    simpa [PEqualNP.Outside.L_meta_9305.zeroCell,PEqualNP.Outside.L_meta_9305.rows] using hz
