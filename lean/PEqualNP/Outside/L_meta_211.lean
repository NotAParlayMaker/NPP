import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_211_aux

open PEqualNP.MetaComplexity

abbrev fn (x : Fin 4 → Bool) : Bool :=
  decide ((if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0) +
    (if x 2 = true then 4 else 0) + (if x 3 = true then 8 else 0) ∈
    ({3, 4, 6, 7, 8, 9, 11, 12} : Finset ℕ))

abbrev nOf (x : Fin 4 → Bool) : ℕ :=
  (if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0) +
    (if x 2 = true then 4 else 0) + (if x 3 = true then 8 else 0)

def xsOf (c : ℕ) : List ℕ :=
  if c = 2 then [3,11]
  else if c = 9 then [3,8,9,11]
  else if c = 14 then [8,9]
  else if c = 5 then [4,8,9,12]
  else if c = 1 then [4,12]
  else if c = 6 then [3,6,7,11]
  else if c = 10 then [4,6,7,12]
  else if c = 13 then [6,7]
  else []

def ysOf (c : ℕ) : List ℕ :=
  if c = 2 then [0,2,10,14]
  else if c = 9 then [13,15]
  else if c = 14 then [0,1,2,5]
  else if c = 5 then [10,14]
  else if c = 1 then [1,5,13,15]
  else if c = 6 then [1,5]
  else if c = 10 then [0,2]
  else if c = 13 then [10,13,14,15]
  else []

def cc (i : Fin 4) (b : Bool) : ℕ := 4 * (i : ℕ) + (if b then 1 else 0) + 1

def tab : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 6, 2, 0, 0, 6, 0, 0, 0, 0, 2, 0, 0, 9, 2, 9,
  10, 1, 10, 0, 0, 1, 0, 0, 0, 0, 5, 0, 0, 1, 5, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  10, 6, 10, 0, 0, 6, 0, 0, 0, 0, 13, 0, 0, 13, 13, 13,
  10, 6, 10, 0, 0, 6, 0, 0, 0, 0, 13, 0, 0, 13, 13, 13,
  14, 14, 14, 0, 0, 14, 0, 0, 0, 0, 5, 0, 0, 9, 5, 9,
  14, 14, 14, 0, 0, 14, 0, 0, 0, 0, 5, 0, 0, 9, 5, 9,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 6, 2, 0, 0, 6, 0, 0, 0, 0, 2, 0, 0, 9, 2, 9,
  10, 1, 10, 0, 0, 1, 0, 0, 0, 0, 5, 0, 0, 1, 5, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
]

def tau (x y : Fin 4 → Bool) : ℕ := (tab.getD (nOf x * 16 + nOf y) 0) / 4

def A (c : ℕ) : Matrix (Fin 4 → Bool) (Fin 1) ℚ :=
  Matrix.of fun x _ => if nOf x ∈ xsOf c then 1 else 0

def B (c : ℕ) : Matrix (Fin 1) (Fin 4 → Bool) ℚ :=
  Matrix.of fun _ y => if nOf y ∈ ysOf c then 1 else 0

lemma typing : IsTyping 4 fn tau := by
  intro x y hx hy
  decide +revert

lemma entry (i : Fin 4) (b : Bool) (x y : Fin 4 → Bool) :
    (fn x = true ∧ fn y = false ∧ tau x y = (i : ℕ) ∧ x i = b) ↔
      (nOf x ∈ xsOf (cc i b) ∧ nOf y ∈ ysOf (cc i b)) := by
  revert i b x y
  decide

lemma rect (i : Fin 4) (b : Bool) (x y : Fin 4 → Bool) :
    typedMatrix 4 fn tau i b x y =
      Matrix.vecMulVec
        (fun x : Fin 4 → Bool => if nOf x ∈ xsOf (cc i b) then (1 : ℚ) else 0)
        (fun y : Fin 4 → Bool => if nOf y ∈ ysOf (cc i b) then (1 : ℚ) else 0) x y := by
  simp only [typedMatrix, Matrix.vecMulVec_apply]
  by_cases hp : nOf x ∈ xsOf (cc i b)
  · by_cases hq : nOf y ∈ ysOf (cc i b)
    · have h := (entry i b x y).mpr ⟨hp, hq⟩
      rw [ite_eq_left h, ite_eq_left hp, ite_eq_left hq]
      norm_num
    · have h : ¬(fn x = true ∧ fn y = false ∧ tau x y = (i : ℕ) ∧ x i = b) :=
        fun hh => hq ((entry i b x y).mp hh).2
      rw [ite_eq_right h, ite_eq_right hq]
      simp
  · have h : ¬(fn x = true ∧ fn y = false ∧ tau x y = (i : ℕ) ∧ x i = b) :=
      fun hh => hp ((entry i b x y).mp hh).1
    rw [ite_eq_right h, ite_eq_right hp]
    simp

lemma rank_le (i : Fin 4) (b : Bool) : (typedMatrix 4 fn tau i b).rank ≤ 1 := by
  have h : typedMatrix 4 fn tau i b =
      Matrix.vecMulVec
        (fun x : Fin 4 → Bool => if nOf x ∈ xsOf (cc i b) then (1 : ℚ) else 0)
        (fun y : Fin 4 → Bool => if nOf y ∈ ysOf (cc i b) then (1 : ℚ) else 0) :=
    funext fun x => funext fun y => rect i b x y
  rw [h]
  exact Matrix.rank_vecMulVec_le _ _

lemma main : HasTypedRank 4 fn 8 := by
  refine ⟨tau, typing, ?_⟩
  calc (∑ i : Fin 4, ∑ b : Bool, (typedMatrix 4 fn tau i b).rank)
      ≤ ∑ i : Fin 4, ∑ b : Bool, (1 : ℕ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => rank_le i b
    _ = 8 := by rw [Fin.sum_univ_four]; rfl

end PEqualNP.Outside.L_meta_211_aux

theorem PEqualNP.Outside.L_meta_211 :
    PEqualNP.MetaComplexity.HasTypedRank 4
      (fun x : Fin 4 → Bool =>
        decide ((if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0) +
          (if x 2 = true then 4 else 0) + (if x 3 = true then 8 else 0) ∈
          ({3, 4, 6, 7, 8, 9, 11, 12} : Finset ℕ))) 8 :=
  PEqualNP.Outside.L_meta_211_aux.main
