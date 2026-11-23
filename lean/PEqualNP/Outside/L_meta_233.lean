import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_233
open PEqualNP.MetaComplexity

abbrev Inputs := Fin 3 → Bool

def target (x : Inputs) : Bool := decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)

def typing (x y : Inputs) : ℕ :=
  if x 0 = false ∧ y 0 = true then 0 else if x 1 = false ∧ y 1 = true then 1 else 2

def M (i : Fin 3) (b : Bool) : Matrix Inputs Inputs ℚ := typedMatrix 3 target typing i b

def u0 (x : Inputs) : ℚ := if target x = true ∧ x 0 = false then 1 else 0

def v0 (y : Inputs) : ℚ := if target y = false ∧ y 0 = true then 1 else 0

def left1 : Matrix Inputs (Fin 2) ℚ :=
  fun x j => if target x = true ∧ x 1 = false ∧ x 0 = decide (j = 1) then 1 else 0

def right1 : Matrix (Fin 2) Inputs ℚ :=
  fun j y => M 1 false (fun i => decide (i = 0 ∧ j = 1)) y

def row (j : Fin 2) : Inputs := fun i => decide (i.val = j.val)

def left2 : Matrix Inputs (Fin 2) ℚ := fun x j => if x = row j then 1 else 0

def right2 : Matrix (Fin 2) Inputs ℚ := fun j y => M 2 false (row j) y

lemma typing_valid : IsTyping 3 target typing := by
  unfold IsTyping
  decide

lemma positive_entries : ∀ (i : Fin 3) (x y : Inputs), M i true x y = 0 := by
  unfold Inputs M typedMatrix
  decide

lemma positive_zero (i : Fin 3) : M i true = 0 := by
  ext x y
  exact positive_entries i x y

lemma all_inputs {P : Inputs → Prop}
    (h : ∀ a b c : Bool, P ![a, b, c]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1, x 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact h _ _ _

set_option maxHeartbeats 2000000 in
lemma factor0_entries : ∀ x y : Inputs, M 0 false x y = Matrix.vecMulVec u0 v0 x y := by
  apply all_inputs
  intro a b c
  apply all_inputs
  intro d e f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    norm_num [M, typedMatrix, target, typing, Matrix.vecMulVec, u0, v0,
      Matrix.mul_apply, Fin.sum_univ_two, left1, right1, left2, right2, row,
      funext_iff, Fin.forall_fin_succ]

set_option maxHeartbeats 2000000 in
lemma factor1_entries : ∀ x y : Inputs, M 1 false x y = (left1 * right1) x y := by
  apply all_inputs
  intro a b c
  apply all_inputs
  intro d e f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    norm_num [M, typedMatrix, target, typing, Matrix.vecMulVec, u0, v0,
      Matrix.mul_apply, Fin.sum_univ_two, left1, right1, left2, right2, row,
      funext_iff, Fin.forall_fin_succ]

set_option maxHeartbeats 2000000 in
lemma factor2_entries : ∀ x y : Inputs, M 2 false x y = (left2 * right2) x y := by
  apply all_inputs
  intro a b c
  apply all_inputs
  intro d e f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    norm_num [M, typedMatrix, target, typing, Matrix.vecMulVec, u0, v0,
      Matrix.mul_apply, Fin.sum_univ_two, left1, right1, left2, right2, row,
      funext_iff, Fin.forall_fin_succ]

lemma bound0 : (M 0 false).rank ≤ 1 := by
  have he : M 0 false = Matrix.vecMulVec u0 v0 := by
    ext x y
    exact factor0_entries x y
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

lemma bound1 : (M 1 false).rank ≤ 2 := by
  have he : M 1 false = left1 * right1 := by
    ext x y
    exact factor1_entries x y
  rw [he]
  exact le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_card_width left1)

lemma bound2 : (M 2 false).rank ≤ 2 := by
  have he : M 2 false = left2 * right2 := by
    ext x y
    exact factor2_entries x y
  rw [he]
  exact le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_card_width left2)

lemma upper : HasTypedRank 3 target 5 := by
  refine ⟨typing, typing_valid, ?_⟩
  change (∑ i : Fin 3, ∑ b : Bool, (M i b).rank) ≤ 5
  have hp (i : Fin 3) : (M i true).rank = 0 := by rw [positive_zero]; simp
  simp only [Fin.sum_univ_three, Fintype.sum_bool, hp, zero_add]
  have h0 := bound0
  have h1 := bound1
  have h2 := bound2
  omega

end PEqualNP.Outside.L_meta_233

theorem PEqualNP.Outside.L_meta_233 : PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 5 := by
  exact PEqualNP.Outside.L_meta_233.upper
