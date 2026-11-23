import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_233

open PEqualNP.MetaComplexity

def g : (Fin 3 → Bool) → Bool :=
  fun x => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)

def τ1 : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ := fun x y =>
  if x 0 = false ∧ y 0 = true then 0
  else if x 1 = false ∧ y 1 = true ∧ (x 0 = false ∨ y 2 = false) then 1 else 2

lemma typing1 : IsTyping 3 g τ1 := by
  unfold IsTyping
  decide

lemma rows_le (i : Fin 3) (b : Bool) (s : Finset (Fin 3 → Bool))
    (hs : ∀ x y, g x = true → g y = false → τ1 x y = (i : ℕ) → x i = b → x ∈ s) :
    (typedMatrix 3 g τ1 i b).rank ≤ s.card := by
  apply Matrix.rank_le_card_of_support_subset
  rw [Function.support_subset_iff']
  intro x hx
  funext y
  rw [Matrix.row_apply]
  simp only [typedMatrix, Pi.zero_apply]
  rw [ite_eq_right_iff]
  rintro ⟨h1, h2, h3, h4⟩
  exact absurd (hs x y h1 h2 h3 h4) hx

lemma cols_le (i : Fin 3) (b : Bool) (t : Finset (Fin 3 → Bool))
    (ht : ∀ x y, g x = true → g y = false → τ1 x y = (i : ℕ) → x i = b → y ∈ t) :
    (typedMatrix 3 g τ1 i b).rank ≤ t.card := by
  rw [← Matrix.rank_transpose]
  apply Matrix.rank_le_card_of_support_subset
  rw [Function.support_subset_iff']
  intro y hy
  funext x
  rw [Matrix.row_apply, Matrix.transpose_apply]
  simp only [typedMatrix, Pi.zero_apply]
  rw [ite_eq_right_iff]
  rintro ⟨h1, h2, h3, h4⟩
  exact absurd (ht x y h1 h2 h3 h4) hy

lemma rank00 : (typedMatrix 3 g τ1 0 false).rank ≤ 1 := by
  have he : typedMatrix 3 g τ1 0 false =
      Matrix.vecMulVec (fun x => if g x = true ∧ x 0 = false then (1 : ℚ) else 0)
        (fun y => if g y = false ∧ y 0 = true then (1 : ℚ) else 0) := by
    ext x y
    rw [Matrix.vecMulVec_apply]
    simp only [typedMatrix, τ1]
    rcases Bool.eq_false_or_eq_true (g x) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (g y) with hy | hy <;>
    rcases Bool.eq_false_or_eq_true (x 0) with hx0 | hx0 <;>
    rcases Bool.eq_false_or_eq_true (y 0) with hy0 | hy0 <;>
    simp [hx, hy, hx0, hy0] <;> split_ifs <;> simp_all
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

lemma bound : HasTypedRank 3 g 5 := by
  refine ⟨τ1, typing1, ?_⟩
  rw [Fin.sum_univ_three, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  have h1 := rank00
  have h2 := (rows_le 0 true ∅ (by decide)).trans (le_of_eq Finset.card_empty)
  have h3 := (cols_le 1 false {![true, true, false], ![false, true, true]} (by decide)).trans
    (le_of_eq (Finset.card_pair (by decide)))
  have h4 := (rows_le 1 true ∅ (by decide)).trans (le_of_eq Finset.card_empty)
  have h5 := (rows_le 2 false {![true, false, false], ![false, true, false]} (by decide)).trans
    (le_of_eq (Finset.card_pair (by decide)))
  have h6 := (rows_le 2 true ∅ (by decide)).trans (le_of_eq Finset.card_empty)
  omega

end PEqualNP.Outside.L_meta_233

theorem PEqualNP.Outside.L_meta_233 : PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 5 :=
  PEqualNP.Outside.L_meta_233.bound
