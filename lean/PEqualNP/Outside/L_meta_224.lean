import Mathlib
import PEqualNP.Defs

-- Type a pair (x, y) of f && g with the typing of f when f y = false, and with the typing of
-- g otherwise. Each literal matrix is then Dg * Mf + Df * Mg * Df, with Df and Dg the 0/1
-- diagonal masks of f and g, so its rank is at most rank Mf + rank Mg.

namespace PEqualNP.Outside.L_meta_224_aux

open PEqualNP.MetaComplexity

-- The rank of a sum of rational matrices is at most the sum of the ranks.
lemma rank_add_le' {m k : Type*} [Fintype m] [Fintype k] (A B : Matrix m k ℚ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

-- The 0/1 diagonal mask of a Boolean function.
def mask {n : ℕ} (f : (Fin n → Bool) → Bool) : Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
  Matrix.diagonal fun x => if f x = true then 1 else 0

lemma split (n : ℕ) (f g : (Fin n → Bool) → Bool) (τf τg : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (i : Fin n) (b : Bool) :
    typedMatrix n (fun x => f x && g x)
        (fun x y => if f y = false then τf x y else τg x y) i b =
      mask g * typedMatrix n f τf i b + mask f * typedMatrix n g τg i b * mask f := by
  ext x y
  simp only [typedMatrix, mask, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hfx : f x = true <;> by_cases hgx : g x = true <;> by_cases hfy : f y = true <;>
    by_cases hgy : g y = true <;> simp_all

end PEqualNP.Outside.L_meta_224_aux

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_224_aux in
theorem PEqualNP.Outside.L_meta_224 : ∀ (n : ℕ) (f g : (Fin n → Bool) → Bool) (s t : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s → PEqualNP.MetaComplexity.HasTypedRank n g t →
    PEqualNP.MetaComplexity.HasTypedRank n (fun x => f x && g x) (s + t)
 := by
  intro n f g s t ⟨τf, hτf, hsf⟩ ⟨τg, hτg, hsg⟩
  refine ⟨fun x y => if f y = false then τf x y else τg x y, ?_, ?_⟩
  · intro x y hx hy
    simp only [Bool.and_eq_true] at hx
    by_cases hfy : f y = false
    · obtain ⟨i, hi, hne⟩ := hτf x y hx.1 hfy
      exact ⟨i, by simp [hfy, hi], hne⟩
    · have hfy' : f y = true := by simpa using hfy
      have hgy : g y = false := by simpa [hfy'] using hy
      obtain ⟨i, hi, hne⟩ := hτg x y hx.2 hgy
      exact ⟨i, by simp [hfy, hi], hne⟩
  · have key : ∀ (i : Fin n) (b : Bool),
        (typedMatrix n (fun x => f x && g x)
          (fun x y => if f y = false then τf x y else τg x y) i b).rank ≤
        (typedMatrix n f τf i b).rank + (typedMatrix n g τg i b).rank := by
      intro i b
      rw [split]
      exact (rank_add_le' _ _).trans (add_le_add (Matrix.rank_mul_le_right _ _)
        ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)))
    calc _ ≤ ∑ i : Fin n, ∑ b : Bool,
          ((typedMatrix n f τf i b).rank + (typedMatrix n g τg i b).rank) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => key i b
      _ = (∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τf i b).rank) +
          ∑ i : Fin n, ∑ b : Bool, (typedMatrix n g τg i b).rank := by
          simp only [Finset.sum_add_distrib]
      _ ≤ s + t := add_le_add hsf hsg
