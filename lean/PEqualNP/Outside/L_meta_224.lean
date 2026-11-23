import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_224_aux

/-- The rank of a sum of matrices is at most the sum of the ranks. -/
theorem rank_add_le' {m k : Type*} [Fintype m] [Fintype k] (A B : Matrix m k ℚ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℚ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℚ (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
          Submodule ℚ (m → ℚ)) := Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

end PEqualNP.Outside.L_meta_224_aux

open PEqualNP.Outside.L_meta_224_aux PEqualNP.MetaComplexity in
/-- Type a pair of  AND g by the typing of  when  is false at the second input, and by
the typing of g otherwise. Each literal matrix of  AND g is then the literal matrix of 
with rows cut to g, plus the literal matrix of g with rows and columns cut to . -/
theorem PEqualNP.Outside.L_meta_224 : ∀ (n : ℕ) (f g : (Fin n → Bool) → Bool) (s t : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s → PEqualNP.MetaComplexity.HasTypedRank n g t →
    PEqualNP.MetaComplexity.HasTypedRank n (fun x => f x && g x) (s + t) := by
  rintro n f g s t ⟨τf, hτf, hsf⟩ ⟨τg, hτg, hsg⟩
  classical
  let τ : (Fin n → Bool) → (Fin n → Bool) → ℕ := fun x y =>
    if f y = false then τf x y else τg x y
  refine ⟨τ, ?_, ?_⟩
  · intro x y hx hy
    have hx' : (f x && g x) = true := hx
    have hx'' : f x = true ∧ g x = true := by simpa using hx'
    have hfx : f x = true := hx''.1
    have hgx : g x = true := hx''.2
    by_cases hfy : f y = false
    · obtain ⟨i, hi, hne⟩ := hτf x y hfx hfy
      exact ⟨i, by simp [τ, hfy, hi], hne⟩
    · have hfy' : f y = true := by simpa using hfy
      have hy' : (f y && g y) = false := hy
      have hgy : g y = false := by rw [hfy'] at hy'; simpa using hy'
      obtain ⟨i, hi, hne⟩ := hτg x y hgx hgy
      exact ⟨i, by simp [τ, hfy', hi], hne⟩
  · have key : ∀ i b, (typedMatrix n (fun x => f x && g x) τ i b).rank ≤
        (typedMatrix n f τf i b).rank + (typedMatrix n g τg i b).rank := by
      intro i b
      let Dg : Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
        Matrix.diagonal (fun x => if g x = true then 1 else 0)
      let Df : Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
        Matrix.diagonal (fun x => if f x = true then 1 else 0)
      have heq : typedMatrix n (fun x => f x && g x) τ i b =
          Dg * typedMatrix n f τf i b + Df * typedMatrix n g τg i b * Df := by
        ext x y
        simp only [typedMatrix, Dg, Df, Matrix.add_apply, Matrix.diagonal_mul,
          Matrix.mul_diagonal, τ]
        by_cases hfx : f x = true <;> by_cases hgx : g x = true <;> by_cases hfy : f y = true <;>
          by_cases hgy : g y = true <;> simp [hfx, hgx, hfy, hgy]
      rw [heq]
      exact (rank_add_le' _ _).trans (add_le_add (Matrix.rank_mul_le_right _ _)
        ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)))
    calc (∑ i : Fin n, ∑ b : Bool, (typedMatrix n (fun x => f x && g x) τ i b).rank)
        ≤ ∑ i : Fin n, ∑ b : Bool,
            ((typedMatrix n f τf i b).rank + (typedMatrix n g τg i b).rank) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => key i b
      _ = (∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τf i b).rank) +
            ∑ i : Fin n, ∑ b : Bool, (typedMatrix n g τg i b).rank := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
      _ ≤ s + t := add_le_add hsf hsg
