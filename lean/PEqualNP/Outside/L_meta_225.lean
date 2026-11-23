import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside

private theorem negate_bound (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (bound : HasTypedRank n f s) : HasTypedRank n (fun x => !f x) s := by
  classical
  obtain ⟨τ, ht, hs⟩ := bound
  refine ⟨fun x y => τ y x, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨i, hi, hd⟩ := ht y x (by simpa using hy) (by simpa using hx)
    exact ⟨i,hi,hd.symm⟩
  · have mat (i : Fin n) (b : Bool) :
        typedMatrix n (fun x => !f x) (fun x y => τ y x) i b =
        (typedMatrix n f τ i (!b)).transpose := by
      ext x y
      by_cases hy : f y = true <;> by_cases hx : f x = false <;> by_cases hτ : τ y x = i.val
      · obtain ⟨j,hj,hd⟩ := ht y x hy hx
        have e : j = i := Fin.ext (hj.symm.trans hτ)
        subst j
        cases b <;> cases ha : x i <;> cases hb : y i <;>
          simp_all [typedMatrix, Matrix.transpose_apply]
      all_goals simp_all [typedMatrix, Matrix.transpose_apply]
    apply le_trans _ hs
    apply Finset.sum_le_sum
    intro i _
    simp only [mat, Matrix.rank_transpose, Fintype.sum_bool, Bool.not_false, Bool.not_true]
    omega

theorem L_meta_225 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
    HasTypedRank n f s ↔ HasTypedRank n (fun x => !f x) s := by
  intro n f s
  refine ⟨negate_bound n f s, fun h => ?_⟩
  simpa using negate_bound n (fun x => !f x) s h

end PEqualNP.Outside
