import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_227 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool) (s : ℕ),
      HasTypedRank n f s → HasTypedRank n (fun x => f (Function.update x i b)) s := by
  classical
  rintro n f i b s ⟨τ, ht, hs⟩
  let fix (x : Fin n → Bool) := Function.update x i b
  have away (x y : Fin n → Bool) (hx : f (fix x) = true) (hy : f (fix y) = false) :
      τ (fix x) (fix y) ≠ i.val := by
    obtain ⟨j, hj, hd⟩ := ht _ _ hx hy
    intro h
    have he : j = i := Fin.ext (hj.symm.trans h)
    subst j
    simpa [fix] using hd
  refine ⟨fun x y => τ (fix x) (fix y), ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨j, hj, hd⟩ := ht (fix x) (fix y) hx hy
    have hji : j ≠ i := fun e => away x y hx hy (hj.trans (congrArg Fin.val e))
    exact ⟨j, hj, by simpa [fix, Function.update_of_ne hji] using hd⟩
  · apply le_trans _ hs
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro c _
    have hmat : typedMatrix n (fun x => f (fix x)) (fun x y => τ (fix x) (fix y)) j c =
        (typedMatrix n f τ j c).submatrix fix fix := by
      ext x y
      by_cases e : j = i
      · subst j
        by_cases hx : f (fix x) = true <;> by_cases hy : f (fix y) = false
        · simp [typedMatrix, Matrix.submatrix, hx, hy, away x y hx hy]
        all_goals simp [typedMatrix, Matrix.submatrix, hx, hy]
      · simp [typedMatrix, Matrix.submatrix, fix, Function.update_of_ne e]
    rw [show typedMatrix n (fun x => f (Function.update x i b))
        (fun x y => τ (fix x) (fix y)) j c = _ from hmat]
    exact Matrix.rank_submatrix_le _ _ _
