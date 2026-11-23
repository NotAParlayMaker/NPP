import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside
open MetaComplexity

private theorem entry_rank {α : Type} [Fintype α] (M : Matrix α α ℚ)
    (x y : α) (h : M x y = 1) : 1 ≤ M.rank := by
  classical
  by_contra! hz
  have zero : M.rank = 0 := by omega
  rw [Matrix.rank_eq_finrank_span_cols] at zero
  have bot := Submodule.finrank_eq_zero.mp zero
  have mem : M.col y ∈ Submodule.span ℚ (Set.range M.col) := Submodule.subset_span ⟨y,rfl⟩
  rw [bot] at mem
  have col : M.col y = 0 := mem
  have e := congrFun col x
  change M x y = 0 at e
  linarith

theorem L_meta_228 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), HasTypedRank n f s →
    (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  rintro n f s ⟨τ,ht,hs⟩
  classical
  let weight (i : Fin n) := ∑ b : Bool, (typedMatrix n f τ i b).rank
  have lower (i : Fin n) (x y : Fin n → Bool) (hx : f x = true) (hy : f y = false)
      (same : ∀ j, j ≠ i → x j = y j) : 1 ≤ weight i := by
    obtain ⟨j,hj,hd⟩ := ht x y hx hy
    have eq : j = i := by by_contra hn; exact hd (same j hn)
    subst j
    have he : typedMatrix n f τ i (x i) x y = 1 := by simp [typedMatrix,hx,hy,hj]
    exact (entry_rank _ _ _ he).trans (Finset.single_le_sum (fun b _ => Nat.zero_le (typedMatrix n f τ i b).rank)
      (Finset.mem_univ (x i)))
  apply le_trans _ hs
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool,
          f x ≠ f (Function.update x i (!x i))), 1 := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool,
          f x ≠ f (Function.update x i (!x i))), weight i := by
      refine Finset.sum_le_sum fun i hi => ?_
      obtain ⟨x,hx⟩ := (Finset.mem_filter.mp hi).2
      let y := Function.update x i (!x i)
      have same : ∀ j, j ≠ i → x j = y j := by intro j hj; simp [y,hj]
      change f x ≠ f y at hx
      cases h₁ : f x <;> cases h₂ : f y
      · simp_all
      · exact lower i y x h₂ h₁ fun j hj => (same j hj).symm
      · exact lower i x y h₁ h₂ same
      · simp_all
    _ ≤ ∑ i, weight i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      (fun _ _ _ => Nat.zero_le _)

end PEqualNP.Outside
