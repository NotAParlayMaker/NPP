import Mathlib
import PEqualNP.Defs

private lemma L_meta_228_one_le_rank {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (x y : α) (h : M x y ≠ 0) : 1 ≤ M.rank := by
  by_contra h0
  have h0' : Module.finrank ℚ (LinearMap.range M.mulVecLin) = 0 := by
    show M.rank = 0
    omega
  rw [Submodule.finrank_eq_zero] at h0'
  have hmem : M.mulVecLin (Pi.single y 1) ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
  rw [h0', Submodule.mem_bot] at hmem
  apply h
  have := congrFun hmem x
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this

private lemma L_meta_228_local (n : ℕ) (f : (Fin n → Bool) → Bool)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (hτ : PEqualNP.MetaComplexity.IsTyping n f τ)
    (i : Fin n) (x : Fin n → Bool) (hx : f x ≠ f (Function.update x i (!x i))) :
    1 ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
  have key : ∀ p q : Fin n → Bool, f p = true → f q = false → (∀ j, j ≠ i → p j = q j) →
      1 ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
    intro p q hp hq hpq
    obtain ⟨j, hj, hne⟩ := hτ p q hp hq
    have hji : j = i := by
      by_contra hc
      exact hne (hpq j hc)
    subst hji
    have h1 : 1 ≤ (PEqualNP.MetaComplexity.typedMatrix n f τ j (p j)).rank := by
      apply L_meta_228_one_le_rank _ p q
      simp [PEqualNP.MetaComplexity.typedMatrix, hp, hq, hj]
    refine le_trans h1 ?_
    exact Finset.single_le_sum (f := fun b => (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hdiff : ∀ j, j ≠ i → x j = Function.update x i (!x i) j := by
    intro j hj
    simp [Function.update_of_ne hj]
  rcases Bool.eq_false_or_eq_true (f x) with h | h
  · have h2 : f (Function.update x i (!x i)) = false := by
      cases hf : f (Function.update x i (!x i)) <;> simp_all
    exact key x _ h h2 hdiff
  · have h2 : f (Function.update x i (!x i)) = true := by
      cases hf : f (Function.update x i (!x i)) <;> simp_all
    exact key _ x h2 h (fun j hj => (hdiff j hj).symm)

theorem PEqualNP.Outside.L_meta_228 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s →
    (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  rintro n f s ⟨τ, hτ, hr⟩
  refine le_trans ?_ hr
  rw [Finset.card_eq_sum_ones]
  refine le_trans (Finset.sum_le_sum (fun i hi => ?_)) (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _))
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hi).2
  exact L_meta_228_local n f τ hτ i x hx
