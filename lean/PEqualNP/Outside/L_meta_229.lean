import Mathlib
import PEqualNP.Defs

private lemma L_meta_229_one_le_rank {α : Type} [Fintype α] [DecidableEq α]
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

private lemma L_meta_229_local (n : ℕ) (f : (Fin n → Bool) → Bool)
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
      apply L_meta_229_one_le_rank _ p q
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

private lemma L_meta_229_lower :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s →
    (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  rintro n f s ⟨τ, hτ, hr⟩
  refine le_trans ?_ hr
  rw [Finset.card_eq_sum_ones]
  refine le_trans (Finset.sum_le_sum (fun i hi => ?_)) (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _))
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hi).2
  exact L_meta_229_local n f τ hτ i x hx

private lemma L_meta_229_row_le_one {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (x0 : α) (h : ∀ x y, x ≠ x0 → M x y = 0) : M.rank ≤ 1 := by
  have := Matrix.rank_le_card_of_support_subset M {x0} (by
    intro x hx
    by_contra hc
    apply hx
    funext y
    exact h x y (by simpa using hc))
  simpa using this

private lemma L_meta_229_col_le_one {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (y0 : α) (h : ∀ x y, y ≠ y0 → M x y = 0) : M.rank ≤ 1 := by
  rw [← Matrix.rank_transpose]
  exact L_meta_229_row_le_one _ y0 (fun x y hx => h y x hx)

theorem PEqualNP.Outside.L_meta_229 :
    ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) n ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  intro n hn
  constructor
  · let τ : (Fin n → Bool) → (Fin n → Bool) → ℕ := fun x _ =>
      if h : ∃ i : Fin n, x i = true then (h.choose : ℕ) else 0
    refine ⟨τ, ?_, ?_⟩
    · intro x y hx hy
      have hx' : ∃ i : Fin n, x i = true := by simpa using hx
      have hy' : ∀ i : Fin n, y i = false := by simpa using hy
      refine ⟨hx'.choose, by simp [τ, hx'], ?_⟩
      rw [hx'.choose_spec, hy']
      decide
    · have hle : ∀ i : Fin n, ∑ b : Bool,
          (PEqualNP.MetaComplexity.typedMatrix n (fun x => decide (∃ i : Fin n, x i = true)) τ i b).rank ≤ 1 := by
        intro i
        rw [Fintype.sum_bool]
        have h0 : PEqualNP.MetaComplexity.typedMatrix n (fun x => decide (∃ i : Fin n, x i = true)) τ i false = 0 := by
          ext x y
          simp only [PEqualNP.MetaComplexity.typedMatrix, Matrix.zero_apply, ite_eq_right_iff,
            one_ne_zero, imp_false]
          rintro ⟨hx, _, hτi, hxi⟩
          have hx' : ∃ i : Fin n, x i = true := by simpa using hx
          have hc : (hx'.choose : ℕ) = i := by simpa [τ, hx'] using hτi
          have := hx'.choose_spec
          rw [Fin.ext hc] at this
          simp_all
        rw [h0, Matrix.rank_zero, add_zero]
        apply L_meta_229_col_le_one _ (fun _ => false)
        intro x y hy
        simp only [PEqualNP.MetaComplexity.typedMatrix, ite_eq_right_iff, one_ne_zero, imp_false]
        rintro ⟨_, hfy, _⟩
        apply hy
        funext j
        have hy' : ∀ i : Fin n, y i = false := by simpa using hfy
        exact hy' j
      calc _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => hle i
        _ = n := by simp
  · intro h
    have hc := L_meta_229_lower n _ (n - 1) h
    have huniv : (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool,
        decide (∃ i : Fin n, x i = true) ≠ decide (∃ j : Fin n, Function.update x i (!x i) j = true))) =
        Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      refine ⟨fun _ => false, ?_⟩
      have : Function.update (fun _ : Fin n => false) i true i = true := by simp
      simp only [Bool.not_false]
      intro heq
      have h2 : decide (∃ j : Fin n, Function.update (fun _ : Fin n => false) i true j = true) = true :=
        decide_eq_true ⟨i, this⟩
      rw [← heq] at h2
      simp at h2
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hc
    omega
