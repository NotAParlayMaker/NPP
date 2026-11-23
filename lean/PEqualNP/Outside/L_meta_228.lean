import Mathlib
import PEqualNP.Defs

private lemma L_meta_228_rank_pos_of_entry_ne_zero {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) {x y : α} (hxy : M x y ≠ 0) : 1 ≤ M.rank := by
  show 1 ≤ Module.finrank ℚ (LinearMap.range M.mulVecLin)
  have hne : M.mulVecLin (Pi.single y (1 : ℚ)) ≠ 0 := by
    intro h0
    have hx := congrFun h0 x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hx
    exact hxy hx
  have hne0 : Module.finrank ℚ (LinearMap.range M.mulVecLin) ≠ 0 := by
    intro h0
    have hbot : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hmem : M.mulVecLin (Pi.single y (1 : ℚ)) ∈ (⊥ : Submodule ℚ (α → ℚ)) :=
      hbot ▸ ⟨Pi.single y (1 : ℚ), rfl⟩
    exact hne (by simpa using hmem)
  omega

theorem PEqualNP.Outside.L_meta_228 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasTypedRank n f s →
      (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  rintro n f s ⟨τ, hτ, hr⟩
  set S : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))
  have hone : ∀ i ∈ S, 1 ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
    intro i hi
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hi).2
    let y : Fin n → Bool := Function.update x i (!x i)
    have hdiff_only : ∀ j : Fin n, x j ≠ y j → j = i := by
      intro j hj
      by_contra hne
      exact hj (by simp [y, Function.update_of_ne hne])
    by_cases hfx : f x = true
    · have hfy : f y = false := by cases h : f y <;> simp_all [y]
      obtain ⟨j, hj, hne⟩ := hτ x y hfx hfy
      have hji : j = i := hdiff_only j hne
      subst hji
      have hentry : PEqualNP.MetaComplexity.typedMatrix n f τ j (x j) x y ≠ 0 := by
        simp [PEqualNP.MetaComplexity.typedMatrix, hfx, hfy, hj]
      have hpos := L_meta_228_rank_pos_of_entry_ne_zero _ hentry
      calc
        1 ≤ (PEqualNP.MetaComplexity.typedMatrix n f τ j (x j)).rank := hpos
        _ ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank :=
          Finset.single_le_sum (f := fun b : Bool => (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (x j))
    · have hfx' : f x = false := by cases h : f x <;> simp_all
      have hfy : f y = true := by cases h : f y <;> simp_all [y]
      obtain ⟨j, hj, hne⟩ := hτ y x hfy hfx'
      have hji : j = i := hdiff_only j (Ne.symm hne)
      subst hji
      have hentry : PEqualNP.MetaComplexity.typedMatrix n f τ j (y j) y x ≠ 0 := by
        simp [PEqualNP.MetaComplexity.typedMatrix, hfy, hfx', hj]
      have hpos := L_meta_228_rank_pos_of_entry_ne_zero _ hentry
      calc
        1 ≤ (PEqualNP.MetaComplexity.typedMatrix n f τ j (y j)).rank := hpos
        _ ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank :=
          Finset.single_le_sum (f := fun b : Bool => (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (y j))
  calc
    S.card = ∑ _i ∈ S, 1 := by simp
    _ ≤ ∑ i ∈ S, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank :=
      Finset.sum_le_sum hone
    _ ≤ ∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ ≤ s := hr
