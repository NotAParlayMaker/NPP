import Mathlib
import PEqualNP.Defs

private lemma L_meta_229_rank_pos_of_entry_ne_zero {α : Type} [Fintype α] [DecidableEq α]
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

private lemma L_meta_229_rank_le_one_of_single_col {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (y₀ : α) (hcol : ∀ x y, y ≠ y₀ → M x y = 0) : M.rank ≤ 1 := by
  show Module.finrank ℚ (LinearMap.range M.mulVecLin) ≤ 1
  let c : α → ℚ := fun x => M x y₀
  have hle : LinearMap.range M.mulVecLin ≤ Submodule.span ℚ {c} := by
    rintro _ ⟨v, rfl⟩
    have hv : M.mulVecLin v = v y₀ • c := by
      ext x
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, c]
      rw [Finset.sum_eq_single y₀]
      · ring
      · intro y _ hy
        simp [hcol x y hy]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  refine le_trans (Submodule.finrank_mono hle) ?_
  by_cases hc : c = 0
  · rw [hc, Submodule.span_zero_singleton, finrank_bot]
    exact Nat.zero_le 1
  · rw [finrank_span_singleton hc]

theorem PEqualNP.Outside.L_meta_229 :
    ∀ n : ℕ, 1 ≤ n →
      PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) n ∧
      ¬ PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  intro n hn
  set f : (Fin n → Bool) → Bool := fun x => decide (∃ i : Fin n, x i = true)
  let zero : Fin n → Bool := fun _ => false
  have hf_zero : f zero = false := by
    simp [f, zero]
  have hf_false_eq : ∀ y : Fin n → Bool, f y = false → y = zero := by
    intro y hy
    ext i
    have hnot : ¬ ∃ j : Fin n, y j = true := by simpa [f] using hy
    cases h : y i
    · rfl
    · exact absurd ⟨i, h⟩ hnot
  constructor
  · classical
    let τ : (Fin n → Bool) → (Fin n → Bool) → ℕ :=
      fun x _ => if h : ∃ i : Fin n, x i = true then (Classical.choose h).val else 0
    refine ⟨τ, ?_, ?_⟩
    · intro x y hx hy
      have hex : ∃ i : Fin n, x i = true := by simpa [f] using hx
      have hy0 : y = zero := hf_false_eq y hy
      refine ⟨Classical.choose hex, by simp [τ, hex], ?_⟩
      rw [Classical.choose_spec hex, hy0]
      simp [zero]
    · have hfalse : ∀ i : Fin n,
          (PEqualNP.MetaComplexity.typedMatrix n f τ i false).rank = 0 := by
        intro i
        have hzero : PEqualNP.MetaComplexity.typedMatrix n f τ i false = 0 := by
          ext x y
          simp only [PEqualNP.MetaComplexity.typedMatrix, Matrix.zero_apply, ite_eq_right_iff,
            one_ne_zero, imp_false]
          rintro ⟨hx, _, hτeq, hxi⟩
          have hex : ∃ j : Fin n, x j = true := by simpa [f] using hx
          have hchoose : Classical.choose hex = i := by
            apply Fin.ext
            simpa [τ, hex] using hτeq
          have htrue : x i = true := hchoose ▸ Classical.choose_spec hex
          rw [htrue] at hxi
          exact Bool.noConfusion hxi
        rw [hzero, Matrix.rank_zero]
      have htrue : ∀ i : Fin n,
          (PEqualNP.MetaComplexity.typedMatrix n f τ i true).rank ≤ 1 := by
        intro i
        refine L_meta_229_rank_le_one_of_single_col _ zero fun x y hy => ?_
        simp only [PEqualNP.MetaComplexity.typedMatrix, ite_eq_right_iff, one_ne_zero, imp_false]
        rintro ⟨_, hfy, _, _⟩
        exact hy (hf_false_eq y hfy)
      calc
        ∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank
          = ∑ i : Fin n, ((PEqualNP.MetaComplexity.typedMatrix n f τ i false).rank +
              (PEqualNP.MetaComplexity.typedMatrix n f τ i true).rank) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [add_comm]
        _ ≤ ∑ _i : Fin n, (0 + 1) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [hfalse i]
            exact Nat.add_le_add_left (htrue i) 0
        _ = n := by simp
  · rintro ⟨τ, hτ, hr⟩
    have hone : ∀ i : Fin n, 1 ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
      intro i
      let x : Fin n → Bool := Function.update zero i true
      have hfx : f x = true := by
        simp only [f, decide_eq_true_eq]
        exact ⟨i, by simp [x]⟩
      obtain ⟨j, hj, hne⟩ := hτ x zero hfx hf_zero
      have hji : j = i := by
        by_contra hne'
        exact hne (by simp [x, Function.update_of_ne hne'])
      subst hji
      have hentry : PEqualNP.MetaComplexity.typedMatrix n f τ j (x j) x zero ≠ 0 := by
        simp [PEqualNP.MetaComplexity.typedMatrix, hfx, hf_zero, hj]
      calc
        1 ≤ (PEqualNP.MetaComplexity.typedMatrix n f τ j (x j)).rank :=
          L_meta_229_rank_pos_of_entry_ne_zero _ hentry
        _ ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank :=
          Finset.single_le_sum (f := fun b : Bool => (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (x j))
    have hge : n ≤ ∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
      calc
        n = ∑ _i : Fin n, 1 := by simp
        _ ≤ ∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank :=
          Finset.sum_le_sum fun i _ => hone i
    omega
