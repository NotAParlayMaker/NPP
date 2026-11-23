import Mathlib
import PEqualNP.Defs

private lemma L_meta_208_rank_pos_of_entry_ne_zero {α : Type} [Fintype α] [DecidableEq α]
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

private lemma L_meta_208_rank_le_one_of_single_row {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (x₀ : α) (hrow : ∀ x y, x ≠ x₀ → M x y = 0) : M.rank ≤ 1 := by
  show Module.finrank ℚ (LinearMap.range M.mulVecLin) ≤ 1
  let e : α → ℚ := Pi.single x₀ (1 : ℚ)
  have hle : LinearMap.range M.mulVecLin ≤ Submodule.span ℚ {e} := by
    rintro _ ⟨v, rfl⟩
    have hv : M.mulVecLin v = (M.mulVec v x₀) • e := by
      ext x
      by_cases hx : x = x₀
      · subst hx
        simp [e, Pi.single_apply]
      · simp [e, Pi.single_apply, hx, Matrix.mulVec, dotProduct, hrow x _ hx]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  refine le_trans (Submodule.finrank_mono hle) ?_
  have he : e ≠ 0 := by
    intro h0
    have := congrFun h0 x₀
    simp [e] at this
  rw [finrank_span_singleton he]

theorem PEqualNP.Outside.L_meta_208 :
    PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 2 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 1 := by
  set f : (Fin 2 → Bool) → Bool := fun x => x 0 && x 1
  let one : Fin 2 → Bool := fun _ => true
  have hf_true_eq : ∀ x : Fin 2 → Bool, f x = true → x = one := by
    intro x hx
    ext i
    have h0 : x 0 = true := by cases h : x 0 <;> simp_all [f]
    have h1 : x 1 = true := by cases h : x 1 <;> simp_all [f]
    fin_cases i
    · exact h0
    · exact h1
  constructor
  · let τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ := fun _ y => if y 0 = false then 0 else 1
    refine ⟨τ, ?_, ?_⟩
    · intro x y hx hy
      have hx1 : x = one := hf_true_eq x hx
      by_cases hy0 : y 0 = false
      · exact ⟨0, by simp [τ, hy0], by simp [hx1, one, hy0]⟩
      · have hy1 : y 1 = false := by cases h0 : y 0 <;> cases h1 : y 1 <;> simp_all [f]
        exact ⟨1, by simp [τ, hy0], by simp [hx1, one, hy1]⟩
    · have hfalse : ∀ i : Fin 2, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i false).rank = 0 := by
        intro i
        have hzero : PEqualNP.MetaComplexity.typedMatrix 2 f τ i false = 0 := by
          ext x y
          simp only [PEqualNP.MetaComplexity.typedMatrix, Matrix.zero_apply, ite_eq_right_iff,
            one_ne_zero, imp_false]
          rintro ⟨hx, _, _, hxi⟩
          have hx1 : x = one := hf_true_eq x hx
          simp [hx1, one] at hxi
        rw [hzero, Matrix.rank_zero]
      have htrue : ∀ i : Fin 2, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i true).rank ≤ 1 := by
        intro i
        refine L_meta_208_rank_le_one_of_single_row _ one fun x y hx => ?_
        simp only [PEqualNP.MetaComplexity.typedMatrix, ite_eq_right_iff, one_ne_zero, imp_false]
        rintro ⟨hfx, _, _, _⟩
        exact hx (hf_true_eq x hfx)
      calc
        ∑ i : Fin 2, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank
          = ∑ i : Fin 2, ((PEqualNP.MetaComplexity.typedMatrix 2 f τ i false).rank +
              (PEqualNP.MetaComplexity.typedMatrix 2 f τ i true).rank) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [add_comm]
        _ ≤ ∑ _i : Fin 2, (0 + 1) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [hfalse i]
            exact Nat.add_le_add_left (htrue i) 0
        _ = 2 := by simp
  · rintro ⟨τ, hτ, hr⟩
    have hf_one : f one = true := by simp [f, one]
    have hone : ∀ i : Fin 2, 1 ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank := by
      intro i
      let y : Fin 2 → Bool := Function.update one i false
      have hfy : f y = false := by
        fin_cases i <;> simp [f, y, one]
      obtain ⟨j, hj, hne⟩ := hτ one y hf_one hfy
      have hji : j = i := by
        by_contra hne'
        exact hne (by simp [y, Function.update_of_ne hne'])
      subst hji
      have hentry : PEqualNP.MetaComplexity.typedMatrix 2 f τ j true one y ≠ 0 := by
        simp [PEqualNP.MetaComplexity.typedMatrix, hf_one, hfy, hj, one]
      calc
        1 ≤ (PEqualNP.MetaComplexity.typedMatrix 2 f τ j true).rank :=
          L_meta_208_rank_pos_of_entry_ne_zero _ hentry
        _ ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f τ j b).rank :=
          Finset.single_le_sum (f := fun b : Bool => (PEqualNP.MetaComplexity.typedMatrix 2 f τ j b).rank)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ true)
    have hge : 2 ≤ ∑ i : Fin 2, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank := by
      calc
        2 = ∑ _i : Fin 2, 1 := by simp
        _ ≤ ∑ i : Fin 2, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank :=
          Finset.sum_le_sum fun i _ => hone i
    omega
