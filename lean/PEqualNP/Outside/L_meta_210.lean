import Mathlib
import PEqualNP.Defs

private lemma L_meta_210_rank_pos_of_entry_ne_zero {α : Type} [Fintype α] [DecidableEq α]
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

private lemma L_meta_210_rank_le_one_of_single_row {α : Type} [Fintype α] [DecidableEq α]
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

theorem PEqualNP.Outside.L_meta_210 :
    PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 4 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 3 := by
  set f : (Fin 2 → Bool) → Bool := fun x => xor (x 0) (x 1)
  constructor
  · let τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ := fun x y => if x 0 ≠ y 0 then 0 else 1
    refine ⟨τ, ?_, ?_⟩
    · intro x y hx hy
      by_cases h0 : x 0 ≠ y 0
      · exact ⟨0, by simp [τ, h0], h0⟩
      · have heq0 : x 0 = y 0 := not_not.mp h0
        have h1 : x 1 ≠ y 1 := by
          intro heq1
          have : f x = f y := by simp [f, heq0, heq1]
          rw [hx, hy] at this
          exact Bool.noConfusion this
        exact ⟨1, by simp [τ, h0], h1⟩
    · have hle1 : ∀ (i : Fin 2) (b : Bool),
          (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank ≤ 1 := by
        intro i b
        let x₀ : Fin 2 → Bool := fun k => if k = i then b else !b
        refine L_meta_210_rank_le_one_of_single_row _ x₀ fun x y hx => ?_
        simp only [PEqualNP.MetaComplexity.typedMatrix, ite_eq_right_iff, one_ne_zero, imp_false]
        rintro ⟨hfx, _, _, hxi⟩
        apply hx
        ext k
        fin_cases i <;> fin_cases k <;>
          cases hb : b <;> cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all [f, x₀]
      calc
        ∑ i : Fin 2, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank
          ≤ ∑ _i : Fin 2, ∑ _b : Bool, 1 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hle1 i b
        _ = 4 := by decide
  · rintro ⟨τ, hτ, hr⟩
    have hge1 : ∀ (i : Fin 2) (b : Bool),
        1 ≤ (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank := by
      intro i b
      let x₀ : Fin 2 → Bool := fun k => if k = i then b else !b
      let y₀ : Fin 2 → Bool := Function.update x₀ i (!b)
      have hfx : f x₀ = true := by fin_cases i <;> cases b <;> decide
      have hfy : f y₀ = false := by fin_cases i <;> cases b <;> decide
      obtain ⟨j, hj, hne⟩ := hτ x₀ y₀ hfx hfy
      have hji : j = i := by
        by_contra hne'
        exact hne (by simp [y₀, Function.update_of_ne hne'])
      subst hji
      have hx0j : x₀ j = b := by simp [x₀]
      have hentry : PEqualNP.MetaComplexity.typedMatrix 2 f τ j b x₀ y₀ ≠ 0 := by
        simp [PEqualNP.MetaComplexity.typedMatrix, hfx, hfy, hj, hx0j]
      exact L_meta_210_rank_pos_of_entry_ne_zero _ hentry
    have hge : 4 ≤ ∑ i : Fin 2, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank := by
      calc
        4 = ∑ _i : Fin 2, ∑ _b : Bool, 1 := by decide
        _ ≤ ∑ i : Fin 2, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f τ i b).rank :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hge1 i b
    omega
