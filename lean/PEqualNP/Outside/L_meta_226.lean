import Mathlib
import PEqualNP.Defs

def L_meta_226_flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update x i (!x i)

@[simp] theorem L_meta_226_flip_flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    L_meta_226_flip i (L_meta_226_flip i x) = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [L_meta_226_flip]
  · simp [L_meta_226_flip, Function.update_of_ne h]

def L_meta_226_equiv {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := L_meta_226_flip i
  invFun := L_meta_226_flip i
  left_inv := L_meta_226_flip_flip i
  right_inv := L_meta_226_flip_flip i

theorem PEqualNP.Outside.L_meta_226 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n) (s : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s →
    PEqualNP.MetaComplexity.HasTypedRank n (fun x => f (Function.update x i (!x i))) s := by
  intro n f i s ⟨τ, ht, hr⟩
  let σ := L_meta_226_equiv i
  let τ' := fun x y => τ (σ x) (σ y)
  have hd (x y : Fin n → Bool) (j : Fin n) : σ x j ≠ σ y j ↔ x j ≠ y j := by
    by_cases h : j = i
    · subst j
      simp [σ, L_meta_226_equiv, L_meta_226_flip]
    · simp [σ, L_meta_226_equiv, L_meta_226_flip, Function.update_of_ne h]
  have hm (j : Fin n) (b : Bool) :
      PEqualNP.MetaComplexity.typedMatrix n (fun x => f (Function.update x i (!x i))) τ' j b =
        (PEqualNP.MetaComplexity.typedMatrix n f τ j (if j = i then !b else b)).submatrix σ σ := by
    ext x y
    by_cases h : j = i
    · subst j
      cases b <;> simp [PEqualNP.MetaComplexity.typedMatrix, τ', σ, L_meta_226_equiv, L_meta_226_flip]
    · simp [PEqualNP.MetaComplexity.typedMatrix, τ', σ, L_meta_226_equiv, L_meta_226_flip, h]
  have hrank (j : Fin n) (b : Bool) :
      (PEqualNP.MetaComplexity.typedMatrix n (fun x => f (Function.update x i (!x i))) τ' j b).rank =
        (PEqualNP.MetaComplexity.typedMatrix n f τ j (if j = i then !b else b)).rank := by
    rw [hm, Matrix.rank_submatrix]
  refine ⟨τ', ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨j, hj, hdif⟩ := ht (σ x) (σ y) hx hy
    exact ⟨j, hj, (hd x y j).mp hdif⟩
  · calc
      _ = ∑ j : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [hrank]
        by_cases h : j = i
        · simp [h, Nat.add_comm]
        · simp [h]
      _ ≤ s := hr
