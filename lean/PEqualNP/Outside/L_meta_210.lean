import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_210_aux

open PEqualNP.MetaComplexity

/-- A matrix that vanishes off one entry has rank at most one. -/
theorem rank_le_one_of_single {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℚ) (x₀ : m) (y₀ : n) (h : ∀ x y, (x ≠ x₀ ∨ y ≠ y₀) → M x y = 0) :
    M.rank ≤ 1 := by
  have hM : M = Matrix.vecMulVec (Pi.single x₀ (M x₀ y₀)) (Pi.single y₀ 1) := by
    ext x y
    simp only [Matrix.vecMulVec_apply]
    by_cases hx : x = x₀ <;> by_cases hy : y = y₀
    · subst hx; subst hy; simp
    · rw [h x y (Or.inr hy)]; simp [hy]
    · rw [h x y (Or.inl hx)]; simp [hx]
    · rw [h x y (Or.inl hx)]; simp [hx]
  rw [hM]
  exact Matrix.rank_vecMulVec_le _ _

/-- A matrix with a nonzero entry has rank at least one. -/
theorem one_le_rank_of_entry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℚ) (x : m) (y : n) (h : M x y ≠ 0) : 1 ≤ M.rank := by
  unfold Matrix.rank
  have hv : M.mulVec (Pi.single y 1) ∈ LinearMap.range M.mulVecLin := ⟨Pi.single y 1, rfl⟩
  have hne : M.mulVec (Pi.single y 1) ≠ 0 := by
    intro h0
    have := congrFun h0 x
    simp at this
    exact h this
  rw [Nat.one_le_iff_ne_zero]
  intro hz
  rw [Submodule.finrank_eq_zero] at hz
  rw [hz] at hv
  exact hne ((Submodule.mem_bot ℚ).1 hv)

end PEqualNP.Outside.L_meta_210_aux

open PEqualNP.Outside.L_meta_210_aux PEqualNP.MetaComplexity in
/-- The four (true, false) pairs of the parity of two inputs each differ in one position only,
so every typing is forced, and each of the four literal matrices has exactly one nonzero entry:
the rank sum is exactly four. -/
theorem PEqualNP.Outside.L_meta_210 : PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 4 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 3 := by
  constructor
  · let τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ := fun x y => if x 0 = y 0 then 1 else 0
    refine ⟨τ, ?_, ?_⟩
    · unfold IsTyping
      decide
    · have h0t : (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ 0 true).rank ≤ 1 := by
        apply rank_le_one_of_single _ ![true, false] ![false, false]
        intro x y hxy
        have : ¬ ((fun x : Fin 2 → Bool => xor (x 0) (x 1)) x = true ∧
            (fun x : Fin 2 → Bool => xor (x 0) (x 1)) y = false ∧ τ x y = ((0 : Fin 2) : ℕ) ∧
            x 0 = true) := by revert x y; decide
        simp only [typedMatrix]; rw [if_neg this]
      have h0f : (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ 0 false).rank ≤ 1 := by
        apply rank_le_one_of_single _ ![false, true] ![true, true]
        intro x y hxy
        have : ¬ ((fun x : Fin 2 → Bool => xor (x 0) (x 1)) x = true ∧
            (fun x : Fin 2 → Bool => xor (x 0) (x 1)) y = false ∧ τ x y = ((0 : Fin 2) : ℕ) ∧
            x 0 = false) := by revert x y; decide
        simp only [typedMatrix]; rw [if_neg this]
      have h1t : (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ 1 true).rank ≤ 1 := by
        apply rank_le_one_of_single _ ![false, true] ![false, false]
        intro x y hxy
        have : ¬ ((fun x : Fin 2 → Bool => xor (x 0) (x 1)) x = true ∧
            (fun x : Fin 2 → Bool => xor (x 0) (x 1)) y = false ∧ τ x y = ((1 : Fin 2) : ℕ) ∧
            x 1 = true) := by revert x y; decide
        simp only [typedMatrix]; rw [if_neg this]
      have h1f : (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ 1 false).rank ≤ 1 := by
        apply rank_le_one_of_single _ ![true, false] ![true, true]
        intro x y hxy
        have : ¬ ((fun x : Fin 2 → Bool => xor (x 0) (x 1)) x = true ∧
            (fun x : Fin 2 → Bool => xor (x 0) (x 1)) y = false ∧ τ x y = ((1 : Fin 2) : ℕ) ∧
            x 1 = false) := by revert x y; decide
        simp only [typedMatrix]; rw [if_neg this]
      simp only [Fin.sum_univ_two, Fintype.sum_bool]
      omega
  · rintro ⟨τ, hτ, hsum⟩
    have forced : ∀ x y : Fin 2 → Bool, xor (x 0) (x 1) = true → xor (y 0) (y 1) = false →
        ∀ j : Fin 2, (∀ i : Fin 2, x i ≠ y i → i = j) → τ x y = j := by
      intro x y hx hy j hj
      obtain ⟨i, hi, hne⟩ := hτ x y hx hy
      rw [hi, hj i hne]
    have e0t := forced ![true, false] ![false, false] (by decide) (by decide) 0 (by decide)
    have e0f := forced ![false, true] ![true, true] (by decide) (by decide) 0 (by decide)
    have e1t := forced ![false, true] ![false, false] (by decide) (by decide) 1 (by decide)
    have e1f := forced ![true, false] ![true, true] (by decide) (by decide) 1 (by decide)
    have r0t := one_le_rank_of_entry (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ 0 true)
      ![true, false] ![false, false] (by simp [typedMatrix, e0t])
    have r0f := one_le_rank_of_entry (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ 0 false)
      ![false, true] ![true, true] (by simp [typedMatrix, e0f])
    have r1t := one_le_rank_of_entry (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ 1 true)
      ![false, true] ![false, false] (by simp [typedMatrix, e1t])
    have r1f := one_le_rank_of_entry (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ 1 false)
      ![true, false] ![true, true] (by simp [typedMatrix, e1f])
    simp only [Fin.sum_univ_two, Fintype.sum_bool] at hsum
    omega
