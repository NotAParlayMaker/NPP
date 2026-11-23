import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_234_aux
open PEqualNP.MetaComplexity

lemma le_rank_of_submatrix {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix m n ℚ) (k : ℕ) (f : Fin k → m) (g : Fin k → n)
    (h : IsUnit (M.submatrix f g).det) : k ≤ M.rank := by
  have hS : M.submatrix f g = (Matrix.of fun i r => if r = f i then (1 : ℚ) else 0) * M *
      (Matrix.of fun c j => if c = g j then (1 : ℚ) else 0) := by
    ext i j
    simp [Matrix.mul_apply, ite_mul, mul_ite]
  have hk : (M.submatrix f g).rank = k := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr h)]
    simp
  calc k = (M.submatrix f g).rank := hk.symm
    _ ≤ M.rank := by
      rw [hS]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

abbrev F : (Fin 3 → Bool) → Bool :=
  fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)

abbrev e0 : Fin 3 → Bool := ![true, false, false]
abbrev e1 : Fin 3 → Bool := ![false, true, false]
abbrev e2 : Fin 3 → Bool := ![false, false, true]
abbrev y01 : Fin 3 → Bool := ![true, true, false]
abbrev y02 : Fin 3 → Bool := ![true, false, true]
abbrev y12 : Fin 3 → Bool := ![false, true, true]

-- the position a typing gives a pair, as one of the positions where the pair differs
lemma typ {τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ} (hτ : IsTyping 3 F τ)
    (x y : Fin 3 → Bool) (hx : F x = true) (hy : F y = false) :
    ∃ i : Fin 3, τ x y = (i : ℕ) ∧ x i ≠ y i := hτ x y hx hy

-- one nonzero entry gives rank at least one
lemma one_le (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (i : Fin 3) (x y : Fin 3 → Bool)
    (h : typedMatrix 3 F τ i false x y = 1) : 1 ≤ (typedMatrix 3 F τ i false).rank := by
  apply le_rank_of_submatrix _ 1 ![x] ![y]
  rw [Matrix.det_fin_one]
  simp [h]

-- a two by two pattern with ones on the diagonal and a zero off it gives rank at least two
lemma two_le (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (i : Fin 3) (x1 x2 y1 y2 : Fin 3 → Bool)
    (h1 : typedMatrix 3 F τ i false x1 y1 = 1) (h2 : typedMatrix 3 F τ i false x2 y2 = 1)
    (h3 : typedMatrix 3 F τ i false x1 y2 = 0 ∨ typedMatrix 3 F τ i false x2 y1 = 0) :
    2 ≤ (typedMatrix 3 F τ i false).rank := by
  apply le_rank_of_submatrix _ 2 ![x1, x2] ![y1, y2]
  rw [Matrix.det_fin_two]
  rcases h3 with h3 | h3 <;> simp [h1, h2, h3]

lemma main : ¬ HasTypedRank 3 F 4 := by
  rintro ⟨τ, hτ, hs⟩
  -- the six pairs that differ in one position only
  have a1 : τ e0 y01 = 1 := by
    obtain ⟨i, hi, hd⟩ := typ hτ e0 y01 (by decide) (by decide)
    fin_cases i <;> simp_all
  have a2 : τ e0 y02 = 2 := by
    obtain ⟨i, hi, hd⟩ := typ hτ e0 y02 (by decide) (by decide)
    fin_cases i <;> simp_all
  have b0 : τ e1 y01 = 0 := by
    obtain ⟨i, hi, hd⟩ := typ hτ e1 y01 (by decide) (by decide)
    fin_cases i <;> simp_all
  have b2 : τ e1 y12 = 2 := by
    obtain ⟨i, hi, hd⟩ := typ hτ e1 y12 (by decide) (by decide)
    fin_cases i <;> simp_all
  have c0 : τ e2 y02 = 0 := by
    obtain ⟨i, hi, hd⟩ := typ hτ e2 y02 (by decide) (by decide)
    fin_cases i <;> simp_all
  have c1 : τ e2 y12 = 1 := by
    obtain ⟨i, hi, hd⟩ := typ hτ e2 y12 (by decide) (by decide)
    fin_cases i <;> simp_all
  -- the three cross pairs
  obtain ⟨p, hp, -⟩ := typ hτ e0 y12 (by decide) (by decide)
  obtain ⟨q, hq, -⟩ := typ hτ e2 y01 (by decide) (by decide)
  obtain ⟨r, hr, -⟩ := typ hτ e1 y02 (by decide) (by decide)
  have hsum : (typedMatrix 3 F τ 0 false).rank + (typedMatrix 3 F τ 1 false).rank +
      (typedMatrix 3 F τ 2 false).rank ≤ 4 := by
    refine le_trans ?_ hs
    simp only [Fin.sum_univ_three, Fintype.sum_bool]
    omega
  have r0 := one_le τ 0 e1 y01 (by simp [typedMatrix, b0])
  have r1 := one_le τ 1 e0 y01 (by simp [typedMatrix, a1])
  have r2 := one_le τ 2 e0 y02 (by simp [typedMatrix, a2])
  -- each matrix has rank at least two unless both of its cross pairs sit at its position
  have k0 : τ e1 y02 ≠ 0 ∨ τ e2 y01 ≠ 0 → 2 ≤ (typedMatrix 3 F τ 0 false).rank := by
    intro h
    apply two_le τ 0 e1 e2 y01 y02 (by simp [typedMatrix, b0]) (by simp [typedMatrix, c0])
    rcases h with h | h
    · left; simp [typedMatrix, h]
    · right; simp [typedMatrix, h]
  have k1 : τ e0 y12 ≠ 1 ∨ τ e2 y01 ≠ 1 → 2 ≤ (typedMatrix 3 F τ 1 false).rank := by
    intro h
    apply two_le τ 1 e0 e2 y01 y12 (by simp [typedMatrix, a1]) (by simp [typedMatrix, c1])
    rcases h with h | h
    · left; simp [typedMatrix, h]
    · right; simp [typedMatrix, h]
  have k2 : τ e0 y12 ≠ 2 ∨ τ e1 y02 ≠ 2 → 2 ≤ (typedMatrix 3 F τ 2 false).rank := by
    intro h
    apply two_le τ 2 e0 e1 y02 y12 (by simp [typedMatrix, a2]) (by simp [typedMatrix, b2])
    rcases h with h | h
    · left; simp [typedMatrix, h]
    · right; simp [typedMatrix, h]
  -- a cross pair sits at one position only, so at most one matrix escapes
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp at hp hq hr <;>
    rw [hp, hq, hr] at * <;> simp at k0 k1 k2 <;> omega

end PEqualNP.Outside.L_meta_234_aux

theorem PEqualNP.Outside.L_meta_234 :
    ¬ PEqualNP.MetaComplexity.HasTypedRank 3
      (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 4 :=
  PEqualNP.Outside.L_meta_234_aux.main
