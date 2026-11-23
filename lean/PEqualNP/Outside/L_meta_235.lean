import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L235

open PEqualNP.MetaComplexity

def F : (Fin 6 → Bool) → Bool := fun x => ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) ||
    ((x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))

def pt (i j : Fin 6) : Fin 6 → Bool := fun t => decide (t = i ∨ t = j)

theorem one_le_rank {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) (x : m) (y : n)
    (h : A x y ≠ 0) : 1 ≤ A.rank := by
  have hli : LinearIndependent ℚ ![A.transpose y] := by
    rw [linearIndependent_unique_iff]
    intro h0
    exact h (by simpa [Matrix.transpose_apply] using congrFun h0 x)
  have hle : Submodule.span ℚ (Set.range ![A.transpose y]) ≤ LinearMap.range A.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    fin_cases k
    exact ⟨y, rfl⟩
  have := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli] at this
  simpa [Matrix.rank] using this

theorem two_le_rank {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) (x1 x2 : m)
    (y1 y2 : n) (h11 : A x1 y1 ≠ 0) (h12 : A x1 y2 = 0) (h22 : A x2 y2 ≠ 0) : 2 ≤ A.rank := by
  have hli : LinearIndependent ℚ ![A.transpose y1, A.transpose y2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrFun hst x1
    simp [Matrix.transpose_apply, h12, h11] at e1
    subst e1
    have e2 := congrFun hst x2
    simp [Matrix.transpose_apply, h22] at e2
    exact ⟨rfl, e2⟩
  have hle : Submodule.span ℚ (Set.range ![A.transpose y1, A.transpose y2]) ≤ LinearMap.range A.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact ⟨y1, rfl⟩
    · exact ⟨y2, rfl⟩
  have := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli] at this
  simpa [Matrix.rank] using this

theorem forced (τ : (Fin 6 → Bool) → (Fin 6 → Bool) → ℕ) (hτ : IsTyping 6 F τ)
    (x y : Fin 6 → Bool) (i : Fin 6) (hx : F x = true) (hy : F y = false) (hxi : x i = true)
    (hd : ∀ j : Fin 6, x j ≠ y j → j = i) : typedMatrix 6 F τ i true x y ≠ 0 := by
  obtain ⟨j, hj, hne⟩ := hτ x y hx hy
  obtain rfl := hd j hne
  simp [typedMatrix, hx, hy, hj, hxi]

theorem unforced (τ : (Fin 6 → Bool) → (Fin 6 → Bool) → ℕ) (x y : Fin 6 → Bool) (i : Fin 6)
    (h : τ x y ≠ (i : ℕ)) : typedMatrix 6 F τ i true x y = 0 := by
  simp [typedMatrix, h]

theorem rank_one (τ : (Fin 6 → Bool) → (Fin 6 → Bool) → ℕ) (hτ : IsTyping 6 F τ) (i j : Fin 6)
    (hx : F (pt i j) = true) (hy : F (pt j j) = false) (hxi : pt i j i = true)
    (hd : ∀ t : Fin 6, pt i j t ≠ pt j j t → t = i) : 1 ≤ (typedMatrix 6 F τ i true).rank :=
  one_le_rank _ _ _ (forced τ hτ _ _ i hx hy hxi hd)

theorem pair (τ : (Fin 6 → Bool) → (Fin 6 → Bool) → ℕ) (hτ : IsTyping 6 F τ) (i j k : Fin 6)
    (hij : i ≠ j)
    (a1 : F (pt i j) = true) (a2 : F (pt i k) = true) (a3 : F (pt j k) = true)
    (b1 : F (pt i i) = false) (b2 : F (pt j j) = false) (b3 : F (pt k k) = false)
    (c1 : pt i j i = true) (c2 : pt i k i = true) (c3 : pt i j j = true) (c4 : pt j k j = true)
    (d1 : ∀ t : Fin 6, pt i j t ≠ pt j j t → t = i) (d2 : ∀ t : Fin 6, pt i k t ≠ pt k k t → t = i)
    (d3 : ∀ t : Fin 6, pt i j t ≠ pt i i t → t = j) (d4 : ∀ t : Fin 6, pt j k t ≠ pt k k t → t = j) :
    2 ≤ (typedMatrix 6 F τ i true).rank ∨ 2 ≤ (typedMatrix 6 F τ j true).rank := by
  by_cases h : τ (pt i j) (pt k k) = (i : ℕ)
  · right
    have hj : τ (pt i j) (pt k k) ≠ (j : ℕ) := by
      rw [h]; exact fun e => hij (Fin.ext e)
    exact two_le_rank _ (pt i j) (pt j k) (pt i i) (pt k k) (forced τ hτ _ _ j a1 b1 c3 d3)
      (unforced τ _ _ j hj) (forced τ hτ _ _ j a3 b3 c4 d4)
  · left
    exact two_le_rank _ (pt i j) (pt i k) (pt j j) (pt k k) (forced τ hτ _ _ i a1 b2 c1 d1)
      (unforced τ _ _ i h) (forced τ hτ _ _ i a2 b3 c2 d2)

end PEqualNP.Outside.L235

open PEqualNP.Outside.L235 in
theorem PEqualNP.Outside.L_meta_235 : ¬ PEqualNP.MetaComplexity.HasTypedRank 6 (fun x : Fin 6 → Bool => ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) ||
    ((x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))) 9 := by
  rintro ⟨τ, hτ, hsum⟩
  change PEqualNP.MetaComplexity.IsTyping 6 F τ at hτ
  change (∑ i : Fin 6, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 6 F τ i b).rank) ≤ 9 at hsum
  simp only [Fin.sum_univ_six, Fintype.sum_bool] at hsum
  have r0 := rank_one τ hτ 0 1 (by decide) (by decide) (by decide) (by decide)
  have r1 := rank_one τ hτ 1 2 (by decide) (by decide) (by decide) (by decide)
  have r2 := rank_one τ hτ 2 0 (by decide) (by decide) (by decide) (by decide)
  have r3 := rank_one τ hτ 3 4 (by decide) (by decide) (by decide) (by decide)
  have r4 := rank_one τ hτ 4 5 (by decide) (by decide) (by decide) (by decide)
  have r5 := rank_one τ hτ 5 3 (by decide) (by decide) (by decide) (by decide)
  have p01 := pair τ hτ 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have p02 := pair τ hτ 0 2 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have p12 := pair τ hτ 1 2 0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have p34 := pair τ hτ 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have p35 := pair τ hτ 3 5 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have p45 := pair τ hτ 4 5 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  omega
