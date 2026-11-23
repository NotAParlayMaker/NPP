import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

namespace L_meta_208_Aux

def f2 (x : Fin 2 → Bool) : Bool := x 0 && x 1

def τ2 (x y : Fin 2 → Bool) : ℕ := if y 0 = false then 0 else 1

theorem τ2_typing : PEqualNP.MetaComplexity.IsTyping 2 f2 τ2 := by
  intro x y hx hy
  simp only [f2, Bool.and_eq_true] at hx
  by_cases hy0 : y 0 = false
  · refine ⟨0, ?_, ?_⟩
    · simp [τ2, hy0]
    · simp [hx.1, hy0]
  · have hy1 : y 1 = false := by simpa [f2, hy0] using hy
    refine ⟨1, ?_, ?_⟩
    · simp [τ2, hy0]
    · simp [hx.2, hy1]

theorem M00_zero :
    (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 0 false) = 0 := by
  ext x y
  simp only [PEqualNP.MetaComplexity.typedMatrix]
  by_cases h : x 0 = false
  · simp [f2, τ2, h]
  · simp [f2, τ2, h]

theorem M10_zero :
    (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 1 false) = 0 := by
  ext x y
  simp only [PEqualNP.MetaComplexity.typedMatrix]
  by_cases h : x 1 = false
  · simp [f2, τ2, h]
  · simp [f2, τ2, h]

theorem M0t_vecMulVec :
    (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 0 true)
      = Matrix.vecMulVec (fun x : Fin 2 → Bool => if x 0 ∧ x 1 then (1 : ℚ) else 0)
          (fun y : Fin 2 → Bool => if f2 y = false ∧ y 0 = false then (1 : ℚ) else 0) := by
  ext x y
  simp only [PEqualNP.MetaComplexity.typedMatrix, Matrix.vecMulVec_apply]
  by_cases hA : x 0 = true ∧ x 1 = true
  · have hfx : f2 x = true := by simp [f2, hA]
    by_cases hB : f2 y = false ∧ y 0 = false
    · have hC : (f2 x = true ∧ f2 y = false ∧ τ2 x y = 0 ∧ x 0 = true) := by
        simp [hfx, hB, τ2, hB.2, hA.1]
      simp [hC, hA, hB]
    · simp [hA, hB, f2, τ2]
  · simp [hA, f2, τ2]

theorem M1t_vecMulVec :
    (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 1 true)
      = Matrix.vecMulVec (fun x : Fin 2 → Bool => if x 0 ∧ x 1 then (1 : ℚ) else 0)
          (fun y : Fin 2 → Bool => if f2 y = false ∧ y 0 = true then (1 : ℚ) else 0) := by
  ext x y
  simp only [PEqualNP.MetaComplexity.typedMatrix, Matrix.vecMulVec_apply]
  by_cases hA : x 0 = true ∧ x 1 = true
  · have hfx : f2 x = true := by simp [f2, hA]
    by_cases hB : f2 y = false ∧ y 0 = true
    · have hC : (f2 x = true ∧ f2 y = false ∧ τ2 x y = 1 ∧ x 1 = true) := by
        simp [hfx, hB, τ2, hB.2, hA.2]
      simp [hC, hA, hB]
    · simp [hA, hB, f2, τ2]
  · simp [hA, f2, τ2]

theorem upper : PEqualNP.MetaComplexity.HasTypedRank 2 f2 2 := by
  refine ⟨τ2, τ2_typing, ?_⟩
  have h0 : ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 0 b).rank ≤ 1 := by
    rw [Fintype.sum_bool]
    have hf : (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 0 false).rank = 0 := by
      rw [M00_zero, Matrix.rank_zero]
    have ht : (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 0 true).rank ≤ 1 := by
      rw [M0t_vecMulVec]
      exact Matrix.rank_vecMulVec_le _ _
    omega
  have h1' : ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 1 b).rank ≤ 1 := by
    rw [Fintype.sum_bool]
    have hf : (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 1 false).rank = 0 := by
      rw [M10_zero, Matrix.rank_zero]
    have ht : (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ2 1 true).rank ≤ 1 := by
      rw [M1t_vecMulVec]
      exact Matrix.rank_vecMulVec_le _ _
    omega
  rw [Fin.sum_univ_two]
  omega

theorem lower : ¬ PEqualNP.MetaComplexity.HasTypedRank 2 f2 1 := by
  rintro ⟨τ, htyping, hsum⟩
  have h11 : f2 (fun _ : Fin 2 => true) = true := by simp [f2]
  have h10 : f2 (fun i : Fin 2 => i = 0) = false := by simp [f2]
  have h01 : f2 (fun i : Fin 2 => i = 1) = false := by simp [f2]
  obtain ⟨k1, hk1, hne1⟩ := htyping (fun _ => true) (fun i => i = 0) h11 h10
  obtain ⟨k0, hk0, hne0⟩ := htyping (fun _ => true) (fun i => i = 1) h11 h01
  fin_cases k1
  · simp at hne1
  · fin_cases k0
    · have he0 : PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 0 true
          (fun _ => true) (fun i => i = 1) = 1 := by
        simp [PEqualNP.MetaComplexity.typedMatrix, hk0, h11, h01]
      have he1 : PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 1 true
          (fun _ => true) (fun i => i = 0) = 1 := by
        simp [PEqualNP.MetaComplexity.typedMatrix, hk1, h11, h10]
      have hsub0 : (1 : Matrix (Fin 1) (Fin 1) ℚ)
          = (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 0 true).submatrix
              (fun _ => fun _ => true) (fun _ => fun i => i = 1) := by
        ext (i : Fin 1) (j : Fin 1)
        fin_cases i <;> fin_cases j
        rw [Matrix.one_apply_eq]
        exact he0.symm
      have hsub1 : (1 : Matrix (Fin 1) (Fin 1) ℚ)
          = (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 1 true).submatrix
              (fun _ => fun _ => true) (fun _ => fun i => i = 0) := by
        ext (i : Fin 1) (j : Fin 1)
        fin_cases i <;> fin_cases j
        rw [Matrix.one_apply_eq]
        exact he1.symm
      have hr0 : 1 ≤ (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 0 true).rank := by
        have hle := Matrix.rank_submatrix_le
            (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 0 true)
            (fun _ : Fin 1 => (fun _ : Fin 2 => true))
            (fun _ : Fin 1 => (fun i : Fin 2 => i = 1))
        have hsubrank : ((PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 0 true).submatrix
            (fun _ : Fin 1 => (fun _ : Fin 2 => true))
            (fun _ : Fin 1 => (fun i : Fin 2 => i = 1))).rank = 1 := by
          rw [← hsub0]
          simp
        rw [hsubrank] at hle
        exact hle
      have hr1 : 1 ≤ (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 1 true).rank := by
        have hle := Matrix.rank_submatrix_le
            (PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 1 true)
            (fun _ : Fin 1 => (fun _ : Fin 2 => true))
            (fun _ : Fin 1 => (fun i : Fin 2 => i = 0))
        have hsubrank : ((PEqualNP.MetaComplexity.typedMatrix 2 f2 τ 1 true).submatrix
            (fun _ : Fin 1 => (fun _ : Fin 2 => true))
            (fun _ : Fin 1 => (fun i : Fin 2 => i = 0))).rank = 1 := by
          rw [← hsub1]
          simp
        rw [hsubrank] at hle
        exact hle
      rw [Fin.sum_univ_two] at hsum
      rw [Fintype.sum_bool, Fintype.sum_bool] at hsum
      omega
    · simp at hne0

end L_meta_208_Aux

open L_meta_208_Aux in
theorem L_meta_208 :
    PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 2 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 1 :=
  ⟨L_meta_208_Aux.upper, L_meta_208_Aux.lower⟩

end PEqualNP.Outside
