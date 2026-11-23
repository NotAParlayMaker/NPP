import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_208_aux

open Finset

private abbrev Assignment := Fin 4 ↪ Fin 6
private abbrev Parameters := Fin 7 → ℂ

private def row (x : Parameters) : Fin 6 → ℂ :=
  ![x 0, x 1, x 2, x 3, x 4, -(x 0 + x 1 + x 2 + x 3 + x 4)]

private def col (x : Parameters) : Fin 4 → ℂ :=
  ![0, x 5, x 6, -(x 5 + x 6)]

private def cross (x : Parameters) (p : Fin 4 × Fin 6) : ℂ :=
  if p.1 = 0 then row x p.2 else if p.2 = 0 then col x p.1 else 0

private def param : Parameters →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := cross
  map_add' x y := by
    funext ⟨i,j⟩
    by_cases hi : i = 0
    · fin_cases j <;> simp [cross, hi, row]
      ring
    · by_cases hj : j = 0
      · fin_cases i <;> simp_all [cross, col]
        ring
      · simp [cross, hi, hj]
  map_smul' a x := by
    funext ⟨i,j⟩
    by_cases hi : i = 0
    · fin_cases j <;> simp [cross, hi, row]
      ring
    · by_cases hj : j = 0
      · fin_cases i <;> simp_all [cross, col]
        ring
      · simp [cross, hi, hj]

private theorem param_inj : Function.Injective param := by
  intro x y h
  funext i
  fin_cases i
  · exact congrFun h (0,0)
  · exact congrFun h (0,1)
  · exact congrFun h (0,2)
  · exact congrFun h (0,3)
  · exact congrFun h (0,4)
  · exact congrFun h (1,0)
  · exact congrFun h (2,0)

/-- Every column occurs equally often as the image of the first row. -/
private theorem row_total (a : Fin 6 → ℂ) (ha : ∑ j, a j = 0) :
    (∑ f : Assignment, a (f 0)) = 0 := by
  classical
  let count (j : Fin 6) := ∑ f : Assignment, if f 0 = j then (1 : ℂ) else 0
  have same (j : Fin 6) : count j = count 0 := by
    let e := Equiv.embeddingCongr (Equiv.refl (Fin 4)) (Equiv.swap (0 : Fin 6) j)
    have h := e.sum_comp (fun f : Assignment => if f 0 = 0 then (1 : ℂ) else 0)
    change (∑ f : Assignment, if Equiv.swap 0 j (f 0) = 0 then (1 : ℂ) else 0) = count 0 at h
    simpa only [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, count] using h
  calc
    _ = ∑ f : Assignment, ∑ j : Fin 6, (if f 0 = j then (1 : ℂ) else 0) * a j := by
      apply sum_congr rfl
      intro f _
      simp [ite_mul]
    _ = ∑ j : Fin 6, count j * a j := by
      rw [sum_comm]
      simp only [count, sum_mul]
    _ = 0 := by simp_rw [same]; rw [← mul_sum, ha, mul_zero]

private def weight (a : Fin 6 → ℂ) (i : Fin 4) (f : Assignment) : ℂ :=
  if f i = 0 then 1 + a (f 0) else 0

/-- Exchanging two nonfirst rows preserves the first-row factor. -/
private theorem weight_total (a : Fin 6 → ℂ) (i : Fin 4) (hi : i ≠ 0) :
    (∑ f : Assignment, weight a i f) = ∑ f : Assignment, weight a 1 f := by
  let e := Equiv.embeddingCongr (Equiv.swap (1 : Fin 4) i) (Equiv.refl (Fin 6))
  have h := e.sum_comp (weight a 1)
  change (∑ f : Assignment, if f (Equiv.swap 1 i 1) = 0 then
    1 + a (f (Equiv.swap 1 i 0)) else 0) = _ at h
  simpa [weight, Equiv.swap_apply_of_ne_of_ne (show (0 : Fin 4) ≠ 1 by decide) (Ne.symm hi)] using h

private theorem expand (x : Parameters) (f : Assignment) :
    (∏ i : Fin 4, (1 + cross x (i, f i))) =
      1 + row x (f 0) + weight (row x) 1 f * x 5 + weight (row x) 2 f * x 6 -
      weight (row x) 3 f * (x 5 + x 6) := by
  have h12 : f 1 ≠ f 2 := f.injective.ne (by decide)
  have h13 : f 1 ≠ f 3 := f.injective.ne (by decide)
  have h23 : f 2 ≠ f 3 := f.injective.ne (by decide)
  by_cases h1 : f 1 = 0 <;> by_cases h2 : f 2 = 0 <;> by_cases h3 : f 3 = 0 <;>
    simp_all [Fin.prod_univ_four, cross, weight, col] <;> ring

end PEqualNP.Outside.L_gct_208_aux

open Finset PEqualNP.Outside.L_gct_208_aux

theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 := by
  classical
  refine ⟨LinearMap.range param, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    change (∑ f : Assignment, ∏ i : Fin 4, (1 + cross x (i, f i))) = 360
    have hr : ∑ j, row x j = 0 := by simp [row, Fin.sum_univ_succ]
    have hc : Fintype.card Assignment = 360 := by
      rw [Fintype.card_embedding_eq]
      decide
    simp_rw [expand]
    simp only [sum_sub_distrib, sum_add_distrib, ← sum_mul, row_total _ hr,
      sum_const, card_univ, hc, nsmul_eq_mul]
    rw [weight_total _ 2 (by decide), weight_total _ 3 (by decide)]
    ring
  · rw [LinearMap.finrank_range_of_inj param_inj]
    simp [Parameters]
