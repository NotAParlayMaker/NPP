import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

theorem PEqualNP.Outside.L_gct_108 : ∀ (q : ℕ), 2 ≤ q → ∃ L : Submodule ℂ (Fin 2 × Fin q → ℂ), (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) ∧ Module.finrank ℂ L + 1 = q := by
  intro q hq
  classical
  let : NeZero q := ⟨by omega⟩
  let total : (Fin q → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => ∑ j, x j
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by simp [Finset.mul_sum] }
  have onto : Function.Surjective total := by
    intro a
    refine ⟨fun j => if j = 0 then a else 0, ?_⟩
    change (∑ j : Fin q, if j = 0 then a else 0) = a
    simp

  -- Put a sum-zero vector in the first row and fill the second row with zeros.
  let firstRow : total.ker →ₗ[ℂ] (Fin 2 × Fin q → ℂ) :=
    { toFun := fun x p => if p.1 = 0 then x.val p.2 else 0
      map_add' := fun x y => by
        funext p
        by_cases h : p.1 = 0 <;> simp [h]
      map_smul' := fun a x => by
        funext p
        by_cases h : p.1 = 0 <;> simp [h] }
  have inj : Function.Injective firstRow := by
    intro x y h
    apply Subtype.ext
    funext j
    simpa [firstRow] using congrFun h (0, j)

  refine ⟨firstRow.range, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    have hx : (∑ j, x.val j) = 0 := x.property
    constructor
    · simpa [firstRow] using hx
    · simp [firstRow]
  · have rankNullity := total.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr onto, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at rankNullity
    rw [LinearMap.finrank_range_of_inj inj]
    omega
