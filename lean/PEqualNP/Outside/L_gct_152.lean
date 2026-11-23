import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

theorem PEqualNP.Outside.L_gct_152 : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V) (v : V) (A : Submodule ℂ V), B.Nondegenerate → B.IsSymm → B v v ≠ 0 → (∀ a ∈ A, B v a = 0) → (∀ a ∈ A, ∀ a' ∈ A, B a a' = 0) → 2 * Module.finrank ℂ A + 1 ≤ Module.finrank ℂ V := by
  intro V _ _ _ B v A nondeg symm hv horth hiso
  have hsub : A ≤ B.orthogonal A :=
    fun x hx y hy => hiso y hy x hx
  have hvOrth : v ∈ B.orthogonal A :=
    fun a ha => (symm.eq a v).trans (horth a ha)
  have hproper : A < B.orthogonal A := by
    refine lt_of_le_not_ge hsub (fun h => ?_)
    exact hv (horth v (h hvOrth))
  have hdim := Submodule.finrank_lt_finrank_of_lt hproper
  rw [LinearMap.BilinForm.finrank_orthogonal nondeg] at hdim
  omega
