import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_152 : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V) (v : V) (A : Submodule ℂ V), B.Nondegenerate → B.IsSymm → B v v ≠ 0 → (∀ a ∈ A, B v a = 0) → (∀ a ∈ A, ∀ a' ∈ A, B a a' = 0) → 2 * Module.finrank ℂ A + 1 ≤ Module.finrank ℂ V := by
  intro V _ _ _ B v A hB hsymm hv horth hiso
  have hle : A ≤ B.orthogonal A := by
    intro a ha
    exact fun b hb => hiso b hb a ha
  have hv_orth : v ∈ B.orthogonal A := by
    intro a ha
    exact (LinearMap.BilinForm.IsSymm.eq_iff hsymm).mpr (horth a ha)
  have hlt : A < B.orthogonal A := by
    refine lt_of_le_of_ne hle fun heq => hv ?_
    have hvA : v ∈ A := heq.symm ▸ hv_orth
    exact hiso v hvA v hvA
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  rw [LinearMap.BilinForm.finrank_orthogonal hB A] at hdim
  omega
