import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_221_aux

theorem sumPerm4 (f : Equiv.Perm (Fin 4) → ℂ) : ∑ σ, f σ =
    ∑ a : Fin 4, ∑ b : Fin 3, ∑ c : Fin 2, ∑ d : Fin 1,
      f (Equiv.Perm.decomposeFin.symm (a, Equiv.Perm.decomposeFin.symm (b,
        Equiv.Perm.decomposeFin.symm (c, Equiv.Perm.decomposeFin.symm (d, 1))))) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_unique]
  rfl

theorem key (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ∑ σ : Equiv.Perm (Fin 4), F (σ 0) (σ 1) (σ 2) (σ 3) =
    (((F 0 1 2 3 + F 0 1 3 2) + ((F 0 2 1 3 + F 0 2 3 1) + (F 0 3 2 1 + F 0 3 1 2))) + (((F 1 0 2 3 + F 1 0 3 2) + ((F 1 2 0 3 + F 1 2 3 0) + (F 1 3 2 0 + F 1 3 0 2))) + (((F 2 1 0 3 + F 2 1 3 0) + ((F 2 0 1 3 + F 2 0 3 1) + (F 2 3 0 1 + F 2 3 1 0))) + ((F 3 1 2 0 + F 3 1 0 2) + ((F 3 2 1 0 + F 3 2 0 1) + (F 3 0 2 1 + F 3 0 1 2)))))) := by
  rw [sumPerm4]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

end PEqualNP.Outside.L_gct_221_aux

open PEqualNP.Outside.L_gct_221_aux in
theorem PEqualNP.Outside.L_gct_221 : Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + (![1, Complex.I, -1, -Complex.I] : Fin 4 → ℂ) (j - i)) = 48 := by
  let T : Fin 4 → Fin 4 → ℂ := fun i s =>
    1 + (![1, Complex.I, -1, -Complex.I] : Fin 4 → ℂ) (i - s)
  have hT : ∀ σ : Equiv.Perm (Fin 4), ∀ i : Fin 4,
      (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + (![1, Complex.I, -1, -Complex.I] : Fin 4 → ℂ) (j - i))
        (σ i) i = T i (σ i) := by
    intro σ i
    rfl
  rw [Matrix.permanent]
  simp only [hT, Fin.prod_univ_four]
  rw [key (fun a b c d => T 0 a * T 1 b * T 2 c * T 3 d)]
  have t00 : T 0 0 = 1 + 1 := by simp only [T]; rw [show (0 : Fin 4) - 0 = 0 by decide]; rfl
  have t01 : T 0 1 = 1 + -Complex.I := by simp only [T]; rw [show (0 : Fin 4) - 1 = 3 by decide]; rfl
  have t02 : T 0 2 = 1 + -1 := by simp only [T]; rw [show (0 : Fin 4) - 2 = 2 by decide]; rfl
  have t03 : T 0 3 = 1 + Complex.I := by simp only [T]; rw [show (0 : Fin 4) - 3 = 1 by decide]; rfl
  have t10 : T 1 0 = 1 + Complex.I := by simp only [T]; rw [show (1 : Fin 4) - 0 = 1 by decide]; rfl
  have t11 : T 1 1 = 1 + 1 := by simp only [T]; rw [show (1 : Fin 4) - 1 = 0 by decide]; rfl
  have t12 : T 1 2 = 1 + -Complex.I := by simp only [T]; rw [show (1 : Fin 4) - 2 = 3 by decide]; rfl
  have t13 : T 1 3 = 1 + -1 := by simp only [T]; rw [show (1 : Fin 4) - 3 = 2 by decide]; rfl
  have t20 : T 2 0 = 1 + -1 := by simp only [T]; rw [show (2 : Fin 4) - 0 = 2 by decide]; rfl
  have t21 : T 2 1 = 1 + Complex.I := by simp only [T]; rw [show (2 : Fin 4) - 1 = 1 by decide]; rfl
  have t22 : T 2 2 = 1 + 1 := by simp only [T]; rw [show (2 : Fin 4) - 2 = 0 by decide]; rfl
  have t23 : T 2 3 = 1 + -Complex.I := by simp only [T]; rw [show (2 : Fin 4) - 3 = 3 by decide]; rfl
  have t30 : T 3 0 = 1 + -Complex.I := by simp only [T]; rw [show (3 : Fin 4) - 0 = 3 by decide]; rfl
  have t31 : T 3 1 = 1 + -1 := by simp only [T]; rw [show (3 : Fin 4) - 1 = 2 by decide]; rfl
  have t32 : T 3 2 = 1 + Complex.I := by simp only [T]; rw [show (3 : Fin 4) - 2 = 1 by decide]; rfl
  have t33 : T 3 3 = 1 + 1 := by simp only [T]; rw [show (3 : Fin 4) - 3 = 0 by decide]; rfl
  simp only [t00, t01, t02, t03, t10, t11, t12, t13, t20, t21, t22, t23, t30, t31, t32, t33]
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  simp only [h3, h4, Complex.I_sq]
  ring_nf
