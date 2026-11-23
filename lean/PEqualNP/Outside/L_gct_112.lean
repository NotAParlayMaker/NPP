import Mathlib
import PEqualNP.Defs

open Equiv Finset Matrix

set_option maxHeartbeats 2000000

private def colF : Fin 24 → Fin 4 → Fin 4
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 3
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 3
  | 1, 3 => 2
  | 2, 0 => 0
  | 2, 1 => 2
  | 2, 2 => 1
  | 2, 3 => 3
  | 3, 0 => 0
  | 3, 1 => 2
  | 3, 2 => 3
  | 3, 3 => 1
  | 4, 0 => 0
  | 4, 1 => 3
  | 4, 2 => 1
  | 4, 3 => 2
  | 5, 0 => 0
  | 5, 1 => 3
  | 5, 2 => 2
  | 5, 3 => 1
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 2
  | 6, 3 => 3
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 3
  | 7, 3 => 2
  | 8, 0 => 1
  | 8, 1 => 2
  | 8, 2 => 0
  | 8, 3 => 3
  | 9, 0 => 1
  | 9, 1 => 2
  | 9, 2 => 3
  | 9, 3 => 0
  | 10, 0 => 1
  | 10, 1 => 3
  | 10, 2 => 0
  | 10, 3 => 2
  | 11, 0 => 1
  | 11, 1 => 3
  | 11, 2 => 2
  | 11, 3 => 0
  | 12, 0 => 2
  | 12, 1 => 0
  | 12, 2 => 1
  | 12, 3 => 3
  | 13, 0 => 2
  | 13, 1 => 0
  | 13, 2 => 3
  | 13, 3 => 1
  | 14, 0 => 2
  | 14, 1 => 1
  | 14, 2 => 0
  | 14, 3 => 3
  | 15, 0 => 2
  | 15, 1 => 1
  | 15, 2 => 3
  | 15, 3 => 0
  | 16, 0 => 2
  | 16, 1 => 3
  | 16, 2 => 0
  | 16, 3 => 1
  | 17, 0 => 2
  | 17, 1 => 3
  | 17, 2 => 1
  | 17, 3 => 0
  | 18, 0 => 3
  | 18, 1 => 0
  | 18, 2 => 1
  | 18, 3 => 2
  | 19, 0 => 3
  | 19, 1 => 0
  | 19, 2 => 2
  | 19, 3 => 1
  | 20, 0 => 3
  | 20, 1 => 1
  | 20, 2 => 0
  | 20, 3 => 2
  | 21, 0 => 3
  | 21, 1 => 1
  | 21, 2 => 2
  | 21, 3 => 0
  | 22, 0 => 3
  | 22, 1 => 2
  | 22, 2 => 0
  | 22, 3 => 1
  | 23, 0 => 3
  | 23, 1 => 2
  | 23, 2 => 1
  | 23, 3 => 0
  | _, _ => 0

private lemma colF_bijective (k : Fin 24) : Function.Bijective (colF k) := by
  fin_cases k <;> decide

noncomputable def toPerm (k : Fin 24) : Perm (Fin 4) :=
  Equiv.ofBijective (colF k) (colF_bijective k)

private lemma colF_inj : Function.Injective (fun k : Fin 24 => colF k) := by
  decide

private lemma toPerm_inj : Function.Injective toPerm := by
  intro a b h
  apply colF_inj
  funext i
  have hcoe : (toPerm a : Fin 4 → Fin 4) = toPerm b := congrArg DFunLike.coe h
  simpa [toPerm] using congrFun hcoe i

private lemma toPerm_bij : Function.Bijective toPerm :=
  (Fintype.bijective_iff_injective_and_card toPerm).2
    ⟨toPerm_inj, by simp [Fintype.card_perm, Fintype.card_fin]; decide⟩

noncomputable def enumPerm : Fin 24 ≃ Perm (Fin 4) :=
  Equiv.ofBijective toPerm toPerm_bij

private lemma enum_apply (k : Fin 24) (i : Fin 4) : enumPerm k i = colF k i := rfl

private lemma sum24 (f : Fin 24 → ℂ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 := by
  repeat rw [Fin.sum_univ_succ]
  simp
  abel

theorem PEqualNP.Outside.L_gct_112 : ∀ w : Fin 4 × Fin 4 → ℂ, MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 4) = (w (0, 0) * w (1, 1) + w (0, 1) * w (1, 0)) * (w (2, 2) * w (3, 3) + w (2, 3) * w (3, 2)) + (w (0, 0) * w (1, 2) + w (0, 2) * w (1, 0)) * (w (2, 1) * w (3, 3) + w (2, 3) * w (3, 1)) + (w (0, 0) * w (1, 3) + w (0, 3) * w (1, 0)) * (w (2, 1) * w (3, 2) + w (2, 2) * w (3, 1)) + (w (0, 1) * w (1, 2) + w (0, 2) * w (1, 1)) * (w (2, 0) * w (3, 3) + w (2, 3) * w (3, 0)) + (w (0, 1) * w (1, 3) + w (0, 3) * w (1, 1)) * (w (2, 0) * w (3, 2) + w (2, 2) * w (3, 0)) + (w (0, 2) * w (1, 3) + w (0, 3) * w (1, 2)) * (w (2, 0) * w (3, 1) + w (2, 1) * w (3, 0)) := by
  intro w
  let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun i j => w (i, j)
  have hEval : MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 4) = M.permanent := by
    simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, M]
  rw [hEval, ← Matrix.permanent_transpose]
  simp only [Matrix.permanent, Matrix.transpose_apply]
  rw [← enumPerm.sum_comp]
  simp only [Fin.prod_univ_four, enum_apply]
  rw [sum24]
  simp only [colF, M, Matrix.of_apply]
  ring
