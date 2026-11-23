import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct194

open Finset

private def entry (c d : ℂ) (j : Fin 4) (r : Fin 5) : ℂ :=
  1 + (if r.val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0)
       else c * (if j.val = r.val then (1 : ℂ) else if j.val = (r.val + 1) % 4 then Complex.I
                 else if j.val = (r.val + 2) % 4 then -Complex.I else -1))

private abbrev distinct4 (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : Prop :=
  p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧
  p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2

private def mkFun (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : Fin 4 → Fin 5
  | ⟨0, _⟩ => p.1
  | ⟨1, _⟩ => p.2.1
  | ⟨2, _⟩ => p.2.2.1
  | ⟨3, _⟩ => p.2.2.2

private lemma mkFun_injective {p : Fin 5 × Fin 5 × Fin 5 × Fin 5} (hp : distinct4 p) :
    Function.Injective (mkFun p) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [mkFun] at hij
  all_goals first
    | rfl
    | exact False.elim (hp.1 hij)
    | exact False.elim (hp.1 hij.symm)
    | exact False.elim (hp.2.1 hij)
    | exact False.elim (hp.2.1 hij.symm)
    | exact False.elim (hp.2.2.1 hij)
    | exact False.elim (hp.2.2.1 hij.symm)
    | exact False.elim (hp.2.2.2.1 hij)
    | exact False.elim (hp.2.2.2.1 hij.symm)
    | exact False.elim (hp.2.2.2.2.1 hij)
    | exact False.elim (hp.2.2.2.2.1 hij.symm)
    | exact False.elim (hp.2.2.2.2.2 hij)
    | exact False.elim (hp.2.2.2.2.2 hij.symm)

private def sumSlice (c d : ℂ) (a : Fin 5) : ℂ :=
  ∑ b : Fin 5, ∑ e : Fin 5, ∑ g : Fin 5,
    if distinct4 (a, b, e, g) then
      entry c d 0 a * entry c d 1 b * entry c d 2 e * entry c d 3 g
    else 0

private lemma sum_emb45 (c d : ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, entry c d j (f j)) = ∑ a : Fin 5, sumSlice c d a := by
  have h1 : (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, entry c d j (f j)) =
      ∑ p ∈ Finset.univ.filter distinct4,
        entry c d 0 p.1 * entry c d 1 p.2.1 * entry c d 2 p.2.2.1 * entry c d 3 p.2.2.2 := by
    refine Finset.sum_nbij (fun f => (f 0, f 1, f 2, f 3)) ?_ ?_ ?_ ?_
    · intro f _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, distinct4]
      exact ⟨f.injective.ne (by decide), f.injective.ne (by decide), f.injective.ne (by decide),
             f.injective.ne (by decide), f.injective.ne (by decide), f.injective.ne (by decide)⟩
    · intro f₁ _ f₂ _ heq
      apply DFunLike.ext
      intro i
      simp only [Prod.mk.injEq] at heq
      fin_cases i
      · exact heq.1
      · exact heq.2.1
      · exact heq.2.2.1
      · exact heq.2.2.2
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine ⟨⟨mkFun p, mkFun_injective hp⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      rfl
    · intro f _
      simp only [Fin.prod_univ_four]
  rw [h1, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, sumSlice]

private lemma i_pows :
    Complex.I ^ 2 = -1 ∧ Complex.I ^ 3 = -Complex.I ∧ Complex.I ^ 4 = 1 := by
  refine ⟨Complex.I_sq, ?_, ?_⟩
  · rw [pow_succ, Complex.I_sq]; ring
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; ring

private lemma slice0 (c d : ℂ) :
    sumSlice c d 0 =
      24 + 30 * c + 10 * c ^ 2 + (4 - 2 * Complex.I) * c ^ 3 - 2 * Complex.I * c ^ 4 -
      6 * d - (8 + 2 * Complex.I) * c * d - (2 + 2 * Complex.I) * c ^ 2 * d := by
  have ⟨h2, h3, _⟩ := i_pows
  simp only [sumSlice, distinct4, entry, Fin.sum_univ_five]
  norm_num
  ring_nf
  simp only [h2, h3]
  ring

private lemma slice1 (c d : ℂ) :
    sumSlice c d 1 =
      24 - 30 * c + 10 * c ^ 2 + (-4 + 2 * Complex.I) * c ^ 3 - 2 * Complex.I * c ^ 4 -
      6 * d + 6 * c * d + (-2 + 2 * Complex.I) * c ^ 2 * d + (2 - 2 * Complex.I) * c ^ 3 * d := by
  have ⟨h2, h3, _⟩ := i_pows
  simp only [sumSlice, distinct4, entry, Fin.sum_univ_five]
  norm_num
  ring_nf
  simp only [h2, h3]
  ring

private lemma slice2 (c d : ℂ) :
    sumSlice c d 2 =
      24 - 30 * Complex.I * c - 10 * c ^ 2 + (-2 + 4 * Complex.I) * c ^ 3 + 2 * Complex.I * c ^ 4 -
      6 * d + (2 + 8 * Complex.I) * c * d + (2 - 2 * Complex.I) * c ^ 2 * d := by
  have ⟨h2, h3, h4⟩ := i_pows
  simp only [sumSlice, distinct4, entry, Fin.sum_univ_five]
  norm_num
  ring_nf
  simp only [h2, h3, h4]
  ring

private lemma slice3 (c d : ℂ) :
    sumSlice c d 3 =
      24 + 30 * Complex.I * c - 10 * c ^ 2 + (2 - 4 * Complex.I) * c ^ 3 + 2 * Complex.I * c ^ 4 -
      6 * d - 6 * Complex.I * c * d + (2 + 2 * Complex.I) * c ^ 2 * d + (-2 + 2 * Complex.I) * c ^ 3 * d := by
  have ⟨h2, h3, h4⟩ := i_pows
  simp only [sumSlice, distinct4, entry, Fin.sum_univ_five]
  norm_num
  ring_nf
  simp only [h2, h3, h4]
  ring

private lemma slice4 (c d : ℂ) :
    sumSlice c d 4 = 24 + 24 * d := by
  have ⟨h2, _, _⟩ := i_pows
  simp only [sumSlice, distinct4, entry, Fin.sum_univ_five]
  norm_num
  ring_nf
  simp only [h2]
  ring

theorem main (c d : ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, entry c d j (f j)) = 120 := by
  rw [sum_emb45, Fin.sum_univ_five, slice0, slice1, slice2, slice3, slice4]
  ring

end PEqualNP.Outside.Gct194

theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 :=
  PEqualNP.Outside.Gct194.main
