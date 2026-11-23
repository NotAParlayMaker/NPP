import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_107 :
    ∀ (p q : ℕ) (u u' : Fin p → ℂ) (w w' : Fin q → ℂ),
      (∑ i, ∑ k, ∑ j, ∑ l, if i = k ∨ j = l then 0 else (u i * w j) * (u' k * w' l))
        = ((∑ i, u i) * (∑ i, u' i) - ∑ i, u i * u' i)
          * ((∑ j, w j) * (∑ j, w' j) - ∑ j, w j * w' j) := by
  intro p q u u' w w'
  have hpoint : ∀ (i k : Fin p) (j l : Fin q),
      (if i = k ∨ j = l then 0 else (u i * w j) * (u' k * w' l))
        = (if i = k then 0 else u i * u' k) * (if j = l then 0 else w j * w' l) := by
    intro i k j l
    by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl] <;> ring
  have hfactor : (∑ i : Fin p, ∑ k : Fin p, ∑ j : Fin q, ∑ l : Fin q,
      if i = k ∨ j = l then 0 else (u i * w j) * (u' k * w' l))
      = (∑ i : Fin p, ∑ k : Fin p, if i = k then 0 else u i * u' k)
        * (∑ j : Fin q, ∑ l : Fin q, if j = l then 0 else w j * w' l) := by
    simp only [hpoint]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have hu : (∑ i : Fin p, ∑ k : Fin p, if i = k then 0 else u i * u' k)
      = (∑ i, u i) * (∑ i, u' i) - ∑ i, u i * u' i := by
    have hpoint' : ∀ i k : Fin p, (if i = k then 0 else u i * u' k)
        = u i * u' k - if i = k then u i * u' k else 0 := by
      intro i k
      by_cases h : i = k <;> simp [h]
    simp only [hpoint', Finset.sum_sub_distrib]
    have hprod : (∑ i : Fin p, ∑ k : Fin p, u i * u' k) = (∑ i, u i) * (∑ i, u' i) := by
      rw [← Fintype.sum_mul_sum]
    have hdiag : (∑ i : Fin p, ∑ k : Fin p, if i = k then u i * u' k else 0)
        = ∑ i : Fin p, u i * u' i := by
      simp
    rw [hprod, hdiag]
  have hw : (∑ j : Fin q, ∑ l : Fin q, if j = l then 0 else w j * w' l)
      = (∑ j, w j) * (∑ j, w' j) - ∑ j, w j * w' j := by
    have hpoint' : ∀ j l : Fin q, (if j = l then 0 else w j * w' l)
        = w j * w' l - if j = l then w j * w' l else 0 := by
      intro j l
      by_cases h : j = l <;> simp [h]
    simp only [hpoint', Finset.sum_sub_distrib]
    have hprod : (∑ j : Fin q, ∑ l : Fin q, w j * w' l) = (∑ j, w j) * (∑ j, w' j) := by
      rw [← Fintype.sum_mul_sum]
    have hdiag : (∑ j : Fin q, ∑ l : Fin q, if j = l then w j * w' l else 0)
        = ∑ j : Fin q, w j * w' j := by
      simp
    rw [hprod, hdiag]
  rw [hfactor, hu, hw]
