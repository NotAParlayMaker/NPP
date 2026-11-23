import Mathlib
import PEqualNP.Defs

lemma term_split {p q : ℕ} (i k : Fin p) (j l : Fin q) (u u' : Fin p → ℂ) (w w' : Fin q → ℂ) :
    (if i = k ∨ j = l then (0 : ℂ) else (u i * w j) * (u' k * w' l)) =
      (if i = k then 0 else u i * u' k) * (if j = l then 0 else w j * w' l) := by
  by_cases hik : i = k
  · simp [hik]
  · by_cases hjl : j = l
    · simp [hjl]
    · simp [hik, hjl]
      ring

lemma sum_mul_sum_4 {α β : Type*} [Fintype α] [Fintype β] (A : α → α → ℂ) (B : β → β → ℂ) :
    (∑ i, ∑ k, ∑ j, ∑ l, A i k * B j l) = (∑ i, ∑ k, A i k) * (∑ j, ∑ l, B j l) := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

lemma sum_distinct {n : ℕ} (u u' : Fin n → ℂ) :
    (∑ i, ∑ k, if i = k then (0 : ℂ) else u i * u' k) =
      ((∑ i, u i) * (∑ i, u' i) - ∑ i, u i * u' i) := by
  have h1 : ∀ i k, (if i = k then (0 : ℂ) else u i * u' k) = u i * u' k - (if i = k then u i * u' k else 0) := by
    intro i k
    by_cases h : i = k <;> simp [h]
  simp_rw [h1]
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [Finset.sum_ite_eq]
  simp

theorem PEqualNP.Outside.L_gct_107 : ∀ (p q : ℕ) (u u' : Fin p → ℂ) (w w' : Fin q → ℂ),
    (∑ i, ∑ k, ∑ j, ∑ l, if i = k ∨ j = l then 0 else (u i * w j) * (u' k * w' l)) =
      ((∑ i, u i) * (∑ i, u' i) - ∑ i, u i * u' i) * ((∑ j, w j) * (∑ j, w' j) - ∑ j, w j * w' j) := by
  intro p q u u' w w'
  simp_rw [term_split]
  rw [sum_mul_sum_4]
  rw [sum_distinct, sum_distinct]
