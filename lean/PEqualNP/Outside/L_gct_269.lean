import Mathlib

namespace PEqualNP.Outside.L_gct_269

open Polynomial

noncomputable def f : Polynomial ℝ :=
  C (-3 / 1000000) * X ^ 10 + C 300 * X ^ 8 + C (-80000) * X ^ 6 + C (1 / 2) * X ^ 2

noncomputable def g : Polynomial ℝ :=
  C (1 / 500) * X ^ 10 + C (-40) * X ^ 8 + C 20000 * X ^ 4 + C (-20000)

lemma f_card : f.support.card ≤ 4 := by
  have h : f.support ⊆ {10, 8, 6, 2} := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra h
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [f, coeff_X_pow, h1, h2, h3, h4]
  exact (Finset.card_le_card h).trans (by decide)

lemma g_card : g.support.card ≤ 4 := by
  have h : g.support ⊆ {10, 8, 4, 0} := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra h
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp [g, coeff_X_pow, coeff_C, h1, h2, h3, h4]
  exact (Finset.card_le_card h).trans (by decide)

lemma eval_p (x : ℝ) : eval x (f * g + 1) =
    (-3 / 1000000 * x ^ 10 + 300 * x ^ 8 + -80000 * x ^ 6 + 1 / 2 * x ^ 2) *
      (1 / 500 * x ^ 10 + -40 * x ^ 8 + 20000 * x ^ 4 + -20000) + 1 := by
  simp [f, g]

lemma p_ne : f * g + 1 ≠ 0 := by
  intro h
  have h0 := congrArg (eval 0) h
  rw [eval_p] at h0
  norm_num at h0

noncomputable def t : Fin 14 → ℝ :=
  ![-20000, -1000, -100, -10, -2, -1 / 10, -1 / 50, 0, 1 / 50, 1 / 10, 2, 10, 100, 1000]

lemma t_strictMono : StrictMono t := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> norm_num [t]

lemma sign_change (i : Fin 13) :
    eval (t i.castSucc) (f * g + 1) * eval (t i.succ) (f * g + 1) < 0 := by
  rw [eval_p, eval_p]
  fin_cases i <;> norm_num [t]

lemma root_between (a b : ℝ) (hab : a < b)
    (h : eval a (f * g + 1) * eval b (f * g + 1) < 0) :
    ∃ r ∈ Set.Ioo a b, IsRoot (f * g + 1) r := by
  have hc : ContinuousOn (fun x => eval x (f * g + 1)) (Set.Icc a b) :=
    (Polynomial.continuous _).continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨r, hr, hr0⟩
  · obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨r, hr, hr0⟩

lemma main : 13 ≤ ((f * g + 1).roots.toFinset).card := by
  have hroot : ∀ i : Fin 13, ∃ r ∈ Set.Ioo (t i.castSucc) (t i.succ), IsRoot (f * g + 1) r :=
    fun i => root_between _ _ (t_strictMono Fin.castSucc_lt_succ) (sign_change i)
  choose r hr hr0 using hroot
  have hmono : StrictMono r := by
    intro i j hij
    have h1 := (hr i).2
    have h2 := (hr j).1
    have h3 : t i.succ ≤ t j.castSucc := by
      apply t_strictMono.monotone
      rw [Fin.le_iff_val_le_val]
      simp only [Fin.val_succ, Fin.val_castSucc]
      rw [Fin.lt_def] at hij
      omega
    linarith
  have hsub : Finset.univ.image r ⊆ (f * g + 1).roots.toFinset := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots p_ne]
    exact hr0 i
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin] at hc
  exact hc

end PEqualNP.Outside.L_gct_269

theorem PEqualNP.Outside.L_gct_269 : ¬ (∀ f g : Polynomial ℝ, (f.support.card ≤ 4 ∧ g.support.card ≤ 4) → ((f * g + 1).roots.toFinset).card ≤ 12) := by
  intro H
  have h12 := H PEqualNP.Outside.L_gct_269.f PEqualNP.Outside.L_gct_269.g
    ⟨PEqualNP.Outside.L_gct_269.f_card, PEqualNP.Outside.L_gct_269.g_card⟩
  have h13 := PEqualNP.Outside.L_gct_269.main
  omega
