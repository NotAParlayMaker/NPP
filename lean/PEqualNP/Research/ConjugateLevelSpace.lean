import Mathlib
import PEqualNP.Gct.Helpers.OrderConditions
import PEqualNP.Gct.Helpers.PermHessian
import PEqualNP.Outside.L_gct_105

namespace PEqualNP.ConjugateLevelSpace

open Finset MvPolynomial PEqualNP.Gct PEqualNP.Gct.Helpers
open scoped BigOperators ComplexOrder

private lemma hessian_ones (k : ℕ) (a b : Fin (k + 2) × Fin (k + 2)) :
    eval (fun _ => (1 : ℂ)) (pderiv a (pderiv b (permPoly ℂ (k + 2)))) =
      if a.1 = b.1 ∨ a.2 = b.2 then 0 else (k.factorial : ℂ) := by
  classical
  have expansion : eval (fun _ => (1 : ℂ)) (pderiv a (pderiv b (permPoly ℂ (k + 2)))) =
      ∑ σ : Equiv.Perm (Fin (k + 2)),
        if σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 then (1 : ℂ) else 0 := by
    simp only [permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum]
    refine sum_congr rfl fun σ _ => ?_
    rw [pderiv_perm_mon]
    by_cases hb : σ b.2 = b.1
    · rw [ite_eq_left ⟨mem_univ _, hb⟩, pderiv_perm_mon]
      by_cases ha : a.2 ≠ b.2 ∧ σ a.2 = a.1
      · simp [ha.1, ha.2, hb]
      · simp [ha, hb]
    · simp [hb]
  rw [expansion, sum_boole]
  by_cases h : a.1 = b.1 ∨ a.2 = b.2
  · rw [ite_eq_left h]
    have e : univ.filter (fun σ : Equiv.Perm (Fin (k + 2)) =>
        σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1) = ∅ := by
      apply filter_eq_empty_iff.mpr
      rintro σ _ ⟨hb, hcol, ha⟩
      rcases h with hrow | hcol'
      · exact hcol (σ.injective (ha.trans (hrow.trans hb.symm)))
      · exact hcol hcol'
    simp [e]
  · have hr : a.1 ≠ b.1 := fun e => h (Or.inl e)
    have hc : a.2 ≠ b.2 := fun e => h (Or.inr e)
    rw [ite_eq_right h, card_two a b hc hr]

private lemma square_sum_zero (k : ℕ)
    (L : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ))
    (level : ∀ t ∈ L, eval (fun p => 1 + t p) (permPoly ℂ (k + 2)) =
      ((k + 2).factorial : ℂ))
    (t : Fin (k + 2) × Fin (k + 2) → ℂ) (ht : t ∈ L)
    (rows : ∀ i, ∑ j, t (i, j) = 0) (cols : ∀ j, ∑ i, t (i, j) = 0) :
    ∑ a, t a ^ 2 = 0 := by
  classical
  have vanish := (OrderCond.order_conditions_of_vanish_on_line
    (permPoly ℂ (k + 2) - C ((k + 2).factorial : ℂ)) (fun _ => 1) t (by
      intro s
      rw [map_sub, eval_C, sub_eq_zero]
      exact level _ (L.smul_mem s ht))).2
  simp only [map_sub, pderiv_C, sub_zero, hessian_ones] at vanish
  have cross : (∑ a, ∑ b, if a.1 = b.1 ∨ a.2 = b.2 then (0 : ℂ) else t a * t b) =
      ∑ a, t a ^ 2 := by
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ i, ∑ r, ∑ j, ∑ c, if i = r ∨ j = c then 0 else t (i, j) * t (r, c) := by
        exact sum_congr rfl fun i _ => sum_comm
      _ = _ := PEqualNP.Outside.L_gct_105 _ _ (fun i j => t (i, j)) rows cols
  have weighted : (k.factorial : ℂ) * (∑ a, t a ^ 2) = 0 := by
    rw [← cross]
    calc
      _ = ∑ a, ∑ b, (if a.1 = b.1 ∨ a.2 = b.2 then 0 else (k.factorial : ℂ))
          * t a * t b := by
        simp only [mul_sum]
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        split_ifs <;> ring
      _ = 0 := vanish
  exact (mul_eq_zero.mp weighted).resolve_left (by exact_mod_cast (Nat.factorial_ne_zero k))

/-- A complex permanent level space stable under entrywise conjugation has dimension
    at most twice its matrix size. -/
theorem finrank_le_two_mul (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (level : ∀ t ∈ L, eval (fun p => 1 + t p) (permPoly ℂ n) = (n.factorial : ℂ))
    (closed : ∀ t ∈ L, star t ∈ L) : Module.finrank ℂ L ≤ 2 * n := by
  classical
  by_cases hn : n < 2
  · have h := Submodule.finrank_le L
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h
    interval_cases n <;> omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  let sums : (Fin (k + 2) × Fin (k + 2) → ℂ) →ₗ[ℂ]
      (Fin (k + 2) → ℂ) × (Fin (k + 2) → ℂ) :=
    LinearMap.prod (LinearMap.pi fun i => ∑ j, LinearMap.proj (i, j))
      (LinearMap.pi fun j => ∑ i, LinearMap.proj (i, j))
  have inj : Function.Injective (sums.domRestrict L) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨t, ht⟩ (hzero : sums t = 0)
    have rows : ∀ i, ∑ j, t (i, j) = 0 := fun i => by
      simpa [sums, LinearMap.sum_apply] using congrFun (congrArg Prod.fst hzero) i
    have cols : ∀ j, ∑ i, t (i, j) = 0 := fun j => by
      simpa [sums, LinearMap.sum_apply] using congrFun (congrArg Prod.snd hzero) j
    have sr : ∀ i, ∑ j, (star t) (i, j) = 0 := fun i => by
      simpa only [Pi.star_apply, ← star_sum, star_zero] using congrArg star (rows i)
    have sc : ∀ j, ∑ i, (star t) (i, j) = 0 := fun j => by
      simpa only [Pi.star_apply, ← star_sum, star_zero] using congrArg star (cols j)
    have hs := closed t ht
    have qt := square_sum_zero k L level t ht rows cols
    have qs := square_sum_zero k L level (star t) hs sr sc
    have qp := square_sum_zero k L level (t + star t) (L.add_mem ht hs)
      (fun i => by simp only [Pi.add_apply, sum_add_distrib, rows, sr, zero_add])
      (fun j => by simp only [Pi.add_apply, sum_add_distrib, cols, sc, zero_add])
    have qprod : ∑ p, t p * star (t p) = 0 := by
      simp only [Pi.star_apply] at qs
      simp only [Pi.add_apply, add_sq, mul_assoc, sum_add_distrib, ← mul_sum,
        qt, qs, Pi.star_apply] at qp
      linear_combination qp / 2
    apply Subtype.ext
    exact dotProduct_self_star_eq_zero.mp qprod
  have h := LinearMap.finrank_le_finrank_of_injective inj
  simpa [Module.finrank_prod, Module.finrank_fin_fun, two_mul] using h

end PEqualNP.ConjugateLevelSpace
