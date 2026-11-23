import Mathlib
import PEqualNP.Defs

open Finset

theorem PEqualNP.Outside.L_gct_121 :
    ∀ (n : ℕ) (u v : Fin n → ℂ), u ≠ 0 → v ≠ 0 → (∀ μ : ℂ, MvPolynomial.eval (fun p : Fin n × Fin n => 1 + μ * u p.1 * v p.2) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → (Finset.univ.filter (fun i => u i ≠ 0)).card ≠ (Finset.univ.filter (fun j => v j ≠ 0)).card := by
  intro n u v hu _ hlevel hcard
  classical
  let U := univ.filter (fun i => u i ≠ 0)
  let V := univ.filter (fun j => v j ≠ 0)
  have hU (i : Fin n) : i ∈ U ↔ u i ≠ 0 := by simp [U]
  have hV (j : Fin n) : j ∈ V ↔ v j ≠ 0 := by simp [V]
  have hUV : U.card = V.card := hcard
  have hm : V.card ≠ 0 := by
    intro hzero
    apply hu
    funext i
    change u i = 0
    by_contra hi
    have hpos := Finset.card_pos.mpr ⟨i, (hU i).mpr hi⟩
    omega
  let P : Polynomial ℂ :=
    ∑ σ : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
      Polynomial.monomial S.card (∏ j ∈ S, u (σ j) * v j)
  have heval (μ : ℂ) : P.eval μ =
      MvPolynomial.eval (fun p : Fin n × Fin n => 1 + μ * u p.1 * v p.2)
        (PEqualNP.Gct.permPoly ℂ n) := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      PEqualNP.Gct.permPoly, Matrix.permanent, map_sum, map_prod,
      Matrix.mvPolynomialX_apply, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [mul_assoc μ]
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [Finset.prod_mul_distrib, Finset.prod_const]
    exact mul_comm _ _
  have hP : P = Polynomial.C (Nat.factorial n : ℂ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hset : {μ : ℂ | P.eval μ = (Polynomial.C (Nat.factorial n : ℂ)).eval μ} =
        Set.univ := by
      ext μ
      simp [heval, hlevel]
    rw [hset]
    exact Set.infinite_univ
  let w := (∏ i ∈ U, u i) * (∏ j ∈ V, v j)
  have hw : w ≠ 0 :=
    mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i hi => (hU i).mp hi)
      (Finset.prod_ne_zero_iff.mpr fun j hj => (hV j).mp hj)
  have hterm (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
      (if S.card = V.card then ∏ j ∈ S, u (σ j) * v j else 0) =
        if S = V ∧ V.map σ.toEmbedding = U then w else 0 := by
    by_cases h : S = V ∧ V.map σ.toEmbedding = U
    · rcases h with ⟨rfl, hmap⟩
      simp only [hmap, and_self, ite_true, Finset.prod_mul_distrib, w]
      rw [← hmap, Finset.prod_map]
      rfl
    · rw [ite_eq_right h]
      split_ifs with hc <;> try rfl
      by_contra hn
      have hprod := Finset.prod_ne_zero_iff.mp hn
      have hSV : S ⊆ V := fun j hj =>
        (hV j).mpr (right_ne_zero_of_mul (hprod j hj))
      have hSU : S.map σ.toEmbedding ⊆ U := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact (hU (σ j)).mpr (left_ne_zero_of_mul (hprod j hj))
      have hS : S = V := Finset.eq_of_subset_of_card_le hSV hc.ge
      have hmap : S.map σ.toEmbedding = U :=
        Finset.eq_of_subset_of_card_le hSU (by rw [Finset.card_map, hc, hUV])
      exact h ⟨hS, hS ▸ hmap⟩
  let A := univ.filter (fun σ : Equiv.Perm (Fin n) => V.map σ.toEmbedding = U)
  have hA : A.card ≠ 0 := by
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq V U hUV.symm
    exact (Finset.card_pos.mpr ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hσ⟩⟩).ne'
  have hcoeff : P.coeff V.card = (A.card : ℂ) * w := by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, hterm]
    calc
      _ = ∑ σ : Equiv.Perm (Fin n), if V.map σ.toEmbedding = U then w else 0 := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        by_cases hmap : V.map σ.toEmbedding = U <;> simp [hmap]
      _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hne : P.coeff V.card ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hA) hw
  apply hne
  rw [hP]
  simp [hm]
