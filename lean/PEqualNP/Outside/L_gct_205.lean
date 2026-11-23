import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.SplitIfs

-- Mythos 6 et Codex Betelgeuse

open scoped BigOperators

namespace PEqualNP.Outside.L_gct_205_aux

noncomputable def levelSum (n k : ℕ) (t : Fin n × Fin n → ℂ) : ℂ :=
  ∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
    if h : R.card = k ∧ C.card = k then
      Matrix.permanent (Matrix.of fun a b =>
        t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0

lemma levelSum_zero (n : ℕ) (t : Fin n × Fin n → ℂ) : levelSum n 0 t = 1 := by
  classical
  unfold levelSum
  rw [Finset.sum_eq_single ∅]
  · simp [Finset.card_eq_zero, Matrix.permanent_isEmpty]
  · intro R _ hR
    apply Finset.sum_eq_zero
    intro C _
    simp [show R.card ≠ 0 by simpa using hR]
  · simp

lemma permanent_expand (n : ℕ) (t : Fin n × Fin n → ℂ) :
    Matrix.permanent (Matrix.of fun a b => (1 : ℂ) + t (a,b)) =
      ∑ σ : Equiv.Perm (Fin n), ∑ C : Finset (Fin n), ∏ j ∈ C, t (σ j,j) := by
  classical
  simp only [Matrix.permanent, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro σ _
  simpa using (Finset.prod_one_add (f := fun j => t (σ j,j)) Finset.univ)

lemma conclusion_of_expansion
    (expansion : ∀ (n : ℕ) (t : Fin n × Fin n → ℂ),
      Matrix.permanent (Matrix.of fun a b => (1 : ℂ) + t (a,b)) =
        ∑ k ∈ Finset.range (n + 1), (Nat.factorial (n-k) : ℂ) * levelSum n k t) :
    ∀ n : ℕ, ∀ L Z : Submodule ℂ (Fin n × Fin n → ℂ),
      (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n →
        (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
          if h : R.card = k ∧ C.card = k then
            Matrix.permanent (Matrix.of fun a b =>
              t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) →
      (∀ z ∈ Z, Matrix.permanent (Matrix.of fun a b => z (a,b)) = 0) →
      (fun _ => (1 : ℂ)) ∉ L ⊔ Z := by
  classical
  intro n L Z hL hZ hJ
  obtain ⟨t, ht, z, hz, htz⟩ := Submodule.mem_sup.mp hJ
  have hneg : -t ∈ L := L.neg_mem ht
  have hzero (k : ℕ) (hk : k ∈ Finset.range (n+1)) (hk0 : k ≠ 0) :
      (Nat.factorial (n-k) : ℂ) * levelSum n k (-t) = 0 := by
    rw [show levelSum n k (-t) = 0 from hL (-t) hneg k (by omega) (by
      simpa only [Finset.mem_range] using Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    simp
  have heq : Matrix.permanent (Matrix.of fun a b => (1 : ℂ) + (-t) (a,b)) =
      (Nat.factorial n : ℂ) := by
    rw [expansion, Finset.sum_eq_single 0]
    · simp [levelSum_zero]
    · exact hzero
    · simp
  have hzfun : (fun a b => z (a,b)) = (fun a b => (1 : ℂ) + (-t) (a,b)) := by
    funext a b
    have h := congrFun htz (a,b)
    change t (a,b) + z (a,b) = 1 at h
    change z (a,b) = 1 + -t (a,b)
    linear_combination h
  have hperm := hZ z hz
  rw [hzfun, heq] at hperm
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) hperm

lemma join_apply_pos {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : Subtype p ≃ Subtype q) (f : {x // ¬p x} ≃ {x // ¬q x})
    (x : α) (hx : p x) : Equiv.subtypeCongr e f x = e ⟨x,hx⟩ := by
  simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]

lemma join_apply_neg {α : Type*} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : Subtype p ≃ Subtype q) (f : {x // ¬p x} ≃ {x // ¬q x})
    (x : α) (hx : ¬p x) : Equiv.subtypeCongr e f x = f ⟨x,hx⟩ := by
  simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_neg hx]

noncomputable def splitPerm {α : Type*} (p q : α → Prop) :
    (Subtype p ≃ Subtype q) × ({x // ¬p x} ≃ {x // ¬q x}) ≃
      {σ : Equiv.Perm α // ∀ x, p x ↔ q (σ x)} := by
  classical
  refine {
    toFun := fun ef => ⟨Equiv.subtypeCongr ef.1 ef.2, ?_⟩
    invFun := fun σ => (σ.1.subtypeEquiv σ.2,
      σ.1.subtypeEquiv (fun x => not_congr (σ.2 x)))
    left_inv := ?_
    right_inv := ?_
  }
  · intro x
    by_cases hx : p x
    · rw [join_apply_pos _ _ _ hx]
      exact iff_of_true hx (ef.1 ⟨x,hx⟩).2
    · rw [join_apply_neg _ _ _ hx]
      exact iff_of_false hx (ef.2 ⟨x,hx⟩).2
  · intro ef
    apply Prod.ext <;> ext x
    · exact join_apply_pos _ _ _ x.2
    · exact join_apply_neg _ _ _ x.2
  · intro σ
    apply Subtype.ext
    ext x
    by_cases hx : p x
    · exact join_apply_pos _ _ _ hx
    · exact join_apply_neg _ _ _ hx

lemma image_eq_iff {α : Type*} [DecidableEq α]
    (C R : Finset α) (σ : Equiv.Perm α) :
    C.image σ = R ↔ ∀ x, x ∈ C ↔ σ x ∈ R := by
  constructor
  · intro h x
    rw [← h]
    simp
  · intro h
    ext x
    constructor
    · rintro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (h y).mp hy
    · intro hx
      exact Finset.mem_image.mpr ⟨σ.symm x, (h _).mpr (by simpa using hx), by simp⟩

lemma sum_compatible (n : ℕ) (C R : Finset (Fin n)) (t : Fin n × Fin n → ℂ) :
    (∑ σ : {σ : Equiv.Perm (Fin n) // ∀ x, x ∈ C ↔ σ x ∈ R},
      ∏ j : C, t (σ.1 j, j)) =
    (Nat.factorial (n-C.card) : ℂ) * ∑ e : C ≃ R, ∏ j : C, t (e j,j) := by
  classical
  rw [← (splitPerm (· ∈ C) (· ∈ R)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [splitPerm, Equiv.coe_fn_mk, join_apply_pos _ _ _ (Subtype.property _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  have he : {x : Fin n // x ∉ C} ≃ {x : Fin n // x ∉ R} :=
    Equiv.toCompl (p := (· ∈ C)) (q := (· ∈ R)) e
  have hcard := Fintype.card_equiv he
  simpa only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] using hcard

lemma bijection_sum (n k : ℕ) (C R : Finset (Fin n)) (hc : C.card = k) (hr : R.card = k)
    (t : Fin n × Fin n → ℂ) :
    (∑ e : C ≃ R, ∏ j : C, t (e j,j)) =
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin hr a, C.orderEmbOfFin hc b)) := by
  classical
  let ec := (C.orderIsoOfFin hc).toEquiv
  let er := (R.orderIsoOfFin hr).toEquiv
  rw [← (Equiv.equivCongr ec er).sum_comp]
  unfold Matrix.permanent
  apply Finset.sum_congr rfl
  intro σ _
  rw [← ec.prod_comp]
  apply Finset.prod_congr rfl
  intro j _
  simp [Equiv.equivCongr, ec, er]

lemma sum_by_image (n : ℕ) (C : Finset (Fin n)) (t : Fin n × Fin n → ℂ) :
    (∑ σ : Equiv.Perm (Fin n), ∏ j : C, t (σ j,j)) =
    ∑ R : Finset (Fin n),
      ∑ σ : {σ : Equiv.Perm (Fin n) // ∀ x, x ∈ C ↔ σ x ∈ R},
        ∏ j : C, t (σ.1 j,j) := by
  classical
  symm
  calc
    _ = ∑ R : Finset (Fin n), ∑ σ : Equiv.Perm (Fin n),
        if C.image σ = R then ∏ j : C, t (σ j,j) else 0 := by
      apply Finset.sum_congr rfl
      intro R _
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype
        (p := fun σ : Equiv.Perm (Fin n) => ∀ x, x ∈ C ↔ σ x ∈ R)
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => C.image σ = R))
        (by intro σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, image_eq_iff])
        (fun σ => ∏ j : C, t (σ j,j))).symm
    _ = _ := by rw [Finset.sum_comm]; simp

lemma fixed_columns (n : ℕ) (C : Finset (Fin n)) (t : Fin n × Fin n → ℂ) :
    (∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j,j)) =
    (Nat.factorial (n-C.card) : ℂ) *
      ∑ R : Finset (Fin n),
        if h : R.card = C.card then Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin h a, C.orderEmbOfFin rfl b)) else 0 := by
  classical
  have hp (σ : Equiv.Perm (Fin n)) :
      (∏ j ∈ C, t (σ j,j)) = ∏ j : C, t (σ j,j) :=
    (Finset.prod_coe_sort C (fun j => t (σ j,j))).symm
  simp_rw [hp]
  rw [sum_by_image]
  simp_rw [sum_compatible]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  congr 1
  split_ifs with h
  · exact bijection_sum n C.card C R rfl h t
  · apply Finset.sum_eq_zero
    intro e _
    exact (h (Finset.card_eq_of_equiv e).symm).elim

lemma insert_card_sum (n : ℕ) (C : Finset (Fin n)) (t : Fin n × Fin n → ℂ) :
    (Nat.factorial (n-C.card) : ℂ) *
      (∑ R : Finset (Fin n),
        if h : R.card = C.card then Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin h a, C.orderEmbOfFin rfl b)) else 0) =
    ∑ k ∈ Finset.range (n+1), (Nat.factorial (n-k) : ℂ) *
      ∑ R : Finset (Fin n),
        if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0 := by
  classical
  symm
  rw [Finset.sum_eq_single C.card]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    have hc : C.card ≤ n := by simpa using Finset.card_le_univ C
    exact (h (Finset.mem_range.mpr (by omega))).elim

lemma expansion (n : ℕ) (t : Fin n × Fin n → ℂ) :
    Matrix.permanent (Matrix.of fun a b => (1 : ℂ) + t (a,b)) =
      ∑ k ∈ Finset.range (n+1), (Nat.factorial (n-k) : ℂ) * levelSum n k t := by
  classical
  rw [permanent_expand, Finset.sum_comm]
  simp_rw [fixed_columns, insert_card_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

end PEqualNP.Outside.L_gct_205_aux

theorem PEqualNP.Outside.L_gct_205 :
∀ n : ℕ, ∀ L Z : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n → (∑ R : Finset (Fin n), ∑ C : Finset (Fin n), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) → (∀ z ∈ Z, Matrix.permanent (Matrix.of fun a b => z (a, b)) = 0) → (fun _ => (1 : ℂ)) ∉ L ⊔ Z :=
  PEqualNP.Outside.L_gct_205_aux.conclusion_of_expansion
    PEqualNP.Outside.L_gct_205_aux.expansion
