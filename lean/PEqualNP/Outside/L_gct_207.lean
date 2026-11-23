import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_207_aux

open Finset

private def rowPart (x : Fin 5 → ℂ) : Fin 6 → ℂ :=
  Fin.lastCases (-∑ j : Fin 5, x j) x

private lemma rowPart_last (x : Fin 5 → ℂ) : rowPart x (Fin.last 5) = -∑ j : Fin 5, x j :=
  Fin.lastCases_last

private lemma rowPart_castSucc (x : Fin 5 → ℂ) (j : Fin 5) : rowPart x j.castSucc = x j := by
  simp [rowPart]

private lemma sum_rowPart (x : Fin 5 → ℂ) : ∑ j : Fin 6, rowPart x j = 0 := by
  rw [Fin.sum_univ_castSucc, rowPart_last]
  simp only [rowPart_castSucc, add_neg_cancel]

private def pt (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) : Fin 5 × Fin 7 → ℂ :=
  fun p => Fin.cases (Fin.cases (-∑ i : Fin 4, y i) (rowPart x) p.2)
    (fun i => Fin.cases (y i) (fun _ => 0) p.2) p.1

private lemma pt_zero_zero (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) :
    pt x y (0, 0) = -∑ i : Fin 4, y i := rfl

private lemma pt_zero_succ (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) (j : Fin 6) :
    pt x y (0, j.succ) = rowPart x j := rfl

private lemma pt_succ_zero (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) (i : Fin 4) :
    pt x y (i.succ, 0) = y i := rfl

private lemma pt_succ_succ (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) (i : Fin 4) (j : Fin 6) :
    pt x y (i.succ, j.succ) = 0 := rfl

private lemma pt_ne_zero_ne_zero (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) {r : Fin 5} {c : Fin 7}
    (hr : r ≠ 0) (hc : c ≠ 0) : pt x y (r, c) = 0 := by
  refine Fin.cases (fun h => absurd rfl h) (fun i _ => ?_) r hr
  refine Fin.cases (fun h => absurd rfl h) (fun j _ => pt_succ_succ x y i j) c hc

private def ptLin : ((Fin 5 → ℂ) × (Fin 4 → ℂ)) →ₗ[ℂ] (Fin 5 × Fin 7 → ℂ) where
  toFun v := pt v.1 v.2
  map_add' v w := by
    funext ⟨i, j⟩
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simp [pt_zero_zero, sum_add_distrib]; ring
      · intro j
        simp only [Pi.add_apply, Prod.fst_add, pt_zero_succ]
        refine Fin.lastCases ?_ ?_ j
        · simp only [rowPart_last, Pi.add_apply, sum_add_distrib]; ring
        · intro j; simp only [rowPart_castSucc, Pi.add_apply]
    · intro i
      refine Fin.cases ?_ ?_ j
      · simp [pt_succ_zero]
      · intro j; simp [pt_succ_succ]
  map_smul' c v := by
    funext ⟨i, j⟩
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simp [pt_zero_zero, mul_sum]
      · intro j
        simp only [Pi.smul_apply, Prod.smul_fst, smul_eq_mul, pt_zero_succ]
        refine Fin.lastCases ?_ ?_ j
        · simp only [rowPart_last, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [← mul_sum]; ring
        · intro j; simp only [rowPart_castSucc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    · intro i
      refine Fin.cases ?_ ?_ j
      · simp [pt_succ_zero]
      · intro j; simp [pt_succ_succ]

private lemma ptLin_injective : Function.Injective ptLin := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h' : pt x y = pt x' y' := h
  have hx : x = x' := by
    funext j
    have := congrFun h' (0, j.castSucc.succ)
    simpa only [pt_zero_succ, rowPart_castSucc] using this
  have hy : y = y' := by
    funext i
    have := congrFun h' (i.succ, 0)
    simpa [pt_succ_zero] using this
  rw [hx, hy]

private lemma perm_ge_three (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) (k : ℕ) (hk : 3 ≤ k)
    (R : Finset (Fin 5)) (C : Finset (Fin 7)) (hR : R.card = k) (hC : C.card = k) :
    Matrix.permanent (Matrix.of fun a b => pt x y (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b)) =
      0 := by
  rw [Matrix.permanent]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hex : ∃ a : Fin k, R.orderEmbOfFin hR (σ a) ≠ 0 ∧ C.orderEmbOfFin hC a ≠ 0 := by
    by_contra hall
    push Not at hall
    have hcard : (Finset.univ : Finset (Fin k)).card ≤
        (Finset.univ.filter (fun a : Fin k => R.orderEmbOfFin hR (σ a) = 0)).card +
        (Finset.univ.filter (fun a : Fin k => C.orderEmbOfFin hC a = 0)).card := by
      calc (Finset.univ : Finset (Fin k)).card
          ≤ (Finset.univ.filter (fun a : Fin k => R.orderEmbOfFin hR (σ a) = 0) ∪
              Finset.univ.filter (fun a : Fin k => C.orderEmbOfFin hC a = 0)).card := by
              refine Finset.card_le_card fun a _ => ?_
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              by_cases hr : R.orderEmbOfFin hR (σ a) = 0
              · exact Or.inl hr
              · exact Or.inr (hall a hr)
        _ ≤ _ := Finset.card_union_le _ _
    have h1 : (Finset.univ.filter (fun a : Fin k => R.orderEmbOfFin hR (σ a) = 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact σ.injective ((R.orderEmbOfFin hR).injective (ha.trans hb.symm))
    have h2 : (Finset.univ.filter (fun a : Fin k => C.orderEmbOfFin hC a = 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact (C.orderEmbOfFin hC).injective (ha.trans hb.symm)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  rcases hex with ⟨a, hr, hc⟩
  exact Finset.prod_eq_zero (Finset.mem_univ a) (pt_ne_zero_ne_zero x y hr hc)

private lemma sum_k1 (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) :
    (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7),
      if h : R.card = 1 ∧ C.card = 1 then
        Matrix.permanent (Matrix.of fun a b => pt x y (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0 := by
  have hR1 : ∀ (R : Finset (Fin 5)) (C : Finset (Fin 7)),
      (if h : R.card = 1 ∧ C.card = 1 then
        Matrix.permanent (Matrix.of fun a b => pt x y (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) =
      if hR : R.card = 1 then
        if hC : C.card = 1 then pt x y (R.orderEmbOfFin hR 0, C.orderEmbOfFin hC 0) else 0
      else 0 := by
    intro R C
    by_cases hR : R.card = 1 <;> by_cases hC : C.card = 1
    · simp only [hR, hC, and_self, ↓reduceDIte, Matrix.permanent, Fintype.sum_unique,
        Fin.prod_univ_one, Matrix.of_apply]
      rfl
    · simp [hR, hC]
    · simp [hR, hC]
    · simp [hR, hC]
  simp_rw [hR1]
  have hsumC : ∀ (r : Fin 5),
      (∑ C : Finset (Fin 7),
        if hC : C.card = 1 then pt x y (r, C.orderEmbOfFin hC 0) else 0) =
      ∑ c : Fin 7, pt x y (r, c) := by
    intro r
    have hfilt : (∑ C : Finset (Fin 7),
        if hC : C.card = 1 then pt x y (r, C.orderEmbOfFin hC 0) else 0) =
        ∑ C ∈ (Finset.univ : Finset (Fin 7)).powersetCard 1,
          if hC : C.card = 1 then pt x y (r, C.orderEmbOfFin hC 0) else 0 := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun C _ hC => ?_).symm
      have hne : C.card ≠ 1 := fun h => hC (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h⟩)
      simp [hne]
    rw [hfilt]
    refine Finset.sum_bij (fun C hC => C.orderEmbOfFin (Finset.mem_powersetCard.mp hC).2 0)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro C1 hC1 C2 hC2 hEq
      have e1 : C1 = {C1.orderEmbOfFin (Finset.mem_powersetCard.mp hC1).2 0} := by
        rcases Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hC1).2 with ⟨c, rfl⟩
        have hmem := Finset.orderEmbOfFin_mem ({c} : Finset (Fin 7))
          (Finset.mem_powersetCard.mp hC1).2 0
        rw [Finset.mem_singleton] at hmem
        simp [hmem]
      have e2 : C2 = {C2.orderEmbOfFin (Finset.mem_powersetCard.mp hC2).2 0} := by
        rcases Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hC2).2 with ⟨c, rfl⟩
        have hmem := Finset.orderEmbOfFin_mem ({c} : Finset (Fin 7))
          (Finset.mem_powersetCard.mp hC2).2 0
        rw [Finset.mem_singleton] at hmem
        simp [hmem]
      rw [e1, e2, hEq]
    · intro c _
      refine ⟨{c}, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_singleton c⟩, ?_⟩
      have hmem := Finset.orderEmbOfFin_mem ({c} : Finset (Fin 7)) (Finset.card_singleton c) 0
      exact Finset.mem_singleton.mp hmem
    · intro C hC
      simp [(Finset.mem_powersetCard.mp hC).2]
  have hstep : ∀ R : Finset (Fin 5),
      (∑ C : Finset (Fin 7),
        if hR : R.card = 1 then
          if hC : C.card = 1 then pt x y (R.orderEmbOfFin hR 0, C.orderEmbOfFin hC 0) else 0
        else 0) =
      if hR : R.card = 1 then ∑ c : Fin 7, pt x y (R.orderEmbOfFin hR 0, c) else 0 := by
    intro R
    by_cases hR : R.card = 1
    · simp only [hR, ↓reduceDIte]
      exact hsumC (R.orderEmbOfFin hR 0)
    · simp [hR]
  simp_rw [hstep]
  have hsumR :
      (∑ R : Finset (Fin 5),
        if hR : R.card = 1 then ∑ c : Fin 7, pt x y (R.orderEmbOfFin hR 0, c) else 0) =
      ∑ r : Fin 5, ∑ c : Fin 7, pt x y (r, c) := by
    have hfilt : (∑ R : Finset (Fin 5),
        if hR : R.card = 1 then ∑ c : Fin 7, pt x y (R.orderEmbOfFin hR 0, c) else 0) =
        ∑ R ∈ (Finset.univ : Finset (Fin 5)).powersetCard 1,
          if hR : R.card = 1 then ∑ c : Fin 7, pt x y (R.orderEmbOfFin hR 0, c) else 0 := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun R _ hR => ?_).symm
      have hne : R.card ≠ 1 := fun h => hR (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h⟩)
      simp [hne]
    rw [hfilt]
    refine Finset.sum_bij (fun R hR => R.orderEmbOfFin (Finset.mem_powersetCard.mp hR).2 0)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro R1 hR1 R2 hR2 hEq
      have e1 : R1 = {R1.orderEmbOfFin (Finset.mem_powersetCard.mp hR1).2 0} := by
        rcases Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hR1).2 with ⟨r, rfl⟩
        have hmem := Finset.orderEmbOfFin_mem ({r} : Finset (Fin 5))
          (Finset.mem_powersetCard.mp hR1).2 0
        rw [Finset.mem_singleton] at hmem
        simp [hmem]
      have e2 : R2 = {R2.orderEmbOfFin (Finset.mem_powersetCard.mp hR2).2 0} := by
        rcases Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hR2).2 with ⟨r, rfl⟩
        have hmem := Finset.orderEmbOfFin_mem ({r} : Finset (Fin 5))
          (Finset.mem_powersetCard.mp hR2).2 0
        rw [Finset.mem_singleton] at hmem
        simp [hmem]
      rw [e1, e2, hEq]
    · intro r _
      refine ⟨{r}, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_singleton r⟩, ?_⟩
      have hmem := Finset.orderEmbOfFin_mem ({r} : Finset (Fin 5)) (Finset.card_singleton r) 0
      exact Finset.mem_singleton.mp hmem
    · intro R hR
      simp [(Finset.mem_powersetCard.mp hR).2]
  rw [hsumR, Fin.sum_univ_succ]
  have hrow0 : (∑ c : Fin 7, pt x y (0, c)) = -∑ i : Fin 4, y i := by
    rw [Fin.sum_univ_succ]
    simp only [pt_zero_zero, pt_zero_succ, sum_rowPart, add_zero]
  have hrows : ∀ i : Fin 4, (∑ c : Fin 7, pt x y (i.succ, c)) = y i := by
    intro i
    rw [Fin.sum_univ_succ]
    simp only [pt_succ_zero, pt_succ_succ, Finset.sum_const_zero, add_zero]
  rw [hrow0]
  simp_rw [hrows]
  ring

private lemma perm2_eval (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.permanent M = M 0 0 * M 1 1 + M 0 1 * M 1 0 := by
  rw [Matrix.permanent]
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [huniv, Finset.sum_pair (by decide)]
  simp only [Fin.prod_univ_two, Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  ring

private lemma sum_k2 (x : Fin 5 → ℂ) (y : Fin 4 → ℂ) :
    (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7),
      if h : R.card = 2 ∧ C.card = 2 then
        Matrix.permanent (Matrix.of fun a b => pt x y (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0 := by
  have hterm : ∀ (R : Finset (Fin 5)) (C : Finset (Fin 7)),
      (if h : R.card = 2 ∧ C.card = 2 then
        Matrix.permanent (Matrix.of fun a b => pt x y (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) =
      if hR : R.card = 2 then
        if R.orderEmbOfFin hR 0 = 0 then
          if hC : C.card = 2 then
            if C.orderEmbOfFin hC 0 = 0 then
              pt x y (0, C.orderEmbOfFin hC 1) * pt x y (R.orderEmbOfFin hR 1, 0)
            else 0
          else 0
        else 0
      else 0 := by
    intro R C
    by_cases hR : R.card = 2 <;> by_cases hC : C.card = 2
    · simp only [hR, hC, and_self, ↓reduceDIte, perm2_eval, Matrix.of_apply]
      have hr1 : R.orderEmbOfFin hR 1 ≠ 0 := by
        have hlt : R.orderEmbOfFin hR 0 < R.orderEmbOfFin hR 1 :=
          (R.orderEmbOfFin hR).strictMono (by decide : (0 : Fin 2) < 1)
        intro h0
        rw [h0] at hlt
        exact Fin.not_lt_zero _ hlt
      have hc1 : C.orderEmbOfFin hC 1 ≠ 0 := by
        have hlt : C.orderEmbOfFin hC 0 < C.orderEmbOfFin hC 1 :=
          (C.orderEmbOfFin hC).strictMono (by decide : (0 : Fin 2) < 1)
        intro h0
        rw [h0] at hlt
        exact Fin.not_lt_zero _ hlt
      by_cases hr0 : R.orderEmbOfFin hR 0 = 0
      · by_cases hc0 : C.orderEmbOfFin hC 0 = 0
        · simp only [hr0, hc0, ↓reduceIte]
          rw [pt_ne_zero_ne_zero x y hr1 hc1, mul_zero, zero_add]
        · simp only [hr0, hc0, ↓reduceIte]
          rw [pt_ne_zero_ne_zero x y hr1 hc1, pt_ne_zero_ne_zero x y hr1 hc0]
          ring
      · simp only [hr0, ↓reduceIte]
        rw [pt_ne_zero_ne_zero x y hr1 hc1, pt_ne_zero_ne_zero x y hr0 hc1]
        ring
    · simp [hR, hC]
    · simp [hR, hC]
    · simp [hR, hC]
  have hsumC : ∀ (r1 : Fin 5),
      (∑ C : Finset (Fin 7),
        if hC : C.card = 2 then
          if C.orderEmbOfFin hC 0 = 0 then
            pt x y (0, C.orderEmbOfFin hC 1) * pt x y (r1, 0)
          else 0
        else 0) = 0 := by
    intro r1
    have hfilt : (∑ C : Finset (Fin 7),
        if hC : C.card = 2 then
          if C.orderEmbOfFin hC 0 = 0 then
            pt x y (0, C.orderEmbOfFin hC 1) * pt x y (r1, 0)
          else 0
        else 0) =
        ∑ j : Fin 6, pt x y (0, j.succ) * pt x y (r1, 0) := by
      have h1 : (∑ C : Finset (Fin 7),
          if hC : C.card = 2 then
            if C.orderEmbOfFin hC 0 = 0 then
              pt x y (0, C.orderEmbOfFin hC 1) * pt x y (r1, 0)
            else 0
          else 0) =
          ∑ C ∈ (Finset.univ : Finset (Fin 6)).image (fun j => ({0, j.succ} : Finset (Fin 7))),
            if hC : C.card = 2 then
              if C.orderEmbOfFin hC 0 = 0 then
                pt x y (0, C.orderEmbOfFin hC 1) * pt x y (r1, 0)
              else 0
            else 0 := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro C _ hCnot
        by_cases hC : C.card = 2
        · simp only [hC, ↓reduceDIte]
          split_ifs with h0
          · exfalso
            have hc1_ne : C.orderEmbOfFin hC 1 ≠ 0 := by
              have hlt := (C.orderEmbOfFin hC).strictMono (by decide : (0 : Fin 2) < 1)
              rw [h0] at hlt
              exact ne_of_gt hlt
            obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hc1_ne
            have hCeq : C = {0, j.succ} := by
              have hrange : C = Finset.univ.image (C.orderEmbOfFin hC) := by
                ext z
                simp only [Finset.mem_image, Finset.mem_univ, true_and]
                constructor
                · intro hz
                  have hz' : z ∈ Set.range (C.orderEmbOfFin hC) := by
                    rw [Finset.range_orderEmbOfFin]; exact hz
                  exact hz'
                · rintro ⟨a, rfl⟩
                  exact Finset.orderEmbOfFin_mem C hC a
              rw [hrange]
              ext z
              simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.exists_fin_two,
                h0, ← hj, Finset.mem_insert, Finset.mem_singleton, eq_comm]
            exact hCnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hCeq.symm⟩)
          · rfl
        · simp [hC]
      rw [h1, Finset.sum_image]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hcard : ({0, j.succ} : Finset (Fin 7)).card = 2 :=
          Finset.card_pair (Fin.succ_ne_zero j).symm
        have h0 : ({0, j.succ} : Finset (Fin 7)).orderEmbOfFin hcard 0 = 0 := by
          have hm := Finset.orderEmbOfFin_mem ({0, j.succ} : Finset (Fin 7)) hcard 0
          have hm1 := Finset.orderEmbOfFin_mem ({0, j.succ} : Finset (Fin 7)) hcard 1
          have hlt := (({0, j.succ} : Finset (Fin 7)).orderEmbOfFin hcard).strictMono
            (by decide : (0 : Fin 2) < 1)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm hm1
          rcases hm with h | h
          · exact h
          · rcases hm1 with h1' | h1'
            · rw [h, h1'] at hlt; exact absurd hlt (Fin.not_lt_zero _)
            · rw [h, h1'] at hlt; exact absurd hlt (lt_irrefl _)
        have h1' : ({0, j.succ} : Finset (Fin 7)).orderEmbOfFin hcard 1 = j.succ := by
          have hm1 := Finset.orderEmbOfFin_mem ({0, j.succ} : Finset (Fin 7)) hcard 1
          have hlt := (({0, j.succ} : Finset (Fin 7)).orderEmbOfFin hcard).strictMono
            (by decide : (0 : Fin 2) < 1)
          rw [h0] at hlt
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm1
          rcases hm1 with h | h
          · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
          · exact h
        simp [hcard, h0, h1']
      · intro j1 _ j2 _ heq
        dsimp only at heq
        have hj1 : j1.succ ∈ ({0, j2.succ} : Finset (Fin 7)) := by
          rw [← heq]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj1
        rcases hj1 with h0 | h12
        · exact absurd h0 (Fin.succ_ne_zero j1)
        · exact Fin.succ_injective _ h12
    rw [hfilt]
    simp_rw [pt_zero_succ, ← Finset.sum_mul, sum_rowPart, zero_mul]
  refine Finset.sum_eq_zero fun R _ => ?_
  by_cases hR : R.card = 2
  · by_cases hr0 : R.orderEmbOfFin hR 0 = 0
    · have hEq : ∀ C : Finset (Fin 7),
          (if h : R.card = 2 ∧ C.card = 2 then
            Matrix.permanent (Matrix.of fun a b =>
              pt x y (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
          else 0) =
          if hC : C.card = 2 then
            if C.orderEmbOfFin hC 0 = 0 then
              pt x y (0, C.orderEmbOfFin hC 1) * pt x y (R.orderEmbOfFin hR 1, 0)
            else 0
          else 0 := by
        intro C
        rw [hterm R C]
        by_cases hC : C.card = 2
        · by_cases hc0 : C.orderEmbOfFin hC 0 = 0
          · simp [hR, hr0, hC, hc0]
          · simp [hR, hr0, hC, hc0]
        · simp [hR, hr0, hC]
      simp_rw [hEq]
      exact hsumC (R.orderEmbOfFin hR 1)
    · refine Finset.sum_eq_zero fun C _ => ?_
      rw [hterm R C]
      simp [hR, hr0]
  · refine Finset.sum_eq_zero fun C _ => ?_
    simp [hR]

theorem witness :
    ∃ L : Submodule ℂ (Fin 5 × Fin 7 → ℂ),
      Module.finrank ℂ L = 9 ∧
      (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 5 →
        (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7),
          if h : R.card = k ∧ C.card = k then
            Matrix.permanent (Matrix.of fun a b =>
              t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
          else 0) = 0) := by
  refine ⟨LinearMap.range ptLin, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj ptLin_injective, Module.finrank_prod,
      Module.finrank_fin_fun, Module.finrank_fin_fun]
  · rintro _ ⟨⟨x, y⟩, rfl⟩ k hk1 hk5
    have hcases : k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
    rcases hcases with rfl | rfl | hk3
    · exact sum_k1 x y
    · exact sum_k2 x y
    · refine Finset.sum_eq_zero fun R _ => Finset.sum_eq_zero fun C _ => ?_
      split_ifs with h
      · exact perm_ge_three x y k hk3 R C h.1 h.2
      · rfl

end PEqualNP.Outside.L_gct_207_aux

theorem PEqualNP.Outside.L_gct_207 :
    ∃ L : Submodule ℂ (Fin 5 × Fin 7 → ℂ),
      Module.finrank ℂ L = 9 ∧
      (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 5 →
        (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7),
          if h : R.card = k ∧ C.card = k then
            Matrix.permanent (Matrix.of fun a b =>
              t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
          else 0) = 0) :=
  PEqualNP.Outside.L_gct_207_aux.witness
