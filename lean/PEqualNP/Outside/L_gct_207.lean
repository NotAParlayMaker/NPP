import Mathlib
import PEqualNP.Defs

namespace Gap207

open Finset

lemma emb_ne_zero {n k : ℕ} (S : Finset (Fin (n + 1))) (h : S.card = k) (a b : Fin k)
    (hab : a < b) : S.orderEmbOfFin h b ≠ 0 := by
  have h1 : S.orderEmbOfFin h a < S.orderEmbOfFin h b := (S.orderEmbOfFin h).strictMono hab
  exact (lt_of_le_of_lt (Fin.zero_le _) h1).ne'

lemma emb_zero_of_mem {n : ℕ} (S : Finset (Fin (n + 1))) (h : S.card = 2) (h0 : 0 ∈ S) :
    S.orderEmbOfFin h 0 = 0 := by
  rw [show (0 : Fin 2) = ⟨0, by omega⟩ from rfl, Finset.orderEmbOfFin_zero h (by omega)]
  exact le_antisymm (Finset.min'_le _ _ h0) (Fin.zero_le _)

lemma emb_ne_of_not_mem {n k : ℕ} (S : Finset (Fin (n + 1))) (h : S.card = k) (h0 : 0 ∉ S)
    (a : Fin k) : S.orderEmbOfFin h a ≠ 0 := fun e =>
  h0 (e ▸ Finset.orderEmbOfFin_mem S h a)

lemma emb_last_two {n : ℕ} (S : Finset (Fin (n + 1))) (h : S.card = 2) :
    S.orderEmbOfFin h 1 = S.sup id := by
  rw [show (1 : Fin 2) = ⟨2 - 1, by omega⟩ from rfl, Finset.orderEmbOfFin_last h (by omega),
    Finset.max'_eq_sup', Finset.sup'_eq_sup]

lemma emb_last_one {n : ℕ} (S : Finset (Fin (n + 1))) (h : S.card = 1) :
    S.orderEmbOfFin h 0 = S.sup id := by
  rw [show (0 : Fin 1) = ⟨1 - 1, by omega⟩ from rfl, Finset.orderEmbOfFin_last h (by omega),
    Finset.max'_eq_sup', Finset.sup'_eq_sup]

lemma sum_one {n : ℕ} (u : Fin (n + 1) → ℂ) :
    (∑ R : Finset (Fin (n + 1)), if R.card = 1 then u (R.sup id) else 0) = ∑ i, u i := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun i _ => ({i} : Finset _)) ?_ ?_ ?_ ?_
  · intro i _; simp
  · intro i _ j _ hij; simpa using hij
  · intro R hR
    rw [Finset.mem_filter, Finset.card_eq_one] at hR
    obtain ⟨_, a, rfl⟩ := hR
    exact ⟨a, mem_univ _, rfl⟩
  · intro i _; simp

lemma sum_two {n : ℕ} (u : Fin (n + 1) → ℂ) :
    (∑ R : Finset (Fin (n + 1)), if R.card = 2 ∧ 0 ∈ R then u (R.sup id) else 0)
      = ∑ i : Fin n, u i.succ := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun i _ => ({0, i.succ} : Finset _)) ?_ ?_ ?_ ?_
  · intro i _
    simp [Finset.card_pair (Fin.succ_ne_zero i).symm]
  · intro i _ j _ hij
    have : (({0, i.succ} : Finset (Fin (n + 1))).sup id) = ({0, j.succ} : Finset _).sup id := by
      rw [hij]
    simpa using this
  · intro R hR
    rw [Finset.mem_filter, Finset.card_eq_two] at hR
    obtain ⟨_, ⟨x, y, hxy, rfl⟩, h0⟩ := hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0
    rcases h0 with h0 | h0
    · subst h0
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hxy.symm
      exact ⟨j, mem_univ _, rfl⟩
    · subst h0
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hxy
      exact ⟨j, mem_univ _, Finset.pair_comm _ _⟩
  · intro i _; simp

lemma perm_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.permanent = M 0 0 * M 1 1 + M 1 0 * M 0 1 := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Matrix.permanent, hu, Finset.sum_pair (by decide)]
  simp [Fin.prod_univ_two]

/-- The level conditions for a matrix supported on row 0 and column 0. -/
lemma level {m n : ℕ} (t : Fin (m + 1) × Fin (n + 1) → ℂ)
    (hsupp : ∀ i j, i ≠ 0 → j ≠ 0 → t (i, j) = 0)
    (hrow : ∑ j, t (0, j) = 0) (hcol : ∑ i : Fin m, t (i.succ, 0) = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ R : Finset (Fin (m + 1)), ∑ C : Finset (Fin (n + 1)),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0 := by
  obtain rfl | rfl | h3 : k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  · have key : ∀ (R : Finset (Fin (m + 1))) (C : Finset (Fin (n + 1))),
        (if h : R.card = 1 ∧ C.card = 1 then
          Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0) = if R.card = 1 then (if C.card = 1 then t (R.sup id, C.sup id) else 0) else 0 := by
      intro R C
      by_cases hR : R.card = 1
      · by_cases hC : C.card = 1
        · rw [dif_pos ⟨hR, hC⟩, if_pos hR, if_pos hC]
          simp [Matrix.permanent, emb_last_one]
        · rw [dif_neg (fun h => hC h.2), if_pos hR, if_neg hC]
      · rw [dif_neg (fun h => hR h.1), if_neg hR]
    simp_rw [key]
    have h1 : ∀ R : Finset (Fin (m + 1)),
        (∑ C : Finset (Fin (n + 1)),
          if R.card = 1 then (if C.card = 1 then t (R.sup id, C.sup id) else 0) else 0)
        = if R.card = 1 then (fun i => ∑ j, t (i, j)) (R.sup id) else 0 := by
      intro R
      split_ifs with hR
      · exact sum_one (fun j => t (R.sup id, j))
      · simp
    simp_rw [h1]
    rw [sum_one (fun i => ∑ j, t (i, j)), Fin.sum_univ_succ, hrow, zero_add]
    have : ∀ i : Fin m, ∑ j, t (i.succ, j) = t (i.succ, 0) := by
      intro i
      rw [Fin.sum_univ_succ]
      simp [hsupp i.succ _ (Fin.succ_ne_zero i) (Fin.succ_ne_zero _)]
    simp_rw [this]
    exact hcol
  · have key : ∀ (R : Finset (Fin (m + 1))) (C : Finset (Fin (n + 1))),
        (if h : R.card = 2 ∧ C.card = 2 then
          Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0) = (if R.card = 2 ∧ 0 ∈ R then (fun i => t (i, 0)) (R.sup id) else 0) *
          (if C.card = 2 ∧ 0 ∈ C then (fun j => t (0, j)) (C.sup id) else 0) := by
      intro R C
      by_cases h : R.card = 2 ∧ C.card = 2
      · rw [dif_pos h, perm_two]
        simp only [Matrix.of_apply]
        have hr1 := emb_ne_zero R h.1 0 1 (by decide)
        have hc1 := emb_ne_zero C h.2 0 1 (by decide)
        rw [hsupp _ _ hr1 hc1, mul_zero, zero_add]
        by_cases hR : 0 ∈ R
        · by_cases hC : 0 ∈ C
          · rw [if_pos ⟨h.1, hR⟩, if_pos ⟨h.2, hC⟩, emb_zero_of_mem R h.1 hR,
              emb_zero_of_mem C h.2 hC, emb_last_two, emb_last_two]
          · rw [hsupp _ _ hr1 (emb_ne_of_not_mem C h.2 hC 0)]
            simp [hC]
        · rw [hsupp _ _ (emb_ne_of_not_mem R h.1 hR 0) hc1]
          simp [hR]
      · rw [dif_neg h]
        by_cases hR : R.card = 2
        · have hC : ¬ C.card = 2 := fun hC => h ⟨hR, hC⟩
          simp [hC]
        · simp [hR]
    simp_rw [key]
    rw [← Finset.sum_mul_sum, sum_two (fun i => t (i, 0)), hcol, zero_mul]
  · refine Finset.sum_eq_zero fun R _ => Finset.sum_eq_zero fun C _ => ?_
    split_ifs with h
    · rw [Matrix.permanent]
      refine Finset.sum_eq_zero fun σ _ => ?_
      simp only [Matrix.of_apply]
      have hc1 := emb_ne_zero C h.2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
      have hc2 := emb_ne_zero C h.2 ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
      by_cases hσ : R.orderEmbOfFin h.1 (σ ⟨1, by omega⟩) = 0
      · have hne : R.orderEmbOfFin h.1 (σ ⟨2, by omega⟩) ≠ 0 := by
          intro h2
          have := σ.injective ((R.orderEmbOfFin h.1).injective (hσ.trans h2.symm))
          simp at this
        exact Finset.prod_eq_zero (mem_univ ⟨2, by omega⟩) (hsupp _ _ hne hc2)
      · exact Finset.prod_eq_zero (mem_univ ⟨1, by omega⟩) (hsupp _ _ hσ hc1)
    · rfl

def colPart (y : Fin 3 → ℂ) : Fin 4 → ℂ :=
  Fin.lastCases (-∑ l, y l) y

lemma colPart_last (y : Fin 3 → ℂ) : colPart y (Fin.last 3) = -∑ l, y l :=
  Fin.lastCases_last

lemma colPart_castSucc (y : Fin 3 → ℂ) (i : Fin 3) : colPart y i.castSucc = y i := by
  simp [colPart]

def pt (x : Fin 6 → ℂ) (y : Fin 3 → ℂ) : Fin 5 × Fin 7 → ℂ :=
  fun p => Fin.cases (Fin.cases (-∑ j, x j) x p.2)
    (fun i => Fin.cases (colPart y i) (fun _ => 0) p.2) p.1

lemma pt_zero_zero (x : Fin 6 → ℂ) (y : Fin 3 → ℂ) : pt x y (0, 0) = -∑ j, x j := rfl

lemma pt_zero_succ (x : Fin 6 → ℂ) (y : Fin 3 → ℂ) (j : Fin 6) : pt x y (0, j.succ) = x j := rfl

lemma pt_succ_zero (x : Fin 6 → ℂ) (y : Fin 3 → ℂ) (i : Fin 4) :
    pt x y (i.succ, 0) = colPart y i := rfl

lemma pt_last_zero (x : Fin 6 → ℂ) (y : Fin 3 → ℂ) :
    pt x y ((Fin.last 3).succ, 0) = -∑ l, y l := by
  rw [pt_succ_zero, colPart_last]

lemma pt_cast_zero (x : Fin 6 → ℂ) (y : Fin 3 → ℂ) (i : Fin 3) :
    pt x y (i.castSucc.succ, 0) = y i := by
  rw [pt_succ_zero, colPart_castSucc]

lemma pt_succ_succ (x : Fin 6 → ℂ) (y : Fin 3 → ℂ) (i : Fin 4) (j : Fin 6) :
    pt x y (i.succ, j.succ) = 0 := rfl

def ptLin : ((Fin 6 → ℂ) × (Fin 3 → ℂ)) →ₗ[ℂ] (Fin 5 × Fin 7 → ℂ) where
  toFun v := pt v.1 v.2
  map_add' v w := by
    funext ⟨i, j⟩
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simp [pt_zero_zero, sum_add_distrib]; ring
      · intro j; simp [pt_zero_succ]
    · intro i
      refine Fin.cases ?_ ?_ j
      · refine Fin.lastCases ?_ ?_ i
        · simp only [pt_last_zero, Prod.fst_add, Prod.snd_add, Pi.add_apply, sum_add_distrib]; ring
        · intro i; simp only [pt_cast_zero, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      · intro j; simp [pt_succ_succ]
  map_smul' c v := by
    funext ⟨i, j⟩
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simp [pt_zero_zero, mul_sum]
      · intro j; simp [pt_zero_succ]
    · intro i
      refine Fin.cases ?_ ?_ j
      · refine Fin.lastCases ?_ ?_ i
        · simp only [pt_last_zero, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_neg, mul_sum]
        · intro i; simp only [pt_cast_zero, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      · intro j; simp [pt_succ_succ]

lemma ptLin_injective : Function.Injective ptLin := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h' : pt x y = pt x' y' := h
  have hx : x = x' := by
    funext j
    have := congrFun h' (0, j.succ)
    simpa only [pt_zero_succ] using this
  have hy : y = y' := by
    funext i
    have := congrFun h' (i.castSucc.succ, 0)
    simpa only [pt_cast_zero] using this
  rw [hx, hy]

end Gap207

theorem PEqualNP.Outside.L_gct_207 : ∃ L : Submodule ℂ (Fin 5 × Fin 7 → ℂ), Module.finrank ℂ L = 9 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 5 → (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) := by
  refine ⟨LinearMap.range Gap207.ptLin, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj Gap207.ptLin_injective]
    simp
  · rintro t ⟨⟨x, y⟩, rfl⟩ k hk _
    change (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => Gap207.pt x y (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0
    refine Gap207.level (m := 4) (n := 6) (Gap207.pt x y) ?_ ?_ ?_ k hk
    · intro i j hi hj
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hi
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hj
      rfl
    · have e : (∑ j : Fin 7, Gap207.pt x y (0, j)) = -∑ j, x j + ∑ j, x j := Fin.sum_univ_succ _
      exact e.trans (by ring)
    · have e : (∑ i : Fin 4, Gap207.pt x y (i.succ, 0)) = ∑ i : Fin 3, y i + -∑ l, y l := by
        rw [Fin.sum_univ_castSucc, Gap207.pt_last_zero]
        simp only [Gap207.pt_cast_zero]
      exact e.trans (by ring)
