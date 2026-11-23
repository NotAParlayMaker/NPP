import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_206

open Finset

private def entries (x : Fin 7 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  ![![-(x 0 + x 1 + x 2 + x 3 + x 4), x 0, x 1, x 2, x 3, x 4],
    ![-(x 5 + x 6), 0, 0, 0, 0, 0],
    ![x 5, 0, 0, 0, 0, 0],
    ![x 6, 0, 0, 0, 0, 0]] p.1 p.2

private def family : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := entries
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entries] <;> ring
  map_smul' c x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entries] <;> ring

private theorem family_injective : Function.Injective family := by
  intro x y h
  let positions : Fin 7 → Fin 4 × Fin 6 :=
    ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (2, 0), (3, 0)]
  funext k
  have hk := congrFun h (positions k)
  fin_cases k <;> exact hk

private theorem entries_zero_of_ne (x : Fin 7 → ℂ) (r : Fin 4) (c : Fin 6)
    (hr : r ≠ 0) (hc : c ≠ 0) : entries x (r, c) = 0 := by
  fin_cases r <;> fin_cases c <;> first | contradiction | rfl

private abbrev KSub (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

private noncomputable def MkRect (k : ℕ) (t : Fin 4 × Fin 6 → ℂ) : ℂ :=
  ∑ R : KSub 4 k, ∑ C : KSub 6 k,
    Matrix.permanent (Matrix.of fun a b : Fin k =>
      t (R.1.orderEmbOfFin R.2 a, C.1.orderEmbOfFin C.2 b))

private theorem sum_dite_ksub {n k : ℕ} (F : ∀ S : Finset (Fin n), S.card = k → ℂ) :
    (∑ S : Finset (Fin n), if h : S.card = k then F S h else 0) =
      ∑ S : KSub n k, F S.1 S.2 := by
  have h1 : (∑ S : Finset (Fin n), if h : S.card = k then F S h else 0) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k),
        (if h : S.card = k then F S h else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    split_ifs with h <;> rfl
  rw [h1, Finset.sum_subtype (p := fun S : Finset (Fin n) => S.card = k) _ (by simp)]
  refine Finset.sum_congr rfl (fun S _ => by simp [S.2])

private theorem sum_eq_MkRect (k : ℕ) (t : Fin 4 × Fin 6 → ℂ) :
    (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = MkRect k t := by
  have hinner : ∀ R : Finset (Fin 4),
      (∑ C : Finset (Fin 6),
        if h : R.card = k ∧ C.card = k then
          Matrix.permanent (Matrix.of fun a b =>
            t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0) =
      if hR : R.card = k then
        ∑ C : KSub 6 k,
          Matrix.permanent (Matrix.of fun a b =>
            t (R.orderEmbOfFin hR a, C.1.orderEmbOfFin C.2 b))
      else 0 := by
    intro R
    by_cases hR : R.card = k
    · simp only [hR, dite_true]
      rw [← sum_dite_ksub (fun C hC =>
        Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b)))]
      refine Finset.sum_congr rfl (fun C _ => ?_)
      by_cases hC : C.card = k <;> simp [hR, hC]
    · simp [hR]
  simp_rw [hinner]
  exact sum_dite_ksub _

private def emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) : Fin k ↪ Fin n :=
  ⟨fun b => S.1.orderEmbOfFin S.2 (σ b), (S.1.orderEmbOfFin S.2).injective.comp σ.injective⟩

private theorem range_emb {n k : ℕ} (S : KSub n k) (σ : Equiv.Perm (Fin k)) :
    Set.range (emb S σ) = (S.1 : Set (Fin n)) := by
  change Set.range ((S.1.orderEmbOfFin S.2) ∘ σ) = _
  rw [σ.surjective.range_comp, Finset.range_orderEmbOfFin]

private theorem emb_bijective (n k : ℕ) :
    Function.Bijective (fun p : KSub n k × Equiv.Perm (Fin k) => emb p.1 p.2) := by
  constructor
  · rintro ⟨S, σ⟩ ⟨T, τ⟩ h
    simp only at h
    have hST : S = T := by
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← range_emb S σ, ← range_emb T τ, h]
    subst hST
    have hστ : σ = τ := by
      ext b
      have := DFunLike.congr_fun h b
      exact congrArg Fin.val ((S.1.orderEmbOfFin S.2).injective this)
    rw [hστ]
  · intro i
    let S : KSub n k := ⟨Finset.univ.map i, by simp⟩
    have hmem : ∀ b, i b ∈ S.1 := fun b => by simp [S]
    let f : Fin k → Fin k := fun b => (S.1.orderIsoOfFin S.2).symm ⟨i b, hmem b⟩
    have hf : Function.Injective f := by
      intro b c hbc
      have := congrArg (fun x => ((S.1.orderIsoOfFin S.2 x : S.1) : Fin n)) hbc
      simp only [f, OrderIso.apply_symm_apply] at this
      exact i.injective this
    refine ⟨(S, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)), ?_⟩
    ext b
    simp only [emb, Function.Embedding.coeFn_mk, Equiv.ofBijective_apply]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [f]

private theorem sum_emb (n k : ℕ) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ i, F i = ∑ S : KSub n k, ∑ σ : Equiv.Perm (Fin k), F (emb S σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (emb_bijective n k) (fun p => F (emb p.1 p.2)) F
    (fun _ => rfl)).symm

private theorem sum_perm_perm (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) :
    ∑ σ : Equiv.Perm (Fin k), ∑ τ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a)
      = (k.factorial : ℂ) * M.permanent := by
  rw [Finset.sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin k),
      ∑ σ : Equiv.Perm (Fin k), ∏ a, M (σ a) (τ a) = M.permanent := by
    intro τ
    have h1 : ∀ σ : Equiv.Perm (Fin k),
        ∏ a, M (σ a) (τ a) = ∏ b, M ((σ * τ⁻¹) b) b := by
      intro σ
      exact Fintype.prod_equiv τ _ _ (fun a => by simp)
    simp_rw [h1]
    unfold Matrix.permanent
    exact Fintype.sum_equiv (Equiv.mulRight τ⁻¹) _ _ (fun _ => rfl)
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

private theorem injFormRect (k : ℕ) (t : Fin 4 × Fin 6 → ℂ) :
    (k.factorial : ℂ) * MkRect k t
      = ∑ i : Fin k ↪ Fin 4, ∑ j : Fin k ↪ Fin 6, ∏ a, t (i a, j a) := by
  rw [sum_emb 4 k]
  simp_rw [sum_emb 6 k (fun j => ∏ a, t (_, j a))]
  rw [MkRect, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun R _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [← sum_perm_perm]
  rfl

private def insertPick {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    Fin (n + 1) ↪ Fin (m + 1) :=
  Fin.Embedding.cons (f.trans (finSuccAboveEquiv p).asEmbedding) (a := p) (by
    rintro ⟨i, hi⟩
    exact ((finSuccAboveEquiv p) (f i)).property hi)

private theorem insertPick_zero {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    insertPick p f 0 = p := rfl

private theorem insertPick_succ {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m)
    (i : Fin n) : insertPick p f i.succ = p.succAbove (f i) := rfl

private noncomputable def pickEquiv (n m : ℕ) :
    Fin (m + 1) × (Fin n ↪ Fin m) ≃ (Fin (n + 1) ↪ Fin (m + 1)) :=
  Equiv.ofBijective (fun pf => insertPick pf.1 pf.2) (by
    constructor
    · rintro ⟨p, f⟩ ⟨q, g⟩ h
      have hpq : p = q := congrArg (fun e : Fin (n + 1) ↪ Fin (m + 1) => e 0) h
      subst q
      congr 1
      apply Function.Embedding.ext
      intro i
      apply Fin.succAbove_right_injective
      exact congrArg (fun e : Fin (n + 1) ↪ Fin (m + 1) => e i.succ) h
    · intro e
      let p := e 0
      let f : Fin n ↪ Fin m :=
        ((Fin.Embedding.tail e).codRestrict {j : Fin (m + 1) | j ≠ p} (fun i hi =>
          Fin.succ_ne_zero i (e.injective hi))).trans (finSuccAboveEquiv p).symm.toEmbedding
      refine ⟨(p, f), ?_⟩
      apply Function.Embedding.ext
      intro i
      change insertPick p f i = e i
      refine Fin.cases rfl (fun j => ?_) i
      rw [insertPick_succ]
      exact congrArg Subtype.val ((finSuccAboveEquiv p).apply_symm_apply
        ⟨e j.succ, fun h => Fin.succ_ne_zero j (e.injective h)⟩))

private theorem sumPick {n m : ℕ} (g : (Fin (n + 1) ↪ Fin (m + 1)) → ℂ) :
    (∑ f, g f) = ∑ j : Fin (m + 1), ∑ f : Fin n ↪ Fin m, g (insertPick j f) := by
  rw [← (pickEquiv n m).sum_comp g, Fintype.sum_prod_type]
  rfl

private theorem exists_both_ne_zero {k : ℕ} (i : Fin k ↪ Fin 4) (j : Fin k ↪ Fin 6)
    (a0 a1 a2 : Fin k) (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h12 : a1 ≠ a2) :
    ∃ a : Fin k, i a ≠ 0 ∧ j a ≠ 0 := by
  by_cases hi0 : i a0 = 0
  · have hi1 : i a1 ≠ 0 := fun h => h01 (i.injective (hi0.trans h.symm))
    have hi2 : i a2 ≠ 0 := fun h => h02 (i.injective (hi0.trans h.symm))
    by_cases hj1 : j a1 = 0
    · have hj2 : j a2 ≠ 0 := fun h => h12 (j.injective (hj1.trans h.symm))
      exact ⟨a2, hi2, hj2⟩
    · exact ⟨a1, hi1, hj1⟩
  · by_cases hj0 : j a0 = 0
    · have hj1 : j a1 ≠ 0 := fun h => h01 (j.injective (hj0.trans h.symm))
      have hj2 : j a2 ≠ 0 := fun h => h02 (j.injective (hj0.trans h.symm))
      by_cases hi1 : i a1 = 0
      · have hi2 : i a2 ≠ 0 := fun h => h12 (i.injective (hi1.trans h.symm))
        exact ⟨a2, hi2, hj2⟩
      · exact ⟨a1, hi1, hj1⟩
    · exact ⟨a0, hi0, hj0⟩

private theorem inj_sum_one (x : Fin 7 → ℂ) :
    (∑ i : Fin 1 ↪ Fin 4, ∑ j : Fin 1 ↪ Fin 6, ∏ a : Fin 1, entries x (i a, j a)) = 0 := by
  rw [sumPick (n := 0) (m := 3)]
  simp_rw [sumPick (n := 0) (m := 5)]
  simp only [Fintype.sum_unique, Fin.prod_univ_one, insertPick_zero]
  simp [Fin.sum_univ_four, Fin.sum_univ_six, entries]
  ring

private theorem inj_sum_two_row (x : Fin 7 → ℂ) (c0 c1 : Fin 6) (hc : c0 ≠ c1) :
    (∑ i : Fin 2 ↪ Fin 4, (entries x (i 0, c0) * entries x (i (Fin.succ 0), c1))) = 0 := by
  simp only [sumPick (n := 1) (m := 3), sumPick (n := 0) (m := 2),
    Fintype.sum_unique, Fin.sum_univ_succ,
    insertPick_zero, insertPick_succ]
  fin_cases c0 <;> fin_cases c1 <;> first | contradiction | (simp +decide [entries, Fin.succAbove]; try ring)

private theorem inj_sum_two (x : Fin 7 → ℂ) :
    (∑ i : Fin 2 ↪ Fin 4, ∑ j : Fin 2 ↪ Fin 6, ∏ a : Fin 2, entries x (i a, j a)) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  have hj : j 0 ≠ j (Fin.succ 0) := fun h => (by decide : (0 : Fin 2) ≠ Fin.succ 0) (j.injective h)
  exact inj_sum_two_row x (j 0) (j (Fin.succ 0)) hj

private theorem inj_sum_three (x : Fin 7 → ℂ) :
    (∑ i : Fin 3 ↪ Fin 4, ∑ j : Fin 3 ↪ Fin 6, ∏ a : Fin 3, entries x (i a, j a)) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  obtain ⟨a, hia, hja⟩ := exists_both_ne_zero i j 0 1 2 (by decide) (by decide) (by decide)
  exact Finset.prod_eq_zero (Finset.mem_univ a) (entries_zero_of_ne x (i a) (j a) hia hja)

private theorem inj_sum_four (x : Fin 7 → ℂ) :
    (∑ i : Fin 4 ↪ Fin 4, ∑ j : Fin 4 ↪ Fin 6, ∏ a : Fin 4, entries x (i a, j a)) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  obtain ⟨a, hia, hja⟩ := exists_both_ne_zero i j 0 1 2 (by decide) (by decide) (by decide)
  exact Finset.prod_eq_zero (Finset.mem_univ a) (entries_zero_of_ne x (i a) (j a) hia hja)

private theorem mkRect_eq_zero (x : Fin 7 → ℂ) (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    MkRect k (entries x) = 0 := by
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  apply mul_left_cancel₀ hfac
  rw [mul_zero, injFormRect]
  interval_cases k
  · exact inj_sum_one x
  · exact inj_sum_two x
  · exact inj_sum_three x
  · exact inj_sum_four x

private theorem main_thm :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), Module.finrank ℂ L = 7 ∧
      (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
        (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
          if h : R.card = k ∧ C.card = k then
            Matrix.permanent (Matrix.of fun a b =>
              t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
          else 0) = 0) := by
  refine ⟨LinearMap.range family, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj family_injective, Module.finrank_fin_fun]
  · rintro t ⟨x, rfl⟩ k hk1 hk4
    change (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b =>
          entries x (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0
    rw [sum_eq_MkRect]
    exact mkRect_eq_zero x k hk1 hk4

end PEqualNP.Outside.L_gct_206

theorem PEqualNP.Outside.L_gct_206 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), Module.finrank ℂ L = 7 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) :=
  PEqualNP.Outside.L_gct_206.main_thm
