import Mathlib

private def rowColumnForm (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) (ij : Fin 4 × Fin 6) : ℂ :=
  Fin.cases
    (Fin.cases (-(∑ j, x.1 j)) x.1 ij.2)
    (fun i => if ij.2 = 0 then Fin.cases (-(∑ j, x.2 j)) x.2 i else 0)
    ij.1

private def rowColumnMap : ((Fin 5 → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := rowColumnForm
  map_add' x y := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;>
        simp [rowColumnForm, Finset.sum_add_distrib, add_comm]
    · refine Fin.cases ?_ (fun l => ?_) j
      · refine Fin.cases ?_ (fun l => ?_) k
        · change -(∑ l, (x + y).2 l) = -(∑ l, x.2 l) + -(∑ l, y.2 l)
          simp [Finset.sum_add_distrib, add_comm]
        · simp [rowColumnForm]
      · simp [rowColumnForm]
  map_smul' c x := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;> simp [rowColumnForm, Finset.mul_sum]
    · refine Fin.cases ?_ (fun l => ?_) j
      · refine Fin.cases ?_ (fun l => ?_) k
        · change -(∑ l, (c • x).2 l) = c * -(∑ l, x.2 l)
          simp
          ring
        · simp [rowColumnForm]
      · simp [rowColumnForm]

private theorem rowColumnMap_injective : Function.Injective rowColumnMap := by
  intro x y h
  apply Prod.ext
  · funext j
    exact congrFun h ((0 : Fin 4), j.succ)
  · funext i
    have hh := congrFun h (i.succ.succ, (0 : Fin 6))
    exact hh

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

private theorem rowColumnEntry (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) (i : Fin 4) (j : Fin 6) :
    rowColumnForm x (i, j) =
      if i = 0 then
        if j = 0 then -(∑ k, x.1 k)
        else if j = 1 then x.1 0
        else if j = 2 then x.1 1
        else if j = 3 then x.1 2
        else if j = 4 then x.1 3
        else x.1 4
      else if j = 0 then
        if i = 1 then -(∑ k, x.2 k) else if i = 2 then x.2 0 else x.2 1
      else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem rowColumnFiber (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) (j : Fin 6) :
    (∑ f : Fin 3 ↪ Fin 5, ∏ i : Fin 4, (1 + rowColumnForm x (i, insertPick j f i))) =
      60 * (1 + rowColumnForm x (0, j)) := by
  simp only [sumPick (n := 2) (m := 4), sumPick (n := 1) (m := 3),
    sumPick (n := 0) (m := 2)]
  simp only [Fintype.sum_unique, Fin.sum_univ_succ,
    Fin.prod_univ_succ, Fin.prod_univ_zero, insertPick_zero, insertPick_succ, mul_one]
  fin_cases j <;>
    simp +decide [rowColumnEntry, Fin.succAbove, Fin.sum_univ_succ] <;> ring

private theorem rowColumnSum (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + rowColumnForm x (i, f i))) = 360 := by
  rw [sumPick]
  simp_rw [rowColumnFiber]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h : (∑ j : Fin 6, rowColumnForm x (0, j)) = 0 := by
    rw [Fin.sum_univ_succ]
    simp [rowColumnForm]
  rw [h]
  norm_num


private lemma sum_finset_card_eq {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (hk : k ≤ Fintype.card α) (f : Finset α → ℂ) :
    (∑ s : Finset α, if s.card = k then f s else 0) =
      ∑ s ∈ (Finset.univ : Finset α).powersetCard k, f s := by
  have huniv : (Finset.univ : Finset (Finset α)) = (Finset.univ : Finset α).powerset := by
    ext s; simp
  rw [huniv, Finset.sum_powerset]
  rw [Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [if_pos (Finset.mem_powersetCard.mp hs).2]
  · intro j hj hjk
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [if_neg]
    intro h
    exact hjk ((Finset.mem_powersetCard.mp hs).2 ▸ h)
  · intro hknot
    exfalso
    exact hknot (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

private lemma total_sum_zero (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) :
    (∑ i : Fin 4, ∑ j : Fin 6, rowColumnForm x (i, j)) = 0 := by
  simp only [Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six, rowColumnEntry]
  simp
  ring

private lemma permanent_eq_zero_of_cross {k : ℕ} (hk : 2 < k)
    (M : Matrix (Fin k) (Fin k) ℂ) (r0 c0 : Fin k)
    (h : ∀ i j, i ≠ r0 → j ≠ c0 → M i j = 0) : M.permanent = 0 := by
  rw [Matrix.permanent]
  refine Finset.sum_eq_zero fun σ _ => ?_
  let i0 := σ.symm r0
  have hcard : 1 < (Finset.univ.erase c0).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, hi, hii0⟩ := Finset.exists_mem_ne hcard i0
  have hic : i ≠ c0 := (Finset.mem_erase.mp hi).1
  have hsig : σ i ≠ r0 := by
    intro hsr
    apply hii0
    have h' : σ.symm (σ i) = σ.symm r0 := congrArg σ.symm hsr
    simpa using h'
  exact Finset.prod_eq_zero (Finset.mem_univ i) (h (σ i) i hsig hic)

private lemma submatrix_permanent_zero {k : ℕ} (hk : 2 < k)
    (R : Finset (Fin 4)) (C : Finset (Fin 6)) (hR : R.card = k) (hC : C.card = k)
    (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) :
    Matrix.permanent (Matrix.of fun a b =>
      rowColumnForm x (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b)) = 0 := by
  let r0 : Fin k := if h0 : (0 : Fin 4) ∈ R then (R.orderIsoOfFin hR).symm ⟨0, h0⟩ else ⟨0, by omega⟩
  let c0 : Fin k := if h0 : (0 : Fin 6) ∈ C then (C.orderIsoOfFin hC).symm ⟨0, h0⟩ else ⟨0, by omega⟩
  refine permanent_eq_zero_of_cross hk _ r0 c0 ?_
  intro i j hi hj
  have hrow : R.orderEmbOfFin hR i ≠ 0 := by
    intro hzero
    by_cases h0 : (0 : Fin 4) ∈ R
    · have hr0 : R.orderEmbOfFin hR r0 = 0 := by
        dsimp [r0]; rw [dif_pos h0]
        change ((R.orderIsoOfFin hR) ((R.orderIsoOfFin hR).symm ⟨0, h0⟩) : Fin 4) = 0
        simp
      apply hi
      apply (R.orderEmbOfFin hR).injective
      rw [hzero, hr0]
    · exact h0 (hzero ▸ R.orderEmbOfFin_mem hR i)
  have hcol : C.orderEmbOfFin hC j ≠ 0 := by
    intro hzero
    by_cases h0 : (0 : Fin 6) ∈ C
    · have hc0 : C.orderEmbOfFin hC c0 = 0 := by
        dsimp [c0]; rw [dif_pos h0]
        change ((C.orderIsoOfFin hC) ((C.orderIsoOfFin hC).symm ⟨0, h0⟩) : Fin 6) = 0
        simp
      apply hj
      apply (C.orderEmbOfFin hC).injective
      rw [hzero, hc0]
    · exact h0 (hzero ▸ C.orderEmbOfFin_mem hC j)
  simp [rowColumnEntry, hrow, hcol]


private lemma orderEmb_singleton {α : Type*} [LinearOrder α] (a : α)
    (h : ({a} : Finset α).card = 1) (i : Fin 1) :
    ({a} : Finset α).orderEmbOfFin h i = a := by
  fin_cases i
  simp [Finset.orderEmbOfFin_apply, Finset.sort_singleton]

private lemma orderEmb_pair {α : Type*} [LinearOrder α] {a b : α} (hab : a < b)
    (h : ({a, b} : Finset α).card = 2) (i : Fin 2) :
    ({a, b} : Finset α).orderEmbOfFin h i = if i = 0 then a else b := by
  have hs : ({a, b} : Finset α).sort (· ≤ ·) = [a, b] := by
    have hset : ({a, b} : Finset α) = insert a ({b} : Finset α) := by ext x; simp
    rw [hset]
    rw [Finset.sort_insert (· ≤ ·) (s := {b}) (a := a)
      (by intro x hx; simp at hx; subst x; exact hab.le) (by simp [hab.ne])]
    rw [Finset.sort_singleton (· ≤ ·)]
  fin_cases i <;> simp [Finset.orderEmbOfFin_apply, hs]

private lemma permanent_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.permanent = M 0 0 * M 1 1 + M 0 1 * M 1 0 := by
  rw [Matrix.permanent]
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, Fin.prod_univ_two, Equiv.Perm.decomposeFin_symm_apply_zero]
  ring


set_option maxRecDepth 10000 in
private lemma M1_zero (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) :
    (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
      if h : R.card = 1 ∧ C.card = 1 then
        Matrix.permanent (Matrix.of fun a b =>
          rowColumnForm x (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0 := by
  let per : (R : Finset (Fin 4)) → R.card = 1 → (C : Finset (Fin 6)) → C.card = 1 → ℂ :=
    fun R hR C hC => Matrix.permanent (Matrix.of fun a b =>
      rowColumnForm x (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b))
  let S : Finset (Finset (Fin 4)) := Finset.univ.filter (fun R => R.card = 1)
  let T : Finset (Finset (Fin 6)) := Finset.univ.filter (fun C => C.card = 1)
  let g : Finset (Fin 4) → ℂ := fun R =>
    if hR : R.card = 1 then ∑ C ∈ T, if hC : C.card = 1 then per R hR C hC else 0 else 0
  change (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
      if h : R.card = 1 ∧ C.card = 1 then per R h.1 C h.2 else 0) = 0
  have h1 : (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
        if h : R.card = 1 ∧ C.card = 1 then per R h.1 C h.2 else 0)
      = ∑ R ∈ S, ∑ C : Finset (Fin 6),
        if h : R.card = 1 ∧ C.card = 1 then per R h.1 C h.2 else 0 := by
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro R _ hR
    have hp : ¬ R.card = 1 := by simpa [S] using hR
    refine Finset.sum_eq_zero fun C _ => ?_
    rw [dif_neg (show ¬(R.card = 1 ∧ C.card = 1) from fun h => hp h.1)]
  rw [h1]
  have h2 : ∀ R ∈ S, (∑ C : Finset (Fin 6),
        if h : R.card = 1 ∧ C.card = 1 then per R h.1 C h.2 else 0) = g R := by
    intro R hR
    have hp : R.card = 1 := (Finset.mem_filter.mp hR).2
    dsimp [g]
    rw [dif_pos hp]
    have hzero : (∑ C : Finset (Fin 6),
          if h : R.card = 1 ∧ C.card = 1 then per R h.1 C h.2 else 0)
        = ∑ C ∈ T, if h : R.card = 1 ∧ C.card = 1 then per R h.1 C h.2 else 0 := by
      refine (Finset.sum_subset (Finset.subset_univ T) ?_).symm
      intro C _ hC
      have hq : ¬ C.card = 1 := by simpa [T] using hC
      rw [dif_neg (show ¬(R.card = 1 ∧ C.card = 1) from fun h => hq h.2)]
    rw [hzero]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hq : C.card = 1 := (Finset.mem_filter.mp hC).2
    rw [dif_pos (show R.card = 1 ∧ C.card = 1 from ⟨hp, hq⟩)]
    rw [dif_pos hq]
  rw [Finset.sum_congr rfl h2]
  have hS : S = ({ {0}, {1}, {2}, {3} } : Finset (Finset (Fin 4))) := by
    decide
  have hT : T = ({ {0}, {1}, {2}, {3}, {4}, {5} } : Finset (Finset (Fin 6))) := by
    decide
  rw [hS]
  simp [g, hT, per, orderEmb_singleton, rowColumnEntry, Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six]
  rw [← total_sum_zero x]
  simp [Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six, rowColumnEntry]
  ring

set_option maxRecDepth 10000 in
private lemma M2_zero (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) :
    (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
      if h : R.card = 2 ∧ C.card = 2 then
        Matrix.permanent (Matrix.of fun a b =>
          rowColumnForm x (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0 := by
  let per : (R : Finset (Fin 4)) → R.card = 2 → (C : Finset (Fin 6)) → C.card = 2 → ℂ :=
    fun R hR C hC => Matrix.permanent (Matrix.of fun a b =>
      rowColumnForm x (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b))
  let S : Finset (Finset (Fin 4)) := Finset.univ.filter (fun R => R.card = 2)
  let T : Finset (Finset (Fin 6)) := Finset.univ.filter (fun C => C.card = 2)
  let g : Finset (Fin 4) → ℂ := fun R =>
    if hR : R.card = 2 then ∑ C ∈ T, if hC : C.card = 2 then per R hR C hC else 0 else 0
  change (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
      if h : R.card = 2 ∧ C.card = 2 then per R h.1 C h.2 else 0) = 0
  have h1 : (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
        if h : R.card = 2 ∧ C.card = 2 then per R h.1 C h.2 else 0)
      = ∑ R ∈ S, ∑ C : Finset (Fin 6),
        if h : R.card = 2 ∧ C.card = 2 then per R h.1 C h.2 else 0 := by
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro R _ hR
    have hp : ¬ R.card = 2 := by simpa [S] using hR
    refine Finset.sum_eq_zero fun C _ => ?_
    rw [dif_neg (show ¬(R.card = 2 ∧ C.card = 2) from fun h => hp h.1)]
  rw [h1]
  have h2 : ∀ R ∈ S, (∑ C : Finset (Fin 6),
        if h : R.card = 2 ∧ C.card = 2 then per R h.1 C h.2 else 0) = g R := by
    intro R hR
    have hp : R.card = 2 := (Finset.mem_filter.mp hR).2
    dsimp [g]
    rw [dif_pos hp]
    have hzero : (∑ C : Finset (Fin 6),
          if h : R.card = 2 ∧ C.card = 2 then per R h.1 C h.2 else 0)
        = ∑ C ∈ T, if h : R.card = 2 ∧ C.card = 2 then per R h.1 C h.2 else 0 := by
      refine (Finset.sum_subset (Finset.subset_univ T) ?_).symm
      intro C _ hC
      have hq : ¬ C.card = 2 := by simpa [T] using hC
      rw [dif_neg (show ¬(R.card = 2 ∧ C.card = 2) from fun h => hq h.2)]
    rw [hzero]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hq : C.card = 2 := (Finset.mem_filter.mp hC).2
    rw [dif_pos (show R.card = 2 ∧ C.card = 2 from ⟨hp, hq⟩)]
    rw [dif_pos hq]
  rw [Finset.sum_congr rfl h2]
  have hS : S = ({{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}} : Finset (Finset (Fin 4))) := by decide
  have hT : T = ({{0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {1,2}, {1,3}, {1,4}, {1,5}, {2,3}, {2,4}, {2,5}, {3,4}, {3,5}, {4,5}} : Finset (Finset (Fin 6))) := by decide
  rw [hS]
  simp +decide [g, hT, per, orderEmb_pair, permanent_fin_two, rowColumnEntry,
    Finset.sum_insert, Finset.sum_singleton]
  ring

private lemma M_ge_three (k : ℕ) (hk : 2 < k) (x : (Fin 5 → ℂ) × (Fin 2 → ℂ)) :
    (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b =>
          rowColumnForm x (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0 := by
  refine Finset.sum_eq_zero fun R _ => Finset.sum_eq_zero fun C _ => ?_
  by_cases h : R.card = k ∧ C.card = k
  · simp [h, submatrix_permanent_zero hk R C h.1 h.2 x]
  · simp [h]

theorem PEqualNP.Outside.L_gct_206 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
    Module.finrank ℂ L = 7 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
        if h : R.card = k ∧ C.card = k then
          Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0) = 0) := by
  refine ⟨rowColumnMap.range, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj rowColumnMap_injective, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    decide
  · rintro t ⟨x, rfl⟩ k hk1 hk4
    interval_cases k
    · exact M1_zero x
    · exact M2_zero x
    · exact M_ge_three 3 (by omega) x
    · exact M_ge_three 4 (by omega) x
