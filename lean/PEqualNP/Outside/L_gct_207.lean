import Mathlib
import PEqualNP.Defs

-- The witness: matrices that vanish outside the first row and the first column, whose first
-- row sums to zero and whose first column, below the corner, sums to zero. Dimension 6 + 3.
-- A k x k subpermanent with k at least 3 has a factor outside the first row and column, so it
-- vanishes; the sums for k = 1 and k = 2 vanish by a direct count.

namespace PEqualNP.Outside.L_gct_207_aux

open Finset

noncomputable def form (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) (ij : Fin 5 × Fin 7) : ℂ :=
  Fin.cases
    (Fin.cases (-(∑ j, x.1 j)) x.1 ij.2)
    (fun i => if ij.2 = 0 then Fin.cases (-(∑ j, x.2 j)) x.2 i else 0)
    ij.1

noncomputable def formMap : ((Fin 6 → ℂ) × (Fin 3 → ℂ)) →ₗ[ℂ] (Fin 5 × Fin 7 → ℂ) where
  toFun := form
  map_add' x y := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;>
        simp [form, Finset.sum_add_distrib, add_comm]
    · refine Fin.cases ?_ (fun l => ?_) j
      · refine Fin.cases ?_ (fun l => ?_) k
        · change -(∑ l, (x + y).2 l) = -(∑ l, x.2 l) + -(∑ l, y.2 l)
          simp [Finset.sum_add_distrib, add_comm]
        · simp [form]
      · simp [form]
  map_smul' c x := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;> simp [form, Finset.mul_sum]
    · refine Fin.cases ?_ (fun l => ?_) j
      · refine Fin.cases ?_ (fun l => ?_) k
        · change -(∑ l, (c • x).2 l) = c * -(∑ l, x.2 l)
          simp [Finset.mul_sum]
        · simp [form]
      · simp [form]

theorem formMap_apply (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) (ij : Fin 5 × Fin 7) :
    formMap x ij = form x ij := rfl

theorem formMap_injective : Function.Injective formMap := by
  intro x y h
  apply Prod.ext
  · funext j
    exact congrFun h ((0 : Fin 5), j.succ)
  · funext i
    exact congrFun h (i.succ.succ, (0 : Fin 7))

theorem form_zero (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) {r : Fin 5} {c : Fin 7} (hr : r ≠ 0)
    (hc : c ≠ 0) : form x (r, c) = 0 := by
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hr
  simp [form, hc]

-- Embeddings are pairs of an image and an ordering.

def emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Fin k ↪ Fin n :=
  ⟨fun a => R.1.orderEmbOfFin R.2 (τ a), (R.1.orderEmbOfFin R.2).injective.comp τ.injective⟩

theorem emb_apply {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k})
    (τ : Equiv.Perm (Fin k)) (a : Fin k) : emb R τ a = R.1.orderEmbOfFin R.2 (τ a) := rfl

theorem range_emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Set.range (emb R τ) = (R.1 : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact Finset.orderEmbOfFin_mem R.1 R.2 _
  · intro hx
    rw [← Finset.range_orderEmbOfFin R.1 R.2] at hx
    obtain ⟨b, rfl⟩ := hx
    exact ⟨τ⁻¹ b, by simp [emb_apply]⟩

theorem emb_bijective {n k : ℕ} :
    Function.Bijective
      (fun x : (Σ _ : {R : Finset (Fin n) // R.card = k}, Equiv.Perm (Fin k)) => emb x.1 x.2) := by
  constructor
  · rintro ⟨R, τ⟩ ⟨R', τ'⟩ h
    have h' : emb R τ = emb R' τ' := h
    have hRR : R = R' := by
      have := congrArg (fun g : Fin k ↪ Fin n => Set.range g) h'
      simp only [range_emb, Finset.coe_inj] at this
      exact Subtype.ext this
    subst hRR
    have hττ : τ = τ' := by
      ext a
      have := DFunLike.congr_fun h' a
      simp only [emb_apply] at this
      rw [(R.1.orderEmbOfFin R.2).injective this]
    subst hττ
    rfl
  · intro f
    have hc : (univ.map f).card = k := by simp
    have hm : ∀ a, f a ∈ univ.map f := fun a => by simp
    let g : Fin k → Fin k := fun a => ((univ.map f).orderIsoOfFin hc).symm ⟨f a, hm a⟩
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at hab
      exact hab
    refine ⟨⟨⟨univ.map f, hc⟩, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)⟩, ?_⟩
    ext a
    simp only [emb_apply, Equiv.ofBijective_apply, g]
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem sum_embedding {n k : ℕ} (G : (Fin k ↪ Fin n) → ℂ) :
    ∑ f, G f = ∑ R : {R : Finset (Fin n) // R.card = k}, ∑ τ : Equiv.Perm (Fin k),
      G (emb R τ) := by
  rw [← (emb_bijective (n := n) (k := k)).sum_comp G]
  exact Fintype.sum_sigma _

theorem sum_dite_card {n k : ℕ} (H : (R : Finset (Fin n)) → R.card = k → ℂ) :
    (∑ R : Finset (Fin n), if h : R.card = k then H R h else 0) =
      ∑ R : {R : Finset (Fin n) // R.card = k}, H R.1 R.2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun R : Finset (Fin n) => R.card = k)]
  have h2 : (∑ R : {R : Finset (Fin n) // ¬ R.card = k},
      (if h : R.1.card = k then H R.1 h else 0)) = 0 :=
    Finset.sum_eq_zero fun R _ => dif_neg R.2
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun R _ => dif_pos R.2

-- The sum of the k x k subpermanents, times k factorial, is a sum over pairs of embeddings.
theorem key {n m : ℕ} (t : Fin n × Fin m → ℂ) (k : ℕ) :
    (k.factorial : ℂ) * (∑ R : Finset (Fin n), ∑ C : Finset (Fin m),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) =
      ∑ g : Fin k ↪ Fin n, ∑ h : Fin k ↪ Fin m, ∏ j, t (g j, h j) := by
  have split : ∀ R : Finset (Fin n), (∑ C : Finset (Fin m),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) =
      if hR : R.card = k then ∑ C : {C : Finset (Fin m) // C.card = k},
        Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin hR a, C.1.orderEmbOfFin C.2 b)) else 0 := by
    intro R
    by_cases hR : R.card = k
    · rw [dif_pos hR, ← sum_dite_card (fun C hC => Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b)))]
      refine Finset.sum_congr rfl fun C _ => ?_
      by_cases hC : C.card = k
      · rw [dif_pos ⟨hR, hC⟩, dif_pos hC]
      · rw [dif_neg (fun h => hC h.2), dif_neg hC]
    · rw [dif_neg hR]
      exact Finset.sum_eq_zero fun C _ => dif_neg (fun h => hR h.1)
  rw [Finset.sum_congr rfl (fun R _ => split R)]
  rw [sum_dite_card (fun R hR => ∑ C : {C : Finset (Fin m) // C.card = k},
    Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin hR a, C.1.orderEmbOfFin C.2 b)))]
  simp only [Matrix.permanent, Matrix.of_apply]
  rw [Finset.sum_comm]
  have rows : ∀ C : {C : Finset (Fin m) // C.card = k},
      (∑ R : {R : Finset (Fin n) // R.card = k}, ∑ σ : Equiv.Perm (Fin k),
        ∏ j, t (R.1.orderEmbOfFin R.2 (σ j), C.1.orderEmbOfFin C.2 j)) =
      ∑ g : Fin k ↪ Fin n, ∏ j, t (g j, C.1.orderEmbOfFin C.2 j) :=
    fun C => (sum_embedding (fun g : Fin k ↪ Fin n => ∏ j, t (g j, C.1.orderEmbOfFin C.2 j))).symm
  rw [Finset.sum_congr rfl (fun C _ => rows C), Finset.mul_sum]
  have perm : ∀ (C : {C : Finset (Fin m) // C.card = k}) (σ : Equiv.Perm (Fin k)),
      (∑ g : Fin k ↪ Fin n, ∏ j, t (g j, C.1.orderEmbOfFin C.2 (σ j))) =
      ∑ g : Fin k ↪ Fin n, ∏ j, t (g j, C.1.orderEmbOfFin C.2 j) := by
    intro C σ
    refine Fintype.sum_equiv (Equiv.embeddingCongr σ (Equiv.refl _)) _ _ (fun g => ?_)
    refine Fintype.prod_equiv σ _ _ (fun j => ?_)
    simp [Equiv.embeddingCongr_apply]
  have fac : ∀ C : {C : Finset (Fin m) // C.card = k},
      (k.factorial : ℂ) * (∑ g : Fin k ↪ Fin n, ∏ j, t (g j, C.1.orderEmbOfFin C.2 j)) =
      ∑ σ : Equiv.Perm (Fin k), ∑ g : Fin k ↪ Fin n,
        ∏ j, t (g j, C.1.orderEmbOfFin C.2 (σ j)) := by
    intro C
    rw [Finset.sum_congr rfl (fun σ _ => perm C σ), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun C _ => fac C)]
  rw [Finset.sum_congr rfl (fun C _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun (g : Fin k ↪ Fin n) _ => ?_
  exact (sum_embedding (fun h : Fin k ↪ Fin m => ∏ j, t (g j, h j))).symm

-- Choosing an embedding of Fin (n + 1): the image of 0, then an embedding of the rest.

def insertPick {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    Fin (n + 1) ↪ Fin (m + 1) :=
  Fin.Embedding.cons (f.trans (finSuccAboveEquiv p).asEmbedding) (a := p) (by
    rintro ⟨i, hi⟩
    exact ((finSuccAboveEquiv p) (f i)).property hi)

theorem insertPick_zero {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    insertPick p f 0 = p := rfl

theorem insertPick_succ {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m)
    (i : Fin n) : insertPick p f i.succ = p.succAbove (f i) := rfl

noncomputable def pickEquiv (n m : ℕ) :
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

theorem sumPick {n m : ℕ} (g : (Fin (n + 1) ↪ Fin (m + 1)) → ℂ) :
    (∑ f, g f) = ∑ j : Fin (m + 1), ∑ f : Fin n ↪ Fin m, g (insertPick j f) := by
  rw [← (pickEquiv n m).sum_comp g, Fintype.sum_prod_type]
  rfl

theorem single {m : ℕ} (F : Fin m → ℂ) :
    (∑ g : Fin 1 ↪ Fin m, F (g 0)) = ∑ a, F a :=
  Fintype.sum_equiv Equiv.uniqueEmbeddingEquivResult _ _ (fun _ => rfl)

theorem pair {m : ℕ} (F : Fin (m + 1) → Fin (m + 1) → ℂ) :
    (∑ g : Fin 2 ↪ Fin (m + 1), F (g 0) (g 1)) = (∑ a, ∑ b, F a b) - ∑ a, F a a := by
  rw [sumPick, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ f : Fin 1 ↪ Fin m, insertPick j f 1 = j.succAbove (f 0) := fun f => rfl
  simp only [insertPick_zero, h1]
  refine (single (fun b => F j (j.succAbove b))).trans ?_
  rw [Fin.sum_univ_succAbove (F j) j]
  ring

-- The sums of pairs of embeddings, for the witness.

theorem big_zero (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) (k : ℕ) (hk : 3 ≤ k) :
    (∑ g : Fin k ↪ Fin 5, ∑ h : Fin k ↪ Fin 7, ∏ j, formMap x (g j, h j)) = 0 := by
  refine Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun h _ => ?_
  by_contra hne
  have h3 : ∀ j, g j = 0 ∨ h j = 0 := by
    intro j
    by_contra hj
    push_neg at hj
    exact hne (Finset.prod_eq_zero (Finset.mem_univ j)
      (by rw [formMap_apply]; exact form_zero x hj.1 hj.2))
  have d01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp
  have d02 : (⟨0, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ := by simp
  have d12 : (⟨1, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ := by simp
  rcases h3 ⟨0, by omega⟩ with a | a <;> rcases h3 ⟨1, by omega⟩ with b | b <;>
    rcases h3 ⟨2, by omega⟩ with c | c <;>
    first
    | exact d01 (g.injective (a.trans b.symm))
    | exact d02 (g.injective (a.trans c.symm))
    | exact d12 (g.injective (b.trans c.symm))
    | exact d01 (h.injective (a.trans b.symm))
    | exact d02 (h.injective (a.trans c.symm))
    | exact d12 (h.injective (b.trans c.symm))

theorem one_zero (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) :
    (∑ g : Fin 1 ↪ Fin 5, ∑ h : Fin 1 ↪ Fin 7, ∏ j, formMap x (g j, h j)) = 0 := by
  simp only [Fin.prod_univ_one]
  refine (single (fun a => ∑ h : Fin 1 ↪ Fin 7, formMap x (a, h 0))).trans ?_
  rw [Finset.sum_congr rfl (fun a _ => single (fun c => formMap x (a, c)))]
  simp [formMap_apply, Fin.sum_univ_succ, form]
  try ring

theorem two_zero (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) :
    (∑ g : Fin 2 ↪ Fin 5, ∑ h : Fin 2 ↪ Fin 7, ∏ j, formMap x (g j, h j)) = 0 := by
  have inner : ∀ g : Fin 2 ↪ Fin 5, (∑ h : Fin 2 ↪ Fin 7, ∏ j, formMap x (g j, h j)) =
      (∑ c, formMap x (g 0, c)) * (∑ d, formMap x (g 1, d)) -
        ∑ c, formMap x (g 0, c) * formMap x (g 1, c) := by
    intro g
    simp only [Fin.prod_univ_two]
    rw [Finset.sum_mul_sum]
    exact pair (fun c d => formMap x (g 0, c) * formMap x (g 1, d))
  rw [Finset.sum_congr rfl (fun g _ => inner g)]
  refine (pair (fun a b => (∑ c, formMap x (a, c)) * (∑ d, formMap x (b, d)) -
    ∑ c, formMap x (a, c) * formMap x (b, c))).trans ?_
  simp only [formMap_apply]
  simp [Fin.sum_univ_succ, form]
  ring

end PEqualNP.Outside.L_gct_207_aux

open PEqualNP.Outside.L_gct_207_aux

theorem PEqualNP.Outside.L_gct_207 : ∃ L : Submodule ℂ (Fin 5 × Fin 7 → ℂ),
    Module.finrank ℂ L = 9 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 5 →
      (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7),
        if h : R.card = k ∧ C.card = k then
          Matrix.permanent (Matrix.of fun a b =>
            t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) := by
  refine ⟨LinearMap.range formMap, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj formMap_injective, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
  · rintro t ⟨x, rfl⟩ k hk1 hk5
    have hT : (∑ g : Fin k ↪ Fin 5, ∑ h : Fin k ↪ Fin 7, ∏ j, formMap x (g j, h j)) = 0 := by
      rcases Nat.lt_or_ge k 3 with hk | hk
      · interval_cases k
        · exact one_zero x
        · exact two_zero x
      · exact big_zero x k hk
    have hk := key (formMap x) k
    rw [hT] at hk
    exact (mul_eq_zero.mp hk).resolve_left (by exact_mod_cast Nat.factorial_ne_zero k)
