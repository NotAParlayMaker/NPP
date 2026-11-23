import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_205_aux

open Finset

private theorem eval_permPoly (m : ℕ) (z : Fin m × Fin m → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ m) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]



open Finset

/-- The restriction of a permutation along an embedding. -/
def res {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) : Fin k ↪ Fin n :=
  ⟨fun a => σ (e a), σ.injective.comp e.injective⟩

@[simp] theorem res_apply {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) (a : Fin k) :
    res e σ a = σ (e a) := rfl

/-- The embedding with image `R`, in the order given by `τ`. -/
def emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Fin k ↪ Fin n :=
  ⟨fun a => R.1.orderEmbOfFin R.2 (τ a), (R.1.orderEmbOfFin R.2).injective.comp τ.injective⟩

@[simp] theorem emb_apply {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k})
    (τ : Equiv.Perm (Fin k)) (a : Fin k) : emb R τ a = R.1.orderEmbOfFin R.2 (τ a) := rfl

/-- The permutations extending a given injection `e a ↦ f a` number `(n - k)!`. -/
theorem card_extend {n k : ℕ} (e f : Fin k ↪ Fin n)
    [Fintype {σ : Equiv.Perm (Fin n) // res e σ = f}] :
    Fintype.card {σ : Equiv.Perm (Fin n) // res e σ = f} = (n - k).factorial := by
  classical
  let φ : Set.range e ≃ Set.range f :=
    (Equiv.ofInjective e e.injective).symm.trans (Equiv.ofInjective f f.injective)
  let σ0 : Equiv.Perm (Fin n) := φ.extendSubtype
  have hσ0 : ∀ a, σ0 (e a) = f a := by
    intro a
    have h1 := φ.extendSubtype_apply_of_mem (e a) (Set.mem_range_self a)
    have h2 : (Equiv.ofInjective e e.injective).symm ⟨e a, Set.mem_range_self a⟩ = a :=
      Equiv.ofInjective_symm_apply e.injective a
    simp only [σ0, h1, φ, Equiv.trans_apply, h2, Equiv.ofInjective_apply]
  have hres : ∀ σ : Equiv.Perm (Fin n), res e σ = f ↔ ∀ a, σ (e a) = f a := by
    intro σ
    constructor
    · intro h a
      have := DFunLike.congr_fun h a
      simpa using this
    · intro h
      ext a
      simp [h a]
  let E : {σ : Equiv.Perm (Fin n) // res e σ = f} ≃
      {τ : Equiv.Perm (Fin n) // ∀ x, ¬ (x ∉ Set.range e) → τ x = x} :=
    { toFun := fun σ => ⟨σ0⁻¹ * σ.1, by
        intro x hx
        rw [not_not] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [Equiv.Perm.mul_apply, (hres σ.1).1 σ.2 a, ← hσ0 a]
        simp⟩
      invFun := fun τ => ⟨σ0 * τ.1, by
        rw [hres]
        intro a
        rw [Equiv.Perm.mul_apply, τ.2 (e a) (by simp), hσ0]⟩
      left_inv := fun σ => Subtype.ext (by simp)
      right_inv := fun τ => Subtype.ext (by simp) }
  rw [Fintype.card_congr E, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm _),
    Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin,
    Fintype.card_fin]

/-- A sum over permutations of a function of the restriction along `e`. -/
theorem sum_perm_res {n k : ℕ} (e : Fin k ↪ Fin n) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), F (res e σ) = ((n - k).factorial : ℂ) * ∑ f, F f := by
  classical
  rw [← Fintype.sum_fiberwise' (fun σ : Equiv.Perm (Fin n) => res e σ) F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_const, Finset.card_univ, card_extend, nsmul_eq_mul]

theorem range_emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Set.range (emb R τ) = (R.1 : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact Finset.orderEmbOfFin_mem R.1 R.2 _
  · intro hx
    rw [← Finset.range_orderEmbOfFin R.1 R.2] at hx
    obtain ⟨b, rfl⟩ := hx
    exact ⟨τ⁻¹ b, by simp⟩

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

/-- Embeddings `Fin k ↪ Fin n` are pairs of an image and an ordering. -/
theorem sum_embedding {n k : ℕ} (G : (Fin k ↪ Fin n) → ℂ) :
    ∑ f, G f = ∑ R : {R : Finset (Fin n) // R.card = k}, ∑ τ : Equiv.Perm (Fin k),
      G (emb R τ) := by
  rw [← (emb_bijective (n := n) (k := k)).sum_comp G]
  exact Fintype.sum_sigma _

theorem prod_orderEmb {n k : ℕ} (C : Finset (Fin n)) (hC : C.card = k) (h : Fin n → ℂ) :
    ∏ j ∈ C, h j = ∏ a, h (C.orderEmbOfFin hC a) := by
  rw [← Finset.prod_coe_sort]
  exact (Fintype.prod_equiv (C.orderIsoOfFin hC).toEquiv _ _
    (fun a => by simp [Finset.coe_orderIsoOfFin_apply])).symm

/-- The contribution of a fixed set `C` of `k` columns. -/
theorem sum_perm_cols {n k : ℕ} (t : Fin n × Fin n → ℂ) (C : Finset (Fin n)) (hC : C.card = k) :
    ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j) =
      ((n - k).factorial : ℂ) * ∑ R : {R : Finset (Fin n) // R.card = k},
        Matrix.permanent (Matrix.of fun i j : Fin k =>
          t (R.1.orderEmbOfFin R.2 i, C.orderEmbOfFin hC j)) := by
  calc ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j)
      = ∑ σ : Equiv.Perm (Fin n), (fun g : Fin k ↪ Fin n => ∏ a, t (g a, C.orderEmbOfFin hC a))
          (res (C.orderEmbOfFin hC).toEmbedding σ) :=
        Finset.sum_congr rfl fun σ _ => prod_orderEmb C hC _
    _ = ((n - k).factorial : ℂ) * ∑ g : Fin k ↪ Fin n, ∏ a, t (g a, C.orderEmbOfFin hC a) :=
        sum_perm_res (C.orderEmbOfFin hC).toEmbedding
          (fun g : Fin k ↪ Fin n => ∏ a, t (g a, C.orderEmbOfFin hC a))
    _ = _ := by rw [sum_embedding]; rfl

/-- The expansion of `perm (J + t)` over the sets of columns. -/
theorem eval_one_add (n : ℕ) (t : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      ∑ C : Finset (Fin n), ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j) := by
  rw [eval_permPoly, Matrix.permanent]
  simp only [Matrix.of_apply]
  simp_rw [Finset.prod_one_add, Finset.powerset_univ]
  rw [Finset.sum_comm]

/-- Grouping a sum over subsets by cardinality. -/
theorem sum_by_card {n : ℕ} (G : Finset (Fin n) → ℂ) :
    ∑ C : Finset (Fin n), G C =
      ∑ k ∈ range (n + 1), ∑ C : {C : Finset (Fin n) // C.card = k}, G C.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1))
    (fun C _ => by
      have := Finset.card_le_univ C
      rw [Fintype.card_fin] at this
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le this))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_subtype _ (by simp) G

/-- The sum of all `k × k` subpermanents of `t`. -/
noncomputable def Mk (n k : ℕ) (t : Fin n × Fin n → ℂ) : ℂ :=
  ∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k},
    Matrix.permanent (Matrix.of fun i j : Fin k =>
      t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j))

/-- The Minc expansion in terms of `Mk`. -/
theorem minc_Mk (n : ℕ) (t : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      ∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) * Mk n k t := by
  rw [eval_one_add, sum_by_card]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [fun C : {C : Finset (Fin n) // C.card = k} => sum_perm_cols t C.1 C.2]
  rw [← Finset.mul_sum, Mk, Finset.sum_comm]

private lemma sum_dite_eq_subtype {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (f : (x : α) → p x → ℂ) :
    (∑ x : α, if h : p x then f x h else 0) = ∑ x : {x // p x}, f x.1 x.2 := by
  let g : α → ℂ := fun x => if h : p x then f x h else 0
  have h1 : (∑ x : {x // p x}, f x.1 x.2) = ∑ x : {x // p x}, g x.1 := by
    apply Finset.sum_congr rfl
    intro x _
    dsimp [g]
    rw [dif_pos x.2]
  rw [h1]
  rw [← Finset.sum_subtype (s := (Finset.univ : Finset α).filter p) (by simp) g]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  dsimp [g]
  split_ifs <;> rfl

private lemma if_sum_eq_Mk (n k : ℕ) (t : Fin n × Fin n → ℂ) :
    (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = Mk n k t := by
  rw [Mk]
  conv_lhs =>
    rw [← Fintype.sum_prod_type (f := fun x : Finset (Fin n) × Finset (Fin n) =>
      if h : x.1.card = k ∧ x.2.card = k then
        Matrix.permanent (Matrix.of fun a b =>
          t (x.1.orderEmbOfFin h.1 a, x.2.orderEmbOfFin h.2 b))
      else 0)]
  rw [sum_dite_eq_subtype
    (p := fun x : Finset (Fin n) × Finset (Fin n) => x.1.card = k ∧ x.2.card = k)
    (f := fun x h => Matrix.permanent (Matrix.of fun a b =>
      t (x.1.orderEmbOfFin h.1 a, x.2.orderEmbOfFin h.2 b)))]
  rw [Fintype.sum_equiv (Equiv.subtypeProdEquivProd)
    (fun x : {x : Finset (Fin n) × Finset (Fin n) // x.1.card = k ∧ x.2.card = k} =>
      Matrix.permanent (Matrix.of fun a b =>
        t (x.1.1.orderEmbOfFin x.2.1 a, x.1.2.orderEmbOfFin x.2.2 b)))
    (fun y : {R : Finset (Fin n) // R.card = k} × {C : Finset (Fin n) // C.card = k} =>
      Matrix.permanent (Matrix.of fun a b =>
        t (y.1.1.orderEmbOfFin y.1.2 a, y.2.1.orderEmbOfFin y.2.2 b)))
    (fun x => rfl)]
  rw [Fintype.sum_prod_type]

theorem Mk_zero (n : ℕ) (t : Fin n × Fin n → ℂ) : Mk n 0 t = 1 := by
  have hu : ∀ S : {S : Finset (Fin n) // S.card = 0}, S = ⟨∅, Finset.card_empty⟩ :=
    fun S => Subtype.ext (Finset.card_eq_zero.mp S.2)
  rw [Mk, Fintype.sum_eq_single ⟨∅, Finset.card_empty⟩ (fun S hS => absurd (hu S) hS),
    Fintype.sum_eq_single ⟨∅, Finset.card_empty⟩ (fun S hS => absurd (hu S) hS),
    Matrix.permanent_isEmpty]

theorem single_bijective (n : ℕ) :
    Function.Bijective
      (fun i : Fin n => (⟨{i}, Finset.card_singleton i⟩ : {S : Finset (Fin n) // S.card = 1})) := by
  constructor
  · intro i j h
    simpa using congrArg Subtype.val h
  · rintro ⟨S, hS⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
    exact ⟨a, rfl⟩

theorem Mk_one (n : ℕ) (t : Fin n × Fin n → ℂ) : Mk n 1 t = ∑ p, t p := by
  rw [Mk, Fintype.sum_prod_type]
  symm
  refine Fintype.sum_bijective _ (single_bijective n) _ _ (fun i => ?_)
  refine Fintype.sum_bijective _ (single_bijective n) _ _ (fun j => ?_)
  rw [Matrix.permanent_unique]
  simp [Finset.orderEmbOfFin_singleton]

/-- The Minc expansion: `perm (J + t) = ∑_k (n - k)! * (sum of the k × k subpermanents)`. -/
theorem minc_expansion :
    ∀ (n : ℕ) (t : Fin n × Fin n → ℂ),
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
        ∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) *
          ∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k},
            Matrix.permanent (Matrix.of fun i j : Fin k =>
              t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j)) :=
  fun n t => minc_Mk n t


end PEqualNP.Outside.L_gct_205_aux

open PEqualNP.Outside.L_gct_205_aux

theorem PEqualNP.Outside.L_gct_205 :
    ∀ n : ℕ, ∀ L Z : Submodule ℂ (Fin n × Fin n → ℂ),
      (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n →
        (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
          if h : R.card = k ∧ C.card = k then
            Matrix.permanent (Matrix.of fun a b =>
              t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
          else 0) = 0) →
      (∀ z ∈ Z, Matrix.permanent (Matrix.of fun a b => z (a, b)) = 0) →
      (fun _ => (1 : ℂ)) ∉ L ⊔ Z := by
  intro n L Z hL hZ hJ
  rw [Submodule.mem_sup] at hJ
  obtain ⟨t, htL, z, hzZ, htz⟩ := hJ
  have hz_eq : z = fun p => (1 : ℂ) + (-t) p := by
    funext p
    have hp := congrFun htz p
    simp only [Pi.add_apply] at hp
    calc z p = (t p + z p) - t p := by ring
      _ = 1 - t p := by rw [hp]
      _ = (1 : ℂ) + (-t) p := by simp only [Pi.neg_apply]; ring
  have hperz : Matrix.permanent (Matrix.of fun a b => z (a, b)) = 0 := hZ z hzZ
  have hneg : (-t) ∈ L := L.neg_mem htL
  have hMk0 : ∀ k : ℕ, 1 ≤ k → k ≤ n → Mk n k (-t) = 0 := by
    intro k hk1 hkn
    rw [← if_sum_eq_Mk]
    exact hL (-t) hneg k hk1 hkn
  have hsum : (∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) * Mk n k (-t)) =
      (n.factorial : ℂ) := by
    rw [Finset.sum_eq_single 0]
    · rw [Mk_zero]
      simp
    · intro k hk hk0
      have hk1 : 1 ≤ k := by
        have := Finset.mem_range.mp hk
        omega
      have hkn : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      rw [hMk0 k hk1 hkn, mul_zero]
    · intro h0
      exfalso
      exact h0 (Finset.mem_range.mpr (Nat.succ_pos n))
  have hperm : Matrix.permanent (Matrix.of fun a b => (1 : ℂ) + (-t) (a, b)) =
      (n.factorial : ℂ) := by
    rw [← eval_permPoly n (fun p => (1 : ℂ) + (-t) p)]
    rw [minc_Mk]
    exact hsum
  have hzperm : Matrix.permanent (Matrix.of fun a b => z (a, b)) =
      Matrix.permanent (Matrix.of fun a b => (1 : ℂ) + (-t) (a, b)) := by
    rw [hz_eq]
  rw [hzperm, hperm] at hperz
  exact (by exact_mod_cast Nat.factorial_ne_zero n : (n.factorial : ℂ) ≠ 0) hperz
