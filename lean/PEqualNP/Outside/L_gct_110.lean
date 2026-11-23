import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct110

open Finset

theorem eval_permPoly {m : ℕ} (z : Fin m × Fin m → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ m) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

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

end PEqualNP.Outside.Gct110

namespace PEqualNP.Outside.Gct110

open Finset

variable {a : ℕ}

/-- Distinct edges have distinct rows and distinct columns. -/
def IsMatch (M : Finset (Fin a × Fin a)) : Prop :=
  (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

noncomputable instance (M : Finset (Fin a × Fin a)) : Decidable (IsMatch M) :=
  Classical.dec _

/-- The matchings of size `s` with rows in `rows` and columns in `cols`. -/
noncomputable def matchings (rows : Finset (Fin a)) (cols : Finset (Fin a)) (s : ℕ) :
    Finset (Finset (Fin a × Fin a)) :=
  ((rows ×ˢ cols).powersetCard s).filter IsMatch

/-- The matching sum of size `s` inside `rows × cols` with edge weights `W`. -/
noncomputable def mpOn {R : Type*} [CommRing R] (rows : Finset (Fin a)) (cols : Finset (Fin a)) (s : ℕ)
    (W : Fin a × Fin a → R) : R :=
  ∑ M ∈ matchings rows cols s, ∏ e ∈ M, W e

theorem mem_matchings {rows : Finset (Fin a)} {cols : Finset (Fin a)} {s : ℕ}
    {M : Finset (Fin a × Fin a)} :
    M ∈ matchings rows cols s ↔ (M ⊆ rows ×ˢ cols ∧ M.card = s) ∧ IsMatch M := by
  simp [matchings, mem_powersetCard]


end PEqualNP.Outside.Gct110

namespace PEqualNP.Outside.Gct110

open Finset

variable {a : ℕ}

/-- The edge set of the matching given by a row set, a column set and a permutation. -/
noncomputable def edge {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin a) // T.card = s} ×
      Equiv.Perm (Fin s)) : Finset (Fin a × Fin a) :=
  univ.image fun k : Fin s => (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k)

theorem edge_fun_injective {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin a) // T.card = s} ×
      Equiv.Perm (Fin s)) :
    Function.Injective fun k : Fin s =>
      (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k) := by
  intro k k' h
  exact (x.2.1.1.orderEmbOfFin x.2.1.2).injective (congrArg Prod.snd h)

theorem edge_image_snd {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin a) // T.card = s} ×
      Equiv.Perm (Fin s)) : (edge x).image Prod.snd = x.2.1.1 := by
  unfold edge
  rw [Finset.image_image]
  exact Finset.image_orderEmbOfFin_univ x.2.1.1 x.2.1.2

theorem edge_image_fst {s : ℕ}
    (x : {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin a) // T.card = s} ×
      Equiv.Perm (Fin s)) : (edge x).image Prod.fst = x.1.1 := by
  unfold edge
  rw [Finset.image_image]
  have : (Prod.fst ∘ fun k : Fin s =>
      (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k), x.2.1.1.orderEmbOfFin x.2.1.2 k))
      = (x.1.1.orderEmbOfFin x.1.2) ∘ x.2.2 := rfl
  rw [this, ← Finset.image_image, Finset.image_univ_equiv]
  exact Finset.image_orderEmbOfFin_univ x.1.1 x.1.2

theorem sumSubperm_eq_mpOn (s : ℕ) (Z : Matrix (Fin a) (Fin a) ℂ) :
    Mk a s (fun e => Z e.1 e.2) = mpOn univ univ s (fun e => Z e.1 e.2) := by
  have h1 : Mk a s (fun e => Z e.1 e.2) = ∑ x : ({S : Finset (Fin a) // S.card = s} ×
      {T : Finset (Fin a) // T.card = s} × Equiv.Perm (Fin s)),
      ∏ k, Z (x.1.1.orderEmbOfFin x.1.2 (x.2.2 k)) (x.2.1.1.orderEmbOfFin x.2.1.2 k) := by
    simp only [Mk, Matrix.permanent, Fintype.sum_prod_type, Matrix.of_apply]
  rw [h1]
  unfold mpOn
  refine Finset.sum_bij (fun x _ => edge x) ?_ ?_ ?_ ?_
  · intro x _
    rw [mem_matchings]
    refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
    · unfold edge
      rw [Finset.card_image_of_injective _ (edge_fun_injective x)]
      simp
    · intro e he e' he' h
      unfold edge at he he'
      obtain ⟨k, _, rfl⟩ := mem_image.mp he
      obtain ⟨k', _, rfl⟩ := mem_image.mp he'
      have : k = k' :=
        x.2.2.injective ((x.1.1.orderEmbOfFin x.1.2).injective h)
      rw [this]
    · intro e he e' he' h
      unfold edge at he he'
      obtain ⟨k, _, rfl⟩ := mem_image.mp he
      obtain ⟨k', _, rfl⟩ := mem_image.mp he'
      have : k = k' := (x.2.1.1.orderEmbOfFin x.2.1.2).injective h
      rw [this]
  · intro x _ x' _ h
    have hS : x.1.1 = x'.1.1 := by rw [← edge_image_fst x, ← edge_image_fst x', h]
    have hT : x.2.1.1 = x'.2.1.1 := by rw [← edge_image_snd x, ← edge_image_snd x', h]
    obtain ⟨⟨S, hS1⟩, ⟨T, hT1⟩, σ⟩ := x
    obtain ⟨⟨S', hS1'⟩, ⟨T', hT1'⟩, σ'⟩ := x'
    simp only at hS hT
    subst hS
    subst hT
    have hσ : σ = σ' := by
      ext k
      have hk : (S.orderEmbOfFin hS1 (σ k), T.orderEmbOfFin hT1 k) ∈
          edge (⟨⟨S, hS1'⟩, ⟨T, hT1'⟩, σ'⟩ :
            {S : Finset (Fin a) // S.card = s} × {T : Finset (Fin a) // T.card = s} ×
              Equiv.Perm (Fin s)) := by
        rw [← h]
        exact mem_image.mpr ⟨k, mem_univ _, rfl⟩
      obtain ⟨k', _, hk'⟩ := mem_image.mp hk
      simp only [Prod.mk.injEq] at hk'
      have hkk : k' = k := (T.orderEmbOfFin hT1).injective hk'.2
      rw [hkk] at hk'
      have := (S.orderEmbOfFin hS1).injective hk'.1
      rw [this]
    rw [hσ]
  · intro M hM
    rw [mem_matchings] at hM
    obtain ⟨⟨_, hcard⟩, hm1, hm2⟩ := hM
    have hS : (M.image Prod.fst).card = s := by
      rw [Finset.card_image_of_injOn, hcard]
      intro e he e' he' h
      exact hm1 e he e' he' h
    have hT : (M.image Prod.snd).card = s := by
      rw [Finset.card_image_of_injOn, hcard]
      intro e he e' he' h
      exact hm2 e he e' he' h
    have hex : ∀ k : Fin s, ∃ e ∈ M, e.2 = (M.image Prod.snd).orderEmbOfFin hT k := by
      intro k
      have := Finset.orderEmbOfFin_mem (M.image Prod.snd) hT k
      obtain ⟨e, he, he2⟩ := mem_image.mp this
      exact ⟨e, he, he2⟩
    choose g hgM hg2 using hex
    have hginj : Function.Injective g := by
      intro k k' h
      have : (M.image Prod.snd).orderEmbOfFin hT k = (M.image Prod.snd).orderEmbOfFin hT k' := by
        rw [← hg2 k, ← hg2 k', h]
      exact ((M.image Prod.snd).orderEmbOfFin hT).injective this
    let φ : Fin s → Fin s := fun k =>
      ((M.image Prod.fst).orderIsoOfFin hS).symm ⟨(g k).1, mem_image_of_mem _ (hgM k)⟩
    have hφ : ∀ k, (M.image Prod.fst).orderEmbOfFin hS (φ k) = (g k).1 := by
      intro k
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp [φ]
    have hφinj : Function.Injective φ := by
      intro k k' h
      have h1 : (g k).1 = (g k').1 := by rw [← hφ k, ← hφ k', h]
      exact hginj (hm1 _ (hgM k) _ (hgM k') h1)
    refine ⟨⟨⟨M.image Prod.fst, hS⟩, ⟨M.image Prod.snd, hT⟩,
      Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hφinj)⟩, mem_univ _, ?_⟩
    have himg : (univ.image g) = M := by
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        obtain ⟨k, _, rfl⟩ := mem_image.mp he
        exact hgM k
      · rw [Finset.card_image_of_injective _ hginj, hcard]
        simp
    refine Eq.trans ?_ himg
    unfold edge
    refine Finset.image_congr fun k _ => ?_
    simp only [Equiv.ofBijective_apply]
    rw [hφ k, ← hg2 k]
  · intro x _
    unfold edge
    rw [Finset.prod_image]
    intro k _ k' _ h
    exact edge_fun_injective x h

end PEqualNP.Outside.Gct110

namespace PEqualNP.Outside.Gct110
open Finset Polynomial

noncomputable def rookOn {n : ℕ} (S : Finset (Fin n × Fin n))
    (t : Fin n × Fin n → ℂ) : ℂ[X] :=
  ∑ M ∈ S.powerset, if IsMatch M then C (∏ e ∈ M, t e) * X ^ M.card else 0

theorem rookOn_coeff {n : ℕ} (S : Finset (Fin n × Fin n))
    (t : Fin n × Fin n → ℂ) (k : ℕ) :
    (rookOn S t).coeff k =
      ∑ M ∈ (S.powersetCard k).filter IsMatch, ∏ e ∈ M, t e := by
  classical
  simp only [rookOn, Polynomial.finsetSum_coeff, powersetCard_eq_filter, sum_filter]
  apply sum_congr rfl
  intro M hM
  by_cases hm : IsMatch M
  · simp only [hm, ite_true, coeff_C_mul_X_pow]
    by_cases hk : M.card = k
    · subst k
      simp
    · rw [ite_eq_right hk, ite_eq_right (Ne.symm hk)]
  · simp only [hm, ite_false, coeff_zero]
    split_ifs <;> rfl

theorem rookOn_univ_coeff {n : ℕ} (t : Fin n × Fin n → ℂ) (k : ℕ) :
    (rookOn univ t).coeff k = Mk n k t := by
  rw [rookOn_coeff]
  have h := sumSubperm_eq_mpOn k (Matrix.of fun i j => t (i,j))
  simpa only [mpOn, matchings, univ_product_univ, Matrix.of_apply] using h.symm

theorem match_card_le {n : ℕ} {M : Finset (Fin n × Fin n)} (hm : IsMatch M) :
    M.card ≤ n := by
  have h := card_le_univ (M.image Prod.fst)
  rw [card_image_of_injOn (fun e he e' he' h => hm.1 e he e' he' h),
    Fintype.card_fin] at h
  exact h

theorem rookOn_restrict {n : ℕ} (S : Finset (Fin n × Fin n))
    (t : Fin n × Fin n → ℂ) (ht : ∀ e, t e ≠ 0 → e ∈ S) :
    rookOn univ t = rookOn S t := by
  classical
  unfold rookOn
  symm
  apply sum_subset (powerset_mono.mpr (subset_univ S))
  intro M hM hnot
  have hn : ¬ M ⊆ S := by simpa only [mem_powerset] using hnot
  obtain ⟨e, he, hne⟩ := not_subset.mp hn
  have hz : t e = 0 := by by_contra h; exact hne (ht e h)
  have hp : ∏ e ∈ M, t e = 0 := prod_eq_zero he hz
  simp [hp]

theorem rookOn_congr {n : ℕ} (S : Finset (Fin n × Fin n))
    (t u : Fin n × Fin n → ℂ) (h : ∀ e ∈ S, t e = u e) :
    rookOn S t = rookOn S u := by
  classical
  unfold rookOn
  apply sum_congr rfl
  intro M hM
  have hp : ∏ e ∈ M, t e = ∏ e ∈ M, u e :=
    prod_congr rfl fun e he => h e ((mem_powerset.mp hM) he)
  rw [hp]

end PEqualNP.Outside.Gct110

namespace PEqualNP.Outside.Gct110
open Finset Polynomial

theorem sum_powerset_union' {α R : Type*} [DecidableEq α] [AddCommMonoid R]
    (S T : Finset α) (hd : Disjoint S T) (f : Finset α → R) :
    ∑ M ∈ (S ∪ T).powerset, f M =
      ∑ P ∈ S.powerset, ∑ Q ∈ T.powerset, f (P ∪ Q) := by
  have recS : ∀ P ⊆ S, ∀ Q ⊆ T, (P ∪ Q) ∩ S = P := by
    intro P hp Q hq
    rw [union_inter_distrib_right, inter_eq_left.mpr hp,
      disjoint_iff_inter_eq_empty.mp (hd.symm.mono hq (Subset.refl S)), union_empty]
  have recT : ∀ P ⊆ S, ∀ Q ⊆ T, (P ∪ Q) ∩ T = Q := by
    intro P hp Q hq
    rw [union_inter_distrib_right, inter_eq_left.mpr hq,
      disjoint_iff_inter_eq_empty.mp (hd.mono hp (Subset.refl T)), empty_union]
  rw [← sum_product S.powerset T.powerset (fun p => f (p.1 ∪ p.2))]
  symm
  refine sum_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro p hp
    obtain ⟨hp, hq⟩ := mem_product.mp hp
    exact mem_powerset.mpr (union_subset_union (mem_powerset.mp hp) (mem_powerset.mp hq))
  · intro p hp q hq heq
    obtain ⟨hp1, hp2⟩ := mem_product.mp hp
    obtain ⟨hq1, hq2⟩ := mem_product.mp hq
    apply Prod.ext
    · rw [← recS p.1 (mem_powerset.mp hp1) p.2 (mem_powerset.mp hp2), heq,
        recS q.1 (mem_powerset.mp hq1) q.2 (mem_powerset.mp hq2)]
    · rw [← recT p.1 (mem_powerset.mp hp1) p.2 (mem_powerset.mp hp2), heq,
        recT q.1 (mem_powerset.mp hq1) q.2 (mem_powerset.mp hq2)]
  · intro M hM
    refine ⟨(M ∩ S, M ∩ T), mem_product.mpr
      ⟨mem_powerset.mpr inter_subset_right, mem_powerset.mpr inter_subset_right⟩, ?_⟩
    rw [← inter_union_distrib_left, inter_eq_left.mpr (mem_powerset.mp hM)]

theorem match_union {n : ℕ} (S T : Finset (Fin n × Fin n))
    (hcross : ∀ e ∈ S, ∀ f ∈ T, e.1 ≠ f.1 ∧ e.2 ≠ f.2)
    (P Q : Finset (Fin n × Fin n)) (hp : P ⊆ S) (hq : Q ⊆ T) :
    IsMatch (P ∪ Q) ↔ IsMatch P ∧ IsMatch Q := by
  constructor
  · intro h
    constructor
    · exact ⟨fun e he f hf h1 => h.1 e (mem_union_left _ he) f (mem_union_left _ hf) h1,
        fun e he f hf h1 => h.2 e (mem_union_left _ he) f (mem_union_left _ hf) h1⟩
    · exact ⟨fun e he f hf h1 => h.1 e (mem_union_right _ he) f (mem_union_right _ hf) h1,
        fun e he f hf h1 => h.2 e (mem_union_right _ he) f (mem_union_right _ hf) h1⟩
  · rintro ⟨hP, hQ⟩
    constructor
    · intro e he f hf h1
      rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
      · exact hP.1 e he f hf h1
      · exact False.elim ((hcross e (hp he) f (hq hf)).1 h1)
      · exact False.elim ((hcross f (hp hf) e (hq he)).1 h1.symm)
      · exact hQ.1 e he f hf h1
    · intro e he f hf h1
      rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
      · exact hP.2 e he f hf h1
      · exact False.elim ((hcross e (hp he) f (hq hf)).2 h1)
      · exact False.elim ((hcross f (hp hf) e (hq he)).2 h1.symm)
      · exact hQ.2 e he f hf h1

theorem rookOn_union {n : ℕ} (S T : Finset (Fin n × Fin n))
    (hd : Disjoint S T)
    (hcross : ∀ e ∈ S, ∀ f ∈ T, e.1 ≠ f.1 ∧ e.2 ≠ f.2)
    (t : Fin n × Fin n → ℂ) :
    rookOn (S ∪ T) t = rookOn S t * rookOn T t := by
  classical
  unfold rookOn
  rw [sum_powerset_union' S T hd, sum_mul_sum]
  apply sum_congr rfl
  intro P hP
  apply sum_congr rfl
  intro Q hQ
  have hp := mem_powerset.mp hP
  have hq := mem_powerset.mp hQ
  have hdPQ := hd.mono hp hq
  simp only [match_union S T hcross P Q hp hq]
  by_cases hmP : IsMatch P <;> by_cases hmQ : IsMatch Q
  · simp only [hmP, hmQ, and_self, ite_true]
    rw [prod_union hdPQ, card_union_of_disjoint hdPQ, map_mul, pow_add]
    ring
  · simp [hmP, hmQ]
  · simp [hmP, hmQ]
  · simp [hmP, hmQ]

end PEqualNP.Outside.Gct110

namespace PEqualNP.Outside.Gct110
open Finset Polynomial

theorem Mk_scale (n k : ℕ) (t : Fin n × Fin n → ℂ) (c : ℂ) :
    Mk n k (fun e => c * t e) = c ^ k * Mk n k t := by
  classical
  simp only [Mk, Matrix.permanent, Matrix.of_apply, prod_mul_distrib,
    prod_const, card_univ, Fintype.card_fin]
  simp only [← mul_sum]

theorem Mk_eq_zero_of_line {n : ℕ} (t : Fin n × Fin n → ℂ)
    (h : ∀ c : ℂ, MvPolynomial.eval (fun p => 1 + c * t p)
      (PEqualNP.Gct.permPoly ℂ n) = (n.factorial : ℂ))
    (k : ℕ) (hk0 : k ≠ 0) (hkn : k ≤ n) : Mk n k t = 0 := by
  classical
  let P : ℂ[X] := ∑ j ∈ range (n + 1), C (((n-j).factorial : ℂ) * Mk n j t) * X ^ j
  have heval (c : ℂ) : P.eval c = (n.factorial : ℂ) := by
    rw [← h c, minc_Mk]
    simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Mk_scale]
    apply sum_congr rfl
    intro j hj
    ring
  have hp : P = C (n.factorial : ℂ) := by
    apply Polynomial.funext
    intro c
    simpa only [eval_C] using heval c
  have hc := congrArg (fun p : ℂ[X] => p.coeff k) hp
  have hk : k ∈ range (n + 1) := mem_range.mpr (by omega)
  have hz : ((n-k).factorial : ℂ) * Mk n k t = 0 := by
    simpa only [P, finsetSum_coeff, coeff_C_mul_X_pow, sum_ite_eq, hk, ite_true,
      coeff_C, hk0, ite_false] using hc
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast (Nat.factorial_ne_zero (n-k)))

theorem rook_eq_one_of_line {n : ℕ} (t : Fin n × Fin n → ℂ)
    (h : ∀ c : ℂ, MvPolynomial.eval (fun p => 1 + c * t p)
      (PEqualNP.Gct.permPoly ℂ n) = (n.factorial : ℂ)) :
    rookOn univ t = 1 := by
  classical
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro k
  by_cases hk0 : k = 0
  · subst k
    rw [rookOn_univ_coeff, Mk_zero]
    simp
  · have hz : (rookOn univ t).coeff k = 0 := by
      by_cases hkn : k ≤ n
      · rw [rookOn_univ_coeff]
        exact Mk_eq_zero_of_line t h k hk0 hkn
      · rw [rookOn_coeff]
        apply sum_eq_zero
        intro M hM
        obtain ⟨hM, hm⟩ := mem_filter.mp hM
        have hcard := (mem_powersetCard.mp hM).2
        have hle := match_card_le hm
        omega
    simpa only [Polynomial.coeff_one, hk0, ite_false] using hz

theorem eval_of_rook_eq_one {n : ℕ} (t : Fin n × Fin n → ℂ)
    (h : rookOn univ t = 1) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      (n.factorial : ℂ) := by
  classical
  have hMk (k : ℕ) : Mk n k t = if k = 0 then 1 else 0 := by
    rw [← rookOn_univ_coeff, h]
    simp [coeff_one]
  rw [minc_Mk]
  simp [hMk, mul_ite]

end PEqualNP.Outside.Gct110

theorem PEqualNP.Outside.L_gct_110 : ∀ (n : ℕ) (A B : Finset (Fin n)) (L1 L2 : Submodule ℂ (Fin n × Fin n → ℂ)), (∀ t ∈ L1, ∀ p, t p ≠ 0 → p.1 ∈ A ∧ p.2 ∈ B) → (∀ t ∈ L2, ∀ p, t p ≠ 0 → p.1 ∉ A ∧ p.2 ∉ B) → (∀ t ∈ L1, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → (∀ t ∈ L2, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → ∀ t ∈ L1 ⊔ L2, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ) := by
  classical
  intro n A B L1 L2 hs1 hs2 h1 h2 t ht
  rcases Submodule.mem_sup.mp ht with ⟨u, hu, v, hv, rfl⟩
  let S : Finset (Fin n × Fin n) := A ×ˢ B
  let T : Finset (Fin n × Fin n) := Aᶜ ×ˢ Bᶜ
  have huS : ∀ e, u e ≠ 0 → e ∈ S := by
    intro e he
    exact Finset.mem_product.mpr (hs1 u hu e he)
  have hvT : ∀ e, v e ≠ 0 → e ∈ T := by
    intro e he
    have hh := hs2 v hv e he
    exact Finset.mem_product.mpr ⟨Finset.mem_compl.mpr hh.1, Finset.mem_compl.mpr hh.2⟩
  have hcross : ∀ e ∈ S, ∀ f ∈ T, e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
    intro e he f hf
    obtain ⟨he1, he2⟩ := Finset.mem_product.mp he
    obtain ⟨hf1, hf2⟩ := Finset.mem_product.mp hf
    constructor
    · intro hef
      exact (Finset.mem_compl.mp hf1) (hef ▸ he1)
    · intro hef
      exact (Finset.mem_compl.mp hf2) (hef ▸ he2)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (hcross e he e hf).1 rfl
  have hsupport : ∀ e, (u + v) e ≠ 0 → e ∈ S ∪ T := by
    intro e he
    by_cases hue : u e = 0
    · apply Finset.mem_union_right
      exact hvT e (by simpa only [Pi.add_apply, hue, zero_add] using he)
    · exact Finset.mem_union_left _ (huS e hue)
  have hS : ∀ e ∈ S, (u + v) e = u e := by
    intro e he
    have hz : v e = 0 := by
      by_contra hn
      exact (Finset.disjoint_left.mp hd) he (hvT e hn)
    simp only [Pi.add_apply, hz, add_zero]
  have hT : ∀ e ∈ T, (u + v) e = v e := by
    intro e he
    have hz : u e = 0 := by
      by_contra hn
      exact (Finset.disjoint_left.mp hd) (huS e hn) he
    simp only [Pi.add_apply, hz, zero_add]
  have hRu : PEqualNP.Outside.Gct110.rookOn Finset.univ u = 1 := by
    apply PEqualNP.Outside.Gct110.rook_eq_one_of_line
    intro c
    simpa only [Pi.smul_apply, smul_eq_mul] using h1 (c • u) (L1.smul_mem c hu)
  have hRv : PEqualNP.Outside.Gct110.rookOn Finset.univ v = 1 := by
    apply PEqualNP.Outside.Gct110.rook_eq_one_of_line
    intro c
    simpa only [Pi.smul_apply, smul_eq_mul] using h2 (c • v) (L2.smul_mem c hv)
  apply PEqualNP.Outside.Gct110.eval_of_rook_eq_one
  rw [PEqualNP.Outside.Gct110.rookOn_restrict (S ∪ T) (u+v) hsupport,
    PEqualNP.Outside.Gct110.rookOn_union S T hd hcross,
    PEqualNP.Outside.Gct110.rookOn_congr S (u+v) u hS,
    PEqualNP.Outside.Gct110.rookOn_congr T (u+v) v hT,
    ← PEqualNP.Outside.Gct110.rookOn_restrict S u huS,
    ← PEqualNP.Outside.Gct110.rookOn_restrict T v hvT, hRu, hRv, one_mul]
