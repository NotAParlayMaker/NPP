import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_205

open Finset

theorem eval_permPoly {n : ℕ} (z : Fin n × Fin n → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ n) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]



def res {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) : Fin k ↪ Fin n :=
  ⟨fun a => σ (e a), σ.injective.comp e.injective⟩

@[local simp] theorem res_apply {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) (a : Fin k) :
    res e σ a = σ (e a) := rfl


def emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Fin k ↪ Fin n :=
  ⟨fun a => R.1.orderEmbOfFin R.2 (τ a), (R.1.orderEmbOfFin R.2).injective.comp τ.injective⟩

@[local simp] theorem emb_apply {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k})
    (τ : Equiv.Perm (Fin k)) (a : Fin k) : emb R τ a = R.1.orderEmbOfFin R.2 (τ a) := rfl


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


theorem eval_one_add (n : ℕ) (t : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      ∑ C : Finset (Fin n), ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j) := by
  rw [eval_permPoly, Matrix.permanent]
  simp only [Matrix.of_apply]
  simp_rw [Finset.prod_one_add, Finset.powerset_univ]
  rw [Finset.sum_comm]


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


noncomputable def Mk (n k : ℕ) (t : Fin n × Fin n → ℂ) : ℂ :=
  ∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k},
    Matrix.permanent (Matrix.of fun i j : Fin k =>
      t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j))


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


theorem sum_dite_subtype {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : ∀ a, p a → ℂ) :
    (∑ a, if h : p a then f a h else 0) = ∑ a : {a // p a}, f a a.property := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun a => if h : p a then f a h else 0)]
  have hyes : (∑ a : {a // p a}, if h : p a.val then f a.val h else 0) =
      ∑ a : {a // p a}, f a a.property := by
    apply Finset.sum_congr rfl
    intro a _
    exact dif_pos a.property
  have hno : (∑ a : {a // ¬ p a}, if h : p a.val then f a.val h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact dif_neg a.property
  rw [hyes, hno, add_zero]

theorem dite_and_zero (p q : Prop) [Decidable p] [Decidable q] (f : p ∧ q → ℂ) :
    (if h : p ∧ q then f h else 0) =
      (if hp : p then (if hq : q then f ⟨hp, hq⟩ else 0) else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem mk_eq (n k : ℕ) (t : Fin n × Fin n → ℂ) :
    (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b =>
          t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = Mk n k t := by
  classical
  simp_rw [dite_and_zero, Finset.sum_dite_irrel, Finset.sum_const_zero, sum_dite_subtype]
  rfl

end PEqualNP.Outside.L_gct_205

theorem PEqualNP.Outside.L_gct_205 : ∀ n : ℕ, ∀ L Z : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n → (∑ R : Finset (Fin n), ∑ C : Finset (Fin n), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) → (∀ z ∈ Z, Matrix.permanent (Matrix.of fun a b => z (a, b)) = 0) → (fun _ => (1 : ℂ)) ∉ L ⊔ Z := by
  classical
  intro n L Z hL hZ hmem
  obtain ⟨t, ht, z, hz, hsum⟩ := Submodule.mem_sup.mp hmem
  have hn : -t ∈ L := L.neg_mem ht
  have hm : ∀ k, 1 ≤ k → k ≤ n → PEqualNP.Outside.L_gct_205.Mk n k (-t) = 0 := by
    intro k hk hkn
    rw [← PEqualNP.Outside.L_gct_205.mk_eq]
    exact hL (-t) hn k hk hkn
  have he : MvPolynomial.eval (fun p => 1 + (-t) p) (PEqualNP.Gct.permPoly ℂ n) =
      (n.factorial : ℂ) := by
    rw [PEqualNP.Outside.L_gct_205.minc_Mk]
    rw [Finset.sum_eq_single 0]
    · simp [PEqualNP.Outside.L_gct_205.Mk_zero]
    · intro k hk hk0
      rw [hm k (by omega) (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)), mul_zero]
    · simp
  rw [PEqualNP.Outside.L_gct_205.eval_permPoly] at he
  have hzval : (fun a b => 1 + (-t) (a, b)) = (fun a b => z (a, b)) := by
    funext a b
    have h := congrFun hsum (a, b)
    change t (a, b) + z (a, b) = 1 at h
    change 1 + -t (a, b) = z (a, b)
    rw [← h]
    ring
  rw [hzval, hZ z hz] at he
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) : (n.factorial : ℂ) ≠ 0) he.symm
