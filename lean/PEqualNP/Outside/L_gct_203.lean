import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.RowShift203

open Finset

-- The subpermanent expansion follows the project proof of the Minc expansion.
private def res {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) : Fin k ↪ Fin n :=
  ⟨fun a => σ (e a), σ.injective.comp e.injective⟩

@[local simp] private theorem res_apply {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) (a : Fin k) :
    res e σ a = σ (e a) := rfl

private def emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Fin k ↪ Fin n :=
  ⟨fun a => R.1.orderEmbOfFin R.2 (τ a), (R.1.orderEmbOfFin R.2).injective.comp τ.injective⟩

@[local simp] private theorem emb_apply {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k})
    (τ : Equiv.Perm (Fin k)) (a : Fin k) : emb R τ a = R.1.orderEmbOfFin R.2 (τ a) := rfl

private theorem card_extend {n k : ℕ} (e f : Fin k ↪ Fin n)
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

private theorem sum_perm_res {n k : ℕ} (e : Fin k ↪ Fin n) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), F (res e σ) = ((n - k).factorial : ℂ) * ∑ f, F f := by
  classical
  rw [← Fintype.sum_fiberwise' (fun σ : Equiv.Perm (Fin n) => res e σ) F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_const, Finset.card_univ, card_extend, nsmul_eq_mul]

private theorem range_emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Set.range (emb R τ) = (R.1 : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact Finset.orderEmbOfFin_mem R.1 R.2 _
  · intro hx
    rw [← Finset.range_orderEmbOfFin R.1 R.2] at hx
    obtain ⟨b, rfl⟩ := hx
    exact ⟨τ⁻¹ b, by simp⟩

private theorem emb_bijective {n k : ℕ} :
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

private theorem sum_embedding {n k : ℕ} (G : (Fin k ↪ Fin n) → ℂ) :
    ∑ f, G f = ∑ R : {R : Finset (Fin n) // R.card = k}, ∑ τ : Equiv.Perm (Fin k),
      G (emb R τ) := by
  rw [← (emb_bijective (n := n) (k := k)).sum_comp G]
  exact Fintype.sum_sigma _

private theorem prod_orderEmb {n k : ℕ} (C : Finset (Fin n)) (hC : C.card = k) (h : Fin n → ℂ) :
    ∏ j ∈ C, h j = ∏ a, h (C.orderEmbOfFin hC a) := by
  rw [← Finset.prod_coe_sort]
  exact (Fintype.prod_equiv (C.orderIsoOfFin hC).toEquiv _ _
    (fun a => by simp [Finset.coe_orderIsoOfFin_apply])).symm

private theorem sum_perm_cols {n k : ℕ} (t : Fin n × Fin n → ℂ) (C : Finset (Fin n)) (hC : C.card = k) :
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

private theorem eval_one_add (n : ℕ) (t : Fin n × Fin n → ℂ) :
    Matrix.permanent (Matrix.of fun i j : Fin n => 1 + t (i,j)) =
      ∑ C : Finset (Fin n), ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j) := by
  rw [Matrix.permanent]
  simp only [Matrix.of_apply]
  simp_rw [Finset.prod_one_add, Finset.powerset_univ]
  rw [Finset.sum_comm]

private theorem sum_by_card {n : ℕ} (G : Finset (Fin n) → ℂ) :
    ∑ C : Finset (Fin n), G C =
      ∑ k ∈ range (n + 1), ∑ C : {C : Finset (Fin n) // C.card = k}, G C.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1))
    (fun C _ => by
      have := Finset.card_le_univ C
      rw [Fintype.card_fin] at this
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le this))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_subtype _ (by simp) G

private noncomputable def Mk (n k : ℕ) (t : Fin n × Fin n → ℂ) : ℂ :=
  ∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k},
    Matrix.permanent (Matrix.of fun i j : Fin k =>
      t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j))

private theorem minc_Mk (n : ℕ) (t : Fin n × Fin n → ℂ) :
    Matrix.permanent (Matrix.of fun i j : Fin n => 1 + t (i,j)) =
      ∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) * Mk n k t := by
  rw [eval_one_add, sum_by_card]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [fun C : {C : Finset (Fin n) // C.card = k} => sum_perm_cols t C.1 C.2]
  rw [← Finset.mul_sum, Mk, Finset.sum_comm]

private theorem Mk_zero (n : ℕ) (t : Fin n × Fin n → ℂ) : Mk n 0 t = 1 := by
  have hu : ∀ S : {S : Finset (Fin n) // S.card = 0}, S = ⟨∅, Finset.card_empty⟩ :=
    fun S => Subtype.ext (Finset.card_eq_zero.mp S.2)
  rw [Mk, Fintype.sum_eq_single ⟨∅, Finset.card_empty⟩ (fun S hS => absurd (hu S) hS),
    Fintype.sum_eq_single ⟨∅, Finset.card_empty⟩ (fun S hS => absurd (hu S) hS),
    Matrix.permanent_isEmpty]

private theorem sum_subtype_dite {I : Type*} [Fintype I] (P : I → Prop)
    [DecidablePred P] (F : {i // P i} → ℂ) :
    ∑ i, F i = ∑ i, if h : P i then F ⟨i,h⟩ else 0 := by
  classical
  let f (i : I) := if h : P i then F ⟨i,h⟩ else 0
  have he : ∑ i ∈ univ.filter P, f i = ∑ i : {i // P i}, F i := by
    rw [Finset.sum_subtype (p := P) (F := inferInstance) (univ.filter P) (by simp)]
    exact sum_congr rfl (fun i _ => dite_eq_left i.property)
  rw [← he]
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simp_all [f])

private theorem affine_perm {n : ℕ} (t : Fin n × Fin n → ℂ)
    (ht : ∀ k : ℕ, 1 ≤ k → k ≤ n → (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
      if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b =>
        t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) :
    Matrix.permanent (Matrix.of fun i j : Fin n => 1 + t (i,j)) = (n.factorial : ℂ) := by
  classical
  rw [minc_Mk, Finset.sum_eq_single 0]
  · simp [Mk_zero]
  · intro k hk hn
    have h := ht k (by omega) (by simpa using Finset.mem_range.mp hk)
    have h' : Mk n k t = 0 := by
      convert h using 1
      unfold Mk
      rw [sum_subtype_dite]
      refine sum_congr rfl fun R _ => ?_
      by_cases hr : R.card = k
      · simp only [hr, dite_true]
        rw [sum_subtype_dite]
        refine sum_congr rfl fun C _ => ?_
        by_cases hc : C.card = k <;> simp [hc]
      · simp [hr]
    rw [h', mul_zero]
  · simp

open Finset

-- Inclusion-exclusion extracts the terms that use every argument exactly once.
private theorem ryser {I : Type*} [Fintype I] [DecidableEq I] (w : I → I → ℂ) :
    (∑ σ : Equiv.Perm I, ∏ i, w i (σ i)) =
    ∑ s : Finset I, (-1 : ℤ) ^ s.card • ∏ i, ∑ j ∈ sᶜ, w i j := by
  classical
  let miss (j : I) : Finset (I → I) := univ.filter fun f => ∀ i, f i ≠ j
  have hinter (s : Finset I) : s.inf miss = Fintype.piFinset (fun _ : I => sᶜ) := by
    ext f
    simp only [Finset.mem_inf, miss, mem_filter, mem_univ, true_and,
      Fintype.mem_piFinset, mem_compl]
    exact ⟨fun h i hj => h _ hj i rfl, fun h j hj i he => h i (he ▸ hj)⟩
  have hperm (f : I → I) :
      f ∈ univ.inf (fun j => (miss j)ᶜ) ↔ Function.Bijective f := by
    simp only [mem_inf, mem_compl, miss, mem_filter, mem_univ, true_and,
      not_forall, not_not, forall_const]
    exact Finite.surjective_iff_bijective
  let F (f : I → I) := ∏ i, w i (f i)
  have he : (∑ σ : Equiv.Perm I, F σ) =
      ∑ f ∈ univ.inf (fun j => (miss j)ᶜ), F f := by
    refine Finset.sum_bij' (fun (σ : Equiv.Perm I) _ => (σ : I → I))
      (fun f hf => Equiv.ofBijective f ((hperm f).mp hf)) ?_ ?_ ?_ ?_ ?_
    · intro σ _
      exact (hperm _).mpr σ.bijective
    · simp
    · intro σ _
      ext
      rfl
    · intro f _
      rfl
    · simp
  rw [show (∑ σ : Equiv.Perm I, ∏ i, w i (σ i)) = _ from he,
    Finset.inclusion_exclusion_sum_inf_compl, powerset_univ]
  apply sum_congr rfl
  intro s _
  rw [hinter, prod_univ_sum]

private theorem mixed_perm {I : Type*} [Fintype I] [DecidableEq I]
    (X Y : I → I × I → ℂ)
    (h : ∀ s : Finset I, Matrix.permanent (Matrix.of fun r c => ∑ j ∈ s, X j (r,c)) =
      Matrix.permanent (Matrix.of fun r c => ∑ j ∈ s, Y j (r,c))) :
    (∑ σ : Equiv.Perm I, ∑ τ : Equiv.Perm I, ∏ i, X (τ i) (σ i,i)) =
    (∑ σ : Equiv.Perm I, ∑ τ : Equiv.Perm I, ∏ i, Y (τ i) (σ i,i)) := by
  classical
  have expand (Z : I → I × I → ℂ) :
      (∑ σ : Equiv.Perm I, ∑ τ : Equiv.Perm I, ∏ i, Z (τ i) (σ i,i)) =
      ∑ s : Finset I, (-1 : ℤ)^s.card •
        Matrix.permanent (Matrix.of fun r c => ∑ j ∈ sᶜ, Z j (r,c)) := by
    simp_rw [fun σ : Equiv.Perm I => ryser (fun i j => Z j (σ i,i))]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [← Finset.smul_sum]
    rfl
  rw [expand, expand]
  exact sum_congr rfl fun s _ => congrArg _ (h sᶜ)

private theorem reorder_mixed {I : Type*} [Fintype I] [DecidableEq I]
    (Z : I → I × I → ℂ) :
    (∑ σ : Equiv.Perm I, ∑ τ : Equiv.Perm I, ∏ i, Z (τ i) (σ i,i)) =
    ∑ c : Equiv.Perm I, ∑ r : Equiv.Perm I, ∏ i, Z i (r i,c i) := by
  classical
  rw [Finset.sum_comm]
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm I))
  intro τ
  apply Fintype.sum_equiv (Equiv.mulRight τ⁻¹)
  intro σ
  apply Fintype.prod_equiv τ
  intro i
  simp

open Finset

private abbrev Fix (I : Type*) [Zero I] := {σ : Equiv.Perm I // σ 0 = 0}

private def factor (I : Type*) [AddCommGroup I] : Equiv.Perm I ≃ I × Fix I where
  toFun σ := (σ 0, ⟨σ.trans (Equiv.subRight (σ 0)), by simp⟩)
  invFun v := v.2.1.trans (Equiv.addRight v.1)
  left_inv σ := by ext j; simp
  right_inv := by
    rintro ⟨x, d, hd⟩
    apply Prod.ext
    · simp [hd]
    · apply Subtype.ext
      ext j
      simp [hd]

private def fixEmb (I : Type*) [Zero I] : Fix I ↪ (I → I) where
  toFun f := f.val
  inj' := by
    intro f g h
    exact Subtype.ext (Equiv.ext (congrFun h))

private def deltas (I : Type*) [AddCommGroup I] [Fintype I] [DecidableEq I] :
    Finset (I → I) := univ.map (fixEmb I)

private theorem card_deltas (n : ℕ) [NeZero n] :
    (deltas (Fin n)).card = (n-1).factorial := by
  classical
  have h := Fintype.card_congr (factor (Fin n))
  rw [Fintype.card_perm, Fintype.card_prod, Fintype.card_fin] at h
  simp only [deltas, card_map, card_univ]
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hh : n.factorial = n * (n-1).factorial := by
    cases n with
    | zero => omega
    | succ k => simp [Nat.factorial_succ]
  exact Nat.eq_of_mul_eq_mul_left hpos (h.symm.trans hh)

private theorem sum_perm_factor {I : Type*} [AddCommGroup I] [Fintype I] [DecidableEq I]
    (F : (I → I) → ℂ) :
    (∑ r : Equiv.Perm I, F r) = ∑ d ∈ deltas I, ∑ x : I, F (fun i => d i + x) := by
  classical
  rw [deltas, sum_map, sum_comm]
  rw [← Fintype.sum_prod_type (fun z : I × Fix I => F (fun i => (fixEmb I) z.2 i + z.1))]
  apply Fintype.sum_equiv (factor I)
  intro r
  congr 1
  funext i
  change r i = (r i - r 0) + r 0
  abel

open Fin.CommRing

private theorem adds_mem {n : ℕ} [NeZero n] (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hr : ∀ t ∈ L, (fun x : Fin n × Fin n => t (finRotate n x.1,x.2)) ∈ L)
    {t : Fin n × Fin n → ℂ} (ht : t ∈ L) (a : Fin n) :
    (fun x : Fin n × Fin n => t (x.1 + a,x.2)) ∈ L := by
  have h (k : ℕ) : (fun x : Fin n × Fin n => t (x.1 + (k : Fin n),x.2)) ∈ L := by
    induction k with
    | zero => simpa using ht
    | succ k ih =>
      simpa [finRotate_apply, Nat.cast_succ, add_assoc, add_comm, add_left_comm] using hr _ ih
  simpa using h a.val

open Finset Matrix
variable {A : Type*} [Fintype A] [DecidableEq A] [AddCommGroup A]

private def tr (R : Type*) [Semiring R] (a : A) : Matrix A A R :=
  Matrix.of fun i j => if i + a = j then 1 else 0

omit [Fintype A] in
private theorem tr_zero (R : Type*) [Semiring R] : tr R (0 : A) = 1 := by
  ext i j
  simp [tr, Matrix.one_apply]

private theorem tr_mul (R : Type*) [Semiring R] (a b : A) :
    tr R a * tr R b = tr R (a + b) := by
  ext i j
  change (∑ k : A, (if i + a = k then (1 : R) else 0) *
    (if k + b = j then 1 else 0)) = _
  rw [Finset.sum_eq_single (i + a)]
  · simp [tr, add_assoc]
  · intro k _ hk
    simp [Ne.symm hk]
  · simp

private theorem tr_pow (R : Type*) [Semiring R] (a : A) (k : ℕ) :
    tr R a ^ k = tr R (k • a) := by
  induction k with
  | zero => simp [tr_zero]
  | succ k ih => rw [pow_succ, ih, tr_mul, succ_nsmul]

-- The translations commute and their prime powers are all the identity.
private theorem trans_sum_pow (p : ℕ) [Fact p.Prime] (s : Finset A)
    (ha : ∀ a : A, p • a = 0) :
    (∑ a ∈ s, tr (ZMod p) a) ^ p = (s.card : Matrix A A (ZMod p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Fact.out (p := p.Prime) |>.ne_zero]
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, add_pow_char_of_commute, tr_pow, ha, tr_zero, ih,
      Finset.card_insert_of_notMem hx, Nat.cast_add, Nat.cast_one, add_comm]
    apply Commute.sum_right
    intro b _
    change tr _ x * tr _ b = tr _ b * tr _ x
    rw [tr_mul, tr_mul, add_comm]

omit [Fintype A] in
private theorem map_tr_sum (R : Type*) [CommRing R] (s : Finset A) :
    (∑ a ∈ s, tr ℤ a).map (fun z : ℤ => (z : R)) = ∑ a ∈ s, tr R a := by
  classical
  ext i j
  simp [Matrix.map_apply, Matrix.sum_apply, tr]

private theorem trans_injective (p : ℕ) [Fact p.Prime] (s : Finset A)
    (ha : ∀ a : A, p • a = 0) (hs : (s.card : ZMod p) ≠ 0) :
    Function.Injective (∑ a ∈ s, tr ℂ a).mulVec := by
  classical
  have hz : (∑ a ∈ s, tr (ZMod p) a).det ≠ 0 := by
    intro h
    have he := congrArg Matrix.det (trans_sum_pow p s ha)
    rw [Matrix.det_pow, h, zero_pow (Fact.out (p := p.Prime)).ne_zero,
      ← Matrix.diagonal_natCast, Matrix.det_diagonal] at he
    exact (Finset.prod_ne_zero_iff.mpr (fun _ _ => hs)) he.symm
  have hi : (∑ a ∈ s, tr ℤ a).det ≠ 0 := by
    intro h
    apply hz
    rw [← map_tr_sum, ← Int.cast_det, h, Int.cast_zero]
  apply Matrix.mulVec_injective_of_isUnit
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [← map_tr_sum, ← Int.cast_det]
  exact_mod_cast hi

private theorem convolution_injective (p : ℕ) [Fact p.Prime] (s : Finset A)
    (ha : ∀ a : A, p • a = 0) (hs : (s.card : ZMod p) ≠ 0)
    (f g : A → ℂ) (h : ∀ x, ∑ a ∈ s, f (x + a) = ∑ a ∈ s, g (x + a)) :
    f = g := by
  apply trans_injective p s ha hs
  funext x
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec]
  simpa [Finset.sum_apply, Matrix.mulVec, dotProduct, tr, ite_mul] using h x

-- Normalize the first row of a permutation and then recover the unshifted row sum.
private theorem collapse (p : ℕ) [Fact p.Prime] [NeZero p]
    (Z W : Fin p × Fin p → ℂ)
    (h : ∀ a : Fin p → Fin p,
      (∑ c : Equiv.Perm (Fin p), ∑ r : Equiv.Perm (Fin p), ∏ i, Z (r i + a i,c i)) =
      (∑ c : Equiv.Perm (Fin p), ∑ r : Equiv.Perm (Fin p), ∏ i, W (r i + a i,c i))) :
    (∑ x : Fin p, ∏ i, Z (x,i)) = ∑ x : Fin p, ∏ i, W (x,i) := by
  classical
  let S := deltas (Fin p)
  let f (V : Fin p × Fin p → ℂ) (a : Fin p → Fin p) :=
    ∑ x, ∑ c : Equiv.Perm (Fin p), ∏ i, V (a i + x,c i)
  have expand (V : Fin p × Fin p → ℂ) (a : Fin p → Fin p) :
      (∑ c : Equiv.Perm (Fin p), ∑ r : Equiv.Perm (Fin p), ∏ i, V (r i + a i,c i)) =
      ∑ d ∈ S, f V (a + d) := by
    rw [sum_comm]
    rw [sum_perm_factor (fun r => ∑ c : Equiv.Perm (Fin p), ∏ i, V (r i + a i,c i))]
    simp [S, f, add_comm, add_left_comm]
  have hp : p.Prime := Fact.out
  have hs : (S.card : ZMod p) ≠ 0 := by
    intro h0
    rw [show S.card = _ from card_deltas p] at h0
    have hh := hp.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff _ p).mp h0)
    have := hp.pos
    omega
  have ha (a : Fin p → Fin p) : p • a = 0 := by
    funext i
    simp
  have eq := convolution_injective p S ha hs (f Z) (f W)
    (fun a => (expand Z a).symm.trans ((h a).trans (expand W a)))
  have eval0 (V : Fin p × Fin p → ℂ) :
      f V 0 = (p.factorial : ℂ) * ∑ x, ∏ i, V (x,i) := by
    unfold f
    simp only [Pi.zero_apply, zero_add]
    simp_rw [fun x (c : Equiv.Perm (Fin p)) => Equiv.prod_comp c (fun j => V (x,j))]
    simp [Fintype.card_perm, nsmul_eq_mul, mul_sum]
  have he := congrFun eq 0
  rw [eval0, eval0] at he
  exact mul_left_cancel₀ (show (p.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero p) he

private theorem mixed_of_level {n : ℕ} [NeZero n] (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, Matrix.permanent (Matrix.of fun i j : Fin n => 1 + t (i,j)) =
      (n.factorial : ℂ))
    (u : Fin n → Fin n × Fin n → ℂ) (hu : ∀ j, u j ∈ L) :
    (∑ c : Equiv.Perm (Fin n), ∑ r : Equiv.Perm (Fin n), ∏ i, (1 + u i (r i,c i))) =
    ∑ c : Equiv.Perm (Fin n), ∑ r : Equiv.Perm (Fin n), ∏ _i : Fin n, (1 : ℂ) := by
  classical
  let X (i : Fin n) (q : Fin n × Fin n) := 1 + u i q
  let W (_i : Fin n) (_q : Fin n × Fin n) := (1 : ℂ)
  have h (s : Finset (Fin n)) :
      Matrix.permanent (Matrix.of fun r c => ∑ j ∈ s, X j (r,c)) =
      Matrix.permanent (Matrix.of fun r c => ∑ j ∈ s, W j (r,c)) := by
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    let b := (s.card : ℂ)
    have hb : b ≠ 0 := by dsimp [b]; exact_mod_cast hs.card_ne_zero
    let v := b⁻¹ • (∑ j ∈ s, u j)
    have hv : v ∈ L := L.smul_mem _ (L.sum_mem (fun j _ => hu j))
    have hm : Matrix.of (fun r c => ∑ j ∈ s, X j (r,c)) =
        b • Matrix.of (fun r c => 1 + v (r,c)) := by
      ext r c
      simp [X, v, b, Matrix.smul_apply, sum_add_distrib, mul_add,
        show (s.card : ℂ) ≠ 0 from hb]
    have hw : Matrix.of (fun r c => ∑ j ∈ s, W j (r,c)) =
        b • Matrix.of (fun _ _ : Fin n => (1 : ℂ)) := by
      ext r c
      simp [W, b]
    rw [hm, hw, Matrix.permanent_smul, Matrix.permanent_smul, hL v hv]
    congr 1
    simpa using (hL 0 L.zero_mem).symm
  exact (reorder_mixed X).symm.trans ((mixed_perm X W h).trans (reorder_mixed W))

private theorem row_identity {n : ℕ} [Fact n.Prime] [NeZero n]
    (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hr : ∀ t ∈ L, (fun x : Fin n × Fin n => t (finRotate n x.1,x.2)) ∈ L)
    (hL : ∀ t ∈ L, Matrix.permanent (Matrix.of fun i j : Fin n => 1 + t (i,j)) =
      (n.factorial : ℂ))
    {t : Fin n × Fin n → ℂ} (ht : t ∈ L) :
    (∑ x : Fin n, ∏ j : Fin n, (1 + t (x,j))) = (n : ℂ) := by
  have h := collapse n (fun q => 1 + t q) (fun _ => 1) (fun a =>
    mixed_of_level L hL (fun i q => t (q.1 + a i,q.2)) (fun i => adds_mem L hr ht (a i)))
  simpa using h

-- The transversal argument follows the project proof of L-gct-171.

open Submodule Module

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*}

private def un (A : ι → Finset W) (s : Finset ι) : Set W := ⋃ j ∈ s, (A j : Set W)

private lemma un_finite (A : ι → Finset W) (s : Finset ι) : (un A s).Finite :=
  s.finite_toSet.biUnion fun j _ => (A j).finite_toSet

private lemma un_insert [DecidableEq ι] (A : ι → Finset W) (i : ι) (s : Finset ι) :
    un A (insert i s) = (A i : Set W) ∪ un A s := by
  simp only [un, Finset.set_biUnion_insert]

private lemma un_union [DecidableEq ι] (A : ι → Finset W) (s t : Finset ι) :
    un A (s ∪ t) = un A s ∪ un A t := by
  simp only [un, Finset.set_biUnion_union]

private lemma un_mono (A : ι → Finset W) {s t : Finset ι} (h : s ⊆ t) : un A s ⊆ un A t :=
  Set.biUnion_subset_biUnion_left (fun _ hx => h hx)

private lemma un_update_of_not_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∉ s) : un (Function.update A i B) s = un A s := by
  unfold un
  refine Set.iUnion₂_congr fun j hj => ?_
  rw [Function.update_of_ne (by rintro rfl; exact h hj)]

private lemma un_update_of_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∈ s) :
    un (Function.update A i B) s = (B : Set W) ∪ un A (s.erase i) := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [un_insert, un_update_of_not_mem _ _ _ _ (Finset.notMem_erase i s),
    Function.update_self]

private def Good (K : Type*) [Field K] [Module K W] (A : ι → Finset W) : Prop :=
  ∀ s : Finset ι, s.card ≤ finrank K (span K (un A s))

private lemma finrank_span_mono {X Y : Set W} (hY : Y.Finite) (h : X ⊆ Y) :
    finrank K (span K X) ≤ finrank K (span K Y) := by
  haveI := FiniteDimensional.span_of_finite K hY
  exact Submodule.finrank_mono (span_mono h)

private lemma bad_erase [DecidableEq ι] [DecidableEq W] (A : ι → Finset W) (hA : Good K A) (i : ι)
    (c : W) (h : ¬ Good K (Function.update A i ((A i).erase c))) :
    ∃ t : Finset ι, i ∉ t ∧
      finrank K (span K ((((A i).erase c : Finset W) : Set W) ∪ un A t)) ≤ t.card := by
  simp only [Good, not_forall, not_le] at h
  obtain ⟨s, hs⟩ := h
  by_cases hi : i ∈ s
  · refine ⟨s.erase i, Finset.notMem_erase i s, ?_⟩
    rw [un_update_of_mem _ _ _ _ hi] at hs
    have := Finset.card_erase_add_one hi
    omega
  · rw [un_update_of_not_mem _ _ _ _ hi] at hs
    exact absurd (hA s) (not_le.mpr hs)

private lemma erase_good [DecidableEq ι] [DecidableEq W] (A : ι → Finset W) (hA : Good K A) (i : ι)
    {a b : W} (ha : a ∈ A i) (hb : b ∈ A i) (hab : a ≠ b) :
    Good K (Function.update A i ((A i).erase a)) ∨
      Good K (Function.update A i ((A i).erase b)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨t1, hi1, h1⟩ := bad_erase A hA i a hcon.1
  obtain ⟨t2, hi2, h2⟩ := bad_erase A hA i b hcon.2
  set X : Set W := (((A i).erase a : Finset W) : Set W) ∪ un A t1 with hX
  set Y : Set W := (((A i).erase b : Finset W) : Set W) ∪ un A t2 with hY
  have hXf : X.Finite := ((A i).erase a).finite_toSet.union (un_finite A t1)
  have hYf : Y.Finite := ((A i).erase b).finite_toSet.union (un_finite A t2)
  haveI : FiniteDimensional K (span K X) := FiniteDimensional.span_of_finite K hXf
  haveI : FiniteDimensional K (span K Y) := FiniteDimensional.span_of_finite K hYf
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (span K X) (span K Y)
  -- the union side
  have hU : un A (insert i (t1 ∪ t2)) ⊆ X ∪ Y := by
    rw [un_insert, un_union]
    intro x hx
    rcases hx with hx | hx | hx
    · by_cases hxa : x = a
      · subst hxa
        exact Or.inr (Or.inl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hab, ha⟩)))
      · exact Or.inl (Or.inl (by simp [Finset.mem_erase, hxa, hx]))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)
  have hi12 : i ∉ t1 ∪ t2 := by simp [hi1, hi2]
  have hcardU := hA (insert i (t1 ∪ t2))
  rw [Finset.card_insert_of_notMem hi12] at hcardU
  have hsup : finrank K (span K (un A (insert i (t1 ∪ t2)))) ≤ finrank K ↥(span K X ⊔ span K Y) := by
    rw [← Submodule.span_union]
    exact finrank_span_mono (hXf.union hYf) hU
  -- the intersection side
  have hinf : finrank K (span K (un A (t1 ∩ t2))) ≤ finrank K ↥(span K X ⊓ span K Y) := by
    haveI : FiniteDimensional K ↥(span K X ⊓ span K Y) :=
      Submodule.finiteDimensional_inf_left _ _
    refine Submodule.finrank_mono (le_inf (span_mono ?_) (span_mono ?_))
    · exact (un_mono A Finset.inter_subset_left).trans Set.subset_union_right
    · exact (un_mono A Finset.inter_subset_right).trans Set.subset_union_right
  have hcardI := hA (t1 ∩ t2)
  have hc := Finset.card_union_add_card_inter t1 t2
  omega

private theorem rado_aux [Fintype ι] [DecidableEq ι] [DecidableEq W] :
    ∀ n : ℕ, ∀ A : ι → Finset W, ∑ j, (A j).card = n → Good K A →
      ∃ f : ι → W, (∀ j, f j ∈ A j) ∧ LinearIndependent K f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn hA
  by_cases hbig : ∃ i, 1 < (A i).card
  · obtain ⟨i, hi⟩ := hbig
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hi
    have key : ∃ c ∈ A i, Good K (Function.update A i ((A i).erase c)) := by
      rcases erase_good A hA i ha hb hab with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    obtain ⟨c, hc, hgood⟩ := key
    set A' := Function.update A i ((A i).erase c) with hA'
    have hlt : ∑ j, (A' j).card < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [hA', Function.update_self]
          exact Finset.card_erase_le
        · simp only [hA', Function.update_of_ne hj, le_refl]
      · simp only [hA', Function.update_self]
        exact Finset.card_erase_lt_of_mem hc
    obtain ⟨f, hf, hli⟩ := ih _ hlt A' rfl hgood
    refine ⟨f, fun j => ?_, hli⟩
    have := hf j
    by_cases hj : j = i
    · subst hj; simp only [hA', Function.update_self] at this
      exact Finset.mem_of_mem_erase this
    · simpa only [hA', Function.update_of_ne hj] using this
  · push_neg at hbig
    have hone : ∀ j, ∃ v, A j = {v} := by
      intro j
      refine Finset.card_eq_one.mp (le_antisymm (hbig j) ?_)
      have h1 := hA {j}
      have hunj : un A {j} = (A j : Set W) := by simp [un]
      rw [hunj, Finset.card_singleton] at h1
      rw [Nat.one_le_iff_ne_zero] at h1 ⊢
      intro h0
      rw [Finset.card_eq_zero] at h0
      apply h1
      simp [h0]
    choose f hf using hone
    refine ⟨f, fun j => by simp [hf j], ?_⟩
    rw [linearIndependent_iff_card_le_finrank_span]
    have h := hA Finset.univ
    have hr : un A Finset.univ = Set.range f := by
      ext x; simp [un, hf, eq_comm]
    rw [hr, Finset.card_univ] at h
    exact h

private def ev {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) (q : Fin n × Fin n) :
    Module.Dual ℂ L := (LinearMap.proj q).comp L.subtype

private theorem ev_basis {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    ∃ q : Fin (Module.finrank ℂ L) → Fin n × Fin n,
      LinearIndependent ℂ (fun i => ev L (q i)) := by
  classical
  have hs : Submodule.span ℂ (Set.range (ev L)) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro t ht
    by_contra! h
    apply ht
    apply Subtype.ext
    funext q
    exact h (ev L q) ⟨q,rfl⟩
  have hh := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range (ev L))
  rw [hs, finrank_top, Subspace.dual_finrank_eq] at hh
  obtain ⟨g,hg,_,hgi⟩ := hh
  choose q hq using hg
  exact ⟨q, by simpa only [hq] using hgi⟩

private theorem count_rows {n d : ℕ} [NeZero n] (row : Fin d → Fin n) (R : Finset (Fin n)) :
    (∑ x : Fin n, (univ.filter (fun i : Fin d => row i + x ∈ R)).card) = d * R.card := by
  classical
  have tone (i : Fin d) : (∑ x : Fin n, if row i + x ∈ R then 1 else 0) = R.card := by
    calc _ = (∑ x : Fin n, if x ∈ R then 1 else 0) :=
             Equiv.sum_comp (Equiv.addLeft (row i)) (fun x => if x ∈ R then 1 else 0)
         _ = _ := by simp
  simp_rw [Finset.card_filter]
  rw [sum_comm]
  simp [tone]

private theorem independent_shift {n d : ℕ} [NeZero n] (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hr : ∀ t ∈ L, (fun x : Fin n × Fin n => t (finRotate n x.1,x.2)) ∈ L)
    (q : Fin d → Fin n × Fin n) (hq : LinearIndependent ℂ (fun i => ev L (q i)))
    (a : Fin n) : LinearIndependent ℂ (fun i => ev L ((q i).1 + a,(q i).2)) := by
  let sh (b : Fin n) : L →ₗ[ℂ] L :=
    { toFun := fun t => ⟨fun x => t.1 (x.1+b,x.2), adds_mem L hr t.2 b⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsu : Function.Surjective (sh a) := by
    intro t
    refine ⟨sh (-a) t, Subtype.ext ?_⟩
    funext x
    change t.1 (x.1+a+ -a,x.2) = t.1 x
    simp
  exact hq.map' (sh a).dualMap (LinearMap.ker_eq_bot.mpr
    (LinearMap.dualMap_injective_of_surjective hsu))

-- Each chosen basis entry is counted once for every row in the given set.
private theorem row_rank {n : ℕ} [NeZero n] (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hr : ∀ t ∈ L, (fun x : Fin n × Fin n => t (finRotate n x.1,x.2)) ∈ L)
    (hd : n ≤ Module.finrank ℂ L)
    (A : Fin n → Finset (Module.Dual ℂ L))
    (hA : ∀ i j, ev L (i,j) ∈ A i) (R : Finset (Fin n)) :
    R.card ≤ Module.finrank ℂ (Submodule.span ℂ (⋃ i ∈ R, (A i : Set (Module.Dual ℂ L)))) := by
  classical
  let d := Module.finrank ℂ L
  obtain ⟨q,hq⟩ := ev_basis L
  let E := Submodule.span ℂ (⋃ i ∈ R, (A i : Set (Module.Dual ℂ L)))
  let U (x : Fin n) := univ.filter (fun i : Fin d => (q i).1 + x ∈ R)
  have each (x : Fin n) : (U x).card ≤ Module.finrank ℂ E := by
    let b (i : U x) : E := ⟨ev L ((q i).1+x,(q i).2), by
      apply Submodule.subset_span
      apply Set.mem_iUnion₂.mpr
      exact ⟨_, (mem_filter.mp i.2).2, hA _ _⟩⟩
    have hi : LinearIndependent ℂ b := by
      apply LinearIndependent.of_comp E.subtype
      exact (independent_shift L hr q hq x).comp _ Subtype.val_injective
    simpa using hi.fintype_card_le_finrank
  have hsum := sum_le_sum (s := (univ : Finset (Fin n))) (fun x _ => each x)
  have hc := count_rows (fun i => (q i).1) R
  change (∑ x, (U x).card) = d * R.card at hc
  rw [hc] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact Nat.le_of_mul_le_mul_left ((Nat.mul_le_mul_right R.card hd).trans hsum) (Nat.pos_of_ne_zero (NeZero.ne n))

private theorem dimension_bound {n : ℕ} [Fact n.Prime] [NeZero n]
    (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hr : ∀ t ∈ L, (fun x : Fin n × Fin n => t (finRotate n x.1,x.2)) ∈ L)
    (hL : ∀ t ∈ L, Matrix.permanent (Matrix.of fun i j : Fin n => 1 + t (i,j)) =
      (n.factorial : ℂ)) : Module.finrank ℂ L ≤ n - 1 := by
  classical
  by_contra! h
  have hp : n.Prime := Fact.out
  have hd : n ≤ Module.finrank ℂ L := by omega
  let A (i : Fin n) := univ.image (fun j : Fin n => ev L (i,j))
  have hin (i j : Fin n) : ev L (i,j) ∈ A i := mem_image_of_mem _ (mem_univ j)
  obtain ⟨f,hf,hi⟩ := rado_aux _ A rfl (row_rank L hr hd A hin)
  obtain ⟨φ,hφ⟩ := Module.exists_dual_forall_apply_eq_one hi.linearIndepOn_univ
  let t : L := (Module.evalEquiv ℂ L).symm φ
  have ht (i : Fin n) : ∃ j : Fin n, t.1 (i,j) = 1 := by
    obtain ⟨j,_,hj⟩ := mem_image.mp (hf i)
    refine ⟨j,?_⟩
    change ev L (i,j) t = 1
    rw [hj]
    simpa [t] using hφ i (Set.mem_univ i)
  have hz (i : Fin n) : (∏ j : Fin n, (1 + (-t.1) (i,j))) = 0 := by
    obtain ⟨j,hj⟩ := ht i
    exact Finset.prod_eq_zero (mem_univ j) (by simp [hj])
  have hid := row_identity L hr hL (L.neg_mem t.2)
  simp only [hz, sum_const_zero] at hid
  exact (Nat.cast_ne_zero.mpr hp.ne_zero : (n : ℂ) ≠ 0) hid.symm

end PEqualNP.Outside.RowShift203

open PEqualNP.Outside.RowShift203 in
theorem PEqualNP.Outside.L_gct_203 :
    ∀ n : ℕ, n.Prime → ∀ L : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ L, (fun x : Fin n × Fin n => t (finRotate n x.1, x.2)) ∈ L) → (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n → (∑ R : Finset (Fin n), ∑ C : Finset (Fin n), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) → Module.finrank ℂ L ≤ n - 1 := by
  intro n hp L hr ht
  letI : Fact n.Prime := ⟨hp⟩
  letI : NeZero n := ⟨hp.ne_zero⟩
  exact dimension_bound L hr (fun t h => affine_perm t (ht t h))
