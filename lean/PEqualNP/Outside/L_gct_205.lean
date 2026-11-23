import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct205

open Finset

private def complIso {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) :
    Fin (n - k) ≃ {x : Fin n // x ∉ S} :=
  have hSc : Sᶜ.card = n - k := by
    rw [Finset.card_compl, Fintype.card_fin, hS]
  (Sᶜ.orderIsoOfFin hSc).toEquiv.trans
    { toFun := fun ⟨x, hx⟩ => ⟨x, Finset.mem_compl.mp hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨x, Finset.mem_compl.mpr hx⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }

private def splitEquiv {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) :
    Fin k ⊕ Fin (n - k) ≃ Fin n :=
  (Equiv.sumCongr (S.orderIsoOfFin hS).toEquiv (complIso S hS)).trans
    (Equiv.sumCompl (· ∈ S))

private lemma splitEquiv_inl {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) (a : Fin k) :
    splitEquiv S hS (Sum.inl a) = S.orderEmbOfFin hS a := rfl

private lemma splitEquiv_inl_mem {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) (a : Fin k) :
    splitEquiv S hS (Sum.inl a) ∈ S :=
  (S.orderIsoOfFin hS a).2

private lemma splitEquiv_inr_notMem {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k)
    (b : Fin (n - k)) :
    splitEquiv S hS (Sum.inr b) ∉ S :=
  (complIso S hS b).2

private lemma mem_iff_isLeft_symm {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) (x : Fin n) :
    x ∈ S ↔ ∃ a : Fin k, (splitEquiv S hS).symm x = Sum.inl a := by
  constructor
  · intro hx
    refine ⟨(S.orderIsoOfFin hS).symm ⟨x, hx⟩, ?_⟩
    apply (splitEquiv S hS).injective
    rw [Equiv.apply_symm_apply]
    simp [splitEquiv]
  · rintro ⟨a, ha⟩
    have hx : x = splitEquiv S hS (Sum.inl a) := by
      have := congrArg (splitEquiv S hS) ha
      simpa using this
    rw [hx]
    exact splitEquiv_inl_mem S hS a

private lemma fiber_sum {n k : ℕ} (u : Fin n × Fin n → ℂ)
    (R C : Finset (Fin n)) (hR : R.card = k) (hC : C.card = k) :
    (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => C.image σ = R),
      ∏ i ∈ C, u (σ i, i)) =
    ((n - k).factorial : ℂ) *
      Matrix.permanent (Matrix.of fun a b => u (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b)) := by
  let eR := splitEquiv R hR
  let eC := splitEquiv C hC
  let Φ : Equiv.Perm (Fin k) × Equiv.Perm (Fin (n - k)) → Equiv.Perm (Fin n) :=
    fun p => eC.symm.trans ((Equiv.sumCongr p.1 p.2).trans eR)
  have hΦ_apply_inl : ∀ (τ : Equiv.Perm (Fin k)) (ρ : Equiv.Perm (Fin (n - k))) (b : Fin k),
      Φ (τ, ρ) (C.orderEmbOfFin hC b) = R.orderEmbOfFin hR (τ b) := by
    intro τ ρ b
    change eR (Equiv.sumCongr τ ρ (eC.symm (eC (Sum.inl b)))) = eR (Sum.inl (τ b))
    rw [Equiv.symm_apply_apply]
    rfl
  have hΦ_img : ∀ p : Equiv.Perm (Fin k) × Equiv.Perm (Fin (n - k)), C.image (Φ p) = R := by
    rintro ⟨τ, ρ⟩
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨b, hb⟩ := (mem_iff_isLeft_symm C hC x).mp hx
      have hx' : x = C.orderEmbOfFin hC b := by
        have := congrArg eC hb
        simpa [eC, splitEquiv_inl] using this
      rw [hx', hΦ_apply_inl]
      exact splitEquiv_inl_mem R hR (τ b)
    · intro hy
      obtain ⟨a, ha⟩ := (mem_iff_isLeft_symm R hR y).mp hy
      have hy' : y = R.orderEmbOfFin hR a := by
        have := congrArg eR ha
        simpa [eR, splitEquiv_inl] using this
      refine ⟨C.orderEmbOfFin hC (τ.symm a), splitEquiv_inl_mem C hC (τ.symm a), ?_⟩
      rw [hΦ_apply_inl, Equiv.apply_symm_apply, hy']
  have hsum :
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => C.image σ = R),
        ∏ i ∈ C, u (σ i, i)) =
      ∑ p : Equiv.Perm (Fin k) × Equiv.Perm (Fin (n - k)),
        ∏ b : Fin k, u (R.orderEmbOfFin hR (p.1 b), C.orderEmbOfFin hC b) := by
    symm
    refine Finset.sum_nbij Φ ?_ ?_ ?_ ?_
    · intro p _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hΦ_img p
    · rintro ⟨τ₁, ρ₁⟩ _ ⟨τ₂, ρ₂⟩ _ heq
      have hsc : Equiv.sumCongr τ₁ ρ₁ = Equiv.sumCongr τ₂ ρ₂ := by
        ext x
        have h1 : Φ (τ₁, ρ₁) (eC x) = Φ (τ₂, ρ₂) (eC x) := congrArg (fun σ => σ (eC x)) heq
        change eR (Equiv.sumCongr τ₁ ρ₁ (eC.symm (eC x))) =
               eR (Equiv.sumCongr τ₂ ρ₂ (eC.symm (eC x))) at h1
        rw [Equiv.symm_apply_apply] at h1
        exact eR.injective h1
      refine Prod.ext (Equiv.ext fun a => ?_) (Equiv.ext fun a => ?_)
      · have := congrArg (fun f => f (Sum.inl a)) hsc
        simpa using this
      · have := congrArg (fun f => f (Sum.inr a)) hsc
        simpa using this
    · intro σ hσ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      let ψ : Equiv.Perm (Fin k ⊕ Fin (n - k)) := eC.trans (σ.trans eR.symm)
      have hψ_inl : ∀ b : Fin k, ∃ a : Fin k, ψ (Sum.inl b) = Sum.inl a := by
        intro b
        have hmem : σ (eC (Sum.inl b)) ∈ R := by
          rw [← hσ]
          exact Finset.mem_image_of_mem σ (splitEquiv_inl_mem C hC b)
        exact (mem_iff_isLeft_symm R hR _).mp hmem
      have hψ_inr : ∀ j : Fin (n - k), ∃ i : Fin (n - k), ψ (Sum.inr j) = Sum.inr i := by
        intro j
        cases hval : ψ (Sum.inr j) with
        | inl a =>
          have hmem : σ (eC (Sum.inr j)) ∈ R := (mem_iff_isLeft_symm R hR _).mpr ⟨a, hval⟩
          rw [← hσ] at hmem
          obtain ⟨x, hxC, hxe⟩ := Finset.mem_image.mp hmem
          have hxe' := σ.injective hxe
          exact False.elim (splitEquiv_inr_notMem C hC j (hxe' ▸ hxC))
        | inr i => exact ⟨i, rfl⟩
      choose τf hτf using hψ_inl
      choose ρf hρf using hψ_inr
      have hτ_inj : Function.Injective τf := by
        intro b₁ b₂ h
        have h1 : ψ (Sum.inl b₁) = ψ (Sum.inl b₂) := by rw [hτf, hτf, h]
        exact Sum.inl.inj (ψ.injective h1)
      have hρ_inj : Function.Injective ρf := by
        intro j₁ j₂ h
        have h1 : ψ (Sum.inr j₁) = ψ (Sum.inr j₂) := by rw [hρf, hρf, h]
        exact Sum.inr.inj (ψ.injective h1)
      let τ : Equiv.Perm (Fin k) := Equiv.ofBijective τf (Finite.injective_iff_bijective.mp hτ_inj)
      let ρ : Equiv.Perm (Fin (n - k)) := Equiv.ofBijective ρf (Finite.injective_iff_bijective.mp hρ_inj)
      refine ⟨(τ, ρ), Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      apply Equiv.ext
      intro x
      have hψeq : Equiv.sumCongr τ ρ = ψ := by
        apply Equiv.ext
        intro s
        cases s with
        | inl b => exact (hτf b).symm
        | inr j => exact (hρf j).symm
      change eR (Equiv.sumCongr τ ρ (eC.symm x)) = σ x
      rw [hψeq]
      simp [ψ]
    · rintro ⟨τ, ρ⟩ _
      have hprod : (∏ i ∈ C, u (Φ (τ, ρ) i, i)) =
          ∏ b : Fin k, u (Φ (τ, ρ) (C.orderEmbOfFin hC b), C.orderEmbOfFin hC b) := by
        symm
        refine Finset.prod_nbij (fun b => C.orderEmbOfFin hC b) ?_ ?_ ?_ ?_
        · intro b _; exact splitEquiv_inl_mem C hC b
        · intro b₁ _ b₂ _ h; exact (C.orderEmbOfFin hC).injective h
        · intro x hx
          obtain ⟨b, hb⟩ := (mem_iff_isLeft_symm C hC x).mp hx
          refine ⟨b, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
          have := congrArg eC hb
          simpa [eC, splitEquiv_inl] using this.symm
        · intro b _; rfl
      rw [hprod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hΦ_apply_inl]
  rw [hsum, Fintype.sum_prod_type_right]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    Matrix.permanent, Matrix.of_apply]

private lemma perm_one_add (n : ℕ) (u : Fin n × Fin n → ℂ) :
    Matrix.permanent (Matrix.of fun a b => (1 : ℂ) + u (a, b)) =
    ∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) *
      ∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
        if h : R.card = k ∧ C.card = k then
          Matrix.permanent (Matrix.of fun a b => u (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0 := by
  rw [Matrix.permanent]
  have h1 : ∀ σ : Equiv.Perm (Fin n),
      (∏ i : Fin n, ((1 : ℂ) + u (σ i, i))) =
      ∑ C : Finset (Fin n), ∏ i ∈ C, u (σ i, i) := by
    intro σ
    have := Finset.prod_add (fun i : Fin n => u (σ i, i)) (fun _ : Fin n => (1 : ℂ)) Finset.univ
    simp only [Finset.prod_const_one, mul_one, add_comm] at this
    rw [this, Finset.powerset_univ]
  simp_rw [Matrix.of_apply, h1]
  rw [Finset.sum_comm]
  have h2 : ∀ C : Finset (Fin n),
      (∑ σ : Equiv.Perm (Fin n), ∏ i ∈ C, u (σ i, i)) =
      ∑ R : Finset (Fin n),
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => C.image σ = R),
          ∏ i ∈ C, u (σ i, i) := by
    intro C
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  simp_rw [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ R C : Finset (Fin n),
      (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => C.image σ = R),
        ∏ i ∈ C, u (σ i, i)) =
      ∑ k ∈ Finset.range (n + 1),
        if h : R.card = k ∧ C.card = k then
          ((n - k).factorial : ℂ) *
            Matrix.permanent (Matrix.of fun a b => u (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0 := by
    intro R C
    by_cases hcard : R.card = C.card
    · have hkmem : R.card ∈ Finset.range (n + 1) := by
        rw [Finset.mem_range]
        have := Finset.card_le_univ R
        rw [Fintype.card_fin] at this
        omega
      rw [Finset.sum_eq_single R.card]
      · rw [dif_pos ⟨rfl, hcard.symm⟩]
        exact fiber_sum u R C rfl hcard.symm
      · intro k _ hne
        rw [dif_neg (fun h => hne h.1.symm)]
      · intro hnot; exact False.elim (hnot hkmem)
    · have hemp : Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => C.image σ = R) = ∅ := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro himg
        apply hcard
        rw [← himg, Finset.card_image_of_injective C σ.injective]
      rw [hemp, Finset.sum_empty]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [dif_neg (fun h => hcard (h.1.trans h.2.symm))]
  simp_rw [h3]
  have hswap : ∀ R : Finset (Fin n),
      (∑ C : Finset (Fin n), ∑ k ∈ Finset.range (n + 1),
        if h : R.card = k ∧ C.card = k then
          ((n - k).factorial : ℂ) *
            Matrix.permanent (Matrix.of fun a b => u (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0) =
      ∑ k ∈ Finset.range (n + 1), ∑ C : Finset (Fin n),
        if h : R.card = k ∧ C.card = k then
          ((n - k).factorial : ℂ) *
            Matrix.permanent (Matrix.of fun a b => u (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0 := fun R => Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  split <;> ring

theorem main (n : ℕ) (L Z : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
        if h : R.card = k ∧ C.card = k then
          Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
        else 0) = 0)
    (hZ : ∀ z ∈ Z, Matrix.permanent (Matrix.of fun a b => z (a, b)) = 0) :
    (fun _ => (1 : ℂ)) ∉ L ⊔ Z := by
  intro hmem
  obtain ⟨t, ht, z, hz, htz⟩ := Submodule.mem_sup.mp hmem
  let u : Fin n × Fin n → ℂ := -t
  have hu : u ∈ L := L.neg_mem ht
  have hz_eq : (Matrix.of fun a b => z (a, b)) = Matrix.of fun a b => (1 : ℂ) + u (a, b) := by
    ext a b
    have hpt := congrFun htz (a, b)
    simp only [Pi.add_apply] at hpt
    simp only [Matrix.of_apply, u, Pi.neg_apply]
    linear_combination hpt
  have hperm0 : Matrix.permanent (Matrix.of fun a b => (1 : ℂ) + u (a, b)) = 0 := by
    rw [← hz_eq]
    exact hZ z hz
  rw [perm_one_add] at hperm0
  have hsum_val :
      (∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) *
        ∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
          if h : R.card = k ∧ C.card = k then
            Matrix.permanent (Matrix.of fun a b => u (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
          else 0) = (n.factorial : ℂ) := by
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.sub_zero]
      have h0 :
          (∑ R : Finset (Fin n), ∑ C : Finset (Fin n),
            if h : R.card = 0 ∧ C.card = 0 then
              Matrix.permanent (Matrix.of fun a b => u (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
            else 0) = 1 := by
        rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
        · rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
          · rw [dif_pos ⟨Finset.card_empty, Finset.card_empty⟩]
            simp [Matrix.permanent]
          · intro C _ hCne
            rw [dif_neg (fun h => hCne (Finset.card_eq_zero.mp h.2))]
          · intro h; exact False.elim (h (Finset.mem_univ _))
        · intro R _ hRne
          refine Finset.sum_eq_zero fun C _ => ?_
          rw [dif_neg (fun h => hRne (Finset.card_eq_zero.mp h.1))]
        · intro h; exact False.elim (h (Finset.mem_univ _))
      rw [h0, mul_one]
    · intro k hk hk0
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [hL u hu k hk1 hkn, mul_zero]
    · intro h; exact False.elim (h (Finset.mem_range.mpr (Nat.zero_lt_succ n)))
  rw [hsum_val] at hperm0
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) hperm0

end PEqualNP.Outside.Gct205

theorem PEqualNP.Outside.L_gct_205 : ∀ n : ℕ, ∀ L Z : Submodule ℂ (Fin n × Fin n → ℂ), (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n → (∑ R : Finset (Fin n), ∑ C : Finset (Fin n), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) → (∀ z ∈ Z, Matrix.permanent (Matrix.of fun a b => z (a, b)) = 0) → (fun _ => (1 : ℂ)) ∉ L ⊔ Z :=
  PEqualNP.Outside.Gct205.main
