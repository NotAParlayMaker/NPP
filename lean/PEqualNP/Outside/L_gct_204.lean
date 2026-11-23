import Mathlib
import PEqualNP.Defs

open Finset

private noncomputable def rectPerm {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℂ) : ℂ := by
  classical
  exact ∑ f : B ≃ A, ∏ j, w (f j) j

private theorem rectChange {A B A' B' : Type*} [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (r : A ≃ A') (c : B ≃ B') (w : A' → B' → ℂ) :
    rectPerm (fun i j => w (r i) (c j)) = rectPerm w := by
  classical
  unfold rectPerm
  refine Fintype.sum_equiv (c.equivCongr r) _ _ fun f => ?_
  refine Fintype.prod_equiv c _ _ fun j => ?_
  simp

private theorem rectMinor {p q k : ℕ} (w : Fin p × Fin q → ℂ)
    (R : Finset (Fin p)) (C : Finset (Fin q)) (hr : R.card = k) (hc : C.card = k) :
    Matrix.permanent (Matrix.of fun a b => w (R.orderEmbOfFin hr a, C.orderEmbOfFin hc b)) =
    rectPerm (fun (i : R) (j : C) => w (i,j)) := by
  have e := rectChange (R.orderIsoOfFin hr).toEquiv (C.orderIsoOfFin hc).toEquiv
    (fun (i : R) (j : C) => w (i,j))
  rw [← e]
  simp only [Matrix.permanent, Matrix.of_apply, rectPerm]
  apply Finset.sum_congr (by ext σ; simp)
  intro σ _
  apply Finset.prod_congr rfl
  intro i _
  rfl

private theorem rectZero {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℂ) (h : Fintype.card A ≠ Fintype.card B) : rectPerm w = 0 := by
  classical
  let : IsEmpty (B ≃ A) := ⟨fun e => h (Fintype.card_congr e.symm)⟩
  simp [rectPerm]

private def blockEntry {A B D E : Type*} (w : A → B → ℂ) (z : D → E → ℂ) :
    A ⊕ D → B ⊕ E → ℂ
  | .inl i, .inl j => w i j
  | .inr i, .inr j => z i j
  | _, _ => 0

set_option maxHeartbeats 1500000 in
private theorem blockPerm {A B D E : Type*} [Fintype A] [Fintype B] [Fintype D] [Fintype E]
    (w : A → B → ℂ) (z : D → E → ℂ) :
    rectPerm (blockEntry w z) = rectPerm w * rectPerm z := by
  classical
  let : DecidableEq (B ⊕ E) := Classical.decEq _
  let : DecidableEq (A ⊕ D) := Classical.decEq _
  let embed : ((B ≃ A) × (E ≃ D)) → ((B ⊕ E) ≃ (A ⊕ D)) := fun p => p.1.sumCongr p.2
  have inj : Function.Injective embed := by
    rintro ⟨f,g⟩ ⟨f',g'⟩ h
    apply Prod.ext
    · ext b
      exact Sum.inl.inj (congrArg (fun e : _ ≃ _ => e (Sum.inl b)) h)
    · ext e
      exact Sum.inr.inj (congrArg (fun f : _ ≃ _ => f (Sum.inr e)) h)
  unfold rectPerm
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type (fun (fg : (B ≃ A) × (E ≃ D)) =>
    (∏ j, w (fg.1 j) j) * ∏ j, z (fg.2 j) j)]
  symm
  refine Fintype.sum_of_injective embed inj
    (fun fg => (∏ j, w (fg.1 j) j) * ∏ j, z (fg.2 j) j)
    (fun f => ∏ j, blockEntry w z (f j) j) ?_ ?_
  · intro f hnot
    by_contra hn
    have nz (j : B ⊕ E) : blockEntry w z (f j) j ≠ 0 := fun h => hn (Finset.prod_eq_zero (Finset.mem_univ j) h)
    have left (b : B) : ∃ a, f (.inl b) = .inl a := by
      cases h : f (.inl b) with
      | inl a => exact ⟨a,rfl⟩
      | inr d => exact False.elim (nz (.inl b) (by rw [h]; rfl))
    have right (e : E) : ∃ d, f (.inr e) = .inr d := by
      cases h : f (.inr e) with
      | inr d => exact ⟨d,rfl⟩
      | inl a => exact False.elim (nz (.inr e) (by rw [h]; rfl))
    choose g hg using left
    choose h hh using right
    have bg : Function.Bijective g := by
      constructor
      · intro x y hxy
        exact Sum.inl.inj (f.injective ((hg x).trans ((congrArg Sum.inl hxy).trans (hg y).symm)))
      · intro a
        obtain ⟨b | e, he⟩ := f.surjective (.inl a)
        · exact ⟨b, Sum.inl.inj ((hg b).symm.trans he)⟩
        · simp [hh e] at he
    have bh : Function.Bijective h := by
      constructor
      · intro x y hxy
        exact Sum.inr.inj (f.injective ((hh x).trans ((congrArg Sum.inr hxy).trans (hh y).symm)))
      · intro d
        obtain ⟨b | e, he⟩ := f.surjective (.inr d)
        · simp [hg b] at he
        · exact ⟨e, Sum.inr.inj ((hh e).symm.trans he)⟩
    apply hnot ⟨(Equiv.ofBijective g bg, Equiv.ofBijective h bh), ?_⟩
    ext (b | e)
    · exact (hg b).symm
    · exact (hh e).symm
  · rintro ⟨f,g⟩
    simp [embed,Fintype.prod_sum_type,blockEntry]

private noncomputable def rookPoly {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℂ) : Polynomial ℂ := by
  classical
  exact ∑ R : Finset A, ∑ C : Finset B, Polynomial.monomial R.card
    (rectPerm fun (i : R) (j : C) => w i j)

private noncomputable def minorTotal {p q : ℕ} (w : Fin p × Fin q → ℂ) (k : ℕ) : ℂ :=
  ∑ R : Finset (Fin p), ∑ C : Finset (Fin q), if h : R.card = k ∧ C.card = k then
    Matrix.permanent (Matrix.of fun a b => w (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b)) else 0

private theorem rookCoeff {p q : ℕ} (w : Fin p × Fin q → ℂ) (k : ℕ) :
    (rookPoly (fun i j => w (i,j))).coeff k = minorTotal w k := by
  classical
  simp only [rookPoly, minorTotal, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro R _
  apply Finset.sum_congr rfl
  intro C _
  by_cases hr : R.card = k
  · by_cases hc : C.card = k
    · simp [hr, hc, rectMinor]
    · have hn : Fintype.card R ≠ Fintype.card C := by simpa [hr] using Ne.symm hc
      simp [hr,hc,rectZero _ hn]
  · simp [hr]

private theorem rookConstant {p q : ℕ} (w : Fin p × Fin q → ℂ)
    (h : ∀ k, 1 ≤ k → k ≤ min p q → minorTotal w k = 0) :
    rookPoly (fun i j => w (i,j)) = Polynomial.C ((rookPoly (fun i j => w (i,j))).coeff 0) := by
  classical
  ext k
  by_cases hk : k = 0
  · subst k; simp
  rw [Polynomial.coeff_C_of_ne_zero hk, rookCoeff]
  by_cases hb : k ≤ min p q
  · exact h k (by omega) hb
  unfold minorTotal
  apply Finset.sum_eq_zero
  intro R _
  apply Finset.sum_eq_zero
  intro C _
  split_ifs with e
  · have hr : R.card ≤ p := by simpa using R.card_le_univ
    have hc : C.card ≤ q := by simpa using C.card_le_univ
    exact False.elim (hb (le_min (e.1 ▸ hr) (e.2 ▸ hc)))
  · rfl

private theorem rookChange {A B A' B' : Type*} [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (r : A ≃ A') (c : B ≃ B') (w : A' → B' → ℂ) :
    rookPoly (fun i j => w (r i) (c j)) = rookPoly w := by
  classical
  unfold rookPoly
  refine Fintype.sum_equiv r.finsetCongr _ _ fun R => ?_
  refine Fintype.sum_equiv c.finsetCongr _ _ fun C => ?_
  simp only [Equiv.finsetCongr_apply, Finset.card_map]
  congr 1
  exact rectChange (Finset.equivMap r.toEmbedding R) (Finset.equivMap c.toEmbedding C)
    (fun i j => w i j)

private def disjParts {A D : Type*} (s : Finset A) (t : Finset D) :
    (s ⊕ t) ≃ s.disjSum t where
  toFun
    | .inl a => ⟨.inl a.val, Finset.inl_mem_disjSum.mpr a.property⟩
    | .inr d => ⟨.inr d.val, Finset.inr_mem_disjSum.mpr d.property⟩
  invFun
    | ⟨.inl a, h⟩ => .inl ⟨a, Finset.inl_mem_disjSum.mp h⟩
    | ⟨.inr d, h⟩ => .inr ⟨d, Finset.inr_mem_disjSum.mp h⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨_ | _, h⟩ <;> rfl

private theorem blockMinor {A B D E : Type*} [Fintype A] [Fintype B] [Fintype D] [Fintype E]
    (w : A → B → ℂ) (z : D → E → ℂ) (r : Finset A) (c : Finset B)
    (s : Finset D) (t : Finset E) :
    rectPerm (fun (i : r.disjSum s) (j : c.disjSum t) => blockEntry w z i j) =
    (rectPerm fun (i : r) (j : c) => w i j) * (rectPerm fun (i : s) (j : t) => z i j) := by
  rw [← rectChange (disjParts r s) (disjParts c t)]
  rw [← blockPerm]
  congr 1
  funext i j
  cases i <;> cases j <;> rfl

private theorem rookBlock {A B D E : Type*} [Fintype A] [Fintype B] [Fintype D] [Fintype E]
    (w : A → B → ℂ) (z : D → E → ℂ) : rookPoly (blockEntry w z) = rookPoly w * rookPoly z := by
  classical
  unfold rookPoly
  let pack (rp : Finset A × Finset D) (cp : Finset B × Finset E) :=
    Polynomial.monomial (rp.1.card + rp.2.card) (
      (rectPerm fun (i : rp.1) (j : cp.1) => w i j) *
      (rectPerm fun (i : rp.2) (j : cp.2) => z i j))
  trans ∑ rp, ∑ cp, pack rp cp
  · refine (Fintype.sum_equiv Finset.sumEquiv.toEquiv.symm _ _ fun rp => ?_).symm
    refine Fintype.sum_equiv Finset.sumEquiv.toEquiv.symm _ _ fun cp => ?_
    change pack rp cp = Polynomial.monomial (rp.1.disjSum rp.2).card
      (rectPerm fun (i : rp.1.disjSum rp.2) (j : cp.1.disjSum cp.2) => blockEntry w z i j)
    rw [Finset.card_disjSum,blockMinor]
  · simp only [Fintype.sum_prod_type, pack, Finset.sum_mul_sum, Polynomial.monomial_mul_monomial]

theorem PEqualNP.Outside.L_gct_204 :
    ∀ p1 q1 p2 q2 : ℕ,
    ∀ L1 : Submodule ℂ (Fin p1 × Fin q1 → ℂ),
    ∀ L2 : Submodule ℂ (Fin p2 × Fin q2 → ℂ),
    (∀ t ∈ L1, ∀ k : ℕ, 1 ≤ k → k ≤ min p1 q1 →
      (∑ R : Finset (Fin p1), ∑ C : Finset (Fin q1), if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) →
    (∀ t ∈ L2, ∀ k : ℕ, 1 ≤ k → k ≤ min p2 q2 →
      (∑ R : Finset (Fin p2), ∑ C : Finset (Fin q2), if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) →
    ∀ t1 ∈ L1, ∀ t2 ∈ L2, ∀ T : Fin (p1 + p2) × Fin (q1 + q2) → ℂ,
    (∀ x, T x = Matrix.fromBlocks (Matrix.of fun a b => t1 (a, b)) 0 0 (Matrix.of fun a b => t2 (a, b)) (finSumFinEquiv.symm x.1) (finSumFinEquiv.symm x.2)) →
    ∀ k : ℕ, 1 ≤ k → k ≤ min (p1 + p2) (q1 + q2) →
      (∑ R : Finset (Fin (p1 + p2)), ∑ C : Finset (Fin (q1 + q2)), if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b => T (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0 := by
  intro p1 q1 p2 q2 L1 L2 h1 h2 t1 ht1 t2 ht2 T hT k hk _
  let w := fun i j => t1 (i,j)
  let z := fun i j => t2 (i,j)
  have hblock : (fun i j => T (i,j)) = fun i j =>
      blockEntry w z (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
    funext i j
    rw [hT (i,j)]
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> rfl
  change minorTotal T k = 0
  rw [← rookCoeff, hblock, rookChange finSumFinEquiv.symm finSumFinEquiv.symm, rookBlock]
  have hc1 := rookConstant t1 (h1 t1 ht1)
  have hc2 := rookConstant t2 (h2 t2 ht2)
  change (rookPoly w * rookPoly z).coeff k = 0
  change rookPoly w = _ at hc1
  change rookPoly z = _ at hc2
  rw [hc1, hc2, ← Polynomial.C_mul, Polynomial.coeff_C_of_ne_zero (by omega)]
