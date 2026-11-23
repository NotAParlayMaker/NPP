import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

private lemma sub_lt (m k : ℕ) (u v : Fin m) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) :
    m + 2 * k * (u.val * m + v.val) + (p - 1) < m + 2 * k * (m * m) := by
  have huv1 : u.val * m + v.val + 1 ≤ (u.val + 1) * m := by
    rw [Nat.add_mul, Nat.one_mul]
    have hv : v.val + 1 ≤ m := v.isLt
    omega
  have huv2 : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m u.isLt
  have huv : u.val * m + v.val + 1 ≤ m * m := Nat.le_trans huv1 huv2
  have hmul : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left (2 * k) huv
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

private def orig (m k : ℕ) (u : Fin m) : Fin (m + 2 * k * (m * m)) :=
  ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right m _)⟩

private lemma orig_inj (m k : ℕ) : Function.Injective (orig m k) := by
  intro u₁ u₂ h
  have hval : (orig m k u₁).val = (orig m k u₂).val := congrArg Fin.val h
  exact Fin.ext hval

private def pathNode (m k : ℕ) (u v : Fin m) (p : ℕ) : Fin (m + 2 * k * (m * m)) :=
  if p = 0 then orig m k u
  else if p = 2 * k + 1 then orig m k v
  else if h : 1 ≤ p ∧ p ≤ 2 * k then
    ⟨m + 2 * k * (u.val * m + v.val) + (p - 1), sub_lt m k u v p h.1 h.2⟩
  else orig m k u

private lemma pathNode_zero (m k : ℕ) (u v : Fin m) : pathNode m k u v 0 = orig m k u := by
  simp [pathNode]

private lemma pathNode_end (m k : ℕ) (u v : Fin m) : pathNode m k u v (2 * k + 1) = orig m k v := by
  simp [pathNode]

private lemma pathNode_mid_val (m k : ℕ) (u v : Fin m) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) :
    (pathNode m k u v p).val = m + 2 * k * (u.val * m + v.val) + (p - 1) := by
  have h0 : p ≠ 0 := by omega
  have h1 : p ≠ 2 * k + 1 := by omega
  simp [pathNode, h0, h1, hp1, hp2]

private lemma pathNode_inj (m k : ℕ) (u₁ v₁ u₂ v₂ : Fin m) (p₁ p₂ : ℕ)
    (hp₁1 : 1 ≤ p₁) (hp₁2 : p₁ ≤ 2 * k) (hp₂1 : 1 ≤ p₂) (hp₂2 : p₂ ≤ 2 * k)
    (h : pathNode m k u₁ v₁ p₁ = pathNode m k u₂ v₂ p₂) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ p₁ = p₂ := by
  have hval := congrArg Fin.val h
  rw [pathNode_mid_val m k u₁ v₁ p₁ hp₁1 hp₁2, pathNode_mid_val m k u₂ v₂ p₂ hp₂1 hp₂2] at hval
  have hq : u₁.val * m + v₁.val = u₂.val * m + v₂.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : 2 * k * (u₁.val * m + v₁.val + 1) ≤ 2 * k * (u₂.val * m + v₂.val) :=
        Nat.mul_le_mul_left (2 * k) hlt
      rw [Nat.mul_add, Nat.mul_one] at hle
      omega
    · have hle : 2 * k * (u₂.val * m + v₂.val + 1) ≤ 2 * k * (u₁.val * m + v₁.val) :=
        Nat.mul_le_mul_left (2 * k) hgt
      rw [Nat.mul_add, Nat.mul_one] at hle
      omega
  have hp : p₁ = p₂ := by
    rw [hq] at hval
    omega
  have hu : u₁.val = u₂.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (u₁.val + 1) * m ≤ u₂.val * m := Nat.mul_le_mul_right m hlt
      rw [Nat.add_mul, Nat.one_mul] at hle
      have hv₁ := v₁.isLt
      omega
    · have hle : (u₂.val + 1) * m ≤ u₁.val * m := Nat.mul_le_mul_right m hgt
      rw [Nat.add_mul, Nat.one_mul] at hle
      have hv₂ := v₂.isLt
      omega
  have hv : v₁.val = v₂.val := by
    rw [hu] at hq
    omega
  exact ⟨Fin.ext hu, Fin.ext hv, hp⟩

private lemma path_cover_even (P : ℕ → Prop) [DecidablePred P] :
    ∀ k : ℕ, (∀ p : ℕ, 1 ≤ p → p < 2 * k → P p ∨ P (p + 1)) →
      k ≤ ((Finset.Icc 1 (2 * k)).filter P).card := by
  intro k
  induction k with
  | zero =>
    intro _
    exact Nat.zero_le _
  | succ k ih =>
    intro hadj
    let S₁ := (Finset.Icc 1 (2 * k)).filter P
    let S₂ := ({2 * k + 1, 2 * k + 2} : Finset ℕ).filter P
    have hih : k ≤ S₁.card :=
      ih (fun p hp1 hp2 => hadj p hp1 (by omega))
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [S₁, S₂, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton] at hx1 hx2
      omega
    have hsub : S₁ ∪ S₂ ⊆ (Finset.Icc 1 (2 * (k + 1))).filter P := by
      intro x hx
      simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton] at hx ⊢
      rcases hx with ⟨⟨h1, h2⟩, hP⟩ | ⟨h2, hP⟩
      · exact ⟨⟨h1, by omega⟩, hP⟩
      · exact ⟨⟨by omega, by omega⟩, hP⟩
    have hS₂ : 1 ≤ S₂.card := by
      apply Finset.card_pos.mpr
      rcases hadj (2 * k + 1) (by omega) (by omega) with hP1 | hP2
      · refine ⟨2 * k + 1, ?_⟩
        simp [S₂, hP1]
      · refine ⟨2 * k + 2, ?_⟩
        simp [S₂, hP2]
    have hle : S₁.card + S₂.card ≤ ((Finset.Icc 1 (2 * (k + 1))).filter P).card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hsub
    omega

private lemma path_cover_both_ends (P : ℕ → Prop) [DecidablePred P] (k : ℕ) (hk : 1 ≤ k)
    (h1 : P 1) (h2k : P (2 * k))
    (hadj : ∀ p : ℕ, 1 ≤ p → p < 2 * k → P p ∨ P (p + 1)) :
    k + 1 ≤ ((Finset.Icc 1 (2 * k)).filter P).card := by
  let Ends : Finset ℕ := {1, 2 * k}
  let Mid : Finset ℕ := ((Finset.Icc 1 (2 * (k - 1))).filter (fun p => P (p + 1))).image (fun p => p + 1)
  have hEnds_card : Ends.card = 2 := by
    have hne : (1 : ℕ) ≠ 2 * k := by omega
    simp [Ends, hne]
  have hMid_card : k - 1 ≤ Mid.card := by
    rw [Finset.card_image_of_injective _ Nat.succ_injective]
    apply path_cover_even (fun p => P (p + 1)) (k - 1)
    intro p hp1 hp2
    exact hadj (p + 1) (by omega) (by omega)
  have hdisj : Disjoint Ends Mid := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Ends, Mid, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_filter, Finset.mem_Icc] at hx1 hx2
    rcases hx2 with ⟨p, ⟨⟨hp1, hp2⟩, _⟩, rfl⟩
    omega
  have hsub : Ends ∪ Mid ⊆ (Finset.Icc 1 (2 * k)).filter P := by
    intro x hx
    simp only [Ends, Mid, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    rcases hx with (rfl | rfl) | ⟨p, ⟨⟨hp1, hp2⟩, hP⟩, rfl⟩
    · exact ⟨⟨by omega, by omega⟩, h1⟩
    · exact ⟨⟨by omega, by omega⟩, h2k⟩
    · exact ⟨⟨by omega, by omega⟩, hP⟩
  have hle : Ends.card + Mid.card ≤ ((Finset.Icc 1 (2 * k)).filter P).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  omega

theorem PEqualNP.Outside.L_meta_470 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ c : ℕ, (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → c ≤ R.card) → ∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro m k H Q S hk hQ hS c hc U hU
  have hQ_path : ∀ (u v : Fin m) (p : ℕ), p ≤ 2 * k + 1 → Q u v p (pathNode m k u v p) := by
    intro u v p hp
    rw [hQ]
    by_cases h0 : p = 0
    · subst h0
      left
      exact ⟨rfl, by simp [pathNode_zero, orig]⟩
    · by_cases h1 : p = 2 * k + 1
      · subst h1
        right; left
        exact ⟨rfl, by simp [pathNode_end, orig]⟩
      · right; right
        have hp1 : 1 ≤ p := by omega
        have hp2 : p ≤ 2 * k := by omega
        refine ⟨hp1, hp2, ?_⟩
        rw [pathNode_mid_val m k u v p hp1 hp2]
        omega
  have hS_step : ∀ (u v : Fin m), u < v → H.Adj u v → ∀ p : ℕ, p ≤ 2 * k →
      pathNode m k u v p ∈ U ∨ pathNode m k u v (p + 1) ∈ U := by
    intro u v huv hadj p hp
    apply hU
    rw [hS]
    exact ⟨u, v, huv, hadj, p, hp, Or.inl ⟨hQ_path u v p (by omega), hQ_path u v (p + 1) (by omega)⟩⟩
  let E : Finset (Fin m × Fin m) := Finset.univ.filter (fun e => e.1 < e.2 ∧ H.Adj e.1 e.2)
  let U₀ : Finset (Fin m) := Finset.univ.filter (fun u => orig m k u ∈ U)
  let Ebad : Finset (Fin m × Fin m) := E.filter (fun e => e.1 ∉ U₀ ∧ e.2 ∉ U₀)
  let A₀ : Finset (Fin (m + 2 * k * (m * m))) := U₀.image (orig m k)
  let Ue : Fin m × Fin m → Finset (Fin (m + 2 * k * (m * m))) := fun e =>
    ((Finset.Icc 1 (2 * k)).filter (fun p => pathNode m k e.1 e.2 p ∈ U)).image (pathNode m k e.1 e.2)
  have hE_ncard : H.edgeSet.ncard = E.card := by
    let Esym : Finset (Sym2 (Fin m)) := E.image (fun e => s(e.1, e.2))
    have hEsym_card : Esym.card = E.card := by
      apply Finset.card_image_of_injOn
      intro e₁ he₁ e₂ he₂ heq
      simp only [Finset.mem_coe, E, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        have : e₁.1 < e₁.1 := lt_trans he₁.1 (h2 ▸ lt_of_le_of_lt (le_of_eq rfl) (h1 ▸ he₂.1))
        exact lt_irrefl _ this
    have hEsym_set : (Esym : Set (Sym2 (Fin m))) = H.edgeSet := by
      ext s
      induction s using Sym2.ind with
      | _ u v =>
        simp only [Finset.mem_coe, Esym, Finset.mem_image, E, Finset.mem_filter, Finset.mem_univ,
          true_and, SimpleGraph.mem_edgeSet]
        constructor
        · rintro ⟨⟨a, b⟩, ⟨_, hab⟩, heq⟩
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hab
          · exact (H.adj_comm _ _).mp hab
        · intro huv
          have hne : u ≠ v := H.ne_of_adj huv
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact ⟨(u, v), ⟨hlt, huv⟩, rfl⟩
          · exact ⟨(v, u), ⟨hgt, (H.adj_comm _ _).mp huv⟩, Sym2.eq_swap⟩
    rw [← hEsym_set, Set.ncard_coe_finset, hEsym_card]
  have hR_card : c ≤ U₀.card + Ebad.card := by
    let R : Finset (Fin m) := U₀ ∪ Ebad.image Prod.fst
    have hR_cover : ∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R := by
      intro u v huv
      by_cases hu : u ∈ U₀
      · exact Or.inl (Finset.mem_union_left _ hu)
      · by_cases hv : v ∈ U₀
        · exact Or.inr (Finset.mem_union_left _ hv)
        · have hne : u ≠ v := H.ne_of_adj huv
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · left
            apply Finset.mem_union_right
            exact Finset.mem_image.mpr ⟨(u, v), by simp [Ebad, E, hlt, huv, hu, hv], rfl⟩
          · right
            apply Finset.mem_union_right
            exact Finset.mem_image.mpr ⟨(v, u), by simp [Ebad, E, hgt, (H.adj_comm _ _).mp huv, hu, hv], rfl⟩
    have hcR : c ≤ R.card := hc R hR_cover
    have hRle : R.card ≤ U₀.card + (Ebad.image Prod.fst).card := Finset.card_union_le _ _
    have himgle : (Ebad.image Prod.fst).card ≤ Ebad.card := Finset.card_image_le
    omega
  have hA₀_sub : A₀ ⊆ U := by
    intro x hx
    simp only [A₀, U₀, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨u, hu, rfl⟩
    exact hu
  have hUe_sub : E.biUnion Ue ⊆ U := by
    intro x hx
    simp only [Finset.mem_biUnion, Ue, Finset.mem_image, Finset.mem_filter] at hx
    rcases hx with ⟨e, _, p, ⟨_, hpU⟩, rfl⟩
    exact hpU
  have hA₀_disj : Disjoint A₀ (E.biUnion Ue) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [A₀, Finset.mem_image] at hx1
    simp only [Finset.mem_biUnion, Ue, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hx2
    rcases hx1 with ⟨u, _, rfl⟩
    rcases hx2 with ⟨e, _, p, ⟨⟨hp1, hp2⟩, _⟩, hxeq⟩
    have hval := congrArg Fin.val hxeq
    rw [pathNode_mid_val m k e.1 e.2 p hp1 hp2] at hval
    have hu : (orig m k u).val < m := u.isLt
    omega
  have hUe_disj : (E : Set (Fin m × Fin m)).PairwiseDisjoint Ue := by
    intro e₁ _ e₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Ue, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hx1 hx2
    rcases hx1 with ⟨p₁, ⟨⟨hp₁1, hp₁2⟩, _⟩, rfl⟩
    rcases hx2 with ⟨p₂, ⟨⟨hp₂1, hp₂2⟩, _⟩, hxeq⟩
    have ⟨h1, h2, _⟩ := pathNode_inj m k e₂.1 e₂.2 e₁.1 e₁.2 p₂ p₁ hp₂1 hp₂2 hp₁1 hp₁2 hxeq
    exact hne (Prod.ext h1.symm h2.symm)
  have hU_ge : U₀.card + ∑ e ∈ E, (Ue e).card ≤ U.card := by
    have h1 : A₀.card + (E.biUnion Ue).card ≤ U.card := by
      rw [← Finset.card_union_of_disjoint hA₀_disj]
      exact Finset.card_le_card (Finset.union_subset hA₀_sub hUe_sub)
    have h2 : A₀.card = U₀.card := Finset.card_image_of_injective _ (orig_inj m k)
    have h3 : (E.biUnion Ue).card = ∑ e ∈ E, (Ue e).card := Finset.card_biUnion hUe_disj
    omega
  have hUe_lb : ∀ e ∈ E, k + (if e ∈ Ebad then 1 else 0) ≤ (Ue e).card := by
    intro e he
    have hUe_card : (Ue e).card = ((Finset.Icc 1 (2 * k)).filter (fun p => pathNode m k e.1 e.2 p ∈ U)).card := by
      apply Finset.card_image_of_injOn
      intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
      exact (pathNode_inj m k e.1 e.2 e.1 e.2 p₁ p₂ hp₁.1.1 hp₁.1.2 hp₂.1.1 hp₂.1.2 heq).2.2
    rw [hUe_card]
    have he' : e.1 < e.2 ∧ H.Adj e.1 e.2 := by
      simpa [E] using he
    have hadj_path : ∀ p : ℕ, 1 ≤ p → p < 2 * k →
        pathNode m k e.1 e.2 p ∈ U ∨ pathNode m k e.1 e.2 (p + 1) ∈ U := by
      intro p hp1 hp2
      exact hS_step e.1 e.2 he'.1 he'.2 p (by omega)
    by_cases hbad : e ∈ Ebad
    · simp only [hbad, ite_true]
      have hbad' : e.1 ∉ U₀ ∧ e.2 ∉ U₀ := (Finset.mem_filter.mp hbad).2
      have h0 : orig m k e.1 ∉ U := by
        intro hmem
        exact hbad'.1 (by simp [U₀, hmem])
      have hend : orig m k e.2 ∉ U := by
        intro hmem
        exact hbad'.2 (by simp [U₀, hmem])
      have hp1 : pathNode m k e.1 e.2 1 ∈ U := by
        rcases hS_step e.1 e.2 he'.1 he'.2 0 (by omega) with hL | hR
        · rw [pathNode_zero] at hL
          exact False.elim (h0 hL)
        · exact hR
      have hp2k : pathNode m k e.1 e.2 (2 * k) ∈ U := by
        rcases hS_step e.1 e.2 he'.1 he'.2 (2 * k) (le_refl _) with hL | hR
        · exact hL
        · rw [pathNode_end] at hR
          exact False.elim (hend hR)
      exact path_cover_both_ends (fun p => pathNode m k e.1 e.2 p ∈ U) k hk hp1 hp2k hadj_path
    · simp only [hbad, ite_false, Nat.add_zero]
      exact path_cover_even (fun p => pathNode m k e.1 e.2 p ∈ U) k hadj_path
  have hsum : k * E.card + Ebad.card ≤ ∑ e ∈ E, (Ue e).card := by
    have h1 : ∑ e ∈ E, (k + (if e ∈ Ebad then 1 else 0)) ≤ ∑ e ∈ E, (Ue e).card :=
      Finset.sum_le_sum hUe_lb
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole] at h1
    have hfilt : E.filter (fun e => e ∈ Ebad) = Ebad := by
      ext e
      simp only [Finset.mem_filter, Ebad, and_iff_right_iff_imp]
      exact fun h => h.1
    rw [hfilt, Nat.cast_id] at h1
    rw [Nat.mul_comm]
    exact h1
  rw [hE_ncard]
  omega
