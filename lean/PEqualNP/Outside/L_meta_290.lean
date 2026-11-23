import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_290_aux

open Finset

private def origVert (k m : ℕ) (w : Fin m) : Fin (m + 2 * k * m * m) :=
  ⟨w.val, by omega⟩

private lemma subVert_lt (k m : ℕ) (u v : Fin m) (i : Fin (2 * k)) :
    m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
  have hu : u.val + 1 ≤ m := u.isLt
  have hv : v.val + 1 ≤ m := v.isLt
  have h1 : u.val * m + v.val + 1 ≤ m * m := by nlinarith
  have h2 : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
    Nat.mul_le_mul_left (2 * k) h1
  have hi : i.val < 2 * k := i.isLt
  nlinarith

private def subVert (k m : ℕ) (u v : Fin m) (i : Fin (2 * k)) : Fin (m + 2 * k * m * m) :=
  ⟨m + 2 * k * (u.val * m + v.val) + i.val, subVert_lt k m u v i⟩

private lemma origVert_inj (k m : ℕ) : Function.Injective (origVert k m) := by
  intro a b h
  have hv := congrArg Fin.val h
  exact Fin.ext hv

private lemma origVert_ne_subVert (k m : ℕ) (w u v : Fin m) (i : Fin (2 * k)) :
    origVert k m w ≠ subVert k m u v i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [origVert, subVert] at hv
  have hw := w.isLt
  omega

private lemma subVert_inj (k m : ℕ) (u₁ v₁ u₂ v₂ : Fin m) (i₁ i₂ : Fin (2 * k))
    (h : subVert k m u₁ v₁ i₁ = subVert k m u₂ v₂ i₂) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ i₁ = i₂ := by
  have hv : 2 * k * (u₁.val * m + v₁.val) + i₁.val = 2 * k * (u₂.val * m + v₂.val) + i₂.val := by
    have := congrArg Fin.val h
    simp only [subVert] at this
    omega
  have hi₁ := i₁.isLt
  have hi₂ := i₂.isLt
  have hq : u₁.val * m + v₁.val = u₂.val * m + v₂.val := by
    rcases lt_trichotomy (u₁.val * m + v₁.val) (u₂.val * m + v₂.val) with hlt | heq | hgt
    · nlinarith
    · exact heq
    · nlinarith
  have hi : i₁ = i₂ := Fin.ext (by nlinarith)
  have hv₁ := v₁.isLt
  have hv₂ := v₂.isLt
  have hu : u₁ = u₂ := by
    apply Fin.ext
    rcases lt_trichotomy u₁.val u₂.val with hlt | heq | hgt
    · nlinarith
    · exact heq
    · nlinarith
  have hv' : v₁ = v₂ := Fin.ext (by rw [congrArg Fin.val hu] at hq; omega)
  exact ⟨hu, hv', hi⟩

private lemma cover_even_pairs (k : ℕ) (I : Finset (Fin (2 * k)))
    (h : ∀ r : Fin k, (⟨2 * r.val, by omega⟩ : Fin (2 * k)) ∈ I ∨
      (⟨2 * r.val + 1, by omega⟩ : Fin (2 * k)) ∈ I) :
    k ≤ I.card := by
  classical
  let f : Fin k → Fin (2 * k) := fun r =>
    if (⟨2 * r.val, by omega⟩ : Fin (2 * k)) ∈ I then ⟨2 * r.val, by omega⟩
    else ⟨2 * r.val + 1, by omega⟩
  have hmem : ∀ r : Fin k, f r ∈ I := by
    intro r
    dsimp only [f]
    split_ifs with hr
    · exact hr
    · exact (h r).resolve_left hr
  have hinj : Function.Injective f := by
    intro r₁ r₂ heq
    have hval := congrArg Fin.val heq
    have h1 : (f r₁).val / 2 = r₁.val := by
      dsimp only [f]; split_ifs <;> (dsimp; omega)
    have h2 : (f r₂).val / 2 = r₂.val := by
      dsimp only [f]; split_ifs <;> (dsimp; omega)
    exact Fin.ext (by omega)
  have hsub : Finset.univ.image f ⊆ I := by
    intro x hx
    obtain ⟨r, -, rfl⟩ := mem_image.1 hx
    exact hmem r
  calc k = (Finset.univ : Finset (Fin k)).card := by simp
    _ = (Finset.univ.image f).card := (card_image_of_injective _ hinj).symm
    _ ≤ I.card := card_le_card hsub

private lemma cover_odd_pairs_ends (k : ℕ) (hk : 1 ≤ k) (I : Finset (Fin (2 * k)))
    (h0 : (⟨0, by omega⟩ : Fin (2 * k)) ∈ I)
    (hlast : (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) ∈ I)
    (hmid : ∀ r : Fin (k - 1), (⟨2 * r.val + 1, by omega⟩ : Fin (2 * k)) ∈ I ∨
      (⟨2 * r.val + 2, by omega⟩ : Fin (2 * k)) ∈ I) :
    k + 1 ≤ I.card := by
  classical
  let g : Fin (k + 1) → Fin (2 * k) := fun r =>
    if h0' : r.val = 0 then ⟨0, by omega⟩
    else if hk' : r.val = k then ⟨2 * k - 1, by omega⟩
    else if (⟨2 * (r.val - 1) + 1, by omega⟩ : Fin (2 * k)) ∈ I then
      ⟨2 * (r.val - 1) + 1, by omega⟩
    else ⟨2 * (r.val - 1) + 2, by omega⟩
  have hmem : ∀ r : Fin (k + 1), g r ∈ I := by
    intro r
    dsimp only [g]
    split_ifs with h0' hk' hm
    · exact h0
    · exact hlast
    · exact hm
    · have hr : r.val - 1 < k - 1 := by omega
      exact (hmid ⟨r.val - 1, hr⟩).resolve_left hm
  have hinj : Function.Injective g := by
    intro r₁ r₂ heq
    have hval := congrArg Fin.val heq
    have h1 : ((g r₁).val + 1) / 2 = r₁.val := by
      dsimp only [g]; split_ifs <;> (dsimp; omega)
    have h2 : ((g r₂).val + 1) / 2 = r₂.val := by
      dsimp only [g]; split_ifs <;> (dsimp; omega)
    exact Fin.ext (by omega)
  have hsub : Finset.univ.image g ⊆ I := by
    intro x hx
    obtain ⟨r, -, rfl⟩ := mem_image.1 hx
    exact hmem r
  calc k + 1 = (Finset.univ : Finset (Fin (k + 1))).card := by simp
    _ = (Finset.univ.image g).card := (card_image_of_injective _ hinj).symm
    _ ≤ I.card := card_le_card hsub

private lemma edge_lt_card_eq_ncard (m : ℕ) (H : SimpleGraph (Fin m))
    [DecidablePred (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)] :
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)).card =
      H.edgeSet.ncard := by
  classical
  let E : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  have hnc : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hnc]
  have himg : E.image (fun p => s(p.1, p.2)) = H.edgeFinset := by
    ext e
    simp only [mem_image, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeFinset, E]
    induction e using Sym2.ind with
    | _ a b =>
      constructor
      · rintro ⟨⟨u, v⟩, ⟨-, hadj⟩, heq⟩
        rw [← heq]
        exact hadj
      · intro hadj
        have hne : a ≠ b := H.ne_of_adj hadj
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ⟨(a, b), ⟨hlt, hadj⟩, rfl⟩
        · exact ⟨(b, a), ⟨hgt, (SimpleGraph.adj_comm H _ _).1 hadj⟩, Sym2.eq_swap⟩
  have hinj : Set.InjOn (fun p : Fin m × Fin m => s(p.1, p.2)) (E : Set (Fin m × Fin m)) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 : p₁.1 < p₁.2 := (mem_filter.1 hp₁).2.1
    have h2 : p₂.1 < p₂.2 := (mem_filter.1 hp₂).2.1
    rcases Sym2.eq_iff.1 heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Prod.ext ha hb
    · exfalso
      have := lt_trans (ha ▸ h1) (hb ▸ h2)
      exact lt_irrefl _ this
  rw [← himg, card_image_of_injOn hinj]

theorem cover_shift :
    ∀ (k m c : ℕ) (H : SimpleGraph (Fin m)),
      1 ≤ k →
      (∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → c ≤ T.card) →
      ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
        S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
            x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
            ((i.val = 0 ∧ y.val = u.val) ∨
             (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
             (i.val + 1 = 2 * k ∧ y.val = v.val))) →
      ∀ U : Finset (Fin (m + 2 * k * m * m)),
        (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) →
        c + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro k m c H hk hcover S hS U hU
  subst hS
  let E : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  let U0 : Finset (Fin m) := Finset.univ.filter (fun w => origVert k m w ∈ U)
  let Eunc : Finset (Fin m × Fin m) := E.filter (fun p => p.1 ∉ U0 ∧ p.2 ∉ U0)
  let Iblock : Fin m × Fin m → Finset (Fin (2 * k)) := fun p =>
    Finset.univ.filter (fun i : Fin (2 * k) => subVert k m p.1 p.2 i ∈ U)
  let Uorig : Finset (Fin (m + 2 * k * m * m)) := U0.image (origVert k m)
  let Uedge : Fin m × Fin m → Finset (Fin (m + 2 * k * m * m)) := fun p =>
    (Iblock p).image (subVert k m p.1 p.2)
  have hadj_zero : ∀ p ∈ E,
      (SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
        ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
          x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
          ((i.val = 0 ∧ y.val = u.val) ∨
           (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
           (i.val + 1 = 2 * k ∧ y.val = v.val)))).Adj
        (subVert k m p.1 p.2 ⟨0, by omega⟩) (origVert k m p.1) := by
    intro p hp
    have ⟨hlt, hadj⟩ := (mem_filter.1 hp).2
    rw [SimpleGraph.fromRel_adj]
    refine ⟨(origVert_ne_subVert k m p.1 p.1 p.2 ⟨0, by omega⟩).symm, Or.inl ?_⟩
    exact ⟨p.1, p.2, hlt, hadj, ⟨0, by omega⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
  have hadj_last : ∀ p ∈ E,
      (SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
        ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
          x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
          ((i.val = 0 ∧ y.val = u.val) ∨
           (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
           (i.val + 1 = 2 * k ∧ y.val = v.val)))).Adj
        (subVert k m p.1 p.2 ⟨2 * k - 1, by omega⟩) (origVert k m p.2) := by
    intro p hp
    have ⟨hlt, hadj⟩ := (mem_filter.1 hp).2
    rw [SimpleGraph.fromRel_adj]
    refine ⟨(origVert_ne_subVert k m p.2 p.1 p.2 ⟨2 * k - 1, by omega⟩).symm, Or.inl ?_⟩
    exact ⟨p.1, p.2, hlt, hadj, ⟨2 * k - 1, by omega⟩, rfl, Or.inr (Or.inr ⟨by dsimp; omega, rfl⟩)⟩
  have hadj_step : ∀ p ∈ E, ∀ (i : ℕ) (hi : i + 1 < 2 * k),
      (SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
        ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
          x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
          ((i.val = 0 ∧ y.val = u.val) ∨
           (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
           (i.val + 1 = 2 * k ∧ y.val = v.val)))).Adj
        (subVert k m p.1 p.2 ⟨i, by omega⟩) (subVert k m p.1 p.2 ⟨i + 1, by omega⟩) := by
    intro p hp i hi
    have ⟨hlt, hadj⟩ := (mem_filter.1 hp).2
    rw [SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      simp only [subVert] at hv
      omega
    · refine ⟨p.1, p.2, hlt, hadj, ⟨i, by omega⟩, rfl, Or.inr (Or.inl ⟨hi, ?_⟩)⟩
      simp only [subVert]
      omega
  have hblock_ge_k : ∀ p ∈ E, k ≤ (Iblock p).card := by
    intro p hp
    apply cover_even_pairs k (Iblock p)
    intro r
    have hcov := hU _ _ (hadj_step p hp (2 * r.val) (by omega))
    rcases hcov with h1 | h2
    · left; exact mem_filter.2 ⟨mem_univ _, h1⟩
    · right; exact mem_filter.2 ⟨mem_univ _, h2⟩
  have hblock_ge_k1 : ∀ p ∈ Eunc, k + 1 ≤ (Iblock p).card := by
    intro p hp
    have hpE : p ∈ E := (mem_filter.1 hp).1
    have ⟨hp1, hp2⟩ := (mem_filter.1 hp).2
    have h1not : origVert k m p.1 ∉ U := fun hm => hp1 (mem_filter.2 ⟨mem_univ _, hm⟩)
    have h2not : origVert k m p.2 ∉ U := fun hm => hp2 (mem_filter.2 ⟨mem_univ _, hm⟩)
    apply cover_odd_pairs_ends k hk (Iblock p)
    · have := (hU _ _ (hadj_zero p hpE)).resolve_right h1not
      exact mem_filter.2 ⟨mem_univ _, this⟩
    · have := (hU _ _ (hadj_last p hpE)).resolve_right h2not
      exact mem_filter.2 ⟨mem_univ _, this⟩
    · intro r
      have hcov := hU _ _ (hadj_step p hpE (2 * r.val + 1) (by omega))
      rcases hcov with h1 | h2
      · left; exact mem_filter.2 ⟨mem_univ _, h1⟩
      · right; exact mem_filter.2 ⟨mem_univ _, h2⟩
  have hUorig_card : Uorig.card = U0.card :=
    card_image_of_injective U0 (origVert_inj k m)
  have hUedge_card : ∀ p, (Uedge p).card = (Iblock p).card := by
    intro p
    refine card_image_of_injective (Iblock p) ?_
    intro i₁ i₂ heq
    exact (subVert_inj k m p.1 p.2 p.1 p.2 i₁ i₂ heq).2.2
  have hpw : (E : Set (Fin m × Fin m)).PairwiseDisjoint Uedge := by
    intro p₁ _ p₂ _ hne
    change Disjoint (Uedge p₁) (Uedge p₂)
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨i₁, -, rfl⟩ := mem_image.1 hx₁
    obtain ⟨i₂, -, heq⟩ := mem_image.1 hx₂
    obtain ⟨hu, hv, -⟩ := subVert_inj k m p₂.1 p₂.2 p₁.1 p₁.2 i₂ i₁ heq
    exact hne (Prod.ext hu.symm hv.symm)
  have hdisj : Disjoint Uorig (E.biUnion Uedge) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨w, -, rfl⟩ := mem_image.1 hx1
    obtain ⟨p, -, hxp⟩ := mem_biUnion.1 hx2
    obtain ⟨i, -, heq⟩ := mem_image.1 hxp
    exact origVert_ne_subVert k m w p.1 p.2 i heq.symm
  have hsubU : Uorig ∪ E.biUnion Uedge ⊆ U := by
    intro x hx
    rcases mem_union.1 hx with h1 | h2
    · obtain ⟨w, hw, rfl⟩ := mem_image.1 h1
      exact (mem_filter.1 hw).2
    · obtain ⟨p, -, hxp⟩ := mem_biUnion.1 h2
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hxp
      exact (mem_filter.1 hi).2
  have hU_ge : U0.card + ∑ p ∈ E, (Iblock p).card ≤ U.card := by
    have h1 : (Uorig ∪ E.biUnion Uedge).card ≤ U.card := card_le_card hsubU
    rw [card_union_of_disjoint hdisj, card_biUnion hpw, hUorig_card] at h1
    simpa only [hUedge_card] using h1
  have hsum_ge : k * E.card + Eunc.card ≤ ∑ p ∈ E, (Iblock p).card := by
    have hpt : ∀ p ∈ E, k + (if p ∈ Eunc then 1 else 0) ≤ (Iblock p).card := by
      intro p hp
      split_ifs with hu
      · exact hblock_ge_k1 p hu
      · simpa using hblock_ge_k p hp
    have hs := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm E.card k] at hs
    have hfilt : ∑ p ∈ E, (if p ∈ Eunc then 1 else 0) = Eunc.card := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      ext p
      simp only [mem_filter, Eunc, and_iff_right_iff_imp]
      intro hp
      exact hp.1
    rw [hfilt] at hs
    exact hs
  let T : Finset (Fin m) := U0 ∪ Eunc.image Prod.fst
  have hTcov : ∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v hadj
    have hne : u ≠ v := H.ne_of_adj hadj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · by_cases hu : u ∈ U0
      · exact Or.inl (mem_union_left _ hu)
      · by_cases hv : v ∈ U0
        · exact Or.inr (mem_union_left _ hv)
        · left
          refine mem_union_right _ (mem_image.2 ⟨(u, v), ?_, rfl⟩)
          exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hlt, hadj⟩, hu, hv⟩
    · by_cases hv : v ∈ U0
      · exact Or.inr (mem_union_left _ hv)
      · by_cases hu : u ∈ U0
        · exact Or.inl (mem_union_left _ hu)
        · right
          refine mem_union_right _ (mem_image.2 ⟨(v, u), ?_, rfl⟩)
          exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hgt, (SimpleGraph.adj_comm H _ _).1 hadj⟩, hv, hu⟩
  have hcT : c ≤ T.card := hcover T hTcov
  have hTle : T.card ≤ U0.card + Eunc.card := by
    calc T.card ≤ U0.card + (Eunc.image Prod.fst).card := card_union_le _ _
      _ ≤ U0.card + Eunc.card := Nat.add_le_add_left card_image_le _
  have hEcard : E.card = H.edgeSet.ncard := edge_lt_card_eq_ncard m H
  rw [← hEcard]
  omega

end PEqualNP.Outside.L_meta_290_aux

theorem PEqualNP.Outside.L_meta_290 : ∀ (k m c : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → (∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → c ≤ T.card) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card :=
  PEqualNP.Outside.L_meta_290_aux.cover_shift
