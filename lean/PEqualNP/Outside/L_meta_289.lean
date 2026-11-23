import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta289

private def orig (k m : ℕ) (u : Fin m) : Fin (m + 2 * k * m * m) :=
  ⟨u.val, by omega⟩

private lemma subdiv_lt (k m : ℕ) (u v : Fin m) (i : Fin (2 * k)) :
    m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
  have huv : u.val * m + v.val + 1 ≤ m * m := by
    have hu : u.val + 1 ≤ m := u.isLt
    have hv : v.val < m := v.isLt
    have hmul : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m hu
    nlinarith
  have h1 : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) :=
    Nat.mul_le_mul_left (2 * k) huv
  have h2 : 2 * k * (m * m) = 2 * k * m * m := (Nat.mul_assoc (2 * k) m m).symm
  have hi : i.val < 2 * k := i.isLt
  nlinarith

private def subdiv (k m : ℕ) (u v : Fin m) (i : Fin (2 * k)) : Fin (m + 2 * k * m * m) :=
  ⟨m + 2 * k * (u.val * m + v.val) + i.val, subdiv_lt k m u v i⟩

private lemma subdiv_inj {k m : ℕ} {u₁ v₁ u₂ v₂ : Fin m} {i₁ i₂ : Fin (2 * k)}
    (h : subdiv k m u₁ v₁ i₁ = subdiv k m u₂ v₂ i₂) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ i₁ = i₂ := by
  have hval : m + 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      m + 2 * k * (u₂.val * m + v₂.val) + i₂.val := congrArg Fin.val h
  have h1 : 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      2 * k * (u₂.val * m + v₂.val) + i₂.val := by omega
  have hk : 0 < 2 * k := Nat.zero_lt_of_lt i₁.isLt
  have hi_eq : i₁.val = i₂.val := by
    have hmod := congrArg (· % (2 * k)) h1
    simp [Nat.mod_eq_of_lt i₁.isLt, Nat.mod_eq_of_lt i₂.isLt] at hmod
    exact hmod
  have huv_eq : u₁.val * m + v₁.val = u₂.val * m + v₂.val := by
    have h2 : 2 * k * (u₁.val * m + v₁.val) = 2 * k * (u₂.val * m + v₂.val) := by omega
    exact Nat.eq_of_mul_eq_mul_left hk h2
  have hm : 0 < m := Nat.zero_lt_of_lt u₁.isLt
  have hv_eq : v₁.val = v₂.val := by
    have hmod := congrArg (· % m) huv_eq
    simp [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt v₁.isLt, Nat.mod_eq_of_lt v₂.isLt] at hmod
    exact hmod
  have hu_eq : u₁.val = u₂.val := by
    have h3 : u₁.val * m = u₂.val * m := by omega
    exact Nat.eq_of_mul_eq_mul_right hm h3
  exact ⟨Fin.ext hu_eq, Fin.ext hv_eq, Fin.ext hi_eq⟩

private lemma path_cover_ge_k {k : ℕ} (P : Fin (2 * k) → Prop) [DecidablePred P]
    (hadj : ∀ i : Fin (2 * k), (h : i.val + 1 < 2 * k) → P i ∨ P ⟨i.val + 1, h⟩) :
    k ≤ (Finset.univ.filter P).card := by
  let f : Fin k → Fin (2 * k) := fun j =>
    if P ⟨2 * j.val, by omega⟩ then ⟨2 * j.val, by omega⟩ else ⟨2 * j.val + 1, by omega⟩
  have hf_mem : ∀ j ∈ (Finset.univ : Finset (Fin k)), f j ∈ Finset.univ.filter P := by
    intro j _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [f]
    split_ifs with hP
    · exact hP
    · have hstep := hadj ⟨2 * j.val, by omega⟩ (by dsimp only; omega)
      exact hstep.resolve_left hP
  have hf_inj : Set.InjOn f (Finset.univ : Finset (Fin k)) := by
    intro j₁ _ j₂ _ hEq
    have hv : (f j₁).val = (f j₂).val := congrArg Fin.val hEq
    have h1 : (f j₁).val / 2 = j₁.val := by
      dsimp only [f]
      split_ifs <;> dsimp only <;> omega
    have h2 : (f j₂).val / 2 = j₂.val := by
      dsimp only [f]
      split_ifs <;> dsimp only <;> omega
    exact Fin.ext (by omega)
  simpa [Finset.card_fin] using Finset.card_le_card_of_injOn f hf_mem hf_inj

private lemma path_cover_ge_k_add_one {k : ℕ} (hk : 1 ≤ k)
    (P : Fin (2 * k) → Prop) [DecidablePred P]
    (hadj : ∀ i : Fin (2 * k), (h : i.val + 1 < 2 * k) → P i ∨ P ⟨i.val + 1, h⟩)
    (h0 : P ⟨0, by omega⟩) (hlast : P ⟨2 * k - 1, by omega⟩) :
    k + 1 ≤ (Finset.univ.filter P).card := by
  let f : Fin (k + 1) → Fin (2 * k) := fun j =>
    if h0j : j.val = 0 then ⟨0, by omega⟩
    else if hkj : j.val = k then ⟨2 * k - 1, by omega⟩
    else if P ⟨2 * j.val - 1, by omega⟩ then ⟨2 * j.val - 1, by omega⟩
    else ⟨2 * j.val, by omega⟩
  have hf_mem : ∀ j ∈ (Finset.univ : Finset (Fin (k + 1))), f j ∈ Finset.univ.filter P := by
    intro j _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [f]
    split_ifs with h0j hkj hP
    · exact h0
    · exact hlast
    · exact hP
    · have hstep := hadj ⟨2 * j.val - 1, by omega⟩ (by dsimp only; omega)
      have hnext :
          (⟨(⟨2 * j.val - 1, by omega⟩ : Fin (2 * k)).val + 1, by dsimp only; omega⟩ : Fin (2 * k)) =
          ⟨2 * j.val, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hnext] at hstep
      exact hstep.resolve_left hP
  have hf_inj : Set.InjOn f (Finset.univ : Finset (Fin (k + 1))) := by
    intro j₁ _ j₂ _ hEq
    have hv : (f j₁).val = (f j₂).val := congrArg Fin.val hEq
    have h1 : ((f j₁).val + 1) / 2 = j₁.val := by
      dsimp only [f]
      split_ifs <;> dsimp only <;> omega
    have h2 : ((f j₂).val + 1) / 2 = j₂.val := by
      dsimp only [f]
      split_ifs <;> dsimp only <;> omega
    exact Fin.ext (by omega)
  simpa [Finset.card_fin] using Finset.card_le_card_of_injOn f hf_mem hf_inj

private lemma edgeSet_ncard_eq_ordered {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    H.edgeSet.ncard =
      (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)).card := by
  let E : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)
  let g : Fin m × Fin m → Sym2 (Fin m) := fun p => s(p.1, p.2)
  have himg : (E.image g : Set (Sym2 (Fin m))) = H.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_coe, Finset.mem_image, E, Finset.mem_filter, Finset.mem_univ,
        true_and, g, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨⟨u, v⟩, ⟨_, huv⟩, hEq⟩
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact huv
        · exact huv.symm
      · intro hab
        rcases lt_or_gt_of_ne hab.ne with hlt | hgt
        · exact ⟨(a, b), ⟨hlt, hab⟩, rfl⟩
        · exact ⟨(b, a), ⟨hgt, hab.symm⟩, Sym2.eq_swap⟩
  have hinj : Set.InjOn g (E : Set (Fin m × Fin m)) := by
    rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ hEq
    simp only [Finset.mem_coe, E, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    simp only [g, Sym2.eq_iff] at hEq
    rcases hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd (lt_trans h₁.1 h₂.1) (lt_irrefl _)
  rw [← himg, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

end PEqualNP.Outside.Meta289

open PEqualNP.Outside.Meta289 in
theorem PEqualNP.Outside.L_meta_289 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → ∀ R : Finset (Fin m), (∀ u : Fin m, u ∈ R ↔ (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧ (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val)) → (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧ R.card + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro k m H hk S hS U hU R hR
  constructor
  · intro u v huv
    rcases lt_or_gt_of_ne huv.ne with hlt | hgt
    · by_cases hu : ∃ x ∈ U, x.val = u.val
      · exact Or.inl ((hR u).mpr (Or.inl hu))
      · by_cases hv : ∃ x ∈ U, x.val = v.val
        · exact Or.inr ((hR v).mpr (Or.inl hv))
        · push Not at hu hv
          exact Or.inl ((hR u).mpr (Or.inr ⟨v, hlt, huv, hu, hv⟩))
    · by_cases hv : ∃ x ∈ U, x.val = v.val
      · exact Or.inr ((hR v).mpr (Or.inl hv))
      · by_cases hu : ∃ x ∈ U, x.val = u.val
        · exact Or.inl ((hR u).mpr (Or.inl hu))
        · push Not at hu hv
          exact Or.inr ((hR v).mpr (Or.inr ⟨u, hgt, huv.symm, hv, hu⟩))
  · let E : Finset (Fin m × Fin m) :=
      Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)
    let Eunc : Finset (Fin m × Fin m) :=
      E.filter (fun p => orig k m p.1 ∉ U ∧ orig k m p.2 ∉ U)
    let U0 : Finset (Fin (m + 2 * k * m * m)) := U.filter (fun x => x.val < m)
    let R0 : Finset (Fin m) := R.filter (fun u => ∃ x ∈ U, x.val = u.val)
    let R1 : Finset (Fin m) := R.filter (fun u => ¬ ∃ x ∈ U, x.val = u.val)
    have hR_split : R0.card + R1.card = R.card := by
      have hdisj : Disjoint R0 R1 := by
        rw [Finset.disjoint_left]
        intro u hu0 hu1
        simp only [R0, R1, Finset.mem_filter] at hu0 hu1
        exact hu1.2 hu0.2
      have hunion : R0 ∪ R1 = R := by
        ext u
        simp only [R0, R1, Finset.mem_union, Finset.mem_filter]
        by_cases h : ∃ x ∈ U, x.val = u.val <;> simp [h]
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hR0_le : R0.card ≤ U0.card := by
      refine Finset.card_le_card_of_injOn (orig k m) ?_ ?_
      · intro u hu
        simp only [R0, Finset.mem_coe, Finset.mem_filter] at hu
        rcases hu.2 with ⟨x, hxU, hxv⟩
        have hEq : orig k m u = x := Fin.ext hxv.symm
        simp only [U0, Finset.mem_coe, Finset.mem_filter]
        exact ⟨hEq ▸ hxU, u.isLt⟩
      · intro u₁ _ u₂ _ hEq
        have hv : (orig k m u₁).val = (orig k m u₂).val := congrArg Fin.val hEq
        exact Fin.ext hv
    have hR1_le : R1.card ≤ Eunc.card := by
      have hsub : R1 ⊆ Eunc.image Prod.fst := by
        intro u hu
        simp only [R1, Finset.mem_filter] at hu
        have hRu := (hR u).mp hu.1
        rcases hRu with h1 | ⟨v, hlt, huv, hnu, hnv⟩
        · exact absurd h1 hu.2
        · rw [Finset.mem_image]
          refine ⟨(u, v), ?_, rfl⟩
          simp only [Eunc, E, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨hlt, huv⟩, ?_, ?_⟩
          · intro hmem
            exact hnu (orig k m u) hmem rfl
          · intro hmem
            exact hnv (orig k m v) hmem rfl
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    let B : Fin m × Fin m → Finset (Fin (m + 2 * k * m * m)) := fun p =>
      (Finset.univ.filter (fun i : Fin (2 * k) => subdiv k m p.1 p.2 i ∈ U)).image
        (subdiv k m p.1 p.2)
    have hB_sub : ∀ p ∈ E, B p ⊆ U := by
      intro p _ x hx
      simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨i, hi, rfl⟩
      exact hi
    have hB_disj : Set.PairwiseDisjoint (E : Set (Fin m × Fin m)) B := by
      intro p₁ _ p₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      rcases hx₁ with ⟨i₁, _, rfl⟩
      rcases hx₂ with ⟨i₂, _, hEq⟩
      have ⟨hu, hv, _⟩ := subdiv_inj hEq.symm
      exact hne (Prod.ext hu hv)
    have hU0_disj : Disjoint U0 (E.biUnion B) := by
      rw [Finset.disjoint_left]
      intro x hx0 hxB
      simp only [U0, Finset.mem_filter] at hx0
      simp only [Finset.mem_biUnion, B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hxB
      rcases hxB with ⟨p, _, i, _, rfl⟩
      have : m ≤ (subdiv k m p.1 p.2 i).val := by
        dsimp only [subdiv]
        omega
      omega
    have hUnion_sub : U0 ∪ E.biUnion B ⊆ U := by
      refine Finset.union_subset (Finset.filter_subset _ _) ?_
      exact Finset.biUnion_subset.mpr hB_sub
    have hU_ge : U0.card + ∑ p ∈ E, (B p).card ≤ U.card := by
      calc U0.card + ∑ p ∈ E, (B p).card
          = U0.card + (E.biUnion B).card := by rw [Finset.card_biUnion hB_disj]
        _ = (U0 ∪ E.biUnion B).card := (Finset.card_union_of_disjoint hU0_disj).symm
        _ ≤ U.card := Finset.card_le_card hUnion_sub
    have hB_card : ∀ p : Fin m × Fin m,
        (B p).card = (Finset.univ.filter (fun i : Fin (2 * k) => subdiv k m p.1 p.2 i ∈ U)).card := by
      intro p
      refine Finset.card_image_of_injOn ?_
      intro i₁ _ i₂ _ hEq
      exact (subdiv_inj hEq).2.2
    have hB_ge : ∀ p ∈ E, (if p ∈ Eunc then k + 1 else k) ≤ (B p).card := by
      intro p hp
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [hB_card p]
      have hadj : ∀ i : Fin (2 * k), (h : i.val + 1 < 2 * k) →
          subdiv k m p.1 p.2 i ∈ U ∨ subdiv k m p.1 p.2 ⟨i.val + 1, h⟩ ∈ U := by
        intro i hi
        apply hU
        rw [hS, SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ⟨p.1, p.2, hp.1, hp.2, i, rfl, Or.inr (Or.inl ⟨hi, rfl⟩)⟩⟩
        intro hEq
        have hv := congrArg Fin.val hEq
        dsimp only [subdiv] at hv
        omega
      split_ifs with hunc
      · simp only [Eunc, Finset.mem_filter] at hunc
        have h0 : subdiv k m p.1 p.2 ⟨0, by omega⟩ ∈ U := by
          have hS0 : S.Adj (subdiv k m p.1 p.2 ⟨0, by omega⟩) (orig k m p.1) := by
            rw [hS, SimpleGraph.fromRel_adj]
            refine ⟨?_, Or.inl ⟨p.1, p.2, hp.1, hp.2, ⟨0, by omega⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
            intro hEq
            have hv := congrArg Fin.val hEq
            dsimp only [subdiv, orig] at hv
            have := p.1.isLt
            omega
          exact (hU _ _ hS0).resolve_right hunc.2.1
        have hlast : subdiv k m p.1 p.2 ⟨2 * k - 1, by omega⟩ ∈ U := by
          have hSl : S.Adj (subdiv k m p.1 p.2 ⟨2 * k - 1, by omega⟩) (orig k m p.2) := by
            rw [hS, SimpleGraph.fromRel_adj]
            refine ⟨?_, Or.inl ⟨p.1, p.2, hp.1, hp.2, ⟨2 * k - 1, by omega⟩, rfl,
              Or.inr (Or.inr ⟨by dsimp only; omega, rfl⟩)⟩⟩
            intro hEq
            have hv := congrArg Fin.val hEq
            dsimp only [subdiv, orig] at hv
            have := p.2.isLt
            omega
          exact (hU _ _ hSl).resolve_right hunc.2.2
        exact path_cover_ge_k_add_one hk (fun i => subdiv k m p.1 p.2 i ∈ U) hadj h0 hlast
      · exact path_cover_ge_k (fun i => subdiv k m p.1 p.2 i ∈ U) hadj
    have hsum : Eunc.card + k * E.card ≤ ∑ p ∈ E, (B p).card := by
      have h1 : ∑ p ∈ E, (if p ∈ Eunc then k + 1 else k) ≤ ∑ p ∈ E, (B p).card :=
        Finset.sum_le_sum hB_ge
      have h2 : ∑ p ∈ E, (if p ∈ Eunc then k + 1 else k) =
          ∑ p ∈ E, (k + if p ∈ Eunc then 1 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        split_ifs <;> omega
      have h3 : ∑ p ∈ E, (if p ∈ Eunc then (1 : ℕ) else 0) = Eunc.card := by
        simp only [Finset.sum_boole, Nat.cast_id]
        congr 1
        ext p
        simp only [Eunc, Finset.mem_filter]
        tauto
      rw [h2, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, h3] at h1
      have hcomm : E.card * k = k * E.card := Nat.mul_comm E.card k
      omega
    have hedge : H.edgeSet.ncard = E.card := edgeSet_ncard_eq_ordered H
    rw [hedge]
    omega
