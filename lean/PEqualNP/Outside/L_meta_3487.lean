import PEqualNP.Defs

open scoped BigOperators
open Finset

namespace PEqualNP.Outside.L_meta_3487_aux

-- The tangent bound for integral degrees comes from (d - 87)(d - 88) ≥ 0.
private theorem degree_bound (d : ℕ) : 174 * d ≤ d * (d - 1) + 7656 := by
  by_cases hd : d = 0
  · simp [hd]
  zify [show 1 ≤ d by omega]
  by_cases h : d ≤ 87
  · have hz : (d : ℤ) ≤ 87 := by exact_mod_cast h
    nlinarith only [mul_nonneg (show 0 ≤ 87 - (d : ℤ) by omega)
      (show 0 ≤ 88 - (d : ℤ) by omega)]
  · have hz : (88 : ℤ) ≤ d := by exact_mod_cast (show 88 ≤ d by omega)
    nlinarith only [mul_nonneg (show 0 ≤ (d : ℤ) - 87 by omega)
      (show 0 ≤ (d : ℤ) - 88 by omega)]

private theorem oriented {n : ℕ} (E : Finset (Fin n × Fin n))
    (h : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (b, c) ∈ E ∧ (a, d) ∈ E ∧ (b, d) ∈ E))
    (hsmall : (E.image Prod.fst).card ≤ 7656) :
    E.card ≤ 44 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
  classical
  if he : E = ∅ then
    simp [he]
  else
    let A := E.image Prod.fst
    let B := E.image Prod.snd
    let N := fun v : Fin n => (E.filter fun p => p.2 = v).image Prod.fst
    have hN (u v : Fin n) : u ∈ N v ↔ (u, v) ∈ E := by
      constructor
      · intro hu
        rcases mem_image.mp hu with ⟨⟨a,b⟩, hp, ha⟩
        rcases mem_filter.mp hp with ⟨hp, hb⟩
        change a = u at ha
        change b = v at hb
        simpa [ha, hb] using hp
      · intro hp
        exact mem_image.mpr ⟨(u,v), mem_filter.mpr ⟨hp, rfl⟩, rfl⟩
    have Nsub (v : Fin n) : N v ⊆ A := by
      intro u hu
      exact mem_image.mpr ⟨(u,v), (hN u v).mp hu, rfl⟩
    have hE : E.card = ∑ v ∈ B, (N v).card := by
      rw [card_eq_sum_card_image Prod.snd E]
      apply sum_congr rfl
      intro v hv
      symm
      apply card_image_of_injOn
      rintro ⟨a,b⟩ hp ⟨a',b'⟩ hq hpq
      have hb : b = v := (mem_filter.mp hp).2
      have hb' : b' = v := (mem_filter.mp hq).2
      exact Prod.ext hpq (hb.trans hb'.symm)
    -- An ordered pair of distinct vertices can have at most one common neighbor.
    have hDisj : (↑B : Set (Fin n)).PairwiseDisjoint fun v => (N v).offDiag := by
      intro v _ w _ hvw
      apply disjoint_left.mpr
      rintro ⟨a,b⟩ hv hw
      obtain ⟨hav,hbv,hab⟩ := mem_offDiag.mp hv
      obtain ⟨haw,hbw,_⟩ := mem_offDiag.mp hw
      exact h a b v w hab hvw ⟨(hN a v).mp hav, (hN b v).mp hbv,
        (hN a w).mp haw, (hN b w).mp hbw⟩
    have hSub : B.biUnion (fun v => (N v).offDiag) ⊆ A.offDiag := by
      rintro ⟨a,b⟩ hp
      obtain ⟨v,_,hv⟩ := mem_biUnion.mp hp
      obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp hv
      exact mem_offDiag.mpr ⟨Nsub v ha, Nsub v hb, hab⟩
    have count (S : Finset (Fin n)) : S.offDiag.card = S.card * (S.card - 1) := by
      rw [offDiag_card, Nat.mul_sub_left_distrib, Nat.mul_one]
    have hpairs : (∑ v ∈ B, (N v).card * ((N v).card - 1)) ≤ A.card * (A.card - 1) := by
      simpa only [card_biUnion hDisj, count] using card_le_card hSub
    have hbound : 174 * E.card ≤ A.card * (A.card - 1) + B.card * 7656 := by
      rw [hE, Finset.mul_sum]
      calc
        _ ≤ ∑ v ∈ B, ((N v).card * ((N v).card - 1) + 7656) :=
          sum_le_sum (fun v _ => degree_bound (N v).card)
        _ ≤ _ := by
          rw [sum_add_distrib, sum_const_nat (fun _ _ => rfl)]
          exact Nat.add_le_add_right hpairs _
    have hApos : 0 < A.card := by
      obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr he
      exact card_pos.mpr ⟨p.1, mem_image_of_mem _ hp⟩
    change A.card ≤ 7656 at hsmall
    have hmul := Nat.mul_le_mul_right (A.card - 1) hsmall
    change E.card ≤ 44 * (A.card + B.card - 1)
    omega

end PEqualNP.Outside.L_meta_3487_aux

theorem PEqualNP.Outside.L_meta_3487 :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n E h hsmall
  by_cases hl : (E.image Prod.fst).card ≤ (E.image Prod.snd).card
  · rw [min_eq_left hl] at hsmall
    exact PEqualNP.Outside.L_meta_3487_aux.oriented E h hsmall
  · rw [min_eq_right (le_of_not_ge hl)] at hsmall
    let F := E.image Prod.swap
    have hm (a b : Fin n) : (a,b) ∈ F ↔ (b,a) ∈ E := by
      constructor
      · intro hp
        obtain ⟨⟨c,d⟩, hcd, heq⟩ := mem_image.mp hp
        change (d,c) = (a,b) at heq
        cases heq
        exact hcd
      · intro hp
        exact mem_image.mpr ⟨(b,a), hp, rfl⟩
    have hf : F.image Prod.fst = E.image Prod.snd := by
      simp [F, image_image, Function.comp_def]
    have hs : F.image Prod.snd = E.image Prod.fst := by
      simp [F, image_image, Function.comp_def]
    have hc : F.card = E.card := card_image_of_injective _ Prod.swap_injective
    have hb := PEqualNP.Outside.L_meta_3487_aux.oriented F (by
      intro a b c d hab hcd hp
      exact h c d a b hcd hab ⟨(hm a c).mp hp.1, (hm a d).mp hp.2.2.1,
        (hm b c).mp hp.2.1, (hm b d).mp hp.2.2.2⟩) (hf ▸ hsmall)
    simpa [hf, hs, hc, Nat.add_comm] using hb
