import Mathlib
import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_3487

private theorem degreeTangent (d : ℕ) : 174 * d ≤ d * d - d + 7656 := by
  have prod : (0 : ℤ) ≤ ((d : ℤ) - 87) * ((d : ℤ) - 88) := by
    by_cases h : d ≤ 87
    · apply mul_nonneg_of_nonpos_of_nonpos <;> omega
    · apply mul_nonneg <;> omega
  have bound : (174 : ℤ) * (d : ℤ) ≤ (d : ℤ) * (d : ℤ) - (d : ℤ) + 7656 := by
    nlinarith only [prod]
  exact_mod_cast (by simpa only [Nat.cast_sub (Nat.le_mul_self d), Nat.cast_mul,
    Nat.cast_add, Nat.cast_ofNat] using bound :
      ((174 * d : ℕ) : ℤ) ≤ ((d * d - d + 7656 : ℕ) : ℤ))

-- Count ordered pairs of neighbors. The rectangle condition makes their line unique.
private theorem boundWithSmallLeft {n : ℕ} (E : Finset (Fin n × Fin n))
    (free : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
      ¬ ((a,c) ∈ E ∧ (b,c) ∈ E ∧ (a,d) ∈ E ∧ (b,d) ∈ E))
    (small : (E.image Prod.fst).card ≤ 7656) :
    E.card ≤ 44 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let fiber (v : Fin n) := E.filter (fun e => e.2 = v)
  let N (v : Fin n) := (fiber v).image Prod.fst
  let W := B.sigma (fun v => (N v).offDiag)
  have atFiber (a v : Fin n) : a ∈ N v ↔ (a,v) ∈ E := by
    constructor
    · intro ha
      obtain ⟨⟨x,y⟩, hxy, e⟩ := Finset.mem_image.mp ha
      obtain ⟨he, hv⟩ := Finset.mem_filter.mp hxy
      change x = a at e
      change y = v at hv
      simpa only [e, hv] using he
    · intro he
      exact Finset.mem_image.mpr ⟨(a,v), Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩
  have cardN (v : Fin n) : (N v).card = (fiber v).card := by
    apply Finset.card_image_of_injOn
    intro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    have hb := (Finset.mem_filter.mp (show (a,b) ∈ fiber v from hab)).2
    have hd := (Finset.mem_filter.mp (show (c,d) ∈ fiber v from hcd)).2
    exact Prod.ext he (hb.trans hd.symm)
  have total : E.card = ∑ v ∈ B, (N v).card := by
    simpa only [cardN] using Finset.card_eq_sum_card_image Prod.snd E
  have pairCount : W.card ≤ A.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun v => v.2)
    · intro ⟨v,a,b⟩ h
      obtain ⟨ha,hb,neq⟩ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp h).2
      change (a,b) ∈ A.offDiag
      exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_image.mpr ⟨(a,v), (atFiber a v).mp ha, rfl⟩,
          Finset.mem_image.mpr ⟨(b,v), (atFiber b v).mp hb, rfl⟩, neq⟩
    · intro ⟨u,a,b⟩ hu ⟨v,c,d⟩ hv eq
      change (a,b) = (c,d) at eq
      cases eq
      obtain ⟨ha,hb,ab⟩ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hu).2
      obtain ⟨hc,hd,_⟩ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hv).2
      have uv : u = v := by
        by_contra ne
        exact free a b u v ab ne
          ⟨(atFiber a u).mp ha, (atFiber b u).mp hb, (atFiber a v).mp hc, (atFiber b v).mp hd⟩
      subst v
      rfl
  have weighted : 174 * E.card ≤ W.card + B.card * 7656 := by
    rw [total, Finset.mul_sum, show W.card = ∑ v ∈ B, (N v).offDiag.card from Finset.card_sigma _ _]
    rw [← Finset.sum_const_nat (s := B) (f := fun _ => 7656) (fun _ _ => rfl), ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    rw [Finset.offDiag_card]
    exact degreeTangent _
  have pa : A.card * A.card - A.card ≤ 7656 * (A.card - 1) := by
    have eq : A.card * (A.card - 1) = A.card * A.card - A.card := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    rw [← eq]
    exact Nat.mul_le_mul_right _ small
  by_cases nonempty : E.Nonempty
  · have posA : 1 ≤ A.card := by
      obtain ⟨e,he⟩ := nonempty
      exact Finset.card_pos.mpr ⟨e.1, Finset.mem_image_of_mem _ he⟩
    have bound := weighted.trans (Nat.add_le_add_right pairCount (B.card * 7656))
    rw [Finset.offDiag_card] at bound
    have hfinal := bound.trans (Nat.add_le_add_right pa (B.card * 7656))
    change E.card ≤ 44 * (A.card + B.card - 1)
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]

end PEqualNP.Outside.L_meta_3487

open PEqualNP.Outside.L_meta_3487

theorem PEqualNP.Outside.L_meta_3487 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n E free small
  rcases min_le_iff.mp small with smallLeft | smallRight
  · exact boundWithSmallLeft E free smallLeft
  let F := E.image Prod.swap
  have swapped (a b : Fin n) : (a,b) ∈ F ↔ (b,a) ∈ E := by
    constructor
    · intro he
      obtain ⟨e, he, eq⟩ := Finset.mem_image.mp he
      have ee : e = (b,a) := by
        simpa using congrArg Prod.swap eq
      exact ee ▸ he
    · intro he
      exact Finset.mem_image.mpr ⟨(b,a), he, rfl⟩
  have left : F.image Prod.fst = E.image Prod.snd := by
    simp [F, Finset.image_image, Function.comp_def]
  have right : F.image Prod.snd = E.image Prod.fst := by
    simp [F, Finset.image_image, Function.comp_def]
  have count : F.card = E.card := Finset.card_image_of_injOn Prod.swap_injective.injOn
  have reverseFree (a b c d : Fin n) (ab : a ≠ b) (cd : c ≠ d) :
      ¬ ((a,c) ∈ F ∧ (b,c) ∈ F ∧ (a,d) ∈ F ∧ (b,d) ∈ F) := by
    rintro ⟨ac,bc,ad,bd⟩
    exact free c d a b cd ab
      ⟨(swapped _ _).mp ac, (swapped _ _).mp ad, (swapped _ _).mp bc, (swapped _ _).mp bd⟩
  have h := boundWithSmallLeft F reverseFree (left.symm ▸ smallRight)
  rwa [count, left, right, add_comm] at h
