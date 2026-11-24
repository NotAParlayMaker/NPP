import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3487

-- The two consecutive degree values 87 and 88 give the tangent bound.
theorem degreeBound {α : Type*} (s : Finset α) : 174*s.card ≤ s.offDiag.card + 7656 := by
  let d := s.card
  have tangent : 175*(d : ℤ) ≤ (d : ℤ)*(d : ℤ)+7656 := by
    by_cases low : d≤87
    · nlinarith [mul_nonneg (show 0≤(87 : ℤ)-d by omega) (show 0≤(88 : ℤ)-d by omega)]
    · nlinarith [mul_nonneg (show 0≤(d : ℤ)-87 by omega) (show 0≤(d : ℤ)-88 by omega)]
  have natBound : 175*d ≤ d*d+7656 := by exact_mod_cast tangent
  rw [Finset.offDiag_card]
  change 174*d ≤ d*d-d+7656
  have self : d≤d*d := Nat.le_mul_self _
  omega

def NoRectangle {n : ℕ} (s : Finset (Fin n × Fin n)) :=
  ∀ a b c d, a≠b → c≠d → ¬((a,c)∈s ∧ (b,c)∈s ∧ (a,d)∈s ∧ (b,d)∈s)

theorem oneSide {n : ℕ} (s : Finset (Fin n × Fin n)) (free : NoRectangle s)
    (small : (s.image Prod.fst).card≤7656) :
    s.card≤44*((s.image Prod.fst).card+(s.image Prod.snd).card-1) := by
  classical
  by_cases empty : s=∅
  · simp [empty]
  let rows := s.image Prod.fst
  let cols := s.image Prod.snd
  let fiber := fun j : Fin n => s.filter (fun e => e.2=j)
  let neighbors := fun j : Fin n => (fiber j).image Prod.fst
  have member (i j : Fin n) : i ∈ neighbors j ↔ (i,j)∈s := by
    constructor
    · intro h
      obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp h
      have h := Finset.mem_filter.mp hab
      exact h.2 ▸ h.1
    · intro h
      exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨h,rfl⟩,rfl⟩
  have degrees (j : Fin n) : (neighbors j).card = (fiber j).card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb eq
    apply Prod.ext eq
    exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  have edges : (∑ j ∈ cols,(neighbors j).card) = s.card := by
    simpa only [degrees] using (Finset.card_eq_sum_card_image Prod.snd s).symm
  have disjoint : (cols : Set (Fin n)).PairwiseDisjoint (fun j => (neighbors j).offDiag) := by
    intro j hj k hk ne
    apply Finset.disjoint_left.mpr
    intro pair ph pk
    obtain ⟨a,b,ab⟩ := Finset.mem_offDiag.mp ph
    obtain ⟨c,d,_⟩ := Finset.mem_offDiag.mp pk
    exact free pair.1 pair.2 j k ab ne ⟨(member _ _).mp a,(member _ _).mp b,(member _ _).mp c,(member _ _).mp d⟩
  have cover : (cols.biUnion fun j => (neighbors j).offDiag) ⊆ rows.offDiag := by
    intro pair hp
    obtain ⟨j,_,h⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a,b,ab⟩ := Finset.mem_offDiag.mp h
    exact Finset.mem_offDiag.mpr ⟨Finset.mem_image.mpr ⟨(pair.1,j),(member _ _).mp a,rfl⟩,
      Finset.mem_image.mpr ⟨(pair.2,j),(member _ _).mp b,rfl⟩,ab⟩
  have pairs : (∑ j ∈ cols,(neighbors j).offDiag.card) ≤ rows.card*(rows.card-1) := by
    rw [← Finset.card_biUnion disjoint,Nat.mul_sub_one]
    simpa only [Finset.offDiag_card] using Finset.card_le_card cover
  have weighted := Finset.sum_le_sum (s:=cols) (fun j _ => degreeBound (neighbors j))
  rw [← Finset.mul_sum,edges,Finset.sum_add_distrib] at weighted
  simp only [Finset.sum_const,nsmul_eq_mul] at weighted
  have cap : rows.card*(rows.card-1) ≤ 7656*(rows.card-1) := Nat.mul_le_mul_right _ small
  have positive : 0<rows.card := Finset.card_pos.mpr ((Finset.nonempty_iff_ne_empty.mpr empty).image _)
  have scalar : 174*s.card ≤ 7656*(rows.card-1) + cols.card*7656 :=
    weighted.trans (Nat.add_le_add_right (pairs.trans cap) _)
  change s.card ≤ 44*(rows.card+cols.card-1)
  omega

end PEqualNP.Outside.L_meta_3487

theorem PEqualNP.Outside.L_meta_3487 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n s free small
  rcases min_le_iff.mp small with h | h
  · exact PEqualNP.Outside.L_meta_3487.oneSide s free h
  let r := s.image Prod.swap
  have swapped (i j : Fin n) : (i,j)∈r ↔ (j,i)∈s := by
    constructor
    · intro h
      obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp h
      have eq' := congrArg Prod.swap eq
      have hp' : p = (j,i) := by simpa using eq'
      exact hp' ▸ hp
    · intro h
      exact Finset.mem_image.mpr ⟨(j,i),h,rfl⟩
  have f : r.image Prod.fst = s.image Prod.snd := by simp [r,Finset.image_image,Function.comp_def]
  have g : r.image Prod.snd = s.image Prod.fst := by simp [r,Finset.image_image,Function.comp_def]
  have sz : r.card = s.card := Finset.card_image_of_injective _ Prod.swap_injective
  have legal : PEqualNP.Outside.L_meta_3487.NoRectangle r := by
    intro i j k l ij kl bad
    exact free k l i j kl ij ⟨(swapped _ _).mp bad.1,(swapped _ _).mp bad.2.2.1,
      (swapped _ _).mp bad.2.1,(swapped _ _).mp bad.2.2.2⟩
  have result := PEqualNP.Outside.L_meta_3487.oneSide r legal (f ▸ h)
  rw [f,g,sz,Nat.add_comm] at result
  exact result
