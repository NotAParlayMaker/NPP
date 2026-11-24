import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3362 :
  ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro x1 x2 x3 x4 _ hcard huniq x8 x9 hbip hcov
  let E : Finset (Fin x1 × Fin x1) := Finset.univ.filter (fun p => x4 p.1 p.2)
  have hE_card : E.card = x1 * x2 := by
    have heqv : { p : Fin x1 × Fin x1 // x4 p.1 p.2 } ≃ Σ L : Fin x1, { p : Fin x1 // x4 p L } :=
      { toFun := fun ⟨⟨p, L⟩, h⟩ => ⟨L, ⟨p, h⟩⟩
        invFun := fun ⟨L, ⟨p, h⟩⟩ => ⟨⟨p, L⟩, h⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
    calc E.card
        = Fintype.card { p : Fin x1 × Fin x1 // x4 p.1 p.2 } := (Fintype.card_subtype _).symm
      _ = Fintype.card (Σ L : Fin x1, { p : Fin x1 // x4 p L }) := Fintype.card_congr heqv
      _ = ∑ L : Fin x1, Fintype.card { p : Fin x1 // x4 p L } := Fintype.card_sigma
      _ = x1 * x2 := by simp [hcard]
  have hE_sub : E ⊆ (Finset.univ : Finset (Fin x3)).biUnion (fun i => x8 i ×ˢ x9 i) := by
    intro ⟨p, L⟩ hpL
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hpL
    obtain ⟨i, hi8, hi9⟩ := hcov p L hpL
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_product.mpr ⟨hi8, hi9⟩⟩
  have hle_sum : E.card ≤ ∑ i : Fin x3, (x8 i).card * (x9 i).card := by
    refine le_trans (Finset.card_le_card hE_sub) ?_
    refine le_trans Finset.card_biUnion_le ?_
    simp [Finset.card_product]
  have hterm : ∀ i : Fin x3, (x8 i).card * (x9 i).card ≤ (x8 i).card + (x9 i).card := by
    intro i
    have hle1 : (x8 i).card ≤ 1 ∨ (x9 i).card ≤ 1 := by
      by_contra h
      push Not at h
      obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp h.1
      obtain ⟨L1, hL1, L2, hL2, hLne⟩ := Finset.one_lt_card.mp h.2
      obtain ⟨L, _, hLuniq⟩ := huniq p1 p2 hpne
      have h1 : L1 = L := hLuniq L1 ⟨hbip i p1 hp1 L1 hL1, hbip i p2 hp2 L1 hL1⟩
      have h2 : L2 = L := hLuniq L2 ⟨hbip i p1 hp1 L2 hL2, hbip i p2 hp2 L2 hL2⟩
      exact hLne (h1.trans h2.symm)
    rcases hle1 with h1 | h2
    · have : (x8 i).card * (x9 i).card ≤ 1 * (x9 i).card := Nat.mul_le_mul_right _ h1
      omega
    · have : (x8 i).card * (x9 i).card ≤ (x8 i).card * 1 := Nat.mul_le_mul_left _ h2
      omega
  rw [← hE_card]
  exact le_trans hle_sum (Finset.sum_le_sum (fun i _ => hterm i))
