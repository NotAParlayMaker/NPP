import Mathlib
import PEqualNP.Defs

-- Two points lie on exactly one common line, so a rectangle of incident pairs has at most
-- one point or at most one line: its area is at most its half-perimeter. The rectangles
-- cover the n * k incident pairs, which gives the bound.
theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro n k m R inst hcol huniq A B hin hcov
  -- the incident pairs, counted line by line
  have hI : (Finset.univ.filter fun pl : Fin n × Fin n => R pl.1 pl.2).card = n * k := by
    rw [← Fintype.card_subtype]
    have e : {pl : Fin n × Fin n // R pl.1 pl.2} ≃ (Σ l : Fin n, {p : Fin n // R p l}) :=
      { toFun := fun x => ⟨x.1.2, ⟨x.1.1, x.2⟩⟩
        invFun := fun y => ⟨(y.2.1, y.1), y.2.2⟩
        left_inv := fun x => by
          rcases x with ⟨⟨p, l⟩, h⟩
          rfl
        right_inv := fun y => by
          rcases y with ⟨l, ⟨p, h⟩⟩
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [hcol, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- every incident pair lies in one of the rectangles
  have hsub : (Finset.univ.filter fun pl : Fin n × Fin n => R pl.1 pl.2) ⊆
      Finset.univ.biUnion fun i : Fin m => A i ×ˢ B i := by
    intro pl hpl
    obtain ⟨i, ha, hb⟩ := hcov pl.1 pl.2 (Finset.mem_filter.mp hpl).2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_product.mpr ⟨ha, hb⟩⟩
  -- a rectangle inside the incidence has one side of size at most one
  have hstar : ∀ i : Fin m, (A i).card * (B i).card ≤ (A i).card + (B i).card := by
    intro i
    by_cases hA : (A i).card ≤ 1
    · calc (A i).card * (B i).card ≤ 1 * (B i).card := Nat.mul_le_mul_right _ hA
        _ ≤ (A i).card + (B i).card := by omega
    · by_cases hB : (B i).card ≤ 1
      · calc (A i).card * (B i).card ≤ (A i).card * 1 := Nat.mul_le_mul_left _ hB
          _ ≤ (A i).card + (B i).card := by omega
      · exfalso
        obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.mp (by omega : 1 < (A i).card)
        obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.mp (by omega : 1 < (B i).card)
        obtain ⟨c, _, hc⟩ := huniq a a' haa
        have h1 := hc b ⟨hin i a ha b hb, hin i a' ha' b hb⟩
        have h2 := hc b' ⟨hin i a ha b' hb', hin i a' ha' b' hb'⟩
        exact hbb (h1.trans h2.symm)
  calc n * k = (Finset.univ.filter fun pl : Fin n × Fin n => R pl.1 pl.2).card := hI.symm
    _ ≤ (Finset.univ.biUnion fun i : Fin m => A i ×ˢ B i).card := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin m, (A i ×ˢ B i).card := Finset.card_biUnion_le
    _ = ∑ i : Fin m, (A i).card * (B i).card := by simp only [Finset.card_product]
    _ ≤ ∑ i : Fin m, ((A i).card + (B i).card) := Finset.sum_le_sum fun i _ => hstar i
