import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  classical
  intro n k m I _ hk huniq A B hbic hcov
  have hE : (Finset.univ.filter fun pl : Fin n × Fin n => I pl.1 pl.2).card = n * k := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    have h1 : ∀ l : Fin n, (∑ p : Fin n, if I p l then 1 else 0) = k := by
      intro l
      rw [← Finset.card_filter, ← hk l, Fintype.card_subtype]
    simp [h1]
  have hsub : (Finset.univ.filter fun pl : Fin n × Fin n => I pl.1 pl.2) ⊆
      Finset.univ.biUnion (fun i => A i ×ˢ B i) := by
    intro pl h
    obtain ⟨i, hp, hl⟩ := hcov pl.1 pl.2 (Finset.mem_filter.1 h).2
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_product.2 ⟨hp, hl⟩⟩
  have hstar : ∀ i, (A i).card * (B i).card ≤ (A i).card + (B i).card := by
    intro i
    by_cases hA : (A i).card ≤ 1
    · exact (Nat.mul_le_mul_right _ hA).trans (by omega)
    by_cases hB : (B i).card ≤ 1
    · exact (Nat.mul_le_mul_left _ hB).trans (by omega)
    exfalso
    obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.1 (by omega : 1 < (A i).card)
    obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.1 (by omega : 1 < (B i).card)
    exact hbb ((huniq a a' haa).unique ⟨hbic i a ha b hb, hbic i a' ha' b hb⟩
      ⟨hbic i a ha b' hb', hbic i a' ha' b' hb'⟩)
  calc n * k = (Finset.univ.filter fun pl : Fin n × Fin n => I pl.1 pl.2).card := hE.symm
    _ ≤ (Finset.univ.biUnion fun i => A i ×ˢ B i).card := Finset.card_le_card hsub
    _ ≤ ∑ i, (A i ×ˢ B i).card := Finset.card_biUnion_le
    _ = ∑ i, (A i).card * (B i).card := by simp only [Finset.card_product]
    _ ≤ ∑ i, ((A i).card + (B i).card) := Finset.sum_le_sum fun i _ => hstar i
