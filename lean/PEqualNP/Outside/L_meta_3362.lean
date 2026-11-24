import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro x1 x2 x3 x4 x5 hcol huniq x8 x9 hrect hcov
  have key : ∀ i : Fin x3, (x8 i).card * (x9 i).card ≤ (x8 i).card + (x9 i).card := by
    intro i
    by_cases hA : (x8 i).card ≤ 1
    · nlinarith
    · have hB : (x9 i).card ≤ 1 := by
        rw [not_le, Finset.one_lt_card_iff] at hA
        rw [Finset.card_le_one]
        intro b hb b' hb'
        obtain ⟨a, a', ha, ha', hne⟩ := hA
        obtain ⟨c, _, hc⟩ := huniq a a' hne
        have e1 := hc b ⟨hrect i a ha b hb, hrect i a' ha' b hb⟩
        have e2 := hc b' ⟨hrect i a ha b' hb', hrect i a' ha' b' hb'⟩
        rw [e1, e2]
      nlinarith
  have hS : (Finset.univ.filter (fun pl : Fin x1 × Fin x1 => x4 pl.1 pl.2)).card = x1 * x2 := by
    have : (Finset.univ.filter (fun pl : Fin x1 × Fin x1 => x4 pl.1 pl.2)).card
        = ∑ l : Fin x1, (Finset.univ.filter (fun p : Fin x1 => x4 p l)).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.card_filter]
    rw [this]
    have h2 : ∀ l : Fin x1, (Finset.univ.filter (fun p : Fin x1 => x4 p l)).card = x2 := by
      intro l
      rw [← hcol l, Fintype.card_subtype]
    rw [Finset.sum_congr rfl (fun l _ => h2 l), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hsub : Finset.univ.filter (fun pl : Fin x1 × Fin x1 => x4 pl.1 pl.2)
      ⊆ Finset.univ.biUnion (fun i => x8 i ×ˢ x9 i) := by
    intro pl hpl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpl
    obtain ⟨i, h1, h2⟩ := hcov pl.1 pl.2 hpl
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product]
    exact ⟨i, h1, h2⟩
  calc x1 * x2 = _ := hS.symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin x3, (x8 i ×ˢ x9 i).card := Finset.card_biUnion_le
    _ = ∑ i : Fin x3, (x8 i).card * (x9 i).card := by simp [Finset.card_product]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => key i)
