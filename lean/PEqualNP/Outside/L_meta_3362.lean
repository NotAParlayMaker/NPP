import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3362

lemma mul_le_add_of_star (a c : ℕ) (h : a ≤ 1 ∨ c ≤ 1) : a * c ≤ a + c := by
  rcases h with h | h
  · interval_cases a <;> omega
  · interval_cases c <;> omega

end PEqualNP.Outside.L_meta_3362

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro N k m I _ hk huniq A B hbic hcov
  classical
  -- the incident pairs
  let S : Finset (Fin N × Fin N) := Finset.univ.filter fun pl => I pl.1 pl.2
  have hS : S.card = N * k := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun pl : Fin N × Fin N => pl.2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ l : Fin N, (S.filter fun pl => pl.2 = l).card = k := by
      intro l
      rw [← hk l, Fintype.card_subtype]
      apply Finset.card_bij (fun pl _ => pl.1)
      · intro pl hpl
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hpl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hpl.2]; exact hpl.1
      · intro a ha b hb hab
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        exact Prod.ext hab (ha.2.trans hb.2.symm)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact ⟨(p, l), by simp [S, hp], rfl⟩
    rw [Finset.sum_congr rfl (fun l _ => hfib l)]
    simp
  -- every incident pair lies in some block
  have hsub : S ⊆ Finset.univ.biUnion fun b => A b ×ˢ B b := by
    intro pl hpl
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hpl
    obtain ⟨b, hp, hl⟩ := hcov pl.1 pl.2 hpl
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_product.mpr ⟨hp, hl⟩⟩
  -- a block with two points has at most one line
  have hstar : ∀ b, (A b).card * (B b).card ≤ (A b).card + (B b).card := by
    intro b
    apply PEqualNP.Outside.L_meta_3362.mul_le_add_of_star
    by_cases h : (A b).card ≤ 1
    · exact Or.inl h
    · right
      obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp (show 1 < (A b).card by omega)
      apply Finset.card_le_one.mpr
      intro l hl l' hl'
      obtain ⟨l0, -, hu⟩ := huniq p p' hne
      rw [hu l ⟨hbic b p hp l hl, hbic b p' hp' l hl⟩, hu l' ⟨hbic b p hp l' hl', hbic b p' hp' l' hl'⟩]
  calc N * k = S.card := hS.symm
    _ ≤ (Finset.univ.biUnion fun b => A b ×ˢ B b).card := Finset.card_le_card hsub
    _ ≤ ∑ b, (A b ×ˢ B b).card := Finset.card_biUnion_le
    _ = ∑ b, (A b).card * (B b).card := by simp [Finset.card_product]
    _ ≤ ∑ b, ((A b).card + (B b).card) := Finset.sum_le_sum fun b _ => hstar b
