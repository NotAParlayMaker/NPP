import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6418

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6418

theorem PEqualNP.Outside.L_meta_6418 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Finset (Finset (Fin x1))) (x5 x6 : Type) (x7 : x5 → Fin x1 → Prop) (x8 : x6 → Fin x1 → Prop), (∀ (x9 : Fin x1), x4 ↑x9 = {{x9}}) → (∀ x10 < x2, ∃ (x12 : ℕ) (x13 : ℕ), x12 < x13 ∧ x13 < x1 + x10 ∧ (x4 (x1 + x10) = x4 x12 ∪ x4 x13 ∨ x4 (x1 + x10) = (x4 x12).biUnion fun (x14 : Finset (Fin x1)) => Finset.image (fun (x15 : Finset (Fin x1)) => x14 ∪ x15) (x4 x13))) → (∀ (x11 : x5), ∀ x12 ∈ x4 x3, ∃ x14 ∈ x12, x7 x11 x14) → (∀ (x12 : x6), ∃ x13 ∈ x4 x3, ∀ x14 ∈ x13, x8 x12 x14) → ∃ (x13 : ℕ → Set x5) (x14 : ℕ → Set x6), (∀ (x15 : Fin x1), x13 ↑x15 = {x16 : x5 | x7 x16 x15} ∧ x14 ↑x15 = {x16 : x6 | x8 x16 x15}) ∧ (∀ x15 < x2, ∃ (x17 : ℕ) (x18 : ℕ), x17 < x18 ∧ x18 < x1 + x15 ∧ x13 (x1 + x15) ×ˢ x14 (x1 + x15) ⊆ x13 x17 ×ˢ x14 x17 ∪ x13 x18 ×ˢ x14 x18) ∧ x13 x3 = Set.univ ∧ x14 x3 = Set.univ := by
  intro n m o F X Y φ ψ hin hg hX hY
  classical
  refine ⟨fun w => {x | ∀ s ∈ F w, ∃ i ∈ s, φ x i}, fun w => {y | ∃ s ∈ F w, ∀ i ∈ s, ψ y i}, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · ext x; simp [hin i]
    · ext y; simp [hin i]
  · intro j hj
    obtain ⟨a, b, hab, hb, h⟩ := hg j hj
    refine ⟨a, b, hab, hb, ?_⟩
    rintro ⟨x, y⟩ ⟨hx, s, hs, hys⟩
    simp only [Set.mem_setOf_eq] at hx
    rcases h with h | h <;> rw [h] at hs hx
    · rcases Finset.mem_union.1 hs with hs | hs
      · exact Or.inl ⟨fun u hu => hx u (Finset.mem_union_left _ hu), s, hs, hys⟩
      · exact Or.inr ⟨fun u hu => hx u (Finset.mem_union_right _ hu), s, hs, hys⟩
    · obtain ⟨u, hu, hs⟩ := Finset.mem_biUnion.1 hs
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hs
      by_cases hA : ∀ u ∈ F a, ∃ i ∈ u, φ x i
      · exact Or.inl ⟨hA, u, hu, fun i hi => hys i (Finset.mem_union_left _ hi)⟩
      · right
        refine ⟨fun v' hv' => ?_, v, hv, fun i hi => hys i (Finset.mem_union_right _ hi)⟩
        by_contra hcon
        apply hA
        intro u' hu'
        obtain ⟨i, hi, hφ⟩ := hx (u' ∪ v') (Finset.mem_biUnion.2 ⟨u', hu', Finset.mem_image.2 ⟨v', hv', rfl⟩⟩)
        rcases Finset.mem_union.1 hi with hi | hi
        · exact ⟨i, hi, hφ⟩
        · exact absurd ⟨i, hi, hφ⟩ hcon
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hX x
  · ext y
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hY y
