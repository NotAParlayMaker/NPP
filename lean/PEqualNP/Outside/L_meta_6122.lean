import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6122

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6122

theorem PEqualNP.Outside.L_meta_6122 : ∀ (x1 x2 : ℕ) (x3 : ℕ → Set (Finset ℕ)), (∀ x4 < x1, x3 x4 = {{x4}}) → (∀ x5 < x2, ∃ x7 < x1 + x5, ∃ x8 < x1 + x5, x3 (x1 + x5) = Set.image2 (fun (x9 x10 : Finset ℕ) => x9 ∪ x10) (x3 x7) (x3 x8) ∨ x3 (x1 + x5) = x3 x7 ∨ x3 (x1 + x5) = {∅} ∨ x3 (x1 + x5) = x3 x7 ∪ x3 x8) → ∃ (x6 : ℕ → Set (Finset ℕ)), (∀ (x7 : ℕ) (x8 : Finset ℕ), x8 ∈ x6 x7 ↔ ∀ x9 ∈ x3 x7, ¬Disjoint x9 x8) ∧ (∀ x7 < x1, x6 x7 = {x9 : Finset ℕ | x7 ∈ x9}) ∧ ∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, x6 (x1 + x7) ∈ [x6 x9 ∪ x6 x10, x6 x9 ∩ x6 x10, x6 x9, ∅] := by
  intro n m F hin hg
  refine ⟨fun i => {t | ∀ s ∈ F i, ¬ Disjoint s t}, fun _ _ => Iff.rfl, ?_, ?_⟩
  · intro i hi
    ext t
    simp [hin i hi]
  · intro j hj
    obtain ⟨a, ha, b, hb, h⟩ := hg j hj
    refine ⟨a, ha, b, hb, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases h with h | h | h | h
    · left
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_union, h]
      constructor
      · intro hall
        by_contra hcon
        rw [not_or] at hcon
        obtain ⟨h1, h2⟩ := hcon
        simp only [not_forall, not_not] at h1 h2
        obtain ⟨s, hs, hsd⟩ := h1
        obtain ⟨s', hs', hsd'⟩ := h2
        exact hall _ (Set.mem_image2_of_mem hs hs') (Finset.disjoint_union_left.2 ⟨hsd, hsd'⟩)
      · rintro (h1 | h1) s hs hd
        · obtain ⟨x, hx, y, hy, rfl⟩ := hs
          exact h1 x hx (Finset.disjoint_union_left.1 hd).1
        · obtain ⟨x, hx, y, hy, rfl⟩ := hs
          exact h1 y hy (Finset.disjoint_union_left.1 hd).2
    · right; right; left
      simp only [h]
    · right; right; right
      ext t
      simp [h]
    · right; left
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, h, Set.mem_union]
      constructor
      · intro hall
        exact ⟨fun s hs => hall s (Or.inl hs), fun s hs => hall s (Or.inr hs)⟩
      · rintro ⟨h1, h2⟩ s (hs | hs)
        · exact h1 s hs
        · exact h2 s hs
