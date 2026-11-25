import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5815 : ∀ (x1 : ℕ) (x2 x3 x4 : Finset (Finset (Fin x1))) (x5 x6 : Set (Fin x1)),   have x7 : Finset (Finset (Fin x1)) → Prop := fun (x7 : Finset (Finset (Fin x1))) => (∀ x8 ∈ x7, ∃ x10 ∈ x8, x10 ∈ x5) ∧ ∃ x8 ∈ x7, ∀ x9 ∈ x8, x9 ∈ x6;   (x4 = x2 ∪ x3 ∨ x4 = x2.biUnion fun (x8 : Finset (Fin x1)) => Finset.image (fun (x9 : Finset (Fin x1)) => x8 ∪ x9) x3) → x7 x4 → x7 x2 ∨ x7 x3 := by
  intro x1 x2 x3 x4 x5 x6 P h hP
  obtain ⟨hall, S, hS, hsub⟩ := hP
  rcases h with rfl | rfl
  · rcases Finset.mem_union.1 hS with h2 | h3
    · exact Or.inl ⟨fun A hA => hall A (Finset.mem_union_left _ hA), S, h2, hsub⟩
    · exact Or.inr ⟨fun A hA => hall A (Finset.mem_union_right _ hA), S, h3, hsub⟩
  · obtain ⟨A, hA, hS'⟩ := Finset.mem_biUnion.1 hS
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hS'
    by_cases h2 : ∀ A' ∈ x2, ∃ a ∈ A', a ∈ x5
    · exact Or.inl ⟨h2, A, hA, fun a ha => hsub a (Finset.mem_union_left _ ha)⟩
    · refine Or.inr ⟨fun B' hB' => ?_, B, hB, fun a ha => hsub a (Finset.mem_union_right _ ha)⟩
      push_neg at h2
      obtain ⟨A', hA', hno⟩ := h2
      obtain ⟨a, ha, ha5⟩ := hall (A' ∪ B') (Finset.mem_biUnion.2 ⟨A', hA', Finset.mem_image.2 ⟨B', hB', rfl⟩⟩)
      rcases Finset.mem_union.1 ha with h | h
      · exact absurd ha5 (hno a h)
      · exact ⟨a, h, ha5⟩
