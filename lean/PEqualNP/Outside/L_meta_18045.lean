import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18045 : ∀ (x1 x2 : Finset (Finset ℕ)), (∀ x3 ∈ x1 \ x2, ∃ x5 ∈ x1, ∃ x6 ∈ x1, x5 ⊂ x3 ∧ x6 ⊂ x3 ∧ x3 = x5 ∪ x6) → ∀ x4 ∈ x1, {x6 ∈ x1 ∩ x2 | x6 ⊆ x4}.biUnion id = x4 := by
  intro F B split S hS
  have cover : ∀ T ∈ F, ∀ a ∈ T, ∃ U ∈ F ∩ B, U ⊆ T ∧ a ∈ U := by
    intro T
    induction T using Finset.strongInductionOn
    rename_i T ih
    intro hT a ha
    by_cases hb : T ∈ B
    · exact ⟨T, Finset.mem_inter.mpr ⟨hT, hb⟩, Finset.Subset.refl T, ha⟩
    obtain ⟨V, hV, W, hW, hv, hw, eqn⟩ := split T (Finset.mem_sdiff.mpr ⟨hT, hb⟩)
    rw [eqn] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨U, hU, sub, hit⟩ := ih V hv hV a ha
      exact ⟨U, hU, sub.trans hv.le, hit⟩
    · obtain ⟨U, hU, sub, hit⟩ := ih W hw hW a ha
      exact ⟨U, hU, sub.trans hw.le, hit⟩
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
  constructor
  · rintro ⟨U, ⟨_, hU⟩, ha⟩
    exact hU ha
  · intro ha
    obtain ⟨U, hU, sub, hit⟩ := cover S hS a ha
    exact ⟨U, ⟨hU, sub⟩, hit⟩
