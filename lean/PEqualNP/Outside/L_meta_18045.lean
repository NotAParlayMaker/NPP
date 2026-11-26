import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18045 : ∀ (x1 x2 : Finset (Finset ℕ)), (∀ x3 ∈ x1 \ x2, ∃ x5 ∈ x1, ∃ x6 ∈ x1, x5 ⊂ x3 ∧ x6 ⊂ x3 ∧ x3 = x5 ∪ x6) → ∀ x4 ∈ x1, {x6 ∈ x1 ∩ x2 | x6 ⊆ x4}.biUnion id = x4 := by
  classical
  intro family base splitSet S hS
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_inter, id_eq]
  constructor
  · rintro ⟨T, ⟨_, hTS⟩, ha⟩
    exact hTS ha
  · intro ha
    have aux (n : ℕ) : ∀ T ∈ family, T.card = n → a ∈ T →
        ∃ R, ((R ∈ family ∧ R ∈ base) ∧ R ⊆ T) ∧ a ∈ R := by
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro T hT hcard haT
        by_cases hb : T ∈ base
        · exact ⟨T, ⟨⟨hT, hb⟩, Finset.Subset.rfl⟩, haT⟩
        · obtain ⟨A, hA, B, hB, hAT, hBT, hu⟩ := splitSet T (Finset.mem_sdiff.mpr ⟨hT, hb⟩)
          rw [hu, Finset.mem_union] at haT
          rcases haT with haA | haB
          · obtain ⟨R, ⟨hR, hRA⟩, haR⟩ :=
              ih A.card (hcard ▸ Finset.card_lt_card hAT) A hA rfl haA
            exact ⟨R, ⟨hR, hRA.trans hAT.le⟩, haR⟩
          · obtain ⟨R, ⟨hR, hRB⟩, haR⟩ :=
              ih B.card (hcard ▸ Finset.card_lt_card hBT) B hB rfl haB
            exact ⟨R, ⟨hR, hRB.trans hBT.le⟩, haR⟩
    exact aux S.card S hS rfl ha
