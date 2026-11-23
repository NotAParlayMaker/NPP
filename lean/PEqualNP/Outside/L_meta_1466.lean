import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1466 : ∀ (q : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1)))
    (X : Finset (Fin (q ^ 2 + q + 1))),
    2 ≤ q → (∀ i, (L i).card = q + 1) → (∀ i j, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i, p ∈ L i ∧ p' ∈ L i) →
    15 * q ≤ X.card + 8 →
    ∃ A : Finset (Fin (q ^ 2 + q + 1)), A ⊆ X ∧ A.card = 7 ∧ ∀ i, (L i ∩ A).card ≤ 2 := by
  intro q L X hq hL hI _ hX
  classical
  have step : ∀ k : ℕ, k ≤ 7 → ∃ A : Finset (Fin (q ^ 2 + q + 1)), A ⊆ X ∧ A.card = k ∧
      ∀ i, (L i ∩ A).card ≤ 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, by simp, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨A, hAX, hAk, hA⟩ := ih (by omega)
      obtain ⟨piece, hpc⟩ : ∃ piece : Finset (Fin (q ^ 2 + q + 1)) → Finset (Fin (q ^ 2 + q + 1)),
          piece = fun T => Finset.univ.filter (fun p => p ∉ T ∧ ∃ i, T ⊆ L i ∧ p ∈ L i) := ⟨_, rfl⟩
      have hpiece : ∀ T ∈ A.powersetCard 2, (piece T).card ≤ q - 1 := by
        intro T hT
        have hT2 := (Finset.mem_powersetCard.mp hT).2
        by_cases h : ∃ i0, T ⊆ L i0
        · obtain ⟨i0, hi0⟩ := h
          have hsub : piece T ⊆ L i0 \ T := by
            intro p hp
            rw [hpc] at hp
            obtain ⟨hpT, i, hTi, hpi⟩ := (Finset.mem_filter.mp hp).2
            have hii : i = i0 := by
              by_contra hne
              have h1 := hI i i0 hne
              have h2 : T ⊆ L i ∩ L i0 := Finset.subset_inter hTi hi0
              have h3 := Finset.card_le_card h2
              omega
            rw [hii] at hpi
            exact Finset.mem_sdiff.mpr ⟨hpi, hpT⟩
          have h4 := Finset.card_le_card hsub
          have h5 := Finset.card_sdiff_add_card_eq_card hi0
          have h6 := hL i0
          omega
        · have h0 : piece T = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro p hp
            rw [hpc] at hp
            obtain ⟨_, i, hTi, _⟩ := (Finset.mem_filter.mp hp).2
            exact h ⟨i, hTi⟩
          rw [h0]
          simp
      have hbad : (A ∪ (A.powersetCard 2).biUnion piece).card < X.card := by
        have h1 : ((A.powersetCard 2).biUnion piece).card ≤ (A.powersetCard 2).card * (q - 1) :=
          Finset.card_biUnion_le_card_mul _ _ _ hpiece
        rw [Finset.card_powersetCard, hAk] at h1
        have h2 : k.choose 2 ≤ 15 := by
          have h : k.choose 2 ≤ Nat.choose 6 2 := Nat.choose_le_choose 2 (by omega)
          have h' : Nat.choose 6 2 = 15 := by decide
          omega
        have h3 := Finset.card_union_le A ((A.powersetCard 2).biUnion piece)
        have h4 : k.choose 2 * (q - 1) ≤ 15 * (q - 1) := Nat.mul_le_mul_right _ h2
        omega
      obtain ⟨p, hpX, hpB⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
      have hpA : p ∉ A := fun h => hpB (Finset.mem_union_left _ h)
      refine ⟨insert p A, Finset.insert_subset hpX hAX,
        by rw [Finset.card_insert_of_notMem hpA, hAk], ?_⟩
      intro i
      by_cases hpi : p ∈ L i
      · rw [Finset.inter_insert_of_mem hpi]
        have hle : (L i ∩ A).card ≤ 1 := by
          by_contra hgt
          obtain ⟨T, hTs, hT2⟩ := Finset.exists_subset_card_eq (by omega : 2 ≤ (L i ∩ A).card)
          apply hpB
          apply Finset.mem_union_right
          refine Finset.mem_biUnion.mpr ⟨T, Finset.mem_powersetCard.mpr
            ⟨hTs.trans Finset.inter_subset_right, hT2⟩, ?_⟩
          rw [hpc]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            fun h => hpA (Finset.inter_subset_right (hTs h)), i,
            hTs.trans Finset.inter_subset_left, hpi⟩
        exact (Finset.card_insert_le _ _).trans (by omega)
      · rw [Finset.inter_insert_of_notMem hpi]
        exact hA i
  obtain ⟨A, h1, h2, h3⟩ := step 7 le_rfl
  exact ⟨A, h1, h2, h3⟩
