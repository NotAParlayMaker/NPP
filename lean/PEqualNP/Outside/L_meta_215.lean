import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_215 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)), (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (∀ w : Fin n, ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t ∧ w ∈ S) → n ≤ 2 * t := by
  intro n t G hmin hall
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · omega
  -- `U` is a union of least covers, `I` their intersection
  have key : ∀ W : Finset (Fin n), ∃ U I : Finset (Fin n), W ⊆ U ∧ I ⊆ U ∧
      (∀ u v : Fin n, G.Adj u v → u ∉ U → v ∈ I) ∧ U.card + I.card ≤ 2 * t := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      obtain ⟨C, hC, hct, _⟩ := hall ⟨0, hpos⟩
      refine ⟨C, C, Finset.empty_subset _, subset_rfl, ?_, by omega⟩
      intro u v huv hu
      rcases hC u v huv with h | h
      · exact absurd h hu
      · exact h
    | insert w W _ ih =>
      obtain ⟨U, I, hWU, hIU, hinv, hcard⟩ := ih
      obtain ⟨C, hC, hct, hwC⟩ := hall w
      refine ⟨U ∪ C, I ∩ C, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_union_right _ hwC
        · exact Finset.mem_union_left _ (hWU hx)
      · intro x hx
        exact Finset.mem_union_left _ (hIU (Finset.mem_inter.mp hx).1)
      · intro u v huv hu
        rw [Finset.mem_union, not_or] at hu
        refine Finset.mem_inter.mpr ⟨hinv u v huv hu.1, ?_⟩
        rcases hC u v huv with h | h
        · exact absurd h hu.2
        · exact h
      · -- the exchanged cover
        have hcov : ∀ u v : Fin n, G.Adj u v → u ∈ (C ∩ U) ∪ (I \ C) ∨ v ∈ (C ∩ U) ∪ (I \ C) := by
          have one : ∀ u v : Fin n, G.Adj u v → u ∈ C →
              u ∈ (C ∩ U) ∪ (I \ C) ∨ v ∈ (C ∩ U) ∪ (I \ C) := by
            intro u v huv huC
            by_cases huU : u ∈ U
            · exact Or.inl (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨huC, huU⟩))
            · have hvI : v ∈ I := hinv u v huv huU
              by_cases hvC : v ∈ C
              · exact Or.inr (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvC, hIU hvI⟩))
              · exact Or.inr (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvI, hvC⟩))
          intro u v huv
          rcases hC u v huv with h | h
          · exact one u v huv h
          · exact (one v u huv.symm h).symm
        have h1 := hmin _ hcov
        have h2 := Finset.card_union_le (C ∩ U) (I \ C)
        have h3 := Finset.card_union_add_card_inter U C
        have h4 := Finset.card_sdiff_add_card_inter I C
        have h5 : (U ∩ C).card = (C ∩ U).card := by rw [Finset.inter_comm]
        omega
  obtain ⟨U, I, hU, _, _, hcard⟩ := key Finset.univ
  have hUn : U.card = n := by
    have : U = Finset.univ := Finset.univ_subset_iff.mp hU
    rw [this]
    simp
  omega
