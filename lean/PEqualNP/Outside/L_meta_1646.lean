import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PEqualNP.TopForm.NoFourCycle G →
      ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) →
      ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) →
      ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))),
        (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧
            ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) →
        (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') →
        (R ∩ Y).card ≤ π.card ∧
        ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G _ h4 U hU x Y hY R π hblocks hcover
  -- every block covers at most one vertex of Y
  have blockY : ∀ B ∈ π, (B ∩ Y).card ≤ 1 := by
    intro B hB
    obtain ⟨hsub, hshape⟩ := hblocks B hB
    rcases hshape with h1 | hbig
    · exact (Finset.card_le_card Finset.inter_subset_left).trans_eq h1
    · obtain ⟨_, c, hadj, hUc⟩ := hbig
      by_contra hcard
      push_neg at hcard
      obtain ⟨b1, hb1, b2, hb2, hne⟩ := Finset.one_lt_card.mp hcard
      obtain ⟨hb1B, hb1Y⟩ := Finset.mem_inter.mp hb1
      obtain ⟨hb2B, hb2Y⟩ := Finset.mem_inter.mp hb2
      have hxc : x ≠ c := by
        intro heq
        subst heq
        exact hUc b1 hb1B (hY b1 hb1Y)
      have hsub2 : ({b1, b2} : Finset (Fin n)) ⊆
          Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj c w) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hw with rfl | rfl
        · exact ⟨hU _ (hY _ hb1Y), hadj _ hb1B⟩
        · exact ⟨hU _ (hY _ hb2Y), hadj _ hb2B⟩
      have h2le : 2 ≤ (Finset.univ.filter fun w => G.Adj x w ∧ G.Adj c w).card :=
        calc 2 = ({b1, b2} : Finset (Fin n)).card := by simp [hne]
          _ ≤ _ := Finset.card_le_card hsub2
      have hle1 := h4 x c hxc
      omega
  -- the blocks reaching Y cover R ∩ Y
  have hsub : R ∩ Y ⊆ π.biUnion (fun B => B ∩ Y) := by
    intro r hr
    obtain ⟨hrR, hrY⟩ := Finset.mem_inter.mp hr
    obtain ⟨B, hBπ, hrB⟩ := hcover r hrR
    exact Finset.mem_biUnion.mpr ⟨B, hBπ, Finset.mem_inter.mpr ⟨hrB, hrY⟩⟩
  have hcardRY : (R ∩ Y).card ≤ ∑ B ∈ π, (B ∩ Y).card :=
    calc (R ∩ Y).card ≤ (π.biUnion fun B => B ∩ Y).card := Finset.card_le_card hsub
      _ ≤ ∑ B ∈ π, (B ∩ Y).card := Finset.card_biUnion_le
  refine ⟨?_, ?_⟩
  · calc (R ∩ Y).card ≤ ∑ B ∈ π, (B ∩ Y).card := hcardRY
      _ ≤ ∑ _B ∈ π, 1 := Finset.sum_le_sum fun B hB => blockY B hB
      _ = π.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  · intro hxR hnsub
    obtain ⟨r0, hr0R, hr0Y⟩ := Finset.not_subset.mp hnsub
    obtain ⟨B0, hB0π, hr0B⟩ := hcover r0 hr0R
    have hB0Y : B0 ∩ Y = ∅ := by
      obtain ⟨hsub0, hshape0⟩ := hblocks B0 hB0π
      rcases hshape0 with h1c | hbig
      · obtain ⟨b, hbeq⟩ := Finset.card_eq_one.mp h1c
        subst hbeq
        rw [Finset.mem_singleton] at hr0B
        subst hr0B
        rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_singleton_left]
        exact hr0Y
      · obtain ⟨_, c, hadj, hUc⟩ := hbig
        by_contra hne
        obtain ⟨y0, hy0⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        obtain ⟨hy0B, hy0Y⟩ := Finset.mem_inter.mp hy0
        have hxc : x ≠ c := by
          intro heq
          subst heq
          exact hUc y0 hy0B (hY y0 hy0Y)
        have hy0R : y0 ∈ R := hsub0 hy0B
        have hsub2 : ({r0, y0} : Finset (Fin n)) ⊆
            Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj c w) := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hw with rfl | rfl
          · exact ⟨hxR _ hr0R, hadj _ hr0B⟩
          · exact ⟨hxR _ hy0R, hadj _ hy0B⟩
        have hne' : r0 ≠ y0 := fun h => hr0Y (h ▸ hy0Y)
        have h2le : 2 ≤ (Finset.univ.filter fun w => G.Adj x w ∧ G.Adj c w).card :=
          calc 2 = ({r0, y0} : Finset (Fin n)).card := by simp [hne']
            _ ≤ _ := Finset.card_le_card hsub2
        have hle1 := h4 x c hxc
        omega
    have hsplit := Finset.add_sum_erase π (fun B => (B ∩ Y).card) hB0π
    rw [hB0Y] at hsplit
    simp only [Finset.card_empty, zero_add] at hsplit
    have hrest : ∑ B ∈ π.erase B0, (B ∩ Y).card ≤ (π.erase B0).card := by
      calc ∑ B ∈ π.erase B0, (B ∩ Y).card
          ≤ ∑ _B ∈ π.erase B0, 1 :=
            Finset.sum_le_sum fun B hB => blockY B (Finset.mem_of_mem_erase hB)
        _ = (π.erase B0).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem hB0π] at hrest
    calc (R ∩ Y).card + 1 ≤ ∑ B ∈ π, (B ∩ Y).card + 1 := Nat.succ_le_succ hcardRY
      _ = ∑ B ∈ π.erase B0, (B ∩ Y).card + 1 := by rw [← hsplit]
      _ ≤ π.card - 1 + 1 := Nat.add_le_add_right hrest 1
      _ = π.card := by
          have : 1 ≤ π.card := Finset.card_pos.mpr ⟨B0, hB0π⟩
          omega
