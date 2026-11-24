import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G _ hN U hU x Y hY R π hπ hcov
  have hkey : ∀ B ∈ π, ∀ a ∈ B, ∀ b ∈ B, a ≠ b → a ∈ Y → G.Adj x b → False := by
    intro B hB a ha b hb hab haY hxb
    obtain ⟨_, h1 | ⟨_, c, hc, hcU⟩⟩ := hπ B hB
    · obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp h1
      simp only [Finset.mem_singleton] at ha hb
      exact hab (ha.trans hb.symm)
    · have hxa : G.Adj x a := by simpa using hU _ (hY a haY)
      have hcx : x ≠ c := by
        rintro rfl
        exact hcU a ha (hY a haY)
      have hle := hN x c hcx
      exact hab (Finset.card_le_one.mp hle a (by simp [hxa, hc a ha]) b (by simp [hxb, hc b hb]))
  have hgen : ∀ Z : Finset (Fin n), Z ⊆ R → (∀ B ∈ π, (B ∩ Z).card ≤ 1) → Z.card ≤ π.card := by
    intro Z hZ h1
    have hsub : Z ⊆ π.biUnion (fun B => B ∩ Z) := by
      intro z hz
      obtain ⟨B, hB, hzB⟩ := hcov z (hZ hz)
      exact Finset.mem_biUnion.mpr ⟨B, hB, Finset.mem_inter.mpr ⟨hzB, hz⟩⟩
    calc Z.card ≤ (π.biUnion (fun B => B ∩ Z)).card := Finset.card_le_card hsub
      _ ≤ ∑ B ∈ π, (B ∩ Z).card := Finset.card_biUnion_le
      _ ≤ ∑ B ∈ π, 1 := Finset.sum_le_sum h1
      _ = π.card := by simp
  refine ⟨?_, ?_⟩
  · apply hgen (R ∩ Y) Finset.inter_subset_left
    intro B hB
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    simp only [Finset.mem_inter] at ha hb
    exact hkey B hB a ha.1 b hb.1 hab ha.2.2 (by simpa using hU _ (hY b hb.2.2))
  · intro hRx hRY
    obtain ⟨r, hrR, hrY⟩ := Finset.not_subset.mp hRY
    have hcard : (insert r (R ∩ Y)).card = (R ∩ Y).card + 1 := by
      apply Finset.card_insert_of_notMem
      simp [hrY]
    rw [← hcard]
    apply hgen
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hrR
      · exact (Finset.mem_inter.mp hz).1
    intro B hB
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    simp only [Finset.mem_inter, Finset.mem_insert] at ha hb
    have haR : a ∈ R := (hπ B hB).1 ha.1
    have hbR : b ∈ R := (hπ B hB).1 hb.1
    rcases ha.2 with rfl | ha2
    · rcases hb.2 with rfl | hb2
      · exact hab rfl
      · exact hkey B hB b hb.1 a ha.1 (Ne.symm hab) hb2.2 (hRx a haR)
    · exact hkey B hB a ha.1 b hb.1 hab ha2.2 (hRx b hbR)
