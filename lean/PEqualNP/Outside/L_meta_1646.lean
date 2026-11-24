import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1646

theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False)
    (U : Finset (Sym2 (Fin n))) (hU : ∀ e ∈ U, e ∈ G.edgeSet) (x : Fin n) (Y : Finset (Fin n))
    (hY : ∀ y ∈ Y, s(x, y) ∈ U) (B : Finset (Fin n))
    (hB : 2 ≤ B.card ∧ ∃ c : Fin n, (∀ y ∈ B, G.Adj c y) ∧ ∀ y ∈ B, s(c, y) ∉ U) :
    (B ∩ Y).card ≤ 1 ∧ ((∀ b ∈ B, G.Adj x b) → B ∩ Y = ∅) := by
  obtain ⟨h2, c, hc, hcU⟩ := hB
  have hxy : ∀ y ∈ Y, G.Adj x y := fun y hy => by
    have := hU _ (hY y hy)
    simpa using this
  have hcx : ∀ y ∈ B ∩ Y, x ≠ c := by
    intro y hy hxc
    rw [Finset.mem_inter] at hy
    exact hcU y hy.1 (hxc ▸ hY y hy.2)
  constructor
  · apply Finset.card_le_one.2
    intro y hy y' hy'
    by_contra hne
    have h1 := Finset.mem_inter.1 hy
    have h2' := Finset.mem_inter.1 hy'
    exact hno x c y y' (hcx y hy) hne (hxy y h1.2) (hc y h1.1) (hxy y' h2'.2) (hc y' h2'.1)
  · intro hall
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have h1 := Finset.mem_inter.1 hy
    obtain ⟨b, hb, hby⟩ := Finset.exists_mem_ne (by omega : 1 < B.card) y
    exact hno x c y b (hcx y hy) (Ne.symm hby) (hxy y h1.2) (hc y h1.1) (hall b hb) (hc b hb)

end PEqualNP.Outside.L_meta_1646

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  classical
  intro n G _ hnf U hU x Y hY R π hπ hcov
  have hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False := by
    intro s t w w' hst hww h1 h2 h3 h4
    exact hww (Finset.card_le_one.1 (hnf s t hst) w (by simp [h1, h2]) w' (by simp [h3, h4]))
  -- a block holds at most one point of `Y`
  have one : ∀ B ∈ π, (B ∩ Y).card ≤ 1 := by
    intro B hB
    rcases (hπ B hB).2 with h1 | h2
    · exact (Finset.card_le_card Finset.inter_subset_left).trans h1.le
    · exact (PEqualNP.Outside.L_meta_1646.core n G hno U hU x Y hY B h2).1
  have hex : ∀ y : Fin n, ∃ B, y ∈ R ∩ Y → B ∈ π ∧ y ∈ B := by
    intro y
    by_cases hy : y ∈ R ∩ Y
    · obtain ⟨B, hB, hyB⟩ := hcov y (Finset.mem_inter.1 hy).1
      exact ⟨B, fun _ => ⟨hB, hyB⟩⟩
    · exact ⟨∅, fun h => absurd h hy⟩
  choose f hf using hex
  have hinj : Set.InjOn f ((R ∩ Y : Finset (Fin n)) : Set (Fin n)) := by
    intro y hy y' hy' hff
    have hy1 : y ∈ R ∩ Y := hy
    have hy1' : y' ∈ R ∩ Y := hy'
    have h1 := hf y hy1
    have h2 := hf y' hy1'
    rw [← hff] at h2
    exact Finset.card_le_one.1 (one (f y) h1.1) y
      (Finset.mem_inter.2 ⟨h1.2, (Finset.mem_inter.1 hy1).2⟩) y'
      (Finset.mem_inter.2 ⟨h2.2, (Finset.mem_inter.1 hy1').2⟩)
  constructor
  · exact Finset.card_le_card_of_injOn f (fun y hy => (hf y hy).1) hinj
  · intro hadj hnot
    obtain ⟨r, hrR, hrY⟩ := Finset.not_subset.1 hnot
    obtain ⟨B0, hB0, hrB0⟩ := hcov r hrR
    have hmiss : ∀ y ∈ R ∩ Y, f y ≠ B0 := by
      intro y hy hfy
      have h1 := hf y hy
      rw [hfy] at h1
      have hyY := (Finset.mem_inter.1 hy).2
      rcases (hπ B0 hB0).2 with hc | h2
      · have := Finset.card_le_one.1 hc.le y h1.2 r hrB0
        exact hrY (this ▸ hyY)
      · have hempty := (PEqualNP.Outside.L_meta_1646.core n G hno U hU x Y hY B0 h2).2
          (fun b hb => hadj b ((hπ B0 hB0).1 hb))
        have : y ∈ B0 ∩ Y := Finset.mem_inter.2 ⟨h1.2, hyY⟩
        rw [hempty] at this
        simp at this
    have hle : (R ∩ Y).card ≤ (π.erase B0).card :=
      Finset.card_le_card_of_injOn f (fun y hy => by
        have hy' : y ∈ R ∩ Y := hy
        exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hmiss y hy', (hf y hy').1⟩)) hinj
    rw [Finset.card_erase_of_mem hB0] at hle
    have hpos : 0 < π.card := Finset.card_pos.2 ⟨B0, hB0⟩
    omega
