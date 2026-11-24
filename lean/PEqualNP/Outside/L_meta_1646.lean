import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1646

theorem block_inter_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' → G.Adj t w' → False)
    (U : Finset (Sym2 (Fin n))) (hU : ∀ e ∈ U, e ∈ G.edgeSet)
    (x : Fin n) (Y : Finset (Fin n)) (hY : ∀ y ∈ Y, s(x, y) ∈ U)
    (B : Finset (Fin n))
    (hB : B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U)) :
    (B ∩ Y).card ≤ 1 := by
  rcases hB with h1 | ⟨_, c, hcAdj, hcU⟩
  · exact (Finset.card_le_card Finset.inter_subset_left).trans (le_of_eq h1)
  · refine Finset.card_le_one.2 ?_
    intro y₁ hy₁ y₂ hy₂
    by_contra hne
    obtain ⟨hy₁B, hy₁Y⟩ := Finset.mem_inter.1 hy₁
    obtain ⟨hy₂B, hy₂Y⟩ := Finset.mem_inter.1 hy₂
    have hxy₁ : G.Adj x y₁ := by simpa [SimpleGraph.mem_edgeSet] using hU _ (hY y₁ hy₁Y)
    have hxy₂ : G.Adj x y₂ := by simpa [SimpleGraph.mem_edgeSet] using hU _ (hY y₂ hy₂Y)
    have hcx : c ≠ x := by
      intro h; subst h
      exact hcU y₁ hy₁B (hY y₁ hy₁Y)
    exact hno c x y₁ y₂ hcx hne (hcAdj y₁ hy₁B) hxy₁ (hcAdj y₂ hy₂B) hxy₂

theorem block_inter_empty_of_not_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' → G.Adj t w' → False)
    (U : Finset (Sym2 (Fin n)))
    (x : Fin n) (Y : Finset (Fin n)) (hY : ∀ y ∈ Y, s(x, y) ∈ U)
    (R B : Finset (Fin n)) (hBR : B ⊆ R) (hRx : ∀ v ∈ R, G.Adj x v)
    (hB : B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))
    (r₀ : Fin n) (hr₀B : r₀ ∈ B) (hr₀Y : r₀ ∉ Y) :
    B ∩ Y = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  obtain ⟨hyB, hyY⟩ := Finset.mem_inter.1 hy
  rcases hB with h1 | ⟨h2, c, hcAdj, hcU⟩
  · have heq : y = r₀ := Finset.card_le_one.1 (le_of_eq h1) y hyB r₀ hr₀B
    exact hr₀Y (heq ▸ hyY)
  · have hcx : c ≠ x := by
      intro h; subst h
      exact hcU y hyB (hY y hyY)
    obtain ⟨b, hbB, hby⟩ : ∃ b ∈ B, b ≠ y := by
      by_contra h
      push Not at h
      have hsub : B ⊆ {y} := fun b hb => Finset.mem_singleton.2 (h b hb)
      have := Finset.card_le_card hsub
      simp at this
      omega
    exact hno c x y b hcx (Ne.symm hby) (hcAdj y hyB) (hRx y (hBR hyB))
      (hcAdj b hbB) (hRx b (hBR hbB))

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G _ hnf U hU x Y hY R π hπ hcov
  have hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False := by
    intro s t w w' hst hww h1 h2 h3 h4
    exact hww (Finset.card_le_one.1 (hnf s t hst) w (by simp [h1, h2]) w' (by simp [h3, h4]))
  have hcard_one : ∀ B ∈ π, (B ∩ Y).card ≤ 1 := fun B hB =>
    block_inter_card_le_one G hno U hU x Y hY B (hπ B hB).2
  constructor
  · have hsub : R ∩ Y ⊆ π.biUnion (fun B => B ∩ Y) := by
      intro r hr
      obtain ⟨hrR, hrY⟩ := Finset.mem_inter.1 hr
      obtain ⟨B, hBπ, hrB⟩ := hcov r hrR
      exact Finset.mem_biUnion.2 ⟨B, hBπ, Finset.mem_inter.2 ⟨hrB, hrY⟩⟩
    calc (R ∩ Y).card
        ≤ (π.biUnion (fun B => B ∩ Y)).card := Finset.card_le_card hsub
      _ ≤ ∑ B ∈ π, (B ∩ Y).card := Finset.card_biUnion_le
      _ ≤ ∑ _B ∈ π, 1 := Finset.sum_le_sum hcard_one
      _ = π.card := by simp
  · intro hRx hnotSub
    obtain ⟨r₀, hr₀R, hr₀Y⟩ : ∃ r₀ ∈ R, r₀ ∉ Y := by
      by_contra h
      push Not at h
      exact hnotSub h
    obtain ⟨B₀, hB₀π, hr₀B₀⟩ := hcov r₀ hr₀R
    have hB₀empty : B₀ ∩ Y = ∅ :=
      block_inter_empty_of_not_mem G hno U x Y hY R B₀ (hπ B₀ hB₀π).1 hRx (hπ B₀ hB₀π).2
        r₀ hr₀B₀ hr₀Y
    have hsub : R ∩ Y ⊆ (π.erase B₀).biUnion (fun B => B ∩ Y) := by
      intro r hr
      obtain ⟨hrR, hrY⟩ := Finset.mem_inter.1 hr
      obtain ⟨B, hBπ, hrB⟩ := hcov r hrR
      have hne : B ≠ B₀ := by
        intro heq; subst heq
        have : r ∈ B ∩ Y := Finset.mem_inter.2 ⟨hrB, hrY⟩
        rw [hB₀empty] at this
        exact Finset.notMem_empty r this
      exact Finset.mem_biUnion.2 ⟨B, Finset.mem_erase.2 ⟨hne, hBπ⟩, Finset.mem_inter.2 ⟨hrB, hrY⟩⟩
    have hle : (R ∩ Y).card ≤ (π.erase B₀).card := by
      calc (R ∩ Y).card
          ≤ ((π.erase B₀).biUnion (fun B => B ∩ Y)).card := Finset.card_le_card hsub
        _ ≤ ∑ B ∈ π.erase B₀, (B ∩ Y).card := Finset.card_biUnion_le
        _ ≤ ∑ _B ∈ π.erase B₀, 1 := Finset.sum_le_sum (fun B hB => hcard_one B (Finset.mem_of_mem_erase hB))
        _ = (π.erase B₀).card := by simp
    have herase : (π.erase B₀).card + 1 = π.card := Finset.card_erase_add_one hB₀π
    omega

end PEqualNP.Outside.L_meta_1646

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) :=
  PEqualNP.Outside.L_meta_1646.main
