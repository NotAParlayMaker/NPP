import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5262_1
    (h1 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ @PEqualNP.TopForm.side x2 x7 x11 (0 : Fin 2) = ∅ ∧ @PEqualNP.TopForm.side x2 x7 x11 (1 : Fin 2) = ∅}.card ≤ x1 * (x7.size + (1 : ℕ)))
    (h2 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ ((@PEqualNP.TopForm.side x2 x7 x11 (0 : Fin 2) = ∅ ∧ (@PEqualNP.TopForm.side x2 x7 x11 (1 : Fin 2)).Nonempty) ∨ ((@PEqualNP.TopForm.side x2 x7 x11 (0 : Fin 2)).Nonempty ∧ @PEqualNP.TopForm.side x2 x7 x11 (1 : Fin 2) = ∅))}.card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  refine ⟨c1 + c2, ?_⟩
  intro x2 x3 inst hGirth hNE x7 hLeast hTF
  have hb1 := hc1 x2 x3 hGirth hNE x7 hLeast hTF
  have hb2 := hc2 x2 x3 hGirth hNE x7 hLeast hTF
  have hsub :
      {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11} ⊆
      {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ @PEqualNP.TopForm.side x2 x7 x11 (0 : Fin 2) = ∅ ∧ @PEqualNP.TopForm.side x2 x7 x11 (1 : Fin 2) = ∅} ∪
      {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ ((@PEqualNP.TopForm.side x2 x7 x11 (0 : Fin 2) = ∅ ∧ (@PEqualNP.TopForm.side x2 x7 x11 (1 : Fin 2)).Nonempty) ∨ ((@PEqualNP.TopForm.side x2 x7 x11 (0 : Fin 2)).Nonempty ∧ @PEqualNP.TopForm.side x2 x7 x11 (1 : Fin 2) = ∅))} := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_union] at he ⊢
    obtain ⟨heU, hno, g, hgC, heg⟩ := he
    have hgSide : @PEqualNP.TopForm.side x2 x7 g (0 : Fin 2) = ∅ ∨ @PEqualNP.TopForm.side x2 x7 g (1 : Fin 2) = ∅ := by
      simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hgC
      exact hgC.2
    by_cases h0 : @PEqualNP.TopForm.side x2 x7 g (0 : Fin 2) = ∅
    · by_cases h1e : @PEqualNP.TopForm.side x2 x7 g (1 : Fin 2) = ∅
      · exact Or.inl ⟨heU, hno, g, hgC, heg, h0, h1e⟩
      · exact Or.inr ⟨heU, hno, g, hgC, heg, Or.inl ⟨h0, Finset.nonempty_iff_ne_empty.mpr h1e⟩⟩
    · rcases hgSide with h0' | h1e
      · exact absurd h0' h0
      · exact Or.inr ⟨heU, hno, g, hgC, heg, Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr h0, h1e⟩⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  calc
    _ ≤ _ := hle
    _ ≤ c1 * (x7.size + 1) + c2 * (x7.size + 1) := Nat.add_le_add hb1 hb2
    _ = (c1 + c2) * (x7.size + 1) := (Nat.add_mul c1 c2 (x7.size + 1)).symm
