import Mathlib
import PEqualNP.Defs

-- Cut of L-meta-9222: edges whose junk gates hold the edge in their side rectangles
-- The first statement is proved by us from the rectangle bound of the accepted L-meta-8393 and follows as its own pull request.
theorem PEqualNP.Outside.R_meta_9222_7
    (rect : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → ∀ x10 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ x12 ∈ x10, ∃ (y1 : Fin x2) (y2 : Fin x2), x12 = s(y1, y2) ∧ ∃ y3 ∈ PEqualNP.TopForm.tops x3 x7, ∃ y4 ∈ PEqualNP.TopForm.junk x3 x7, ∃ y5 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 y3 (0 : Fin (2 : ℕ))) y4 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 y3 (1 : Fin (2 : ℕ))) y5 ∧ (∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x7 y4 y6 ∨ y2 ∈ PEqualNP.TopForm.side x7 y4 y6) ∧ (∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x7 y5 y6 ∨ y2 ∈ PEqualNP.TopForm.side x7 y5 y6)) → x10.card ≤ x1 * (x7.size + (1 : ℕ)))
    (deep : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → ∀ x8 ⊆ PEqualNP.TopForm.Ustar x3 x5, (∀ x9 ∈ x8, ∃ x10 ∈ PEqualNP.TopForm.tops x3 x5 \ PEqualNP.TopForm.centreless x3 x5, ∃ x11 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x5, x11 ≠ x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x10 (0 : Fin (2 : ℕ))) x11 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x10 (1 : Fin (2 : ℕ))) x12 ∧ x9 ∈ PEqualNP.TopForm.gammaE x3 x5 x11 ∧ x9 ∈ PEqualNP.TopForm.gammaE x3 x5 x12) → (∀ x9 ∈ x8, ¬(∃ (y1 : Fin x2) (y2 : Fin x2), x9 = s(y1, y2) ∧ ∃ y3 ∈ PEqualNP.TopForm.tops x3 x5, ∃ y4 ∈ PEqualNP.TopForm.junk x3 x5, ∃ y5 ∈ PEqualNP.TopForm.junk x3 x5, PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 y3 (0 : Fin (2 : ℕ))) y4 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 y3 (1 : Fin (2 : ℕ))) y5 ∧ (∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x5 y4 y6 ∨ y2 ∈ PEqualNP.TopForm.side x5 y4 y6) ∧ (∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x5 y5 y6 ∨ y2 ∈ PEqualNP.TopForm.side x5 y5 y6))) → x8.card ≤ x1 * (x5.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ x10 ∈ PEqualNP.TopForm.tops x3 x5 \ PEqualNP.TopForm.centreless x3 x5, ∃ x11 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x5, x11 ≠ x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x10 (0 : Fin (2 : ℕ))) x11 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x10 (1 : Fin (2 : ℕ))) x12 ∧ x9 ∈ PEqualNP.TopForm.gammaE x3 x5 x11 ∧ x9 ∈ PEqualNP.TopForm.gammaE x3 x5 x12}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  classical
  obtain ⟨cA, hA⟩ := rect
  obtain ⟨cB, hB⟩ := deep
  refine ⟨cA + cB, ?_⟩
  intro n G inst C hg hL hT
  by_cases hne : G.edgeFinset.Nonempty
  swap
  · have hU : ∀ e, e ∉ PEqualNP.TopForm.Ustar G C := by
      intro e he
      unfold PEqualNP.TopForm.Ustar at he
      exact hne ⟨e, (Finset.mem_sdiff.mp he).1⟩
    refine le_trans (le_of_eq (Finset.card_eq_zero.mpr ?_)) (Nat.zero_le _)
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    exact hU e (Finset.mem_filter.mp he).1
  set F := ({x9 ∈ PEqualNP.TopForm.Ustar G C | ∃ x10 ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C, ∃ x11 ∈ PEqualNP.TopForm.junk G C, ∃ x12 ∈ PEqualNP.TopForm.junk G C, x11 ≠ x12 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x10 (0 : Fin (2 : ℕ))) x11 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x10 (1 : Fin (2 : ℕ))) x12 ∧ x9 ∈ PEqualNP.TopForm.gammaE G C x11 ∧ x9 ∈ PEqualNP.TopForm.gammaE G C x12} : Finset (Sym2 (Fin n))) with hF
  let P : Sym2 (Fin n) → Prop := fun e => ∃ (y1 : Fin n) (y2 : Fin n), e = s(y1, y2) ∧ ∃ y3 ∈ PEqualNP.TopForm.tops G C, ∃ y4 ∈ PEqualNP.TopForm.junk G C, ∃ y5 ∈ PEqualNP.TopForm.junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C y3 (0 : Fin (2 : ℕ))) y4 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C y3 (1 : Fin (2 : ℕ))) y5 ∧ (∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side C y4 y6 ∨ y2 ∈ PEqualNP.TopForm.side C y4 y6) ∧ (∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side C y5 y6 ∨ y2 ∈ PEqualNP.TopForm.side C y5 y6)
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) P
  have h1 : (F.filter P).card ≤ cA * (C.size + 1) := by
    refine hA n G hg hne C hL hT (F.filter P) (fun e he => ?_) ?_
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    · intro e he
      exact (Finset.mem_filter.mp he).2
  have h2 : (F.filter (fun e => ¬ P e)).card ≤ cB * (C.size + 1) := by
    refine hB n G C hg hL hT (F.filter (fun e => ¬ P e)) (fun e he => ?_) ?_ ?_
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    · intro e he
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    · intro e he
      exact (Finset.mem_filter.mp he).2
  rw [← hsplit]
  nlinarith
