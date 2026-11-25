import Mathlib
import PEqualNP.Defs

-- Cut of L-meta-9419: edges whose two junk gates hold the edge in their side rectangles, and the rest.
-- The first statement is proved by us from the rectangle bound of the accepted L-meta-8393 and follows as its own pull request.
theorem PEqualNP.Outside.R_meta_9419_7
    (rect : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → ∀ x10 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ x12 ∈ x10, ∃ (y1 : Fin x2) (y2 : Fin x2), x12 = s(y1, y2) ∧ ∃ y3 ∈ PEqualNP.TopForm.tops x3 x7, ∃ y4 ∈ PEqualNP.TopForm.junk x3 x7, ∃ y5 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 y3 (0 : Fin (2 : ℕ))) y4 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 y3 (1 : Fin (2 : ℕ))) y5 ∧ (∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x7 y4 y6 ∨ y2 ∈ PEqualNP.TopForm.side x7 y4 y6) ∧ (∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x7 y5 y6 ∨ y2 ∈ PEqualNP.TopForm.side x7 y5 y6)) → x10.card ≤ x1 * (x7.size + (1 : ℕ)))
    (deep : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → ∀ x10 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ x12 ∈ x10, ¬∃ (x14 : Fin x2) (x15 : Fin x2), x12 = s(x14, x15) ∧ ∃ x16 < x7.gates.length, ∃ (x17 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x16)).card ∧ (∀ x18 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x16), x3.Adj x14 x18) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x16 x17) = {x15}) → (∀ x13 ∈ x10, ∃ (x15 : Fin x2) (x16 : Fin x2), x13 = s(x15, x16) ∧ ∃ x17 ∈ PEqualNP.TopForm.tops x3 x7 \ PEqualNP.TopForm.centreless x3 x7, (∀ x18 ∈ PEqualNP.TopForm.side x7 x17 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x7 x17 (1 : Fin (2 : ℕ)), x18 ∉ s(x15, x16)) ∧ ∃ x18 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x19 ∈ PEqualNP.TopForm.junk x3 x7, x18 ≠ x19 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x17 (0 : Fin (2 : ℕ))) x18 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x17 (1 : Fin (2 : ℕ))) x19 ∧ ¬PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x17 (1 : Fin (2 : ℕ))) x18 ∧ ¬PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x17 (0 : Fin (2 : ℕ))) x19 ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x18 (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x19 (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.true ∧ ¬((∀ (y6 : Fin (2 : ℕ)), ∃ z ∈ x13, z ∈ PEqualNP.TopForm.side x7 x18 y6) ∧ ∀ (y6 : Fin (2 : ℕ)), ∃ z ∈ x13, z ∈ PEqualNP.TopForm.side x7 x19 y6)) → x10.card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → ∀ x10 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ x12 ∈ x10, ¬∃ (x14 : Fin x2) (x15 : Fin x2), x12 = s(x14, x15) ∧ ∃ x16 < x7.gates.length, ∃ (x17 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x16)).card ∧ (∀ x18 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x16), x3.Adj x14 x18) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x16 x17) = {x15}) → (∀ x13 ∈ x10, ∃ (x15 : Fin x2) (x16 : Fin x2), x13 = s(x15, x16) ∧ ∃ x17 ∈ PEqualNP.TopForm.tops x3 x7 \ PEqualNP.TopForm.centreless x3 x7, (∀ x18 ∈ PEqualNP.TopForm.side x7 x17 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x7 x17 (1 : Fin (2 : ℕ)), x18 ∉ s(x15, x16)) ∧ ∃ x18 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x19 ∈ PEqualNP.TopForm.junk x3 x7, x18 ≠ x19 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x17 (0 : Fin (2 : ℕ))) x18 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x17 (1 : Fin (2 : ℕ))) x19 ∧ ¬PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x17 (1 : Fin (2 : ℕ))) x18 ∧ ¬PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x17 (0 : Fin (2 : ℕ))) x19 ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x18 (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x19 (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.true) → x10.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨cA, hA⟩ := rect
  obtain ⟨cB, hB⟩ := deep
  refine ⟨cA + cB, ?_⟩
  intro n G inst hg hne C hL hT F hFU hpat hwit
  let P : Sym2 (Fin n) → Prop := fun e => ∃ x17 ∈ PEqualNP.TopForm.tops G C,
    ∃ x18 ∈ PEqualNP.TopForm.junk G C, ∃ x19 ∈ PEqualNP.TopForm.junk G C,
      PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x17 (0 : Fin 2)) x18 ∧
      PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x17 (1 : Fin 2)) x19 ∧
      (∀ (y6 : Fin 2), ∃ z ∈ e, z ∈ PEqualNP.TopForm.side C x18 y6) ∧
      (∀ (y6 : Fin 2), ∃ z ∈ e, z ∈ PEqualNP.TopForm.side C x19 y6)
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) P
  have h1 : (F.filter P).card ≤ cA * (C.size + 1) := by
    refine hA n G hg hne C hL hT (F.filter P) (fun e he => hFU (Finset.mem_filter.mp he).1) ?_
    intro e he
    obtain ⟨heF, t, ht, i, hi, j, hj, r0, r1, ri, rj⟩ := Finset.mem_filter.mp he
    obtain ⟨u, v, huv, -⟩ := hwit e heF
    subst huv
    refine ⟨u, v, rfl, t, ht, i, hi, j, hj, r0, r1, ?_, ?_⟩
    · intro b
      obtain ⟨z, hz, hs⟩ := ri b
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact Or.inl hs
      · exact Or.inr hs
    · intro b
      obtain ⟨z, hz, hs⟩ := rj b
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact Or.inl hs
      · exact Or.inr hs
  have h2 : (F.filter (fun e => ¬ P e)).card ≤ cB * (C.size + 1) := by
    refine hB n G hg hne C hL hT (F.filter (fun e => ¬ P e))
      (fun e he => hFU (Finset.mem_filter.mp he).1) ?_ ?_
    · intro e he
      exact hpat e (Finset.mem_filter.mp he).1
    · intro e he
      obtain ⟨heF, hnP⟩ := Finset.mem_filter.mp he
      obtain ⟨u, v, huv, t, ht, hsd, i, hi, j, hj, hij, r0, r1, n1, n0, g0, g1⟩ := hwit e heF
      refine ⟨u, v, huv, t, ht, hsd, i, hi, j, hj, hij, r0, r1, n1, n0, g0, g1, ?_⟩
      rintro ⟨ri, rj⟩
      exact hnP ⟨t, (Finset.mem_sdiff.mp ht).1, i, hi, j, hj, r0, r1, ri, rj⟩
  rw [← hsplit]
  nlinarith
