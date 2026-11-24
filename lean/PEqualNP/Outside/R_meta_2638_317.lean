import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2638_317
    (cEmpty : ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool),
      (∀ (x8 : Fin x1), (x4.neighborSet x8).ncard = (3 : ℕ)) →
      (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
      (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) →
      (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) →
      (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) →
      PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 →
      (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ))
    (cNonempty : ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool),
      x5.Nonempty →
      (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) →
      (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
      (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) →
      (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) →
      x6 ∉ x5 →
      (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) →
      (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) →
      PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 →
      x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ)) :
    ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 x6 x7 hdeg hgirth hdisj hedge hx6 hfun hvc hcs
  rcases Finset.eq_empty_or_nonempty x5 with rfl | hne
  · have h0 := cEmpty x1 x2 x3 x4 x6 x7
      (fun v => hdeg v (Finset.notMem_empty v))
      hgirth hedge
      (fun z => by simpa using hfun z)
      hvc hcs
    simpa using h0
  · exact cNonempty x1 x2 x3 x4 x5 x6 x7 hne hdeg hgirth hdisj hedge hx6 hfun hvc hcs
