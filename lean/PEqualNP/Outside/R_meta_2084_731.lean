import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- Each marked isolated variable costs a gate before the graph-only lower bound.
theorem PEqualNP.Outside.R_meta_2084_731 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool),
      (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∀ s, HasCircuitSize n f s → ∃ t, t + A.card ≤ s ∧ HasCircuitSize n (fun x : Fin n → Bool =>
        @decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) t) →
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (p : G.Walk w w), p.IsCycle → 7 ≤ p.length) →
      (∃ i j, G.Adj i j) →
      (∀ S : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ S ∨ j ∈ S) → k ≤ S.card) →
      ∀ s, HasCircuitSize n (fun x : Fin n → Bool =>
        @decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → G.edgeSet.ncard + k ≤ s + 1) →
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by
  classical
  intro peel core n k G A f deg girth isolated hedge cover calculated s circuit
  have degree (v : Fin n) : (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3 := by
    by_cases h : v ∈ A
    · left
      have empty : G.neighborSet v = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro w hit
        exact isolated v w hit h
      simp [empty]
    · exact Or.inr (deg v h)
  obtain ⟨t, saved, restricted⟩ := peel n G A f isolated hedge calculated s circuit
  have lower := core n k G degree girth hedge cover t restricted
  omega
