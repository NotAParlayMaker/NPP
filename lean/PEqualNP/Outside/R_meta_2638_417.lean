import Mathlib
import PEqualNP.Defs

-- Delete the three incidences and record the degrees and distances in the remaining graph.
-- State the circuit bound using only that remaining graph and its three degree-two vertices.
theorem PEqualNP.Outside.R_meta_2638_417
    (shape : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (z : Fin n),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → z ∉ A →
      let H := G.deleteEdges (G.incidenceSet z)
      ∃ T : Finset (Fin n), T.card = 3 ∧
        (∀ v, (H.neighborSet v).ncard = if v ∈ A ∨ v = z then 0 else if v ∈ T then 2 else 3) ∧
        (∀ v ∈ T, v ∉ A ∧ v ≠ z) ∧
        (∀ u ∈ T, ∀ v ∈ T, u ≠ v → ∀ p : H.Walk u v, 5 ≤ p.length) ∧
        (∀ (v : Fin n) (p : H.Walk v v), p.IsCycle → 7 ≤ p.length))
    (bound : ∀ (n k s : ℕ) (H : SimpleGraph (Fin n)) (A T : Finset (Fin n)) (f : (Fin n → Bool) → Bool),
      T.card = 3 →
      (∀ v ∈ T, (H.neighborSet v).ncard = 2) →
      (∀ v ∉ T, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = 3) →
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v → ∀ p : H.Walk u v, 5 ≤ p.length) →
      (∀ (v : Fin n) (p : H.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, H.Adj u v → u ∉ A) →
      (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ S : Finset (Fin n), (∀ u v, H.Adj u v → u ∈ S ∨ v ∈ S) → k ≤ S.card) →
      PEqualNP.MetaComplexity.HasCircuitSize n f s →
      A.card + H.edgeSet.ncard + k ≤ s + 1)
    : ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  intro n k s G A z f regular girth outside _ zOutside computes cover size
  classical
  let H := G.deleteEdges (G.incidenceSet z)
  obtain ⟨T,count,degrees,members,distance,cycles⟩ := shape n G A z regular girth outside zOutside
  apply bound n k s H A T f count ?_ ?_ distance cycles ?_ computes cover size
  · intro v member
    obtain ⟨na,nz⟩ := members v member
    exact (degrees v).trans (by simp [na,nz,member])
  · intro v excluded
    by_cases hv : v ∈ A ∨ v = z
    · exact Or.inl ((degrees v).trans (by simp [hv]))
    · exact Or.inr ((degrees v).trans (by simp [hv,excluded]))
  · intro u v edge
    exact outside u v (SimpleGraph.deleteEdges_le _ edge)
