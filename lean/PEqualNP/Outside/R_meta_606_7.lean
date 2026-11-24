import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Prune the vertices of low degree. Deleting, one after the other, every vertex whose degree
-- is under a quarter of the average degree removes less than half of the edges, so the
-- conjecture is only needed for graphs where every vertex that is not isolated has degree at
-- least a quarter of the average. The first statement is that fact about graphs, the second
-- says that a circuit for a graph gives a circuit, one gate larger at most, for the graph
-- induced on any set of vertices (feed false to the other inputs), and the third is the
-- conjecture for the pruned graphs.
theorem PEqualNP.Outside.R_meta_606_7
    (prune : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∃ S : Finset (Fin n),
      ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      (∀ i j : Fin n, H.Adj i j ↔ G.Adj i j ∧ i ∈ S ∧ j ∈ S) →
      G.edgeFinset.card ≤ 2 * H.edgeFinset.card ∧
      ∀ v : Fin n, H.degree v = 0 ∨ G.edgeFinset.card ≤ 2 * n * H.degree v)
    (restrict : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
      (S : Finset (Fin n)), (∀ i j : Fin n, H.Adj i j ↔ G.Adj i j ∧ i ∈ S ∧ j ∈ S) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool =>
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ D' : Circuit, Monotone2 D' ∧ D'.size ≤ D.size + 1 ∧
        circuitFun n D' = (fun x : Fin n → Bool =>
          decide (∃ i j : Fin n, H.Adj i j ∧ x i = true ∧ x j = true)))
    (dense : ∃ c : ℕ, ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      (∀ (v : Fin n) (p : H.Walk v v), p.IsCycle → 5 ≤ p.length) →
      (∀ v : Fin n, H.degree v = 0 ∨ H.edgeFinset.card ≤ 2 * n * H.degree v) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool =>
        decide (∃ i j : Fin n, H.Adj i j ∧ x i = true ∧ x j = true)) →
      H.edgeFinset.card ≤ c * (D.size + 1)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨c, hc⟩ := dense
  refine ⟨4 * c, ?_⟩
  intro n G _ hg D hD hf
  obtain ⟨S, hS⟩ := prune n G
  obtain ⟨H, hH⟩ : ∃ H : SimpleGraph (Fin n),
      ∀ i j : Fin n, H.Adj i j ↔ G.Adj i j ∧ i ∈ S ∧ j ∈ S := by
    refine ⟨SimpleGraph.fromRel (fun i j : Fin n => G.Adj i j ∧ i ∈ S ∧ j ∈ S), ?_⟩
    intro i j
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, h | h⟩
      · exact h
      · exact ⟨h.1.symm, h.2.2, h.2.1⟩
    · intro h
      exact ⟨G.ne_of_adj h.1, Or.inl h⟩
  classical
  obtain ⟨h1, h2⟩ := hS H hH
  obtain ⟨D', hD', hsz, hf'⟩ := restrict n G H S hH D hD hf
  have hle : H ≤ G := fun i j h => ((hH i j).1 h).1
  have hgH : ∀ (v : Fin n) (p : H.Walk v v), p.IsCycle → 5 ≤ p.length := by
    intro v p hp
    simpa only [SimpleGraph.Walk.length_mapLe] using hg v (p.mapLe hle) (hp.mapLe hle)
  have hcard : H.edgeFinset.card ≤ G.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_subset_edgeFinset.2 hle)
  have h3 := hc n H hgH (fun v => (h2 v).imp id (fun h => le_trans hcard h)) D' hD' hf'
  have hm : c * (D'.size + 1) ≤ c * (2 * (D.size + 1)) := Nat.mul_le_mul_left c (by omega)
  have e : 4 * c * (D.size + 1) = 2 * (c * (2 * (D.size + 1))) := by ring
  omega
