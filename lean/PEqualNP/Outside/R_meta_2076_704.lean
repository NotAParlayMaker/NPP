import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Peeling small edge cuts preserves all but a linear number of edges.
-- Each remaining independent probe must be distinguished from a far edge by a dirty AND.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2076_704
    (extract : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (H : SimpleGraph (Fin n)) (k : ℕ),
      IsLeastAO G C → H ≤ G →
      ∃ J : SimpleGraph (Fin n), J ≤ H ∧
        (∀ v, (J.neighborSet v).ncard = 0 ∨ k < (J.neighborSet v).ncard) ∧
        (∀ (D : Finset (Sym2 (Fin n))), D.card ≤ k → ∀ u v, J.Reachable u v → (J.deleteEdges ↑D).Reachable u v) ∧
        H.edgeSet.ncard ≤ J.edgeSet.ncard + k * (C.size + 1))
    (barren : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)),
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → H ≤ G →
      (∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) →
      (∀ u v, H.Adj u v →
        (∃ a ∈ A, G.Adj a u) ∨ ∃ a ∈ A, G.Adj a v) →
      (∀ v, (H.neighborSet v).ncard = 0 ∨ A.card < (H.neighborSet v).ncard) → H = ⊥)
    (pointwise : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (A : Finset (Fin n)) (u v : Fin n),
      IsAO2 n C → circuitFun n C = graphFun G ∅ →
      (∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) → G.Adj u v → s(u, v) ∉ starEdges G C →
      (∀ j ∈ junk G C, gateVal n C j (pairInput u v) = true → gateVal n C j (fun i => decide (i ∈ A)) = true) →
        (∃ a ∈ A, G.Adj a u) ∨ ∃ a ∈ A, G.Adj a v)
    (remaining : ∃ k c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (J : SimpleGraph (Fin n)),
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → G.edgeFinset.Nonempty →
      IsLeastAO G C → TopForm G C → J ≤ G.deleteEdges ↑(starEdges G C) → J ≠ ⊥ →
      (∀ v, (J.neighborSet v).ncard = 0 ∨ k < (J.neighborSet v).ncard) →
      (∀ (D : Finset (Sym2 (Fin n))), D.card ≤ k → ∀ u v, J.Reachable u v → (J.deleteEdges ↑D).Reachable u v) →
      (∀ A : Finset (Fin n), (∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) →
        (A.card ≤ k → ∃ u v : Fin n, J.Adj u v ∧ (∀ a ∈ A, ¬G.Adj a u ∧ ¬G.Adj a v)) ∧
        (∀ u v : Fin n, J.Adj u v → (∀ a ∈ A, ¬G.Adj a u ∧ ¬G.Adj a v) →
          ∃ j ∈ junk G C, gateVal n C j (pairInput u v) = true ∧ gateVal n C j (fun i => decide (i ∈ A)) = false)) →
      J.edgeSet.ncard ≤ c * (C.size+1))
    : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k,c,hard⟩ := remaining
  refine ⟨c+k, ?_⟩
  intro n G inst girth hEdge C H least top hdel _
  obtain ⟨J,jh,hdeg,stable,cost⟩ := extract n G C H k least (hdel.trans (G.deleteEdges_le _))
  have jd := jh.trans hdel
  have bound : J.edgeSet.ncard ≤ c*(C.size+1) := by
    by_cases hBot : J = ⊥
    · simp [hBot]
    apply hard n G C J girth hEdge least top jd hBot hdeg stable
    intro A independent
    constructor
    · intro ha
      by_contra hn
      apply hBot
      apply barren n G J A girth (jd.trans (G.deleteEdges_le _)) independent _
        (fun v => (hdeg v).imp_right (fun h => lt_of_le_of_lt ha h))
      intro u v huv
      by_contra! h
      exact hn ⟨u,v,huv, fun a ha => ⟨h.1 a ha,h.2 a ha⟩⟩
    · intro u v huv away
      have hE := SimpleGraph.deleteEdges_adj.mp (jd huv)
      apply Classical.byContradiction
      intro none
      have same (j) (hj : j ∈ junk G C) (hp : gateVal n C j (pairInput u v) = true) :
          gateVal n C j (fun i => decide (i ∈ A)) = true := by
        cases ht : gateVal n C j (fun i => decide (i ∈ A)) with
        | false => exact False.elim (none ⟨j,hj,hp,ht⟩)
        | true => rfl
      have contact := pointwise n G C A u v least.1 least.2.1 independent hE.1 hE.2 same
      rcases contact with ⟨a,ha,h⟩ | ⟨a,ha,h⟩
      · exact (away a ha).1 h
      · exact (away a ha).2 h
  calc
    H.edgeSet.ncard ≤ J.edgeSet.ncard + k*(C.size+1) := cost
    _ ≤ c*(C.size+1) + k*(C.size+1) := Nat.add_le_add_right bound _
    _ = (c+k)*(C.size+1) := (Nat.add_mul _ _ _).symm
