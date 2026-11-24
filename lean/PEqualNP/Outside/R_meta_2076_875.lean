import Mathlib
import PEqualNP.Defs

open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- In a graph of girth at least five, the endpoints of a maximal matching
-- cover every edge. Pairs of endpoints bound the edges in a core of minimum degree three.
theorem PEqualNP.Outside.R_meta_2076_875
    (extract : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (H : SimpleGraph (Fin n)),
      IsLeastAO G C → H≤G → ∃ (J : SimpleGraph (Fin n)) (A B : Finset (Fin n)), J≤H ∧ J.IsBipartiteWith A B ∧
      (∀ v : Fin n, (J.neighborSet v).ncard=0 ∨ 3≤(J.neighborSet v).ncard) ∧ H.edgeSet.ncard≤2*J.edgeSet.ncard+4*(C.size+1))
    (packing : ∀ (n : ℕ) (G J : SimpleGraph (Fin n)), (∀ v (w : G.Walk v v), w.IsCycle → 5≤w.length) → J≤G → (∀ v : Fin n, (J.neighborSet v).ncard=0 ∨ 3≤(J.neighborSet v).ncard) →
      ∃ M : J.Subgraph, M.IsMatching ∧ 2*J.edgeSet.ncard≤M.verts.ncard*(M.verts.ncard-1))
    (large : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (J : SimpleGraph (Fin n)) (A B : Finset (Fin n)), (∀ v (w : G.Walk v v), w.IsCycle → 5≤w.length) → G.edgeFinset.Nonempty →
      IsLeastAO G C → TopForm G C → J≤G.deleteEdges ↑(starEdges G C) → J.IsBipartiteWith A B →
      (∀ v : Fin n, (J.neighborSet v).ncard=0 ∨ 3≤(J.neighborSet v).ncard) → (∃ M : J.Subgraph, M.IsMatching ∧ 2*(C.size+1)<M.verts.ncard*(M.verts.ncard-1)) →
      J.edgeSet.ncard≤k*(C.size+1))
    : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k,price⟩ := large
  refine ⟨2*(k+1)+4,?_⟩
  intro n G d girth edges C H least top sub _
  have chain := sub.trans (G.deleteEdges_le _)
  obtain ⟨J,A,B,below,parts,dense,cost⟩ := extract n G C H least chain
  obtain ⟨M,matching,bound⟩ := packing n G J girth (below.trans chain) dense
  have hj : J.edgeSet.ncard≤(k+1)*(C.size+1) := by
    by_cases high : 2*(C.size+1)<M.verts.ncard*(M.verts.ncard-1)
    · exact (price n G C J A B girth edges least top (below.trans sub) parts dense ⟨M,matching,high⟩).trans
        (Nat.mul_le_mul_right _ (Nat.le_succ k))
    · rw [Nat.add_mul,Nat.one_mul]
      omega
  calc
    H.edgeSet.ncard ≤ 2*J.edgeSet.ncard+4*(C.size+1) := cost
    _ ≤ 2*((k+1)*(C.size+1))+4*(C.size+1) := by omega
    _ = _ := by ring
