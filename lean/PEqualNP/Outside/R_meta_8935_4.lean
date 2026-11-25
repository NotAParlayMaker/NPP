import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

-- A cut of the bipartite, no-4-cycle bound by the OR gates that are not below the function and
-- lie outside the stars (the set orN minus lam) and by the centreless tops.
-- pure: no such OR gate at all. single: exactly one such OR gate and no centreless top.
-- Both hold for every two-coloured graph with no 4-cycle, with no assumption on junk gates.
-- rest: the step itself with the two closed cases excluded.
theorem PEqualNP.Outside.R_meta_8935_4
    (pure : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (col : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → col u ≠ col v) → NoFourCycle G → IsLeastAO G C → TopForm G C →
      orN G C \ lam G C = ∅ →
      ∃ K : Finset (Fin n), G.IsVertexCover (↑K : Set (Fin n)) ∧ G.edgeFinset.card + K.card ≤ C.size + 1)
    (single : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (col : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → col u ≠ col v) → NoFourCycle G → IsLeastAO G C → TopForm G C →
      centreless G C = ∅ → (orN G C \ lam G C).card = 1 →
      ∃ K : Finset (Fin n), G.IsVertexCover (↑K : Set (Fin n)) ∧ G.edgeFinset.card + K.card ≤ C.size + 1)
    (rest : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.IsBipartite → ¬ G.IsAcyclic → NoFourCycle G → IsLeastAO G C → TopForm G C →
      (∃ j < C.size, (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j ∧
        ∃ (a b c d : Fin n), G.Adj a b ∧ G.Adj c d ∧ s(a, b) ≠ s(c, d) ∧
          PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = false ∧
          PEqualNP.ReadK.readsAtMost C n [c.val, d.val] 1 = false ∧
          gateVal n C j (pairInput a b) = true ∧ gateVal n C j (pairInput c d) = true) →
      orN G C \ lam G C ≠ ∅ →
      (centreless G C = ∅ → (orN G C \ lam G C).card ≠ 1) →
      ∃ K : Finset (Fin n), G.IsVertexCover (↑K : Set (Fin n)) ∧ G.edgeFinset.card + K.card ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x11 : Finset (Fin x1)), x2.IsVertexCover ↑x11 ∧ x2.edgeFinset.card + x11.card ≤ x4.size + (1 : ℕ) := by
  intro n G inst C hbip hnac hno hL hT hj
  have two : ∀ a b : Fin 2, a ≠ b → decide (a = 0) ≠ decide (b = 0) := by decide
  obtain ⟨c⟩ := hbip
  have hcol : ∀ u v : Fin n, G.Adj u v →
      (fun w : Fin n => decide (c w = 0)) u ≠ (fun w : Fin n => decide (c w = 0)) v :=
    fun u v h => two (c u) (c v) (c.valid h)
  rcases Classical.em (orN G C \ lam G C = ∅) with hm | hm
  · exact pure n G C (fun w : Fin n => decide (c w = 0)) hcol hno hL hT hm
  · rcases Classical.em (centreless G C = ∅ ∧ (orN G C \ lam G C).card = 1) with hc | hc
    · exact single n G C (fun w : Fin n => decide (c w = 0)) hcol hno hL hT hc.1 hc.2
    · exact rest n G C ⟨c⟩ hnac hno hL hT hj hm (fun h0 h1 => hc ⟨h0, h1⟩)
