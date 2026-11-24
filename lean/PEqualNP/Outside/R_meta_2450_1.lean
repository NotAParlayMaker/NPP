import Mathlib
import PEqualNP.Defs

-- First statement: in a least monotone fan-in-two circuit for the edge function of any graph,
-- every AND gate is true at the pair input of some edge. An AND gate false at every edge input
-- can be set to constant false without changing the function, and then removed.
-- Second statement: on graphs with no triangle and no 4-cycle, in a least circuit, an AND gate
-- true at the pair input of some edge owns some edge.
-- Together they show that the given least circuit itself already has every AND gate owning an
-- edge, so it is its own witness and keeps its star profile.
theorem PEqualNP.Outside.R_meta_2450_1 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
        PEqualNP.MetaComplexity.circuitFun n D =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → C.size ≤ D.size) →
      ∀ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = true) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
        PEqualNP.MetaComplexity.circuitFun n D =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → C.size ≤ D.size) →
      ∀ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        (∃ u v : Fin n, G.Adj u v ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = true) →
        ∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n C j u v) →
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) → (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 → x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x4.size ≤ x9.size) → PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ PEqualNP.MetaComplexity.circuitFun x1 x11 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x11.size ≤ x4.size ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧ ∀ x12 < x11.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16 := by
  intro hidle hshadow n G _ C htri hc4 hmono hfun hmin hstar
  refine ⟨C, hmono, hfun, le_refl _, hstar, ?_⟩
  intro j hj hand
  exact hshadow n G C htri hc4 hmono hfun hmin j hj hand
    (hidle n G C hmono hfun hmin j hj hand)
