import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CircuitMoves

theorem PEqualNP.Outside.R_meta_2670_661
    (lowDirty : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (j : ℕ),
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      j < C.size → (gateAt C j).op = .and → (∀ u v, G.Adj u v → ¬ Owns n C j u v) →
      let count (D : Circuit) := {i : ℕ | i < D.size ∧ (gateAt D i).op = .and ∧
        ∀ u v, G.Adj u v → ¬ Owns n D i u v}.ncard
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      (∃ a b, G.Adj a b) → (junk G C).card ≤ 1 →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧ count D < count C)
    (singlePivotal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (j : ℕ),
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      j < C.size → (gateAt C j).op = .and → (∀ u v, G.Adj u v → ¬ Owns n C j u v) →
      let count (D : Circuit) := {i : ℕ | i < D.size ∧ (gateAt D i).op = .and ∧
        ∀ u v, G.Adj u v → ¬ Owns n D i u v}.ncard
      let pivotal (u v : Fin n) := G.Adj u v ∧
        circuitFun n (eraseGate n C j (n+C.size)) (pairInput u v) = false
      ∀ u v, pivotal u v → gateVal n C j (pairInput u v) = true →
      (∀ a b, pivotal a b → (a=u ∧ b=v) ∨ (a=v ∧ b=u)) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧ count D < count C)
    (manyPivotal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (j : ℕ),
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      j < C.size → (gateAt C j).op = .and → (∀ u v, G.Adj u v → ¬ Owns n C j u v) →
      let count (D : Circuit) := {i : ℕ | i < D.size ∧ (gateAt D i).op = .and ∧
        ∀ u v, G.Adj u v → ¬ Owns n D i u v}.ncard
      let pivotal (u v : Fin n) := G.Adj u v ∧
        circuitFun n (eraseGate n C j (n+C.size)) (pairInput u v) = false
      ∀ u v, pivotal u v → gateVal n C j (pairInput u v) = true →
      (∃ a b, pivotal a b ∧ ¬ ((a=u ∧ b=v) ∨ (a=v ∧ b=u))) →
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      2 ≤ (junk G C).card →
      (∀ i<j, (gateAt C i).op = .and → ∃ a b, G.Adj a b ∧ Owns n C i a b) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧ count D < count C) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => {x7 : ℕ | x7 < x6.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → ¬PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9}.ncard;       ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x13 x14 : Fin x1), x2.Adj x13 x14 → ¬PEqualNP.EdgeOwnership.Owns x1 x7 x10 x13 x14) → (∀ x14 < x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x17 : Fin x1) (x18 : Fin x1), x2.Adj x17 x18 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x14 x17 x18) → ∀ (x15 x16 : Fin x1), x2.Adj x15 x16 → PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 (PEqualNP.CircuitMoves.eraseGate x1 x7 x10 (x1 + x7.gates.length)) (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.false → ∃ (x20 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x20 ∧ PEqualNP.MetaComplexity.circuitFun x1 x20 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x20.size ≤ x7.size ∧ x6 x20 < x6 x7 := by
  intro n G _ triangle no4 ownerCount C least sem j range kind unowned earlier u v edge on deleted
  by_cases few : (junk G C).card ≤ 1
  · exact lowDirty n G C j least sem range kind unowned triangle no4 ⟨u,v,edge⟩ few
  let pivotal (a b : Fin n) := G.Adj a b ∧
    circuitFun n (eraseGate n C j (n+C.size)) (pairInput a b) = false
  have thisOne : pivotal u v := ⟨edge,deleted⟩
  classical
  by_cases multiple : ∃ a b, pivotal a b ∧ ¬ ((a=u ∧ b=v) ∨ (a=v ∧ b=u))
  · exact manyPivotal n G C j least sem range kind unowned u v thisOne on multiple triangle no4 (by omega) earlier
  · apply singlePivotal n G C j least sem range kind unowned u v thisOne on
    intro a b row
    by_contra off
    exact multiple ⟨a,b,row,off⟩
