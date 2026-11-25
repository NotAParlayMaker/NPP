import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4848_743
    (firstSource : ∀ (n : ℕ) (C : Circuit) (a b : Fin n), Monotone2 C →
    (∃ i < C.gates.length, (gateAt C i).op = GateOp.and ∧
      gateVal n C i (pairInput a b) = true) →
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      ∀ w ∈ (gateAt C j).inputs, w < n+j ∧ (a ∈ orIn n C w ∨ b ∈ orIn n C w))
    (blocked : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
    ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ a b : Fin n, ¬G.Adj a b →
    ∃ w ∈ (gateAt C j).inputs, n+j ≤ w ∨ (a ∉ orIn n C w ∧ b ∉ orIn n C w)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x9 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x6 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true → x2.Adj x12 x13 := by
  intro n G inst tri sq C least exactG j hj andGate a b lit
  by_contra absent
  obtain ⟨k,hk,op,sources⟩ := firstSource n C a b least.1 ⟨j,hj,andGate,lit⟩
  obtain ⟨w,hw,invalid | missing⟩ := blocked n G tri sq C least exactG k hk op a b absent
  · exact (Nat.not_le_of_lt (sources w hw).1) invalid
  · exact (sources w hw).2.elim missing.1 missing.2
