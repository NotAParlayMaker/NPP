import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- A vertex cover gives an explicit circuit with one owning AND for each nonempty star.
-- A least circuit that already has a witness at every AND can be retained directly.
theorem PEqualNP.Outside.R_meta_2450_57
    (construct : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (T : Finset (Fin n)), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ G.edgeFinset.card + T.card - 1 ∧ HasStarProfile n G D ∧
        ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          ∃ u v, G.Adj u v ∧ Owns n D j u v)
    (budget : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → HasStarProfile n G C →
      (∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        ∀ u v, G.Adj u v → ¬ Owns n C j u v) →
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        G.edgeFinset.card + T.card ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) → (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 → x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x4.size ≤ x9.size) → PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ PEqualNP.MetaComplexity.circuitFun x1 x11 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x11.size ≤ x4.size ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧ ∀ x12 < x11.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16 := by
  intro n G _ C triangle square mono correct least profile
  classical
  by_cases ready : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ u v, G.Adj u v ∧ Owns n C j u v
  · exact ⟨C, mono, correct, le_rfl, profile, ready⟩
  · have missing : ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        ∀ u v, G.Adj u v → ¬ Owns n C j u v := by
      by_contra none
      apply ready
      intro j hj op
      by_contra empty
      exact none ⟨j, hj, op, fun u v edge owned => empty ⟨u, v, edge, owned⟩⟩
    have minimal : IsMinimalMonoCircuit n C :=
      ⟨mono, fun D hD same => least D hD (same.trans correct)⟩
    obtain ⟨T, cover, cap⟩ := budget n G C triangle square minimal correct profile missing
    obtain ⟨D, hD, fn, size, stars, owns⟩ := construct n G T cover
    exact ⟨D, hD, fn, by omega, stars, owns⟩
