import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1900_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = Bool.true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true) →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (B T : Finset ℕ),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit n D ∧
        D.size ≤ C.size ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = Bool.true ↔
          ∃ u v : Fin n, G.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true) ∧
        T ⊆ Finset.range D.size ∧
        PEqualNP.MetaComplexity.NestedCover.IsOrTree n D T (B.image (fun j => n + j)) D.output ∧
        (∀ j ∈ B, j < D.size ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.CircuitMoves.WireBelowOutput n D (n + j)) ∧
        (∀ j < D.size, PEqualNP.CircuitMoves.WireBelowOutput n D (n + j) → j ∈ B ∨ j ∈ T))
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (B T : Finset ℕ),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a) →
      PEqualNP.MetaComplexity.IsMinimalMonoCircuit n D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = Bool.true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true) →
      T ⊆ Finset.range D.size →
      PEqualNP.MetaComplexity.NestedCover.IsOrTree n D T (B.image (fun j => n + j)) D.output →
      (∀ j ∈ B, j < D.size ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.CircuitMoves.WireBelowOutput n D (n + j)) →
      (∀ j < D.size, PEqualNP.CircuitMoves.WireBelowOutput n D (n + j) → j ∈ B ∨ j ∈ T) →
      PEqualNP.BicliqueBlockCost.HasBlockCost G D.size) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size :=
  fun x1 x2 x3 hEdge hC4 hMono hEval =>
    (h1 x1 x2 x3 hEdge hMono hEval).elim fun D hD =>
    hD.elim fun B hB0 =>
    hB0.elim fun T hP =>
    (h2 x1 x2 D B T hEdge hC4 hP.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1
      hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2).elim fun F hF =>
    ⟨F, hF.1, Nat.le_trans hF.2 hP.2.1⟩
