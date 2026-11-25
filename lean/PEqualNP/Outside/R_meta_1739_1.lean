import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1739_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) = Bool.true ↔ ∃ i j : Fin n, G.Adj i j ∧ x i = Bool.true ∧ x j = Bool.true) →
        G.edgeSet.ncard ≤ C.size)
    (h2 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∃ i j : Fin n, G.Adj i j) →
        (∀ (a b c d : Fin n), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
        (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
        (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) = Bool.true ↔ ∃ i j : Fin n, G.Adj i j ∧ x i = Bool.true ∧ x j = Bool.true) →
        t - 1 ≤ C.size - G.edgeSet.ncard)
    : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x5 : Fin x1) (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x6 ≠ x8 → x6 ≠ x9 → x7 ≠ x8 → x7 ≠ x9 → x8 ≠ x9 → x3.Adj x6 x7 → x3.Adj x7 x8 → x3.Adj x8 x9 → ¬x3.Adj x9 x6) → (∃ (x7 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x3 x7 ∧ x7.card = x2) → (∀ (x8 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x3 x8 → x2 ≤ x8.card) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin x1 → Bool), x4.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x3.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ¬x3.IsAcyclic → x3.edgeSet.ncard + x2 ≤ x4.size + (1 : ℕ) := by
  intro n t G C hE hno4 hcov hmin hM hev hcyc
  have hA := h1 n G C hM hev
  have hB := h2 n t G C hE hno4 hcov hmin hM hev
  omega
