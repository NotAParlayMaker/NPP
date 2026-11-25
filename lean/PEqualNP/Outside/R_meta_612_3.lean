import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_612_3
    (h_leaf : ∀ (n t : ℕ) (G : SimpleGraph (Fin n))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∃ v : Fin n, (G.neighborSet v).ncard ≤ 1) →
        (∃ u v : Fin n, G.Adj u v) →
        (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
          G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
        (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
        (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
        G.edgeSet.ncard + t ≤ C.size + 1)
    (h_core : ∀ (n t : ℕ) (G : SimpleGraph (Fin n))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ v : Fin n, 2 ≤ (G.neighborSet v).ncard) →
        (∃ u v : Fin n, G.Adj u v) →
        (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
          G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
        (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
        (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
        G.edgeSet.ncard + t ≤ C.size + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard + t ≤ C.size + 1 := by
  intro n t G C hedge hc4 hcover hmin hmono hfun
  by_cases h : ∃ v : Fin n, (G.neighborSet v).ncard ≤ 1
  · exact h_leaf n t G C h hedge hc4 hcover hmin hmono hfun
  · push_neg at h
    exact h_core n t G C (fun v => by have := h v; omega) hedge hc4 hcover hmin hmono hfun
