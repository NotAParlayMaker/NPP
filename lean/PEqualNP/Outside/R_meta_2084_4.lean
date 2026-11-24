import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2084_4
    (strip : ∀ (n s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool),
        (∀ p v : Fin n, G.Adj p v → p ∉ A) →
        (∃ p v : Fin n, G.Adj p v) →
        (∀ x : Fin n → Bool, f x = true ↔
          (∃ a ∈ A, x a = true) ∨ ∃ p v : Fin n, G.Adj p v ∧ x p = true ∧ x v = true) →
        PEqualNP.MetaComplexity.HasCircuitSize n f s →
        ∃ (t : ℕ) (g : (Fin n → Bool) → Bool), A.card + t ≤ s ∧
          (∀ x : Fin n → Bool, g x = true ↔
            ∃ p v : Fin n, G.Adj p v ∧ x p = true ∧ x v = true) ∧
          PEqualNP.MetaComplexity.HasCircuitSize n g t)
    (cubic : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (g : (Fin n → Bool) → Bool),
        (∀ v : Fin n, (∃ w : Fin n, G.Adj v w) → (G.neighborSet v).ncard = 3) →
        (∀ (w : Fin n) (p : G.Walk w w), p.IsCycle → 7 ≤ p.length) →
        (∃ u v : Fin n, G.Adj u v) →
        (∀ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
        (∀ x : Fin n → Bool, g x = true ↔
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
        ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n g t → G.edgeSet.ncard + k ≤ t + 1) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (∀ x6 ∉ x4, (x3.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x3.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x3.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10) → (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x3.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x2 ≤ x10.card) → (∀ (x11 : Fin x1 → Bool), x5 x11 = Bool.true ↔ (∃ x12 ∈ x4, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → ∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x12 → x4.card + x3.edgeSet.ncard + x2 ≤ x12 + (1 : ℕ) := by
  intro n k G A f hdeg hgirth hiso hedge hcover hsem s hsize
  obtain ⟨t, g, hbudget, hgraph, hgsize⟩ :=
    strip n s G A f hiso hedge hsem hsize
  have hcubic (v : Fin n) (h : ∃ w, G.Adj v w) : (G.neighborSet v).ncard = 3 := by
    obtain ⟨w, hvw⟩ := h
    exact hdeg v (hiso v w hvw)
  have hbound := cubic n k G g hcubic hgirth hedge hcover hgraph t hgsize
  omega
