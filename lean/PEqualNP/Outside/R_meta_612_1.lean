import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_612_1
    (hNormalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (cen : ℕ → Fin n)
        (A : Finset ℕ),
        D.size ≤ C.size ∧
        PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ x : Fin n → Bool, (D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) ∧
        (∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
          D.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
        (∀ j ∈ A, ∀ x : Fin n → Bool,
          (D.wires (List.ofFn x)).getD (n + j) false = true →
            (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true) ∧
        (∀ j ∈ A, ∀ i ∈ A,
          ¬ Relation.TransGen
            (fun a b : ℕ => b < a ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
              D.gates[a]? = some g ∧ n + b ∈ g.inputs) j i))
    (hCount : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit) (cen : ℕ → Fin n) (A : Finset ℕ),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      (∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
        C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (∀ j ∈ A, ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = true →
          (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true) →
      (∀ j ∈ A, ∀ i ∈ A,
        ¬ Relation.TransGen
          (fun a b : ℕ => b < a ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
            C.gates[a]? = some g ∧ n + b ∈ g.inputs) j i) →
      G.edgeSet.ncard + (A.image cen).card ≤ C.size + 1)
    (hCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit) (cen : ℕ → Fin n) (A : Finset ℕ),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      (∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
        C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (∀ j ∈ A, ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = true →
          (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true) →
      PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (A.image cen)) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin n),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n),
        PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard + t ≤ C.size + 1 := by
  intro n t G C hEdge hC4 hCoverExists hMin hMono hf
  obtain ⟨D, cen, A, hSize, hDMono, hfD, hA, h4, h5⟩ :=
    hNormalize n G C hEdge hC4 hMono hf
  have hBound := hCount n G D cen A hC4 hDMono hfD hA h4 h5
  have hVertexCover := hCover n G D cen A hDMono hfD hA h4
  have ht : t ≤ (A.image cen).card := hMin _ hVertexCover
  omega
