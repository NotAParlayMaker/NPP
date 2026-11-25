import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5126_1
    (hFlag : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
    (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
    (∀ k ∈ PEqualNP.TopForm.junk G C, ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
    ∀ k1 ∈ PEqualNP.TopForm.junk G C, ∀ k2 ∈ PEqualNP.TopForm.junk G C, k1 ≠ k2 →
    (∃ u v : Fin n, u ≠ v ∧ PEqualNP.SplitCount.singletonSet n C k1 = {u} ∧ PEqualNP.SplitCount.singletonSet n C k2 = {v}) →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C' ∧ (PEqualNP.TopForm.junk G C').card = 1)
    (hRect : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
    (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
    (∀ k ∈ PEqualNP.TopForm.junk G C, ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
    ∀ k1 ∈ PEqualNP.TopForm.junk G C, ∀ k2 ∈ PEqualNP.TopForm.junk G C, k1 ≠ k2 →
    (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, 2 < (PEqualNP.TopForm.side (n := n) C a b).card ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) k1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a (1 - b)) k2) →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C' ∧ (PEqualNP.TopForm.junk G C').card = 1)
    (hFactor : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
    (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
    (∀ k ∈ PEqualNP.TopForm.junk G C, ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
    ∀ k1 ∈ PEqualNP.TopForm.junk G C, ∀ k2 ∈ PEqualNP.TopForm.junk G C, k1 ≠ k2 →
    ¬ (∃ u v : Fin n, u ≠ v ∧ PEqualNP.SplitCount.singletonSet n C k1 = {u} ∧ PEqualNP.SplitCount.singletonSet n C k2 = {v}) → ¬ (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, 2 < (PEqualNP.TopForm.side (n := n) C a b).card ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) k1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a (1 - b)) k2) →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C' ∧ (PEqualNP.TopForm.junk G C').card = 1) :
(∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (PEqualNP.TopForm.junk G C).card ≠ 1) →
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (∀ k ∈ PEqualNP.TopForm.junk G C, ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
  (PEqualNP.TopForm.junk G C).card ≠ 2 := by
  intro H
  intro n G instG C s hcol hnfc hleast honhot
  by_contra hcard2
  rcases Finset.card_eq_two.mp hcard2 with ⟨k1, k2, hk12, hset⟩
  have hk1 : k1 ∈ PEqualNP.TopForm.junk G C := by
    rw [hset]
    simp
  have hk2 : k2 ∈ PEqualNP.TopForm.junk G C := by
    rw [hset]
    simp
  by_cases hP1 : ∃ u v : Fin n, u ≠ v ∧ PEqualNP.SplitCount.singletonSet n C k1 = {u} ∧ PEqualNP.SplitCount.singletonSet n C k2 = {v}
  · rcases hFlag n G C s hcol hnfc hleast honhot k1 hk1 k2 hk2 hk12 hP1 with ⟨C', hleast', hcard1⟩
    exact (H n G C' s hcol hnfc hleast') hcard1
  · by_cases hP2 : ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, 2 < (PEqualNP.TopForm.side (n := n) C a b).card ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) k1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a (1 - b)) k2
    · rcases hRect n G C s hcol hnfc hleast honhot k1 hk1 k2 hk2 hk12 hP2 with ⟨C', hleast', hcard1⟩
      exact (H n G C' s hcol hnfc hleast') hcard1
    · rcases hFactor n G C s hcol hnfc hleast honhot k1 hk1 k2 hk2 hk12 hP1 hP2 with ⟨C', hleast', hcard1⟩
      exact (H n G C' s hcol hnfc hleast') hcard1
