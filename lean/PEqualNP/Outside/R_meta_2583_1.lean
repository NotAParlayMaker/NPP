import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2583_1
    (hgraph : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      ∃ G : SimpleGraph (Fin (N + N)), ∃ _hAdj : DecidableRel G.Adj,
        PEqualNP.TopForm.NoFourCycle G ∧ G.edgeFinset.Nonempty ∧
        ∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ z =
            decide (∃ p l : Fin N, I p l ∧
              z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hnorm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ C0 : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C0 ∧ PEqualNP.TopForm.TopForm G C0 ∧ C0.size ≤ C.size)
    (hblocks : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ z =
          decide (∃ p l : Fin N, I p l ∧
            z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) D ∧
        PEqualNP.MetaComplexity.circuitFun (N + N) D =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z =
          decide (∃ p l : Fin N, I p l ∧
            z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) D ∧
        (∀ y : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D y =
            decide (∃ p l : Fin N, I p l ∧
              y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  intro q N I hI C hq hN hdegree hpair hC hEval
  obtain ⟨G, _hAdj, hNo4, hEdge, hGraph⟩ := hgraph q N I hq hN hdegree hpair
  have hEq : PEqualNP.MetaComplexity.circuitFun (N + N) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hEval z, hGraph z]
  obtain ⟨C0, hLeast, hTop, hC0Size⟩ := hnorm (N + N) G C hC hEq
  obtain ⟨D, hD, hDEq, hDSize, hRead⟩ :=
    hblocks q N I G C0 hq hN hdegree hpair hNo4 hEdge hGraph hLeast hTop
  refine ⟨D, hD, ?_, ?_, hRead⟩
  · intro y
    rw [congrFun hDEq y, hGraph y]
  · omega
