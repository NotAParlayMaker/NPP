import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2582_419
    (h_norm :
      ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 n C →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 n C' ∧
          (∀ z : Fin n → Bool,
            PEqualNP.MetaComplexity.circuitFun n C' z = PEqualNP.MetaComplexity.circuitFun n C z) ∧
          (∀ E : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.TopForm.IsAO2 n E →
            (∀ z : Fin n → Bool,
              PEqualNP.MetaComplexity.circuitFun n E z = PEqualNP.MetaComplexity.circuitFun n C z) →
            C'.size ≤ E.size) ∧
          (∀ i < C'.size, ∀ j < C'.size,
            PEqualNP.CircuitMoves.WireBelowOutput n C' (n + i) →
            (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ¬ PEqualNP.EdgeOwnership.InCone n C' i j))
    (h_flat :
      ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.TopForm.andPairs n C = 0 →
        PEqualNP.ReadK.IsReadK n C 2)
    (h_nested :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
        2 ≤ q →
        N = q ^ 2 + q + 1 →
        (∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) →
        (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
        PEqualNP.TopForm.IsAO2 (N + N) C →
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) C z =
            decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
        (∀ E : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 (N + N) E →
          (∀ z : Fin (N + N) → Bool,
            PEqualNP.MetaComplexity.circuitFun (N + N) E z =
              decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
          C.size ≤ E.size) →
        (∀ i < C.size, ∀ j < C.size,
          PEqualNP.CircuitMoves.WireBelowOutput (N + N) C (N + N + i) →
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ¬ PEqualNP.EdgeOwnership.InCone (N + N) C i j) →
        0 < PEqualNP.TopForm.andPairs (N + N) C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 (N + N) D ∧
          (∀ y : Fin (N + N) → Bool,
            PEqualNP.MetaComplexity.circuitFun (N + N) D y =
              decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
          D.size ≤ C.size ∧
          PEqualNP.ReadK.IsReadK (N + N) D 2) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2 := by
  intro q N I inst C hq hN hdeg huniq hAO hfun
  obtain ⟨C', hAO', hfun', hmin', hlift'⟩ := h_norm (N + N) C hAO
  have hC'fun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C' z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :=
    fun z => (hfun' z).trans (hfun z)
  have hC'le : C'.size ≤ C.size := hmin' C hAO (fun _ => rfl)
  by_cases hflat : PEqualNP.TopForm.andPairs (N + N) C' = 0
  · exact ⟨C', hAO', hC'fun, hC'le, h_flat (N + N) C' hAO' hflat⟩
  · have hmin'' : ∀ E : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) E →
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) E z =
            decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
        C'.size ≤ E.size := by
      intro E hE hEfun
      exact hmin' E hE (fun z => (hEfun z).trans (hfun z).symm)
    obtain ⟨D, hDAO, hDfun, hDsize, hDread⟩ :=
      h_nested q N I C' hq hN (fun l => by simpa only [Fintype.card_subtype] using hdeg l)
        huniq hAO' hC'fun hmin'' hlift' (Nat.pos_of_ne_zero hflat)
    exact ⟨D, hDAO, hDfun, hDsize.trans hC'le, hDread⟩
