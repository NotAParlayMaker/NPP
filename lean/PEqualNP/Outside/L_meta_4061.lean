import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4061 :
    ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      (∀ a b : Fin 26, G.Adj a b ↔ ∃ p l : Fin 13,
        (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
            (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ v : Fin 26, v = 0 ∨ v = 1 ∨ v = 14 →
            PEqualNP.EdgeOwnership.gateVal 26 C j
              (PEqualNP.EdgeOwnership.pairInput 0 v) = false := by
  intro G _ hAdj C hLeast j hj hAnd v hv
