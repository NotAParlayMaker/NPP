import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2391_1
    (upper : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [inst : DecidableRel G.Adj], (∀ (x4 x5 : Fin (26 : ℕ)), G.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 26 C ∧ PEqualNP.MetaComplexity.circuitFun 26 C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C.size ≤ 64)
    (lower : ∀ (G : SimpleGraph (Fin (26 : ℕ))) [inst : DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), G.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsAO2 26 C → PEqualNP.MetaComplexity.circuitFun 26 C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → (PEqualNP.TopForm.junk G C).Nonempty → 65 ≤ C.size) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 = ∅ := by
  intro G inst C hgraph hleast
  obtain ⟨D, hD, hfun, hsize⟩ := upper G hgraph
  have hbound := hleast.2.2 D hD hfun
  by_contra hne
  have hbad := lower G C hgraph hleast.1 hleast.2.1 (Finset.nonempty_iff_ne_empty.mpr hne)
  omega
