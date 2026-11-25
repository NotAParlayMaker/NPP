import Mathlib
import PEqualNP.Defs

-- A reduction of the two-junk step: the two junk AND gates are either nested in one
-- another's cone or incomparable.  In either case the missing construction is a circuit
-- that computes the same edge function with strictly fewer gates, which contradicts
-- leastness.  The two children below are the two constructions.
theorem PEqualNP.Outside.R_meta_5012_1
    (nested : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
      (PEqualNP.TopForm.junk G C).card = 2 →
      (∃ g ∈ PEqualNP.TopForm.junk G C, ∃ h ∈ PEqualNP.TopForm.junk G C,
        g ≠ h ∧ (PEqualNP.EdgeOwnership.InCone n C g h ∨
          PEqualNP.EdgeOwnership.InCone n C h g)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n D ∧
        PEqualNP.MetaComplexity.circuitFun n D =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        D.size < C.size)
    (apart : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
      (PEqualNP.TopForm.junk G C).card = 2 →
      (∃ g ∈ PEqualNP.TopForm.junk G C, ∃ h ∈ PEqualNP.TopForm.junk G C,
        g ≠ h ∧ ¬ PEqualNP.EdgeOwnership.InCone n C g h ∧
          ¬ PEqualNP.EdgeOwnership.InCone n C h g) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n D ∧
        PEqualNP.MetaComplexity.circuitFun n D =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        D.size < C.size) :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
      (PEqualNP.TopForm.junk G C).card ≠ 1) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
      (PEqualNP.TopForm.junk G C).card ≠ 2 := by
  intro hfirst n G _ C s hbip hfour hleast htwo
  classical
  obtain ⟨g, h, hgh, hset⟩ := Finset.card_eq_two.mp htwo
  have hgj : g ∈ PEqualNP.TopForm.junk G C := by
    rw [hset]
    simp
  have hhj : h ∈ PEqualNP.TopForm.junk G C := by
    rw [hset]
    simp
  rcases hleast with ⟨hAO, hFun, hmin⟩
  by_cases hcone : PEqualNP.EdgeOwnership.InCone n C g h ∨
      PEqualNP.EdgeOwnership.InCone n C h g
  · obtain ⟨D, hDAO, hDFun, hDlt⟩ :=
      nested n G C s hbip hfour ⟨hAO, hFun, hmin⟩ htwo ⟨g, hgj, h, hhj, hgh, hcone⟩
    have := hmin D hDAO hDFun
    omega
  · push_neg at hcone
    obtain ⟨D, hDAO, hDFun, hDlt⟩ :=
      apart n G C s hbip hfour ⟨hAO, hFun, hmin⟩ htwo
        ⟨g, hgj, h, hhj, hgh, hcone.1, hcone.2⟩
    have := hmin D hDAO hDFun
    omega
