import Mathlib
import PEqualNP.Defs

-- A cut of L-meta-8897 by the presence of an AND gate.  A circuit with no AND gate is a single
-- OR of the input wires, so the negative side is a genuinely restricted class, and the positive
-- side is the case where the AND structure carries the argument.
theorem PEqualNP.Outside.R_meta_8897_733
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 →
      (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ)) →
      (∃ (j : Fin x1.gates.length),
        (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (64 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 →
      (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ)) →
      ¬ (∃ (j : Fin x1.gates.length),
        (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (64 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 →
      (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ)) →
      (64 : ℕ) ≤ x1.size := by
  intro x1 hmono hinc hdeg
  by_cases h : (∃ (j : Fin x1.gates.length),
      (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  · exact h1 x1 hmono hinc hdeg h
  · exact h2 x1 hmono hinc hdeg h
