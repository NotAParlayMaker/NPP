import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4051_317
    (cLe1 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool),
      (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) →
      (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) →
      (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) →
      (∀ (x7 : Fin x1 → Bool), x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) →
      ∀ (x8 : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ x8 →
        (∀ z : Fin x1 → Bool, C.eval (List.ofFn z) = x3 z) →
        (∀ v : Fin x1, (x2.neighborSet v).ncard = (3 : ℕ) → (C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val ≤ (1 : ℕ)) →
        ∃ (x10 : Fin x1), (x2.neighborSet x10).ncard = (3 : ℕ) ∧ ∃ (x11 : ℕ), x11 + (4 : ℕ) ≤ x8 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update x12 x10 Bool.false)) x11)
    (cEq2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool),
      (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) →
      (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) →
      (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) →
      (∀ (x7 : Fin x1 → Bool), x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) →
      ∀ (x8 : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ x8 →
        (∀ z : Fin x1 → Bool, C.eval (List.ofFn z) = x3 z) →
        (∀ v : Fin x1, (x2.neighborSet v).ncard = (3 : ℕ) → (C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val ≤ (2 : ℕ)) →
        (∃ v : Fin x1, (x2.neighborSet v).ncard = (3 : ℕ) ∧ (C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val = (2 : ℕ)) →
        ∃ (x10 : Fin x1), (x2.neighborSet x10).ncard = (3 : ℕ) ∧ ∃ (x11 : ℕ), x11 + (4 : ℕ) ≤ x8 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update x12 x10 Bool.false)) x11)
    (cGe3 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool),
      (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) →
      (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) →
      (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) →
      (∀ (x7 : Fin x1 → Bool), x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) →
      ∀ (x8 : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ x8 →
        (∀ z : Fin x1 → Bool, C.eval (List.ofFn z) = x3 z) →
        (∃ v : Fin x1, (x2.neighborSet v).ncard = (3 : ℕ) ∧ (3 : ℕ) ≤ (C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val) →
        ∃ (x10 : Fin x1), (x2.neighborSet x10).ncard = (3 : ℕ) ∧ ∃ (x11 : ℕ), x11 + (4 : ℕ) ≤ x8 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update x12 x10 Bool.false)) x11) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 : Fin x1 → Bool), x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x8 → ∃ (x10 : Fin x1), (x2.neighborSet x10).ncard = (3 : ℕ) ∧ ∃ (x11 : ℕ), x11 + (4 : ℕ) ≤ x8 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update x12 x10 Bool.false)) x11 := by
  intro x1 x2 x3 hdeg hgirth hedge hfun x8 hcs
  obtain ⟨C, hfan, hsize, hev⟩ := hcs
  by_cases h3 : ∃ v : Fin x1, (x2.neighborSet v).ncard = 3 ∧ 3 ≤ (C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val
  · exact cGe3 x1 x2 x3 hdeg hgirth hedge hfun x8 C hfan hsize hev h3
  · have hle2 : ∀ v : Fin x1, (x2.neighborSet v).ncard = 3 → (C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val ≤ 2 := by
      intro v hv
      by_contra hgt
      exact h3 ⟨v, hv, by omega⟩
    by_cases h2 : ∃ v : Fin x1, (x2.neighborSet v).ncard = 3 ∧ (C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val = 2
    · exact cEq2 x1 x2 x3 hdeg hgirth hedge hfun x8 C hfan hsize hev hle2 h2
    · have hle1 : ∀ v : Fin x1, (x2.neighborSet v).ncard = 3 → (C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val ≤ 1 := by
        intro v hv
        have hlt := hle2 v hv
        by_contra hgt
        exact h2 ⟨v, hv, by omega⟩
      exact cLe1 x1 x2 x3 hdeg hgirth hedge hfun x8 C hfan hsize hev hle1
