import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- A nonempty circuit has a last gate, and IsAO2 says that gate is an AND or an OR; the empty
-- circuit has no gate and its read at index zero is the default OR. The step is asked once for
-- each of the two cases of that last gate.
theorem PEqualNP.Outside.R_meta_2389_613
    (lastAnd :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) C → (∀ (x3 : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) →
                (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                (64 : ℕ) ≤ C.size)
    (lastOr :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) C → (∀ (x3 : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) →
                (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
                (64 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (64 : ℕ) ≤ x1.size := by
  intro x1 hAO hEval
  have hsz : x1.size = x1.gates.length := rfl
  have hop : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hAO.1
  have hcase : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = GateOp.or := by
    rcases Nat.eq_zero_or_pos x1.size with _hz | hpos
    · right
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = PEqualNP.CircuitLowerBounds.Gate.mk GateOp.or [] := by
        show List.getD x1.gates (x1.size - (1 : ℕ))
            (PEqualNP.CircuitLowerBounds.Gate.mk GateOp.or []) = _
        apply List.getD_eq_default
        omega
      rw [hg]
    · have hj : x1.size - (1 : ℕ) < x1.gates.length := by rw [← hsz]; omega
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = x1.gates[x1.size - (1 : ℕ)] :=
        List.getD_eq_getElem _ _ hj
      rw [hg]
      exact hop _ (List.getElem_mem hj)
  rcases hcase with hand | har
  · exact lastAnd x1 hAO hEval hand
  · exact lastOr x1 hAO hEval har
