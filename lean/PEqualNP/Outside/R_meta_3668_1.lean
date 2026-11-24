import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3668_1
    (restrictInput : ∀ (n : ℕ) (C : Circuit) (v : Fin n),
      Monotone2 C → NestedCover.ReadsBack n C →
      ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧
        ∀ z : Fin n → Bool,
          circuitFun n D z = circuitFun n C (Function.update z v false))
    (normalize : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      (∀ (n : ℕ) (D : Circuit) (v : Fin n),
        Monotone2 D → NestedCover.ReadsBack n D →
        ∃ E : Circuit, Monotone2 E ∧ NestedCover.ReadsBack n E ∧ E.size ≤ D.size ∧
          ∀ z : Fin n → Bool,
            circuitFun n E z = circuitFun n D (Function.update z v false)) →
      Monotone2 C → NestedCover.ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool,
          circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
          (∀ p : Fin N,
            (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD
              (N + N + j) false = false) ∧
          ∀ l : Fin N,
            (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD
              (N + N + j) false = false)) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C
  exact normalize N I C restrictInput
