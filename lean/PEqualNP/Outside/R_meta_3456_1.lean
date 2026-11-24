import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit

theorem PEqualNP.Outside.R_meta_3456_1
  (h1 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    ∃ D1 : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D1 ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D1 ∧
      D1.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D1 z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ p : Fin N, (D1.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false))
  (h2 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D1 : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 D1 →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D1 →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D1 z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (∀ j < D1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ p : Fin N, (D1.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
      D.size ≤ D1.size ∧
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false))
  : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
      D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C hMono hReads hFun
  rcases h1 N I C hMono hReads hFun with ⟨D1, hMono1, hReads1, hSize1, hFun1, hAndP1⟩
  rcases h2 N I D1 hMono1 hReads1 hFun1 hAndP1 with ⟨D, hMono2, hReads2, hSize2, hFun2, hAndBoth⟩
  exact ⟨D, hMono2, hReads2, Nat.le_trans hSize2 hSize1, hFun2, hAndBoth⟩