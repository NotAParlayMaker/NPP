import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]

theorem PEqualNP.Outside.R_meta_3456_1
  (h1 : ∃ (D1 : Circuit), Monotone2 D1 ∧ NestedCover.ReadsBack (N + N) D1 ∧ D1.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D1.gates.length, (NestedCover.gateAt D1 j).op = GateOp.and → (∀ p : Fin N, (D1.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false)))
  (h2 : ∀ (D1 : Circuit), Monotone2 D1 ∧ NestedCover.ReadsBack (N + N) D1 ∧ D1.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D1.gates.length, (NestedCover.gateAt D1 j).op = GateOp.and → (∀ p : Fin N, (D1.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false)) → ∃ (D : Circuit), Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ D1.size ∧ (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false))
  : ∃ (D : Circuit), Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  sorry