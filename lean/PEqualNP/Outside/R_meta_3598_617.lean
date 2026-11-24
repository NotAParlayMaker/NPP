import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3598_617
    (privatePoint : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], (∀ l, Fintype.card {p : Fin N // I p l} = q+1) → (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) → (∀ (S : Finset (Fin N)), S.card ≤ q → ∀ l ∉ S, ∃ p, I p l ∧ ∀ k ∈ S, ¬ I p k))
    (sensitiveInput : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (S : Finset (Fin N)), S.card ≤ q → ∀ l ∉ S, ∃ p, I p l ∧ ∀ k ∈ S, ¬ I p k) → PEqualNP.MetaComplexity.Monotone2 C → N+N ≤ C.output → C.output < N+N+C.size → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[C.output-(N+N)]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ j (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → ∃ a b : ℕ, g.inputs = [a,b] ∧ a<b ∧ b<N+N+j) → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N+N) C (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) → (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q → (¬∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N+N) C x = false) → (∀ (S : Finset (Fin N)), S.card ≤ q →
        let x : Fin (N+N) → Bool := Fin.addCases
          (fun p => decide (∀ l ∈ S, ¬ I p l)) (fun l => decide (l ∈ S))
        let val (w : ℕ) (z : Fin (N+N) → Bool) := (C.wires (List.ofFn z)).getD w false
        ∃ (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ), C.gates[C.output-(N+N)]? = some g ∧ w ∈ g.inputs ∧
          val w x = false ∧ (∀ i : Fin (N+N), x i = false →
            val w (fun j => x j || decide (i=j)) = true)))
    (gateBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 300 ≤ q → N=q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l} = q+1) → (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) → PEqualNP.MetaComplexity.Monotone2 C → N+N ≤ C.output → C.output < N+N+C.size → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[C.output-(N+N)]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ j (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → ∃ a b : ℕ, g.inputs = [a,b] ∧ a<b ∧ b<N+N+j) → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N+N) C (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) → (∀ (S : Finset (Fin N)), S.card ≤ q →
        let x : Fin (N+N) → Bool := Fin.addCases
          (fun p => decide (∀ l ∈ S, ¬ I p l)) (fun l => decide (l ∈ S))
        let val (w : ℕ) (z : Fin (N+N) → Bool) := (C.wires (List.ofFn z)).getD w false
        ∃ (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ), C.gates[C.output-(N+N)]? = some g ∧ w ∈ g.inputs ∧
          val w x = false ∧ (∀ i : Fin (N+N), x i = false →
            val w (fun j => x j || decide (i=j)) = true)) → N*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq hn degrees lines mono lo hi root order positive sound
  have geo := privatePoint q N I degrees lines
  have certificate := sensitiveInput q N I C geo mono lo hi root order positive sound
  exact gateBound q N I C hq hn degrees lines mono lo hi root order positive certificate
