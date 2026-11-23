import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_624

open PEqualNP.CircuitLowerBounds

-- Vertices 0, 1 and 2 have degree three. Their private leaves are 6, 7 and 8.
private def adjacent (a b : Fin 9) : Bool :=
  (![112,168,280,6,5,3,1,2,4] a : Nat).testBit b.val

private def graph : SimpleGraph (Fin 9) where
  Adj a b := adjacent a b = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel graph.Adj :=
  fun a b => inferInstanceAs (Decidable (adjacent a b = true))

private def circuit : Circuit := ⟨[
  ⟨.or, [0,1]⟩,
  ⟨.or, [2,9]⟩,
  ⟨.and, [10,3]⟩,
  ⟨.or, [7,11]⟩,
  ⟨.and, [1,12]⟩,
  ⟨.and, [10,4]⟩,
  ⟨.or, [6,14]⟩,
  ⟨.and, [0,15]⟩,
  ⟨.or, [5,13]⟩,
  ⟨.and, [9,17]⟩,
  ⟨.or, [2,18]⟩,
  ⟨.or, [8,11]⟩,
  ⟨.or, [20,14]⟩,
  ⟨.or, [21,18]⟩,
  ⟨.and, [19,22]⟩,
  ⟨.or, [16,23]⟩], 24⟩

private def ands : Finset ℕ := {2,4,5,7,9,14}
private def charged : Finset ℕ := {0,1}

private def gateTag (j : ℕ) : ℕ :=
  match circuit.gates[j]? with
  | some ⟨.and, _⟩ => 1
  | some ⟨.or, _⟩ => 2
  | _ => 0

private def goodGate (g : Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  have all : circuit.gates.all goodGate = true := by decide
  intro g hg
  have h := List.all_eq_true.mp all g hg
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [goodGate]

private def bitAt (j : ℕ) (v : Fin 9) : Bool :=
  (circuit.wires (List.ofFn (fun i : Fin 9 => decide (i = v)))).getD (9+j) false

private theorem coverAnd (j : ℕ) (g : Gate)
    (hj : circuit.gates[j]? = some g) (op : g.op = .and) : j ∈ ands := by
  have tag : gateTag j = 1 := by cases g with | mk o ins => cases o <;> simp_all [gateTag]
  have bound : j < 16 := (List.getElem?_eq_some_iff.mp hj).1
  exact (by decide : ∀ i : Fin 16, gateTag i.val = 1 → i.val ∈ ands) ⟨j,bound⟩ tag

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem coverOr (j : ℕ) (g : Gate)
    (hj : circuit.gates[j]? = some g) (op : g.op = .or)
    (two : ∃ u v : Fin 9, u ≠ v ∧ bitAt j u = true ∧ bitAt j v = true) : j ∈ charged := by
  have tag : gateTag j = 2 := by cases g with | mk o ins => cases o <;> simp_all [gateTag]
  have bound : j < 16 := (List.getElem?_eq_some_iff.mp hj).1
  exact (by decide : ∀ i : Fin 16, gateTag i.val = 2 →
    (∃ u v : Fin 9, u ≠ v ∧ bitAt i.val u = true ∧ bitAt i.val v = true) → i.val ∈ charged)
    ⟨j,bound⟩ tag two

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 16000 in
private theorem computes : ∀ x : Fin 9 → Bool,
    circuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 9, graph.Adj u v ∧ x u = true ∧ x v = true := by
  decide

private theorem noFour : ∀ a b c e : Fin 9, graph.Adj a b → graph.Adj b c →
    graph.Adj c e → graph.Adj e a → a = c ∨ b = e := by
  decide

private theorem edgeCount : graph.edgeSet.ncard = 9 := by
  rw [Set.ncard_eq_toFinset_card']
  decide

end PEqualNP.Outside.L_meta_624

open PEqualNP.Outside.L_meta_624

theorem PEqualNP.Outside.L_meta_624 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B : Finset ℕ), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ B) → G.edgeSet.ncard ≤ A.card + B.card) := by
  intro asserted
  have contra := asserted 9 graph circuit ands charged noFour monotone computes coverAnd coverOr
  rw [edgeCount] at contra
  have size : ands.card + charged.card = 8 := by decide
  omega
