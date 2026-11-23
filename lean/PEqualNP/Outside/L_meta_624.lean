import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_624

open PEqualNP.CircuitLowerBounds

-- Vertices 0, 1 and 2 alternate around the cycle. Each also has a pendant leaf.
def edges : Finset (Sym2 (Fin 9)) :=
  {s(0, 3), s(1, 3), s(1, 4), s(2, 4), s(0, 5), s(2, 5), s(0, 6), s(1, 7), s(2, 8)}

abbrev graph : SimpleGraph (Fin 9) := SimpleGraph.fromEdgeSet (edges : Set (Sym2 (Fin 9)))

-- Wire 10 is the disjunction of the three alternating vertices. Wires 11 to 13
-- mask the other cycle vertices with wire 10. Each following neighborhood
-- disjunction can therefore be true on only one singleton, its pendant leaf.
def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [9, 2]⟩,
    ⟨.and, [10, 3]⟩, ⟨.and, [10, 4]⟩, ⟨.and, [10, 5]⟩,
    ⟨.or, [6, 11]⟩, ⟨.or, [14, 13]⟩, ⟨.and, [0, 15]⟩,
    ⟨.or, [7, 11]⟩, ⟨.or, [17, 12]⟩, ⟨.and, [1, 18]⟩,
    ⟨.or, [8, 12]⟩, ⟨.or, [20, 13]⟩, ⟨.and, [2, 21]⟩,
    ⟨.or, [16, 19]⟩, ⟨.or, [23, 22]⟩], 24⟩

def andGates : Finset ℕ := {2, 3, 4, 7, 10, 13}
def wideGates : Finset ℕ := {0, 1}

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def isOr : GateOp → Bool
  | .or => true
  | _ => false

lemma edge_count : graph.edgeSet.ncard = 9 := by
  have hdiag : ∀ e ∈ edges, e ∉ Sym2.diagSet := by decide
  have hset : graph.edgeSet = (edges : Set (Sym2 (Fin 9))) := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    exact ⟨And.left, fun he => ⟨he, hdiag e he⟩⟩
  rw [hset, Set.ncard_coe_finset]
  decide

set_option maxRecDepth 10000 in
lemma no_square : ∀ a b c e : Fin 9,
    graph.Adj a b → graph.Adj b c → graph.Adj c e → graph.Adj e a → a = c ∨ b = e := by
  decide

lemma monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  have allGood : circuit.gates.all (fun g =>
      (isAnd g.op || isOr g.op) && decide (g.inputs.length ≤ 2)) = true := by decide
  intro g hg
  have good := List.all_eq_true.mp allGood g hg
  cases h : g.op <;> simp_all [isAnd, isOr]

set_option maxRecDepth 10000 in
lemma computes : ∀ x : Fin 9 → Bool, circuit.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 9, graph.Adj u v ∧ x u = true ∧ x v = true := by
  decide

lemma and_indices : ∀ j : Fin circuit.gates.length,
    isAnd circuit.gates[j.val].op = true → j.val ∈ andGates := by decide

set_option maxRecDepth 10000 in
lemma wide_indices : ∀ j : Fin circuit.gates.length,
    isOr circuit.gates[j.val].op = true →
    (∃ u v : Fin 9, u ≠ v ∧
      (circuit.wires (List.ofFn (fun i : Fin 9 => decide (i = u)))).getD (9 + j.val) false = true ∧
      (circuit.wires (List.ofFn (fun i : Fin 9 => decide (i = v)))).getD (9 + j.val) false = true) →
    j.val ∈ wideGates := by decide

end PEqualNP.Outside.L_meta_624

open PEqualNP.Outside.L_meta_624


theorem PEqualNP.Outside.L_meta_624 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B : Finset ℕ), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ B) → G.edgeSet.ncard ≤ A.card + B.card) := by
  intro claimed
  have bound := claimed 9 graph circuit andGates wideGates no_square monotone computes
    (by
      intro j g hget hop
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hget
      apply and_indices ⟨j, hlt⟩
      rw [hop]
      rfl)
    (by
      intro j g hget hop hs
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hget
      apply wide_indices ⟨j, hlt⟩ _ hs
      rw [hop]
      rfl)
  rw [edge_count] at bound
  have wrong : ¬ 9 ≤ andGates.card + wideGates.card := by decide
  exact wrong bound
