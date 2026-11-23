import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_624

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first three vertices alternate with 3, 4, 5 around the cycle.
-- Vertices 6, 7, 8 are their respective leaves.
private def edges : List (Fin 9 × Fin 9) :=
  [(0,3),(0,5),(0,6),(1,3),(1,4),(1,7),(2,4),(2,5),(2,8)]

private def adjacent (a b : Fin 9) := (a,b) ∈ edges ∨ (b,a) ∈ edges

private def graph : SimpleGraph (Fin 9) where
  Adj := adjacent
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by unfold adjacent; decide⟩

private def adjDec (i j : Fin 9) : Decidable (graph.Adj i j) :=
  inferInstanceAs (Decidable ((i,j) ∈ edges ∨ (j,i) ∈ edges))

set_option maxHeartbeats 0 in
private lemma no_square : ∀ a b c d : Fin 9, graph.Adj a b → graph.Adj b c →
    graph.Adj c d → graph.Adj d a → a = c ∨ b = d := by
  let : DecidableRel graph.Adj := adjDec
  decide

private lemma edge_count : graph.edgeSet.ncard = 9 := by
  let : DecidableRel graph.Adj := adjDec
  rw [Set.ncard_eq_toFinset_card']
  decide

-- Wires 11, 12 and 13 mask the three shared cycle neighbours.
-- The unmasked leaf in each branch is its only possible singleton.
private def circ : Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.or,[9,2]⟩,
    ⟨.and,[3,10]⟩,⟨.and,[4,10]⟩,⟨.and,[5,10]⟩,
    ⟨.or,[11,13]⟩,⟨.or,[14,6]⟩,⟨.and,[0,15]⟩,
    ⟨.or,[11,12]⟩,⟨.or,[17,7]⟩,⟨.and,[1,18]⟩,
    ⟨.or,[12,13]⟩,⟨.or,[20,8]⟩,⟨.and,[2,21]⟩,
    ⟨.or,[16,19]⟩,⟨.or,[23,22]⟩],24⟩

private def ands : Finset ℕ := {2,3,4,7,10,13}
private def wides : Finset ℕ := {0,1}

private def bin (g : Gate) : Bool := match g.op with
  | .and | .or => decide (g.inputs.length ≤ 2)
  | _ => false

private lemma monotone : Monotone2 circ := by
  have hall : circ.gates.all bin = true := by decide
  intro g hg
  have hb := List.all_eq_true.mp hall g hg
  cases he : g.op <;> simp_all [bin]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma correct : ∀ x : Fin 9 → Bool, circ.eval (List.ofFn x) = true ↔
    ∃ a b : Fin 9, graph.Adj a b ∧ x a = true ∧ x b = true := by
  let : DecidableRel graph.Adj := adjDec
  decide

private def isAnd (g : Gate) : Bool := match g.op with | .and => true | _ => false

private lemma covers_and (j : ℕ) (g : Gate) (hg : circ.gates[j]? = some g)
    (hop : g.op = .and) : j ∈ ands := by
  have hj : j < circ.gates.length := List.getElem?_eq_some_iff.mp hg |>.1
  have all : ∀ i : Fin circ.gates.length,
      (circ.gates[i.val]?.map isAnd).getD false = true → i.val ∈ ands := by decide
  apply all ⟨j,hj⟩
  simp [hg, isAnd, hop]

private lemma covers_wide (j : ℕ) (g : Gate) (hg : circ.gates[j]? = some g)
    (_hop : g.op = .or) (hw : ∃ a b : Fin 9, a ≠ b ∧
      (circ.wires (List.ofFn (fun i : Fin 9 => decide (i = a)))).getD (9+j) false = true ∧
      (circ.wires (List.ofFn (fun i : Fin 9 => decide (i = b)))).getD (9+j) false = true) : j ∈ wides := by
  have hj : j < circ.gates.length := List.getElem?_eq_some_iff.mp hg |>.1
  have all : ∀ i : Fin circ.gates.length, (∃ a b : Fin 9, a ≠ b ∧
      (circ.wires (List.ofFn (fun k : Fin 9 => decide (k = a)))).getD (9+i.val) false = true ∧
      (circ.wires (List.ofFn (fun k : Fin 9 => decide (k = b)))).getD (9+i.val) false = true) →
      i.val ∈ wides := by decide +kernel
  exact all ⟨j,hj⟩ hw

end PEqualNP.Outside.L_meta_624

open PEqualNP.Outside.L_meta_624
theorem PEqualNP.Outside.L_meta_624 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B : Finset ℕ), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ B) → G.edgeSet.ncard ≤ A.card + B.card) := by
  intro h
  have bad := h 9 graph circ ands wides no_square monotone correct covers_and covers_wide
  rw [edge_count] at bad
  exact (by decide : ¬ (9 ≤ ands.card + wides.card)) bad
