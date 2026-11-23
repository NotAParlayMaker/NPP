import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_662

open PEqualNP.CircuitLowerBounds

-- A triangle with pendant edges, two attached at vertex zero and one at each other vertex.
private def pairs : List (Fin 7 × Fin 7) :=
  [(0, 1), (0, 3), (0, 4), (0, 6), (1, 2), (1, 4), (4, 5)]

private abbrev graph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun (u v : Fin 7) => (u, v) ∈ pairs)

private def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [3, 6]⟩,
    ⟨.or, [7, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [4, 13]⟩,
    ⟨.and, [11, 14]⟩], 15⟩

private def ands : Finset ℕ := {2, 6, 8}
private def wides : Finset ℕ := {0, 1, 3, 4, 5}
private def narrows : Finset ℕ := {7}

private abbrev wide (j : ℕ) : Prop :=
  ∃ u v : Fin 7, u ≠ v ∧
    (circuit.wires (List.ofFn (fun i : Fin 7 => decide (i = u)))).getD (7 + j) false = true ∧
    (circuit.wires (List.ofFn (fun i : Fin 7 => decide (i = v)))).getD (7 + j) false = true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 2048 in
private lemma no_four : ∀ a b c e : Fin 7,
    graph.Adj a b → graph.Adj b c → graph.Adj c e → graph.Adj e a → a = c ∨ b = e := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private lemma cover_bound : ∀ T : Finset (Fin 7),
    (∀ i j : Fin 7, graph.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide

private lemma edge_bound : 7 ≤ graph.edgeSet.ncard := by
  let E : Finset (Sym2 (Fin 7)) := {s(0, 1), s(0, 3), s(0, 4), s(0, 6), s(1, 2), s(1, 4), s(4, 5)}
  have hE : E.card = 7 := by decide
  have hs : (E : Set (Sym2 (Fin 7))) ⊆ graph.edgeSet := by
    intro e he
    simp only [E, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [SimpleGraph.mem_edgeSet] <;> decide
  have hn := Set.ncard_le_ncard hs (Set.toFinite _)
  simpa only [Set.ncard_coe_finset, hE] using hn

private lemma monotone_circuit : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
set_option synthInstance.maxSize 2048 in
private lemma computes : ∀ x : Fin 7 → Bool,
    circuit.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, graph.Adj u v ∧ x u = true ∧ x v = true := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide

private lemma gate_index {j : ℕ} {g : Gate} (h : circuit.gates[j]? = some g) : j < 9 := by
  by_contra! hj
  have hn : circuit.gates.length ≤ j := by simpa [circuit] using hj
  simp [List.getElem?_eq_none hn] at h

private lemma narrow_seven : ¬ wide 7 := by decide
private lemma wide_zero : wide 0 := ⟨0, 1, by decide, by decide, by decide⟩
private lemma wide_one : wide 1 := ⟨0, 2, by decide, by decide, by decide⟩
private lemma wide_three : wide 3 := ⟨3, 6, by decide, by decide, by decide⟩
private lemma wide_four : wide 4 := ⟨0, 1, by decide, by decide, by decide⟩
private lemma wide_five : wide 5 := ⟨1, 3, by decide, by decide, by decide⟩

private lemma all_ands (j : ℕ) (g : Gate) (h : circuit.gates[j]? = some g)
    (hop : g.op = .and) : j ∈ ands := by
  have hj := gate_index h
  interval_cases j <;> simp [circuit] at h <;> subst g <;> simp_all [ands]

private lemma all_wides (j : ℕ) (g : Gate) (h : circuit.gates[j]? = some g)
    (hop : g.op = .or) (hw : wide j) : j ∈ wides := by
  have hj := gate_index h
  interval_cases j <;> simp [circuit] at h <;> subst g <;> simp_all [wides, narrow_seven]

private lemma all_narrows (j : ℕ) (g : Gate) (h : circuit.gates[j]? = some g)
    (hop : g.op = .or) (hw : ¬ wide j) : j ∈ narrows := by
  have hj := gate_index h
  interval_cases j <;> simp [circuit] at h <;> subst g <;>
    simp_all [narrows, wide_zero, wide_one, wide_three, wide_four, wide_five]

private lemma weight : ands.card + wides.card + 2 * narrows.card = 10 := by decide

end PEqualNP.Outside.L_meta_662

open PEqualNP.Outside.L_meta_662 in
theorem PEqualNP.Outside.L_meta_662 : ¬ (
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ), (∀ a b c e : Fin n, G.Adj a b →
    G.Adj b c →
    G.Adj c e →
    G.Adj e a →
    a = c ∨ b = e) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j →
    i ∈ T ∨ j ∈ T) →
    k ≤ T.card) →
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n →
    Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
    g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
    j ∈ A) →
    (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
    (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) →
    j ∈ B) →
    (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
    ¬ (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) →
    j ∈ D) →
    G.edgeSet.ncard + 2 * k ≤ A.card + B.card + 2 * D.card + 2) := by
  intro h
  have hbad := h 7 3 graph circuit ands wides narrows no_four cover_bound monotone_circuit
    computes all_ands all_wides all_narrows
  have hedges := edge_bound
  have hweight := weight
  omega
