import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_662

open PEqualNP.CircuitLowerBounds

abbrev graph : SimpleGraph (Fin 6) := SimpleGraph.fromRel fun a b =>
  (a, b) ∈ ([(0, 1), (1, 3), (1, 4), (2, 3), (3, 4), (4, 5)] : List (Fin 6 × Fin 6))

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [3, 0]⟩, ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.or, [7, 5]⟩,
    ⟨GateOp.and, [8, 7]⟩, ⟨GateOp.and, [6, 10]⟩,
    ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.and, [12, 9]⟩], 13⟩

def andSet : Finset ℕ := {4, 5, 7}

def wideSet : Finset ℕ := {0, 1, 2, 3}

def narrowSet : Finset ℕ := {6}

def Wide (j : ℕ) : Prop := ∃ u v : Fin 6, u ≠ v ∧
  (circuit.wires (List.ofFn (fun i : Fin 6 => decide (i = u)))).getD (6 + j) false = true ∧
  (circuit.wires (List.ofFn (fun i : Fin 6 => decide (i = v)))).getD (6 + j) false = true

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 10000 in
theorem no_four : ∀ a b c e : Fin 6, graph.Adj a b → graph.Adj b c → graph.Adj c e →
    graph.Adj e a → a = c ∨ b = e := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide +kernel

set_option maxRecDepth 100000 in
theorem cover_lower : ∀ T : Finset (Fin 6),
    (∀ i j : Fin 6, graph.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  simp [PEqualNP.MetaComplexity.Monotone2, circuit]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 10000 in
theorem computes : ∀ x : Fin 6 → Bool, circuit.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 6, graph.Adj u v ∧ x u = true ∧ x v = true := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide +kernel

set_option maxRecDepth 100000 in
theorem wide_classification : ∀ j : Fin 8, Wide j.val ↔ j.val ∈ wideSet := by
  unfold Wide wideSet
  decide +kernel

theorem and_coverage : ∀ j g, circuit.gates[j]? = some g → g.op = GateOp.and → j ∈ andSet := by
  intro j g hj hop
  have hjlt : j < 8 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simpa [circuit] using this
  interval_cases j <;> simp [circuit] at hj <;> subst g <;> simp_all [andSet]

theorem wide_coverage : ∀ j g, circuit.gates[j]? = some g → g.op = GateOp.or →
    Wide j → j ∈ wideSet := by
  intro j g hj _ hw
  have hjlt : j < 8 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simpa [circuit] using this
  exact (wide_classification ⟨j, hjlt⟩).mp hw

theorem narrow_coverage : ∀ j g, circuit.gates[j]? = some g → g.op = GateOp.or →
    ¬ Wide j → j ∈ narrowSet := by
  intro j g hj hop hw
  have hjlt : j < 8 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simpa [circuit] using this
  have hn : j ∉ wideSet := fun h => hw ((wide_classification ⟨j, hjlt⟩).mpr h)
  interval_cases j <;> simp [circuit] at hj <;> subst g <;> simp_all [wideSet, narrowSet]

theorem edge_count : graph.edgeSet.ncard = 6 := by
  rw [Set.ncard_eq_toFinset_card']
  decide +kernel

end PEqualNP.Outside.L_meta_662

theorem PEqualNP.Outside.L_meta_662 : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ D) → G.edgeSet.ncard + 2 * k ≤ A.card + B.card + 2 * D.card + 2) := by
  intro h
  have bound := h 6 3 PEqualNP.Outside.L_meta_662.graph PEqualNP.Outside.L_meta_662.circuit PEqualNP.Outside.L_meta_662.andSet PEqualNP.Outside.L_meta_662.wideSet PEqualNP.Outside.L_meta_662.narrowSet
    PEqualNP.Outside.L_meta_662.no_four PEqualNP.Outside.L_meta_662.cover_lower PEqualNP.Outside.L_meta_662.monotone PEqualNP.Outside.L_meta_662.computes PEqualNP.Outside.L_meta_662.and_coverage
    PEqualNP.Outside.L_meta_662.wide_coverage PEqualNP.Outside.L_meta_662.narrow_coverage
  rw [PEqualNP.Outside.L_meta_662.edge_count] at bound
  norm_num [PEqualNP.Outside.L_meta_662.andSet, PEqualNP.Outside.L_meta_662.wideSet, PEqualNP.Outside.L_meta_662.narrowSet] at bound

