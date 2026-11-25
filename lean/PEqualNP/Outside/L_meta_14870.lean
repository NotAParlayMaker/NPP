import PEqualNP.Outside.L_meta_11639
import PEqualNP.Outside.L_meta_8646

namespace PEqualNP.Outside.L_meta_14870
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_8646_aux

private def edgeFn (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 5) || (x 2 && x 6) || (x 2 && x 7) || (x 3 && x 6) || (x 5 && x 7)

private def circuit : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩

private theorem basis : ∀ g ∈ circuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [circuit]

set_option maxRecDepth 12000 in
private theorem circuit_eval : ∀ x : Fin 8 → Bool,
    circuit.eval (List.ofFn x) = edgeFn x := by decide +kernel

set_option maxRecDepth 12000 in
private theorem table_eval : ∀ x : Fin 8 → Bool, edgeFn x = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

private def relabelInput : Fin 8 → Fin 8 := ![6, 5, 7, 4, 2, 0, 1, 3]

private theorem lower (s : ℕ) (h : HasCircuitSize 8 edgeFn s) : 11 ≤ s := by
  let F : (Fin 8 → Bool) → Bool := fun x => edgeFn (x ∘ relabelInput)
  have hr : HasCircuitSize 8 F s := relabel_size relabelInput edgeFn s h
  have hd : ∃ x : Fin 8 → Bool, F (Function.update x (Fin.last 7) (!x (Fin.last 7))) ≠ F x :=
    ⟨fun j => decide (j.val = 0), by decide +kernel⟩
  have hn : ∃ y z : Fin 7 → Bool, F (Fin.snoc y false) ≠ F (Fin.snoc z false) :=
    ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨k, hk, hh⟩ := gate_elim_one 7 F false s hd hn hr
  have eqn : (fun y : Fin 7 → Bool => F (Fin.snoc y false)) = PEqualNP.Outside.L_meta_11639.graph := by
    funext y
    exact (by decide +kernel : ∀ z : Fin 7 → Bool, F (Fin.snoc z false) = PEqualNP.Outside.L_meta_11639.graph z) y
  rw [eqn] at hh
  have := PEqualNP.Outside.L_meta_11639.lower k hh
  omega

end PEqualNP.Outside.L_meta_14870

open PEqualNP.Outside.L_meta_14870 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_14870 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legalG _ computes
  have h := lower gates.length ⟨⟨gates, o⟩, legalG, le_rfl, fun x => (computes x).trans (table_eval x).symm⟩
  exact ⟨circuit.gates, circuit.output, basis, (show circuit.gates.length = 11 from rfl).le.trans h,
    fun x => (circuit_eval x).trans (table_eval x)⟩
