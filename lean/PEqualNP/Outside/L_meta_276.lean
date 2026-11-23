import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_276

open PEqualNP.CircuitLowerBounds

private def appendWire (wires : List Bool) (gate : Gate) : List Bool :=
  wires ++ [gate.op.eval (gate.inputs.map fun wire => wires.getD wire false)]

private theorem read_earlier_wire (gates : List Gate) (wires : List Bool)
    (wire : ℕ) (h : wire < wires.length) :
    (gates.foldl appendWire wires).getD wire false = wires.getD wire false := by
  induction gates generalizing wires with
  | nil => rfl
  | cons gate gates ih =>
    rw [List.foldl_cons, ih (appendWire wires gate)]
    · exact List.getD_append _ _ _ _ h
    · simpa [appendWire] using Nat.lt_succ_of_lt h

private theorem eval_at_gate (gates : List Gate) (wires : List Bool) (j : ℕ) (gate : Gate)
    (hg : gates[j]? = some gate)
    (hEarlier : ∀ wire ∈ gate.inputs, wire < wires.length + j) :
    (gates.foldl appendWire wires).getD (wires.length + j) false =
      gate.op.eval (gate.inputs.map fun wire => (gates.foldl appendWire wires).getD wire false) := by
  induction gates generalizing wires j with
  | nil => simp at hg
  | cons head tail ih =>
    cases j with
    | zero =>
      have heq : head = gate := by simpa using hg
      subst head
      have hNew :
          ((gate :: tail).foldl appendWire wires).getD wires.length false =
            gate.op.eval (gate.inputs.map fun wire => wires.getD wire false) := by
        rw [List.foldl_cons,
          read_earlier_wire tail (appendWire wires gate) wires.length (by simp [appendWire])]
        simp [appendWire]
      rw [Nat.add_zero, hNew]
      congr 1
      apply List.map_congr_left
      intro wire hmem
      exact (read_earlier_wire (gate :: tail) wires wire (by simpa using hEarlier wire hmem)).symm
    | succ j =>
      have hIndex : wires.length + (j + 1) = (appendWire wires head).length + j := by
        simp [appendWire]
        omega
      rw [List.foldl_cons, hIndex]
      exact ih (appendWire wires head) j (by simpa using hg) (by simpa only [← hIndex] using hEarlier)

theorem circuit_eval_at_gate (C : Circuit) (inputs : List Bool) (j : ℕ) (gate : Gate)
    (hg : C.gates[j]? = some gate)
    (hEarlier : ∀ wire ∈ gate.inputs, wire < inputs.length + j) :
    (C.wires inputs).getD (inputs.length + j) false =
      gate.op.eval (gate.inputs.map fun wire => (C.wires inputs).getD wire false) := by
  exact eval_at_gate C.gates inputs j gate hg hEarlier

end PEqualNP.Outside.L_meta_276

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_276

theorem PEqualNP.Outside.L_meta_276 :
    ∀ (n j a b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[j]? = some g → g.inputs = [a, b] → a < n + j → b < n + j →
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) =
        (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∪
        (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) =
        (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∩
        (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) := by
  intro n j a b C g hg hInputs ha hb
  have hEarlier : ∀ wire ∈ g.inputs, wire < n + j := by
    rw [hInputs]
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro wire (rfl | rfl)
    · exact ha
    · exact hb
  have hEval (p : Fin n) :
      (C.wires (List.ofFn fun q : Fin n => decide (q = p))).getD (n + j) false =
        g.op.eval ([a, b].map fun wire =>
          (C.wires (List.ofFn fun q : Fin n => decide (q = p))).getD wire false) := by
    rw [← hInputs]
    let inputs := List.ofFn fun q : Fin n => decide (q = p)
    have hLength : inputs.length = n := List.length_ofFn
    have hRead : ∀ wire ∈ g.inputs, wire < inputs.length + j := by
      simpa only [hLength] using hEarlier
    simpa only [hLength] using circuit_eval_at_gate C inputs j g hg hRead
  constructor
  · intro hop
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [hEval p, hop]
    simp [GateOp.eval]
  · intro hop
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    rw [hEval p, hop]
    simp [GateOp.eval]
