import PEqualNP.Defs

private def L_meta_237_toBinaryGate (g : PEqualNP.CircuitLowerBounds.Gate) :
    PEqualNP.MetaComplexity.BinaryGate :=
  match g.op, g.inputs with
  | .and, [] => ⟨fun _ _ => true, 0, 0⟩
  | .and, [a] => ⟨fun x _ => x, a, 0⟩
  | .and, [a, b] => ⟨fun x y => x && y, a, b⟩
  | .or, [] => ⟨fun _ _ => false, 0, 0⟩
  | .or, [a] => ⟨fun x _ => x, a, 0⟩
  | .or, [a, b] => ⟨fun x y => x || y, a, b⟩
  | .not, [] => ⟨fun _ _ => true, 0, 0⟩
  | .not, [a] => ⟨fun x _ => !x, a, 0⟩
  | .not, [a, _] => ⟨fun x _ => !x, a, 0⟩
  | _, _ => ⟨fun _ _ => false, 0, 0⟩

private lemma L_meta_237_gate_eq (g : PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    let bg := L_meta_237_toBinaryGate g
    bg.op (w.getD bg.left false) (w.getD bg.right false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, inputs⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl <;>
    match inputs, hlen with
    | [], _ => rfl
    | [a], _ => simp [L_meta_237_toBinaryGate, PEqualNP.CircuitLowerBounds.GateOp.eval]
    | [a, b], _ => simp [L_meta_237_toBinaryGate, PEqualNP.CircuitLowerBounds.GateOp.eval]

private lemma L_meta_237_wires_eq (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (hfan : ∀ g ∈ gs,
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.map L_meta_237_toBinaryGate).foldl
        (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hfan g (by simp)
    rw [L_meta_237_gate_eq g w hg.1 hg.2]
    exact ih _ (fun g' hg' => hfan g' (by simp [hg']))

theorem PEqualNP.Outside.L_meta_237 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasCircuitSize n f s →
      PEqualNP.MetaComplexity.HasBinarySize n f s := by
  rintro n f s ⟨C, hfan, hsize, heval⟩
  refine ⟨⟨C.gates.map L_meta_237_toBinaryGate, C.output⟩, ?_, ?_⟩
  · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size, PEqualNP.CircuitLowerBounds.Circuit.size] using hsize
  · intro x
    have hw : (PEqualNP.MetaComplexity.BinaryCircuit.wires
        ⟨C.gates.map L_meta_237_toBinaryGate, C.output⟩ (List.ofFn x)) =
        C.wires (List.ofFn x) :=
      L_meta_237_wires_eq C.gates (List.ofFn x) hfan
    simp only [PEqualNP.MetaComplexity.BinaryCircuit.eval, hw]
    exact heval x
