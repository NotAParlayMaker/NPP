import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1206

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [4, 11]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.and, [5, 13]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [15, 12]⟩,
    ⟨GateOp.or, [16, 14]⟩], 17⟩

set_option maxHeartbeats 1500000 in
lemma evaluates : ∀ a b c d e f g h : Bool,
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (b && d) || (c && e) || (d && e) || (f && g) || (f && h)) := by
  decide

end PEqualNP.Outside.L_meta_1206

theorem PEqualNP.Outside.L_meta_1206 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1206.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1206.circuit]
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [hx]
    exact PEqualNP.Outside.L_meta_1206.evaluates (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
