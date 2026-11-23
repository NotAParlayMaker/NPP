import Mathlib
import PEqualNP.Defs

-- The 8-gate circuit for graph n8-032 (inputs are wires 0 to 7, output is wire 15).
def PEqualNP.Outside.L_meta_1180_aux.ckt : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩], 15⟩

-- Evaluation on all 256 inputs, checked by the kernel.
theorem PEqualNP.Outside.L_meta_1180_aux.ckt_eval : ∀ a b c d e f g h : Bool,
    PEqualNP.Outside.L_meta_1180_aux.ckt.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (f && g) || (f && h)) := by
  decide

theorem PEqualNP.Outside.L_meta_1180 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1180_aux.ckt, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_1180_aux.ckt, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [hx, PEqualNP.Outside.L_meta_1180_aux.ckt_eval]
