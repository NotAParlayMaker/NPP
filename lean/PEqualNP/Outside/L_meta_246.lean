import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open CircuitLowerBounds

theorem L_meta_246 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩], 12⟩ → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 7 ∧ PEqualNP.MetaComplexity.circuitFun 6 C = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 4 && x 5)) ∧ C.gates.zipIdx.countP (fun p => decide (7 < 6 + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains 7) = 2 := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_, by decide⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · funext x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp [List.ofFn_succ]
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, hx]
    generalize x 0 = a, x 1 = b, x 2 = c, x 3 = d, x 4 = e, x 5 = f
    revert a b c d e f
    decide

end PEqualNP.Outside
