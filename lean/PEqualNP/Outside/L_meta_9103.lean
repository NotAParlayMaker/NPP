import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9103 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (51811205313 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [4, 15]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.and, [7, 1]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.and, [14, 19]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [20, 21]⟩, ⟨GateOp.or, [22, 23]⟩], 24⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
