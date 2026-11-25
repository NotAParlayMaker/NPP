import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9097 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (18624707 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [12, 10]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [18, 19]⟩, ⟨GateOp.or, [17, 20]⟩], 21⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
