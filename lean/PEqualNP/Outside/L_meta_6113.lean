import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepReads

namespace PEqualNP.Outside.L_meta_6113_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (5887 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 11]⟩], 13⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (5887 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  intro h
  have hr := PEqualNP.MetaComplexity.RepReads.reads_le _ h
  revert hr
  decide

end PEqualNP.Outside.L_meta_6113_aux

theorem PEqualNP.Outside.L_meta_6113 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5887 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5887 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_6113_aux.upper, PEqualNP.Outside.L_meta_6113_aux.lower⟩
