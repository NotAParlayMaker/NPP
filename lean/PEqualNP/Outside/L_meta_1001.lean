import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1001

private def witness : Circuit :=
  ⟨[
    ⟨.or, [1, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩,
    ⟨.or, [2, 6]⟩, ⟨.and, [1, 12]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [14, 8]⟩, ⟨.and, [3, 15]⟩,
    ⟨.or, [2, 5]⟩, ⟨.and, [7, 17]⟩,
    ⟨.or, [6, 5]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [11, 13]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [23, 20]⟩], 24⟩

end PEqualNP.Outside.L_meta_1001

theorem PEqualNP.Outside.L_meta_1001 :
    PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
      (x 6 && x 8) || (x 8 && x 5)) 16 := by
  refine ⟨PEqualNP.Outside.L_meta_1001.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_1001.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp
  · intro x
    simp only [PEqualNP.Outside.L_meta_1001.witness, Circuit.eval, Circuit.wires,
      List.foldl_cons, List.foldl_nil, List.ofFn_succ, List.ofFn_zero, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
      GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id,
      Bool.and_true, Bool.or_false, Bool.and_or_distrib_left]
    change ((((((x 0 && x 1 || x 0 && x 4) || x 0 && x 5) || (x 1 && x 2 || x 1 && x 6)) ||
      ((x 3 && x 2 || x 3 && x 4) || x 3 && x 8)) || (x 7 && x 2 || x 7 && x 5)) ||
      (x 8 && x 6 || x 8 && x 5)) = _
    ac_rfl
