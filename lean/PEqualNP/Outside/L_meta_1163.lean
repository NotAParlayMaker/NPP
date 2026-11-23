import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1163
open PEqualNP.CircuitLowerBounds

private def witness : Circuit := ⟨[
  ⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 4]⟩,
  ⟨.or, [1, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [6, 7]⟩,
  ⟨.or, [9, 10]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩

end PEqualNP.Outside.L_meta_1163
open PEqualNP.Outside.L_meta_1163 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1163 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    simp [witness, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ,
      List.getD_eq_getElem?_getD] <;>
      (apply Bool.eq_iff_iff.mpr; simp only [Bool.and_eq_true, Bool.or_eq_true]; tauto)
