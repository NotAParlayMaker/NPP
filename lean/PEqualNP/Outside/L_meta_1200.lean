import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1200

open PEqualNP.CircuitLowerBounds

def circ : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

lemma ofFnN (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  rfl

lemma wf : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma key : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
    circ.eval [a0, a1, a2, a3, a4, a5, a6, a7] =
      ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a2 && a5) || (a4 && a6) || (a6 && a7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1200

theorem PEqualNP.Outside.L_meta_1200 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1200.circ, PEqualNP.Outside.L_meta_1200.wf, by decide, fun x => ?_⟩
  rw [PEqualNP.Outside.L_meta_1200.ofFnN x]
  exact PEqualNP.Outside.L_meta_1200.key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
