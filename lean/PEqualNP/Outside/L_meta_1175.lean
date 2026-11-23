import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1175

-- pattern adapted from L_meta_1143
open PEqualNP.CircuitLowerBounds

theorem ofFnN (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [11, 14]⟩], output := 15 }

theorem e1 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, c1.eval [v0, v1, v2, v3, v4, v5, v6, v7] = ((v0 && v1) || (v0 && v2) || (v0 && v3) || (v0 && v4) || (v1 && v5) || (v1 && v6) || (v1 && v7)) := by
  decide

theorem f1 : PEqualNP.MetaComplexity.Monotone2 c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1175

theorem PEqualNP.Outside.L_meta_1175 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1175.c1, PEqualNP.Outside.L_meta_1175.f1, by decide, fun x => by rw [PEqualNP.Outside.L_meta_1175.ofFnN x]; exact PEqualNP.Outside.L_meta_1175.e1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
