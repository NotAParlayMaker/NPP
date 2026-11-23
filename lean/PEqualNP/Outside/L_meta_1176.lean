import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1176_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [1, 12]⟩,
    ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.or, [11, 13]⟩,
    ⟨GateOp.or, [15, 14]⟩], 16⟩

end PEqualNP.Outside.L_meta_1176_aux

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_1176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1176_aux.circuit, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [PEqualNP.Outside.L_meta_1176_aux.circuit,
      List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [hx]
    change
      (((x 0 && ((((x 1 || (x 2 || false)) || (x 3 || false)) ||
          (x 4 || false)) && true)) ||
        ((x 1 && ((x 5 || (x 6 || false)) && true)) || false)) ||
          ((x 2 && (x 7 && true)) || false)) = _
    simp only [Bool.and_true, Bool.or_false, Bool.and_or_distrib_left, Bool.or_assoc]
