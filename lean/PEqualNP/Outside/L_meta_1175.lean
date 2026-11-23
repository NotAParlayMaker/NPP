import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1175

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [1, 2] },
        { op := GateOp.or, inputs := [8, 3] },
        { op := GateOp.or, inputs := [9, 4] },
        { op := GateOp.and, inputs := [0, 10] },
        { op := GateOp.or, inputs := [5, 6] },
        { op := GateOp.or, inputs := [12, 7] },
        { op := GateOp.and, inputs := [1, 13] },
        { op := GateOp.or, inputs := [11, 14] } ],
    output := 15 }

theorem table : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
    circ.eval [a0, a1, a2, a3, a4, a5, a6, a7] =
      ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a0 && a4) || (a1 && a5) || (a1 && a6) ||
        (a1 && a7)) := by
  decide

theorem ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1175

theorem PEqualNP.Outside.L_meta_1175 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1175.circ, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_1175.circ, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide
  · intro x
    rw [PEqualNP.Outside.L_meta_1175.ofFn8, PEqualNP.Outside.L_meta_1175.table]
