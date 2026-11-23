import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1195

open PEqualNP.CircuitLowerBounds

def ckt : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.and, [7, 4]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem keval :
    ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
      ckt.eval [a0, a1, a2, a3, a4, a5, a6, a7] =
        ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a2 && a5) || (a3 && a6) || (a4 && a7)) := by
  decide

end PEqualNP.Outside.L_meta_1195

theorem PEqualNP.Outside.L_meta_1195 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1195.ckt, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1195.ckt]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1195.keval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
