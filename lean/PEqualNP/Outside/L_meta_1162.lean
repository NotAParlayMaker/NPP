import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1162

open PEqualNP.CircuitLowerBounds

def ckt : Circuit :=
  ⟨[⟨GateOp.and, [1, 0]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.and, [7, 6]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem keval :
    ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
      ckt.eval [a0, a1, a2, a3, a4, a5, a6, a7] =
        ((a0 && a1) || (a0 && a2) || (a1 && a2) || (a3 && a4) || (a3 && a5) || (a6 && a7)) := by
  decide

end PEqualNP.Outside.L_meta_1162

theorem PEqualNP.Outside.L_meta_1162 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1162.ckt, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1162.ckt]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1162.keval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
