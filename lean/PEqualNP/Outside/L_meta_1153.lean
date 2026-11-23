import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1153_aux

open PEqualNP.CircuitLowerBounds

def C0 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 12]⟩,
    ⟨GateOp.or, [15, 13]⟩], 16⟩

theorem keval :
    ∀ a b c d e f g h : Bool,
      C0.eval [a, b, c, d, e, f, g, h] =
        ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (g && h)) := by
  decide

theorem tex :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool =>
              (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) ||
                (x 6 && x 7))
              x := by
  refine ⟨C0, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C0]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact keval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Outside.L_meta_1153_aux

theorem PEqualNP.Outside.L_meta_1153 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 6 && x 7)) x := by
  exact PEqualNP.Outside.L_meta_1153_aux.tex
