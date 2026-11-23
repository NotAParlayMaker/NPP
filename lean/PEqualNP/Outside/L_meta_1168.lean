import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1168_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.or, [10, 5]⟩,
    ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k : ∀ a b c d e f g h : Bool,
    circ.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && c) || (g && h)) := by
  decide

theorem t : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 9 ∧
    ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool =>
          (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) ||
            (x 1 && x 2) || (x 6 && x 7)) x := by
  refine ⟨circ, ?_, by decide, ?_⟩
  · simp [Monotone2, circ]
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Outside.L_meta_1168_aux

theorem PEqualNP.Outside.L_meta_1168 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool =>
              (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) ||
                (x 1 && x 2) || (x 6 && x 7)) x :=
  PEqualNP.Outside.L_meta_1168_aux.t
