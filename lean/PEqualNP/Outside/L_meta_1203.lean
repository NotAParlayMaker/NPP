import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1203

open PEqualNP.CircuitLowerBounds

def edgeCircuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [8, 3]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [15, 13]⟩,
    ⟨.or, [16, 14]⟩], 17⟩

lemma edgeCircuit_eval :
    ∀ a b c d e f g h : Bool,
      edgeCircuit.eval [a, b, c, d, e, f, g, h] =
        ((a && b) || (a && c) || (a && d) || (b && e) ||
          (f && g) || (f && h) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1203

theorem PEqualNP.Outside.L_meta_1203 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1203.edgeCircuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1203.edgeCircuit]
  · decide
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [inputs]
    exact PEqualNP.Outside.L_meta_1203.edgeCircuit_eval
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
