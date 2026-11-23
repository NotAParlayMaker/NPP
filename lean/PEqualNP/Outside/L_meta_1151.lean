import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1151_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [6, 7]⟩,
    ⟨.or, [10, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩

set_option maxHeartbeats 2000000 in
lemma eval_bits : ∀ a b c d e f g h : Bool,
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && c) || (e && f) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1151_aux

open PEqualNP.Outside.L_meta_1151_aux

theorem PEqualNP.Outside.L_meta_1151 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨circuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, circuit]
  · decide
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact eval_bits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
