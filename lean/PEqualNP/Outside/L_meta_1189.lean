import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1189_aux

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [15, 14]⟩], 16⟩

lemma mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma size_le : circ.size ≤ 9 := by
  decide

lemma evalB : ∀ a b c d e f g h : Bool,
    circ.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && c) || (e && f) || (e && g) || (e && h)) := by
  decide

lemma ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  rfl

end PEqualNP.Outside.L_meta_1189_aux

theorem PEqualNP.Outside.L_meta_1189 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 4 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1189_aux.circ, PEqualNP.Outside.L_meta_1189_aux.mono,
    PEqualNP.Outside.L_meta_1189_aux.size_le, ?_⟩
  intro x
  rw [PEqualNP.Outside.L_meta_1189_aux.ofFn8]
  exact PEqualNP.Outside.L_meta_1189_aux.evalB _ _ _ _ _ _ _ _
