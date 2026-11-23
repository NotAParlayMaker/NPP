import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1163_aux

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[ ⟨GateOp.or, [1, 2]⟩,
     ⟨GateOp.and, [0, 8]⟩,
     ⟨GateOp.and, [2, 4]⟩,
     ⟨GateOp.or, [1, 5]⟩,
     ⟨GateOp.and, [3, 11]⟩,
     ⟨GateOp.and, [6, 7]⟩,
     ⟨GateOp.or, [9, 10]⟩,
     ⟨GateOp.or, [14, 12]⟩,
     ⟨GateOp.or, [15, 13]⟩ ], 16⟩

lemma mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact ⟨by simp, by decide⟩

lemma size_circ : circ.size ≤ 9 := by
  decide

lemma eval_circ (x : Fin 8 → Bool) :
    circ.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 6 && x 7)) := by
  have key : ∀ a b c d e f g h : Bool,
      circ.eval (List.ofFn ![a, b, c, d, e, f, g, h]) =
        ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (g && h)) := by
    decide +kernel
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Outside.L_meta_1163_aux

theorem PEqualNP.Outside.L_meta_1163 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1163_aux.circ,
   PEqualNP.Outside.L_meta_1163_aux.mono,
   PEqualNP.Outside.L_meta_1163_aux.size_circ,
   PEqualNP.Outside.L_meta_1163_aux.eval_circ⟩
