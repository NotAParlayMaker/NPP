import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1194

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩,
    ⟨.or, [4, 5]⟩, ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 7]⟩, ⟨.and, [6, 13]⟩,
    ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩

lemma evaluates (a b c d e f g h : Bool) :
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && e) ||
       (b && f) || (c && g) || (g && h)) := by
  revert a b c d e f g h
  decide +kernel

end PEqualNP.Outside.L_meta_1194

open PEqualNP.Outside.L_meta_1194

theorem PEqualNP.Outside.L_meta_1194 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) x := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h <;> subst gate <;>
      constructor <;> first | exact Or.inl rfl | exact Or.inr rfl | decide
  · intro x
    exact evaluates (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
