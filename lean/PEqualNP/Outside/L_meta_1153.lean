import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside
open CircuitLowerBounds MetaComplexity

theorem L_meta_1153 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 6 && x 7)) x := by
  let C : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[8,3]⟩,⟨.and,[0,9]⟩,⟨.and,[1,4]⟩,
    ⟨.and,[2,5]⟩,⟨.and,[6,7]⟩,⟨.or,[10,11]⟩,⟨.or,[14,12]⟩,⟨.or,[15,13]⟩],16⟩
  refine ⟨C,?_,by decide,?_⟩
  · intro g hg
    simp [C] at hg
    rcases hg with h|h|h|h|h|h|h|h|h <;> subst g <;> simp
  · decide +kernel
end PEqualNP.Outside
