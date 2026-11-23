import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1198
open PEqualNP.CircuitLowerBounds
def circ : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[8,3]⟩,⟨.and,[0,9]⟩,⟨.and,[2,5]⟩,⟨.or,[1,6]⟩,⟨.or,[12,7]⟩,⟨.and,[4,13]⟩,⟨.or,[10,11]⟩,⟨.or,[15,14]⟩],16⟩
theorem mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  intro g hg
  simp only [circ,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
end PEqualNP.Outside.L_meta_1198
open PEqualNP.Outside.L_meta_1198 in
theorem PEqualNP.Outside.L_meta_1198 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 4 && x 7)) x := by
  exact ⟨circ,mono,by decide,by decide +kernel⟩
