import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1146_aux
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 3]⟩,
    ⟨.and, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩

lemma mono : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [PEqualNP.MetaComplexity.Monotone2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma correct : ∀ x : Fin 8 → Bool,
    circuit.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) ||
        (x 4 && x 5) || (x 6 && x 7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1146_aux

theorem PEqualNP.Outside.L_meta_1146 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 6 && x 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1146_aux.circuit,
    PEqualNP.Outside.L_meta_1146_aux.mono, by decide,
    PEqualNP.Outside.L_meta_1146_aux.correct⟩
