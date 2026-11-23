import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1170_aux
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩,
    ⟨.or, [10, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 6]⟩,
    ⟨.and, [2, 7]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩

lemma mono : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [PEqualNP.MetaComplexity.Monotone2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma correct : ∀ x : Fin 8 → Bool,
    circuit.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1170_aux

theorem PEqualNP.Outside.L_meta_1170 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1170_aux.circuit,
    PEqualNP.Outside.L_meta_1170_aux.mono, by decide,
    PEqualNP.Outside.L_meta_1170_aux.correct⟩
