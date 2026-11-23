import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1178

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [0, 10]⟩,
    ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩,
    ⟨.or, [11, 12]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem monotone : Monotone2 circuit := by
  simp [Monotone2, circuit, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem computes : ∀ a b c d e f g h : Bool,
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (a && e) ||
       (b && f) || (c && g) || (d && h)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1178

open PEqualNP.Outside.L_meta_1178 in
theorem PEqualNP.Outside.L_meta_1178 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) x := by
  refine ⟨circuit, monotone, by decide, ?_⟩
  intro x
  rw [show List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] from rfl]
  exact computes (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
