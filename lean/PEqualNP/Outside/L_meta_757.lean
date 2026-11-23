import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104

namespace PEqualNP.Outside.L_meta_757_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)

def circuit : Circuit where
  gates := [⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩]
  output := 10

end PEqualNP.Outside.L_meta_757_aux

open PEqualNP.Outside.L_meta_757_aux

theorem PEqualNP.Outside.L_meta_757 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) s ↔
    5 ≤ s := by
  intro s
  change PEqualNP.MetaComplexity.HasCircuitSize 6 edge s ↔ 5 ≤ s
  constructor
  · intro hs
    have essential : ∀ i : Fin 6, ∃ x : Fin 6 → Bool,
        edge (Function.update x i (!x i)) ≠ edge x := by decide
    have h := PEqualNP.MetaComplexity.Helpers.dep_lower 6 edge essential s hs
    omega
  · intro hs
    refine ⟨circuit, ?_, hs, ?_⟩
    · intro g hg
      simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
    · decide
