import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1197 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  let gs : List Gate :=
    [⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 4]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [5, 12]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [10, 11]⟩,
      ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩]
  refine ⟨⟨gs, 17⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by rfl
    rw [hx]
    simp [gs, Circuit.eval, Circuit.wires, GateOp.eval, Bool.and_or_distrib_left,
      Bool.and_or_distrib_right, Bool.or_assoc, Bool.and_comm]
