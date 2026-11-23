import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1169

def C : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩],
    output := 15 }

theorem tab : ∀ a b c d e f g h : Bool,
    C.eval (List.ofFn ![a, b, c, d, e, f, g, h]) =
      ((a && b) || (a && c) || (a && d) || (a && e) || (a && f) || (b && g) || (b && h)) := by
  decide

theorem fn (x : Fin 8 → Bool) :
    C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 1 && x 7)) := by
  have h := tab (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  have hx : ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] = x := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at h
  exact h

end PEqualNP.Outside.L_meta_1169

theorem PEqualNP.Outside.L_meta_1169 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 1 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1169.C, ?_, by decide, PEqualNP.Outside.L_meta_1169.fn⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_1169.C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
