import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1207

def C : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩],
    output := 17 }

theorem tab : ∀ a b c d e f g h : Bool,
    C.eval (List.ofFn ![a, b, c, d, e, f, g, h]) =
      ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && f) || (g && h)) := by
  decide

theorem fn (x : Fin 8 → Bool) :
    C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) := by
  have h := tab (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  have hx : ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] = x := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at h
  exact h

end PEqualNP.Outside.L_meta_1207

theorem PEqualNP.Outside.L_meta_1207 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1207.C, ?_, by decide, PEqualNP.Outside.L_meta_1207.fn⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_1207.C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
