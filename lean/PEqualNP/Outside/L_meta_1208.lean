import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1208

def C : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩],
    output := 17 }

theorem tab : ∀ a b c d e f g h : Bool,
    C.eval (List.ofFn ![a, b, c, d, e, f, g, h]) =
      ((a && b) || (a && c) || (b && d) || (c && e) || (d && f) || (e && g) || (f && h)) := by
  decide

theorem fn (x : Fin 8 → Bool) :
    C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) := by
  have h := tab (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
  have hx : ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] = x := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at h
  exact h

end PEqualNP.Outside.L_meta_1208

theorem PEqualNP.Outside.L_meta_1208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1208.C, ?_, by decide, PEqualNP.Outside.L_meta_1208.fn⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_1208.C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
