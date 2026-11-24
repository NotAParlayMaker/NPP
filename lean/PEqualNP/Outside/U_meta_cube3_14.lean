import Mathlib
import PEqualNP.Defs

-- An explicit circuit of 14 AND and OR gates, each reading two wires, for the edge function
-- of the 3-cube, checked by the kernel on all 256 inputs. Together with L-meta-970 (at least
-- 12 gates) this places the least such circuit at 12, 13 or 14 gates.

namespace PEqualNP.Outside.U_meta_cube3_14

open PEqualNP.CircuitLowerBounds

def g (op : GateOp) (a b : ℕ) : Gate := ⟨op, [a, b]⟩

def cube3 : Circuit :=
  ⟨[g .or 1 2, g .or 0 3, g .or 1 4, g .or 2 4, g .or 3 5, g .or 0 5, g .and 8 9,
    g .and 6 11, g .or 6 12, g .and 10 13, g .or 14 15, g .and 7 16, g .or 17 19,
    g .or 18 20], 21⟩

end PEqualNP.Outside.U_meta_cube3_14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.U_meta_cube3_14 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 14 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨PEqualNP.Outside.U_meta_cube3_14.cube3, ?_, by decide, ?_⟩
  · intro gt hg
    simp only [PEqualNP.Outside.U_meta_cube3_14.cube3, PEqualNP.Outside.U_meta_cube3_14.g,
      List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
