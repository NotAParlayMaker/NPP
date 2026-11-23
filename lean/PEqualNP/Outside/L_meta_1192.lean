import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1192

def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], output := 16 }

lemma key : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool, circ.eval [a0, a1, a2, a3, a4, a5, a6, a7] = ((a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a1 && a5) || (a2 && a6) || (a3 && a7)) := by
  decide

end PEqualNP.Outside.L_meta_1192

theorem PEqualNP.Outside.L_meta_1192 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1192.circ, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_1192.circ, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : x = (![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] : Fin 8 → Bool) := by
      funext i; fin_cases i <;> rfl
    have h := PEqualNP.Outside.L_meta_1192.key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    rw [hx]
    simpa [List.ofFn_succ] using h
