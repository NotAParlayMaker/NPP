import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_1176

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩,
    ⟨.and, [0, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 12]⟩,
    ⟨.and, [2, 7]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩

lemma allowed : Monotone2 circuit := by
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma computes (x : Fin 8 → Bool) :
    circuit.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) := by
  simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, List.getD]
  generalize x 0 = a, x 1 = b, x 2 = c, x 3 = d, x 4 = e, x 5 = f, x 6 = g, x 7 = h
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;> decide

end PEqualNP.Outside.L_meta_1176

open PEqualNP.Outside.L_meta_1176 in
theorem PEqualNP.Outside.L_meta_1176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  exact ⟨circuit, allowed, by decide, computes⟩
