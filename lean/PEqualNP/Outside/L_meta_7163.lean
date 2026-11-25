import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7163
open PEqualNP.CircuitLowerBounds

theorem wl (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

end PEqualNP.Outside.L_meta_7163

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7163 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : Bool) (x5 x6 : ℕ), ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8) = (if x4 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or).eval [(x2.wires (List.ofFn x8)).getD x5 Bool.false, (x2.wires (List.ofFn x8)).getD x6 Bool.false] := by
  intro n C hC b i j
  refine ⟨⟨C.gates ++ [⟨if b = true then GateOp.and else GateOp.or, [i, j]⟩], n + C.size⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC g hg
    · constructor
      · cases b <;> simp
      · simp
  · simp [Circuit.size]
  · intro x
    have h := PEqualNP.Outside.L_meta_7163.wl C.gates (List.ofFn x)
    simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Circuit.size]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h]; simp)]
    rw [h]
    simp
