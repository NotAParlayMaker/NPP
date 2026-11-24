import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2878

open PEqualNP.CircuitLowerBounds

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
      List.length_nil]; omega

end PEqualNP.Outside.L_meta_2878

theorem PEqualNP.Outside.L_meta_2878 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : PEqualNP.CircuitLowerBounds.GateOp), x4 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ (x6 x7 : ℕ), ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval [(x2.wires (List.ofFn x9)).getD x6 Bool.false, (x2.wires (List.ofFn x9)).getD x7 Bool.false] := by
  intro x1 x2 hm x4 hx4 x6 x7
  refine ⟨⟨x2.gates ++ [⟨x4, [x6, x7]⟩], x1 + x2.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hm g h
    · simp only [List.mem_singleton] at h
      subst h
      refine ⟨?_, by simp⟩
      rcases hx4 with rfl | rfl <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x9
    have hlen := PEqualNP.Outside.L_meta_2878.foldl_len x2.gates (List.ofFn x9)
    simp only [List.getD_eq_getElem?_getD, List.length_ofFn] at hlen
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
