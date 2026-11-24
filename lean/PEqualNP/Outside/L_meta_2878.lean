import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2878

open PEqualNP.CircuitLowerBounds

theorem foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

end PEqualNP.Outside.L_meta_2878

theorem PEqualNP.Outside.L_meta_2878 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : PEqualNP.CircuitLowerBounds.GateOp), x4 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ (x6 x7 : ℕ), ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval [(x2.wires (List.ofFn x9)).getD x6 Bool.false, (x2.wires (List.ofFn x9)).getD x7 Bool.false] := by
  intro n C hC op hop a b
  refine ⟨⟨C.gates ++ [⟨op, [a, b]⟩], n + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hC g h
    · rw [List.mem_singleton] at h
      subst h
      refine ⟨?_, by simp⟩
      rcases hop with h | h <;> simp [h]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [PEqualNP.Outside.L_meta_2878.foldl_length]
      simp
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
    change ((C.wires (List.ofFn x)) ++ [_]).getD (n + C.gates.length) false = _
    rw [← hlen]
    simp
