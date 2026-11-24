import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2878

lemma foldl_wires_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
    w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

end PEqualNP.Outside.L_meta_2878

theorem PEqualNP.Outside.L_meta_2878 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : PEqualNP.CircuitLowerBounds.GateOp), x4 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ (x6 x7 : ℕ), ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval [(x2.wires (List.ofFn x9)).getD x6 Bool.false, (x2.wires (List.ofFn x9)).getD x7 Bool.false] := by
  intro x1 x2 hmon x4 hop x6 x7
  refine ⟨⟨x2.gates ++ [⟨x4, [x6, x7]⟩], x1 + x2.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hmon g hg
    · exact ⟨hop, by simp⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x9
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.map]
    have hlen : (x2.wires (List.ofFn x9)).length = x1 + x2.gates.length := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires]
      rw [PEqualNP.Outside.L_meta_2878.foldl_wires_length, List.length_ofFn]
    change ((x2.wires (List.ofFn x9)) ++ [x4.eval [(x2.wires (List.ofFn x9)).getD x6 false, (x2.wires (List.ofFn x9)).getD x7 false]]).getD (x1 + x2.gates.length) false = _
    rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _)]
    simp [PEqualNP.CircuitLowerBounds.Circuit.wires]
