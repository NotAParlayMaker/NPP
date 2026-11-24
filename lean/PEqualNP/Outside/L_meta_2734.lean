import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2734 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 x6 : Fin (x1 + (1 : ℕ))) (x7 x8 : PEqualNP.CircuitLowerBounds.GateOp),   x7 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7 = PEqualNP.CircuitLowerBounds.GateOp.or →     x8 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8 = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ (x11 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x11 →           x11.size ≤ x2 →             ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit),               PEqualNP.MetaComplexity.Monotone2 x14 ∧                 x14.size ≤ x2 + (2 : ℕ) ∧                   ∀ (x15 : Fin x1 → Bool),                     have x16 : List Bool := List.ofFn x15 ++ [x7.eval [x15 x3, x15 x4]];                     x14.eval (List.ofFn x15) = x11.eval (x16 ++ [x8.eval [x16.getD (↑x5) Bool.false, x16.getD (↑x6) Bool.false]]) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 h7 h8 x11 hm hs
  refine ⟨⟨⟨x7, [x3.val, x4.val]⟩ :: ⟨x8, [x5.val, x6.val]⟩ :: x11.gates, x11.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · refine ⟨?_, by simp⟩
      rcases h7 with h | h <;> simp [h]
    rcases List.mem_cons.mp hg with rfl | hg
    · refine ⟨?_, by simp⟩
      rcases h8 with h | h <;> simp [h]
    exact hm g hg
  · show x11.gates.length + 2 ≤ x2 + 2
    have : x11.gates.length ≤ x2 := hs
    omega
  · intro x15
    have e3 : (List.ofFn x15).getD x3.val false = x15 x3 := by
      simp [List.getD_eq_getElem?_getD]
    have e4 : (List.ofFn x15).getD x4.val false = x15 x4 := by
      simp [List.getD_eq_getElem?_getD]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.map_cons, List.map_nil, e3, e4]
