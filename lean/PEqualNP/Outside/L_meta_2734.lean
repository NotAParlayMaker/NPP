import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2734 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 x6 : Fin (x1 + (1 : ℕ))) (x7 x8 : PEqualNP.CircuitLowerBounds.GateOp),   x7 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7 = PEqualNP.CircuitLowerBounds.GateOp.or →     x8 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8 = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ (x11 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x11 →           x11.size ≤ x2 →             ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit),               PEqualNP.MetaComplexity.Monotone2 x14 ∧                 x14.size ≤ x2 + (2 : ℕ) ∧                   ∀ (x15 : Fin x1 → Bool),                     have x16 : List Bool := List.ofFn x15 ++ [x7.eval [x15 x3, x15 x4]];                     x14.eval (List.ofFn x15) = x11.eval (x16 ++ [x8.eval [x16.getD (↑x5) Bool.false, x16.getD (↑x6) Bool.false]]) := by
  intro n s a b c d o1 o2 h1 h2 D hD hs
  refine ⟨⟨⟨o1, [a, b]⟩ :: ⟨o2, [c, d]⟩ :: D.gates, D.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by rcases h1 with h | h <;> simp [h], by simp⟩
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by rcases h2 with h | h <;> simp [h], by simp⟩
      · exact hD g hg
  · have hs' : D.gates.length ≤ s := hs
    show (_ :: _ :: D.gates).length ≤ s + 2
    simp only [List.length_cons]
    omega
  · intro x
    have hget : ∀ i : Fin n, (List.ofFn x).getD i false = x i := by
      intro i
      simp [List.getD_eq_getElem?_getD]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.map_cons, List.map_nil, hget]
