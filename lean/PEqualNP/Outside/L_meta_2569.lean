import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2569
open PEqualNP.CircuitLowerBounds

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem step (gs : List Gate) (op : GateOp) (o a b : ℕ) (x : List Bool) :
    Circuit.eval ⟨⟨op, [a, b]⟩ :: gs, o⟩ x
      = Circuit.eval ⟨gs, o⟩ (x ++ [op.eval [x.getD a false, x.getD b false]]) := by
  simp [Circuit.eval, Circuit.wires]

end PEqualNP.Outside.L_meta_2569

theorem PEqualNP.Outside.L_meta_2569 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : PEqualNP.CircuitLowerBounds.GateOp) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x5 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5 = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ x2 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x2 + (1 : ℕ) ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = x6.eval (List.ofFn x11 ++ [x5.eval [x11 x3, x11 x4]]) := by
  intro x1 x2 x3 x4 x5 x6 hop hm hs
  refine ⟨⟨⟨x5, [(x3 : ℕ), (x4 : ℕ)]⟩ :: x6.gates, x6.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · refine ⟨?_, by simp⟩
      rcases hop with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact hm g hg
  · have : x6.gates.length ≤ x2 := hs
    simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
  · intro x11
    rw [PEqualNP.Outside.L_meta_2569.step, PEqualNP.Outside.L_meta_2569.getD_ofFn,
      PEqualNP.Outside.L_meta_2569.getD_ofFn]
