import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9175

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9175

theorem PEqualNP.Outside.L_meta_9175 : ∃ (x1 : SimpleGraph (Fin (6 : ℕ))) (x2 : PEqualNP.AndCount.AndCountCircuit (6 : ℕ)), x2.WellFormed ∧ ∀ (x3 : Finset (Fin (6 : ℕ))), (∀ x4 ∈ x3, ∀ x6 ∈ x3, ¬x1.Adj x4 x6) → (∀ x5 ∉ x3, ∃ x7 ∈ x3, x1.Adj x5 x7) → x2.eval x3 = Bool.false ∧ ∀ x6 ∉ x3, x2.eval (Insert.insert x6 x3) = Bool.true := by
  refine ⟨⊥, ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, ∅⟩, fun i => Fin.elim0 i, fun S _ hm => ⟨?_, fun x hx => ?_⟩⟩
  · simp [PEqualNP.AndCount.AndCountCircuit.eval]
  · obtain ⟨y, _, h⟩ := hm x hx
    exact absurd h (by simp)
