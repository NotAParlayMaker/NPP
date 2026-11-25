import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17142
open PEqualNP.CircuitLowerBounds



theorem key : ∀ (x1 x2 : Fin 13), x1 - x2 = 0 ∨ x1 - x2 = 1 ∨ x1 - x2 = 3 ∨ x1 - x2 = 9 ↔ x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 := by
  decide

end PEqualNP.Outside.L_meta_17142

open PEqualNP.Outside.L_meta_17142 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_17142 : ∀ (x1 : Finset (Fin (13 : ℕ))) (x2 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1 ↔ ∀ x3 ∈ x1, ¬(x3 - x2 = (0 : Fin (13 : ℕ)) ∨ x3 - x2 = (1 : Fin (13 : ℕ)) ∨ x3 - x2 = (3 : Fin (13 : ℕ)) ∨ x3 - x2 = (9 : Fin (13 : ℕ))) := by
  intro Q l
  unfold PEqualNP.HeptadCover.missLines
  rw [Finset.mem_filter, Finset.disjoint_left]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro h x hx hk
    exact h ((key x l).1 hk) hx
  · intro h x hx hq
    exact h x hq ((key x l).2 hx)
