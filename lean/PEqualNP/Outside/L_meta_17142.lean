import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17142_aux

theorem mem_iff : ∀ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ↔ (p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9) := by
  decide

end PEqualNP.Outside.L_meta_17142_aux

theorem PEqualNP.Outside.L_meta_17142 : ∀ (x1 : Finset (Fin (13 : ℕ))) (x2 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1 ↔ ∀ x3 ∈ x1, ¬(x3 - x2 = (0 : Fin (13 : ℕ)) ∨ x3 - x2 = (1 : Fin (13 : ℕ)) ∨ x3 - x2 = (3 : Fin (13 : ℕ)) ∨ x3 - x2 = (9 : Fin (13 : ℕ))) := by
  intro x1 x2
  simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  constructor
  · intro h x3 hx3 hc
    exact h ((PEqualNP.Outside.L_meta_17142_aux.mem_iff x3 x2).2 hc) hx3
  · intro h p hp hpx
    exact h p hpx ((PEqualNP.Outside.L_meta_17142_aux.mem_iff p x2).1 hp)
