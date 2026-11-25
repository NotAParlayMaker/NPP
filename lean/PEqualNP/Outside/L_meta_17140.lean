import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17140

theorem sing (p l : Fin 13) : (p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9) ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l := by
  revert p l
  decide

end PEqualNP.Outside.L_meta_17140

theorem PEqualNP.Outside.L_meta_17140 :
    ∀ (x1 x2 : Fin (13 : ℕ)), x1 - x2 = (0 : Fin (13 : ℕ)) ∨ x1 - x2 = (1 : Fin (13 : ℕ)) ∨ x1 - x2 = (3 : Fin (13 : ℕ)) ∨ x1 - x2 = (9 : Fin (13 : ℕ)) ↔ x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 := by
  exact PEqualNP.Outside.L_meta_17140.sing
