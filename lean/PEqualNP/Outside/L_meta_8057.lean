import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8057

def tab : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {0, 1, 2, 5}, {0, 1, 2, 5}, {0, 2, 3, 4}, {0, 1, 4, 6}, {0, 1, 2, 5}, {0, 1, 2, 6}, {0, 1, 2, 7}, {0, 1, 4, 8}, {0, 2, 4, 9}, {0, 1, 5, 10}, {0, 1, 2, 11}, {0, 1, 4, 12}, {2, 4, 5, 6}, {0, 3, 5, 6}, {0, 1, 4, 6}, {0, 1, 2, 5}, {1, 2, 3, 6}, {0, 2, 3, 4}, {0, 1, 4, 8}, {0, 1, 2, 5}, {0, 1, 2, 5}, {0, 1, 2, 6}, {1, 2, 3, 7}, {0, 2, 3, 4}, {1, 3, 4, 5}]

def w (i : Fin 26) : Finset (Fin 13) := tab.getD i.val ∅

set_option maxRecDepth 100000 in
theorem key : ∀ (x1 : Fin (26 : ℕ)), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 (w x1) ∧ ((List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ (w x1))) ++ List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 (w x1))).getD (↑x1) Bool.false = Bool.true := by
  decide +kernel

end PEqualNP.Outside.L_meta_8057

theorem PEqualNP.Outside.L_meta_8057 : ∀ (x1 : Fin (26 : ℕ)), ∃ (x2 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x2 ∧ ((List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2)) ++ List.ofFn fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x2)).getD (↑x1) Bool.false = Bool.true := fun x1 => ⟨PEqualNP.Outside.L_meta_8057.w x1, PEqualNP.Outside.L_meta_8057.key x1⟩
