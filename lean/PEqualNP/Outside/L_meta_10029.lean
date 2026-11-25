import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10029

-- 21 all-0 rectangles (rows, columns), found by a SAT search for covers invariant under an
-- automorphism of order 3 of the affine plane of order 5 (the matrix is its point-line incidence).
def cover : List (Finset (Fin 25) × Finset (Fin 30)) :=
  [(({4, 6, 14, 16, 18, 23} : Finset (Fin 25)), ({0, 2, 6, 11, 13, 20, 23} : Finset (Fin 30))),
    (({2, 4, 13, 17, 20, 21} : Finset (Fin 25)), ({5, 8, 15, 16, 21, 23, 26} : Finset (Fin 30))),
    (({6, 8, 10, 11, 20, 22} : Finset (Fin 25)), ({4, 10, 13, 16, 17, 25, 28} : Finset (Fin 30))),
    (({1, 4, 8, 9, 21, 22, 23} : Finset (Fin 25)), ({0, 5, 17, 18, 23, 27, 28} : Finset (Fin 30))),
    (({5, 11, 14, 16, 19, 20, 21} : Finset (Fin 25)), ({2, 3, 5, 11, 14, 16, 25} : Finset (Fin 30))),
    (({6, 7, 11, 13, 17, 23, 24} : Finset (Fin 25)), ({0, 7, 8, 13, 21, 24, 25} : Finset (Fin 30))),
    (({0, 17, 19, 23} : Finset (Fin 25)), ({1, 7, 8, 12, 14, 17, 19, 21, 23, 24, 26, 27} : Finset (Fin 30))),
    (({0, 7, 21, 22} : Finset (Fin 25)), ({3, 4, 9, 11, 12, 16, 17, 18, 22, 24, 27, 28} : Finset (Fin 30))),
    (({0, 9, 11, 16} : Finset (Fin 25)), ({2, 3, 6, 7, 11, 13, 14, 18, 19, 21, 22, 29} : Finset (Fin 30))),
    (({9, 10, 13} : Finset (Fin 25)), ({1, 2, 5, 9, 10, 15, 18, 21, 23, 24, 25, 28, 29} : Finset (Fin 30))),
    (({8, 18, 19} : Finset (Fin 25)), ({0, 1, 2, 8, 9, 10, 14, 16, 17, 18, 20, 25, 29} : Finset (Fin 30))),
    (({2, 7, 14} : Finset (Fin 25)), ({0, 1, 5, 8, 9, 11, 13, 14, 15, 20, 24, 28, 29} : Finset (Fin 30))),
    (({1, 4, 5, 6, 12, 14, 17} : Finset (Fin 25)), ({3, 8, 12, 15, 23, 29} : Finset (Fin 30))),
    (({3, 4, 5, 13, 20, 22, 24} : Finset (Fin 25)), ({1, 7, 10, 16, 22, 28} : Finset (Fin 30))),
    (({1, 6, 8, 15, 16, 20, 24} : Finset (Fin 25)), ({2, 9, 13, 19, 20, 27} : Finset (Fin 30))),
    (({10, 12, 24} : Finset (Fin 25)), ({1, 3, 6, 7, 9, 10, 12, 14, 15, 18, 20, 25, 26, 28} : Finset (Fin 30))),
    (({1, 3, 18} : Finset (Fin 25)), ({0, 2, 4, 7, 9, 10, 14, 15, 20, 22, 24, 26, 27, 29} : Finset (Fin 30))),
    (({2, 5, 15} : Finset (Fin 25)), ({1, 3, 4, 5, 6, 8, 10, 15, 18, 19, 20, 24, 27, 29} : Finset (Fin 30))),
    (({3, 12, 13, 16, 23} : Finset (Fin 25)), ({0, 4, 7, 11, 12, 15, 19, 21, 26} : Finset (Fin 30))),
    (({3, 8, 15, 17, 21} : Finset (Fin 25)), ({4, 5, 6, 10, 12, 17, 21, 22, 27} : Finset (Fin 30))),
    (({11, 12, 14, 15, 22} : Finset (Fin 25)), ({3, 6, 11, 17, 19, 20, 22, 25, 26} : Finset (Fin 30)))]

end PEqualNP.Outside.L_meta_10029

theorem PEqualNP.Outside.L_meta_10029 : ∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 21 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_10029.cover, by decide, ?_, ?_⟩
  · intro r hr
    simp only [PEqualNP.Outside.L_meta_10029.cover, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro i
    unfold PEqualNP.Outside.L_meta_10029.cover
    fin_cases i <;> decide +kernel
