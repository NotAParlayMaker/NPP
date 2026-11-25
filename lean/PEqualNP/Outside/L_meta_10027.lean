import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10027

-- Eighteen all-zero rectangles covering every zero of the matrix, each given by a mask of rows
-- and a mask of columns (found by a search over sets of rows, each taken with all columns that
-- are zero on the whole set).
def masks : List (ℕ × ℕ) :=
  [(16990784, 34119753), (545090, 546968321), (3276838, 142656824), (5366282, 4719136), (20971832, 407966786), (163969, 694300954), (25176067, 353116548), (13566546, 142606465), (592020, 540346409), (9748496, 68331782), (17831552, 304136842), (787978, 553797252), (6592512, 105253968), (20925449, 67190784), (4210693, 361310794), (533024, 596380838), (2105416, 287415829), (8455424, 45379700)]

def rect (s q : ℕ) : Finset (Fin 25) × Finset (Fin 30) :=
  (Finset.univ.filter (fun i : Fin 25 => s.testBit i.val = true),
   Finset.univ.filter (fun j : Fin 30 => q.testBit j.val = true))

def cover : List (Finset (Fin 25) × Finset (Fin 30)) := masks.map (fun m => rect m.1 m.2)

theorem zero_inside : ∀ m ∈ masks, ∀ (i : Fin 25) (j : Fin 30),
    m.1.testBit i.val = true → m.2.testBit j.val = true →
    (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false := by
  decide +kernel

theorem zero_covered : ∀ (i : Fin 25) (j : Fin 30),
    (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false →
    ∃ m ∈ masks, m.1.testBit i.val = true ∧ m.2.testBit j.val = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_10027

theorem PEqualNP.Outside.L_meta_10027 : ∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 18 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_10027.cover, ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_10027.cover, PEqualNP.Outside.L_meta_10027.masks]
  · intro r hr i hi j hj
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hr
    simp only [PEqualNP.Outside.L_meta_10027.rect, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact PEqualNP.Outside.L_meta_10027.zero_inside m hm i j hi hj
  · intro i j h
    obtain ⟨m, hm, h1, h2⟩ := PEqualNP.Outside.L_meta_10027.zero_covered i j h
    refine ⟨PEqualNP.Outside.L_meta_10027.rect m.1 m.2, List.mem_map.mpr ⟨m, hm, rfl⟩, ?_, ?_⟩
    · simp [PEqualNP.Outside.L_meta_10027.rect, h1]
    · simp [PEqualNP.Outside.L_meta_10027.rect, h2]
