import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10029

def masks : List (ℕ × ℕ) := [(8585472, 178810993), (1649688, 69271716), (169556, 539001928), (9699922, 142778500), (17334276, 222037770), (17664, 848523878), (2097153, 501701468), (4788242, 76812425), (44, 957992050), (5249120, 303565976), (432400, 541197632), (18890944, 318870281), (787072, 721832579), (4587521, 230891730), (18954, 826949669), (8413204, 343976227), (106624, 577026608), (6333450, 83891760), (25463808, 118759492), (8483, 818680084), (17830016, 309379978)]
def data : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]

def columns (i : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: ps => (if p.1.testBit i then p.2 else 0) ||| columns i ps

theorem covered (i j : ℕ) (ps : List (ℕ × ℕ)) :
    (columns i ps).testBit j = true ↔
    ∃ p ∈ ps, p.1.testBit i = true ∧ p.2.testBit j = true := by
  induction ps with
  | nil => simp [columns]
  | cons p ps ih =>
    cases h : p.1.testBit i <;> simp [columns, h, Nat.testBit_or, ih]

def want (i : Fin 25) : ℕ := ((2 ^ 30 - 1) ^^^ (data.getD i.val 0))

theorem rows : ∀ i : Fin 25, columns i.val masks = want i := by decide +kernel

theorem agrees (i : Fin 25) (j : Fin 30) :
    (want i).testBit j.val = true ↔ (data.getD i.val 0).testBit j.val = false := by
  unfold want
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  simp [j.isLt]

def rectangle (p : ℕ × ℕ) : Finset (Fin 25) × Finset (Fin 30) :=
  (Finset.univ.filter (fun i => p.1.testBit i.val),
   Finset.univ.filter (fun j => p.2.testBit j.val))

end PEqualNP.Outside.L_meta_10029

theorem PEqualNP.Outside.L_meta_10029 : ∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 21 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_10029.masks.map PEqualNP.Outside.L_meta_10029.rectangle, by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    simp only [PEqualNP.Outside.L_meta_10029.rectangle, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    apply (PEqualNP.Outside.L_meta_10029.agrees i j).mp
    rw [← PEqualNP.Outside.L_meta_10029.rows]
    exact (PEqualNP.Outside.L_meta_10029.covered _ _ _).mpr ⟨p, hp, hi, hj⟩
  · intro i j h
    have hw := (PEqualNP.Outside.L_meta_10029.agrees i j).mpr h
    rw [← PEqualNP.Outside.L_meta_10029.rows] at hw
    obtain ⟨p, hp, hi, hj⟩ := (PEqualNP.Outside.L_meta_10029.covered _ _ _).mp hw
    exact ⟨PEqualNP.Outside.L_meta_10029.rectangle p, List.mem_map.mpr ⟨p, hp, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
