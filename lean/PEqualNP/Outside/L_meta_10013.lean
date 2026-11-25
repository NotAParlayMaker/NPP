import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10013

def masks : List (ℕ × ℕ) := [(268567744, 844923265), (1347820134, 1074806788), (19546160, 541229222), (1678010116, 209718273), (172181832, 1242038544), (596994, 822095900), (16779032, 242483266), (170951300, 1082527904), (51384834, 37885004), (1055498256, 8896), (621805664, 542327240), (1375731713, 275103492), (1084039320, 270598163), (1503668800, 18893440), (67141925, 696721440), (54665346, 38045208), (671887396, 1746961408), (69533710, 67915800), (377944760, 335544352), (12624013, 50429993), (14979392, 8389445), (143213088, 285869250), (1218084874, 269625346), (541083667, 46747650)]
def data : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]

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

def want (i : Fin 31) : ℕ := ((2 ^ 31 - 1) ^^^ (data.getD i.val 0))

theorem rows : ∀ i : Fin 31, columns i.val masks = want i := by decide +kernel

theorem agrees (i : Fin 31) (j : Fin 31) :
    (want i).testBit j.val = true ↔ (data.getD i.val 0).testBit j.val = false := by
  unfold want
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  simp [j.isLt]

def rectangle (p : ℕ × ℕ) : Finset (Fin 31) × Finset (Fin 31) :=
  (Finset.univ.filter (fun i => p.1.testBit i.val),
   Finset.univ.filter (fun j => p.2.testBit j.val))

end PEqualNP.Outside.L_meta_10013

theorem PEqualNP.Outside.L_meta_10013 : ∃ L : List (Finset (Fin 31) × Finset (Fin 31)), L.length ≤ 24 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 31) (j : Fin 31), (([1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_10013.masks.map PEqualNP.Outside.L_meta_10013.rectangle, by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    simp only [PEqualNP.Outside.L_meta_10013.rectangle, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    apply (PEqualNP.Outside.L_meta_10013.agrees i j).mp
    rw [← PEqualNP.Outside.L_meta_10013.rows]
    exact (PEqualNP.Outside.L_meta_10013.covered _ _ _).mpr ⟨p, hp, hi, hj⟩
  · intro i j h
    have hw := (PEqualNP.Outside.L_meta_10013.agrees i j).mpr h
    rw [← PEqualNP.Outside.L_meta_10013.rows] at hw
    obtain ⟨p, hp, hi, hj⟩ := (PEqualNP.Outside.L_meta_10013.covered _ _ _).mp hw
    exact ⟨PEqualNP.Outside.L_meta_10013.rectangle p, List.mem_map.mpr ⟨p, hp, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
