import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10037

def masks : List (ℕ × ℕ) := [(17412, 139659), (51808, 98881), (1712, 598272), (24778, 279569), (37061, 296994), (1619, 542792), (2396, 528914), (179, 786564), (13664, 70696), (4616, 139636), (10241, 142980), (33026, 184708)]
def data : List ℕ := [69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528]

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

def want (i : Fin 16) : ℕ := ((2 ^ 20 - 1) ^^^ (data.getD i.val 0))

theorem rows : ∀ i : Fin 16, columns i.val masks = want i := by decide +kernel

theorem agrees (i : Fin 16) (j : Fin 20) :
    (want i).testBit j.val = true ↔ (data.getD i.val 0).testBit j.val = false := by
  unfold want
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  simp [j.isLt]

def rectangle (p : ℕ × ℕ) : Finset (Fin 16) × Finset (Fin 20) :=
  (Finset.univ.filter (fun i => p.1.testBit i.val),
   Finset.univ.filter (fun j => p.2.testBit j.val))

end PEqualNP.Outside.L_meta_10037

theorem PEqualNP.Outside.L_meta_10037 : ∃ L : List (Finset (Fin 16) × Finset (Fin 20)), L.length ≤ 12 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 16) (j : Fin 20), (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_10037.masks.map PEqualNP.Outside.L_meta_10037.rectangle, by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    simp only [PEqualNP.Outside.L_meta_10037.rectangle, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    apply (PEqualNP.Outside.L_meta_10037.agrees i j).mp
    rw [← PEqualNP.Outside.L_meta_10037.rows]
    exact (PEqualNP.Outside.L_meta_10037.covered _ _ _).mpr ⟨p, hp, hi, hj⟩
  · intro i j h
    have hw := (PEqualNP.Outside.L_meta_10037.agrees i j).mpr h
    rw [← PEqualNP.Outside.L_meta_10037.rows] at hw
    obtain ⟨p, hp, hi, hj⟩ := (PEqualNP.Outside.L_meta_10037.covered _ _ _).mp hw
    exact ⟨PEqualNP.Outside.L_meta_10037.rectangle p, List.mem_map.mpr ⟨p, hp, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
