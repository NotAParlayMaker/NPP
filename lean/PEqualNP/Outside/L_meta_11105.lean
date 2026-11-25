import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11105

/-- Entry `(i, j)` of the matrix. -/
def M (i : Fin 20) (j : Fin 20) : Bool := (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val

/-- The rectangles, rows and columns as lists. -/
def cover : List (List (Fin 20) × List (Fin 20)) :=
  [([1, 4, 13, 16, 18, 19], [1, 4, 6, 7, 10, 11, 13, 16]),
   ([3, 6, 8, 9, 11, 14], [0, 1, 3, 6, 11, 14, 16, 17]),
   ([0, 3, 12, 15, 17, 18], [0, 3, 5, 6, 9, 10, 12, 15]),
   ([4, 7, 9, 10, 12, 15], [1, 2, 4, 7, 12, 15, 17, 18]),
   ([2, 5, 7, 8, 10, 13], [0, 2, 5, 10, 13, 15, 16, 19]),
   ([0, 1, 3, 5, 6, 8, 10, 13, 15, 18], [3, 8, 13, 15, 18]),
   ([11, 16], [2, 3, 4, 5, 8, 9, 13, 14, 18, 19]),
   ([1, 2, 4, 6, 7, 9, 12, 14, 17, 19], [4, 9, 12, 14, 19]),
   ([0, 2, 5, 14, 17, 19], [2, 5, 7, 8, 11, 12, 14, 17])]

theorem zero_ok : cover.all (fun p => p.1.all (fun i => p.2.all (fun j => !(M i j)))) = true := by
  decide +kernel

theorem cover_ok : (List.finRange 20).all (fun i => (List.finRange 20).all (fun j =>
    M i j || cover.any (fun p => p.1.contains i && p.2.contains j))) = true := by
  decide +kernel

theorem of_not_true {b : Bool} (h : (!b) = true) : b = false := by
  revert h
  cases b <;> decide

end PEqualNP.Outside.L_meta_11105

theorem PEqualNP.Outside.L_meta_11105 : ∃ L : List (Finset (Fin 20) × Finset (Fin 20)), L.length ≤ 9 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 20) (j : Fin 20), (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨PEqualNP.Outside.L_meta_11105.cover.map (fun p => (p.1.toFinset, p.2.toFinset)), ?_, ?_, ?_⟩
  · rw [List.length_map]
    decide
  · intro r hr i hi j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have hi' : i ∈ p.1 := by simpa using hi
    have hj' : j ∈ p.2 := by simpa using hj
    have h1 := List.all_eq_true.mp PEqualNP.Outside.L_meta_11105.zero_ok p hp
    have h2 := List.all_eq_true.mp h1 i hi'
    have h3 := List.all_eq_true.mp h2 j hj'
    exact PEqualNP.Outside.L_meta_11105.of_not_true h3
  · intro i j hij
    have h1 := List.all_eq_true.mp PEqualNP.Outside.L_meta_11105.cover_ok i (List.mem_finRange i)
    have h2 : (PEqualNP.Outside.L_meta_11105.M i j || PEqualNP.Outside.L_meta_11105.cover.any (fun p => p.1.contains i && p.2.contains j)) = true :=
      List.all_eq_true.mp h1 j (List.mem_finRange j)
    have h0 : PEqualNP.Outside.L_meta_11105.M i j = false := hij
    rw [h0, Bool.false_or] at h2
    obtain ⟨p, hp, hpq⟩ := List.any_eq_true.mp h2
    simp only [Bool.and_eq_true] at hpq
    refine ⟨(p.1.toFinset, p.2.toFinset), List.mem_map.mpr ⟨p, hp, rfl⟩, ?_, ?_⟩
    · simpa using hpq.1
    · simpa using hpq.2
