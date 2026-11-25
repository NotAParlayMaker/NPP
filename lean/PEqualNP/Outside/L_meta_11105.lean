import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_11105 :
    ∃ L : List (Finset (Fin 20) × Finset (Fin 20)), L.length ≤ 9 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 20) (j : Fin 20), (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  let L : List (Finset (Fin 20) × Finset (Fin 20)) := [
    ({2, 4, 5, 7, 10, 19}, {2, 7, 10, 12, 13, 16, 17, 19}),
    ({0, 2, 3, 5, 7, 8, 10, 12, 13, 15, 17, 18}, {0, 5, 10, 15}),
    ({8, 11, 13, 14, 16, 19}, {1, 2, 5, 6, 8, 11, 16, 19}),
    ({0, 9, 12, 14, 15, 17}, {0, 2, 3, 6, 7, 9, 12, 17}),
    ({1, 3, 4, 6, 9, 18}, {1, 6, 9, 11, 12, 15, 16, 18}),
    ({1, 10, 13, 15, 16, 18}, {1, 3, 4, 7, 8, 10, 13, 18}),
    ({0, 3, 5, 6, 8, 11}, {0, 3, 8, 11, 13, 14, 17, 18}),
    ({1, 4, 6, 7, 9, 11, 12, 16}, {1, 4, 9, 14, 18, 19}),
    ({2, 14, 17, 19}, {4, 8, 9, 11, 14, 19})]
  let M : List ℕ := [589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921]
  have allZero : ∀ k : Fin L.length, ∀ i j : Fin 20,
      i ∈ (L.get k).1 → j ∈ (L.get k).2 →
      (M.getD i.val 0).testBit j.val = false := by decide +kernel
  have hits : ∀ i j : Fin 20, (M.getD i.val 0).testBit j.val = false →
      ∃ k : Fin L.length, i ∈ (L.get k).1 ∧ j ∈ (L.get k).2 := by decide +kernel
  refine ⟨L, by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hr
    exact allZero k i j hi hj
  · intro i j h
    obtain ⟨k, hi, hj⟩ := hits i j h
    exact ⟨L.get k, List.get_mem L k, hi, hj⟩
