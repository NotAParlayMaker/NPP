import PEqualNP.Defs

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2200000 in
theorem PEqualNP.Outside.R_meta_3420_691
    (andCase :
      let seed : List (BitVec 24) :=
        [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968,5689661]
      ¬∃ ws : List (BitVec 24), ws.length = 24 ∧ ws.take 10 = seed ∧ ws.getD 23 0 = 4095 ∧
        (0 :: ws).Nodup ∧ (BitVec.allOnes 24) ∉ ws ∧
        (∀ j, 10 ≤ j → j < 24 →
          ∃ a ∈ ws.take j, ∃ b ∈ ws.take j,
            (ws.getD j 0 = a &&& b ∨ ws.getD j 0 = a ||| b)) ∧
        ∃ a ∈ ws.take 23, ∃ b ∈ ws.take 23, (4095 : BitVec 24) = a &&& b)
    (orCase :
      let seed : List (BitVec 24) :=
        [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968,5689661]
      ¬∃ ws : List (BitVec 24), ws.length = 24 ∧ ws.take 10 = seed ∧ ws.getD 23 0 = 4095 ∧
        (0 :: ws).Nodup ∧ (BitVec.allOnes 24) ∉ ws ∧
        (∀ j, 10 ≤ j → j < 24 →
          ∃ a ∈ ws.take j, ∃ b ∈ ws.take j,
            (ws.getD j 0 = a &&& b ∨ ws.getD j 0 = a ||| b)) ∧
        ∃ a ∈ ws.take 23, ∃ b ∈ ws.take 23, (4095 : BitVec 24) = a ||| b) :
    ¬∃ (x1 : List (BitVec (24 : ℕ))),     x1.length = (24 : ℕ) ∧       List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧         x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧           ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧             ∀ (x2 : ℕ),               (0 : ℕ) < x2 →                 x2 < (15 : ℕ) →                   have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ));                   x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧ x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7) := by
  rintro ⟨xs, length, initial, target, distinct, gate⟩
  classical
  let seed : List (BitVec 24) :=
    [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968,5689661]
  let full := BitVec.allOnes 24
  have seedEq : xs.take 10 = seed := initial
  have seedClosed (k : ℕ) (hk : 10 ≤ k) : seed ⊆ xs.take k := by
    rw [← seedEq]
    exact List.take_subset_take_left xs hk
  let options := ((seed.product seed).flatMap fun p => [p.1 &&& p.2, p.1 ||| p.2]).filter
    fun v => v != full
  have count : 25 < options.toFinset.card := by decide
  have used : (0 :: xs).toFinset.card ≤ 25 := by
    calc
      _ ≤ (0 :: xs).length := List.toFinset_card_le (0 :: xs)
      _ = 25 := by simp [length]
  obtain ⟨filler, hf, unused⟩ : ∃ filler ∈ options, filler ∉ (0 :: xs) := by
    obtain ⟨z, hz, no⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show (0 :: xs).toFinset.card < options.toFinset.card by omega)
    exact ⟨z, List.mem_toFinset.mp hz, fun h => no (List.mem_toFinset.mpr h)⟩
  have goodFiller : filler ≠ full := by
    have h := (List.mem_filter.mp hf).2
    simpa using h
  obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp (List.mem_filter.mp hf).1
  obtain ⟨inFirst, inSecond⟩ := List.mem_product.mp hp
  have fromSeed : filler = p.1 &&& p.2 ∨ filler = p.1 ||| p.2 := by
    simpa only [List.mem_cons, List.mem_nil_iff, or_false] using ha
  let rename (z : BitVec 24) := if z = full then filler else z
  let ys := xs.map rename
  have zeroKeep : rename (0 : BitVec 24) = 0 :=
    ite_eq_right (show (0 : BitVec 24) ≠ full by decide)
  have keepSeed (z) (hz : z ∈ seed) : rename z = z := by
    have notFull : full ∉ seed := by decide
    have ne : z ≠ full := fun h => notFull (h ▸ hz)
    exact ite_eq_right ne
  have mapped (j : ℕ) : ys.getD j 0 = rename (xs.getD j 0) := by
    calc
      _ = ys.getD j (rename 0) := by rw [zeroKeep]
      _ = _ := List.getD_map _ _ _
  have takeMap (j : ℕ) : ys.take j = (xs.take j).map rename := by
    simp only [ys, List.map_take]
  have initialY : ys.take 10 = seed := by
    rw [takeMap, seedEq]
    exact (List.map_congr_left keepSeed).trans (List.map_id seed)
  have targetY : ys.getD 23 0 = 4095 := by
    rw [mapped, target]
    exact ite_eq_right (show (4095 : BitVec 24) ≠ full by decide)
  have nodupY : (0 :: ys).Nodup := by
    rw [show (0 :: ys) = (0 :: xs).map rename by simp only [List.map_cons, zeroKeep, ys]]
    apply List.Nodup.map_on _ distinct
    intro a hasA b hasB eq
    by_cases aFull : a = full <;> by_cases bFull : b = full
    · exact aFull.trans bFull.symm
    · have hb : b = filler := by simpa only [rename, ite_eq_left aFull, ite_eq_right bFull] using eq.symm
      exact (unused (hb ▸ hasB)).elim
    · have ha' : a = filler := by simpa only [rename, ite_eq_right aFull, ite_eq_left bFull] using eq
      exact (unused (ha' ▸ hasA)).elim
    · simpa only [rename, ite_eq_right aFull, ite_eq_right bFull] using eq
  have noFull : full ∉ ys := by
    intro h
    obtain ⟨z, _, eq⟩ := List.mem_map.mp h
    by_cases hz : z = full
    · exact goodFiller (by simpa only [rename, ite_eq_left hz] using eq)
    · exact hz (by simpa only [rename, ite_eq_right hz] using eq)
  have before (j : ℕ) (hj : j < xs.length) : xs.getD j 0 ∉ xs.take j := by
    intro mem
    obtain ⟨k, hk, eq⟩ := List.mem_take_iff_getElem.mp mem
    rw [List.getD_eq_getElem _ _ hj] at eq
    have eqIdx := (List.nodup_cons.mp distinct).2.eq_of_getElem_eq (by omega) hj eq
    omega
  have normalized (j : ℕ) (hjlo : 10 ≤ j) (hjhi : j < 24) :
      ∃ a ∈ ys.take j, ∃ b ∈ ys.take j,
        (ys.getD j 0 = a &&& b ∨ ys.getD j 0 = a ||| b) := by
    have jform : 9+(j-9) = j := by omega
    have rule := gate (j-9) (by omega) (by omega)
    rw [jform] at rule
    by_cases same : xs.getD j 0 = full
    · have first : p.1 ∈ ys.take j := by
        rw [takeMap]
        exact List.mem_map.mpr ⟨p.1, seedClosed j hjlo inFirst, keepSeed p.1 inFirst⟩
      have second : p.2 ∈ ys.take j := by
        rw [takeMap]
        exact List.mem_map.mpr ⟨p.2, seedClosed j hjlo inSecond, keepSeed p.2 inSecond⟩
      refine ⟨p.1, first, p.2, second, ?_⟩
      rw [mapped, same, show rename full = filler from ite_eq_left rfl]
      exact fromSeed
    · obtain ⟨a, b, ain, bin, operation⟩ :=
        rule.resolve_left (show xs.getD j 0 ≠ (16777215 : BitVec 24) from same)
      have notOlder := before j (by omega)
      have aNo : a ≠ full := by
        intro aFull
        rcases operation with h | h
        · rw [aFull, BitVec.allOnes_and] at h
          exact notOlder (h.symm ▸ bin)
        · rw [aFull, BitVec.allOnes_or] at h
          exact same h
      have bNo : b ≠ full := by
        intro bFull
        rcases operation with h | h
        · rw [bFull, BitVec.and_allOnes] at h
          exact notOlder (h.symm ▸ ain)
        · rw [bFull, BitVec.or_allOnes] at h
          exact same h
      have aY : a ∈ ys.take j := by
        rw [takeMap]
        exact List.mem_map.mpr ⟨a, ain, ite_eq_right aNo⟩
      have bY : b ∈ ys.take j := by
        rw [takeMap]
        exact List.mem_map.mpr ⟨b, bin, ite_eq_right bNo⟩
      exact ⟨a, aY, b, bY, by rwa [mapped, show rename (xs.getD j 0) = _ from ite_eq_right same]⟩
  have lengthY : ys.length = 24 := by simp only [ys, List.length_map, length]
  obtain ⟨a, ha, b, hb, out⟩ := normalized 23 (by decide) (by decide)
  rw [targetY] at out
  rcases out with h | h
  · exact andCase ⟨ys, lengthY, initialY, targetY, nodupY, noFull, normalized, a, ha, b, hb, h⟩
  · exact orCase ⟨ys, lengthY, initialY, targetY, nodupY, noFull, normalized, a, ha, b, hb, h⟩
