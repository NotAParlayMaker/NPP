import PEqualNP.Defs

-- The first 21 bits are the edge rows in statement order. The remaining 37
-- bits are maximal independent sets, sorted by their 14-bit vertex masks.
-- Each list starts with the 14 vertex columns and the value of the first gate.
-- The three possible first ORs represent a same-side pair, a flag, and an antiflag.
-- Replacing a first nonedge AND by false preserves all edge rows and can only
-- decrease the output on independent sets. Constants and copies can then be removed.
-- The Fano plane's collineations and point-line duality give the three pair orbits.
-- Each subsequent instruction appends the union or intersection of two columns.
-- A forward read gives zero. A short program can be padded with repeated operands.
-- The target is true on the 21 edges and false on the 37 maximal independent sets.
theorem PEqualNP.Outside.R_meta_971_58
    (normalize : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C → ∀ s : Nat, C.size ≤ s →
      (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (54476011632248939714359330176 : Nat).testBit (14 * u.val + v.val) = true ∧ x u = true ∧ x v = true)) →
      ∃ z ∈ ([1, 95274182876594239, 284526031944024591, 241600541374316567] : List Nat),
        ∃ p : Fin (s - 1) → Bool × Fin (13 + s) × Fin (13 + s),
        2097151 ∈ (List.ofFn p).foldl (fun (w : List Nat) g =>
          let a := w.getD g.2.1.val 0
          let b := w.getD g.2.2.val 0
          w ++ [cond g.1 (a ||| b) (a &&& b)])
          [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
           8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
           155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
           270286071508633728, 288160007407550752, z])
    (edgeAnd : ∀ p : Fin 25 → Bool × Fin 39 × Fin 39,
      ¬ (2097151 ∈ (List.ofFn p).foldl (fun (w : List Nat) g =>
          let a := w.getD g.2.1.val 0
          let b := w.getD g.2.2.val 0
          w ++ [cond g.1 (a ||| b) (a &&& b)])
          [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
           8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
           155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
           270286071508633728, 288160007407550752, 1]))
    (firstOr : ∀ z ∈ ([95274182876594239, 284526031944024591, 241600541374316567] : List Nat),
      ∀ p : Fin 25 → Bool × Fin 39 × Fin 39,
      ¬ (2097151 ∈ (List.ofFn p).foldl (fun (w : List Nat) g =>
          let a := w.getD g.2.1.val 0
          let b := w.getD g.2.2.val 0
          w ++ [cond g.1 (a ||| b) (a &&& b)])
          [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
           8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
           155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
           270286071508633728, 288160007407550752, z])) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  intro C hm hf
  apply Nat.le_of_not_lt
  intro hs
  have table : ∀ u v : Fin 14,
      ((54476011632248939714359330176 : Nat).testBit (14 * u.val + v.val) = true ↔
       (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))) := by decide
  have rows := hf
  simp only [← table] at rows
  obtain ⟨z, hz, p, hp⟩ := normalize C hm 26 (by omega) rows
  rcases List.mem_cons.mp hz with he | ho
  · subst z
    exact edgeAnd p hp
  · exact firstOr z ho p hp
