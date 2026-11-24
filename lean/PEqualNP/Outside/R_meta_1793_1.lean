import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Eliminate the arbitrary fan-in-at-most-two OR input list x1 into three canonical
-- second-gate cases over the 10-wire base (x0..x8, x0 && x1):
-- (1) degenerate/redundant wire (false, x k, or x0 && x1),
-- (2) OR of two distinct input variables x i || x j with i < j,
-- (3) OR of wire 9 with an input outside {0, 1}: (x0 && x1) || x k.
theorem PEqualNP.Outside.R_meta_1793_1 :
    (∀ (b : (Fin 9 → Bool) → Bool),
      (b = fun _ => false) ∨ (∃ k : Fin 9, b = fun x => x k) ∨ (b = fun x => x 0 && x 1) →
      ∀ (x3 : Circuit), FanInTwo x3 → x3.size ≤ 13 →
        ∃ (x6 : Fin 9 → Bool),
          x3.eval (List.ofFn x6 ++ [x6 0 && x6 1, b x6]) ≠
            (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 ||
             x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 ||
             x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) →
    (∀ (i j : Fin 9), i < j →
      ∀ (x3 : Circuit), FanInTwo x3 → x3.size ≤ 13 →
        ∃ (x6 : Fin 9 → Bool),
          x3.eval (List.ofFn x6 ++ [x6 0 && x6 1, x6 i || x6 j]) ≠
            (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 ||
             x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 ||
             x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) →
    (∀ (k : Fin 9), k ≠ 0 → k ≠ 1 →
      ∀ (x3 : Circuit), FanInTwo x3 → x3.size ≤ 13 →
        ∃ (x6 : Fin 9 → Bool),
          x3.eval (List.ofFn x6 ++ [x6 0 && x6 1, (x6 0 && x6 1) || x6 k]) ≠
            (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 ||
             x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 ||
             x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) →
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro hDeg hPair hWire9 x1 hlen x3 hFan hSize
  have hor0 : GateOp.or.eval [] = false := rfl
  have hor1 : ∀ b : Bool, GateOp.or.eval [b] = b := Bool.or_false
  have hor2 : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have hlt9 : ∀ (x6 : Fin 9 → Bool) (a : ℕ) (ha : a < 9),
      (List.ofFn x6 ++ [x6 0 && x6 1]).getD a false = x6 ⟨a, ha⟩ := by
    intro x6 a ha
    have h1 : a < (List.ofFn x6).length := by rw [List.length_ofFn]; exact ha
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, List.getElem?_ofFn]
    simp [ha]
  have heq9 : ∀ (x6 : Fin 9 → Bool),
      (List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 false = (x6 0 && x6 1) := by
    intro x6
    have h1 : (List.ofFn x6).length ≤ 9 := by rw [List.length_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h1, List.length_ofFn, Nat.sub_self]
    rfl
  have hgt9 : ∀ (x6 : Fin 9 → Bool) (a : ℕ), 10 ≤ a →
      (List.ofFn x6 ++ [x6 0 && x6 1]).getD a false = false := by
    intro x6 a ha
    have hlen10 : (List.ofFn x6 ++ [x6 0 && x6 1]).length ≤ a := by
      rw [List.length_append, List.length_ofFn]; exact ha
    exact List.getD_eq_default _ _ hlen10
  have hSingle : ∀ (a : ℕ),
      ∃ b : (Fin 9 → Bool) → Bool,
        ((b = fun _ => false) ∨ (∃ k : Fin 9, b = fun x => x k) ∨ (b = fun x => x 0 && x 1)) ∧
        ∀ x6 : Fin 9 → Bool, (List.ofFn x6 ++ [x6 0 && x6 1]).getD a false = b x6 := by
    intro a
    by_cases ha : a < 9
    · exact ⟨fun x => x ⟨a, ha⟩, Or.inr (Or.inl ⟨⟨a, ha⟩, rfl⟩), fun x6 => hlt9 x6 a ha⟩
    · by_cases ha9 : a = 9
      · subst ha9
        exact ⟨fun x => x 0 && x 1, Or.inr (Or.inr rfl), fun x6 => heq9 x6⟩
      · exact ⟨fun _ => false, Or.inl rfl, fun x6 => hgt9 x6 a (by omega)⟩
  have hFinish : ∀ (b : (Fin 9 → Bool) → Bool),
      (∀ x6 : Fin 9 → Bool,
        GateOp.or.eval (List.map (fun x8 => (List.ofFn x6 ++ [x6 0 && x6 1]).getD x8 false) x1) = b x6) →
      (∃ x6 : Fin 9 → Bool,
        x3.eval (List.ofFn x6 ++ [x6 0 && x6 1, b x6]) ≠
          (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 ||
           x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 ||
           x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) →
      ∃ x6 : Fin 9 → Bool,
        have x7 : List Bool := List.ofFn x6 ++ [x6 0 && x6 1]
        x3.eval (x7 ++ [GateOp.or.eval (List.map (fun x8 => x7.getD x8 false) x1)]) ≠
          (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 ||
           x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 ||
           x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5) := by
    intro b hbeq hex
    obtain ⟨x6, hx6⟩ := hex
    refine ⟨x6, ?_⟩
    have happ : (List.ofFn x6 ++ [x6 0 && x6 1]) ++ [b x6] = List.ofFn x6 ++ [x6 0 && x6 1, b x6] :=
      List.append_assoc ..
    change x3.eval ((List.ofFn x6 ++ [x6 0 && x6 1]) ++
      [GateOp.or.eval (List.map (fun x8 => (List.ofFn x6 ++ [x6 0 && x6 1]).getD x8 false) x1)]) ≠ _
    rw [hbeq x6, happ]
    exact hx6
  have habsorb0 : ∀ b0 b1 : Bool, ((b0 && b1) || b0) = b0 := by decide
  have habsorb1 : ∀ b0 b1 : Bool, ((b0 && b1) || b1) = b1 := by decide
  cases x1 with
  | nil =>
    exact hFinish (fun _ => false) (fun _ => hor0) (hDeg _ (Or.inl rfl) x3 hFan hSize)
  | cons a tail =>
    cases tail with
    | nil =>
      obtain ⟨bf, hbf, hbeq⟩ := hSingle a
      refine hFinish bf (fun x6 => ?_) (hDeg bf hbf x3 hFan hSize)
      rw [List.map_cons, List.map_nil, hor1, hbeq x6]
    | cons b r =>
      have hr : r = [] := by
        simp only [List.length_cons] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hr
      by_cases ha10 : 10 ≤ a
      · obtain ⟨bf, hbf, hbeq⟩ := hSingle b
        refine hFinish bf (fun x6 => ?_) (hDeg bf hbf x3 hFan hSize)
        rw [List.map_cons, List.map_cons, List.map_nil, hor2, hgt9 x6 a ha10, Bool.false_or, hbeq x6]
      · by_cases hb10 : 10 ≤ b
        · obtain ⟨bf, hbf, hbeq⟩ := hSingle a
          refine hFinish bf (fun x6 => ?_) (hDeg bf hbf x3 hFan hSize)
          rw [List.map_cons, List.map_cons, List.map_nil, hor2, hgt9 x6 b hb10, Bool.or_false, hbeq x6]
        · by_cases ha9 : a = 9
          · subst ha9
            by_cases hb9 : b = 9
            · subst hb9
              refine hFinish (fun x => x 0 && x 1) (fun x6 => ?_) (hDeg _ (Or.inr (Or.inr rfl)) x3 hFan hSize)
              rw [List.map_cons, List.map_cons, List.map_nil, hor2, heq9 x6, Bool.or_self]
            · have hb : b < 9 := by omega
              let k : Fin 9 := ⟨b, hb⟩
              by_cases hk0 : k = 0
              · refine hFinish (fun x => x 0) (fun x6 => ?_) (hDeg _ (Or.inr (Or.inl ⟨0, rfl⟩)) x3 hFan hSize)
                rw [List.map_cons, List.map_cons, List.map_nil, hor2, heq9 x6, hlt9 x6 b hb]
                change ((x6 0 && x6 1) || x6 k) = x6 0
                rw [hk0]; exact habsorb0 (x6 0) (x6 1)
              · by_cases hk1 : k = 1
                · refine hFinish (fun x => x 1) (fun x6 => ?_) (hDeg _ (Or.inr (Or.inl ⟨1, rfl⟩)) x3 hFan hSize)
                  rw [List.map_cons, List.map_cons, List.map_nil, hor2, heq9 x6, hlt9 x6 b hb]
                  change ((x6 0 && x6 1) || x6 k) = x6 1
                  rw [hk1]; exact habsorb1 (x6 0) (x6 1)
                · refine hFinish (fun x => (x 0 && x 1) || x k) (fun x6 => ?_) (hWire9 k hk0 hk1 x3 hFan hSize)
                  rw [List.map_cons, List.map_cons, List.map_nil, hor2, heq9 x6, hlt9 x6 b hb]
          · have ha : a < 9 := by omega
            by_cases hb9 : b = 9
            · subst hb9
              let k : Fin 9 := ⟨a, ha⟩
              by_cases hk0 : k = 0
              · refine hFinish (fun x => x 0) (fun x6 => ?_) (hDeg _ (Or.inr (Or.inl ⟨0, rfl⟩)) x3 hFan hSize)
                rw [List.map_cons, List.map_cons, List.map_nil, hor2, hlt9 x6 a ha, heq9 x6, Bool.or_comm]
                change ((x6 0 && x6 1) || x6 k) = x6 0
                rw [hk0]; exact habsorb0 (x6 0) (x6 1)
              · by_cases hk1 : k = 1
                · refine hFinish (fun x => x 1) (fun x6 => ?_) (hDeg _ (Or.inr (Or.inl ⟨1, rfl⟩)) x3 hFan hSize)
                  rw [List.map_cons, List.map_cons, List.map_nil, hor2, hlt9 x6 a ha, heq9 x6, Bool.or_comm]
                  change ((x6 0 && x6 1) || x6 k) = x6 1
                  rw [hk1]; exact habsorb1 (x6 0) (x6 1)
                · refine hFinish (fun x => (x 0 && x 1) || x k) (fun x6 => ?_) (hWire9 k hk0 hk1 x3 hFan hSize)
                  rw [List.map_cons, List.map_cons, List.map_nil, hor2, hlt9 x6 a ha, heq9 x6, Bool.or_comm]
            · have hb : b < 9 := by omega
              by_cases hab : a = b
              · subst hab
                refine hFinish (fun x => x ⟨a, ha⟩) (fun x6 => ?_) (hDeg _ (Or.inr (Or.inl ⟨⟨a, ha⟩, rfl⟩)) x3 hFan hSize)
                rw [List.map_cons, List.map_cons, List.map_nil, hor2, hlt9 x6 a ha, Bool.or_self]
              · by_cases hlt : a < b
                · refine hFinish (fun x => x ⟨a, ha⟩ || x ⟨b, hb⟩) (fun x6 => ?_)
                    (hPair ⟨a, ha⟩ ⟨b, hb⟩ hlt x3 hFan hSize)
                  rw [List.map_cons, List.map_cons, List.map_nil, hor2, hlt9 x6 a ha, hlt9 x6 b hb]
                · have hgt : b < a := by omega
                  refine hFinish (fun x => x ⟨b, hb⟩ || x ⟨a, ha⟩) (fun x6 => ?_)
                    (hPair ⟨b, hb⟩ ⟨a, ha⟩ hgt x3 hFan hSize)
                  rw [List.map_cons, List.map_cons, List.map_nil, hor2, hlt9 x6 a ha, hlt9 x6 b hb, Bool.or_comm]
