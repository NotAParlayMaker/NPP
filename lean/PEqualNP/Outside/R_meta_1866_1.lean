import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1866_1
    (h1 : ∀ (b : (Fin 9 → Bool) → Bool),
      (b = fun _ => false) ∨ (b = fun _ => true) ∨ (∃ k : Fin 9, b = fun x => x k) ∨
        (b = fun x => x 0 && x 3) →
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x5 : Fin 9 → Bool),
          x1.eval (List.ofFn x5 ++ [x5 0 && x5 3, b x5]) =
            (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5)) →
        14 ≤ x1.size)
    (h2 : ∀ (i j : Fin 9), i < j →
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x5 : Fin 9 → Bool),
          x1.eval (List.ofFn x5 ++ [x5 0 && x5 3, x5 i && x5 j]) =
            (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5)) →
        14 ≤ x1.size)
    (h3 : ∀ (k : Fin 9), k ≠ 0 → k ≠ 3 →
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x5 : Fin 9 → Bool),
          x1.eval (List.ofFn x5 ++ [x5 0 && x5 3, x5 0 && x5 3 && x5 k]) =
            (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5)) →
        14 ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  have wire_lt : ∀ (x : Fin 9 → Bool) (w : Fin 11) (hw : w.val < 9),
      (List.ofFn x ++ [x 0 && x 3]).getD w.val false = x ⟨w.val, hw⟩ := by
    intro x w hw
    have hl : w.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl,
      List.getElem?_eq_getElem hl, Option.getD_some, List.getElem_ofFn]
  have wire_9 : ∀ (x : Fin 9 → Bool) (w : Fin 11), w.val = 9 →
      (List.ofFn x ++ [x 0 && x 3]).getD w.val false = (x 0 && x 3) := by
    intro x w hw
    have hl : (List.ofFn x).length = 9 := List.length_ofFn
    rw [hw, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_eq hl),
      hl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have wire_10 : ∀ (x : Fin 9 → Bool) (w : Fin 11), w.val = 10 →
      (List.ofFn x ++ [x 0 && x 3]).getD w.val false = false := by
    intro x w hw
    have hl : (List.ofFn x ++ [x 0 && x 3]).length = 10 := by
      rw [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    rw [hw, List.getD_eq_getElem?_getD, List.getElem?_eq_none (le_of_eq hl), Option.getD_none]
  have split11 : ∀ w : Fin 11, w.val < 9 ∨ w.val = 9 ∨ w.val = 10 := by
    intro w
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ w.isLt) with h10 | h10
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h10) with h9 | h9
      · exact Or.inl h9
      · exact Or.inr (Or.inl h9)
    · exact Or.inr (Or.inr h10)
  have and_0_3_0 : ∀ p q : Bool, ((p && q) && p) = (p && q) := by
    intro p q; cases p <;> cases q <;> rfl
  have and_0_3_3 : ∀ p q : Bool, ((p && q) && q) = (p && q) := by
    intro p q; cases p <;> cases q <;> rfl
  have reduce_b : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin 11))
      (b : (Fin 9 → Bool) → Bool),
      (∀ x5 : Fin 9 → Bool,
        have x6 : List Bool := List.ofFn x5 ++ [x5 0 && x5 3]
        x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (List.map (fun x7 : Fin 11 => x6.getD x7.val false) x2)]) =
          (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5)) →
      (∀ x5 : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (List.map (fun x7 : Fin 11 => (List.ofFn x5 ++ [x5 0 && x5 3]).getD x7.val false) x2) = b x5) →
      ∀ x5 : Fin 9 → Bool,
        x1.eval (List.ofFn x5 ++ [x5 0 && x5 3, b x5]) =
          (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5) := by
    intro x1 x2 b hev hb x5
    have h : x1.eval ((List.ofFn x5 ++ [x5 0 && x5 3]) ++
        [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (List.map (fun x7 : Fin 11 => (List.ofFn x5 ++ [x5 0 && x5 3]).getD x7.val false) x2)]) =
        (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5) :=
      hev x5
    rw [hb x5, List.append_assoc] at h
    exact h
  intro x1 x2 hfan hlen hev
  cases x2 with
  | nil =>
    exact h1 (fun _ => true) (Or.inr (Or.inl rfl)) x1 hfan
      (reduce_b x1 [] (fun _ => true) hev (fun _ => rfl))
  | cons a t =>
    cases t with
    | nil =>
      rcases split11 a with ha9 | ha9 | ha10
      · exact h1 (fun x => x ⟨a.val, ha9⟩) (Or.inr (Or.inr (Or.inl ⟨⟨a.val, ha9⟩, rfl⟩))) x1 hfan
          (reduce_b x1 [a] _ hev (fun x5 => by
            change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false && true) = _
            rw [Bool.and_true, wire_lt x5 a ha9]))
      · exact h1 (fun x => x 0 && x 3) (Or.inr (Or.inr (Or.inr rfl))) x1 hfan
          (reduce_b x1 [a] _ hev (fun x5 => by
            change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false && true) = _
            rw [Bool.and_true, wire_9 x5 a ha9]))
      · exact h1 (fun _ => false) (Or.inl rfl) x1 hfan
          (reduce_b x1 [a] _ hev (fun x5 => by
            change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false && true) = _
            rw [Bool.and_true, wire_10 x5 a ha10]))
    | cons c u =>
      cases u with
      | cons d v =>
        exfalso
        exact Nat.not_succ_le_self 2 (Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le v.length)))) hlen)
      | nil =>
        rcases split11 a with ha9 | ha9 | ha10
        · rcases split11 c with hc9 | hc9 | hc10
          · let i : Fin 9 := ⟨a.val, ha9⟩
            let j : Fin 9 := ⟨c.val, hc9⟩
            rcases lt_trichotomy i j with hij | hij | hji
            · exact h2 i j hij x1 hfan
                (reduce_b x1 [a, c] _ hev (fun x5 => by
                  change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                    ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                  rw [Bool.and_true, wire_lt x5 a ha9, wire_lt x5 c hc9]))
            · exact h1 (fun x => x i) (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))) x1 hfan
                (reduce_b x1 [a, c] _ hev (fun x5 => by
                  change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                    ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                  rw [Bool.and_true, wire_lt x5 a ha9, wire_lt x5 c hc9]
                  change (x5 i && x5 j) = x5 i
                  rw [← hij, Bool.and_self]))
            · exact h2 j i hji x1 hfan
                (reduce_b x1 [a, c] _ hev (fun x5 => by
                  change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                    ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                  rw [Bool.and_true, wire_lt x5 a ha9, wire_lt x5 c hc9]
                  exact Bool.and_comm (x5 i) (x5 j)))
          · let k : Fin 9 := ⟨a.val, ha9⟩
            by_cases hk0 : k = 0
            · exact h1 (fun x => x 0 && x 3) (Or.inr (Or.inr (Or.inr rfl))) x1 hfan
                (reduce_b x1 [a, c] _ hev (fun x5 => by
                  change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                    ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                  rw [Bool.and_true, wire_lt x5 a ha9, wire_9 x5 c hc9]
                  change (x5 k && (x5 0 && x5 3)) = (x5 0 && x5 3)
                  rw [hk0, Bool.and_comm, and_0_3_0]))
            · by_cases hk3 : k = 3
              · exact h1 (fun x => x 0 && x 3) (Or.inr (Or.inr (Or.inr rfl))) x1 hfan
                  (reduce_b x1 [a, c] _ hev (fun x5 => by
                    change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                      ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                    rw [Bool.and_true, wire_lt x5 a ha9, wire_9 x5 c hc9]
                    change (x5 k && (x5 0 && x5 3)) = (x5 0 && x5 3)
                    rw [hk3, Bool.and_comm, and_0_3_3]))
              · exact h3 k hk0 hk3 x1 hfan
                  (reduce_b x1 [a, c] _ hev (fun x5 => by
                    change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                      ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                    rw [Bool.and_true, wire_lt x5 a ha9, wire_9 x5 c hc9]
                    exact Bool.and_comm (x5 k) (x5 0 && x5 3)))
          · exact h1 (fun _ => false) (Or.inl rfl) x1 hfan
              (reduce_b x1 [a, c] _ hev (fun x5 => by
                change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                  ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                rw [Bool.and_true, wire_10 x5 c hc10, Bool.and_false]))
        · rcases split11 c with hc9 | hc9 | hc10
          · let k : Fin 9 := ⟨c.val, hc9⟩
            by_cases hk0 : k = 0
            · exact h1 (fun x => x 0 && x 3) (Or.inr (Or.inr (Or.inr rfl))) x1 hfan
                (reduce_b x1 [a, c] _ hev (fun x5 => by
                  change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                    ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                  rw [Bool.and_true, wire_9 x5 a ha9, wire_lt x5 c hc9]
                  change ((x5 0 && x5 3) && x5 k) = (x5 0 && x5 3)
                  rw [hk0, and_0_3_0]))
            · by_cases hk3 : k = 3
              · exact h1 (fun x => x 0 && x 3) (Or.inr (Or.inr (Or.inr rfl))) x1 hfan
                  (reduce_b x1 [a, c] _ hev (fun x5 => by
                    change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                      ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                    rw [Bool.and_true, wire_9 x5 a ha9, wire_lt x5 c hc9]
                    change ((x5 0 && x5 3) && x5 k) = (x5 0 && x5 3)
                    rw [hk3, and_0_3_3]))
              · exact h3 k hk0 hk3 x1 hfan
                  (reduce_b x1 [a, c] _ hev (fun x5 => by
                    change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                      ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                    rw [Bool.and_true, wire_9 x5 a ha9, wire_lt x5 c hc9]))
          · exact h1 (fun x => x 0 && x 3) (Or.inr (Or.inr (Or.inr rfl))) x1 hfan
              (reduce_b x1 [a, c] _ hev (fun x5 => by
                change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                  ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                rw [Bool.and_true, wire_9 x5 a ha9, wire_9 x5 c hc9, Bool.and_self]))
          · exact h1 (fun _ => false) (Or.inl rfl) x1 hfan
              (reduce_b x1 [a, c] _ hev (fun x5 => by
                change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                  ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
                rw [Bool.and_true, wire_10 x5 c hc10, Bool.and_false]))
        · exact h1 (fun _ => false) (Or.inl rfl) x1 hfan
            (reduce_b x1 [a, c] _ hev (fun x5 => by
              change ((List.ofFn x5 ++ [x5 0 && x5 3]).getD a.val false &&
                ((List.ofFn x5 ++ [x5 0 && x5 3]).getD c.val false && true)) = _
              rw [Bool.and_true, wire_10 x5 a ha10, Bool.false_and]))
