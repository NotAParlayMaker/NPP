import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1791_1 :
    (∀ (b : (Fin (9 : ℕ) → Bool) → Bool),
      (b = fun _ => Bool.false) ∨ (b = fun _ => Bool.true) ∨
        (∃ (k : Fin (9 : ℕ)), b = fun x => x k) ∨
        (b = fun x => x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ))) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
        x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          x3.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)), b x6]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) →
    (∀ (i j : Fin (9 : ℕ)), i < j →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
        x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          x3.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)), x6 i && x6 j]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) →
    (∀ (k : Fin (9 : ℕ)), k ≠ (0 : Fin (9 : ℕ)) → k ≠ (1 : Fin (9 : ℕ)) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
        x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          x3.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) && x6 k]) ≠
            (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) →
    ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ))]; x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro hDeg hPair hThree x1 hx1 x3 hF hS
  have hAnd0 : PEqualNP.CircuitLowerBounds.GateOp.and.eval [] = Bool.true := rfl
  have hAnd1 : ∀ b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [b] = b := by
    intro b; cases b <;> rfl
  have hAnd2 : ∀ b1 b2 : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [b1, b2] = (b1 && b2) := by
    intro b1 b2; cases b1 <;> cases b2 <;> rfl
  have hGetLt : ∀ (x6 : Fin 9 → Bool) (a : ℕ) (ha : a < 9),
      (List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false = x6 ⟨a, ha⟩ := by
    intro x6 a ha
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [List.length_ofFn]; exact ha)]
    rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact ha)]
    rw [List.getElem_ofFn]
    rfl
  have hGet9 : ∀ (x6 : Fin 9 → Bool),
      (List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false = (x6 0 && x6 1) := by
    intro x6
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [List.length_ofFn])]
    rw [List.length_ofFn, Nat.sub_self]
    rfl
  have hGetGe : ∀ (x6 : Fin 9 → Bool) (a : ℕ), 10 ≤ a →
      (List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false = Bool.false := by
    intro x6 a ha
    rw [List.getD_eq_getElem?_getD]
    have hlen : (List.ofFn x6 ++ [x6 0 && x6 1]).length ≤ a := by
      rw [List.length_append, List.length_ofFn]
      exact ha
    rw [List.getElem?_eq_none hlen]
    rfl
  have hApply : ∀ (f : (Fin 9 → Bool) → Bool),
      (∀ x6 : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (List.map (fun x8 => (List.ofFn x6 ++ [x6 0 && x6 1]).getD x8 Bool.false) x1) = f x6) →
      (∃ x6 : Fin 9 → Bool,
        x3.eval (List.ofFn x6 ++ [x6 0 && x6 1, f x6]) ≠
          (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) →
      ∃ x6 : Fin 9 → Bool,
        have x7 : List Bool := List.ofFn x6 ++ [x6 0 && x6 1]
        x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun x8 => x7.getD x8 Bool.false) x1)]) ≠
          (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5) := by
    intro f hf hEx
    rcases hEx with ⟨x6, hx6⟩
    refine ⟨x6, ?_⟩
    change x3.eval ((List.ofFn x6 ++ [x6 0 && x6 1]) ++
      [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun x8 => (List.ofFn x6 ++ [x6 0 && x6 1]).getD x8 Bool.false) x1)]) ≠ _
    rw [hf x6]
    have happ : (List.ofFn x6 ++ [x6 0 && x6 1]) ++ [f x6] = List.ofFn x6 ++ [x6 0 && x6 1, f x6] :=
      List.append_assoc _ _ _
    rw [happ]
    exact hx6
  cases x1 with
  | nil =>
    exact hApply (fun _ => Bool.true) (fun _ => hAnd0)
      (hDeg (fun _ => Bool.true) (Or.inr (Or.inl rfl)) x3 hF hS)
  | cons a t =>
    cases t with
    | nil =>
      by_cases ha9 : a < 9
      · exact hApply (fun x => x ⟨a, ha9⟩)
          (fun x6 => by
            change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false] = _
            rw [hAnd1, hGetLt x6 a ha9])
          (hDeg (fun x => x ⟨a, ha9⟩) (Or.inr (Or.inr (Or.inl ⟨⟨a, ha9⟩, rfl⟩))) x3 hF hS)
      · by_cases haEq : a = 9
        · subst haEq
          exact hApply (fun x => x 0 && x 1)
            (fun x6 => by
              change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false] = _
              rw [hAnd1, hGet9 x6])
            (hDeg (fun x => x 0 && x 1) (Or.inr (Or.inr (Or.inr rfl))) x3 hF hS)
        · have hge : 10 ≤ a := by omega
          exact hApply (fun _ => Bool.false)
            (fun x6 => by
              change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false] = _
              rw [hAnd1, hGetGe x6 a hge])
            (hDeg (fun _ => Bool.false) (Or.inl rfl) x3 hF hS)
    | cons b t2 =>
      cases t2 with
      | nil =>
        by_cases ha10 : 10 ≤ a
        · exact hApply (fun _ => Bool.false)
            (fun x6 => by
              change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD b Bool.false] = _
              rw [hAnd2, hGetGe x6 a ha10]; exact Bool.false_and _)
            (hDeg (fun _ => Bool.false) (Or.inl rfl) x3 hF hS)
        · by_cases hb10 : 10 ≤ b
          · exact hApply (fun _ => Bool.false)
              (fun x6 => by
                change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD b Bool.false] = _
                rw [hAnd2, hGetGe x6 b hb10]; exact Bool.and_false _)
              (hDeg (fun _ => Bool.false) (Or.inl rfl) x3 hF hS)
          · by_cases haEq : a = 9
            · subst haEq
              by_cases hbEq : b = 9
              · subst hbEq
                exact hApply (fun x => x 0 && x 1)
                  (fun x6 => by
                    change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false] = _
                    rw [hAnd2, hGet9 x6]; exact Bool.and_self _)
                  (hDeg (fun x => x 0 && x 1) (Or.inr (Or.inr (Or.inr rfl))) x3 hF hS)
              · have hb9 : b < 9 := by omega
                by_cases hb0 : b = 0
                · subst hb0
                  exact hApply (fun x => x 0 && x 1)
                    (fun x6 => by
                      change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD 0 Bool.false] = _
                      rw [hAnd2, hGet9 x6, hGetLt x6 0 hb9]
                      change ((x6 0 && x6 1) && x6 0) = (x6 0 && x6 1)
                      cases x6 0 <;> cases x6 1 <;> rfl)
                    (hDeg (fun x => x 0 && x 1) (Or.inr (Or.inr (Or.inr rfl))) x3 hF hS)
                · by_cases hb1 : b = 1
                  · subst hb1
                    exact hApply (fun x => x 0 && x 1)
                      (fun x6 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD 1 Bool.false] = _
                        rw [hAnd2, hGet9 x6, hGetLt x6 1 hb9]
                        change ((x6 0 && x6 1) && x6 1) = (x6 0 && x6 1)
                        cases x6 0 <;> cases x6 1 <;> rfl)
                      (hDeg (fun x => x 0 && x 1) (Or.inr (Or.inr (Or.inr rfl))) x3 hF hS)
                  · have hne0 : (⟨b, hb9⟩ : Fin 9) ≠ 0 := fun h => hb0 (congrArg Fin.val h)
                    have hne1 : (⟨b, hb9⟩ : Fin 9) ≠ 1 := fun h => hb1 (congrArg Fin.val h)
                    exact hApply (fun x => x 0 && x 1 && x ⟨b, hb9⟩)
                      (fun x6 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD b Bool.false] = _
                        rw [hAnd2, hGet9 x6, hGetLt x6 b hb9])
                      (hThree ⟨b, hb9⟩ hne0 hne1 x3 hF hS)
            · have ha9 : a < 9 := by omega
              by_cases hbEq : b = 9
              · subst hbEq
                by_cases ha0 : a = 0
                · subst ha0
                  exact hApply (fun x => x 0 && x 1)
                    (fun x6 => by
                      change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD 0 Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false] = _
                      rw [hAnd2, hGetLt x6 0 ha9, hGet9 x6]
                      change (x6 0 && (x6 0 && x6 1)) = (x6 0 && x6 1)
                      cases x6 0 <;> cases x6 1 <;> rfl)
                    (hDeg (fun x => x 0 && x 1) (Or.inr (Or.inr (Or.inr rfl))) x3 hF hS)
                · by_cases ha1 : a = 1
                  · subst ha1
                    exact hApply (fun x => x 0 && x 1)
                      (fun x6 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD 1 Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false] = _
                        rw [hAnd2, hGetLt x6 1 ha9, hGet9 x6]
                        change (x6 1 && (x6 0 && x6 1)) = (x6 0 && x6 1)
                        cases x6 0 <;> cases x6 1 <;> rfl)
                      (hDeg (fun x => x 0 && x 1) (Or.inr (Or.inr (Or.inr rfl))) x3 hF hS)
                  · have hne0 : (⟨a, ha9⟩ : Fin 9) ≠ 0 := fun h => ha0 (congrArg Fin.val h)
                    have hne1 : (⟨a, ha9⟩ : Fin 9) ≠ 1 := fun h => ha1 (congrArg Fin.val h)
                    exact hApply (fun x => x 0 && x 1 && x ⟨a, ha9⟩)
                      (fun x6 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false] = _
                        rw [hAnd2, hGetLt x6 a ha9, hGet9 x6]
                        exact Bool.and_comm _ _)
                      (hThree ⟨a, ha9⟩ hne0 hne1 x3 hF hS)
              · have hb9 : b < 9 := by omega
                by_cases hab : a = b
                · subst hab
                  exact hApply (fun x => x ⟨a, ha9⟩)
                    (fun x6 => by
                      change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false] = _
                      rw [hAnd2, hGetLt x6 a ha9]
                      exact Bool.and_self _)
                    (hDeg (fun x => x ⟨a, ha9⟩) (Or.inr (Or.inr (Or.inl ⟨⟨a, ha9⟩, rfl⟩))) x3 hF hS)
                · by_cases hlt : a < b
                  · exact hApply (fun x => x ⟨a, ha9⟩ && x ⟨b, hb9⟩)
                      (fun x6 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD b Bool.false] = _
                        rw [hAnd2, hGetLt x6 a ha9, hGetLt x6 b hb9])
                      (hPair ⟨a, ha9⟩ ⟨b, hb9⟩ hlt x3 hF hS)
                  · have hlt' : b < a := by omega
                    exact hApply (fun x => x ⟨b, hb9⟩ && x ⟨a, ha9⟩)
                      (fun x6 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.and.eval [(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false, (List.ofFn x6 ++ [x6 0 && x6 1]).getD b Bool.false] = _
                        rw [hAnd2, hGetLt x6 a ha9, hGetLt x6 b hb9]
                        exact Bool.and_comm _ _)
                      (hPair ⟨b, hb9⟩ ⟨a, ha9⟩ hlt' x3 hF hS)
      | cons c t3 =>
        exfalso
        have hlen : 3 ≤ (a :: b :: c :: t3).length := by
          rw [List.length_cons, List.length_cons, List.length_cons]
          omega
        omega
