import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1868_1 :
    (∀ (b : (Fin (9 : ℕ) → Bool) → Bool),
      (b = fun _ => Bool.false) ∨
        (∃ (k : Fin (9 : ℕ)), b = fun x => x k) ∨
        (b = fun x => x (0 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ))) →
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x5 : Fin (9 : ℕ) → Bool),
          x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)), b x5]) =
            (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
        (14 : ℕ) ≤ x1.size) →
    (∀ (i j : Fin (9 : ℕ)), i < j →
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x5 : Fin (9 : ℕ) → Bool),
          x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)), x5 i || x5 j]) =
            (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
        (14 : ℕ) ≤ x1.size) →
    (∀ (k : Fin (9 : ℕ)), k ≠ (0 : Fin (9 : ℕ)) → k ≠ (3 : Fin (9 : ℕ)) →
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
        (∀ (x5 : Fin (9 : ℕ) → Bool),
          x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)), (x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))) || x5 k]) =
            (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
        (14 : ℕ) ≤ x1.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]; x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro hDeg hPair hThree x1 x2 hF hx2 hEq
  have hOr0 : PEqualNP.CircuitLowerBounds.GateOp.or.eval [] = Bool.false := rfl
  have hOr1 : ∀ b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [b] = b := by
    intro b; cases b <;> rfl
  have hOr2 : ∀ b1 b2 : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [b1, b2] = (b1 || b2) := by
    intro b1 b2; cases b1 <;> cases b2 <;> rfl
  have hGetLt : ∀ (x5 : Fin 9 → Bool) (a : ℕ) (ha : a < 9),
      (List.ofFn x5 ++ [x5 0 && x5 3]).getD a Bool.false = x5 ⟨a, ha⟩ := by
    intro x5 a ha
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by rw [List.length_ofFn]; exact ha)]
    rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact ha)]
    rw [List.getElem_ofFn]
    rfl
  have hGet9 : ∀ (x5 : Fin 9 → Bool),
      (List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false = (x5 0 && x5 3) := by
    intro x5
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [List.length_ofFn])]
    rw [List.length_ofFn, Nat.sub_self]
    rfl
  have hGet10 : ∀ (x5 : Fin 9 → Bool),
      (List.ofFn x5 ++ [x5 0 && x5 3]).getD 10 Bool.false = Bool.false := by
    intro x5
    rw [List.getD_eq_getElem?_getD]
    have hlen : (List.ofFn x5 ++ [x5 0 && x5 3]).length ≤ 10 := by
      rw [List.length_append, List.length_ofFn]
      exact le_refl 10
    rw [List.getElem?_eq_none hlen]
    rfl
  have hUse : ∀ (f : (Fin 9 → Bool) → Bool),
      (∀ x5 : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (List.map (fun (x7 : Fin 11) => (List.ofFn x5 ++ [x5 0 && x5 3]).getD (↑x7) Bool.false) x2) = f x5) →
      ∀ x5 : Fin 9 → Bool,
        x1.eval (List.ofFn x5 ++ [x5 0 && x5 3, f x5]) =
          (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5) := by
    intro f hf x5
    have h5 := hEq x5
    change x1.eval ((List.ofFn x5 ++ [x5 0 && x5 3]) ++
      [PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (List.map (fun (x7 : Fin 11) => (List.ofFn x5 ++ [x5 0 && x5 3]).getD (↑x7) Bool.false) x2)]) = _ at h5
    rw [hf x5] at h5
    have happ : (List.ofFn x5 ++ [x5 0 && x5 3]) ++ [f x5] = List.ofFn x5 ++ [x5 0 && x5 3, f x5] :=
      List.append_assoc _ _ _
    rw [happ] at h5
    exact h5
  have hSingle : ∀ (w : Fin 11),
      (∀ x5 : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (List.map (fun (x7 : Fin 11) => (List.ofFn x5 ++ [x5 0 && x5 3]).getD (↑x7) Bool.false) x2) =
          (List.ofFn x5 ++ [x5 0 && x5 3]).getD w.val Bool.false) →
      14 ≤ x1.size := by
    intro w hw
    rcases w with ⟨a, ha⟩
    by_cases ha9 : a < 9
    · exact hDeg (fun x => x ⟨a, ha9⟩) (Or.inr (Or.inl ⟨⟨a, ha9⟩, rfl⟩)) x1 hF
        (hUse (fun x => x ⟨a, ha9⟩) (fun x5 => (hw x5).trans (hGetLt x5 a ha9)))
    · by_cases haEq : a = 9
      · subst haEq
        exact hDeg (fun x => x 0 && x 3) (Or.inr (Or.inr rfl)) x1 hF
          (hUse (fun x => x 0 && x 3) (fun x5 => (hw x5).trans (hGet9 x5)))
      · have ha10 : a = 10 := by omega
        subst ha10
        exact hDeg (fun _ => Bool.false) (Or.inl rfl) x1 hF
          (hUse (fun _ => Bool.false) (fun x5 => (hw x5).trans (hGet10 x5)))
  cases x2 with
  | nil =>
    exact hDeg (fun _ => Bool.false) (Or.inl rfl) x1 hF
      (hUse (fun _ => Bool.false) (fun _ => hOr0))
  | cons u t =>
    cases t with
    | nil =>
      exact hSingle u (fun x5 => by
        change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD u.val Bool.false] = _
        exact hOr1 _)
    | cons v t2 =>
      cases t2 with
      | nil =>
        rcases u with ⟨a, ha⟩
        rcases v with ⟨b, hb⟩
        by_cases ha10 : a = 10
        · subst ha10
          exact hSingle ⟨b, hb⟩ (fun x5 => by
            change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD 10 Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD b Bool.false] = _
            rw [hOr2, hGet10 x5]; exact Bool.false_or _)
        · by_cases hb10 : b = 10
          · subst hb10
            exact hSingle ⟨a, ha⟩ (fun x5 => by
              change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD a Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD 10 Bool.false] = _
              rw [hOr2, hGet10 x5]; exact Bool.or_false _)
          · by_cases haEq : a = 9
            · subst haEq
              by_cases hbEq : b = 9
              · subst hbEq
                exact hDeg (fun x => x 0 && x 3) (Or.inr (Or.inr rfl)) x1 hF
                  (hUse (fun x => x 0 && x 3) (fun x5 => by
                    change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false] = _
                    rw [hOr2, hGet9 x5]; exact Bool.or_self _))
              · have hb9 : b < 9 := by omega
                by_cases hb0 : b = 0
                · subst hb0
                  exact hDeg (fun x => x 0) (Or.inr (Or.inl ⟨0, rfl⟩)) x1 hF
                    (hUse (fun x => x 0) (fun x5 => by
                      change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD 0 Bool.false] = _
                      rw [hOr2, hGet9 x5, hGetLt x5 0 hb9]
                      change ((x5 0 && x5 3) || x5 0) = x5 0
                      cases x5 0 <;> cases x5 3 <;> rfl))
                · by_cases hb3 : b = 3
                  · subst hb3
                    exact hDeg (fun x => x 3) (Or.inr (Or.inl ⟨3, rfl⟩)) x1 hF
                      (hUse (fun x => x 3) (fun x5 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD 3 Bool.false] = _
                        rw [hOr2, hGet9 x5, hGetLt x5 3 hb9]
                        change ((x5 0 && x5 3) || x5 3) = x5 3
                        cases x5 0 <;> cases x5 3 <;> rfl))
                  · have hne0 : (⟨b, hb9⟩ : Fin 9) ≠ 0 := fun h => hb0 (congrArg Fin.val h)
                    have hne3 : (⟨b, hb9⟩ : Fin 9) ≠ 3 := fun h => hb3 (congrArg Fin.val h)
                    exact hThree ⟨b, hb9⟩ hne0 hne3 x1 hF
                      (hUse (fun x => (x 0 && x 3) || x ⟨b, hb9⟩) (fun x5 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD b Bool.false] = _
                        rw [hOr2, hGet9 x5, hGetLt x5 b hb9]))
            · have ha9 : a < 9 := by omega
              by_cases hbEq : b = 9
              · subst hbEq
                by_cases ha0 : a = 0
                · subst ha0
                  exact hDeg (fun x => x 0) (Or.inr (Or.inl ⟨0, rfl⟩)) x1 hF
                    (hUse (fun x => x 0) (fun x5 => by
                      change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD 0 Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false] = _
                      rw [hOr2, hGetLt x5 0 ha9, hGet9 x5]
                      change (x5 0 || (x5 0 && x5 3)) = x5 0
                      cases x5 0 <;> cases x5 3 <;> rfl))
                · by_cases ha3 : a = 3
                  · subst ha3
                    exact hDeg (fun x => x 3) (Or.inr (Or.inl ⟨3, rfl⟩)) x1 hF
                      (hUse (fun x => x 3) (fun x5 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD 3 Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false] = _
                        rw [hOr2, hGetLt x5 3 ha9, hGet9 x5]
                        change (x5 3 || (x5 0 && x5 3)) = x5 3
                        cases x5 0 <;> cases x5 3 <;> rfl))
                  · have hne0 : (⟨a, ha9⟩ : Fin 9) ≠ 0 := fun h => ha0 (congrArg Fin.val h)
                    have hne3 : (⟨a, ha9⟩ : Fin 9) ≠ 3 := fun h => ha3 (congrArg Fin.val h)
                    exact hThree ⟨a, ha9⟩ hne0 hne3 x1 hF
                      (hUse (fun x => (x 0 && x 3) || x ⟨a, ha9⟩) (fun x5 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD a Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD 9 Bool.false] = _
                        rw [hOr2, hGetLt x5 a ha9, hGet9 x5]
                        exact Bool.or_comm _ _))
              · have hb9 : b < 9 := by omega
                by_cases hab : a = b
                · subst hab
                  exact hDeg (fun x => x ⟨a, ha9⟩) (Or.inr (Or.inl ⟨⟨a, ha9⟩, rfl⟩)) x1 hF
                    (hUse (fun x => x ⟨a, ha9⟩) (fun x5 => by
                      change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD a Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD a Bool.false] = _
                      rw [hOr2, hGetLt x5 a ha9]
                      exact Bool.or_self _))
                · by_cases hlt : a < b
                  · exact hPair ⟨a, ha9⟩ ⟨b, hb9⟩ hlt x1 hF
                      (hUse (fun x => x ⟨a, ha9⟩ || x ⟨b, hb9⟩) (fun x5 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD a Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD b Bool.false] = _
                        rw [hOr2, hGetLt x5 a ha9, hGetLt x5 b hb9]))
                  · have hlt' : b < a := by omega
                    exact hPair ⟨b, hb9⟩ ⟨a, ha9⟩ hlt' x1 hF
                      (hUse (fun x => x ⟨b, hb9⟩ || x ⟨a, ha9⟩) (fun x5 => by
                        change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x5 ++ [x5 0 && x5 3]).getD a Bool.false, (List.ofFn x5 ++ [x5 0 && x5 3]).getD b Bool.false] = _
                        rw [hOr2, hGetLt x5 a ha9, hGetLt x5 b hb9]
                        exact Bool.or_comm _ _))
      | cons c t3 =>
        exfalso
        have hlen : 3 ≤ (u :: v :: c :: t3).length := by
          rw [List.length_cons, List.length_cons, List.length_cons]
          omega
        omega
