import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1795_1 :
    (∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
      x3.size ≤ 13 →
      ∃ (x6 : Fin 9 → Bool),
        x3.eval (List.ofFn x6 ++ [x6 0 && x6 1, Bool.true]) ≠ (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) →
    (∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
      x3.size ≤ 13 →
      ∃ (x6 : Fin 9 → Bool),
        x3.eval (List.ofFn x6 ++ [x6 0 && x6 1, !(x6 0 && x6 1)]) ≠ (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) →
    (∀ (k : Fin 9) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
      x3.size ≤ 13 →
      ∃ (x6 : Fin 9 → Bool),
        x3.eval (List.ofFn x6 ++ [x6 0 && x6 1, !(x6 k)]) ≠ (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) →
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro h1 h2 h3 x1 _ x3 hFan hSize
  cases x1 with
  | nil =>
    rcases h1 x3 hFan hSize with ⟨x6, hx6⟩
    refine ⟨x6, fun hCont => hx6 ((congrArg x3.eval (List.append_assoc (List.ofFn x6) [x6 0 && x6 1] [Bool.true]).symm).trans hCont)⟩
  | cons a rest =>
    rcases Nat.lt_or_ge a 9 with ha9 | haGe9
    · rcases h3 ⟨a, ha9⟩ x3 hFan hSize with ⟨x6, hx6⟩
      refine ⟨x6, fun hCont => ?_⟩
      have hLen : (List.ofFn x6).length = 9 := List.length_ofFn
      have hGet : (List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false = x6 ⟨a, ha9⟩ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (hLen.symm ▸ ha9),
          List.getElem?_eq_getElem (hLen.symm ▸ ha9), List.getElem_ofFn]
        rfl
      have hEq : (List.ofFn x6 ++ [x6 0 && x6 1]) ++
          [!(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false] =
          List.ofFn x6 ++ [x6 0 && x6 1, !(x6 ⟨a, ha9⟩)] := by
        rw [List.append_assoc, hGet]
        rfl
      exact hx6 ((congrArg x3.eval hEq.symm).trans hCont)
    · rcases Nat.eq_or_lt_of_le haGe9 with hEq9 | haGt9
      · subst hEq9
        rcases h2 x3 hFan hSize with ⟨x6, hx6⟩
        refine ⟨x6, fun hCont => ?_⟩
        have h9 : (List.ofFn x6 ++ [x6 0 && x6 1])[9]? = Option.some (x6 0 && x6 1) := by
          have h := List.getElem?_append_right (l₁ := List.ofFn x6) (l₂ := [x6 0 && x6 1]) (i := 9)
            (Nat.le_of_eq List.length_ofFn)
          rw [List.length_ofFn] at h
          exact h
        have hGet : (List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false = (x6 0 && x6 1) := by
          rw [List.getD_eq_getElem?_getD, h9]
          rfl
        have hEq : (List.ofFn x6 ++ [x6 0 && x6 1]) ++
            [!(List.ofFn x6 ++ [x6 0 && x6 1]).getD 9 Bool.false] =
            List.ofFn x6 ++ [x6 0 && x6 1, !(x6 0 && x6 1)] := by
          rw [List.append_assoc, hGet]
          rfl
        exact hx6 ((congrArg x3.eval hEq.symm).trans hCont)
      · rcases h1 x3 hFan hSize with ⟨x6, hx6⟩
        refine ⟨x6, fun hCont => ?_⟩
        have hLen : (List.ofFn x6 ++ [x6 0 && x6 1]).length = 10 := by
          rw [List.length_append, List.length_ofFn, List.length_singleton]
        have hGet : (List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false = Bool.false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hLen.symm ▸ haGt9)]
          rfl
        have hEq : (List.ofFn x6 ++ [x6 0 && x6 1]) ++
            [!(List.ofFn x6 ++ [x6 0 && x6 1]).getD a Bool.false] =
            List.ofFn x6 ++ [x6 0 && x6 1, Bool.true] := by
          rw [List.append_assoc, hGet]
          rfl
        exact hx6 ((congrArg x3.eval hEq.symm).trans hCont)
