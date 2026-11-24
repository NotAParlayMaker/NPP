import PEqualNP.Defs

-- Eliminate the arbitrary NOT input list into the three exact semantic cases:
-- constant true, negation of wire 9 (x 0 && x 3), or negation of an input bit x k.
theorem PEqualNP.Outside.R_meta_1870_1
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ (x : Fin 9 → Bool),
        C.eval (List.ofFn x ++ [x 0 && x 3, Bool.true]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      14 ≤ C.size)
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ (x : Fin 9 → Bool),
        C.eval (List.ofFn x ++ [x 0 && x 3, !(x 0 && x 3)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      14 ≤ C.size)
    (h3 : ∀ (k : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ (x : Fin 9 → Bool),
        C.eval (List.ofFn x ++ [x 0 && x 3, !(x k)]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      14 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  intro C inp hfan _ heval
  cases inp with
  | nil =>
    apply h1 C hfan
    intro x
    have hx := heval x
    exact Eq.trans (congrArg C.eval (List.append_assoc (List.ofFn x) [x 0 && x 3] [Bool.true]).symm) hx
  | cons w tl =>
    by_cases hlt : w.val < 9
    · apply h3 ⟨w.val, hlt⟩ C hfan
      intro x
      have hx := heval x
      have hget : (List.ofFn x ++ [x 0 && x 3]).getD w.val false = x ⟨w.val, hlt⟩ := by
        have hlen : (List.ofFn x).length = 9 := List.length_ofFn
        have hlt' : w.val < (List.ofFn x).length := Eq.subst hlen.symm hlt
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt',
          List.getElem?_eq_getElem hlt', Option.getD_some, List.getElem_ofFn]
      have harg : (List.ofFn x ++ [x 0 && x 3]) ++
          [PEqualNP.CircuitLowerBounds.GateOp.not.eval
            (List.map (fun w0 : Fin 11 => (List.ofFn x ++ [x 0 && x 3]).getD w0.val false) (w :: tl))] =
          List.ofFn x ++ [x 0 && x 3, !(x ⟨w.val, hlt⟩)] := by
        rw [List.append_assoc]
        change List.ofFn x ++ [x 0 && x 3, !((List.ofFn x ++ [x 0 && x 3]).getD w.val false)] = _
        rw [hget]
      exact Eq.trans (congrArg C.eval harg.symm) hx
    · by_cases h9 : w.val = 9
      · apply h2 C hfan
        intro x
        have hx := heval x
        have hget : (List.ofFn x ++ [x 0 && x 3]).getD w.val false = (x 0 && x 3) := by
          have hlen : (List.ofFn x).length = 9 := List.length_ofFn
          rw [h9, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_eq hlen),
            hlen, Nat.sub_self]
          rfl
        have harg : (List.ofFn x ++ [x 0 && x 3]) ++
            [PEqualNP.CircuitLowerBounds.GateOp.not.eval
              (List.map (fun w0 : Fin 11 => (List.ofFn x ++ [x 0 && x 3]).getD w0.val false) (w :: tl))] =
            List.ofFn x ++ [x 0 && x 3, !(x 0 && x 3)] := by
          rw [List.append_assoc]
          change List.ofFn x ++ [x 0 && x 3, !((List.ofFn x ++ [x 0 && x 3]).getD w.val false)] = _
          rw [hget]
        exact Eq.trans (congrArg C.eval harg.symm) hx
      · apply h1 C hfan
        intro x
        have hx := heval x
        have hge : 10 ≤ w.val :=
          Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm h9))
        have hget : (List.ofFn x ++ [x 0 && x 3]).getD w.val false = false := by
          have hlen : (List.ofFn x ++ [x 0 && x 3]).length = 10 := by
            rw [List.length_append, List.length_ofFn, List.length_singleton]
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (Eq.subst (motive := fun m => m ≤ w.val) hlen.symm hge)]
          rfl
        have harg : (List.ofFn x ++ [x 0 && x 3]) ++
            [PEqualNP.CircuitLowerBounds.GateOp.not.eval
              (List.map (fun w0 : Fin 11 => (List.ofFn x ++ [x 0 && x 3]).getD w0.val false) (w :: tl))] =
            List.ofFn x ++ [x 0 && x 3, Bool.true] := by
          rw [List.append_assoc]
          change List.ofFn x ++ [x 0 && x 3, !((List.ofFn x ++ [x 0 && x 3]).getD w.val false)] = _
          rw [hget]
          rfl
        exact Eq.trans (congrArg C.eval harg.symm) hx
