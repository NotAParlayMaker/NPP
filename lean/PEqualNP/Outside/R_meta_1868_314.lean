import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1868_314
  (normalize :
    let edge := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
      (x 6 && x 8) || (x 8 && x 5)
    ∀ (C : Circuit) (pins : List (Fin 11)), FanInTwo C → pins.length ≤ 2 →
      (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 && x 3]
        C.eval (w ++ [GateOp.or.eval (pins.map (fun i => w.getD i.val false))]) = edge x) →
      C.size ≤ 13 → ∃ B : Circuit, FanInTwo B ∧ B.size ≤ 14 ∧
        PEqualNP.NotBracket.notCount B ≤ 1 ∧
        ∀ x : Fin 9 → Bool, (x 0 && x 3) = false → B.eval (List.ofFn x) = edge x)
  (mono :
    let edge := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
      (x 6 && x 8) || (x 8 && x 5)
    ∀ B : Circuit, FanInTwo B → PEqualNP.NotBracket.notCount B = 0 →
      (∀ x : Fin 9 → Bool, (x 0 && x 3) = false → B.eval (List.ofFn x) = edge x) → 15 ≤ B.size)
  (oneNot :
    let edge := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
      (x 6 && x 8) || (x 8 && x 5)
    ∀ B : Circuit, FanInTwo B → PEqualNP.NotBracket.notCount B = 1 →
      (∀ x : Fin 9 → Bool, (x 0 && x 3) = false → B.eval (List.ofFn x) = edge x) → 15 ≤ B.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  intro C pins fan card agree
  by_contra fail
  obtain ⟨B,fanin,size,negs,correct⟩ := normalize C pins fan card agree (by omega)
  rcases (show PEqualNP.NotBracket.notCount B = 0 ∨ PEqualNP.NotBracket.notCount B = 1 by omega) with h | h
  · have := mono B fanin h correct
    omega
  · have := oneNot B fanin h correct
    omega
