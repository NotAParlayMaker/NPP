import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1868_524
    (mask : ∀ ins : List (Fin 11), ins.length ≤ 2 →
      ∃ (b : Bool) (T : Finset (Fin 9)), (if b then 1 else 0) + T.card ≤ 2 ∧
      ∀ x : Fin 9 → Bool,
        GateOp.or.eval (ins.map fun i => (List.ofFn x ++ [x 0 && x 3]).getD i.val false) =
          ((b && (x 0 && x 3)) || decide (∃ a ∈ T, x a = true)))
    (withoutFixed : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C → T.card ≤ 2 →
      (∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 && x 3, decide (∃ a ∈ T, x a = true)]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size)
    (withFixed : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C → T.card ≤ 1 →
      (∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 && x 3, (x 0 && x 3) || decide (∃ a ∈ T, x a = true)]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size) :∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  dsimp only
  intro C ins fan length eval
  obtain ⟨b,T,cost,norm⟩ := mask ins length
  cases b with
  | false =>
    apply withoutFixed C T fan (by simpa using cost)
    intro x
    have e := eval x
    rw [norm x] at e
    simp only [Bool.false_and, Bool.false_or, List.append_assoc, List.singleton_append] at e
    exact e
  | true =>
    apply withFixed C T fan (by simp at cost; omega)
    intro x
    have e := eval x
    rw [norm x] at e
    simp only [Bool.true_and, List.append_assoc, List.singleton_append] at e
    exact e