import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2191_526
    (join : ∀ (n : ℕ) (P Q : Circuit) (o : ℕ), FanInTwo P → FanInTwo Q → o < n + P.size →
      ∃ C : Circuit, FanInTwo C ∧ C.size = P.size + Q.size ∧
        ∀ x : Fin n → Bool, let w := P.wires (List.ofFn x)
          C.eval (List.ofFn x) = Q.eval (w ++ [w.getD o false]))
    (lower : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)) 12)
    (exactBudget :
      let f := fun x : Fin 8 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)
      let h := fun x : Fin 8 → Bool => f x || x 0 || x 3
      ∀ (P Q : Circuit) (o : ℕ) (b : Bool), FanInTwo P → FanInTwo Q →
      P.size + Q.size = 13 → o < 8 + P.size →
      let w := fun x : Fin 8 → Bool => P.wires (List.ofFn x)
      let g := fun x : Fin 8 → Bool => (w x).getD o false
      (∀ i : Fin 8, (g ≠ fun x => x i) ∧ g ≠ fun x => !x i) →
      (∀ x, f x ≠ h x → g x = !b) →
      (∀ x, Q.eval (w x ++ [g x]) = f x) →
      ∃ x : Fin 8 → Bool, Q.eval (w x ++ [b]) ≠ h x) :have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   PEqualNP.MetaComplexity.FanInTwo x3 →     PEqualNP.MetaComplexity.FanInTwo x4 →       x3.size + x4.size ≤ (13 : ℕ) →         x5 < (8 : ℕ) + x3.size →           have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x3.wires (List.ofFn x11);           have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x5 Bool.false;           (∀ (x13 : Fin (8 : ℕ)), (x12 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => x14 x13) ∧ x12 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => !x14 x13) → (∀ (x14 : Fin (8 : ℕ) → Bool), x1 x14 ≠ x2 x14 → x12 x14 = !x6) → (∀ (x15 : Fin (8 : ℕ) → Bool), x4.eval (x11 x15 ++ [x12 x15]) = x1 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x4.eval (x11 x16 ++ [x6]) ≠ x2 x16 := by
  dsimp only
  intro P Q o b fanP fanQ budget available form separates computes
  obtain ⟨C,fanC,size,eval⟩ := join 8 P Q o fanP fanQ available
  have exactSize : P.size + Q.size = 13 := by
    by_contra unequal
    have hsmall : C.size ≤ 12 := by omega
    apply lower
    exact ⟨C,fanC,hsmall,fun x => (eval x).trans (computes x)⟩
  exact exactBudget P Q o b fanP fanQ exactSize available form separates computes