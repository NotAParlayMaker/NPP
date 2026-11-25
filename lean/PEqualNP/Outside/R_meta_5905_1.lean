import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5905_1
    (h1 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
          x1.size ≤ (14 : ℕ) →
            (2 : ℕ) ≤ List.countP (fun g => g.op.eval [Bool.false] || g.inputs.any fun w => w == 0 || w == 10) x1.gates →
              ∃ (x4 : Fin (10 : ℕ) → Bool),
                x4 (0 : Fin (10 : ℕ)) = Bool.false ∧
                x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠
                  (fun (x5 : Fin (10 : ℕ) → Bool) =>
                    Decidable.decide (∃ (x6 : Fin (10 : ℕ)) (x7 : Fin (10 : ℕ)),
                      x5 x6 = Bool.true ∧ x5 x7 = Bool.true ∧
                      ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true)) x4)
    (h2 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
          x1.size ≤ (14 : ℕ) →
            List.countP (fun g => g.op.eval [Bool.false]) x1.gates = (0 : ℕ) →
              List.countP (fun g => g.op.eval [Bool.false] || g.inputs.any fun w => w == 0 || w == 10) x1.gates ≤ (1 : ℕ) →
                ∃ (x4 : Fin (10 : ℕ) → Bool),
                  x4 (0 : Fin (10 : ℕ)) = Bool.false ∧
                  x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠
                    (fun (x5 : Fin (10 : ℕ) → Bool) =>
                      Decidable.decide (∃ (x6 : Fin (10 : ℕ)) (x7 : Fin (10 : ℕ)),
                        x5 x6 = Bool.true ∧ x5 x7 = Bool.true ∧
                        ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true)) x4)
    (h3 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x1 →
          x1.size ≤ (14 : ℕ) →
            List.countP (fun g => g.op.eval [Bool.false]) x1.gates = (1 : ℕ) →
              List.countP (fun g => g.op.eval [Bool.false] || g.inputs.any fun w => w == 0 || w == 10) x1.gates = (1 : ℕ) →
                ∃ (x4 : Fin (10 : ℕ) → Bool),
                  x4 (0 : Fin (10 : ℕ)) = Bool.false ∧
                  x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠
                    (fun (x5 : Fin (10 : ℕ) → Bool) =>
                      Decidable.decide (∃ (x6 : Fin (10 : ℕ)) (x7 : Fin (10 : ℕ)),
                        x5 x6 = Bool.true ∧ x5 x7 = Bool.true ∧
                        ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true)) x4) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size ≤ (14 : ℕ) →
          ∃ (x4 : Fin (10 : ℕ) → Bool),
            x4 (0 : Fin (10 : ℕ)) = Bool.false ∧
            x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠
              (fun (x5 : Fin (10 : ℕ) → Bool) =>
                Decidable.decide (∃ (x6 : Fin (10 : ℕ)) (x7 : Fin (10 : ℕ)),
                  x5 x6 = Bool.true ∧ x5 x7 = Bool.true ∧
                  ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true)) x4 := by
  intro x1 hfan hsize
  have hle :
      List.countP (fun g => g.op.eval [Bool.false]) x1.gates ≤
        List.countP (fun g => g.op.eval [Bool.false] || g.inputs.any fun w => w == 0 || w == 10) x1.gates := by
    induction x1.gates with
    | nil => exact Nat.le_refl 0
    | cons g gs ih =>
      rw [List.countP_cons, List.countP_cons]
      cases g.op.eval [Bool.false] <;> cases g.inputs.any (fun w => w == 0 || w == 10)
      · exact ih
      · exact Nat.le_succ_of_le ih
      · exact Nat.succ_le_succ ih
      · exact Nat.succ_le_succ ih
  by_cases hc : (2 : ℕ) ≤ List.countP (fun g => g.op.eval [Bool.false] || g.inputs.any fun w => w == 0 || w == 10) x1.gates
  · exact h1 x1 hfan hsize hc
  · by_cases hn : List.countP (fun g => g.op.eval [Bool.false]) x1.gates = 0
    · exact h2 x1 hfan hsize hn (by omega)
    · exact h3 x1 hfan hsize (by omega) (by omega)
