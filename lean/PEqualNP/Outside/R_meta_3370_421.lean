import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3370_421
    (mandatory :
      let readGate := fun (g : PEqualNP.CircuitLowerBounds.Gate) (v : ℕ) =>
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some v) ∨
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ v ∈ g.inputs)
      let target := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2
      ∀ (k : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [false, x 0 || x 4 || x k]) = target x) →
        (∀ v : Fin 9, ∃ g ∈ C.gates, readGate g v.val))
    (remaining :
      let readGate := fun (g : PEqualNP.CircuitLowerBounds.Gate) (v : ℕ) =>
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some v) ∨
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ v ∈ g.inputs)
      have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)), x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (2 : Fin (9 : ℕ)) ∨ x2 = (3 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [Bool.false, x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) || x7 x2]) = x1 x7) →
      (∀ v : Fin 9, ∃ g ∈ x4.gates, readGate g v.val) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)), x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (2 : Fin (9 : ℕ)) ∨ x2 = (3 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [Bool.false, x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) || x7 x2]) = x1 x7) → False := by
  dsimp only
  intro k hk C hFan hSize hCompute
  exact remaining k hk C hFan hSize hCompute (mandatory k C hCompute)
