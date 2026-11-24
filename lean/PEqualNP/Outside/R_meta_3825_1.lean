import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3825_1
    (hBinary : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun 9 C = (fun (x8 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x9 : Fin (9 : ℕ)) (x10 : Fin (9 : ℕ)), ([(34 : ℕ), (68 : ℕ), (136 : ℕ), (272 : ℕ), (1 : ℕ), (128 : ℕ), (256 : ℕ), (0 : ℕ), (32 : ℕ)].getD ↑x9 (0 : ℕ)).testBit ↑x10 = Bool.true ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) → 14 ≤ C.gates.countP (fun g => g.op.eval [true]))
    (hRemaining : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size = (15 : ℕ) → x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(1 : ℕ), (0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ) + x5) ∧ x6.inputs.Nodup ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.not → x6.inputs.length = (1 : ℕ)) ∧ (x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x6.inputs.length = (2 : ℕ))) → List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1.gates ≤ (1 : ℕ) → (∀ x7 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x9 : Finset ℕ), (∀ x10 ∈ x9, x10 < x1.size ∧ (↑x7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs ∨ ∃ x12 < x10, ↑x7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (9 : ℕ) + x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs)) → x9.card ≤ (3 : ℕ)) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x8 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x9 : Fin (9 : ℕ)) (x10 : Fin (9 : ℕ)), ([(34 : ℕ), (68 : ℕ), (136 : ℕ), (272 : ℕ), (1 : ℕ), (128 : ℕ), (256 : ℕ), (0 : ℕ), (32 : ℕ)].getD ↑x9 (0 : ℕ)).testBit ↑x10 = Bool.true ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size = (15 : ℕ) → x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(1 : ℕ), (0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ) + x5) ∧ x6.inputs.Nodup ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.not → x6.inputs.length = (1 : ℕ)) ∧ (x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x6.inputs.length = (2 : ℕ))) → List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1.gates ≤ (2 : ℕ) → (∀ x7 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x9 : Finset ℕ), (∀ x10 ∈ x9, x10 < x1.size ∧ (↑x7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs ∨ ∃ x12 < x10, ↑x7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (9 : ℕ) + x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs)) → x9.card ≤ (3 : ℕ)) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x8 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x9 : Fin (9 : ℕ)) (x10 : Fin (9 : ℕ)), ([(34 : ℕ), (68 : ℕ), (136 : ℕ), (272 : ℕ), (1 : ℕ), (128 : ℕ), (256 : ℕ), (0 : ℕ), (32 : ℕ)].getD ↑x9 (0 : ℕ)).testBit ↑x10 = Bool.true ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) := by
  intro C hMinimal hSize hFirst hClean _ hCap hFun
  have hBinaryCount := hBinary C hMinimal.1 hFun
  have hPartition (ls : List PEqualNP.CircuitLowerBounds.Gate)
      (hls : ∀ g ∈ ls, g ∈ C.gates) :
      ls.countP (fun g => g.op.eval [true]) +
        ls.countP (fun g => g.op.eval [false]) = ls.length := by
    induction ls with
    | nil => rfl
    | cons g ls ih =>
      have hRest := ih (fun a ha => hls a (List.mem_cons_of_mem _ ha))
      have hOp := (hMinimal.1 g (hls g List.mem_cons_self)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hOp
      have hComplement : g.op.eval [false] = !(g.op.eval [true]) := by
        rcases hOp with hOp | hOp | hOp <;> rw [hOp] <;> rfl
      cases hEval : g.op.eval [true] <;> simp [hComplement, hEval] <;> omega
  have hTotal := hPartition C.gates (fun _ h => h)
  have hOne : C.gates.countP (fun g => g.op.eval [false]) ≤ 1 := by
    change C.gates.length = 15 at hSize
    omega
  exact hRemaining C hMinimal hSize hFirst hClean hOne hCap hFun
