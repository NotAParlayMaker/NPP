import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- In a minimum circuit under this budget, some essential input has only one operand position.
set_option synthInstance.maxSize 4096 in
theorem PEqualNP.Outside.R_meta_1985_27
    (inputReads : ∀ (n : ℕ) (D : Circuit), IsMinimalMonoCircuit n D →
      D.size + 1 < 2 * n →
      (∀ u : Fin n, (∃ x : Fin n → Bool, D.eval (List.ofFn x) ≠ x u) ∧
        ∃ x y : Fin n → Bool, (∀ i ≠ u, x i = y i) ∧ D.eval (List.ofFn x) ≠ D.eval (List.ofFn y)) →
      ∃ u : Fin n, (D.gates.flatMap Gate.inputs).count u.val = 1)
    (singleRead : let edges : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      ∀ (D : Circuit) (u : Fin 14), IsMinimalMonoCircuit 14 D →
        (D.gates.flatMap Gate.inputs).count u.val = 1 →
        (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true) →
        27 ≤ D.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  classical
  intro C hC _ _ hEval
  let P (s : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun 14 D = circuitFun 14 C ∧ D.size = s
  have hex : ∃ s, P s := ⟨C.size, C, hC, rfl, rfl⟩
  obtain ⟨D, hD, hEq, hSize⟩ := Nat.find_spec hex
  have hle : D.size ≤ C.size := hSize.trans_le (Nat.find_min' hex ⟨C, hC, rfl, rfl⟩)
  have hMin : IsMinimalMonoCircuit 14 D :=
    ⟨hD, fun T hT e => hSize.trans_le (Nat.find_min' hex ⟨T, hT, e.trans hEq, rfl⟩)⟩
  let edges : List (ℕ × ℕ) :=
    [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let hit (x : Fin 14 → Bool) := ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
  have spec (x : Fin 14 → Bool) : D.eval (List.ofFn x) = true ↔ hit x := by
    simpa only [show D.eval (List.ofFn x) = C.eval (List.ofFn x) from congrFun hEq x] using hEval x
  let one (u i : Fin 14) := i == u
  let two (u v i : Fin 14) := i == u || i == v
  have rows : ∀ u : Fin 14, ¬ hit (one u) ∧ ∃ v : Fin 14, hit (two u v) := by
    dsimp only [hit, edges, one, two]
    decide
  by_contra! hsmall
  obtain ⟨u, hu⟩ := inputReads 14 D hMin (by omega) (fun u => by
    obtain ⟨v, hv⟩ := (rows u).2
    refine ⟨⟨one u, ?_⟩, ⟨two u v, one v, ?_, ?_⟩⟩
    · simpa [one] using mt (spec (one u)).mp (rows u).1
    · intro i hi
      simp [one, two, hi]
    · rw [(spec _).mpr hv]
      exact Ne.symm (mt (spec (one v)).mp (rows v).1))
  have := singleRead D u hMin hu spec
  omega
