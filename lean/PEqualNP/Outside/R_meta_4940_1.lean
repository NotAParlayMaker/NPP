import PEqualNP.Defs

/-- Reduction of `L-meta-4940`: cut by the functional form of the single gate `g`.
Any fan-in-2 gate computes the AND or OR of two wires `u v` (a missing wire reads
`false`), the NOT of one wire, or a constant. -/
theorem PEqualNP.Outside.R_meta_4940_1
    (h1 : ∀ (u v : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (17 : ℕ) → have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)); have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ((List.ofFn x9) ++ [(List.ofFn x9).getD u false && (List.ofFn x9).getD v false])).getD x10 Bool.false; (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false)
    (h2 : ∀ (u v : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (17 : ℕ) → have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)); have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ((List.ofFn x9) ++ [(List.ofFn x9).getD u false || (List.ofFn x9).getD v false])).getD x10 Bool.false; (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false)
    (h3 : ∀ (u : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (17 : ℕ) → have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)); have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ((List.ofFn x9) ++ [!((List.ofFn x9).getD u false)])).getD x10 Bool.false; (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false)
    (h4 : ∀ (b : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (17 : ℕ) → have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)); have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ((List.ofFn x9) ++ [b])).getD x10 Bool.false; (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size = (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro x1 x2 x3 x4 hf1 hf2 hsize
  have hgate := hf1 x1 (by simp)
  rcases x1 with ⟨op, inputs⟩
  rcases hgate with ⟨hop, hlen⟩
  simp at hop
  rcases hop with rfl | rfl | rfl
  · rcases inputs with _ | ⟨a, t⟩
    ·
      have hw : ∀ (x : Fin (10 : ℕ) → Bool),
          ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
            = (List.ofFn x) ++ [Bool.true] := by
        intro x
        rfl
      simp only [hw]
      exact h4 Bool.true x2 x3 x4 hf2 hsize
    · rcases t with _ | ⟨b, t'⟩
      ·
        have hw : ∀ (x : Fin (10 : ℕ) → Bool),
            ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a]⟩], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
              = (List.ofFn x) ++ [(List.ofFn x).getD a false && (List.ofFn x).getD a false] := by
          intro x
          show (List.ofFn x) ++ [(List.ofFn x).getD a false && Bool.true] =
            (List.ofFn x) ++ [(List.ofFn x).getD a false && (List.ofFn x).getD a false]
          simp
        simp only [hw]
        exact h1 a a x2 x3 x4 hf2 hsize
      · rcases t' with _ | ⟨c, t''⟩
        ·
          have hw : ∀ (x : Fin (10 : ℕ) → Bool),
              ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
                = (List.ofFn x) ++ [(List.ofFn x).getD a false && (List.ofFn x).getD b false] := by
            intro x
            show (List.ofFn x) ++ [(List.ofFn x).getD a false && ((List.ofFn x).getD b false && Bool.true)] =
              (List.ofFn x) ++ [(List.ofFn x).getD a false && (List.ofFn x).getD b false]
            simp
          simp only [hw]
          exact h1 a b x2 x3 x4 hf2 hsize
        · simp at hlen
  · rcases inputs with _ | ⟨a, t⟩
    ·
      have hw : ∀ (x : Fin (10 : ℕ) → Bool),
          ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
            = (List.ofFn x) ++ [Bool.false] := by
        intro x
        rfl
      simp only [hw]
      exact h4 Bool.false x2 x3 x4 hf2 hsize
    · rcases t with _ | ⟨b, t'⟩
      ·
        have hw : ∀ (x : Fin (10 : ℕ) → Bool),
            ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
              = (List.ofFn x) ++ [(List.ofFn x).getD a false || (List.ofFn x).getD a false] := by
          intro x
          show (List.ofFn x) ++ [(List.ofFn x).getD a false || Bool.false] =
            (List.ofFn x) ++ [(List.ofFn x).getD a false || (List.ofFn x).getD a false]
          simp
        simp only [hw]
        exact h2 a a x2 x3 x4 hf2 hsize
      · rcases t' with _ | ⟨c, t''⟩
        ·
          have hw : ∀ (x : Fin (10 : ℕ) → Bool),
              ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
                = (List.ofFn x) ++ [(List.ofFn x).getD a false || (List.ofFn x).getD b false] := by
            intro x
            show (List.ofFn x) ++ [(List.ofFn x).getD a false || ((List.ofFn x).getD b false || Bool.false)] =
              (List.ofFn x) ++ [(List.ofFn x).getD a false || (List.ofFn x).getD b false]
            simp
          simp only [hw]
          exact h2 a b x2 x3 x4 hf2 hsize
        · simp at hlen
  · rcases inputs with _ | ⟨a, t⟩
    ·
      have hw : ∀ (x : Fin (10 : ℕ) → Bool),
          ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.not, []⟩], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
            = (List.ofFn x) ++ [Bool.true] := by
        intro x
        rfl
      simp only [hw]
      exact h4 Bool.true x2 x3 x4 hf2 hsize
    ·
      have hw : ∀ (x : Fin (10 : ℕ) → Bool),
          ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.not, a :: t⟩], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
            = (List.ofFn x) ++ [!((List.ofFn x).getD a false)] := by
        intro x
        rfl
      simp only [hw]
      exact h3 a x2 x3 x4 hf2 hsize
