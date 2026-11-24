import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2373_1
    (h1 : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) =>
        x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) ||
        x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) ||
        x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) ||
        x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) ||
        x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) ||
        x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) =>
        (x2.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(0 : ℕ)] }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false)
    (h2 : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) =>
        x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) ||
        x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) ||
        x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) ||
        x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) ||
        x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) ||
        x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) =>
        (x2.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (1 : ℕ)] }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false)
    (h3 : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) =>
        x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) ||
        x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) ||
        x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) ||
        x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) ||
        x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) ||
        x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) =>
        (x2.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (2 : ℕ)] }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false)
    (h4 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      (x1 = (1 : ℕ) ∨ x1 = (2 : ℕ)) →
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size ≤ (17 : ℕ) →
      have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) =>
        x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) ||
        x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) ||
        x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) ||
        x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) ||
        x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) ||
        x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) ||
        x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));
      have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) =>
        (x2.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), x1] }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;
      (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) →
      (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) →
      (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro x1 x2 x3 x4 hfan1 hfan2 hsz
  dsimp only
  intro h34 h43 hbelow
  let pet : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have hstep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool),
      (gs.foldl step ws).length = ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro ws; simp
    | cons g gs ih =>
      intro ws
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have hstep_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws : List Bool) (i : ℕ),
      i < ws.length → (gs.foldl step ws).getD i false = ws.getD i false := by
    intro gs
    induction gs with
    | nil => intro ws i _; rfl
    | cons g gs ih =>
      intro ws i hi
      rw [List.foldl_cons]
      have hlt : i < (step ws g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (step ws g) i hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hsingle_wires : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (x : Fin 10 → Bool),
      ({ gates := [g], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x) =
        List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)] := by
    intro g x
    rfl
  -- Helper: replacing x1 by an extensionally equivalent gate g'
  have hreplace_g1 : ∀ (g' : PEqualNP.CircuitLowerBounds.Gate),
      (∀ x : Fin 10 → Bool,
        g'.op.eval (g'.inputs.map fun i => (List.ofFn x).getD i false) =
        x1.op.eval (x1.inputs.map fun i => (List.ofFn x).getD i false)) →
      ((∃ x10 : Fin 10 → Bool,
          (x2.wires ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x3 false = true ∧
          (x2.wires ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x4 false = false) →
       (∃ x11 : Fin 10 → Bool,
          (x2.wires ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x3 false = false ∧
          (x2.wires ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x4 false = true) →
       (∀ x12 : Fin 10 → Bool, pet x12 = false →
          (x2.wires ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x12))).getD x3 false = false ∧
          (x2.wires ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x12))).getD x4 false = false) →
       ∃ x13 : Fin 10 → Bool, pet x13 = true ∧
          (x2.wires ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x3 false = false ∧
          (x2.wires ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x4 false = false) →
      ∃ x13 : Fin 10 → Bool, pet x13 = true ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x3 false = false ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x4 false = false := by
    intro g' heq hgoal
    have hw : ∀ x : Fin 10 → Bool,
        ({ gates := [g'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x) =
        ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x) := by
      intro x
      rw [hsingle_wires g' x, hsingle_wires x1 x, heq x]
    have hres := hgoal
      (by obtain ⟨z, hz1, hz2⟩ := h34; exact ⟨z, by rw [hw z]; exact hz1, by rw [hw z]; exact hz2⟩)
      (by obtain ⟨z, hz1, hz2⟩ := h43; exact ⟨z, by rw [hw z]; exact hz1, by rw [hw z]; exact hz2⟩)
      (by intro z hz; rw [hw z]; exact hbelow z hz)
    obtain ⟨z, hz0, hz1, hz2⟩ := hres
    exact ⟨z, hz0, by rw [← hw z]; exact hz1, by rw [← hw z]; exact hz2⟩
  -- Helper: wire replacement for wire 10 when x1 computes false or x_r
  have helim_const_or_var : ∀ (rep : ℕ),
      (∀ x : Fin 10 → Bool,
        x1.op.eval (x1.inputs.map fun i => (List.ofFn x).getD i false) =
        (List.ofFn x).getD rep false) →
      (rep < 10 ∨ 1000 ≤ rep) →
      ∃ x13 : Fin 10 → Bool, pet x13 = true ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x3 false = false ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x4 false = false := by
    intro rep hrep hrep_bound
    let rw10 : ℕ → ℕ := fun w => if w = 10 then rep else w
    let x2' : PEqualNP.CircuitLowerBounds.Circuit :=
      { gates := x2.gates.map fun g => { op := g.op, inputs := g.inputs.map rw10 }
        output := x2.output }
    let gcanon : PEqualNP.CircuitLowerBounds.Gate :=
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }
    have hfan2' : PEqualNP.MetaComplexity.FanInTwo x2' := by
      intro g hg
      simp only [x2', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have hf := hfan2 g0 hg0
      exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
    have hsz' : x2'.size ≤ 17 := by
      change (x2.gates.map _).length ≤ 17
      rw [List.length_map]
      exact hsz
    have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws1 ws2 : List Bool),
        ws1.length = ws2.length →
        11 ≤ ws1.length →
        ws1.length + gs.length < 1000 →
        (∀ i : ℕ, i ≠ 10 → ws1.getD i false = ws2.getD i false) →
        ws1.getD 10 false = ws2.getD rep false →
        (gs.foldl step ws1).length = ((gs.map fun g => { op := g.op, inputs := g.inputs.map rw10 }).foldl step ws2).length ∧
        ∀ i : ℕ, i ≠ 10 →
          (gs.foldl step ws1).getD i false =
          ((gs.map fun g => { op := g.op, inputs := g.inputs.map rw10 }).foldl step ws2).getD i false := by
      intro gs
      induction gs with
      | nil =>
        intro ws1 ws2 hlen _ _ hne _
        exact ⟨hlen, hne⟩
      | cons g gs ih =>
        intro ws1 ws2 hlen h11 hlt hne h10
        simp only [List.map_cons, List.foldl_cons]
        have hev : g.op.eval (g.inputs.map fun i => ws1.getD i false) =
            g.op.eval ((g.inputs.map rw10).map fun i => ws2.getD i false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          dsimp only [Function.comp_apply, rw10]
          by_cases hi : i = 10
          · subst hi; simp only [↓reduceIte]; exact h10
          · simp only [hi, ↓reduceIte]; exact hne i hi
        have hlen1 : (step ws1 g).length = (step ws2 { op := g.op, inputs := g.inputs.map rw10 }).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
        have h11' : 11 ≤ (step ws1 g).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        have hlt' : (step ws1 g).length + gs.length < 1000 := by
          simp only [step, List.length_append, List.length_cons, List.length_nil, List.length_cons] at hlt ⊢; omega
        have hne' : ∀ i : ℕ, i ≠ 10 →
            (step ws1 g).getD i false =
            (step ws2 { op := g.op, inputs := g.inputs.map rw10 }).getD i false := by
          intro i hi
          by_cases hil : i < ws1.length
          · have hil2 : i < ws2.length := by omega
            simp only [step, List.getD_eq_getElem?_getD,
              List.getElem?_append_left hil, List.getElem?_append_left hil2]
            have := hne i hi
            simpa only [List.getD_eq_getElem?_getD] using this
          · by_cases hieq : i = ws1.length
            · subst hieq
              have h1eq : (step ws1 g).getD ws1.length false =
                  g.op.eval (g.inputs.map fun k => ws1.getD k false) := by
                simp only [step, List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_right (le_refl _)]
                simp
              have h2eq : (step ws2 { op := g.op, inputs := g.inputs.map rw10 }).getD ws1.length false =
                  g.op.eval ((g.inputs.map rw10).map fun k => ws2.getD k false) := by
                simp only [step, List.getD_eq_getElem?_getD, hlen]
                rw [List.getElem?_append_right (le_refl _)]
                simp
              rw [h1eq, h2eq, hev]
            · have hge1 : (step ws1 g).length ≤ i := by
                simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
              have hge2 : (step ws2 { op := g.op, inputs := g.inputs.map rw10 }).length ≤ i := by
                omega
              simp only [List.getD_eq_getElem?_getD,
                List.getElem?_eq_none hge1, List.getElem?_eq_none hge2, Option.getD_none]
        have h10' : (step ws1 g).getD 10 false =
            (step ws2 { op := g.op, inputs := g.inputs.map rw10 }).getD rep false := by
          have h10lt : 10 < ws1.length := by omega
          have hl : (step ws1 g).getD 10 false = ws1.getD 10 false := by
            simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h10lt]
          rw [hl, h10]
          rcases hrep_bound with hrep10 | hrep1000
          · have hreplt : rep < ws2.length := by omega
            simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hreplt]
          · have hge_old : ws2.length ≤ rep := by omega
            have hge_new : (step ws2 { op := g.op, inputs := g.inputs.map rw10 }).length ≤ rep := by
              simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
            simp only [List.getD_eq_getElem?_getD,
              List.getElem?_eq_none hge_old, List.getElem?_eq_none hge_new, Option.getD_none]
        exact ih (step ws1 g) (step ws2 { op := g.op, inputs := g.inputs.map rw10 }) hlen1 h11' hlt' hne' h10'
    have hwire_eq : ∀ (x : Fin 10 → Bool) (w : ℕ),
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x))).getD w false =
        (x2'.wires ({ gates := [gcanon], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x))).getD (rw10 w) false := by
      intro x w
      let ws1 := ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
      let ws2 := ({ gates := [gcanon], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
      have hlen_ofFn : (List.ofFn x).length = 10 := List.length_ofFn
      have hlen1 : ws1.length = 11 := by
        show (List.ofFn x ++ [_]).length = 11
        rw [List.length_append, hlen_ofFn]; rfl
      have hlen2 : ws2.length = 11 := by
        show (List.ofFn x ++ [_]).length = 11
        rw [List.length_append, hlen_ofFn]; rfl
      have hne_init : ∀ i : ℕ, i ≠ 10 → ws1.getD i false = ws2.getD i false := by
        intro i hi
        by_cases h10 : i < 10
        · have hi1 : i < (List.ofFn x).length := by omega
          show (List.ofFn x ++ [_]).getD i false = (List.ofFn x ++ [_]).getD i false
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi1]
        · have hge1 : ws1.length ≤ i := by omega
          have hge2 : ws2.length ≤ i := by omega
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hge1, List.getElem?_eq_none hge2, Option.getD_none]
      have h10_init : ws1.getD 10 false = ws2.getD rep false := by
        have h1 : ws1.getD 10 false = x1.op.eval (x1.inputs.map fun i => (List.ofFn x).getD i false) := by
          show (List.ofFn x ++ [x1.op.eval (x1.inputs.map fun i => (List.ofFn x).getD i false)]).getD 10 false = _
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by rw [hlen_ofFn])]
          simp only [hlen_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [h1, hrep x]
        rcases hrep_bound with hrep10 | hrep1000
        · have hi : rep < (List.ofFn x).length := by omega
          show (List.ofFn x).getD rep false = (List.ofFn x ++ [_]).getD rep false
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · have hge0 : (List.ofFn x).length ≤ rep := by omega
          have hge2 : ws2.length ≤ rep := by omega
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hge0, List.getElem?_eq_none hge2, Option.getD_none]
      have hsz_lt : ws1.length + x2.gates.length < 1000 := by
        have : x2.gates.length ≤ 17 := hsz
        omega
      have hf := hfold x2.gates ws1 ws2 (by omega) (by omega) hsz_lt hne_init h10_init
      change (x2.gates.foldl step ws1).getD w false =
        ((x2.gates.map fun g => { op := g.op, inputs := g.inputs.map rw10 }).foldl step ws2).getD (rw10 w) false
      dsimp only [rw10]
      by_cases hw : w = 10
      · subst hw
        simp only [↓reduceIte]
        have h10lt : 10 < ws1.length := by omega
        rw [hstep_lt x2.gates ws1 10 h10lt, h10_init]
        rcases hrep_bound with hrep10 | hrep1000
        · have hreplt : rep < ws2.length := by omega
          exact (hstep_lt (x2.gates.map fun g => { op := g.op, inputs := g.inputs.map rw10 }) ws2 rep hreplt).symm
        · have hge0 : ws2.length ≤ rep := by omega
          have hge1 : ((x2.gates.map fun g => { op := g.op, inputs := g.inputs.map rw10 }).foldl step ws2).length ≤ rep := by
            rw [hstep_len, List.length_map]; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hge0, List.getElem?_eq_none hge1]
      · simp only [hw, ↓reduceIte]
        exact hf.2 w hw
    dsimp only [gcanon] at hwire_eq
    have hres := h2 x2' (rw10 x3) (rw10 x4) hfan2' hsz'
      (by dsimp only; obtain ⟨z, hz1, hz2⟩ := h34; exact ⟨z, by rw [← hwire_eq z x3]; exact hz1, by rw [← hwire_eq z x4]; exact hz2⟩)
      (by dsimp only; obtain ⟨z, hz1, hz2⟩ := h43; exact ⟨z, by rw [← hwire_eq z x3]; exact hz1, by rw [← hwire_eq z x4]; exact hz2⟩)
      (by dsimp only; intro z hz; rw [← hwire_eq z x3, ← hwire_eq z x4]; exact hbelow z hz)
    dsimp only at hres
    obtain ⟨z, hz0, hz1, hz2⟩ := hres
    exact ⟨z, hz0, by rw [hwire_eq z x3]; exact hz1, by rw [hwire_eq z x4]; exact hz2⟩
  -- Helper: eliminate x1 ≡ true
  have helim_true :
      (∀ x : Fin 10 → Bool,
        x1.op.eval (x1.inputs.map fun i => (List.ofFn x).getD i false) = true) →
      ∃ x13 : Fin 10 → Bool, pet x13 = true ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x3 false = false ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x4 false = false := by
    intro htrue
    have hzero_pet : pet (fun _ => false) = false := rfl
    have hzero_both := hbelow (fun _ => false) hzero_pet
    have hwire10_true : (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (fun _ : Fin 10 => false)))).getD 10 false = true := by
      let ws0 := ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn (fun _ : Fin 10 => false))
      have hlen0 : ws0.length = 11 := by
        show (List.ofFn (fun _ : Fin 10 => false) ++ [_]).length = 11
        rw [List.length_append, List.length_ofFn]; rfl
      change (x2.gates.foldl step ws0).getD 10 false = true
      rw [hstep_lt x2.gates ws0 10 (by omega)]
      show (List.ofFn (fun _ : Fin 10 => false) ++ [x1.op.eval (x1.inputs.map fun i => (List.ofFn (fun _ : Fin 10 => false)).getD i false)]).getD 10 false = true
      have hl : (List.ofFn (fun _ : Fin 10 => false)).length = 10 := List.length_ofFn
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]), hl, Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      exact htrue (fun _ => false)
    have hx3_ne10 : x3 ≠ 10 := by
      intro heq; subst heq; rw [hwire10_true] at hzero_both; cases hzero_both.1
    have hx4_ne10 : x4 ≠ 10 := by
      intro heq; subst heq; rw [hwire10_true] at hzero_both; cases hzero_both.2
    let elimGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
      PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
        { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := g.inputs.filter (fun w => decide (w ≠ 10)) }
        (if 10 ∈ g.inputs then { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } else g)
        (if g.inputs.head? = some 10 then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }
          else { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := g.inputs.take 1 })
        (fun _ => g)
        g
    let x2' : PEqualNP.CircuitLowerBounds.Circuit :=
      { gates := x2.gates.map elimGate, output := x2.output }
    let gcanon : PEqualNP.CircuitLowerBounds.Gate :=
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }
    have hfan2' : PEqualNP.MetaComplexity.FanInTwo x2' := by
      intro g hg
      simp only [x2', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      obtain ⟨hop, hlen⟩ := hfan2 g0 hg0
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hand | hor | hnot
      · have he : elimGate g0 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := g0.inputs.filter (fun w => decide (w ≠ 10)) } := by
          dsimp only [elimGate]; rw [hand]
        rw [he]
        refine ⟨by simp, ?_⟩
        exact le_trans (List.length_filter_le _ _) hlen
      · have he : elimGate g0 = (if 10 ∈ g0.inputs then
            { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } else g0) := by
          dsimp only [elimGate]; rw [hor]
        rw [he]
        split_ifs
        · exact ⟨by simp, by simp⟩
        · exact ⟨by simp [hor], hlen⟩
      · have he : elimGate g0 = (if g0.inputs.head? = some 10 then
            { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }
            else { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := g0.inputs.take 1 }) := by
          dsimp only [elimGate]; rw [hnot]
        rw [he]
        split_ifs
        · exact ⟨by simp, by simp⟩
        · refine ⟨by simp, ?_⟩
          simp only [List.length_take]
          omega
    have hsz' : x2'.size ≤ 17 := by
      change (x2.gates.map elimGate).length ≤ 17
      rw [List.length_map]
      exact hsz
    have hand_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
    have hor_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
    have hnot_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := fun _ => rfl
    have helim_eval : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (ws1 ws2 : List Bool),
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) →
        (∀ i : ℕ, i ≠ 10 → ws1.getD i false = ws2.getD i false) →
        ws1.getD 10 false = true →
        g.op.eval (g.inputs.map fun i => ws1.getD i false) =
        (elimGate g).op.eval ((elimGate g).inputs.map fun i => ws2.getD i false) := by
      intro g ws1 ws2 hop hne h10
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hand | hor | hnot
      · have he : elimGate g = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := g.inputs.filter (fun w => decide (w ≠ 10)) } := by
          dsimp only [elimGate]; rw [hand]
        rw [he, hand, hand_eval, hand_eval]
        induction g.inputs with
        | nil => rfl
        | cons a l ih =>
          simp only [List.map_cons, List.all_cons, List.filter_cons, id_eq]
          by_cases ha : a = 10
          · subst ha
            simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, h10, Bool.true_and, ih]
          · simp only [ne_eq, ha, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons, List.all_cons, id_eq, hne a ha, ih]
      · have he : elimGate g = (if 10 ∈ g.inputs then
            { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } else g) := by
          dsimp only [elimGate]; rw [hor]
        rw [he]
        by_cases hm : 10 ∈ g.inputs
        · simp only [hm, ↓reduceIte, hor, hor_eval, hand_eval, List.map_nil, List.all_nil]
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.mpr ⟨10, hm, h10⟩, rfl⟩
        · simp only [hm, ↓reduceIte]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hne a (fun h => hm (h ▸ ha))
      · have he : elimGate g = (if g.inputs.head? = some 10 then
            { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }
            else { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := g.inputs.take 1 }) := by
          dsimp only [elimGate]; rw [hnot]
        rw [he]
        cases hinp : g.inputs with
        | nil =>
          simp only [List.head?_nil, reduceCtorEq, ↓reduceIte, List.take_nil, hnot, hnot_eval, List.map_nil]
        | cons a l =>
          simp only [List.head?_cons, Option.some.injEq]
          by_cases ha : a = 10
          · subst ha
            simp only [↓reduceIte, hnot, hnot_eval, hor_eval, List.map_cons, List.headD_cons, h10,
              Bool.not_true, List.map_nil, List.any_nil]
          · simp only [ha, ↓reduceIte, List.take_succ_cons, List.take_zero, hnot, hnot_eval,
              List.map_cons, List.map_nil, List.headD_cons, hne a ha]
    have hfold_true : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws1 ws2 : List Bool),
        (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) →
        ws1.length = ws2.length →
        11 ≤ ws1.length →
        (∀ i : ℕ, i ≠ 10 → ws1.getD i false = ws2.getD i false) →
        ws1.getD 10 false = true →
        ∀ i : ℕ, i ≠ 10 →
          (gs.foldl step ws1).getD i false =
          ((gs.map elimGate).foldl step ws2).getD i false := by
      intro gs
      induction gs with
      | nil => intro ws1 ws2 _ _ _ hne _ i hi; exact hne i hi
      | cons g gs ih =>
        intro ws1 ws2 hgs hlen h11 hne h10
        simp only [List.map_cons, List.foldl_cons]
        have hg_op := hgs g List.mem_cons_self
        have hev := helim_eval g ws1 ws2 hg_op hne h10
        have hlen1 : (step ws1 g).length = (step ws2 (elimGate g)).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
        have h11' : 11 ≤ (step ws1 g).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        have hne' : ∀ i : ℕ, i ≠ 10 →
            (step ws1 g).getD i false = (step ws2 (elimGate g)).getD i false := by
          intro i hi
          by_cases hil : i < ws1.length
          · have hil2 : i < ws2.length := by omega
            simp only [step, List.getD_eq_getElem?_getD,
              List.getElem?_append_left hil, List.getElem?_append_left hil2]
            have := hne i hi
            simpa only [List.getD_eq_getElem?_getD] using this
          · by_cases hieq : i = ws1.length
            · subst hieq
              have h1eq : (step ws1 g).getD ws1.length false =
                  g.op.eval (g.inputs.map fun k => ws1.getD k false) := by
                simp only [step, List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_right (le_refl _)]
                simp
              have h2eq : (step ws2 (elimGate g)).getD ws1.length false =
                  (elimGate g).op.eval ((elimGate g).inputs.map fun k => ws2.getD k false) := by
                simp only [step, List.getD_eq_getElem?_getD, hlen]
                rw [List.getElem?_append_right (le_refl _)]
                simp
              rw [h1eq, h2eq, hev]
            · have hge1 : (step ws1 g).length ≤ i := by
                simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
              have hge2 : (step ws2 (elimGate g)).length ≤ i := by omega
              simp only [List.getD_eq_getElem?_getD,
                List.getElem?_eq_none hge1, List.getElem?_eq_none hge2, Option.getD_none]
        have h10' : (step ws1 g).getD 10 false = true := by
          have h10lt : 10 < ws1.length := by omega
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h10lt]
          simpa only [List.getD_eq_getElem?_getD] using h10
        exact ih (step ws1 g) (step ws2 (elimGate g))
          (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) hlen1 h11' hne' h10'
    have hwire_eq : ∀ (x : Fin 10 → Bool) (w : ℕ), w ≠ 10 →
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x))).getD w false =
        (x2'.wires ({ gates := [gcanon], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x))).getD w false := by
      intro x w hw
      let ws1 := ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
      let ws2 := ({ gates := [gcanon], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn x)
      have hlen_ofFn : (List.ofFn x).length = 10 := List.length_ofFn
      have hlen1 : ws1.length = 11 := by
        show (List.ofFn x ++ [_]).length = 11
        rw [List.length_append, hlen_ofFn]; rfl
      have hlen2 : ws2.length = 11 := by
        show (List.ofFn x ++ [_]).length = 11
        rw [List.length_append, hlen_ofFn]; rfl
      have hne_init : ∀ i : ℕ, i ≠ 10 → ws1.getD i false = ws2.getD i false := by
        intro i hi
        by_cases h10 : i < 10
        · have hi1 : i < (List.ofFn x).length := by omega
          show (List.ofFn x ++ [_]).getD i false = (List.ofFn x ++ [_]).getD i false
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi1]
        · have hge1 : ws1.length ≤ i := by omega
          have hge2 : ws2.length ≤ i := by omega
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hge1, List.getElem?_eq_none hge2, Option.getD_none]
      have h10_init : ws1.getD 10 false = true := by
        show (List.ofFn x ++ [x1.op.eval (x1.inputs.map fun i => (List.ofFn x).getD i false)]).getD 10 false = true
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen_ofFn]), hlen_ofFn,
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        exact htrue x
      exact hfold_true x2.gates ws1 ws2 (fun g hg => (hfan2 g hg).1) (by omega) (by omega) hne_init h10_init w hw
    dsimp only [gcanon] at hwire_eq
    have hres := h2 x2' x3 x4 hfan2' hsz'
      (by dsimp only; obtain ⟨z, hz1, hz2⟩ := h34; exact ⟨z, by rw [← hwire_eq z x3 hx3_ne10]; exact hz1, by rw [← hwire_eq z x4 hx4_ne10]; exact hz2⟩)
      (by dsimp only; obtain ⟨z, hz1, hz2⟩ := h43; exact ⟨z, by rw [← hwire_eq z x3 hx3_ne10]; exact hz1, by rw [← hwire_eq z x4 hx4_ne10]; exact hz2⟩)
      (by dsimp only; intro z hz; rw [← hwire_eq z x3 hx3_ne10, ← hwire_eq z x4 hx4_ne10]; exact hbelow z hz)
    dsimp only at hres
    obtain ⟨z, hz0, hz1, hz2⟩ := hres
    exact ⟨z, hz0, by rw [hwire_eq z x3 hx3_ne10]; exact hz1, by rw [hwire_eq z x4 hx4_ne10]; exact hz2⟩
  -- Petersen graph Kneser model KG(5,2) and S_5 automorphisms
  let pairOf : Fin 10 → Fin 5 × Fin 5 := fun v =>
    ([(0, 1), (2, 3), (4, 0), (1, 2), (3, 4), (2, 4), (1, 4), (1, 3), (0, 3), (0, 2)] :
      List (Fin 5 × Fin 5)).getD v.val (0, 1)
  let ofPair : Fin 5 → Fin 5 → Fin 10 := fun a b =>
    let lo := if a.val ≤ b.val then a.val else b.val
    let hi := if a.val ≤ b.val then b.val else a.val
    if lo = 0 ∧ hi = 1 then 0
    else if lo = 2 ∧ hi = 3 then 1
    else if lo = 0 ∧ hi = 4 then 2
    else if lo = 1 ∧ hi = 2 then 3
    else if lo = 3 ∧ hi = 4 then 4
    else if lo = 2 ∧ hi = 4 then 5
    else if lo = 1 ∧ hi = 4 then 6
    else if lo = 1 ∧ hi = 3 then 7
    else if lo = 0 ∧ hi = 3 then 8
    else 9
  let petAdj : Fin 10 → Fin 10 → Bool := fun a b =>
    decide ((pairOf a).1 ≠ (pairOf b).1 ∧ (pairOf a).1 ≠ (pairOf b).2 ∧
            (pairOf a).2 ≠ (pairOf b).1 ∧ (pairOf a).2 ≠ (pairOf b).2)
  have hpair_ne : ∀ v : Fin 10, (pairOf v).1 ≠ (pairOf v).2 := by decide
  have hof_pair : ∀ v : Fin 10, ofPair (pairOf v).1 (pairOf v).2 = v := by decide
  have hof_symm : ∀ a b : Fin 5, ofPair a b = ofPair b a := by decide
  have hpair_of : ∀ a b : Fin 5, a ≠ b →
      pairOf (ofPair a b) = (a, b) ∨ pairOf (ofPair a b) = (b, a) := by decide
  have hpetAdj_symm : ∀ a b : Fin 10, petAdj a b = petAdj b a := by decide
  have hpetAdj_explicit : ∀ a b : Fin 10, petAdj a b =
      (decide (a = 0 ∧ b = 1) || decide (b = 0 ∧ a = 1) ||
       decide (a = 1 ∧ b = 2) || decide (b = 1 ∧ a = 2) ||
       decide (a = 2 ∧ b = 3) || decide (b = 2 ∧ a = 3) ||
       decide (a = 3 ∧ b = 4) || decide (b = 3 ∧ a = 4) ||
       decide (a = 4 ∧ b = 0) || decide (b = 4 ∧ a = 0) ||
       decide (a = 0 ∧ b = 5) || decide (b = 0 ∧ a = 5) ||
       decide (a = 1 ∧ b = 6) || decide (b = 1 ∧ a = 6) ||
       decide (a = 2 ∧ b = 7) || decide (b = 2 ∧ a = 7) ||
       decide (a = 3 ∧ b = 8) || decide (b = 3 ∧ a = 8) ||
       decide (a = 4 ∧ b = 9) || decide (b = 4 ∧ a = 9) ||
       decide (a = 5 ∧ b = 7) || decide (b = 5 ∧ a = 7) ||
       decide (a = 7 ∧ b = 9) || decide (b = 7 ∧ a = 9) ||
       decide (a = 9 ∧ b = 6) || decide (b = 9 ∧ a = 6) ||
       decide (a = 6 ∧ b = 8) || decide (b = 6 ∧ a = 8) ||
       decide (a = 8 ∧ b = 5) || decide (b = 8 ∧ a = 5)) := by decide
  have hpet_iff : ∀ x : Fin 10 → Bool,
      pet x = true ↔ ∃ a b : Fin 10, petAdj a b = true ∧ x a = true ∧ x b = true := by
    intro x
    constructor
    · intro hx
      dsimp only [pet] at hx
      simp only [Bool.or_eq_true, Bool.and_eq_true, or_assoc] at hx
      rcases hx with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨0, 1, by decide, h1', h2'⟩
      · exact ⟨1, 2, by decide, h1', h2'⟩
      · exact ⟨2, 3, by decide, h1', h2'⟩
      · exact ⟨3, 4, by decide, h1', h2'⟩
      · exact ⟨4, 0, by decide, h1', h2'⟩
      · exact ⟨0, 5, by decide, h1', h2'⟩
      · exact ⟨1, 6, by decide, h1', h2'⟩
      · exact ⟨2, 7, by decide, h1', h2'⟩
      · exact ⟨3, 8, by decide, h1', h2'⟩
      · exact ⟨4, 9, by decide, h1', h2'⟩
      · exact ⟨5, 7, by decide, h1', h2'⟩
      · exact ⟨7, 9, by decide, h1', h2'⟩
      · exact ⟨9, 6, by decide, h1', h2'⟩
      · exact ⟨6, 8, by decide, h1', h2'⟩
      · exact ⟨8, 5, by decide, h1', h2'⟩
    · intro hex
      obtain ⟨a, b, hab, ha, hb⟩ := hex
      rw [hpetAdj_explicit a b] at hab
      dsimp only [pet]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] at hab ⊢
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [ha, hb]
  let act : Equiv.Perm (Fin 5) → Fin 10 → Fin 10 := fun p v =>
    ofPair (p (pairOf v).1) (p (pairOf v).2)
  have hact_inv : ∀ (p : Equiv.Perm (Fin 5)) (v : Fin 10), act p.symm (act p v) = v := by
    intro p v
    dsimp only [act]
    have hne : p (pairOf v).1 ≠ p (pairOf v).2 := fun h => hpair_ne v (p.injective h)
    rcases hpair_of (p (pairOf v).1) (p (pairOf v).2) hne with h | h
    · rw [h]; simp only [Equiv.symm_apply_apply]; exact hof_pair v
    · rw [h]; simp only [Equiv.symm_apply_apply]; rw [hof_symm]; exact hof_pair v
  have hact_inv' : ∀ (p : Equiv.Perm (Fin 5)) (v : Fin 10), act p (act p.symm v) = v := by
    intro p v
    simpa using hact_inv p.symm v
  have hact_adj : ∀ (p : Equiv.Perm (Fin 5)) (a b : Fin 10),
      petAdj (act p a) (act p b) = petAdj a b := by
    intro p a b
    dsimp only [petAdj, act]
    have hnea : p (pairOf a).1 ≠ p (pairOf a).2 := fun h => hpair_ne a (p.injective h)
    have hneb : p (pairOf b).1 ≠ p (pairOf b).2 := fun h => hpair_ne b (p.injective h)
    rcases hpair_of _ _ hnea with ha | ha <;> rcases hpair_of _ _ hneb with hb | hb <;>
    · rw [ha, hb]
      apply decide_eq_decide.mpr
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
      try tauto
  have hact_pet : ∀ (p : Equiv.Perm (Fin 5)) (x : Fin 10 → Bool),
      pet (fun v => x (act p v)) = pet x := by
    intro p x
    rw [Bool.eq_iff_iff, hpet_iff (fun v => x (act p v)), hpet_iff x]
    constructor
    · intro hex
      obtain ⟨a, b, hab, ha, hb⟩ := hex
      exact ⟨act p a, act p b, by rw [hact_adj]; exact hab, ha, hb⟩
    · intro hex
      obtain ⟨a, b, hab, ha, hb⟩ := hex
      refine ⟨act p.symm a, act p.symm b, ?_, ?_, ?_⟩
      · rw [hact_adj]; exact hab
      · rw [hact_inv']; exact ha
      · rw [hact_inv']; exact hb
  -- Generic circuit conjugation by an S_5 permutation p
  have hconj : ∀ (p : Equiv.Perm (Fin 5)) (g1 : PEqualNP.CircuitLowerBounds.Gate),
      (∀ x : Fin 10 → Bool,
        g1.op.eval (g1.inputs.map fun i => (List.ofFn x).getD i false) =
        x1.op.eval (x1.inputs.map fun i => (List.ofFn x).getD i false)) →
      let remap : ℕ → ℕ := fun w => if h : w < 10 then (act p ⟨w, h⟩).val else w
      let g1' : PEqualNP.CircuitLowerBounds.Gate := { op := g1.op, inputs := g1.inputs.map remap }
      let x2' : PEqualNP.CircuitLowerBounds.Circuit :=
        { gates := x2.gates.map fun g => { op := g.op, inputs := g.inputs.map remap }
          output := remap x2.output }
      (PEqualNP.MetaComplexity.FanInTwo x2' →
       x2'.size ≤ 17 →
       (∃ x10 : Fin 10 → Bool,
          (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD (remap x3) false = true ∧
          (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD (remap x4) false = false) →
       (∃ x11 : Fin 10 → Bool,
          (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD (remap x3) false = false ∧
          (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD (remap x4) false = true) →
       (∀ x12 : Fin 10 → Bool, pet x12 = false →
          (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x12))).getD (remap x3) false = false ∧
          (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x12))).getD (remap x4) false = false) →
       ∃ x13 : Fin 10 → Bool, pet x13 = true ∧
          (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD (remap x3) false = false ∧
          (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD (remap x4) false = false) →
      ∃ x13 : Fin 10 → Bool, pet x13 = true ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x3 false = false ∧
        (x2.wires ({ gates := [x1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x13))).getD x4 false = false := by
    intro p g1 hg1 remap g1' x2' hgoal
    apply hreplace_g1 g1 hg1
    intro h34' h43' hbelow'
    have hfan2' : PEqualNP.MetaComplexity.FanInTwo x2' := by
      intro g hg
      simp only [x2', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have hf := hfan2 g0 hg0
      exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
    have hsz' : x2'.size ≤ 17 := by
      change (x2.gates.map _).length ≤ 17
      rw [List.length_map]
      exact hsz
    have hfold_remap : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws1 ws2 : List Bool),
        ws1.length = ws2.length →
        10 ≤ ws1.length →
        (∀ w : ℕ, ws2.getD (remap w) false = ws1.getD w false) →
        ∀ w : ℕ,
          ((gs.map fun g => { op := g.op, inputs := g.inputs.map remap }).foldl step ws2).getD (remap w) false =
          (gs.foldl step ws1).getD w false := by
      intro gs
      induction gs with
      | nil => intro ws1 ws2 _ _ heq w; exact heq w
      | cons g gs ih =>
        intro ws1 ws2 hlen h10 heq
        simp only [List.map_cons, List.foldl_cons]
        have hev : g.op.eval ((g.inputs.map remap).map fun i => ws2.getD i false) =
            g.op.eval (g.inputs.map fun i => ws1.getD i false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact heq i
        have hlen1 : (step ws1 g).length = (step ws2 { op := g.op, inputs := g.inputs.map remap }).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
        have h10' : 10 ≤ (step ws1 g).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        have heq' : ∀ w : ℕ,
            (step ws2 { op := g.op, inputs := g.inputs.map remap }).getD (remap w) false =
            (step ws1 g).getD w false := by
          intro w
          by_cases hw10 : w < 10
          · have hrw : remap w < 10 := by
              dsimp only [remap]; simp only [hw10, ↓reduceDIte]; exact (act p ⟨w, hw10⟩).isLt
            have hlt1 : w < ws1.length := by omega
            have hlt2 : remap w < ws2.length := by omega
            simp only [step, List.getD_eq_getElem?_getD,
              List.getElem?_append_left hlt1, List.getElem?_append_left hlt2]
            have := heq w
            simpa only [List.getD_eq_getElem?_getD] using this
          · have hrw : remap w = w := by dsimp only [remap]; simp only [hw10, ↓reduceDIte]
            rw [hrw]
            by_cases hwl : w < ws1.length
            · have hwl2 : w < ws2.length := by omega
              simp only [step, List.getD_eq_getElem?_getD,
                List.getElem?_append_left hwl, List.getElem?_append_left hwl2]
              have := heq w
              rw [hrw] at this
              simpa only [List.getD_eq_getElem?_getD] using this
            · by_cases hweq : w = ws1.length
              · subst hweq
                have h1eq : (step ws1 g).getD ws1.length false =
                    g.op.eval (g.inputs.map fun k => ws1.getD k false) := by
                  simp only [step, List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (le_refl _)]
                  simp
                have h2eq : (step ws2 { op := g.op, inputs := g.inputs.map remap }).getD ws1.length false =
                    g.op.eval ((g.inputs.map remap).map fun k => ws2.getD k false) := by
                  simp only [step, List.getD_eq_getElem?_getD, hlen]
                  rw [List.getElem?_append_right (le_refl _)]
                  simp
                rw [h1eq, h2eq, hev]
              · have hge1 : (step ws1 g).length ≤ w := by
                  simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
                have hge2 : (step ws2 { op := g.op, inputs := g.inputs.map remap }).length ≤ w := by omega
                simp only [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none hge1, List.getElem?_eq_none hge2, Option.getD_none]
        exact ih (step ws1 g) (step ws2 { op := g.op, inputs := g.inputs.map remap }) hlen1 h10' heq'
    have hwire_conj : ∀ (y : Fin 10 → Bool) (w : ℕ),
        (x2'.wires ({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn y))).getD (remap w) false =
        (x2.wires ({ gates := [g1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (fun v => y (act p v))))).getD w false := by
      intro y w
      have hinit : ∀ i : ℕ, (List.ofFn y).getD (remap i) false = (List.ofFn (fun v => y (act p v))).getD i false := by
        intro i
        dsimp only [remap]
        by_cases hi : i < 10
        · simp only [hi, ↓reduceDIte]
          have hlt1 : (act p ⟨i, hi⟩).val < (List.ofFn y).length := by rw [List.length_ofFn]; exact (act p ⟨i, hi⟩).isLt
          have hlt2 : i < (List.ofFn (fun v => y (act p v))).length := by rw [List.length_ofFn]; exact hi
          rw [List.getD_eq_getElem _ _ hlt1, List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn, List.getElem_ofFn]
        · simp only [hi, ↓reduceDIte]
          have hge1 : (List.ofFn y).length ≤ i := by rw [List.length_ofFn]; omega
          have hge2 : (List.ofFn (fun v => y (act p v))).length ≤ i := by rw [List.length_ofFn]; omega
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hge1, List.getElem?_eq_none hge2, Option.getD_none]
      have hstep1 := hfold_remap [g1] (List.ofFn (fun v => y (act p v))) (List.ofFn y)
        (by rw [List.length_ofFn, List.length_ofFn]) (by rw [List.length_ofFn]) hinit
      have hlen1 : (({ gates := [g1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn (fun v => y (act p v)))).length = 11 := by
        show (List.ofFn (fun v => y (act p v)) ++ [_]).length = 11
        rw [List.length_append, List.length_ofFn]; rfl
      have hlen2 : (({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn y)).length = 11 := by
        show (List.ofFn y ++ [_]).length = 11
        rw [List.length_append, List.length_ofFn]; rfl
      exact hfold_remap x2.gates
        (({ gates := [g1], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn (fun v => y (act p v))))
        (({ gates := [g1'], output := 0 : PEqualNP.CircuitLowerBounds.Circuit }).wires (List.ofFn y))
        (by omega) (by omega) hstep1 w
    have hres := hgoal hfan2' hsz'
      (by
        obtain ⟨z, hz1, hz2⟩ := h34'
        refine ⟨fun v => z (act p.symm v), ?_, ?_⟩
        · rw [hwire_conj]; simp only [hact_inv]; exact hz1
        · rw [hwire_conj]; simp only [hact_inv]; exact hz2)
      (by
        obtain ⟨z, hz1, hz2⟩ := h43'
        refine ⟨fun v => z (act p.symm v), ?_, ?_⟩
        · rw [hwire_conj]; simp only [hact_inv]; exact hz1
        · rw [hwire_conj]; simp only [hact_inv]; exact hz2)
      (by
        intro y hy
        rw [hwire_conj y x3, hwire_conj y x4]
        exact hbelow' (fun v => y (act p v)) (by rw [hact_pet]; exact hy))
    obtain ⟨y, hy0, hy1, hy2⟩ := hres
    refine ⟨fun v => y (act p v), ?_, ?_, ?_⟩
    · rw [hact_pet]; exact hy0
    · rw [← hwire_conj y x3]; exact hy1
    · rw [← hwire_conj y x4]; exact hy2
  -- S_5 transitivity helpers via Equiv.swap
  have hperm_pair : ∀ a b : Fin 5, a ≠ b → ∃ p : Equiv.Perm (Fin 5), p a = 0 ∧ p b = 1 := by
    intro a b hab
    let p1 : Equiv.Perm (Fin 5) := Equiv.swap a 0
    have hp1a : p1 a = 0 := Equiv.swap_apply_left a 0
    have hp1b_ne : p1 b ≠ 0 := by intro h; exact hab (p1.injective (h.trans hp1a.symm)).symm
    let p2 : Equiv.Perm (Fin 5) := Equiv.swap (p1 b) 1 * p1
    refine ⟨p2, ?_, ?_⟩
    · dsimp only [p2]; rw [Equiv.Perm.mul_apply, hp1a]
      exact Equiv.swap_apply_of_ne_of_ne hp1b_ne.symm (by decide)
    · dsimp only [p2]; rw [Equiv.Perm.mul_apply]
      exact Equiv.swap_apply_left (p1 b) 1
  have hperm_triple : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      ∃ p : Equiv.Perm (Fin 5), p a = 0 ∧ p b = 1 ∧ p c = 4 := by
    intro a b c hab hac hbc
    obtain ⟨p2, hp2a, hp2b⟩ := hperm_pair a b hab
    have hc0 : p2 c ≠ 0 := fun h => hac (p2.injective (hp2a.trans h.symm))
    have hc1 : p2 c ≠ 1 := fun h => hbc (p2.injective (hp2b.trans h.symm))
    let p3 : Equiv.Perm (Fin 5) := Equiv.swap (p2 c) 4 * p2
    refine ⟨p3, ?_, ?_, ?_⟩
    · dsimp only [p3]; rw [Equiv.Perm.mul_apply, hp2a]
      exact Equiv.swap_apply_of_ne_of_ne hc0.symm (by decide)
    · dsimp only [p3]; rw [Equiv.Perm.mul_apply, hp2b]
      exact Equiv.swap_apply_of_ne_of_ne hc1.symm (by decide)
    · dsimp only [p3]; rw [Equiv.Perm.mul_apply]
      exact Equiv.swap_apply_left (p2 c) 4
  have hperm_quad : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ p : Equiv.Perm (Fin 5), p a = 0 ∧ p b = 1 ∧ p c = 2 ∧ p d = 3 := by
    intro a b c d hab hac had hbc hbd hcd
    obtain ⟨p2, hp2a, hp2b⟩ := hperm_pair a b hab
    have hc0 : p2 c ≠ 0 := fun h => hac (p2.injective (hp2a.trans h.symm))
    have hc1 : p2 c ≠ 1 := fun h => hbc (p2.injective (hp2b.trans h.symm))
    let p3 : Equiv.Perm (Fin 5) := Equiv.swap (p2 c) 2 * p2
    have hp3a : p3 a = 0 := by
      dsimp only [p3]; rw [Equiv.Perm.mul_apply, hp2a]
      exact Equiv.swap_apply_of_ne_of_ne hc0.symm (by decide)
    have hp3b : p3 b = 1 := by
      dsimp only [p3]; rw [Equiv.Perm.mul_apply, hp2b]
      exact Equiv.swap_apply_of_ne_of_ne hc1.symm (by decide)
    have hp3c : p3 c = 2 := by
      dsimp only [p3]; rw [Equiv.Perm.mul_apply]
      exact Equiv.swap_apply_left (p2 c) 2
    have hd0 : p3 d ≠ 0 := fun h => had (p3.injective (hp3a.trans h.symm))
    have hd1 : p3 d ≠ 1 := fun h => hbd (p3.injective (hp3b.trans h.symm))
    have hd2 : p3 d ≠ 2 := fun h => hcd (p3.injective (hp3c.trans h.symm))
    let p4 : Equiv.Perm (Fin 5) := Equiv.swap (p3 d) 3 * p3
    refine ⟨p4, ?_, ?_, ?_, ?_⟩
    · dsimp only [p4]; rw [Equiv.Perm.mul_apply, hp3a]
      exact Equiv.swap_apply_of_ne_of_ne hd0.symm (by decide)
    · dsimp only [p4]; rw [Equiv.Perm.mul_apply, hp3b]
      exact Equiv.swap_apply_of_ne_of_ne hd1.symm (by decide)
    · dsimp only [p4]; rw [Equiv.Perm.mul_apply, hp3c]
      exact Equiv.swap_apply_of_ne_of_ne hd2.symm (by decide)
    · dsimp only [p4]; rw [Equiv.Perm.mul_apply]
      exact Equiv.swap_apply_left (p3 d) 3
  have hex_vertex : ∀ u : Fin 10, ∃ p : Equiv.Perm (Fin 5), act p u = 0 := by
    intro u
    obtain ⟨p, h1', h2'⟩ := hperm_pair (pairOf u).1 (pairOf u).2 (hpair_ne u)
    exact ⟨p, by dsimp only [act]; rw [h1', h2']; rfl⟩
  have hex_edge : ∀ u v : Fin 10, petAdj u v = true →
      ∃ p : Equiv.Perm (Fin 5), act p u = 0 ∧ act p v = 1 := by
    intro u v huv
    dsimp only [petAdj] at huv
    simp only [decide_eq_true_eq] at huv
    obtain ⟨h1', h2', h3', h4'⟩ := huv
    obtain ⟨p, hpa, hpb, hpc, hpd⟩ := hperm_quad (pairOf u).1 (pairOf u).2 (pairOf v).1 (pairOf v).2
      (hpair_ne u) h1' h2' h3' h4' (hpair_ne v)
    exact ⟨p, by dsimp only [act]; rw [hpa, hpb]; rfl, by dsimp only [act]; rw [hpc, hpd]; rfl⟩
  have hex_nonedge : ∀ u v : Fin 10, u ≠ v → petAdj u v = false →
      ∃ p : Equiv.Perm (Fin 5), act p u = 0 ∧ act p v = 2 := by
    intro u v huv hne
    dsimp only [petAdj] at hne
    simp only [decide_eq_false_iff_not, not_and_or, Classical.not_not] at hne
    have hneq_u := hpair_ne u
    have hneq_v := hpair_ne v
    rcases hne with h11 | h12 | h21 | h22
    · have h22ne : (pairOf u).2 ≠ (pairOf v).2 := by
        intro h
        have : u = v := by rw [← hof_pair u, ← hof_pair v, h11, h]
        exact huv this
      obtain ⟨p, hp0, hp1, hp4⟩ := hperm_triple (pairOf u).1 (pairOf u).2 (pairOf v).2
        hneq_u (by rw [h11]; exact hneq_v) h22ne
      exact ⟨p, by dsimp only [act]; rw [hp0, hp1]; rfl, by dsimp only [act]; rw [← h11, hp0, hp4]; rfl⟩
    · have h21ne : (pairOf u).2 ≠ (pairOf v).1 := by
        intro h
        have : u = v := by rw [← hof_pair u, ← hof_pair v, h12, h, hof_symm]
        exact huv this
      obtain ⟨p, hp0, hp1, hp4⟩ := hperm_triple (pairOf u).1 (pairOf u).2 (pairOf v).1
        hneq_u (by rw [h12]; exact hneq_v.symm) h21ne
      exact ⟨p, by dsimp only [act]; rw [hp0, hp1]; rfl, by dsimp only [act]; rw [← h12, hp0, hp4]; rfl⟩
    · have h12ne : (pairOf u).1 ≠ (pairOf v).2 := by
        intro h
        have : u = v := by rw [← hof_pair u, ← hof_pair v, h21, h, hof_symm]
        exact huv this
      obtain ⟨p, hp0, hp1, hp4⟩ := hperm_triple (pairOf u).2 (pairOf u).1 (pairOf v).2
        hneq_u.symm (by rw [h21]; exact hneq_v) h12ne
      exact ⟨p, by dsimp only [act]; rw [hp0, hp1]; rfl, by dsimp only [act]; rw [← h21, hp0, hp4]; rfl⟩
    · have h11ne : (pairOf u).1 ≠ (pairOf v).1 := by
        intro h
        have : u = v := by rw [← hof_pair u, ← hof_pair v, h22, h]
        exact huv this
      obtain ⟨p, hp0, hp1, hp4⟩ := hperm_triple (pairOf u).2 (pairOf u).1 (pairOf v).1
        hneq_u.symm (by rw [h22]; exact hneq_v.symm) h11ne
      exact ⟨p, by dsimp only [act]; rw [hp0, hp1]; rfl, by dsimp only [act]; rw [← h22, hp0, hp4]; rfl⟩
  -- Small GateOp.eval helpers
  have hand_ev : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have hor_ev : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
  have hnot_ev : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have hgetD_ge10 : ∀ (x : Fin 10 → Bool) (w : ℕ), 10 ≤ w → (List.ofFn x).getD w false = false := by
    intro x w hw
    have hge : (List.ofFn x).length ≤ w := by rw [List.length_ofFn]; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
  -- Now classify x1 completely!
  have h1info := hfan1 x1 List.mem_cons_self
  obtain ⟨hop1, hlen1⟩ := h1info
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop1
  cases hinp1 : x1.inputs with
  | nil =>
    rcases hop1 with h_and | h_or | h_not
    · exact helim_true (fun x => by rw [h_and, hinp1, hand_ev]; rfl)
    · exact helim_const_or_var 1000 (fun x => by rw [h_or, hinp1, hor_ev, hgetD_ge10 x 1000 (by omega)]; rfl) (Or.inr (le_refl _))
    · exact helim_true (fun x => by rw [h_not, hinp1, hnot_ev]; rfl)
  | cons a rest =>
    cases rest with
    | nil =>
      by_cases ha : a < 10
      · rcases hop1 with h_and | h_or | h_not
        · exact helim_const_or_var a (fun x => by rw [h_and, hinp1, hand_ev]; simp) (Or.inl ha)
        · exact helim_const_or_var a (fun x => by rw [h_or, hinp1, hor_ev]; simp) (Or.inl ha)
        · obtain ⟨p, hp0⟩ := hex_vertex ⟨a, ha⟩
          apply hconj p { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [a] }
            (fun x => by rw [h_not, hinp1])
          intro hfan2' hsz' h1' h2' h3'
          have hmap : ([a].map fun w => if h : w < 10 then (act p ⟨w, h⟩).val else w) = [0] := by
            simp only [List.map_cons, List.map_nil, ha, ↓reduceDIte, hp0, Fin.val_zero]
          rw [hmap] at h1' h2' h3' ⊢
          exact h1 _ _ _ hfan2' hsz' h1' h2' h3'
      · have ha10 : 10 ≤ a := Nat.le_of_not_lt ha
        rcases hop1 with h_and | h_or | h_not
        · exact helim_const_or_var 1000 (fun x => by rw [h_and, hinp1, hand_ev]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hgetD_ge10 x a ha10, hgetD_ge10 x 1000 (by omega), Bool.false_and]) (Or.inr (le_refl _))
        · exact helim_const_or_var 1000 (fun x => by rw [h_or, hinp1, hor_ev]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hgetD_ge10 x a ha10, hgetD_ge10 x 1000 (by omega), Bool.false_or]) (Or.inr (le_refl _))
        · exact helim_true (fun x => by rw [h_not, hinp1, hnot_ev]; simp only [List.map_cons, List.map_nil, List.headD_cons, hgetD_ge10 x a ha10, Bool.not_false])
    | cons b rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hinp1] at hlen1
        simp only [List.length_cons] at hlen1
        omega
      | nil =>
        rcases hop1 with h_and | h_or | h_not
        · by_cases ha : a < 10
          · by_cases hb : b < 10
            · by_cases hab : a = b
              · subst hab
                exact helim_const_or_var a (fun x => by rw [h_and, hinp1, hand_ev]; simp) (Or.inl ha)
              · have hne_fin : (⟨a, ha⟩ : Fin 10) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
                cases hadj : petAdj ⟨a, ha⟩ ⟨b, hb⟩
                · obtain ⟨p, hp0, hp2⟩ := hex_nonedge ⟨a, ha⟩ ⟨b, hb⟩ hne_fin hadj
                  apply hconj p { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a, b] }
                    (fun x => by rw [h_and, hinp1])
                  intro hfan2' hsz' h1' h2' h3'
                  have hmap : ([a, b].map fun w => if h : w < 10 then (act p ⟨w, h⟩).val else w) = [0, 2] := by
                    simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceDIte, hp0, hp2]; rfl
                  rw [hmap] at h1' h2' h3' ⊢
                  exact h3 _ _ _ hfan2' hsz' h1' h2' h3'
                · obtain ⟨p, hp0, hp1⟩ := hex_edge ⟨a, ha⟩ ⟨b, hb⟩ hadj
                  apply hconj p { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a, b] }
                    (fun x => by rw [h_and, hinp1])
                  intro hfan2' hsz' h1' h2' h3'
                  have hmap : ([a, b].map fun w => if h : w < 10 then (act p ⟨w, h⟩).val else w) = [0, 1] := by
                    simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceDIte, hp0, hp1]; rfl
                  rw [hmap] at h1' h2' h3' ⊢
                  exact h2 _ _ _ hfan2' hsz' h1' h2' h3'
            · have hb10 : 10 ≤ b := Nat.le_of_not_lt hb
              exact helim_const_or_var 1000 (fun x => by rw [h_and, hinp1, hand_ev]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hgetD_ge10 x b hb10, hgetD_ge10 x 1000 (by omega), Bool.and_false, Bool.false_and]) (Or.inr (le_refl _))
          · have ha10 : 10 ≤ a := Nat.le_of_not_lt ha
            exact helim_const_or_var 1000 (fun x => by rw [h_and, hinp1, hand_ev]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hgetD_ge10 x a ha10, hgetD_ge10 x 1000 (by omega), Bool.false_and]) (Or.inr (le_refl _))
        · by_cases ha : a < 10
          · by_cases hb : b < 10
            · by_cases hab : a = b
              · subst hab
                exact helim_const_or_var a (fun x => by rw [h_or, hinp1, hor_ev]; simp) (Or.inl ha)
              · have hne_fin : (⟨a, ha⟩ : Fin 10) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
                cases hadj : petAdj ⟨a, ha⟩ ⟨b, hb⟩
                · obtain ⟨p, hp0, hp2⟩ := hex_nonedge ⟨a, ha⟩ ⟨b, hb⟩ hne_fin hadj
                  apply hconj p { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] }
                    (fun x => by rw [h_or, hinp1])
                  intro hfan2' hsz' h1' h2' h3'
                  have hmap : ([a, b].map fun w => if h : w < 10 then (act p ⟨w, h⟩).val else w) = [0, 2] := by
                    simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceDIte, hp0, hp2]; rfl
                  rw [hmap] at h1' h2' h3' ⊢
                  exact h4 2 _ _ _ (Or.inr rfl) hfan2' hsz' h1' h2' h3'
                · obtain ⟨p, hp0, hp1⟩ := hex_edge ⟨a, ha⟩ ⟨b, hb⟩ hadj
                  apply hconj p { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] }
                    (fun x => by rw [h_or, hinp1])
                  intro hfan2' hsz' h1' h2' h3'
                  have hmap : ([a, b].map fun w => if h : w < 10 then (act p ⟨w, h⟩).val else w) = [0, 1] := by
                    simp only [List.map_cons, List.map_nil, ha, hb, ↓reduceDIte, hp0, hp1]; rfl
                  rw [hmap] at h1' h2' h3' ⊢
                  exact h4 1 _ _ _ (Or.inl rfl) hfan2' hsz' h1' h2' h3'
            · have hb10 : 10 ≤ b := Nat.le_of_not_lt hb
              exact helim_const_or_var a (fun x => by rw [h_or, hinp1, hor_ev]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hgetD_ge10 x b hb10, Bool.or_false]) (Or.inl ha)
          · have ha10 : 10 ≤ a := Nat.le_of_not_lt ha
            by_cases hb : b < 10
            · exact helim_const_or_var b (fun x => by rw [h_or, hinp1, hor_ev]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hgetD_ge10 x a ha10, Bool.false_or, Bool.or_false]) (Or.inl hb)
            · have hb10 : 10 ≤ b := Nat.le_of_not_lt hb
              exact helim_const_or_var 1000 (fun x => by rw [h_or, hinp1, hor_ev]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hgetD_ge10 x a ha10, hgetD_ge10 x b hb10, hgetD_ge10 x 1000 (by omega), Bool.false_or]) (Or.inr (le_refl _))
        · by_cases ha : a < 10
          · obtain ⟨p, hp0⟩ := hex_vertex ⟨a, ha⟩
            apply hconj p { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [a] }
              (fun x => by rw [h_not, hinp1, hnot_ev, hnot_ev]; rfl)
            intro hfan2' hsz' h1' h2' h3'
            have hmap : ([a].map fun w => if h : w < 10 then (act p ⟨w, h⟩).val else w) = [0] := by
              simp only [List.map_cons, List.map_nil, ha, ↓reduceDIte, hp0, Fin.val_zero]
            rw [hmap] at h1' h2' h3' ⊢
            exact h1 _ _ _ hfan2' hsz' h1' h2' h3'
          · have ha10 : 10 ≤ a := Nat.le_of_not_lt ha
            exact helim_true (fun x => by rw [h_not, hinp1, hnot_ev]; simp only [List.map_cons, List.map_nil, List.headD_cons, hgetD_ge10 x a ha10, Bool.not_false])
