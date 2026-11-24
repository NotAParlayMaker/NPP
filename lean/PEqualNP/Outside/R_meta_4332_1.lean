import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4332_1
    (andCase :
      let F := fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ) (b : Bool),
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
        10 ≤ i → i < j → j < 10 + D.size →
        ∃ x : Fin 10 → Bool, x 9 = false ∧
          let w := D.wires (List.ofFn x)
          let y := w.getD i false && w.getD j false
          (if b = true then !y else y) ≠ F x)
    (orCase :
      let F := fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ) (b : Bool),
        PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
        10 ≤ i → i < j → j < 10 + D.size →
        ∃ x : Fin 10 → Bool, x 9 = false ∧
          let w := D.wires (List.ofFn x)
          let y := w.getD i false || w.getD j false
          (if b = true then !y else y) ≠ F x) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8 := by
  let target := fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let signed (b y : Bool) := if b = true then !y else y
  let wire (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (x : Fin 10 → Bool) :=
    (C.wires (List.ofFn x)).getD u false
  let before (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) :
      PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.take j, 0⟩
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) := gs.foldl step w
  have runCons (g : PEqualNP.CircuitLowerBounds.Gate) (gs) (w) :
      run (g :: gs) w = run gs (step w g) := rfl
  have runAppend (gs hs) (w) : run (gs ++ hs) w = run hs (run gs w) := by
    simp only [run, List.foldl_append]
  have runLength : ∀ gs w, (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons g gs ih =>
        intro w
        rw [runCons, ih]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
  have runInput : ∀ gs w u, u < w.length → (run gs w).getD u false = w.getD u false := by
    intro gs
    induction gs with
    | nil => intro w u hu; rfl
    | cons g gs ih =>
        intro w u hu
        rw [runCons, ih _ _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hu
  have inputWire (C : PEqualNP.CircuitLowerBounds.Circuit) (i : Fin 10) (x : Fin 10 → Bool) :
      wire C i.val x = x i := by
    change (run C.gates (List.ofFn x)).getD i.val false = x i
    have hu : i.val < (List.ofFn x).length := by simp
    rw [runInput _ _ _ hu, List.getD_eq_getElem _ _ hu, List.getElem_ofFn]
  have runGate (gs) (w) (j : ℕ) (hj : j < gs.length) :
      (run gs w).getD (w.length + j) false =
        gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) w).getD i false) := by
    have hrun : run gs w = run (gs.drop (j + 1)) (step (run (gs.take j) w) gs[j]) := by
      conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
      rw [runAppend, runCons]
    have hlen : (run (gs.take j) w).length = w.length + j := by
      rw [runLength, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hstep : w.length + j < (step (run (gs.take j) w) gs[j]).length := by
      simp [step, hlen]
    rw [hrun, runInput _ _ _ hstep]
    simp only [step]
    rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
    rfl
  have shapes (ins : List ℕ) (bound : ins.length ≤ 2) :
      ins = [] ∨ (∃ a, ins = [a]) ∨ ∃ a d, ins = [a, d] := by
    cases ins with
    | nil => exact Or.inl rfl
    | cons a rest =>
        cases rest with
        | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
        | cons d rest =>
            cases rest with
            | nil => exact Or.inr (Or.inr ⟨a, d, rfl⟩)
            | cons e tail => simp at bound
  let zero : Fin 10 → Bool := fun _ => false
  let edge01 : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)
  let edge23 : Fin 10 → Bool := fun i => decide (i = 2 ∨ i = 3)
  let one (i j : Fin 10) := decide (i = j)
  let allActive (i : Fin 10) := decide (i ≠ 9)
  have oneTarget : ∀ i, target (one i) = false := by decide
  have allTarget : target allActive = true := by decide
  have edgeAway (i : Fin 10) :
      ∃ x : Fin 10 → Bool, x 9 = false ∧ x i = false ∧ target x = true := by
    by_cases hi : i = 0 ∨ i = 1
    · have hi' : ¬ (i = 2 ∨ i = 3) := by rcases hi with rfl | rfl <;> decide
      exact ⟨edge23, by decide, decide_eq_false hi', by decide⟩
    · exact ⟨edge01, by decide, decide_eq_false hi, by decide⟩
  have falseWitness (b : Bool) :
      ∃ x : Fin 10 → Bool, x 9 = false ∧ signed b false ≠ target x := by
    cases b
    · exact ⟨edge01, by decide, by decide⟩
    · exact ⟨zero, rfl, by decide⟩
  have trueWitness (b : Bool) :
      ∃ x : Fin 10 → Bool, x 9 = false ∧ signed b true ≠ target x := by
    cases b
    · exact ⟨zero, rfl, by decide⟩
    · exact ⟨edge01, by decide, by decide⟩
  have inputWitness (i : Fin 10) (b : Bool) :
      ∃ x : Fin 10 → Bool, x 9 = false ∧ signed b (x i) ≠ target x := by
    cases b
    · obtain ⟨x, hx, hi, ht⟩ := edgeAway i
      exact ⟨x, hx, by simp [signed, hi, ht]⟩
    · exact ⟨zero, rfl, by decide⟩
  have flip (b y : Bool) : signed b (!y) = signed (!b) y := by cases b <;> cases y <;> rfl
  have mismatch (k : ℕ) :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (b : Bool),
        C.size = k → k ≤ 15 → PEqualNP.MetaComplexity.FanInTwo C →
        ∃ x : Fin 10 → Bool, x 9 = false ∧ signed b (wire C u x) ≠ target x := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro C u b hSize hBudget hFan
      have lift (v : (Fin 10 → Bool) → Bool)
          (sem : ∀ x, signed b (wire C u x) = v x)
          (fail : ∃ x, x 9 = false ∧ v x ≠ target x) :
          ∃ x, x 9 = false ∧ signed b (wire C u x) ≠ target x := by
        obtain ⟨x, hx, hm⟩ := fail
        exact ⟨x, hx, by rwa [sem x]⟩
      by_cases hInput : u < 10
      · let i : Fin 10 := ⟨u, hInput⟩
        exact lift (fun x => signed b (x i))
          (fun x => congrArg (signed b) (inputWire C i x)) (inputWitness i b)
      by_cases hMissing : 10 + C.size ≤ u
      · refine lift (fun _ => signed b false) (fun x => ?_) (falseWitness b)
        change signed b ((run C.gates (List.ofFn x)).getD u false) = _
        have hout : (run C.gates (List.ofFn x)).length ≤ u := by
          simpa [runLength, PEqualNP.CircuitLowerBounds.Circuit.size] using hMissing
        rw [List.getD_eq_default _ _ hout]
      let j := u - 10
      have hj : j < C.gates.length := by
        dsimp [j]
        exact (by unfold PEqualNP.CircuitLowerBounds.Circuit.size at hMissing; omega)
      let g := C.gates[j]
      let D := before C j
      have fanD : PEqualNP.MetaComplexity.FanInTwo D := by
        intro g' hg'
        exact hFan g' (List.mem_of_mem_take hg')
      have sizeD : D.size = j := by
        simp [D, before, PEqualNP.CircuitLowerBounds.Circuit.size, Nat.min_eq_left (Nat.le_of_lt hj)]
      have smaller : j < k := by
        rw [← hSize]
        exact hj
      have budgetD : D.size ≤ 14 := by omega
      have recur (i : ℕ) (q : Bool) :
          ∃ x : Fin 10 → Bool, x 9 = false ∧ signed q (wire D i x) ≠ target x :=
        ih j smaller D i q sizeD (by omega) fanD
      let live (i : ℕ) := i ≠ 9 ∧ i < 10 + D.size
      have deadWire (i : ℕ) (hi : ¬ live i) (x : Fin 10 → Bool) (hx : x 9 = false) :
          wire D i x = false := by
        by_cases h9 : i = 9
        · subst i
          exact (inputWire D 9 x).trans hx
        · have hl : 10 + D.size ≤ i := Nat.le_of_not_gt (fun h => hi ⟨h9, h⟩)
          have ho : (run D.gates (List.ofFn x)).length ≤ i := by
            simpa [runLength, PEqualNP.CircuitLowerBounds.Circuit.size] using hl
          exact List.getD_eq_default _ _ ho
      let combine (isAnd y z : Bool) := if isAnd then y && z else y || z
      have gateInput (i : Fin 10) (ni : i ≠ 9) (isAnd : Bool)
          (other : (Fin 10 → Bool) → Bool) :
          ∃ x : Fin 10 → Bool, x 9 = false ∧
            signed b (combine isAnd (x i) (other x)) ≠ target x := by
        cases isAnd <;> cases b
        · have hi : one i i = true := by simp [one]
          exact ⟨one i, by simp [one, ni], by simp [combine, hi, oneTarget, signed]⟩
        · have hi : allActive i = true := by simp [allActive, ni]
          exact ⟨allActive, by decide, by simp [combine, hi, allTarget, signed]⟩
        · obtain ⟨x, hx, hi, ht⟩ := edgeAway i
          exact ⟨x, hx, by simp [combine, signed, hi, ht]⟩
        · exact ⟨zero, rfl, by simp [combine, signed, zero, target]⟩
      have binary (a d : ℕ) (isAnd : Bool) :
          ∃ x : Fin 10 → Bool, x 9 = false ∧
            signed b (combine isAnd (wire D a x) (wire D d x)) ≠ target x := by
        let fails (i t : ℕ) := ∃ x : Fin 10 → Bool, x 9 = false ∧
          signed b (combine isAnd (wire D i x) (wire D t x)) ≠ target x
        have swap {i t : ℕ} (h : fails i t) : fails t i := by
          obtain ⟨x, hx, hm⟩ := h
          refine ⟨x, hx, ?_⟩
          cases isAnd <;> simpa [combine, Bool.and_comm, Bool.or_comm] using hm
        have zeroArg (i t : ℕ) (hi : ¬ live i) : fails i t := by
          cases isAnd
          · obtain ⟨x, hx, hm⟩ := recur t b
            exact ⟨x, hx, by simpa [combine, deadWire i hi x hx] using hm⟩
          · obtain ⟨x, hx, hm⟩ := falseWitness b
            exact ⟨x, hx, by simpa [combine, deadWire i hi x hx] using hm⟩
        have ordered (i t : ℕ) (hi : live i) (ht : live t) (ord : i < t) : fails i t := by
          by_cases hInput : i < 10
          · let k : Fin 10 := ⟨i, hInput⟩
            have hk : k ≠ 9 := fun h => hi.1 (congrArg Fin.val h)
            obtain ⟨x, hx, hm⟩ := gateInput k hk isAnd (wire D t)
            have hval : wire D i x = x k := inputWire D k x
            exact ⟨x, hx, by rwa [hval]⟩
          · have hGate : 10 ≤ i := by omega
            cases isAnd
            · exact orCase D i t b fanD budgetD hGate ord ht.2
            · exact andCase D i t b fanD budgetD hGate ord ht.2
        by_cases ha : live a
        · by_cases hd : live d
          · rcases lt_trichotomy a d with lt | eq | gt
            · exact ordered a d ha hd lt
            · subst d
              obtain ⟨x, hx, hm⟩ := recur a b
              refine ⟨x, hx, ?_⟩
              cases isAnd <;> simpa [combine] using hm
            · exact swap (ordered d a hd ha gt)
          · exact swap (zeroArg d a hd)
        · exact zeroArg a d ha
      have gateEval (x : Fin 10 → Bool) :
          wire C u x = g.op.eval (g.inputs.map fun i => wire D i x) := by
        have hu : u = 10 + j := by dsimp [j]; omega
        rw [hu]
        simpa only [wire, D, before, g, run, step, PEqualNP.CircuitLowerBounds.Circuit.wires,
          List.length_ofFn] using runGate C.gates (List.ofFn x) j hj
      have allowed := hFan g (by dsimp [g]; exact List.getElem_mem _)
      have op : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using allowed.1
      rcases op with op | op | op
      · rcases shapes g.inputs allowed.2 with noArgs | ⟨a, oneArg⟩ | ⟨a, d, twoArgs⟩
        · exact lift _ (fun x => by simp [gateEval x, op, noArgs, PEqualNP.CircuitLowerBounds.GateOp.eval])
            (trueWitness b)
        · exact lift _ (fun x => by simp [gateEval x, op, oneArg, PEqualNP.CircuitLowerBounds.GateOp.eval])
            (recur a b)
        · exact lift (fun x => signed b (wire D a x && wire D d x))
            (fun x => by simp [gateEval x, op, twoArgs, PEqualNP.CircuitLowerBounds.GateOp.eval])
            (by simpa [combine] using binary a d true)
      · rcases shapes g.inputs allowed.2 with noArgs | ⟨a, oneArg⟩ | ⟨a, d, twoArgs⟩
        · exact lift _ (fun x => by simp [gateEval x, op, noArgs, PEqualNP.CircuitLowerBounds.GateOp.eval])
            (falseWitness b)
        · exact lift _ (fun x => by simp [gateEval x, op, oneArg, PEqualNP.CircuitLowerBounds.GateOp.eval])
            (recur a b)
        · exact lift (fun x => signed b (wire D a x || wire D d x))
            (fun x => by simp [gateEval x, op, twoArgs, PEqualNP.CircuitLowerBounds.GateOp.eval])
            (by simpa [combine] using binary a d false)
      · cases args : g.inputs with
        | nil =>
            exact lift _ (fun x => by simp [gateEval x, op, args, PEqualNP.CircuitLowerBounds.GateOp.eval])
              (trueWitness b)
        | cons a rest =>
            exact lift _ (fun x => by simp [gateEval x, op, args, PEqualNP.CircuitLowerBounds.GateOp.eval, flip])
              (recur a (!b))
  intro full C u b fan budget
  dsimp only
  obtain ⟨x, hx, hm⟩ := mismatch C.size C u b rfl budget fan
  exact ⟨x, hx, by
    simpa only [full, target, signed, wire, hx, Bool.and_false, Bool.false_and,
      Bool.or_false, Bool.false_or] using hm⟩
