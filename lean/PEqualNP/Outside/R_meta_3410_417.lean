import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3410_417
    (ordinary : ∀ C : Circuit, FanInTwo C →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) → 15 ≤ C.size)
    (liveCase :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (pins : List (Fin 11)) (A B : Circuit), pins.length ≤ 2 →
        Monotone2 A → FanInTwo B → A.size + B.size = 12 → A.output ≤ 24 →
        B.output = 23 → 11 + A.size < B.output →
        (∀ g ∈ A.gates ++ B.gates, ∀ i ∈ g.inputs, i ≤ 24) →
        (∃ g ∈ B.gates, 11 + A.size ∈ g.inputs ∧
          (g.op ≠ GateOp.not ∨ g.inputs.head? = some (11 + A.size))) →
        ∃ x : Fin 9 → Bool,
          let w := List.ofFn x ++ [x 0 || x 4]
          let v := A.wires (w ++ [GateOp.or.eval (pins.map fun i => w.getD i.val false)])
          B.eval (v ++ [!(v.getD A.output false)]) ≠ f x) :
    ∀ (x1 : List (Fin (11 : ℕ))) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x2 →       PEqualNP.MetaComplexity.FanInTwo x3 →         x2.size + x3.size ≤ (12 : ℕ) →           x2.output ≤ (24 : ℕ) →             x3.output ≤ (24 : ℕ) →               (∀ x10 ∈ x2.gates ++ x3.gates, ∀ x12 ∈ x10.inputs, x12 ≤ (24 : ℕ)) →                 ∃ (x11 : Fin (9 : ℕ) → Bool),                   have x12 : List Bool := List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))];                   have x13 : List Bool := x2.wires (x12 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x13 : Fin (11 : ℕ)) => x12.getD (↑x13) Bool.false) x1)]);                   x3.eval (x13 ++ [!x13.getD x2.output Bool.false]) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by
  intro pins A B pinsSize mono fan budget tapBound outputBound addresses
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let start (x : Fin 9 → Bool) := base x ++ [GateOp.or.eval (pins.map fun i => (base x).getD i.val false)]
  let mid (x : Fin 9 → Bool) := A.wires (start x)
  let afterNot (x : Fin 9 → Bool) := mid x ++ [!((mid x).getD A.output false)]
  let cut := 11 + A.size
  let first : Gate := ⟨GateOp.or,[0,4]⟩
  let second : Gate := ⟨GateOp.or,pins.map Fin.val⟩
  let inv : Gate := ⟨GateOp.not,[A.output]⟩
  let prefixGates := first :: second :: A.gates
  let allowed (g : Gate) :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  have sameTarget (x : Fin 9 → Bool) : f x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5) := by
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  by_contra! wrong
  have correct (x : Fin 9 → Bool) : B.eval (afterNot x) = f x := by
    have same := wrong x
    change ¬(B.eval (afterNot x) ≠ _) at same
    exact (not_ne_iff.mp same).trans (sameTarget x).symm
  have lengthRun (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step, List.length_append, List.length_singleton]
        omega
  have lengthMid (x : Fin 9 → Bool) : (mid x).length = cut := by
    change (A.gates.foldl step (start x)).length = _
    rw [lengthRun]
    change (start x).length + A.gates.length = 11 + A.gates.length
    simp [start, base]
  have lengthAfter (x : Fin 9 → Bool) : (afterNot x).length = cut + 1 := by
    simp only [afterNot, List.length_append, List.length_singleton, lengthMid]
  have baseEval (x : Fin 9 → Bool) : prefixGates.foldl step (List.ofFn x) = mid x := by
    have firstEval : step (List.ofFn x) first = base x := by
      change List.ofFn x ++
        [((List.ofFn x).getD 0 false || ((List.ofFn x).getD 4 false || false))] = base x
      simp [base, List.getD_eq_getElem?_getD]
    change A.gates.foldl step (step (step (List.ofFn x) first) second) = _
    rw [firstEval]
    change A.gates.foldl step (base x ++ [GateOp.or.eval
      ((pins.map Fin.val).map fun i => (base x).getD i false)]) = A.gates.foldl step (start x)
    simp only [start, List.map_map, Function.comp_def]
  have notEval (x : Fin 9 → Bool) : step (mid x) inv = afterNot x := rfl
  have prefixSize : prefixGates.length = 2 + A.size := by
    change (first :: second :: A.gates).length = 2 + A.gates.length
    simp only [List.length_cons]
    omega
  have prefixLegal (g : Gate) (hg : g ∈ prefixGates) : allowed g := by
    change g ∈ first :: second :: A.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [allowed, first]
    rcases List.mem_cons.mp hg with rfl | hg
    · simpa [allowed, second] using pinsSize
    have h := mono g hg
    rcases h.1 with hOp | hOp
    · exact ⟨Or.inl hOp, h.2⟩
    · exact ⟨Or.inr (Or.inl (Set.mem_singleton_iff.mp hOp)), h.2⟩
  have appendBound (gs : List Gate) (o : ℕ) (hgs : ∀ g ∈ gs, allowed g)
      (computes : ∀ x, (gs.foldl step (mid x)).getD o false = f x) :
      13 ≤ A.size + gs.length := by
    let C : Circuit := ⟨prefixGates ++ gs, o⟩
    have legal : FanInTwo C := by
      intro g hg
      change g ∈ prefixGates ++ gs at hg
      exact (List.mem_append.mp hg).elim (prefixLegal g) (hgs g)
    have result : circuitFun 9 C = fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5) := by
      funext x
      change ((prefixGates ++ gs).foldl step (List.ofFn x)).getD o false = _
      rw [List.foldl_append, baseEval, computes, sameTarget]
    have lower := ordinary C legal result
    change 15 ≤ (prefixGates ++ gs).length at lower
    rw [List.length_append, prefixSize] at lower
    omega
  have withNotBound (gs : List Gate) (o : ℕ) (hgs : ∀ g ∈ gs, allowed g)
      (computes : ∀ x, (gs.foldl step (afterNot x)).getD o false = f x) :
      12 ≤ A.size + gs.length := by
    have h := appendBound (inv :: gs) o (by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [allowed, inv]
      · exact hgs g hg) (fun x => by
        rw [List.foldl_cons, notEval]
        exact computes x)
    simp only [List.length_cons] at h
    omega
  have lower : 12 ≤ A.size + B.size := withNotBound B.gates B.output fan correct
  have exactBudget : A.size + B.size = 12 := by omega
  have nonconstant : f (fun _ => false) ≠ f (fun _ => true) := by decide
  have above : cut ≤ B.output := by
    by_contra! h
    have bd := appendBound [] B.output (by simp) (fun x => by
      have hc := correct x
      change (B.gates.foldl step (afterNot x)).getD B.output false = f x at hc
      rw [keep _ _ _ (by rw [lengthAfter]; omega)] at hc
      change ((mid x) ++ [_]).getD B.output false = f x at hc
      rw [List.getD_append _ _ _ _ (by rw [lengthMid]; exact h)] at hc
      exact hc)
    simp at bd
    omega
  have evalOrder (g : Gate) (hg : g ∈ A.gates) (w z : List Bool)
      (h : ∀ i, w.getD i false = true → z.getD i false = true)
      (htrue : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
      g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
    rcases (mono g hg).1 with op | op
    · rw [op] at htrue ⊢
      change ((g.inputs.map fun i => w.getD i false).all id) = true at htrue
      change ((g.inputs.map fun i => z.getD i false).all id) = true
      rw [List.all_eq_true] at htrue ⊢
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      exact h i (htrue _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
    · have op' : g.op = GateOp.or := Set.mem_singleton_iff.mp op
      rw [op'] at htrue ⊢
      change ((g.inputs.map fun i => w.getD i false).any id) = true at htrue
      change ((g.inputs.map fun i => z.getD i false).any id) = true
      obtain ⟨b, hb, ht⟩ := List.any_eq_true.mp htrue
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, h i ht⟩
  have runOrder (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ A.gates) (w z : List Bool)
      (len : w.length = z.length)
      (h : ∀ i, w.getD i false = true → z.getD i false = true) :
      ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step z).getD i false = true := by
    induction gs generalizing w z with
    | nil => exact h
    | cons g gs ih =>
      simp only [List.foldl_cons]
      apply ih (fun i hi => sub i (List.mem_cons_of_mem _ hi))
      · simp only [step, List.length_append, List.length_singleton, len]
      · intro i
        dsimp only [step]
        by_cases low : i < w.length
        · rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ (by omega)]
          exact h i
        · rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), len]
          by_cases same : i = z.length
          · simp only [same, Nat.sub_self]
            exact evalOrder g (sub g (by simp)) w z h
          · have hh : 1 ≤ i - z.length := by omega
            rw [List.getD_eq_default _ _ (by simpa using hh),
                List.getD_eq_default _ _ (by simpa using hh)]
            exact id
  have seedOrder : ∀ i, (start (fun _ => false)).getD i false = true →
      (start (fun _ => true)).getD i false = true := by
    have allFalse : ∀ i, (base (fun _ => false)).getD i false = false := by
      intro i
      by_cases hi : i < 10
      · interval_cases i <;> rfl
      · exact List.getD_eq_default _ _ (by simpa [base] using hi)
    have anyFalse : GateOp.or.eval (pins.map fun i => (base (fun _ => false)).getD i.val false) = false := by
      change (pins.map fun i => (base (fun _ => false)).getD i.val false).any id = false
      rw [Bool.eq_false_iff]
      intro eq
      obtain ⟨value, hmem, hv⟩ := List.any_eq_true.mp eq
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
      change (base (fun _ => false)).getD i.val false = true at hv
      rw [allFalse] at hv
      contradiction
    intro i h
    change (base (fun _ => false) ++ [_]).getD i false = true at h
    rw [anyFalse] at h
    by_cases hi : i < (base (fun _ => false)).length
    · rw [List.getD_append _ _ _ _ hi, allFalse] at h
      contradiction
    · rw [List.getD_append_right _ _ _ _ (by omega)] at h
      have atFalse (k : ℕ) : ([false] : List Bool).getD k false = false := by
        cases k <;> rfl
      rw [atFalse] at h
      contradiction
  have later : cut < B.output := by
    by_contra! h
    have eq : B.output = cut := by omega
    have outNot (x : Fin 9 → Bool) : (!(mid x).getD A.output false) = f x := by
      have h := correct x
      change (B.gates.foldl step (afterNot x)).getD B.output false = f x at h
      rw [eq, keep _ _ _ (by rw [lengthAfter]; omega)] at h
      change ((mid x) ++ [_]).getD cut false = f x at h
      rw [← lengthMid x, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self] at h
      exact h
    have low : (mid (fun _ => false)).getD A.output false = true := by
      have e := outNot (fun _ => false)
      change (!(mid (fun _ => false)).getD A.output false) = false at e
      cases value : (mid (fun _ => false)).getD A.output false with
      | false =>
        rw [value] at e
        exact Bool.noConfusion e
      | true => rfl
    have high : (mid (fun _ => true)).getD A.output false = true :=
      runOrder A.gates (fun _ h => h) _ _ (by simp [start, base]) seedOrder A.output low
    have e := outNot (fun _ => true)
    change (!(mid (fun _ => true)).getD A.output false) = true at e
    rw [high] at e
    exact Bool.noConfusion e
  have inside : B.output < 24 := by
    by_contra! h
    have always (x : Fin 9 → Bool) : f x = false := by
      rw [← correct x]
      change (B.gates.foldl step (afterNot x)).getD B.output false = false
      apply List.getD_eq_default
      rw [lengthRun, lengthAfter]
      change 11 + A.size + 1 + B.size ≤ B.output
      omega
    exact nonconstant ((always (fun _ => false)).trans (always (fun _ => true)).symm)
  -- A shorter suffix would compute the same function with fewer gates.
  have outputLast : B.output = 23 := by
    by_contra h
    let k := B.output - cut
    have klt : k < B.gates.length := by
      change B.output - (11 + A.size) < B.size
      omega
    have smaller := withNotBound (B.gates.take k) B.output
      (fun g hg => fan g (List.mem_of_mem_take hg)) (fun x => by
        have hc := correct x
        change (B.gates.foldl step (afterNot x)).getD B.output false = f x at hc
        conv_lhs at hc => rw [← List.take_append_drop k B.gates, List.foldl_append]
        rw [keep] at hc
        · exact hc
        · rw [lengthRun, lengthAfter, List.length_take, Nat.min_eq_left (Nat.le_of_lt klt)]
          omega)
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt klt)] at smaller
    change k < B.size at klt
    omega
  let reads (g : Gate) := cut ∈ g.inputs ∧ (g.op ≠ GateOp.not ∨ g.inputs.head? = some cut)
  -- If the suffix never reads this wire, remove its slot and renumber later wires.
  have used : ∃ g ∈ B.gates, reads g := by
    by_contra! no
    let mapIdx (i : ℕ) := if i < cut then i else i - 1
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map mapIdx⟩
    have removeSim (gs : List Gate) (silent : ∀ g ∈ gs, ¬ reads g)
        (u v : List Bool) (len : u.length = v.length + 1) (room : cut ≤ v.length)
        (rel : ∀ i ≠ cut, u.getD i false = v.getD (mapIdx i) false) :
        ∀ i ≠ cut, (gs.foldl step u).getD i false =
          ((gs.map mapGate).foldl step v).getD (mapIdx i) false := by
      induction gs generalizing u v with
      | nil => exact rel
      | cons g gs ih =>
        simp only [List.foldl_cons, List.map_cons]
        have gate : g.op.eval (g.inputs.map fun i => u.getD i false) =
            (mapGate g).op.eval ((mapGate g).inputs.map fun i => v.getD i false) := by
          simp only [mapGate, List.map_map, Function.comp_def]
          by_cases hn : g.op = GateOp.not
          · rw [hn]
            cases h : g.inputs with
            | nil => rfl
            | cons i rest =>
              have hi : i ≠ cut := by
                intro e
                exact silent g (by simp) ⟨by simp [h, e], Or.inr (by simp [h, e])⟩
              change (!(u.getD i false)) = (!(v.getD (mapIdx i) false))
              rw [rel i hi]
          · congr 1
            exact List.map_congr_left (fun i hi => rel i (fun eq =>
              silent g (by simp) ⟨eq ▸ hi, Or.inl hn⟩))
        apply ih (fun g hg => silent g (List.mem_cons_of_mem _ hg))
        · simp only [step, List.length_append, List.length_singleton, len]
        · simp only [step, List.length_append, List.length_singleton]; omega
        · intro i hi
          dsimp only [step]
          rw [gate]
          by_cases h : i < u.length
          · have hs : mapIdx i < v.length := by dsimp only [mapIdx]; split <;> omega
            rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ hs]
            exact rel i hi
          · have offset : mapIdx i - v.length = i - u.length := by
              dsimp only [mapIdx]
              rw [ite_eq_right (show ¬i < cut by omega)]
              omega
            rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by
                  dsimp only [mapIdx]; split <;> omega), offset]
    have eq (x : Fin 9 → Bool) (i : ℕ) (hi : i ≠ cut) :
        (afterNot x).getD i false = (mid x).getD (mapIdx i) false := by
      by_cases lo : i < cut
      · simp only [afterNot, mapIdx, ite_eq_left lo]
        exact List.getD_append _ _ _ _ (by rw [lengthMid]; exact lo)
      · rw [List.getD_eq_default _ _ (by rw [lengthAfter]; omega),
          List.getD_eq_default _ _ (by rw [lengthMid]; dsimp only [mapIdx]; split <;> omega)]
    have bound := appendBound (B.gates.map mapGate) (mapIdx B.output) (by
      intro g hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      exact ⟨(fan a ha).1, by simpa only [mapGate, List.length_map] using (fan a ha).2⟩)
      (fun x => (removeSim B.gates no _ _ (by rw [lengthAfter, lengthMid])
        (by rw [lengthMid]) (eq x) B.output (by omega)).symm.trans (correct x))
    rw [List.length_map] at bound
    change 13 ≤ A.size + B.size at bound
    omega
  obtain ⟨x,hx⟩ := liveCase pins A B pinsSize mono fan exactBudget tapBound outputLast later addresses used
  exact hx (correct x)
