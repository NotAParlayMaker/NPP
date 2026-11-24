import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3350_417
    (ordinary : ∀ C : Circuit, FanInTwo C →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 15 ≤ C.size)
    (uniqueReads : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → C.size ≤ 15 →
      ∀ i ∈ ([4,6] : List ℕ), ∃! j : Fin (C.gates.drop 1).length,
        let g := (C.gates.drop 1).get j
        g.inputs[0]? = some i ∨ g.op ≠ GateOp.not ∧ i ∈ g.inputs)
    (remaining :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (C : Circuit) (g : Gate), FanInTwo C →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
        C.gates[1]? = some g → g.op = GateOp.not → C.size = 15 → C.output = 23 →
        (∀ i ∈ ([4,6] : List ℕ), ∃! j : Fin (C.gates.drop 1).length,
          let h := (C.gates.drop 1).get j
          h.inputs[0]? = some i ∨ h.op ≠ GateOp.not ∧ i ∈ h.inputs) →
        (∀ i ∈ ([4,6] : List ℕ), g.inputs[0]? = some i →
          ∃ h ∈ C.gates.drop 2, h.op = GateOp.not) →
        ∃ x, circuitFun 9 C x ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C fan firstCorrect correct secondOp
  by_contra! small
  have exactSize : C.size = 15 := by
    have lo := ordinary C fan correct
    omega
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have same (x : Fin 9 → Bool) : circuitFun 9 C x = f x := by
    rw [correct]
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) :
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
  have existsFirst : ∃ a tail, C.gates = a :: tail := by
    apply List.exists_cons_of_ne_nil
    intro h
    simp [h] at secondOp
  obtain ⟨a, rest, firstSplit⟩ := existsFirst
  have existsSecond : ∃ b tail, rest = b :: tail := by
    apply List.exists_cons_of_ne_nil
    intro h
    simp [firstSplit,h] at secondOp
  obtain ⟨b, tail, secondSplit⟩ := existsSecond
  have split : C.gates = a :: b :: tail := firstSplit.trans (congrArg (List.cons a) secondSplit)
  have atB : C.gates[1]? = some b := by rw [split]; rfl
  have bOp : b.op = GateOp.not := by
    rw [atB] at secondOp
    exact Option.some.inj secondOp
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
  have seedLen (x : Fin 9 → Bool) : (seed x).length = 10 := by simp [seed]
  have firstStep (x : Fin 9 → Bool) : step (List.ofFn x) a = seed x := by
    have wire := firstCorrect x
    change (C.gates.foldl step (List.ofFn x)).getD 9 false = _ at wire
    rw [split] at wire
    simp only [List.foldl_cons] at wire
    have wire' : (step (List.ofFn x) a).getD 9 false = (x 4 || x 6) := by
      have lk := keep (b :: tail) (step (List.ofFn x) a) 9 (by simp [step])
      exact lk.symm.trans wire
    change (List.ofFn x ++ [_]).getD 9 false = _ at wire'
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn] at wire'
    change a.op.eval (a.inputs.map fun i => (List.ofFn x).getD i false) = _ at wire'
    change List.ofFn x ++ [_] = seed x
    rw [wire']
  have outputAfter (x : Fin 9 → Bool) :
      (tail.foldl step (step (seed x) b)).getD C.output false = f x := by
    have out := same x
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = _ at out
    simpa only [split, List.foldl_cons, firstStep] using out
  have beforeLimit (x : Fin 9 → Bool) :
      (step (seed x) b).length = 11 := by
    simp only [step, List.length_append, List.length_singleton, seedLen]
  have seedZero : ∀ i, (seed (fun _ => false)).getD i false = false := by
    intro i
    by_cases small : i < 10
    · interval_cases i <;> rfl
    · apply List.getD_eq_default
      rw [seedLen]
      omega
  have notLit (x : Fin 9 → Bool) (i : ℕ) (h : b.inputs[0]? = some i) :
      step (seed x) b = seed x ++ [!((seed x).getD i false)] := by
    cases eq : b.inputs with
    | nil => simp [eq] at h
    | cons j rest =>
      rw [eq] at h
      have ji : j = i := Option.some.inj h
      dsimp only [step]
      rw [bOp, eq, ji]
      rfl
  have notZero : (step (seed (fun _ => false)) b).getD 10 false = true := by
    cases eq : b.inputs with
    | nil =>
      dsimp only [step]
      rw [bOp, eq]
      rfl
    | cons i rest =>
      have at0 : b.inputs[0]? = some i := by rw [eq]; rfl
      rw [notLit _ _ at0, seedZero]
      rfl
  have outBeyond : 11 ≤ C.output := by
    by_contra! low
    by_cases raw : C.output < 9
    · let x : Fin 9 → Bool := fun i => i.val != C.output
      have allExcept (j : ℕ) (hj : j < 9) : f (fun i => i.val != j) = true := by
        interval_cases j <;> decide
      have fx : f x = true := allExcept C.output raw
      have read : (List.ofFn x).getD C.output false = false := by
        rw [List.getD_eq_getElem _ _ (by simpa using raw), List.getElem_ofFn]
        simp [x]
      have eh := same x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _ at eh
      rw [keep _ _ _ (by simpa using raw), read, fx] at eh
      exact Bool.noConfusion eh
    · have e : C.output = 9 ∨ C.output = 10 := by omega
      rcases e with e | e
      · let x : Fin 9 → Bool := fun i => i == 4
        have h := outputAfter x
        rw [e, keep _ _ _ (by rw [beforeLimit]; decide)] at h
        exact Bool.noConfusion h
      · have h := outputAfter (fun _ => false)
        rw [e, keep _ _ _ (by rw [beforeLimit]; decide), notZero] at h
        exact Bool.noConfusion h
  have inRange : C.output < 24 := by
    by_contra! large
    have h := same (fun _ => true)
    change (C.gates.foldl step (List.ofFn (fun _ : Fin 9 => true))).getD C.output false = true at h
    rw [List.getD_eq_default _ _ (by
      rw [len, List.length_ofFn]
      change 9 + C.size ≤ C.output
      omega)] at h
    exact Bool.noConfusion h
  have outLast : C.output = 23 := by
    by_contra h
    let k := C.output - 9 + 1
    have lt : k < C.gates.length := by
      change C.output - 9 + 1 < C.size
      omega
    let D : Circuit := ⟨C.gates.take k, C.output⟩
    have fanD : FanInTwo D := fun g hg => fan g (List.mem_of_mem_take hg)
    have preserves : circuitFun 9 D = circuitFun 9 C := by
      funext x
      change ((C.gates.take k).foldl step (List.ofFn x)).getD C.output false =
        (C.gates.foldl step (List.ofFn x)).getD C.output false
      conv_rhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
      symm
      apply keep
      rw [len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt lt)]
      omega
    have lower := ordinary D fanD (preserves.trans correct)
    change 15 ≤ (C.gates.take k).length at lower
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt lt)] at lower
    change k < C.size at lt
    omega
  have unique := uniqueReads C fan firstCorrect correct (by omega)
  have noReadOf (i : ℕ) (mem : i ∈ ([4,6] : List ℕ)) (pin : b.inputs[0]? = some i) :
      ∀ g ∈ tail, g.op ≠ GateOp.not → i ∉ g.inputs := by
    have here : ∃! j : Fin (b :: tail).length,
        let g := (b :: tail).get j
        g.inputs[0]? = some i ∨ g.op ≠ GateOp.not ∧ i ∈ g.inputs := by
      have u := unique i mem
      rw [split] at u
      exact u
    obtain ⟨j, _, only⟩ := here
    have j0 : (0 : Fin (b :: tail).length) = j := only 0 (Or.inl pin)
    intro g hg notInv uses
    obtain ⟨k, hk, elem⟩ := List.getElem_of_mem hg
    let j' : Fin (b :: tail).length := ⟨k+1, by simpa using hk⟩
    have atj : (b :: tail).get j' = g := elem
    have jp : j' = j := only j' (by dsimp only; rw [atj]; exact Or.inr ⟨notInv, uses⟩)
    have q := congrArg Fin.val (jp.trans j0.symm)
    change k+1 = 0 at q
    omega
  -- If raw input four or six is seen only as its complement, a later negation is required.
  have extraNot (i : ℕ) (mem : i ∈ ([4,6] : List ℕ)) (pin : b.inputs[0]? = some i) :
      ∃ g ∈ C.gates.drop 2, g.op = GateOp.not := by
    rw [split]
    change ∃ g ∈ tail, g.op = GateOp.not
    by_contra! hMono
    have safe (g : Gate) (hg : g ∈ tail) : i ∉ g.inputs := noReadOf i mem pin g hg (hMono g hg)
    have grows (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ tail) (u v : List Bool)
        (equal : u.length = v.length)
        (le : ∀ n ≠ i, u.getD n false = true → v.getD n false = true) :
        ∀ n ≠ i, (gs.foldl step u).getD n false = true → (gs.foldl step v).getD n false = true := by
      induction gs generalizing u v with
      | nil => exact le
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have member := sub g (List.mem_cons_self)
        have hn := hMono g member
        have agree (n : ℕ) (hn' : n ∈ g.inputs) : u.getD n false = true → v.getD n false = true :=
          le n (fun h => safe g member (h ▸ hn'))
        have gate (h : g.op.eval (g.inputs.map fun n => u.getD n false) = true) :
            g.op.eval (g.inputs.map fun n => v.getD n false) = true := by
          have ha := (fan g (by rw [split]; simp [member])).1
          rcases ha with ha | ha | ha
          · have e : g.op = GateOp.and := ha
            rw [e] at h ⊢
            change ((g.inputs.map fun n => u.getD n false).all id) = true at h
            change ((g.inputs.map fun n => v.getD n false).all id) = true
            rw [List.all_eq_true] at h ⊢
            intro b hb
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
            exact agree j hj (h _ (List.mem_map.mpr ⟨j,hj,rfl⟩))
          · have e : g.op = GateOp.or := ha
            rw [e] at h ⊢
            change ((g.inputs.map fun n => u.getD n false).any id) = true at h
            change ((g.inputs.map fun n => v.getD n false).any id) = true
            obtain ⟨b,hb,ht⟩ := List.any_eq_true.mp h
            obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
            exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,agree j hj ht⟩
          · exact (hn (Set.mem_singleton_iff.mp ha)).elim
        apply ih (fun g hg => sub g (List.mem_cons_of_mem _ hg))
        · simp only [step, List.length_append, List.length_singleton, equal]
        · intro n ni
          dsimp only [step]
          by_cases low : n < u.length
          · rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ (by omega)]
            exact le n ni
          · rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by omega), equal]
            by_cases hn' : n = v.length
            · simp only [hn', Nat.sub_self]
              exact gate
            · have k : 1 ≤ n - v.length := by omega
              rw [List.getD_eq_default _ _ (by simpa using k),
                List.getD_eq_default _ _ (by simpa using k)]
              exact id
    have runPair (x y : Fin 9 → Bool) (fx : f x = true) (fy : f y = false)
        (le : ∀ n ≠ i, (step (seed x) b).getD n false = true →
          (step (seed y) b).getD n false = true) : False := by
      have ht := outputAfter x
      have hf := outputAfter y
      rw [fx] at ht
      rw [fy] at hf
      have oe : C.output ≠ i := by simp at mem; omega
      have r := grows tail (fun _ h => h) _ _ (by rw [beforeLimit, beforeLimit]) le C.output oe ht
      rw [hf] at r
      exact Bool.noConfusion r
    have either : i = 4 ∨ i = 6 := by simpa using mem
    rcases either with rfl | rfl
    · let x : Fin 9 → Bool := fun j => j == 0 || j == 6 || j == 4
      let y : Fin 9 → Bool := fun j => j == 0 || j == 6
      apply runPair x y (by decide) (by decide)
      intro n ni
      rw [notLit x 4 pin, notLit y 4 pin]
      by_cases small : n < 11
      · interval_cases n <;> first | contradiction | decide
      · rw [List.getD_eq_default _ _ (by simp only [List.length_append,List.length_singleton,seedLen]; omega),
            List.getD_eq_default _ _ (by simp only [List.length_append,List.length_singleton,seedLen]; omega)]
        exact id
    · let x : Fin 9 → Bool := fun j => j == 1 || j == 4 || j == 6
      let y : Fin 9 → Bool := fun j => j == 1 || j == 4
      apply runPair x y (by decide) (by decide)
      intro n ni
      rw [notLit x 6 pin, notLit y 6 pin]
      by_cases small : n < 11
      · interval_cases n <;> first | contradiction | decide
      · rw [List.getD_eq_default _ _ (by simp only [List.length_append,List.length_singleton,seedLen]; omega),
            List.getD_eq_default _ _ (by simp only [List.length_append,List.length_singleton,seedLen]; omega)]
        exact id
  obtain ⟨x,hx⟩ := remaining C b fan firstCorrect atB bOp exactSize outLast unique extraNot
  exact hx (same x)
