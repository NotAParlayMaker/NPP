import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4500000 in
theorem PEqualNP.Outside.R_meta_2843_417
    (ordinary : ∀ C : Circuit, FanInTwo C →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 15 ≤ C.size)
    (internalOutput :
      let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),
        (1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ (C : Circuit) (v : Fin 9) (g : Gate), FanInTwo C → C.size = 13 → C.output = 23 →
        C.gates.getLast? = some g →
        (((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b,
          g.inputs = [a,b] ∧ 11 ≤ a ∧ 11 ≤ b ∧ a < 23 ∧ b < 23 ∧ a ≠ b) ∨
         (g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ 11 ≤ a ∧ a < 23)) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x v]) ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) || x4 x2]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (14 : ℕ) ≤ x1.size := by
  intro C v legal correct
  by_contra! budget
  let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),
    (1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x v]
  have fits (x : Fin 9 → Bool) : C.eval (seed x) = f x := correct x
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (u : List Bool) :
      (gs.foldl step u).length = u.length + gs.length := by
    induction gs generalizing u with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have seedLen (x : Fin 9 → Bool) : (seed x).length = 11 := by simp [seed]
  have keep (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i < u.length) :
      (gs.foldl step u).getD i false = u.getD i false := by
    induction gs generalizing u with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step, List.length_append, List.length_singleton]; omega
  let first : Gate := ⟨GateOp.or,[0,4]⟩
  let second : Gate := ⟨GateOp.or,[9,v.val]⟩
  have raw (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have prepend (x : Fin 9 → Bool) : step (step (List.ofFn x) first) second = seed x := by
    have e1 : step (List.ofFn x) first = List.ofFn x ++ [x 0 || x 4] := by
      change List.ofFn x ++ [((List.ofFn x).getD 0 false || ((List.ofFn x).getD 4 false || false))] = _
      rw [show (List.ofFn x).getD 0 false = x 0 from raw x 0,
        show (List.ofFn x).getD 4 false = x 4 from raw x 4, Bool.or_false]
    rw [e1]
    let w := List.ofFn x ++ [x 0 || x 4]
    have prior : w.getD 9 false = (x 0 || x 4) := by
      dsimp only [w]
      rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
      rfl
    have tap : w.getD v.val false = x v := by
      dsimp only [w]
      rw [List.getD_append _ _ _ _ (by simp), raw]
    change w ++ [(w.getD 9 false || (w.getD v.val false || false))] = seed x
    rw [prior,tap,Bool.or_false]
    simp [w,seed]
  have need (D : Circuit) (hD : FanInTwo D) (hf : ∀ x, D.eval (seed x) = f x) : 13 ≤ D.size := by
    let E : Circuit := ⟨first :: second :: D.gates,D.output⟩
    have ok : FanInTwo E := by
      intro g hg
      change g ∈ first :: second :: D.gates at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [first]
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [second]
      exact hD g hg
    have equiv : circuitFun 9 E = fun x => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      funext x
      change (D.gates.foldl step (step (step (List.ofFn x) first) second)).getD D.output false = _
      rw [prepend]
      have h := hf x
      change (D.gates.foldl step (seed x)).getD D.output false = f x at h
      rw [h]
      simp only [f,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    have lower := ordinary E ok equiv
    change 15 ≤ (first :: second :: D.gates).length at lower
    simp only [List.length_cons] at lower
    change 13 ≤ D.gates.length
    omega
  have exactSize : C.size = 13 := by have lower := need C legal fits; omega
  have cLen : C.gates.length = 13 := exactSize
  have highOnFalse (i : Fin 11) :
      ∃ x : Fin 9 → Bool, (seed x).getD i.val false = true ∧ f x = false := by
    let x : Fin 9 → Bool := fun j => decide (j.val = if i.val < 9 then i.val else 0)
    refine ⟨x,?_⟩
    fin_cases i <;> fin_cases v <;> decide
  have lowOnTrue (i : Fin 11) :
      ∃ x : Fin 9 → Bool, (seed x).getD i.val false = false ∧ f x = true := by
    let x : Fin 9 → Bool := fun j =>
      if i.val < 9 then decide (j.val ≠ i.val)
      else if v = 1 ∨ v = 2 then decide (j = 6 ∨ j = 8)
      else decide (j = 1 ∨ j = 2)
    refine ⟨x,?_⟩
    fin_cases i <;> fin_cases v <;> decide
  have bound : C.output < 24 := by
    by_contra! h
    have e := fits (fun _ => true)
    change (C.gates.foldl step (seed (fun _ => true))).getD C.output false = true at e
    rw [List.getD_eq_default _ _ (by rw [len,seedLen,cLen]; exact h)] at e
    exact Bool.noConfusion e
  have outLast : C.output = 23 := by
    by_contra h
    let k := if C.output < 11 then 0 else C.output-11+1
    have klt : k < C.gates.length := by rw [cLen]; dsimp only [k]; split <;> omega
    let D : Circuit := ⟨C.gates.take k,C.output⟩
    have dCorrect (x : Fin 9 → Bool) : D.eval (seed x) = f x := by
      rw [← fits x]
      change ((C.gates.take k).foldl step (seed x)).getD C.output false =
        (C.gates.foldl step (seed x)).getD C.output false
      conv_rhs => rw [← List.take_append_drop k C.gates,List.foldl_append]
      symm
      apply keep
      rw [len,seedLen,List.length_take_of_le klt.le]
      dsimp only [k]
      split <;> omega
    have lo := need D (fun g hg => legal g (List.mem_of_mem_take hg)) dCorrect
    change 13 ≤ (C.gates.take k).length at lo
    rw [List.length_take_of_le klt.le] at lo
    omega
  obtain noGates | ⟨pre,g,split⟩ := List.eq_nil_or_concat C.gates
  · have h : 0 = 13 := by simpa only [noGates,List.length_nil] using cLen
    omega
  rw [List.concat_eq_append] at split
  have preLen : pre.length = 12 := by
    rw [split,List.length_append,List.length_singleton] at cLen
    omega
  let before (x : Fin 9 → Bool) := pre.foldl step (seed x)
  let R (x : Fin 9 → Bool) (i : ℕ) := (before x).getD i false
  have wireLen (x : Fin 9 → Bool) : (before x).length = 23 := by
    change (pre.foldl step (seed x)).length = _
    rw [len,preLen,seedLen]
  have final (x : Fin 9 → Bool) :
      g.op.eval (g.inputs.map (R x)) = f x := by
    have e := fits x
    change (C.gates.foldl step (seed x)).getD C.output false = f x at e
    rw [split,List.foldl_append,List.foldl_cons,List.foldl_nil,outLast] at e
    change (before x ++ [_]).getD 23 false = f x at e
    have readEnd (z : List Bool) (p : Bool) (h : z.length = 23) :
        (z++[p]).getD 23 false = p := by
      rw [List.getD_append_right _ _ _ _ (by rw [h]), h, Nat.sub_self]
      rfl
    rw [readEnd _ _ (wireLen x)] at e
    exact e
  have sub (h : Gate) (hh : h ∈ pre) : h ∈ C.gates := by
    rw [split]
    exact List.mem_append_left _ hh
  have shorterFrom (i : ℕ) (realizes : ∀ x, R x i = f x) : False := by
    let A : Circuit := ⟨pre,i⟩
    have lb := need A (fun h hh => legal h (sub h hh)) realizes
    change 13 ≤ pre.length at lb
    omega
  have pinRaw (x : Fin 9 → Bool) (i : ℕ) (h : i < 11) :
      R x i = (seed x).getD i false := keep pre _ _ (by rwa [seedLen])
  have pinLate (x : Fin 9 → Bool) (i : ℕ) (h : 23 ≤ i) : R x i = false :=
    List.getD_eq_default _ _ (by rwa [wireLen])
  have pinLow (i : ℕ) (h : i < 11) : ∃ x, R x i = false ∧ f x = true := by
    obtain ⟨x,p,q⟩ := lowOnTrue ⟨i,h⟩
    exact ⟨x,(pinRaw x i h).trans p,q⟩
  have pinHigh (i : ℕ) (h : i < 11) : ∃ x, R x i = true ∧ f x = false := by
    obtain ⟨x,p,q⟩ := highOnFalse ⟨i,h⟩
    exact ⟨x,(pinRaw x i h).trans p,q⟩
  have pairGate (op : g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∃ a b, g.inputs = [a,b] ∧ 11 ≤ a ∧ 11 ≤ b ∧ a < 23 ∧ b < 23 ∧ a ≠ b := by
    have member : g ∈ C.gates := by rw [split]; simp
    have arity := (legal g member).2
    cases inp : g.inputs with
    | nil =>
      rcases op with op | op
      · have e := final (fun _ => false)
        rw [inp,op] at e
        exact Bool.noConfusion e
      · have e := final (fun _ => true)
        rw [inp,op] at e
        exact Bool.noConfusion e
    | cons a rest =>
      cases rest with
      | nil =>
        exact (shorterFrom a (fun x => by
          have e := final x
          rcases op with op | op
          · rw [inp,op] at e
            change (R x a && true) = f x at e
            simpa only [Bool.and_true] using e
          · rw [inp,op] at e
            change (R x a || false) = f x at e
            simpa only [Bool.or_false] using e)).elim
      | cons b rest =>
        have empty : rest = [] := by
          rw [inp] at arity
          simp only [List.length_cons] at arity
          cases rest with
          | nil => rfl
          | cons _ tl => simp only [List.length_cons] at arity; omega
        subst rest
        have valid (i j : ℕ) (order : g.inputs = [i,j] ∨ g.inputs = [j,i]) :
            11 ≤ i ∧ i < 23 := by
          have present : i ∈ g.inputs := by rcases order with h | h <;> simp [h]
          rcases op with op | op
          · have must (x : Fin 9 → Bool) (q : f x = true) : R x i = true := by
              have e := final x
              rw [op,q] at e
              change (g.inputs.map (R x)).all id = true at e
              exact List.all_eq_true.mp e _ (List.mem_map.mpr ⟨i,present,rfl⟩)
            refine ⟨?_,?_⟩
            · by_contra! h
              obtain ⟨x,p,q⟩ := pinLow i h
              exact Bool.noConfusion (p.symm.trans (must x q))
            · by_contra! h
              have p := pinLate (fun _ => true) i h
              exact Bool.noConfusion (p.symm.trans (must _ (by decide)))
          · have excludes (x : Fin 9 → Bool) (q : f x = false) (h : R x i = true) : False := by
              have e := final x
              rw [op,q] at e
              change (g.inputs.map (R x)).any id = false at e
              exact Bool.noConfusion (e.symm.trans
                (List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,present,rfl⟩,h⟩))
            refine ⟨?_,?_⟩
            · by_contra! h
              obtain ⟨x,p,q⟩ := pinHigh i h
              exact excludes x q p
            · by_contra! h
              apply shorterFrom j
              intro x
              have e := final x
              rw [op] at e
              rcases order with r | r
              · rw [r] at e
                change (R x i || (R x j || false)) = f x at e
                simpa only [pinLate x i h,Bool.false_or,Bool.or_false] using e
              · rw [r] at e
                change (R x j || (R x i || false)) = f x at e
                simpa only [pinLate x i h,Bool.or_false] using e
        have av := valid a b (Or.inl inp)
        have bv := valid b a (Or.inr inp)
        refine ⟨a,b,rfl,av.1,bv.1,av.2,bv.2,?_⟩
        intro same
        apply shorterFrom a
        intro x
        have e := final x
        rcases op with op | op
        · rw [inp,op,← same] at e
          change (R x a && (R x a && true)) = f x at e
          simpa only [Bool.and_true,Bool.and_self] using e
        · rw [inp,op,← same] at e
          change (R x a || (R x a || false)) = f x at e
          simpa only [Bool.or_false,Bool.or_self] using e
  have notGate (op : g.op = GateOp.not) :
      ∃ i, g.inputs.head? = some i ∧ 11 ≤ i ∧ i < 23 := by
    let zero : Fin 9 → Bool := fun _ => false
    have e := final zero
    rw [op] at e
    cases inp : g.inputs with
    | nil =>
      rw [inp] at e
      exact Bool.noConfusion e
    | cons i rest =>
      rw [inp] at e
      change (!(R zero i)) = false at e
      have trueIn : R zero i = true := by
        cases b : R zero i with
        | false => rw [b] at e; exact Bool.noConfusion e
        | true => rfl
      refine ⟨i,rfl,?_,?_⟩
      · by_contra! h
        have allZero (i : Fin 11) : (seed zero).getD i.val false = false := by
          fin_cases i <;> rfl
        have pin := (pinRaw zero i h).trans (allZero ⟨i,h⟩)
        exact Bool.noConfusion (pin.symm.trans trueIn)
      · by_contra! h
        exact Bool.noConfusion ((pinLate zero i h).symm.trans trueIn)
  have member : g ∈ C.gates := by rw [split]; simp
  have shape := (legal g member).1
  have options :
      (((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b,
        g.inputs = [a,b] ∧ 11 ≤ a ∧ 11 ≤ b ∧ a < 23 ∧ b < 23 ∧ a ≠ b) ∨
       (g.op = GateOp.not ∧ ∃ a,g.inputs.head? = some a ∧ 11 ≤ a ∧ a < 23)) := by
    rcases shape with ha | ho | hn
    · exact Or.inl ⟨Or.inl ha,pairGate (Or.inl ha)⟩
    · exact Or.inl ⟨Or.inr ho,pairGate (Or.inr ho)⟩
    · exact Or.inr ⟨hn,notGate hn⟩
  have last : C.gates.getLast? = some g := by rw [split,List.getLast?_concat]
  obtain ⟨x,hx⟩ := internalOutput C v g legal exactSize outLast last options
  exact hx (fits x)
