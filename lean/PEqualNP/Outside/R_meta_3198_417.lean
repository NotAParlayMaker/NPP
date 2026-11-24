import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3198_417
    (ordinary : ∀ C : Circuit, FanInTwo C →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 15 ≤ C.size)
    (nonfinal :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : Circuit, FanInTwo C → C.size = 15 → C.output = 23 →
        (∃ i j : Fin C.gates.length, i < j ∧ i.val = 5 ∧
          (C.gates.get i).op = GateOp.not ∧ (C.gates.get j).op = GateOp.not ∧
          ∀ k : Fin C.gates.length, (C.gates.get k).op = GateOp.not → k = i ∨ k = j) →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        (∀ g : Gate, C.gates[14]? = some g → g.op ≠ GateOp.not) →
        ∃ x : Fin 9 → Bool, circuitFun 9 C x ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (5 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan exactlyTwo first correct
  by_contra! small
  have exactSize : C.size = 15 := by
    have lo := ordinary C fan correct
    omega
  have lenC : C.gates.length = 15 := exactSize
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have graph (x : Fin 9 → Bool) : f x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  have agrees (x : Fin 9 → Bool) : circuitFun 9 C x = f x :=
    (congrFun correct x).trans (graph x).symm
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have lengthRun (gs : List Gate) (u : List Bool) :
      (gs.foldl step u).length = u.length + gs.length := by
    induction gs generalizing u with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have keep (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i < u.length) :
      (gs.foldl step u).getD i false = u.getD i false := by
    induction gs generalizing u with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step, List.length_append, List.length_singleton]
        omega
  have outputBound : C.output < 24 := by
    by_contra! h
    have out := agrees (fun _ => true)
    have dead : (C.gates.foldl step (List.ofFn (fun _ : Fin 9 => true))).getD C.output false = false := by
      apply List.getD_eq_default
      rw [lengthRun, List.length_ofFn, lenC]
      exact h
    change (C.gates.foldl step (List.ofFn (fun _ : Fin 9 => true))).getD C.output false = true at out
    exact Bool.noConfusion (dead.symm.trans out)
  have outputLast : C.output = 23 := by
    by_contra h
    let k := if C.output < 9 then 0 else C.output - 9 + 1
    have klt : k < C.gates.length := by
      rw [lenC]
      dsimp only [k]
      split <;> omega
    let D : Circuit := ⟨C.gates.take k, C.output⟩
    have fanD : FanInTwo D := fun g hg => fan g (List.mem_of_mem_take hg)
    have val : circuitFun 9 D = circuitFun 9 C := by
      funext x
      change ((C.gates.take k).foldl step (List.ofFn x)).getD C.output false =
        (C.gates.foldl step (List.ofFn x)).getD C.output false
      conv_rhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
      symm
      apply keep
      rw [lengthRun, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt klt)]
      dsimp only [k]
      split <;> omega
    have lo := ordinary D fanD (val.trans correct)
    change 15 ≤ (C.gates.take k).length at lo
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt klt)] at lo
    omega
  have two := exactlyTwo
  obtain ⟨i,j,_,iFive,iNot,_,only⟩ := exactlyTwo
  -- If the final gate is the second NOT, every rising pair of graph outputs
  -- must pass through a falling value on the first NOT.
  have lastMono (g : Gate) (atLast : C.gates[14]? = some g) : g.op ≠ GateOp.not := by
    intro gNot
    let last : Fin C.gates.length := ⟨14, by omega⟩
    have at14 : C.gates[14] = g := by
      rw [List.getElem?_eq_getElem (by omega)] at atLast
      exact Option.some.inj atLast
    have lastOp : (C.gates.get last).op = GateOp.not := by
      change C.gates[14].op = _
      rw [at14, gNot]
    have lastIsJ : last = j := by
      rcases only last lastOp with e | e
      · have value := congrArg Fin.val e
        change 14 = i.val at value
        omega
      · exact e
    have jFourteen : j.val = 14 := (congrArg Fin.val lastIsJ).symm
    let a : Gate := C.gates.get i
    let P := C.gates.take 5
    let Q := (C.gates.drop 6).take 8
    have aOp : a.op = GateOp.not := iNot
    have divide (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
        gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      calc
        gs = gs.take (k + 1) ++ gs.drop (k + 1) := (List.take_append_drop _ _).symm
        _ = _ := by rw [← List.take_append_getElem hk, List.append_assoc, List.singleton_append]
    have firstGate : C.gates[5] = a := by
      change C.gates[5] = C.gates[i.val]
      congr 1
      omega
    have headSplit : C.gates = P ++ a :: C.gates.drop 6 := by
      rw [← firstGate]
      exact divide C.gates 5 (by omega)
    have dropLen : (C.gates.drop 6).length = 9 := by simp [lenC]
    have end8 : (C.gates.drop 6)[8] = g := by
      rw [List.getElem_drop]
      exact at14
    have tailSplit : C.gates.drop 6 = Q ++ [g] := by
      conv_lhs => rw [divide (C.gates.drop 6) 8 (by omega)]
      have empty : ((C.gates.drop 6).drop (8+1)) = [] :=
        List.drop_eq_nil_iff.mpr (by omega)
      rw [end8, empty]
    have split : C.gates = P ++ [a] ++ Q ++ [g] := by
      conv_lhs => rw [headSplit]
      rw [tailSplit]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have noElse (k : ℕ) (hk : k < C.gates.length) (h5 : k ≠ 5) (h14 : k ≠ 14) :
        C.gates[k].op ≠ GateOp.not := by
      intro h
      rcases only ⟨k,hk⟩ h with h | h
      · have e := congrArg Fin.val h
        exact h5 (e.trans iFive)
      · have e := congrArg Fin.val h
        exact h14 (e.trans jFourteen)
    have pMono : ∀ b ∈ P, b.op = GateOp.and ∨ b.op = GateOp.or := by
      intro b hb
      obtain ⟨k, hk, atB⟩ := List.getElem_of_mem hb
      have lt : k < 5 := by
        rw [show P.length = 5 from List.length_take_of_le (by omega)] at hk
        exact hk
      have e : C.gates[k] = b := by
        rw [← atB]
        exact (List.getElem_take).symm
      have h := (fan b (List.mem_of_mem_take hb)).1
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (noElse k (by omega) (by omega) (by omega)
          (e ▸ Set.mem_singleton_iff.mp h)).elim
    have qMono : ∀ b ∈ Q, b.op = GateOp.and ∨ b.op = GateOp.or := by
      intro b hb
      obtain ⟨k, hk, atB⟩ := List.getElem_of_mem hb
      have lt : k < 8 := by
        rw [show Q.length = 8 from List.length_take_of_le (by omega)] at hk
        exact hk
      have e : C.gates[6+k] = b := by
        rw [← atB]
        exact (List.getElem_take.trans List.getElem_drop).symm
      have h := (fan b (List.mem_of_mem_drop (List.mem_of_mem_take hb))).1
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (noElse (6+k) (by omega) (by omega) (by omega)
          (e ▸ Set.mem_singleton_iff.mp h)).elim
    let pres (x : Fin 9 → Bool) := P.foldl step (List.ofFn x)
    let tap := a.inputs.headD 14
    let tapped (x : Fin 9 → Bool) := (pres x).getD tap false
    let before (x : Fin 9 → Bool) := Q.foldl step (pres x ++ [!(tapped x)])
    let lastTap := g.inputs.headD 23
    have preLen (x : Fin 9 → Bool) : (pres x).length = 14 := by
      change (P.foldl step (List.ofFn x)).length = _
      rw [lengthRun, List.length_ofFn, show P.length = 5 from List.length_take_of_le (by omega)]
    have beforeLen (x : Fin 9 → Bool) : (before x).length = 23 := by
      change (Q.foldl step (pres x ++ [!(tapped x)])).length = _
      rw [lengthRun, List.length_append, List.length_singleton, preLen,
        show Q.length = 8 from List.length_take_of_le (by omega)]
    have evalNot (b : Gate) (h : b.op = GateOp.not) (u : List Bool) (k : ℕ) (hk : u.length ≤ k) :
        step u b = u ++ [!(u.getD (b.inputs.headD k) false)] := by
      dsimp only [step]
      rw [h]
      cases e : b.inputs with
      | nil =>
        change u ++ [true] = u ++ [!(u.getD k false)]
        rw [List.getD_eq_default _ _ hk]
        rfl
      | cons a rest => rfl
    have firstEval (x : Fin 9 → Bool) : step (pres x) a = pres x ++ [!(tapped x)] :=
      evalNot a aOp _ _ (by rw [preLen])
    have finalEval (x : Fin 9 → Bool) : (!(before x).getD lastTap false) = f x := by
      have h := agrees x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = f x at h
      rw [split, List.foldl_append, List.foldl_append, List.foldl_append, outputLast] at h
      simp only [List.foldl_cons, List.foldl_nil] at h
      change (step (Q.foldl step (step (pres x) a)) g).getD 23 false = f x at h
      rw [firstEval] at h
      change (step (before x) g).getD 23 false = f x at h
      have readEnd (u : List Bool) (v : Bool) (last : u.length = 23) :
          (u ++ [v]).getD 23 false = v := by
        rw [List.getD_append_right _ _ _ _ (by rw [last]), last, Nat.sub_self]
        rfl
      rw [evalNot g gNot _ 23 (by rw [beforeLen]), readEnd _ _ (beforeLen x)] at h
      exact h
    let increases (u v : List Bool) := ∀ k, u.getD k false = true → v.getD k false = true
    have appendOrder (u v : List Bool) (hLen : u.length = v.length)
        (h : increases u v) (b c : Bool) (hbc : b = true → c = true) :
        increases (u ++ [b]) (v ++ [c]) := by
      intro k t
      by_cases small : k < u.length
      · rw [List.getD_append _ _ _ _ small] at t
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h k t
      · rw [List.getD_append_right _ _ _ _ (by omega), hLen] at t
        rw [List.getD_append_right _ _ _ _ (by omega)]
        by_cases last : k = v.length
        · rw [last, Nat.sub_self] at t ⊢
          exact hbc t
        · have n : 1 ≤ k - v.length := by omega
          rw [List.getD_eq_default _ _ (by simpa using n)] at t
          contradiction
    have folder (gs : List Gate) (mono : ∀ b ∈ gs, b.op = GateOp.and ∨ b.op = GateOp.or)
        (u v : List Bool) (len : u.length = v.length) (h : increases u v) :
        increases (gs.foldl step u) (gs.foldl step v) := by
      induction gs generalizing u v with
      | nil => exact h
      | cons b gs ih =>
        simp only [List.foldl_cons]
        apply ih (fun c hc => mono c (List.mem_cons_of_mem _ hc))
        · simp only [step, List.length_append, List.length_singleton, len]
        · apply appendOrder _ _ len h
          intro t
          rcases mono b List.mem_cons_self with op | op
          · rw [op] at t ⊢
            change ((b.inputs.map fun i => u.getD i false).all id) = true at t
            change ((b.inputs.map fun i => v.getD i false).all id) = true
            rw [List.all_eq_true] at t ⊢
            intro z hz
            obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
            exact h q (t _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
          · rw [op] at t ⊢
            change ((b.inputs.map fun i => u.getD i false).any id) = true at t
            change ((b.inputs.map fun i => v.getD i false).any id) = true
            obtain ⟨z,hz,ht⟩ := List.any_eq_true.mp t
            obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
            exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨q,hq,rfl⟩,h q ht⟩
    have rawOrder (x y : Fin 9 → Bool) (h : ∀ k, x k = true → y k = true) :
        increases (List.ofFn x) (List.ofFn y) := by
      intro k t
      by_cases hs : k < 9
      · rw [List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_ofFn] at t ⊢
        exact h ⟨k,hs⟩ t
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hs)] at t
        contradiction
    have mustToggle (x y : Fin 9 → Bool) (hxy : ∀ k, x k = true → y k = true)
        (fx : f x = false) (fy : f y = true) : tapped x = false ∧ tapped y = true := by
      have order : increases (pres x) (pres y) :=
        folder P pMono _ _ (by simp) (rawOrder x y hxy)
      have bad (ord : (!(tapped x)) = true → (!(tapped y)) = true) : False := by
        have wires : increases (before x) (before y) :=
          folder Q qMono _ _ (by simp only [List.length_append,List.length_singleton,preLen])
            (appendOrder _ _ (by rw [preLen, preLen]) order _ _ ord)
        have tx : (before x).getD lastTap false = true := by
          have h := finalEval x
          rw [fx] at h
          cases value : (before x).getD lastTap false with
          | false => rw [value] at h; exact Bool.noConfusion h
          | true => rfl
        have t := wires lastTap tx
        have hy := finalEval y
        rw [fy, t] at hy
        exact Bool.noConfusion hy
      cases hx : tapped x <;> cases hy : tapped y
      · exact (bad (by rw [hx,hy]; exact id)).elim
      · exact ⟨rfl,rfl⟩
      · exact (bad (by rw [hx,hy]; intro h; contradiction)).elim
      · exact (bad (by rw [hx,hy]; exact id)).elim
    have computes (x : Fin 9 → Bool) : tapped x = f x := by
      cases hx : f x
      · exact (mustToggle x (fun _ => true) (by intro; simp) hx (by decide)).1
      · exact (mustToggle (fun _ => false) x (by intro k h; contradiction) (by decide) hx).2
    let D : Circuit := ⟨P, tap⟩
    have fanD : FanInTwo D := fun g hg => fan g (List.mem_of_mem_take hg)
    have h := ordinary D fanD (by
      funext x
      change tapped x = _
      exact (computes x).trans (graph x))
    change 15 ≤ P.length at h
    rw [show P.length = 5 from List.length_take_of_le (by omega)] at h
    omega
  obtain ⟨x,hx⟩ := nonfinal C fan exactSize outputLast two first lastMono
  exact hx (agrees x)
