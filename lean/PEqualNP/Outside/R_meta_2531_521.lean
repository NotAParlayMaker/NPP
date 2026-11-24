import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_2531_521
    (allZero : ∀ C : Circuit, Monotone2 C → ∀ w : List Bool,
      C.eval (List.replicate w.length false) = true → C.eval w = true)
    (compile : ∀ C : Circuit, FanInTwo C → ∃ (B : BinaryCircuit) (p : Bool),
      (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) ∧ B.size + notCount C ≤ C.size ∧
      ∀ w : List Bool, w.length = 10 → (B.eval (w ++ [false]) != p) = C.eval w)
    (monoBound : ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 6]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      13 ≤ C.size)
    (signedBound : ∀ (B : BinaryCircuit) (p : Bool), (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
      (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x 0 && x 6, false]) != p) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      13 ≤ B.size) :have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 : ℕ),   x2.length ≤ (11 : ℕ) →     x4 ≤ (21 : ℕ) →       PEqualNP.MetaComplexity.FanInTwo { gates := x2 ++ [x3], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →         (∀ x8 ∈ x2 ++ [x3], ∀ x10 ∈ x8.inputs, x10 ≤ (21 : ℕ)) →           have x9 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x9 : Fin (9 : ℕ) → Bool) => { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ))]);           have x10 : (Fin (9 : ℕ) → Bool) → Bool := fun (x10 : Fin (9 : ℕ) → Bool) => x3.op.eval (List.map (fun (x11 : ℕ) => (x9 x10).getD x11 Bool.false) x3.inputs);           (∀ (x11 : Fin (9 : ℕ) → Bool), x1 x11 = Bool.false → x10 x11 = Bool.false ∧ (x9 x11).getD x4 Bool.false = Bool.true) → ∃ (x12 : Fin (9 : ℕ) → Bool), x1 x12 = Bool.true ∧ x10 x12 = Bool.false ∧ (x9 x12).getD x4 Bool.false = Bool.true := by
  dsimp only
  intro pre g o small _ fan _ rejected
  let F := fun x : Fin 9 → Bool =>
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun i => x (Fin.ofNat 9 (i / 10)) && x (Fin.ofNat 9 (i % 10)))
  let E := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  have equiv : F = E := by decide +kernel
  let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 && x 6]
  let step := fun (w : List Bool) (a : Gate) =>
    w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
  let w := fun x => pre.foldl step (row x)
  let v := fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
  let q := fun x => (w x).getD o false
  change (∀ x, F x = false → v x = false ∧ q x = true) at rejected
  change ∃ x, F x = true ∧ v x = false ∧ q x = true
  by_contra lacks
  have fv (x : Fin 9 → Bool) : (v x || !q x) = F x := by
    cases hf : F x
    · obtain ⟨hv,hq⟩ := rejected x hf
      simp [hv,hq]
    · cases hv : v x <;> cases hq : q x
      · rfl
      · exact (lacks ⟨x,hf,hv,hq⟩).elim
      · rfl
      · rfl
  let b := 10 + pre.length
  let P : Circuit := ⟨pre,o⟩
  let M : Circuit := ⟨pre ++ [g],b⟩
  let pred : Gate → Bool := fun a =>
    @decide (a.op = GateOp.not) (lineDegreeGateOpDecEq _ _)
  have length (gs : List Gate) (ws : List Bool) :
      (gs.foldl step ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons a rest ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have lenW (x : Fin 9 → Bool) : (w x).length = b := by
    change (pre.foldl step (row x)).length = _
    rw [length]
    simp [row,b]
  have last (ws : List Bool) (a : Bool) (i : ℕ) (hi : i = ws.length) :
      (ws ++ [a]).getD i false = a := by
    subst i
    simp [List.getD_eq_getElem?_getD]
  have keep (ws : List Bool) (a : Bool) (i : ℕ) (hi : i < ws.length) :
      (ws ++ [a]).getD i false = ws.getD i false := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
  have fzero : F (fun _ => false) = false := by decide +kernel
  have qzero : q (fun _ => false) = true := (rejected _ fzero).2
  have earlier : o < b := by
    by_contra h
    have hh : (w (fun _ => false)).length ≤ o := by rw [lenW]; omega
    have e : q (fun _ => false) = false := List.getD_eq_default _ _ hh
    exact Bool.noConfusion (qzero.symm.trans e)
  have evalM (x : Fin 9 → Bool) : M.eval (row x) = v x := by
    change ((pre ++ [g]).foldl step (row x)).getD b false = _
    rw [List.foldl_append]
    exact last (w x) (v x) b (lenW x).symm
  have fanM : FanInTwo M := fun a ha => fan a ha
  have sizeM : M.size ≤ 12 := by
    change (pre ++ [g]).length ≤ 12
    simp
    omega
  by_cases hn : notCount M = 0
  · have monoM : Monotone2 M := by
      intro a ha
      have noNot : a.op ≠ GateOp.not := by
        intro h
        have mem : a ∈ M.gates.filter pred := List.mem_filter.mpr ⟨ha,by simp [pred,h]⟩
        have nil : M.gates.filter pred = [] := List.eq_nil_of_length_eq_zero hn
        rw [nil] at mem
        exact List.not_mem_nil mem
      have fg := fanM a ha
      rcases fg.1 with h | h | h
      · exact ⟨Or.inl h,fg.2⟩
      · exact ⟨Or.inr h,fg.2⟩
      · exact (noNot h).elim
    have monoP : Monotone2 P := fun a ha => monoM a (List.mem_append_left _ ha)
    have zeroRow : row (fun _ => false) = List.replicate 10 false := by decide +kernel
    have qall (x : Fin 9 → Bool) : q x = true := by
      apply allZero P monoP (row x)
      have e : P.eval (row (fun _ => false)) = true := qzero
      rw [zeroRow] at e
      simpa [row] using e
    have bound := monoBound M monoM (by
      intro x
      have e := fv x
      rw [qall x] at e
      change (v x || false) = F x at e
      rw [evalM]
      rw [Bool.or_false] at e
      exact e.trans (congrFun equiv x))
    omega
  · let inv : Gate := ⟨GateOp.not,[o]⟩
    let out : Gate := ⟨GateOp.or,[b,b+1]⟩
    let D : Circuit := ⟨M.gates ++ [inv,out],b+2⟩
    have fanD : FanInTwo D := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact fanM a h
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl
        · exact ⟨Or.inr (Or.inr rfl),by change 1 ≤ 2; decide⟩
        · exact ⟨Or.inr (Or.inl rfl),Nat.le_refl 2⟩
    have sizeD : D.size ≤ 14 := by
      change (M.gates ++ [inv,out]).length ≤ 14
      have sz : M.gates.length ≤ 12 := sizeM
      simp
      omega
    have counts : 2 ≤ notCount D := by
      change 2 ≤ ((M.gates ++ [inv,out]).filter pred).length
      rw [List.filter_append,List.length_append]
      have h : (M.gates.filter pred).length = notCount M := rfl
      have v : ([inv,out].filter pred).length = 1 := by
        simp [pred,inv,out]
      omega
    have evalD (x : Fin 9 → Bool) : D.eval (row x) = E x := by
      let a := w x ++ [v x]
      let c := a ++ [!q x]
      have la : a.length = b+1 := by simp [a,lenW]
      have lc : c.length = b+2 := by simp [c,la,Nat.add_assoc]
      have aQ : a.getD o false = q x :=
        keep (w x) (v x) o (by rw [lenW]; exact earlier)
      have cv : c.getD b false = v x := by
        change (a ++ [!q x]).getD b false = _
        rw [keep a _ _ (by rw [la]; omega)]
        exact last (w x) (v x) b (lenW x).symm
      have cq : c.getD (b+1) false = !q x := last a _ _ la.symm
      change (((pre ++ [g]) ++ [inv,out]).foldl step (row x)).getD (b+2) false = _
      rw [List.foldl_append,List.foldl_append]
      change (step (step a inv) out).getD (b+2) false = _
      have invEval : step a inv = c := by
        change a ++ [!(a.getD o false)] = a ++ [!q x]
        rw [aQ]
      have outEval : step c out = c ++ [c.getD b false || c.getD (b+1) false] := by
        change c ++ [c.getD b false || (c.getD (b+1) false || false)] = _
        rw [Bool.or_false]
      rw [invEval,outEval,last c _ _ lc.symm,cv,cq,fv]
      exact congrFun equiv x
    obtain ⟨B,p,shape,cost,replay⟩ := compile D fanD
    have bound := signedBound B p shape (fun x => by
      change (B.eval (row x ++ [false]) != p) = E x
      exact (replay (row x) (by simp [row])).trans (evalD x))
    omega
