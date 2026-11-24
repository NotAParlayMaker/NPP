import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2600000 in
theorem PEqualNP.Outside.R_meta_1675_417
    (reader :
      ∀ (C : Circuit) (a b : List Bool) (i j : ℕ) (v : Bool),
        FanInTwo C → a.length = b.length → j < a.length →
        a.getD j false = v → b.getD j false = v → C.output ≠ i →
        (∀ k ≠ i, a.getD k false = b.getD k false) → C.eval a ≠ C.eval b →
        ∃ g ∈ C.gates,
          i ∈ (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs) ∧
          ¬(g.op = (if v then GateOp.or else GateOp.and) ∧ j ∈ g.inputs))
    (bound :
      let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
        (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      let permitted (i : ℕ) (v : Bool) : List ℕ :=
        if i = 0 then (if v then [2,4,8] else [3,9]) else (if v then [1,4,5] else [0,9])
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 → 10 ≤ D.output →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 3]) = f x) →
        (∀ i ∈ ([0,3] : List ℕ), ∀ j < 10, j ≠ i → ∀ v : Bool, j ∉ permitted i v →
          ∃ g ∈ D.gates, i ∈ (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs) ∧
            ¬(g.op = (if v then GateOp.or else GateOp.and) ∧ j ∈ g.inputs)) → False) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan anchor correct
  by_contra! tooSmall
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
    (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
  let row (mask : ℕ) (i : Fin 9) := mask.testBit i.val
  have len (x : Fin 9 → Bool) : (base x).length = 10 := by simp [base]
  cases hg : C.gates with
  | nil =>
    have h := anchor (fun _ => true)
    change (C.gates.foldl step (List.ofFn (fun _ : Fin 9 => true))).getD 9 false = true at h
    rw [hg, List.foldl_nil, List.getD_eq_default _ _ (by simp)] at h
    cases h
  | cons g gs =>
    let D : Circuit := ⟨gs,C.output⟩
    have dfan : FanInTwo D := by
      intro h hh
      apply fan h
      rw [hg]
      exact List.mem_cons_of_mem _ hh
    have dsize : D.size ≤ 14 := by
      have sz : C.size = D.size+1 := by simp [Circuit.size,hg,D]
      omega
    have first (x : Fin 9 → Bool) : step (List.ofFn x) g = base x := by
      have h := anchor x
      change (C.gates.foldl step (List.ofFn x)).getD 9 false = _ at h
      rw [hg,List.foldl_cons,keep _ _ _ (by simp [step])] at h
      have v : (step (List.ofFn x) g).getD 9 false =
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [v] at h
      exact congrArg (fun b => List.ofFn x ++ [b]) h
    have exactEval (x : Fin 9 → Bool) : D.eval (base x) = f x := by
      have h := congrFun correct x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _ at h
      rw [hg,List.foldl_cons,first] at h
      simpa [D,Circuit.eval,Circuit.wires,step,f,Bool.or_assoc] using h
    have trueA : f (row 6) = true := by dsimp [f,row]; decide +kernel
    have trueB : f (row 160) = true := by dsimp [f,row]; decide +kernel
    have disjoint : ∀ i : Fin 10,
        (base (row 6)).getD i.val false = false ∨ (base (row 160)).getD i.val false = false := by
      dsimp [base,row]
      decide +kernel
    have outputGate : 10 ≤ D.output := by
      by_contra! low
      have ac (mask : ℕ) (yes : f (row mask) = true)
          (no : (base (row mask)).getD D.output false = false) : False := by
        have h := exactEval (row mask)
        change (D.gates.foldl step (base (row mask))).getD D.output false = f (row mask) at h
        rw [keep _ _ _ (by rwa [len]), no, yes] at h
        cases h
      rcases disjoint ⟨D.output,low⟩ with a | b
      · exact ac 6 trueA a
      · exact ac 160 trueB b
    apply bound D dfan dsize outputGate exactEval
    let endpoint (left : Bool) : ℕ := if left then 0 else 3
    let permitted (i : ℕ) (v : Bool) : List ℕ :=
      if i = 0 then (if v then [2,4,8] else [3,9]) else (if v then [1,4,5] else [0,9])
    let mask (left : Bool) (k : Fin 2) := (if left then [104,138] else [69,385]).getD k.val 0
    let a (left : Bool) (k : Fin 2) := row (mask left k)
    let b (left : Bool) (k : Fin 2) := row (mask left k + 2^endpoint left)
    have pairs : ∀ (left : Bool) (j : Fin 10) (v : Bool), j.val ≠ endpoint left →
        j.val ∉ permitted (endpoint left) v → ∃ k : Fin 2,
        (base (a left k)).getD j.val false = v ∧ (base (b left k)).getD j.val false = v ∧
        f (a left k) = false ∧ f (b left k) = true ∧
        ∀ t : Fin 10, t.val ≠ endpoint left →
          (base (a left k)).getD t.val false = (base (b left k)).getD t.val false := by
      dsimp [base,a,b,row,mask,endpoint,permitted,f]
      decide +kernel
    intro i hi j hj other v forbidden
    have choose : ∃ left : Bool, endpoint left = i := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl
      · exact ⟨true,rfl⟩
      · exact ⟨false,rfl⟩
    obtain ⟨left,rfl⟩ := choose
    obtain ⟨k,ja,jb,fa,fb,rel⟩ := pairs left ⟨j,hj⟩ v other forbidden
    apply reader D (base (a left k)) (base (b left k)) (endpoint left) j v
      dfan (by rw [len,len]) (by rwa [len]) ja jb
    · have iSmall : endpoint left < 10 := by cases left <;> decide
      omega
    · intro t ht
      by_cases h : t < 10
      · exact rel ⟨t,h⟩ ht
      · rw [List.getD_eq_default _ _ (by rw [len]; omega),
          List.getD_eq_default _ _ (by rw [len]; omega)]
    · intro eq
      rw [exactEval,exactEval,fa,fb] at eq
      cases eq
