import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_2744_2
    (anchor :
      ∀ (op : Fin 3) (a b out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)),
        tail.length ≤ 13 → 11 ≤ out.val → out.val < 11 + tail.length → (a.val = 9 ∨ (op.val ≠ 2 ∧ b.val = 9)) →
        (∀ i : ℕ, i < 9 → (∃ g ∈ tail, g.2.1.val = i ∨ (g.1.val ≠ 2 ∧ g.2.2.val = i)) ∨ (op.val = 0 ∧ (i = 4 ∨ i = 6) ∧ (a.val = i ∨ b.val = i))) →
        ∃ m : ℕ, m < 512 ∧
          let x : Fin 9 → Bool := fun i => m.testBit i.val
          let read (w : List Bool) (j : Fin 26) := if j.val = 25 then true else w.getD j.val false
          let wires := ((op, a, b) :: tail).foldl (fun w g =>
            w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
              else if g.1.val = 1 then read w g.2.1 || read w g.2.2
              else !read w g.2.1]) (List.ofFn x ++ [x 4 || x 6])
          wires.getD out.val false ≠
            ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
              (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (raw :
      ∀ (op : Fin 3) (a b out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)),
        tail.length ≤ 13 → 11 ≤ out.val → out.val < 11 + tail.length → ¬(a.val = 9 ∨ (op.val ≠ 2 ∧ b.val = 9)) →
        (∀ i : ℕ, i < 9 → (∃ g ∈ tail, g.2.1.val = i ∨ (g.1.val ≠ 2 ∧ g.2.2.val = i)) ∨ (let q (j : Fin 26) := if j.val < 10 then j.val else if j.val = 25 then 11 else 10
          let a := q a
          let b := q b
          let op := op.val
          let j := if a = i then b else if b = i then a else 120
          if op = 2 then a = i else j = i ∨
            if op = 0 then j = 11 ∨ 12 * i + j ∈ ([54,57,76,81] : List ℕ)
            else j = 10 ∨ 12 * i + j ∈ ([49,56,72,75] : List ℕ))) →
        ∃ m : ℕ, m < 512 ∧
          let x : Fin 9 → Bool := fun i => m.testBit i.val
          let read (w : List Bool) (j : Fin 26) := if j.val = 25 then true else w.getD j.val false
          let wires := ((op, a, b) :: tail).foldl (fun w g =>
            w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
              else if g.1.val = 1 then read w g.2.1 || read w g.2.2
              else !read w g.2.1]) (List.ofFn x ++ [x 4 || x 6])
          wires.getD out.val false ≠
            ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
              (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (16 : ℕ) ≤ x1.size := by
  intro C allowed first outputEq second
  by_contra! small
  let src (i : ℕ) : Fin 26 := if hi : i < 24 then ⟨i, by omega⟩ else 24
  let firstCode (g : Gate) : Fin 3 := by
    classical
    exact if g.op = .and then 0 else if g.op = .or then 1 else 2
  let code (g : Gate) : Fin 3 × Fin 26 × Fin 26 :=
    let fallback : Fin 26 := by
      classical
      exact if g.op = .and then 25 else 24
    (firstCode g,
      if g.inputs.isEmpty then fallback else src (g.inputs.getD 0 0),
      if g.inputs.isEmpty then fallback
      else if g.inputs.length = 1 then src (g.inputs.getD 0 0)
      else src (g.inputs.getD 1 0))
  let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
  let step (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :=
    w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
      else if g.1.val = 1 then read w g.2.1 || read w g.2.2
      else !read w g.2.1]
  let stepOrig (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have srcRead (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
      read w (src i) = w.getD i false := by
    by_cases hi : i < 24
    · have ne : i ≠ 25 := by omega
      simp [read,src,hi,ne]
    · have notin := List.getD_eq_default w false (by omega : w.length ≤ i)
      rw [notin]
      simpa [read,src,hi] using (List.getD_eq_default w false hw)
  have constTrue (w : List Bool) : read w 25 = true := by simp [read]
  have constFalse (w : List Bool) (hw : w.length ≤ 24) : read w 24 = false := by
    simpa [read] using List.getD_eq_default w false hw
  have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have notEval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have stepEq (w : List Bool) (hw : w.length ≤ 24) (g : Gate)
      (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      step w (code g) = stepOrig w g := by
    obtain ⟨op,ar⟩ := hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    cases h : g.inputs with
    | nil =>
      rcases op with e | e | e
      · simp [step,code,firstCode,stepOrig,h,e,andEval,constTrue]
      · simp [step,code,firstCode,stepOrig,h,e,orEval,constFalse w hw]
      · simp [step,code,firstCode,stepOrig,h,e,notEval,constFalse w hw]
    | cons a rest =>
      cases k : rest with
      | nil =>
        rcases op with e | e | e
        · simp [step,code,firstCode,stepOrig,h,k,e,andEval,srcRead w hw]
        · simp [step,code,firstCode,stepOrig,h,k,e,orEval,srcRead w hw]
        · simp [step,code,firstCode,stepOrig,h,k,e,notEval,srcRead w hw]
      | cons b tail =>
        have bounded : (a :: b :: tail).length ≤ 2 := by
          rw [← k, ← h]
          exact ar
        have nil : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at bounded
          omega
        subst tail
        rcases op with e | e | e
        · simp [step,code,firstCode,stepOrig,h,k,e,andEval,srcRead w hw]
        · simp [step,code,firstCode,stepOrig,h,k,e,orEval,srcRead w hw]
        · simp [step,code,firstCode,stepOrig,h,k,e,notEval,srcRead w hw]
  have foldEq (gs : List Gate)
      (ok : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (w : List Bool) (hw : w.length + gs.length ≤ 24) :
      (gs.map code).foldl step w = gs.foldl stepOrig w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have hneed : w.length ≤ 24 := by simp at hw; omega
      have ok' := ok g (by simp)
      have bound : (stepOrig w g).length + gs.length ≤ 24 := by
        simp only [stepOrig, List.length_append, List.length_singleton]
        simp only [List.length_cons] at hw
        omega
      simp only [List.map_cons, List.foldl_cons]
      rw [stepEq w hneed g ok']
      exact ih (fun a ha => ok a (List.mem_cons_of_mem g ha)) _ bound
  have foldLength (gs : List Gate) (w : List Bool) :
      (gs.foldl stepOrig w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp only [stepOrig,List.length_append,List.length_cons,List.length_nil]
      omega
  have foldRead (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl stepOrig w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih _ (by simp [stepOrig]; omega)]
      exact List.getD_append _ _ _ _ h
  cases cg : C.gates with
  | nil => simp [cg] at second
  | cons g rest =>
    cases rs : rest with
    | nil => simp [cg,rs] at second
    | cons g2 tail =>
      have all : C.gates = g :: g2 :: tail := cg.trans (congrArg (List.cons g) rs)
      have allowedSuffix (gate : Gate) (hg : gate ∈ g2 :: tail) :=
        allowed gate (by rw [all]; exact List.mem_cons_of_mem g hg)
      have tailBound : tail.length ≤ 13 := by
        change C.gates.length < 16 at small
        rw [all] at small
        simp only [List.length_cons] at small
        omega
      let op := (code g2).1
      let a := (code g2).2.1
      let b := (code g2).2.2
      let out := src C.output
      let t := tail.map code
      have codeEq : (g2 :: tail).map code = (op,a,b) :: t := by
        simp only [List.map_cons,t]
        rfl
      let goalFun (x : Fin 9 → Bool) :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

      have edgeForm : ∀ y : Fin 9 → Bool,
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
            y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
            y 6 && y 8 || y 8 && y 5) = goalFun y := by decide +kernel
      have evalEq (x : Fin 9 → Bool) : C.eval (List.ofFn x) = goalFun x :=
        (congrFun outputEq x).trans (edgeForm x)
      let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
      have encodedEval (x : Fin 9 → Bool) :
          (((op,a,b) :: t).foldl step (seed x)).getD out.val false = goalFun x := by
        let w := List.ofFn x
        let after := stepOrig w g
        have wlen : w.length = 9 := by simp [w]
        have secondList : after = w ++ [x 4 || x 6] := by
          have agree : (C.wires w).getD 9 false = after.getD 9 false := by
            change (C.gates.foldl stepOrig w).getD 9 false = _
            rw [all]
            change ((g2 :: tail).foldl stepOrig after).getD 9 false = _
            have bound : 9 < after.length := by simp [after,stepOrig,wlen]
            exact foldRead _ _ _ bound
          have last : after.getD 9 false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
            change (w ++ [_]).getD 9 false = _
            rw [List.getD_append_right _ _ _ _ (by omega),wlen]
            rfl
          have eq : g.op.eval (g.inputs.map fun i => w.getD i false) = (x 4 || x 6) :=
            last.symm.trans (agree.symm.trans (first x))
          change w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] = _
          rw [eq]
        have enough : (w ++ [x 4 || x 6]).length + (g2 :: tail).length ≤ 24 := by
          simp [wlen]
          omega
        have outputAgree : ((g2 :: tail).foldl stepOrig (w ++ [x 4 || x 6])).getD out.val false =
            C.eval w := by
          rw [← secondList]
          change ((g2 :: tail).foldl stepOrig after).getD out.val false =
            (C.gates.foldl stepOrig w).getD C.output false
          rw [all]
          change ((g2 :: tail).foldl stepOrig after).getD out.val false =
            ((g2 :: tail).foldl stepOrig after).getD C.output false
          by_cases le : C.output < 24
          · simp [out,src,le]
          · have limit : ((g2 :: tail).foldl stepOrig after).length ≤ 24 := by
              rw [foldLength,secondList]; exact enough
            rw [show out.val = 24 from by simp [out,src,le],List.getD_eq_default _ _ limit,
              List.getD_eq_default _ _ (by omega : ((g2 :: tail).foldl stepOrig after).length ≤ C.output)]
        change (((op,a,b) :: t).foldl step (w ++ [x 4 || x 6])).getD out.val false = _
        rw [← codeEq, foldEq _ allowedSuffix _ enough, outputAgree]
        exact evalEq x

      let effective (g : Fin 3 × Fin 26 × Fin 26) (i : ℕ) :=
        g.2.1.val = i ∨ (g.1.val ≠ 2 ∧ g.2.2.val = i)
      let skip (op i a b : ℕ) : Prop :=
          let j := if a = i then b else if b = i then a else 120
          if op = 2 then a = i else j = i ∨
            if op = 0 then j = 11 ∨ 12 * i + j ∈ ([54,57,76,81] : List ℕ)
            else j = 10 ∨ 12 * i + j ∈ ([49,56,72,75] : List ℕ)
      let narrow (j : Fin 26) : Fin 12 :=
        if h : j.val < 10 then ⟨j.val, by omega⟩ else if j.val = 25 then 11 else 10
      let smallRead (x : Fin 9 → Bool) (p : Fin 12) : Bool :=
        if h : p.val < 9 then x ⟨p.val,h⟩ else if p.val = 9 then x 4 || x 6 else p.val = 11
      let choose (o : Fin 3) (u v : Bool) : Bool :=
        if o.val = 0 then u && v else if o.val = 1 then u || v else !u
      let toggle (x : Fin 9 → Bool) (i : Fin 9) : Fin 9 → Bool := fun j => x j || decide (j=i)
      let input (m : ℕ) : Fin 9 → Bool := fun j => m.testBit j.val
      let probes : List (List ℕ) := [
        [2,10,16,20,32,80,130,258], [1,4,9,20,36,64,129,257],
        [2,8,9,18,34,72,128,258], [4,5,16,18,36,68,144,256],
        [65,69,72,104,193], [1,5,9,65,128,130,144,256], [18,50,146,272,276],
        [4,5,20,32,34,40,68,260], [8,9,10,32,36,48,64,136]]
      let probe (o : Fin 3) (i : Fin 9) (u v : Fin 12) (m : ℕ) : Bool :=
        let x := input m
        let z := toggle x i
        ((x 4 || x 6) == (z 4 || z 6)) &&
          ((choose o (smallRead x u) (smallRead x v) ==
            choose o (smallRead z u) (smallRead z v)) &&
           !(goalFun x == goalFun z))
      let cell (o : Fin 3) (i : Fin 9) (u v : Fin 12) : Bool :=
        let miss := @decide (skip o.val i.val u.val v.val) (by unfold skip; infer_instance)
        miss || (probes.getD i.val []).any (probe o i u v)
      have goodCells : ∀ o i u v, cell o i u v = true := by
        intro o i
        fin_cases o <;> fin_cases i <;> decide +kernel
      have sampleValid : ∀ (o : Fin 3) (i : Fin 9) (u v : Fin 12),
          ¬ skip o.val i.val u.val v.val →
          ∃ m : ℕ,
          let x := input m
          let z := toggle x i
          (x 4 || x 6) = (z 4 || z 6) ∧
          choose o (smallRead x u) (smallRead x v) = choose o (smallRead z u) (smallRead z v) ∧
          goalFun x ≠ goalFun z := by
        intro o i u v noSkip
        have parsed := goodCells o i u v
        simp only [cell,Bool.or_eq_true,decide_eq_true_eq] at parsed
        rcases parsed with h | h
        · exact (noSkip h).elim
        · obtain ⟨m,_,cert⟩ := List.any_eq_true.mp h
          simp only [probe,Bool.and_eq_true,beq_iff_eq] at cert
          rcases cert with ⟨a,b,c⟩
          exact ⟨m,a,b,fun e => by simp [e] at c⟩
      have ofFnRead {n : ℕ} (f : Fin n → Bool) (j : Fin n) :
          (List.ofFn f).getD j.val false = f j := by
        rw [List.getD_eq_getElem _ _ (by simp)]
        simp
      have seedLen (f : Fin 9 → Bool) : (seed f).length = 10 := by simp [seed]
      have seedRaw (f : Fin 9 → Bool) (j : Fin 9) : (seed f).getD j.val false = f j := by
        change (List.ofFn f ++ [_]).getD j.val false = f j
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using j.isLt),ofFnRead]
      have seedLast (f : Fin 9 → Bool) : (seed f).getD 9 false = (f 4 || f 6) := by
        change (List.ofFn f ++ [_]).getD 9 false = _
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
      have narrowVal (j : Fin 26) : (narrow j).val =
          if j.val < 10 then j.val else if j.val = 25 then 11 else 10 := by
        unfold narrow
        split
        · rfl
        · split <;> rfl
      have smallReadEq (x : Fin 9 → Bool) (j : Fin 26) :
          read (seed x) j = smallRead x (narrow j) := by
        by_cases lt : j.val < 10
        · have nTrue : j.val ≠ 25 := by omega
          by_cases raw : j.val < 9
          · simpa only [read,nTrue,ite_false,narrow,lt,smallRead,raw,dite_true] using
              seedRaw x (⟨j.val,raw⟩ : Fin 9)
          · have nine : j.val = 9 := by omega
            have nEq : (narrow j).val = 9 := by simp [narrowVal,nine]
            unfold read
            rw [ite_eq_right nTrue,nine,seedLast]
            simp [smallRead,nEq]
        · by_cases top : j.val = 25
          · rw [show narrow j = 11 from by ext; simp [narrowVal,top]]
            simp [read,top,smallRead]
          · have outOfSeed : (seed x).length ≤ j.val := by rw [seedLen]; omega
            rw [show narrow j = 10 from by ext; simp [narrowVal,lt,top]]
            unfold read
            rw [ite_eq_right top,List.getD_eq_default _ _ outOfSeed]
            rfl
      have foldOff (i : ℕ) (ls : List (Fin 3 × Fin 26 × Fin 26)) (w z : List Bool)
          (hlen : w.length = z.length)
          (agree : ∀ j, j ≠ i → w.getD j false = z.getD j false)
          (absent : ∀ g ∈ ls, ¬ effective g i)
          (j : ℕ) (jne : j ≠ i) :
          (ls.foldl step w).getD j false = (ls.foldl step z).getD j false := by
        induction ls generalizing w z with
        | nil => exact agree j jne
        | cons g ls ih =>
          have ga : g.2.1.val ≠ i := fun e => absent g (by simp) (Or.inl e)
          have eqRead (v : Fin 26) (vne : v.val ≠ i) : read w v = read z v := by
            dsimp [read]
            rw [agree _ vne]
          let bit := choose g.1 (read z g.2.1) (read z g.2.2)
          have eqBit : choose g.1 (read w g.2.1) (read w g.2.2) = bit := by
            unfold bit
            rw [eqRead _ ga]
            by_cases unary : g.1.val = 2
            · have a0 : g.1.val ≠ 0 := by omega
              have a1 : g.1.val ≠ 1 := by omega
              simp only [choose,ite_eq_right a0,ite_eq_right a1]
            · rw [eqRead _ (fun e => absent g (by simp) (Or.inr ⟨unary,e⟩))]
          change (ls.foldl step (step w g)).getD j false =
            (ls.foldl step (step z g)).getD j false
          have ew : step w g = w ++ [bit] := by
            change w ++ [choose g.1 (read w g.2.1) (read w g.2.2)] = _
            rw [eqBit]
          have ez : step z g = z ++ [bit] := rfl
          rw [ew,ez]
          apply ih _ _ (by simp [hlen]) ?_ (fun r hr => absent r (List.mem_cons_of_mem g hr))
          intro k kn
          by_cases lt : k < w.length
          · rw [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (by omega),agree _ kn]
          · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hlen]
      have noRawOutput (i : Fin 9) : out.val ≠ i.val := by
        intro e
        have cOut : C.output = i.val := by
          by_cases lt : C.output < 24
          · simpa [out,src,lt] using e
          · have below := i.isLt
            simp [out,src,lt] at e
            omega
        let rawTest : Fin 9 → Bool := fun j => decide (j=i)
        have noEdge : ∀ i : Fin 9, goalFun (fun j => decide (j=i)) = false := by decide +kernel
        have calcOut := evalEq rawTest
        change (C.gates.foldl stepOrig (List.ofFn rawTest)).getD C.output false = _ at calcOut
        rw [cOut,foldRead _ _ _ (by simpa only [List.length_ofFn] using i.isLt),noEdge i] at calcOut
        rw [ofFnRead] at calcOut
        simp [rawTest] at calcOut
      have mandatory : ∀ i : ℕ, i < 9 →
          (∃ g ∈ t, effective g i) ∨ skip op.val i (narrow a).val (narrow b).val := by
        intro i bound
        by_cases allow : skip op.val i (narrow a).val (narrow b).val
        · exact Or.inr allow
        · apply Or.inl
          by_contra absent
          let p : Fin 9 := ⟨i,bound⟩
          obtain ⟨m,eqFirst,eqSecond,unequal⟩ := sampleValid op p (narrow a) (narrow b) allow
          let x := input m
          let z := toggle x p
          have secEq : choose op (read (seed x) a) (read (seed x) b) =
              choose op (read (seed z) a) (read (seed z) b) := by
            simp only [smallReadEq]
            exact eqSecond
          let pre (u : Fin 9 → Bool) := step (seed u) (op,a,b)
          have prefixAgree (k : ℕ) (kne : k ≠ i) : (pre x).getD k false = (pre z).getD k false := by
            have form (u : Fin 9 → Bool) : pre u = seed u ++ [choose op (read (seed u) a) (read (seed u) b)] := rfl
            rw [form x,form z,secEq]
            let bit := choose op (read (seed z) a) (read (seed z) b)
            change (seed x ++ [bit]).getD k false = (seed z ++ [bit]).getD k false
            by_cases ap : k < 10
            · have before (f : Fin 9 → Bool) :
                  (seed f ++ [bit]).getD k false = (seed f).getD k false :=
                List.getD_append _ _ _ _ (by rw [seedLen]; exact ap)
              rw [before x, before z]
              by_cases raw : k < 9
              · let q : Fin 9 := ⟨k,raw⟩
                change (seed x).getD q.val false = (seed z).getD q.val false
                rw [seedRaw,seedRaw]
                have ne : q ≠ p := fun h => kne (congrArg Fin.val h)
                simp [z,toggle,ne]
              · have nine : k = 9 := by omega
                rw [nine,seedLast,seedLast]
                exact eqFirst
            · have after (f : Fin 9 → Bool) :
                  (seed f ++ [bit]).getD k false = ([bit] : List Bool).getD (k-10) false := by
                rw [List.getD_append_right _ _ _ _ (by rw [seedLen]; omega),seedLen]
              rw [after x,after z]
          have noGate (g : Fin 3 × Fin 26 × Fin 26) (hg : g ∈ t) : ¬effective g i :=
            fun e => absent ⟨g,hg,e⟩
          have same := foldOff i t (pre x) (pre z) (by simp [pre,step,seedLen])
            prefixAgree noGate out.val (noRawOutput p)
          change (((op,a,b) :: t).foldl step (seed x)).getD out.val false =
            (((op,a,b) :: t).foldl step (seed z)).getD out.val false at same
          exact unequal ((encodedEval x).symm.trans (same.trans (encodedEval z)))
      have narrowOrd (j : Fin 26) (k : ℕ) (klt : k < 10) : (narrow j).val = k ↔ j.val = k := by
        rw [narrowVal]
        split
        · rfl
        · split <;> omega
      let anchorCell (o : Fin 3) (i : Fin 9) (u v : Fin 12) : Bool :=
        let miss := @decide (skip o.val i.val u.val v.val) (by unfold skip; infer_instance)
        !(decide (u.val = 9 ∨ (o.val ≠ 2 ∧ v.val = 9))) || !miss ||
          decide (o.val = 0 ∧ (i.val = 4 ∨ i.val = 6) ∧ (u.val = i.val ∨ v.val = i.val))
      have anchorCells : ∀ o i u v, anchorCell o i u v = true := by
        intro o i
        fin_cases o <;> fin_cases i <;> decide +kernel
      have anchoredSkip (o : Fin 3) (i : Fin 9) (u v : Fin 12)
          (pref : u.val = 9 ∨ (o.val ≠ 2 ∧ v.val = 9))
          (miss : skip o.val i.val u.val v.val) :
          o.val = 0 ∧ (i.val = 4 ∨ i.val = 6) ∧ (u.val = i.val ∨ v.val = i.val) := by
        have p := anchorCells o i u v
        simp only [anchorCell,decide_eq_true pref,decide_eq_true miss,
          Bool.not_true,Bool.false_or,decide_eq_true_eq] at p
        exact p
      let unavailable (u v : Fin 12) : Fin 9 :=
        if u.val ≠ 0 ∧ v.val ≠ 0 then 0 else if u.val ≠ 1 ∧ v.val ≠ 1 then 1 else 2
      let absentCell (o : Fin 3) (u v : Fin 12) : Bool :=
        !(@decide (skip o.val (unavailable u v).val u.val v.val) (by unfold skip; infer_instance))
      have absentCells : ∀ o u v, absentCell o u v = true := by
        intro o
        fin_cases o <;> decide +kernel
      have foldWire (L : List (Fin 3 × Fin 26 × Fin 26)) (w : List Bool)
          (j : ℕ) (h : j < w.length) : (L.foldl step w).getD j false = w.getD j false := by
        induction L generalizing w with
        | nil => rfl
        | cons g L ih =>
          rw [List.foldl_cons,ih _ (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ h
      have foldWireLen (L : List (Fin 3 × Fin 26 × Fin 26)) (w : List Bool) :
          (L.foldl step w).length = w.length + L.length := by
        induction L generalizing w with
        | nil => simp
        | cons g L ih =>
          simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]
          omega
      have outValid : out.val < 11 + t.length := by
        by_contra! invalid
        let x : Fin 9 → Bool := fun _ => true
        have trueOut : goalFun x = true := by decide +kernel
        have p := encodedEval x
        rw [trueOut,List.getD_eq_default] at p
        · contradiction
        · rw [foldWireLen,seedLen,List.length_cons]
          omega
      have outSuffix : 11 ≤ out.val := by
        by_contra! lo
        have nine : 9 ≤ out.val := by
          by_contra! r
          exact noRawOutput (⟨out.val,r⟩ : Fin 9) rfl
        let p := unavailable (narrow a) (narrow b)
        have notMiss : ¬ skip op.val p.val (narrow a).val (narrow b).val := by
          have h := absentCells op (narrow a) (narrow b)
          simpa only [absentCell,Bool.not_eq_true',decide_eq_false_iff_not,p] using h
        obtain ⟨m,eqFirst,eqSecond,unequal⟩ := sampleValid op p (narrow a) (narrow b) notMiss
        let x := input m
        let z := toggle x p
        let pre (u : Fin 9 → Bool) := step (seed u) (op,a,b)
        have preLen (u : Fin 9 → Bool) : (pre u).length = 11 := by simp [pre,step,seedLen]
        have preEq : (pre x).getD out.val false = (pre z).getD out.val false := by
          by_cases h9 : out.val = 9
          · rw [h9]
            change (seed x ++ [_]).getD 9 false = (seed z ++ [_]).getD 9 false
            have before (u : Fin 9 → Bool) (b : Bool) :
                (seed u ++ [b]).getD 9 false = (seed u).getD 9 false :=
              List.getD_append (seed u) [b] false 9 (by rw [seedLen]; decide)
            rw [before x,before z,seedLast,seedLast]
            exact eqFirst
          · have h10 : out.val = 10 := by omega
            rw [h10]
            change (seed x ++ [choose op (read (seed x) a) (read (seed x) b)]).getD 10 false =
              (seed z ++ [choose op (read (seed z) a) (read (seed z) b)]).getD 10 false
            rw [List.getD_append_right _ _ _ _ (by simp [seedLen]),
              List.getD_append_right _ _ _ _ (by simp [seedLen]),seedLen,seedLen]
            simpa only [Nat.sub_self,List.getD_cons_zero,smallReadEq] using eqSecond
        apply unequal
        rw [← encodedEval x, ← encodedEval z]
        change (t.foldl step (pre x)).getD out.val false = (t.foldl step (pre z)).getD out.val false
        rw [foldWire _ _ _ (by rw [preLen]; exact lo),foldWire _ _ _ (by rw [preLen]; exact lo)]
        exact preEq
      have closed : ∃ m : ℕ, m < 512 ∧
          (((op,a,b) :: t).foldl step (seed (input m))).getD out.val false ≠ goalFun (input m) := by
        by_cases pref : a.val = 9 ∨ (op.val ≠ 2 ∧ b.val = 9)
        · apply anchor op a b out t (by simpa [t] using tailBound) outSuffix outValid pref
          intro i hi
          rcases mandatory i hi with h | h
          · exact Or.inl h
          · apply Or.inr
            let p : Fin 9 := ⟨i,hi⟩
            have smallPref : (narrow a).val = 9 ∨ (op.val ≠ 2 ∧ (narrow b).val = 9) := by
              rw [narrowOrd a 9 (by decide),narrowOrd b 9 (by decide)]
              exact pref
            obtain ⟨op0,i46,hit⟩ := anchoredSkip op p (narrow a) (narrow b) smallPref h
            exact ⟨op0,i46,by
              rw [narrowOrd a i (by omega),narrowOrd b i (by omega)] at hit
              exact hit⟩
        · apply raw op a b out t (by simpa [t] using tailBound) outSuffix outValid pref
          intro i hi
          simpa only [narrowVal] using mandatory i hi
      obtain ⟨m,_,bad⟩ := closed
      exact bad (encodedEval (input m))
