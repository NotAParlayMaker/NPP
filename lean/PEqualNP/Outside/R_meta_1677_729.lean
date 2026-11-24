import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The baseline is the checked statement L-meta-3610.
-- A final AND or OR cannot use a raw input or the supplied OR wire. Its
-- absorbing value occurs on an assignment where the edge function disagrees.
-- The final gate must read wire 22: bypassing the preceding gate otherwise
-- gives a tail of at most 13 gates, which the baseline rules out.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1677_729
    (baseline :
      let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
      ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x, D.eval (X x) ≠ F x)
    (inverter :
      let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
      ∀ D : Circuit, FanInTwo D → D.size = 13 → ∃ x, (D.wires (X x)).getD 22 false ≠ !(F x))
    (binary :
      let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
      ∀ D : Circuit, FanInTwo D → D.size = 13 → ∀ j : Fin 12, ∀ u : Bool,
        ∃ x, let w := D.wires (X x)
             let a := w.getD 22 false
             let b := w.getD (10 + j.val) false
             (if u then a || b else a && b) ≠ F x)
    : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
  let edge := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have evalA (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalO (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have evalN (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl
  have ft (x : Fin 9 → Bool) : F x = edge x := by
    simp only [F, edge, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  have lenX (x : Fin 9 → Bool) : (X x).length = 10 := by simp [X]
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have length (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]; omega
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD i false = _
      rw [ih (step w g) (by simp [step]; omega), List.getD_append _ _ _ _ hi]
  have readAppend (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases eq : i = w.length
    · subst i; simp [List.getD]
    · rw [ite_eq_right eq]
      by_cases lt : i < w.length
      · exact List.getD_append _ _ _ _ lt
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have separates : ∀ i : Fin 10, ∀ b : Bool, ∃ x : Fin 9 → Bool,
      (X x).getD i.val false = b ∧ F x = !b := by
    intro i b
    let seed : ℕ := if b then 2 ^ (if i.val = 9 then 0 else i.val)
      else ([6,12,3,3,3,3,3,3,3,6] : List ℕ).getD i.val 0
    refine ⟨fun j => seed.testBit j.val, ?_⟩
    dsimp only [seed]
    revert i b
    decide +kernel
  have fTrue : F (fun _ => true) = true := by decide +kernel
  have fFalse : F (fun _ => false) = false := by decide +kernel
  intro C fan first computes
  by_contra short
  obtain ⟨gates, o⟩ := C
  cases gates with
  | nil =>
    have bad := first (fun _ => true)
    contradiction
  | cons g gs =>
    have extn (x : Fin 9 → Bool) : (gs.foldl step (X x)).getD o false = F x := by
      let w := List.ofFn x
      let b := g.op.eval (g.inputs.map fun j => w.getD j false)
      have hn : w.length = 9 := List.length_ofFn
      have h := first x
      change (gs.foldl step (w ++ [b])).getD 9 false = (x 0 || x 6) at h
      rw [keep gs _ _ (by simp [hn]), List.getD_append_right _ _ _ _ (by omega), hn] at h
      change b = (x 0 || x 6) at h
      rw [ft]
      change (gs.foldl step (w ++ [x 0 || x 6])).getD o false = edge x
      rw [← h]
      exact congrFun computes x
    have tailFan : FanInTwo ⟨gs, o⟩ := fun z hz => fan z (List.mem_cons_of_mem _ hz)
    have cap : gs.length ≤ 14 := by change ¬16 ≤ (g :: gs).length at short; simp at short; omega
    have eq14 : gs.length = 14 := by
      by_contra bad
      obtain ⟨x, hx⟩ := baseline ⟨gs,o⟩ tailFan (show gs.length ≤ 13 by omega)
      exact hx (extn x)
    obtain ⟨pre,last,split⟩ := (List.eq_nil_or_concat' gs).resolve_left (by intro e; simp [e] at eq14)
    subst gs
    have plen : pre.length = 13 := by simpa using eq14
    have prefixFan (i : ℕ) : FanInTwo ⟨pre,i⟩ := fun z hz => tailFan z (List.mem_append_left _ hz)
    let wires := fun x => pre.foldl step (X x)
    let v := fun i x => (wires x).getD i false
    let lastBit := fun x => last.op.eval (last.inputs.map fun i => v i x)
    have width (x : Fin 9 → Bool) : (wires x).length = 23 := by simp [wires,length,lenX,plen]
    have endValue (x : Fin 9 → Bool) : (if o = 23 then lastBit x else v o x) = F x := by
      have h := extn x
      change ((pre ++ [last]).foldl step (X x)).getD o false = _ at h
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
      change (wires x ++ [lastBit x]).getD o false = _ at h
      simpa only [readAppend,width] using h
    have noWire (i : ℕ) : ¬∀ x, v i x = F x := by
      intro eq
      obtain ⟨x,h⟩ := baseline ⟨pre,i⟩ (prefixFan i) (show pre.length ≤ 13 by omega)
      exact h (eq x)
    have out : o = 23 := by
      by_contra bad
      exact noWire o (fun x => by simpa [bad] using endValue x)
    have computesLast (x : Fin 9 → Bool) : lastBit x = F x := by simpa [out] using endValue x
    have low (i : ℕ) (hi : i < 10) (x : Fin 9 → Bool) : v i x = (X x).getD i false :=
      keep pre _ i (by rw [lenX]; exact hi)
    have high (i : ℕ) (hi : 23 ≤ i) (x : Fin 9 → Bool) : v i x = false :=
      List.getD_eq_default _ _ (by rw [width]; exact hi)
    let join := fun (u a b : Bool) => if u then a || b else a && b
    have valid (u : Bool) (i j : ℕ) (h : ∀ x, join u (v i x) (v j x) = F x) : 10 ≤ i ∧ i < 23 := by
      constructor
      · by_contra bad
        obtain ⟨x, eq, f⟩ := separates ⟨i,by omega⟩ u
        have t := h x
        rw [low i (by omega), show (X x).getD i false = u from eq, f] at t
        cases u <;> simp [join] at t
      · by_contra bad
        have beyond : 23 ≤ i := by omega
        cases u with
        | false =>
          have t := h (fun _ => true)
          rw [high i beyond, fTrue] at t
          contradiction
        | true => exact noWire j (fun x => by simpa [join,high i beyond] using h x)
    obtain ⟨hop, arity⟩ := tailFan last (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have mustUse (z : Gate) (hz : FanInTwo ⟨[z],0⟩)
        (zcomp : ∀ x, z.op.eval (z.inputs.map fun i => v i x) = F x) : 22 ∈ z.inputs := by
      by_contra skip
      obtain ⟨prev, pen, r⟩ := (List.eq_nil_or_concat' pre).resolve_left (by intro e; simp [e] at plen)
      have prevLen : prev.length = 12 := by simp [r] at plen; omega
      let before := fun x => prev.foldl step (X x)
      have widthBefore (x : Fin 9 → Bool) : (before x).length = 22 := by simp [before,length,lenX,prevLen]
      have oldW (x : Fin 9 → Bool) : wires x = step (before x) pen := by
        simp only [wires,r,List.foldl_append,List.foldl_cons,List.foldl_nil,before]
      have args (x : Fin 9 → Bool) :
          z.inputs.map (fun i => (before x).getD i false) = z.inputs.map (fun i => v i x) := by
        apply List.map_congr_left
        intro i hi
        have neq : i ≠ 22 := fun e => skip (e ▸ hi)
        simp only [v,oldW,step,readAppend,widthBefore,neq,ite_false]
      let D : Circuit := ⟨prev ++ [z],22⟩
      have fd : FanInTwo D := by
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · exact prefixFan 0 y (r ▸ List.mem_append_left [pen] h)
        · exact hz y h
      obtain ⟨x,hx⟩ := baseline D fd (show (prev ++ [z]).length ≤ 13 by simp [prevLen])
      apply hx
      change ((prev ++ [z]).foldl step (X x)).getD 22 false = F x
      rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
      change (before x ++ [_]).getD 22 false = F x
      simp only [readAppend,widthBefore,ite_true]
      change z.op.eval (z.inputs.map fun i => (before x).getD i false) = F x
      rw [args x]
      exact zcomp x
    have lastFan : FanInTwo ⟨[last],0⟩ := by
      intro y hy
      have e : y = last := List.mem_singleton.mp hy
      exact e ▸ tailFan last (by simp)
    have handle (u : Bool) (op : last.op = if u then GateOp.or else GateOp.and) : False := by
      cases il : last.inputs with
      | nil =>
        cases u with
        | false => have t := computesLast (fun _ => false); simp [lastBit,op,il,evalA,fFalse] at t
        | true => have t := computesLast (fun _ => true); simp [lastBit,op,il,evalO,fTrue] at t
      | cons i rest =>
        cases rest with
        | nil =>
          apply noWire i
          intro x
          cases u <;> simpa [lastBit,op,il,evalA,evalO] using computesLast x
        | cons j more =>
          have empty : more = [] := by simpa [il] using arity
          subst more
          have joint (x : Fin 9 → Bool) : join u (v i x) (v j x) = F x := by
            cases u <;> simpa [join,lastBit,op,il,evalA,evalO] using computesLast x
          have hi := valid u i j joint
          have hj := valid u j i (by
            intro x
            simpa only [join, Bool.and_comm (v i x) (v j x), Bool.or_comm (v i x) (v j x)] using joint x)
          have ne : i ≠ j := by
            rintro rfl
            exact noWire i (fun x => by simpa [join] using joint x)
          have use := mustUse last lastFan computesLast
          simp only [il,List.mem_cons,List.not_mem_nil,or_false] at use
          have finish (p : ℕ) (hp : 10 ≤ p) (hp' : p < 22)
              (hw : ∀ x, join u (v 22 x) (v p x) = F x) : False := by
            let b : Fin 12 := ⟨p - 10, by omega⟩
            have hb : 10 + b.val = p := by dsimp [b]; omega
            obtain ⟨x,hx⟩ := binary ⟨pre,0⟩ (prefixFan 0) plen b u
            apply hx
            change join u (v 22 x) (v (10 + b.val) x) = F x
            rw [hb]
            exact hw x
          rcases use with rfl | rfl
          · exact finish j hj.1 (by omega) joint
          · apply finish i hi.1 (by omega)
            intro x
            simpa only [join, Bool.and_comm (v i x) (v 22 x), Bool.or_comm (v i x) (v 22 x)] using joint x
    rcases hop with ha | ho | hn
    · exact handle false ha
    · exact handle true ho
    · cases il : last.inputs with
      | nil =>
        have t := computesLast (fun _ => false)
        simp [lastBit,hn,il,evalN,fFalse] at t
      | cons i rest =>
        let z : Gate := ⟨.not,[i]⟩
        have good : FanInTwo ⟨[z],0⟩ := by
          intro y hy
          have e : y = z := List.mem_singleton.mp hy
          subst y
          simp [z]
        have same (x : Fin 9 → Bool) : z.op.eval (z.inputs.map fun j => v j x) = F x := by
          simpa [lastBit,hn,il,evalN,z] using computesLast x
        have eq : 22 = i := List.mem_singleton.mp (mustUse z good same)
        obtain ⟨x,hx⟩ := inverter ⟨pre,i⟩ (prefixFan i) plen
        apply hx
        change v 22 x = !(F x)
        rw [eq]
        simpa [lastBit,hn,il,evalN] using computesLast x
