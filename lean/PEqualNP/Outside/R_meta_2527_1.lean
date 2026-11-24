import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 7000000 in
set_option synthInstance.maxSize 512 in
theorem PEqualNP.Outside.R_meta_2527_1
    (minor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)) 12)
    (singleReader : ∀ (D : Circuit) (f : (Fin 9 → Bool) → Bool),
      FanInTwo D → D.size ≤ 14 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4]) = f x) →
      f (fun i => decide (i = 0)) = false →
      f (fun i => decide (i = 0 ∨ i = 4)) = true →
      (∃ g ∈ D.gates, 4 ∈ g.inputs) →
      ¬ HasCircuitSize 8 (fun y => f (Fin.insertNth 4 false y)) 12 →
      ∃ g : Gate, g.op = GateOp.or ∧ D.gates.filter (fun h => decide (4 ∈ h.inputs)) = [g])
    (remaining :
      let f (x : Fin 9 → Bool) : Bool :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
      Option.map (fun g => g.op) D.gates[0]? = some GateOp.or →
      (∃ g ∈ D.gates, 0 ∈ g.inputs) →
      (∃ g : Gate, g.op = GateOp.or ∧
        D.gates.filter (fun h => decide (4 ∈ h.inputs)) = [g] ∧
        ∀ j ∈ ([0,2,3,6,7,8,9] : List ℕ), j ∉ g.inputs) →
      ¬ (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4]) = f x)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (∃ x7 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x7.inputs) → (∃ x8 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x8.inputs) → (16 : ℕ) ≤ x2.size := by
  dsimp only
  intro C fan first correct second read0 read4
  by_contra! small
  let f (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
  have minorEq : (fun y : Fin 8 → Bool => f (Fin.insertNth 4 false y)) =
      (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
        (x 5 && x 7) || (x 7 && x 4)) := by decide +kernel
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]
        omega
  rcases C with ⟨gates,o⟩
  cases gates with
  | nil => cases second
  | cons g gs =>
    let D : Circuit := ⟨gs,o⟩
    let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
    have firstValue (x : Fin 9 → Bool) : step (List.ofFn x) g = row x := by
      have e := first x
      change (gs.foldl step (step (List.ofFn x) g)).getD 9 false = _ at e
      rw [keep _ _ _ (by simp [step])] at e
      have read : (step (List.ofFn x) g).getD 9 false =
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
        change (List.ofFn x ++ [_]).getD 9 false = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      rw [read] at e
      change List.ofFn x ++ [_] = List.ofFn x ++ [_]
      rw [e]
    have fanD : FanInTwo D := fun h hh => fan h (List.mem_cons_of_mem g hh)
    have sizeD : D.size ≤ 14 := by
      change (g::gs).length < 16 at small
      change gs.length ≤ 14
      simp only [List.length_cons] at small
      omega
    have good (x : Fin 9 → Bool) : D.eval (row x) = f x := by
      have e := congrFun correct x
      change (gs.foldl step (step (List.ofFn x) g)).getD o false = _ at e
      rw [firstValue] at e
      exact e.trans rfl
    have secondD : Option.map (fun h => h.op) D.gates[0]? = some GateOp.or := second
    have readD0 : ∃ h ∈ D.gates, 0 ∈ h.inputs := read0
    have readD4 : ∃ h ∈ D.gates, 4 ∈ h.inputs := read4
    obtain ⟨h, hor, hfilter⟩ :=
      singleReader D f fanD sizeD good (by decide +kernel) (by decide +kernel)
        readD4 (minorEq ▸ minor)
    have witnessOut : o ≠ 4 := by
      intro same
      let x : Fin 9 → Bool := fun i => decide (i = 4)
      have e := good x
      change (gs.foldl step (row x)).getD o false = f x at e
      rw [same, keep _ _ _ (by simp [row])] at e
      have hx : (row x).getD 4 false = true ∧ f x = false := by decide +kernel
      rw [hx.1, hx.2] at e
      contradiction
    let off (j : ℕ) (i : Fin 9) : Bool := decide (i.val = 0 ∨ i.val = j)
    let on (j : ℕ) (i : Fin 9) : Bool := decide (i.val = 0 ∨ i.val = j ∨ i.val = 4)
    have tests : ∀ j : Fin 10, j.val ∈ ([0,2,3,6,7,8,9] : List ℕ) →
        f (off j.val) = false ∧ f (on j.val) = true ∧
        (row (off j.val)).getD j.val false = true ∧
        (row (on j.val)).getD j.val false = true ∧
        ∀ k : Fin 10, k.val ≠ 4 →
          (row (off j.val)).getD k.val false = (row (on j.val)).getD k.val false :=
      by decide +kernel
    have allowed : ∀ j ∈ ([0,2,3,6,7,8,9] : List ℕ), j ∉ h.inputs := by
      intro j hj jread
      have jlt : j < 10 := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
        omega
      let j' : Fin 10 := ⟨j,jlt⟩
      obtain ⟨f0,f1,aOn,bOn,agree⟩ := tests j' hj
      let a := row (off j)
      let b := row (on j)
      have aLen : a.length = 10 := by simp [a,row]
      have bLen : b.length = 10 := by simp [b,row]
      have sameExcept (k : ℕ) (hk : k ≠ 4) : a.getD k false = b.getD k false := by
        by_cases inRange : k < 10
        · exact agree ⟨k,inRange⟩ hk
        · simp [List.getD_eq_getElem?_getD, aLen, bLen, Nat.le_of_not_gt inRange]
      have propagate (l : List Gate) (u v : List Bool) (sameLen : u.length = v.length)
          (jValid : j < u.length) (uOn : u.getD j false = true) (vOn : v.getD j false = true)
          (equal : ∀ k : ℕ, k ≠ 4 → u.getD k false = v.getD k false)
          (masked : ∀ q ∈ l, 4 ∈ q.inputs → q.op = GateOp.or ∧ j ∈ q.inputs) :
          ∀ k : ℕ, k ≠ 4 → (l.foldl step u).getD k false = (l.foldl step v).getD k false := by
        induction l generalizing u v with
        | nil => exact equal
        | cons q rest ih =>
          let gu := q.op.eval (q.inputs.map fun k => u.getD k false)
          let gv := q.op.eval (q.inputs.map fun k => v.getD k false)
          have eqGate : gu = gv := by
            by_cases uses : 4 ∈ q.inputs
            · obtain ⟨op, readj⟩ := masked q (by simp) uses
              have evalOn (w : List Bool) (signal : w.getD j false = true) :
                  q.op.eval (q.inputs.map fun k => w.getD k false) = true := by
                rw [op]
                change (q.inputs.map fun k => w.getD k false).any id = true
                exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨j, readj, signal⟩, rfl⟩
              exact (evalOn u uOn).trans (evalOn v vOn).symm
            · have eqInputs : (q.inputs.map fun k => u.getD k false) =
                  q.inputs.map (fun k => v.getD k false) :=
                List.map_congr_left (fun k hk => equal k (fun same => uses (same ▸ hk)))
              exact congrArg (q.op.eval) eqInputs
          have jv : j < v.length := sameLen ▸ jValid
          rw [List.foldl_cons, List.foldl_cons]
          apply ih (step u q) (step v q)
          · simp [step,sameLen]
          · simp [step]
            omega
          · exact (List.getD_append _ _ _ _ jValid).trans uOn
          · exact (List.getD_append _ _ _ _ jv).trans vOn
          · intro k hk
            change (u ++ [gu]).getD k false = (v ++ [gv]).getD k false
            by_cases before : k < u.length
            · rw [List.getD_append _ _ _ _ before,
                  List.getD_append _ _ _ _ (sameLen ▸ before), equal k hk]
            · rw [eqGate]
              simp only [List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (Nat.le_of_not_gt before),
                  List.getElem?_append_right (sameLen ▸ Nat.le_of_not_gt before), sameLen]
          · intro q' hq'
            exact masked q' (List.mem_cons_of_mem q hq')
      have maskInput : ∀ q ∈ gs, 4 ∈ q.inputs → q.op = GateOp.or ∧ j ∈ q.inputs := by
        intro q qmem q4
        have filtered : q ∈ D.gates.filter (fun r => decide (4 ∈ r.inputs)) :=
          List.mem_filter.mpr ⟨qmem, decide_eq_true q4⟩
        rw [hfilter] at filtered
        have same : q = h := by simpa using filtered
        exact same.symm ▸ ⟨hor,jread⟩
      have e := propagate gs a b (aLen.trans bLen.symm) (aLen ▸ jlt)
        aOn bOn sameExcept maskInput o witnessOut
      change D.eval (row (off j)) = D.eval (row (on j)) at e
      rw [good, good, f0, f1] at e
      contradiction
    exact remaining D fanD sizeD secondD readD0 ⟨h, hor, hfilter, allowed⟩ good
