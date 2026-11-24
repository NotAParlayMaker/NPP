import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The lower bound premise is the checked theorem L_meta_2012.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3077_421
    (lower : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (other : ∀ (b out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)),
      tail.length ≤ 13 → b.val < 9 → b.val ≠ 0 → b.val ≠ 4 →
      (∀ i < 9, ∃ g ∈ tail, g.2.1.val = i ∨ g.2.2.val = i) →
      ∃ m < 512,
        let x : Fin 9 → Bool := fun i => m.testBit i.val
        let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
        let wires := tail.foldl (fun w g =>
          w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
            else if g.1.val = 1 then read w g.2.1 || read w g.2.2
            else !read w g.2.1])
          (List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || read (List.ofFn x) b])
        wires.getD out.val false ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  classical
  intro l r out tail budget anchor left right used
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
  let step (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :=
    w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
      else if g.1.val = 1 then read w g.2.1 || read w g.2.2
      else !read w g.2.1]
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let run (x : Fin 9 → Bool) := tail.foldl step (step (seed x) (1,l,r))
  have orient : ∃ b : Fin 26, b.val ≠ 25 ∧
      ∀ w, step w (1,l,r) = step w (1,9,b) := by
    rcases anchor with hl | hr
    · have e : l = (9 : Fin 26) := Fin.ext hl
      exact ⟨r,right,fun w => by rw [e]⟩
    · have e : r = (9 : Fin 26) := Fin.ext hr
      refine ⟨l,left,?_⟩
      intro w
      rw [e]
      change w ++ [read w l || read w 9] = w ++ [read w 9 || read w l]
      rw [Bool.or_comm]
  obtain ⟨b,not25,orient⟩ := orient
  have lengthSeed (x : Fin 9 → Bool) : (seed x).length = 10 := by simp [seed]
  have read9 (x : Fin 9 → Bool) : read (seed x) 9 = (x 0 || x 4) := by
    change (List.ofFn x ++ [x 0 || x 4]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    rfl
  have readSmall (x : Fin 9 → Bool) (h : b.val < 9) :
      read (seed x) b = read (List.ofFn x) b := by
    have hb : b.val < (List.ofFn x).length := by simpa using h
    simp only [read, not25, ↓reduceIte, seed]
    exact List.getD_append _ _ _ _ hb
  by_cases distinct : b.val < 9 ∧ b.val ≠ 0 ∧ b.val ≠ 4
  · obtain ⟨m,hm,fail⟩ := other b out tail budget distinct.1 distinct.2.1 distinct.2.2 used
    refine ⟨m,hm,?_⟩
    let x : Fin 9 → Bool := fun i => m.testBit i.val
    change (run x).getD out.val false ≠ f x
    have eq : step (seed x) (1,l,r) =
        List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || read (List.ofFn x) b] := by
      rw [orient]
      change seed x ++ [read (seed x) 9 || read (seed x) b] = _
      rw [read9, readSmall x distinct.1]
      rfl
    change (tail.foldl step (List.ofFn x ++
      [x 0 || x 4, (x 0 || x 4) || read (List.ofFn x) b])).getD out.val false ≠ f x at fail
    simpa only [run, eq] using fail
  · have duplicate (x : Fin 9 → Bool) : step (seed x) (1,l,r) = seed x ++ [x 0 || x 4] := by
      rw [orient]
      change seed x ++ [read (seed x) 9 || read (seed x) b] = _
      rw [read9]
      by_cases h : b.val < 9
      · rw [readSmall x h]
        have hb : b.val = 0 ∨ b.val = 4 := by
          by_contra! absent
          exact distinct ⟨h,absent.1,absent.2⟩
        rcases hb with h0 | h4
        · have hb' : b = (0 : Fin 26) := Fin.ext h0
          rw [hb']
          have r0 : read (List.ofFn x) 0 = x 0 := by
            change (List.ofFn x).getD 0 false = _
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
            rfl
          rw [r0]
          cases x 0 <;> cases x 4 <;> rfl
        · have hb' : b = (4 : Fin 26) := Fin.ext h4
          rw [hb']
          have r4 : read (List.ofFn x) 4 = x 4 := by
            change (List.ofFn x).getD 4 false = _
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
            rfl
          rw [r4]
          cases x 0 <;> cases x 4 <;> rfl
      · by_cases hn : b.val = 9
        · rw [show b = (9 : Fin 26) from Fin.ext hn, read9]
          simp only [Bool.or_self]
        · have off : read (seed x) b = false := by
            simp only [read, not25, ↓reduceIte]
            exact List.getD_eq_default _ _ (by rw [lengthSeed]; omega)
          rw [off, Bool.or_false]
    let wire (i : ℕ) := if i < 10 then i else if i = 10 then 9 else i - 1
    let encode (g : Fin 3 × Fin 26 × Fin 26) : Gate :=
      let a := g.2.1.val
      let b := g.2.2.val
      if g.1.val = 0 then
        ⟨.and, (if a = 25 then [] else [wire a]) ++ (if b = 25 then [] else [wire b])⟩
      else if g.1.val = 1 then
        if a = 25 ∨ b = 25 then ⟨.and, []⟩ else ⟨.or, [wire a, wire b]⟩
      else if a = 25 then ⟨.or, []⟩ else ⟨.not, [wire a]⟩
    let gateStep (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have legal (g : Fin 3 × Fin 26 × Fin 26) :
        (encode g).op ∈ ({.and,.or,.not} : Set GateOp) ∧ (encode g).inputs.length ≤ 2 := by
      by_cases ha : g.2.1.val = 25 <;> by_cases hb : g.2.2.val = 25 <;>
        by_cases op0 : g.1.val = 0 <;> by_cases op1 : g.1.val = 1 <;>
        simp only [encode,ha,hb,op0,op1,Nat.one_ne_zero,or_true,or_false,↓reduceIte] <;> simp
    have appendRead (w : List Bool) (a : Bool) (i : ℕ) :
        (w ++ [a]).getD i false = if i < w.length then w.getD i false
          else if i = w.length then a else false := by
      rcases lt_trichotomy i w.length with before | atEnd | after
      · rw [List.getD_append _ _ _ _ before, ite_eq_left before]
      · rw [List.getD_append_right _ _ _ _ atEnd.ge]
        simp [atEnd, List.getD_eq_getElem?_getD]
      · have sub : ∃ k, i - w.length = k+1 := ⟨i-w.length-1, by omega⟩
        obtain ⟨k,hk⟩ := sub
        rw [List.getD_append_right _ _ _ _ (by omega), hk]
        simp [List.getD_eq_getElem?_getD, show ¬ i < w.length by omega, show i ≠ w.length by omega]
    have agreeBit (g : Fin 3 × Fin 26 × Fin 26) (w u : List Bool)
        (lookup : ∀ i, w.getD i false = u.getD (wire i) false) :
        (encode g).op.eval ((encode g).inputs.map fun i => u.getD i false) =
          (if g.1.val = 0 then read w g.2.1 && read w g.2.2
            else if g.1.val = 1 then read w g.2.1 || read w g.2.2
            else !read w g.2.1) := by
      have hAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
      have hOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
      have hNot (xs : List Bool) : GateOp.not.eval xs = !xs.headD false := rfl
      by_cases ha : g.2.1.val = 25 <;> by_cases hb : g.2.2.val = 25 <;>
        by_cases op0 : g.1.val = 0 <;> by_cases op1 : g.1.val = 1 <;>
        simp only [encode,read,ha,hb,op0,op1,Nat.one_ne_zero,or_true,or_false,↓reduceIte,
          List.nil_append,List.append_nil,List.cons_append,List.map_cons,List.map_nil,
          hAnd,hOr,hNot,List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.headD_cons,
          id,Bool.and_true,Bool.true_and,Bool.or_true,Bool.true_or,Bool.or_false,Bool.not_true,
          ← lookup]
    have simulate (gs : List (Fin 3 × Fin 26 × Fin 26)) (w u : List Bool)
        (len : w.length = u.length + 1) (enough : 10 ≤ u.length)
        (lookup : ∀ i, w.getD i false = u.getD (wire i) false) :
        ∀ i, (gs.foldl step w).getD i false =
          ((gs.map encode).foldl gateStep u).getD (wire i) false := by
      induction gs generalizing w u with
      | nil => exact lookup
      | cons g gs ih =>
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        apply ih
        · simp only [step, gateStep, List.length_append, List.length_singleton, len]
        · simp only [gateStep, List.length_append, List.length_singleton]
          omega
        intro i
        have equal := agreeBit g w u lookup
        change (w ++ [_]).getD i false = (u ++ [_]).getD (wire i) false
        rw [equal, appendRead, appendRead]
        by_cases small : i < w.length
        · have before : wire i < u.length := by
            unfold wire
            split_ifs <;> omega
          rw [ite_eq_left small, ite_eq_left before]
          exact lookup i
        · by_cases atEnd : i = w.length
          · have atEnd' : wire i = u.length := by
              unfold wire
              split_ifs <;> omega
            rw [ite_eq_right small, ite_eq_right (by omega : ¬ wire i < u.length),
              ite_eq_left atEnd, ite_eq_left atEnd']
          · have after : u.length < wire i := by
              unfold wire
              split_ifs <;> omega
            rw [ite_eq_right small, ite_eq_right (by omega : ¬ wire i < u.length),
              ite_eq_right atEnd, ite_eq_right (by omega : wire i ≠ u.length)]
    have initial (x : Fin 9 → Bool) (i : ℕ) :
        (seed x ++ [x 0 || x 4]).getD i false = (seed x).getD (wire i) false := by
      rw [appendRead, lengthSeed]
      by_cases small : i < 10
      · rw [ite_eq_left small]
        simp only [wire, small, ↓reduceIte]
      · by_cases eq : i = 10
        · have at9 : (seed x).getD 9 false = (x 0 || x 4) := read9 x
          simp only [wire, eq, ↓reduceIte] at *
          exact at9.symm
        · have c : 10 ≤ wire i := by
            simp only [wire, small, eq, ↓reduceIte]
            omega
          rw [ite_eq_right small, ite_eq_right eq, List.getD_eq_default _ _ (by rwa [lengthSeed])]
    by_contra bad
    apply lower
    let first : Gate := ⟨.or,[0,4]⟩
    let D : Circuit := ⟨first :: tail.map encode, wire out.val⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ first :: tail.map encode at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr (Or.inl rfl), by decide⟩
      · obtain ⟨g,_,rfl⟩ := List.mem_map.mp hg
        exact legal g
    · change (first :: tail.map encode).length ≤ 14
      simp only [List.length_cons, List.length_map]
      omega
    · intro x
      let bits := BitVec.ofBoolListLE (List.ofFn x)
      have mlt : bits.toNat < 512 := by
        have h := bits.isLt
        simpa only [List.length_ofFn] using h
      have decode : (fun i : Fin 9 => bits.toNat.testBit i.val) = x := by
        funext i
        change (BitVec.ofBoolListLE (List.ofFn x)).toNat.testBit i.val = _
        rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
          List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have correct : ∀ m < 512, (run (fun i => m.testBit i.val)).getD out.val false =
          f (fun i => m.testBit i.val) := by
        intro m hm
        by_contra ne
        exact bad ⟨m,hm,ne⟩
      have evaluates := correct bits.toNat mlt
      rw [decode] at evaluates
      have firstStep : gateStep (List.ofFn x) first = seed x := by
        have r0 : (List.ofFn x).getD 0 false = x 0 := by
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
          rfl
        have r4 : (List.ofFn x).getD 4 false = x 4 := by
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
          rfl
        change List.ofFn x ++ [[(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false].any id] = _
        rw [r0,r4]
        simp only [seed, List.any_cons, List.any_nil, id, Bool.or_false]
      change ((tail.map encode).foldl gateStep (gateStep (List.ofFn x) first)).getD
        (wire out.val) false = f x
      rw [firstStep, ← simulate tail (seed x ++ [x 0 || x 4]) (seed x)
        (by simp only [List.length_append, List.length_singleton]) (by rw [lengthSeed]) (initial x)]
      change (tail.foldl step (step (seed x) (1,l,r))).getD out.val false = f x at evaluates
      rwa [duplicate] at evaluates
