import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 9000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_5150_27
  (lower : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
  (atlas : ∀ v : Fin 10, ∃ p : Fin 10 → Fin 10, p v = 9 ∧ ∀ y : Fin 9 → Bool,
      let x : Fin 10 → Bool := fun i => (List.ofFn y).getD (p i).val false
      ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).foldl (fun acc e => acc || (x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) false = ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).foldl (fun acc e => acc || (y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10)))) false) :
  ∀ (x1 : Fin (10 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → (x2.size + if x3 = Bool.true then (1 : ℕ) else (0 : ℕ)) ≤ (15 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x6 x1 = Bool.false ∧ (if x3 = Bool.true then !x2.eval (List.ofFn x6) else x2.eval (List.ofFn x6)) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) := by
  have rewire(p : Fin 10 → Fin 10) (C : Circuit) (phase : Bool) (fan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size + (if phase then 1 else 0) ∧
      ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) =
        (if phase then !(C.eval (List.ofFn (fun i => (List.ofFn y).getD (p i).val false)))
         else C.eval (List.ofFn (fun i => (List.ofFn y).getD (p i).val false))) := by
    let far := 10 + C.gates.length
    let idx (i : Nat) : Nat := if h : i < 10 then
      if (p ⟨i,h⟩).val < 9 then (p ⟨i,h⟩).val else far
      else i - 1
    let rewriteGate (g : Gate) : Gate := ⟨g.op,g.inputs.map idx⟩
    let T : Circuit := ⟨C.gates.map rewriteGate,idx C.output⟩
    have valid : FanInTwo T := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
      exact ⟨(fan h hh).1, by simpa [rewriteGate] using (fan h hh).2⟩
    have sizeT : T.size = C.size := by
      change (C.gates.map rewriteGate).length = C.gates.length
      exact List.length_map rewriteGate
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    have read (y : Fin 9 → Bool) (z : List Bool) (hz : z.length ≤ C.gates.length) (i : Nat) :
        (List.ofFn y ++ z).getD (idx i) false =
        (List.ofFn (fun j => (List.ofFn y).getD (p j).val false) ++ z).getD i false := by
      by_cases hi : i < 10
      · rw [List.getD_append (List.ofFn (fun j => (List.ofFn y).getD (p j).val false)) z false i (by simpa only [List.length_ofFn] using hi)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
        by_cases hp : (p ⟨i,hi⟩).val < 9
        · simp only [idx, dite_eq_left hi, ite_eq_left hp, List.getElem?_append_left (show (p ⟨i,hi⟩).val < (List.ofFn y).length by simpa only [List.length_ofFn] using hp), List.getElem?_ofFn, dite_eq_left hp, Option.getD_some]
        · have bound : (List.ofFn y ++ z).length ≤ far := by simp [far]; omega
          simp only [idx, dite_eq_left hi, ite_eq_right hp, List.getElem?_eq_none bound, dite_eq_right hp, Option.getD_none]
      · have hi' : 10 ≤ i := by omega
        simp only [idx,dite_eq_right hi,List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
        simp only [List.length_ofFn]
        congr 2
    have same (y : Fin 9 → Bool) :
        ∃ z : List Bool, z.length = C.gates.length ∧
          T.wires (List.ofFn y) = List.ofFn y ++ z ∧
          C.wires (List.ofFn (fun j => (List.ofFn y).getD (p j).val false)) =
            List.ofFn (fun j => (List.ofFn y).getD (p j).val false) ++ z := by
      let x := List.ofFn (fun j => (List.ofFn y).getD (p j).val false)
      have aux (gs : List Gate) (z : List Bool) (h : z.length + gs.length ≤ C.gates.length) :
          ∃ zz : List Bool, zz.length = z.length + gs.length ∧
            (gs.map rewriteGate).foldl step (List.ofFn y ++ z) = List.ofFn y ++ zz ∧
            gs.foldl step (x ++ z) = x ++ zz := by
        induction gs generalizing z with
        | nil => exact ⟨z, by simp, rfl, rfl⟩
        | cons g gs ih =>
          let val := g.op.eval (g.inputs.map (fun i => (x ++ z).getD i false))
          have equal : (rewriteGate g).op.eval ((rewriteGate g).inputs.map (fun i => (List.ofFn y ++ z).getD i false)) = val := by
            change g.op.eval ((g.inputs.map idx).map _) = _
            rw [List.map_map]
            exact congrArg g.op.eval (List.map_congr_left fun i _ => read y z (by simp at h; omega) i)
          obtain ⟨zz,len,a,b⟩ := ih (z ++ [val]) (by simp at h ⊢; omega)
          refine ⟨zz, by simp at len ⊢; omega, ?_, ?_⟩
          · simpa only [List.map_cons,List.foldl_cons,step,equal,List.append_assoc] using a
          · simpa only [List.foldl_cons,step,val,List.append_assoc] using b
      unfold Circuit.wires
      simpa only [T,x,List.append_nil,List.length_nil,Nat.zero_add,step] using aux C.gates [] (by simp)
    have evalT (y : Fin 9 → Bool) : T.eval (List.ofFn y) =
        C.eval (List.ofFn (fun i => (List.ofFn y).getD (p i).val false)) := by
      obtain ⟨z,len,a,b⟩ := same y
      change (T.wires _).getD (idx C.output) false = (C.wires _).getD C.output false
      rw [a,b]
      exact read y z (by omega) _
    cases phase with
    | false => exact ⟨T,valid,by simpa using sizeT, evalT⟩
    | true =>
      let neg : Gate := ⟨.not,[T.output]⟩
      let U : Circuit := ⟨T.gates ++ [neg],9 + C.gates.length⟩
      refine ⟨U, ?_, ?_, ?_⟩
      · intro g hg
        change g ∈ T.gates ++ [neg] at hg
        rcases List.mem_append.mp hg with old | new
        · exact valid g old
        · obtain rfl := List.mem_singleton.mp new
          exact ⟨by simp [neg],by simp [neg]⟩
      · change ((C.gates.map rewriteGate) ++ [neg]).length = C.gates.length + 1
        simp
      · intro y
        obtain ⟨z,len,a,_⟩ := same y
        have sz : (T.wires (List.ofFn y)).length = 9+C.gates.length := by rw [a,List.length_append,List.length_ofFn,len]
        change ((T.gates ++ [neg]).foldl step (List.ofFn y)).getD _ false = _
        rw [List.foldl_append]
        change (T.wires (List.ofFn y) ++ [!(T.eval (List.ofFn y))]).getD (9+C.gates.length) false = _
        rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega),sz,Nat.sub_self]
        simpa using congrArg Bool.not (evalT y)
  intro v C phase fan budget
  obtain ⟨p,pv,graphEq⟩ := atlas v
  obtain ⟨D,fanD,sizeD,evalD⟩ := rewire p C phase fan
  apply Classical.byContradiction
  intro no
  apply lower
  refine ⟨D,fanD,?_,?_⟩
  · cases phase <;> simpa [sizeD] using budget
  · intro y
    let x : Fin 10 → Bool := fun i => (List.ofFn y).getD (p i).val false
    have xv : x v = false := by simp only [x,pv,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; rfl
    have value : (if phase = true then !C.eval (List.ofFn x) else C.eval (List.ofFn x)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
      apply Classical.byContradiction
      intro ne
      exact no ⟨x,xv,ne⟩
    have edge := graphEq y
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) at edge
    rw [evalD y]
    exact value.trans edge
