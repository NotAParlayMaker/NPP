import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4936_317
    (liftCircuit :
∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (xs : List (BitVec n)),
  PEqualNP.MetaComplexity.FanInTwo C →
  let pool := xs ++ [0, ~~~0]
  ∃ (gs : List (BitVec n)) (v : BitVec n), gs.length ≤ C.size ∧
    (∀ j : Fin gs.length, let avail := pool ++ gs.take j.val
      let w := gs.get j
      w ∉ avail ∧ (∃ a ∈ avail, ∃ b ∈ avail,
        w = a &&& b ∨ w = a ||| b ∨ w = ~~~a)) ∧
    v ∈ pool ++ gs ∧ ∀ j : Fin n, v.getLsbD j.val =
      C.eval (xs.map fun u => u.getLsbD j.val))
    (search :
∀ (flag : Bool) (x : ℕ → BitVec 1024),
  (∀ i j : ℕ, j < 1024 → (x i).getLsbD j = j.testBit i) →
  let seed := ((List.range 10).map x ++ [if flag then x 0 &&& x 1 else x 0 ||| x 1]) ++ [0, ~~~0]
  let target := ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).foldl
    (fun t e => t ||| (x (e/10) &&& x (e%10))) 0
  ∀ gs : List (BitVec 1024), gs.length ≤ 18 →
    (∀ j : Fin gs.length, let avail := seed ++ gs.take j.val
      let w := gs.get j
      w ∉ avail ∧ (∃ a ∈ avail, ∃ b ∈ avail,
        w = a &&& b ∨ w = a ||| b ∨ w = ~~~a)) →
    target ∉ seed ++ gs) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7 := by
  intro C flag fan bound _ _
  let x (i : ℕ) : BitVec 1024 :=
    let l := List.ofFn (fun j : Fin 1024 => j.val.testBit i)
    (BitVec.ofBoolListLE l).cast (List.length_ofFn)
  have base (i : ℕ) (j : Fin 1024) : (x i).getLsbD j.val = j.val.testBit i := by
    simp only [x,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt), List.getElem_ofFn]
  have characterized (i j : ℕ) (hj : j < 1024) : (x i).getLsbD j = j.testBit i := base i ⟨j,hj⟩
  let xs := (List.range 10).map x ++ [if flag then x 0 &&& x 1 else x 0 ||| x 1]
  obtain ⟨gs,v,ls,gen,mem,sim⟩ := liftCircuit 1024 C xs fan
  let T := ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).foldl
    (fun t e => t ||| (x (e/10) &&& x (e%10))) 0
  have diff : v ≠ T := by
    intro h
    apply search flag x characterized gs (ls.trans bound) gen
    change T ∈ xs ++ [0,~~~0] ++ gs
    rw [← h]
    exact mem
  have someBit : ∃ j : Fin 1024, v.getLsbD j.val ≠ T.getLsbD j.val := by
    by_contra! h
    exact diff (BitVec.eq_of_getLsbD_eq (fun i hi => h ⟨i,hi⟩))
  obtain ⟨j,neq⟩ := someBit
  let row (i : Fin 10) := j.val.testBit i.val
  have start : (List.range 10).map (fun i => j.val.testBit i) = List.ofFn row := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro i _ _
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,row]
  have hx : xs.map (fun w => w.getLsbD j.val) =
      List.ofFn row ++ [if flag then row 0 && row 1 else row 0 || row 1] := by
    cases flag <;> simp only [xs,Bool.false_eq_true, ↓reduceIte,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,base,start,BitVec.getLsbD_and,BitVec.getLsbD_or] <;> rfl
  refine ⟨row, ?_⟩
  rw [← hx, ← sim j]
  have zero : (0 : BitVec 1024).getLsbD j.val = false := by simp
  intro e
  apply neq
  rw [e]
  simp only [T,List.foldl_cons,List.foldl_nil,BitVec.getLsbD_or,BitVec.getLsbD_and,zero,Bool.false_or,base,row]
  rfl
