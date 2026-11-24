import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Swap the independent initial gates and use the symmetries of the incidence graph.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 6500000 in
theorem PEqualNP.Outside.R_meta_3275_415
    (known : let edge (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ r ∈ ([(0,1), (0,4), (0,6), (4,6)] : List (Fin 9 × Fin 9)), ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x r.1 && x r.2)) →
        circuitFun 9 C = edge → 16 ≤ C.size)
    (additional : let edge (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ r ∈ ([(0,2), (0,3)] : List (Fin 9 × Fin 9)), ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x r.1 && x r.2)) →
        circuitFun 9 C = edge → 16 ≤ C.size) :
∀ x1 ∈ [((0 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (5 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (8 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (8 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let edge (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
  let raw (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let value (x : Fin 9 → Bool) (i : Fin 12) :=
    if i = 11 then true else (raw x).getD i.val false
  let original : List (Fin 12 × Fin 12) := [(0,1), (0,2), (0,3), (0,4), (0,6), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (1,8), (2,3), (2,4), (2,6), (2,7), (2,8), (3,4), (3,6), (4,6), (6,7)]
  let knownPairs : List (Fin 9 × Fin 9) := [(0,1), (0,4), (0,6), (4,6)]
  let additionalPairs : List (Fin 9 × Fin 9) := [(0,2), (0,3)]
  let perms : List (List (Fin 9)) := [[0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 5, 8, 3, 4, 1, 7, 6, 2], [1, 0, 5, 8, 6, 2, 4, 7, 3], [1, 2, 3, 8, 6, 0, 7, 4, 5], [2, 1, 0, 5, 7, 3, 6, 4, 8], [2, 3, 8, 5, 7, 1, 4, 6, 0], [3, 2, 1, 0, 4, 8, 7, 6, 5], [3, 8, 5, 0, 4, 2, 6, 7, 1], [5, 0, 1, 2, 7, 8, 4, 6, 3], [5, 8, 3, 2, 7, 0, 6, 4, 1], [8, 3, 2, 1, 6, 5, 4, 7, 0], [8, 5, 0, 1, 6, 3, 7, 4, 2]]
  let rho (j : Fin 12) (i : Fin 9) : Fin 9 := (perms.getD j.val []).getD i.val 0
  have form (x : Fin 9 → Bool) :
      edge x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    simp only [edge,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  intro r member C hfan size
  change r ∈ original at member
  change ∃ x, C.eval (raw x ++ [value x r.1 && value x r.2]) ≠ _
  by_contra! equal
  have computes (x : Fin 9 → Bool) :
      C.eval (raw x ++ [value x r.1 && value x r.2]) = edge x := by
    rw [form]
    exact equal x
  have admissible : ∀ r : Fin 12 × Fin 12, r ∈ original →
      r.1.val < 9 ∧ r.2.val < 9 := by decide +kernel
  let route : List (Fin 12 × (Fin 9 × Fin 9)) := [(0,0,1), (0,0,2), (0,0,3), (0,0,4), (0,0,6), (4,0,1), (6,0,2), (2,0,6), (2,0,2), (2,0,4), (8,0,6), (2,0,3), (6,0,1), (11,0,6), (4,0,6), (4,0,4), (10,0,2), (6,0,4), (7,0,6), (0,4,6), (4,4,6)]
  have checked (i : Fin 21) :
      let r := original.getD i.val (0,0)
      let j := (route.getD i.val (0,0,0)).1
      let q := (route.getD i.val (0,0,0)).2
      (q ∈ knownPairs ∨ q ∈ additionalPairs) ∧
        ((rho j (Fin.ofNat 9 r.1.val) = q.1 ∧ rho j (Fin.ofNat 9 r.2.val) = q.2) ∨
          (rho j (Fin.ofNat 9 r.1.val) = q.2 ∧ rho j (Fin.ofNat 9 r.2.val) = q.1)) := by
    have all : ∀ i : Fin 21,
        let r := original.getD i.val (0,0)
        let j := (route.getD i.val (0,0,0)).1
        let q := (route.getD i.val (0,0,0)).2
        (q ∈ knownPairs ∨ q ∈ additionalPairs) ∧
          ((rho j (Fin.ofNat 9 r.1.val) = q.1 ∧ rho j (Fin.ofNat 9 r.2.val) = q.2) ∨
            (rho j (Fin.ofNat 9 r.1.val) = q.2 ∧ rho j (Fin.ofNat 9 r.2.val) = q.1)) := by
      decide +kernel
    exact all i
  have preserves : ∀ (j : Fin 12) (x : Fin 9 → Bool), edge (x ∘ rho j) = edge x := by
    decide +kernel
  obtain ⟨r1,r2⟩ := admissible r member
  obtain ⟨i,hi,found⟩ := List.mem_iff_getElem.mp member
  let index : Fin 21 := ⟨i,by simpa [original] using hi⟩
  let j := (route.getD index.val (0,0,0)).1
  let q := (route.getD index.val (0,0,0)).2
  have pinned : original.getD index.val (0,0) = r :=
    (List.getD_eq_getElem original (0,0) hi).trans found
  have mapped := checked index
  dsimp only at mapped
  rw [pinned] at mapped
  obtain ⟨hq,align⟩ := mapped
  let u : Fin 9 := Fin.ofNat 9 r.1.val
  let v : Fin 9 := Fin.ofNat 9 r.2.val
  have uval : u.val = r.1.val := Nat.mod_eq_of_lt r1
  have vval : v.val = r.2.val := Nat.mod_eq_of_lt r2
  have input (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have firstBit (x : Fin 9 → Bool) : value x r.1 = x u := by
    have h : r.1 ≠ 11 := by intro e; have w := congrArg Fin.val e; change r.1.val=11 at w; omega
    rw [show value x r.1 = (raw x).getD r.1.val false by simp [value,h],←uval]
    rw [show raw x = (List.ofFn x) ++ [!x 0] from rfl,List.getD_append _ _ _ _ (by simp)]
    exact input x u
  have secondBit (x : Fin 9 → Bool) : value x r.2 = x v := by
    have h : r.2 ≠ 11 := by intro e; have w := congrArg Fin.val e; change r.2.val=11 at w; omega
    rw [show value x r.2 = (raw x).getD r.2.val false by simp [value,h],←vval]
    rw [show raw x = (List.ofFn x) ++ [!x 0] from rfl,List.getD_append _ _ _ _ (by simp)]
    exact input x v
  have aligns (x : Fin 9 → Bool) :
      (x (rho j u) && x (rho j v)) = (x q.1 && x q.2) := by
    rcases align with h | h
    · rw [show rho j u = q.1 from h.1,show rho j v = q.2 from h.2]
    · rw [show rho j u = q.2 from h.1,show rho j v = q.1 from h.2,Bool.and_comm]
  let move (i : ℕ) : ℕ :=
    if h : i < 9 then (rho j ⟨i,h⟩).val else if i = 9 then 10 else if i = 10 then 9 else i
  have m9 : move 9 = 10 := rfl
  have m10 : move 10 = 9 := rfl
  have high (i : ℕ) (hi : 11 ≤ i) : move i = i := by
    simp [move,dite_eq_right (by omega : ¬ i<9),show i≠9 by omega,show i≠10 by omega]
  have small (i : ℕ) (hi : i < 11) : move i < 11 := by
    by_cases raw : i < 9
    · rw [show move i = (rho j ⟨i,raw⟩).val from dite_eq_left raw]
      exact (rho j ⟨i,raw⟩).isLt.trans (by decide)
    · have e : i=9 ∨ i=10 := by omega
      rcases e with rfl | rfl <;> simp [m9,m10]
  let relabel (g : Gate) : Gate := ⟨g.op,g.inputs.map move⟩
  let g0 : Gate := ⟨.and,[q.1.val,q.2.val]⟩
  let g1 : Gate := ⟨.not,[(rho j 0).val]⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let D : Circuit := ⟨g0::g1::C.gates.map relabel,move C.output⟩
  have dFan : FanInTwo D := by
    intro g hg
    change g ∈ g0::g1::C.gates.map relabel at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [g0]
    · rcases List.mem_cons.mp hg with rfl | hg
      · simp [g1]
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
        exact ⟨(hfan z hz).1,by simpa only [relabel,List.length_map] using (hfan z hz).2⟩
  have dSize : D.size ≤ 15 := by
    change (g0::g1::C.gates.map relabel).length ≤ 15
    simp only [List.length_cons,List.length_map]
    exact Nat.add_le_add_right size 2
  have step0 (x : Fin 9 → Bool) : step (List.ofFn x) g0 =
      List.ofFn x ++ [x q.1 && x q.2] := by
    change List.ofFn x ++ [((List.ofFn x).getD q.1.val false &&
      ((List.ofFn x).getD q.2.val false && true))] = _
    rw [input x q.1,input x q.2,Bool.and_true]
  have step1 (x : Fin 9 → Bool) :
      step (List.ofFn x ++ [x q.1 && x q.2]) g1 =
      List.ofFn x ++ [x q.1 && x q.2, !x (rho j 0)] := by
    change (List.ofFn x ++ [x q.1 && x q.2]) ++
      [!((List.ofFn x ++ [x q.1 && x q.2]).getD (rho j 0).val false)] = _
    rw [List.getD_append _ _ _ _ (by simp),input x (rho j 0),List.append_assoc]
    rfl
  have retained (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons a gs ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have headGood (x : Fin 9 → Bool) :
      (D.wires (List.ofFn x)).getD 9 false = (x q.1 && x q.2) := by
    change ((g0::g1::C.gates.map relabel).foldl step (List.ofFn x)).getD 9 false = _
    simp only [List.foldl_cons,step0,step1]
    rw [retained _ _ 9 (by simp),List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
    rfl
  let agree (w z : List Bool) := w.length = z.length ∧ 11 ≤ w.length ∧
    ∀ i, w.getD i false = z.getD (move i) false
  have save (w z : List Bool) (a : Bool) (h : agree w z) : agree (w++[a]) (z++[a]) := by
    obtain ⟨len,lower,same⟩ := h
    refine ⟨by simp [len],by simp; omega,fun i => ?_⟩
    by_cases raw : i < 11
    · rw [List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by have := small i raw; omega)]
      exact same i
    · rw [high i (by omega)]
      by_cases inside : i < w.length
      · rw [List.getD_append _ _ _ _ inside,List.getD_append _ _ _ _ (by omega)]
        simpa only [high i (by omega)] using same i
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),len]
  have run (gs : List Gate) (w z : List Bool) (h : agree w z) :
      agree (gs.foldl step w) ((gs.map relabel).foldl step z) := by
    induction gs generalizing w z with
    | nil => exact h
    | cons a gs ih =>
      change agree (gs.foldl step (step w a))
        ((gs.map relabel).foldl step (step z (relabel a)))
      apply ih
      have operands : (a.inputs.map fun i => w.getD i false) =
          ((relabel a).inputs.map fun i => z.getD i false) := by
        change _ = (a.inputs.map move).map (fun i => z.getD i false)
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => h.2.2 i)
      unfold step
      rw [operands]
      exact save w z _ h
  have correctness : circuitFun 9 D = edge := by
    funext x
    let y := x ∘ rho j
    let w := List.ofFn y ++ [!y 0,x q.1 && x q.2]
    let z := List.ofFn x ++ [x q.1 && x q.2,!y 0]
    have exactRow : raw y ++ [value y r.1 && value y r.2] = w := by
      rw [firstBit,secondBit]
      change (List.ofFn y ++ [!y 0]) ++ [x (rho j u) && x (rho j v)] = _
      rw [aligns,List.append_assoc]
      rfl
    have init : agree w z := by
      refine ⟨by simp [w,z],by simp [w],?_⟩
      intro i
      by_cases raw : i < 9
      · let k : Fin 9 := ⟨i,raw⟩
        rw [show move i = (rho j k).val from dite_eq_left raw]
        unfold w z
        rw [List.getD_append _ _ _ _ (by simpa using raw),
          List.getD_append _ _ _ _ (by simp)]
        exact (input y k).trans (input x (rho j k)).symm
      · by_cases lo : i=9
        · subst i
          simp [w,z,m9]
        · by_cases hi : i=10
          · subst i
            simp [w,z,m10]
          · have h : 11 ≤ i := by omega
            rw [high i h,List.getD_eq_default _ _ (by simpa [w] using h),
              List.getD_eq_default _ _ (by simpa [z] using h)]
    have e := (run C.gates w z init).2.2 C.output
    have old : C.eval w = edge x := by rw [← exactRow,computes]; exact preserves j x
    change ((g0::g1::C.gates.map relabel).foldl step (List.ofFn x)).getD (move C.output) false = edge x
    simp only [List.foldl_cons,step0,step1]
    exact e.symm.trans old
  have lower : 16 ≤ D.size := by
    rcases hq with h | h
    · exact known q h D dFan headGood correctness
    · exact additional q h D dFan headGood correctness
  omega
