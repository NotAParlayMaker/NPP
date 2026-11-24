import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reflect the graph while preserving the first OR, and identify equivalent second gates.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3020_418
    (orbit : let codes : List ℕ := [0, 1, 2, 4, 5, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 26, 27, 29, 31, 32, 49, 50, 51, 52, 53, 54, 62, 63, 64, 65, 86, 87, 109]
      let decode (n : ℕ) : List (Fin 11) := if n = 0 then [] else
        if n < 12 then [Fin.ofNat 11 (n-1)] else
        [Fin.ofNat 11 ((n-12)/11),Fin.ofNat 11 ((n-12)%11)]
      let first (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]
      let second (p : List (Fin 11)) (x : Fin 9 → Bool) :=
        GateOp.and.eval (p.map fun i => (first x).getD i.val false)
      let flip (j : Fin 9) : Fin 9 := ([2,1,0,5,7,3,6,4,8] : List (Fin 9)).getD j.val 0
      ∀ (p : List (Fin 11)), p.length ≤ 2 →
        ∃ n ∈ codes, ∃ b : Bool, ∀ x : Fin 9 → Bool,
          second p (if b then x ∘ flip else x) = second (decode n) x)
    (binary : let edge (x : Fin 9 → Bool) : Bool := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : Circuit, FanInTwo C → C.gates.countP (fun g => !(g.op.eval [false])) ≤ 12 →
        ∃ x, C.eval (List.ofFn x) ≠ edge x)
    (finite : let codes : List ℕ := [0, 1, 2, 4, 5, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 26, 27, 29, 31, 32, 49, 50, 51, 52, 53, 54, 62, 63, 64, 65, 86, 87, 109]
      let decode (n : ℕ) : List (Fin 11) := if n = 0 then [] else
        if n < 12 then [Fin.ofNat 11 (n-1)] else
        [Fin.ofNat 11 ((n-12)/11),Fin.ofNat 11 ((n-12)%11)]
      let first (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]
      let second (p : List (Fin 11)) (x : Fin 9 → Bool) :=
        GateOp.and.eval (p.map fun i => (first x).getD i.val false)
      let edge (x : Fin 9 → Bool) : Bool := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ n ∈ codes, ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        C.gates.countP (fun g => g.op.eval [false]) ≤ 2 →
        ∃ x, C.eval (first x ++ [second (decode n) x]) ≠ edge x) :
∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let codes : List ℕ := [0, 1, 2, 4, 5, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 26, 27, 29, 31, 32, 49, 50, 51, 52, 53, 54, 62, 63, 64, 65, 86, 87, 109]
  let decode (n : ℕ) : List (Fin 11) := if n = 0 then [] else
    if n < 12 then [Fin.ofNat 11 (n-1)] else
    [Fin.ofNat 11 ((n-12)/11),Fin.ofNat 11 ((n-12)%11)]
  let first (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]
  let second (p : List (Fin 11)) (x : Fin 9 → Bool) :=
    GateOp.and.eval (p.map fun i => (first x).getD i.val false)
  let edge (x : Fin 9 → Bool) : Bool := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let flip (j : Fin 9) : Fin 9 := ([2,1,0,5,7,3,6,4,8] : List (Fin 9)).getD j.val 0
  let neg (g : Gate) : Bool := g.op.eval [false]
  have format (x : Fin 9 → Bool) :
      edge x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    simp only [edge,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  intro pins hlen C hfan hs
  by_contra! hit
  have computes (x : Fin 9 → Bool) : C.eval (first x ++ [second pins x]) = edge x := by
    rw [format]
    exact not_not.mp (hit x)
  let g0 : Gate := ⟨.or,[0,2]⟩
  let g1 : Gate := ⟨.and,pins.map Fin.val⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have stepFirst (x : Fin 9 → Bool) : step (List.ofFn x) g0 = first x := by
    have eq : ∀ x : Fin 9 → Bool,
        (List.ofFn x).getD 0 false = x 0 ∧ (List.ofFn x).getD 2 false = x 2 := by decide +kernel
    rcases eq x with ⟨h0,h2⟩
    change List.ofFn x ++ [(List.ofFn x).getD 0 false || ((List.ofFn x).getD 2 false || false)] = _
    rw [h0,h2,Bool.or_false]
  have stepSecond (x : Fin 9 → Bool) : step (first x) g1 = first x ++ [second pins x] := by
    change first x ++ [GateOp.and.eval ((pins.map Fin.val).map _)] = _
    rw [List.map_map]
    rfl
  by_cases allowed : C.gates.countP neg ≤ 2
  · obtain ⟨n,hn,b,matched⟩ := orbit pins hlen
    let perm (i : Fin 9) := if b then flip i else i
    let move (i : ℕ) := if h : i < 9 then (perm ⟨i,h⟩).val else i
    have small (i : ℕ) (h : i < 9) : move i < 9 := by
      simp only [move,dite_eq_left h]
      exact (perm ⟨i,h⟩).isLt
    have other (i : ℕ) (h : 9 ≤ i) : move i = i := dite_eq_right (by omega)
    let relabel (g : Gate) : Gate := ⟨g.op,g.inputs.map move⟩
    have keepNeg (l : List Gate) : (l.map relabel).countP neg = l.countP neg := by
      induction l with
      | nil => rfl
      | cons g l ih =>
        simp only [List.map_cons,List.countP_cons,ih]
        rfl
    let D : Circuit := ⟨C.gates.map relabel,move C.output⟩
    have dFan : FanInTwo D := by
      intro d hd
      change d ∈ C.gates.map relabel at hd
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hd
      exact ⟨(hfan a ha).1,by simpa only [relabel,List.length_map] using (hfan a ha).2⟩
    have dSize : D.size ≤ 13 := by
      change (C.gates.map relabel).length ≤ 13
      rw [List.length_map]
      exact hs
    have dNeg : D.gates.countP neg ≤ 2 := by
      change (C.gates.map relabel).countP neg ≤ 2
      rwa [keepNeg]
    obtain ⟨x,fail⟩ := finite n hn D dFan dSize dNeg
    let agree (w v : List Bool) := w.length = v.length ∧ 9 ≤ w.length ∧
      ∀ i, w.getD i false = v.getD (move i) false
    have save (w v : List Bool) (t : Bool) (h : agree w v) :
        agree (w ++ [t]) (v ++ [t]) := by
      obtain ⟨len,lower,same⟩ := h
      refine ⟨by simp [len],by simp; omega,fun i => ?_⟩
      by_cases raw : i < 9
      · rw [List.getD_append _ _ _ _ (by omega),
          List.getD_append _ _ _ _ (by have := small i raw; omega)]
        exact same i
      · rw [other i (by omega)]
        by_cases inside : i < w.length
        · rw [List.getD_append _ _ _ _ inside,List.getD_append _ _ _ _ (by omega)]
          simpa only [other i (by omega)] using same i
        · rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega),len]
    have run (gs : List Gate) (w v : List Bool) (h : agree w v) :
        agree (gs.foldl step w) ((gs.map relabel).foldl step v) := by
      induction gs generalizing w v with
      | nil => exact h
      | cons g gs ih =>
        change agree (gs.foldl step (step w g))
          ((gs.map relabel).foldl step (step v (relabel g)))
        apply ih
        have operands : (g.inputs.map fun i => w.getD i false) =
            ((relabel g).inputs.map fun i => v.getD i false) := by
          change _ = (g.inputs.map move).map (fun i => v.getD i false)
          rw [List.map_map]
          exact List.map_congr_left (fun i _ => h.2.2 i)
        unfold step
        rw [operands]
        exact save w v _ h
    let y : Fin 9 → Bool := x ∘ perm
    have firstSym : ∀ b : Bool, ∀ x : Fin 9 → Bool,
        ((if b then x ∘ flip else x) 0 || (if b then x ∘ flip else x) 2) = (x 0 || x 2) := by
      decide +kernel
    have edgeSym : ∀ b : Bool, ∀ x : Fin 9 → Bool,
        edge (if b then x ∘ flip else x) = edge x := by decide +kernel
    have y_eq : y = (if b then x ∘ flip else x) := by
      cases b <;> rfl
    have lastEq : second pins y = second (decode n) x := by
      rw [y_eq]
      exact matched x
    have firstEq : (y 0 || y 2) = (x 0 || x 2) := by
      rw [y_eq]
      exact firstSym b x
    have init (u : List Bool) : agree (List.ofFn y ++ u) (List.ofFn x ++ u) := by
      refine ⟨by simp,by simp,fun i => ?_⟩
      by_cases h : i < 9
      · let j : Fin 9 := ⟨i,h⟩
        rw [List.getD_append _ _ _ _ (by simpa using h),
          List.getD_append _ _ _ _ (by simpa using small i h)]
        change (List.ofFn y).getD j.val false = (List.ofFn x).getD (move j.val) false
        have jval : move j.val = (perm j).val := dite_eq_left h
        rw [jval,List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simp),
          List.getElem_ofFn,List.getElem_ofFn]
        rfl
      · rw [other i (by omega),List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,List.length_ofFn]
    have rowAgree : agree (first y ++ [second pins y]) (first x ++ [second (decode n) x]) := by
      simp only [first,List.append_assoc,List.singleton_append,firstEq,lastEq]
      exact init _
    have eq := (run C.gates _ _ rowAgree).2.2 C.output
    change C.eval (first y ++ [second pins y]) = D.eval (first x ++ [second (decode n) x]) at eq
    have sameEdge : edge y = edge x := by rw [y_eq]; exact edgeSym b x
    exact fail (eq.symm.trans ((computes y).trans sameEdge))
  · let D : Circuit := ⟨g0::g1::C.gates,C.output⟩
    have dFan : FanInTwo D := by
      intro g hg
      change g ∈ g0::g1::C.gates at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [g0]
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨by simp [g1],by simpa [g1] using hlen⟩
        · exact hfan g hg
    have parts (l : List Gate) : l.countP (fun g => !neg g) + l.countP neg = l.length := by
      induction l with
      | nil => rfl
      | cons g l ih =>
        simp only [List.countP_cons,List.length_cons]
        cases neg g <;> simp <;> omega
    have lower : D.gates.countP (fun g => !(g.op.eval [false])) ≤ 12 := by
      change (g0::g1::C.gates).countP (fun g => !neg g) ≤ 12
      simp only [List.countP_cons]
      have h0 : neg g0 = false := rfl
      have h1 : neg g1 = false := rfl
      simp only [h0,h1,Bool.not_false,ite_true]
      have count := parts C.gates
      change C.gates.length ≤ 13 at hs
      omega
    obtain ⟨x,fail⟩ := binary D dFan lower
    apply fail
    change (C.gates.foldl step (step (step (List.ofFn x) g0) g1)).getD C.output false = _
    rw [stepFirst,stepSecond]
    exact computes x
