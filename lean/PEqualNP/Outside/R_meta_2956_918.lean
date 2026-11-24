import PEqualNP.Defs

-- The tail count uses the two-position replacement argument from PR 6019.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2956_918 :
    (∀ B : Circuit, FanInTwo B → circuitFun 9 B = (fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      13 ≤ B.gates.countP (fun a => !(a.op.eval [false,false]))) →
    (∀ D : Circuit, FanInTwo D → D.gates.countP (fun a => !(a.op.eval [false,false])) ≤ 12 →
      (∀ x : Fin 10 → Bool, x 9 = (x 0 || x 2) → circuitFun 10 D x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      (∀ i : Fin 10, ∃ p q : Fin 10 → Bool, (∀ j, j ≠ i → p j = q j) ∧
        circuitFun 10 D p ≠ circuitFun 10 D q) →
      (∀ (i : Fin 10) (b : Bool), ∃ p q : Fin 10 → Bool, p i = b ∧ q i = b ∧
        circuitFun 10 D p ≠ circuitFun 10 D q) → False) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.gates.length = (15 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x4 : Fin x1.gates.length) (x5 : Fin x1.gates.length), x4 < x5 ∧ (4 : ℕ) ≤ ↑x4 ∧ ↑x4 ≤ (7 : ℕ) ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x1.gates.length), (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (PEqualNP.MetaComplexity.tableIndex x6 / (64 : ℕ)) (0 : ℕ)).testBit (PEqualNP.MetaComplexity.tableIndex x6 % (64 : ℕ)) := by
  intro hBound excluded C hlen hfan hNOT first
  by_contra! correct
  obtain ⟨u,v,ord,lo,_,hu,hv,_⟩ := hNOT
  let F : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let plug (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := Fin.lastCases b x
  let runStep (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let binary (gs : List Gate) := gs.countP (fun g => !(g.op.eval [false,false]))
  let embed (x : Fin 9 → Bool) := plug x (x 0 || x 2)
  let maskBits (m : Nat) (j : Fin 9) := m.testBit j.val
  have hfun : circuitFun 9 C = F := by
    have packed (x : Fin 9 → Bool) :
        F x = ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (tableIndex x / 64) 0).testBit
          (tableIndex x % 64) := by
      revert x
      decide +kernel
    funext x
    exact (correct x).trans (packed x).symm
  have getFromPrefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl runStep w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl runStep (runStep w g)).getD i false = w.getD i false
      rw [ih _ (by simp [runStep]; omega)]
      exact List.getD_append _ _ _ _ hi
  have plug_list (x : Fin 9 → Bool) (b : Bool) :
      List.ofFn (plug x b) = List.ofFn x ++ [b] := by
    rw [List.ofFn_succ_last]
    simp [plug]
    rfl

  let before : Fin 9 → ℕ := ![20,1,9,4,1,1,2,4,8]
  let after : Fin 9 → ℕ := ![21,3,13,12,17,33,66,132,264]

  have rawPairs : ∀ i : Fin 9, let a := maskBits (before i); let b := maskBits (after i)
      (∀ j : Fin 10, j ≠ i.castSucc → embed a j = embed b j) ∧ F a ≠ F b := by decide +kernel

  have twoNot (gs : List Gate) (i j : Fin gs.length) (hne : i ≠ j)
      (hi : (gs.get i).op = .not) (hj : (gs.get j).op = .not) : binary gs + 2 ≤ gs.length := by
    let g : Gate := ⟨.and, []⟩
    let first := gs.set i.val g
    have ij : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hj' : j.val < first.length := by simp [first]
    have unchanged : first[j.val].op = .not := by
      rw [show first[j.val] = gs[j.val] from List.getElem_set_ne ij hj']
      exact hj
    have zg : (!g.op.eval [false,false]) = true := rfl
    have zn : (!GateOp.not.eval [false,false]) = false := rfl
    have c1 : binary first = binary gs + 1 := by
      have e : (!gs[i.val].op.eval [false,false]) = false := by
        rw [← List.get_eq_getElem, hi]
        exact zn
      simp only [binary, first, List.countP_set i.isLt, e, zg, ite_true, Bool.false_eq_true, ite_false, Nat.sub_zero]
    have c2 : binary (first.set j.val g) = binary first + 1 := by
      have e : (!first[j.val].op.eval [false,false]) = false := by
        rw [unchanged]
        exact zn
      simp only [binary, List.countP_set hj', e, zg, ite_true, Bool.false_eq_true, ite_false, Nat.sub_zero]
    have h : binary (first.set j.val g) ≤ (first.set j.val g).length := List.countP_le_length
    rw [c2,c1,List.length_set,show first.length = gs.length from List.length_set] at h
    omega

  let cofactorNo (i : Fin 10) (b : Bool) : Nat :=
    if b then ![1,2,4,8,16,32,64,128,256,1] i else ![0,0,0,0,0,0,0,0,0,0] i

  let cofactorYes (i : Fin 10) (b : Bool) : Nat :=
    if b then ![3,3,6,11,17,33,66,131,259,3] i else ![6,12,3,3,3,3,3,3,3,24] i

  have cofactorPairs : ∀ (i : Fin 10) (b : Bool),
      let p := maskBits (cofactorNo i b)
      let q := maskBits (cofactorYes i b)
      embed p i = b ∧ embed q i = b ∧ F p ≠ F q := by decide +kernel
  rcases C with ⟨gs,out⟩
  cases gs with
  | nil => exact Fin.elim0 u
  | cons g gs =>
    let D : Circuit := ⟨gs,out⟩
    have hfd : FanInTwo D := fun a ha => hfan a (List.mem_cons_of_mem _ ha)
    have pos : 0 < u.val := by omega
    have hb : binary gs ≤ 12 := by
      have iu : u.val < (g :: gs).length := u.isLt
      have iv : v.val < (g :: gs).length := v.isLt
      have huv : u.val < v.val := ord
      simp only [List.length_cons] at iu iv
      let i : Fin gs.length := ⟨u.val - 1, by omega⟩
      let j : Fin gs.length := ⟨v.val - 1, by omega⟩
      have getTail (v : Fin (g :: gs).length) (a : Fin gs.length) (ha : v.val = a.val + 1) :
          (g :: gs).get v = gs.get a := by simp [List.get_eq_getElem, ha]
      have hi : (gs.get i).op = .not := by rwa [← getTail u i (by dsimp [i]; omega)]
      have hj : (gs.get j).op = .not := by rwa [← getTail v j (by dsimp [j]; omega)]
      have ne : i ≠ j := fun e => by have h := congrArg Fin.val e; dsimp [i,j] at h; omega
      have bound := twoNot gs i j ne hi hj
      change (g :: gs).length = 15 at hlen
      simp only [List.length_cons] at hlen
      omega
    have seed (x : Fin 9 → Bool) : runStep (List.ofFn x) g = List.ofFn (embed x) := by
      let val := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
      have h := first x
      change (gs.foldl runStep (List.ofFn x ++ [val])).getD 9 false = _ at h
      rw [getFromPrefix gs _ _ (by simp)] at h
      have v : val = (x 0 || x 2) := by simpa [List.getD_eq_getElem?_getD] using h
      change runStep (List.ofFn x) g = List.ofFn (plug x (x 0 || x 2))
      rw [plug_list]
      exact congrArg (fun b => List.ofFn x ++ [b]) v
    have valid (x : Fin 9 → Bool) : circuitFun 10 D (embed x) = F x := by
      have hx := congrFun hfun x
      change (gs.foldl runStep (runStep (List.ofFn x) g)).getD out false = F x at hx
      rw [seed] at hx
      exact hx
    apply excluded D hfd hb
    · intro x hx
      have heq : embed (fun i : Fin 9 => x i.castSucc) = x := by
        funext j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · change Fin.lastCases (motive := fun _ => Bool) (x 0 || x 2) (fun i : Fin 9 => x i.castSucc) (Fin.last 9) = x 9
          rw [Fin.lastCases_last]
          exact hx.symm
        · simp [embed, plug]
      have agree := valid (fun i : Fin 9 => x i.castSucc)
      rw [heq] at agree
      exact agree
    · intro i
      by_cases hlt : i.val < 9
      · let v : Fin 9 := ⟨i.val,hlt⟩
        have hi : i = v.castSucc := Fin.ext rfl
        obtain ⟨hp,hd⟩ := rawPairs v
        exact ⟨embed (maskBits (before v)), embed (maskBits (after v)), by simpa only [hi] using hp,
          by simpa only [valid] using hd⟩
      · have last : i = Fin.last 9 := Fin.ext (by have := i.isLt; change i.val = 9; omega)
        subst i
        by_contra! hind
        let a : Gate := ⟨.not,[0]⟩
        let E : Circuit := ⟨a :: gs,out⟩
        have fan : FanInTwo E := by
          intro q hq
          change q ∈ a :: gs at hq
          rcases List.mem_cons.mp hq with rfl | hmem
          · simp [a]
          · exact hfd q hmem
        have start (x : Fin 9 → Bool) : runStep (List.ofFn x) a = List.ofFn (plug x (!x 0)) := by
          rw [plug_list]
          have input : (List.ofFn x).getD 0 false = x 0 := by simp [List.getD_eq_getElem?_getD]
          change List.ofFn x ++ [GateOp.not.eval [(List.ofFn x).getD 0 false]] = _
          rw [input]
          rfl
        have he (x : Fin 9 → Bool) : circuitFun 9 E x = F x := by
          have hx := hind (plug x (!x 0)) (embed x) (by
            intro j hj
            refine Fin.lastCases ?_ (fun j => ?_) j hj
            · exact fun h => (h rfl).elim
            · simp [embed,plug])
          change (gs.foldl runStep (runStep (List.ofFn x) a)).getD out false = F x
          rw [start]
          exact hx.trans (valid x)
        have bad := hBound E fan (funext he)
        change 13 ≤ binary (a :: gs) at bad
        have same : binary (a :: gs) = binary gs := by unfold binary; rw [List.countP_cons]; rfl
        rw [same] at bad
        omega
    · intro i b
      obtain ⟨hp,hq,hf⟩ := cofactorPairs i b
      exact ⟨embed (maskBits (cofactorNo i b)), embed (maskBits (cofactorYes i b)),
        hp, hq, by simpa only [valid] using hf⟩
