import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3083_1
    (binaryBound :
      let F (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      ∀ C : Circuit, FanInTwo C → circuitFun 9 C = F →
        13 + C.gates.countP (fun g => g.op.eval [false]) ≤ C.size)
    (suffixBound :
      let F (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
        2 ≤ D.gates.countP (fun g => g.op.eval [false]) →
        (∃ j : Fin D.gates.length, j.val ≤ 2 ∧ (D.gates.get j).op = .not) →
        (∀ x : Fin 10 → Bool, x 9 = (x 0 || x 2) →
          circuitFun 10 D x = F (fun i : Fin 9 => x i.castSucc)) →
        (∀ i : Fin 10, ∃ x y : Fin 10 → Bool,
          (∀ j, j ≠ i → x j = y j) ∧ circuitFun 10 D x ≠ circuitFun 10 D y) →
        (∀ (i : Fin 10) (b : Bool), ∃ x y : Fin 10 → Bool,
          circuitFun 10 D (Function.update x i b) ≠ circuitFun 10 D (Function.update y i b)) → False) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x2.gates.length) (x5 : Fin x2.gates.length), x4 < x5 ∧ ↑x4 ≤ (3 : ℕ) ∧ (x2.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) → (16 : ℕ) ≤ x2.size := by
  dsimp only
  intro C hfan hnots hfirst hcorrect _
  by_contra! hsmall
  let F (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  have hfun : circuitFun 9 C = F := hcorrect
  let plug (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := Fin.lastCases b x
  let embed (x : Fin 9 → Bool) : Fin 10 → Bool := plug x (x 0 || x 2)
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hplug (x : Fin 9 → Bool) (b : Bool) : List.ofFn (plug x b) = List.ofFn x ++ [b] := by
    rw [List.ofFn_succ_last]
    simp [plug]
    rfl
  rcases C with ⟨gs, out⟩
  obtain ⟨i, j, hij, hearly, hi, hj, _⟩ := hnots
  cases gs with
  | nil => exact Fin.elim0 i
  | cons g tail =>
    have seed (x : Fin 9 → Bool) : step (List.ofFn x) g = List.ofFn (embed x) := by
      have hf := hfirst x
      change ((tail.foldl step (step (List.ofFn x) g)).getD 9 false) = (x 0 || x 2) at hf
      have keep (ts : List Gate) (w : List Bool) (hw : 9 < w.length) :
          (ts.foldl step w).getD 9 false = w.getD 9 false := by
        induction ts generalizing w with
        | nil => rfl
        | cons a ts ih =>
          rw [List.foldl_cons, ih]
          · rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ hw]
            exact List.getElem_append_left hw
          · simp [step]; omega
      rw [keep tail (step (List.ofFn x) g) (by simp [step])] at hf
      have hg : g.op.eval (g.inputs.map fun k => (List.ofFn x).getD k false) = (x 0 || x 2) := by
        simpa [step, List.getD] using hf
      change step (List.ofFn x) g = List.ofFn (plug x (x 0 || x 2))
      rw [hplug]
      exact congrArg (fun bit => List.ofFn x ++ [bit]) hg
    have gNot : g.op ≠ .not := by
      intro hnot
      let xs := List.ofFn (fun _ : Fin 9 => false)
      have hzero : step xs g = xs ++ [false] := by
        simpa only [xs, embed, hplug, Bool.false_or] using seed (fun _ => false)
      have hval := (List.cons.inj (List.append_cancel_left hzero)).1
      have getZero (i : ℕ) : (xs[i]?).getD false = false := by
        simp only [xs, List.getElem?_ofFn]
        split <;> rfl
      cases hargs : g.inputs <;> simp [hnot, hargs, GateOp.eval, getZero] at hval
    have hiPos : 0 < i.val := by
      by_contra! h
      have : i.val = 0 := by omega
      exact gNot (by simpa [List.get_eq_getElem, this] using hi)
    have hjPos : 0 < j.val := lt_trans hiPos hij
    let a : Fin tail.length := ⟨i.val - 1, by have := i.isLt; simp only [List.length_cons] at this; omega⟩
    let b : Fin tail.length := ⟨j.val - 1, by have := j.isLt; simp only [List.length_cons] at this; omega⟩
    have ha : (tail.get a).op = .not := by
      have hx : a.succ = i := Fin.ext (by simp [a]; omega)
      change ((g :: tail).get i).op = .not at hi
      simpa only [← hx, List.get_cons_succ'] using hi
    have hb : (tail.get b).op = .not := by
      have hx : b.succ = j := Fin.ext (by simp [b]; omega)
      change ((g :: tail).get j).op = .not at hj
      simpa only [← hx, List.get_cons_succ'] using hj
    have hlt : a < b := by
      change i.val - 1 < j.val - 1
      have : i.val < j.val := hij
      omega
    have hcount : 2 ≤ tail.countP (fun g => g.op.eval [false]) := by
      have two (l : List Gate) (a b : ℕ) (ha : a < l.length) (hb : b < l.length) (hab : a < b)
          (pa : l[a].op = .not) (pb : l[b].op = .not) : 2 ≤ l.countP (fun g => g.op.eval [false]) := by
        let l' := l.set a ⟨.or, []⟩
        have hb' : b < l'.length := by simpa [l'] using hb
        have pb' : (l'[b]).op = .not := by
          simpa [l', List.getElem_set_ne (Nat.ne_of_lt hab)] using pb
        have nezero : 1 ≤ l'.countP (fun g => g.op.eval [false]) := by
          apply Nat.one_le_iff_ne_zero.mpr
          intro z
          have all := List.countP_eq_zero.mp z
          have yes := all l'[b] (List.getElem_mem hb')
          simp [pb', GateOp.eval] at yes
        have wasNot : l[a].op.eval [false] = true := by rw [pa]; rfl
        have isOr : (⟨.or, []⟩ : Gate).op.eval [false] = false := rfl
        have countDiff := List.countP_set (p := fun g : Gate => g.op.eval [false])
          (a := (⟨.or, []⟩ : Gate)) ha
        change l'.countP (fun g => g.op.eval [false]) = _ at countDiff
        simp only [wasNot, isOr, ite_true, Bool.false_eq_true, ite_false, Nat.add_zero] at countDiff
        omega
      exact two tail a.val b.val a.isLt b.isLt hlt ha hb
    let D : Circuit := ⟨tail, out⟩
    have hD : FanInTwo D := fun q hq => hfan q (List.mem_cons_of_mem _ hq)
    have hlen : D.size ≤ 14 := by
      change (g :: tail).length < 16 at hsmall
      change tail.length ≤ 14
      simp only [List.length_cons] at hsmall
      omega
    have early : a.val ≤ 2 := by dsimp [a]; omega
    have agree (x : Fin 9 → Bool) : circuitFun 10 D (embed x) = F x := by
      have hx := congrFun hfun x
      change (tail.foldl step (step (List.ofFn x) g)).getD out false = F x at hx
      rw [seed x] at hx
      exact hx
    have agree10 (x : Fin 10 → Bool) (hx : x 9 = (x 0 || x 2)) :
        circuitFun 10 D x = F (fun i : Fin 9 => x i.castSucc) := by
      have he : embed (fun i : Fin 9 => x i.castSucc) = x := by
        funext k
        refine Fin.lastCases ?_ (fun i => ?_) k
        · exact hx.symm
        · simp [embed, plug]
      exact he ▸ agree (fun i : Fin 9 => x i.castSucc)
    let bits (m : ℕ) (i : Fin 9) := m.testBit i.val
    let before : Fin 9 → ℕ := ![20, 1, 9, 4, 1, 1, 2, 4, 8]
    let after : Fin 9 → ℕ := ![21, 3, 13, 12, 17, 33, 66, 132, 264]
    have raw : ∀ i : Fin 9, let p := bits (before i); let q := bits (after i)
        (∀ j : Fin 10, j ≠ i.castSucc → embed p j = embed q j) ∧ F p ≠ F q := by
      decide +kernel
    have essential (k : Fin 10) : ∃ x y : Fin 10 → Bool,
        (∀ j, j ≠ k → x j = y j) ∧ circuitFun 10 D x ≠ circuitFun 10 D y := by
      by_cases h : k.val < 9
      · let i : Fin 9 := ⟨k.val, h⟩
        have eq : k = i.castSucc := Fin.ext rfl
        obtain ⟨hp, hq⟩ := raw i
        exact ⟨embed (bits (before i)), embed (bits (after i)), by simpa only [eq] using hp,
          by simpa only [agree] using hq⟩
      · have eq : k = Fin.last 9 := Fin.ext (by have := k.isLt; change k.val = 9; omega)
        subst k
        by_contra! ind
        let negate : Gate := ⟨.not, [0]⟩
        let E : Circuit := ⟨negate :: tail, out⟩
        have fanE : FanInTwo E := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | ht
          · simp [negate]
          · exact hD q ht
        have start (x : Fin 9 → Bool) : step (List.ofFn x) negate = List.ofFn (plug x (!x 0)) := by
          rw [hplug]
          simp [step, negate, GateOp.eval, List.getD]
        have eqE : circuitFun 9 E = F := by
          funext x
          have eq := ind (plug x (!x 0)) (embed x) (by
            intro j hj
            refine Fin.lastCases ?_ (fun i => ?_) j hj
            · exact fun h => (h rfl).elim
            · simp [plug, embed])
          change (tail.foldl step (step (List.ofFn x) negate)).getD out false = F x
          rw [start]
          exact eq.trans (agree x)
        have hE := binaryBound E fanE eqE
        change 13 + (negate :: tail).countP (fun g => g.op.eval [false]) ≤ (negate :: tail).length at hE
        have hn : negate.op.eval [false] = true := rfl
        simp only [List.countP_cons, hn, ite_true, List.length_cons] at hE
        change tail.length ≤ 14 at hlen
        omega
    let zeroRows (i : Fin 10) (b : Bool) := if b then ![1, 2, 4, 8, 16, 32, 64, 128, 256, 1] i else ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0] i
    let oneRows (i : Fin 10) (b : Bool) := if b then ![3, 3, 6, 11, 17, 33, 66, 131, 259, 3] i else ![6, 12, 3, 3, 3, 3, 3, 3, 3, 24] i
    have rows : ∀ (i : Fin 10) (b : Bool),
        let x := bits (zeroRows i b); let y := bits (oneRows i b)
        embed x i = b ∧ embed y i = b ∧ F x ≠ F y := by
      decide +kernel
    apply suffixBound D hD hlen hcount ⟨a, early, ha⟩ agree10 essential
    intro i b
    let x := bits (zeroRows i b)
    let y := bits (oneRows i b)
    obtain ⟨hx, hy, hf⟩ := rows i b
    have ex : Function.update (embed x) i b = embed x := hx ▸ Function.update_eq_self _ _
    have ey : Function.update (embed y) i b = embed y := hy ▸ Function.update_eq_self _ _
    exact ⟨embed x, embed y, by simpa only [ex, ey, agree] using hf⟩
