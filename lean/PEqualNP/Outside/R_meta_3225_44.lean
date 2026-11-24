import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3225_44
  (lower : ∀ E : Circuit, FanInTwo E → circuitFun 9 E = (fun y : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun k =>
    y (Fin.ofNat 9 (k/10)) && y (Fin.ofNat 9 (k % 10))) →
    (∃ a b : Fin 9, (a,b) ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)) ∧ ∀ y : Fin 9 → Bool, (E.wires (List.ofFn y)).getD 9 false = (y a && y b)) → 16 ≤ E.size)
  (core : let p (y : Fin 9 → Bool) := List.ofFn y ++ [y 0 || y 6]
    let reads (g : Gate) := (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i=6))
    ∀ C : Circuit, FanInTwo C → C.size=14 → C.gates.countP reads ≤ 1 →
      (∃ g ∈ C.gates, g.op=.or ∧ 6 ∈ g.inputs) →
      (∀ j < C.size, ∀ a b : Fin 9, a < b → ∃ y : Fin 9 → Bool,
        (C.wires (p y)).getD (10+j) false ≠ (y a && y b)) →
      ∃ y : Fin 9 → Bool, C.eval (p y) ≠ (fun y : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun k =>
    y (Fin.ofNat 9 (k/10)) && y (Fin.ofNat 9 (k % 10))) y) : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x8 ∈ x4.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x8.inputs) → (∀ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x9) = x3 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x10) ≠ (x3 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  let value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let step (w : List Bool) (g : Gate) := w ++ [value w g]
  have stepEq (w : List Bool) (g : Gate) : step w g = w ++ [value w g] := rfl
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w
  let rename (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩
  have len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length+gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons a t ih => change (run t (step w a)).length = _; rw [ih]; simp [step]; omega
  have keep (gs : List Gate) {w : List Bool} {i : Nat} (h : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons a t ih =>
      change (run t (step w a)).getD i false = _
      rw [ih (by simp [step];omega)]
      exact List.getD_append _ _ _ _ h
  have renameRun (r : Nat → Nat) (gs : List Gate) (s t : List Bool)
      (agree : ∀ i, t.getD (r i) false = s.getD i false)
      (past : ∀ i < s.length, r i < t.length)
      (future : ∀ i, s.length ≤ i → r i = t.length+(i-s.length)) :
      ∀ i, (run (gs.map (rename r)) t).getD (r i) false = (run gs s).getD i false := by
    induction gs generalizing s t with
    | nil => exact agree
    | cons g gs ih =>
      have val : value t (rename r g) = value s g := by simp only [value,rename,List.map_map,Function.comp_def,agree]
      apply ih (step s g) (step t (rename r g))
      · intro i
        by_cases h : i < s.length
        · rw [stepEq,stepEq,List.getD_append _ _ _ _ (past i h),List.getD_append _ _ _ _ h,agree]
        · have e := future i (by omega)
          simp only [step,val]
          rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
          congr 1 <;> omega
      · intro i hi
        simp only [step,List.length_append,List.length_cons,List.length_nil] at hi ⊢
        by_cases h : i<s.length
        · have := past i h; omega
        · have := future i (by omega); omega
      · intro i hi
        simp only [step,List.length_append,List.length_cons,List.length_nil] at hi ⊢
        have := future i (by omega)
        omega

  let push (n i : Nat) := if i<n then i else i+1
  let rotate (n k i : Nat) := if i<n+k then push n i else if i=n+k then n else i
  have rotateEq (n k i : Nat) : rotate n k i = (if i<n+k then push n i else if i=n+k then n else i) := rfl
  let promote (n : Nat) (pre post : List Gate) (first : Gate) (out : Nat) : Circuit :=
    ⟨first :: pre.map (rename (push n)) ++ post.map (rename (rotate n pre.length)),rotate n pre.length out⟩

  have promoteEval {n : Nat} (x : List Bool) (hx : x.length=n) (pre post : List Gate) (g first : Gate) (out : Nat)
      (same : value (run pre x) g = value x first) :
      (promote n pre post first out).eval x = (⟨pre ++ g::post,out⟩ : Circuit).eval x := by
    let s := run pre x
    let t := run (pre.map (rename (push n))) (step x first)
    have ls : s.length=n+pre.length := by simp [s,len,hx]
    have lt : t.length=n+pre.length+1 := by simp [t,len,step,hx];omega
    have inPrefix (i : Nat) : t.getD (push n i) false = s.getD i false := by
      apply renameRun
      · intro j
        by_cases h : j<n
        · simpa [push,h,step] using List.getD_append x [value x first] false j (by omega)
        · rw [show push n j=j+1 by simp [push,h],List.getD_eq_default _ _ (by simp [step,hx];omega),List.getD_eq_default _ _ (by omega)]
      · intro j h; simp [push,show j<n by omega,step,hx];omega
      · intro j h; simp [push,show ¬j<n by omega,step,hx];omega
    have saved : t.getD n false = value x first := by
      rw [show t=run (pre.map (rename (push n))) (step x first) by rfl,keep _ (by simp [step,hx])]
      simp [step,List.getD_eq_getElem?_getD,hx,List.getElem?_append]
    have agree (i : Nat) : t.getD (rotate n pre.length i) false = (step s g).getD i false := by
      by_cases h : i<n+pre.length
      · rw [rotateEq,if_pos h,stepEq,List.getD_append _ _ _ _ (by omega),inPrefix]
      · by_cases e : i=n+pre.length
        · subst i
          rw [rotateEq,if_neg h,if_pos rfl,saved,stepEq,List.getD_append_right _ _ _ _ (by omega),ls,Nat.sub_self]
          exact same.symm
        · rw [rotateEq,if_neg h,if_neg e,List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp [step,ls];omega)]
    have eq := renameRun (rotate n pre.length) post (step s g) t agree (by
      intro i hi
      simp only [step,List.length_append,List.length_cons,List.length_nil,ls] at hi
      unfold rotate push
      split_ifs <;> omega) (by
      intro i hi
      simp only [step,List.length_append,List.length_cons,List.length_nil,ls] at hi ⊢
      simp [rotate,show ¬i<n+pre.length by omega,show i≠n+pre.length by omega,lt];omega) out
    change (run (first :: pre.map (rename (push n)) ++ post.map (rename (rotate n pre.length))) x).getD (rotate n pre.length out) false =
      (run (pre ++ g::post) x).getD out false
    simpa only [run,List.foldl_cons,List.foldl_append,s,t] using eq

  have promoteSemantic {n : Nat} (C : Circuit) (u v : Fin n) (j : Nat) (legal : FanInTwo C)
      (hj : j < C.gates.length) (column : ∀ y : Fin n → Bool,
        (C.wires (List.ofFn y)).getD (n+j) false = (y u && y v)) :
      ∃ E : Circuit, FanInTwo E ∧ E.size = C.size ∧ circuitFun n E = circuitFun n C ∧
        ∀ y : Fin n → Bool, (E.wires (List.ofFn y)).getD n false = (y u && y v) := by
    rcases C with ⟨gs,out⟩
    change j<gs.length at hj
    let pre := gs.take j
    let g := gs[j]
    let post := gs.drop (j+1)
    have splitG : gs=pre ++ g::post := by
      change gs = gs.take j ++ gs[j] :: gs.drop (j+1)
      rw [←List.drop_eq_getElem_cons hj,List.take_append_drop]
    have lp : pre.length=j := by simp [pre,Nat.min_eq_left (Nat.le_of_lt hj)]
    let first : Gate := ⟨.and,[u.val,v.val]⟩
    let E := promote n pre post first out
    have av (y : Fin n → Bool) : value (List.ofFn y) first = (y u && y v) := by
      change ([(List.ofFn y).getD u.val false,(List.ofFn y).getD v.val false] : List Bool).all id = _
      simp [List.getD_eq_getElem?_getD]
    have eqg (y : Fin n → Bool) : value (run pre (List.ofFn y)) g = (y u && y v) := by
      have h := column y
      change (run gs (List.ofFn y)).getD (n+j) false = _ at h
      rw [splitG] at h
      let w := run pre (List.ofFn y)
      have lw : w.length=n+j := by simp [w,len,lp]
      change ((pre ++ g::post).foldl step (List.ofFn y)).getD (n+j) false = _ at h
      rw [List.foldl_append,List.foldl_cons] at h
      change (run post (step w g)).getD (n+j) false = _ at h
      rw [keep _ (by simp [step,lw]),stepEq,List.getD_append_right _ _ _ _ (by omega),lw,Nat.sub_self] at h
      exact h
    refine ⟨E,?_,?_,?_,?_⟩
    · intro gate hm
      change gate ∈ first :: pre.map (rename (push n)) ++ post.map (rename (rotate n pre.length)) at hm
      rcases List.mem_cons.mp hm with rfl|h
      · exact ⟨Or.inl rfl,by simp [first]⟩
      · have valid (r : Nat → Nat) (a : Gate) (ha : a ∈ gs) :
            (rename r a).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ (rename r a).inputs.length ≤ 2 := by
          simpa only [rename,List.length_map] using legal a ha
        rcases List.mem_append.mp h with hp|hs
        · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
          exact valid _ _ (splitG ▸ List.mem_append_left _ ha)
        · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
          exact valid _ _ (splitG ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ha))
    · change (first :: pre.map _ ++ post.map _).length = gs.length
      have ln := congrArg List.length splitG
      simp_all only [List.length_cons,List.length_append,List.length_map]
      omega
    · funext y
      change E.eval (List.ofFn y) = (⟨gs,out⟩ : Circuit).eval (List.ofFn y)
      conv_rhs => rw [splitG]
      exact promoteEval _ (by simp) _ _ _ _ _ ((eqg y).trans (av y).symm)
    · intro y
      let gs' := pre.map (rename (push n)) ++ post.map (rename (rotate n pre.length))
      change (run gs' (step (List.ofFn y) first)).getD n false = _
      rw [keep _ (by simp [step]),stepEq,List.getD_append_right _ _ _ _ (by simp)]
      simpa using av y
  let graph : ((Fin 9) → Bool) → Bool := (fun y : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun k =>
      y (Fin.ofNat 9 (k/10)) && y (Fin.ofNat 9 (k % 10)))
  let perm : Fin 12 → (Fin 9) → (Fin 9) := ![
    ![0,1,2,3,4,5,6,7,8], ![0,5,8,3,4,1,7,6,2],
    ![1,0,5,8,6,2,4,7,3], ![1,2,3,8,6,0,7,4,5],
    ![2,1,0,5,7,3,6,4,8], ![2,3,8,5,7,1,4,6,0],
    ![3,2,1,0,4,8,7,6,5], ![3,8,5,0,4,2,6,7,1],
    ![5,0,1,2,7,8,4,6,3], ![5,8,3,2,7,0,6,4,1],
    ![8,3,2,1,6,5,4,7,0], ![8,5,0,1,6,3,7,4,2]]
  let reps : List ((Fin 9) × (Fin 9)) := [(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)]
  have invariant : ∀ m : Fin 12, ∀ y : (Fin 9) → Bool, graph (y ∘ perm m) = graph y := by decide +kernel
  have orbit : ∀ a b : (Fin 9), a<b → ∃ m : Fin 12,
      (perm m a,perm m b) ∈ reps ∨ (perm m b,perm m a) ∈ reps := by decide +kernel

  have allPairs : ∀ E : Circuit, FanInTwo E → circuitFun 9 E = graph →
      (∃ a b : (Fin 9), a<b ∧ ∀ y : (Fin 9) → Bool, (E.wires (List.ofFn y)).getD 9 false = (y a && y b)) → 16 ≤ E.size := by
    intro E ok fn casesPair
    obtain ⟨a,b,lt,head⟩ := casesPair
    obtain ⟨m,orient⟩ := orbit a b lt
    let r (i : Nat) : Nat := if h : i<9 then (perm m ⟨i,h⟩).val else i
    let D : Circuit := ⟨E.gates.map (rename r),r E.output⟩
    have r9 : r 9=9 := rfl
    have sim (y : (Fin 9) → Bool) (i : Nat) : (D.wires (List.ofFn y)).getD (r i) false =
        (E.wires (List.ofFn (y ∘ perm m))).getD i false := by
      apply renameRun
      · intro j
        by_cases h : j<9
        · simp only [r,h,List.getD_eq_getElem?_getD,List.getElem?_ofFn,Fin.is_lt,dif_pos,dif_neg,Option.getD_some,Option.getD_none,Function.comp_apply]
        · rw [show r j=j by simp [r,h],List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
      · intro j hj
        have h : j<9 := by simpa using hj
        simp [r,h]
      · intro j hj
        have h : 9≤j := by simpa using hj
        simp [r,show ¬j<9 by omega];omega
    have legal : FanInTwo D := by
      intro gate hm
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
      simpa only [rename,List.length_map] using ok g hg
    have eqF : circuitFun 9 D = graph := by
      funext y
      exact (sim y E.output).trans ((congrFun fn _).trans (invariant m y))
    have fst (y : (Fin 9) → Bool) : (D.wires (List.ofFn y)).getD 9 false = (y (perm m a) && y (perm m b)) :=
      (r9 ▸ sim y 9).trans (head (y ∘ perm m))
    have bound : 16 ≤ D.size := by
      rcases orient with h|h
      · exact lower D legal eqF ⟨_,_,h,fst⟩
      · exact lower D legal eqF ⟨_,_,h,fun y => (fst y).trans (Bool.and_comm ..)⟩
    change 16 ≤ (E.gates.map (rename r)).length at bound
    change 16 ≤ E.gates.length
    simpa only [List.length_map] using bound
  dsimp only
  intro C ok sz cnt reader low
  by_contra! high
  let pin (b : Bool) (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,b,x 6,x 3,x 1 || b]
  let lo (x : Fin 8 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  change ∀ x, C.eval (pin false x) = lo x at low
  change ∀ x, C.eval (pin true x) = (lo x || x 0 || x 3) at high
  let base (y : Fin 9 → Bool) : Fin 8 → Bool := ![y 1,y 0,y 5,y 8,y 2,y 4,y 7,y 3]
  let target (y : Fin 9 → Bool) := (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) ||
    (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) ||
    (y 6 && y 8) || (y 8 && y 5)
  have table : ∀ y : Fin 9 → Bool,
      (if y 6 then lo (base y) || (base y) 0 || (base y) 3 else lo (base y)) = target y := by decide +kernel
  let first : Gate := ⟨.or,[0,6]⟩
  let D : Circuit := ⟨first :: C.gates,C.output⟩
  let step (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have start (y : Fin 9 → Bool) : step (List.ofFn y) first = List.ofFn y ++ [y 0 || y 6] := by
    change List.ofFn y ++ [([(List.ofFn y).getD 0 false,(List.ofFn y).getD 6 false] : List Bool).any id] = _
    simp [List.getD_eq_getElem?_getD]
  have saved (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (gs.foldl step xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      · simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
      · simp [step];omega
  have permitted : FanInTwo D := by
    intro g hg
    change g ∈ first :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl|h
    · exact ⟨Or.inr (Or.inl rfl),by decide⟩
    · exact ok g h
  have firstValue (y : Fin 9 → Bool) : (D.wires (List.ofFn y)).getD 9 false = (y 0 || y 6) := by
    change (C.gates.foldl step (step (List.ofFn y) first)).getD 9 false = _
    rw [start,saved _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append]
  have funD : circuitFun 9 D = target := by
    funext y
    change (C.gates.foldl step (step (List.ofFn y) first)).getD C.output false = _
    rw [start]
    have repr : List.ofFn y ++ [y 0 || y 6] = pin (y 6) (base y) := by rfl
    rw [repr]
    change C.eval (pin (y 6) (base y)) = target y
    rw [←table y]
    cases h : y 6
    · exact low _
    · exact high _
  have encoded : ∀ y : Fin 9 → Bool, target y = (fun y : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun k =>
    y (Fin.ofNat 9 (k/10)) && y (Fin.ofNat 9 (k % 10))) y := by decide +kernel
  have matching (y : Fin 9 → Bool) (j : Nat) : (D.wires (List.ofFn y)).getD (9+(j+1)) false =
      (C.wires (List.ofFn y ++ [y 0 || y 6])).getD (10+j) false := by
    change (C.gates.foldl step (step (List.ofFn y) first)).getD (9+(j+1)) false = _
    rw [start,show 9+(j+1)=10+j by omega]
    rfl
  have clean (j : Nat) (hj : j<C.size) (a b : Fin 9) (hab : a<b) :
      ∃ y : Fin 9 → Bool, (C.wires (List.ofFn y ++ [y 0 || y 6])).getD (10+j) false ≠ (y a && y b) := by
    by_contra! col
    have index : j+1<D.gates.length := by change j<C.gates.length at hj; change j+1<C.gates.length+1; omega
    obtain ⟨E,el,es,ef,ew⟩ := promoteSemantic D a b (j+1) permitted index (fun y => (matching y j).trans (col y))
    have bound := allPairs E el (ef.trans (funD.trans (funext encoded))) ⟨a,b,hab,ew⟩
    rw [es] at bound
    change 16 ≤ C.gates.length+1 at bound
    change C.gates.length=14 at sz
    omega
  obtain ⟨y,hy⟩ := core C ok sz cnt reader clean
  apply hy
  have h := congrFun funD y
  change (C.gates.foldl step (step (List.ofFn y) first)).getD C.output false = target y at h
  rw [start] at h
  exact h.trans (encoded y)
