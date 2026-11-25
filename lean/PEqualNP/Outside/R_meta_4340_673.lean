import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4340_673
    (orbit : let G := fun x : Fin 9 → Bool => (List.finRange 9).any fun i => x i && (List.finRange 9).any fun j => x j && (([50, 69, 138, 276, 9, 385, 258, 36, 104] : List Nat).getD i.val 0).testBit j.val
    let ok := fun a b : Nat => (([192, 144, 80, 192, 294, 80, 45, 267, 144] : List Nat).getD a 0).testBit b
    ∀ p∈([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p.1 || x p.2]) = G x) →
      p=(0,6) ∧ ∀ g∈C.gates, ∀ a b : Nat, a<9 → b<9 → a≠b → g.inputs=[a,b] → g.op=.or → ok a b=true)
    (minor : let G := fun x : Fin 9 → Bool => (List.finRange 9).any fun i => x i && (List.finRange 9).any fun j => x j && (([50, 69, 138, 276, 9, 385, 258, 36, 104] : List Nat).getD i.val 0).testBit j.val
    let pin := fun (v : Nat) (x : Fin 8 → Bool) (i : Fin 9) => if i.val = v then false else x (Fin.ofNat 8 (if i.val < v then i.val else i.val-1))
    ∀ v ∈ ([0,6] : List Nat), ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = G (pin v x)) →
        (if v = 6 then 13 else 12) ≤ D.size)
    (erase : ∀ (S : List (Bool ⊕ Nat)) (C : Circuit) (K : Finset (Fin C.gates.length)),
      let val := fun (x : Fin 8 → Bool) (j : Nat) =>
        (C.wires (S.map fun s => Sum.elim id (fun w => (List.ofFn x).getD w false) s)).getD j false
      FanInTwo C → (∀ s∈S, ∀ k, s=Sum.inr k → k<8) →
      (∃ x y, val x C.output ≠ val y C.output) →
      (∀ j∈K, (∃ b : Bool, ∀ x, val x (S.length+j.val)=b) ∨
        ∃ w<S.length+j.val, ∀ x, val x (S.length+j.val)=val x w) →
      ∃ D : Circuit, FanInTwo D ∧ D.size+K.card≤C.size ∧
        ∀ x, D.eval (List.ofFn x)=val x C.output)
    (search : let G := fun x : Fin 9 → Bool => (List.finRange 9).any fun i => x i && (List.finRange 9).any fun j => x j && (([50, 69, 138, 276, 9, 385, 258, 36, 104] : List Nat).getD i.val 0).testBit j.val
    let ok := fun a b : Nat => (([192, 144, 80, 192, 294, 80, 45, 267, 144] : List Nat).getD a 0).testBit b
    let pin := fun (v : Nat) (x : Fin 8 → Bool) (i : Fin 9) => if i.val = v then false else x (Fin.ofNat 8 (if i.val < v then i.val else i.val-1))
    ∀ C : Circuit,
      let val := fun (v : Nat) (x : Fin 8 → Bool) (w : Nat) => (C.wires (List.ofFn (pin v x) ++ [(pin v x 0 || pin v x 6)])).getD w false
      FanInTwo C → C.size ≤ 14 →
      (∀ g∈C.gates, (∀ i∈g.inputs, i<9) → g.op=.or ∧ g.inputs.Pairwise (fun a b => a=b ∨ ok a b=true)) →
      (∀ v : Fin 9, (208 : Nat).testBit v.val = false →
      ∃ g ∈ C.gates, (g.inputs.filter (· < 9)).toFinset = {v.val}) →
      (∀ v∈([0,6] : List Nat), ∀ K : Finset (Fin C.gates.length),
       (∀ j∈K, (∃ b : Bool, ∀ x, val v x (10+j.val)=b) ∨
        ∃ w<10+j.val, ∀ x, val v x (10+j.val)=val v x w) →
       K.card+(if v = 6 then 13 else 12)≤C.size) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) ≠ G x) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [x7 x1.1 || x7 x1.2]) ≠ (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7 := by
  let G := fun x : Fin 9 → Bool => (List.finRange 9).any fun i => x i && (List.finRange 9).any fun j => x j && (([50, 69, 138, 276, 9, 385, 258, 36, 104] : List Nat).getD i.val 0).testBit j.val
  let ok := fun a b : Nat => (([192, 144, 80, 192, 294, 80, 45, 267, 144] : List Nat).getD a 0).testBit b
  let pin := fun (v : Nat) (x : Fin 8 → Bool) (i : Fin 9) => if i.val = v then false else x (Fin.ofNat 8 (if i.val < v then i.val else i.val-1))
  intro p pm C fan size guards
  by_contra! computes
  have graph (x : Fin 9 → Bool) :
      G x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    revert x
    decide +kernel
  have full (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x p.1 || x p.2]) = G x :=
    (computes x).trans (graph x).symm
  obtain ⟨rfl,ro⟩ := orbit p pm C fan size full
  have six : ∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∃ g ∈ C.gates, v.val∈g.inputs ∧ ∀ j∈g.inputs, j<9 → j=v.val := by
    let low : List ℕ := [4,6,7]
    let high : List (Fin 9) := [0,1,2,3,5,8]
    let base (i : Fin 9) : Bool := low.contains i.val
    let toggle (v i : Fin 9) : Bool := base i || decide (i=v)
    let single (v i : Fin 9) : Bool := decide (i=v)
    let input (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
    let rawPair (g : Gate) : Prop :=
      ∀ i ∈ g.inputs, ∀ j ∈ g.inputs, i < 9 → j < 9 → i ≠ j →
        g.op = .or ∧ (i ∈ low ∨ j ∈ low)
    let dedicated (v : ℕ) (g : Gate) : Prop :=
      v ∈ g.inputs ∧ ∀ j ∈ g.inputs, j < 9 → j = v
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have length_input (x : Fin 9 → Bool) : (input x).length = 10 := by simp [input]
    have stay (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (gs.foldl step (step w g)).getD i false = _
        rw [ih _ (by simp [step];omega)]
        exact List.getD_append _ _ _ _ h

    have get_append (a b t : List Bool) (len : a.length = b.length) {v : ℕ}
        (agree : ∀ i, i ≠ v → a.getD i false = b.getD i false) :
        ∀ i, i ≠ v → (a++t).getD i false = (b++t).getD i false := by
      intro i hi
      by_cases h : i<a.length
      · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (len ▸ h)]
        exact agree i hi
      · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : a.length ≤ i),
          List.getElem?_append_right (by omega : b.length ≤ i),len]

    have twins (gs : List Gate) (v : Fin 9) (nv : v.val ∉ low)
        (raw : ∀ g ∈ gs, rawPair g) (none : ∀ g ∈ gs, ¬dedicated v.val g)
        (a b : List Bool) (lengths : a.length = b.length)
        (agree : ∀ i, i ≠ v.val → a.getD i false = b.getD i false)
        (on : ∀ j ∈ low, j < a.length ∧ a.getD j false = true) :
        ∀ i, i ≠ v.val → (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
      induction gs generalizing a b with
      | nil => exact agree
      | cons g gs ih =>
        have valEq : g.op.eval (g.inputs.map fun i => a.getD i false) =
            g.op.eval (g.inputs.map fun i => b.getD i false) := by
          by_cases hv : v.val ∈ g.inputs
          · have t := none g (by simp)
            obtain ⟨j,hj,jlt,ne⟩ : ∃ j ∈ g.inputs, j < 9 ∧ j ≠ v.val := by
              by_contra! no
              exact t ⟨hv,no⟩
            obtain ⟨op,hv'|hl⟩ := raw g (by simp) v.val hv j hj v.isLt jlt ne.symm
            · exact (nv hv').elim
            · have hA := (on j hl).2
              have hB := (agree j ne).symm.trans hA
              rw [op]
              change (g.inputs.map _).any id = (g.inputs.map _).any id
              have A : (g.inputs.map fun i => a.getD i false).any id = true :=
                List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,hA⟩
              have B : (g.inputs.map fun i => b.getD i false).any id = true :=
                List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,hB⟩
              exact A.trans B.symm
          · congr 1
            apply List.map_congr_left
            exact fun i hi => agree i (fun e => hv (e ▸ hi))
        have len : (step a g).length = (step b g).length := by simp [step,lengths]
        have eq : ∀ i, i ≠ v.val → (step a g).getD i false = (step b g).getD i false := by
          unfold step
          rw [valEq]
          exact get_append a b _ lengths agree
        have next : ∀ j ∈ low, j < (step a g).length ∧ (step a g).getD j false = true := by
          intro j hj
          obtain ⟨lt,on⟩ := on j hj
          exact ⟨by simp [step];omega,(List.getD_append _ _ _ _ lt).trans on⟩
        exact ih (fun g hg => raw g (List.mem_cons_of_mem _ hg))
          (fun g hg => none g (List.mem_cons_of_mem _ hg)) _ _ len eq next

    have data : ∀ v ∈ high, v.val ∉ low ∧ G base = false ∧ G (toggle v) = true ∧
        G (single v) = false ∧ (input (single v)).getD v.val false = true ∧
        (∀ j : Fin 10, j.val ≠ v.val → (input base).getD j.val false = (input (toggle v)).getD j.val false) ∧
        ∀ j ∈ low, j < (input base).length ∧ (input base).getD j false = true := by
      dsimp only [high,low,base,toggle,single,input,G]
      decide +kernel

    have ends : ∀ a b : Fin 9, ok a.val b.val = true → a.val ∈ low ∨ b.val ∈ low := by
      dsimp only [ok,low]
      decide +kernel
    have orderTwo {l : List Nat} {a b : Nat} (h : l.length ≤ 2) (ha : a∈l) (hb : b∈l) (ne : a ≠ b) :
        l=[a,b] ∨ l=[b,a] := by
      cases l with
      | nil => simp at ha
      | cons x tail =>
        cases tail with
        | nil =>
          have eq := List.mem_singleton.mp ha
          exact (ne (eq.trans (List.mem_singleton.mp hb).symm)).elim
        | cons y z =>
          have empty : z=[] := by simpa using h
          subst z
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
          rcases ha with ha|ha <;> rcases hb with hb|hb
          · exact (ne (ha.trans hb.symm)).elim
          · exact Or.inl (by rw [ha,hb])
          · exact Or.inr (by rw [ha,hb])
          · exact (ne (ha.trans hb.symm)).elim
    have raw : ∀ g ∈ C.gates, rawPair g := by
      intro g hg i hi j hj il jl ne
      have ord := orderTwo (fan g hg).2 hi hj ne
      have valid : ∀ n ∈ g.inputs, n < 9 := by
        intro n hn
        rcases ord with h|h <;> rw [h] at hn <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
        · rcases hn with rfl|rfl <;> assumption
        · rcases hn with rfl|rfl <;> assumption
      have guard := guards g hg valid
      have allowed := (fan g hg).1
      have op : g.op = .or := by
        rcases allowed with eq|eq|eq
        · exact (guard.1 eq).elim
        · exact eq
        · exact (guard.2 eq).elim
      refine ⟨op,?_⟩
      rcases ord with ord|ord
      · exact ends ⟨i,il⟩ ⟨j,jl⟩ (ro g hg i j il jl ne ord op)
      · exact (ends ⟨j,jl⟩ ⟨i,il⟩ (ro g hg j i jl il ne.symm ord op)).symm
    intro v hv
    change ∃ g ∈ C.gates, dedicated v.val g
    obtain ⟨nv,off,on,singleOff,singleBit,agrees,lows⟩ := data v hv
    have output : C.output ≠ v.val := by
      intro e
      have h := full (single v)
      change (C.gates.foldl step (input (single v))).getD C.output false = _ at h
      rw [e,stay _ _ _ (by rw [length_input];omega),singleBit,singleOff] at h
      contradiction
    by_contra! no
    have eq := twins C.gates v nv raw no (input base) (input (toggle v))
      ((length_input _).trans (length_input _).symm) (by
        intro i ne
        by_cases lt : i<10
        · exact agrees ⟨i,lt⟩ ne
        · rw [List.getD_eq_default _ _ (by rw [length_input];omega),
            List.getD_eq_default _ _ (by rw [length_input];omega)]) lows C.output output
    change C.eval (List.ofFn base ++ [base 0 || base 6]) = C.eval (List.ofFn (toggle v) ++ [toggle v 0 || toggle v 6]) at eq
    rw [full,full,off,on] at eq
    contradiction

  have sixShort : ∀ v : Fin 9, (208 : Nat).testBit v.val = false →
      ∃ g ∈ C.gates, (g.inputs.filter (· < 9)).toFinset = {v.val} := by
    intro v hv
    have verts : ∀ v : Fin 9, (208 : Nat).testBit v.val = false →
        v ∈ ([0,1,2,3,5,8] : List (Fin 9)) := by decide +kernel
    obtain ⟨g,hg,readV,unique⟩ := six v (verts v hv)
    refine ⟨g,hg,?_⟩
    ext j
    simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_singleton]
    exact ⟨fun h => unique j h.1 h.2,fun e => e ▸ ⟨readV,v.isLt⟩⟩

  have masked : ∀ g∈C.gates, (∀ i∈g.inputs, i<9) → g.op=.or ∧ g.inputs.Pairwise (fun a b => a=b ∨ ok a b=true) := by
    intro g hg hlow
    have hm := (fan g hg).1
    change g.op=.and ∨ g.op=.or ∨ g.op=.not at hm
    obtain ⟨na,nn⟩ := guards g hg hlow
    have hOR := ((hm.resolve_left na).resolve_right nn)
    refine ⟨hOR,?_⟩
    have n := (fan g hg).2
    have e : g.inputs=[] ∨ (∃ a, g.inputs=[a]) ∨ ∃ a b,g.inputs=[a,b] := by
      cases h:g.inputs with
      | nil => simp
      | cons a l =>
        cases l with
        | nil => simp
        | cons b l =>
           have nl : l=[] := by rw [h] at n; cases l with
             | nil => rfl
             | cons c t => simp at n
           subst l
           exact Or.inr (Or.inr ⟨_,_,rfl⟩)
    rcases e with hr|⟨a,hr⟩|⟨a,b,hr⟩
    · simp [hr]
    · simp [hr]
    · have ha := hlow a (by simp [hr])
      have hb := hlow b (by simp [hr])
      by_cases eq:a=b
      · simp [hr,eq]
      · simpa [hr,eq,ok] using ro g hg a b ha hb eq hr hOR
  have loss (v : Nat) (vh : v∈([0,6] : List Nat)) (K : Finset (Fin C.gates.length)) :
    let val := fun (x : Fin 8 → Bool) (w : Nat) => (C.wires (List.ofFn (pin v x) ++ [pin v x 0 || pin v x 6])).getD w false
    (∀ j∈K, (∃ b : Bool, ∀ x, val x (10+j.val)=b) ∨ ∃ w<10+j.val, ∀ x, val x (10+j.val)=val x w) →
    K.card+(if v=6 then 13 else 12) ≤ C.size := by
    let val := fun (x : Fin 8 → Bool) (w : Nat) => (C.wires (List.ofFn (pin v x) ++ [pin v x 0 || pin v x 6])).getD w false
    dsimp only
    intro red
    let sym := fun (i : Fin 9) => if i.val=v then (Sum.inl false : Bool ⊕ Nat) else Sum.inr ((if i.val < v then i.val else i.val-1) % 8)
    let port : Fin 9 := if v=6 then 0 else 6
    let S := List.ofFn sym ++ [sym port]
    have slen : S.length=10 := by simp [S]
    have evalS (x : Fin 8 → Bool) : S.map (fun s => Sum.elim id (fun w => (List.ofFn x).getD w false) s) = List.ofFn (pin v x) ++ [pin v x 0 || pin v x 6] := by
      let read := fun s : Bool ⊕ Nat => Sum.elim id (fun w => (List.ofFn x).getD w false) s
      have spec (i : Fin 9) : read (sym i) = pin v x i := by
        by_cases h : i.val=v
        · simp [read,sym,pin,h]
        · simp only [read,sym,pin,h,ite_false,Sum.elim_inr]
          rw [List.getD_eq_getElem _ _ (by simp; exact Nat.mod_lt _ (by decide)),List.getElem_ofFn]
          rfl
      have eqs : (List.ofFn sym).map read = List.ofFn (pin v x) := by
        rw [List.map_ofFn]
        exact congrArg List.ofFn (funext spec)
      change (List.ofFn sym ++ [sym port]).map read = _
      simp only [List.map_append,List.map_cons,List.map_nil,eqs,spec]
      rcases (by simpa using vh : v=0 ∨ v=6) with rfl|rfl
      · simp [port,pin]
      · simp [port,pin]
    have bd : ∀ s∈S, ∀ k, s=Sum.inr k → k<8 := by
      intro s hs k eq
      have valid (i : Fin 9) (h : sym i=Sum.inr k) : k<8 := by
        dsimp only [sym] at h
        split at h
        · contradiction
        · cases h
          exact Nat.mod_lt _ (by decide)
      rcases List.mem_append.mp hs with hs|hs
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
        exact valid i eq
      · obtain rfl := List.mem_singleton.mp hs
        exact valid _ eq
    have output (x : Fin 8 → Bool) : val x C.output = G (pin v x) := full (pin v x)
    have nc : ∃ x y : Fin 8 → Bool, G (pin v x) ≠ G (pin v y) := by
      rcases (by simpa using vh : v=0 ∨ v=6) with rfl|rfl <;> exact ⟨fun _ => false,fun _ => true,by decide⟩
    have n : ∃ x y, val x C.output ≠ val y C.output := by
      obtain ⟨x,y,d⟩ := nc
      exact ⟨x,y,by simpa only [output] using d⟩
    have z := erase S C K fan bd
    simp only [evalS,slen] at z
    obtain ⟨D,df,ds,de⟩ := z n red
    have floor := minor v vh D df (fun x => (de x).trans (output x))
    omega
  obtain ⟨x,bad⟩ := search C fan size masked sixShort loss
  exact bad (full x)
