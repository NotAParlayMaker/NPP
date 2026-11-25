import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Seven sensitivity rows per marked input classify every two-input companion.
set_option maxHeartbeats 3500000 in
set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.R_meta_2116_641
    (cover : let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun j => x (Fin.ofNat 9 (j / 9)) && x (Fin.ofNat 9 (j % 9)))
      let allowed := fun (v p q : Fin 9) (a b : Bool) =>
        ((if v=4 then [8,16,268443650,28529726501] else if v=6 then [536870912,1342177280,2064,10812921453] else [4096,10242,1073741824,28454225517] : List Nat).getD (a.toNat+2*b.toNat) 0).testBit (q.val*(q.val-1)/2+p.val)
      let sample := fun (v : Fin 9) (j : Fin 7) => ((if v=4 then [42,69,104,138,261,385,201] else if v=6 then [42,50,138,261,276,385,402] else [42,50,69,104,261,276,116] : List Nat).getD j.val 0)
      ∀ (v : Fin 9), v ∈ ([4,6,7] : List (Fin 9)) → ∀ (p q : Fin 9),p<q → p≠v → q≠v →
        ∀ a b : Bool,allowed v p q a b=false → ∃ j : Fin 7,
          let x := fun i : Fin 9 => (sample v j).testBit i.val
          f x=false ∧ f (Function.update x v true)=true ∧ x p=a ∧ x q=b)
    (mask : ∀ (n : ℕ) (C : Circuit), (∀ j : Fin C.size,∀ u ∈ (C.gates.get j).inputs,u<n+j.val) →
      ∀ (v : Fin n) (i : Fin C.size) (w : ℕ) (x : Fin n → Bool), (∃ z : Fin n → Bool,C.eval (List.ofFn z)≠z v) →
      (C.gates.get i).op=GateOp.or →
      ((C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val]) →
      (∀ j : Fin C.size,j≠i → v.val∉(C.gates.get j).inputs) →
      C.eval (List.ofFn x)≠C.eval (List.ofFn (Function.update x v true)) →
      PEqualNP.BlindGate.wireValue C n x w=false)
    (useful : ∀ (n : ℕ) (C : Circuit),IsMinimalCircuit n C → ∀ (i : Fin C.size) (v : Fin n) (w : ℕ),
      (∀ t∈(C.gates.get i).inputs,t<n+i.val) → (C.gates.get i).op=.or →
      ((C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val]) →
      ∃ x : Fin n → Bool,PEqualNP.BlindGate.wireValue C n x w=true)
    (search : let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun j => x (Fin.ofNat 9 (j / 9)) && x (Fin.ofNat 9 (j % 9)))
      let allowed := fun (v p q : Fin 9) (a b : Bool) =>
        ((if v=4 then [8,16,268443650,28529726501] else if v=6 then [536870912,1342177280,2064,10812921453] else [4096,10242,1073741824,28454225517] : List Nat).getD (a.toNat+2*b.toNat) 0).testBit (q.val*(q.val-1)/2+p.val)
      ∀ C : Circuit,IsMinimalCircuit 9 C → C.size≤15 → circuitFun 9 C=f →
      (∀ j : Fin C.size,let g := C.gates.get j
        (∀ t∈g.inputs,t<9+j.val) ∧ g.inputs.Nodup ∧ ((g.op=.not ∧ g.inputs.length=1) ∨ (g.op≠.not ∧ g.inputs.length=2))) →
      (∀ v ∈ ([4,6,7] : List (Fin 9)), ∃ (i : Fin C.size) (w : ℕ),
        (C.gates.get i).op=.or ∧ (C.gates.get i).inputs.Perm [v.val,w] ∧
        (∀ j : Fin C.size,v.val∈(C.gates.get j).inputs ↔ j=i) ∧
        (∃ x,PEqualNP.BlindGate.wireValue C 9 x w=true) ∧
        ∀ p q : Fin 9,p<q → p≠v → q≠v → ∀ h : Bool → Bool → Bool,
        (∀ x,PEqualNP.BlindGate.wireValue C 9 x w=h (x p) (x q)) →
        ∀ a b,h a b=allowed v p q a b) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C model single
  obtain ⟨minimal,budget,computes,shape,_⟩ := model
  let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun j => x (Fin.ofNat 9 (j / 9)) && x (Fin.ofNat 9 (j % 9)))
  let allowed := fun (v p q : Fin 9) (a b : Bool) =>
        ((if v=4 then [8,16,268443650,28529726501] else if v=6 then [536870912,1342177280,2064,10812921453] else [4096,10242,1073741824,28454225517] : List Nat).getD (a.toNat+2*b.toNat) 0).testBit (q.val*(q.val-1)/2+p.val)
  let sample := fun (v : Fin 9) (j : Fin 7) => ((if v=4 then [42,69,104,138,261,385,201] else if v=6 then [42,50,138,261,276,385,402] else [42,50,69,104,261,276,116] : List Nat).getD j.val 0)
  have spec : circuitFun 9 C=f := by
    rw [computes]
    funext x
    simp only [f,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  have oneCell : ∀ v ∈ ([4,6,7] : List (Fin 9)),∀ p q : Fin 9,p<q → p≠v → q≠v →
    ∀ a b c d : Bool,allowed v p q a b=true → allowed v p q c d=true → a=c ∧ b=d := by decide +kernel
  have oneOff : ∀ v : Fin 9,f (fun j => decide (j=v))=false := by decide +kernel
  apply search C minimal budget spec
  · exact shape
  · intro v hv
    obtain ⟨cardinal,types⟩ := single v hv
    let readers : Finset (Fin C.size) := {j | v.val ∈ (C.gates.get j).inputs}
    change readers.card=1 at cardinal
    obtain ⟨i,one⟩ := Finset.card_eq_one.mp cardinal
    have hit (j : Fin C.size) : v.val ∈ (C.gates.get j).inputs ↔ j=i := by
      have h : j∈readers ↔ j=i := by rw [one,Finset.mem_singleton]
      simpa [readers] using h
    have op := types i (show i∈readers by rw [one];simp)
    have arity : (C.gates.get i).inputs.length=2 := by
      rcases (shape i).2.2 with ⟨bad,_⟩|⟨_,ok⟩
      · rw [op] at bad
        cases bad
      · exact ok
    obtain ⟨c,d,cd⟩ := List.length_eq_two.mp arity
    have contains : v.val=c ∨ v.val=d := by simpa [cd] using (hit i).mpr rfl
    have produce (w : ℕ) (pins : (C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val]) :
        ∀ p q : Fin 9,p<q → p≠v → q≠v → ∀ h : Bool → Bool → Bool,
        (∀ x,PEqualNP.BlindGate.wireValue C 9 x w=h (x p) (x q)) →
        ∀ a b,h a b=true → allowed v p q a b=true := by
      intro p q ordered pv qv h depends a b on
      cases ok : allowed v p q a b with
      | true => rfl
      | false =>
        obtain ⟨j,good⟩ := cover v hv p q ordered pv qv a b ok
        let x := fun t : Fin 9 => (sample v j).testBit t.val
        change f x=false ∧ f (Function.update x v true)=true ∧ x p=a ∧ x q=b at good
        obtain ⟨before,after,pa,qb⟩ := good
        have changes : C.eval (List.ofFn x)≠C.eval (List.ofFn (Function.update x v true)) := by
          change circuitFun 9 C x≠circuitFun 9 C (Function.update x v true)
          rw [spec,before,after]
          decide
        have notProjection : ∃ z : Fin 9 → Bool,C.eval (List.ofFn z) ≠ z v := by
          refine ⟨fun j => decide (j=v),?_⟩
          change circuitFun 9 C (fun j => decide (j=v)) ≠ decide (v=v)
          rw [spec,oneOff]
          simp
        have shut := mask 9 C (fun j => (shape j).1) v i w x notProjection op pins
          (fun j ne hmem => ne ((hit j).mp hmem)) changes
        rw [depends x,pa,qb,on] at shut
        cases shut
    have exactTable (w : ℕ) (pins : (C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val]) :
        (∃ x,PEqualNP.BlindGate.wireValue C 9 x w=true) ∧
        ∀ p q : Fin 9,p<q → p≠v → q≠v → ∀ h : Bool → Bool → Bool,
        (∀ x,PEqualNP.BlindGate.wireValue C 9 x w=h (x p) (x q)) →
        ∀ a b,h a b=allowed v p q a b := by
      obtain ⟨z,live⟩ := useful 9 C minimal i v w (shape i).1 op pins
      refine ⟨⟨z,live⟩,?_⟩
      intro p q ordered pv qv h depends a b
      have forward := produce w pins p q ordered pv qv h depends
      rw [depends z] at live
      have lit := forward _ _ live
      apply Bool.eq_iff_iff.mpr
      refine ⟨forward a b,?_⟩
      intro yes
      obtain ⟨ea,eb⟩ := oneCell v hv p q ordered pv qv a b (z p) (z q) yes lit
      rw [ea,eb]
      exact live
    rcases contains with e|e
    · subst c
      exact ⟨i,d,op,(by rw [cd]),hit,exactTable d (Or.inl cd)⟩
    · subst d
      have perm : (C.gates.get i).inputs.Perm [v.val,c] := by
        rw [cd]
        exact List.Perm.swap _ _ []
      exact ⟨i,c,op,perm,hit,exactTable c (Or.inr cd)⟩

-- The finite child closes by decide +kernel. The general wire child can be recovered below.
-- The wire fold facts originate in willakone, L_meta_1490.
--
-- namespace Eric.PetersenPorts
-- open PEqualNP.CircuitLowerBounds
--
-- -- Basic fold lemmas from willakone, original project lemma L_meta_1490.
-- def stepWire (w : List Bool) (g : Gate) : List Bool :=
--   w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--
-- lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
--     C.wires x = C.gates.foldl stepWire x := rfl
--
-- lemma foldl_length (gs : List Gate) (w : List Bool) :
--     (gs.foldl stepWire w).length = w.length + gs.length := by
--   induction gs generalizing w with
--   | nil => simp
--   | cons g gs ih =>
--     rw [List.foldl_cons, ih]
--     simp [stepWire]
--     omega
--
-- lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
--     (gs.foldl stepWire w).getD i false = w.getD i false := by
--   induction gs generalizing w with
--   | nil => rfl
--   | cons g gs ih =>
--     simp only [List.foldl_cons]
--     have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
--     rw [ih (stepWire w g) hlt]
--     simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
--
-- lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
--   simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
--
-- lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
--     (gs.foldl stepWire w).getD (w.length + j) false =
--       (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
--         if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
--   induction gs generalizing w j with
--   | nil => simp at hj
--   | cons g gs ih =>
--     rw [List.foldl_cons]
--     cases j with
--     | zero =>
--       have h1 : w.length < (stepWire w g).length := by simp [stepWire]
--       rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
--       simp only [List.getElem_cons_zero]
--       have h2 : (stepWire w g).getD w.length false =
--           g.op.eval (g.inputs.map fun i => w.getD i false) := by
--         simp [stepWire, List.getD_eq_getElem?_getD]
--       rw [h2]
--       congr 1
--       apply List.map_congr_left
--       intro i _
--       by_cases hi : i < w.length
--       · simp only [hi, ↓reduceIte]
--         rw [foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
--         simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
--       · simp only [hi, ↓reduceIte]; exact getD_ge w i (by omega)
--     | succ j =>
--       have hj' : j < gs.length := by simpa using hj
--       have key := ih (stepWire w g) j hj'
--       have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
--       rw [hl] at key
--       have e : w.length + (j + 1) = w.length + 1 + j := by omega
--       simp only [List.getElem_cons_succ]
--       rw [e]
--       exact key
--
--
-- abbrev readWire (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) :=
--   PEqualNP.BlindGate.wireValue C n x w
--
-- theorem raw (C : Circuit) (n : ℕ) (x : Fin n → Bool) (v : Fin n) :
--     readWire C n x v.val = x v := by
--   unfold readWire PEqualNP.BlindGate.wireValue
--   rw [wires_eq_foldl,foldl_getD_lt _ _ _ (by simp)]
--   simp [List.getD_eq_getElem?_getD]
--
-- theorem atGate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : Fin C.size)
--     (bounded : ∀ u ∈ (C.gates.get j).inputs,u<n+j.val) :
--     readWire C n x (n+j.val) =
--       (C.gates.get j).op.eval ((C.gates.get j).inputs.map (readWire C n x)) := by
--   have h := foldl_getD_gate C.gates (List.ofFn x) j.val j.isLt
--   rw [List.length_ofFn] at h
--   refine h.trans ?_
--   congr 1
--   apply List.map_congr_left
--   intro u hu
--   simp only [bounded u hu, ↓reduceIte]
--   rfl
--
-- theorem maskReader (n : ℕ) (C : Circuit)
--     (bounded : ∀ j : Fin C.size,∀ u ∈ (C.gates.get j).inputs,u<n+j.val)
--     (v : Fin n) (i : Fin C.size) (w : ℕ) (x : Fin n → Bool)
--     (out : C.output ≠ v.val) (op : (C.gates.get i).op = GateOp.or)
--     (pins : (C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val])
--     (only : ∀ j : Fin C.size,j ≠ i → v.val ∉ (C.gates.get j).inputs)
--     (changes : C.eval (List.ofFn x) ≠ C.eval (List.ofFn (Function.update x v true))) :
--     readWire C n x w=false := by
--   by_contra fail
--   have on : readWire C n x w = true := by cases e : readWire C n x w <;> simp_all
--   let y := Function.update x v true
--   have sy : readWire C n y v.val=true := by rw [raw]; simp [y]
--   have agree (t : ℕ) : t ≠ v.val → readWire C n x t = readWire C n y t := by
--     induction t using Nat.strong_induction_on with
--     | _ t ih =>
--       intro different
--       by_cases small : t<n
--       · let a : Fin n := ⟨t,small⟩
--         change readWire C n x a.val=readWire C n y a.val
--         rw [raw,raw]
--         have ne : a ≠ v := fun eq => different (congrArg Fin.val eq)
--         simp [y,Function.update_of_ne ne]
--       by_cases large : n+C.gates.length≤t
--       · have z (s : Fin n → Bool) : readWire C n s t=false := by
--           unfold readWire PEqualNP.BlindGate.wireValue
--           rw [wires_eq_foldl]
--           apply getD_ge
--           simpa [foldl_length] using large
--         rw [z,z]
--       let j : Fin C.size := ⟨t-n,by change t-n < C.gates.length;omega⟩
--       have et : t=n+j.val := by dsimp [j];omega
--       rw [et,atGate C n x j (bounded j),atGate C n y j (bounded j)]
--       by_cases ji : j=i
--       · rw [ji,op]
--         rcases pins with pin|pin <;>
--           simp [pin,GateOp.eval,on,sy]
--       · congr 1
--         apply List.map_congr_left
--         intro u hu
--         have bound := bounded j u hu
--         exact ih u (by omega) (fun uv => only j ji (uv ▸ hu))
--   exact changes (agree C.output out)
--
-- end Eric.PetersenPorts
--
-- open PEqualNP.CircuitLowerBounds
-- set_option maxHeartbeats 3500000 in
-- set_option maxRecDepth 6000 in
-- theorem exactPortMask : ∀ (n : ℕ) (C : Circuit), (∀ j : Fin C.size,∀ u ∈ (C.gates.get j).inputs,u<n+j.val) →
--       ∀ (v : Fin n) (i : Fin C.size) (w : ℕ) (x : Fin n → Bool), (∃ z : Fin n → Bool,C.eval (List.ofFn z)≠z v) →
--       (C.gates.get i).op=GateOp.or →
--       ((C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val]) →
--       (∀ j : Fin C.size,j≠i → v.val∉(C.gates.get j).inputs) →
--       C.eval (List.ofFn x)≠C.eval (List.ofFn (Function.update x v true)) →
--       PEqualNP.BlindGate.wireValue C n x w=false := by
--   intro n C bound v i w x different op pins only changes
--   apply Eric.PetersenPorts.maskReader n C bound v i w x _ op pins only changes
--   intro out
--   obtain ⟨z,h⟩ := different
--   apply h
--   change Eric.PetersenPorts.readWire C n z C.output=z v
--   rw [out,Eric.PetersenPorts.raw]
--
-- -- Erasure lemmas adapted from Farodin-claude, upstream L_meta_2642.
-- namespace Eric.PetersenErase
--
-- open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves
--
--
-- def step (w : List Bool) (g : Gate) : List Bool :=
--   w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--
-- theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl
--
-- theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool),
--     ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length
--   | [], w => ⟨[], by simp⟩
--   | g :: gs, w => by
--     obtain ⟨t, ht, hl⟩ := fold_prefix gs (step w g)
--     refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
--     rw [List.foldl_cons, ht]
--     simp [step]
--
-- theorem fold_length (gs : List Gate) (w : List Bool) :
--     (gs.foldl step w).length = w.length + gs.length := by
--   obtain ⟨t, ht, hl⟩ := fold_prefix gs w
--   rw [ht, List.length_append, hl]
--
-- theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
--     (gs.foldl step w).getD i false = w.getD i false := by
--   obtain ⟨t, ht, -⟩ := fold_prefix gs w
--   rw [ht, List.getD_append _ _ _ _ hi]
--
-- theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false :=
--   List.getD_eq_default _ _ hi
--
--
--
--
-- def up (k i : ℕ) : ℕ := if i < k then i else i + 1
--
--
-- def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩
--
-- theorem up_redir (n m p r : ℕ) (hr : r ≠ n + m) : up (n + m) (eraseRedirect n m p r) = r := by
--   unfold up eraseRedirect
--   split_ifs <;> omega
--
-- theorem sim (n m p : ℕ) : ∀ (rest : List Gate) (U V : List Bool),
--     (∀ i, U.getD i false = V.getD (up (n + m) i) false) → n + m ≤ U.length →
--     V.length = U.length + 1 →
--     ((U.getD p false = V.getD (n + m) false ∧ (p < n + m ∨ U.length + rest.length < p)) ∨
--       ∀ g ∈ rest, n + m ∉ g.inputs) →
--     ∀ i, ((rest.map (ren n m p)).foldl step U).getD i false =
--       (rest.foldl step V).getD (up (n + m) i) false
--   | [], U, V, hrel, _, _, _ => by simpa using hrel
--   | g :: rest, U, V, hrel, hk, hlen, hS => by
--     have hread : ∀ r ∈ g.inputs, U.getD (eraseRedirect n m p r) false = V.getD r false := by
--       intro r hr
--       by_cases hrk : r = n + m
--       · subst hrk
--         rcases hS with ⟨hS, -⟩ | hS
--         · simpa [eraseRedirect] using hS
--         · exact absurd hr (hS g (List.mem_cons_self ..))
--       · rw [hrel, up_redir n m p r hrk]
--     set a := g.op.eval (g.inputs.map fun i => V.getD i false) with ha
--     have hU : step U (ren n m p g) = U ++ [a] := by
--       simp only [step, ren, List.map_map]
--       congr 3
--       exact List.map_congr_left fun r hr => hread r hr
--     have hV : step V g = V ++ [a] := rfl
--     simp only [List.map_cons, List.foldl_cons, hU, hV]
--     apply sim n m p rest
--     · intro i
--       rcases lt_trichotomy i U.length with hi | rfl | hi
--       · have hup : up (n + m) i < V.length := by unfold up; split_ifs <;> omega
--         rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hup, hrel]
--       · have hup : up (n + m) U.length = V.length := by unfold up; split_ifs <;> omega
--         rw [hup, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
--         simp
--       · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; unfold up; split_ifs <;> omega)]
--     · simp; omega
--     · simp; omega
--     · rcases hS with ⟨hS, hp⟩ | hS
--       · left
--         refine ⟨?_, ?_⟩
--         · rw [List.getD_append _ _ _ _ (by omega : n + m < V.length)]
--           rcases hp with hp | hp
--           · rw [List.getD_append _ _ _ _ (by omega)]; exact hS
--           · rw [getD_ge _ _ (by simp at hp ⊢; omega)]
--             rw [getD_ge _ _ (by simp at hp ⊢; omega)] at hS
--             exact hS
--         · rcases hp with hp | hp
--           · exact Or.inl hp
--           · right; simp at hp ⊢; omega
--       · exact Or.inr fun g' hg' => hS g' (List.mem_cons_of_mem _ hg')
--
-- theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
--     (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) ∧
--     (eraseGate n C m p).output = eraseRedirect n m p C.output := by
--   unfold eraseGate
--   rw [if_pos hm]
--   exact ⟨rfl, rfl⟩
--
-- theorem erase_eval (n : ℕ) (C : Circuit) (m p : ℕ) (y : List Bool) (hy : y.length = n)
--     (hm : m < C.gates.length) (hp : p < n + m ∨ n + C.gates.length ≤ p)
--     (hc : (C.wires y).getD (n + m) false = (C.wires y).getD p false ∨
--       (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs)) :
--     (eraseGate n C m p).eval y = C.eval y := by
--   obtain ⟨hg, ho⟩ := erase_gates n C m p hm
--   have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
--     rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
--   set A := (C.gates.take m).foldl step y with hA
--   have hAl : A.length = n + m := by
--     rw [hA, fold_length, hy, List.length_take]; omega
--   set rest := C.gates.drop (m + 1) with hrest
--   have hrl : rest.length = C.gates.length - (m + 1) := List.length_drop
--   have hW : C.wires y = rest.foldl step (step A C.gates[m]) := by
--     rw [wires_eq]
--     conv_lhs => rw [hsplit]
--     rw [List.foldl_append, List.foldl_cons]
--   have hW' : (eraseGate n C m p).wires y = (rest.map (ren n m p)).foldl step A := by
--     rw [wires_eq, hg, List.foldl_append]
--   have hVl : (step A C.gates[m]).length = A.length + 1 := by simp [step]
--   have hWl : (C.wires y).length = n + C.gates.length := by
--     rw [wires_eq, fold_length, hy]
--   have hstable : ∀ i, i < n + m + 1 → (step A C.gates[m]).getD i false = (C.wires y).getD i false := by
--     intro i hi
--     rw [hW, fold_getD_lt _ _ _ (by omega)]
--   have hsim := sim n m p rest A (step A C.gates[m]) (by
--       intro i
--       by_cases hi : i < n + m
--       · simp only [up, if_pos hi, step]
--         rw [List.getD_append _ _ _ _ (by omega)]
--       · simp only [up, if_neg hi]
--         rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)])
--     (by omega) hVl (by
--       rcases hc with hc | ⟨-, hc⟩
--       · left
--         refine ⟨?_, ?_⟩
--         · rw [hstable _ (by omega)]
--           rcases hp with hp | hp
--           · rw [hc, ← hstable _ (by omega), step, List.getD_append _ _ _ _ (by omega)]
--           · rw [getD_ge _ _ (by omega), hc, getD_ge _ _ (by omega)]
--         · rcases hp with hp | hp
--           · exact Or.inl hp
--           · right; omega
--       · exact Or.inr hc)
--   unfold Circuit.eval
--   rw [ho, hW', hsim, ← hW]
--   by_cases hout : C.output = n + m
--   · rcases hc with hc | ⟨hc, -⟩
--     · have hr : eraseRedirect n m p C.output = p := by
--         unfold eraseRedirect; rw [if_pos hout]
--       rw [hr, hout]
--       rcases hp with hp | hp
--       · have hu : up (n + m) p = p := by unfold up; rw [if_pos hp]
--         rw [hu]; exact hc.symm
--       · have hu : up (n + m) p = p + 1 := by unfold up; rw [if_neg (by omega)]
--         rw [hu, hc, getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
--     · exact absurd hout hc
--   · rw [up_redir n m p _ hout]
--
-- theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
--     (eraseGate n C m p).size + 1 = C.size := by
--   unfold Circuit.size
--   rw [(erase_gates n C m p hm).1]
--   simp
--   omega
--
-- theorem erase_fanin (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
--     (hC : PEqualNP.MetaComplexity.FanInTwo C) :
--     PEqualNP.MetaComplexity.FanInTwo (eraseGate n C m p) := by
--   intro g hg
--   rw [(erase_gates n C m p hm).1, List.mem_append] at hg
--   rcases hg with hg | hg
--   · exact hC g (List.mem_of_mem_take hg)
--   · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
--     obtain ⟨h1, h2⟩ := hC g' (List.mem_of_mem_drop hg')
--     exact ⟨h1, by simpa [ren] using h2⟩
-- end Eric.PetersenErase
--
-- namespace Eric.PetersenPorts
--
-- open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves
-- open Eric.PetersenErase
--
-- theorem useful (n : ℕ) (C : Circuit) (minimal : IsMinimalCircuit n C)
--     (i : Fin C.size) (v : Fin n) (w : ℕ)
--     (bounded : ∀ t ∈ (C.gates.get i).inputs,t<n+i.val)
--     (op : (C.gates.get i).op=.or)
--     (pins : (C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val]) :
--     ∃ x : Fin n → Bool, readWire C n x w=true := by
--   by_contra no
--   have zero (x : Fin n → Bool) : readWire C n x w=false := by
--     cases val : readWire C n x w with
--     | false => rfl
--     | true => exact False.elim (no ⟨x,val⟩)
--   let D := eraseGate n C i.val v.val
--   have eqfun : circuitFun n D=circuitFun n C := by
--     funext x
--     change (eraseGate n C i.val v.val).eval (List.ofFn x)=C.eval (List.ofFn x)
--     apply erase_eval n C i.val v.val (List.ofFn x) (by simp) i.isLt (Or.inl (by omega))
--     left
--     change readWire C n x (n+i.val)=readWire C n x v.val
--     rw [atGate C n x i bounded,op]
--     rcases pins with pin|pin <;> simp [pin,GateOp.eval,zero x]
--   have less := minimal.2 D (erase_fanin n C i.val v.val i.isLt minimal.1) eqfun
--   have sz := erase_size n C i.val v.val i.isLt
--   change C.size ≤ (eraseGate n C i.val v.val).size at less
--   have hi : i.val<C.size := i.isLt
--   omega
--
-- end Eric.PetersenPorts
--
--
-- open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
--
-- namespace Eric.PetersenSeven
--
-- def edge (m : Nat) := ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
--   (fun e => (m &&& e) == e)
--
-- def pairs (v : Fin 9) : List Nat := if v=4 then [14,16,24,26,51,71,61] else if v=6 then [2,7,22,32,34,41,43] else [6,8,12,13,33,44,42]
--
-- def samples (v : Fin 9) : List Nat := if v=4 then [42,69,104,138,261,385,201] else if v=6 then [42,50,138,261,276,385,402] else [42,50,69,104,261,276,116]
--
-- def hits (m j : Nat) : Bool := m.testBit (j / 9) && m.testBit (j % 9)
--
-- set_option maxRecDepth 6000 in
-- set_option maxHeartbeats 3500000 in
-- theorem sevenNecessary : ∀ v : Fin 9,v ∈ [4,6,7] →
--   (pairs v).Nodup ∧ (pairs v).length=7 ∧
--   ((pairs v).all (fun j => (samples v).any (fun m => !m.testBit v.val && !edge m &&
--     edge (m ||| (2^v.val)) && hits m j)))=true ∧
--   ∀ m : Fin 512,m.val.testBit v.val=false → edge m.val=false → edge (m.val ||| (2^v.val))=true →
--     ((pairs v).filter (hits m.val)).length≤1 := by decide +kernel
--
-- end Eric.PetersenSeven
