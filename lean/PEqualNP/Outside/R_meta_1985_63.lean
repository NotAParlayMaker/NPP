import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Earlier gates produce a register bank. The marked AND costs one further gate.
-- Switching off the marked gate forecloses a genuine pair if the output then goes dark.
-- Every earlier AND is silent on every wrong pair, not just on the marked one's witness.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1985_63
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      Monotone2 C → ReadsBack n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, D.size = C.size ∧ Monotone2 D ∧ ReadsBack n D ∧ circuitFun n D = graphFun G ∅ ∧
        ∀ j < D.size, (gateAt D j).op = .and →
        (∃ u v, ¬ G.Adj u v ∧ gateVal n D j (pairInput u v) = true) →
        let foreclosed := fun a b : Fin n => G.Adj a b ∧ circuitFun n ⟨D.gates.set j ⟨.or,[]⟩,D.output⟩ (pairInput a b) = false
        ∃ a b c d, foreclosed a b ∧ foreclosed c d ∧ s(a,b) ≠ s(c,d))
    (clean : ∀ D : Circuit,
      let rows := [11,69,98,49,88,44,22]
      let E := (List.range 7).flatMap fun p => ((List.range 7).filter (fun l => (rows.getD p 0).testBit l)).map (fun l => (p,7+l))
      let G := edgeGraph 14 E
      Monotone2 D → circuitFun 14 D = graphFun G ∅ →
      (∀ j < D.size, (gateAt D j).op = .and → ∀ u v, gateVal 14 D j (pairInput u v) = true → G.Adj u v) → 27 ≤ D.size)
    (twoPulse : ∀ (P S : Circuit) (ks : List ℕ),
      let rows := [11,69,98,49,88,44,22]
      let E := (List.range 7).flatMap fun p => ((List.range 7).filter (fun l => (rows.getD p 0).testBit l)).map (fun l => (p,7+l))
      let G := edgeGraph 14 E
      let bank := fun x : Fin 14 → Bool => P.wires (List.ofFn x)
      let tap := fun x => GateOp.and.eval (ks.map (fun i => (bank x).getD i false))
      let go := fun x b => S.eval (bank x ++ [b])
      Monotone2 P → Monotone2 S → ks.length ≤ 2 → (∀ i ∈ ks, i < 14+P.size) →
      (∀ x, go x (tap x) = graphFun G ∅ x) →
      (∀ j < P.size, (gateAt P j).op = .and → ∀ u v, gateVal 14 P j (pairInput u v) = true → G.Adj u v) →
      (∃ u v, ¬ G.Adj u v ∧ tap (pairInput u v) = true) →
      (∃ a b c d, G.Adj a b ∧ G.Adj c d ∧ s(a,b) ≠ s(c,d) ∧ go (pairInput a b) false = false ∧ go (pairInput c d) false = false) →
      26 ≤ P.size+S.size) :
    ∀ C : Circuit, Monotone2 C → ReadsBack 14 C →
    (∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 14 C i j) →
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val,v.val) ∈
      [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] ∧ x u = true ∧ x v = true) → 27 ≤ C.size := by
  classical
  intro C mono back _ exactC
  let rows := [11,69,98,49,88,44,22]
  let E := (List.range 7).flatMap fun p => ((List.range 7).filter (fun l => (rows.getD p 0).testBit l)).map (fun l => (p,7+l))
  let G := edgeGraph 14 E
  have listed : E = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)] := by decide
  have unequal : ∀ a b : Fin 14, (a.val,b.val) ∈ E → a ≠ b := by decide
  have correct : circuitFun 14 C=graphFun G ∅ := by
    funext x; apply Bool.eq_iff_iff.mpr
    rw [show circuitFun 14 C x=C.eval (List.ofFn x) from rfl,exactC,←listed]
    delta graphFun
    simp only [Finset.notMem_empty,Bool.false_or,false_and,exists_false,decide_false,decide_eq_true_eq]
    constructor
    · rintro ⟨a,b,edge,ha,hb⟩; exact ⟨a,b,⟨unequal a b edge,Or.inl edge⟩,ha,hb⟩
    · rintro ⟨a,b,⟨_,edge|edge⟩,ha,hb⟩; exact ⟨a,b,edge,ha,hb⟩; exact ⟨b,a,edge,hb,ha⟩
  obtain ⟨D,size,dm,db,df,norm⟩ := normalize 14 G C mono back correct
  let bad := fun j : ℕ => j<D.size ∧ (gateAt D j).op=.and ∧ ∃ u v, ¬ G.Adj u v ∧ gateVal 14 D j (pairInput u v)=true
  by_cases existsBad : ∃j,bad j
  swap
  · rw [←size]; apply clean D dm df
    intro j hj op u v on_; by_contra wrong; exact existsBad ⟨j,hj,op,u,v,wrong,on_⟩
  let j := Nat.find existsBad
  obtain ⟨hj,andG,u,v,wrong,leak⟩ := (show bad j from Nat.find_spec existsBad)
  obtain ⟨a,b,c,d,⟨ab,off1⟩,⟨cd,off2⟩,ne⟩ := norm j hj andG ⟨u,v,wrong,leak⟩
  let P : Circuit := ⟨D.gates.take j,0⟩
  let S : Circuit := ⟨D.gates.drop (j+1),D.output⟩
  let g := gateAt D j
  have hj' : j<D.gates.length := hj
  have plen : P.gates.length=j := by simp [P,Nat.min_eq_left hj'.le]
  have split : D.gates=P.gates++g::S.gates := by
    change D.gates=D.gates.take j++(D.gates.getD j _)::D.gates.drop (j+1)
    rw [List.getD_eq_getElem _ _ hj',←List.drop_eq_getElem_cons hj',List.take_append_drop]
  have pm : Monotone2 P := fun z hz=>dm z (List.mem_of_mem_take hz)
  have sm : Monotone2 S := fun z hz=>dm z (List.mem_of_mem_drop hz)
  have member : g∈D.gates := by rw [split]; simp
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl (fun t z => t ++ [z.op.eval (z.inputs.map (fun i=>t.getD i false))]) w
  have rlen (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons z zs ih => change (run zs (w++[_])).length=_; rw [ih]; simp;omega
  have stays (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i<w.length) : (run gs w).getD i false=w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons z zs ih => change (run zs (w++[_])).getD i false=_; rw [ih _ (by simp;omega)]
                      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
  let bank := fun x : Fin 14→Bool=> P.wires (List.ofFn x)
  let tap := fun x=> GateOp.and.eval (g.inputs.map (fun i=>(bank x).getD i false))
  let go := fun x b=> S.eval (bank x++[b])
  have bl (x) : (bank x).length=14+j := by change (run P.gates _).length=_; rw [rlen,plen,List.length_ofFn]
  have appendRun (l r : List Gate) (w : List Bool) : run (l++r) w=run r (run l w) := by simp only [run,List.foldl_append]
  have expanded (x : Fin 14→Bool) : D.wires (List.ofFn x)=run S.gates (bank x++[tap x]) := by
    change run D.gates (List.ofFn x)=_; rw [split,appendRun]
    change run S.gates (bank x++[g.op.eval (g.inputs.map (fun i=>(bank x).getD i false))])=_
    rw [show g.op=.and from andG]
  have hit (x : Fin 14→Bool) : gateVal 14 D j x=tap x := by
    change (D.wires (List.ofFn x)).getD (14+j) false=_
    rw [expanded,stays _ _ _ (by simp [bl])];simp [List.getD_eq_getElem?_getD,←bl x]
  have offEq (x : Fin 14→Bool) : circuitFun 14 ⟨D.gates.set j ⟨.or,[]⟩,D.output⟩ x = go x false := by
    change (run (D.gates.set j _) (List.ofFn x)).getD D.output false=_
    have replaced : (P.gates++g::S.gates).set P.gates.length ⟨.or,[]⟩ = P.gates++⟨.or,[]⟩::S.gates := by simp [List.set_append_right]
    rw [split,←plen,replaced,appendRun];rfl
  have preVal (i : ℕ) (hi : i<P.size) (x : Fin 14→Bool) : gateVal 14 P i x=gateVal 14 D i x := by
    change (P.wires (List.ofFn x)).getD (14+i) false=(D.wires (List.ofFn x)).getD (14+i) false
    rw [expanded,stays _ _ _ (by change i<P.gates.length at hi; simp [bl];omega)]
    change (bank x).getD (14+i) false=_
    have ht : 14+i < (bank x).length := by rw [bl];change i<P.gates.length at hi;omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left ht]
  have cost := twoPulse P S g.inputs pm sm (dm g member).2 (fun i hi=>by change i<14+P.gates.length; rw [plen];exact db j hj i hi)
    (fun x=>by change go x (tap x)=_; rw [←congrFun df]; change _=(D.wires (List.ofFn x)).getD _ false; rw [expanded];rfl)
    (fun i hi op u' v' on_=>by
      have ilt : i<j := by change i<P.gates.length at hi;omega
      have oa : (gateAt D i).op=.and := by
        delta gateAt at op ⊢
        simpa only [P,List.getD_eq_getElem?_getD,List.getElem?_take_of_lt ilt] using op
      by_contra wrong';exact Nat.find_min existsBad ilt ⟨by omega,oa,u',v',wrong',(preVal i hi _).symm.trans on_⟩)
    ⟨u,v,wrong,(hit _).symm.trans leak⟩
    ⟨a,b,c,d,ab,cd,ne,(offEq _).symm.trans off1,(offEq _).symm.trans off2⟩
  rw [←size];change 27≤D.gates.length; rw [split]
  change 26≤P.gates.length+S.gates.length at cost; simp only [List.length_append,List.length_cons];omega
