import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_2375_619
    (charge : ∀(C:Circuit)(a b:Nat),FanInTwo C → let w:=fun (j:Nat) (x:Fin 10→Bool)=>(C.wires (List.ofFn x)).getD j false
    let F:=fun (x:Fin 10→Bool)=> ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]:List Nat).any (fun e=>x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
    let set:=fun (x:Fin 10→Bool) (p:Fin 10) (b:Bool) (j:Fin 10)=> if j=p then b else x j
    let blind:=fun (f:(Fin 10→Bool)→Bool) (p:Fin 10)=>∀ x b,f (set x p b)=f x
    (∃x,w a x=true ∧ w b x=false) → (∃x,w a x=false ∧ w b x=true) → (∀x,(w a x && w b x)=F x) → 14≤a ∧ ((∀p,¬blind (w b) p) → 18≤b) ∧ ((∃p,blind (w a) p) → 19≤b))
    (count : ∀(p q:Fin 10),let F:=fun (x:Fin 10→Bool)=> ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]:List Nat).any (fun e=>x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
    let set:=fun (x:Fin 10→Bool) (p:Fin 10) (b:Bool) (j:Fin 10)=> if j=p then b else x j
    ∃T:Finset (Fin 10→Bool), T.card≤(if p=q then 18 else 5) ∧ ∀y,y p=false → y q=false → F (set (set y p true) q true)=false → y∈T)
    (both : ∀(C:Circuit)(a b:Nat),FanInTwo C → C.size≤18 → 14≤a → 18≤b → let w:=fun (j:Nat) (x:Fin 10→Bool)=>(C.wires (List.ofFn x)).getD j false
    let F:=fun (x:Fin 10→Bool)=> ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]:List Nat).any (fun e=>x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
    let set:=fun (x:Fin 10→Bool) (p:Fin 10) (b:Bool) (j:Fin 10)=> if j=p then b else x j
    let blind:=fun (f:(Fin 10→Bool)→Bool) (p:Fin 10)=>∀ x b,f (set x p b)=f x
    (∃x,w a x=true ∧ w b x=false) → (∃x,w a x=false ∧ w b x=true) → (∀p,¬blind (w b) p) → (∀p,¬blind (w a) p) → ¬(∀x,(w a x && w b x)=F x))
    (partialCase : ∀(C:Circuit)(a b:Nat),FanInTwo C → C.size≤18 → 14≤a → 19≤b → let w:=fun (j:Nat) (x:Fin 10→Bool)=>(C.wires (List.ofFn x)).getD j false
    let F:=fun (x:Fin 10→Bool)=> ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]:List Nat).any (fun e=>x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
    let set:=fun (x:Fin 10→Bool) (p:Fin 10) (b:Bool) (j:Fin 10)=> if j=p then b else x j
    let blind:=fun (f:(Fin 10→Bool)→Bool) (p:Fin 10)=>∀ x b,f (set x p b)=f x
    (∃x,w a x=true ∧ w b x=false) → (∃x,w a x=false ∧ w b x=true) → (∀p,¬blind (w b) p) → ∀(p q:Fin 10)(S:Finset (Fin 10→Bool)), (p=q → ∀r,blind (w a) r → r=p) → (S.card≤(if p=q then 18 else 5) ∧ (∀y∈S,F (set (set y p true) q true)=false) ∧ ∀x,w a x=decide (set (set x p false) q false ∉ S)) → ¬(∀x,(w a x && w b x)=F x)) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  intro g C a b fg fc cap
  dsimp only
  intro apart apart' sound
  by_contra! fail
  let P:Circuit:=⟨g::C.gates,0⟩
  let w := fun (j:Nat) (x:Fin 10→Bool)=>(P.wires (List.ofFn x)).getD j false
  let F := fun (x:Fin 10→Bool)=> ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]:List Nat).any (fun e=>x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  let set := fun (x:Fin 10→Bool) (p:Fin 10) (b:Bool) (j:Fin 10)=> if j=p then b else x j
  let blind := fun (f:(Fin 10→Bool)→Bool) (p:Fin 10)=>∀ x b,f (set x p b)=f x
  have fp:FanInTwo P:=by
    intro k hk
    rcases List.mem_cons.mp hk with rfl|hk
    · exact fg _ List.mem_cons_self
    · exact fc _ hk
  have total:P.size≤18:=by change C.gates.length≤17 at cap;change (g::C.gates).length≤18;simp;omega
  have eqGraph : ∀x:Fin 10→Bool,F x = (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))) := by decide +kernel
  have valid (x:Fin 10→Bool) : (w a x && w b x)=F x:=by
    have t:=sound x;have z:=fail x
    change (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))=true → w a x=true ∧ w b x=true at t
    change (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))=false → w a x=true → w b x≠true at z
    rw [←eqGraph x] at t z
    cases e:F x with
    | true => obtain ⟨wa,wb⟩:=t e;simp [wa,wb]
    | false =>
      cases h:w a x
      · simp
      · simp [Bool.eq_false_iff.mpr (z e h)]
  change ∃x,w a x=true ∧ w b x=false at apart
  change ∃x,w a x=false ∧ w b x=true at apart'
  have table (A B : (Fin 10→Bool)→Bool) (i j:Fin 10) (joint:∀x,(A x && B x)=F x)
      (hi:blind A i) (hj:blind A j) : ∃S:Finset (Fin 10→Bool),S.card≤(if i=j then 18 else 5) ∧ (∀y∈S,y i=false ∧ y j=false ∧ F (set (set y i true) j true)=false) ∧ ∀x,A x=decide (set (set x i false) j false ∉ S) :=by
    classical
    obtain ⟨roster,cap,complete⟩:=count i j
    let S:=roster.filter (fun y=>y i=false ∧ y j=false ∧ F (set (set y i true) j true)=false ∧ A y=false)
    refine ⟨S,(Finset.card_le_card (Finset.filter_subset _ _)).trans cap,?_,?_⟩
    · intro y hy
      obtain ⟨_,z1,z2,neg,_⟩:=Finset.mem_filter.mp hy
      exact ⟨z1,z2,neg⟩
    · intro x
      let y:=set (set x i false) j false
      have ey:A y=A x:=(hj _ _).trans (hi _ _)
      change A x = decide (y∉S)
      cases e:A x with
      | true =>
        apply (decide_eq_true _).symm
        intro mem
        exact Bool.noConfusion (((Finset.mem_filter.mp mem).2.2.2.2).symm.trans (ey.trans e))
      | false =>
        have raised:A (set (set y i true) j true)=false:=(hj _ _).trans ((hi _ _).trans (ey.trans e))
        have neg:F (set (set y i true) j true)=false:=by rw [←joint,raised];rfl
        have zeros:y i=false ∧ y j=false:=by by_cases same:i=j <;> simp [y,set,same]
        have mem:y∈S:=Finset.mem_filter.mpr ⟨complete _ zeros.1 zeros.2 neg,zeros.1,zeros.2,neg,ey.trans e⟩
        simp [mem]
  let tie := fun (p q:Fin 10) (r:Fin 10)=>(([2,20,2,16,10,130,2,32,32,16,20,1,9,4,1,1,257,4,64,64,2,9,2,18,8,128,2,34,8,128,16,4,18,4,5,256,256,4,36,16,10,1,8,5,1,1,512,512,8,65,130,1,128,256,1,1,256,5,9,128,2,257,2,256,512,256,2,512,10,18,32,4,34,4,512,5,512,4,32,20,32,64,8,36,8,9,10,32,8,64,16,64,128,16,65,128,18,20,64,16]:List Nat).getD (10*p.val+q.val) 0).testBit r.val
  have ties : ∀p q:Fin 10,F (tie p q)=false ∧ F (set (tie p q) p true)=true ∧ F (set (tie p q) q true)=true :=by decide +kernel
  have full : (∀p,¬blind (w a) p) ∨ (∀p,¬blind (w b) p) :=by
    by_cases h:∀p,¬blind (w a) p
    · exact Or.inl h
    push_neg at h
    obtain ⟨p,hp⟩:=h
    right
    intro q hq
    obtain ⟨off,pOn,qOn⟩:=ties p q
    have ax: w a (tie p q)=true:=(hp _ _).symm.trans (Bool.and_eq_true_iff.mp ((valid _).trans pOn)).1
    have bx: w b (tie p q)=true:=(hq _ _).symm.trans (Bool.and_eq_true_iff.mp ((valid _).trans qOn)).2
    have impossible:=valid (tie p q)
    rw [ax,bx,off] at impossible
    contradiction
  have finish (i j:Nat)
      (ab:∃x,w i x=true ∧ w j x=false) (ba:∃x,w i x=false ∧ w j x=true)
      (joint:∀x,(w i x && w j x)=F x) (allJ:∀p,¬blind (w j) p):False:=by
    obtain ⟨li,base,strong⟩:=charge P i j fp ab ba joint
    have lj:=base allJ
    by_cases allI:∀p,¬blind (w i) p
    · exact both P i j fp total li lj ab ba allJ allI joint
    push_neg at allI
    obtain ⟨p,miss⟩:=allI
    have strongJ:=strong ⟨p,miss⟩
    by_cases more:∃q:Fin 10,q≠p ∧ blind (w i) q
    · obtain ⟨q,diff,hq⟩:=more
      obtain ⟨S,small⟩:=table (w i) (w j) p q joint miss hq
      exact partialCase P i j fp total li strongJ ab ba allJ p q S (fun eq=>False.elim (diff eq.symm)) ⟨small.1,fun y hy=>(small.2.1 y hy).2.2,small.2.2⟩ joint
    · obtain ⟨S,small⟩:=table (w i) (w j) p p joint miss miss
      exact partialCase P i j fp total li strongJ ab ba allJ p p S (fun _ r hr=>Classical.byContradiction (fun nr=>more ⟨r,nr,hr⟩)) ⟨small.1,fun y hy=>(small.2.1 y hy).2.2,small.2.2⟩ joint
  rcases full with hu|hv
  · obtain ⟨x,ax,bx⟩:=apart
    obtain ⟨y,ay,by'⟩:=apart'
    exact finish b a ⟨y,by',ay⟩ ⟨x,bx,ax⟩ (fun x=>by rw [Bool.and_comm];exact valid x) hu
  · exact finish a b apart apart' valid hv
