import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- On pinning a vertex, equal wire functions can be represented by a single wire.
-- The zero cofactor is the Petersen graph minus a vertex. The positive cofactor
-- consists of three singleton terms and the six-cycle outside the closed neighbourhood.
-- Every input pin is tested, on each of the two values.
theorem PEqualNP.Outside.R_meta_651_427
    (compress : ∀ (n m : ℕ) (C : Circuit) (a : Fin m→(Fin n→Bool)→Bool),
    let A:=((Finset.univ.image (fun i : Fin n=>fun x : Fin n→Bool=>x i)) ∪ {fun _=>false,fun _=>true} : Finset ((Fin n→Bool)→Bool))
    let w:=fun (j : ℕ) (x : Fin n→Bool)=>(C.wires (List.ofFn (fun k=>a k x))).getD (m+j) false
    let f:=fun x : Fin n→Bool=>C.eval (List.ofFn (fun k=>a k x))
    (∀i,a i∈A) → (∃x y,f x≠f y) → FanInTwo C →
      HasCircuitSize n f ((((Finset.range C.size).image w) \ A).card))
    (deleted : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (positive : ¬ HasCircuitSize 9 (fun x : Fin 9→Bool => x 4 || x 6 || x 7 || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0)) 10)
    (remaining : ∀ C : Circuit,
    let A:=((Finset.univ.image (fun i : Fin 10=>fun x : Fin 10→Bool=>x i)) ∪ {fun _=>false,fun _=>true} : Finset ((Fin 10→Bool)→Bool))
    let size:=fun (p : Fin 10) (b : Bool)=>(((Finset.range C.size).image (fun j=>fun x : Fin 10→Bool=>
      (C.wires (List.ofFn (Function.update x p b))).getD (10+j) false)) \ A).card
    FanInTwo C → C.size≤19 → (∀p,16≤size p false ∧ 11≤size p true) →
    ¬(∀x,C.eval (List.ofFn x)=(fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 19 := by
  rintro ⟨C,hc,small,eval⟩
  let F:=(fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let G:=(fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let H:=(fun x : Fin 9→Bool => x 4 || x 6 || x 7 || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0))
  let perm : Fin 10→Fin 10→Fin 10 := ![![9,4,0,1,6,7,3,5,2,8],![4,9,6,1,0,3,7,8,2,5],![0,4,9,6,1,5,3,7,8,2],![0,1,6,9,4,5,2,8,7,3],![4,0,1,6,9,3,5,2,8,7],![4,0,1,2,3,9,5,6,7,8],![0,4,3,2,1,5,9,8,7,6],![0,1,6,8,5,4,2,9,3,7],![0,1,2,7,5,4,6,3,9,8],![0,1,2,3,4,5,6,7,8,9]]
  have last : ∀p,perm p p=Fin.last 9 := by simp only [perm]; decide +kernel
  have sym : ∀p (x : Fin 10→Bool), F (x ∘ perm p)=F x := by
    intro p; fin_cases p <;> intro x
    · change ((x 9 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && x 9) || (x 9 && x 7) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 4 && x 9) || (x 9 && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 9 && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 0 && x 5) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 0 && x 4) || (x 4 && x 9) || (x 9 && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && x 3) || (x 9 && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 9) || (x 9 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (x 9 && x 7) || (x 4 && x 3) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && x 9) || (x 9 && x 4) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (x 9 && x 7) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 4 && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 9) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 9)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 7) || (x 7 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 2) || (x 6 && x 9) || (x 8 && x 3) || (x 5 && x 7) || (x 4 && x 9) || (x 9 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && x 9) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
  have lo : ∀x : Fin 9→Bool,F (Fin.snoc x false)=G x := by simp only [F,G]; decide +kernel
  have hi : ∀x : Fin 9→Bool,F (Fin.snoc x true)=H x := by simp only [F,H]; decide +kernel
  have sep : ∀ b : Bool,F (Fin.snoc (fun _=>false) b)≠F (Fin.snoc (fun _=>true) b) := by simp only [F]; decide +kernel
  have sep2 : ∀ (p : Fin 10) (b : Bool), F (Function.update (fun _=>false) p b)≠F (Function.update (fun _=>true) p b) := by simp only [F]; decide +kernel
  let base (n : ℕ) := ((Finset.univ.image (fun i : Fin n=>fun x : Fin n→Bool=>x i)) ∪
    {fun _=>false,fun _=>true} : Finset ((Fin n→Bool)→Bool))
  have bound (D : Circuit) (a : Fin 10→(Fin 9→Bool)→Bool)
      (raw : ∀i,a i∈base 9) (f : (Fin 9→Bool)→Bool)
      (sem : ∀ x,D.eval (List.ofFn (fun i=>a i x))=f x) (law : FanInTwo D) (nc : ∃x y,f x≠f y) :
      HasCircuitSize 9 f D.size := by
    let vals (j : ℕ) (x : Fin 9→Bool):=(D.wires (List.ofFn (fun i=>a i x))).getD (10+j) false
    obtain ⟨B,ok,sz,val⟩:=compress 9 10 D a raw (by simpa only [sem] using nc) law
    have card : (((Finset.range D.size).image vals) \ base 9).card≤D.size :=
      (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_image_le).trans (by simp))
    exact ⟨B,ok,sz.trans card,fun x=>(val x).trans (sem x)⟩
  have position (p : Fin 10) (b : Bool) (D : Circuit) (law : FanInTwo D)
      (sem : ∀x : Fin 10→Bool,D.eval (List.ofFn x)=F (Function.update x p b)) :
      HasCircuitSize 9 (fun x=>F (Fin.snoc x b)) D.size := by
    let a (i : Fin 10) (x : Fin 9→Bool) := (Fin.snoc x b : Fin 10→Bool) (perm p i)
    have source (i : Fin 10) : a i∈base 9 := by
      have raw (j : Fin 10) : (fun x : Fin 9→Bool=>(Fin.snoc x b : Fin 10→Bool) j)∈base 9 := by
        refine Fin.lastCases ?_ (fun k=>?_) j
        · cases b <;> simp only [Fin.snoc_last] <;> simp [base]
        · simp only [Fin.snoc_castSucc]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
      exact raw _
    refine bound D a source _ ?_ law ?_
    · intro x
      let y:=Fin.snoc x b ∘ perm p
      have yp:y p=b:=by simp only [y,Function.comp_apply,last,Fin.snoc_last]
      have pin:Function.update y p b=y:=by rw [←yp,Function.update_eq_self]
      change D.eval (List.ofFn y)=_
      rw [sem,pin,show F y=F (Fin.snoc x b) from sym ..]
    · exact ⟨fun _=>false,fun _=>true,sep b⟩
  apply remaining C hc small _ eval
  intro p
  let width (b : Bool) := (((Finset.range C.size).image (fun j=>fun x : Fin 10→Bool=>
    (C.wires (List.ofFn (Function.update x p b))).getD (10+j) false)) \ base 10).card
  have project (b : Bool) : HasCircuitSize 9 (fun x=>F (Fin.snoc x b)) (width b) := by
    let a (i : Fin 10) (x : Fin 10→Bool) := Function.update x p b i
    have raw (i) : a i∈base 10 := by
      by_cases e:i=p
      · subst i; cases b <;> simp [a,base]
      · have arg:a i=(fun x=>x i):=by funext x; simp [a,e]
        rw [arg]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    have var : ∃x y : Fin 10→Bool, C.eval (List.ofFn (fun i=>a i x))≠C.eval (List.ofFn (fun i=>a i y)) := by
      refine ⟨fun _=>false,fun _=>true,?_⟩
      change C.eval (List.ofFn (Function.update (fun _=>false) p b))≠C.eval (List.ofFn (Function.update (fun _=>true) p b))
      rw [eval,eval]
      exact sep2 p b
    obtain ⟨D,law,size,sem⟩:=compress 10 10 C a raw var hc
    have eq (x : Fin 10→Bool) : D.eval (List.ofFn x)=F (Function.update x p b) := (sem x).trans (eval _)
    obtain ⟨B,lawB,bs,val⟩:=position p b D law eq
    exact ⟨B,lawB,bs.trans size,val⟩
  change 16 ≤ width false ∧ 11 ≤ width true
  constructor
  · by_contra! tiny
    obtain ⟨B,law,sz,sem⟩:=project false
    exact deleted ⟨B,law,sz.trans (show width false≤15 by omega),fun y=>(sem y).trans (lo y)⟩
  · by_contra! tiny
    obtain ⟨B,law,sz,sem⟩:=project true
    exact positive ⟨B,law,sz.trans (show width true≤10 by omega),fun y=>(sem y).trans (hi y)⟩
