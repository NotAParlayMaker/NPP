import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2602_493
  (collision : ∀ (C : Circuit) (p q : ℕ) (d K : ℕ → Bool),
  let v (p w : ℕ) := (C.wires (List.ofFn fun i : Fin 26=>decide (i.val=p))).getD w false
  let G := gateAt C
  (∀ (i : ℕ) (g : Gate), C.gates[i]?=some g →
    (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ,g.inputs=[a,b] ∧ a≠b ∧ a<26+i ∧ b<26+i) → C.output<26+C.size → (∀w<26,d w=decide (w=q)) → (∀ (i : ℕ) (g : Gate) (a b : ℕ), C.gates[i]?=some g → g.inputs=[a,b] →
    (g.op=.and → d (26+i)=(v p a && d b || d a && v p b)) ∧ (g.op=.or → d (26+i)=(d a || d b))) →
  K C.output=true → (∀w<26,K w=true → w=p ∨ w=q) → (∀ i : Fin C.size,K (26+i.val)=true → (G i.val).op.eval ((G i.val).inputs.map K)=true) →
  v p C.output=false → d C.output=false →
  ∃i : Fin C.size,K (26+i.val)=true ∧ (G i.val).op=GateOp.and ∧
    ((G i.val).inputs.map (v p)).any id=false)
  (mixed : ∀ C : Circuit,
  let v (p w : ℕ) := (C.wires (List.ofFn fun i : Fin 26=>decide (i.val=p))).getD w false
  let G := gateAt C
  let trace (K : ℕ → Bool) := K C.output=true ∧ (∀ w<26,K w=true → w=0 ∨ w=13) ∧ (∀ i : Fin C.size,K (26+i.val)=true → (G i.val).op.eval ((G i.val).inputs.map K)=true)
  let bad (p : ℕ) (i : Fin C.size) := (G i.val).op=GateOp.and ∧
    ((G i.val).inputs.map (v p)).any id=false
  (63 ≤ C.size ∧ C.size ≤ 64) → IsAO2 26 C → (∀i : Fin C.size,(G i.val).inputs.Nodup) → (∀x : Fin 26 → Bool,C.eval (List.ofFn x)=true ↔
    ∃ i j : Fin 13,(i=j ∨ i=j+1 ∨ i=j+3 ∨ i=j+9) ∧ x (Fin.castAdd 13 i)=true ∧ x (Fin.natAdd 13 j)=true) →
  ∃ K : ℕ → Bool,trace K ∧ ∀i,K (26+i.val)=true → ¬(bad 0 i ∧ bad 13 i))
  (opposed : ∀ C : Circuit,
  let v (p w : ℕ) := (C.wires (List.ofFn fun i : Fin 26=>decide (i.val=p))).getD w false
  let G := gateAt C
  let trace (K : ℕ → Bool) := K C.output=true ∧ (∀ w<26,K w=true → w=0 ∨ w=13) ∧ (∀ i : Fin C.size,K (26+i.val)=true → (G i.val).op.eval ((G i.val).inputs.map K)=true)
  let bad (p : ℕ) (i : Fin C.size) := (G i.val).op=GateOp.and ∧
    ((G i.val).inputs.map (v p)).any id=false
  (63 ≤ C.size ∧ C.size ≤ 64) → IsAO2 26 C → (∀i : Fin C.size,(G i.val).inputs.Nodup) → (∀x : Fin 26 → Bool,C.eval (List.ofFn x)=true ↔
    ∃ i j : Fin 13,(i=j ∨ i=j+1 ∨ i=j+3 ∨ i=j+9) ∧ x (Fin.castAdd 13 i)=true ∧ x (Fin.natAdd 13 j)=true) →
  (∃ K : ℕ → Bool,trace K ∧ ∀i,K (26+i.val)=true → ¬(bad 0 i ∧ bad 13 i)) →
  ∃ K : ℕ → Bool, trace K ∧ ((∀i,K (26+i.val)=true → ¬bad 0 i) ∨
    (∀i,K (26+i.val)=true → ¬bad 13 i))) :
  ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  rintro ⟨C,sz1,sz2,legal,compute,⟨d,dp,dt,dc⟩,⟨e,ep,et,ec⟩⟩
  have area : 63 ≤ C.size ∧ C.size ≤ 64 := ⟨sz1,sz2⟩
  have each {g : Gate} (h : g∈C.gates) : (g.op=.and ∨ g.op=.or) ∧ ∃a b : ℕ,g.inputs=[a,b] ∧ a≠b ∧ ∃ j : ℕ,a<26+j ∧ b<26+j := by
    obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem h
    obtain ⟨o,a,b,inp,ne,ha,hb⟩:=legal i _ (List.getElem?_eq_getElem hi)
    exact ⟨o,a,b,inp,ne,i,ha,hb⟩
  have ao : IsAO2 26 C := by
    refine ⟨fun g h=>(each h).1,?_,?_⟩
    · intro i hi w hw
      let g:=C.gates[i]
      have gh : gateAt C i=g := List.getD_eq_getElem _ _ hi
      obtain ⟨_,a,b,ins,_,ha,hb⟩:=legal i g (List.getElem?_eq_getElem hi)
      rw [gh,ins] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> assumption
    · intro g hg;obtain ⟨_,a,b,h,_,_,_⟩:=each hg;simp [h]
  have distinct : ∀i : Fin C.size,(gateAt C i.val).inputs.Nodup := by
    intro i
    have hi : i.val<C.gates.length:=i.isLt
    let g:=C.gates[i.val]
    have h : gateAt C i.val=g := List.getD_eq_getElem _ _ hi
    have hg : C.gates[i.val]?=some g := List.getElem?_eq_getElem hi
    obtain ⟨_,a,b,ins,ne,_,_⟩:=legal i.val g hg
    have good : g.inputs.Nodup := by rw [ins];simp [ne]
    exact (congrArg (fun z : Gate=>z.inputs.Nodup) h).mpr good
  let v (p w : ℕ) := (C.wires (List.ofFn fun i : Fin 26=>decide (i.val=p))).getD w false
  have single (p : ℕ) (h : p=0 ∨ p=13) : v p C.output=false := by
    apply Bool.eq_false_iff.mpr;intro pos
    obtain ⟨i,j,_,l,r⟩:=(compute _).mp pos
    simp only [decide_eq_true_eq,Fin.val_castAdd,Fin.val_natAdd] at l r
    have hi:=i.isLt
    omega
  have yes : C.eval (List.ofFn fun i : Fin 26=>decide (i.val=0 ∨ i.val=13))=true :=
    (compute _).mpr ⟨0,0,Or.inl rfl,by decide,by decide⟩
  have length (gs : List Gate) (x : List Bool) :
      (gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map (fun u=>w.getD u false))]) x).length=x.length+gs.length := by
    induction gs generalizing x with
    | nil=>simp
    | cons g gs ih=>simp only [List.foldl_cons,ih,List.length_append,List.length_cons,List.length_nil];omega
  have valid : C.output<26+C.size := by
    by_contra! no
    let X:=List.ofFn fun i : Fin 26=>decide (i.val=0 ∨ i.val=13)
    have len : (C.wires X).length=26+C.size := by
      change (C.gates.foldl _ X).length=26+C.size
      rw [length]
      change (List.ofFn _).length+C.gates.length=26+C.gates.length
      rw [List.length_ofFn]
    have off : (C.wires X).getD C.output false=false := List.getD_eq_default _ _ (by omega)
    exact Bool.noConfusion (off.symm.trans yes)
  obtain ⟨K,⟨ko,ki,flow⟩,n⟩:=opposed C area ao distinct compute (mixed C area ao distinct compute)
  rcases n with n|n
  · obtain ⟨i,mem,op,dead⟩:=collision C 0 13 d K legal valid dp dt ko ki flow (single 0 (Or.inl rfl)) dc
    exact n i mem ⟨op,dead⟩
  · have rev : ∀w<26,K w=true → w=13 ∨ w=0 := fun w hw h=>(ki w hw h).symm
    obtain ⟨i,mem,op,dead⟩:=collision C 13 0 e K legal valid ep et ko rev flow (single 13 (Or.inr rfl)) ec
    exact n i mem ⟨op,dead⟩
