import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CircuitMoves PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2846_882
    (essential : ∀ (p l : Nat) (I : Fin p→Fin l→Prop) [DecidableRel I] (C : Circuit),
    let n:=p+l
    let f:=fun x : Fin n→Bool=>decide (∃ a b,I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
    let g:=gateAt C
    let ok:=fun D : Circuit=>IsAO2 n D ∧ circuitFun n D=f
    (ok C ∧ ∀ D,ok D → C.size ≤ D.size) →
    (∀ k < C.size,∃ a b,I a b ∧ gateVal n C k (pairInput (Fin.castAdd l a) (Fin.natAdd p b))=true) ∧
    (0 < C.size → C.output=n+(C.size-1)) ∧
    (∀ k < C.size,(g k).op=.and → (∀ w∈(g k).inputs,w < n) → WireBelowOutput n C (n+k)) ∧
    ∀ k < C.size,(g k).op=.and → ∀ w∈(g k).inputs,¬WireBelowOutput n C w)
    (localPairs : ∀ (p l : Nat) (I : Fin p→Fin l→Prop) [DecidableRel I] (C : Circuit),
    let n:=p+l
    let f:=fun x : Fin n→Bool=>decide (∃ a b,I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
    let g:=gateAt C
    let R:=fun w=>(Finset.range C.size).filter fun k=>w∈(g k).inputs
    let O:=fun k=>(g k).op=.or
    let ok:=fun D : Circuit=>IsAO2 n D ∧ circuitFun n D=f
    (ok C ∧ ∀ D,ok D → C.size ≤ D.size) →
    (∀ a b i j,a≠b → i≠j → ¬(I a i ∧ I a j ∧ I b i ∧ I b j)) →
    (∃ T : Finset Nat,(∀ i∈T,i < C.size ∧ O i) ∧ (∀ i∈T,n+i=C.output ∨ ∃ k∈T,R (n+i)={k}) ∧
       ∀ w,WireBelowOutput n C w → (∃ j∈R w,O j) → R w⊆T) →
    ∀ k < C.size,(g k).op=.and →
    (∀ j < k,(g j).op=.and → WireBelowOutput n C (n+j)) → (∃ w∈(g k).inputs,n ≤ w) → (∃ a b,I a b ∧ gateVal n C k (pairInput (Fin.castAdd l a) (Fin.natAdd p b))=true) →
    ∀ u v : Fin n,gateVal n C k (pairInput u v)=true → f (pairInput u v)=true)
    (propagate : ∀ (p l : Nat) (I : Fin p→Fin l→Prop) [DecidableRel I] (C : Circuit),
  ∀ T : Finset Nat,
    let n:=p+l
    let f:=fun x : Fin n→Bool=>decide (∃ a b,I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
    let g:=gateAt C
    let low:=fun w=>w < n ∨ ∃ j < C.size,w=n+j ∧ (g j).op=.or ∧ j∉T
    let floor:=fun k=>∀ w∈(g k).inputs,low w
    IsAO2 n C →
    (∀ k < C.size,(∀ j < k,(g j).op=.and → WireBelowOutput n C (n+j)) →
       ((g k).op=.and ∨ k∉T) → floor k) →
    circuitFun n C=f →
    (∀ k < C.size,(g k).op=.and → (∀ j < k,(g j).op=.and → WireBelowOutput n C (n+j)) →
      ∀ u v : Fin n,gateVal n C k (pairInput u v)=true → f (pairInput u v)=true) →
    (∀ k < C.size,((g k).op=.and ∨ k∉T) → floor k) ∧
    ∀ k < C.size,(g k).op=.and →
      gateVal n C k (fun i=>decide (i.val < p))=false ∧ gateVal n C k (fun i=>decide (p ≤ i.val))=false)
    (classify : ∀ (p l : Nat) (C : Circuit) (T : Finset Nat),
    let n:=p+l
    let g:=gateAt C
    let low:=fun w=>w < n ∨ ∃ j < C.size,w=n+j ∧ (g j).op=.or ∧ j∉T
    let floor:=fun k=>∀ w∈(g k).inputs,low w
    let pure:=fun (B : Nat→Prop) (S : Finset Nat)=>∀ w∈S,B w ∨ ∃ i < C.size,
      w=n+i ∧ (g i).op=.or ∧ ∀ u∈(g i).inputs,u∈S
    IsAO2 n C → (∀ k < C.size, ((g k).op=.and ∨ k∉T) → floor k) →
    (∀ k < C.size,(g k).op=.and →
      gateVal n C k (fun i=>decide (i.val < p))=false ∧ gateVal n C k (fun i=>decide (p ≤ i.val))=false) →
    ∃ P L : Finset Nat, pure (fun w=>w < p) P ∧ pure (fun w=>p ≤ w ∧ w < n) L ∧
      ∀ k < C.size,(g k).op=.and → ∃ a b,(g k).inputs=[a,b] ∧ ((a∈P ∧ b∈L) ∨ (a∈L ∧ b∈P)))
    : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  classical
  intro p l I decI C no4 ao run minimum stuck
  let n:=p+l
  let g:=gateAt C
  let f:=fun x : Fin n→Bool=>decide (∃ a b,I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
  let R (w : Nat):=(Finset.range C.size).filter fun k=>w∈(g k).inputs
  let O:=fun k=>(g k).op=.or
  let ok:=fun D : Circuit=>IsAO2 n D ∧ circuitFun n D=f
  have optimum : ok C ∧ ∀ D,ok D → C.size ≤ D.size:=
    ⟨⟨ao,funext run⟩,fun D h=>minimum D h.1 (fun x=>congrFun h.2 x)⟩
  obtain ⟨hot,last,rawSound,noDirect⟩:=essential p l I C optimum
  obtain ⟨T,tree,allReaders⟩:=stuck
  have Rmem (w k : Nat) : k∈R w ↔ k < C.size ∧ w∈(g k).inputs:=by simp [R]
  have below (w : Nat) (h : WireBelowOutput n C w) (x : Fin n→Bool)
      (on : (C.wires (List.ofFn x)).getD w false=true) :
      ∃ a b,I a b ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true:=by
    apply of_decide_eq_true
    exact (run x) ▸ h x on
  have cls (w : Nat) (h : WireBelowOutput n C w) (hit : ∃ k∈R w,O k) : R w⊆T:=by
    obtain ⟨j,rj,jo⟩:=hit
    obtain ⟨jb,jr⟩:=(Rmem w j).mp rj
    intro k hk
    obtain ⟨kb,kr⟩:=(Rmem w k).mp hk
    exact allReaders w (below w h) ⟨j,jb,jo,jr⟩ k kb kr
  have marked (i : Nat) (it : i∈T) : i < C.size ∧ O i:=by
    exact ⟨(tree i it).1,(tree i it).2.1⟩
  have branches (i : Nat) (it : i∈T) : n+i=C.output ∨ ∃ k∈T,R (n+i)={k}:=by
    obtain ⟨_,_,out|⟨k,kt,h⟩⟩:=tree i it
    · exact Or.inl out
    · refine Or.inr ⟨k,kt,?_⟩
      ext j
      rw [Rmem,Finset.mem_singleton]
      constructor
      · exact fun hr=>(h j hr.1).mp hr.2
      · rintro rfl
        exact ⟨(tree j kt).1,(h j (tree j kt).1).mpr rfl⟩
  have safe:=localPairs p l I C optimum no4 ⟨T,fun _=>marked _,branches,cls⟩
  have gates (k : Nat) (hk : k < C.size) : (g k).op=.and ∨ (g k).op=.or:=by
    apply ao.1
    change C.gates.getD k _∈C.gates
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
    exact List.getElem_mem hk
  have topRead {j k : Nat} (jt : j∈T) (hk : k < C.size) (r : n+j∈(g k).inputs) : k∈T:=by
    rcases branches j jt with out|⟨t,tt,only⟩
    · have hi : j < C.size:=(tree j jt).1
      have back : n+j < n+k:=ao.2.1 k hk _ r
      have lastEq:=last (by omega)
      omega
    · have mem:=(Rmem _ _).mpr ⟨hk,r⟩
      rw [only,Finset.mem_singleton] at mem
      exact mem ▸ tt
  have floorAt (k : Nat) (hk : k < C.size)
      (earlier : ∀ j < k,(g j).op=.and → WireBelowOutput n C (n+j))
      (layer : (g k).op=.and ∨ k∉T) (w : Nat) (read : w∈(g k).inputs) :
      w < n ∨ ∃ j < C.size,w=n+j ∧ (g j).op=.or ∧ j∉T:=by
    by_cases raw : w < n
    · exact Or.inl raw
    obtain ⟨j,rfl⟩ : ∃ j,w=n+j:=⟨w-n,by omega⟩
    have back : n+j < n+k:=ao.2.1 k hk _ read
    have jk : j < k:=by omega
    have hj : j < C.size:=by omega
    have nt : j∉T:=by
      intro jt
      have kt:=topRead jt hk read
      rcases layer with andK|nt
      · have oo:=(marked k kt).2
        rw [oo] at andK
        contradiction
      · contradiction
    rcases gates j hj with jo|jo
    · have clean:=earlier j jk jo
      rcases gates k hk with andK|orK
      · exact (noDirect k hk andK _ read clean).elim
      · have kt:=cls (n+j) clean ⟨k,(Rmem _ _).mpr ⟨hk,read⟩,orK⟩ ((Rmem _ _).mpr ⟨hk,read⟩)
        rcases layer with andK|noT
        · rw [orK] at andK;contradiction
        · contradiction
    · exact Or.inr ⟨j,hj,rfl,jo,nt⟩
  obtain ⟨closed,off⟩:=propagate p l I C T ao floorAt (funext run)
    (fun k hk op earlier u v on=>by
      by_cases raw : ∀ w∈(g k).inputs,w < n
      · exact (run (pairInput u v)).symm.trans (rawSound k hk op raw (pairInput u v) on)
      · push Not at raw
        exact safe k hk op earlier raw (hot k hk) u v on)
  exact classify p l C T ao closed off
