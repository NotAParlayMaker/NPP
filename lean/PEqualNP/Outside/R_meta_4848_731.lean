import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CircuitMoves PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_4848_731
  (essential : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ → let hit := fun (k : ℕ) (a b : Fin n) => gateVal n C k (pairInput a b)=true
    ∀ j<C.gates.length,(gateAt C j).op=.and → ∃ u v,G.Adj u v ∧ hit j u v ∧ circuitFun n (eraseGate n C j (n+C.gates.length)) (pairInput u v)=false)
  (context : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ → let hit := fun (k : ℕ) (a b : Fin n) => gateVal n C k (pairInput a b)=true
    ∀ j<C.gates.length,(gateAt C j).op=.and → ∀ p∈(gateAt C j).inputs, ∃ S : Finset (Fin n), (∀ a∈S,∀ b∈S,¬G.Adj a b) ∧ gateVal n C j (fun i=>decide (i∈S))=false ∧ wireVal n C p (fun i=>decide (i∈S))=true ∧ ∀ u v, ¬G.Adj u v → hit j u v → ∃ t∈S,G.Adj t u ∨ G.Adj t v)
  (barrier : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ → let hit := fun (k : ℕ) (a b : Fin n) => gateVal n C k (pairInput a b)=true
    ∀ j<C.gates.length,(gateAt C j).op=.and → (∃ u v,¬G.Adj u v ∧ hit j u v) → (∀ k,j<k → k<C.gates.length → (gateAt C k).op=.and → ∀ u v,hit k u v → G.Adj u v) → ∃ s d q : ℕ, j≤s ∧ s<d ∧ d<C.gates.length ∧ (gateAt C d).op=.and ∧ ((gateAt C d).inputs=[n+s,q] ∨ (gateAt C d).inputs=[q,n+s]) ∧ (∀ x,gateVal n C j x=true → gateVal n C s x=true) ∧ (∃ u v,G.Adj u v ∧ hit d u v) ∧ ∀ u v,¬G.Adj u v → hit j u v → wireVal n C q (pairInput u v)=false)
  (exclude : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → PEqualNP.TopForm.NoFourCycle G → IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ → let hit := fun (k : ℕ) (a b : Fin n) => gateVal n C k (pairInput a b)=true
    ∀ j<C.gates.length,(gateAt C j).op=.and → (∃ u v,G.Adj u v ∧ hit j u v ∧ circuitFun n (eraseGate n C j (n+C.gates.length)) (pairInput u v)=false) → (∀ p∈(gateAt C j).inputs, ∃ S : Finset (Fin n), (∀ a∈S,∀ b∈S,¬G.Adj a b) ∧ gateVal n C j (fun i=>decide (i∈S))=false ∧ wireVal n C p (fun i=>decide (i∈S))=true ∧ ∀ u v, ¬G.Adj u v → hit j u v → ∃ t∈S,G.Adj t u ∨ G.Adj t v) → (∃ d q : ℕ, j<d ∧ d<C.gates.length ∧ (gateAt C d).op=.and ∧ q∈(gateAt C d).inputs ∧ (∃ u v,G.Adj u v ∧ hit d u v) ∧ (∀ u v,hit d u v → G.Adj u v) ∧ ∀ u v,¬G.Adj u v → hit j u v → wireVal n C q (pairInput u v)=false) → ∀ u v,hit j u v → G.Adj u v) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x9 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x6 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true → x2.Adj x12 x13 := by
  classical
  intro n G inst tri square C hm sem j hj op u v yes
  by_contra no
  let B := (Finset.range C.gates.length).filter fun k => (gateAt C k).op=.and ∧ ∃ a b,¬G.Adj a b ∧ gateVal n C k (pairInput a b)=true
  have bj : j∈B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,op,_,_,no,yes⟩
  let r := B.max' ⟨j,bj⟩
  have br : r∈B := B.max'_mem _
  obtain ⟨mem,ar,a,b,nab,on⟩ := Finset.mem_filter.mp br
  have hr := Finset.mem_range.mp mem
  have last : ∀ k,r<k → k<C.gates.length → (gateAt C k).op=.and → ∀ x y,gateVal n C k (pairInput x y)=true → G.Adj x y := by
    intro k rk hk ak x y xy
    by_contra nxy
    have bk : k∈B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,ak,x,y,nxy,xy⟩
    exact (Nat.not_lt_of_ge (B.le_max' k bk)) rk
  obtain ⟨s,d,q,rs,sd,hd,ad,pins,_,pos,mask⟩ := barrier n G C hm sem r hr ar ⟨a,b,nab,on⟩ last
  have rd := lt_of_le_of_lt rs sd
  have pin : q∈(gateAt C d).inputs := by rcases pins with eq|eq <;> simp [eq]
  exact nab (exclude n G C tri square hm sem r hr ar (essential n G C hm sem r hr ar) (context n G C hm sem r hr ar) ⟨d,q,rd,hd,ad,pin,pos,last d rd hd ad,mask⟩ a b on)
