import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

theorem PEqualNP.Outside.R_meta_2640_881
    (collisions : ∀ (n : ℕ) (row : (Fin n → Bool) → (Fin n → Bool)) (C : Circuit),
      let w := fun (j : ℕ) (x : Fin n → Bool) => (C.wires (List.ofFn (row x))).getD j false
      let b : ℕ := by
        classical
        exact (((Finset.range C.size).image (fun i => w (n+i))) \ ((Finset.range n).image w)).card
      ∃ D : ℕ → Circuit, D 0 = C ∧
        ∀ j < C.size-b, ∃ m p, m < (D j).size ∧ p < n+m ∧ D (j+1)=eraseGate n (D j) m p ∧
          ∀ x : Fin n → Bool, let ws := (D j).wires (List.ofFn (row x))
                              ws.getD (n+m) false = ws.getD p false)
    (peel : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit),
    (∀ u v,G.Adj u v → u∉A) → (∃ u v,G.Adj u v) → FanInTwo C →
    (∀ x : Fin n→Bool, circuitFun n C x=true ↔ (∃ a∈A,x a=true) ∨ ∃ u v,G.Adj u v ∧ x u=true ∧ x v=true) →
    ∃ P : Circuit, IsMinimalCircuit n P ∧ P.size+A.card≤C.size ∧
      ∀ x : Fin n→Bool, circuitFun n P x=true ↔ ∃ u v,G.Adj u v ∧ x u=true ∧ x v=true)
    (restore : ∀ (n k : ℕ) (A : Finset (Fin n)) (row : (Fin n→Bool)→(Fin n→Bool)) (D : ℕ→Circuit),
    let M := fun (P Q : Circuit) => ∃ m p, m<P.size ∧ p<n+m ∧ Q=eraseGate n P m p ∧
      ((∀ x : Fin n→Bool, let ws := P.wires (List.ofFn (row x)); ws.getD (n+m) false=ws.getD p false) ∨
        P.output≠n+m ∧ ∀ g∈P.gates.drop (m+1), n+m∉g.inputs)
    FanInTwo (D 0) → (∀ j<k,M (D j) (D (j+1))) →
    ∃ T : ℕ→Circuit, FanInTwo (T 0) ∧ (T 0).size=(D 0).size+A.card ∧
      (∀ x : Fin n→Bool,circuitFun n (T 0) x=true ↔ circuitFun n (D 0) x=true ∨ ∃ a∈A,x a=true) ∧
      ∀ j<k,M (T j) (T (j+1)))
    (remaining : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
    let W := fun (P : Circuit) (u v : Fin n) (j : ℕ) (x : Fin n→Bool) =>
      (P.wires (List.ofFn (Function.update (Function.update x u false) v false))).getD j false
    let M := fun (u v : Fin n) (P Q : Circuit) => ∃ m p,m<P.size ∧ p<n+m ∧ Q=eraseGate n P m p ∧
      (W P u v (n+m)=W P u v p ∨ P.output≠n+m ∧ ∀ g∈P.gates.drop (m+1),n+m∉g.inputs)
    (¬G.Colorable 2 ∧ (∀ u v,G.Adj u v → (G.neighborSet u).ncard=3) ∧
     (∀ (v : Fin n) (w : G.Walk v v),w.IsCycle → 7≤w.length) ∧ IsMinimalCircuit n C ∧
     (∀ x : Fin n→Bool,circuitFun n C x=true ↔ ∃ u v,G.Adj u v ∧ x u=true ∧ x v=true)) →
    (∀ u v,G.Adj u v →
      let b : ℕ := by
        classical
        exact (((Finset.range C.size).image (fun i => W C u v (n+i))) \ ((Finset.range n).image (W C u v))).card
      C.size<b+7) →
    ∃ u v,G.Adj u v ∧ ∃ D : ℕ→Circuit, FanInTwo (D 0) ∧ (D 0).size≤C.size ∧ circuitFun n (D 0)=circuitFun n C ∧
      ∀ j<7,M u v (D j) (D (j+1)))
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →       (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →         (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →           (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →               (∀ (x11 : Fin x1 → Bool), x4.eval (List.ofFn x11) = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →                 ∃ (x12 : Fin x1) (x13 : Fin x1),                   x2.Adj x12 x13 ∧                     ∃ (x14 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x14 (0 : ℕ)) ∧                         (x14 (0 : ℕ)).size ≤ x4.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x14 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x4 ∧                             ∀ x15 < (7 : ℕ),                               ∃ (x17 : ℕ) (x18 : ℕ),                                 x17 < (x14 x15).size ∧                                   (x18 < x1 + x17 ∨ x1 + (x14 x15).size ≤ x18) ∧                                     x14 (x15 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x14 x15) x17 x18 ∧                                       ((∀ (x19 : Fin x1 → Bool),                                           have x20 : List Bool := (x14 x15).wires (List.ofFn (Function.update (Function.update x19 x12 Bool.false) x13 Bool.false));                                           x20.getD (x1 + x17) Bool.false = x20.getD x18 Bool.false) ∨                                         (x14 x15).output ≠ x1 + x17 ∧ ∀ x19 ∈ List.drop (x17 + (1 : ℕ)) (x14 x15).gates, x1 + x17 ∉ x19.inputs) := by
  classical
  intro n G A C odd cubic girth iso edges min spec
  obtain ⟨P,least,budget,pure⟩ := peel n G A C iso edges min.1 spec
  let face := fun (u v : Fin n) (x : Fin n→Bool) => Function.update (Function.update x u false) v false
  let count := fun (row : (Fin n→Bool)→(Fin n→Bool)) =>
    let w := fun j (x : Fin n→Bool) => (P.wires (List.ofFn (row x))).getD j false
    (((Finset.range P.size).image (fun i => w (n+i))) \ ((Finset.range n).image w)).card
  let good := fun (row : (Fin n→Bool)→(Fin n→Bool)) => fun (P Q : Circuit) => ∃ m p, m<P.size ∧ p<n+m ∧ Q=eraseGate n P m p ∧
      ((∀ x : Fin n→Bool, let ws := P.wires (List.ofFn (row x)); ws.getD (n+m) false=ws.getD p false) ∨
        P.output≠n+m ∧ ∀ g∈P.gates.drop (m+1), n+m∉g.inputs)
  have core : ∃ u v,G.Adj u v ∧ ∃ D : ℕ→Circuit, FanInTwo (D 0) ∧ (D 0).size≤P.size ∧
      circuitFun n (D 0)=circuitFun n P ∧ ∀ j<7,good (face u v) (D j) (D (j+1)) := by
    by_cases easy : ∃ u v,G.Adj u v ∧ count (face u v)+7≤P.size
    · obtain ⟨u,v,e,cap⟩:=easy
      obtain ⟨D,start,all⟩:=collisions n (face u v) P
      refine ⟨u,v,e,D,start ▸ least.1,start ▸ le_rfl,start ▸ rfl,?_⟩
      intro j hj
      have enough : j<P.size-count (face u v) := by omega
      obtain ⟨m,p,fit,valid,next,eq⟩:=all j enough
      exact ⟨m,p,fit,valid,next,Or.inl eq⟩
    · obtain ⟨u,v,e,D,ok,sz,run,steps⟩:=remaining n G P ⟨odd,fun u v e=>cubic u (iso u v e),girth,least,pure⟩ (by
        intro u v e
        change P.size<count (face u v)+7
        exact Nat.lt_of_not_ge (fun z=>easy ⟨u,v,e,z⟩))
      refine ⟨u,v,e,D,ok,sz,run,?_⟩
      intro j hj
      obtain ⟨m,p,fit,early,next,eq|dead⟩:=steps j hj
      · exact ⟨m,p,fit,early,next,Or.inl (fun x=>congrFun eq x)⟩
      · exact ⟨m,p,fit,early,next,Or.inr dead⟩
  obtain ⟨u,v,e,D,fan,size,run,moves⟩:=core
  obtain ⟨T,ok,sz,truth,step⟩:=restore n 7 A (face u v) D fan moves
  refine ⟨u,v,e,T,ok,by omega,?_,?_⟩
  · funext x
    apply Bool.eq_iff_iff.mpr
    rw [truth x,run,pure x]
    exact or_comm.trans (spec x).symm
  · intro j hj
    obtain ⟨m,p,fit,valid,next,w⟩:=step j hj
    exact ⟨m,p,fit,Or.inl valid,next,w⟩
