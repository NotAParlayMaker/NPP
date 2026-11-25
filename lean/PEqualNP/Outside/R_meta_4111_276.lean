import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.R_meta_4111_276
  (crowded : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    let p := fun g : Gate=>g.inputs.take (bif g.op.eval [false] then 1 else 2)
    let r := fun i : Fin n=>C.gates.countP fun g=>(p g).contains i.val
    let E := Finset.univ.filter fun e : Fin n × Fin n => e.1<e.2 ∧ G.Adj e.1 e.2
    IsMinimalCircuit n C → circuitFun n C (fun _=>false)=false →
    (C.size+1<2*(∑ e∈E, (r e.1+r e.2-6)) ∨ ∃u v : Fin n,G.Adj u v ∧ 7≤C.gates.countP (fun g=>(p g).any fun j=>j==u.val || j==v.val)) →
    ∃u v : Fin n,G.Adj u v ∧ ∃t : Nat,t+7≤C.size ∧ HasCircuitSize n (fun x=>circuitFun n C (Function.update (Function.update x u false) v false)) t)
  (sparse : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    let p := fun g : Gate=>g.inputs.take (bif g.op.eval [false] then 1 else 2)
    let r := fun i : Fin n=>C.gates.countP fun g=>(p g).contains i.val
    let E := Finset.univ.filter fun e : Fin n × Fin n => e.1<e.2 ∧ G.Adj e.1 e.2
    ¬G.Colorable 2 → (∀u,(∃v,G.Adj u v) → (G.neighborSet u).ncard=3) →
    (∀u (w:G.Walk u u),w.IsCycle → 7≤w.length) → IsMinimalCircuit n C → circuitFun n C=graphFun G ∅ →
    (∀T,IsVertexCover G T → C.size+1<G.edgeSet.ncard+T.card) →
    (∀u v : Fin n,G.Adj u v → C.gates.countP (fun g=>(p g).any fun j=>j==u.val || j==v.val)≤6) →
    2*(∑ e∈E, (r e.1+r e.2-6))≤C.size+1 → ∃u v : Fin n,G.Adj u v ∧ ∃t : Nat,t+7≤C.size ∧ HasCircuitSize n (fun x=>circuitFun n C (Function.update (Function.update x u false) v false)) t) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x9 + (1 : ℕ) < x2.edgeSet.ncard + x10.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ ∃ (x14 : ℕ), x14 + (7 : ℕ) ≤ x9 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x3 (Function.update (Function.update x15 x12 Bool.false) x13 Bool.false)) x14 := by
  classical
  intro n G f nonbi deg girth _ spec s small has
  let ev := fun k=>HasCircuitSize n f k
  have ex : ∃k,ev k:=⟨s,has⟩
  obtain ⟨C,fan,cap,fit⟩:=Nat.find_spec ex
  have bound : C.size≤s:=cap.trans (Nat.find_min' ex has)
  have minimal : IsMinimalCircuit n C := by
    refine ⟨fan,?_⟩
    intro D legal same
    exact cap.trans (Nat.find_min' ex (show HasCircuitSize n f D.size from
      ⟨D,legal,le_rfl,fun x=>(congrFun same x).trans (fit x)⟩))
  have eq : circuitFun n C=f := funext fit
  have compute : circuitFun n C=graphFun G ∅ := by
    rw [eq];funext x
    apply Bool.eq_iff_iff.mpr
    change (f x=true) ↔ (decide (∃v∈(∅:Finset (Fin n)),x v=true) || decide (∃u v,G.Adj u v ∧ x u=true ∧ x v=true))=true
    simpa using spec x
  have zero : circuitFun n C (fun _=>false)=false := by
    rw [eq]
    cases h:f (fun _=>false) with
    | false=>rfl
    | true=>have hx:=(spec _).mp h;simp at hx
  let p := fun g : Gate=>g.inputs.take (bif g.op.eval [false] then 1 else 2)
  let r := fun i : Fin n=>C.gates.countP fun g=>(p g).contains i.val
  let E := Finset.univ.filter fun e : Fin n × Fin n => e.1<e.2 ∧ G.Adj e.1 e.2
  have hit := crowded n G C minimal zero
  have miss := sparse n G C nonbi deg girth minimal compute (fun T cover => (Nat.add_le_add_right bound 1).trans_lt (small T cover))
  have result : ∃u v : Fin n,G.Adj u v ∧ ∃t : Nat,t+7≤C.size ∧ HasCircuitSize n (fun x=>circuitFun n C (Function.update (Function.update x u false) v false)) t := by
    by_cases many : C.size+1<2*(∑ e∈E, (r e.1+r e.2-6))
    · exact hit (Or.inl many)
    by_cases heavy : ∃u v : Fin n,G.Adj u v ∧ 7≤C.gates.countP (fun g=>(p g).any fun j=>j==u.val || j==v.val)
    · exact hit (Or.inr heavy)
    apply miss _ (Nat.le_of_not_gt many)
    intro u v adj
    by_contra! bad
    exact heavy ⟨u,v,adj,Nat.succ_le_of_lt bad⟩
  obtain ⟨u,v,adj,t,sz,ok⟩:=result
  exact ⟨u,v,adj,t,sz.trans bound,by simpa only [eq] using ok⟩
