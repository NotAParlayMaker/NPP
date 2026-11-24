import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_4117_3
    (three : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (B : Finset (Fin C.gates.length)),
    let f := circuitFun n C
    let pin (x : Fin n → Bool) := Function.update x v false
    IsMinimalCircuit n C → f (fun _ => false) = false → (∃ x, f (pin x) = true) →
    3 ≤ B.card → (∀ j ∈ B, ∀ x, (C.wires (List.ofFn (pin x))).getD (n+j.val) false = false) →
    ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (pin x)) s)
    (two : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (a b : Fin C.gates.length),
    let f := circuitFun n C
    let pin (x : Fin n → Bool) := Function.update x v false
    let meet (i : Fin C.gates.length) := (C.gates.get i).op = GateOp.and ∧ v.val ∈ (C.gates.get i).inputs
    IsMinimalCircuit n C → f (fun _ => false) = false → (∃ x, f (pin x) = true) →
    a ≠ b → meet a → meet b → ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (pin x)) s)
    (remaining : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    let rd (w : Nat) (g : Gate) := (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains w
    let r (v : Fin n) := C.gates.filter (rd v.val)
    let g := gateAt C
    let f := graphFun G A
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) → 7 ≤ G.egirth → (∀ v w, G.Adj v w → v ∉ A) →
    (∃ v w, G.Adj v w) → IsMinimalCircuit n C → circuitFun n C = f →
    (∀ v ∉ A, (r v).length ≤ 3 ∧ ((r v).length = 3 → ∀ g ∈ r v, g.op = GateOp.or) ∧
      (r v).countP (fun g => !g.op.eval [false,true]) ≤ 1) →
    (∃ v ∉ A, (r v).length ≤ 1 ∧ ∀ g ∈ r v, ∀ p : Fin n, p ≠ v →
      g.inputs.Perm [v.val,p.val] → g.op = GateOp.not) →
    (∀ v ∉ A, ∀ j < C.size, rd v.val (g j) = true → (g j).op ≠ GateOp.or →
      ((Finset.range C.size).filter (fun k => k ≠ j ∧ (rd v.val (g k) = true ∨
          j < k ∧ rd (n+j) (g k) = true))).card ≤ 2) →
    (∀ v ∉ A, ∀ B : Finset (Fin C.gates.length), (∀ j ∈ B, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn (Function.update x v false))).getD (n+j.val) false = false) → B.card ≤ 2) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x16 ∉ x4, (x9 x16).length ≤ (3 : ℕ) ∧ ((x9 x16).length = (3 : ℕ) → ∀ x19 ∈ x9 x16, x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x17 ∉ x4, (x9 x17).length ≤ (1 : ℕ) ∧ ∀ x18 ∈ x9 x17, ∀ (x20 : Fin x1), x20 ≠ x17 → x18.inputs.Perm [↑x17, ↑x20] → x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ x18 ∉ x4, ∃ x19 < x5.gates.length, x7 (↑x18) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x18 x19).card) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20 := by
 classical
 intro n G _ A C f read near readers deg girth unmarked edge minimum eq profile sole far
 have zero : circuitFun n C (fun _=>false)=false:=by
   rw [eq]
   change (decide (∃a∈A, false=true) || decide (∃u w,G.Adj u w ∧ false=true ∧ false=true))=false
   simp
 have positive (v : Fin n) (vm : v∉A) : ∃x,circuitFun n C (Function.update x v false)=true:=by
   have pick (y : Fin n) (ym : y∉A) (z : Fin n) : ∃w,G.Adj y w ∧ w≠z:=by
     have size : (G.neighborFinset y).card=3:=by change G.degree y=3;rw [←G.ncard_neighborSet];exact deg y ym
     have pos : 0<((G.neighborFinset y).erase z).card:=by rw [Finset.card_erase_eq_ite,size];split <;> decide
     obtain ⟨w,hw⟩:=Finset.card_pos.mp pos
     obtain ⟨wz,m⟩:=Finset.mem_erase.mp hw
     exact ⟨w,(G.mem_neighborFinset y w).mp m,wz⟩
   obtain ⟨p,vp,pv⟩:=pick v vm v
   obtain ⟨q,pq,qv⟩:=pick p (unmarked _ _ vp.symm) v
   refine ⟨fun _=>true,?_⟩
   rw [eq]
   let x : Fin n→Bool:=Function.update (fun _=>true) v false
   change (decide (∃i∈A,x i=true) || decide (∃i j,G.Adj i j ∧ x i=true ∧ x j=true))=true
   simp only [Bool.or_eq_true,decide_eq_true_eq]
   right
   exact ⟨p,q,pq,by simp [x,pv],by simp [x,qv]⟩
 by_contra fails
 apply fails
 apply remaining n G A C deg girth unmarked edge minimum eq
 · intro v vm
   obtain ⟨size,all⟩:=profile v vm
   refine ⟨size,all,?_⟩
   have bound (gs : List Gate) (p : Gate → Bool)
       (unique : ∀ i j : Fin gs.length,p (gs.get i)=true → p (gs.get j)=true → i=j) :
       gs.countP p≤1 := by
     induction gs with
     | nil=>simp
     | cons g gs ih=>
       by_cases ok:p g=true
       · have none : gs.countP p=0:=by
           apply List.countP_eq_zero.mpr
           intro h hm
           obtain ⟨i,rfl⟩:=List.get_of_mem hm
           intro on
           have e:=unique ⟨0,by simp⟩ i.succ ok on
           have := congrArg Fin.val e
           simp at this
         simp [List.countP_cons,ok,none]
       · have u (i j : Fin gs.length) (hi : p (gs.get i)=true) (hj : p (gs.get j)=true) : i=j:=
           Fin.succ_inj.mp (unique i.succ j.succ hi hj)
         simpa [List.countP_cons,ok] using ih u
   rw [List.countP_filter]
   apply bound
   intro a b ha hb
   by_contra ne
   have split (i : Fin C.gates.length)
       (h : ((!(C.gates.get i).op.eval [false,true]) && read v.val (C.gates.get i))=true) :
       (C.gates.get i).op=GateOp.and ∧ v.val∈(C.gates.get i).inputs:=by
     obtain ⟨op,m⟩:=Bool.and_eq_true_iff.mp h
     have andOp : (C.gates.get i).op=.and:=by
       rcases (minimum.1 _ (List.get_mem C.gates i)).1 with h|h|h
       · exact h
       · rw [h] at op;contradiction
       · rw [h] at op;contradiction
     refine ⟨andOp,?_⟩
     exact List.mem_of_mem_take (List.contains_iff_mem.mp m)
   obtain ⟨s,cap,has⟩:=two n C v a b minimum zero (positive v vm) ne (split a ha) (split b hb)
   exact fails ⟨v,vm,s,cap,eq ▸ has⟩
 · obtain ⟨v,vm,size,noRaw⟩:=sole
   refine ⟨v,vm,size,?_⟩
   intro g m p pv sides
   have hs:=noRaw g m p pv sides
   have ok:=(minimum.1 g (List.mem_of_mem_filter m)).1
   exact ok.resolve_left hs.1 |>.resolve_left hs.2
 · intro v vm j small readj kind
   by_contra! big
   exact far ⟨v,vm,j,small,readj,kind,big⟩
 · intro v vm B z
   by_contra! big
   obtain ⟨s,cap,has⟩:=three n C v B minimum zero (positive v vm) big z
   exact fails ⟨v,vm,s,cap,eq ▸ has⟩
