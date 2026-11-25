import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- Fix a vertex input to false. Whenever an edge survives, this saves a gate.
-- To restore the deleted edges, take the OR of the neighbors in each copy
-- and conjoin it with the vertex in the other copy. Restoring a vertex of
-- degree t costs at most 2t + 2 gates. Charge this to the saved gate and
-- repeat until every positive degree reaches the chosen threshold.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2001_371
    (remove : ∀ (n : ℕ) (C : Circuit) (v : Fin n), Monotone2 C →
      (∃ x : Fin n → Bool, circuitFun n C x ≠ circuitFun n C (Function.update x v false)) →
      (∃ x y : Fin n → Bool, circuitFun n C (Function.update x v false) ≠ circuitFun n C (Function.update y v false)) →
      ∃ B : Circuit, Monotone2 B ∧ B.size < C.size ∧ ∀ x : Fin n → Bool, circuitFun n B x = circuitFun n C (Function.update x v false))
    (high : ∃ k d : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ d+4 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ p q, G.Adj p q ∧ x p = true ∧ x q = true)) →
      ∃ D : Circuit, Monotone2 D ∧ D.size+1 ≤ k*(C.size+1) ∧ ∀ x y : Fin n → Bool,
        D.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p q, G.Adj p q ∧ x p = true ∧ y q = true)) :
∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) := by
  let out {n : ℕ} (C : Circuit) (x y : Fin n → Bool) := C.eval (List.ofFn x ++ List.ofFn y)

  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have lengthRun (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega

  have prior (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step w g) (by simp [step]; omega)]
      simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left h]

  let gate (op : GateOp) (a b : ℕ) : Gate := ⟨op,[a,b]⟩

  let endWire (n : ℕ) (P : List Gate) := n+n+P.length

  let value {n : ℕ} (P : List Gate) (x y : Fin n → Bool) (i : ℕ) :=
    (P.foldl step (List.ofFn x ++ List.ofFn y)).getD i false

  let pin {n : ℕ} (right : Bool) (v : Fin n) := if right then n+v.val else v.val

  let side {n : ℕ} (right : Bool) (x y : Fin n → Bool) := if right then y else x

  have onPin {n : ℕ} (P : List Gate) (x y : Fin n → Bool) (right : Bool) (v : Fin n) :
      value P x y (pin right v) = side right x y v := by
    have hi : pin right v < (List.ofFn x ++ List.ofFn y).length := by
      cases right <;> simp [pin]; omega
    unfold value
    rw [prior _ _ _ hi]
    cases right <;> simp [pin,side,List.getD_eq_getElem?_getD,List.getElem?_append_left (show v.val<(List.ofFn x).length by simp)]

  have keepVal {n : ℕ} (P M : List Gate) (x y : Fin n → Bool) (i : ℕ) (low : i < endWire n P) :
      value (P++M) x y i = value P x y i := by
    unfold value
    rw [List.foldl_append,prior _ _ _ (by simpa [lengthRun,endWire] using low)]

  have fresh {n : ℕ} (P : List Gate) (x y : Fin n → Bool) (op : GateOp) (a b : ℕ) :
      value (P++[gate op a b]) x y (endWire n P) = op.eval [value P x y a,value P x y b] := by
    let w := P.foldl step (List.ofFn x++List.ofFn y)
    have len : w.length=endWire n P := by simp [w,lengthRun,endWire]
    unfold value
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (w++[op.eval [w.getD a false,w.getD b false]]).getD (endWire n P) false = _
    rw [← len]; simp [List.getD_eq_getElem?_getD,w]

  have andBit (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
  have orBit (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl

  have sumPins {n : ℕ} (P : List Gate) (b : Fin n) (bs : List (Fin n)) (right : Bool) :
      ∃ (M : List Gate) (i : ℕ), M.length=bs.length ∧ (∀ g ∈ M, g.op=GateOp.or ∧ g.inputs.length=2) ∧
        i < endWire n (P++M) ∧ ∀ x y : Fin n → Bool, value (P++M) x y i = true ↔ ∃ c ∈ b::bs, side right x y c = true := by
    induction bs generalizing b with
    | nil =>
      refine ⟨[],pin right b,rfl,by simp,?_,?_⟩
      · cases right <;> simp [endWire,pin] <;> omega
      · intro x y; simp [onPin]
    | cons c cs ih =>
      obtain ⟨M,i,len,allOr,_,old⟩ := ih c
      let Q := P++M
      let g := gate .or (pin right b) i
      refine ⟨M++[g],endWire n Q,by simp [len],?_,by simp [endWire,Q],?_⟩
      · intro t ht
        rcases List.mem_append.mp ht with before|last
        · exact allOr t before
        · obtain rfl := List.mem_singleton.mp last
          exact ⟨rfl,rfl⟩
      · intro x y
        have layout : P++(M++[g]) = Q++[g] := by simp [Q]
        rw [layout,show g=gate .or (pin right b) i by rfl,fresh,orBit,Bool.or_eq_true,onPin]
        rw [old]
        simp

  have oneDirection {n : ℕ} (C : Circuit) (a b : Fin n) (bs : List (Fin n)) (right : Bool) (valid : Monotone2 C) :
      ∃ D : Circuit, Monotone2 D ∧ D.size=C.size+bs.length+2 ∧ ∀ x y : Fin n → Bool,
        out D x y = true ↔ out C x y = true ∨ side (!right) x y a = true ∧ ∃ w ∈ b::bs, side right x y w = true := by
    obtain ⟨M,i,len,legal,_,sum⟩ := sumPins C.gates b bs right
    let P := C.gates++M
    let j := endWire n P
    let h := gate .and (pin (!right) a) i
    let Q := P++[h]
    let saved := if C.output < endWire n C.gates then C.output else j
    let k := gate .or saved j
    let D : Circuit := ⟨Q++[k],endWire n Q⟩
    have size : D.size=C.size+bs.length+2 := by
      change (((C.gates++M)++[h])++[k]).length = C.gates.length+bs.length+2
      simp [len]; omega
    refine ⟨D,?_,size,?_⟩
    · intro t ht
      change t ∈ ((C.gates++M)++[h])++[k] at ht
      simp only [List.mem_append,List.mem_singleton] at ht
      rcases ht with ((old|inside)|rfl)|rfl
      · exact valid t old
      · obtain ⟨op,arity⟩ := legal t inside
        exact ⟨Or.inr op,arity.le⟩
      · exact ⟨Or.inl rfl,le_rfl⟩
      · exact ⟨Or.inr rfl,le_rfl⟩
    · intro x y
      have hit : value Q x y j = true ↔ side (!right) x y a = true ∧ ∃ w ∈ b::bs, side right x y w = true := by
        change value (P++[gate .and _ i]) x y (endWire n P) = true ↔ _
        rw [fresh,andBit,Bool.and_eq_true,onPin,sum]
      change value (Q++[gate .or saved j]) x y (endWire n Q) = true ↔ _
      rw [fresh,orBit,Bool.or_eq_true]
      by_cases usable : C.output < endWire n C.gates
      · have extra : Q = C.gates++(M++[h]) := by simp [Q,P]
        have earlier : value Q x y saved = out C x y := by
          rw [extra,show saved=C.output by simp [saved,usable],keepVal _ _ _ _ _ usable]
          rfl
        rw [earlier,hit]
      · have off : out C x y = false := by
          change (C.gates.foldl step (List.ofFn x++List.ofFn y)).getD C.output false = false
          apply List.getD_eq_default
          simpa [lengthRun,endWire] using Nat.le_of_not_gt usable
        simp [saved,usable,or_self,off,hit]

  have extend {n : ℕ} (C : Circuit) (a : Fin n) (N : List (Fin n)) (old : Monotone2 C) :
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size+2*N.length+2 ∧ ∀ x y : Fin n → Bool,
        out D x y = true ↔ out C x y = true ∨
          ∃ b ∈ N, (x a = true ∧ y b = true) ∨ (x b = true ∧ y a = true) := by
    cases N with
    | nil => exact ⟨C,old,by simp,by simp⟩
    | cons b bs =>
      obtain ⟨B,hB,sizeB,forward⟩ := oneDirection C a b bs true old
      obtain ⟨D,hD,sizeD,reverse⟩ := oneDirection B a b bs false hB
      refine ⟨D,hD,by rw [sizeD,sizeB,List.length_cons]; omega,?_⟩
      intro x y
      rw [reverse,forward]
      simp only [side,Bool.not_true,Bool.not_false,ite_true,ite_false,Bool.false_eq_true]
      constructor
      · rintro ((ready|⟨atA,w,mem,on⟩)|⟨atA,w,mem,on⟩)
        · exact Or.inl ready
        · exact Or.inr ⟨w,mem,Or.inl ⟨atA,on⟩⟩
        · exact Or.inr ⟨w,mem,Or.inr ⟨on,atA⟩⟩
      · rintro (ready|⟨w,mem,hit⟩)
        · exact Or.inl (Or.inl ready)
        · rcases hit with ⟨atA,on⟩|⟨on,atA⟩
          · exact Or.inl (Or.inr ⟨atA,w,mem,on⟩)
          · exact Or.inr ⟨atA,w,mem,on⟩
  let edgeVal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x y : Fin n → Bool) :=
    decide (∃ p q, G.Adj p q ∧ x p = true ∧ y q = true)

  have zeroVal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
      edgeVal G (fun _ => false) (fun _ => false) = false := by simp [edgeVal]

  have pairVal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n) (hit : G.Adj a b) :
      edgeVal G (pairInput a b) (pairInput a b) = true :=
    decide_eq_true ⟨a,b,hit,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩

  have masked {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (x : Fin n → Bool) :
      edgeVal G (Function.update x v false) (Function.update x v false) = edgeVal (G.deleteIncidenceSet v) x x := by
    apply Bool.eq_iff_iff.mpr
    simp only [edgeVal,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · rintro ⟨a,b,edge,h,k⟩
      have ha : a ≠ v := by intro e; subst a; simp at h
      have hb : b ≠ v := by intro e; subst b; simp at k
      exact ⟨a,b,⟨edge,ha,hb⟩,by simpa [Function.update_of_ne ha] using h,by simpa [Function.update_of_ne hb] using k⟩
    · rintro ⟨a,b,⟨edge,ha,hb⟩,onA,onB⟩
      exact ⟨a,b,edge,by simpa [Function.update_of_ne ha] using onA,by simpa [Function.update_of_ne hb] using onB⟩

  have changes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (positive : 0 < G.degree v) :
      ∃ x : Fin n → Bool, edgeVal G x x ≠ edgeVal G (Function.update x v false) (Function.update x v false) := by
    obtain ⟨w,edge⟩ := (G.degree_pos_iff_exists_adj v).mp positive
    refine ⟨pairInput v w,?_⟩
    rw [pairVal G v w edge,masked]
    intro eq
    obtain ⟨a,b,ab,ha,hb⟩ := of_decide_eq_true eq.symm
    obtain ⟨ab,av,bv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp ab
    have aw : a=w := (of_decide_eq_true ha : a=v ∨ a=w).resolve_left av
    have bw : b=w := (of_decide_eq_true hb : b=v ∨ b=w).resolve_left bv
    exact ab.ne (aw.trans bw.symm)

  have restore {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
      (D : Circuit) (valid : Monotone2 D) (correct : ∀ x y : Fin n → Bool, out D x y = edgeVal (G.deleteIncidenceSet v) x y) :
      ∃ U : Circuit, Monotone2 U ∧ U.size ≤ D.size + 2*G.degree v+2 ∧ ∀ x y : Fin n → Bool, out U x y = edgeVal G x y := by
    obtain ⟨U,ok,sz,truth⟩ := extend D v (G.neighborFinset v).toList valid
    refine ⟨U,ok,by simpa [SimpleGraph.card_neighborFinset_eq_degree] using sz,?_⟩
    intro x y
    apply Bool.eq_iff_iff.mpr
    rw [truth,correct]
    simp only [edgeVal,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj,Finset.mem_toList,SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (⟨a,b,⟨ab,_,_⟩,ha,hb⟩|⟨w,vw,hit⟩)
      · exact ⟨a,b,ab,ha,hb⟩
      · rcases hit with ⟨hv,hw⟩|⟨hw,hv⟩
        · exact ⟨v,w,vw,hv,hw⟩
        · exact ⟨w,v,vw.symm,hw,hv⟩
    · rintro ⟨a,b,ab,ha,hb⟩
      by_cases av : a = v
      · subst a; exact Or.inr ⟨b,ab,Or.inl ⟨ha,hb⟩⟩
      · by_cases bv : b = v
        · subst b; exact Or.inr ⟨a,ab.symm,Or.inr ⟨ha,hb⟩⟩
        · exact Or.inl ⟨a,b,⟨ab,av,bv⟩,ha,hb⟩
  classical
  obtain ⟨k,d,core⟩ := high
  let K := max k (2*(d+3)+3)
  have solve (s : ℕ) : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, C.size=s → Monotone2 C → (∀ x : Fin n → Bool, circuitFun n C x = edgeVal G x x) →
      ∃ D : Circuit, Monotone2 D ∧ D.size+1 ≤ K*(C.size+1) ∧ ∀ x y : Fin n → Bool, out D x y = edgeVal G x y := by
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro n G inst girth C size mono funC
      by_cases highDegrees : ∀ v, G.degree v=0 ∨ d+4 ≤ G.degree v
      · obtain ⟨D,ok,cost,truth⟩ := core n G highDegrees girth C mono funC
        exact ⟨D,ok,cost.trans (Nat.mul_le_mul_right _ (show k ≤ K from le_max_left _ _)),truth⟩
      · push Not at highDegrees
        obtain ⟨v,active,bound⟩ := highDegrees
        let H := G.deleteIncidenceSet v
        have gH (w : Fin n) (p : H.Walk w w) (cy : p.IsCycle) : 5 ≤ p.length := by
          have incl : H ≤ G := G.deleteIncidenceSet_le v
          simpa using girth w (p.mapLe incl) (cy.mapLe incl)
        have low : 2*G.degree v+3 ≤ K := by
          have budget : 2*(d+3)+3 ≤ K := le_max_right _ _
          omega
        by_cases hasEdge : ∃ a b, H.Adj a b
        · obtain ⟨a,b,ab⟩ := hasEdge
          have mask (x : Fin n → Bool) : circuitFun n C (Function.update x v false) = edgeVal H x x :=
            (funC _).trans (masked G v x)
          have difference : ∃ x : Fin n → Bool, circuitFun n C x ≠ circuitFun n C (Function.update x v false) := by
            obtain ⟨x,hx⟩ := changes G v (by omega)
            exact ⟨x,by simpa only [funC] using hx⟩
          have nonconstant : ∃ x y : Fin n → Bool,
              circuitFun n C (Function.update x v false) ≠ circuitFun n C (Function.update y v false) := by
            exact ⟨fun _ => false,pairInput a b,by rw [mask,mask,zeroVal,pairVal H a b ab]; decide⟩
          obtain ⟨B,okB,smaller,fB⟩ := remove n C v mono difference nonconstant
          obtain ⟨D,okD,cost,works⟩ := ih B.size (smaller.trans_le size.le) n H gH B rfl okB (fun x => (fB x).trans (mask x))
          obtain ⟨U,okU,added,done⟩ := restore G v D okD works
          refine ⟨U,okU,?_,done⟩
          have charge := Nat.mul_le_mul_left K (show B.size+1 ≤ C.size by omega)
          rw [Nat.mul_add,Nat.mul_one]
          omega
        · let E : Circuit := ⟨[],n+n⟩
          have valid : Monotone2 E := fun g member => (List.not_mem_nil member).elim
          have blank (x y : Fin n → Bool) : out E x y = edgeVal H x y := by
            have left : out E x y = false := by
              change (List.ofFn x ++ List.ofFn y).getD (n+n) false = false
              apply List.getD_eq_default; simp
            rw [left]
            symm
            apply decide_eq_false
            rintro ⟨a,b,ab,_,_⟩
            exact hasEdge ⟨a,b,ab⟩
          obtain ⟨U,okU,added,works⟩ := restore G v E valid blank
          have es : E.size=0 := rfl
          refine ⟨U,okU,?_,works⟩
          have ge := Nat.mul_le_mul_left K (show 1 ≤ C.size+1 by omega)
          rw [Nat.mul_one] at ge
          omega
  exact ⟨K,fun n G _ _ girth C mono obs => solve C.size n G girth C rfl mono obs⟩
