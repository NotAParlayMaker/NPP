import Mathlib
import PEqualNP.Defs

/-! Count the OR gates whose two operands are live on a chosen vertex set. -/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_4837_aux
/-- The columns evaluate a wire on S, T, X and the intersection of X with T. Both T and X are subsets of S. -/
abbrev P := Fin 4→Bool
def zero : P := fun _=>false
def ok (p:P) : Prop := p 1≤p 0 ∧ p 2≤p 0
def flat (p:P) : Prop := p 1=true → p 2=true → p 3=true
def ev (op:GateOp) (rs:List P) : P :=fun j=>op.eval (rs.map fun p=>p j)
def fee (op:GateOp) (rs:List P) (j:Fin 4) : Nat :=
  match op,rs with
  | .or,[a,b] => if a j && b j then 1 else 0
  | _,_=>0
def good (op:GateOp) (rs:List P) := ok (ev op rs) ∧ fee op rs 1≤fee op rs 0 ∧
  ((∀p∈rs,flat p) → fee op rs 1=fee op rs 0 → flat (ev op rs))
instance (p:P) : Decidable (ok p) :=by unfold ok;infer_instance
instance (p:P) : Decidable (flat p) :=by unfold flat;infer_instance
instance (op:GateOp) (rs:List P) : Decidable (good op rs) :=by unfold good;infer_instance

/-- Check the truth tables of each AND and OR on at most two operands. -/
lemma localGood (op:GateOp) (basis:op=.and ∨ op=.or) (rs:List P) (len:rs.length≤2)
    (hh:∀p∈rs,ok p) : good op rs :=by
  cases rs with
  | nil => rcases basis with rfl|rfl <;> decide +kernel
  | cons a rs =>
    cases rs with
    | nil =>
      have h:=hh a (by simp)
      rcases basis with rfl|rfl
      · exact (by decide +kernel : ∀p:P,ok p → good .and [p]) a h
      · exact (by decide +kernel : ∀p:P,ok p → good .or [p]) a h
    | cons b rest =>
      cases rest with
      | nil =>
        have aok:=hh a (by simp);have bok:=hh b (by simp)
        rcases basis with rfl|rfl
        · exact (by decide +kernel : ∀p q:P,ok p → ok q → good .and [p,q]) a b aok bok
        · exact (by decide +kernel : ∀p q:P,ok p → ok q → good .or [p,q]) a b aok bok
      | cons _ _ => simp at len
lemma memDefault {α : Type} (Q:α→Prop) (l:List α) (d:α) (i:Nat) (hd:Q d) (hl:∀p∈l,Q p) : Q (l.getD i d) :=by
  by_cases h:i<l.length
  · rw [List.getD_eq_getElem _ _ h];exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)];exact hd
end PEqualNP.Outside.L_meta_4837_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_4837_aux

abbrev W (n:Nat) := Finset (Fin n)→Bool
def noneW {n:Nat}:W n:=fun _=>false
def raw (n:Nat) : List (W n) :=List.ofFn (fun v S=>decide (v∈S))
abbrev Record (n:Nat) := GateOp × List (W n)
def out {n:Nat} (r:Record n) : W n:=fun S=>r.1.eval (r.2.map fun f=>f S)
def recAt {n:Nat} (ws:List (W n)) (g:Gate) : Record n :=(g.op,g.inputs.map fun i=>ws.getD i noneW)
def advance {n:Nat} (ws:List (W n)) (g:Gate) :=ws++[out (recAt ws g)]
def history {n:Nat} : List Gate→List (W n)→List (Record n)
  | [],_=>[]
  | g::gs,ws=>recAt ws g :: history gs (advance ws g)
def hist (n:Nat) (C:Circuit) :=history C.gates (raw n)
def wireOut (n:Nat) (C:Circuit) : W n :=(C.gates.foldl advance (raw n)).getD C.output noneW

lemma mapAt {α β : Type} (f:α→β) (l:List α) (i:Nat) (a:α) :
    f (l.getD i a)=(l.map f).getD i (f a) :=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map];cases l[i]? <;> rfl
lemma advanceAt {n:Nat} (ws:List (W n)) (g:Gate) (S:Finset (Fin n)) :
    (advance ws g).map (fun f=>f S)=ws.map (fun f=>f S) ++
      [g.op.eval (g.inputs.map fun i=>(ws.map (fun f=>f S)).getD i false)] :=by
  simp only [advance,recAt,out,List.map_append,List.map_cons,List.map_nil,List.map_map,
    Function.comp_def,List.append_cancel_left_eq,List.cons.injEq,and_true]
  apply congrArg;apply List.map_congr_left;intro i _;exact mapAt (fun f:W n=>f S) ws i noneW
lemma phys {n:Nat} (ws:List (W n)) (gs:List Gate) (S:Finset (Fin n)) :
    (gs.foldl advance ws).map (fun f=>f S)=(Circuit.mk gs 0).wires (ws.map (fun f=>f S)) :=by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => exact (ih (advance ws g)).trans (by rw [advanceAt];rfl)
theorem physical (n:Nat) (C:Circuit) (S:Finset (Fin n)) :
    wireOut n C S=C.eval (List.ofFn fun i=>decide (i∈S)) :=by
  unfold wireOut
  rw [mapAt (fun f:W n=>f S),phys]
  simp only [raw,List.map_ofFn,noneW,Function.comp_def]
  rfl

def costed {n:Nat} (r:Record n) (S:Finset (Fin n)) : Bool :=
  match r.1,r.2 with
  | .or,[a,b]=>a S && b S
  | _,_=>false
def Price {n:Nat} (rs:List (Record n)) (S:Finset (Fin n)) :=rs.countP (fun r=>costed r S)
def liftRow {n:Nat} (E:Fin 4→Finset (Fin n)) (f:W n) : P :=fun i=>f (E i)
lemma outRow {n:Nat} (E:Fin 4→Finset (Fin n)) (r:Record n) :
    liftRow E (out r)=ev r.1 (r.2.map (liftRow E)) :=by
  funext j;simp [liftRow,out,ev,List.map_map,Function.comp_def]
lemma feeRow {n:Nat} (E:Fin 4→Finset (Fin n)) (r:Record n) (j:Fin 4) :
    fee r.1 (r.2.map (liftRow E)) j=(if costed r (E j) then 1 else 0) :=by
  rcases r with ⟨op,rs⟩;cases op <;> cases rs with
  | nil => rfl
  | cons a tail => cases tail with
    | nil => rfl
    | cons b tail => cases tail <;> rfl

lemma spread {α:Type} (Q:α→Prop) (l:List α) (u:α) (h:∀v∈l,Q v) (hu:Q u) : ∀v∈l++[u],Q v :=by
  intro v hv;rcases List.mem_append.mp hv with hv|hv
  · exact h _ hv
  · simpa only [List.mem_singleton.mp hv] using hu

/-- If the output accepts T and X but rejects their intersection, some OR that loses a live operand must already distinguish these three inputs. -/
theorem costWitness {n:Nat} (E:Fin 4→Finset (Fin n)) (gs:List Gate) (ws:List (W n))
    (mono:∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (okws:∀f∈ws,ok (liftRow E f)) :
    (∀r∈history gs ws,costed r (E 1)=true → costed r (E 0)=true) ∧
    ((∀f∈ws,flat (liftRow E f)) →
      (∀r∈history gs ws,costed r (E 0)=true → costed r (E 1)=false → flat (liftRow E (out r))) →
      ∀f∈gs.foldl advance ws,flat (liftRow E f)) :=by
  induction gs generalizing ws with
  | nil => exact ⟨by simp [history],fun h _=>h⟩
  | cons g gs ih =>
    let r:=recAt ws g
    obtain ⟨base,len⟩:=mono g (by simp)
    have lenR:(r.2.map (liftRow E)).length≤2:=by simpa [r,recAt] using len
    have allOp (Q:P→Prop) (zeroQ:Q zero) (h:∀f∈ws,Q (liftRow E f)) : ∀p∈r.2.map (liftRow E),Q p :=by
      intro p hp;obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hp
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp hf
      exact memDefault (fun f=>Q (liftRow E f)) ws noneW i zeroQ h
    obtain ⟨bound,le,rel⟩:=localGood g.op base _ lenR (allOp ok (by decide) okws)
    change ok (ev r.1 _) at bound
    rw [←outRow] at bound
    change fee r.1 _ 1≤fee r.1 _ 0 at le
    rw [feeRow,feeRow] at le
    have leB:costed r (E 1)=true → costed r (E 0)=true:=by
      intro hi
      cases h0:costed r (E 0) with
      | true => rfl
      | false => simp [hi,h0] at le
    obtain ⟨remain,flatRest⟩:=ih (advance ws g) (fun v hv=>mono v (by simp [hv])) (spread _ ws _ okws bound)
    constructor
    · intro a ha;rcases List.mem_cons.mp ha with eq|mem
      · exact eq ▸ leB
      · exact remain _ mem
    · intro flats certified
      have head : flat (liftRow E (out r)) :=by
        by_cases differ:costed r (E 0)=true ∧ costed r (E 1)=false
        · exact certified r (by simp [r,history]) differ.1 differ.2
        · rw [outRow]
          apply rel (allOp flat (by decide) flats)
          change fee r.1 _ 1=fee r.1 _ 0
          rw [feeRow,feeRow]
          have eqb:costed r (E 1)=costed r (E 0):=by
            cases h1:costed r (E 1) <;> cases h0:costed r (E 0)
            · rfl
            · exact (differ ⟨h0,h1⟩).elim
            · exact Bool.noConfusion (h0.symm.trans (leB h1))
            · rfl
          rw [eqb]
      exact flatRest (spread _ ws _ flats head) (fun a ha=>certified a (List.mem_cons_of_mem _ ha))
end PEqualNP.Outside.L_meta_4837_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_4837_aux
def tests {n:Nat} (S T X:Finset (Fin n)) : Fin 4→Finset (Fin n) := ![S,T,X,X∩T]
lemma rawValid {n:Nat} (S T X:Finset (Fin n)) (ts:T⊆S) (xs:X⊆S) :
  ∀ f∈raw n,ok (liftRow (tests S T X) f) ∧ flat (liftRow (tests S T X) f) :=by
  intro f hf;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf
  change (decide (i∈T)≤decide (i∈S) ∧ decide (i∈X)≤decide (i∈S)) ∧
    (decide (i∈T)=true → decide (i∈X)=true → decide (i∈X∩T)=true)
  simp only [Bool.le_iff_imp,decide_eq_true_eq,Finset.mem_inter]
  exact ⟨⟨fun h=>ts h,fun h=>xs h⟩,fun a b=>⟨b,a⟩⟩

theorem lostWitness {n:Nat} (C:Circuit) (mono:Monotone2 C) (S T X:Finset (Fin n))
    (ts:T⊆S) (xs:X⊆S) (t:wireOut n C T=true) (x:wireOut n C X=true) (low:wireOut n C (X∩T)=false) :
    ∃r∈hist n C,costed r S=true ∧ costed r T=false ∧ out r T=true ∧ out r X=true ∧ out r (X∩T)=false :=by
  classical
  let E:=tests S T X
  have valid:=rawValid S T X ts xs
  obtain ⟨_,remain⟩:=costWitness E C.gates (raw n) (fun g hg=>⟨(mono g hg).1,(mono g hg).2⟩) (fun f hf=>(valid f hf).1)
  by_contra! no
  have flats:=remain (fun f hf=>(valid f hf).2) (by
    intro r hr rs rt yt yx
    change out r (X∩T)=true
    have h:=no r hr rs rt yt yx
    cases e:out r (X∩T) <;> simp_all)
  have o:=memDefault (fun f:W n=>flat (liftRow E f)) _ noneW C.output (by simp [flat,liftRow,noneW]) flats
  exact Bool.noConfusion (low.symm.trans (o t x))
lemma costMono {n:Nat} (C:Circuit) (mono:Monotone2 C) (S T:Finset (Fin n)) (ts:T⊆S) :
    ∀r∈hist n C,costed r T=true → costed r S=true :=
  (costWitness (tests S T T) C.gates (raw n) (fun g hg=>⟨(mono g hg).1,(mono g hg).2⟩)
    (fun f hf=>(rawValid S T T ts ts f hf).1)).1
def losses {n:Nat} (rs:List (Record n)) (S T:Finset (Fin n)) :=rs.filter fun r=>costed r S && !costed r T
lemma priceLoss {n:Nat} (rs:List (Record n)) (S T:Finset (Fin n))
    (incl:∀ r∈rs,costed r T=true → costed r S=true) :
    Price rs S=Price rs T+(losses rs S T).length :=by
  induction rs with
  | nil=>rfl
  | cons a rs ih=>
    have head:=incl a (by simp)
    have rest:=ih (fun r hr=>incl r (by simp [hr]))
    simp only [Price,losses] at rest ⊢
    cases x:costed a S <;> cases y:costed a T <;>
      simp_all [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma shortList {α:Type} (l:List α) (h:l.length≤1) {a b:α} (ha:a∈l) (hb:b∈l) : a=b :=by
  cases l with
  | nil=>simp at ha
  | cons v vs=>
    cases vs with
    | nil=>simpa [List.mem_singleton.mp ha] using (List.mem_singleton.mp hb).symm
    | cons w ws=>simp at h

theorem priceStep {n:Nat} (C:Circuit) (mono:Monotone2 C) (S T X:Finset (Fin n))
    (ts:T⊆S) (xs:X⊆S) (t:wireOut n C T=true) (x:wireOut n C X=true) (low:wireOut n C (X∩T)=false) :
    Price (hist n C) T<Price (hist n C) S :=by
  obtain ⟨r,hr,rs,rt,_⟩:=lostWitness C mono S T X ts xs t x low
  have hi:r∈losses (hist n C) S T:=by simp [losses,hr,rs,rt]
  have h:=List.length_pos_of_mem hi
  have sum:=priceLoss (hist n C) S T (costMono C mono S T ts)
  omega
theorem sole {n:Nat} (C:Circuit) (mono:Monotone2 C) (S T X:Finset (Fin n))
    (ts:T⊆S) (xs:X⊆S) (t:wireOut n C T=true) (x:wireOut n C X=true) (low:wireOut n C (X∩T)=false)
    (r:Record n) (hr:r∈hist n C) (rs:costed r S=true) (rt:costed r T=false)
    (small:Price (hist n C) S≤Price (hist n C) T+1) :
    out r X=true ∧ out r (X∩T)=false :=by
  obtain ⟨b,hb,bs,bt,_,bx,by'⟩:=lostWitness C mono S T X ts xs t x low
  have sum:=priceLoss (hist n C) S T (costMono C mono S T ts)
  have h0:r∈losses (hist n C) S T:=by simp [losses,hr,rs,rt]
  have h1:b∈losses (hist n C) S T:=by simp [losses,hb,bs,bt]
  obtain rfl:=shortList _ (by omega) h0 h1
  exact ⟨bx,by'⟩
end PEqualNP.Outside.L_meta_4837_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_4837_aux
def term {n:Nat} (S M:Finset (Fin n)) (f:W n) :=M⊆S ∧ ∀X⊆S,f X=true ↔ M⊆X
def simple {n:Nat} (S:Finset (Fin n)) (f:W n) := (∀ X⊆S,f X=false) ∨ ∃M,term S M f
def splitRec {n:Nat} (S:Finset (Fin n)) (r:Record n) :=
  ∃ a b M N,r=(.or,[a,b]) ∧ term S M a ∧ term S N b ∧ ¬M⊆N ∧ ¬N⊆M
lemma rawSimple {n:Nat} (S:Finset (Fin n)) : ∀f∈raw n,simple S f :=by
  intro f hf;obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hf
  by_cases hv:v∈S
  · exact Or.inr ⟨{v},by simpa using hv,fun X _=>by simp⟩
  · exact Or.inl fun X hx=>by simp [show v∉X from fun h=>hv (hx h)]
lemma eqSimple {n:Nat} {S:Finset (Fin n)} {f g:W n} (h:∀X⊆S,f X=g X) (s:simple S g) : simple S f :=by
  rcases s with z|⟨M,ms,mm⟩
  · exact Or.inl fun X hs=>(h X hs).trans (z X hs)
  · exact Or.inr ⟨M,ms,fun X hs=>by rw [h X hs];exact mm X hs⟩
lemma simpleStep {n:Nat} (S:Finset (Fin n)) (r:Record n) (base:r.1=.and ∨ r.1=.or)
    (len:r.2.length≤2) (hs:∀f∈r.2,simple S f) (no:¬splitRec S r) : simple S (out r) :=by
  rcases r with ⟨op,rs⟩;change op=.and ∨ op=.or at base;change rs.length≤2 at len
  cases rs with
  | nil =>
    rcases base with rfl|rfl
    · exact Or.inr ⟨∅,Finset.empty_subset _,fun X _=>by simp [out,GateOp.eval]⟩
    · exact Or.inl fun _ _=>rfl
  | cons a tail =>
    cases tail with
    | nil =>
      apply eqSimple (g:=a) _ (hs a (by simp))
      intro X _;rcases base with rfl|rfl <;> simp [out,GateOp.eval]
    | cons b tail =>
      cases tail with
      | cons _ _=>simp at len
      | nil =>
        have sa:=hs a (by simp);have sb:=hs b (by simp)
        rcases base with rfl|rfl
        · rcases sa with za|⟨M,ms,ma⟩
          · exact Or.inl fun X h=>by simp [out,GateOp.eval,za X h]
          rcases sb with zb|⟨N,ns,nb⟩
          · exact Or.inl fun X h=>by simp [out,GateOp.eval,zb X h]
          exact Or.inr ⟨M∪N,Finset.union_subset ms ns,fun X h=>by simp [out,GateOp.eval,ma X h,nb X h,Finset.union_subset_iff]⟩
        · rcases sa with za|⟨M,hm⟩
          · exact eqSimple (g:=b) (fun X h=>by simp [out,GateOp.eval,za X h]) sb
          rcases sb with zb|⟨N,hn⟩
          · exact eqSimple (g:=a) (fun X h=>by simp [out,GateOp.eval,zb X h]) (Or.inr ⟨M,hm⟩)
          by_cases le:M⊆N
          · refine Or.inr ⟨M,hm.1,fun X h=>?_⟩
            simp only [out,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true,hm.2 X h,hn.2 X h]
            exact or_iff_left_of_imp (fun nx=>le.trans nx)
          by_cases ge:N⊆M
          · refine Or.inr ⟨N,hn.1,fun X h=>?_⟩
            simp only [out,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true,hm.2 X h,hn.2 X h]
            exact or_iff_right_of_imp (fun mx=>ge.trans mx)
          exact (no ⟨a,b,M,N,rfl,hm,hn,le,ge⟩).elim

theorem simpleRun {n:Nat} (S:Finset (Fin n)) (gs:List Gate) (ws:List (W n))
    (mono:∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (simpWs:∀f∈ws,simple S f) (no:∀r∈history gs ws,¬splitRec S r) : ∀f∈gs.foldl advance ws,simple S f :=by
  induction gs generalizing ws with
  | nil=>exact simpWs
  | cons g gs ih=>
    obtain ⟨op,cap⟩:=mono g (by simp)
    have add:=simpleStep S (recAt ws g) op (by simpa [recAt] using cap) (by
      intro f hf;obtain ⟨i,_,rfl⟩:=List.mem_map.mp hf
      exact memDefault (simple S) _ noneW i (Or.inl fun _ _=>rfl) simpWs) (no _ (by simp [history]))
    exact ih (advance ws g) (fun v hv=>mono v (by simp [hv])) (spread _ _ _ simpWs add)
      (fun r hr=>no r (List.mem_cons_of_mem _ hr))

/-- Before the first OR with incomparable conjunctive operands, every wire is zero or a conjunction on subsets of S. -/
theorem firstSplit {n:Nat} (C:Circuit) (mono:Monotone2 C) (S:Finset (Fin n)) (outNon:¬simple S (wireOut n C)) :
    ∃r∈hist n C,splitRec S r :=by
  classical
  by_contra! no
  exact outNon (memDefault (simple S) _ noneW _ (Or.inl fun _ _=>rfl)
    (simpleRun S _ _ (fun g hg=>⟨(mono g hg).1,(mono g hg).2⟩) (rawSimple S) no))
end PEqualNP.Outside.L_meta_4837_aux

namespace PEqualNP.Outside.L_meta_4837_aux
abbrev V (n:Nat) := Fin n
def hasEdge {n:Nat} (G:SimpleGraph (V n)) (S:Finset (V n)) : Prop := ∃u∈S,∃v∈S,G.Adj u v
def twoTerm {n:Nat} (M N X:Finset (V n)) := M⊆X ∨ N⊆X
def pairSensitive {n:Nat} (G:SimpleGraph (V n)) (S M N:Finset (V n)) :=
  ∀u∈M∪N,∀ X⊆S,hasEdge G X → ¬hasEdge G (X.erase u) →
    twoTerm M N X ∧ ¬twoTerm M N (X.erase u)
lemma pairAdj {n:Nat} (G:SimpleGraph (V n)) (a b:V n) :
    hasEdge G {a,b} ↔ G.Adj a b :=by
  constructor
  · rintro ⟨i,hi,j,hj,edge⟩
    have hi' : i=a ∨ i=b:=by simpa using hi
    have hj' : j=a ∨ j=b:=by simpa using hj
    rcases hi' with rfl|rfl <;> rcases hj' with rfl|rfl
    all_goals first | exact edge | exact edge.symm | exact (G.loopless.irrefl _ edge).elim
  · intro h;exact ⟨a,by simp,b,by simp,h⟩
lemma across {n:Nat} (G:SimpleGraph (V n)) (S M N:Finset (V n)) (u:V n)
    (inM:u∈M) (notN:u∉N) (sub:M⊆S) (sens:pairSensitive G S M N)
    (d:∃ a∈S,∃ b∈S,a≠b ∧ G.Adj u a ∧ G.Adj u b) : M={u} :=by
  obtain ⟨a,ha,b,hb,ne,ea,eb⟩:=d
  have onPair (y:V n) (hy:y∈S) (ey:G.Adj u y) : M⊆{u,y} :=by
    have uy:u≠y:=ey.ne
    have claim:=sens u (Finset.mem_union_left _ inM) {u,y} (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro (sub inM) hy) ((pairAdj G u y).2 ey)
    have no : ¬hasEdge G (({u,y}:Finset _).erase u):=by
      have e : ({u,y}:Finset _).erase u={y}:=by ext t;simp;grind
      simp [e,hasEdge]
    obtain ⟨hm,none⟩:=claim no
    rcases hm with yes|other
    · exact yes
    · exact False.elim (none (Or.inr fun v hv=>Finset.mem_erase.mpr ⟨fun e=>notN (e ▸ hv),other hv⟩))
  have qa:=onPair a ha ea;have qb:=onPair b hb eb
  apply Finset.Subset.antisymm _ (by simpa using inM)
  intro v hv
  have one:=qa hv;have two:=qb hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at one two ⊢
  grind

/-- Two distinct neighbors force each conjunctive operand of a sole distinguishing OR to be a singleton. Its two vertices would then have the same neighbors, producing a four-cycle. -/
theorem noModule {n:Nat} (G:SimpleGraph (V n)) (S M N:Finset (V n)) (ms:M⊆S) (ns:N⊆S)
    (left:¬M⊆N) (right:¬N⊆M)
    (deg:∀u∈S,∃ a∈S,∃ b∈S,a≠b ∧ G.Adj u a ∧ G.Adj u b)
    (nosq:∀u w a b:V n,u≠w → a≠b → G.Adj u a → G.Adj u b → G.Adj w a → ¬G.Adj w b)
    (sens:pairSensitive G S M N) : False :=by
  classical
  obtain ⟨u,hu,hun⟩:=Finset.not_subset.mp left
  obtain ⟨w,hw,hwm⟩:=Finset.not_subset.mp right
  have sm:=across G S M N u hu hun ms sens (deg u (ms hu))
  have flip:pairSensitive G S N M:=by
    intro i hi X hs he hn
    rw [Finset.union_comm] at hi
    simpa [twoTerm,or_comm] using sens i hi X hs he hn
  have sn:=across G S N M w hw hwm ns flip (deg w (ns hw))
  have ne:u≠w:=by intro e;exact hun (e ▸ hw)
  have minu:=ms hu;have minw:=ns hw
  rw [sm,sn] at sens
  have uw:¬G.Adj u w:=by
    intro e
    have c:=sens u (by simp) {u,w} (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro minu minw) ((pairAdj G _ _).2 e)
    have erase : ({u,w}:Finset _).erase u={w}:=by ext t;simp;grind
    rw [erase] at c
    have no:¬hasEdge G {w}:=by simp [hasEdge]
    exact (c no).2 (Or.inr (Finset.Subset.refl _))
  have neighbor (v:V n) (hv:v∈S) (h:G.Adj u v) : G.Adj w v :=by
    by_contra neg
    have uv:=h.ne
    have eq:({u,w,v}:Finset _).erase u={w,v}:=by ext t;simp;grind
    have one:hasEdge G {u,w,v}:=⟨u,by simp,v,by simp,h⟩
    have cut:=sens u (by simp) {u,w,v} (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro minu (And.intro minw hv)) one
    rw [eq] at cut
    exact (cut (fun t=>neg ((pairAdj G w v).mp t))).2 (Or.inr (by simp))
  obtain ⟨a,ha,b,hb,ab,ea,eb⟩:=deg u minu
  exact nosq u w a b ne ab ea eb (neighbor a ha ea) (neighbor b hb eb)
end PEqualNP.Outside.L_meta_4837_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_4837_aux

def DegTwo {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) :=
  ∀u∈S,∃ a∈S,∃ b∈S,a≠b ∧ G.Adj u a ∧ G.Adj u b
def NoSquare {n:Nat} (G:SimpleGraph (Fin n)) :=
  ∀u w a b:Fin n,u≠w → a≠b → G.Adj u a → G.Adj u b → G.Adj w a → ¬G.Adj w b

lemma survives {n:Nat} {G:SimpleGraph (Fin n)} {S:Finset (Fin n)} (deg:DegTwo G S) (v:Fin n) (hv:v∈S) :
    hasEdge G (S.erase v) :=by
  obtain ⟨a,ha,_,_,_,ea,_⟩:=deg v hv
  obtain ⟨b,hb,c,hc,bc,ab,ac⟩:=deg a ha
  have mem:a∈S.erase v:=Finset.mem_erase.mpr ⟨ea.ne.symm,ha⟩
  by_cases eq:b=v
  · exact ⟨a,mem,c,Finset.mem_erase.mpr ⟨fun h=>bc (eq.trans h.symm),hc⟩,ac⟩
  · exact ⟨a,mem,b,Finset.mem_erase.mpr ⟨eq,hb⟩,ab⟩

lemma falseSingle {n:Nat} (G:SimpleGraph (Fin n)) (v:Fin n) : ¬hasEdge G {v} :=by simp [hasEdge]
lemma notTerm {n:Nat} {G:SimpleGraph (Fin n)} {S:Finset (Fin n)} {f:W n}
    (correct:∀X,f X=true ↔ hasEdge G X) (deg:DegTwo G S) (pos:S.Nonempty) : ¬simple S f :=by
  obtain ⟨u,hu⟩:=pos
  obtain ⟨a,ha,b,hb,ab,ea,eb⟩:=deg u hu
  have both (v:Fin n) (hv:G.Adj u v):f {u,v}=true:=(correct _).2 ((pairAdj G _ _).2 hv)
  have sub (v:Fin n) (hv:v∈S):({u,v}:Finset _)⊆S:=by simp [Finset.insert_subset_iff,hu,hv]
  rintro (zero|⟨M,_,rule⟩)
  · exact Bool.noConfusion ((zero _ (sub a ha)).symm.trans (both a ea))
  · have a':= (rule _ (sub a ha)).1 (both a ea)
    have b':= (rule _ (sub b hb)).1 (both b eb)
    have inside:M⊆{u}:=by
      intro v hv
      have one:=a' hv;have two:=b' hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at one two ⊢
      grind
    exact falseSingle G u ((correct _).1 ((rule _ (by simpa using hu)).2 inside))

/-- In an induced subgraph of minimum degree at least two, deleting some vertex deactivates at least two OR gates. -/
theorem twoLost {n:Nat} (G:SimpleGraph (Fin n)) (C:Circuit) (mono:Monotone2 C)
    (correct:∀X,wireOut n C X=true ↔ hasEdge G X) (nosq:NoSquare G)
    (S:Finset (Fin n)) (pos:S.Nonempty) (deg:DegTwo G S) :
    ∃u∈S,Price (hist n C) (S.erase u)+2≤Price (hist n C) S :=by
  classical
  by_contra! small
  obtain ⟨r,hr,a,b,M,N,rfl,ma,nb,l,r'⟩:=firstSplit C mono S (notTerm correct deg pos)
  let R : Record n:=(.or,[a,b])
  have rule (X:Finset (Fin n)) (xs:X⊆S) : out R X=true ↔ twoTerm M N X :=by
    simp [R,out,GateOp.eval,twoTerm,ma.2 X xs,nb.2 X xs]
  apply noModule G S M N ma.1 nb.1 l r' deg nosq
  intro v hv X xs ex clean
  have vs:v∈S:=(Finset.union_subset ma.1 nb.1) hv
  let T:=S.erase v
  have xt:X∩T=X.erase v:=by ext t;simp [T];have :=@xs t;grind
  have copy:wireOut n C (X∩T)=false:=by
    cases eq:wireOut n C (X∩T)
    · rfl
    · exact (clean (xt ▸ (correct _).1 eq)).elim
  have ts:T⊆S:=Finset.erase_subset _ _
  have tpos:wireOut n C T=true:=(correct _).2 (survives deg v vs)
  have cs:costed R S=true:=by simp [R,costed,(ma.2 S (Finset.Subset.refl _)).2 ma.1,(nb.2 S (Finset.Subset.refl _)).2 nb.1]
  have ct:costed R T=false:=by
    rcases Finset.mem_union.mp hv with vm|vn
    · have na:a T=false:=by
        cases e:a T
        · rfl
        · exact ((Finset.mem_erase.mp ((ma.2 T ts).1 e vm)).1 rfl).elim
      simp [R,costed,na]
    · have nn:b T=false:=by
        cases e:b T
        · rfl
        · exact ((Finset.mem_erase.mp ((nb.2 T ts).1 e vn)).1 rfl).elim
      simp [R,costed,nn]
  have budget:=small v vs
  have val:=sole C mono S T X ts xs tpos ((correct _).2 ex) copy R hr cs ct (by dsimp [T];omega)
  refine ⟨(rule X xs).1 val.1,?_⟩
  intro yes
  have off:=xt ▸ val.2
  exact Bool.noConfusion (off.symm.trans ((rule _ ((Finset.erase_subset _ _).trans xs)).2 yes))
end PEqualNP.Outside.L_meta_4837_aux

namespace PEqualNP.Outside.L_meta_4837_aux
open SimpleGraph
open scoped Classical
def restricted {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v:=u∈S ∧ v∈S ∧ G.Adj u v
  symm :=⟨fun _ _ h=>⟨h.2.1,h.1,h.2.2.symm⟩⟩
  loopless :=⟨fun _ h=>h.2.2.ne rfl⟩
noncomputable def es {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) : Finset (Sym2 (Fin n)) :=by
  classical
  exact (restricted G S).edgeFinset
noncomputable def ns {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) (u:Fin n) : Finset (Fin n) :=by
  classical
  exact S.filter (G.Adj u)
lemma memEs {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) (u v:Fin n) :
    s(u,v)∈es G S ↔ u∈S ∧ v∈S ∧ G.Adj u v :=by
  classical
  exact SimpleGraph.mem_edgeFinset
lemma memNs {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) (u v:Fin n) :
    v∈ns G S u ↔ v∈S ∧ G.Adj u v :=by
  classical
  exact Finset.mem_filter
lemma sizeEs {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) :
    (es G S).card={e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀v∈e,v∈S}.ncard :=by
  classical
  have eq:(↑(es G S):Set _)={e:Sym2 (Fin n)|e∈G.edgeSet ∧ ∀v∈e,v∈S}:=by
    ext e;induction e using Sym2.ind with
    | _ a b=>simp only [Finset.mem_coe,memEs,Set.mem_ofPred_eq,SimpleGraph.mem_edgeSet,Sym2.mem_iff];grind
  rw [←eq,Set.ncard_coe_finset]
lemma isPos {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) :
    (es G S).Nonempty ↔ hasEdge G S :=by
  constructor
  · rintro ⟨e,he⟩;induction e using Sym2.ind with
    | _ a b=>obtain ⟨ha,hb,h⟩:=(memEs _ _ _ _).mp he;exact ⟨_,ha,_,hb,h⟩
  · rintro ⟨u,hu,v,hv,h⟩;exact ⟨_,(memEs _ _ _ _).mpr ⟨hu,hv,h⟩⟩
lemma degreeR {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) (v:Fin n) (hv:v∈S) :
    (restricted G S).degree v= (ns G S v).card :=by
  classical
  have e:(restricted G S).neighborFinset v=ns G S v:=by
    ext x;simp only [SimpleGraph.mem_neighborFinset,memNs];change (v∈S ∧ _ ∧ _) ↔ _;simp [hv]
  rw [←e];symm;exact SimpleGraph.card_neighborFinset_eq_degree (restricted G S) v
lemma degreeSum {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) :
    ∑v∈S,(ns G S v).card=2*(es G S).card :=by
  classical
  let H:=restricted G S
  have sub:∑v∈S,H.degree v=∑v,H.degree v:=by
    apply Finset.sum_subset (by simp)
    intro v _ hv
    rw [←H.card_neighborFinset_eq_degree v,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
    intro w hw;exact hv ((H.mem_neighborFinset v w).1 hw).1
  have same:∑v∈S,(ns G S v).card=∑v∈S,H.degree v:=Finset.sum_congr rfl (fun v hv=>(degreeR G S v hv).symm)
  exact same.trans (sub.trans H.sum_degrees_eq_twice_card_edges)
lemma eraseEq {n:Nat} (G:SimpleGraph (Fin n)) (S:Finset (Fin n)) (v:Fin n) (hv:v∈S) :
    (es G S).card=(es G (S.erase v)).card+(ns G S v).card :=by
  classical
  let H:=restricted G S
  have eq:es G S \ es G (S.erase v)=H.incidenceFinset v:=by
    ext e;induction e using Sym2.ind with
    | _ a b=>
      simp only [Finset.mem_sdiff,memEs,Finset.mem_erase,SimpleGraph.mem_incidenceFinset,
        SimpleGraph.mk'_mem_incidenceSet_iff]
      change (_ ∧ _ ∧ _) ∧ ¬((_ ∧ _) ∧ (_ ∧ _) ∧ _) ↔ (_ ∧ _ ∧ _) ∧ _
      grind
  have sub:es G (S.erase v)⊆es G S:=by
    intro e he;induction e using Sym2.ind with
    | _ a b=>
      obtain ⟨ha,hb,h⟩:=(memEs _ _ _ _).mp he
      exact (memEs _ _ _ _).mpr ⟨(Finset.mem_erase.mp ha).2,(Finset.mem_erase.mp hb).2,h⟩
  have c:=congrArg Finset.card eq
  rw [Finset.card_sdiff_of_subset sub,SimpleGraph.card_incidenceFinset_eq_degree] at c
  dsimp only [H] at c
  rw [degreeR G S v hv] at c
  have :=Finset.card_le_card sub
  omega
end PEqualNP.Outside.L_meta_4837_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SimpleGraph.Walk
namespace PEqualNP.Outside.L_meta_4837_aux
lemma noSquareOf {n:Nat} (G:SimpleGraph (Fin n)) (nocycle:∀v (c:G.Walk v v),c.IsCycle → c.length≠4) : NoSquare G :=by
  intro u w a b uw ab ua ub wa wb
  have au:=ua.ne.symm;have bu:=ub.ne.symm;have aw:=wa.ne.symm;have bw:=wb.ne.symm
  let path:G.Walk u u:=.cons ua (.cons wa.symm (.cons wb (.cons ub.symm .nil)))
  have cycle:path.IsCycle:=by
    simp [path,isCycle_def,isTrail_def,uw,uw.symm,ab,ua.ne,au,ub.ne,bu,aw,wb.ne]
  exact nocycle u path cycle rfl

lemma priceUpper {n:Nat} (gs:List Gate) (ws:List (W n)) (j:Nat) (A:Finset Nat) (S:Finset (Fin n)) (covers:
    ∀k (g:Gate),gs[k]?=some g → g.op=.or → j+k∈A) : Price (history gs ws) S≤A.card :=by
  induction gs generalizing ws j A with
  | nil=>simp [history,Price]
  | cons g gs ih=>
    have tail:Price (history gs (advance ws g)) S≤(A.erase j).card:=by
      apply ih (advance ws g) (j+1) (A.erase j)
      intro k z get op
      have mem:=covers (k+1) z (by simpa using get) op
      exact Finset.mem_erase.mpr ⟨by omega,by convert mem using 1; omega⟩
    have count : Price (history (g::gs) ws) S=Price (history gs (advance ws g)) S+
        (if costed (recAt ws g) S then 1 else 0):=by cases e:costed (recAt ws g) S <;> simp [history,Price,e,Nat.add_comm]
    rw [count]
    cases e:costed (recAt ws g) S
    · simpa using tail.trans (Finset.card_le_card (Finset.erase_subset _ _))
    · have op:g.op=.or:=by
        unfold recAt costed at e
        cases h:g.op <;> simp [h] at e ⊢
      have mem:j∈A:=by simpa using covers 0 g (by simp) op
      have eq:=Finset.card_erase_add_one mem
      simp only [ite_true];omega
end PEqualNP.Outside.L_meta_4837_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_4837_aux

/-- Induct on the vertex set. A leaf costs one lost OR while its edge is removed. If there is no leaf or isolate, sparsity forces every vertex to have degree two. -/
theorem bound {n:Nat} (G:SimpleGraph (Fin n)) (C:Circuit) (mono:Monotone2 C)
    (correct:∀X,wireOut n C X=true ↔ hasEdge G X) (noc:NoSquare G)
    (sparse:∀S,(es G S).card≤S.card) (S:Finset (Fin n)) :
    (es G S).card≤Price (hist n C) S+1 :=by
  classical
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases few:(es G S).card≤1
  · omega
  have has:(es G S).Nonempty:=Finset.card_pos.mp (by omega)
  obtain ⟨v,hv,_,_,_⟩:=(isPos G S).1 has
  let R:=hist n C
  by_cases low:∃v∈S,(ns G S v).card≤1
  · obtain ⟨u,hu,low⟩:=low
    let T:=S.erase u
    have smaller:=ih T (Finset.erase_ssubset hu)
    have eq:=eraseEq G S u hu
    change (es G S).card=(es G T).card+_ at eq
    have ts:T⊆S:=Finset.erase_subset _ _
    have monot:=priceLoss R S T (costMono C mono S T ts)
    by_cases empty:(ns G S u).card=0
    · change (es G T).card≤Price R T+1 at smaller
      change (es G S).card≤Price R S+1
      omega
    have one:(ns G S u).card=1:=by omega
    obtain ⟨w,hw⟩:=Finset.card_pos.mp (by omega : 0<(ns G S u).card)
    obtain ⟨ws,adj⟩:=(memNs G S u w).1 hw
    have x:wireOut n C {u,w}=true:=(correct _).2 ((pairAdj G _ _).2 adj)
    have t:wireOut n C T=true:=(correct _).2 ((isPos G T).1 (Finset.card_pos.mp (by omega)))
    have iw:({u,w}:Finset _)∩T={w}:=by ext a;simp [T];have ne:=adj.ne;grind
    have off:wireOut n C (({u,w}:Finset _)∩T)=false:=by
      rw [iw]
      cases h:wireOut n C {w}
      · rfl
      · exact (falseSingle G w ((correct _).1 h)).elim
    have high:=priceStep C mono S T {u,w} ts (by simp [Finset.insert_subset_iff,hu,ws]) t x off
    omega
  · push Not at low
    have deg:DegTwo G S:=by
      intro u hu
      obtain ⟨a,ha,b,hb,ab⟩:=Finset.one_lt_card.mp (low u hu)
      obtain ⟨as,ea⟩:=(memNs _ _ _ _).1 ha
      obtain ⟨bs,eb⟩:=(memNs _ _ _ _).1 hb
      exact ⟨a,as,b,bs,ab,ea,eb⟩
    obtain ⟨u,hu,cost⟩:=twoLost G C mono correct noc S ⟨v,hv⟩ deg
    have each:(ns G S u).card≤2:=by
      by_contra! big
      have less:=Finset.sum_lt_sum (s:=S) (f:=fun _=>2) (g:=fun v=>(ns G S v).card)
        (fun v hv=>low v hv) ⟨u,hu,big⟩
      rw [degreeSum] at less
      simp only [Finset.sum_const,Nat.nsmul_eq_mul] at less
      have cap:=sparse S
      omega
    have eq:=eraseEq G S u hu
    have small:=ih (S.erase u) (Finset.erase_ssubset hu)
    omega

theorem finalResult :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → G.edgeSet.ncard ≤ A.card + 1 :=by
  classical
  intro n G C A sparse cyc mono spec covers
  have correct (X:Finset (Fin n)) : wireOut n C X=true ↔ hasEdge G X :=by
    rw [physical,spec]
    simp only [decide_eq_true_eq,hasEdge]
    constructor
    · rintro ⟨u,v,h,hu,hv⟩;exact ⟨u,hu,v,hv,h⟩
    · rintro ⟨u,hu,v,hv,h⟩;exact ⟨u,v,h,hu,hv⟩
  have main:=bound G C mono correct (noSquareOf G cyc) (fun S=>by rw [sizeEs];exact sparse S) Finset.univ
  have count:=priceUpper C.gates (raw n) 0 A Finset.univ (fun k g h op=>by simpa using covers k g h op)
  rw [sizeEs] at main
  have setEq:{e:Sym2 (Fin n)|e∈G.edgeSet ∧ ∀ v∈e,v∈(Finset.univ:Finset (Fin n))}=G.edgeSet:=by ext;simp
  rw [setEq] at main
  exact main.trans (Nat.add_le_add_right count 1)
end PEqualNP.Outside.L_meta_4837_aux

theorem PEqualNP.Outside.L_meta_4837 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → G.edgeSet.ncard ≤ A.card + 1 :=
  PEqualNP.Outside.L_meta_4837_aux.finalResult
