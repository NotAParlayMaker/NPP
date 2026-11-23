import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta172

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private abbrev V (n : ℕ) := Fin n → Bool
private abbrev il := @Or.inl
private abbrev ir := @Or.inr
private abbrev cf := @congrFun
local macro "J" : term => `(Circuit)
local macro "cF" : term => `(circuitFun)
local macro "O" : tactic => `(tactic| omega)
local macro "W" : term => `(by omega)
local macro "X" t:term : tactic => `(tactic| exact $t)
local macro "Y" t:term : tactic => `(tactic| refine $t)
local macro "R" : tactic => `(tactic| rfl)
private def pq (n:ℕ) (x:V n):Bool :=
 decide (∃i j:Fin n,i.val+1=j.val/\x i=true/\x j=true)
private def pK (gs:List Gate) (w:List Bool):List Bool :=
 gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
private def p0 (C:J) {n:ℕ} (x:V n) (i:ℕ):Bool :=
 (C.wires (List.ofFn x)).getD i false
private def p8 (C:J) {n:ℕ} (t:ℕ) (x:V n):Bool :=
 p0 C x (n+t)
private def Ok (g:Gate):Prop :=
 g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
private lemma qu (C:J) (w:List Bool) :
  C.wires w=pK C.gates w:=rfl
private lemma zd (w:List Bool):pK [] w=w:=rfl
private lemma qA (g:Gate) (gs:List Gate) (w:List Bool) :
  pK (g::gs) w =
   pK gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
private lemma ql (gs1 gs2:List Gate) (w:List Bool) :
  pK (gs1++gs2) w=pK gs2 (pK gs1 w):=by
 induction gs1 generalizing w with
 | nil=>rfl
 | cons g gs1 ih=>simp[qA,ih]
private lemma qm (gs:List Gate) (w:List Bool) :
  (pK gs w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil=>simp[pK]
 | cons g gs ih=>
  rw[qA,ih];simp;O
private lemma q5 (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i< w.length) :
  (pK gs w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  rw[qA,ih _ (by simp;O)]
  rw[List.getD_eq_getElem _ _ (by simp;O),List.getD_eq_getElem _ _ hi]
  X List.getElem_append_left hi
private lemma kh (gs:List Gate) (w:List Bool) (i:ℕ)
  (hi:w.length+gs.length<=i) :
  (pK gs w).getD i false=false:=by
 rw[List.getD_eq_default _ _ (by rw[qm];X hi)]
private lemma p7 (C:J) {n:ℕ} (x:V n) (i:ℕ) (hi:i< n) :
  p0 C x i=x ⟨i,hi⟩:=by
 unfold p0
 rw[qu,q5 _ _ _ (by simp[hi])]
 rw[List.getD_eq_getElem _ _ (by simp[hi])]
 simp
private lemma z3 (C:J) {n:ℕ} (x:V n) (i:ℕ) (hi:n+C.size<=i) :
  p0 C x i=false:=by
 unfold p0
 rw[qu];X kh C.gates (List.ofFn x) i (by simpa [Circuit.size] using hi)
private lemma pj (C:J) {n:ℕ} (x:V n) (t:ℕ) (ht:t< C.size) :
  p0 C x (n+t) =
   (C.gates[t]'ht).op.eval
    ((C.gates[t]'ht).inputs.map fun i=>if i< n+t then p0 C x i else false):=by
 have b:C.gates=C.gates.take t++(C.gates[t]'ht)::C.gates.drop (t+1):=by
  have h1:=List.take_append_drop t C.gates
  have h2:C.gates.drop t=(C.gates[t]'ht)::C.gates.drop (t+1) :=
   List.drop_eq_getElem_cons ht
  rw[←h2,h1]
 set pre:=pK (C.gates.take t) (List.ofFn x) with hpre_def
 have a:pre.length=n+t:=by
  rw[hpre_def,qm,List.length_ofFn,List.length_take]
  have:t<=C.gates.length:=Nat.le_of_lt ht
  O
 have c:∀i,pre.getD i false=if i< n+t then p0 C x i else false:=by
  intro i
  split_ifs with hi
  ·unfold p0
   rw[qu,b,ql];X (q5 _ pre i W).symm
  ·X List.getD_eq_default _ _ W
 unfold p0
 conv_lhs=>rw[qu,b,ql,qA,←hpre_def]
 rw[q5 _ _ (n+t) (by simp[a])]
 rw[List.getD_eq_getElem _ _ (by simp[a])]
 rw[List.getElem_append_right W];simp only[a,Nat.sub_self,List.getElem_singleton];congr 1;X List.map_congr_left fun i _=>c i
private lemma pb (C:J) {n:ℕ} (x:V n) :
  cF n C x=p0 C x C.output:=rfl
private def e0 {n:ℕ}:V n:=fun _=>false
private def e1 {n:ℕ} (a:ℕ):V n:=fun i=>decide (i.val=a)
private def e2 {n:ℕ} (a b:ℕ):V n:=fun i=>decide (i.val=a\/i.val=b)
private def pe {n:ℕ} (a:ℕ):V n:=e2 a (a+1)
private lemma px {n:ℕ} {x:V n} :
  pq n x=true↔∃i j:Fin n,i.val+1=j.val/\x i=true/\x j=true:=by
 simp[pq]
private lemma zq (n:ℕ):pq n e0=false:=by
 simp[pq,e0]
private lemma pW (n a:ℕ):pq n (e1 a)=false:=by
 rw[Bool.eq_false_iff,Ne,px]
 rintro ⟨i,j,b,hi,hj⟩
 simp[e1] at hi hj;O
private lemma q0 {n a:ℕ} (ha:a+1< n):pq n (pe a)=true:=by
 rw[px];Y ⟨⟨a,by O⟩,⟨a+1,ha⟩,rfl,?_,?_⟩<;>simp[pe,e2]
private lemma jC {n a b:ℕ} (h1:a+1≠b) (h2:b+1≠a) :
  pq n (e2 a b)=false:=by
 rw[Bool.eq_false_iff,Ne,px]
 rintro ⟨i,j,c,hi,hj⟩
 simp[e2] at hi hj;rcases hi with rfl|rfl<;>rcases hj with h|h<;>O
private lemma z8 (n:ℕ) (y:V n) :
  pq (n+1) (Fin.snoc y false)=pq n y:=by
 apply Bool.eq_iff_iff.2;simp only[px]
 constructor
 ·rintro ⟨i,j,d,hi,hj⟩
  have a:j.val< n:=by
   by_contra h
   have c:j=Fin.last n:=Fin.ext (by simp[Fin.last];O)
   subst c;simp at hj
  have b:i.val< n :=W;Y ⟨⟨i.val,b⟩,⟨j.val,a⟩,d,?_,?_⟩
  ·have:i=Fin.castSucc ⟨i.val,b⟩:=Fin.ext rfl
   rw[this,Fin.snoc_castSucc] at hi;X hi
  ·have:j=Fin.castSucc ⟨j.val,a⟩:=Fin.ext rfl
   rw[this,Fin.snoc_castSucc] at hj;X hj
 ·rintro ⟨i,j,d,hi,hj⟩
  Y ⟨Fin.castSucc i,Fin.castSucc j,d,?_,?_⟩<;>simp[hi,hj]
private lemma qT (n:ℕ) (hn:1<=n) (y:V n) :
  pq (n+1) (Fin.snoc y true) =
   (y ⟨n-1,by O⟩||pq (n-1) (fun i=>y ⟨i.val,by O⟩)):=by
 apply Bool.eq_iff_iff.2;simp only[px,Bool.or_eq_true]
 constructor
 ·rintro ⟨i,j,e,hi,hj⟩
  by_cases f:j.val=n
  ·left
   have a:i=Fin.castSucc ⟨n-1,by O⟩:=Fin.ext (by simp;O)
   rw[a,Fin.snoc_castSucc] at hi;X hi
  ·by_cases g:j.val=n-1
   ·left
    have b:j=Fin.castSucc ⟨n-1,by O⟩:=Fin.ext (by simp;O)
    rw[b,Fin.snoc_castSucc] at hj;X hj
   ·right
    have c:j.val< n-1 :=W;have d:i.val< n-1 :=W;Y ⟨⟨i.val,d⟩,⟨j.val,c⟩,e,?_,?_⟩
    ·have:i=Fin.castSucc ⟨i.val,by O⟩:=Fin.ext rfl
     rw[this,Fin.snoc_castSucc] at hi;X hi
    ·have:j=Fin.castSucc ⟨j.val,by O⟩:=Fin.ext rfl
     rw[this,Fin.snoc_castSucc] at hj;X hj
 ·rintro (hy|⟨i,j,e,hi,hj⟩)
  ·Y ⟨Fin.castSucc ⟨n-1,by O⟩,Fin.last n,by simp[Fin.last];O,?_,?_⟩
   ·rw[Fin.snoc_castSucc];X hy
   ·simp
  ·Y ⟨Fin.castSucc ⟨i.val,by O⟩,Fin.castSucc ⟨j.val,by O⟩,e,?_,?_⟩
   ·rw[Fin.snoc_castSucc];X hi
   ·rw[Fin.snoc_castSucc];X hj
private lemma ps {n:ℕ} (hn:2<=n) :
  ∃x y:V n,pq n x≠pq n y:=by
 Y ⟨e0,pe 0,?_⟩;rw[zq,q0 W]
 decide
private def pa (g:Gate):List ℕ :=
 match g.op,g.inputs with
 | .not,[]=>[]
 | .not,a::_=>[a]
 | _,ins=>ins
private def pC (n t w:ℕ) (g:Gate):Prop :=
 w∈pa g/\w< n+t
private def z0 (C:J):Prop :=
 ∀g∈C.gates,g.op≠GateOp.not
private lemma jD {op:GateOp} (d:op=.and\/op=.or)
  {l1 l2:List Bool} (a:l1.length=l2.length)
  (c:∀i (hi:i< l1.length),l1[i]=true->l2[i]'(a▸hi)=true) :
  op.eval l1=true->op.eval l2=true:=by
 rcases d with rfl|rfl
 ·simp only[GateOp.eval,List.all_eq_true,id_eq]
  intro h b hb;obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem hb;X c i (a.symm▸hi) (h _ (List.getElem_mem (a.symm▸hi)))
 ·simp only[GateOp.eval,List.any_eq_true,id_eq]
  rintro ⟨b,hb,rfl⟩
  obtain ⟨i,hi,e⟩:=List.getElem_of_mem hb;X ⟨l2[i]'(a▸hi),List.getElem_mem (a▸hi),c i hi e⟩
private lemma zz (C:J) {n:ℕ} (f:FanInTwo C) (g:z0 C)
  {x y:V n} (j:∀i,x i=true->y i=true) :
  ∀k,p0 C x k=true->p0 C y k=true:=by
 intro k
 induction k using Nat.strong_induction_on with
 | ind k ih=>
  intro hx;by_cases hk:k< n
  ·rw[p7 C x k hk] at hx
   rw[p7 C y k hk];X j ⟨k,hk⟩ hx
  ·by_cases m:k< n+C.size
   ·set t:=k-n
    have ht:t< C.size :=W;have c:k=n+t :=W;rw[c] at hx ⊢;rw[pj C x t ht] at hx;rw[pj C y t ht];have b:C.gates[t]'ht∈C.gates:=List.getElem_mem ht;have a:=(f _ b).1;have d:=g _ b
    have l:(C.gates[t]'ht).op=.and\/(C.gates[t]'ht).op=.or:=by
     simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at a;rcases a with h|h|h
     ·X il h
     ·X ir h
     ·X absurd h d
    Y jD l (by simp) (fun i hi e=>?_) hx
    simp only[List.getElem_map] at e ⊢
    split_ifs at e ⊢ with hlt
    X ih _ W e
   ·rw[z3 C x k W] at hx
    cases hx
private def qV (n t0 target i:ℕ):ℕ :=
 if i=n+t0 then target
 else if i< n+t0 then i
 else i-1
private def qQ (C:J) (n t0 target:ℕ):J :=
  { gates:=C.gates.take t0++(C.gates.drop (t0+1)).map fun g=>
      { op:=g.op,inputs:=g.inputs.map (qV n t0 target) }
    output:=qV n t0 target C.output }
private lemma qS (C:J) (a:FanInTwo C) (n t0 target:ℕ) :
  FanInTwo (qQ C n t0 target):=by
 intro g hg;simp only[qQ,List.mem_append,List.mem_map] at hg;rcases hg with hg|⟨g0,b,rfl⟩
 ·X a g (List.mem_of_mem_take hg)
 ·have h:=a g0 (List.mem_of_mem_drop b)
  X ⟨h.1,by simpa using h.2⟩
private lemma zn (C:J) (n t0 target:ℕ) (a:t0< C.size) :
  (qQ C n t0 target).size=C.size-1:=by
 simp only[qQ,Circuit.size,List.length_append,List.length_take,List.length_map,
  List.length_drop]
 have:t0< C.gates.length:=a
 O
private def ze:ℕ->List Gate->List Bool->Bool->List Bool
 | _,[],w,_=>w
 | 0,_::gs,w,v0=>pK gs (w++[v0])
 | k+1,g::gs,w,v0=>
  ze k gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) v0
private def pl (C:J) {n:ℕ} (x:V n) (t0:ℕ) (v0:Bool) (i:ℕ):Bool :=
 (ze t0 C.gates (List.ofFn x) v0).getD i false
private lemma jW (t0:ℕ) (gs:List Gate) (w:List Bool) (v0:Bool) :
  (ze t0 gs w v0).length=w.length+gs.length:=by
 induction t0 generalizing gs w with
 | zero=>
  cases gs with
  | nil=>simp[ze]
  | cons g gs=>simp[ze,qm];O
 | succ k ih=>
  cases gs with
  | nil=>simp[ze]
  | cons g gs=>simp[ze,ih];O
private lemma zx (t0:ℕ) (gs:List Gate) (w:List Bool) (v0:Bool)
  (a:t0< gs.length) :
  ze t0 gs w v0 =
   pK (gs.drop (t0+1)) (pK (gs.take t0) w++[v0]):=by
 induction t0 generalizing gs w with
 | zero=>
  cases gs with
  | nil=>simp at a
  | cons g gs=>simp[ze,pK]
 | succ k ih=>
  cases gs with
  | nil=>simp at a
  | cons g gs=>
   simp only[ze,List.take_succ_cons,List.drop_succ_cons,qA];X ih gs _ (by simp at a;O)
private lemma pA (C:J) {n:ℕ} (x:V n) (t0:ℕ) (c:t0< C.size)
  (v0:Bool) (i:ℕ) (hi:i< n+t0) :
  pl C x t0 v0 i=p0 C x i:=by
 unfold pl p0
 rw[qu,zx t0 C.gates (List.ofFn x) v0 c]
 have b:(pK (C.gates.take t0) (List.ofFn x)).length=n+t0:=by
  rw[qm,List.length_ofFn,List.length_take]
  have:t0<=C.gates.length:=Nat.le_of_lt c
  O
 rw[q5 _ _ i (by simp[b];O)]
 rw[List.getD_eq_getElem _ _ (by simp[b];O),List.getElem_append_left W]
 have a:C.gates=C.gates.take t0++C.gates.drop t0:=(List.take_append_drop t0 C.gates).symm
 conv_rhs=>rw[a,ql]
 rw[q5 _ _ i W,List.getD_eq_getElem _ _ W]
private lemma qs (C:J) {n:ℕ} (x:V n) (t0:ℕ) (b:t0< C.size)
  (v0:Bool) :
  pl C x t0 v0 (n+t0)=v0:=by
 unfold pl
 rw[zx t0 C.gates (List.ofFn x) v0 b]
 have a:(pK (C.gates.take t0) (List.ofFn x)).length=n+t0:=by
  rw[qm,List.length_ofFn,List.length_take]
  have:t0<=C.gates.length:=Nat.le_of_lt b
  O
 rw[q5 _ _ (n+t0) (by simp[a])]
 rw[List.getD_eq_getElem _ _ (by simp[a]),List.getElem_append_right W]
 simp[a]
private lemma jd (C:J) {n:ℕ} (x:V n) (t0:ℕ) (v0:Bool)
  (i:ℕ) (hi:n+C.size<=i) :
  pl C x t0 v0 i=false:=by
 unfold pl
 rw[List.getD_eq_default _ _ (by rw[jW];simpa [Circuit.size] using hi)]
private lemma z9 (C:J) {n:ℕ} (x:V n) (t0:ℕ)
  (j:t0< C.size) (v0:Bool) (t:ℕ) (ht:t0< t) (f:t< C.size) :
  pl C x t0 v0 (n+t) =
   (C.gates[t]'f).op.eval
    ((C.gates[t]'f).inputs.map fun i=>if i< n+t then pl C x t0 v0 i else false):=by
 have k:C.size=C.gates.length:=rfl
 have c:C.gates.drop (t0+1) =
   (C.gates.drop (t0+1)).take (t-(t0+1)) ++
    (C.gates[t]'f)::C.gates.drop (t+1):=by
  have h1:=List.take_append_drop (t-(t0+1)) (C.gates.drop (t0+1));have g:t-(t0+1)< (C.gates.drop (t0+1)).length:=by simp;O
  have h2:(C.gates.drop (t0+1)).drop (t-(t0+1)) =
    ((C.gates.drop (t0+1))[t-(t0+1)]'g)::(C.gates.drop (t0+1)).drop (t-(t0+1)+1) :=
   List.drop_eq_getElem_cons g
  have h:(C.gates.drop (t0+1))[t-(t0+1)]'g=C.gates[t]'f:=by
   rw[List.getElem_drop];congr 1;O
  have e:(C.gates.drop (t0+1)).drop (t-(t0+1)+1)=C.gates.drop (t+1):=by
   rw[List.drop_drop];congr 1;O
  rw[h,e] at h2;rw[←h2,h1]
 set base:=pK (C.gates.take t0) (List.ofFn x)++[v0] with hbase_def;set pre:=pK ((C.gates.drop (t0+1)).take (t-(t0+1))) base with hpre_def
 have b:base.length=n+t0+1:=by
  rw[hbase_def,List.length_append,qm,List.length_ofFn,List.length_take];simp;O
 have a:pre.length=n+t:=by
  rw[hpre_def,qm,b,List.length_take,List.length_drop];O
 have d:∀i,pre.getD i false=if i< n+t then pl C x t0 v0 i else false:=by
  intro i
  split_ifs with hi
  ·unfold pl
   rw[zx t0 C.gates (List.ofFn x) v0 j,c,ql];X (q5 _ pre i W).symm
  ·X List.getD_eq_default _ _ W
 unfold pl
 conv_lhs=>rw[zx t0 C.gates (List.ofFn x) v0 j,c,ql,qA,←hbase_def,←hpre_def]
 rw[q5 _ _ (n+t) (by simp[a])]
 rw[List.getD_eq_getElem _ _ (by simp[a]),List.getElem_append_right W]
 simp only[a,Nat.sub_self,List.getElem_singleton];congr 1;X List.map_congr_left fun i _=>d i
private lemma pV (C:J) {n:ℕ} (x:V n) (t0:ℕ)
  (b:t0< C.size) (v0:Bool) (hv:v0=p0 C x (n+t0)) :
  ∀k,pl C x t0 v0 k=p0 C x k:=by
 intro k
 induction k using Nat.strong_induction_on with
 | ind k ih=>
  by_cases h1:k< n+t0
  ·X pA C x t0 b v0 k h1
  ·by_cases h2:k=n+t0
   ·subst h2;rw[qs C x t0 b v0,hv]
   ·by_cases h3:k< n+C.size
    ·set t:=k-n
     have ht:t0< t :=W;have c:t< C.size :=W;have hk:k=n+t :=W;rw[hk,z9 C x t0 b v0 t ht c,pj C x t c];congr 1;apply List.map_congr_left;intro a _
     split_ifs with ha
     ·X ih a W
     ·rfl
    ·rw[jd C x t0 v0 k W,z3 C x k W]
private lemma jo (C:J) {n:ℕ} (j:FanInTwo C) (l:z0 C)
  (x:V n) (t0:ℕ) (c:t0< C.size) {v1 v2:Bool} (hv:v1=true->v2=true) :
  ∀k,pl C x t0 v1 k=true->pl C x t0 v2 k=true:=by
 intro k
 induction k using Nat.strong_induction_on with
 | ind k ih=>
  intro h1;by_cases g:k< n+t0
  ·rw[pA C x t0 c v1 k g] at h1
   rw[pA C x t0 c v2 k g];X h1
  ·by_cases m:k=n+t0
   ·subst m
    rw[qs C x t0 c v1] at h1;rw[qs C x t0 c v2];X hv h1
   ·by_cases q:k< n+C.size
    ·set t:=k-n
     have ht:t0< t :=W;have d:t< C.size :=W;have hk:k=n+t :=W;rw[hk] at h1 ⊢;rw[z9 C x t0 c v1 t ht d] at h1;rw[z9 C x t0 c v2 t ht d];have b:C.gates[t]'d∈C.gates:=List.getElem_mem d;have a:=(j _ b).1;have e:=l _ b
     have p:(C.gates[t]'d).op=.and\/(C.gates[t]'d).op=.or:=by
      simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at a;rcases a with h|h|h
      ·X il h
      ·X ir h
      ·X absurd h e
     Y jD p (by simp) (fun i hi f=>?_) h1
     simp only[List.getElem_map] at f ⊢
     split_ifs at f ⊢ with ha
     X ih _ W f
    ·rw[jd C x t0 v1 k W] at h1
     cases h1
private lemma k6 (C:J) {n:ℕ} (x:V n) (t0 target:ℕ)
    (j:t0< C.size) (h:target< n+t0\/n+C.size<=target) :
    ∀k,p0 (qQ C n t0 target) x (qV n t0 target k) =
      pl C x t0 (if target< n+t0 then p0 C x target else false) k:=by
  set v0:=if target< n+t0 then p0 C x target else false with hv0_def;set D:=qQ C n t0 target with hD_def;have z:C.size=C.gates.length:=rfl;have hh:D.size=C.size-1:=zn C n t0 target j
  have m:∀i,i< n+t0->p0 D x i=p0 C x i:=by
    intro i hi
    unfold p0
    rw[qu,qu]
    have d:D.gates=C.gates.take t0++(C.gates.drop (t0+1)).map fun g=>
        { op:=g.op,inputs:=g.inputs.map (qV n t0 target) }:=rfl
    have e:C.gates=C.gates.take t0++C.gates.drop t0:=(List.take_append_drop t0 C.gates).symm
    have hA:(pK (C.gates.take t0) (List.ofFn x)).length=n+t0:=by
      rw[qm,List.length_ofFn,List.length_take]
      have:t0<=C.gates.length:=Nat.le_of_lt j
      O
    rw[d,ql,q5 _ _ i W]
    conv_rhs=>rw[e,ql,q5 _ _ i W]
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih=>
    by_cases v:k< n+t0
    · have c:qV n t0 target k=k:=by simp[qV,show k≠n+t0 by O,v]
      rw[c,m k v,pA C x t0 j v0 k v]
    · by_cases hB:k=n+t0
      · subst hB
        have c:qV n t0 target (n+t0)=target:=by simp[qV]
        rw[c,qs C x t0 j v0,hv0_def];rcases h with htarg1|htarg2
        · rw[if_pos htarg1,m target htarg1]
        · rw[if_neg W,z3 D x target W]
      · by_cases hC:k< n+C.size
        · set t:=k-n
          have ht:t0< t :=W;have w:t< C.size :=W;have y:t-1< D.size :=W;have hk:k=n+t :=W
          have c:qV n t0 target k=n+(t-1):=by
            simp only[qV,show k≠n+t0 by O,↓reduceIte,v]
            O
          rw[c,hk,pj D x (t-1) y,z9 C x t0 j v0 t ht w]
          have p:D.gates[t-1]'y =
              { op:=(C.gates[t]'w).op,inputs:=(C.gates[t]'w).inputs.map (qV n t0 target) }:=by
            simp only[D,qQ]
            have b:(C.gates.take t0).length=t0:=by
              rw[List.length_take];X Nat.min_eq_left (Nat.le_of_lt j)
            rw[List.getElem_append_right (by rw[b];O),List.getElem_map]
            have q:(C.gates.drop (t0+1))[t-1-(C.gates.take t0).length]'(by rw[List.length_drop,b];O) =
                C.gates[t]'w:=by
              rw[List.getElem_drop];congr 1;rw[b];O
            rw[q]
          rw[p];simp only[List.map_map,Function.comp_def];congr 1;apply List.map_congr_left;intro a _;by_cases ha:a< n+t
          · rw[if_pos ha]
            have l:=ih a W;by_cases r:a=n+t0
            · subst r
              simp only[qV,↓reduceIte] at l ⊢;rcases h with htarg1|htarg2
              · rw[if_pos W,l]
              · rw[if_neg W,qs C x t0 j v0,hv0_def,if_neg W]
            · have s:qV n t0 target a< n+(t-1):=by
                unfold qV
                split_ifs<;>O
              rw[if_pos s,l]
          · rw[if_neg ha]
            have u:¬(qV n t0 target a< n+(t-1)):=by
              unfold qV
              split_ifs<;>O
            rw[if_neg u]
        · have f:n+D.size<=qV n t0 target k:=by
            unfold qV
            split_ifs<;>O
          rw[z3 D x _ f,jd C x t0 v0 k W]
private lemma z7 (C:J) {n:ℕ} (x:V n) (t0 target:ℕ)
  (b:t0< C.size) (a:target< n+t0\/n+C.size<=target) :
  cF n (qQ C n t0 target) x =
   pl C x t0 (if target< n+t0 then p0 C x target else false) C.output :=
 k6 C x t0 target b a C.output
private inductive qw where
 | const (b:Bool)
 | wire (idx:ℕ)
deriving DecidableEq
private def qw.isConst:qw->Bool
 | .const _=>true
 | .wire _=>false
private def qD (ws:List Bool):qw->Bool
 | .const b=>b
 | .wire idx=>ws.getD idx false
private def zC (bound:ℕ):qw->Prop
 | .const _=>True
 | .wire idx=>idx< bound
private lemma jX (ws extra:List Bool) (s:qw) (hs:zC ws.length s) :
  qD (ws++extra) s=qD ws s:=by
 cases s with
 | const b=>rfl
 | wire idx=>
  simp only[qD,zC] at hs ⊢;rw[List.getD_eq_getElem _ _ (by simp;O),List.getD_eq_getElem _ _ hs]
  X List.getElem_append_left hs
private def pr (env:List qw) (nextIdx:ℕ) (g:Gate):qw × Option Gate :=
 match g.op,g.inputs with
 | .not,[]=>(.const true,none)
 | .not,a::_=>
  match env.getD a (.const false) with
  | .const c=>(.const (!c),none)
  | .wire w=>(.wire nextIdx,some ⟨.not,[w]⟩)
 | .and,[]=>(.const true,none)
 | .and,[a]=>(env.getD a (.const false),none)
 | .and,a::b::_=>
  match env.getD a (.const false),env.getD b (.const false) with
  | .const false,_=>(.const false,none)
  | _,.const false=>(.const false,none)
  | .const true,s=>(s,none)
  | s,.const true=>(s,none)
  | .wire w1,.wire w2=>(.wire nextIdx,some ⟨.and,[w1,w2]⟩)
 | .or,[]=>(.const false,none)
 | .or,[a]=>(env.getD a (.const false),none)
 | .or,a::b::_=>
  match env.getD a (.const false),env.getD b (.const false) with
  | .const true,_=>(.const true,none)
  | _,.const true=>(.const true,none)
  | .const false,s=>(s,none)
  | s,.const false=>(s,none)
  | .wire w1,.wire w2=>(.wire nextIdx,some ⟨.or,[w1,w2]⟩)
 | _,_=>(.const false,none)
private structure z5 where
 fc:List qw
 gates:List Gate
 fb:List Bool
private def pZ (b:ℕ) (a:ℕ->Option qw) (st:z5) (g:Gate):z5 :=
  match a st.fb.length with
  | some s=>
    { fc:=st.fc++[s]
      gates:=st.gates
      fb:=st.fb++[false] }
  | none=>
    match pr st.fc (b+st.gates.length) g with
    | (s,none)=>
      { fc:=st.fc++[s]
        gates:=st.gates
        fb:=st.fb++[false] }
    | (s,some g')=>
      { fc:=st.fc++[s]
        gates:=st.gates++[g']
        fb:=st.fb++[true] }
private def qF (c:ℕ) (b:List qw) (a:ℕ->Option qw)
  (gs:List Gate):z5 :=
 gs.foldl (pZ c a) { fc:=b,gates:=[],fb:=[] }
private def kE (a:ℕ) (st:z5) (outIdx:ℕ):J :=
  { gates:=st.gates
    output:=match st.fc.getD outIdx (.const false) with
      | .wire w=>w
      | .const _=>a+st.gates.length }
private lemma kB (env:List qw) (nextIdx:ℕ) (g:Gate) (hg:Ok g)
  (e:∀s∈env,zC nextIdx s) :
  let (s,mg):=pr env nextIdx g
  match mg with
  | none=>zC nextIdx s
  | some g'=>s=.wire nextIdx/\g'.op=g.op/\Ok g'/\∀w∈g'.inputs,w< nextIdx:=by
 have d:∀a,zC nextIdx (env.getD a (.const false)):=by
  intro a;by_cases ha:a< env.length
  ·rw[List.getD_eq_getElem _ _ ha];X e _ (List.getElem_mem ha)
  ·rw[List.getD_eq_default _ _ W];trivial
 obtain ⟨op,ins⟩:=g;obtain ⟨i,f⟩:=hg
 cases op with
 | not=>
  cases ins with
  | nil=>simp[pr,zC]
  | cons a rest=>
   simp only[pr];have ha:=d a
   cases hga:env.getD a (.const false) with
   | const c=>simp[zC]
   | wire w=>
    rw[hga] at ha;X ⟨rfl,rfl,⟨by simp,by simp⟩,fun w' j=>by simp at j;subst j;X ha⟩
 | and=>
  match ins,f with
  | [],_=>simp[pr,zC]
  | [a],_=>X d a
  | [a,b],_=>
   simp only[pr];have ha:=d a;have hb:=d b
   cases hga:env.getD a (.const false) with
   | const ca=>
    cases ca<;>cases hgb:env.getD b (.const false) with
    | const cb=>cases cb<;>X trivial
    | wire wb=>rw[hgb] at hb;first|X trivial|X hb
   | wire wa=>
    rw[hga] at ha
    cases hgb:env.getD b (.const false) with
    | const cb=>cases cb<;>first|X trivial|X ha
    | wire wb=>
     rw[hgb] at hb;Y ⟨rfl,rfl,⟨by simp,by simp⟩,?_⟩
     intro w hw;simp at hw;rcases hw with rfl|rfl<;>assumption
  | _::_::_::_,h=>simp at h
 | or=>
  match ins,f with
  | [],_=>simp[pr,zC]
  | [a],_=>X d a
  | [a,b],_=>
   simp only[pr];have ha:=d a;have hb:=d b
   cases hga:env.getD a (.const false) with
   | const ca=>
    cases ca<;>cases hgb:env.getD b (.const false) with
    | const cb=>cases cb<;>X trivial
    | wire wb=>rw[hgb] at hb;first|X trivial|X hb
   | wire wa=>
    rw[hga] at ha
    cases hgb:env.getD b (.const false) with
    | const cb=>cases cb<;>first|X trivial|X ha
    | wire wb=>
     rw[hgb] at hb;Y ⟨rfl,rfl,⟨by simp,by simp⟩,?_⟩
     intro w hw;simp at hw;rcases hw with rfl|rfl<;>assumption
  | _::_::_::_,h=>simp at h
 | mod _=>simp at i
 | maj=>simp at i
private lemma ki (env:List qw) (e ws:List Bool) (g:Gate) (hg:Ok g)
  (f:env.length=e.length)
  (d:∀i,qD ws (env.getD i (.const false))=e.getD i false) :
  let (s,mg):=pr env ws.length g
  match mg with
  | none=>
   qD ws s=g.op.eval (g.inputs.map fun i=>e.getD i false)
  | some g'=>
   s=.wire ws.length /\
   g'.op.eval (g'.inputs.map fun i=>ws.getD i false) =
    g.op.eval (g.inputs.map fun i=>e.getD i false):=by
 obtain ⟨op,ins⟩:=g;obtain ⟨k,j⟩:=hg
 cases op with
 | not=>
  cases ins with
  | nil=>simp[pr,qD,GateOp.eval]
  | cons a rest=>
   simp only[pr];have ha:=d a
   cases hga:env.getD a (.const false) with
   | const c=>
    rw[hga] at ha;simp only[qD,GateOp.eval,List.map_cons,List.headD_cons] at ha ⊢;rw[←ha]
   | wire w=>
    rw[hga] at ha;simp only[qD] at ha;Y ⟨rfl,?_⟩;simp only[GateOp.eval,List.map_cons,List.headD_cons];rw[ha]
 | and=>
  match ins,j with
  | [],_=>simp[pr,qD,GateOp.eval]
  | [a],_=>
   simp only[pr,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    id_eq,Bool.and_true]
   X d a
  | [a,b],_=>
   simp only[pr];have ha:=d a;have hb:=d b
   cases hga:env.getD a (.const false) with
   | const ca=>
    rw[hga] at ha;simp only[qD] at ha
    cases ca<;>cases hgb:env.getD b (.const false) with
    | const cb=>
     rw[hgb] at hb;simp only[qD] at hb
     cases cb <;>
      (simp only[qD,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
       List.all_nil,id_eq,Bool.and_true];rw[←ha,←hb];rfl)
    | wire wb=>
     rw[hgb] at hb;simp only[qD] at hb
     simp only[qD,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
      List.all_nil,id_eq,Bool.and_true]
     rw[←ha,←hb];simp
   | wire wa=>
    rw[hga] at ha;simp only[qD] at ha
    cases hgb:env.getD b (.const false) with
    | const cb=>
     rw[hgb] at hb;simp only[qD] at hb
     cases cb <;>
      (simp only[qD,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
       List.all_nil,id_eq,Bool.and_true];rw[←ha,←hb];simp)
    | wire wb=>
     rw[hgb] at hb;simp only[qD] at hb;Y ⟨rfl,?_⟩
     simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
      id_eq,Bool.and_true]
     rw[ha,hb]
  | _::_::_::_,h=>simp at h
 | or=>
  match ins,j with
  | [],_=>simp[pr,qD,GateOp.eval]
  | [a],_=>
   simp only[pr,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
    id_eq,Bool.or_false]
   X d a
  | [a,b],_=>
   simp only[pr];have ha:=d a;have hb:=d b
   cases hga:env.getD a (.const false) with
   | const ca=>
    rw[hga] at ha;simp only[qD] at ha
    cases ca<;>cases hgb:env.getD b (.const false) with
    | const cb=>
     rw[hgb] at hb;simp only[qD] at hb
     cases cb <;>
      (simp only[qD,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,
       List.any_nil,id_eq,Bool.or_false];rw[←ha,←hb];rfl)
    | wire wb=>
     rw[hgb] at hb;simp only[qD] at hb
     simp only[qD,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,
      List.any_nil,id_eq,Bool.or_false]
     rw[←ha,←hb];simp
   | wire wa=>
    rw[hga] at ha;simp only[qD] at ha
    cases hgb:env.getD b (.const false) with
    | const cb=>
     rw[hgb] at hb;simp only[qD] at hb
     cases cb <;>
      (simp only[qD,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,
       List.any_nil,id_eq,Bool.or_false];rw[←ha,←hb];simp)
    | wire wb=>
     rw[hgb] at hb;simp only[qD] at hb;Y ⟨rfl,?_⟩
     simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
      id_eq,Bool.or_false]
     rw[ha,hb]
  | _::_::_::_,h=>simp at h
 | mod _=>simp at k
 | maj=>simp at k
private structure je (nNew:ℕ) (initLen:ℕ) (gs:List Gate) (st:z5):Prop where
 env_len:st.fc.length=initLen+st.fb.length
 kept_len:st.fb.length=gs.length
 gates_len:st.gates.length=st.fb.count true
 gates_ok:∀g∈st.gates,Ok g
 env_lt:∀s∈st.fc,zC (nNew+st.gates.length) s
 kept_ops:∀g'∈st.gates,∃(t:ℕ) (ht:t< gs.length),
  st.fb[t]'(by rw[kept_len];X ht)=true/\g'.op=(gs[t]'ht).op
 kept_wire:∀(t:ℕ) (ht:t< gs.length),st.fb[t]'(by rw[kept_len];X ht)=true ->
  ∃(k:ℕ) (hk:k< st.gates.length),
   st.fc[initLen+t]'(by rw[env_len,kept_len];O)=.wire (nNew+k) /\
   (st.gates[k]'hk).op=(gs[t]'ht).op
 kept_inj:∀(t1 t2:ℕ) (h1:t1< gs.length) (h2:t2< gs.length),
  st.fb[t1]'(by rw[kept_len];X h1)=true ->
  st.fb[t2]'(by rw[kept_len];X h2)=true ->
  st.fc[initLen+t1]'(by rw[env_len,kept_len];O) =
   st.fc[initLen+t2]'(by rw[env_len,kept_len];O)->t1=t2
private lemma kk (i initLen:ℕ) (d:ℕ->Option qw)
  (a:List Gate) (g:Gate) (st:z5)
  (hA:Ok g) (hG:∀t s,d t=some s->zC i s)
  (b:je i initLen a st) :
  je i initLen (a++[g]) (pZ i d st g):=by
 have q:st.fb.length=a.length:=b.kept_len;have y:st.fc.length=initLen+a.length:=by rw[b.env_len,q]
 have hB:st.gates.length=st.fb.count true:=b.gates_len
 unfold pZ
 cases hov_t:d st.fb.length with
 | some s=>
  simp only[hov_t]
  have hC:zC (i+st.gates.length) s:=by
   have:=hG _ _ hov_t
   cases s with
   | const _=>trivial
   | wire idx=>simp only[zC] at this ⊢;O
  Y ⟨?_,?_,?_,b.gates_ok,?_,?_,?_,?_⟩
  ·simp[y];O
  ·simp[q]
  ·simp[hB,List.count_append]
  ·intro s' e
   rcases List.mem_append.1 e with e|e
   ·X b.env_lt s' e
   ·rw[List.mem_singleton.1 e];X hC
  ·intro g' hD
   obtain ⟨t,ht,hk,r⟩:=b.kept_ops g' hD;Y ⟨t,by simp;O,?_,?_⟩
   ·rw[List.getElem_append_left W];X hk
   ·rw[List.getElem_append_left ht];X r
  ·intro t ht p
   have c:t< a.length:=by
    by_contra h
    have w:t=a.length:=by simp at ht;O
    subst w;rw[List.getElem_append_right W] at p;simp[q] at p
   rw[List.getElem_append_left W] at p;obtain ⟨k,hk,he,r⟩:=b.kept_wire t c p;Y ⟨k,hk,?_,?_⟩
   ·rw[List.getElem_append_left W];X he
   ·rw[List.getElem_append_left c];X r
  ·intro t1 t2 h1 h2 j l f
   have z:t1< a.length:=by
    by_contra h;have:t1=a.length:=by simp at h1;O
    subst this;rw[List.getElem_append_right W] at j;simp[q] at j
   have hh:t2< a.length:=by
    by_contra h;have:t2=a.length:=by simp at h2;O
    subst this;rw[List.getElem_append_right W] at l;simp[q] at l
   rw[List.getElem_append_left W] at j l;rw[List.getElem_append_left W,List.getElem_append_left W] at f;X b.kept_inj t1 t2 z hh j l f
 | none=>
  simp only[hov_t];have m:=kB st.fc (i+st.gates.length) g hA b.env_lt
  cases hev:pr st.fc (i+st.gates.length) g with
  | mk s mg=>
   rw[hev] at m
   cases mg with
   | none=>
    simp only[hev];simp only at m;Y ⟨?_,?_,?_,b.gates_ok,?_,?_,?_,?_⟩
    ·simp[y];O
    ·simp[q]
    ·simp[hB,List.count_append]
    ·intro s' e
     rcases List.mem_append.1 e with e|e
     ·X b.env_lt s' e
     ·rw[List.mem_singleton.1 e];X m
    ·intro g' hD
     obtain ⟨t,ht,hk,r⟩:=b.kept_ops g' hD;Y ⟨t,by simp;O,?_,?_⟩
     ·rw[List.getElem_append_left W];X hk
     ·rw[List.getElem_append_left ht];X r
    ·intro t ht p
     have c:t< a.length:=by
      by_contra h;have:t=a.length:=by simp at ht;O
      subst this;rw[List.getElem_append_right W] at p;simp[q] at p
     rw[List.getElem_append_left W] at p;obtain ⟨k,hk,he,r⟩:=b.kept_wire t c p;Y ⟨k,hk,?_,?_⟩
     ·rw[List.getElem_append_left W];X he
     ·rw[List.getElem_append_left c];X r
    ·intro t1 t2 h1 h2 j l f
     have z:t1< a.length:=by
      by_contra h;have:t1=a.length:=by simp at h1;O
      subst this;rw[List.getElem_append_right W] at j;simp[q] at j
     have hh:t2< a.length:=by
      by_contra h;have:t2=a.length:=by simp at h2;O
      subst this;rw[List.getElem_append_right W] at l;simp[q] at l
     rw[List.getElem_append_left W] at j l;rw[List.getElem_append_left W,List.getElem_append_left W] at f;X b.kept_inj t1 t2 z hh j l f
   | some g'=>
    simp only[hev];obtain ⟨n,u,x,_⟩:=m;Y ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    ·simp[y];O
    ·simp[q]
    ·simp[hB,List.count_append]
    ·intro g0 v
     rcases List.mem_append.1 v with v|v
     ·X b.gates_ok g0 v
     ·rw[List.mem_singleton.1 v];X x
    ·intro s' e
     rcases List.mem_append.1 e with e|e
     ·have hH:=b.env_lt s' e
      cases s' with
      | const _=>trivial
      | wire idx=>simp only[zC,List.length_append,List.length_singleton] at hH ⊢;O
     ·rw[List.mem_singleton.1 e,n]
      simp[zC]
    ·intro g0 v
     rcases List.mem_append.1 v with v|v
     ·obtain ⟨t,ht,hk,r⟩:=b.kept_ops g0 v
      Y ⟨t,by simp;O,?_,?_⟩
      ·rw[List.getElem_append_left W];X hk
      ·rw[List.getElem_append_left ht];X r
     ·rw[List.mem_singleton.1 v]
      Y ⟨a.length,by simp,?_,?_⟩
      ·rw[List.getElem_append_right W];simp[q]
      ·rw[List.getElem_append_right W];simp[u]
    ·intro t ht p
     by_cases c:t< a.length
     ·rw[List.getElem_append_left W] at p
      obtain ⟨k,hk,he,r⟩:=b.kept_wire t c p;Y ⟨k,by simp;O,?_,?_⟩
      ·rw[List.getElem_append_left W];X he
      ·rw[List.getElem_append_left hk,List.getElem_append_left c];X r
     ·have w:t=a.length:=by simp at ht;O
      subst w;Y ⟨st.gates.length,by simp,?_,?_⟩
      ·rw[List.getElem_append_right W];simp[y,n]
      ·rw[List.getElem_append_right W,List.getElem_append_right W]
       simp[u]
    ·intro t1 t2 h1 h2 j l f
     by_cases z:t1< a.length<;>by_cases hh:t2< a.length
     ·rw[List.getElem_append_left W] at j l
      rw[List.getElem_append_left W,List.getElem_append_left W] at f;X b.kept_inj t1 t2 z hh j l f
     ·exfalso
      have hE:t2=a.length:=by simp at h2;O
      subst hE;rw[List.getElem_append_left W] at j;rw[List.getElem_append_left W,List.getElem_append_right W] at f;simp only[y,Nat.sub_self,List.getElem_singleton,n] at f;obtain ⟨k,hk,hI,_⟩:=b.kept_wire t1 z j;rw[hI] at f;injection f with hidx;O
     ·exfalso
      have hF:t1=a.length:=by simp at h1;O
      subst hF;rw[List.getElem_append_left W] at l;rw[List.getElem_append_right W,List.getElem_append_left W] at f;simp only[y,Nat.sub_self,List.getElem_singleton,n] at f;obtain ⟨k,hk,hJ,_⟩:=b.kept_wire t2 hh l;rw[hJ] at f;injection f with hidx;O
     ·simp at h1 h2;O
private lemma ju (c:ℕ) (a:List qw) (b:ℕ->Option qw)
  (gs:List Gate) (k:∀g∈gs,Ok g)
  (i:∀s∈a,zC c s)
  (l:∀t s,b t=some s->zC c s) :
  je c a.length gs (qF c a b gs):=by
 have j:∀(d rest:List Gate) (st:z5),
   (∀g∈rest,Ok g) ->
   je c a.length d st ->
   je c a.length (d++rest) (rest.foldl (pZ c b) st):=by
  intro d rest
  induction rest generalizing d with
  | nil=>intro st _ h;simpa using h
  | cons g rest ih=>
   intro st f h;have e:d++g::rest=(d++[g])++rest:=by simp
   rw[e,List.foldl_cons]
   X ih (d++[g]) (pZ c b st g)
    (fun g' m=>f g' (List.mem_cons_of_mem _ m))
    (kk c a.length b d g st (f g List.mem_cons_self) l h)
 have h0:je c a.length [] { fc:=a,gates:=[],fb:=[] } :=
  ⟨by simp,rfl,rfl,by simp,by simpa using i,by simp,by simp,by simp⟩
 simpa [qF] using j [] gs _ k h0
private lemma k5 (k:ℕ) (f:List qw) (d:ℕ->Option qw)
  (gs:List Gate) (a wInitNew:List Bool)
  (hR:∀g∈gs,Ok g)
  (z:∀s∈f,zC k s)
  (hh:∀t s,d t=some s->zC k s)
  (q:wInitNew.length=k)
  (r:f.length=a.length)
  (hA:∀i,qD wInitNew (f.getD i (.const false))=a.getD i false)
  (hH:∀t (ht:t< gs.length) s,d t=some s ->
   qD wInitNew s=(pK (gs.take (t+1)) a).getD (a.length+t) false) :
  let st:=qF k f d gs
  ∀i,qD (pK st.gates wInitNew) (st.fc.getD i (.const false)) =
   (pK gs a).getD i false:=by
 have hO:∀(e rest:List Gate) (st:z5),
   (∀g∈rest,Ok g) ->
   je k f.length e st ->
   (∀t (ht:t< rest.length) s,d (e.length+t)=some s ->
    qD wInitNew s =
     (pK ((e++rest).take (e.length+t+1)) a).getD (a.length+(e.length+t)) false) ->
   (∀i,qD (pK st.gates wInitNew) (st.fc.getD i (.const false)) =
    (pK e a).getD i false) ->
   ∀i,qD (pK (rest.foldl (pZ k d) st).gates wInitNew)
    ((rest.foldl (pZ k d) st).fc.getD i (.const false)) =
    (pK (e++rest) a).getD i false:=by
  intro e rest
  induction rest generalizing e with
  | nil=>intro st _ _ _ hm i;simpa using hm i
  | cons g rest ih=>
   intro st hE hB hF hm;have hG:Ok g:=hE g List.mem_cons_self;have hI:∀g'∈rest,Ok g':=fun g' hS=>hE g' (List.mem_cons_of_mem _ hS);have hP:st.fb.length=e.length:=hB.kept_len;have hQ:st.fc.length=f.length+e.length:=by rw[hB.env_len,hP]
   have p:(pK e a).length=st.fc.length:=by
    rw[qm,hQ,r]
   have l:(pK st.gates wInitNew).length=k+st.gates.length:=by
    rw[qm,q]
   have u:e++g::rest=(e++[g])++rest:=by simp
   rw[u,List.foldl_cons];have hK:=kk k f.length d e g st hG hh hB;Y ih (e++[g]) (pZ k d st g) hI hK ?_ ?_
   ·intro t ht s hs
    have y:(e++[g]).length+t=e.length+(t+1):=by simp;O
    have h1:=hF (t+1) (by simp;O) s (by rwa[←y])
    rwa[u,←y] at h1
   ·intro i
    set h:=pK e a with hwOld_def;set wNew:=pK st.gates wInitNew with hwNew_def;have c:h.length=st.fc.length:=p
    have m:pK (e++[g]) a =
      h++[g.op.eval (g.inputs.map fun j=>h.getD j false)]:=by
     rw[ql,qA,zd]
    rw[m]
    unfold pZ
    cases hov_t:d st.fb.length with
    | some s=>
     simp only[hov_t];have w:=hF 0 (by simp) s (by simpa [hP] using hov_t)
     have hJ:(e++g::rest).take (e.length+0+1)=e++[g]:=by
      rw[Nat.add_zero,List.take_append]
      have:e.length+1-e.length=1 :=W
      simp[this]
     rw[hJ,m,List.getD_eq_getElem _ _ (by simp only[List.length_append,List.length_singleton,c,hQ,r];O),
      List.getElem_append_right W] at w
     simp only[show a.length+e.length-h.length=0 by O,
      List.getElem_singleton] at w
     have hC:qD wNew s=qD wInitNew s:=by
      have hL:zC wInitNew.length s:=q▸hh _ _ hov_t
      cases s with
      | const b=>rfl
      | wire idx=>
       simp only[qD,zC] at hL ⊢;X q5 st.gates wInitNew idx hL
     by_cases hi:i< st.fc.length
     ·rw[List.getD_eq_getElem (st.fc++[_]) _ (by simp only[List.length_append,List.length_singleton];O),
       List.getElem_append_left hi,←List.getD_eq_getElem _ _ hi]
      rw[List.getD_eq_getElem (h++[_]) _ (by simp only[List.length_append,List.length_singleton,c];O),
       List.getElem_append_left W,←List.getD_eq_getElem _ _ W]
      X hm i
     ·by_cases v:i=st.fc.length
      ·subst v
       rw[List.getD_eq_getElem (st.fc++[_]) _ (by simp only[List.length_append,List.length_singleton];O),
        List.getElem_append_right (le_refl _)]
       rw[List.getD_eq_getElem (h++[_]) _ (by simp only[List.length_append,List.length_singleton,c];O),
        List.getElem_append_right W]
       simp only[Nat.sub_self,List.getElem_singleton,show st.fc.length-h.length=0 by O]
       rw[hC,w]
      ·rw[List.getD_eq_default (st.fc++[_]) _ (by simp only[List.length_append,List.length_singleton];O),
        List.getD_eq_default (h++[_]) _ (by simp only[List.length_append,List.length_singleton,c];O)]
       R
    | none=>
     have n:=ki st.fc h wNew g hG c.symm hm;rw[l] at n
     cases hev:pr st.fc (k+st.gates.length) g with
     | mk s mg=>
      rw[hev] at n
      cases mg with
      | none=>
       simp only at n;by_cases hi:i< st.fc.length
       ·rw[List.getD_eq_getElem (st.fc++[_]) _ (by simp only[List.length_append,List.length_singleton];O),
         List.getElem_append_left hi,←List.getD_eq_getElem _ _ hi]
        rw[List.getD_eq_getElem (h++[_]) _ (by simp only[List.length_append,List.length_singleton,c];O),
         List.getElem_append_left W,←List.getD_eq_getElem _ _ W]
        X hm i
       ·by_cases v:i=st.fc.length
        ·subst v
         rw[List.getD_eq_getElem (st.fc++[_]) _ (by simp only[List.length_append,List.length_singleton];O),
          List.getElem_append_right (le_refl _)]
         rw[List.getD_eq_getElem (h++[_]) _ (by simp only[List.length_append,List.length_singleton,c];O),
          List.getElem_append_right W]
         simp only[Nat.sub_self,List.getElem_singleton,show st.fc.length-h.length=0 by O]
         X n
        ·rw[List.getD_eq_default (st.fc++[_]) _ (by simp only[List.length_append,List.length_singleton];O),
          List.getD_eq_default (h++[_]) _ (by simp only[List.length_append,List.length_singleton,c];O)]
         R
      | some g'=>
       obtain ⟨hM,hD⟩:=n
       have x:pK (st.gates++[g']) wInitNew =
         wNew++[g'.op.eval (g'.inputs.map fun j=>wNew.getD j false)]:=by
        rw[ql,qA,zd]
       rw[x];by_cases hi:i< st.fc.length
       ·rw[List.getD_eq_getElem (st.fc++[_]) _ (by simp only[List.length_append,List.length_singleton];O),
         List.getElem_append_left hi,←List.getD_eq_getElem _ _ hi]
        rw[List.getD_eq_getElem (h++[_]) _ (by simp only[List.length_append,List.length_singleton,c];O),
         List.getElem_append_left W,←List.getD_eq_getElem _ _ W]
        have hN:zC wNew.length (st.fc.getD i (.const false)):=by
         rw[List.getD_eq_getElem _ _ hi,l];X hB.env_lt _ (List.getElem_mem hi)
        rw[jX _ _ _ hN];X hm i
       ·by_cases v:i=st.fc.length
        ·subst v
         rw[List.getD_eq_getElem (st.fc++[_]) _ (by simp only[List.length_append,List.length_singleton];O),
          List.getElem_append_right (le_refl _)]
         rw[List.getD_eq_getElem (h++[_]) _ (by simp only[List.length_append,List.length_singleton,c];O),
          List.getElem_append_right W]
         simp only[Nat.sub_self,List.getElem_singleton,hM,qD,
          show st.fc.length-h.length=0 by O]
         rw[List.getD_eq_getElem _ _ (by simp only[List.length_append,List.length_singleton,l];O),
          List.getElem_append_right W]
         simp only[show k+st.gates.length-wNew.length=0 by O,List.getElem_singleton]
         X hD
        ·rw[List.getD_eq_default _ _ (by simp only[List.length_append,List.length_singleton];O),
          List.getD_eq_default _ _ (by simp only[List.length_append,List.length_singleton,p];O)]
         R
 have h0:je k f.length [] { fc:=f,gates:=[],fb:=[] } :=
  ⟨by simp,rfl,rfl,by simp,by simpa using z,by simp,by simp,by simp⟩
 simpa [qF] using hO [] gs _ hR h0 (by simpa using hH) (by simpa [pK] using hA)
private lemma zJ (b:ℕ) (a:ℕ->Option qw) (st:z5) (g:Gate) :
  (∀i,i< st.fc.length->(pZ b a st g).fc[i]?=st.fc[i]?) /\
  (∀i,i< st.fb.length->(pZ b a st g).fb[i]?=st.fb[i]?) /\
  (pZ b a st g).fc.length=st.fc.length+1 /\
  (pZ b a st g).fb.length=st.fb.length+1:=by
 unfold pZ
 cases h1:a st.fb.length with
 | some s=>
  simp only[h1]
  X ⟨fun i hi=>by simp[List.getElem?_append_left hi],
   fun i hi=>by simp[List.getElem?_append_left hi],by simp,by simp⟩
 | none=>
  simp only[h1]
  cases h2:pr st.fc (b+st.gates.length) g with
  | mk s mg=>
   cases mg<;>simp only[h2] <;>
   X ⟨fun i hi=>by simp[List.getElem?_append_left hi],
    fun i hi=>by simp[List.getElem?_append_left hi],by simp,by simp⟩
private lemma jj (b:ℕ) (a:ℕ->Option qw) (gs:List Gate) (st:z5) :
  (∀i,i< st.fc.length->(gs.foldl (pZ b a) st).fc[i]?=st.fc[i]?) /\
  (∀i,i< st.fb.length->(gs.foldl (pZ b a) st).fb[i]?=st.fb[i]?):=by
 induction gs generalizing st with
 | nil=>X ⟨fun _ _=>rfl,fun _ _=>rfl⟩
 | cons g gs ih=>
  have h1:=zJ b a st g;have h2:=ih (pZ b a st g);Y ⟨fun i hi=>?_,fun i hi=>?_⟩
  ·rw[List.foldl_cons,h2.1 i W,h1.1 i hi]
  ·rw[List.foldl_cons,h2.2 i W,h1.2.1 i hi]
private lemma zK (c:ℕ) (b:List qw) (a:ℕ->Option qw)
  (gs:List Gate) (t:ℕ) (ht:t< gs.length) :
  let st:=qF c b a gs;let stPre:=qF c b a (gs.take t)
  (∀i,i< b.length+t->st.fc.getD i (.const false)=stPre.fc.getD i (.const false)) /\
  st.fc[b.length+t]?=(pZ c a stPre (gs[t]'ht)).fc[b.length+t]? /\
  st.fb[t]?=(pZ c a stPre (gs[t]'ht)).fb[t]?:=by
 have k:gs=gs.take t++(gs[t]'ht)::gs.drop (t+1):=by
  have h1:=List.take_append_drop t gs;have h2:gs.drop t=(gs[t]'ht)::gs.drop (t+1):=List.drop_eq_getElem_cons ht;rw[←h2,h1]
 have e:∀(l:List Gate) (st0:z5),
   (l.foldl (pZ c a) st0).fc.length=st0.fc.length+l.length /\
   (l.foldl (pZ c a) st0).fb.length=st0.fb.length+l.length:=by
  intro l
  induction l with
  | nil=>intro st0;simp
  | cons g l ih=>
   intro st0;rw[List.foldl_cons];have h1:=ih (pZ c a st0 g);have h2:=zJ c a st0 g;simp only[List.length_cons];X ⟨by O,by O⟩
 set stPre:=qF c b a (gs.take t);have d:(gs.take t).length=t:=by rw[List.length_take];O
 have j:stPre.fc.length=b.length+t:=by
  have:=(e (gs.take t) { fc:=b,gates:=[],fb:=[] }).1
  simpa [stPre,qF,d] using this
 have h:stPre.fb.length=t:=by
  have:=(e (gs.take t) { fc:=b,gates:=[],fb:=[] }).2
  simpa [stPre,qF,d] using this
 have f:qF c b a gs =
   (gs.drop (t+1)).foldl (pZ c a) (pZ c a stPre (gs[t]'ht)):=by
  unfold qF
  conv_lhs=>rw[k]
  rw[List.foldl_append,List.foldl_cons];R
 have h1:=zJ c a stPre (gs[t]'ht);have h2:=jj c a (gs.drop (t+1)) (pZ c a stPre (gs[t]'ht));Y ⟨?_,?_,?_⟩
 ·intro i hi
  have m:(qF c b a gs).fc[i]?=stPre.fc[i]?:=by
   rw[f,h2.1 i W,h1.1 i W]
  simp only[List.getD_eq_getElem?_getD,m]
 ·rw[f,h2.1 (b.length+t) W]
 ·rw[f,h2.2 t W]
private lemma zO (b:ℕ) (a:List qw) (gs:List Gate)
  (t:ℕ) (ht:t< gs.length) :
  let st:=qF b a (fun _=>none) gs;let stPre:=qF b a (fun _=>none) (gs.take t);let p:=pr stPre.fc (b+stPre.gates.length) (gs[t]'ht)
  st.fc.getD (a.length+t) (.const false)=p.1 /\
  st.fb.getD t false=p.2.isSome:=by
 have e:=zK b a (fun _=>none) gs t ht
 have d:∀(l:List Gate) (st0:z5),
   (l.foldl (pZ b (fun _=>none)) st0).fc.length=st0.fc.length+l.length /\
   (l.foldl (pZ b (fun _=>none)) st0).fb.length=st0.fb.length+l.length:=by
  intro l
  induction l with
  | nil=>intro st0;simp
  | cons g l ih=>
   intro st0;rw[List.foldl_cons];have h1:=ih (pZ b (fun _=>none) st0 g);have h2:=zJ b (fun _=>none) st0 g;simp only[List.length_cons];X ⟨by O,by O⟩
 set stPre:=qF b a (fun _=>none) (gs.take t);have c:(gs.take t).length=t:=by rw[List.length_take];O
 have f:stPre.fc.length=a.length+t:=by
  have:=(d (gs.take t) { fc:=a,gates:=[],fb:=[] }).1
  simpa [stPre,qF,c] using this
 have h:stPre.fb.length=t:=by
  have:=(d (gs.take t) { fc:=a,gates:=[],fb:=[] }).2
  simpa [stPre,qF,c] using this
 simp only[List.getD_eq_getElem?_getD,e.2.1,e.2.2]
 unfold pZ
 cases hev:pr stPre.fc (b+stPre.gates.length) (gs[t]'ht) with
 | mk s mg=>
  cases mg<;>simp[hev,f,h]
private lemma qk (l:List Bool) :
  l.count false+l.count true=l.length:=by
 induction l with
 | nil=>simp
 | cons b l ih=>cases b<;>simp[List.count_cons]<;>O
private lemma j4 {l:List Bool} {i:ℕ} (hi:i< l.length) (h:l[i]=false) :
  1<=l.count false:=by
 have a:false∈l:=h▸List.getElem_mem hi;X List.count_pos_iff.2 a
private lemma za {l:List Bool} {i j:ℕ} (hi:i< l.length) (hj:j< l.length)
  (c:i≠j) (h1:l[i]=false) (h2:l[j]=false) :
  2<=l.count false:=by
 have a:∀(l:List Bool) (i j:ℕ) (c:i< j) (hj:j< l.length),
   l[i]'W=false->l[j]'hj=false->2<=l.count false:=by
  intro l
  induction l with
  | nil=>intro _ _ _ hj;simp at hj
  | cons b l ih=>
   intro i j c hj h1 h2
   cases i with
   | zero=>
    cases j with
    | zero=>O
    | succ j=>
     simp only[List.getElem_cons_zero] at h1;simp only[List.getElem_cons_succ] at h2;subst h1
     have:=j4 (show j< l.length by simp at hj;O) h2
     simp only[List.count_cons,beq_self_eq_true,↓reduceIte];O
   | succ i=>
    cases j with
    | zero=>O
    | succ j=>
     simp only[List.getElem_cons_succ] at h1 h2
     have:=ih i j W (by simp at hj;O) h1 h2
     cases b with
     | false=>simp only[List.count_cons,beq_self_eq_true,↓reduceIte];O
     | true=>simp only[List.count_cons,Bool.true_beq,Bool.not_false,↓reduceIte];O
 rcases Nat.lt_or_gt_of_ne c with hlt|hgt
 ·X a l i j hlt hj h1 h2
 ·X a l j i hgt hi h2 h1
private lemma zR {l:List Bool} {i j k:ℕ}
  (hi:i< l.length) (hj:j< l.length) (hk:k< l.length)
  (d:i≠j) (e:i≠k) (c:j≠k)
  (h1:l[i]=false) (h2:l[j]=false) (h3:l[k]=false) :
  3<=l.count false:=by
 have a:∀(l:List Bool) (i j k:ℕ) (d:i< j) (c:j< k) (hk:k< l.length),
   l[i]'W=false->l[j]'W=false->l[k]'hk=false->3<=l.count false:=by
  intro l
  induction l with
  | nil=>intro _ _ _ _ _ hk;simp at hk
  | cons b l ih=>
   intro i j k d c hk h1 h2 h3
   cases i with
   | zero=>
    cases j with
    | zero=>O
    | succ j=>
     cases k with
     | zero=>O
     | succ k=>
      simp only[List.getElem_cons_zero] at h1;simp only[List.getElem_cons_succ] at h2 h3;subst h1
      have:=za (show j< l.length by simp at hk;O)
       (show k< l.length by simp at hk;O) W h2 h3
      simp[List.count_cons];O
   | succ i=>
    cases j with
    | zero=>O
    | succ j=>
     cases k with
     | zero=>O
     | succ k=>
      simp only[List.getElem_cons_succ] at h1 h2 h3
      have:=ih i j k W W (by simp at hk;O) h1 h2 h3
      cases b<;>simp[List.count_cons]<;>O
 rcases Nat.lt_or_gt_of_ne d with hlt1|hgt1
 ·rcases Nat.lt_or_gt_of_ne c with hlt2|hgt2
  ·X a l i j k hlt1 hlt2 hk h1 h2 h3
  ·rcases Nat.lt_or_gt_of_ne e with hlt3|hgt3
   ·X a l i k j hlt3 hgt2 hj h1 h3 h2
   ·X a l k i j hgt3 hlt1 hj h3 h1 h2
 ·rcases Nat.lt_or_gt_of_ne e with hlt2|hgt2
  ·X a l j i k hgt1 hlt2 hk h2 h1 h3
  ·rcases Nat.lt_or_gt_of_ne c with hlt3|hgt3
   ·X a l j k i hlt3 hgt2 hi h2 h3 h1
   ·X a l k j i hgt3 hgt1 hi h3 h2 h1
private lemma z4 {n:ℕ} {C:J} (b:IsMinimalCircuit n C)
  (t0:ℕ) (d:t0< C.size) :
  ∃x:V n,p8 C t0 x=true:=by
 by_contra h
 push Not at h;have a:∀x,p0 C x (n+t0)=false:=fun x=>Bool.eq_false_iff.2 (h x);set D:=qQ C n t0 (n+C.size);have e:FanInTwo D:=qS C b.1 n t0 (n+C.size)
 have c:cF n D=cF n C:=by
  funext x
  rw[z7 C x t0 (n+C.size) d (ir le_rfl),if_neg W];X pV C x t0 d false (a x).symm C.output
 have f:=b.2 D e c;rw[zn C n t0 (n+C.size) d] at f;O
private lemma py {n:ℕ} {C:J} (a:IsMinimalCircuit n C)
  (t0:ℕ) (c:t0< C.size) (w:ℕ) (hw:w< n+t0) :
  ∃x:V n,p8 C t0 x≠p0 C x w:=by
 by_contra h
 push Not at h;set D:=qQ C n t0 w;have d:FanInTwo D:=qS C a.1 n t0 w
 have b:cF n D=cF n C:=by
  funext x
  rw[z7 C x t0 w c (il hw),if_pos hw];X pV C x t0 c (p0 C x w) (h x).symm C.output
 have e:=a.2 D d b;rw[zn C n t0 w c] at e;O
private lemma zU {n:ℕ} {C:J} (m:IsMinimalCircuit n C)
  (hD:∃x y:V n,cF n C x≠cF n C y)
  (t0:ℕ) (u:t0< C.size) :
  ∃x:V n,p8 C t0 x=false:=by
 by_contra h
 push Not at h;have hE:C.size=C.gates.length:=rfl
 have z:∀x,p0 C x (n+t0)=true:=fun x=>by
  cases hb:p0 C x (n+t0) with
  | false=>X absurd hb (h x)
  | true=>rfl
 set a:List qw:=(List.range n).map qw.wire;set ov:ℕ->Option qw:=fun t=>if t=t0 then some (.const true) else none;set st:=qF n a ov C.gates;have v:a.length=n:=by simp[a]
 have d:∀s∈a,zC n s:=by
  intro s hs;simp only[a,List.mem_map,List.mem_range] at hs;obtain ⟨i,hi,rfl⟩:=hs;X hi
 have e:∀t s,ov t=some s->zC n s:=by
  intro t s hs;simp only[ov] at hs;split_ifs at hs with h;injection hs with hs;subst hs;trivial
 have f:=ju n a ov C.gates m.1 d e
 have j:∀x:V n,∀i,
   qD (pK st.gates (List.ofFn x)) (st.fc.getD i (.const false))=p0 C x i:=by
  intro x
  Y k5 n a ov C.gates (List.ofFn x) (List.ofFn x) m.1 d e
   (by simp) (by simp[a]) ?_ ?_
  ·intro i
   by_cases hi:i< n
   ·rw[List.getD_eq_getElem _ _ (by simp[a,hi])]
    simp[a,qD]
   ·rw[List.getD_eq_default _ _ (by simp[a];O),
     List.getD_eq_default _ _ (by simp;O)]
    R
  ·intro t ht s hs
   simp only[ov] at hs
   split_ifs at hs with hteq
   ·injection hs with hs;subst hs;rw[hteq]
    have q:C.gates=C.gates.take (t0+1)++C.gates.drop (t0+1) :=
     (List.take_append_drop (t0+1) C.gates).symm
    have p:=z x
    unfold p0 at p
    rw[qu,q,ql] at p;rw[q5 _ _ (n+t0) (by rw[qm,List.length_ofFn,List.length_take];O)] at p
    simpa [qD] using p.symm
 cases hout:st.fc.getD C.output (.const false) with
 | const b=>
  obtain ⟨x,y,hF⟩:=hD;have hx:=j x C.output;have hy:=j y C.output;rw[hout] at hx hy;X hF (by rw[pb,pb,←hx,←hy];rfl)
 | wire w=>
  set D:J:={ gates:=st.gates,output:=w };have hB:FanInTwo D:=f.gates_ok
  have hh:cF n D=cF n C:=by
   funext x
   have hx:=j x C.output;rw[hout] at hx;simpa [D,pb,p0,qu,qD] using hx
  have hA:st.fb[t0]'(by rw[f.kept_len];X u)=false:=by
   have hG:=zK n a ov C.gates t0 u;have c:=hG.2.2;rw[List.getElem?_eq_getElem (by rw[f.kept_len];X u)] at c
   have l:=ju n a ov (C.gates.take t0)
    (fun g hg=>m.1 g (List.mem_of_mem_take hg)) d e
   have hC:(qF n a ov (C.gates.take t0)).fb.length=t0:=by
    rw[l.kept_len,List.length_take];O
   set stPre:=qF n a ov (C.gates.take t0) with hstPre_def;have r:ov stPre.fb.length=some (.const true):=by simp[ov,hC]
   have k:(pZ n ov stPre (C.gates[t0]'u)).fb=stPre.fb++[false]:=by
    unfold pZ;simp only[r]
   change some (st.fb[t0]'(by rw[f.kept_len];X u))=_ at c
   rw[k,List.getElem?_append_right W] at c;simp only[hC,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at c;X c
  have hI:=j4 (by rw[f.kept_len];X u) hA
  have hH:=qk st.fb
  have hJ:D.size< C.size:=by
   have h1:st.fb.length=C.gates.length:=f.kept_len;have h2:st.gates.length=st.fb.count true:=f.gates_len;change st.gates.length< C.gates.length;O
  have hK:=m.2 D hB hh;O
private lemma zy (g:Gate) (hg:Ok g) (f1 f2:ℕ->Bool)
  (h:∀a∈pa g,f1 a=f2 a) :
  g.op.eval (g.inputs.map f1)=g.op.eval (g.inputs.map f2):=by
 obtain ⟨op,ins⟩:=g;obtain ⟨b,c⟩:=hg
 cases op with
 | not=>
  cases ins with
  | nil=>rfl
  | cons a rest=>
   simp only[GateOp.eval,List.map_cons,List.headD_cons];rw[h a (by simp[pa])]
 | and=>
  congr 1
  X List.map_congr_left fun a ha=>h a ha
 | or=>
  congr 1
  X List.map_congr_left fun a ha=>h a ha
 | mod _=>simp at b
 | maj=>simp at b
private lemma pY {n:ℕ} {C:J} (c:IsMinimalCircuit n C)
  (t0:ℕ) (i:t0< C.size) :
  C.output=n+t0\/∃t':ℕ,∃(p:t'< C.size),t0< t' /\
   pC n t' (n+t0) (C.gates[t']'p):=by
 by_contra h
 push Not at h;obtain ⟨l,q⟩:=h;set D:=qQ C n t0 (n+C.size);have m:FanInTwo D:=qS C c.1 n t0 (n+C.size)
 have d:∀(x:V n) (k:ℕ),k≠n+t0 ->
   pl C x t0 false k=p0 C x k:=by
  intro x k
  induction k using Nat.strong_induction_on with
  | ind k ih=>
   intro s;by_cases h1:k< n+t0
   ·X pA C x t0 i false k h1
   ·by_cases h2:k< n+C.size
    ·set t:=k-n
     have ht:t0< t :=W;have j:t< C.size :=W;have hk:k=n+t :=W;rw[hk,z9 C x t0 i false t ht j,pj C x t j];apply zy _ (c.1 _ (List.getElem_mem j));intro a ha;by_cases b:a< n+t
     ·have e:a≠n+t0:=by
       intro f;subst f;X q t j ht ⟨ha,b⟩
      rw[if_pos b,if_pos b];X ih a W e
     ·rw[if_neg b,if_neg b]
    ·rw[jd C x t0 false k W,z3 C x k W]
 have g:cF n D=cF n C:=by
  funext x
  rw[z7 C x t0 (n+C.size) i (ir le_rfl),if_neg W];X d x C.output l
 have r:=c.2 D m g;rw[zn C n t0 (n+C.size) i] at r;O
private lemma pc {n:ℕ} {C:J} (d:IsMinimalCircuit n C)
  (h:∃x y:V n,cF n C x≠cF n C y)
  (t:ℕ) (ht:t< C.size) :
  let g:=C.gates[t]'ht
  (g.op=.not/\∃a,g.inputs.head?=some a/\a< n+t) \/
  ((g.op=.and\/g.op=.or)/\∃a b,g.inputs=[a,b]/\a< n+t/\b< n+t/\a≠b):=by
 have f:=d.1 _ (List.getElem_mem ht);obtain ⟨k,e⟩:=f;set g:=C.gates[t]'ht with hg_def;simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at k;rcases k with c|c|c
 ·
  right;Y ⟨il c,?_⟩
  cases hins:g.inputs with
  | nil=>
   exfalso;obtain ⟨x,hx⟩:=zU d h t ht;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8] at hv hx;rw[hv] at hx;cases hx
  | cons a rest=>
   cases rest with
   | nil=>
    exfalso;by_cases ha:a< n+t
    ·obtain ⟨x,hx⟩:=py d t ht a ha
     have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,ha] at hv hx;X hx hv
    ·obtain ⟨x,hx⟩:=z4 d t ht
     have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,ha] at hv hx;rw[hv] at hx;cases hx
   | cons b rest2=>
    cases rest2 with
    | nil=>
     have ha:a< n+t:=by
      by_contra hna
      obtain ⟨x,hx⟩:=z4 d t ht;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,hna] at hv hx;rw[hv] at hx;cases hx
     have hb:b< n+t:=by
      by_contra hnb
      obtain ⟨x,hx⟩:=z4 d t ht;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,hnb] at hv hx;rw[hv] at hx;cases hx
     have i:a≠b:=by
      intro j;subst j;obtain ⟨x,hx⟩:=py d t ht a ha;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,ha] at hv hx;X hx hv
     X ⟨a,b,rfl,ha,hb,i⟩
    | cons _ _=>
     rw[hins] at e;simp at e
 ·
  right;Y ⟨ir c,?_⟩
  cases hins:g.inputs with
  | nil=>
   exfalso;obtain ⟨x,hx⟩:=z4 d t ht;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8] at hv hx;rw[hv] at hx;cases hx
  | cons a rest=>
   cases rest with
   | nil=>
    exfalso;by_cases ha:a< n+t
    ·obtain ⟨x,hx⟩:=py d t ht a ha
     have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,ha] at hv hx;X hx hv
    ·obtain ⟨x,hx⟩:=z4 d t ht
     have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,ha] at hv hx;rw[hv] at hx;cases hx
   | cons b rest2=>
    cases rest2 with
    | nil=>
     have ha:a< n+t:=by
      by_contra hna
      by_cases hb:b< n+t
      ·obtain ⟨x,hx⟩:=py d t ht b hb
       have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,hna,hb] at hv hx;X hx hv
      ·obtain ⟨x,hx⟩:=z4 d t ht
       have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,hna,hb] at hv hx;rw[hv] at hx;cases hx
     have hb:b< n+t:=by
      by_contra hnb
      obtain ⟨x,hx⟩:=py d t ht a ha;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,ha,hnb] at hv hx;X hx hv
     have i:a≠b:=by
      intro j;subst j;obtain ⟨x,hx⟩:=py d t ht a ha;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,ha] at hv hx;X hx hv
     X ⟨a,b,rfl,ha,hb,i⟩
    | cons _ _=>
     rw[hins] at e;simp at e
 ·
  left;Y ⟨c,?_⟩
  cases hins:g.inputs with
  | nil=>
   exfalso;obtain ⟨x,hx⟩:=zU d h t ht;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8] at hv hx;rw[hv] at hx;cases hx
  | cons a rest=>
   have ha:a< n+t:=by
    by_contra hna
    obtain ⟨x,hx⟩:=zU d h t ht;have hv:=pj C x t ht;rw[←hg_def,c,hins] at hv;simp[GateOp.eval,p8,hna] at hv hx;rw[hv] at hx;cases hx
   X ⟨a,rfl,ha⟩
private lemma qG {n:ℕ} {C:J} (b:IsMinimalCircuit n C)
  (h:z0 C) (t0:ℕ) (c:t0< C.size) (w:ℕ) (hw:w< n+t0)
  (h1:∀x:V n,p8 C t0 x=true->p0 C x w=true)
  (h2:∀x:V n,p0 C x w=true->cF n C x=true) :
  False:=by
 set D:=qQ C n t0 w;have f:FanInTwo D:=qS C b.1 n t0 w
 have d:cF n D=cF n C:=by
  funext x
  rw[z7 C x t0 w c (il hw),if_pos hw]
  cases hf:cF n C x with
  | false=>
   have g:p0 C x w=false:=by
    cases hwx:p0 C x w with
    | false=>rfl
    | true=>have:=h2 x hwx;rw[hf] at this;cases this
   have e:p0 C x (n+t0)=false:=by
    cases htx:p8 C t0 x with
    | false=>X htx
    | true=>have:=h1 x htx;rw[g] at this;cases this
   rw[g,pV C x t0 c false e.symm C.output];X hf
  | true=>
   have a:=jo C b.1 h x t0 c (h1 x) C.output
   unfold p8 at a
   rw[pV C x t0 c (p0 C x (n+t0)) rfl C.output] at a;X a hf
 have i:=b.2 D f d;rw[zn C n t0 w c] at i;O
private def pn (n:ℕ) (b:Bool):List qw :=
 (List.range n).map qw.wire++[.const b]
private def p5 (C:J) (n:ℕ) (b:Bool):z5 :=
 qF n (pn n b) (fun _=>none) C.gates
private def p3 (C:J) (n:ℕ) (b:Bool):J :=
 kE n (p5 C n b) C.output
private lemma pk (C:J) (n:ℕ) (b:Bool) (c:FanInTwo C) :
  je n (n+1) C.gates (p5 C n b):=by
 have a:(pn n b).length=n+1:=by simp[pn]
 have d:∀s∈pn n b,zC n s:=by
  intro s hs
  simp only[pn,List.mem_append,List.mem_map,List.mem_range,
   List.mem_singleton] at hs
  rcases hs with ⟨i,hi,rfl⟩|rfl
  ·X hi
  ·trivial
 have h:=ju n (pn n b) (fun _=>none) C.gates c d (by simp)
 simpa [p5,a] using h
private lemma pH (C:J) (n:ℕ) (b:Bool) (f:FanInTwo C)
  (y:V n) (i:ℕ) :
  qD (pK (p5 C n b).gates (List.ofFn y))
   ((p5 C n b).fc.getD i (.const false)) =
  p0 C (Fin.snoc y b) i:=by
 have g:∀s∈pn n b,zC n s:=by
  intro s hs
  simp only[pn,List.mem_append,List.mem_map,List.mem_range,
   List.mem_singleton] at hs
  rcases hs with ⟨i,hi,rfl⟩|rfl
  ·X hi
  ·trivial
 have a:List.ofFn (Fin.snoc y b)=List.ofFn y++[b]:=by
  apply List.ext_getElem
  ·simp
  ·intro k h1 h2
   by_cases hk:k< n
   ·rw[List.getElem_ofFn,List.getElem_append_left (by simp[hk]),List.getElem_ofFn]
    have:(⟨k,by O⟩:Fin (n+1))=Fin.castSucc ⟨k,hk⟩:=Fin.ext rfl
    rw[this,Fin.snoc_castSucc]
   ·have d:k=n:=by simp at h1;O
    subst d;rw[List.getElem_ofFn,List.getElem_append_right (by simp)]
    have c:(⟨k,by O⟩:Fin (k+1))=Fin.last k:=Fin.ext rfl
    rw[c,Fin.snoc_last];simp
 have h:=k5 n (pn n b) (fun _=>none) C.gates
  (List.ofFn (Fin.snoc y b)) (List.ofFn y) f g (by simp) (by simp)
  (by simp[pn]) ?_ (by simp) i
 ·X h
 ·intro j
  rw[a];by_cases hj:j< n
  ·rw[List.getD_eq_getElem _ _ (by simp[pn];O)]
   simp only[pn,List.getElem_append_left (by simp[hj]:j< ((List.range n).map qw.wire).length),
    List.getElem_map,List.getElem_range,qD]
   conv_rhs=>rw[List.getD_eq_getElem _ _ (by simp;O),List.getElem_append_left (by simp[hj])]
   rw[List.getD_eq_getElem _ _ (by simp[hj])]
  ·by_cases e:j=n
   ·subst e
    rw[List.getD_eq_getElem _ _ (by simp[pn])]
    simp only[pn,List.getElem_append_right (by simp:((List.range j).map qw.wire).length<=j),
     List.length_map,List.length_range,Nat.sub_self,List.getElem_singleton,qD]
    rw[List.getD_eq_getElem _ _ (by simp),List.getElem_append_right (by simp)]
    simp
   ·rw[List.getD_eq_default _ _ (by simp[pn];O),
     List.getD_eq_default _ _ (by simp;O)]
    R
private lemma qi (C:J) (n:ℕ) (b:Bool) (a:FanInTwo C) :
  FanInTwo (p3 C n b) :=
 (pk C n b a).gates_ok
private lemma q6 (C:J) (n:ℕ) (b:Bool) (a:FanInTwo C)
  (d:∃y1 y2:V n,
   cF (n+1) C (Fin.snoc y1 b)≠cF (n+1) C (Fin.snoc y2 b)) :
  ∀y:V n,
   cF n (p3 C n b) y=cF (n+1) C (Fin.snoc y b):=by
 set st:=p5 C n b
 cases hout:st.fc.getD C.output (.const false) with
 | const c=>
  exfalso;obtain ⟨y1,y2,e⟩:=d;have h1:=pH C n b a y1 C.output;have h2:=pH C n b a y2 C.output;rw[hout] at h1 h2;X e (by rw[pb,pb,←h1,←h2];rfl)
 | wire w=>
  intro y;have h:=pH C n b a y C.output;rw[hout] at h
  change (pK st.gates (List.ofFn y)).getD
   (match st.fc.getD C.output (.const false) with|.wire w=>w|.const _=>n+st.gates.length) false =
   p0 C (Fin.snoc y b) C.output
  rw[hout];X h
private lemma pL {C:J} {n:ℕ} {b:Bool}
  (a:FanInTwo C)
  (d:∃y1 y2:V n,
   cF (n+1) C (Fin.snoc y1 b)≠cF (n+1) C (Fin.snoc y2 b))
  {i:ℕ} {c:Bool} (hc:(p5 C n b).fc.getD i (.const false)=.const c) :
  C.output≠i:=by
 intro e;subst e;obtain ⟨y1,y2,f⟩:=d;have h1:=pH C n b a y1 C.output;have h2:=pH C n b a y2 C.output;rw[hc] at h1 h2;X f (by rw[pb,pb,←h1,←h2];rfl)
private lemma pw {C:J} {n:ℕ} {b:Bool}
  (m:FanInTwo C) {t:ℕ} (ht:t< C.size) {w:ℕ} {c:Bool}
  (hr:pC (n+1) t w (C.gates[t]'ht))
  (hc:(p5 C n b).fc.getD w (.const false)=.const c) :
  (p5 C n b).fb.getD t false=false:=by
 have h:(pn n b).length=n+1:=by simp[pn]
 have j:=zK n (pn n b) (fun _=>none) C.gates t ht;have k:=zO n (pn n b) C.gates t ht;rw[h] at j k
 have d:(qF n (pn n b) (fun _=>none) (C.gates.take t)).fc.getD w (.const false)=.const c:=by
  rw[←j.1 w hr.2];X hc
 rw[show p5 C n b=qF n (pn n b) (fun _=>none) C.gates from rfl];rw[k.2];obtain ⟨e,_⟩:=hr;have l:=m _ (List.getElem_mem ht);obtain ⟨f,i⟩:=l;set g:=C.gates[t]'ht;set envPre:=(qF n (pn n b) (fun _=>none) (C.gates.take t)).fc
 cases hop:g.op with
 | not=>
  cases hins:g.inputs with
  | nil=>simp only[pr,hop,hins,Option.isSome_none]
  | cons a rest=>
   simp only[pa,hop,hins,List.mem_singleton] at e;subst e;simp only[pr,hop,hins,d,Option.isSome_none]
 | and=>
  cases hins:g.inputs with
  | nil=>simp only[pr,hop,hins,Option.isSome_none]
  | cons a rest=>
   cases rest with
   | nil=>simp only[pr,hop,hins,Option.isSome_none]
   | cons b2 rest2=>
    cases rest2 with
    | nil=>
     simp only[pa,hop,hins,List.mem_cons,List.not_mem_nil,or_false] at e;rcases e with rfl|rfl
     ·cases c<;>cases hgb:envPre.getD b2 (.const false) with
      | const cb=>cases cb<;>simp only[pr,hop,hins,d,hgb,Option.isSome_none]
      | wire _=>simp only[pr,hop,hins,d,hgb,Option.isSome_none]
     ·cases c<;>cases hga:envPre.getD a (.const false) with
      | const ca=>cases ca<;>simp only[pr,hop,hins,d,hga,Option.isSome_none]
      | wire _=>simp only[pr,hop,hins,d,hga,Option.isSome_none]
    | cons _ _=>rw[hins] at i;simp at i
 | or=>
  cases hins:g.inputs with
  | nil=>simp only[pr,hop,hins,Option.isSome_none]
  | cons a rest=>
   cases rest with
   | nil=>simp only[pr,hop,hins,Option.isSome_none]
   | cons b2 rest2=>
    cases rest2 with
    | nil=>
     simp only[pa,hop,hins,List.mem_cons,List.not_mem_nil,or_false] at e;rcases e with rfl|rfl
     ·cases c<;>cases hgb:envPre.getD b2 (.const false) with
      | const cb=>cases cb<;>simp only[pr,hop,hins,d,hgb,Option.isSome_none]
      | wire _=>simp only[pr,hop,hins,d,hgb,Option.isSome_none]
     ·cases c<;>cases hga:envPre.getD a (.const false) with
      | const ca=>cases ca<;>simp only[pr,hop,hins,d,hga,Option.isSome_none]
      | wire _=>simp only[pr,hop,hins,d,hga,Option.isSome_none]
    | cons _ _=>rw[hins] at i;simp at i
 | mod _=>rw[hop] at f;simp at f
 | maj=>rw[hop] at f;simp at f
private lemma p9 (C:J) (n:ℕ) (b:Bool) (e:FanInTwo C) :
  (p5 C n b).fc.getD n (.const false)=.const b:=by
 have h1:=jj n (fun _=>none) C.gates { fc:=pn n b,gates:=[],fb:=[] };have d:n< (pn n b).length:=by simp[pn]
 have c:=h1.1 n d
 have a:(pn n b)[n]?=some (.const b):=by
  rw[List.getElem?_eq_getElem d];simp[pn]
 rw[List.getD_eq_getElem?_getD];change ((C.gates.foldl (pZ n (fun _=>none)) { fc:=pn n b,gates:=[],fb:=[] }).fc[n]?).getD (.const false)=.const b;rw[c,a];R
private lemma pd (C:J) (n:ℕ) (b:Bool) (i:ℕ) (hi:i< n) :
  (p5 C n b).fc.getD i (.const false)=.wire i:=by
 have h1:=jj n (fun _=>none) C.gates { fc:=pn n b,gates:=[],fb:=[] };have d:i< (pn n b).length:=by simp[pn];O
 have c:=h1.1 i d
 have a:(pn n b)[i]?=some (.wire i):=by
  rw[List.getElem?_eq_getElem d];simp[pn,List.getElem_append_left (by simp[hi]:i< ((List.range n).map qw.wire).length)]
 rw[List.getD_eq_getElem?_getD];change ((C.gates.foldl (pZ n (fun _=>none)) { fc:=pn n b,gates:=[],fb:=[] }).fc[i]?).getD (.const false)=.wire i;rw[c,a];R
private lemma pR {C:J} {n:ℕ} {b:Bool}
  (u:FanInTwo C) {t:ℕ} (ht:t< C.size) :
  let st:=p5 C n b;let g:=C.gates[t]'ht
  (g.op=.not->∀a,g.inputs.head?=some a->a< n+1+t ->
   ∀c,st.fc.getD a (.const false)=.const c ->
    st.fc.getD (n+1+t) (.const false)=.const (!c)/\st.fb.getD t false=false) /\
  (g.op=.and->∀a1 a2,g.inputs=[a1,a2]->a1< n+1+t->a2< n+1+t ->
   (st.fc.getD a1 (.const false)=.const false\/st.fc.getD a2 (.const false)=.const false ->
    st.fc.getD (n+1+t) (.const false)=.const false/\st.fb.getD t false=false) /\
   (st.fc.getD a1 (.const false)=.const true ->
    st.fc.getD (n+1+t) (.const false)=st.fc.getD a2 (.const false)/\st.fb.getD t false=false) /\
   (st.fc.getD a2 (.const false)=.const true ->
    st.fc.getD (n+1+t) (.const false)=st.fc.getD a1 (.const false)/\st.fb.getD t false=false)) /\
  (g.op=.or->∀a1 a2,g.inputs=[a1,a2]->a1< n+1+t->a2< n+1+t ->
   (st.fc.getD a1 (.const false)=.const true\/st.fc.getD a2 (.const false)=.const true ->
    st.fc.getD (n+1+t) (.const false)=.const true/\st.fb.getD t false=false) /\
   (st.fc.getD a1 (.const false)=.const false ->
    st.fc.getD (n+1+t) (.const false)=st.fc.getD a2 (.const false)/\st.fb.getD t false=false) /\
   (st.fc.getD a2 (.const false)=.const false ->
    st.fc.getD (n+1+t) (.const false)=st.fc.getD a1 (.const false)/\st.fb.getD t false=false)):=by
 have i:(pn n b).length=n+1:=by simp[pn]
 have e:=zK n (pn n b) (fun _=>none) C.gates t ht;have k:=zO n (pn n b) C.gates t ht;rw[i] at e k;set st:=p5 C n b;set stPre:=qF n (pn n b) (fun _=>none) (C.gates.take t);set g:=C.gates[t]'ht;have h1:st.fc.getD (n+1+t) (.const false)=(pr stPre.fc (n+stPre.gates.length) g).1:=k.1;have h2:st.fb.getD t false=(pr stPre.fc (n+stPre.gates.length) g).2.isSome:=k.2;Y ⟨?_,?_,?_⟩
 ·intro f a ha s c hc
  cases d:g.inputs with
  | nil=>rw[d] at ha;simp at ha
  | cons a0 rest=>
   rw[d] at ha;simp at ha;subst ha
   have r:stPre.fc.getD a0 (.const false)=.const c:=by
    have hp:st.fc.getD a0 (.const false)=stPre.fc.getD a0 (.const false):=e.1 a0 s;rw[←hp];X hc
   rw[h1,h2];simp only[pr,f,d,r,Option.isSome_none,and_self]
 ·intro f a1 a2 d l m
  have p:st.fc.getD a1 (.const false)=stPre.fc.getD a1 (.const false):=e.1 a1 l;have q:st.fc.getD a2 (.const false)=stPre.fc.getD a2 (.const false):=e.1 a2 m;Y ⟨?_,?_,?_⟩
  ·rintro (j|h)
   ·rw[p] at j;rw[h1,h2];simp only[pr,f,d,j,Option.isSome_none,and_self]
   ·rw[q] at h;rw[h1,h2]
    cases hga:stPre.fc.getD a1 (.const false) with
    | const ca=>cases ca<;>simp only[pr,f,d,h,hga,Option.isSome_none,and_self]
    | wire _=>simp only[pr,f,d,h,hga,Option.isSome_none,and_self]
  ·intro j
   rw[p] at j;rw[h1,h2,q]
   cases hgb:stPre.fc.getD a2 (.const false) with
   | const cb=>cases cb<;>simp only[pr,f,d,j,hgb,Option.isSome_none,and_self]
   | wire _=>simp only[pr,f,d,j,hgb,Option.isSome_none,and_self]
  ·intro h
   rw[q] at h;rw[h1,h2,p]
   cases hga:stPre.fc.getD a1 (.const false) with
   | const ca=>cases ca<;>simp only[pr,f,d,h,hga,Option.isSome_none,and_self]
   | wire _=>simp only[pr,f,d,h,hga,Option.isSome_none,and_self]
 ·intro f a1 a2 d l m
  have p:st.fc.getD a1 (.const false)=stPre.fc.getD a1 (.const false):=e.1 a1 l;have q:st.fc.getD a2 (.const false)=stPre.fc.getD a2 (.const false):=e.1 a2 m;Y ⟨?_,?_,?_⟩
  ·rintro (j|h)
   ·rw[p] at j;rw[h1,h2];simp only[pr,f,d,j,Option.isSome_none,and_self]
   ·rw[q] at h;rw[h1,h2]
    cases hga:stPre.fc.getD a1 (.const false) with
    | const ca=>cases ca<;>simp only[pr,f,d,h,hga,Option.isSome_none,and_self]
    | wire _=>simp only[pr,f,d,h,hga,Option.isSome_none,and_self]
  ·intro j
   rw[p] at j;rw[h1,h2,q]
   cases hgb:stPre.fc.getD a2 (.const false) with
   | const cb=>cases cb<;>simp only[pr,f,d,j,hgb,Option.isSome_none,and_self]
   | wire _=>simp only[pr,f,d,j,hgb,Option.isSome_none,and_self]
  ·intro h
   rw[q] at h;rw[h1,h2,p]
   cases hga:stPre.fc.getD a1 (.const false) with
   | const ca=>cases ca<;>simp only[pr,f,d,h,hga,Option.isSome_none,and_self]
   | wire _=>simp only[pr,f,d,h,hga,Option.isSome_none,and_self]
private lemma zk {n:ℕ} {C:J} (f:IsMinimalCircuit (n+1) C)
  (g:∃y:V n,cF (n+1) C (Fin.snoc y false)≠cF (n+1) C (Fin.snoc y true))
  (c:∃x:Fin (n+1)->Bool,cF (n+1) C x≠x (Fin.last n)) :
  ∃t:ℕ,∃(ht:t< C.size),pC (n+1) t n (C.gates[t]'ht):=by
 by_contra hno
 push Not at hno
 have d:∀(y:V n) (k:ℕ),k≠n ->
   p0 C (Fin.snoc y false) k=p0 C (Fin.snoc y true) k:=by
  intro y k
  induction k using Nat.strong_induction_on with
  | ind k ih=>
   intro l;by_cases j:k< n
   ·rw[p7 C _ k W,p7 C _ k W]
    have:(⟨k,by O⟩:Fin (n+1))=Fin.castSucc ⟨k,j⟩:=Fin.ext rfl
    rw[this,Fin.snoc_castSucc,Fin.snoc_castSucc]
   ·by_cases m:k< n+1+C.size
    ·set t:=k-(n+1)
     have ht:t< C.size :=W;have hk:k=n+1+t :=W;rw[hk,pj C _ t ht,pj C _ t ht];apply zy _ (f.1 _ (List.getElem_mem ht));intro a ha;by_cases b:a< n+1+t
     ·have h:a≠n:=by
       intro i;subst i;X hno t ht ⟨ha,b⟩
      rw[if_pos b,if_pos b];X ih a W h
     ·rw[if_neg b,if_neg b]
    ·rw[z3 C _ k W,z3 C _ k W]
 by_cases e:C.output=n
 ·obtain ⟨x,hx⟩:=c
  apply hx;rw[pb,e,p7 C x n W];R
 ·obtain ⟨y,hy⟩:=g
  X hy (d y C.output e)
private lemma j0 {n:ℕ} {C:J} (c:IsMinimalCircuit (n+1) C) (b:Bool)
  (h:∃y:V n,cF (n+1) C (Fin.snoc y false)≠cF (n+1) C (Fin.snoc y true))
  (i:∃y1 y2:V n,cF (n+1) C (Fin.snoc y1 b)≠cF (n+1) C (Fin.snoc y2 b)) :
  (p3 C n b).size+1<=C.size:=by
 have d:∃x:Fin (n+1)->Bool,cF (n+1) C x≠x (Fin.last n):=by
  obtain ⟨y1,y2,j⟩:=i;by_cases h1:cF (n+1) C (Fin.snoc y1 b)=b
  ·X ⟨Fin.snoc y2 b,by simpa [h1] using j.symm⟩
  ·X ⟨Fin.snoc y1 b,by simpa using h1⟩
 obtain ⟨t0,g,k⟩:=zk c h d;have a:=pk C n b c.1;have f:=pw c.1 g k (p9 C n b c.1)
 have e:(p5 C n b).fb[t0]'(by rw[a.kept_len];X g)=false:=by
  rwa[List.getD_eq_getElem _ _ (by rw[a.kept_len];X g)] at f
 have m:=j4 (by rw[a.kept_len];X g) e
 have l:=qk (p5 C n b).fb;change (p5 C n b).gates.length+1<=C.gates.length;rw[a.gates_len]
 have:=a.kept_len
 O
private lemma zV {n:ℕ} {C:J} (i:IsMinimalCircuit (n+1) C) (b:Bool)
  (hF:∃y:V n,cF (n+1) C (Fin.snoc y false)≠cF (n+1) C (Fin.snoc y true))
  (hG:∃y1 y2:V n,cF (n+1) C (Fin.snoc y1 b)≠cF (n+1) C (Fin.snoc y2 b))
  (hS:∀D:J,FanInTwo D ->
   (∀y:V n,cF n D y=cF (n+1) C (Fin.snoc y b)) ->
   C.size<=D.size+1) :
  let st:=p5 C n b;let D:=p3 C n b
  IsMinimalCircuit n D/\D.size+1=C.size /\
  ∃tstar:ℕ,∃(d:tstar< C.size),
   (∀t (ht:t< C.size),pC (n+1) t n (C.gates[t]'ht)↔t=tstar) /\
   (∀t (ht:t< C.size),st.fb[t]'(by rw[(pk C n b i.1).kept_len];X ht)=false↔t=tstar) /\
   (C.gates[tstar]'d).op=(if b then GateOp.and else GateOp.or) /\
   ∃w,w< n+1+tstar/\w≠n /\
    ((C.gates[tstar]'d).inputs=[n,w]\/(C.gates[tstar]'d).inputs=[w,n]) /\
    st.fc.getD (n+1+tstar) (.const false)=st.fc.getD w (.const false):=by
 set st:=p5 C n b;set D:=p3 C n b;have r:=pk C n b i.1;have hH:FanInTwo D:=qi C n b i.1
 have z:∀y,cF n D y=cF (n+1) C (Fin.snoc y b) :=
  q6 C n b i.1 hG
 have hZ:D.size+1<=C.size:=j0 i b hF hG;have hU:=hS D hH z;have hT:D.size+1=C.size :=W
 have hD:IsMinimalCircuit n D:=by
  Y ⟨hH,fun E hN hI=>?_⟩;have hE:=hS E hN (fun y=>by rw[hI,z])
  O
 have hO:st.fb.count false=1:=by
  have hV:=qk st.fb;have H0:D.size=st.fb.count true:=r.gates_len;have H1:st.fb.length=C.size:=r.kept_len;O
 have hB:∃x:Fin (n+1)->Bool,cF (n+1) C x≠x (Fin.last n):=by
  obtain ⟨y1,y2,hJ⟩:=hG;by_cases h1:cF (n+1) C (Fin.snoc y1 b)=b
  ·X ⟨Fin.snoc y2 b,by simpa [h1] using hJ.symm⟩
  ·X ⟨Fin.snoc y1 b,by simpa using h1⟩
 obtain ⟨tstar,d,s⟩:=zk i hF hB
 have m:st.fb[tstar]'(by rw[r.kept_len];X d)=false:=by
  have:=pw i.1 d s (p9 C n b i.1)
  rwa[List.getD_eq_getElem _ _ (by rw[r.kept_len];X d)] at this
 have f:∀t (ht:t< C.size),
   st.fb[t]'(by rw[r.kept_len];X ht)=false↔t=tstar:=by
  intro t ht
  constructor
  ·intro hL
   by_contra hJ
   have hW:=za (by rw[r.kept_len];X ht)
    (by rw[r.kept_len];X d) hJ hL m
   O
  ·rintro rfl;X m
 have u:∀t (ht:t< C.size),pC (n+1) t n (C.gates[t]'ht)↔t=tstar:=by
  intro t ht
  constructor
  ·intro hX
   have hL:=pw i.1 ht hX (p9 C n b i.1);rw[List.getD_eq_getElem _ _ (by rw[r.kept_len];X ht)] at hL
   X (f t ht).1 hL
  ·rintro rfl;X s
 have hh:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2:=by
  obtain ⟨y1,y2,hJ⟩:=hG;X ⟨Fin.snoc y1 b,Fin.snoc y2 b,hJ⟩
 have e:∀c,st.fc.getD (n+1+tstar) (.const false)≠.const c:=by
  intro c hc;have hP:=pL i.1 hG hc;rcases pY i tstar d with heq|⟨t',hQ,H2,hY⟩
  ·X hP heq
  ·have hA:=pw i.1 hQ hY hc
   rw[List.getD_eq_getElem _ _ (by rw[r.kept_len];X hQ)] at hA
   have:=(f t' hQ).1 hA
   O
 have hK:=pc i hh tstar d;have hC:=pR (n:=n) (b:=b) i.1 d;have j:=p9 C n b i.1;rcases hK with ⟨hM,a,ha,hR⟩|⟨hM,a1,a2,g,p,q,v⟩
 ·exfalso
  obtain ⟨k,_⟩:=s
  cases g:(C.gates[tstar]'d).inputs with
  | nil=>rw[g] at ha;simp at ha
  | cons a0 rest=>
   rw[g] at ha;simp at ha;subst ha;simp only[pa,hM,g,List.mem_singleton] at k;subst k;have hc:=(hC.1 hM n (by rw[g];rfl) hR b j).1
   X e (!b) hc
 ·obtain ⟨k,_⟩:=s
  rcases hM with h|l
  ·simp only[pa,h,g,List.mem_cons,List.not_mem_nil,or_false] at k
   cases b with
   | false=>
    exfalso;rcases k with rfl|rfl
    ·X e false ((hC.2.1 h n a2 g p q).1 (il j)).1
    ·X e false ((hC.2.1 h a1 n g p q).1 (ir j)).1
   | true=>
    Y ⟨hD,hT,tstar,d,u,f,by simpa using h,?_⟩
    rcases k with rfl|rfl
    ·X ⟨a2,q,v.symm,il g,((hC.2.1 h n a2 g p q).2.1 j).1⟩
    ·X ⟨a1,p,v,ir g,((hC.2.1 h a1 n g p q).2.2 j).1⟩
  ·simp only[pa,l,g,List.mem_cons,List.not_mem_nil,or_false] at k
   cases b with
   | true=>
    exfalso;rcases k with rfl|rfl
    ·X e true ((hC.2.2 l n a2 g p q).1 (il j)).1
    ·X e true ((hC.2.2 l a1 n g p q).1 (ir j)).1
   | false=>
    Y ⟨hD,hT,tstar,d,u,f,by simpa using l,?_⟩
    rcases k with rfl|rfl
    ·X ⟨a2,q,v.symm,il g,((hC.2.2 l n a2 g p q).2.1 j).1⟩
    ·X ⟨a1,p,v,ir g,((hC.2.2 l a1 n g p q).2.2 j).1⟩
private lemma zh {n:ℕ} {C:J} (l:IsMinimalCircuit (n+1) C) (b c:Bool)
  (hN:∃y1 y2:V n,cF (n+1) C (Fin.snoc y1 b)≠cF (n+1) C (Fin.snoc y2 b))
  (tstar:ℕ) (m:tstar< C.size)
  (hH:pC (n+1) tstar n (C.gates[tstar]'m))
  (f:(p5 C n b).fc.getD (n+1+tstar) (.const false)=.const c)
  (hY:∀D:J,FanInTwo D ->
   (∀y:V n,cF n D y=cF (n+1) C (Fin.snoc y b)) ->
   C.size<=D.size+2) :
  let st:=p5 C n b;let D:=p3 C n b
  IsMinimalCircuit n D/\D.size+2=C.size /\
  ∃d:ℕ,∃(e:d< C.size),tstar< d /\
   (∀t (ht:t< C.size),pC (n+1) t (n+1+tstar) (C.gates[t]'ht)↔t=d) /\
   (∀t (ht:t< C.size),st.fb[t]'(by rw[(pk C n b l.1).kept_len];X ht)=false↔(t=tstar\/t=d)) /\
   (C.gates[d]'e).op=(if c then GateOp.and else GateOp.or) /\
   ∃u,u< n+1+d/\u≠n+1+tstar /\
    ((C.gates[d]'e).inputs=[n+1+tstar,u]\/(C.gates[d]'e).inputs=[u,n+1+tstar]) /\
    st.fc.getD (n+1+d) (.const false)=st.fc.getD u (.const false):=by
 set st:=p5 C n b;set D:=p3 C n b;have q:=pk C n b l.1;have hI:FanInTwo D:=qi C n b l.1
 have hB:∀y,cF n D y=cF (n+1) C (Fin.snoc y b) :=
  q6 C n b l.1 hN
 have p:st.fb[tstar]'(by rw[q.kept_len];X m)=false:=by
  have:=pw l.1 m hH (p9 C n b l.1)
  rwa[List.getD_eq_getElem _ _ (by rw[q.kept_len];X m)] at this
 have hA:=pL l.1 hN f
 have hJ:∃d:ℕ,∃(e:d< C.size),tstar< d /\
   pC (n+1) d (n+1+tstar) (C.gates[d]'e):=by
  rcases pY l tstar m with heq|h
  ·X absurd heq hA
  ·X h
 obtain ⟨d,e,hZ,hO⟩:=hJ
 have x:st.fb[d]'(by rw[q.kept_len];X e)=false:=by
  have:=pw l.1 e hO f
  rwa[List.getD_eq_getElem _ _ (by rw[q.kept_len];X e)] at this
 have hP:=za (by rw[q.kept_len];X m)
  (by rw[q.kept_len];X e) W p x
 have H2:=qk st.fb;have H6:D.size=st.fb.count true:=q.gates_len;have H7:st.fb.length=C.size:=q.kept_len;have H3:=hY D hI hB;have H0:D.size+2=C.size :=W;have hT:st.fb.count false=2 :=W
 have hG:IsMinimalCircuit n D:=by
  Y ⟨hI,fun E hU hK=>?_⟩;have hE:=hY E hU (fun y=>by rw[hK,hB])
  O
 have i:∀t (ht:t< C.size),
   st.fb[t]'(by rw[q.kept_len];X ht)=false↔(t=tstar\/t=d):=by
  intro t ht
  constructor
  ·intro hQ
   by_contra hL
   push Not at hL
   have H4:=zR (by rw[q.kept_len];X ht)
    (by rw[q.kept_len];X m) (by rw[q.kept_len];X e)
    hL.1 hL.2 W hQ p x
   O
  ·rintro (rfl|rfl)
   ·X p
   ·X x
 have z:∀t (ht:t< C.size),
   pC (n+1) t (n+1+tstar) (C.gates[t]'ht)↔t=d:=by
  intro t ht
  constructor
  ·intro H1
   have hQ:=pw l.1 ht H1 f;rw[List.getD_eq_getElem _ _ (by rw[q.kept_len];X ht)] at hQ
   rcases (i t ht).1 hQ with rfl|rfl
   ·exfalso;have:=H1.2;O
   ·rfl
  ·rintro rfl;X hO
 have hC:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2:=by
  obtain ⟨y1,y2,hL⟩:=hN;X ⟨Fin.snoc y1 b,Fin.snoc y2 b,hL⟩
 have g:∀c',st.fc.getD (n+1+d) (.const false)≠.const c':=by
  intro c' hR;have hV:=pL l.1 hN hR;rcases pY l d e with heq|⟨t',hW,H8,H5⟩
  ·X hV heq
  ·have hD:=pw l.1 hW H5 hR
   rw[List.getD_eq_getElem _ _ (by rw[q.kept_len];X hW)] at hD
   rcases (i t' hW).1 hD with rfl|rfl<;>O
 have hM:=pc l hC d e;have hF:=pR (n:=n) (b:=b) l.1 e;rcases hM with ⟨hS,a,ha,hX⟩|⟨hS,a1,a2,j,v,w,hh⟩
 ·exfalso
  obtain ⟨r,_⟩:=hO
  cases j:(C.gates[d]'e).inputs with
  | nil=>rw[j] at ha;simp at ha
  | cons a0 rest=>
   rw[j] at ha;simp at ha;subst ha;simp only[pa,hS,j,List.mem_singleton] at r;subst r;have hR:=(hF.1 hS (n+1+tstar) (by rw[j];rfl) hX c f).1
   X g (!c) hR
 ·obtain ⟨r,_⟩:=hO
  rcases hS with k|s
  ·simp only[pa,k,j,List.mem_cons,List.not_mem_nil,or_false] at r
   cases c with
   | false=>
    exfalso;rcases r with rfl|rfl
    ·X g false ((hF.2.1 k (n+1+tstar) a2 j v w).1 (il f)).1
    ·X g false ((hF.2.1 k a1 (n+1+tstar) j v w).1 (ir f)).1
   | true=>
    Y ⟨hG,H0,d,e,hZ,z,i,by simpa using k,?_⟩
    rcases r with rfl|rfl
    ·X ⟨a2,w,hh.symm,il j,((hF.2.1 k (n+1+tstar) a2 j v w).2.1 f).1⟩
    ·X ⟨a1,v,hh,ir j,((hF.2.1 k a1 (n+1+tstar) j v w).2.2 f).1⟩
  ·simp only[pa,s,j,List.mem_cons,List.not_mem_nil,or_false] at r
   cases c with
   | true=>
    exfalso;rcases r with rfl|rfl
    ·X g true ((hF.2.2 s (n+1+tstar) a2 j v w).1 (il f)).1
    ·X g true ((hF.2.2 s a1 (n+1+tstar) j v w).1 (ir f)).1
   | false=>
    Y ⟨hG,H0,d,e,hZ,z,i,by simpa using s,?_⟩
    rcases r with rfl|rfl
    ·X ⟨a2,w,hh.symm,il j,((hF.2.2 s (n+1+tstar) a2 j v w).2.1 f).1⟩
    ·X ⟨a1,v,hh,ir j,((hF.2.2 s a1 (n+1+tstar) j v w).2.2 f).1⟩
private lemma jJ {n:ℕ} {C:J} (e:IsMinimalCircuit (n+1) C)
  (Hc:∃y:V n,cF (n+1) C (Fin.snoc y false)≠cF (n+1) C (Fin.snoc y true))
  (hE:∃y1 y2:V n,cF (n+1) C (Fin.snoc y1 false)≠cF (n+1) C (Fin.snoc y2 false))
  (hP:∃y1 y2:V n,cF (n+1) C (Fin.snoc y1 true)≠cF (n+1) C (Fin.snoc y2 true))
  (hJ:∀D:J,FanInTwo D ->
   (∀y:V n,cF n D y=cF (n+1) C (Fin.snoc y false)) ->
   C.size<=D.size+2)
  (hQ:∀D:J,FanInTwo D ->
   (∀y:V n,cF n D y=cF (n+1) C (Fin.snoc y true)) ->
   C.size<=D.size+2) :
  ∃tstar:ℕ,∃(p:tstar< C.size),
   (∀t (ht:t< C.size),pC (n+1) t n (C.gates[t]'ht)↔t=tstar) /\
   ((C.gates[tstar]'p).op=.and\/(C.gates[tstar]'p).op=.or) /\
   ∃w,w< n+1+tstar/\w≠n /\
    ((C.gates[tstar]'p).inputs=[n,w]\/(C.gates[tstar]'p).inputs=[w,n]):=by
 have g:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2:=by
  obtain ⟨y1,y2,hX⟩:=hE;X ⟨Fin.snoc y1 false,Fin.snoc y2 false,hX⟩
 have hK:∃x:Fin (n+1)->Bool,cF (n+1) C x≠x (Fin.last n):=by
  obtain ⟨y1,y2,hX⟩:=hE;by_cases h1:cF (n+1) C (Fin.snoc y1 false)=false
  ·X ⟨Fin.snoc y2 false,by simpa [h1] using hX.symm⟩
  ·X ⟨Fin.snoc y1 false,by simpa using h1⟩
 obtain ⟨t1,q,hI⟩:=zk e Hc hK
 have hY:∀t2 (hZ:t2< C.size),pC (n+1) t2 n (C.gates[t2]'hZ)->t2=t1:=by
  intro t2 hZ Hg;by_contra hX
  have m:∀(ta tb:ℕ) (hR:ta< C.size) (hG:tb< C.size),
    pC (n+1) ta n (C.gates[ta]'hR)->pC (n+1) tb n (C.gates[tb]'hG) ->
    ta< tb->¬pC (n+1) tb (n+1+ta) (C.gates[tb]'hG):=by
   intro ta tb hR hG Hh Hi HD Hj;have Hp:=pc e g ta hR;have Hq:=pc e g tb hG;rcases Hq with ⟨r,a,ha,_⟩|⟨r,a1,a2,hO,_,_,_⟩
   ·cases d:(C.gates[tb]'hG).inputs with
    | nil=>rw[d] at ha;simp at ha
    | cons a0 rest=>
     rw[d] at ha;simp at ha;subst ha;have h1:=Hi.1;have h2:=Hj.1;simp only[pa,r,d,List.mem_singleton] at h1 h2;O
   ·have h1:=Hi.1;have h2:=Hj.1
    have hL:(a1=n/\a2=n+1+ta)\/(a1=n+1+ta/\a2=n):=by
     rcases r with h|h <;>
      (simp only[pa,h,hO,List.mem_cons,List.not_mem_nil,or_false] at h1 h2;
       rcases h1 with Hr|Hs<;>rcases h2 with Ht|Hu <;>
        first|X il ⟨Hr.symm,Hu.symm⟩|X ir ⟨Ht.symm,Hs.symm⟩|O)
    have j:∀x:Fin (n+1)->Bool,
      p8 C tb x =
       match (C.gates[tb]'hG).op with
       | .and=>p0 C x n&&p0 C x (n+1+ta)
       | .or=>p0 C x n||p0 C x (n+1+ta)
       | _=>false:=by
     intro x;have hv:=pj C x tb hG;rw[hO] at hv;have H0:n< n+1+tb :=W;have hS:n+1+ta< n+1+tb :=W
     rcases hL with ⟨Hk,Hl⟩|⟨Hk,Hl⟩ <;>
      rcases r with k|k <;>
      simp[p8,hv,k,Hk,Hl,GateOp.eval,H0,hS,Bool.and_comm,Bool.or_comm]
    rcases Hp with ⟨hM,aa,H1,_⟩|⟨hM,b1,b2,hh,hA,hB,Hm⟩
    ·cases d:(C.gates[ta]'hR).inputs with
     | nil=>rw[d] at H1;simp at H1
     | cons a0 rest=>
      rw[d] at H1;simp at H1;subst H1;have s:=Hh.1;simp only[pa,hM,d,List.mem_singleton] at s
      have i:∀x:Fin (n+1)->Bool,p0 C x (n+1+ta)=!p0 C x n:=by
       intro x;have hv:=pj C x ta hR;rw[hM,d,←s] at hv;simpa [GateOp.eval,show n< n+1+ta by O] using hv
      rcases r with k|k
      ·obtain ⟨x,hx⟩:=z4 e tb hG
       rw[j x,k,i x] at hx;simp at hx
      ·obtain ⟨x,hx⟩:=zU e g tb hG
       rw[j x,k,i x] at hx;simp at hx
    ·have s:=Hh.1
     rcases hM with hopa'|hopa'
     ·simp only[pa,hopa',hh,List.mem_cons,List.not_mem_nil,or_false] at s
      have i:∀x:Fin (n+1)->Bool,
        p0 C x (n+1+ta) =
         (if b1=n then p0 C x n&&p0 C x b2 else p0 C x b1&&p0 C x n):=by
       intro x;have hv:=pj C x ta hR;rw[hopa',hh] at hv;rcases s with hb1|hb2
       ·have h1:b1=n:=hb1.symm
        simp only[hv,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
         id_eq,Bool.and_true,hA,hB,↓reduceIte,h1,show n< n+1+ta by O]
       ·have h2:b2=n:=hb2.symm
        have hU:b1≠n :=W
        simp only[hv,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
         id_eq,Bool.and_true,hA,hB,↓reduceIte,h2,hU,show n< n+1+ta by O]
      rcases r with k|k
      ·obtain ⟨x,hx⟩:=py e tb hG (n+1+ta) W
       apply hx;rw[j x,k,i x]
       split_ifs<;>cases p0 C x n<;>cases p0 C x b1<;>cases p0 C x b2<;>rfl
      ·obtain ⟨x,hx⟩:=py e tb hG n W
       apply hx;rw[j x,k,i x]
       split_ifs<;>cases p0 C x n<;>cases p0 C x b1<;>cases p0 C x b2<;>rfl
     ·simp only[pa,hopa',hh,List.mem_cons,List.not_mem_nil,or_false] at s
      have i:∀x:Fin (n+1)->Bool,
        p0 C x (n+1+ta) =
         (if b1=n then p0 C x n||p0 C x b2 else p0 C x b1||p0 C x n):=by
       intro x;have hv:=pj C x ta hR;rw[hopa',hh] at hv;rcases s with hb1|hb2
       ·have h1:b1=n:=hb1.symm
        simp only[hv,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
         id_eq,Bool.or_false,hA,hB,↓reduceIte,h1,show n< n+1+ta by O]
       ·have h2:b2=n:=hb2.symm
        have hU:b1≠n :=W
        simp only[hv,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
         id_eq,Bool.or_false,hA,hB,↓reduceIte,h2,hU,show n< n+1+ta by O]
      rcases r with k|k
      ·obtain ⟨x,hx⟩:=py e tb hG n W
       apply hx;rw[j x,k,i x]
       split_ifs<;>cases p0 C x n<;>cases p0 C x b1<;>cases p0 C x b2<;>rfl
      ·obtain ⟨x,hx⟩:=py e tb hG (n+1+ta) W
       apply hx;rw[j x,k,i x]
       split_ifs<;>cases p0 C x n<;>cases p0 C x b1<;>cases p0 C x b2<;>rfl
  have f:∀(b:Bool),
    (∃y1 y2:V n,cF (n+1) C (Fin.snoc y1 b)≠cF (n+1) C (Fin.snoc y2 b)) ->
    (∀D:J,FanInTwo D ->
     (∀y:V n,cF n D y=cF (n+1) C (Fin.snoc y b))->C.size<=D.size+2) ->
    ∀c,(p5 C n b).fc.getD (n+1+t1) (.const false)≠.const c:=by
   intro b H2 Hd c hc;have l:=pk C n b e.1;have H3:=pw e.1 q hI (p9 C n b e.1);have H4:=pw e.1 hZ Hg (p9 C n b e.1);rw[List.getD_eq_getElem _ _ (by rw[l.kept_len];X q)] at H3
   rw[List.getD_eq_getElem _ _ (by rw[l.kept_len];X hZ)] at H4
   have H5:=pL e.1 H2 hc;rcases pY e t1 q with H6|⟨t',Hb,He,Hn⟩
   ·X H5 H6
   ·have H7:t'≠t2:=by
     intro H6;subst H6;X m t1 t' q Hb hI Hg He Hn
    have H8:=pw e.1 Hb Hn hc;rw[List.getD_eq_getElem _ _ (by rw[l.kept_len];X Hb)] at H8
    have Hv:=zR (by rw[l.kept_len];X q)
     (by rw[l.kept_len];X hZ) (by rw[l.kept_len];X Hb)
     (Ne.symm hX) W (Ne.symm H7) H3 H4 H8
    have Hw:=qk (p5 C n b).fb
    have Hx:=Hd (p3 C n b) (qi C n b e.1)
     (q6 C n b e.1 H2)
    have HE:(p3 C n b).size=(p5 C n b).fb.count true:=l.gates_len;have HF:(p5 C n b).fb.length=C.size:=l.kept_len;O
  have Hf:=pc e g t1 q;have hV:=pR (n:=n) (b:=false) e.1 q;have H9:=pR (n:=n) (b:=true) e.1 q;have u:=p9 C n false e.1;have hH:=p9 C n true e.1;rcases Hf with ⟨k,a,ha,hN⟩|⟨k,a1,a2,d,v,z,_⟩
  ·cases d:(C.gates[t1]'q).inputs with
   | nil=>rw[d] at ha;simp at ha
   | cons a0 rest=>
    rw[d] at ha;simp at ha;subst ha;have hC:=hI.1;simp only[pa,k,d,List.mem_singleton] at hC;subst hC;X f false hE hJ true ((hV.1 k n (by rw[d];rfl) hN false u).1)
  ·rcases k with hop_and|hop_or
   ·have hC:=hI.1;simp only[pa,hop_and,d,List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl|rfl
    ·X f false hE hJ false ((hV.2.1 hop_and n a2 d v z).1 (il u)).1
    ·X f false hE hJ false ((hV.2.1 hop_and a1 n d v z).1 (ir u)).1
   ·have hC:=hI.1;simp only[pa,hop_or,d,List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl|rfl
    ·X f true hP hQ true ((H9.2.2 hop_or n a2 d v z).1 (il hH)).1
    ·X f true hP hQ true ((H9.2.2 hop_or a1 n d v z).1 (ir hH)).1
 have Hf:=pc e g t1 q;rcases Hf with ⟨k,a,ha,hN⟩|⟨k,a1,a2,d,v,z,hD⟩
 ·exfalso
  cases d:(C.gates[t1]'q).inputs with
  | nil=>rw[d] at ha;simp at ha
  | cons a0 rest=>
   rw[d] at ha;simp at ha;subst ha;have hC:=hI.1;simp only[pa,k,d,List.mem_singleton] at hC;subst hC
   have Hy:=((pR (b:=false) e.1 q).1 k n (by rw[d];rfl) hN false
    (p9 C n false e.1)).1
   have Hz:=((pR (b:=true) e.1 q).1 k n (by rw[d];rfl) hN true
    (p9 C n true e.1)).1
   have hF:=zh e false true hE t1 q hI Hy hJ;have hT:=zh e true false hP t1 q hI Hz hQ;obtain ⟨_,_,h1,Ho,_,HA,_,Ha,_⟩:=hF;obtain ⟨_,_,h2,HG,_,HB,_,hW,_⟩:=hT;have HC:h1=h2:=(HB h1 Ho).1 ((HA h1 Ho).2 rfl);subst HC;simp only[↓reduceIte,Bool.false_eq_true] at Ha hW;rw[Ha] at hW;cases hW
 ·Y ⟨t1,q,fun t ht=>⟨hY t ht,fun H6=>H6▸hI⟩,k,?_⟩
  have hC:=hI.1
  rcases k with hop_eq|hop_eq <;>
   simp only[pa,hop_eq,d,List.mem_cons,List.not_mem_nil,or_false] at hC <;>
   rcases hC with rfl|rfl
  ·X ⟨a2,z,hD.symm,il d⟩
  ·X ⟨a1,v,hD,ir d⟩
  ·X ⟨a2,z,hD.symm,il d⟩
  ·X ⟨a1,v,hD,ir d⟩
private lemma jP {n:ℕ} (f:(V n)->Bool)
  (h:∃C:J,FanInTwo C/\cF n C=f) :
  ∃C:J,IsMinimalCircuit n C/\cF n C=f:=by
 classical
 let P:ℕ->Prop:=fun s=>∃C:J,FanInTwo C/\cF n C=f/\C.size=s
 have b:∃s,P s:=by
  obtain ⟨C,c,hf⟩:=h;X ⟨C.size,C,c,hf,rfl⟩
 let s0:=Nat.find b;obtain ⟨C,c,hf,e⟩:=Nat.find_spec b;Y ⟨C,⟨c,fun D d a=>?_⟩,hf⟩;rw[e];X Nat.find_min' b ⟨D,d,by rw[a,hf],rfl⟩
private lemma zl {n:ℕ} (f:(V n)->Bool)
  (g:∃y1 y2:V n,f y1≠f y2)
  (r:∀D:J,FanInTwo D->cF n D=f->∀s,s<=D.size->s<=D.size)
  (s0:ℕ) (i:∀D:J,FanInTwo D->cF n D=f->s0<=D.size)
  (C:J) (h:FanInTwo C)
  (hC:∀x:Fin (n+1)->Bool,cF (n+1) C x=(x (Fin.last n)||f (Fin.init x))) :
  s0+1<=C.size:=by
 have j:∃D:J,FanInTwo D/\cF (n+1) D=cF (n+1) C :=
  ⟨C,h,rfl⟩
 obtain ⟨M,a,b⟩:=jP (cF (n+1) C) j;have k:M.size<=C.size:=a.2 C h b.symm
 have hM:∀x:Fin (n+1)->Bool,cF (n+1) M x=(x (Fin.last n)||f (Fin.init x)):=by
  intro x;rw[b];X hC x
 have l:∃y0,f y0=false:=by
  obtain ⟨y1,y2,d⟩:=g;cases h1:f y1
  ·X ⟨y1,h1⟩
  ·cases h2:f y2
   ·X ⟨y2,h2⟩
   ·rw[h1,h2] at d;X absurd rfl d
 have e:∃y:V n,
   cF (n+1) M (Fin.snoc y false)≠cF (n+1) M (Fin.snoc y true):=by
  obtain ⟨y0,m⟩:=l;Y ⟨y0,?_⟩;rw[hM,hM];simp[m]
 have c:∃y1 y2:V n,
   cF (n+1) M (Fin.snoc y1 false)≠cF (n+1) M (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,d⟩:=g;Y ⟨y1,y2,?_⟩;rw[hM,hM];simpa using d
 have t:=j0 a false e c
 have p:cF n (p3 M n false)=f:=by
  funext y
  rw[q6 M n false a.1 c y,hM];simp
 have q:=i (p3 M n false) (qi M n false a.1) p;O
private def qx (n:ℕ):ℕ->List Gate
 | 0=>[]
 | 1=>[⟨.or,[0,2]⟩,⟨.and,[1,n]⟩]
 | r+2=>
  let prev:=qx n (r+1);let base:=n+prev.length;let c:=2*(r+1)+1
  prev++[⟨.or,[c-1,c+1]⟩,⟨.and,[c,base]⟩,⟨.or,[base-1,base+1]⟩]
private def zi (m:ℕ):J :=
 let gs:=qx (2*m+1) m
 { gates:=gs,output:=(2*m+1)+gs.length-1 }
private def qY (m:ℕ):J :=
  match m with
  | 0=>⟨[],0⟩
  | 1=>⟨[⟨.and,[0,1]⟩],2⟩
  | k+2=>
    let n:=2*(k+2);let gs:=qx n (k+1)
    { gates:=gs++[⟨.and,[n-2,n-1]⟩,⟨.or,[n+gs.length-1,n+gs.length]⟩]
      output:=n+gs.length+1 }
private lemma zj (n m:ℕ) (hm:1<=m) :
  (qx n m).length=3*m-1:=by
 induction m with
 | zero=>O
 | succ k ih=>
  cases k with
  | zero=>simp[qx]
  | succ k'=>
   have hk:=ih W;simp only[qx,List.length_append,List.length_cons,List.length_nil];O
private lemma jE (n m:ℕ) :
  ∀g∈qx n m,Ok g:=by
 induction m with
 | zero=>simp[qx]
 | succ k ih=>
  cases k with
  | zero=>
   intro g hg;simp only[qx,List.mem_cons,List.not_mem_nil,or_false] at hg;rcases hg with rfl|rfl<;>X ⟨by simp,by simp⟩
  | succ k'=>
   intro g hg;simp only[qx,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg;rcases hg with hg|rfl|rfl|rfl
   ·X ih g hg
   ·X ⟨by simp,by simp⟩
   ·X ⟨by simp,by simp⟩
   ·X ⟨by simp,by simp⟩
private lemma jp (n m:ℕ) (hm:1<=m) (hS:2*m+1<=n) (x:V n) :
  let gs:=qx n m
  (pK gs (List.ofFn x)).getD (n+gs.length-1) false =
   decide (∃i j:Fin n,i.val+1=j.val/\j.val<=2*m/\x i=true/\x j=true):=by
 induction m with
 | zero=>O
 | succ k ih=>
  cases k with
  | zero=>
   simp only[qx,List.length_cons,List.length_nil,qA,zd];have d:(List.ofFn x).length=n:=List.length_ofFn
   have h0:(List.ofFn x).getD 0 false=x ⟨0,by O⟩:=by
    rw[List.getD_eq_getElem _ _ W];simp
   have h1:(List.ofFn x).getD 1 false=x ⟨1,by O⟩:=by
    rw[List.getD_eq_getElem _ _ W];simp
   have h2:(List.ofFn x).getD 2 false=x ⟨2,by O⟩:=by
    rw[List.getD_eq_getElem _ _ W];simp
   have y:((List.ofFn x)++[x ⟨0,by O⟩||x ⟨2,by O⟩]).getD 1 false=x ⟨1,by O⟩:=by
    rw[List.getD_eq_getElem _ _ (by simp[d];O),List.getElem_append_left W]
    simp
   have z:((List.ofFn x)++[x ⟨0,by O⟩||x ⟨2,by O⟩]).getD n false =
     (x ⟨0,by O⟩||x ⟨2,by O⟩):=by
    rw[List.getD_eq_getElem _ _ (by simp[d]),List.getElem_append_right W]
    simp[d]
   simp only[List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,
    Bool.or_false,h0,h2,y,z,List.all_cons,List.all_nil,Bool.and_true]
   rw[List.getD_eq_getElem _ _ (by simp[d]),
    List.getElem_append_right (by simp[d])]
   simp only[List.length_append,d,List.length_singleton,
    show n+2-1-(n+1)=0 by O,List.getElem_singleton]
   apply Bool.eq_iff_iff.2;simp only[Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
   constructor
   ·rintro ⟨hF,hI|hJ⟩
    ·X ⟨⟨0,by O⟩,⟨1,by O⟩,rfl,by simp,hI,hF⟩
    ·X ⟨⟨1,by O⟩,⟨2,by O⟩,rfl,by simp,hF,hJ⟩
   ·rintro ⟨i,j,hD,hj,hi,w⟩
    have:(i.val=0/\j.val=1)\/(i.val=1/\j.val=2) :=W
    rcases this with ⟨hK,hL⟩|⟨hM,hN⟩
    ·have hh:i=⟨0,by O⟩:=Fin.ext hK
     have hA:j=⟨1,by O⟩:=Fin.ext hL
     rw[hh] at hi;rw[hA] at w;X ⟨w,il hi⟩
    ·have hh:i=⟨1,by O⟩:=Fin.ext hM
     have hA:j=⟨2,by O⟩:=Fin.ext hN
     rw[hh] at hi;rw[hA] at w;X ⟨hi,ir w⟩
  | succ k'=>
   set r:=k'+1;have hO:=ih W W;set prev:=qx n r;have hG:prev.length=3*r-1:=zj n r W;set w0:=pK prev (List.ofFn x);have a:w0.length=n+prev.length:=by rw[qm,List.length_ofFn]
   have e:∀i (hi:i< n),w0.getD i false=x ⟨i,hi⟩:=by
    intro i hi;rw[q5 _ _ i (by simp[hi]),List.getD_eq_getElem _ _ (by simp[hi])]
    simp
   set c:=2*r+1;have l:c-1< n :=W;have hc:c< n :=W;have p:c+1< n :=W
   have hP:qx n (r+1) =
     prev++[⟨.or,[c-1,c+1]⟩,⟨.and,[c,n+prev.length]⟩,
      ⟨.or,[n+prev.length-1,n+prev.length+1]⟩]:=rfl
   dsimp only;rw[hP,ql]
   simp only[qA,zd,List.map_cons,List.map_nil,GateOp.eval,
    List.any_cons,List.any_nil,List.all_cons,List.all_nil,id_eq,Bool.or_false,Bool.and_true]
   have q:w0.getD (c-1) false=x ⟨c-1,l⟩:=e (c-1) l;have s:w0.getD (c+1) false=x ⟨c+1,p⟩:=e (c+1) p;set s1:=x ⟨c-1,l⟩||x ⟨c+1,p⟩
   have hB:(w0++[s1]).getD c false=x ⟨c,hc⟩:=by
    rw[List.getD_eq_getElem _ _ (by simp[a];O),List.getElem_append_left W]
    rw[←List.getD_eq_getElem _ _ W];X e c hc
   have g:(w0++[s1]).getD (n+prev.length) false=s1:=by
    rw[List.getD_eq_getElem _ _ (by simp[a]),List.getElem_append_right W]
    simp[a]
   set s2:=x ⟨c,hc⟩&&s1
   have h:((w0++[s1])++[s2]).getD (n+prev.length-1) false =
     w0.getD (n+prev.length-1) false:=by
    rw[List.getD_eq_getElem _ _ (by simp only[List.length_append,List.length_singleton,a];O),
     List.getElem_append_left (by simp only[List.length_append,List.length_singleton,a];O),
     List.getElem_append_left W,
     ← List.getD_eq_getElem _ _ W]
   have f:((w0++[s1])++[s2]).getD (n+prev.length+1) false=s2:=by
    rw[List.getD_eq_getElem _ _ (by simp only[List.length_append,List.length_singleton,a];O),
     List.getElem_append_right (by simp only[List.length_append,List.length_singleton,a];O)]
    simp only[List.length_append,List.length_singleton,a,Nat.sub_self,List.getElem_singleton]
   rw[q,s,hB,g,h,f]
   have t:(prev++([⟨.or,[c-1,c+1]⟩,⟨.and,[c,n+prev.length]⟩,
     ⟨.or,[n+prev.length-1,n+prev.length+1]⟩]:List Gate)).length=prev.length+3:=by simp
   have b:(pK prev (List.ofFn x)).length=n+prev.length:=a
   rw[t,
    List.getD_eq_getElem _ _ (by simp only[List.length_append,List.length_singleton,b];O),
    List.getElem_append_right (by simp only[List.length_append,List.length_singleton,b];O)]
   simp only[List.length_append,b,List.length_singleton,
    show n+(prev.length+3)-1-(n+prev.length+1+1)=0 by O,
    List.getElem_singleton]
   rw[hO];apply Bool.eq_iff_iff.2;simp only[Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,s2,s1]
   constructor
   ·rintro (⟨i,j,hD,hj,hi,w⟩|⟨hH,hQ|hR⟩)
    ·X ⟨i,j,hD,by O,hi,w⟩
    ·X ⟨⟨c-1,l⟩,⟨c,hc⟩,by show c-1+1=c;O,by show c<=2*(r+1);O,hQ,hH⟩
    ·X ⟨⟨c,hc⟩,⟨c+1,p⟩,rfl,by show c+1<=2*(r+1);O,hH,hR⟩
   ·rintro ⟨i,j,hD,hj,hi,w⟩
    by_cases hE:j.val<=2*r
    ·X il ⟨i,j,hD,hE,hi,w⟩
    ·right
     have hC:(i.val=c-1/\j.val=c)\/(i.val=c/\j.val=c+1) :=W;rcases hC with ⟨hh,hA⟩|⟨hh,hA⟩
     ·have u:i=⟨c-1,l⟩:=Fin.ext hh
      have v:j=⟨c,hc⟩:=Fin.ext hA;subst u;subst v;X ⟨w,il hi⟩
     ·have u:i=⟨c,hc⟩:=Fin.ext hh
      have v:j=⟨c+1,p⟩:=Fin.ext hA;subst u;subst v;X ⟨hi,ir w⟩
private lemma jv (m:ℕ):FanInTwo (zi m) :=
 jE (2*m+1) m
private lemma jk (m:ℕ) (hm:1<=m) :
  (zi m).size=3*m-1 :=
 zj (2*m+1) m hm
private lemma jl (m:ℕ) (hm:1<=m) :
  cF (2*m+1) (zi m)=pq (2*m+1):=by
 funext x
 have h:=jp (2*m+1) m hm le_rfl x
 change (pK (qx (2*m+1) m) (List.ofFn x)).getD
  ((2*m+1)+(qx (2*m+1) m).length-1) false=pq (2*m+1) x
 rw[h];apply Bool.eq_iff_iff.2;simp only[px,decide_eq_true_eq]
 constructor
 ·rintro ⟨i,j,a,_,hi,hj⟩;X ⟨i,j,a,hi,hj⟩
 ·rintro ⟨i,j,a,hi,hj⟩;X ⟨i,j,a,by O,hi,hj⟩
private lemma jq (m:ℕ):FanInTwo (qY m):=by
 cases m with
 | zero=>intro g hg;simp[qY] at hg
 | succ k=>
  cases k with
  | zero=>
   intro g hg;simp only[qY,List.mem_singleton] at hg;subst hg;X ⟨by simp,by simp⟩
  | succ k'=>
   intro g hg;simp only[qY,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg;rcases hg with hg|rfl|rfl
   ·X jE _ _ g hg
   ·X ⟨by simp,by simp⟩
   ·X ⟨by simp,by simp⟩
private lemma jf (m:ℕ) (hm:1<=m) :
  (qY m).size=3*m-2:=by
 cases m with
 | zero=>O
 | succ k=>
  cases k with
  | zero=>simp[qY,Circuit.size]
  | succ k'=>
   simp only[qY,Circuit.size,List.length_append,List.length_cons,List.length_nil];rw[zj _ (k'+1) W];O
private lemma zS (m:ℕ) (hm:1<=m) :
  cF (2*m) (qY m)=pq (2*m):=by
 cases m with
 | zero=>O
 | succ k=>
  cases k with
  | zero=>
   funext x
   change (pK [⟨.and,[0,1]⟩] (List.ofFn x)).getD 2 false=pq 2 x
   simp only[qA,zd,List.map_cons,List.map_nil,GateOp.eval,
    List.all_cons,List.all_nil,id_eq,Bool.and_true]
   have h0:(List.ofFn x).getD 0 false=x ⟨0,by O⟩:=by
    rw[List.getD_eq_getElem _ _ (by simp)];simp
   have h1:(List.ofFn x).getD 1 false=x ⟨1,by O⟩:=by
    rw[List.getD_eq_getElem _ _ (by simp)];simp
   rw[h0,h1,List.getD_eq_getElem _ _ (by simp),List.getElem_append_right (by simp)]
   simp only[List.length_ofFn,Nat.sub_self,List.getElem_singleton];apply Bool.eq_iff_iff.2;simp only[px,Bool.and_eq_true]
   constructor
   ·rintro ⟨y,s⟩;X ⟨⟨0,by O⟩,⟨1,by O⟩,rfl,y,s⟩
   ·rintro ⟨i,j,p,hi,hj⟩
    have h1:i.val< 2:=i.isLt;have h2:j.val< 2:=j.isLt;have z:i=⟨0,by O⟩:=by ext;simp;O
    have hh:j=⟨1,by O⟩:=by ext;simp;O
    rw[z] at hi;rw[hh] at hj;X ⟨hi,hj⟩
  | succ k'=>
   set n:=2*(k'+1+1) with hn_def;funext x;set gs:=qx n (k'+1);have v:gs.length=3*(k'+1)-1:=zj n (k'+1) W;have g:=jp n (k'+1) W W x;set w0:=pK gs (List.ofFn x);have b:w0.length=n+gs.length:=by rw[qm,List.length_ofFn]
   have d:∀i (hi:i< n),w0.getD i false=x ⟨i,hi⟩:=by
    intro i hi;have t:(List.ofFn x).length=n:=List.length_ofFn;rw[q5 _ _ i W,List.getD_eq_getElem _ _ W,List.getElem_ofFn]
   change (pK (gs++[⟨.and,[n-2,n-1]⟩,⟨.or,[n+gs.length-1,n+gs.length]⟩])
    (List.ofFn x)).getD (n+gs.length+1) false=pq n x
   rw[ql]
   simp only[qA,zd,List.map_cons,List.map_nil,GateOp.eval,
    List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false]
   have q:n-2< n :=W;have r:n-1< n :=W;rw[d (n-2) q,d (n-1) r];set e:=x ⟨n-2,q⟩&&x ⟨n-1,r⟩
   have c:(w0++[e]).getD (n+gs.length-1) false=w0.getD (n+gs.length-1) false:=by
    rw[List.getD_eq_getElem _ _ (by simp only[List.length_append,List.length_singleton,b];O),
     List.getElem_append_left W,
     ← List.getD_eq_getElem _ _ W]
   have f:(w0++[e]).getD (n+gs.length) false=e:=by
    rw[List.getD_eq_getElem _ _ (by simp only[List.length_append,List.length_singleton,b];O),
     List.getElem_append_right W]
    simp only[b,Nat.sub_self,List.getElem_singleton]
   have a:(pK gs (List.ofFn x)).length=n+gs.length:=b
   rw[c,f,
    List.getD_eq_getElem _ _ (by simp only[List.length_append,List.length_singleton,a];O),
    List.getElem_append_right (by simp only[List.length_append,List.length_singleton,a];O)]
   simp only[List.length_append,a,List.length_singleton,Nat.sub_self,
    List.getElem_singleton]
   rw[g];apply Bool.eq_iff_iff.2;simp only[px,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,e]
   constructor
   ·rintro (⟨i,j,p,_,hi,hj⟩|⟨s,hA⟩)
    ·X ⟨i,j,p,hi,hj⟩
    ·X ⟨⟨n-2,q⟩,⟨n-1,r⟩,by show n-2+1=n-1;O,s,hA⟩
   ·rintro ⟨i,j,p,hi,hj⟩
    by_cases u:j.val<=2*(k'+1)
    ·X il ⟨i,j,p,u,hi,hj⟩
    ·right
     have hB:j.val< n:=j.isLt;have w:n=2*(k'+1+1):=hn_def;have h:i=⟨n-2,q⟩:=Fin.ext (by dsimp;O)
     have l:j=⟨n-1,r⟩:=Fin.ext (by dsimp;O)
     subst h;subst l;X ⟨hi,hj⟩
private lemma q9 :
  ∀n:ℕ,2<=n->∀C:J,FanInTwo C->cF n C=pq n ->
   (if n%2=0 then 3*(n/2)-2 else 3*(n/2)-1)<=C.size:=by
 intro n
 induction n using Nat.strong_induction_on with
 | ind n ih=>
  intro hn C H5 hC;obtain ⟨M,d,m⟩:=jP (pq n) ⟨C,H5,hC⟩;have Ha:M.size<=C.size:=d.2 C H5 (hC.trans m.symm)
  suffices hM:(if n%2=0 then 3*(n/2)-2 else 3*(n/2)-1)<=M.size by O
  by_cases Hb:n=2
  ·subst Hb
   simp only[Nat.reduceMod,↓reduceIte,Nat.reduceDiv,Nat.mul_one,Nat.reduceSub];by_contra h0;have hX:M.size=0 :=W;have hH:M.gates=[]:=List.eq_nil_of_length_eq_zero hX
   have hI:∀x:Fin 2->Bool,pq 2 x=(List.ofFn x).getD M.output false:=by
    intro x;rw[←cf m x,pb,p0,qu,hH,zd]
   match ho:M.output with
   | 0=>
    have:=hI (e1 0);rw[ho,pW] at this
    simp[e1] at this
   | 1=>
    have:=hI (e1 1);rw[ho,pW] at this
    simp[e1] at this
   | k+2=>
    have:=hI (pe 0);rw[ho,q0 W] at this
    rw[List.getD_eq_default _ _ (by simp)] at this;cases this
  ·by_cases hB:n%2=0
   ·
    obtain ⟨n',rfl⟩:∃n',n=n'+1:=⟨n-1,by O⟩
    have v:2<=n' :=W;have H6:2<=n'-1 :=W
    have e:∀y:Fin n'->Bool,cF (n'+1) M (Fin.snoc y false)=pq n' y:=by
     intro y;rw[m,z8]
    have g:∀y:Fin n'->Bool,
      cF (n'+1) M (Fin.snoc y true) =
       (y ⟨n'-1,by O⟩||pq (n'-1) (fun i=>y ⟨i.val,by O⟩)):=by
     intro y;rw[m,qT n' W]
    have hJ:∃y:Fin n'->Bool,
      cF (n'+1) M (Fin.snoc y false)≠cF (n'+1) M (Fin.snoc y true):=by
     Y ⟨e1 (n'-1),?_⟩;rw[e,g,pW];simp[e1]
    have q:∃y1 y2:Fin n'->Bool,
      cF (n'+1) M (Fin.snoc y1 false)≠cF (n'+1) M (Fin.snoc y2 false):=by
     obtain ⟨y1,y2,hK⟩:=ps v;X ⟨y1,y2,by rw[e,e];X hK⟩
    have hP:∃y1 y2:Fin n'->Bool,
      cF (n'+1) M (Fin.snoc y1 true)≠cF (n'+1) M (Fin.snoc y2 true):=by
     Y ⟨e0,e1 (n'-1),?_⟩;rw[g,g];have Hc:pq (n'-1) (fun _=>false)=false:=zq (n'-1);simp[e0,e1,Hc]
    have hD:∀D:J,FanInTwo D ->
      (∀y:Fin n'->Bool,cF n' D y=cF (n'+1) M (Fin.snoc y false)) ->
      3*((n'+1)/2)-4<=D.size:=by
     intro D hL r;have h:=ih n' W v D hL (funext fun y=>by rw[r y,e])
     have hY:n'%2≠0 :=W;simp only[hY,↓reduceIte] at h
     have:n'/2=(n'+1)/2-1 :=W
     O
    have hQ:∀D:J,FanInTwo D ->
      (∀y:Fin n'->Bool,cF n' D y=cF (n'+1) M (Fin.snoc y true)) ->
      3*((n'+1)/2)-4<=D.size:=by
     intro D hL r;obtain ⟨k,hE⟩:∃k,n'=k+1:=⟨n'-1,by O⟩
     have hN:k%2=0 :=W;have H7:2<=k :=W
     have Hd:∀E:J,FanInTwo E->cF k E=pq k ->
       3*(k/2)-2<=E.size:=by
      intro E hZ hR;have h:=ih k W H7 E hZ hR;simpa [hN] using h
     have He:∀x:Fin (k+1)->Bool,
       cF (k+1) D x=(x (Fin.last k)||pq k (Fin.init x)):=by
      intro x;let y:Fin n'->Bool:=fun i=>x (Fin.cast hE i);have h1:=r y;have h2:=g y;rw[h2] at h1
      have Hf:List.ofFn x=List.ofFn y:=by
       apply List.ext_getElem
       ·simp[hE]
       ·intro i Ho Hp
        rw[List.getElem_ofFn,List.getElem_ofFn];simp[y]
      have hS:cF (k+1) D x=cF n' D y:=by
       unfold circuitFun Circuit.eval
       rw[Hf]
      rw[hS,h1];congr 1
      ·simp[y,Fin.last];congr 1;ext;simp;O
      ·apply Bool.eq_iff_iff.2
       simp only[px]
       constructor
       ·rintro ⟨i,j,H0,hi,hj⟩
        Y ⟨⟨i.val,by O⟩,⟨j.val,by O⟩,H0,?_,?_⟩
        ·X (congrArg x (Fin.ext rfl)).trans hi
        ·X (congrArg x (Fin.ext rfl)).trans hj
       ·rintro ⟨i,j,H0,hi,hj⟩
        Y ⟨⟨i.val,by O⟩,⟨j.val,by O⟩,H0,?_,?_⟩
        ·X (congrArg x (Fin.ext rfl)).trans hi
        ·X (congrArg x (Fin.ext rfl)).trans hj
     have Hg:=zl (pq k) (ps H7) (fun _ _ _ _ h=>h)
      (3*(k/2)-2) Hd D hL He
     have:k/2=(n'+1)/2-1 :=W
     O
    have hh:∃x:Fin (n'+1)->Bool,cF (n'+1) M x≠x (Fin.last n'):=by
     obtain ⟨y1,y2,hK⟩:=q;by_cases h1:cF (n'+1) M (Fin.snoc y1 false)=false
     ·X ⟨Fin.snoc y2 false,by simpa [h1] using hK.symm⟩
     ·X ⟨Fin.snoc y1 false,by simpa using h1⟩
    obtain ⟨t0,hF,hV⟩:=zk d hJ hh
    have w:∃x1 x2:Fin (n'+1)->Bool,cF (n'+1) M x1≠cF (n'+1) M x2:=by
     obtain ⟨y1,y2,hK⟩:=q;X ⟨Fin.snoc y1 false,Fin.snoc y2 false,hK⟩
    have f:∀b c,
      (∃y1 y2:Fin n'->Bool,cF (n'+1) M (Fin.snoc y1 b)≠cF (n'+1) M (Fin.snoc y2 b)) ->
      (p5 M n' b).fc.getD (n'+1+t0) (.const false)=.const c ->
      (p3 M n' b).size+2<=M.size:=by
     intro b c H1 hc;have p:=pk M n' b d.1;have H8:=pw d.1 hF hV (p9 M n' b d.1);rw[List.getD_eq_getElem _ _ (by rw[p.kept_len];X hF)] at H8
     have H2:=pL d.1 H1 hc;rcases pY d t0 hF with heq|⟨t',H3,Hh,Hi⟩
     ·X absurd heq H2
     ·have hT:=pw d.1 H3 Hi hc
      rw[List.getD_eq_getElem _ _ (by rw[p.kept_len];X H3)] at hT
      have Hj:=za (by rw[p.kept_len];X hF)
       (by rw[p.kept_len];X H3) W H8 hT
      have Hk:=qk (p5 M n' b).fb;have Hq:(p3 M n' b).size=(p5 M n' b).fb.count true:=p.gates_len;have Hr:(p5 M n' b).fb.length=M.size:=p.kept_len;O
    have Hl:=pc d w t0 hF;have hO:=pR (n:=n') (b:=false) d.1 hF;have hU:=pR (n:=n') (b:=true) d.1 hF;have s:=p9 M n' false d.1;have z:=p9 M n' true d.1;simp only[hB,↓reduceIte];rcases Hl with ⟨hW,a,ha,Hm⟩|⟨hW,a1,a2,l,t,u,_⟩
    ·cases l:(M.gates[t0]'hF).inputs with
     | nil=>rw[l] at ha;simp at ha
     | cons a0 rest=>
      rw[l] at ha;simp at ha;subst ha;have hG:=hV.1;simp only[pa,hW,l,List.mem_singleton] at hG;have hc:=(hO.1 hW n' (by rw[l,←hG];rfl) W false s).1
      have hT:=f false true q hc
      have H9:=hD (p3 M n' false) (qi M n' false d.1)
       (q6 M n' false d.1 q)
      O
    ·rcases hW with hop_and|hop_or
     ·have hG:=hV.1;simp only[pa,hop_and,l,List.mem_cons,List.not_mem_nil,or_false] at hG
      have hc:(p5 M n' false).fc.getD (n'+1+t0) (.const false)=.const false:=by
       rcases hG with ha1|ha2
       ·rw[←ha1] at l t;X ((hO.2.1 hop_and n' a2 l t u).1 (il s)).1
       ·rw[←ha2] at l u;X ((hO.2.1 hop_and a1 n' l t u).1 (ir s)).1
      have hT:=f false false q hc
      have H9:=hD (p3 M n' false) (qi M n' false d.1)
       (q6 M n' false d.1 q)
      O
     ·have hG:=hV.1;simp only[pa,hop_or,l,List.mem_cons,List.not_mem_nil,or_false] at hG
      have hc:(p5 M n' true).fc.getD (n'+1+t0) (.const false)=.const true:=by
       rcases hG with ha1|ha2
       ·rw[←ha1] at l t;X ((hU.2.2 hop_or n' a2 l t u).1 (il z)).1
       ·rw[←ha2] at l u;X ((hU.2.2 hop_or a1 n' l t u).1 (ir z)).1
      have hT:=f true true hP hc
      have H9:=hQ (p3 M n' true) (qi M n' true d.1)
       (q6 M n' true d.1 hP)
      O
   ·
    obtain ⟨n',rfl⟩:∃n',n=n'+1:=⟨n-1,by O⟩
    have v:2<=n' :=W;have hA:n'%2=0 :=W
    have e:∀y:Fin n'->Bool,cF (n'+1) M (Fin.snoc y false)=pq n' y:=by
     intro y;rw[m,z8]
    have g:∀y:Fin n'->Bool,
      cF (n'+1) M (Fin.snoc y true) =
       (y ⟨n'-1,by O⟩||pq (n'-1) (fun i=>y ⟨i.val,by O⟩)):=by
     intro y;rw[m,qT n' W]
    have hJ:∃y:Fin n'->Bool,
      cF (n'+1) M (Fin.snoc y false)≠cF (n'+1) M (Fin.snoc y true):=by
     Y ⟨e1 (n'-1),?_⟩;rw[e,g,pW];simp[e1]
    have q:∃y1 y2:Fin n'->Bool,
      cF (n'+1) M (Fin.snoc y1 false)≠cF (n'+1) M (Fin.snoc y2 false):=by
     obtain ⟨y1,y2,hK⟩:=ps v;X ⟨y1,y2,by rw[e,e];X hK⟩
    have Hs:=j0 d false hJ q
    have Hn:cF n' (p3 M n' false)=pq n':=by
     funext y;rw[q6 M n' false d.1 q y,e]
    have H4:=ih n' W v (p3 M n' false)
     (qi M n' false d.1) Hn
    simp only[hB,↓reduceIte];simp only[hA,↓reduceIte] at H4
    have:n'/2=(n'+1)/2 :=W
    O
private lemma zr {m:ℕ} (hm:1<=m) {C:J}
  (a:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m)) :
  C.size=3*m-2:=by
 have b:=q9 (2*m) W C a.1 hfun;have c:=a.2 (qY m) (jq m) (by rw[zS m hm,hfun])
 rw[jf m hm] at c;simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left m (by O:0< 2)] at b
 O
private lemma jw {m:ℕ} (hm:1<=m) {C:J}
  (a:IsMinimalCircuit (2*m+1) C) (hfun:cF (2*m+1) C=pq (2*m+1)) :
  C.size=3*m-1:=by
 have d:=q9 (2*m+1) W C a.1 hfun;have e:=a.2 (zi m) (jv m) (by rw[jl m hm,hfun])
 rw[jk m hm] at e;have b:(2*m+1)%2≠0 :=W;have c:(2*m+1)/2=m :=W;simp only[b,↓reduceIte,c] at d;O
private lemma jm (env:List qw) (nextWire:ℕ) (g:Gate) (s:qw) (g':Gate)
  (b:pr env nextWire g=(s,some g')) :
  s=.wire nextWire/\g'.op=g.op /\
  (∀a∈g'.inputs,∃idx,env.getD idx (.const false)=.wire a):=by
 obtain ⟨op,ins⟩:=g
 cases op with
 | not=>
  cases ins with
  | nil=>simp[pr] at b
  | cons a rest=>
   simp only[pr] at b
   cases h1:env.getD a (.const false) with
   | const _=>rw[h1] at b;simp at b
   | wire wa=>
    rw[h1] at b;simp only[Prod.mk.injEq,Option.some.injEq] at b;Y ⟨b.1.symm,by rw[←b.2],?_⟩
    rw[←b.2];simp only[List.mem_singleton];rintro _ rfl;X ⟨a,h1⟩
 | and=>
  match ins with
  | []=>simp[pr] at b
  | [_]=>simp[pr] at b
  | a1::a2::_=>
   simp only[pr] at b
   cases h1:env.getD a1 (.const false) with
   | const c1=>
    rw[h1] at b
    cases h2:env.getD a2 (.const false) with
    | const c2=>rw[h2] at b;cases c1<;>cases c2<;>simp at b
    | wire _=>rw[h2] at b;cases c1<;>simp at b
   | wire w1=>
    rw[h1] at b
    cases h2:env.getD a2 (.const false) with
    | const c2=>rw[h2] at b;cases c2<;>simp at b
    | wire w2=>
     rw[h2] at b;simp only[Prod.mk.injEq,Option.some.injEq] at b;Y ⟨b.1.symm,by rw[←b.2],?_⟩
     rw[←b.2];simp only[List.mem_cons,List.not_mem_nil,or_false]
     rintro a (rfl|rfl)
     ·X ⟨a1,h1⟩
     ·X ⟨a2,h2⟩
 | or=>
  match ins with
  | []=>simp[pr] at b
  | [_]=>simp[pr] at b
  | a1::a2::_=>
   simp only[pr] at b
   cases h1:env.getD a1 (.const false) with
   | const c1=>
    rw[h1] at b
    cases h2:env.getD a2 (.const false) with
    | const c2=>rw[h2] at b;cases c1<;>cases c2<;>simp at b
    | wire _=>rw[h2] at b;cases c1<;>simp at b
   | wire w1=>
    rw[h1] at b
    cases h2:env.getD a2 (.const false) with
    | const c2=>rw[h2] at b;cases c2<;>simp at b
    | wire w2=>
     rw[h2] at b;simp only[Prod.mk.injEq,Option.some.injEq] at b;Y ⟨b.1.symm,by rw[←b.2],?_⟩
     rw[←b.2];simp only[List.mem_cons,List.not_mem_nil,or_false]
     rintro a (rfl|rfl)
     ·X ⟨a1,h1⟩
     ·X ⟨a2,h2⟩
 | mod _=>simp[pr] at b
 | maj=>simp[pr] at b
private lemma jR (b:ℕ) (a:ℕ->Option qw) (st:z5) (g:Gate) :
  st.gates.length<=(pZ b a st g).gates.length /\
  (∀k,k< st.gates.length->(pZ b a st g).gates[k]?=st.gates[k]?):=by
 unfold pZ
 cases a st.fb.length with
 | some s=>X ⟨le_refl _,fun _ _=>rfl⟩
 | none=>
  cases pr st.fc (b+st.gates.length) g with
  | mk s mg=>
   cases mg with
   | none=>X ⟨le_refl _,fun _ _=>rfl⟩
   | some g'=>
    X ⟨by simp,fun k hk=>by simp[List.getElem?_append_left hk]⟩
private lemma j7 (b:ℕ) (a:ℕ->Option qw) (gs:List Gate) (st:z5) :
  st.gates.length<=(gs.foldl (pZ b a) st).gates.length /\
  (∀k,k< st.gates.length->(gs.foldl (pZ b a) st).gates[k]?=st.gates[k]?):=by
 induction gs generalizing st with
 | nil=>X ⟨le_refl _,fun _ _=>rfl⟩
 | cons g gs ih=>
  have h1:=jR b a st g;have h2:=ih (pZ b a st g);Y ⟨le_trans h1.1 h2.1,fun k hk=>?_⟩;rw[List.foldl_cons,h2.2 k (lt_of_lt_of_le hk h1.1),h1.2 k hk]
private lemma p4 {C:J} {n:ℕ} {b:Bool}
    (hG:FanInTwo C) {t:ℕ} (ht:t< C.size)
    (hD:(p5 C n b).fb[t]'(by rw[(pk C n b hG).kept_len];X ht)=true) :
    let st:=p5 C n b;let D:=p3 C n b
    ∃(k:ℕ) (hk:k< D.size),
      k=(qF n (pn n b) (fun _=>none) (C.gates.take t)).gates.length /\
      st.fc.getD (n+1+t) (.const false)=.wire (n+k) /\
      (D.gates[k]'hk).op=(C.gates[t]'ht).op /\
      (∀(op:GateOp) (a1 a2:ℕ),
        (op=.and\/op=.or) ->
        (C.gates[t]'ht).op=op ->
        (C.gates[t]'ht).inputs=[a1,a2] ->
        a1< n+1+t->a2< n+1+t ->
        ∃w1 w2:ℕ,w1< n+k/\w2< n+k /\
          st.fc.getD a1 (.const false)=.wire w1 /\
          st.fc.getD a2 (.const false)=.wire w2 /\
          (D.gates[k]'hk).inputs=[w1,w2]) /\
      (∀y:V n,p0 D y (n+k)=p0 C (Fin.snoc y b) (n+1+t)):=by
  set st:=p5 C n b;set D:=p3 C n b;set stPre:=qF n (pn n b) (fun _=>none) (C.gates.take t);set k:=stPre.gates.length;have hP:C.gates.length=C.size:=rfl;have d:(pn n b).length=n+1:=by simp[pn]
  have hH:=pk C n b hG
  have c:je n (n+1) (C.gates.take t) stPre:=by
    have hQ:∀s∈pn n b,zC n s:=by
      intro s hs;simp only[pn,List.mem_append,List.mem_map,List.mem_range,List.mem_singleton] at hs;rcases hs with ⟨i,hi,rfl⟩|rfl
      · X hi
      · trivial
    have z:∀g∈C.gates.take t,Ok g:=fun g hg=>hG g (List.mem_of_mem_take hg);have h:=ju n (pn n b) (fun _=>none) (C.gates.take t) z hQ (by simp)
    simpa [stPre,d] using h
  have l:=zK n (pn n b) (fun _=>none) C.gates t ht;have m:=zO n (pn n b) C.gates t ht;rw[d] at l m
  have hh:st.fb.getD t false=true:=by
    rw[List.getD_eq_getElem _ _ (by rw[hH.kept_len];X ht)];X hD
  have hA:C.gates=C.gates.take t++(C.gates[t]'ht)::C.gates.drop (t+1):=by
    have h1:=List.take_append_drop t C.gates;have h2:C.gates.drop t=(C.gates[t]'ht)::C.gates.drop (t+1):=List.drop_eq_getElem_cons ht;rw[←h2,h1]
  have p:st=(C.gates.drop (t+1)).foldl (pZ n (fun _=>none))
      (pZ n (fun _=>none) stPre (C.gates[t]'ht)):=by
    show qF n (pn n b) (fun _=>none) C.gates=_
    unfold qF
    conv_lhs=>rw[hA]
    rw[List.foldl_append,List.foldl_cons];R
  cases hev:pr stPre.fc (n+k) (C.gates[t]'ht) with
  | mk s mg=>
    have w:mg.isSome=true:=by
      have h2:=m.2;change st.fb.getD t false=(pr stPre.fc (n+k) (C.gates[t]'ht)).2.isSome at h2;rw[hh,hev] at h2;X h2.symm
    cases mg with
    | none=>simp at w
    | some g'=>
      have hE:st.fc.getD (n+1+t) (.const false)=s:=by
        have h1:=m.1;change st.fc.getD (n+1+t) (.const false)=(pr stPre.fc (n+k) (C.gates[t]'ht)).1 at h1;rw[hev] at h1;X h1
      have e:pZ n (fun _=>none) stPre (C.gates[t]'ht) =
          { fc:=stPre.fc++[s],gates:=stPre.gates++[g'],fb:=stPre.fb++[true] }:=by
        simp[pZ,hev,k]
      have x:=j7 n (fun _=>none) (C.gates.drop (t+1))
        (pZ n (fun _=>none) stPre (C.gates[t]'ht))
      have hk:k< D.size:=by
        have hF:(pZ n (fun _=>none) stPre (C.gates[t]'ht)).gates.length=k+1:=by
          rw[e];simp[k]
        have hL:=x.1;rw[←p,hF] at hL;X hL
      have hI:D.gates[k]'hk=g':=by
        have q:=x.2 k (by rw[e];simp[k])
        rw[←p] at q;change D.gates[k]?=_ at q;rw[List.getElem?_eq_getElem hk,e] at q;simp[k] at q;X q
      have ⟨hJ,hK,_⟩:=jm stPre.fc (n+k) (C.gates[t]'ht) s g' hev;have r:st.fc.getD (n+1+t) (.const false)=.wire (n+k):=hE.trans hJ;Y ⟨k,hk,rfl,r,by rw[hI,hK],?_,?_⟩
      · intro op a1 a2 hB hC f hR hS
        have j:(C.gates.take t).length=t:=by rw[List.length_take];O
        have hT:stPre.fc.length=n+1+t:=by rw[c.env_len,c.kept_len,j]
        have hM:=l.1 a1 hR;have hN:=l.1 a2 hS;rcases hB with rfl|rfl
        · have a:pr stPre.fc (n+k) ⟨.and,[a1,a2]⟩=(s,some g'):=by
            cases hg:C.gates[t]'ht with
            | mk op0 ins0=>
              rw[hg] at hC f hev;dsimp at hC f;subst hC;subst f;X hev
          simp only[pr] at a
          cases h1:stPre.fc.getD a1 (.const false) with
          | const c1=>
            rw[h1] at a
            cases h2:stPre.fc.getD a2 (.const false) with
            | const c2=>rw[h2] at a;cases c1<;>cases c2<;>simp at a
            | wire _=>rw[h2] at a;cases c1<;>simp at a
          | wire w1=>
            rw[h1] at a
            cases h2:stPre.fc.getD a2 (.const false) with
            | const c2=>rw[h2] at a;cases c2<;>simp at a
            | wire w2=>
              rw[h2] at a;simp only[Prod.mk.injEq,Option.some.injEq] at a
              have u:w1< n+k :=
                c.env_lt (.wire w1) (by rw[←h1,List.getD_eq_getElem _ _ W];X List.getElem_mem _)
              have v:w2< n+k :=
                c.env_lt (.wire w2) (by rw[←h2,List.getD_eq_getElem _ _ W];X List.getElem_mem _)
              X ⟨w1,w2,u,v,hM.trans h1,hN.trans h2,by rw[hI,←a.2]⟩
        · have a:pr stPre.fc (n+k) ⟨.or,[a1,a2]⟩=(s,some g'):=by
            cases hg:C.gates[t]'ht with
            | mk op0 ins0=>
              rw[hg] at hC f hev;dsimp at hC f;subst hC;subst f;X hev
          simp only[pr] at a
          cases h1:stPre.fc.getD a1 (.const false) with
          | const c1=>
            rw[h1] at a
            cases h2:stPre.fc.getD a2 (.const false) with
            | const c2=>rw[h2] at a;cases c1<;>cases c2<;>simp at a
            | wire _=>rw[h2] at a;cases c1<;>simp at a
          | wire w1=>
            rw[h1] at a
            cases h2:stPre.fc.getD a2 (.const false) with
            | const c2=>rw[h2] at a;cases c2<;>simp at a
            | wire w2=>
              rw[h2] at a;simp only[Prod.mk.injEq,Option.some.injEq] at a
              have u:w1< n+k :=
                c.env_lt (.wire w1) (by rw[←h1,List.getD_eq_getElem _ _ W];X List.getElem_mem _)
              have v:w2< n+k :=
                c.env_lt (.wire w2) (by rw[←h2,List.getD_eq_getElem _ _ W];X List.getElem_mem _)
              X ⟨w1,w2,u,v,hM.trans h1,hN.trans h2,by rw[hI,←a.2]⟩
      · intro y
        have hO:=pH C n b hG y (n+1+t);rw[r] at hO;X hO
private lemma zm {C:J} {n:ℕ} {b:Bool} (h:FanInTwo C)
  {t1 t2:ℕ} (d:t1< C.size) (p:t2< C.size) (u:t1< t2)
  (q:(p5 C n b).fb[t1]'(by rw[(pk C n b h).kept_len];X d)=true)
  (v:(p5 C n b).fb[t2]'(by rw[(pk C n b h).kept_len];X p)=true)
  {k1 k2:ℕ}
  (w:(p5 C n b).fc.getD (n+1+t1) (.const false)=.wire (n+k1))
  (x:(p5 C n b).fc.getD (n+1+t2) (.const false)=.wire (n+k2)) :
  k1< k2:=by
 have y:C.gates.length=C.size:=rfl;obtain ⟨j1,_,hA,h1,_,_,_⟩:=p4 h d q;obtain ⟨j2,_,hB,h2,_,_,_⟩:=p4 h p v;rw[w] at h1;rw[x] at h2;simp only[qw.wire.injEq] at h1 h2;have z:k1=(qF n (pn n b) (fun _=>none) (C.gates.take t1)).gates.length :=W;have hh:k2=(qF n (pn n b) (fun _=>none) (C.gates.take t2)).gates.length :=W;rw[z,hh]
 have f:C.gates.take t2=C.gates.take t1++(C.gates[t1]'d)::(C.gates.take t2).drop (t1+1):=by
  have r:(C.gates.take t2).length=t2:=by rw[List.length_take];O
  have i:(C.gates.take t2).take t1=C.gates.take t1:=by rw[List.take_take,Nat.min_eq_left (le_of_lt u)]
  have e:(C.gates.take t2).drop t1=((C.gates.take t2)[t1]'W)::(C.gates.take t2).drop (t1+1) :=
   List.drop_eq_getElem_cons W
  have k:(C.gates.take t2)[t1]'W=C.gates[t1]'d:=List.getElem_take;rw[k] at e
  conv_lhs=>rw[←List.take_append_drop t1 (C.gates.take t2),i,e]
 have a:(pn n b).length=n+1:=by simp[pn]
 have c:=zO n (pn n b) C.gates t1 d;rw[a] at c;set st1:=qF n (pn n b) (fun _=>none) (C.gates.take t1)
 have g:(p5 C n b).fb.getD t1 false=true:=by
  rw[List.getD_eq_getElem _ _ (by rw[(pk C n b h).kept_len];X d)];X q
 have j:st1.gates.length< (pZ n (fun _=>none) st1 (C.gates[t1]'d)).gates.length:=by
  cases hev:pr st1.fc (n+st1.gates.length) (C.gates[t1]'d) with
  | mk s mg=>
   have hm:mg.isSome=true:=by
    have l:=c.2;change (p5 C n b).fb.getD t1 false=_ at l;rw[g,hev] at l;X l.symm
   cases mg with
   | none=>simp at hm
   | some g'=>simp[pZ,hev]
 have t:=(j7 n (fun _=>none) ((C.gates.take t2).drop (t1+1))
  (pZ n (fun _=>none) st1 (C.gates[t1]'d))).1
 have m:qF n (pn n b) (fun _=>none) (C.gates.take t2) =
   ((C.gates.take t2).drop (t1+1)).foldl (pZ n (fun _=>none))
    (pZ n (fun _=>none) st1 (C.gates[t1]'d)):=by
  unfold qF
  conv_lhs=>rw[f]
  rw[List.foldl_append,List.foldl_cons];R
 rw[m];O
private lemma kl (b:ℕ) (a:List qw) (gs:List Gate) :
  let st:=qF b a (fun _=>none) gs
  ∀k (_:k< st.gates.length),
   ∃(t:ℕ) (_:t< gs.length),
    st.fb.getD t false=true /\
    st.fc.getD (a.length+t) (.const false)=.wire (b+k):=by
 have m:∀(c rest:List Gate) (st:z5),
   st.fb.length=c.length ->
   st.fc.length=a.length+c.length ->
   (∀k,k< st.gates.length->∃t,t< c.length /\
    st.fb.getD t false=true/\st.fc.getD (a.length+t) (.const false)=.wire (b+k)) ->
   ∀k,k< (rest.foldl (pZ b (fun _=>none)) st).gates.length ->
    ∃t,t< (c++rest).length /\
     (rest.foldl (pZ b (fun _=>none)) st).fb.getD t false=true /\
     (rest.foldl (pZ b (fun _=>none)) st).fc.getD (a.length+t) (.const false)=.wire (b+k):=by
  intro c rest
  induction rest generalizing c with
  | nil=>
   intro st _ _ h k hk;simpa using h k hk
  | cons g rest ih=>
   intro st n p q k hk;rw[List.foldl_cons] at hk ⊢;have f:=zJ b (fun _=>none) st g;have r:c++g::rest=(c++[g])++rest:=by simp
   rw[r]
   Y ih (c++[g]) (pZ b (fun _=>none) st g) (by simp[f.2.2.2,n])
    (by simp[f.2.2.1,p];O) ?_ k hk
   intro k' i
   unfold pZ at i ⊢
   cases hev:pr st.fc (b+st.gates.length) g with
   | mk s mg=>
    rw[hev] at i
    cases mg with
    | none=>
     simp only at i ⊢;obtain ⟨t,ht,j,l⟩:=q k' i;Y ⟨t,by simp;O,?_,?_⟩
     ·rw[List.getD_eq_getElem _ _ (by simp;O),List.getElem_append_left W,
       ← List.getD_eq_getElem _ _ W];X j
     ·rw[List.getD_eq_getElem _ _ (by simp;O),List.getElem_append_left W,
       ← List.getD_eq_getElem _ _ W];X l
    | some g'=>
     simp only[List.length_append,List.length_singleton] at i;by_cases u:k'< st.gates.length
     ·obtain ⟨t,ht,j,l⟩:=q k' u
      Y ⟨t,by simp;O,?_,?_⟩
      ·rw[List.getD_eq_getElem _ _ (by simp;O),List.getElem_append_left W,
        ← List.getD_eq_getElem _ _ W];X j
      ·rw[List.getD_eq_getElem _ _ (by simp;O),List.getElem_append_left W,
        ← List.getD_eq_getElem _ _ W];X l
     ·have e:k'=st.gates.length :=W
      subst e
      have d:s=.wire (b+st.gates.length) :=
       (jm st.fc (b+st.gates.length) g s g' hev).1
      Y ⟨c.length,by simp,?_,?_⟩
      ·rw[List.getD_eq_getElem _ _ (by simp[n]),List.getElem_append_right W]
       simp[n]
      ·rw[List.getD_eq_getElem _ _ (by simp[p]),List.getElem_append_right W]
       simp[p,d]
 dsimp only;intro k hk
 obtain ⟨t,ht,j,l⟩:=m [] gs { fc:=a,gates:=[],fb:=[] }
  rfl (by simp) (fun _ h=>by simp at h) k hk
 X ⟨t,by simpa using ht,j,l⟩
private lemma zD {C:J} {n:ℕ} {b:Bool} (e:FanInTwo C)
  (k:ℕ) (hk:k< (p3 C n b).size) :
  ∃(t:ℕ) (ht:t< C.size),
   (p5 C n b).fb[t]'(by rw[(pk C n b e).kept_len];X ht)=true /\
   (p5 C n b).fc.getD (n+1+t) (.const false)=.wire (n+k):=by
 have a:(pn n b).length=n+1:=by simp[pn]
 obtain ⟨t,ht,c,f⟩:=kl n (pn n b) C.gates k hk;rw[a] at f;have d:=pk C n b e;change (p5 C n b).fb.getD t false=true at c;rw[List.getD_eq_getElem _ _ (by rw[d.kept_len];X ht)] at c
 X ⟨t,ht,c,f⟩
private lemma qK {C:J} {n:ℕ} {b:Bool} (e:FanInTwo C)
  (d:z0 (p3 C n b))
  (a:∀(t:ℕ) (ht:t< C.size),
   (p5 C n b).fb[t]'(by rw[(pk C n b e).kept_len];X ht)=false ->
   (C.gates[t]'ht).op≠.not) :
  z0 C:=by
 intro g hg;obtain ⟨t,ht,rfl⟩:=List.mem_iff_getElem.1 hg;have c:=pk C n b e
 cases hkt:(p5 C n b).fb[t]'(by rw[c.kept_len];X ht) with
 | false=>X a t ht hkt
 | true=>
  obtain ⟨k,hk,_,f⟩:=c.kept_wire t ht hkt;rw[←f];X d _ (List.getElem_mem hk)
private lemma zs (C:J) {n:ℕ} (x:V n)
  (t0:ℕ) (b:t0< C.size) (v0:Bool) (t:ℕ) (ht:t< C.size) (c:t≠t0) :
  pl C x t0 v0 (n+t) =
   (C.gates[t]'ht).op.eval
    ((C.gates[t]'ht).inputs.map fun a=>if a< n+t then pl C x t0 v0 a else false):=by
 rcases Nat.lt_or_gt_of_ne c with hlt|hgt
 ·rw[pA C x t0 b v0 (n+t) W,pj C x t ht]
  congr 1
  apply List.map_congr_left;intro a _;by_cases ha:a< n+t
  ·simp only[ha,↓reduceIte]
   X (pA C x t0 b v0 a W).symm
  ·simp only[ha,↓reduceIte]
 ·X z9 C x t0 b v0 t hgt ht
private def zG (C:J) (n:ℕ) (i:ℕ):Prop :=
 ∃i':ℕ,(p5 C n true).fc.getD i (.const false)=.wire i' /\
  p0 (p3 C n true) (e1 (n-1):V n) i'=true
private lemma pM {C:J} {n i i':ℕ}
  (hw:(p5 C n true).fc.getD i (.const false)=.wire i') :
  zG C n i↔p0 (p3 C n true) (e1 (n-1):V n) i'=true:=by
 constructor
 ·rintro ⟨j,hj,a⟩;rw[hw] at hj;cases hj;X a
 ·intro a;X ⟨i',hw,a⟩
private lemma pI {C:J} {n i:ℕ} {c:Bool}
  (hc:(p5 C n true).fc.getD i (.const false)=.const c) :
  ¬zG C n i:=by
 rintro ⟨_,hw,_⟩;rw[hc] at hw;cases hw
private lemma zE {C:J} {n:ℕ} (hn:1<=n) :
  zG C n (n-1):=by
 Y ⟨n-1,pd C n true (n-1) W,?_⟩;rw[p7 _ (e1 (n-1):V n) (n-1) W];simp[e1]
private lemma ja {C:J} {n i:ℕ} (hi:i< n-1) :
  ¬zG C n i:=by
 rintro ⟨i',hw,a⟩
 rw[pd C n true i W] at hw;cases hw;rw[p7 _ (e1 (n-1):V n) i W] at a;simp[e1] at a;O
private lemma jK {C:J} {n:ℕ} (e:FanInTwo C) (hn:1<=n) {i:ℕ}
  (hi:zG C n i) :
  p0 C (e2 (n-1) n:Fin (n+1)->Bool) i=true:=by
 obtain ⟨i',hw,b⟩:=hi;have c:=pH C n true e (e1 (n-1):V n) i;rw[hw] at c
 have a:Fin.snoc (e1 (n-1):V n) true=(e2 (n-1) n:Fin (n+1)->Bool):=by
  funext j
  by_cases hj:j.val< n
  ·have:j=Fin.castSucc ⟨j.val,hj⟩:=Fin.ext rfl
   rw[this,Fin.snoc_castSucc];simp only[e1,e2,Fin.val_castSucc];apply Bool.eq_iff_iff.2;simp;O
  ·have d:j=Fin.last n:=Fin.ext (by have:=j.isLt;simp;O)
   rw[d,Fin.snoc_last];simp[e2]
 rw[a] at c;X c.symm.trans b
private lemma qL {C:J} {n:ℕ}
  (e:IsMinimalCircuit (n+1) C) (hW:z0 C) (hn:1<=n)
  (hO:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2)
  {a hstar u:ℕ} (hG:a< C.size) (c:hstar< C.size) (hX:a< hstar)
  (q:∀(t:ℕ) (ht:t< C.size),
   (p5 C n true).fb[t]'(by rw[(pk C n true e.1).kept_len];X ht)=false ↔
   (t=a\/t=hstar))
  (f:(p5 C n true).fc.getD (n+1+a) (.const false)=.const true)
  (r:(C.gates[hstar]'c).op=.and)
  (s:(C.gates[hstar]'c).inputs=[n+1+a,u] \/
       (C.gates[hstar]'c).inputs=[u,n+1+a])
  (v:u< n+1+hstar)
  (m:(p5 C n true).fc.getD (n+1+hstar) (.const false) =
       (p5 C n true).fc.getD u (.const false))
  (w:∀(k:ℕ) (hk:k< (p3 C n true).size),
   p0 (p3 C n true) (e1 (n-1):V n) (n+k)=true ->
   ((p3 C n true).gates[k]'hk).op=.or)
  (x:Fin (n+1)->Bool) (hx:x ⟨n-1,by O⟩=true)
  (y:p0 C x (n+1+a)=true\/¬zG C n u) :
  ∀i< n+1+C.size,zG C n i->p0 C x i=true:=by
 set st:=p5 C n true;set D:=p3 C n true;have z:=pk C n true e.1;intro i
 induction i using Nat.strong_induction_on with
 | ind i ih=>
  intro hP j;by_cases hY:i< n+1
  ·by_cases g:i=n
   ·rw[g] at j
    X absurd j (pI (p9 C n true e.1))
   ·by_cases hh:i< n-1
    ·X absurd j (ja hh)
    ·have hA:i=n-1 :=W
     rw[hA,p7 C x (n-1) W];X hx
  ·set t:=i-(n+1)
   have ht:t< C.size :=W;have g:i=n+1+t :=W;rw[g] at j ⊢;by_cases hJ:t=a
   ·rw[hJ] at j;X absurd j (pI f)
   ·by_cases hK:t=hstar
    ·rw[hK] at j ⊢
     have hL:zG C n u:=by
      obtain ⟨i',hw,hH⟩:=j;rw[m] at hw;X ⟨i',hw,hH⟩
     have hQ:p0 C x (n+1+a)=true:=by
      rcases y with h1|h2
      ·X h1
      ·X absurd hL h2
     have hR:p0 C x u=true:=ih u W W hL;rw[pj C x hstar c,r]
     rcases s with h|h<;>rw[h] <;>
      simp[GateOp.eval,show n+1+a< n+1+hstar by O,v,hQ,hR]
    ·have l:st.fb[t]'(by rw[z.kept_len];X ht)=true:=by
      cases hk:st.fb[t]'(by rw[z.kept_len];X ht) with
      | true=>rfl
      | false=>
       rcases (q t ht).1 hk with rfl|rfl
       ·X absurd rfl hJ
       ·X absurd rfl hK
     obtain ⟨k,hk,_,p,hB,hC,_⟩:=p4 e.1 ht l;have hF:p0 D (e1 (n-1):V n) (n+k)=true:=(pM p).1 j;have d:(D.gates[k]'hk).op=.or:=w k hk hF;have b:(C.gates[t]'ht).op=.or:=hB.symm.trans d;have hD:=pc e hO t ht;rcases hD with ⟨hE,_,_,_⟩|⟨_,a1,a2,h,hM,hN,_⟩
     ·rw[b] at hE;cases hE
     ·obtain ⟨w1,w2,hS,hT,hU,hV,hI⟩:=hC .or a1 a2 (ir rfl) b h hM hN
      rw[pj D (e1 (n-1):V n) k hk,d,hI] at hF
      simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
       id_eq,Bool.or_false,hS,hT,↓reduceIte,Bool.or_eq_true] at hF
      rw[pj C x t ht,b,h]
      simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
       id_eq,Bool.or_false,hM,hN,↓reduceIte,Bool.or_eq_true]
      rcases hF with h1|h2
      ·X il (ih a1 W W ((pM hU).2 h1))
      ·X ir (ih a2 W W ((pM hV).2 h2))
private lemma jt {C:J} {n:ℕ}
  (c:IsMinimalCircuit (n+1) C) (hK:z0 C) (hn:1<=n)
  (hT:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2)
  (z:cF (n+1) C (e1 (n-1):Fin (n+1)->Bool)=false)
  {g hstar:ℕ} (hG:g< C.size) (hH:hstar< C.size) (hX:g< hstar)
  (s:∀(t:ℕ) (ht:t< C.size),
   (p5 C n true).fb[t]'(by rw[(pk C n true c.1).kept_len];X ht)=false ↔
   (t=g\/t=hstar))
  (b:∀(k:ℕ) (hk:k< (p3 C n true).size),
   ((p3 C n true).gates[k]'hk).op=.and ->
   ∀a,pC n k a ((p3 C n true).gates[k]'hk) ->
    p0 (p3 C n true) (e1 (n-1):V n) a=false) :
  ∀(t:ℕ),hstar< t->t< C.size->p0 C (e1 (n-1):Fin (n+1)->Bool) (n+1+t)=false:=by
 set st:=p5 C n true;set D:=p3 C n true;have l:=pk C n true c.1
 suffices hh:∀d (t:ℕ),C.size-t<=d->hstar< t->t< C.size ->
   p0 C (e1 (n-1):Fin (n+1)->Bool) (n+1+t)=false by
  intro t hL u;X hh (C.size-t) t le_rfl hL u
 intro d
 induction d with
 | zero=>intro t hU _ u;O
 | succ d ih=>
  intro t hU hL u
  cases hvt:p0 C (e1 (n-1):Fin (n+1)->Bool) (n+1+t) with
  | false=>rfl
  | true=>
   exfalso;rcases pY c t u with hout|⟨r,hr,hY,h⟩
   ·rw[←hout,←pb] at hvt
    rw[z] at hvt;cases hvt
   ·have m:st.fb[t]'(by rw[l.kept_len];X u)=true:=by
     cases hk:st.fb[t]'(by rw[l.kept_len];X u) with
     | true=>rfl
     | false=>rcases (s t u).1 hk with rfl|rfl<;>O
    have p:st.fb[r]'(by rw[l.kept_len];X hr)=true:=by
     cases hk:st.fb[r]'(by rw[l.kept_len];X hr) with
     | true=>rfl
     | false=>rcases (s r hr).1 hk with rfl|rfl<;>O
    obtain ⟨kt,hZ,_,e,_,_,_⟩:=p4 c.1 u m;obtain ⟨kr,hF,_,_,hA,hB,_⟩:=p4 c.1 hr p
    have hM:p0 D (e1 (n-1):V n) (n+kt)=true:=by
     have w:∀j:Fin (n+1),(e1 (n-1):Fin (n+1)->Bool) j=true ->
       (e2 (n-1) n:Fin (n+1)->Bool) j=true:=by
      intro j hj;simp only[e1,e2,decide_eq_true_eq] at hj ⊢;X il hj
     have hm:=zz C c.1 hK w (n+1+t) hvt;have hN:=pH C n true c.1 (e1 (n-1):V n) (n+1+t)
     have hC:Fin.snoc (e1 (n-1):V n) true=(e2 (n-1) n:Fin (n+1)->Bool):=by
      funext j
      by_cases hj:j.val< n
      ·have:j=Fin.castSucc ⟨j.val,hj⟩:=Fin.ext rfl
       rw[this,Fin.snoc_castSucc];simp only[e1,e2,Fin.val_castSucc];apply Bool.eq_iff_iff.2;simp;O
      ·have:j=Fin.last n:=Fin.ext (by have:=j.isLt;simp;O)
       rw[this,Fin.snoc_last];simp[e2]
     rw[e,hC] at hN;X hN.trans hm
    have hD:=pc c hT r hr;rcases hD with ⟨hI,_,_,_⟩|⟨x,a1,a2,q,hO,hP,_⟩
    ·X absurd hI (hK _ (List.getElem_mem hr))
    ·rcases x with hop_and|hop_or
     ·obtain ⟨w1,w2,hV,hW,hQ,hR,hJ⟩:=hB .and a1 a2 (il rfl) hop_and q hO hP
      have hE:=h.1;simp only[pa,hop_and,q,List.mem_cons,List.not_mem_nil,or_false] at hE;have f:(D.gates[kr]'hF).op=.and:=hA.trans hop_and;have v:(D.gates[kr]'hF).inputs=[w1,w2]:=hJ;rcases hE with rfl|rfl
      ·rw[e] at hQ;cases hQ
       have i:=b kr hF f (n+kt)
        ⟨by simp[pa,f,v],hV⟩
       rw[hM] at i;cases i
      ·rw[e] at hR;cases hR
       have i:=b kr hF f (n+kt)
        ⟨by simp[pa,f,v],hW⟩
       rw[hM] at i;cases i
     ·have hS:p0 C (e1 (n-1):Fin (n+1)->Bool) (n+1+r)=true:=by
       rw[pj C (e1 (n-1):Fin (n+1)->Bool) r hr,hop_or,q]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
        id_eq,Bool.or_false,hO,hP,↓reduceIte,Bool.or_eq_true]
       have hE:=h.1;simp only[pa,hop_or,q,List.mem_cons,List.not_mem_nil,or_false] at hE;rcases hE with rfl|rfl
       ·X il hvt
       ·X ir hvt
      have y:=ih r W W hr;rw[y] at hS;cases hS
private lemma qI {C:J} {n:ℕ} (j:FanInTwo C)
  {b hstar:ℕ}
  (e:∀(t:ℕ) (ht:t< C.size),pC (n+1) t n (C.gates[t]'ht)↔t=b)
  (f:∀(t:ℕ) (ht:t< C.size),pC (n+1) t (n+1+b) (C.gates[t]'ht)↔t=hstar)
  (y:V n) :
  ∀i< n+1+hstar,i≠n->i≠n+1+b ->
   p0 C (Fin.snoc y false) i=p0 C (Fin.snoc y true) i:=by
 intro i
 induction i using Nat.strong_induction_on with
 | ind i ih=>
  intro k g h;by_cases p:i< n+1
  ·have hi:i< n :=W
   rw[p7 C _ i W,p7 C _ i W]
   have:(⟨i,by O⟩:Fin (n+1))=Fin.castSucc ⟨i,hi⟩:=Fin.ext rfl
   rw[this,Fin.snoc_castSucc,Fin.snoc_castSucc]
  ·by_cases q:i< n+1+C.size
   ·set t:=i-(n+1)
    have ht:t< C.size :=W;have d:i=n+1+t :=W;rw[d,pj C _ t ht,pj C _ t ht];apply zy _ (j _ (List.getElem_mem ht));intro a ha;by_cases c:a< n+1+t
    ·simp only[c,↓reduceIte]
     have l:a≠n:=by
      intro rfl
      have:=(e t ht).1 ⟨ha,c⟩
      O
     have m:a≠n+1+b:=by
      intro rfl
      have:=(f t ht).1 ⟨ha,c⟩
      O
     X ih a W W l m
    ·simp only[c,↓reduceIte]
   ·rw[z3 C _ i W,z3 C _ i W]
private lemma qW {C:J} {n:ℕ}
  (q:IsMinimalCircuit (n+1) C) (Hc:z0 C) (hn:1<=n)
  (Hd:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2)
  (hT:cF (n+1) C (e1 (n-1):Fin (n+1)->Bool)=false)
  {i b u:ℕ} (hK:i< C.size) (y:b< C.size) (Ho:i< b)
  (Hf:∀(t:ℕ) (ht:t< C.size),pC (n+1) t n (C.gates[t]'ht)↔t=i)
  (Hg:∀(t:ℕ) (ht:t< C.size),pC (n+1) t (n+1+i) (C.gates[t]'ht)↔t=b)
  (hD:∀(t:ℕ) (ht:t< C.size),
   (p5 C n true).fb[t]'(by rw[(pk C n true q.1).kept_len];X ht)=false ↔
   (t=i\/t=b))
  (hA:(p5 C n true).fc.getD (n+1+i) (.const false)=.const true)
  (hL:∀a,pC (n+1) i a (C.gates[i]'hK)->¬zG C n a)
  (hU:(C.gates[b]'y).op=.and)
  (hV:(C.gates[b]'y).inputs=[n+1+i,u] \/
       (C.gates[b]'y).inputs=[u,n+1+i])
  (hW:u< n+1+b)
  (e:∀(k:ℕ) (hk:k< (p3 C n true).size),
   ((p3 C n true).gates[k]'hk).op=.and ->
   ∀a,pC n k a ((p3 C n true).gates[k]'hk) ->
    p0 (p3 C n true) (e1 (n-1):V n) a=false) :
  (∀t (ht:t< C.size),b< t->∀a,pC (n+1) t a (C.gates[t]'ht) ->
   a< n+1+b->¬zG C n a) /\
  (∀t (ht:t< C.size),t< b->zG C n (n+1+t)->n+1+t<=u) /\
  (∀tu (_:tu< b),u=n+1+tu->zG C n u ->
   ∀t (ht:t< C.size),pC (n+1) t u (C.gates[t]'ht)↔t=b):=by
 set st:=p5 C n true;set D:=p3 C n true;have hI:=jt q Hc hn Hd hT hK y Ho hD e;have hJ:=pk C n true q.1
 have H2:Fin.snoc (e1 (n-1):V n) false=(e1 (n-1):Fin (n+1)->Bool):=by
  funext j
  by_cases hj:j.val< n
  ·have:j=Fin.castSucc ⟨j.val,hj⟩:=Fin.ext rfl
   rw[this,Fin.snoc_castSucc];R
  ·have:j=Fin.last n:=Fin.ext (by have:=j.isLt;simp;O)
   rw[this,Fin.snoc_last];simp[e1];O
 have H3:Fin.snoc (e1 (n-1):V n) true=(e2 (n-1) n:Fin (n+1)->Bool):=by
  funext j
  by_cases hj:j.val< n
  ·have:j=Fin.castSucc ⟨j.val,hj⟩:=Fin.ext rfl
   rw[this,Fin.snoc_castSucc];simp only[e1,e2,Fin.val_castSucc];apply Bool.eq_iff_iff.2;simp;O
  ·have:j=Fin.last n:=Fin.ext (by have:=j.isLt;simp;O)
   rw[this,Fin.snoc_last];simp[e2]
 have v:∀a< n+1+b,zG C n a->p0 C (e1 (n-1):Fin (n+1)->Bool) a=true:=by
  intro a ha H7;have Hp:a≠n:=fun h=>pI (p9 C n true q.1) (h▸H7);have Hq:a≠n+1+i:=fun h=>pI hA (h▸H7);have H9:=qI q.1 Hf Hg (e1 (n-1):V n) a ha Hp Hq;rw[H2,H3] at H9;rw[H9];X jK q.1 hn H7
 have hC:∀t (ht:t< C.size),b< t->∀a,pC (n+1) t a (C.gates[t]'ht) ->
   a< n+1+b->¬zG C n a:=by
  intro t ht Hh a c ha H7;have hX:p0 C (e1 (n-1):Fin (n+1)->Bool) a=true:=v a ha H7
  have z:st.fb[t]'(by rw[hJ.kept_len];X ht)=true:=by
   cases hk:st.fb[t]'(by rw[hJ.kept_len];X ht) with
   | true=>rfl
   | false=>rcases (hD t ht).1 hk with rfl|rfl<;>O
  obtain ⟨kt,hM,_,_,hE,hF,_⟩:=p4 q.1 ht z;have hB:=pc q Hd t ht;rcases hB with ⟨hN,_,_,_⟩|⟨w,a1,a2,g,hY,hZ,_⟩
  ·X absurd hN (Hc _ (List.getElem_mem ht))
  ·rcases w with hop_and|hop_or
   ·obtain ⟨w1,w2,hQ,hR,hG,hH,hh⟩:=hF .and a1 a2 (il rfl) hop_and g hY hZ
    have x:=c.1;simp only[pa,hop_and,g,List.mem_cons,List.not_mem_nil,or_false] at x;have f:(D.gates[kt]'hM).op=.and:=hE.trans hop_and;have s:(D.gates[kt]'hM).inputs=[w1,w2]:=hh;obtain ⟨a',m,p⟩:=H7;rcases x with rfl|rfl
    ·rw[m] at hG;cases hG
     have l:=e kt hM f w1 ⟨by simp[pa,f,s],hQ⟩
     rw[p] at l;cases l
    ·rw[m] at hH;cases hH
     have l:=e kt hM f w2 ⟨by simp[pa,f,s],hR⟩
     rw[p] at l;cases l
   ·have Hl:p0 C (e1 (n-1):Fin (n+1)->Bool) (n+1+t)=true:=by
     rw[pj C (e1 (n-1):Fin (n+1)->Bool) t ht,hop_or,g]
     simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
      id_eq,Bool.or_false,hY,hZ,↓reduceIte,Bool.or_eq_true]
     have x:=c.1;simp only[pa,hop_or,g,List.mem_cons,List.not_mem_nil,or_false] at x;rcases x with rfl|rfl
     ·X il hX
     ·X ir hX
    rw[hI t Hh ht] at Hl;cases Hl
 have hO:∀t (ht:t< C.size),t< b->zG C n (n+1+t)->n+1+t<=u:=by
  suffices Ha:∀d (t:ℕ),b-t<=d->t< C.size->t< b ->
    zG C n (n+1+t)->n+1+t<=u by
   intro t ht Hb hP;X Ha (b-t) t le_rfl ht Hb hP
  intro d
  induction d with
  | zero=>intro t Hr _ Hb _;O
  | succ d ih=>
   intro t Hr ht Hb hP;have Hv:t≠i:=fun h=>pI hA (h▸hP);rcases pY q t ht with hout|⟨r,hr,Hw,c⟩
   ·exfalso
    have h1:=v (n+1+t) W hP;rw[←hout,←pb,hT] at h1;cases h1
   ·by_cases Hs:r=b
    ·subst Hs
     have x:=c.1
     rcases hV with g|g <;>
      simp only[pa,hU,g,List.mem_cons,List.not_mem_nil,or_false] at x
     ·rcases x with h1|h2<;>O
     ·rcases x with h1|h2<;>O
    ·by_cases Hi:b< r
     ·exfalso;X hC r hr Hi (n+1+t) c W hP
     ·have Hj:r< b :=W
      have hS:st.fb[r]'(by rw[hJ.kept_len];X hr)=true:=by
       cases hk:st.fb[r]'(by rw[hJ.kept_len];X hr) with
       | true=>rfl
       | false=>
        rcases (hD r hr).1 hk with rfl|rfl
        ·X absurd hP (hL (n+1+t) c)
        ·O
      obtain ⟨kr,H8,_,H4,H0,H1,_⟩:=p4 q.1 hr hS;have hB:=pc q Hd r hr;rcases hB with ⟨hN,_,_,_⟩|⟨w,a1,a2,g,hY,hZ,_⟩
      ·X absurd hN (Hc _ (List.getElem_mem hr))
      ·rcases w with hop_and|hop_or
       ·exfalso
        obtain ⟨w1,w2,hQ,hR,hG,hH,hh⟩:=H1 .and a1 a2 (il rfl) hop_and g hY hZ;have x:=c.1;simp only[pa,hop_and,g,List.mem_cons,List.not_mem_nil,or_false] at x;have f:(D.gates[kr]'H8).op=.and:=H0.trans hop_and;have s:(D.gates[kr]'H8).inputs=[w1,w2]:=hh;obtain ⟨a',m,p⟩:=hP;rcases x with rfl|rfl
        ·rw[m] at hG;cases hG
         have l:=e kr H8 f w1 ⟨by simp[pa,f,s],hQ⟩
         rw[p] at l;cases l
        ·rw[m] at hH;cases hH
         have l:=e kr H8 f w2 ⟨by simp[pa,f,s],hR⟩
         rw[p] at l;cases l
       ·have Ht:zG C n (n+1+r):=by
         rw[pM H4];obtain ⟨w1,w2,hQ,hR,hG,hH,hh⟩:=H1 .or a1 a2 (ir rfl) hop_or g hY hZ;have H5:(D.gates[kr]'H8).op=.or:=H0.trans hop_or;rw[pj D (e1 (n-1):V n) kr H8,H5,hh]
         simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
          id_eq,Bool.or_false,hQ,hR,↓reduceIte,Bool.or_eq_true]
         have x:=c.1;simp only[pa,hop_or,g,List.mem_cons,List.not_mem_nil,or_false] at x;obtain ⟨a',m,p⟩:=hP;rcases x with rfl|rfl
         ·rw[m] at hG;cases hG;X il p
         ·rw[m] at hH;cases hH;X ir p
        have Hm:=ih r W hr Hj Ht;O
 Y ⟨hC,hO,?_⟩;intro tu Hx Hn He t ht
 constructor
 ·intro c
  by_cases Hh:b< t
  ·X absurd He (hC t ht Hh u c hW)
  ·by_cases Hu:t=b
   ·X Hu
   ·exfalso
    have Hb:t< b :=W;have Hk:tu< t:=by have:=c.2;O
    have z:st.fb[t]'(by rw[hJ.kept_len];X ht)=true:=by
     cases hk:st.fb[t]'(by rw[hJ.kept_len];X ht) with
     | true=>rfl
     | false=>
      rcases (hD t ht).1 hk with rfl|rfl
      ·X absurd He (hL u c)
      ·O
    obtain ⟨kt,hM,_,H6,hE,hF,_⟩:=p4 q.1 ht z;have hB:=pc q Hd t ht;rcases hB with ⟨hN,_,_,_⟩|⟨w,a1,a2,g,hY,hZ,_⟩
    ·X absurd hN (Hc _ (List.getElem_mem ht))
    ·rcases w with hop_and|hop_or
     ·obtain ⟨w1,w2,hQ,hR,hG,hH,hh⟩:=hF .and a1 a2 (il rfl) hop_and g hY hZ
      have x:=c.1;simp only[pa,hop_and,g,List.mem_cons,List.not_mem_nil,or_false] at x;have f:(D.gates[kt]'hM).op=.and:=hE.trans hop_and;have s:(D.gates[kt]'hM).inputs=[w1,w2]:=hh;obtain ⟨a',m,p⟩:=He;rcases x with rfl|rfl
      ·rw[m] at hG;cases hG
       have l:=e kt hM f w1 ⟨by simp[pa,f,s],hQ⟩
       rw[p] at l;cases l
      ·rw[m] at hH;cases hH
       have l:=e kt hM f w2 ⟨by simp[pa,f,s],hR⟩
       rw[p] at l;cases l
     ·have hP:zG C n (n+1+t):=by
       rw[pM H6];obtain ⟨w1,w2,hQ,hR,hG,hH,hh⟩:=hF .or a1 a2 (ir rfl) hop_or g hY hZ;have H5:(D.gates[kt]'hM).op=.or:=hE.trans hop_or;rw[pj D (e1 (n-1):V n) kt hM,H5,hh]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
        id_eq,Bool.or_false,hQ,hR,↓reduceIte,Bool.or_eq_true]
       have x:=c.1;simp only[pa,hop_or,g,List.mem_cons,List.not_mem_nil,or_false] at x;obtain ⟨a',m,p⟩:=He;rcases x with rfl|rfl
       ·rw[m] at hG;cases hG;X il p
       ·rw[m] at hH;cases hH;X ir p
      have:=hO t ht Hb hP
      O
 ·rintro rfl
  Y ⟨?_,hW⟩;rcases hV with g|g<;>simp[pa,hU,g]
private lemma j8 {C:J} {n:ℕ}
  (l:IsMinimalCircuit (n+1) C) (hL:z0 C) (hn:2<=n)
  (hS:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2)
  {b hstar u:ℕ} (hI:b< C.size) (c:hstar< C.size) (hW:b< hstar)
  (y:∀(t:ℕ) (ht:t< C.size),
   (p5 C n true).fb[t]'(by rw[(pk C n true l.1).kept_len];X ht)=false ↔
   (t=b\/t=hstar))
  (p:(p5 C n true).fc.getD (n+1+b) (.const false)=.const true)
  (z:(C.gates[hstar]'c).op=.and)
  (hh:(C.gates[hstar]'c).inputs=[n+1+b,u] \/
       (C.gates[hstar]'c).inputs=[u,n+1+b])
  (hA:u< n+1+hstar)
  (hB:∀(k:ℕ) (hk:k< (p3 C n true).size),
   p0 (p3 C n true) (e1 (n-1):V n) (n+k)=true ->
   ((p3 C n true).gates[k]'hk).op=.or)
  (e:p0 C (e2 (n-2) (n-1):Fin (n+1)->Bool) (n+1+b)=false)
  (f:∀(t:ℕ) (ht:t< C.size),zG C n (n+1+t)->t≠b->t≠hstar ->
   ∀a,pC (n+1) t a (C.gates[t]'ht)->¬zG C n a ->
    p0 C (e2 (n-2) (n-1):Fin (n+1)->Bool) a=false) :
  ∀i< n+1+C.size,zG C n i ->
   p0 C (e2 (n-2) (n-1):Fin (n+1)->Bool) i =
    p0 C (e1 (n-1):Fin (n+1)->Bool) i:=by
 set st:=p5 C n true;set D:=p3 C n true;have hC:=pk C n true l.1
 have m:∀j:Fin (n+1),(e1 (n-1):Fin (n+1)->Bool) j=true ->
   (e2 (n-2) (n-1):Fin (n+1)->Bool) j=true:=by
  intro j hj;simp only[e1,e2,decide_eq_true_eq] at hj ⊢;X ir hj
 have g:p0 C (e1 (n-1):Fin (n+1)->Bool) (n+1+b)=false:=by
  cases hv:p0 C (e1 (n-1):Fin (n+1)->Bool) (n+1+b) with
  | false=>rfl
  | true=>
   have:=zz C l.1 hL m (n+1+b) hv
   rw[e] at this;cases this
 intro i
 induction i using Nat.strong_induction_on with
 | ind i ih=>
  intro hT v;by_cases hX:i< n+1
  ·by_cases q:i=n
   ·rw[q] at v
    X absurd v (pI (p9 C n true l.1))
   ·by_cases hD:i< n-1
    ·X absurd v (ja hD)
    ·have hE:i=n-1 :=W
     rw[hE,p7 C _ (n-1) W,p7 C _ (n-1) W];simp[e2,e1]
  ·set t:=i-(n+1)
   have ht:t< C.size :=W;have q:i=n+1+t :=W;rw[q] at v ⊢;by_cases hM:t=b
   ·rw[hM] at v;X absurd v (pI p)
   ·by_cases hN:t=hstar
    ·rw[hN,pj C _ hstar c,pj C _ hstar c,z]
     rcases hh with r|r<;>rw[r] <;>
      simp[GateOp.eval,show n+1+b< n+1+hstar by O,hA,e,g]
    ·have s:st.fb[t]'(by rw[hC.kept_len];X ht)=true:=by
      cases hk:st.fb[t]'(by rw[hC.kept_len];X ht) with
      | true=>rfl
      | false=>rcases (y t ht).1 hk with rfl|rfl<;>O
     obtain ⟨k,hk,_,w,hF,_,_⟩:=p4 l.1 ht s;have hU:p0 D (e1 (n-1):V n) (n+k)=true:=(pM w).1 v;have d:(C.gates[t]'ht).op=.or:=hF.symm.trans (hB k hk hU);have hG:=pc l hS t ht;rcases hG with ⟨hH,_,_,_⟩|⟨_,a1,a2,r,hO,hP,_⟩
     ·rw[d] at hH;cases hH
     ·have h:∀a,(a=a1\/a=a2)->a< n+1+t ->
        p0 C (e2 (n-2) (n-1):Fin (n+1)->Bool) a =
         p0 C (e1 (n-1):Fin (n+1)->Bool) a:=by
       intro a hJ hK;by_cases hQ:zG C n a
       ·X ih a W W hQ
       ·have x:pC (n+1) t a (C.gates[t]'ht) :=
         ⟨by simp[pa,d,r,hJ],hK⟩
        have hR:=f t ht v hM hN a x hQ
        have hV:p0 C (e1 (n-1):Fin (n+1)->Bool) a=false:=by
         cases hv:p0 C (e1 (n-1):Fin (n+1)->Bool) a with
         | false=>rfl
         | true=>
          have:=zz C l.1 hL m a hv
          rw[hR] at this;cases this
        rw[hR,hV]
      rw[pj C _ t ht,pj C _ t ht,d,r]
      simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
       id_eq,Bool.or_false,hO,hP,↓reduceIte]
      rw[h a1 (il rfl) hO,h a2 (ir rfl) hP]
private def pD (r c:ℕ) (x:Fin (2*r+1)->Bool):Bool :=
 decide (∃k:Fin (2*r+1),(k.val+1=c\/k.val=c+1)/\x k=true)
private def jg (r:ℕ) (f:(Fin (2*r+1)->Bool)->Bool):Prop :=
 ∃c:ℕ,c%2=1/\c< 2*r/\f=pD r c
private def qa (r:ℕ) (P:Finset ℕ) (x:Fin (2*r+1)->Bool):Bool :=
 decide (∃c∈P,∃(hc:c< 2*r+1),x ⟨c,hc⟩=true/\pD r c x=true)
private def pX (r:ℕ) (f:(Fin (2*r+1)->Bool)->Bool):Prop :=
 ∃P:Finset ℕ,P.Nonempty/\(∀c∈P,c%2=1/\c< 2*r)/\f=qa r P
private def zb (r:ℕ) (C:J):Prop :=
 z0 C /\
 (∀t (_:t< C.size),jg r (p8 C t)\/pX r (p8 C t)) /\
 (∀t (_:t< C.size) (P:Finset ℕ),
  P.Nonempty->(∀c∈P,c%2=1/\c< 2*r)->p8 C t=qa r P ->
  ∀c∈P,pl C (pe (c-1):Fin (2*r+1)->Bool) t false C.output=false)
private lemma pG {r c:ℕ} {x:Fin (2*r+1)->Bool} :
  pD r c x=true↔∃k:Fin (2*r+1),(k.val+1=c\/k.val=c+1)/\x k=true:=by
 simp[pD]
private lemma pt {r c a:ℕ} (d:1<=c) (e:c< 2*r) (ha:a< 2*r+1) :
  pD r c (e1 a)=true↔a+1=c\/a=c+1:=by
 rw[pG]
 constructor
 ·rintro ⟨k,hk,b⟩
  simp only[e1,decide_eq_true_eq] at b;subst b;X hk
 ·intro h
  X ⟨⟨a,ha⟩,h,by simp[e1]⟩
private lemma qp {r:ℕ} {P:Finset ℕ} {x:Fin (2*r+1)->Bool} :
  qa r P x=true ↔
   ∃c∈P,∃(hc:c< 2*r+1),x ⟨c,hc⟩=true/\pD r c x=true:=by
 simp[qa]
private lemma zF {r:ℕ} {P:Finset ℕ} {x:Fin (2*r+1)->Bool}
  (hx:qa r P x=true) :
  pq (2*r+1) x=true:=by
 rw[qp] at hx;obtain ⟨c,_,hc,a,b⟩:=hx;rw[pG] at b;obtain ⟨k,hk,d⟩:=b;rw[px];rcases hk with h1|h2
 ·X ⟨k,⟨c,hc⟩,h1,d,a⟩
 ·X ⟨⟨c,hc⟩,k,h2.symm,a,d⟩
private lemma q2 {r:ℕ} {P:Finset ℕ} (a:ℕ) :
  qa r P (e1 a)=false:=by
 cases hv:qa r P (e1 a) with
 | false=>rfl
 | true=>
  have:=zF hv
  rw[pW] at this;cases this
private lemma q7 {r:ℕ} {P:Finset ℕ}
  (hP:∀c∈P,c%2=1/\c< 2*r) {c:ℕ} (a:c%2=1) (e:c< 2*r) :
  qa r P (pe (c-1))=true↔c∈P:=by
 rw[qp]
 constructor
 ·rintro ⟨d,f,g,h,k⟩
  have b:=(hP d f).1;simp only[pe,e2,decide_eq_true_eq] at h;have i:d=c :=W;subst i;X f
 ·intro j
  Y ⟨c,j,by O,by simp[pe,e2];O,?_⟩
  rw[pG];X ⟨⟨c-1,by O⟩,il (by dsimp;O),by simp[pe,e2]⟩
private lemma zL {r:ℕ} {P:Finset ℕ}
  (hP:∀c∈P,c%2=1/\c< 2*r) {c:ℕ} (a:c%2=1) (e:c< 2*r) :
  qa r P (pe c)=true↔c∈P:=by
 rw[qp]
 constructor
 ·rintro ⟨d,f,g,h,k⟩
  have b:=(hP d f).1;simp only[pe,e2,decide_eq_true_eq] at h;have i:d=c :=W;subst i;X f
 ·intro j
  Y ⟨c,j,by O,by simp[pe,e2],?_⟩
  rw[pG];X ⟨⟨c+1,by O⟩,ir rfl,by simp[pe,e2]⟩
private lemma zY (r:ℕ) (x:Fin (2*r+1)->Bool) :
  pq (2*r+1) x=qa r ((Finset.range (2*r)).filter (fun c=>c%2=1)) x:=by
 apply Bool.eq_iff_iff.2;rw[px,qp]
 constructor
 ·rintro ⟨i,j,f,g,h⟩
  have d:i.val< 2*r+1:=i.isLt;have e:j.val< 2*r+1:=j.isLt;by_cases a:i.val%2=1
  ·Y ⟨i.val,Finset.mem_filter.2 ⟨Finset.mem_range.2 W,a⟩,d,g,?_⟩
   rw[pG];X ⟨j,ir f.symm,h⟩
  ·have b:j.val%2=1 :=W
   Y ⟨j.val,Finset.mem_filter.2 ⟨Finset.mem_range.2 W,b⟩,e,h,?_⟩;rw[pG];X ⟨i,il f,g⟩
 ·rintro ⟨c,_,hc,l,m⟩
  rw[pG] at m;obtain ⟨k,hk,n⟩:=m;rcases hk with h1|h2
  ·X ⟨k,⟨c,hc⟩,h1,n,l⟩
  ·X ⟨⟨c,hc⟩,k,h2.symm,l,n⟩
private lemma jS {r c j:ℕ} (b:c%2=1) (a:c< 2*r) (hj:j< 2*r+1) :
  pD r c≠(fun x:Fin (2*r+1)->Bool=>x ⟨j,hj⟩):=by
 intro d;have h1:=cf d (e1 (c-1));have h2:=cf d (e1 (c+1));rw[(pt W a W).2 (il W)] at h1;rw[(pt W a W).2 (ir rfl)] at h2;simp only[e1,decide_eq_true_eq] at h1 h2
 have:j=c-1:=by
  have:true=decide (j=c-1):=h1
  X of_decide_eq_true this.symm
 have:j=c+1:=by
  have:true=decide (j=c+1):=h2
  X of_decide_eq_true this.symm
 O
private lemma qt {r j:ℕ} {P:Finset ℕ} (hj:j< 2*r+1) :
  qa r P≠(fun x:Fin (2*r+1)->Bool=>x ⟨j,hj⟩):=by
 intro a;have h:=cf a (e1 j);rw[q2] at h;simp[e1] at h
private lemma q3 {r c:ℕ} {P:Finset ℕ} (b:c%2=1) (a:c< 2*r) :
  pD r c≠qa r P:=by
 intro d;have h:=cf d (e1 (c-1));rw[(pt W a W).2 (il W),q2] at h;cases h
private lemma qH {r:ℕ} {C:J} (d:zb r C)
  (w:ℕ) (hw:w< 2*r+1+C.size) :
  (∃(j:ℕ) (hj:j< 2*r+1),w=j/\(fun x:Fin (2*r+1)->Bool=>p0 C x w)=fun x=>x ⟨j,hj⟩) \/
  (∃(t:ℕ) (_:t< C.size),w=2*r+1+t/\jg r (fun x=>p0 C x w)) \/
  (∃(t:ℕ) (_:t< C.size),w=2*r+1+t/\pX r (fun x=>p0 C x w)):=by
 by_cases e:w< 2*r+1
 ·left
  X ⟨w,e,rfl,funext fun x=>p7 C x w e⟩
 ·right
  set t:=w-(2*r+1);have ht:t< C.size :=W;have a:w=2*r+1+t :=W;rcases d.2.1 t ht with c|b
  ·left;X ⟨t,ht,a,by rw[a];X c⟩
  ·right;X ⟨t,ht,a,by rw[a];X b⟩
private lemma qO {r:ℕ} (hr:1<=r) {C:J}
  (hJ:IsMinimalCircuit (2*r+1) C) (hfun:cF (2*r+1) C=pq (2*r+1))
  (u:zb r C) {k:ℕ} (hk:k< C.size)
  (Hc:(C.gates[k]'hk).op=.and) :
  ∃(c:ℕ) (a1 a2:ℕ),c%2=1/\c< 2*r /\
   (C.gates[k]'hk).inputs=[a1,a2]/\a1< 2*r+1+k/\a2< 2*r+1+k /\
   p8 C k=qa r {c} /\
   ((a1=c/\(fun x=>p0 C x a2)=pD r c) \/
    (a2=c/\(fun x=>p0 C x a1)=pD r c)):=by
 have Hd:∃x1 x2:Fin (2*r+1)->Bool,cF (2*r+1) C x1≠cF (2*r+1) C x2:=by
  rw[hfun];X ps W
 rcases pc hJ Hd k hk with ⟨hT,_,_,_⟩|⟨_,a1,a2,hK,hU,H1,Hj⟩
 ·rw[Hc] at hT;cases hT
 ·have q:∀x:Fin (2*r+1)->Bool,p8 C k x=(p0 C x a1&&p0 C x a2):=by
   intro x;change p0 C x (2*r+1+k)=_;rw[pj C x k hk,Hc,hK];simp[GateOp.eval,hU,H1]
  have s:¬jg r (p8 C k):=by
   rintro ⟨c,H2,hE,hS⟩
   have v:∀x,pD r c x=true->p0 C x a1=true:=by
    intro x hx;have h:=q x;rw[hS,hx] at h
    cases h1:p0 C x a1 with
    | true=>rfl
    | false=>rw[h1,Bool.false_and] at h;cases h
   have h1:=v (e1 (c-1)) ((pt W hE W).2 (il W));have h2:=v (e1 (c+1)) ((pt W hE W).2 (ir rfl));rcases qH u a1 W with ⟨j,hj,_,a⟩|⟨_,_,_,c',hV,hA,a⟩|⟨_,_,_,P',_,_,a⟩
   ·have hF:=cf a (e1 (c-1));rw[h1] at hF
    have hW:=cf a (e1 (c+1));rw[h2] at hW;have e1_1:j=c-1:=of_decide_eq_true hF.symm;have e1_2:j=c+1:=of_decide_eq_true hW.symm;O
   ·have hF:=cf a (e1 (c-1));rw[h1] at hF
    have hW:=cf a (e1 (c+1));rw[h2] at hW;have e1_1:=(pt W hA W).1 hF.symm;have e1_2:=(pt W hA W).1 hW.symm;have H3:c'=c :=W;subst H3;obtain ⟨x,hx⟩:=py hJ k hk a1 hU;X hx (by rw[cf hS x,cf a x])
   ·have hF:=cf a (e1 (c-1));rw[h1,q2] at hF;cases hF
  have t:pX r (p8 C k):=by
   rcases u.2.1 k hk with hs|hu
   ·X absurd hs s
   ·X hu
  obtain ⟨P,H4,p,hS⟩:=t
  have g:∀w,w< 2*r+1+k ->
    (∀x:Fin (2*r+1)->Bool,p8 C k x=true->p0 C x w=true) ->
    ¬pX r (fun x=>p0 C x w):=by
   rintro w hw hL ⟨Q,_,_,hM⟩
   X qG hJ u.1 k hk w hw hL fun x He=>by
    rw[hfun];X zF (by rw[←cf hM x];X He)
  have hN:∀x:Fin (2*r+1)->Bool,p8 C k x=true->p0 C x a1=true:=by
   intro x hx;have h:=q x;rw[hx] at h
   cases h1:p0 C x a1 with
   | true=>rfl
   | false=>rw[h1,Bool.false_and] at h;cases h
  have y:∀x:Fin (2*r+1)->Bool,p8 C k x=true->p0 C x a2=true:=by
   intro x hx;have h:=q x;rw[hx] at h
   cases h2:p0 C x a2 with
   | true=>rfl
   | false=>rw[h2,Bool.and_false] at h;cases h
  obtain ⟨c0,hB⟩:=H4;have f:=(p c0 hB).1;have i:=(p c0 hB).2
  have hG:p8 C k (pe (c0-1):Fin (2*r+1)->Bool)=true:=by
   rw[hS];X (q7 p f i).2 hB
  have hH:p8 C k (pe c0:Fin (2*r+1)->Bool)=true:=by
   rw[hS];X (zL p f i).2 hB
  have hX:(∃(j:ℕ) (hj:j< 2*r+1),a1=j/\(fun x=>p0 C x a1)=fun x=>x ⟨j,hj⟩) \/
    jg r (fun x=>p0 C x a1):=by
   rcases qH u a1 W with h|⟨_,_,_,h⟩|⟨_,_,_,h⟩
   ·X il h
   ·X ir h
   ·X absurd h (g a1 hU hN)
  have hI:(∃(j:ℕ) (hj:j< 2*r+1),a2=j/\(fun x=>p0 C x a2)=fun x=>x ⟨j,hj⟩) \/
    jg r (fun x=>p0 C x a2):=by
   rcases qH u a2 W with h|⟨_,_,_,h⟩|⟨_,_,_,h⟩
   ·X il h
   ·X ir h
   ·X absurd h (g a2 H1 y)
  have l:∀w j (hj:j< 2*r+1),
    (fun x:Fin (2*r+1)->Bool=>p0 C x w)=(fun x:Fin (2*r+1)->Bool=>x ⟨j,hj⟩) ->
    (∀x:Fin (2*r+1)->Bool,p8 C k x=true->p0 C x w=true)->j=c0:=by
   intro w j hj hM hL;have h1:=cf hM (pe (c0-1));rw[hL _ hG] at h1;have h2:=cf hM (pe c0);rw[hL _ hH] at h2;have e1:j=c0-1\/j=c0-1+1:=of_decide_eq_true h1.symm;have e2:j=c0\/j=c0+1:=of_decide_eq_true h2.symm;O
  have d:∀w c' (hV:c'%2=1) (hA:c'< 2*r),
    (fun x:Fin (2*r+1)->Bool=>p0 C x w)=pD r c' ->
    (∀x:Fin (2*r+1)->Bool,p8 C k x=true->p0 C x w=true)->c'=c0:=by
   intro w c' hV hA hM hL;have h1:=cf hM (pe (c0-1));rw[hL _ hG] at h1;have h2:=cf hM (pe c0);rw[hL _ hH] at h2;obtain ⟨k1,Hk,H5⟩:=pG.1 h1.symm;obtain ⟨k2,Hl,H6⟩:=pG.1 h2.symm;have e1:k1.val=c0-1\/k1.val=c0-1+1:=of_decide_eq_true H5;have e2:k2.val=c0\/k2.val=c0+1:=of_decide_eq_true H6;O
  have b:∀(w1 w2:ℕ),
    (∀x:Fin (2*r+1)->Bool,p8 C k x=(p0 C x w1&&p0 C x w2)) ->
    (fun x:Fin (2*r+1)->Bool=>p0 C x w1)=(fun x:Fin (2*r+1)->Bool=>x ⟨c0,by O⟩) ->
    (fun x:Fin (2*r+1)->Bool=>p0 C x w2)=pD r c0 ->
    p8 C k=qa r {c0}:=by
   intro w1 w2 Hf Hg Hh;funext x;rw[Hf x,cf Hg x,cf Hh x];apply Bool.eq_iff_iff.2;simp only[Bool.and_eq_true,qp,Finset.mem_singleton]
   constructor
   ·rintro ⟨H7,H8⟩;X ⟨c0,rfl,by O,H7,H8⟩
   ·rintro ⟨c,rfl,_,H7,H8⟩;X ⟨H7,H8⟩
  rcases hX with ⟨j1,Hi,hO,a⟩|⟨c1,H9,Ha,a⟩
  ·have z:j1=c0:=l a1 j1 Hi a hN
   have hC:a1=c0:=hO.trans z
   have hY:(fun x:Fin (2*r+1)->Bool=>p0 C x a1)=(fun x=>x ⟨c0,by O⟩) :=
    funext fun x=>(cf a x).trans (congrArg x (Fin.ext z))
   rcases hI with ⟨j2,Hb,hh,e⟩|⟨c2,hP,hQ,e⟩
   ·have m:j2=c0:=l a2 j2 Hb e y
    O
   ·have n:c2=c0:=d a2 c2 hP hQ e y
    rw[n] at e
    X ⟨c0,a1,a2,f,i,hK,hU,H1,
     b a1 a2 q hY e,il ⟨hC,e⟩⟩
  ·have hR:c1=c0:=d a1 c1 H9 Ha a hN
   rw[hR] at a;rcases hI with ⟨j2,Hb,hh,e⟩|⟨c2,hP,hQ,e⟩
   ·have m:j2=c0:=l a2 j2 Hb e y
    have hD:a2=c0:=hh.trans m
    have hZ:(fun x:Fin (2*r+1)->Bool=>p0 C x a2)=(fun x=>x ⟨c0,by O⟩) :=
     funext fun x=>(cf e x).trans (congrArg x (Fin.ext m))
    X ⟨c0,a1,a2,f,i,hK,hU,H1,
     b a2 a1 (fun x=>by rw[q x,Bool.and_comm]) hZ a,
     ir ⟨hD,a⟩⟩
   ·have n:c2=c0:=d a2 c2 hP hQ e y
    rw[n] at e;have H0:=q (e1 (c0-1))
    rw[cf a (e1 (c0-1)),cf e (e1 (c0-1)),
     (pt W i W).2 (il W),
     hS,q2] at H0
    cases H0
private lemma zf {r:ℕ} (hr:1<=r) {C:J}
  (q:IsMinimalCircuit (2*r+1) C) (hfun:cF (2*r+1) C=pq (2*r+1))
  (i:zb r C) {kz kr:ℕ} (hP:kz< C.size) (k:kr< C.size)
  (hF:pX r (p8 C kz)) (b:pC (2*r+1) kr (2*r+1+kz) (C.gates[kr]'k)) :
  (C.gates[kr]'k).op=.or/\pX r (p8 C kr) /\
  (∀x:Fin (2*r+1)->Bool,p8 C kz x=true->p8 C kr x=true):=by
 have hK:∃x1 x2:Fin (2*r+1)->Bool,cF (2*r+1) C x1≠cF (2*r+1) C x2:=by
  rw[hfun];X ps W
 rcases pc q hK kr k with ⟨hA,_,_,_⟩|⟨s,a1,a2,f,hB,hC,_⟩
 ·X absurd hA (i.1 _ (List.getElem_mem k))
 ·rcases s with hop_and|a
  ·exfalso
   obtain ⟨c,b1,b2,hD,u,m,_,_,_,v⟩:=qO hr q hfun i k hop_and;rw[m] at f;injection f with h1 h2;injection h2 with t;subst h1;subst t;have l:=b.1;simp only[pa,hop_and,m,List.mem_cons,List.not_mem_nil,or_false] at l;obtain ⟨P,_,_,w⟩:=hF;rcases v with ⟨rfl,hG⟩|⟨rfl,hH⟩
   ·rcases l with h|h
    ·O
    ·rw[←h] at hG
     X q3 hD u (hG.symm.trans w)
   ·rcases l with h|h
    ·rw[←h] at hH
     X q3 hD u (hH.symm.trans w)
    ·O
  ·have hL:∀x:Fin (2*r+1)->Bool,p8 C kz x=true->p8 C kr x=true:=by
    intro x hI;change p0 C x (2*r+1+kr)=true;rw[pj C x kr k,a,f]
    simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
     id_eq,Bool.or_false,hB,hC,↓reduceIte,Bool.or_eq_true]
    have l:=b.1;simp only[pa,a,f,List.mem_cons,List.not_mem_nil,or_false] at l;rcases l with rfl|rfl
    ·X il hI
    ·X ir hI
   have y:pX r (p8 C kr):=by
    rcases i.2.1 kr k with ⟨c,hD,u,hJ⟩|hu
    ·exfalso
     have l:=b.1;simp only[pa,a,f,List.mem_cons,List.not_mem_nil,or_false] at l;obtain ⟨P,_,_,w⟩:=hF
     have e:∀x,pD r c x=(p0 C x a1||p0 C x a2):=by
      intro x;rw[←cf hJ x];change p0 C x (2*r+1+kr)=_;rw[pj C x kr k,a,f];simp[GateOp.eval,hB,hC]
     have g:∀d,d< 2*r+1+kr ->
       (∀x,pD r c x=(qa r P x||p0 C x d))->False:=by
      intro d hd z;have h1:=z (e1 (c-1));rw[(pt W u W).2 (il W),q2] at h1;have h2:=z (e1 (c+1));rw[(pt W u W).2 (ir rfl),q2] at h2;simp only[Bool.false_or] at h1 h2;rcases qH i d W with ⟨j,hj,_,n⟩|⟨_,_,_,c',hM,hh,n⟩|⟨_,_,_,Q,_,_,n⟩
      ·have p:=cf n (e1 (c-1));rw[←h1] at p
       have t:=cf n (e1 (c+1));rw[←h2] at t;have hN:j=c-1:=of_decide_eq_true p.symm;have hO:j=c+1:=of_decide_eq_true t.symm;O
      ·have p:=cf n (e1 (c-1));rw[←h1] at p
       have t:=cf n (e1 (c+1));rw[←h2] at t;have hN:=(pt W hh W).1 p.symm;have hO:=(pt W hh W).1 t.symm;have hE:c'=c :=W;subst hE;obtain ⟨x,hx⟩:=py q kr k d hd;X hx (by rw[cf hJ x,cf n x])
      ·have p:=cf n (e1 (c-1));rw[q2,←h1] at p;cases p
     rcases l with rfl|rfl
     ·X g a2 hC (fun x=>by rw[e x];change (p0 C x (2*r+1+kz)||_)=_;rw[←cf w x];rfl)
     ·X g a1 hB (fun x=>by rw[e x,Bool.or_comm];change (p0 C x (2*r+1+kz)||_)=_;rw[←cf w x];rfl)
    ·X hu
   X ⟨a,y,hL⟩
private lemma zZ {r:ℕ} (hr:1<=r) {C:J}
  (e:IsMinimalCircuit (2*r+1) C) (hfun:cF (2*r+1) C=pq (2*r+1))
  (t:zb r C) {kz:ℕ} (hW:kz< C.size) (H0:pX r (p8 C kz))
  {kr1 kr2:ℕ} (d:kr1< C.size) (w:kr2< C.size)
  (hM:pC (2*r+1) kr1 (2*r+1+kz) (C.gates[kr1]'d))
  (hN:pC (2*r+1) kr2 (2*r+1+kz) (C.gates[kr2]'w)) :
  kr1=kr2:=by
 by_contra hne
 have hX:∃x1 x2:Fin (2*r+1)->Bool,cF (2*r+1) C x1≠cF (2*r+1) C x2:=by
  rw[hfun];X ps W
 obtain ⟨Pz,⟨c,k⟩,a,hO⟩:=H0;have l:=(a c k).1;have z:=(a c k).2;set ye:Fin (2*r+1)->Bool:=pe (c-1)
 have n:p8 C kz ye=true:=by
  rw[hO];X (q7 a l z).2 k
 obtain ⟨hA,⟨P1,hF,p,hG⟩,hP⟩:=zf hr e hfun t hW d ⟨Pz,⟨c,k⟩,a,hO⟩ hM;obtain ⟨hQ,hB,hR⟩:=zf hr e hfun t hW w ⟨Pz,⟨c,k⟩,a,hO⟩ hN;have hS:c∈P1:=(q7 p l z).1 (by rw[←cf hG ye];X hP ye n)
 have q:pl C ye kr1 false C.output=false:=t.2.2 kr1 d P1 hF p hG c hS;have hC:kz< kr1:=by have:=hM.2;O
 have f:kz< kr2:=by have:=hN.2;O
 have y:pl C ye kr1 false (2*r+1+kz)=true:=by
  rw[pA C ye kr1 d false (2*r+1+kz) W];X n
 have b:∀v (hv:v< C.size) (u:ℕ),v≠kr1 ->
   (C.gates[v]'hv).op=.or->pC (2*r+1) v u (C.gates[v]'hv) ->
   pl C ye kr1 false u=true ->
   pl C ye kr1 false (2*r+1+v)=true:=by
  intro v hv u hH hD H1 hY;rcases pc e hX v hv with ⟨s,_,_,_⟩|⟨_,a1,a2,hI,H2,H3,_⟩
  ·rw[hD] at s;cases s
  ·rw[zs C ye kr1 d false v hv hH,hD,hI]
   simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
    id_eq,Bool.or_false,H2,H3,↓reduceIte,Bool.or_eq_true]
   have hZ:=H1.1;simp only[pa,hD,hI,List.mem_cons,List.not_mem_nil,or_false] at hZ;rcases hZ with rfl|rfl
   ·X il hY
   ·X ir hY
 rcases pc e hX kr1 d with ⟨s,_,_,_⟩|⟨_,d1,d2,hh,H4,H5,H6⟩
 ·rw[hA] at s;cases s
 ·
  suffices hdown:∀m (v:ℕ),C.size-v<=m->v< C.size->v≠kr1->kz< v ->
    pX r (p8 C v) ->
    (∀x,p8 C kz x=true->p8 C v x=true) ->
    pl C ye kr1 false (2*r+1+v)=true->False by
   X hdown (C.size-kr2) kr2 le_rfl w (Ne.symm hne) f hB hR
    (b kr2 w (2*r+1+kz) (Ne.symm hne) hQ hN y)
  intro m
  induction m with
  | zero=>intro v H7 hv _ _ _ _ _;O
  | succ m ih=>
   intro v H7 hv hH H8 H9 hE i;rcases pY e v hv with hout|⟨vnext,g,Hb,hT⟩
   ·rw[←hout] at i;rw[q] at i;cases i
   ·obtain ⟨hU,Ha,hV⟩:=zf hr e hfun t hv g H9 hT
    by_cases h:vnext=kr1
    ·subst h
     have hJ:=hM.1;have hK:=hT.1;simp only[pa,hA,hh,List.mem_cons,List.not_mem_nil,or_false] at hJ hK
     have hL:∀x:Fin (2*r+1)->Bool,p8 C vnext x=(p0 C x d1||p0 C x d2):=by
      intro x;change p0 C x (2*r+1+vnext)=_;rw[pj C x vnext d,hA,hh];simp[GateOp.eval,H4,H5]
     have j:∀x:Fin (2*r+1)->Bool,p8 C vnext x=p0 C x (2*r+1+v):=by
      intro x;rw[hL x];rcases hJ with h1|h1<;>rcases hK with h2|h2
      ·O
      ·rw[←h1,←h2]
       cases hzx:p0 C x (2*r+1+kz) with
       | false=>simp
       | true=>X (Bool.true_or _).trans (hE x hzx).symm
      ·rw[←h1,←h2]
       cases hzx:p0 C x (2*r+1+kz) with
       | false=>simp
       | true=>X (Bool.or_true _).trans (hE x hzx).symm
      ·O
     obtain ⟨x,hx⟩:=py e vnext d (2*r+1+v) W;X hx (j x)
    ·X ih vnext W g h W Ha
      (fun x hx=>hV x (hE x hx))
      (b vnext g (2*r+1+v) h hU hT i)
private lemma km {m:ℕ} (hm:1<=m) {e:J}
  (Hx:IsMinimalCircuit ((2*m+1)+1) e)
  (Hy:∀y:Fin ((2*m+1)+1)->Bool,
   cF ((2*m+1)+1) e y=(y (Fin.last (2*m+1))||pq (2*m+1) (Fin.init y)))
  (z:zb m (p3 e (2*m+1) false)) :
  let r:=p5 e (2*m+1) false;let p:=p3 e (2*m+1) false
  z0 e /\
  (∃H3:ℕ,∃(Hz:H3< e.size),
   (∀k (hk:k< e.size),pC ((2*m+1)+1) k (2*m+1) (e.gates[k]'hk)↔k=H3) /\
   (∀k (hk:k< e.size),r.fb[k]'(by rw[(pk e (2*m+1) false Hx.1).kept_len];X hk)=false↔k=H3) /\
   (e.gates[H3]'Hz).op=.or /\
   ∃HO hC:ℕ,∃(Hd:hC< p.size),
    HO< ((2*m+1)+1)+H3/\HO≠2*m+1 /\
    ((e.gates[H3]'Hz).inputs=[2*m+1,HO]\/(e.gates[H3]'Hz).inputs=[HO,2*m+1]) /\
    r.fc.getD (((2*m+1)+1)+H3) (.const false)=.wire ((2*m+1)+hC) /\
    r.fc.getD HO (.const false)=.wire ((2*m+1)+hC) /\
    pX m (p8 p hC)) /\
  (∀k (hk:k< e.size),
   p0 e (e1 (2*m+1):Fin ((2*m+1)+1)->Bool) (((2*m+1)+1)+k)=true ->
   (e.gates[k]'hk).op=.or) /\
  (∀k (hk:k< e.size),(e.gates[k]'hk).op=.and ->
   ∀a,pC ((2*m+1)+1) k a (e.gates[k]'hk) ->
    p0 e (e1 (2*m+1):Fin ((2*m+1)+1)->Bool) a=false) /\
  (∀i< ((2*m+1)+1)+e.size,
   p0 e (e1 (2*m+1):Fin ((2*m+1)+1)->Bool) i=false ->
   ∀y:Fin ((2*m+1)+1)->Bool,
    p0 e y i=p0 e (Fin.snoc (Fin.init y) false) i) /\
  (∀k (hk:k< e.size),
   p0 e (e1 (2*m+1):Fin ((2*m+1)+1)->Bool) (((2*m+1)+1)+k)=true ->
   ∃(hV:ℕ),r.fc.getD (((2*m+1)+1)+k) (.const false)=.wire hV /\
    ∀y:Fin (2*m+1)->Bool,p0 p y hV=true->pq (2*m+1) y=true):=by
 dsimp only;have d:IsMinimalCircuit ((2*m+1)+1) e:=Hx
 have hA:∀y:Fin (2*m+1)->Bool,
   cF ((2*m+1)+1) e (Fin.snoc y false)=pq (2*m+1) y:=by
  intro y;rw[Hy,Fin.snoc_last,Fin.init_snoc,Bool.false_or]
 have hZ:∀y:Fin (2*m+1)->Bool,
   cF ((2*m+1)+1) e (Fin.snoc y true)=true:=by
  intro y;rw[Hy,Fin.snoc_last,Bool.true_or]
 have _t:∃y:Fin (2*m+1)->Bool,
   cF ((2*m+1)+1) e (Fin.snoc y false) ≠
    cF ((2*m+1)+1) e (Fin.snoc y true):=by
  Y ⟨e0,?_⟩;rw[hA,hZ,zq];decide
 have HA:∃y1 y2:Fin (2*m+1)->Bool,
   cF ((2*m+1)+1) e (Fin.snoc y1 false) ≠
    cF ((2*m+1)+1) e (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,_L⟩:=ps (n:=2*m+1) W;X ⟨y1,y2,by rw[hA,hA];X _L⟩
 have h03:e.size=3*m:=by
  have hub:e.size<=(zi m).size+1:=by
   let P:=zi m
   let E:J:={
    gates:=P.gates++[⟨.or,[2*m+1,(2*m+1)+P.output]⟩],
    output:=(2*m+1)+1+P.size
   }
   let shiftIdx:ℕ->ℕ:=fun i=>if i< 2*m+1 then i else i+1;let P':List Gate:=P.gates.map fun g=>⟨g.op,g.inputs.map shiftIdx⟩
   let E':J:={
    gates:=P'++[⟨.or,[2*m+1,shiftIdx P.output]⟩],
    output:=(2*m+1)+1+P.size
   }
   have _u:FanInTwo E':=by
    intro g hg;simp only[E',P',List.mem_append,List.mem_map,List.mem_singleton] at hg;rcases hg with ⟨g0,hg0,rfl⟩|rfl
    ·have:=jv m g0 hg0;X ⟨this.1,by simpa using this.2⟩
    ·X ⟨by simp,by simp⟩
   have HB:∀(y:Fin (2*m+1)->Bool) (b:Bool) (i:ℕ),i< (2*m+1)+P.size ->
     (pK P' (List.ofFn (Fin.snoc y b))).getD (shiftIdx i) false=p0 P y i:=by
    intro y b i
    induction i using Nat.strong_induction_on with
    | ind i ih=>
     intro hi;by_cases _m:i< 2*m+1
     ·simp only[shiftIdx,_m,↓reduceIte]
      rw[q5 _ _ i (by simp;O),List.getD_eq_getElem _ _ (by simp;O),
       List.getElem_ofFn,p7 P y i _m]
      have:(⟨i,by O⟩:Fin ((2*m+1)+1))=Fin.castSucc ⟨i,_m⟩:=Fin.ext rfl
      rw[this,Fin.snoc_castSucc]
     ·set t:=i-(2*m+1)
      have ht:t< P.size :=W;have H4:i=(2*m+1)+t :=W;have hsh:shiftIdx i=((2*m+1)+1)+t:=by simp only[shiftIdx,_m,↓reduceIte];O
      rw[hsh,H4,pj P y t ht];let Cshift:J:={ gates:=P',output:=0 };have h04:Cshift.size=P.size:=by simp[Cshift,P',Circuit.size]
      have ht':t< Cshift.size :=W;change p0 Cshift (Fin.snoc y b) (((2*m+1)+1)+t)=_;rw[pj Cshift (Fin.snoc y b) t ht']
      have hgt:Cshift.gates[t]'ht'=⟨(P.gates[t]'ht).op,(P.gates[t]'ht).inputs.map shiftIdx⟩ :=
       List.getElem_map _
      rw[hgt];simp only[List.map_map,Function.comp_def];congr 1;apply List.map_congr_left;intro a _;by_cases ha:a< (2*m+1)+t
      ·have _P:shiftIdx a< ((2*m+1)+1)+t:=by simp only[shiftIdx];split_ifs<;>O
       simp only[ha,_P,↓reduceIte];X ih a W W
      ·have _P:¬shiftIdx a< ((2*m+1)+1)+t:=by simp only[shiftIdx];split_ifs<;>O
       simp only[ha,_P,↓reduceIte]
   have _3:cF ((2*m+1)+1) E'=cF ((2*m+1)+1) e:=by
    funext x
    have _v:x=Fin.snoc (Fin.init x) (x (Fin.last (2*m+1))):=(Fin.snoc_init_self x).symm;rw[_v];set y:=Fin.init x;set b:=x (Fin.last (2*m+1))
    have _w:P.output< (2*m+1)+P.size:=by
     simp[P,zi,Circuit.size,zj (2*m+1) m hm]
    have Hi:(pK P' (List.ofFn (Fin.snoc y b))).length=((2*m+1)+1)+P.size:=by
     rw[qm,List.length_ofFn];simp[P',Circuit.size]
    have _Q:cF ((2*m+1)+1) E' (Fin.snoc y b)=(b||pq (2*m+1) y):=by
     unfold circuitFun Circuit.eval
     rw[qu]
     change (pK (P'++[⟨.or,[2*m+1,shiftIdx P.output]⟩])
      (List.ofFn (Fin.snoc y b))).getD (((2*m+1)+1)+P.size) false=_
     rw[ql,qA,zd]
     rw[List.getD_eq_getElem (pK P' (List.ofFn (Fin.snoc y b))++[_]) _
       (by simp only[List.length_append,List.length_singleton,Hi];O),
      List.getElem_append_right W]
     simp only[Hi,Nat.sub_self,List.getElem_singleton,GateOp.eval,
      List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
     have h1:(pK P' (List.ofFn (Fin.snoc y b))).getD (2*m+1) false=b:=by
      rw[q5 _ _ (2*m+1) (by simp),List.getD_eq_getElem _ _ (by simp),
       List.getElem_ofFn]
      have:(⟨2*m+1,by O⟩:Fin ((2*m+1)+1))=Fin.last (2*m+1):=Fin.ext rfl
      rw[this,Fin.snoc_last]
     have h2:=HB y b P.output _w;rw[h1,h2,←pb,jl m hm]
    rw[_Q];cases b
    ·rw[Bool.false_or,hA]
    ·rw[Bool.true_or,hZ]
   have hle:=d.2 E' _u _3;have h05:E'.size=(zi m).size+1:=by simp[E',P',P,Circuit.size]
   O
  have hlb:3*m<=e.size:=by
   have hD:=j0 d false _t HA
   have HC:cF (2*m+1) (p3 e (2*m+1) false)=pq (2*m+1):=by
    funext y;rw[q6 e (2*m+1) false d.1 HA y,hA]
   have _4:=q9 (2*m+1) W _ (qi e (2*m+1) false d.1) HC;have _5:(2*m+1)%2≠0 :=W;have _6:(2*m+1)/2=m :=W;simp only[_5,↓reduceIte,_6] at _4;O
  have h06:=jk m hm;O
 have HD:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m+1)->Bool,cF (2*m+1) D y=cF ((2*m+1)+1) e (Fin.snoc y false)) ->
   e.size<=D.size+1:=by
  intro D _R _7;have HC:cF (2*m+1) D=pq (2*m+1):=funext fun y=>(_7 y).trans (hA y);have _4:=q9 (2*m+1) W D _R HC;have _5:(2*m+1)%2≠0 :=W;have _6:(2*m+1)/2=m :=W;simp only[_5,↓reduceIte,_6] at _4;O
 obtain ⟨hP,_S,H3,Hz,s,q,H5,HO,_x,HE,_y,hK⟩ :=
  zV d false _t HA HD
 simp only[Bool.false_eq_true,↓reduceIte] at H5;set r:=p5 e (2*m+1) false;set p:=p3 e (2*m+1) false;have l:=pk e (2*m+1) false d.1
 have Hj:cF (2*m+1) p=pq (2*m+1):=by
  funext y;rw[q6 e (2*m+1) false d.1 HA y,hA]
 have HF:z0 e:=by
  Y qK d.1 z.1 ?_;intro t ht _z;have _M:=(q t ht).1 _z;subst _M;rw[H5];intro h;cases h
 set vU:Fin ((2*m+1)+1)->Bool:=e1 (2*m+1)
 have Hs:∀i< ((2*m+1)+1)+e.size,i≠2*m+1 ->
   ∃hV:ℕ,hV< (2*m+1)+p.size/\r.fc.getD i (.const false)=.wire hV:=by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih=>
   intro _T _L;by_cases _n:i< 2*m+1
   ·X ⟨i,by O,pd e (2*m+1) false i _n⟩
   ·set t:=i-((2*m+1)+1)
    have ht:t< e.size :=W;have H4:i=((2*m+1)+1)+t :=W;rw[H4];by_cases htq:t=H3
    ·subst htq
     rw[hK];X ih HO W W HE
    ·have HG:r.fb[t]'(by rw[l.kept_len];X ht)=true:=by
      cases hk:r.fb[t]'(by rw[l.kept_len];X ht) with
      | true=>rfl
      | false=>X absurd ((q t ht).1 hk) htq
     obtain ⟨k,hk,_,_U,_,_,_⟩:=p4 d.1 ht HG;have hk':k< p.size:=hk;X ⟨(2*m+1)+k,by O,_U⟩
 obtain ⟨hO,H6,w⟩:=Hs HO W HE
 have hX:∃x1 x2:Fin ((2*m+1)+1)->Bool,
   cF ((2*m+1)+1) e x1≠cF ((2*m+1)+1) e x2:=by
  obtain ⟨y1,y2,_L⟩:=HA;X ⟨Fin.snoc y1 false,Fin.snoc y2 false,_L⟩
 have hL:∀(k:ℕ) (hk:k< e.size),
   p0 e vU (((2*m+1)+1)+k)=true->(e.gates[k]'hk).op=.or:=by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih=>
   intro hk Ht
   have HX:∀v< ((2*m+1)+1)+k,p0 e vU v=true->v≠2*m+1 ->
     ∀y:Fin (2*m+1)->Bool,p0 p y hO=true ->
      p0 e (Fin.snoc y false) v=true:=by
    intro v
    induction v using Nat.strong_induction_on with
    | ind v ihv=>
     intro _V He _8 y Hc;by_cases _9:v< (2*m+1)+1
     ·rw[p7 e vU v _9] at He
      have:v=2*m+1:=of_decide_eq_true He
      X absurd this _8
     ·set tv:=v-((2*m+1)+1)
      have Hf:tv< e.size :=W;have HH:v=((2*m+1)+1)+tv :=W;rw[HH] at He ⊢;by_cases Hg:tv=H3
      ·subst Hg
       have _A:=pH e (2*m+1) false d.1 y (((2*m+1)+1)+tv);rw[hK,w] at _A;X _A.symm.trans Hc
      ·have hQ:(e.gates[tv]'Hf).op=.or:=ih tv W Hf He
       rcases pc d hX tv Hf with ⟨hI,_,_,_⟩|⟨_,b1,b2,hJ,_B,_C,_⟩
       ·rw[hQ] at hI;cases hI
       ·rw[pj e vU tv Hf,hQ,hJ] at He
        simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
         id_eq,Bool.or_false,_B,_C,↓reduceIte,Bool.or_eq_true] at He
        rw[pj e (Fin.snoc y false) tv Hf,hQ,hJ]
        simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
         id_eq,Bool.or_false,_B,_C,↓reduceIte,Bool.or_eq_true]
        have H7:b1≠2*m+1:=fun h=>Hg ((s tv Hf).1 ⟨by simp[pa,hQ,hJ,h],by O⟩)
        have H8:b2≠2*m+1:=fun h=>Hg ((s tv Hf).1 ⟨by simp[pa,hQ,hJ,h],by O⟩)
        rcases He with h1|h2
        ·X il (ihv b1 W W h1 H7 y Hc)
        ·X ir (ihv b2 W W h2 H8 y Hc)
   rcases pc d hX k hk with ⟨hI,_,_,_⟩|⟨hR,a1,a2,hE,Hk,Hl,_⟩
   ·X absurd hI (HF _ (List.getElem_mem hk))
   ·rcases hR with f|u
    ·exfalso
     have HI:k≠H3:=by intro rfl;rw[H5] at f;cases f
     have H0:r.fb[k]'(by rw[l.kept_len];X hk)=true:=by
      cases h:r.fb[k]'(by rw[l.kept_len];X hk) with
      | true=>rfl
      | false=>X absurd ((q k hk).1 h) HI
     obtain ⟨hF,hG,_,HJ,H9,Ha,_a⟩:=p4 d.1 hk H0;have Hm:(p.gates[hF]'hG).op=.and:=H9.trans f;obtain ⟨w1,w2,_o,_p,_b,_c,Hu⟩:=Ha .and a1 a2 (il rfl) f hE Hk Hl;obtain ⟨c,c1,c2,_N,HP,HK,_,_,_d,Hn⟩:=qO hm hP Hj z hG Hm;rw[Hu] at HK;injection HK with hcw1 hcw2;injection hcw2 with hcw2';subst hcw1;subst hcw2';rw[pj e vU k hk,f,hE] at Ht
     simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
      id_eq,Bool.and_true,Hk,Hl,↓reduceIte,Bool.and_eq_true] at Ht
     have H7:a1≠2*m+1:=fun h=>HI ((s k hk).1 ⟨by simp[pa,f,hE,h],by O⟩)
     have H8:a2≠2*m+1:=fun h=>HI ((s k hk).1 ⟨by simp[pa,f,hE,h],by O⟩)
     have Ho:∀y:Fin (2*m+1)->Bool,p0 p y hO=true ->
       qa m {c} y=true:=by
      intro y Hc;have h1:=HX a1 Hk Ht.1 H7 y Hc;have h2:=HX a2 Hl Ht.2 H8 y Hc;have hs1:=pH e (2*m+1) false d.1 y a1;have hs2:=pH e (2*m+1) false d.1 y a2;rw[_b] at hs1;rw[_c] at hs2;have _W:p0 p y w1=true:=hs1.trans h1;have _X:p0 p y w2=true:=hs2.trans h2
      have hk1:p8 p hF y=true:=by
       change p0 p y ((2*m+1)+hF)=true;rw[pj p y hF hG,Hm,Hu];simp[GateOp.eval,_o,_p,_W,_X]
      rwa[←_d]
     have HL:pX m (fun y=>p0 p y hO):=by
      rcases qH z hO H6 with ⟨j,hj,_,Hw⟩|⟨_,_,_,c',_e,H1,Hw⟩|⟨_,_,_,hu⟩
      ·have hS:=Ho (e1 j) (by rw[cf Hw (e1 j)];simp[e1])
       rw[q2] at hS;cases hS
      ·have hS:=Ho (e1 (c'-1)) (by rw[cf Hw (e1 (c'-1))];X (pt W H1 W).2 (il W))
       rw[q2] at hS;cases hS
      ·X hu
     have hT:∀a,a< ((2*m+1)+1)+k->p0 e vU a=true->a≠2*m+1 ->
       r.fc.getD a (.const false)=.wire c->False:=by
      intro a h07 _q _f _D;by_cases _Y:a< (2*m+1)+1
      ·rw[p7 e vU a _Y] at _q
       X _f (of_decide_eq_true _q)
      ·set ta:=a-((2*m+1)+1)
       have _r:ta< e.size :=W;have Hp:a=((2*m+1)+1)+ta :=W;rw[Hp] at _D;by_cases _E:ta=H3
       ·subst _E
        rw[hK,w] at _D;injection _D with hzc;subst hzc;obtain ⟨Pz,_,_,Hw⟩:=HL;X qt (j:=hO) W (Hw.symm.trans (funext fun x=>p7 p x hO W))
       ·have HQ:r.fb[ta]'(by rw[l.kept_len];X _r)=true:=by
         cases h:r.fb[ta]'(by rw[l.kept_len];X _r) with
         | true=>rfl
         | false=>X absurd ((q ta _r).1 h) _E
        obtain ⟨ka,_,_,_g,_,_,_⟩:=p4 d.1 _r HQ;rw[_g] at _D;injection _D with _M;O
     rcases Hn with ⟨rfl,_⟩|⟨rfl,_⟩
     ·X hT a1 Hk Ht.1 H7 _b
     ·X hT a2 Hl Ht.2 H8 _c
    ·X u
 have hM:∀v< ((2*m+1)+1)+e.size,p0 e vU v=true->v≠2*m+1 ->
   ∀y:Fin (2*m+1)->Bool,p0 p y hO=true ->
    p0 e (Fin.snoc y false) v=true:=by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ihv=>
   intro _V He _8 y Hc;by_cases _9:v< (2*m+1)+1
   ·rw[p7 e vU v _9] at He
    X absurd (of_decide_eq_true He) _8
   ·set tv:=v-((2*m+1)+1)
    have Hf:tv< e.size :=W;have HH:v=((2*m+1)+1)+tv :=W;rw[HH] at He ⊢;by_cases Hg:tv=H3
    ·subst Hg
     have _A:=pH e (2*m+1) false d.1 y (((2*m+1)+1)+tv);rw[hK,w] at _A;X _A.symm.trans Hc
    ·have hQ:(e.gates[tv]'Hf).op=.or:=hL tv Hf He
     rcases pc d hX tv Hf with ⟨hI,_,_,_⟩|⟨_,b1,b2,hJ,_B,_C,_⟩
     ·rw[hQ] at hI;cases hI
     ·rw[pj e vU tv Hf,hQ,hJ] at He
      simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
       id_eq,Bool.or_false,_B,_C,↓reduceIte,Bool.or_eq_true] at He
      rw[pj e (Fin.snoc y false) tv Hf,hQ,hJ]
      simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
       id_eq,Bool.or_false,_B,_C,↓reduceIte,Bool.or_eq_true]
      have H7:b1≠2*m+1:=fun h=>Hg ((s tv Hf).1 ⟨by simp[pa,hQ,hJ,h],by O⟩)
      have H8:b2≠2*m+1:=fun h=>Hg ((s tv Hf).1 ⟨by simp[pa,hQ,hJ,h],by O⟩)
      rcases He with h1|h2
      ·X il (ihv b1 W W h1 H7 y Hc)
      ·X ir (ihv b2 W W h2 H8 y Hc)
 have HR:e.output< ((2*m+1)+1)+e.size:=by
  by_contra hge
  have h1:=hZ e0;rw[pb,z3 e _ e.output W] at h1;cases h1
 have _h:p0 e vU e.output=true:=by
  have HM:vU=Fin.snoc (e0:Fin (2*m+1)->Bool) true:=by
   funext j
   by_cases hj:j.val< 2*m+1
   ·have:j=Fin.castSucc ⟨j.val,hj⟩:=Fin.ext rfl
    rw[this,Fin.snoc_castSucc];simp[vU,e1,e0];O
   ·have:j=Fin.last (2*m+1):=Fin.ext (by have:=j.isLt;simp;O)
    rw[this,Fin.snoc_last];simp[vU,e1]
  rw[←pb,HM,hZ]
 have HS:e.output≠2*m+1:=by
  intro _M;have h:=hA (pe 0);rw[pb,_M,p7 e _ (2*m+1) W] at h;have _F:(⟨2*m+1,by O⟩:Fin ((2*m+1)+1))=Fin.last (2*m+1):=Fin.ext rfl
  rw[_F,Fin.snoc_last,q0 W] at h;cases h
 have hU:∀y:Fin (2*m+1)->Bool,p0 p y hO=true->pq (2*m+1) y=true:=by
  intro y Hc;rw[←hA y,pb];X hM e.output HR _h HS y Hc
 have hW:∃(hC:ℕ) (Hd:hC< p.size),
   hO=(2*m+1)+hC/\pX m (p8 p hC):=by
  rcases qH z hO H6 with ⟨j,hj,_,Hw⟩|⟨_,_,_,c',_e,H1,Hw⟩|⟨kz,hkz,_G,hu⟩
  ·have hS:=hU (e1 j) (by rw[cf Hw (e1 j)];simp[e1])
   rw[pW] at hS;cases hS
  ·have hS:=hU (e1 (c'-1)) (by rw[cf Hw (e1 (c'-1))];X (pt W H1 W).2 (il W))
   rw[pW] at hS;cases hS
  ·X ⟨kz,hkz,_G,by rw[_G] at hu;X hu⟩
 obtain ⟨hC,Hd,hH,hB⟩:=hW
 have hh:∀k (hk:k< e.size),p0 e vU (((2*m+1)+1)+k)=true ->
   ∃(hV:ℕ),r.fc.getD (((2*m+1)+1)+k) (.const false)=.wire hV /\
    pX m (fun y=>p0 p y hV):=by
  intro k hk Ht;by_cases HI:k=H3
  ·subst HI
   Y ⟨hO,hK.trans w,?_⟩;rw[hH];X hB
  ·have HG:r.fb[k]'(by rw[l.kept_len];X hk)=true:=by
    cases h:r.fb[k]'(by rw[l.kept_len];X hk) with
    | true=>rfl
    | false=>X absurd ((q k hk).1 h) HI
   obtain ⟨hF,hG,_,HJ,H9,Ha,_a⟩:=p4 d.1 hk HG;have Hq:hF< p.size:=hG;Y ⟨(2*m+1)+hF,HJ,?_⟩;rcases z.2.1 hF hG with ⟨c,_N,HP,_Z⟩|hu
   ·exfalso
    have u:(e.gates[k]'hk).op=.or:=hL k hk Ht;rcases pc d hX k hk with ⟨hI,_,_,_⟩|⟨_,a1,a2,hE,Hk,Hl,_⟩
    ·rw[u] at hI;cases hI
    ·obtain ⟨w1,w2,_o,_p,_b,_c,Hu⟩:=Ha .or a1 a2 (ir rfl) u hE Hk Hl
     have h00:(p.gates[hF]'hG).op=.or:=H9.trans u;rw[pj e vU k hk,u,hE] at Ht
     simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
      id_eq,Bool.or_false,Hk,Hl,↓reduceIte,Bool.or_eq_true] at Ht
     have H7:a1≠2*m+1:=fun h=>HI ((s k hk).1 ⟨by simp[pa,u,hE,h],by O⟩)
     have H8:a2≠2*m+1:=fun h=>HI ((s k hk).1 ⟨by simp[pa,u,hE,h],by O⟩)
     have hY:∀(u_in o_in:ℕ),u_in< (2*m+1)+hF->o_in< (2*m+1)+hF ->
       (∀y:Fin (2*m+1)->Bool,p0 p y hO=true->p0 p y u_in=true) ->
       (∀y:Fin (2*m+1)->Bool,pD m c y=(p0 p y u_in||p0 p y o_in))->False:=by
      intro u_in o_in _H _I HY HN
      have HZ:∀a,p0 p (e1 a:Fin (2*m+1)->Bool) u_in=false:=by
       obtain ⟨Pz,⟨cz,_O⟩,HT,Hw⟩:=hB;have _0:=(HT cz _O).1;have _1:=(HT cz _O).2
       have hzl:p0 p (pe (cz-1)) u_in=true :=
        HY _ (by rw[hH];change p8 p hC _=true;rw[Hw];X (q7 HT _0 _1).2 _O)
       have hzr:p0 p (pe cz) u_in=true :=
        HY _ (by rw[hH];change p8 p hC _=true;rw[Hw];X (zL HT _0 _1).2 _O)
       rcases qH z u_in W with ⟨j,hj,_,HU⟩|⟨_,_,_,c',_e,H1,HU⟩|⟨_,_,_,Q,_,_,HU⟩
       ·
        have e1':j=cz-1\/j=cz-1+1:=of_decide_eq_true (by have:=cf HU (pe (cz-1));rw[hzl] at this;X this.symm)
        have e2':j=cz\/j=cz+1:=of_decide_eq_true (by have:=cf HU (pe cz);rw[hzr] at this;X this.symm)
        have h01:j=cz :=W;subst h01
        have HV:pD m c (e1 j)=true:=by
         rw[HN (e1 j),cf HU (e1 j)];simp[e1]
        have:=(pt W HP W).1 HV
        O
       ·
        have hc1:pD m c (e1 (c'-1))=true:=by
         rw[HN (e1 (c'-1)),cf HU (e1 (c'-1)),
          (pt W H1 W).2 (il W)];R
        have hc2:pD m c (e1 (c'+1))=true:=by
         rw[HN (e1 (c'+1)),cf HU (e1 (c'+1)),
          (pt W H1 W).2 (ir rfl)];R
        have e1':=(pt W HP W).1 hc1;have e2':=(pt W HP W).1 hc2;have _i:c'=c :=W;subst _i;obtain ⟨x,hx⟩:=py hP hF Hq u_in _H;X absurd (by rw[cf _Z x,cf HU x]) hx
       ·intro a;rw[cf HU (e1 a),q2]
      have h1:=HN (e1 (c-1));rw[(pt W HP W).2 (il W),HZ (c-1),Bool.false_or] at h1;have h2:=HN (e1 (c+1));rw[(pt W HP W).2 (ir rfl),HZ (c+1),Bool.false_or] at h2;rcases qH z o_in W with ⟨j,hj,_,_2⟩|⟨_,_,_,c',_e,H1,_2⟩|⟨_,_,_,Q,_,_,_2⟩
      ·have e1':j=c-1:=of_decide_eq_true (by have:=cf _2 (e1 (c-1));rw[←h1] at this;X this.symm)
       have e2':j=c+1:=of_decide_eq_true (by have:=cf _2 (e1 (c+1));rw[←h2] at this;X this.symm)
       O
      ·have e1':=(pt (a:=c-1) W H1 W).1 (by have:=cf _2 (e1 (c-1));rw[←h1] at this;X this.symm)
       have e2':=(pt (a:=c+1) W H1 W).1 (by have:=cf _2 (e1 (c+1));rw[←h2] at this;X this.symm)
       have _i:c'=c :=W;subst _i;obtain ⟨x,hx⟩:=py hP hF Hq o_in _I;X hx (by rw[cf _Z x,cf _2 x])
      ·have h1':=cf _2 (e1 (c-1));rw[q2,←h1] at h1';cases h1'
     have Hb:∀y,pD m c y=(p0 p y w1||p0 p y w2):=by
      intro y;rw[←cf _Z y];change p0 p y ((2*m+1)+hF)=_;rw[pj p y hF hG,h00,Hu];simp[GateOp.eval,_o,_p]
     rcases Ht with h1|h2
     ·X hY w1 w2 _o _p
       (fun y Hc=>by
        have hs:=pH e (2*m+1) false d.1 y a1;rw[_b] at hs;X hs.trans (hM a1 W h1 H7 y Hc))
       Hb
     ·X hY w2 w1 _p _o
       (fun y Hc=>by
        have hs:=pH e (2*m+1) false d.1 y a2;rw[_c] at hs;X hs.trans (hM a2 W h2 H8 y Hc))
       (fun y=>by rw[Hb y,Bool.or_comm])
   ·X hu
 have hN:∀k (hk:k< e.size),(e.gates[k]'hk).op=.and ->
   ∀a,pC ((2*m+1)+1) k a (e.gates[k]'hk)->p0 e vU a=false:=by
  intro k hk f a Hh
  cases _q:p0 e vU a with
  | false=>rfl
  | true=>
   exfalso;have HI:k≠H3:=by intro rfl;rw[H5] at f;cases f
   have _f:a≠2*m+1:=fun h=>HI ((s k hk).1 (h▸Hh))
   have h02:¬a< (2*m+1)+1:=by
    intro _m;rw[p7 e vU a _m] at _q;X _f (of_decide_eq_true _q)
   set ta:=a-((2*m+1)+1);have _r:ta< e.size:=by have:=Hh.2;O
   have Hp:a=((2*m+1)+1)+ta :=W;obtain ⟨Hr,H2,Hv⟩:=hh ta _r (Hp▸_q)
   have H0:r.fb[k]'(by rw[l.kept_len];X hk)=true:=by
    cases h:r.fb[k]'(by rw[l.kept_len];X hk) with
    | true=>rfl
    | false=>X absurd ((q k hk).1 h) HI
   obtain ⟨hF,hG,_,_,H9,Ha,_⟩:=p4 d.1 hk H0;have Hm:(p.gates[hF]'hG).op=.and:=H9.trans f;rcases pc d hX k hk with ⟨hI,_,_,_⟩|⟨_,a1,a2,hE,Hk,Hl,_⟩
   ·rw[f] at hI;cases hI
   ·obtain ⟨w1,w2,_o,_p,_b,_c,Hu⟩:=Ha .and a1 a2 (il rfl) f hE Hk Hl
    obtain ⟨c,c1,c2,_N,HP,HK,_,_,_,Hn⟩:=qO hm hP Hj z hG Hm;rw[Hu] at HK;injection HK with hcw1 hcw2;injection hcw2 with hcw2';subst hcw1;subst hcw2';have hrm:=Hh.1;simp only[pa,f,hE,List.mem_cons,List.not_mem_nil,or_false] at hrm;obtain ⟨P,_,_,_s⟩:=Hv;rw[←Hp] at H2;rcases hrm with rfl|rfl
    ·rw[H2] at _b;cases _b
     rcases Hn with ⟨rfl,_⟩|⟨_,hst⟩
     ·X qt (j:=Hr) W (_s.symm.trans (funext fun x=>p7 p x Hr W))
     ·X q3 _N HP (hst.symm.trans _s)
    ·rw[H2] at _c;cases _c
     rcases Hn with ⟨_,hst⟩|⟨rfl,_⟩
     ·X q3 _N HP (hst.symm.trans _s)
     ·X qt (j:=Hr) W (_s.symm.trans (funext fun x=>p7 p x Hr W))
 have _j:∀i< ((2*m+1)+1)+e.size,p0 e vU i=false ->
   ∀y:Fin ((2*m+1)+1)->Bool,
    p0 e y i=p0 e (Fin.snoc (Fin.init y) false) i:=by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih=>
   intro _T HW y;by_cases _n:i< (2*m+1)+1
   ·have h08:i≠2*m+1:=by
     intro rfl;rw[p7 e vU (2*m+1) _n] at HW;simp[vU,e1] at HW
    have _J:i< 2*m+1 :=W;rw[p7 e y i _n,p7 e _ i _n]
    have:(⟨i,_n⟩:Fin ((2*m+1)+1))=Fin.castSucc ⟨i,_J⟩:=Fin.ext rfl
    rw[this,Fin.snoc_castSucc];R
   ·set t:=i-((2*m+1)+1)
    have ht:t< e.size :=W;have H4:i=((2*m+1)+1)+t :=W;rw[H4] at HW ⊢;rcases pc d hX t ht with ⟨hI,_,_,_⟩|⟨hR,a1,a2,hE,Hk,Hl,_⟩
    ·X absurd hI (HF _ (List.getElem_mem ht))
    ·have _k:p0 e vU a1=false:=by
      rcases hR with f|u
      ·X hN t ht f a1 ⟨by simp[pa,f,hE],Hk⟩
      ·rw[pj e vU t ht,u,hE] at HW
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
        id_eq,Bool.or_false,Hk,Hl,↓reduceIte,Bool.or_eq_false_iff] at HW
       X HW.1
     have _l:p0 e vU a2=false:=by
      rcases hR with f|u
      ·X hN t ht f a2 ⟨by simp[pa,f,hE],Hl⟩
      ·rw[pj e vU t ht,u,hE] at HW
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
        id_eq,Bool.or_false,Hk,Hl,↓reduceIte,Bool.or_eq_false_iff] at HW
       X HW.2
     rw[pj e y t ht,pj e _ t ht,hE]
     rcases hR with hop_g|hop_g<;>rw[hop_g] <;>
      simp[GateOp.eval,Hk,Hl,ih a1 W W _k y,ih a2 W W _l y]
 Y ⟨HF,?_,hL,hN,_j,?_⟩
 ·X ⟨H3,Hz,s,q,H5,HO,hC,Hd,_x,HE,_y,
   hK.trans (w.trans (by rw[hH])),
   w.trans (by rw[hH]),hB⟩
 ·intro k hk Ht
  obtain ⟨hV,_K,P,_,_,_s⟩:=hh k hk Ht;X ⟨hV,_K,fun y hy=>zF (by rw[←cf _s y];X hy)⟩
private lemma jF {C:J}
  (u:IsMinimalCircuit 3 C) (hfun:cF 3 C=pq 3) :
  zb 1 C:=by
 have HD:C.size=2:=jw (m:=1) le_rfl u hfun
 have p:∀y:Fin 2->Bool,cF 3 C (Fin.snoc y false)=pq 2 y:=by
  intro y;rw[hfun,z8]
 have hT:∀y:Fin 2->Bool,cF 3 C (Fin.snoc y true)=y ⟨1,by O⟩:=by
  intro y;rw[hfun,qT 2 W]
  have h1:pq 1 (fun i=>y ⟨i.val,by O⟩)=false:=by
   cases hv:pq 1 (fun i=>y ⟨i.val,by O⟩) with
   | false=>rfl
   | true=>rw[px] at hv;obtain ⟨i,j,HM,_,_⟩:=hv;O
  rw[h1,Bool.or_false]
 have Hb:∃y:Fin 2->Bool,cF 3 C (Fin.snoc y false)≠cF 3 C (Fin.snoc y true):=by
  Y ⟨e1 1,?_⟩;rw[p,hT,pW];simp[e1]
 have H2:∃y1 y2:Fin 2->Bool,cF 3 C (Fin.snoc y1 false)≠cF 3 C (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,Hc⟩:=ps (n:=2) W;X ⟨y1,y2,by rw[p,p];X Hc⟩
 have HE:∀D:J,FanInTwo D ->
   (∀y:Fin 2->Bool,cF 2 D y=cF 3 C (Fin.snoc y false))->C.size<=D.size+1:=by
  intro D Hd hU;have He:=q9 2 le_rfl D Hd (funext fun y=>(hU y).trans (p y));simp at He;O
 obtain ⟨hM,HF,hN,Hf,H8,q,z,w,hO,Hx,hP,hV⟩ :=
  zV (n:=2) u false Hb H2 HE
 simp only[Bool.false_eq_true,↓reduceIte] at z;set D:=p3 C 2 false;set st:=p5 C 2 false;have hh:=pk C 2 false u.1;have hC:cF 2 D=pq 2:=funext fun y=>(q6 C 2 false u.1 H2 y).trans (p y);have hQ:D.size=1 :=W;have Hg:C.gates.length=2:=HD;have Hh:D.gates.length=1:=hQ;have hF:0< D.size :=W;have Hy:0< C.size :=W;have hG:1< C.size :=W
 have b:(D.gates[0]'hF).op=.and /\
   ((D.gates[0]'hF).inputs=[0,1]\/(D.gates[0]'hF).inputs=[1,0]) /\
   D.output=2:=by
  have Hi:∃y1 y2:Fin 2->Bool,cF 2 D y1≠cF 2 D y2:=by
   rw[hC];X ps le_rfl
  have hW:D.output=2:=by
   rcases pY hM 0 hF with H0|⟨t',Hz,_,_⟩
   ·X H0
   ·O
  rcases pc hM Hi 0 hF with ⟨hH,a,ha,hX⟩|⟨hY,a1,a2,l,H1,H3,Hc⟩
  ·exfalso
   have h0:cF 2 D e0=false:=by rw[hC,zq]
   rw[pb,hW,pj D e0 0 hF,hH] at h0
   cases l:(D.gates[0]'hF).inputs with
   | nil=>rw[l] at ha;simp at ha
   | cons a0 r=>
    rw[l] at ha h0;simp at ha;subst ha
    simp only[GateOp.eval,List.map_cons,List.headD_cons,hX,↓reduceIte,
     p7 D e0 a0 hX] at h0
    simp[e0] at h0
  ·rcases hY with hI|hop_or
   ·Y ⟨hI,?_,hW⟩
    have:(a1=0/\a2=1)\/(a1=1/\a2=0) :=W
    rcases this with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    ·X il l
    ·X ir l
   ·exfalso
    have h1:cF 2 D (e1 a1)=false:=by rw[hC,pW]
    rw[pb,hW,pj D (e1 a1) 0 hF,hop_or,l] at h1
    have Hj:p0 D (e1 a1:Fin 2->Bool) a1=true:=by
     rw[p7 D _ a1 H1];simp[e1]
    simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
     id_eq,Bool.or_false,H1,H3,↓reduceIte,Hj,Bool.true_or] at h1
    cases h1
 have Hk:z0 D:=by
  intro g hg;obtain ⟨k,hk,rfl⟩:=List.mem_iff_getElem.1 hg;have HG:k=0 :=W;subst HG;have Hl:D.gates[0]'hk=D.gates[0]'hF:=rfl;rw[Hl,b.1];intro h;cases h
 have Hm:z0 C:=by
  Y qK u.1 Hk ?_;intro t ht H4;have H0:=(q t ht).1 H4;subst H0;rw[z];intro h;cases h
 have Hn:∃x1 x2:Fin 3->Bool,cF 3 C x1≠cF 3 C x2:=by
  rw[hfun];X ps W
 have hA:C.output=4:=by
  rcases pY u 1 hG with H0|⟨t',Hz,_,_⟩
  ·X H0
  ·O
 have hJ:hN=0:=by
  by_contra Hc
  have HH:hN=1 :=W;subst HH;have e:cF 3 C (e1 2)=false:=by rw[hfun,pW]
  rw[pb,hA,show (4:ℕ)=3+1 by rfl,pj C (e1 2) 1 hG,z] at e
  have H5:(2:ℕ)< 3+1 :=W
  have HA:p0 C (e1 2:Fin 3->Bool) 2=true:=by
   rw[p7 C _ 2 W];simp[e1]
  rcases hP with l|l<;>rw[l] at e
  ·simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
    id_eq,Bool.or_false,H5,hO,↓reduceIte,HA,Bool.true_or] at e
   cases e
  ·simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
    id_eq,Bool.or_false,H5,hO,↓reduceIte,HA,Bool.or_true] at e
   cases e
 subst hJ
 have hZ:st.fb[1]'(by rw[hh.kept_len];X hG)=true:=by
  cases h:st.fb[1]'(by rw[hh.kept_len];X hG) with
  | true=>rfl
  | false=>have:=(q 1 hG).1 h;O
 obtain ⟨k1,HN,_,HB,Ho,Hp,_⟩:=p4 u.1 hG hZ;have Hq:(p3 C 2 false).size=1:=hQ;have Hr:k1=0 :=W;subst Hr;have d:(C.gates[1]'hG).op=.and:=Ho.symm.trans b.1
 have hK:pC 3 1 3 (C.gates[1]'hG):=by
  rcases pY u 0 Hy with H0|⟨t',Hz,HI,H9⟩
  ·O
  ·have:t'=1 :=W
   subst this;X H9
 have HJ:w=0:=by
  have hD:w=0\/w=1 :=W;rcases hD with h0|h1
  ·X h0
  ·exfalso
   subst h1;rcases pc u Hn 1 hG with ⟨hH,_,_,_⟩|⟨_,a1,a2,hE,H1,H3,hR⟩
   ·rw[d] at hH;cases hH
   ·obtain ⟨w1,w2,HO,HP,Hs,Ht,Hu⟩:=Hp .and a1 a2 (il rfl) d hE H1 H3
    have HC:=hK.1;simp only[pa,d,hE,List.mem_cons,List.not_mem_nil,or_false] at HC
    have hS:st.fc.getD 3 (.const false)=.wire 1 :=
     hV.trans (pd C 2 false 1 W)
    have hB:∀a,a< 4->a≠3->st.fc.getD a (.const false)=.wire 0->a=0:=by
     intro a hX HK Ha
     have:a=0\/a=1\/a=2 :=W
     rcases this with rfl|rfl|rfl
     ·rfl
     ·rw[pd C 2 false 1 W] at Ha;cases Ha
     ·rw[p9 C 2 false u.1] at Ha;cases Ha
    have hL:a1=0\/a2=0:=by
     have f:(D.gates[0]'hF).inputs=[w1,w2]:=Hu;rcases HC with rfl|rfl
     ·rw[hS] at Hs;cases Hs
      have Hv:w2=0:=by
       rcases b.2.1 with h01|h10
       ·rw[h01] at f;injection f with h;O
       ·rw[h10] at f;injection f with _ h;injection h with h';X h'.symm
      subst Hv;X ir (hB a2 H3 hR.symm Ht)
     ·rw[hS] at Ht;cases Ht
      have Hw:w1=0:=by
       rcases b.2.1 with h01|h10
       ·rw[h01] at f;injection f with h;X h.symm
       ·rw[h10] at f;injection f with _ h;injection h with h';O
      subst Hw;X il (hB a1 H1 hR Hs)
    have e:cF 3 C (pe 1)=true:=by rw[hfun,q0 W]
    rw[pb,hA,show (4:ℕ)=3+1 by rfl,
     pj C (pe 1) 1 hG,d,hE] at e
    simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
     id_eq,Bool.and_true,H1,H3,↓reduceIte,Bool.and_eq_true] at e
    rcases hL with rfl|rfl
    ·rw[p7 C (pe 1) 0 W] at e;simp[pe,e2] at e
    ·rw[p7 C (pe 1) 0 W] at e;simp[pe,e2] at e
 subst HJ
 have s:p8 C 0=pD 1 1:=by
  funext x
  change p0 C x 3=pD 1 1 x;rw[show (3:ℕ)=3+0 by rfl,pj C x 0 Hy,z]
  have hl:p0 C x 2=x ⟨2,by O⟩:=p7 C x 2 W
  have H9:p0 C x 0=x ⟨0,by O⟩:=p7 C x 0 W
  rcases hP with l|l<;>rw[l]
  ·simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
    id_eq,Bool.or_false,show (2:ℕ)< 3+0 by O,show (0:ℕ)< 3+0 by O,
    ↓reduceIte,hl,H9]
   apply Bool.eq_iff_iff.2;rw[pG,Bool.or_eq_true]
   constructor
   ·rintro (h2|h0)
    ·X ⟨⟨2,by O⟩,ir rfl,h2⟩
    ·X ⟨⟨0,by O⟩,il rfl,h0⟩
   ·rintro ⟨k,hk,H6⟩
    have:k=⟨0,by O⟩\/k=⟨2,by O⟩:=by
     rcases hk with h|h<;>[left;right]<;>ext<;>dsimp<;>O
    rcases this with rfl|rfl
    ·X ir H6
    ·X il H6
  ·simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
    id_eq,Bool.or_false,show (2:ℕ)< 3+0 by O,show (0:ℕ)< 3+0 by O,
    ↓reduceIte,hl,H9]
   apply Bool.eq_iff_iff.2;rw[pG,Bool.or_eq_true]
   constructor
   ·rintro (h0|h2)
    ·X ⟨⟨0,by O⟩,il rfl,h0⟩
    ·X ⟨⟨2,by O⟩,ir rfl,h2⟩
   ·rintro ⟨k,hk,H6⟩
    have:k=⟨0,by O⟩\/k=⟨2,by O⟩:=by
     rcases hk with h|h<;>[left;right]<;>ext<;>dsimp<;>O
    rcases this with rfl|rfl
    ·X il H6
    ·X ir H6
 have v:p8 C 1=qa 1 {1}:=by
  funext x
  have h1:p8 C 1 x=pq 3 x:=by
   rw[←cf hfun x,pb,hA];R
  rw[h1,zY 1 x];have H7:(Finset.range (2*1)).filter (fun c=>c%2=1)={1}:=by decide
  rw[H7]
 Y ⟨Hm,?_,?_⟩
 ·intro t ht
  have:t=0\/t=1 :=W
  rcases this with rfl|rfl
  ·X il ⟨1,rfl,by O,s⟩
  ·X ir ⟨{1},Finset.singleton_nonempty 1,by simp,v⟩
 ·intro t ht P _ _ HL c _
  have:t=0\/t=1 :=W
  rcases this with rfl|rfl
  ·exfalso;X q3 (r:=1) (c:=1) rfl W (s.symm.trans HL)
  ·rw[hA,show (4:ℕ)=3+1 by rfl,qs C _ 1 ht false]
private lemma j5 {m c:ℕ} (hc:c< 2*m) (x:Fin (2*(m+1)+1)->Bool) :
  pD m c (fun j=>x ⟨j.val,by O⟩)=pD (m+1) c x:=by
 apply Bool.eq_iff_iff.2;simp only[pG]
 constructor
 ·rintro ⟨k,hk,a⟩;X ⟨⟨k.val,by O⟩,hk,a⟩
 ·rintro ⟨k,hk,a⟩
  have b:k.val< 2*m+1 :=W;X ⟨⟨k.val,b⟩,hk,a⟩
private lemma jx {m:ℕ} {P:Finset ℕ} (hP:∀c∈P,c%2=1/\c< 2*m)
  (x:Fin (2*(m+1)+1)->Bool) :
  qa m P (fun j=>x ⟨j.val,by O⟩)=qa (m+1) P x:=by
 apply Bool.eq_iff_iff.2;simp only[qp]
 constructor
 ·rintro ⟨c,b,d,e,f⟩
  have a:=(hP c b).2;Y ⟨c,b,by O,e,?_⟩
  rwa[←j5 a x]
 ·rintro ⟨c,b,d,e,f⟩
  have a:=(hP c b).2;Y ⟨c,b,by O,e,?_⟩
  rwa[j5 a x]
private lemma pB {n:ℕ} {C:J}
  (a:∃x1 x2:V n,cF n C x1≠cF n C x2) :
  C.output< n+C.size:=by
 by_contra hge
 obtain ⟨x1,x2,b⟩:=a;X b (by rw[pb,pb,z3 C x1 C.output W,z3 C x2 C.output W])
private lemma pm {C:J} {n t a1 a2:ℕ} (x:V n) (ht:t< C.size)
  (b:(C.gates[t]'ht).op=.and) (a:(C.gates[t]'ht).inputs=[a1,a2])
  (c:a1< n+t) (d:a2< n+t) :
  p0 C x (n+t)=(p0 C x a1&&p0 C x a2):=by
 rw[pj C x t ht,b,a];simp[GateOp.eval,c,d]
private lemma p6 {C:J} {n t a1 a2:ℕ} (x:V n) (ht:t< C.size)
  (b:(C.gates[t]'ht).op=.or) (a:(C.gates[t]'ht).inputs=[a1,a2])
  (c:a1< n+t) (d:a2< n+t) :
  p0 C x (n+t)=(p0 C x a1||p0 C x a2):=by
 rw[pj C x t ht,b,a];simp[GateOp.eval,c,d]
private lemma pF {C:J} {n t0 t a1 a2:ℕ} (x:V n)
  (b:t0< C.size) (v0:Bool) (ht:t< C.size) (c:t≠t0)
  (d:(C.gates[t]'ht).op=.and) (a:(C.gates[t]'ht).inputs=[a1,a2])
  (e:a1< n+t) (f:a2< n+t) :
  pl C x t0 v0 (n+t)=(pl C x t0 v0 a1&&pl C x t0 v0 a2):=by
 rw[zs C x t0 b v0 t ht c,d,a];simp[GateOp.eval,e,f]
private lemma pJ {C:J} {n t0 t a1 a2:ℕ} (x:V n)
  (b:t0< C.size) (v0:Bool) (ht:t< C.size) (c:t≠t0)
  (d:(C.gates[t]'ht).op=.or) (a:(C.gates[t]'ht).inputs=[a1,a2])
  (e:a1< n+t) (f:a2< n+t) :
  pl C x t0 v0 (n+t)=(pl C x t0 v0 a1||pl C x t0 v0 a2):=by
 rw[zs C x t0 b v0 t ht c,d,a];simp[GateOp.eval,e,f]
private lemma q4 {C:J} {n q:ℕ} {b:Bool} (c:FanInTwo C)
  (a:∀t (ht:t< C.size),(p5 C n b).fb[t]'(by rw[(pk C n b c).kept_len];X ht)=false↔t=q)
  {t:ℕ} (ht:t< C.size) (d:t≠q) :
  (p5 C n b).fb[t]'(by rw[(pk C n b c).kept_len];X ht)=true:=by
 cases hk:(p5 C n b).fb[t]'(by rw[(pk C n b c).kept_len];X ht) with
 | true=>rfl
 | false=>X absurd ((a t ht).1 hk) d
private lemma pE {C:J} {n g h:ℕ} {b:Bool} (c:FanInTwo C)
  (a:∀t (ht:t< C.size),(p5 C n b).fb[t]'(by rw[(pk C n b c).kept_len];X ht)=false↔(t=g\/t=h))
  {t:ℕ} (ht:t< C.size) (d:t≠g) (e:t≠h) :
  (p5 C n b).fb[t]'(by rw[(pk C n b c).kept_len];X ht)=true:=by
 cases hk:(p5 C n b).fb[t]'(by rw[(pk C n b c).kept_len];X ht) with
 | true=>rfl
 | false=>rcases (a t ht).1 hk with rfl|rfl<;>contradiction
private lemma jy (n:ℕ) :
  Fin.snoc (e1 n:Fin (n+1)->Bool) false=(e1 n:Fin (n+2)->Bool):=by
 funext j;by_cases hj:j.val< n+1
 ·have:j=Fin.castSucc ⟨j.val,hj⟩:=Fin.ext rfl;rw[this,Fin.snoc_castSucc];R
 ·have:j=Fin.last (n+1):=Fin.ext (by have:=j.isLt;simp;O)
  rw[this,Fin.snoc_last];simp[e1]
private lemma jL (n:ℕ) :
  Fin.snoc (e1 n:Fin (n+1)->Bool) true=(e2 n (n+1):Fin (n+2)->Bool):=by
 funext j;by_cases hj:j.val< n+1
 ·have:j=Fin.castSucc ⟨j.val,hj⟩:=Fin.ext rfl
  rw[this,Fin.snoc_castSucc];simp only[e1,e2,Fin.val_castSucc];apply Bool.eq_iff_iff.2;simp;O
 ·have:j=Fin.last (n+1):=Fin.ext (by have:=j.isLt;simp;O)
  rw[this,Fin.snoc_last];simp[e2]
private def zc {m:ℕ} (x:Fin (2*m+3)->Bool):Fin (2*m+1)->Bool :=
 fun j=>x ⟨j.val,by have:=j.isLt;O⟩
private lemma q8 {C:J} {n:ℕ} {b:Bool} (a:FanInTwo C)
  (d:∃y1 y2:V n,cF (n+1) C (Fin.snoc y1 b)≠cF (n+1) C (Fin.snoc y2 b)) :
  (p5 C n b).fc.getD C.output (.const false)=.wire (p3 C n b).output:=by
 have h1:(p3 C n b).output =
   match (p5 C n b).fc.getD C.output (.const false) with
   | .wire w=>w|.const _=>n+(p5 C n b).gates.length:=rfl
 cases he:(p5 C n b).fc.getD C.output (.const false) with
 | const c=>X absurd rfl (pL a d he)
 | wire w=>rw[he] at h1;rw[h1]
private lemma zW {C:J} {n i w:ℕ} {b:Bool} (e:FanInTwo C)
  (hi:i< n+1+C.size) (he:(p5 C n b).fc.getD i (.const false)=.wire w) :
  w< n+(p3 C n b).size:=by
 have a:=pk C n b e;have c:i< (p5 C n b).fc.length:=by rw[a.env_len,a.kept_len];X hi
 rw[List.getD_eq_getElem _ _ c] at he;have d:qw.wire w∈(p5 C n b).fc:=he▸List.getElem_mem c;X a.env_lt (.wire w) d
private lemma jh {C:J} {n q z:ℕ} (hq:q< C.size)
  (a:(C.gates[q]'hq).op=.or)
  (b:(C.gates[q]'hq).inputs=[n,z]\/(C.gates[q]'hq).inputs=[z,n])
  (hz:z< n+1+q) :
  p0 C (e1 n:Fin (n+1)->Bool) (n+1+q)=true:=by
 rcases b with hins|hins
 ·rw[p6 _ hq a hins W hz,p7 C _ n W];simp[e1]
 ·rw[p6 _ hq a hins hz W,p7 C _ n W];simp[e1]
private lemma jV {C:J} {n q:ℕ} (hq:q< C.size)
  (l:IsMinimalCircuit (n+1) C)
  (m:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2)
  (a:∀k (hk:k< C.size),pC (n+1) k n (C.gates[k]'hk)↔k=q)
  (f:∀k (hk:k< C.size),p0 C (e1 n:Fin (n+1)->Bool) (n+1+k)=true->(C.gates[k]'hk).op=.or) :
  ∀i< n+1+q,i≠n->p0 C (e1 n:Fin (n+1)->Bool) i=false:=by
 intro i
 induction i using Nat.strong_induction_on with
 | ind i ih=>
  intro p r;by_cases s:i< n+1
  ·rw[p7 C _ i s];simp[e1,r]
  ·set k:=i-(n+1)
   have hk:k< C.size :=W;have g:i=n+1+k :=W;rw[g]
   cases hvk:p0 C (e1 n:Fin (n+1)->Bool) (n+1+k) with
   | false=>rfl
   | true=>
    exfalso;have b:=f k hk hvk;rcases pc l m k hk with ⟨j,_,_,_⟩|⟨_,b1,b2,c,t,u,_⟩
    ·rw[b] at j;cases j
    ·have d:b1≠n:=fun h=>by have:=(a k hk).1 ⟨by simp[pa,b,c,h],by O⟩;O
     have e:b2≠n:=fun h=>by have:=(a k hk).1 ⟨by simp[pa,b,c,h],by O⟩;O
     rw[p6 _ hk b c t u,Bool.or_eq_true] at hvk;rcases hvk with h1|h2
     ·rw[ih b1 W W d] at h1;cases h1
     ·rw[ih b2 W W e] at h2;cases h2
private lemma pO {C:J} {n:ℕ} {b:Bool} (c:FanInTwo C)
  {t1 t2:ℕ} (d:t1< C.size) (e:t2< C.size)
  (i:(p5 C n b).fb[t1]'(by rw[(pk C n b c).kept_len];X d)=true)
  (j:(p5 C n b).fb[t2]'(by rw[(pk C n b c).kept_len];X e)=true)
  {w:ℕ}
  (k:(p5 C n b).fc.getD (n+1+t1) (.const false)=.wire w)
  (l:(p5 C n b).fc.getD (n+1+t2) (.const false)=.wire w) :
  t1=t2:=by
 have a:=pk C n b c;have f:C.gates.length=C.size:=rfl;have g:n+1+t1< (p5 C n b).fc.length:=by rw[a.env_len,a.kept_len,f];O
 have h:n+1+t2< (p5 C n b).fc.length:=by rw[a.env_len,a.kept_len,f];O
 have h1:(p5 C n b).fc[n+1+t1]'g=.wire w:=by rwa[←List.getD_eq_getElem _ (.const false) g]
 have h2:(p5 C n b).fc[n+1+t2]'h=.wire w:=by rwa[←List.getD_eq_getElem _ (.const false) h]
 X a.kept_inj t1 t2 d e i j (h1.trans h2.symm)
private lemma pp {C:J} {n:ℕ} {b:Bool}
  (e:IsMinimalCircuit (n+1) C) (y:z0 C)
  (z:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2)
  {t:ℕ} (ht:t< C.size)
  (i:(p5 C n b).fb[t]'(by rw[(pk C n b e.1).kept_len];X ht)=true)
  {kt:ℕ} (s:kt< (p3 C n b).size)
  (f:(p5 C n b).fc.getD (n+1+t) (.const false)=.wire (n+kt))
  {a wa:ℕ} (g:pC (n+1) t a (C.gates[t]'ht))
  (c:(p5 C n b).fc.getD a (.const false)=.wire wa) :
  pC n kt wa ((p3 C n b).gates[kt]'s):=by
 obtain ⟨u,hh,_,d,m,p,_⟩:=p4 e.1 ht i;rw[f] at d;have q:u=kt:=by simp only[qw.wire.injEq] at d;O
 subst q;rcases pc e z t ht with ⟨r,_,_,_⟩|⟨h,a1,a2,j,hA,hB,_⟩
 ·X absurd r (y _ (List.getElem_mem ht))
 ·rcases h with hop_eq|hop_eq<;>(
   obtain ⟨w1,w2,hC,hD,v,w,k⟩:=p _ a1 a2 (by simp[hop_eq]) hop_eq j hA hB
   have x:=g.1;simp only[pa,hop_eq,j,List.mem_cons,List.not_mem_nil,or_false] at x;have l:((p3 C n b).gates[u]'s).op=_:=m.trans hop_eq;rcases x with rfl|rfl
   ·rw[c] at v;cases v;X ⟨by simp[pa,l,k],hC⟩
   ·rw[c] at w;cases w;X ⟨by simp[pa,l,k],hD⟩)
private lemma zN {C:J} {n:ℕ} {b:Bool}
  (d:IsMinimalCircuit (n+1) C) (hA:z0 C)
  (hB:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2)
  (f:IsMinimalCircuit n (p3 C n b))
  (q:∃y1 y2:V n,cF n (p3 C n b) y1≠cF n (p3 C n b) y2)
  {t:ℕ} (ht:t< C.size)
  (g:(p5 C n b).fb[t]'(by rw[(pk C n b d.1).kept_len];X ht)=true)
  {a1 a2 w:ℕ} (y:a1≠a2)
  (hC:pC (n+1) t a1 (C.gates[t]'ht)) (hD:pC (n+1) t a2 (C.gates[t]'ht))
  (z:(p5 C n b).fc.getD a1 (.const false)=.wire w)
  (hh:(p5 C n b).fc.getD a2 (.const false)=.wire w):False:=by
 obtain ⟨kt,hE,_,_,r,s,_⟩:=p4 d.1 ht g;rcases pc d hB t ht with ⟨u,_,_,_⟩|⟨e,b1,b2,i,hF,hG,_⟩
 ·X absurd u (hA _ (List.getElem_mem ht))
 ·have j:=hC.1;have k:=hD.1
  rcases e with hop_eq|hop_eq<;>(
   simp only[pa,hop_eq,i,List.mem_cons,List.not_mem_nil,or_false] at j k;obtain ⟨w1,w2,_,_,m,p,v⟩:=s _ b1 b2 (by simp[hop_eq]) hop_eq i hF hG
   have l:w1=w2:=by
    rcases j with rfl|rfl<;>rcases k with h|h
    ·X absurd h.symm y
    ·rw[z] at m;rw[←h,hh] at p;cases m;cases p;R
    ·rw[z] at p;rw[←h,hh] at m;cases m;cases p;R
    ·X absurd h.symm y
   rcases pc f q kt hE with ⟨a,_,_,_⟩|⟨_,_,_,c,_,_,x⟩
   ·rw[r,hop_eq] at a;cases a
   ·rw[v] at c;cases c;X x l)
private lemma j3 {C:J} {n:ℕ}
  (e:IsMinimalCircuit (n+1) C) (w:z0 C)
  (x:∃x1 x2:Fin (n+1)->Bool,cF (n+1) C x1≠cF (n+1) C x2)
  (b:∀k (hk:k< (p3 C n true).size),((p3 C n true).gates[k]'hk).op=.and ->
   ∀a,pC n k a ((p3 C n true).gates[k]'hk) ->
    p0 (p3 C n true) (e1 (n-1):V n) a=false)
  {t:ℕ} (ht:t< C.size)
  (g:(p5 C n true).fb[t]'(by rw[(pk C n true e.1).kept_len];X ht)=true)
  (l:¬zG C n (n+1+t)) {a:ℕ} (c:pC (n+1) t a (C.gates[t]'ht)) :
  ¬zG C n a:=by
 intro ⟨wa,r,i⟩;obtain ⟨kt,s,_,d,h,m,_⟩:=p4 e.1 ht g;have f:=pp e w x ht g s d c r;rcases pc e x t ht with ⟨u,_,_,_⟩|⟨j,a1,a2,p,hA,hB,_⟩
 ·X absurd u (w _ (List.getElem_mem ht))
 ·rcases j with hop_and|hop_or
  ·have q:=b kt s (h.trans hop_and) wa f
   rw[i] at q;cases q
  ·obtain ⟨w1,w2,hC,hD,y,z,v⟩:=m .or a1 a2 (ir rfl) hop_or p hA hB
   have hh:=c.1;simp only[pa,hop_or,p,List.mem_cons,List.not_mem_nil,or_false] at hh;apply l;Y (pM d).2 ?_;rw[p6 _ s (h.trans hop_or) v hC hD,Bool.or_eq_true];rcases hh with rfl|rfl
   ·rw[r] at y;cases y;X il i
   ·rw[r] at z;cases z;X ir i
private structure zp (m:ℕ) (C:J) where
 hm:1<=m
 f0:IsMinimalCircuit (2*m+3) C
 fd:cF (2*m+3) C=pq (2*m+3)
 fJ:z0 C
 fn:∃x1 x2:Fin (2*m+3)->Bool,cF (2*m+3) C x1≠cF (2*m+3) C x2
 f3:ℕ
 f4:ℕ
 w:ℕ
 u:ℕ
 f9:f3< C.size
 fa:f4< C.size
 fP:f3< f4
 fi:∀t (ht:t< C.size),pC (2*m+3) t (2*m+2) (C.gates[t]'ht)↔t=f3
 fl:(C.gates[f3]'f9).op=.or
 fs:w< 2*m+3+f3
 fM:w≠2*m+2
 ft:(C.gates[f3]'f9).inputs=[2*m+2,w]\/(C.gates[f3]'f9).inputs=[w,2*m+2]
 fh:(p5 C (2*m+2) true).fc.getD (2*m+3+f3) (.const false)=.const true
 fe:∀t (ht:t< C.size),
  (p5 C (2*m+2) true).fb[t]'(by rw[(pk C (2*m+2) true f0.1).kept_len];X ht)=false ↔
  (t=f3\/t=f4)
 fj:∀t (ht:t< C.size),pC (2*m+3) t (2*m+3+f3) (C.gates[t]'ht)↔t=f4
 fm:(C.gates[f4]'fa).op=.and
 fu:u< 2*m+3+f4
 fU:u≠2*m+3+f3
 fy:(C.gates[f4]'fa).inputs=[2*m+3+f3,u]\/(C.gates[f4]'fa).inputs=[u,2*m+3+f3]
 fz:(p5 C (2*m+2) true).fc.getD (2*m+3+f4) (.const false) =
      (p5 C (2*m+2) true).fc.getD u (.const false)
 f7:IsMinimalCircuit (2*m+2) (p3 C (2*m+2) true)
 fr:∀y:Fin (2*m+2)->Bool,
  cF (2*m+2) (p3 C (2*m+2) true) y=(y (Fin.last (2*m+1))||pq (2*m+1) (Fin.init y))
 fC:z0 (p3 C (2*m+2) true)
 fq:∃y1 y2:Fin (2*m+2)->Bool,
  cF (2*m+2) (p3 C (2*m+2) true) y1≠cF (2*m+2) (p3 C (2*m+2) true) y2
 fO:∃y1 y2:Fin (2*m+1)->Bool,
  cF (2*m+2) (p3 C (2*m+2) true) (Fin.snoc y1 false) ≠
   cF (2*m+2) (p3 C (2*m+2) true) (Fin.snoc y2 false)
 fN:∃y1 y2:Fin (2*m+2)->Bool,
  cF (2*m+3) C (Fin.snoc y1 true)≠cF (2*m+3) C (Fin.snoc y2 true)
 f5:IsMinimalCircuit (2*m+1) (p3 (p3 C (2*m+2) true) (2*m+1) false)
 f8:cF (2*m+1) (p3 (p3 C (2*m+2) true) (2*m+1) false)=pq (2*m+1)
 f6:zb m (p3 (p3 C (2*m+2) true) (2*m+1) false)
 fv:ℕ
 fD:fv< (p3 C (2*m+2) true).size
 fB:∀k (hk:k< (p3 C (2*m+2) true).size),
  pC (2*m+2) k (2*m+1) ((p3 C (2*m+2) true).gates[k]'hk)↔k=fv
 ff:∀k (hk:k< (p3 C (2*m+2) true).size),
  (p5 (p3 C (2*m+2) true) (2*m+1) false).fb[k]'(by rw[(pk (p3 C (2*m+2) true) (2*m+1) false f7.1).kept_len];X hk)=false↔k=fv
 fI:((p3 C (2*m+2) true).gates[fv]'fD).op=.or
 z'':ℕ
 fg:ℕ
 fA:fg< (p3 (p3 C (2*m+2) true) (2*m+1) false).size
 fw:z''< 2*m+2+fv
 fR:z''≠2*m+1
 fK:((p3 C (2*m+2) true).gates[fv]'fD).inputs=[2*m+1,z''] \/
      ((p3 C (2*m+2) true).gates[fv]'fD).inputs=[z'',2*m+1]
 fx:(p5 (p3 C (2*m+2) true) (2*m+1) false).fc.getD (2*m+2+fv) (.const false) =
       .wire (2*m+1+fg)
 fL:(p5 (p3 C (2*m+2) true) (2*m+1) false).fc.getD z'' (.const false) =
       .wire (2*m+1+fg)
 fG:pX m (p8 (p3 (p3 C (2*m+2) true) (2*m+1) false) fg)
 fk:∀k (hk:k< (p3 C (2*m+2) true).size),
  p0 (p3 C (2*m+2) true) (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+k)=true ->
  ((p3 C (2*m+2) true).gates[k]'hk).op=.or
 fp:∀k (hk:k< (p3 C (2*m+2) true).size),
  ((p3 C (2*m+2) true).gates[k]'hk).op=.and ->
  ∀a,pC (2*m+2) k a ((p3 C (2*m+2) true).gates[k]'hk) ->
   p0 (p3 C (2*m+2) true) (e1 (2*m+1):Fin (2*m+2)->Bool) a=false
 fQ:∀k (hk:k< (p3 C (2*m+2) true).size),
  p0 (p3 C (2*m+2) true) (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+k)=true ->
  ∃w''':ℕ,
   (p5 (p3 C (2*m+2) true) (2*m+1) false).fc.getD (2*m+2+k) (.const false)=.wire w''' /\
   ∀y:Fin (2*m+1)->Bool,
    p0 (p3 (p3 C (2*m+2) true) (2*m+1) false) y w'''=true ->
    pq (2*m+1) y=true
 fo:zG C (2*m+2) C.output
 fH:zG C (2*m+2) u
 fT:zG C (2*m+2) (2*m+3+f4)
 fE:¬zG C (2*m+2) w
private lemma kC {m:ℕ} (hm:1<=m) {C:J}
  (g:IsMinimalCircuit (2*m+3) C)
  (hfun:cF (2*m+3) C=pq (2*m+3))
  (Hx:∀D:J,IsMinimalCircuit (2*m+1) D->cF (2*m+1) D=pq (2*m+1)->zb m D) :
  Nonempty (zp m C):=by
 have Hy:C.size=3*m+2:=by have:=jw (m:=m+1) W g hfun;O
 have Hb:∃x1 x2:Fin (2*m+3)->Bool,cF (2*m+3) C x1≠cF (2*m+3) C x2:=by
  rw[hfun];X ps W
 have p:∀y:Fin (2*m+2)->Bool,cF (2*m+3) C (Fin.snoc y false)=pq (2*m+2) y:=by
  intro y;rw[hfun];X z8 (2*m+2) y
 have d:∀y:Fin (2*m+2)->Bool,
   cF (2*m+3) C (Fin.snoc y true)=(y (Fin.last (2*m+1))||pq (2*m+1) (Fin.init y)):=by
  intro y;rw[hfun,qT (2*m+2) W y];R
 have Hl:∃y:Fin (2*m+2)->Bool,cF (2*m+3) C (Fin.snoc y false)≠cF (2*m+3) C (Fin.snoc y true):=by
  Y ⟨e1 (2*m+1),?_⟩;rw[p,d,pW];simp[e1]
 have Hm:∃y1 y2:Fin (2*m+2)->Bool,cF (2*m+3) C (Fin.snoc y1 false)≠cF (2*m+3) C (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,Hc⟩:=ps (n:=2*m+2) W;X ⟨y1,y2,by rw[p,p];X Hc⟩
 have hL:∃y1 y2:Fin (2*m+2)->Bool,cF (2*m+3) C (Fin.snoc y1 true)≠cF (2*m+3) C (Fin.snoc y2 true):=by
  Y ⟨e0,e1 (2*m+1),?_⟩;rw[d,d];have h0:(e0:Fin (2*m+2)->Bool) (Fin.last (2*m+1))=false:=rfl;have h1:(e1 (2*m+1):Fin (2*m+2)->Bool) (Fin.last (2*m+1))=true:=by simp[e1]
  have Hz:Fin.init (e0:Fin (2*m+2)->Bool)=e0:=rfl;rw[h0,h1,Hz,zq];simp
 have Hn:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m+2)->Bool,cF (2*m+2) D y=cF (2*m+3) C (Fin.snoc y false))->C.size<=D.size+1:=by
  intro D hM Hd;have Ho:=q9 (2*(m+1)) W D hM (funext fun y=>(Hd y).trans (p y));simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left (m+1) (by O:0< 2)] at Ho;O
 obtain ⟨_,_,hh,a,j,_,l,w,hA,hY,hN,_⟩ :=
  zV (n:=2*m+2) g false Hl Hm Hn
 simp only[Bool.false_eq_true,↓reduceIte] at l
 have f:(p5 C (2*m+2) true).fc.getD (2*m+3+hh) (.const false)=.const true:=by
  have Hv:=(pR (n:=2*m+2) (b:=true) g.1 a).2.2 l;have hZ:=p9 C (2*m+2) true g.1;rcases hN with hins|hins
  ·X ((Hv (2*m+2) w hins W hA).1 (il hZ)).1
  ·X ((Hv w (2*m+2) hins hA W).1 (ir hZ)).1
 have Hp:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m+2)->Bool,cF (2*m+2) D y=cF (2*m+3) C (Fin.snoc y true))->C.size<=D.size+2:=by
  intro D hM Hd
  have HA:=zl (pq (2*m+1)) (ps W)
   (fun _ _ _ _ h=>h) (3*m-1)
   (fun E Hq He=>by
    have h:=q9 (2*m+1) W E Hq He;have H4:(2*m+1)%2≠0 :=W;have H5:(2*m+1)/2=m :=W;simp only[H4,↓reduceIte,H5] at h;X h)
   D hM (fun y=>(Hd y).trans (d y))
  O
 obtain ⟨q,Hw,H0,hE,Hr,hB,i,hC,u,hO,Hf,hP,r⟩ :=
  zh (n:=2*m+2) g true true hL hh a ((j hh a).2 rfl) f Hp
 simp only[↓reduceIte] at hC;set hJ:=p3 C (2*m+2) true
 have e:∀y:Fin (2*m+2)->Bool,cF (2*m+2) hJ y=(y (Fin.last (2*m+1))||pq (2*m+1) (Fin.init y)):=by
  intro y;rw[q6 C (2*m+2) true g.1 hL y,d]
 have Hg:∃y1 y2:Fin (2*m+2)->Bool,cF (2*m+2) hJ y1≠cF (2*m+2) hJ y2:=by
  obtain ⟨y1,y2,Hc⟩:=hL;X ⟨y1,y2,by rw[e,e,←d,←d];X Hc⟩
 have c:∀y:Fin (2*m+1)->Bool,cF (2*m+2) hJ (Fin.snoc y false)=pq (2*m+1) y:=by
  intro y;rw[e,Fin.snoc_last,Fin.init_snoc,Bool.false_or]
 have H6:∃y:Fin (2*m+1)->Bool,cF (2*m+2) hJ (Fin.snoc y false)≠cF (2*m+2) hJ (Fin.snoc y true):=by
  Y ⟨e0,?_⟩;rw[c,e,Fin.snoc_last,zq];simp
 have hF:∃y1 y2:Fin (2*m+1)->Bool,cF (2*m+2) hJ (Fin.snoc y1 false)≠cF (2*m+2) hJ (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,Hc⟩:=ps (n:=2*m+1) W;X ⟨y1,y2,by rw[c,c];X Hc⟩
 have H7:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m+1)->Bool,cF (2*m+1) D y=cF (2*m+2) hJ (Fin.snoc y false))->hJ.size<=D.size+1:=by
  intro D hM Hd;have h:=q9 (2*m+1) W D hM (funext fun y=>(Hd y).trans (c y));have H4:(2*m+1)%2≠0 :=W;have H5:(2*m+1)/2=m :=W;simp only[H4,↓reduceIte,H5] at h;O
 obtain ⟨hG,_,_,_,_,_,_,_,_,_,_,_⟩:=zV q false H6 hF H7;set H8:=p3 hJ (2*m+1) false
 have hH:cF (2*m+1) H8=pq (2*m+1) :=
  funext fun y=>by rw[q6 hJ (2*m+1) false q.1 hF y,c]
 have hI:zb m H8:=Hx H8 hG hH
 obtain ⟨H1,⟨HB,Hs,hK,s,hT,HC,Hh,H9,hU,hV,hW,
   hQ,hR,v⟩,x,hD,_,z⟩ :=
  km hm q e hI
 have Ht:z0 C:=qK g.1 H1 fun t ht Hi=>by
  rcases (i t ht).1 Hi with rfl|rfl
  ·rw[l];intro h;cases h
  ·rw[hC];intro h;cases h
 have k:zG C (2*m+2) C.output:=by
  Y ⟨hJ.output,q8 g.1 hL,?_⟩;rw[←pb,e];simp[e1]
 have H2:cF (2*m+3) C (e1 (2*m+1))=false:=by rw[hfun];X pW _ _
 have hS:zG C (2*m+2) u:=by
  by_contra hnotU
  have h1:=qL g Ht W Hb a hE Hr i
   f hC hP hO r x (e1 (2*m+1)) (by simp only[e1,decide_eq_true_eq];O) (ir hnotU)
   C.output (pB Hb) k
  rw[←pb,H2] at h1;cases h1
 have Ha:zG C (2*m+2) (2*m+3+H0):=by
  obtain ⟨wu,HD,Hu⟩:=hS;X ⟨wu,r.trans HD,Hu⟩
 have hX:¬zG C (2*m+2) w:=by
  intro HE
  have Hj:=qI g.1 j hB (e1 (2*m+1):Fin (2*m+2)->Bool)
   w W hY W
  rw[jy (2*m+1),jL (2*m+1)] at Hj;have H3:p0 C (e1 (2*m+1):Fin (2*m+3)->Bool) w=true:=Hj.trans (jK g.1 W HE)
  have Hk:p0 C (e1 (2*m+1):Fin (2*m+3)->Bool) (2*m+3+hh)=true:=by
   rcases hN with hins|hins
   ·rw[p6 _ a l hins W hA,H3,Bool.or_true]
   ·rw[p6 _ a l hins hA W,H3,Bool.true_or]
  have h1:=qL g Ht W Hb a hE Hr i
   f hC hP hO r x (e1 (2*m+1)) (by simp only[e1,decide_eq_true_eq];O) (il Hk)
   C.output (pB Hb) k
  rw[←pb,H2] at h1;cases h1
 X ⟨⟨
  hm,g,hfun,Ht,Hb,hh,H0,w,u,a,hE,Hr,j,l,hA,hY,
  hN,f,i,hB,hC,hO,Hf,hP,r,q,e,H1,Hg,
  hF,hL,hG,hH,hI,HB,Hs,hK,s,hT,HC,Hh,
  H9,hU,hV,hW,hQ,hR,v,x,hD,
  z,k,hS,Ha,hX
 ⟩⟩
private lemma qX {m:ℕ} {C:J} (d:zp m C) :
  let hI:=p5 C (2*m+2) true;let hC:=p3 C (2*m+2) true;let hD:=p5 hC (2*m+1) false;let f:=p3 hC (2*m+1) false
  ∀i< 2*m+3+C.size,i≠2*m+2->i≠2*m+3+d.f3->¬zG C (2*m+2) i ->
   ∃i'' i''':ℕ,i''< 2*m+2+hC.size/\i'''< 2*m+1+f.size /\
    hI.fc.getD i (.const false)=.wire i'' /\
    hD.fc.getD i'' (.const false)=.wire i''' /\
    (2*m+3<=i->2*m+1<=i''') /\
    (∀x:Fin (2*m+3)->Bool,p0 C x i=p0 f (zc x) i'''):=by
 dsimp only;set hI:=p5 C (2*m+2) true;set hC:=p3 C (2*m+2) true;set hD:=p5 hC (2*m+1) false;set f:=p3 hC (2*m+1) false;intro i
 induction i using Nat.strong_induction_on with
 | ind i ih=>
  intro H9 hJ hK c;by_cases Hg:i< 2*m+3
  ·have hE:i< 2*m+1:=by
    by_contra hge;have hW:i=2*m+1 :=W
    X c (hW▸zE (C:=C) (n:=2*m+2) W)
   Y ⟨i,i,by O,by O,
    pd C (2*m+2) true i W,
    pd hC (2*m+1) false i hE,by O,fun x=>?_⟩
   have h1:=p7 f (zc x) i hE;rw[p7 C x i W,h1];R
  ·set t:=i-(2*m+3)
   have ht:t< C.size :=W;have hL:i=2*m+3+t :=W;rw[hL] at hK c ⊢;have H5:t≠d.f3 :=W;have H6:t≠d.f4:=fun h=>c (h▸d.fT);have k:=pE d.f0.1 d.fe ht H5 H6;obtain ⟨hX,hH,_,q,l,hF,_⟩:=p4 d.f0.1 ht k;have hV:hX< hC.size:=hH
   have p:hX≠d.fv:=fun hW=>
    c ((pM (hW▸q)).2 (jh d.fD d.fI d.fK d.fw))
   have r:=q4 d.f7.1 d.ff hH p;obtain ⟨hM,hN,_,hB,s,u,_⟩:=p4 d.f7.1 hH r;have e:hM< f.size:=hN;Y ⟨2*m+2+hX,2*m+1+hM,by O,by O,q,hB,by O,fun x=>?_⟩
   rcases pc d.f0 d.fn t ht with ⟨hY,_,_,_⟩|⟨v,a1,a2,w,hO,hP,_⟩
   ·X absurd hY (d.fJ _ (List.getElem_mem ht))
   ·have hG:∀a,(a=a1\/a=a2)->a< 2*m+3+t ->
      a≠2*m+2/\a≠2*m+3+d.f3/\¬zG C (2*m+2) a:=by
     intro a hZ H0
     have g:pC (2*m+3) t a (C.gates[t]'ht):=by
      rcases v with h|h<;>X ⟨by simp[pa,h,w,hZ],H0⟩
     X ⟨fun h=>H5 ((d.fi t ht).1 (h▸g)),
         fun h=>H6 ((d.fj t ht).1 (h▸g)),
         j3 d.f0 d.fJ d.fn d.fp ht k c g⟩
    obtain ⟨Ha,Hb,Hc⟩:=hG a1 (il rfl) hO;obtain ⟨Hd,He,Hf⟩:=hG a2 (ir rfl) hP;obtain ⟨b1,c1,_,_,hQ,hS,_,H7⟩:=ih a1 W W Ha Hb Hc;obtain ⟨b2,c2,_,_,hT,hU,_,H8⟩:=ih a2 W W Hd He Hf;rcases v with hop_eq|hop_eq
    ·obtain ⟨w1,w2,H1,H2,y,z,j⟩:=hF .and a1 a2 (il rfl) hop_eq w hO hP
     obtain ⟨u1,u2,H3,H4,hh,hA,b⟩:=u .and w1 w2 (il rfl) (l.trans hop_eq) j H1 H2;rw[hQ] at y;cases y;rw[hT] at z;cases z;rw[hS] at hh;cases hh;rw[hU] at hA;cases hA;have hR:=pm (C:=f) (zc x) e (s.trans (l.trans hop_eq)) b H3 H4;rw[pm x ht hop_eq w hO hP,hR,H7 x,H8 x]
    ·obtain ⟨w1,w2,H1,H2,y,z,j⟩:=hF .or a1 a2 (ir rfl) hop_eq w hO hP
     obtain ⟨u1,u2,H3,H4,hh,hA,b⟩:=u .or w1 w2 (ir rfl) (l.trans hop_eq) j H1 H2;rw[hQ] at y;cases y;rw[hT] at z;cases z;rw[hS] at hh;cases hh;rw[hU] at hA;cases hA;have hR:=p6 (C:=f) (zc x) e (s.trans (l.trans hop_eq)) b H3 H4;rw[p6 x ht hop_eq w hO hP,hR,H7 x,H8 x]
private lemma zX {m:ℕ} {C:J} (d:zp m C)
  {i:ℕ} (k:i< (p3 C (2*m+2) true).size)
  (g:p0 (p3 C (2*m+2) true) (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+i)=true) :
  ∃a:ℕ,∃(e:a< (p3 (p3 C (2*m+2) true) (2*m+1) false).size),
   (p5 (p3 C (2*m+2) true) (2*m+1) false).fc.getD (2*m+2+i) (.const false) =
    .wire (2*m+1+a) /\
   pX m (p8 (p3 (p3 C (2*m+2) true) (2*m+1) false) a):=by
 set l:=p3 (p3 C (2*m+2) true) (2*m+1) false;obtain ⟨h,f,p⟩:=d.fQ i k g;have b:h< 2*m+1+l.size:=zW d.f7.1 W f;rcases qH d.f6 h b with ⟨j,hj,_,n⟩|⟨_,_,_,c,_,q,n⟩|⟨a,e,rfl,r⟩
 ·have hp:=p (e1 j) (by rw[cf n (e1 j)];simp[e1]);rw[pW] at hp;cases hp
 ·have hp:=p (e1 (c-1)) (by rw[cf n (e1 (c-1))];X (pt W q W).2 (il W))
  rw[pW] at hp;cases hp
 ·X ⟨a,e,f,r⟩
private lemma zt {m:ℕ} {C:J} (d:zp m C)
  {c a'' a''':ℕ} (a:c< (p3 C (2*m+2) true).size)
  (e:p0 (p3 C (2*m+2) true) (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+c)=true)
  (f:pC (2*m+2) c a'' ((p3 C (2*m+2) true).gates[c]'a))
  (g:(p5 (p3 C (2*m+2) true) (2*m+1) false).fc.getD a'' (.const false)=.wire a''') :
  ∀y:Fin (2*m+1)->Bool,
   p0 (p3 (p3 C (2*m+2) true) (2*m+1) false) y a'''=true ->
   pq (2*m+1) y=true:=by
 intro y hy;set k:=p3 C (2*m+2) true;set i:=p3 k (2*m+1) false;obtain ⟨l,n,b⟩:=d.fQ c a e;apply b y
 have p:p0 i y a'''=p0 k (Fin.snoc y false) a'':=by
  have h:=pH k (2*m+1) false d.f7.1 y a'';rw[g] at h;X h
 have s:p0 i y l=p0 k (Fin.snoc y false) (2*m+2+c):=by
  have h:=pH k (2*m+1) false d.f7.1 y (2*m+2+c);rw[n] at h;X h
 have j:=d.fk c a e;rcases pc d.f7 d.fq c a with ⟨q,_,_,_⟩|⟨_,b1,b2,r,u,v,_⟩
 ·rw[j] at q;cases q
 ·have t:=f.1;simp only[pa,j,r,List.mem_cons,List.not_mem_nil,or_false] at t
  change p0 i y l=true;rw[s,p6 _ a j r u v,Bool.or_eq_true];rcases t with rfl|rfl
  ·X il (p.symm.trans hy)
  ·X ir (p.symm.trans hy)
private lemma kq {m:ℕ} {C:J} (d:zp m C):d.w=2*m:=by
 set hO:=p3 C (2*m+2) true;set l:=p3 hO (2*m+1) false;have hA:d.w< 2*m+3+C.size:=by have:=d.fs;have:=d.f9;O
 have hB:d.w≠2*m+3+d.f3:=by have:=d.fs;O
 obtain ⟨hZ,p,_,q,hG,hC,g,v⟩ :=
  qX d d.w hA d.fM hB d.fE
 have i:zc (e2 (2*m) (2*m+1):Fin (2*m+3)->Bool) =
   (e1 (2*m):Fin (2*m+1)->Bool):=by
  funext j;simp only[zc,e2,e1];apply Bool.eq_iff_iff.2;have:=j.isLt;simp;O
 have x:p0 l (e1 (2*m):Fin (2*m+1)->Bool) p=true:=by
  cases hD:p0 l (e1 (2*m):Fin (2*m+1)->Bool) p with
  | true=>rfl
  | false=>
   exfalso
   have hL:p0 C (e2 (2*m) (2*m+1):Fin (2*m+3)->Bool) (2*m+3+d.f3)=false:=by
    have y:p0 C (e2 (2*m) (2*m+1):Fin (2*m+3)->Bool) (2*m+2)=false:=by
     rw[p7 C _ (2*m+2) W];simp[e2]
    have hH:p0 C (e2 (2*m) (2*m+1):Fin (2*m+3)->Bool) d.w=false:=by
     rw[v,i];X hD
    rcases d.ft with hins|hins
    ·rw[p6 _ d.f9 d.fl hins W d.fs,y,hH];R
    ·rw[p6 _ d.f9 d.fl hins d.fs W,hH,y];R
   have s:∀t (ht:t< C.size),zG C (2*m+2) (2*m+3+t)->t≠d.f3->t≠d.f4 ->
     ∀a,pC (2*m+3) t a (C.gates[t]'ht)->¬zG C (2*m+2) a ->
      p0 C (e2 (2*m) (2*m+1):Fin (2*m+3)->Bool) a=false:=by
    intro t ht hV hP hQ a b hE
    obtain ⟨H0,hM,_,_,hI,hF,_,hW⟩ :=
     qX d a (by have:=b.2;O) (fun h=>hP ((d.fi t ht).1 (h▸b)))
      (fun h=>hQ ((d.fj t ht).1 (h▸b))) hE
    rw[hW,i];have k:=pE d.f0.1 d.fe ht hP hQ;obtain ⟨hX,z,_,e,_,_,_⟩:=p4 d.f0.1 ht k;have r:=pp d.f0 d.fJ d.fn ht k z e b hI
    cases hv:p0 l (e1 (2*m):Fin (2*m+1)->Bool) hM with
    | false=>rfl
    | true=>
     have hp:=zt d z ((pM e).1 hV) r hF _ hv;rw[pW] at hp;cases hp
   have c:=j8 d.f0 d.fJ W d.fn d.f9 d.fa d.fP
    d.fe d.fh d.fm d.fy d.fu d.fk hL s C.output (pB d.fn) d.fo
   change cF (2*m+3) C (pe (2*m))=cF (2*m+3) C (e1 (2*m+1)) at c;rw[d.fd,pW,q0 W] at c;cases c
 have f:∀a< 2*m,p0 l (e1 a:Fin (2*m+1)->Bool) p=false:=by
  intro a ha
  cases hv:p0 l (e1 a:Fin (2*m+1)->Bool) p with
  | false=>rfl
  | true=>
   exfalso
   have hJ:zc (e2 a (2*m+1):Fin (2*m+3)->Bool) =
     (e1 a:Fin (2*m+1)->Bool):=by
    funext j;simp only[zc,e2,e1];apply Bool.eq_iff_iff.2;have:=j.isLt;simp;O
   have hL:p0 C (e2 a (2*m+1):Fin (2*m+3)->Bool) (2*m+3+d.f3)=true:=by
    have hH:p0 C (e2 a (2*m+1):Fin (2*m+3)->Bool) d.w=true:=by rw[v,hJ];X hv
    rcases d.ft with hins|hins
    ·rw[p6 _ d.f9 d.fl hins W d.fs,hH,Bool.or_true]
    ·rw[p6 _ d.f9 d.fl hins d.fs W,hH,Bool.true_or]
   have hh:=qL d.f0 d.fJ W d.fn d.f9 d.fa d.fP
    d.fe d.fh d.fm d.fy d.fu d.fz d.fk (e2 a (2*m+1))
    (by simp only[e2,decide_eq_true_eq];O) (il hL)
    C.output (pB d.fn) d.fo
   rw[←pb,d.fd,jC W W] at hh;cases hh
 rcases qH d.f6 p q with ⟨j,hj,hK,hD⟩|⟨_,_,_,c',_,hN,hD⟩|⟨_,_,_,_,_,_,hD⟩
 ·have hR:j=2*m:=of_decide_eq_true (by have h:=cf hD (e1 (2*m));rw[x] at h;X h.symm)
  have hS:d.w< 2*m+3:=by by_contra hge;have:=g W;O
  have u:d.w< 2*m+1:=by
   by_contra hge;have hY:d.w=2*m+1:=by have:=d.fM;O
   X d.fE (hY▸zE (C:=C) (n:=2*m+2) W)
  have hT:=pd C (2*m+2) true d.w W;have hU:=pd hO (2*m+1) false d.w u;rw[hG] at hT;cases hT;rw[hC] at hU;cases hU;O
 ·have h1:=cf hD (e1 (c'-1))
  rw[f (c'-1) W,(pt W hN W).2 (il W)] at h1;cases h1
 ·have h1:=cf hD (e1 (2*m));rw[x,q2] at h1;cases h1
private lemma zP {m:ℕ} {C:J} (d:zp m C) (hw:d.w=2*m)
  {tq tz:ℕ} (hL:tq< C.size) (hR:tz< C.size)
  (y:(p5 C (2*m+2) true).fb[tq]'(by rw[(pk C (2*m+2) true d.f0.1).kept_len];X hL)=true)
  (hO:(p5 C (2*m+2) true).fc.getD (2*m+3+tq) (.const false)=.wire (2*m+2+d.fv))
  (hP:(p5 C (2*m+2) true).fc.getD (2*m+3+tz) (.const false)=.wire d.z'')
  (n:tz≠d.f3) (p:2*m+3+tz≠d.u)
  {hB:ℕ} (q:hB< (p3 C (2*m+2) true).size)
  (b:pC (2*m+2) hB (2*m+2+d.fv) ((p3 C (2*m+2) true).gates[hB]'q)) :
  ∀v (hv:v< C.size),pC (2*m+3) v (2*m+3+tz) (C.gates[v]'hv)->v=tq:=by
 set hQ:=p3 C (2*m+2) true;set hH:=p3 hQ (2*m+1) false
 have hC:∃y1 y2:Fin (2*m+1)->Bool,cF (2*m+1) hH y1≠cF (2*m+1) hH y2:=by
  rw[d.f8];X ps (by have:=d.hm;O)
 have c:=q4 d.f7.1 d.ff q (by have:=b.2;O)
 obtain ⟨hM,t,_,h,_,_,_⟩:=p4 d.f7.1 q c;have k:=pp d.f7 d.fC d.fq q c t h b d.fx;intro v hv g;by_contra hv_ne_q
 have z:v≠d.f3:=fun hD=>by
  have hE:=g.1;have hI:C.gates[v]'hv=C.gates[d.f3]'d.f9:=by subst hD;R
  rw[hI] at hE
  rcases d.ft with hins|hins <;>
   simp only[pa,d.fl,hins,hw,List.mem_cons,List.not_mem_nil,or_false] at hE<;>O
 have hh:v≠d.f4:=fun hD=>by
  have hE:=g.1;have hJ:C.gates[v]'hv=C.gates[d.f4]'d.fa:=by subst hD;R
  rw[hJ] at hE
  rcases d.fy with hins|hins <;>
   simp only[pa,d.fm,hins,List.mem_cons,List.not_mem_nil,or_false] at hE
  ·rcases hE with h1|h2<;>[X n W;X p h2]
  ·rcases hE with h1|h2<;>[X p h1;X n W]
 have e:=pE d.f0.1 d.fe hv z hh;obtain ⟨hK,i,_,r,_,_,_⟩:=p4 d.f0.1 hv e;have f:=pp d.f0 d.fJ d.fn hv e i r g hP
 have s:hK≠d.fv:=fun hF=>
  hv_ne_q (pO d.f0.1 hv hL e y (hF▸r) hO)
 have a:=q4 d.f7.1 d.ff i s;obtain ⟨hN,x,_,j,_,_,_⟩:=p4 d.f7.1 i a;have l:=pp d.f7 d.fC d.fq i a x j f d.fL;have hA:=zZ d.hm d.f5 d.f8 d.f6 d.fA d.fG x t l k;have hG:=pO d.f7.1 i q a c (hA▸j) h;subst hG
 X zN d.f7 d.fC d.fq d.f5 hC
  i a (by have:=d.fw;O) f b d.fL d.fx
private lemma zT {m:ℕ} {C:J} (d:zp m C) :
  2*m+2<=d.z'':=by
 by_contra hlt
 have h1:=pd (p3 C (2*m+2) true) (2*m+1) false d.z'' (by have:=d.fR;O)
 rw[d.fL] at h1;injection h1 with h1;have:=d.fR;O
private lemma jz {m:ℕ} {C:J} (d:zp m C) :
  2*m+3+d.f4<=C.output:=by
 by_contra hlt
 have a:C.output≠2*m+2:=fun h=>pI (p9 C (2*m+2) true d.f0.1) (h▸d.fo);have b:C.output≠2*m+3+d.f3:=fun h=>pI d.fh (h▸d.fo)
 have c:=qI d.f0.1 d.fi d.fj
  (e1 (2*m+1):Fin (2*m+2)->Bool) C.output W a b
 rw[jy (2*m+1),jL (2*m+1)] at c;have h1:=c.trans (jK d.f0.1 W d.fo);rw[←pb,d.fd,pW] at h1;cases h1
private lemma ks {m:ℕ} {C:J} (d:zp m C) (hw:d.w=2*m):d.u=2*m+1:=by
 set Hp:=p5 C (2*m+2) true;set HD:=p3 C (2*m+2) true;set Hg:=p5 HD (2*m+1) false;set Hk:=p3 HD (2*m+1) false;by_contra hu_ne
 have _f:2*m+3<=d.u:=by
  by_contra hlt
  have _n:d.u≠2*m+2:=fun h=>pI (p9 C (2*m+2) true d.f0.1) (h▸d.fH);have _o:¬d.u< 2*m+1:=fun h=>ja h d.fH;O
 set tu:=d.u-(2*m+3);have _t:tu< d.f4:=by have:=d.fu;O
 have hX:tu< C.size:=by have:=d.fa;O
 have Hh:d.u=2*m+3+tu :=W;have Hq:tu≠d.f3:=fun h=>pI d.fh (by rw[←h,←Hh];X d.fH)
 have hE:=pE d.f0.1 d.fe hX Hq W;obtain ⟨Hr,H0,_,hh,_,_,_⟩:=p4 d.f0.1 hX hE
 have H8:p0 HD (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+Hr)=true :=
  (pM (Hh▸hh)).1 d.fH
 obtain ⟨j,hL,c,P_u,⟨c0,HG⟩,hY,H9⟩:=zX d H0 H8;have _g:=(hY c0 HG).1;have _h:=(hY c0 HG).2;set xe:Fin (2*m+3)->Bool:=pe (c0-1);set ye:Fin (2*m+1)->Bool:=pe (c0-1)
 have hG:p0 C xe (2*m+3+d.f4)=false:=by
  have HT:p0 C xe (2*m+3+d.f3)=false:=by
   have h1:p0 C xe (2*m+2)=false:=by
    rw[p7 C xe (2*m+2) W];simp only[xe,pe,e2,decide_eq_false_iff_not];O
   have h2:p0 C xe (2*m)=false:=by
    rw[p7 C xe (2*m) W];simp only[xe,pe,e2,decide_eq_false_iff_not];O
   rcases d.ft with g|g
   ·rw[p6 xe d.f9 d.fl (hw▸g) W W,h1,h2];R
   ·rw[p6 xe d.f9 d.fl (hw▸g) W W,h2,h1];R
  have _u:=d.fP;rcases d.fy with g|g
  ·rw[pm xe d.fa d.fm g W d.fu,HT,Bool.false_and]
  ·rw[pm xe d.fa d.fm g d.fu W,HT,Bool.and_false]
 have HU:cF (2*m+3) C (e1 (2*m+1))=false:=by rw[d.fd];X pW _ _
 have HM:∀a,pC (2*m+3) d.f3 a (C.gates[d.f3]'d.f9)->¬zG C (2*m+2) a:=by
  intro a hr;have _4:=hr.1;rcases d.ft with g|g
  ·simp only[pa,d.fl,g,List.mem_cons,List.not_mem_nil,or_false] at _4
   rcases _4 with rfl|rfl
   ·X pI (p9 C (2*m+2) true d.f0.1)
   ·X d.fE
  ·simp only[pa,d.fl,g,List.mem_cons,List.not_mem_nil,or_false] at _4
   rcases _4 with rfl|rfl
   ·X d.fE
   ·X pI (p9 C (2*m+2) true d.f0.1)
 obtain ⟨hM,_,_⟩ :=
  qW d.f0 d.fJ W d.fn HU d.f9 d.fa d.fP
   d.fi d.fj d.fe d.fh HM d.fm d.fy d.fu d.fp
 have Hl:2*m+3+d.f4≠C.output:=fun HH=>by
  have h1:p0 C xe C.output=true:=by rw[←pb,d.fd];X q0 W
  rw[←HH,hG] at h1;cases h1
 have HN:d.fv<=Hr:=by
  by_contra hlt
  have h:=jV d.fD d.f7 d.fq d.fB d.fk (2*m+2+Hr) W W;rw[H8] at h;cases h
 have p:∀a< 2*m+3+C.size,a≠2*m+2->a≠2*m+3+d.f3 ->
   ¬zG C (2*m+2) a->∀_7,Hp.fc.getD a (.const false)=.wire _7 ->
    Hg.fc.getD _7 (.const false)=.wire (2*m+1+j) ->
   ∀v (hv:v< C.size),v≠tu->¬pC (2*m+3) v a (C.gates[v]'hv):=by
  intro a HI _p _i q _7 H1 Ha v hv _8 e
  have _j:2*m+3<=a:=by
   by_contra hlt
   have Hi:a< 2*m+1:=by
    by_contra hge;have HH:a=2*m+1 :=W
    X q (HH▸zE (C:=C) (n:=2*m+2) W)
   have h1:=pd C (2*m+2) true a W;have h2:=pd HD (2*m+1) false a Hi;rw[H1] at h1;cases h1;rw[Ha] at h2;cases h2;O
  set ta:=a-(2*m+3);have _9:ta< C.size :=W;have hA:a=2*m+3+ta :=W;have H2:ta≠d.f3 :=W;have Hs:ta≠d.f4:=fun h=>q (by rw[hA,h];X d.fT)
  have Hm:=pE d.f0.1 d.fe _9 H2 Hs;obtain ⟨HO,Ht,_,H3,_,_,_⟩:=p4 d.f0.1 _9 Hm;rw[←hA,H1] at H3;cases H3
  have Hb:HO≠d.fv:=fun HH=>
   q ((pM (by rw[hA,←HH];X hA▸H1)).2 (jh d.fD d.fI d.fK d.fw))
  have hN:=q4 d.f7.1 d.ff Ht Hb;by_cases hO:Hr=d.fv
  ·have Hu:j=d.fg:=by
    rw[hO,d.fx] at c;injection c with h;O
   have HV:=zT d;set Hn:=d.z''-(2*m+2);have H4:Hn< HD.size:=by have hq:d.fv< HD.size:=d.fD;have:=d.fw;O
   have y:=q4 d.f7.1 d.ff H4 (by have:=d.fw;O)
   have _a:HO=Hn:=pO d.f7.1 Ht H4 hN y
    (Hu▸Ha) (by rw[show 2*m+2+Hn=d.z'' by O];X d.fL)
   rcases pY d.f0 d.f4 d.fa with hout|⟨r,hr,_v,Hv⟩
   ·X Hl hout.symm
   ·have hV:=pE d.f0.1 d.fe hr (by have:=d.fP;O) W
    obtain ⟨_q,HL,_,Hw,_,_,_⟩:=p4 d.f0.1 hr hV
    have _r:Hp.fc.getD (2*m+3+d.f4) (.const false)=.wire (2*m+2+d.fv):=by
     rw[d.fz,Hh,hh,hO]
    have H5:=pp d.f0 d.fJ d.fn hr hV HL Hw Hv _r
    have HW:=zP d hw hX _9 hE (hO▸hh)
     (by rw[←hA,H1,show 2*m+2+HO=d.z'' by O])
     H2 (fun h=>q (by rw[hA,h];X d.fH)) HL H5 v hv (hA▸e)
    X _8 HW
  ·have z:=q4 d.f7.1 d.ff H0 hO
   have Ho:=pO d.f7.1 Ht H0 hN z Ha c;X q ((pM (by rw[hA];X hA▸H1)).2 (by rw[Ho];X H8))
 have _b:∀i< 2*m+3+C.size,i≠2*m+2->i≠2*m+3+d.f3 ->
   ∀(_c HJ:ℕ),Hp.fc.getD i (.const false)=.wire _c->Hg.fc.getD _c (.const false)=.wire HJ ->
    (i=2*m+3+d.f4\/(zG C (2*m+2) i/\2*m+3+d.f4< i) \/
     (¬zG C (2*m+2) i/\HJ≠2*m+1+j)) ->
    p0 C xe i=true->pl Hk ye j false HJ=true:=by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih=>
   intro _s _p _i _c HJ hH hP HX hJ;rcases HX with rfl|⟨_k,_w⟩|⟨hF,_d⟩
   ·rw[hG] at hJ;cases hJ
   ·set t:=i-(2*m+3)
    have ht:t< C.size :=W;have Hx:i=2*m+3+t :=W;have _5:d.f4< t :=W;have k:=pE d.f0.1 d.fe ht (by have:=d.fP;O) W
    obtain ⟨HP,hI,_,s,x,hK,_⟩:=p4 d.f0.1 ht k;rw[Hx] at hH _k hJ;rw[hH] at s;cases s;have hQ:=d.fk HP hI ((pM hH).1 _k);have Hj:(C.gates[t]'ht).op=.or:=x.symm.trans hQ;have H6:=zm d.f0.1 hX ht W hE k hh hH;have f:=q4 d.f7.1 d.ff hI W;obtain ⟨Hy,hZ,_,l,hB,hC,_⟩:=p4 d.f7.1 hI f;rw[hP] at l;cases l
    have b:Hy≠j:=by
     by_cases hO:Hr=d.fv
     ·have Hu:j=d.fg:=by
       rw[hO,d.fx] at c;injection c with h;O
      have HV:=zT d;set Hn:=d.z''-(2*m+2);have H4:Hn< HD.size:=by have hq:d.fv< HD.size:=d.fD;have:=d.fw;O
      have y:=q4 d.f7.1 d.ff H4 (by have:=d.fw;O)
      have:=zm d.f7.1 H4 hI (by have:=d.fw;O)
       y f (by rw[show 2*m+2+Hn=d.z'' by O];X d.fL) hP
      O
     ·have z:=q4 d.f7.1 d.ff H0 hO
      have:=zm d.f7.1 H0 hI H6 z f c hP
      O
    rcases pc d.f0 d.fn t ht with ⟨HK,_,_,_⟩|⟨_,a1,a2,g,HE,HF,_⟩
    ·rw[Hj] at HK;cases HK
    ·obtain ⟨w1,w2,HY,HZ,_0,_1,hR⟩:=hK .or a1 a2 (ir rfl) Hj g HE HF
     obtain ⟨u1,u2,_2,_3,Hz,HA,hD⟩:=hC .or w1 w2 (ir rfl) hQ hR HY HZ;rw[p6 xe ht Hj g HE HF,Bool.or_eq_true] at hJ;rw[pJ ye hL false hZ b (hB.trans hQ) hD _2 _3,Bool.or_eq_true]
     have hS:∀a wa ua,(a=a1\/a=a2)->a< 2*m+3+t ->
       Hp.fc.getD a (.const false)=.wire wa->Hg.fc.getD wa (.const false)=.wire ua ->
       p0 C xe a=true->pl Hk ye j false ua=true:=by
      intro a wa ua HQ HI Hc Hd H7;have e:pC (2*m+3) t a (C.gates[t]'ht):=⟨by simp[pa,Hj,g,HQ],HI⟩
      have hT:a≠2*m+2:=fun h=>by have:=(d.fi t ht).1 (h▸e);have:=d.fP;O
      have hU:a≠2*m+3+d.f3:=fun h=>by have:=(d.fj t ht).1 (h▸e);O
      by_cases _6:zG C (2*m+2) a
      ·have _l:2*m+3+d.f4<=a:=by
        by_contra hlt;X hM t ht _5 a e W _6
       by_cases _e:a=2*m+3+d.f4
       ·X ih a W W hT hU wa ua Hc Hd (il _e) H7
       ·X ih a W W hT hU wa ua Hc Hd (ir (il ⟨_6,by O⟩)) H7
      ·have HB:ua≠2*m+1+j:=fun h=>
        p a W hT hU _6 wa Hc (h▸Hd) t ht W e
       X ih a W W hT hU wa ua Hc Hd (ir (ir ⟨_6,HB⟩)) H7
     rcases hJ with h1|h2
     ·X il (hS a1 w1 u1 (il rfl) HE _0 Hz h1)
     ·X ir (hS a2 w2 u2 (ir rfl) HF _1 HA h2)
   ·by_cases _x:i< 2*m+3
    ·have Hi:i< 2*m+1:=by
      by_contra hge;have HH:i=2*m+1 :=W
      X hF (HH▸zE (C:=C) (n:=2*m+2) W)
     have h1:=pd C (2*m+2) true i W;have h2:=pd HD (2*m+1) false i Hi;rw[hH] at h1;cases h1;rw[hP] at h2;cases h2;rw[pA Hk ye j hL false i W,p7 Hk ye i Hi];rwa[p7 C xe i W] at hJ
    ·set t:=i-(2*m+3)
     have ht:t< C.size :=W;have Hx:i=2*m+3+t :=W;rw[Hx] at _i hF hH hJ;have _m:t≠d.f3 :=W;have _5:t≠d.f4:=fun h=>hF (h▸d.fT);have HR:t≠tu:=fun h=>hF (by rw[h,←Hh];X d.fH)
     have k:=pE d.f0.1 d.fe ht _m _5;obtain ⟨HP,hI,_,s,x,hK,_⟩:=p4 d.f0.1 ht k;rw[hH] at s;cases s
     have He:HP≠d.fv:=fun HH=>
      hF ((pM (HH▸hH)).2 (jh d.fD d.fI d.fK d.fw))
     have f:=q4 d.f7.1 d.ff hI He;obtain ⟨Hy,hZ,_,l,hB,hC,_⟩:=p4 d.f7.1 hI f;rw[hP] at l;cases l;have b:Hy≠j :=W;rcases pc d.f0 d.fn t ht with ⟨HK,_,_,_⟩|⟨HC,a1,a2,g,HE,HF,_⟩
     ·X absurd HK (d.fJ _ (List.getElem_mem ht))
     ·have hS:∀a wa ua,(a=a1\/a=a2)->a< 2*m+3+t ->
        Hp.fc.getD a (.const false)=.wire wa->Hg.fc.getD wa (.const false)=.wire ua ->
        p0 C xe a=true->pl Hk ye j false ua=true:=by
       intro a wa ua HQ HI Hc Hd H7
       have e:pC (2*m+3) t a (C.gates[t]'ht):=by
        rcases HC with h|h<;>X ⟨by simp[pa,h,g,HQ],HI⟩
       have hT:a≠2*m+2:=fun h=>_m ((d.fi t ht).1 (h▸e));have hU:a≠2*m+3+d.f3:=fun h=>_5 ((d.fj t ht).1 (h▸e));have q:=j3 d.f0 d.fJ d.fn d.fp ht k hF e
       have HB:ua≠2*m+1+j:=fun h=>
        p a W hT hU q wa Hc (h▸Hd) t ht HR e
       X ih a W W hT hU wa ua Hc Hd (ir (ir ⟨q,HB⟩)) H7
      rcases HC with hop_eq|hop_eq
      ·obtain ⟨w1,w2,HY,HZ,_0,_1,hR⟩:=hK .and a1 a2 (il rfl) hop_eq g HE HF
       obtain ⟨u1,u2,_2,_3,Hz,HA,hD⟩:=hC .and w1 w2 (il rfl) (x.trans hop_eq) hR HY HZ;rw[pm xe ht hop_eq g HE HF,Bool.and_eq_true] at hJ;rw[pF ye hL false hZ b (hB.trans (x.trans hop_eq)) hD _2 _3,Bool.and_eq_true];X ⟨hS a1 w1 u1 (il rfl) HE _0 Hz hJ.1,hS a2 w2 u2 (ir rfl) HF _1 HA hJ.2⟩
      ·obtain ⟨w1,w2,HY,HZ,_0,_1,hR⟩:=hK .or a1 a2 (ir rfl) hop_eq g HE HF
       obtain ⟨u1,u2,_2,_3,Hz,HA,hD⟩:=hC .or w1 w2 (ir rfl) (x.trans hop_eq) hR HY HZ;rw[p6 xe ht hop_eq g HE HF,Bool.or_eq_true] at hJ;rw[pJ ye hL false hZ b (hB.trans (x.trans hop_eq)) hD _2 _3,Bool.or_eq_true];rcases hJ with h1|h2
       ·X il (hS a1 w1 u1 (il rfl) HE _0 Hz h1)
       ·X ir (hS a2 w2 u2 (ir rfl) HF _1 HA h2)
 have HS:=jz d
 have hW:=_b C.output (pB d.fn)
  (fun h=>pI (p9 C (2*m+2) true d.f0.1) (h▸d.fo))
  (fun h=>pI d.fh (h▸d.fo))
  HD.output Hk.output (q8 d.f0.1 d.fN) (q8 d.f7.1 d.fO)
  (ir (il ⟨d.fo,by O⟩))
  (by rw[←pb,d.fd];X q0 W)
 have Hf:=d.f6.2.2 j hL P_u ⟨c0,HG⟩ hY H9 c0 HG;rw[Hf] at hW;cases hW
private lemma k7 {m:ℕ} {C:J} (d:zp m C) (hu:d.u=2*m+1)
  (y:∀t (ht:t< C.size),d.f4< t->∀a,pC (2*m+3) t a (C.gates[t]'ht) ->
   a< 2*m+3+d.f4->¬zG C (2*m+2) a) :
  ∀v (hv:v< C.size),d.f4<=v->zG C (2*m+2) (2*m+3+v) ->
   ∀w (Hd:w< v),d.f4<=w->zG C (2*m+2) (2*m+3+w) ->
   ∀r (hr:r< C.size),pC (2*m+3) r (2*m+3+w) (C.gates[r]'hr)->r<=v:=by
 set hT:=p5 C (2*m+2) true;set hU:=p3 C (2*m+2) true;set He:=p5 hU (2*m+1) false;set Ho:=p3 hU (2*m+1) false
 have hG:∀v (hv:v< C.size),d.f4<=v->zG C (2*m+2) (2*m+3+v) ->
   ∀r1 r2 (hN:r1< C.size) (hO:r2< C.size),
    pC (2*m+3) r1 (2*m+3+v) (C.gates[r1]'hN) ->
    pC (2*m+3) r2 (2*m+3+v) (C.gates[r2]'hO)->r1=r2:=by
  intro v hv Hp H4 r1 r2 hN hO hK hL;have Hq:=d.fP;have b:=pE d.f0.1 d.fe hN (by have:=hK.2;O) (by have:=hK.2;O)
  have c:=pE d.f0.1 d.fe hO (by have:=hL.2;O) (by have:=hL.2;O)
  obtain ⟨hV,k,_,i,_,_,_⟩:=p4 d.f0.1 hN b;obtain ⟨hW,l,_,j,_,_,_⟩:=p4 d.f0.1 hO c;by_cases hJ:v=d.f4
  ·have Hf:hT.fc.getD (2*m+3+v) (.const false)=.wire (2*m+1):=by
    rw[hJ,d.fz,hu];X pd C (2*m+2) true (2*m+1) W
   have h1:=(d.fB hV k).1 (pp d.f0 d.fJ d.fn hN b k i hK Hf);have h2:=(d.fB hW l).1 (pp d.f0 d.fJ d.fn hO c l j hL Hf);X pO d.f0.1 hN hO b c (h1▸i) (h2▸j)
  ·have n:=pE d.f0.1 d.fe hv W hJ
   obtain ⟨hH,hB,_,e,_,_,_⟩:=p4 d.f0.1 hv n
   have q:p0 hU (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+hH)=true :=
    (pM e).1 H4
   obtain ⟨Hg,hQ,hA,hI⟩:=zX d hB q;have s:=pp d.f0 d.fJ d.fn hN b k i hK e;have x:=pp d.f0 d.fJ d.fn hO c l j hL e
   have hX:d.fv<=hH:=by
    by_contra hlt
    have h:=jV d.fD d.f7 d.fq d.fB d.fk (2*m+2+hH) W W;rw[q] at h;cases h
   have f:=q4 d.f7.1 d.ff k (by have:=s.2;O)
   have g:=q4 d.f7.1 d.ff l (by have:=x.2;O)
   obtain ⟨H5,hC,_,z,_,_,_⟩:=p4 d.f7.1 k f;obtain ⟨H6,hD,_,hh,_,_,_⟩:=p4 d.f7.1 l g;have hY:=pp d.f7 d.fC d.fq k f hC z s hA;have hZ:=pp d.f7 d.fC d.fq l g hD hh x hA;have hR:=zZ d.hm d.f5 d.f8 d.f6 hQ hI hC hD hY hZ;have H0:=pO d.f7.1 k l f g (hR▸z) hh;X pO d.f0.1 hN hO b c (H0▸i) j
 intro v
 induction v using Nat.strong_induction_on with
 | ind v ih=>
  intro hv Hp H4 w Hr H7 H8 r hr Hh;have Hq:=d.fP;have Hs:d.f4< v :=W;have n:=pE d.f0.1 d.fe hv W W;obtain ⟨hH,hB,_,e,hE,hM,_⟩:=p4 d.f0.1 hv n
  have q:p0 hU (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+hH)=true :=
   (pM e).1 H4
  have hF:(C.gates[v]'hv).op=.or:=hE.symm.trans (d.fk hH hB q)
  have H1:∃p,d.f4<=p/\p< v/\zG C (2*m+2) (2*m+3+p)/\pC (2*m+3) v (2*m+3+p) (C.gates[v]'hv):=by
   rcases pc d.f0 d.fn v hv with ⟨H2,_,_,_⟩|⟨_,a1,a2,H3,Hi,Hj,_⟩
   ·rw[hF] at H2;cases H2
   ·obtain ⟨w1,w2,Ht,Hu,Hv,Hw,hS⟩:=hM .or a1 a2 (ir rfl) hF H3 Hi Hj
    rw[p6 _ hB (hE.trans hF) hS Ht Hu,Bool.or_eq_true] at q
    have hP:∀a wa,(a=a1\/a=a2)->a< 2*m+3+v->hT.fc.getD a (.const false)=.wire wa ->
      p0 hU (e1 (2*m+1):Fin (2*m+2)->Bool) wa=true ->
      ∃p,d.f4<=p/\p< v/\zG C (2*m+2) (2*m+3+p)/\pC (2*m+3) v (2*m+3+p) (C.gates[v]'hv):=by
     intro a wa H9 Ha Hb Hc;have Hx:=(pM Hb).2 Hc;have Hy:pC (2*m+3) v a (C.gates[v]'hv):=⟨by simp[pa,hF,H3,H9],Ha⟩
     have Hz:2*m+3+d.f4<=a:=by by_contra hlt;X y v hv Hs a Hy W Hx
     Y ⟨a-(2*m+3),by O,by O,?_,?_⟩<;>rwa[show 2*m+3+(a-(2*m+3))=a by O]
    rcases q with h1|h2
    ·X hP a1 w1 (il rfl) Hi Hv h1
    ·X hP a2 w2 (ir rfl) Hj Hw h2
  obtain ⟨p,Hk,Hl,Hm,Hn⟩:=H1;rcases Nat.lt_trichotomy w p with hwp|rfl|hpw
  ·X le_trans (ih p Hl W Hk Hm w hwp H7 H8 r hr Hh) (le_of_lt Hl)
  ·have:=hG w W H7 H8 r v hr hv Hh Hn;O
  ·have:=ih w Hr W H7 H8 p hpw Hk Hm v hv Hn;O
private lemma jG {m:ℕ} (hm:1<=m) {C:J}
  (h0h:IsMinimalCircuit (2*(m+1)+1) C)
  (hfun:cF (2*(m+1)+1) C=pq (2*(m+1)+1))
  (hIH:∀D:J,IsMinimalCircuit (2*m+1) D->cF (2*m+1) D=pq (2*m+1)->zb m D) :
  zb (m+1) C:=by
 have _P:IsMinimalCircuit (2*m+3) C:=h0h;have _Q:cF (2*m+3) C=pq (2*m+3):=hfun;obtain ⟨d⟩:=kC hm _P _Q hIH;have hw:d.w=2*m:=kq d;have hu:d.u=2*m+1:=ks d hw;set _q:=p5 C (2*m+2) true;set Hz:=p3 C (2*m+2) true;set HA:=p5 Hz (2*m+1) false;set hA:=p3 Hz (2*m+1) false;have _R:cF (2*m+3) C (e1 (2*m+1))=false:=by rw[d.fd];X pW _ _
 have _r:∀a,pC (2*m+3) d.f3 a (C.gates[d.f3]'d.f9)->¬zG C (2*m+2) a:=by
  intro a hr;have hrm:=hr.1;rcases d.ft with e|e
  ·simp only[pa,d.fl,e,List.mem_cons,List.not_mem_nil,or_false] at hrm
   rcases hrm with rfl|rfl
   ·X pI (p9 C (2*m+2) true d.f0.1)
   ·X d.fE
  ·simp only[pa,d.fl,e,List.mem_cons,List.not_mem_nil,or_false] at hrm
   rcases hrm with rfl|rfl
   ·X d.fE
   ·X pI (p9 C (2*m+2) true d.f0.1)
 obtain ⟨q,_c,_⟩ :=
  qW d.f0 d.fJ W d.fn _R d.f9 d.fa d.fP
   d.fi d.fj d.fe d.fh _r d.fm d.fy d.fu d.fp
 have z:∀t (ht:t< C.size),t< d.f4->¬zG C (2*m+2) (2*m+3+t) :=
  fun t ht HB HP=>by have:=_c t ht HB HP;O
 have hJ:p8 C d.f3=pD (m+1) (2*m+1):=by
  funext x;change p0 C x (2*m+3+d.f3)=_
  have h1:=p7 C x (2*m+2) W;have h2:=p7 C x (2*m) W;rcases d.ft with e|e
  ·have _s:=p6 (n:=2*m+3) x d.f9 d.fl (hw▸e) W W
   rw[_s,h1,h2];apply Bool.eq_iff_iff.2;rw[pG,Bool.or_eq_true]
   constructor
   ·rintro (h|h)
    ·X ⟨⟨2*m+2,by O⟩,ir rfl,h⟩
    ·X ⟨⟨2*m,by O⟩,il rfl,h⟩
   ·rintro ⟨k,hk,hxk⟩
    have:k=⟨2*m,by O⟩\/k=⟨2*m+2,by O⟩:=by
     rcases hk with h|h<;>[left;right]<;>ext<;>dsimp<;>O
    rcases this with rfl|rfl<;>simp[hxk]
  ·have _s:=p6 (n:=2*m+3) x d.f9 d.fl (hw▸e) W W
   rw[_s,h1,h2];apply Bool.eq_iff_iff.2;rw[pG,Bool.or_eq_true]
   constructor
   ·rintro (h|h)
    ·X ⟨⟨2*m,by O⟩,il rfl,h⟩
    ·X ⟨⟨2*m+2,by O⟩,ir rfl,h⟩
   ·rintro ⟨k,hk,hxk⟩
    have:k=⟨2*m,by O⟩\/k=⟨2*m+2,by O⟩:=by
     rcases hk with h|h<;>[left;right]<;>ext<;>dsimp<;>O
    rcases this with rfl|rfl<;>simp[hxk]
 have H0:p8 C d.f4=qa (m+1) {2*m+1}:=by
  funext x;change p0 C x (2*m+3+d.f4)=_
  have h1:p0 C x (2*m+3+d.f3)=pD (m+1) (2*m+1) x:=cf hJ x;have h2:=p7 C x (2*m+1) W;have hgh:=d.fP
  rcases d.fy with e|e<;>(
   have _s:=pm (n:=2*m+3) x d.fa d.fm (hu▸e) W W;rw[_s,h1,h2];apply Bool.eq_iff_iff.2;rw[qp,Bool.and_eq_true]
   constructor
   ·intro ⟨ha,hb⟩;X ⟨2*m+1,Finset.mem_singleton_self _,by O,by tauto,by tauto⟩
   ·rintro ⟨c,hc,_,_J,_K⟩;rw[Finset.mem_singleton] at hc;subst hc;X ⟨by tauto,by tauto⟩)
 have hV:∀t (ht:t< C.size),
   (t=d.f3/\p8 C t=pD (m+1) (2*m+1)) \/
   (¬zG C (2*m+2) (2*m+3+t)/\t≠d.f3 /\
    ((∃c,c%2=1/\c< 2*m/\p8 C t=pD (m+1) c) \/
     (∃P:Finset ℕ,P.Nonempty/\(∀c∈P,c%2=1/\c< 2*m)/\p8 C t=qa (m+1) P))) \/
   (zG C (2*m+2) (2*m+3+t)/\d.f4<=t /\
    ∃P:Finset ℕ,P.Nonempty/\(∀c∈P,c%2=1/\c< 2*(m+1)) /\
     (2*m+1)∈P/\p8 C t=qa (m+1) P):=by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih=>
   intro ht;by_cases _S:t=d.f3
   ·X il ⟨_S,_S▸hJ⟩
   ·by_cases HP:zG C (2*m+2) (2*m+3+t)
    ·right;right
     have _T:d.f4<=t:=by by_contra HB;X z t ht W HP
     Y ⟨HP,_T,?_⟩;by_cases hth:t=d.f4
     ·X ⟨{2*m+1},Finset.singleton_nonempty _,
       fun c hc=>by rw[Finset.mem_singleton] at hc;O,Finset.mem_singleton_self _,hth▸H0⟩
     ·have p:=pE d.f0.1 d.fe ht _S hth
      obtain ⟨H6,hN,_,hh,HC,_d,_⟩:=p4 d.f0.1 ht p
      have Hb:p0 Hz (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+H6)=true :=
       (pM hh).1 HP
      have Hk:(C.gates[t]'ht).op=.or:=HC.symm.trans (d.fk H6 hN Hb);rcases pc d.f0 d.fn t ht with ⟨Hc,_,_,_⟩|⟨_,a1,a2,e,hW,hX,_⟩
      ·rw[Hk] at Hc;cases Hc
      ·obtain ⟨w1,w2,_U,_V,_i,_j,hK⟩:=_d .or a1 a2 (ir rfl) Hk e hW hX
       have HD:∀a,(a=a1\/a=a2)->a< 2*m+3+t ->
         ∃P:Finset ℕ,P.Nonempty/\(∀c∈P,c%2=1/\c< 2*(m+1)) /\
          (zG C (2*m+2) a->(2*m+1)∈P)/\(fun x=>p0 C x a)=qa (m+1) P:=by
        intro a H1 hO;have b:pC (2*m+3) t a (C.gates[t]'ht):=⟨by simp[pa,Hk,e,H1],hO⟩
        by_cases _b:zG C (2*m+2) a
        ·have _W:2*m+3+d.f4<=a:=by
          by_contra HB;X q t ht W a b W _b
         set ta:=a-(2*m+3);have _k:a=2*m+3+ta :=W;rcases ih ta W W with ⟨h0z,_⟩|⟨_X,_,_⟩|⟨_,_,P,Hl,Ht,_Y,hPf⟩
         ·have:=d.fP;O
         ·X absurd (_k▸_b) _X
         ·X ⟨P,Hl,Ht,fun _=>_Y,_k▸hPf⟩
        ·obtain ⟨a'',_t,_,HQ,HR,Hu,_,_L⟩ :=
          qX d a W (fun h=>_S ((d.fi t ht).1 (h▸b)))
           (fun h=>hth ((d.fj t ht).1 (h▸b))) _b
         have H2:=pp d.f0 d.fJ d.fn ht p hN hh b HR;have _l:=zt d hN Hb H2 Hu;rcases qH d.f6 _t HQ with ⟨j,hj,_,_Z⟩|⟨_,_,_,c',_,_u,_Z⟩|⟨_,_,_,Q,Hv,Hw,_Z⟩
         ·have hp:=_l (e1 j) (by rw[cf _Z (e1 j)];simp[e1]);rw[pW] at hp;cases hp
         ·have hp:=_l (e1 (c'-1)) (by rw[cf _Z (e1 (c'-1))];X (pt W _u W).2 (il W))
          rw[pW] at hp;cases hp
         ·X ⟨Q,Hv,fun c hc=>⟨(Hw c hc).1,by have:=(Hw c hc).2;O⟩,fun h=>absurd h _b,
           funext fun x=>by
            have h1:=cf _Z (zc x);have h2:=jx Hw x;X (_L x).trans (h1.trans h2)⟩
       obtain ⟨P1,h00,h0i,h0j,h0k⟩:=HD a1 (il rfl) hW;obtain ⟨P2,h0v,h0l,h0m,h0n⟩:=HD a2 (ir rfl) hX;rw[p6 _ hN (HC.trans Hk) hK _U _V,Bool.or_eq_true] at Hb
       Y ⟨P1∪P2,h00.mono Finset.subset_union_left,
        fun c hc=>by rcases Finset.mem_union.1 hc with h|h<;>[X h0i c h;X h0l c h],?_,?_⟩
       ·rcases Hb with h1|h2
        ·X Finset.mem_union_left _ (h0j ((pM _i).2 h1))
        ·X Finset.mem_union_right _ (h0m ((pM _j).2 h2))
       ·funext x;change p0 C x (2*m+3+t)=_
        have _s:=p6 (n:=2*m+3) x ht Hk e hW hX;rw[_s,cf h0k x,cf h0n x];apply Bool.eq_iff_iff.2;simp only[Bool.or_eq_true,qp]
        constructor
        ·rintro (⟨c,hc,HB,_J,_K⟩|⟨c,hc,HB,_J,_K⟩)
         ·X ⟨c,Finset.mem_union_left _ hc,HB,_J,_K⟩
         ·X ⟨c,Finset.mem_union_right _ hc,HB,_J,_K⟩
        ·rintro ⟨c,hc,HB,_J,_K⟩
         rcases Finset.mem_union.1 hc with h|h<;>[left;right]<;>X ⟨c,h,HB,_J,_K⟩
    ·right;left;Y ⟨HP,_S,?_⟩
     obtain ⟨_,Hm,_,HS,_,_,h01,_e⟩:=qX d (2*m+3+t) W W W HP;have h02:2*m+1<=Hm:=h01 W;have _M:Hm< 2*m+1+hA.size:=HS;set HT:=Hm-(2*m+1);have h03:HT< hA.size :=W;have HU:Hm=2*m+1+HT :=W
     have HE:∀x:Fin (2*m+3)->Bool,p8 C t x=p8 hA HT (zc x):=by
      intro x;change p0 C x (2*m+3+t)=p0 hA (zc x) (2*m+1+HT);rw[_e x,HU]
     rcases d.f6.2.1 HT h03 with ⟨c,_f,_v,hkf⟩|⟨P,Hl,Ht,hkf⟩
     ·X il ⟨c,_f,_v,funext fun x=>(HE x).trans ((cf hkf (zc x)).trans (j5 _v x))⟩
     ·X ir ⟨P,Hl,Ht,funext fun x=>(HE x).trans ((cf hkf (zc x)).trans (jx Ht x))⟩
 have HV:=k7 d hu q;obtain ⟨tq,htq,hG,hD⟩:=zD d.f0.1 d.fv d.fD
 have h04:d.f4< tq:=by
  have hUq:zG C (2*m+2) (2*m+3+tq):=(pM hD).2 (jh d.fD d.fI d.fK d.fw);have hge:d.f4<=tq:=by by_contra HB;X z tq htq W hUq
  have hne:tq≠d.f4:=fun _N=>by
   have h1:=(d.fe d.f4 d.fa).2 (ir rfl)
   have h2:(p5 C (2*m+2) true).fb[d.f4]'(by rw[(pk C (2*m+2) true d.f0.1).kept_len];X d.fa)=true:=by
    subst _N;X hG
   rw[h1] at h2;cases h2
  O
 have h0w:=zT d;set _w:=d.z''-(2*m+2);have HW:_w< Hz.size:=by have hq:d.fv< Hz.size:=d.fD;have:=d.fw;O
 have Hd:d.z''=2*m+2+_w :=W;obtain ⟨tz,htz,H7,H3⟩:=zD d.f0.1 _w HW
 have HX:tz≠d.f3:=fun _N=>by
  have h1:=(d.fe d.f3 d.f9).2 (il rfl)
  have h2:(p5 C (2*m+2) true).fb[d.f3]'(by rw[(pk C (2*m+2) true d.f0.1).kept_len];X d.f9)=true:=by
   subst _N;X H7
  rw[h1] at h2;cases h2
 Y ⟨d.fJ,?_,?_⟩
 ·intro t ht
  rcases hV t ht with ⟨_,HE⟩|⟨_,_,⟨c,_f,_v,HE⟩|⟨P,Hl,Ht,HE⟩⟩|⟨_,_,P,Hl,Ht,_,HE⟩
  ·X il ⟨2*m+1,by O,by O,HE⟩
  ·X il ⟨c,_f,by O,HE⟩
  ·X ir ⟨P,Hl,fun c hc=>⟨(Ht c hc).1,by have:=(Ht c hc).2;O⟩,HE⟩
  ·X ir ⟨P,Hl,Ht,HE⟩
 ·intro t ht P Hl Ht _O c hcP
  have _f:=(Ht c hcP).1;have _v:=(Ht c hcP).2
  have HF:t≠d.f3:=fun h=>
   q3 (r:=m+1) (c:=2*m+1) W W ((h▸hJ).symm.trans _O)
  by_cases _x:c=2*m+1
  ·
   subst _x
   have HP:zG C (2*m+2) (2*m+3+t):=by
    rcases hV t ht with ⟨rfl,_⟩|⟨_,_,⟨c',h0o,_,HE⟩|⟨Q,_,Hw,HE⟩⟩|⟨hU,_,_⟩
    ·X absurd rfl HF
    ·X absurd (HE.symm.trans _O) (q3 (r:=m+1) (c:=c') h0o W)
    ·exfalso
     have h1:=cf (HE.symm.trans _O) (pe (2*m))
     have htr:qa (m+1) P (pe (2*m))=true :=
      (q7 (c:=2*m+1) Ht W W).2 hcP
     rw[htr] at h1;have H1:=(q7 (c:=2*m+1) (fun c hc=>⟨(Hw c hc).1,by have:=(Hw c hc).2;O⟩) W W).1 h1
     have:=(Hw (2*m+1) H1).2;O
    ·X hU
   have _y:d.f4<=t:=by by_contra HB;X z t ht W HP
   set xe:Fin (2*m+3)->Bool:=pe (2*m)
   have HY:zc xe=(e1 (2*m):Fin (2*m+1)->Bool):=by
    funext j;simp only[zc,xe,pe,e2,e1];apply Bool.eq_iff_iff.2;have:=j.isLt;simp only[decide_eq_true_eq]
    constructor<;>intro hj<;>O
   have HL:∀i< 2*m+3+C.size,i≠2*m+2->i≠2*m+3+d.f3 ->
     ¬zG C (2*m+2) i->pl C xe t false i=p0 C xe i:=by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih=>
     intro h05 han hag He;by_cases hin:i< 2*m+3
     ·X pA C xe t ht false i W
     ·set v:=i-(2*m+3)
      have hv:v< C.size :=W;have Hn:i=2*m+3+v :=W;rw[Hn] at hag He ⊢;have HG:v≠t:=fun h=>He (h▸HP);have hH:v≠d.f3 :=W;have hI:v≠d.f4:=fun h=>He (h▸d.fT);have f:=pE d.f0.1 d.fe hv hH hI;rcases pc d.f0 d.fn v hv with ⟨Hc,_,_,_⟩|⟨H4,a1,a2,e,hW,hX,_⟩
      ·X absurd Hc (d.fJ _ (List.getElem_mem hv))
      ·have hma:∀a,(a=a1\/a=a2)->a< 2*m+3+v->pl C xe t false a=p0 C xe a:=by
        intro a H1 hO
        have b:pC (2*m+3) v a (C.gates[v]'hv):=by
         rcases H4 with h|h<;>X ⟨by simp[pa,h,e,H1],hO⟩
        X ih a W W (fun h=>hH ((d.fi v hv).1 (h▸b)))
         (fun h=>hI ((d.fj v hv).1 (h▸b)))
         (j3 d.f0 d.fJ d.fn d.fp hv f He b)
       rcases H4 with hop_eq|hop_eq
       ·rw[pF xe ht false hv HG hop_eq e hW hX,pm xe hv hop_eq e hW hX,
         hma a1 (il rfl) hW,hma a2 (ir rfl) hX]
       ·rw[pJ xe ht false hv HG hop_eq e hW hX,p6 xe hv hop_eq e hW hX,
         hma a1 (il rfl) hW,hma a2 (ir rfl) hX]
   have Hf:∀v (hv:v< C.size),t<=v->zG C (2*m+2) (2*m+3+v) ->
     pl C xe t false (2*m+3+v)=false:=by
    intro v
    induction v using Nat.strong_induction_on with
    | ind v ih=>
     intro hv htv hUv;by_cases _e:v=t
     ·rw[_e];X qs C xe t ht false
     ·have hgh:=d.fP
      have f:=pE d.f0.1 d.fe hv W W;obtain ⟨HZ,hP,_,hE,hB,_,_⟩:=p4 d.f0.1 hv f
      have _0:p0 Hz (e1 (2*m+1):Fin (2*m+2)->Bool) (2*m+2+HZ)=true :=
       (pM hE).1 hUv
      have H5:(C.gates[v]'hv).op=.or:=hB.symm.trans (d.fk HZ hP _0);rcases pc d.f0 d.fn v hv with ⟨Hc,_,_,_⟩|⟨_,a1,a2,e,hW,hX,_⟩
      ·rw[H5] at Hc;cases Hc
      ·rw[pJ xe ht false hv _e H5 e hW hX,Bool.or_eq_false_iff]
       have h06:∀a,(a=a1\/a=a2)->a< 2*m+3+v->pl C xe t false a=false:=by
        intro a H1 hO;have b:pC (2*m+3) v a (C.gates[v]'hv):=⟨by simp[pa,H5,e,H1],hO⟩
        have HH:a≠2*m+2:=fun h=>by have:=(d.fi v hv).1 (h▸b);O
        have HI:a≠2*m+3+d.f3:=fun h=>by have:=(d.fj v hv).1 (h▸b);O
        by_cases _b:zG C (2*m+2) a
        ·have _W:2*m+3+d.f4<=a:=by
          by_contra HB;X q v hv W a b W _b
         set wa:=a-(2*m+3);have Hg:a=2*m+3+wa :=W
         have _1:t<=wa:=by
          by_contra HB
          have:=HV t ht _y HP wa W W (Hg▸_b) v hv (Hg▸b);O
         rw[Hg];X ih wa W W _1 (Hg▸_b)
        ·rw[HL a W HH HI _b]
         obtain ⟨a'',_t,_,_,HR,Hu,_,_L⟩:=qX d a W HH HI _b;rw[_L xe,HY];have H2:=pp d.f0 d.fJ d.fn hv f hP hE b HR
         cases hQ:p0 hA (e1 (2*m):Fin (2*m+1)->Bool) _t with
         | false=>rfl
         | true=>
          have hp:=zt d hP _0 H2 Hu _ hQ;rw[pW] at hp;cases hp
       X ⟨h06 a1 (il rfl) hW,h06 a2 (ir rfl) hX⟩
   have h0f:=pB d.fn
   have h0g:2*m+3+t<=C.output:=by
    by_contra HB
    suffices hno:∀k (v:ℕ),C.size-v<=k->t<=v->v< C.size->False by
     X hno (C.size-t) t le_rfl le_rfl ht
    intro k
    induction k with
    | zero=>intro v hle _ hv;O
    | succ k ihk=>
     intro v hle htv hv;rcases pY d.f0 v hv with hout|⟨r,hr,hvr,_⟩
     ·O
     ·X ihk r W W hr
   set vout:=C.output-(2*m+3);have Ho:C.output=2*m+3+vout :=W;rw[Ho];X Hf vout W W (Ho▸d.fo)
  ·
   have HJ:c< 2*m :=W
   have Hh:t≠d.f4:=fun h=>by
    have h1:=cf ((h▸H0).symm.trans _O) (pe (c-1));rw[(q7 Ht _f _v).2 hcP] at h1
    have h07:∀x∈({2*m+1}:Finset ℕ),x%2=1/\x< 2*(m+1):=by
     intro x hx;rw[Finset.mem_singleton] at hx;O
    have hm1:=(q7 h07 _f _v).1 h1;rw[Finset.mem_singleton] at hm1;O
   set xe:Fin (2*m+3)->Bool:=pe (c-1);set ye:Fin (2*m+1)->Bool:=pe (c-1);by_cases _2:2*m+3+t=C.output
   ·rw[←_2];X qs C xe t ht false
   have p:=pE d.f0.1 d.fe ht HF Hh;obtain ⟨H6,hN,_,hh,_,_,_⟩:=p4 d.f0.1 ht p
   have Hp:∀y:Fin (2*m+1)->Bool,∀i< 2*m+3+C.size,i≠2*m+2->i≠2*m+3+d.f3 ->
     p0 C (Fin.snoc (Fin.snoc y false) false) i=p0 C (Fin.snoc (Fin.snoc y false) true) i:=by
    intro y i
    induction i using Nat.strong_induction_on with
    | ind i ihi=>
     intro h05 h10 h0p;by_cases hin:i< 2*m+3
     ·rw[p7 C _ i hin,p7 C _ i hin]
      have:(⟨i,hin⟩:Fin (2*m+3))=Fin.castSucc ⟨i,by O⟩:=Fin.ext rfl
      rw[this,Fin.snoc_castSucc,Fin.snoc_castSucc]
     ·set v:=i-(2*m+3)
      have hv:v< C.size :=W;have Hn:i=2*m+3+v :=W;rw[Hn] at h0p ⊢;by_cases hvh:v=d.f4
      ·rw[hvh]
       have h08:p0 C (Fin.snoc (Fin.snoc y false) false) (2*m+1)=false:=by
        rw[p7 C _ (2*m+1) W]
        have:(⟨2*m+1,by O⟩:Fin (2*m+3))=Fin.castSucc (Fin.last (2*m+1)):=Fin.ext rfl
        rw[this,Fin.snoc_castSucc,Fin.snoc_last]
       have h09:p0 C (Fin.snoc (Fin.snoc y false) true) (2*m+1)=false:=by
        rw[p7 C _ (2*m+1) W]
        have:(⟨2*m+1,by O⟩:Fin (2*m+3))=Fin.castSucc (Fin.last (2*m+1)):=Fin.ext rfl
        rw[this,Fin.snoc_castSucc,Fin.snoc_last]
       have hgh:=d.fP;rcases d.fy with e|e
       ·rw[pm _ d.fa d.fm (hu▸e) W W,
         pm _ d.fa d.fm (hu▸e) W W,h08,h09,Bool.and_false,Bool.and_false]
       ·rw[pm _ d.fa d.fm (hu▸e) W W,
         pm _ d.fa d.fm (hu▸e) W W,h08,h09,Bool.false_and,Bool.false_and]
      ·rw[pj C _ v hv,pj C _ v hv]
       apply zy _ (d.f0.1 _ (List.getElem_mem hv));intro a ha;by_cases hO:a< 2*m+3+v
       ·simp only[hO,↓reduceIte]
        X ihi a W W (fun h=>by have:=(d.fi v hv).1 ⟨h▸ha,h▸hO⟩;O)
         (fun h=>hvh ((d.fj v hv).1 ⟨h▸ha,h▸hO⟩))
       ·simp only[hO,↓reduceIte]
   have hC:∀(y:Fin (2*m+1)->Bool) (_g:ℕ),
     HA.fc.getD (2*m+2+H6) (.const false)=.wire _g ->
     p0 hA y _g=p0 C (Fin.snoc (Fin.snoc y false) false) (2*m+3+t):=by
    intro y _g hew
    have hs2:p0 hA y _g=p0 Hz (Fin.snoc y false) (2*m+2+H6):=by
     have h:=pH Hz (2*m+1) false d.f7.1 y (2*m+2+H6);rw[hew] at h;X h
    have hs1:p0 Hz (Fin.snoc y false) (2*m+2+H6)=p0 C (Fin.snoc (Fin.snoc y false) true) (2*m+3+t):=by
     have h:=pH C (2*m+2) true d.f0.1 (Fin.snoc y false) (2*m+3+t);rw[hh] at h;X h
    X (hs2.trans hs1).trans (Hp y (2*m+3+t) W W W).symm
   have _3:xe=Fin.snoc (Fin.snoc ye false) false:=by
    funext j;by_cases h1:j.val< 2*m+1
    ·have:j=Fin.castSucc (Fin.castSucc ⟨j.val,h1⟩):=Fin.ext rfl;rw[this,Fin.snoc_castSucc,Fin.snoc_castSucc];R
    ·by_cases h2:j.val=2*m+1
     ·have:j=Fin.castSucc (Fin.last (2*m+1)):=Fin.ext (by simp[h2])
      rw[this,Fin.snoc_castSucc,Fin.snoc_last];simp only[xe,pe,e2,decide_eq_false_iff_not];O
     ·have:j=Fin.last (2*m+2):=Fin.ext (by have:=j.isLt;simp;O)
      rw[this,Fin.snoc_last];simp only[xe,pe,e2,decide_eq_false_iff_not];O
   have HM:∃l:ℕ,∃(hF:l< hA.size),
     HA.fc.getD (2*m+2+H6) (.const false)=.wire (2*m+1+l) /\
     ∃Q:Finset ℕ,Q.Nonempty/\(∀c'∈Q,c'%2=1/\c'< 2*m)/\p8 hA l=qa m Q/\c∈Q:=by
    have _m:p0 C (Fin.snoc (Fin.snoc ye false) false) (2*m+3+t)=true:=by
     rw[←_3];change p8 C t xe=true;rw[_O];X (q7 Ht _f _v).2 hcP
    by_cases hkq:H6=d.fv
    ·obtain ⟨Q,Hv,Hw,hQf⟩:=d.fG
     have _4:p8 hA d.fg ye=true:=(hC ye _ (hkq▸d.fx)).trans _m;rw[hQf] at _4;X ⟨d.fg,d.fA,hkq▸d.fx,Q,Hv,Hw,hQf,(q7 Hw _f HJ).1 _4⟩
    ·have hL:=q4 d.f7.1 d.ff hN hkq
     obtain ⟨l,hF,_,g,_,_,_⟩:=p4 d.f7.1 hN hL;have _4:p8 hA l ye=true:=(hC ye _ g).trans _m;rcases d.f6.2.1 l hF with ⟨c',_,_u,hkf⟩|⟨Q,Hv,Hw,hQf⟩
     ·exfalso
      have _5:(e1 (c'-1):Fin (2*m+3)->Bool)=Fin.snoc (Fin.snoc (e1 (c'-1):Fin (2*m+1)->Bool) false) false:=by
       funext j;by_cases h1':j.val< 2*m+1
       ·have:j=Fin.castSucc (Fin.castSucc ⟨j.val,h1'⟩):=Fin.ext rfl;rw[this,Fin.snoc_castSucc,Fin.snoc_castSucc];R
       ·by_cases h2':j.val=2*m+1
        ·have:j=Fin.castSucc (Fin.last (2*m+1)):=Fin.ext (by simp[h2'])
         rw[this,Fin.snoc_castSucc,Fin.snoc_last];simp[e1];O
        ·have:j=Fin.last (2*m+2):=Fin.ext (by have:=j.isLt;simp;O)
         rw[this,Fin.snoc_last];simp[e1];O
      have h1:=hC (e1 (c'-1)) _ g;rw[←_5] at h1
      have h0a:p8 hA l (e1 (c'-1):Fin (2*m+1)->Bool)=true:=by
       rw[hkf];X (pt W _u W).2 (il W)
      have _z:p8 C t (e1 (c'-1):Fin (2*m+3)->Bool)=false:=by
       rw[_O];X q2 (c'-1)
      change p8 hA l (e1 (c'-1):Fin (2*m+1)->Bool)=p8 C t (e1 (c'-1):Fin (2*m+3)->Bool) at h1;rw[h0a,_z] at h1;cases h1
     ·rw[hQf] at _4
      X ⟨l,hF,g,Q,Hv,Hw,hQf,(q7 Hw _f HJ).1 _4⟩
   obtain ⟨l,hF,g,Q,Hv,Hw,Hx,hcQ⟩:=HM
   have Hq:t=tq->∀v (hv:v< C.size),pC (2*m+3) v (2*m+3+tz) (C.gates[v]'hv)->v=tq:=by
    intro h0b;rcases pY d.f0 tq htq with hout|⟨r,hr,hqr,hrr⟩
    ·X absurd (h0b▸hout.symm) _2
    ·have hgh:=d.fP
     have H8:=pE d.f0.1 d.fe hr W W;obtain ⟨h11,_n,_,_6,_,_,_⟩:=p4 d.f0.1 hr H8
     X zP d hw htq htz hG hD (Hd▸H3)
      HX W _n (pp d.f0 d.fJ d.fn hr H8 _n _6 hrr hD)
   have hS:pl C xe t false (2*m+1)=false:=by
    rw[pA C xe t ht false (2*m+1) W,p7 C xe (2*m+1) W];simp only[xe,pe,e2,decide_eq_false_iff_not];O
   have HK:pl C xe t false (2*m+3+d.f4)=false:=by
    have hgh:=d.fP;rcases d.fy with e|e
    ·rw[pF xe ht false d.fa Hh.symm d.fm (hu▸e) W W,hS,Bool.and_false]
    ·rw[pF xe ht false d.fa Hh.symm d.fm (hu▸e) W W,hS,Bool.false_and]
   have _7:∀i< 2*m+3+C.size,i≠2*m+2->i≠2*m+3+d.f3 ->
     i≠2*m+1->i≠2*m+3+d.f4->(t=tq->i≠2*m+3+tz) ->
     ∀(i'' Hm:ℕ),_q.fc.getD i (.const false)=.wire i''->HA.fc.getD i'' (.const false)=.wire Hm ->
      pl C xe t false i=true->pl hA ye l false Hm=true:=by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih=>
     intro h05 h0x h0q h0y h0r _o i'' Hm H9 hT hQ;by_cases hin:i< 2*m+3
     ·have _p:i< 2*m+1 :=W
      have h1:=pd C (2*m+2) true i W;have h2:=pd Hz (2*m+1) false i _p;rw[H9] at h1;cases h1;rw[hT] at h2;cases h2;rw[pA C xe t ht false i W,p7 C xe i W] at hQ;rw[pA hA ye l hF false i W,p7 hA ye i _p];X hQ
     ·set v:=i-(2*m+3)
      have hv:v< C.size :=W;have Hn:i=2*m+3+v :=W;rw[Hn] at h0q h0r _o H9 hQ;by_cases _A:v=t
      ·rw[_A,qs C xe t ht false] at hQ;cases hQ
      ·have hH:v≠d.f3 :=W
       have hI:v≠d.f4 :=W;have f:=pE d.f0.1 d.fe hv hH hI;obtain ⟨HZ,hP,_,hE,hB,Hi,_⟩:=p4 d.f0.1 hv f;rw[H9] at hE;cases hE;rcases pc d.f0 d.fn v hv with ⟨Hc,_,_,_⟩|⟨H4,a1,a2,e,hW,hX,_⟩
       ·X absurd Hc (d.fJ _ (List.getElem_mem hv))
       ·by_cases hvq:HZ=d.fv
        ·have H5:(C.gates[v]'hv).op=.or:=hB.symm.trans (hvq▸d.fI)
         obtain ⟨w1,w2,_,_,_i,_j,hK⟩:=Hi .or a1 a2 (ir rfl) H5 e hW hX;have _B:v=tq:=pO d.f0.1 hv htq f hG (hvq▸H9) hD;have _8:t≠tq:=fun h=>_A (_B.trans h.symm);rw[hvq,d.fx] at hT;cases hT;rw[pJ xe ht false hv _A H5 e hW hX,Bool.or_eq_true] at hQ
         have hY:∀a wa,(a=a1\/a=a2)->a< 2*m+3+v->_q.fc.getD a (.const false)=.wire wa ->
           (wa=2*m+1\/wa=d.z'')->pl C xe t false a=true ->
           pl hA ye l false (2*m+1+d.fg)=true:=by
          intro a wa H1 hO _9 _h s;have b:pC (2*m+3) v a (C.gates[v]'hv):=⟨by simp[pa,H5,e,H1],hO⟩
          have HH:a≠2*m+2:=fun h=>hH ((d.fi v hv).1 (h▸b));have HI:a≠2*m+3+d.f3:=fun h=>hI ((d.fj v hv).1 (h▸b));rcases _h with rfl|rfl
          ·by_cases h0s:a=2*m+1
           ·rw[h0s,hS] at s;cases s
           ·by_cases hah:a=2*m+3+d.f4
            ·rw[hah,HK] at s;cases s
            ·exfalso
             by_cases h12:a< 2*m+3
             ·have h1:=pd C (2*m+2) true a W;rw[_9] at h1;injection h1 with h1;O
             ·set va:=a-(2*m+3)
              have _L:va< C.size :=W;have hka:=pE d.f0.1 d.fe _L W W;obtain ⟨ka,_,_,_C,_,_,_⟩:=p4 d.f0.1 _L hka;rw[show 2*m+3+va=a by O,_9] at _C;injection _C with _C;O
          ·X ih a W W HH HI
            (fun h=>by rw[h,hS] at s;cases s) (fun h=>by rw[h,HK] at s;cases s)
            (fun h=>absurd h _8) d.z'' (2*m+1+d.fg) _9 d.fL s
         have _D:[w1,w2]=[2*m+1,d.z'']\/[w1,w2]=[d.z'',2*m+1]:=by
          have:(Hz.gates[HZ]'hP).inputs=(Hz.gates[d.fv]'d.fD).inputs:=by subst hvq;R
          rw[hK] at this;rw[this];X d.fK
         rcases _D with h|h<;>cases h<;>rcases hQ with h1|h2
         ·X hY a1 (2*m+1) (il rfl) hW _i (il rfl) h1
         ·X hY a2 d.z'' (ir rfl) hX _j (ir rfl) h2
         ·X hY a1 d.z'' (il rfl) hW _i (ir rfl) h1
         ·X hY a2 (2*m+1) (ir rfl) hX _j (il rfl) h2
        ·have hM:=q4 d.f7.1 d.ff hP hvq
         obtain ⟨h0c,_a,_,Ha,Hr,Hs,_⟩:=p4 d.f7.1 hP hM;rw[hT] at Ha;cases Ha
         have hR:h0c≠l:=fun _N=>by
          by_cases _E:H6=d.fv
          ·have _F:=pO d.f0.1 ht htq p hG (_E▸hh) hD
           have _G:l=d.fg:=by rw[_E,d.fx] at g;injection g with h;O
           have Hy:=q4 d.f7.1 d.ff HW (by have:=d.fw;O)
           have HN:=pO d.f7.1 hP HW hM Hy (by rw[←_G,←_N];X hT) (Hd▸d.fL)
           have h0d:=pO d.f0.1 hv htz f H7 (HN▸H9) H3;X _o _F W
          ·have hL:=q4 d.f7.1 d.ff hN _E
           have HO:=pO d.f7.1 hP hN hM hL (_N▸hT) g;X _A (pO d.f0.1 hv ht f p (HO▸H9) hh)
         have hZ:∀a wa ua,(a=a1\/a=a2)->a< 2*m+3+v ->
           _q.fc.getD a (.const false)=.wire wa->HA.fc.getD wa (.const false)=.wire ua ->
           pl C xe t false a=true->pl hA ye l false ua=true:=by
          intro a wa ua H1 hO _9 h0t s
          have b:pC (2*m+3) v a (C.gates[v]'hv):=by
           rcases H4 with h|h<;>X ⟨by simp[pa,h,e,H1],hO⟩
          X ih a W W (fun h=>hH ((d.fi v hv).1 (h▸b)))
           (fun h=>hI ((d.fj v hv).1 (h▸b)))
           (fun h=>by rw[h,hS] at s;cases s) (fun h=>by rw[h,HK] at s;cases s)
           (fun h0e h0u=>_A ((Hq h0e v hv (h0u▸b)).trans h0e.symm)) wa ua _9 h0t s
         rcases H4 with hop_eq|hop_eq
         ·obtain ⟨w1,w2,_U,_V,_i,_j,hK⟩:=Hi .and a1 a2 (il rfl) hop_eq e hW hX
          obtain ⟨u1,u2,hu1,hu2,_H,_I,Hj⟩:=Hs .and w1 w2 (il rfl) (hB.trans hop_eq) hK _U _V;rw[pF xe ht false hv _A hop_eq e hW hX,Bool.and_eq_true] at hQ;rw[pF ye hF false _a hR (Hr.trans (hB.trans hop_eq)) Hj hu1 hu2,Bool.and_eq_true];X ⟨hZ a1 w1 u1 (il rfl) hW _i _H hQ.1,hZ a2 w2 u2 (ir rfl) hX _j _I hQ.2⟩
         ·obtain ⟨w1,w2,_U,_V,_i,_j,hK⟩:=Hi .or a1 a2 (ir rfl) hop_eq e hW hX
          obtain ⟨u1,u2,hu1,hu2,_H,_I,Hj⟩:=Hs .or w1 w2 (ir rfl) (hB.trans hop_eq) hK _U _V;rw[pJ xe ht false hv _A hop_eq e hW hX,Bool.or_eq_true] at hQ;rw[pJ ye hF false _a hR (Hr.trans (hB.trans hop_eq)) Hj hu1 hu2,Bool.or_eq_true];rcases hQ with h1|h2
          ·X il (hZ a1 w1 u1 (il rfl) hW _i _H h1)
          ·X ir (hZ a2 w2 u2 (ir rfl) hX _j _I h2)
   cases hval_out:pl C xe t false C.output with
   | false=>rfl
   | true=>
    exfalso
    have htr:=_7 C.output (pB d.fn)
     (fun h=>pI (p9 C (2*m+2) true d.f0.1) (h▸d.fo))
     (fun h=>pI d.fh (h▸d.fo))
     (fun h=>by rw[h,hS] at hval_out;cases hval_out)
     (fun h=>by rw[h,HK] at hval_out;cases hval_out)
     (fun _ h=>by
      have hUz:p0 Hz (e1 (2*m+1):Fin (2*m+2)->Bool) d.z''=true :=
       (pM (Hd▸H3)).1 (h▸d.fo)
      rw[jV d.fD d.f7 d.fq d.fB d.fk d.z'' d.fw d.fR] at hUz;cases hUz)
     Hz.output hA.output (q8 d.f0.1 d.fN) (q8 d.f7.1 d.fO) hval_out
    rw[d.f6.2.2 l hF Q Hv Hw Hx c hcQ] at htr;cases htr
private lemma k8:∀r:ℕ,1<=r->∀C:J,
  IsMinimalCircuit (2*r+1) C->cF (2*r+1) C=pq (2*r+1)->zb r C:=by
 intro r
 induction r with
 | zero=>intro h;O
 | succ r ih=>
  intro _ C a hfun
  cases r with
  | zero=>X jF a hfun
  | succ m=>X jG W a hfun (ih W)
private def e3 {n:ℕ} (a b c:ℕ):V n :=
 fun j=>decide (j.val=a\/j.val=b\/j.val=c)
private def ph (m:ℕ) (S:Finset ℕ) (x:Fin (2*m)->Bool):Bool :=
 decide (∃i j:Fin (2*m),i.val∈S/\i.val+1=j.val/\x i=true/\x j=true)
private def q1 (m:ℕ) (f:(Fin (2*m)->Bool)->Bool):Prop :=
 ∃S:Finset ℕ,S.Nonempty/\(∀i∈S,i+1< 2*m)/\f=ph m S
private def pP (m c:ℕ) (x:Fin (2*m)->Bool):Bool :=
 decide (∃k:Fin (2*m),(k.val+1=c\/k.val=c+1)/\x k=true)
private def zM (m:ℕ) (f:(Fin (2*m)->Bool)->Bool):Prop :=
 ∃c:ℕ,1<=c/\c+1< 2*m/\f=pP m c
private def qd (m i k:ℕ) (x:Fin (2*m)->Bool):Bool :=
 ph m {i} x||(if hk:k< 2*m then x ⟨k,hk⟩ else false)
private def qb (m:ℕ) (f:(Fin (2*m)->Bool)->Bool):Prop :=
 ∃i k:ℕ,i%2=0/\i+1< 2*m/\k< 2*m/\(k=i+2\/k+1=i)/\f=qd m i k
private def qf (m:ℕ) (C:J):Prop :=
 z0 C /\
 ∀t (_:t< C.size),
  q1 m (p8 C t)\/zM m (p8 C t)\/qb m (p8 C t)
private lemma po {m:ℕ} {S:Finset ℕ} {x:Fin (2*m)->Bool} :
  ph m S x=true ↔
   ∃i j:Fin (2*m),i.val∈S/\i.val+1=j.val/\x i=true/\x j=true:=by
 simp[ph]
private lemma pT {m:ℕ} {S:Finset ℕ} {x:Fin (2*m)->Bool}
  (hx:ph m S x=true):pq (2*m) x=true:=by
 rw[po] at hx;obtain ⟨i,j,_,a,hi,hj⟩:=hx;rw[px];X ⟨i,j,a,hi,hj⟩
private lemma pz {m:ℕ} {S:Finset ℕ} (a:ℕ) :
  ph m S (e1 a)=false:=by
 cases hv:ph m S (e1 a) with
 | false=>rfl
 | true=>have:=pT hv;rw[pW] at this;cases this
private lemma pg {m:ℕ} {S:Finset ℕ}
  (hS:∀i∈S,i+1< 2*m) {e:ℕ} (he:e+1< 2*m) :
  ph m S (pe e)=true↔e∈S:=by
 rw[po]
 constructor
 ·rintro ⟨i,j,f,g,a,b⟩
  simp only[pe,e2,decide_eq_true_eq] at a b;have c:i.val=e :=W;rwa[←c]
 ·intro d
  X ⟨⟨e,by O⟩,⟨e+1,he⟩,d,rfl,by simp[pe,e2],by simp[pe,e2]⟩
private lemma qM {m:ℕ} {S1 S2:Finset ℕ}
  (h1:∀i∈S1,i+1< 2*m) (h2:∀i∈S2,i+1< 2*m)
  (b:ph m S1=ph m S2):S1=S2:=by
 ext e
 constructor
 ·intro he
  have a:=h1 e he
  have:=cf b (pe e)
  rw[(pg h1 a).2 he] at this;X (pg h2 a).1 this.symm
 ·intro he
  have a:=h2 e he
  have:=cf b (pe e)
  rw[(pg h2 a).2 he] at this;X (pg h1 a).1 this
private lemma qZ {m:ℕ} (S1 S2:Finset ℕ) (x:Fin (2*m)->Bool) :
  (ph m S1 x||ph m S2 x)=ph m (S1∪S2) x:=by
 apply Bool.eq_iff_iff.2;simp only[Bool.or_eq_true,po,Finset.mem_union]
 constructor
 ·rintro (⟨i,j,h,a,hi,hj⟩|⟨i,j,h,a,hi,hj⟩)
  ·X ⟨i,j,il h,a,hi,hj⟩
  ·X ⟨i,j,ir h,a,hi,hj⟩
 ·rintro ⟨i,j,h|h,a,hi,hj⟩
  ·X il ⟨i,j,h,a,hi,hj⟩
  ·X ir ⟨i,j,h,a,hi,hj⟩
private lemma pv {m i:ℕ} (hi:i+1< 2*m) (x:Fin (2*m)->Bool) :
  ph m {i} x=(x ⟨i,by O⟩&&x ⟨i+1,hi⟩):=by
 apply Bool.eq_iff_iff.2;simp only[po,Finset.mem_singleton,Bool.and_eq_true]
 constructor
 ·rintro ⟨a,b,ha,g,c,d⟩
  have e:a=⟨i,by O⟩:=Fin.ext ha
  have f:b=⟨i+1,hi⟩:=Fin.ext (by dsimp;O)
  X ⟨e▸c,f▸d⟩
 ·rintro ⟨h1,h2⟩
  X ⟨⟨i,by O⟩,⟨i+1,hi⟩,rfl,rfl,h1,h2⟩
private lemma zu {m a b:ℕ} (x:Fin (2*m)->Bool) :
  ph m {a,b} x=(ph m {a} x||ph m {b} x):=by
 rw[qZ];R
private lemma jb {m a b c:ℕ} (x:Fin (2*m)->Bool) :
  ph m {a,b,c} x=((ph m {a} x||ph m {b} x)||ph m {c} x):=by
 rw[qZ,qZ];congr 1;ext e;simp[or_assoc]
private lemma jM (m:ℕ) (x:Fin (2*m)->Bool) :
  pq (2*m) x=ph m (Finset.range (2*m-1)) x:=by
 apply Bool.eq_iff_iff.2;simp only[px,po,Finset.mem_range]
 constructor
 ·rintro ⟨i,j,a,hi,hj⟩;X ⟨i,j,by have:=j.isLt;O,a,hi,hj⟩
 ·rintro ⟨i,j,_,a,hi,hj⟩;X ⟨i,j,a,hi,hj⟩
private lemma j9 {m c:ℕ} {x:Fin (2*m)->Bool} :
  pP m c x=true↔∃k:Fin (2*m),(k.val+1=c\/k.val=c+1)/\x k=true:=by
 simp[pP]
private lemma qe {m c:ℕ} (d:1<=c) (a:c+1< 2*m) (x:Fin (2*m)->Bool) :
  pP m c x=(x ⟨c-1,by O⟩||x ⟨c+1,a⟩):=by
 apply Bool.eq_iff_iff.2;simp only[j9,Bool.or_eq_true]
 constructor
 ·rintro ⟨k,hk,b⟩
  rcases hk with h|h
  ·left;X (Fin.ext (by dsimp;O):k=⟨c-1,by O⟩)▸b
  ·right;X (Fin.ext h:k=⟨c+1,a⟩)▸b
 ·rintro (h|h)
  ·X ⟨⟨c-1,by O⟩,il (by dsimp;O),h⟩
  ·X ⟨⟨c+1,a⟩,ir rfl,h⟩
private lemma pu {m c a:ℕ} (b:1<=c) (d:c+1< 2*m) (ha:a< 2*m) :
  pP m c (e1 a)=true↔a+1=c\/a=c+1:=by
 rw[qe b d];simp only[Bool.or_eq_true,e1,decide_eq_true_eq];O
private lemma qh {m i k:ℕ} (hi:i+1< 2*m) (hk:k< 2*m) (x:Fin (2*m)->Bool) :
  qd m i k x=((x ⟨i,by O⟩&&x ⟨i+1,hi⟩)||x ⟨k,hk⟩):=by
 simp only[qd,pv hi,hk,↓reduceDIte]
private lemma pN {m i k a:ℕ} (hk:k< 2*m) (ha:a< 2*m) :
  qd m i k (e1 a)=true↔a=k:=by
 simp only[qd,pz,Bool.false_or,hk,↓reduceDIte,e1,decide_eq_true_eq];X eq_comm
private lemma qo {m i k e:ℕ} (hi:i+1< 2*m) (hk:k< 2*m) (he:e+1< 2*m) :
  qd m i k (pe e)=true↔e=i\/e=k\/e+1=k:=by
 rw[qh hi hk];simp only[Bool.or_eq_true,Bool.and_eq_true,pe,e2,decide_eq_true_eq];O
private lemma ky {m i k:ℕ} (b:i%2=0) (hi:i+1< 2*m) (hk:k< 2*m)
  (a:k=i+2\/k+1=i):1<=k/\k+1< 2*m:=by
 rcases a with rfl|h<;>O
private lemma zv {m j:ℕ} {S:Finset ℕ} (hj:j< 2*m) :
  ph m S≠(fun x:Fin (2*m)->Bool=>x ⟨j,hj⟩):=by
 intro h;have h1:=cf h (e1 j);rw[pz] at h1;simp[e1] at h1
private lemma jr {m c j:ℕ} (b:1<=c) (a:c+1< 2*m) (hj:j< 2*m) :
  pP m c≠(fun x:Fin (2*m)->Bool=>x ⟨j,hj⟩):=by
 intro h;have h1:=cf h (e1 (c-1));have h2:=cf h (e1 (c+1));rw[(pu b a W).2 (il W)] at h1;rw[(pu b a a).2 (ir rfl)] at h2;have d:j=c-1:=of_decide_eq_true h1.symm;have e:j=c+1:=of_decide_eq_true h2.symm;O
private lemma zw {m i k j:ℕ} (hi:i+1< 2*m) (hk:k< 2*m)
  (a:k=i+2\/k+1=i) (hj:j< 2*m) :
  qd m i k≠(fun x:Fin (2*m)->Bool=>x ⟨j,hj⟩):=by
 intro h;have h1:=cf h (e1 k);rw[(pN hk hk).2 rfl] at h1;have b:j=k:=of_decide_eq_true h1.symm;subst b;have h2:=cf h (pe i);rw[(qo hi hk hi).2 (il rfl)] at h2;simp only[pe,e2] at h2
 have:j=i\/j=i+1:=of_decide_eq_true h2.symm
 O
private lemma z6 {m c:ℕ} {S:Finset ℕ} (a:1<=c) (b:c+1< 2*m) :
  ph m S≠pP m c:=by
 intro h;have h1:=cf h (e1 (c-1));rw[pz,(pu a b W).2 (il W)] at h1;cases h1
private lemma qJ {m i k:ℕ} {S:Finset ℕ} (hk:k< 2*m) :
  ph m S≠qd m i k:=by
 intro h;have h1:=cf h (e1 k);rw[pz,(pN hk hk).2 rfl] at h1;cases h1
private lemma qj {m c i k:ℕ} (b:1<=c) (a:c+1< 2*m) (hk:k< 2*m) :
  pP m c≠qd m i k:=by
 intro h;have h1:=cf h (e1 (c-1));have h2:=cf h (e1 (c+1));rw[(pu b a W).2 (il W)] at h1;rw[(pu b a a).2 (ir rfl)] at h2;have d:=(pN hk W).1 h1.symm;have e:=(pN hk a).1 h2.symm;O
private lemma zg {m c1 c2:ℕ} (b:1<=c1) (a:c1+1< 2*m)
  (c:1<=c2) (d:c2+1< 2*m) (e:pP m c1=pP m c2):c1=c2:=by
 have ha:=cf e (e1 (c1-1));have hb:=cf e (e1 (c1+1));rw[(pu b a W).2 (il W)] at ha;rw[(pu b a a).2 (ir rfl)] at hb;have f:=(pu c d W).1 ha.symm;have g:=(pu c d a).1 hb.symm;O
private lemma kG {m i1 k1 i2 k2:ℕ} (c:i1+1< 2*m) (a:k1< 2*m)
  (g:k1=i1+2\/k1+1=i1) (e:i2+1< 2*m) (f:k2< 2*m)
  (d:qd m i1 k1=qd m i2 k2):i1=i2/\k1=k2:=by
 have b:k1=k2:=by
  have h:=cf d (e1 k1);rw[(pN a a).2 rfl] at h;X (pN f a).1 h.symm
 subst b;have h2:=cf d (pe i1);rw[(qo c a c).2 (il rfl)] at h2;have h3:=(qo e a c).1 h2.symm;X ⟨by O,rfl⟩
private def qq {m:ℕ} (x:Fin (2*m+2)->Bool):Fin (2*m)->Bool :=
 fun j=>x ⟨j.val,by have:=j.isLt;O⟩
private def pf {m:ℕ} (x:Fin (2*m+2)->Bool):Fin (2*m+1)->Bool :=
 fun j=>x ⟨j.val,by have:=j.isLt;O⟩
private lemma js {m:ℕ} {S:Finset ℕ} (hS:∀i∈S,i+1< 2*m)
  (x:Fin (2*m+2)->Bool) :
  ph m S (qq x)=ph (m+1) S x:=by
 apply Bool.eq_iff_iff.2;simp only[po]
 constructor
 ·rintro ⟨i,j,a,b,c,d⟩
  X ⟨⟨i.val,by O⟩,⟨j.val,by O⟩,a,b,c,d⟩
 ·rintro ⟨i,j,a,b,c,d⟩
  have e:=hS i.val a;X ⟨⟨i.val,by O⟩,⟨j.val,by O⟩,a,b,c,d⟩
private lemma kD {m c:ℕ} (a:1<=c) (b:c+1< 2*m)
  (x:Fin (2*m+2)->Bool) :
  pP m c (qq x)=pP (m+1) c x:=by
 rw[qe a b,qe a W];R
private lemma kF {m i k:ℕ} (hi:i+1< 2*m) (hk:k< 2*m)
  (x:Fin (2*m+2)->Bool) :
  qd m i k (qq x)=qd (m+1) i k x:=by
 rw[qh hi hk,qh W W];R
private lemma j6 {m c:ℕ} (a:c%2=1) (d:c< 2*m)
  (x:Fin (2*m+2)->Bool) :
  pD m c (pf x)=pP (m+1) c x:=by
 apply Bool.eq_iff_iff.2;simp only[pG,j9]
 constructor
 ·rintro ⟨k,hk,b⟩;X ⟨⟨k.val,by O⟩,hk,b⟩
 ·rintro ⟨k,hk,b⟩;X ⟨⟨k.val,by O⟩,hk,b⟩
private lemma zH {m:ℕ} {P:Finset ℕ} (hP:∀c∈P,c%2=1/\c< 2*m)
  (x:Fin (2*m+2)->Bool) :
  qa m P (pf x)=ph (m+1) (P.biUnion fun c=>{c-1,c}) x:=by
 apply Bool.eq_iff_iff.2
 simp only[qp,po,Finset.mem_biUnion,Finset.mem_insert,
  Finset.mem_singleton]
 constructor
 ·rintro ⟨c,a,f,g,h⟩
  have b:=(hP c a).1;have d:=(hP c a).2;rw[pG] at h;obtain ⟨k,hk,l⟩:=h;rcases hk with h1|h2
  ·X ⟨⟨k.val,by O⟩,⟨c,by O⟩,⟨c,a,il (by dsimp;O)⟩,h1,l,g⟩
  ·X ⟨⟨c,by O⟩,⟨k.val,by O⟩,⟨c,a,ir rfl⟩,h2.symm,g,l⟩
 ·rintro ⟨i,j,⟨c,a,n|n⟩,hij,p,q⟩
  ·have b:=(hP c a).1;have d:=(hP c a).2
   have r:j=⟨c,by O⟩:=Fin.ext (by dsimp;O)
   Y ⟨c,a,by O,r▸q,?_⟩
   rw[pG];X ⟨⟨i.val,by O⟩,il (by dsimp;O),p⟩
  ·have b:=(hP c a).1;have d:=(hP c a).2
   have e:i=⟨c,by O⟩:=Fin.ext n
   Y ⟨c,a,by O,e▸p,?_⟩
   rw[pG];X ⟨⟨j.val,by O⟩,ir (by dsimp;O),q⟩
private lemma qE {m:ℕ} {C:J} (b:qf m C)
  (w:ℕ) (hw:w< 2*m+C.size) :
  (∃(j:ℕ) (hj:j< 2*m),w=j/\(fun x:Fin (2*m)->Bool=>p0 C x w)=fun x=>x ⟨j,hj⟩) \/
  (∃(t:ℕ) (_:t< C.size),w=2*m+t/\q1 m (fun x=>p0 C x w)) \/
  (∃(t:ℕ) (_:t< C.size),w=2*m+t/\zM m (fun x=>p0 C x w)) \/
  (∃(t:ℕ) (_:t< C.size),w=2*m+t/\qb m (fun x=>p0 C x w)):=by
 by_cases c:w< 2*m
 ·left;X ⟨w,c,rfl,funext fun x=>p7 C x w c⟩
 ·right
  set t:=w-2*m;have ht:t< C.size :=W;have a:w=2*m+t :=W;rcases b.2 t ht with h1|h2|h3
  ·left;X ⟨t,ht,a,by rw[a];X h1⟩
  ·right;left;X ⟨t,ht,a,by rw[a];X h2⟩
  ·right;right;X ⟨t,ht,a,by rw[a];X h3⟩
private lemma kn {m:ℕ} {S:Finset ℕ} (HC:S.Nonempty) (hS:∀i∈S,i+1< 2*m)
  {f1 f2:(Fin (2*m)->Bool)->Bool} (hR:f1≠f2)
  (f:∀x,ph m S x=(f1 x&&f2 x))
  (h1:(∃(j:ℕ) (hj:j< 2*m),f1=fun x=>x ⟨j,hj⟩)\/zM m f1\/qb m f1)
  (h2:(∃(j:ℕ) (hj:j< 2*m),f2=fun x=>x ⟨j,hj⟩)\/zM m f2\/qb m f2) :
  (∃e,e+1< 2*m/\ph m S=ph m {e} /\
   ((∃H9 Ha,f1=(fun x=>x ⟨e,H9⟩)/\f2=(fun x=>x ⟨e+1,Ha⟩)) \/
    (∃H9 Ha,f1=(fun x=>x ⟨e+1,H9⟩)/\f2=(fun x=>x ⟨e,Ha⟩)))) \/
  (∃c,1<=c/\c+1< 2*m/\ph m S=ph m {c-1,c} /\
   ((∃Hb,f1=(fun x=>x ⟨c,Hb⟩)/\f2=pP m c) \/
    (∃Hb,f2=(fun x=>x ⟨c,Hb⟩)/\f1=pP m c))) \/
  (∃i,i%2=0/\i+2< 2*m/\ph m S=ph m {i,i+1} /\
   ((∃hW,f1=(fun x=>x ⟨i+1,hW⟩)/\f2=qd m i (i+2)) \/
    (∃hW,f2=(fun x=>x ⟨i+1,hW⟩)/\f1=qd m i (i+2)))) \/
  (∃i,i%2=0/\1<=i/\i+1< 2*m/\ph m S=ph m {i-1,i} /\
   ((∃hW,f1=(fun x=>x ⟨i,hW⟩)/\f2=qd m i (i-1)) \/
    (∃hW,f2=(fun x=>x ⟨i,hW⟩)/\f1=qd m i (i-1)))) \/
  (∃i,i%2=0/\i+3< 2*m/\ph m S=ph m {i,i+1,i+2} /\
   ((f1=pP m (i+2)/\f2=qd m i (i+2)) \/
    (f2=pP m (i+2)/\f1=qd m i (i+2)) \/
    (f1=pP m (i+1)/\f2=qd m (i+2) (i+1)) \/
    (f2=pP m (i+1)/\f1=qd m (i+2) (i+1)) \/
    (f1=qd m i (i+2)/\f2=qd m (i+2) (i+1)) \/
    (f2=qd m i (i+2)/\f1=qd m (i+2) (i+1)))):=by
 have g:∀x,f1 x=true->f2 x=true->pq (2*m) x=true:=fun x HD HE=>
  pT (by rw[f x,HD,HE];rfl)
 have q:∀(j:ℕ) (hj:j< 2*m) (c:ℕ) (hG:1<=c) (s:c+1< 2*m),
   (∀x,ph m S x=(x ⟨j,hj⟩&&pP m c x)) ->
   j=c/\ph m S=ph m {c-1,c}:=by
  intro j hj c hG s l
  have Hc:j≠c-1:=fun h=>by
   have hv:=l (e1 (c-1));rw[pz,(pu hG s W).2 (il W)] at hv;simp[e1,h] at hv
  have Hd:j≠c+1:=fun h=>by
   have hv:=l (e1 (c+1));rw[pz,(pu hG s s).2 (ir rfl)] at hv;simp[e1,h] at hv
  have Hp:pq (2*m) (e2 j (c-1))=true:=pT (by
   rw[l,qe hG s];simp[e2])
  have Hq:pq (2*m) (e2 j (c+1))=true:=pT (by
   rw[l,qe hG s];simp[e2])
  rw[px] at Hp Hq;obtain ⟨u1,v1,He,Hf,Hg⟩:=Hp;obtain ⟨u2,v2,Hh,Hi,Hj⟩:=Hq;simp only[e2,decide_eq_true_eq] at Hf Hg Hi Hj;have HF:j=c :=W;subst HF;Y ⟨rfl,funext fun x=>?_⟩
  rw[l x,qe hG s,zu,
   pv W,pv s]
  have hX:(⟨j-1+1,by O⟩:Fin (2*m))=⟨j,hj⟩:=Fin.ext (by dsimp;O)
  rw[hX];cases x ⟨j,hj⟩<;>cases x ⟨j-1,by O⟩<;>cases x ⟨j+1,s⟩<;>rfl
 have hE:∀(j:ℕ) (hj:j< 2*m) (i k:ℕ) (Hk:i%2=0) (hi:i+1< 2*m)
   (hk:k< 2*m) (hI:k=i+2\/k+1=i),
   (∀x,ph m S x=(x ⟨j,hj⟩&&qd m i k x)) ->
   (k=i+2/\j=i+1/\ph m S=ph m {i,i+1}) \/
   (k+1=i/\j=i/\ph m S=ph m {i-1,i}):=by
  intro j hj i k Hk hi hk hI l
  have HN:j≠k:=fun h=>by
   have hv:=l (e1 k);rw[pz,(pN hk hk).2 rfl] at hv;simp[e1,h] at hv
  have hp:pq (2*m) (e2 j k)=true:=pT (by
   rw[l,qh hi hk];simp[e2])
  rw[px] at hp;obtain ⟨u,v,H7,hu,hv⟩:=hp;simp only[e2,decide_eq_true_eq] at hu hv;have hA:j+1=k\/k+1=j :=W;rcases hI with rfl|hY
  ·rcases hA with h1|h2
   ·have hJ:j=i+1 :=W
    subst hJ;left;Y ⟨rfl,rfl,funext fun x=>?_⟩
    rw[l x,qh hi hk,zu,
     pv hi,pv hk]
    cases x ⟨i,by O⟩<;>cases x ⟨i+1,hi⟩<;>cases x ⟨i+2,hk⟩<;>rfl
   ·exfalso
    have z:∀e∈S,e=i+2:=by
     intro e hH;have hv:=l (pe e);rw[(pg hS (hS e hH)).2 hH,Bool.true_eq,Bool.and_eq_true] at hv;simp only[pe,e2,decide_eq_true_eq] at hv
     have:=(qo hi hk (hS e hH)).1 hv.2
     O
    have hT:=l (e3 i (i+1) (i+3))
    have hK:((e3 i (i+1) (i+3):Fin (2*m)->Bool) ⟨j,hj⟩ &&
      qd m i (i+2) (e3 i (i+1) (i+3)))=true:=by
     rw[qh hi hk];simp[e3,show j=i+3 by O]
    rw[hK,po] at hT;obtain ⟨a,b,H3,Hr,H8,Hl⟩:=hT;have hU:=z a.val H3;simp only[e3,decide_eq_true_eq] at H8;O
  ·rcases hA with h1|h2
   ·exfalso
    have z:∀e∈S,e=j:=by
     intro e hH;have hv:=l (pe e);rw[(pg hS (hS e hH)).2 hH,Bool.true_eq,Bool.and_eq_true] at hv;simp only[pe,e2,decide_eq_true_eq] at hv
     have:=(qo hi hk (hS e hH)).1 hv.2
     O
    have hT:=l (e3 j i (i+1))
    have hK:((e3 j i (i+1):Fin (2*m)->Bool) ⟨j,hj⟩ &&
      qd m i k (e3 j i (i+1)))=true:=by
     rw[qh hi hk];simp[e3]
    rw[hK,po] at hT;obtain ⟨a,b,H3,Hr,H8,Hl⟩:=hT;have hU:=z a.val H3;simp only[e3,decide_eq_true_eq] at Hl;O
   ·have hJ:j=i :=W
    subst hJ;right;Y ⟨hY,rfl,funext fun x=>?_⟩
    rw[l x,qh hi hk,zu,
     pv W,pv hi]
    have hX:(⟨j-1+1,by O⟩:Fin (2*m))=⟨j,hj⟩:=Fin.ext (by dsimp;O)
    have H4:(⟨k,hk⟩:Fin (2*m))=⟨j-1,by O⟩:=Fin.ext (by dsimp;O)
    rw[hX,H4];cases x ⟨j-1,by O⟩<;>cases x ⟨j,hj⟩<;>cases x ⟨j+1,hi⟩<;>rfl
 have r:∀(c:ℕ) (hG:1<=c) (s:c+1< 2*m) (i k:ℕ) (Hk:i%2=0)
   (hi:i+1< 2*m) (hk:k< 2*m) (hI:k=i+2\/k+1=i),
   (∀x,ph m S x=(pP m c x&&qd m i k x)) ->
   c=k /\
   ((k=i+2/\i+3< 2*m/\ph m S=ph m {i,i+1,i+2}) \/
    (k+1=i/\2<=i/\ph m S=ph m {i-2,i-1,i})):=by
  intro c hG s i k Hk hi hk hI l
  have HO:k+1≠c/\k≠c+1:=by
   have hv:=l (e1 k);rw[pz,(pN hk hk).2 rfl,Bool.and_true] at hv
   constructor<;>intro h<;>X Bool.false_ne_true (hv.trans ((pu hG s hk).2 W))
  have Hs:pq (2*m) (e2 (c-1) k)=true:=pT (by
   rw[l,qe hG s,qh hi hk];simp[e2])
  have Ht:pq (2*m) (e2 (c+1) k)=true:=pT (by
   rw[l,qe hG s,qh hi hk];simp[e2])
  rw[px] at Hs Ht;obtain ⟨u1,v1,He,Hf,Hg⟩:=Hs;obtain ⟨u2,v2,Hh,Hi,Hj⟩:=Ht;simp only[e2,decide_eq_true_eq] at Hf Hg Hi Hj;have HG:c=k :=W;subst HG;Y ⟨rfl,?_⟩;rcases hI with rfl|hY
  ·left;Y ⟨rfl,by O,funext fun x=>?_⟩
   rw[l x,qe hG s,qh hi hk,jb,
    pv hi,pv hk,pv s]
   have hs:(⟨i+2-1,by O⟩:Fin (2*m))=⟨i+1,hi⟩:=Fin.ext rfl
   rw[hs];cases x ⟨i,by O⟩<;>cases x ⟨i+1,hi⟩<;>cases x ⟨i+2,hk⟩<;>cases x ⟨i+3,s⟩<;>rfl
  ·right;Y ⟨hY,by O,funext fun x=>?_⟩
   rw[l x,qe hG s,qh hi hk,jb,
    pv W,pv W,pv hi]
   have HH:(⟨i-2+1,by O⟩:Fin (2*m))=⟨c,hk⟩:=Fin.ext (by dsimp;O)
   have HI:(⟨i-1,by O⟩:Fin (2*m))=⟨c,hk⟩:=Fin.ext (by dsimp;O)
   have HJ:(⟨i-1+1,by O⟩:Fin (2*m))=⟨i,by O⟩:=Fin.ext (by dsimp;O)
   have HK:(⟨c-1,by O⟩:Fin (2*m))=⟨i-2,by O⟩:=Fin.ext (by dsimp;O)
   have HL:(⟨c+1,s⟩:Fin (2*m))=⟨i,by O⟩:=Fin.ext (by dsimp;O)
   rw[HH,HI,HJ,HK,HL];cases x ⟨i-2,by O⟩<;>cases x ⟨c,hk⟩<;>cases x ⟨i,by O⟩<;>cases x ⟨i+1,hi⟩<;>rfl
 rcases h1 with ⟨j1,hO,rfl⟩|⟨c1,hB,t,rfl⟩|⟨i1,k1,w,hV,hP,Hm,rfl⟩
 ·rcases h2 with ⟨j2,hL,rfl⟩|⟨c2,y,n,rfl⟩|⟨i2,k2,p,hN,hQ,H5,rfl⟩
  ·
   have HM:j1≠j2:=fun h=>hR (by subst h;rfl)
   have hp:=g (e2 j1 j2) (by simp[e2]) (by simp[e2])
   rw[px] at hp;obtain ⟨u,v,H7,hu,hv⟩:=hp;simp only[e2,decide_eq_true_eq] at hu hv;have hA:j1+1=j2\/j2+1=j1 :=W;left;rcases hA with rfl|rfl
   ·Y ⟨j1,hL,funext fun x=>by rw[f x,pv hL],il ⟨hO,hL,rfl,rfl⟩⟩
   ·Y ⟨j2,hO,funext fun x=>by rw[f x,pv hO,Bool.and_comm],
     ir ⟨hO,hL,rfl,rfl⟩⟩
  ·
   obtain ⟨rfl,d⟩:=q j1 hO c2 y n f;right;left;X ⟨j1,y,n,d,il ⟨hO,rfl,rfl⟩⟩
  ·
   rcases hE j1 hO i2 k2 p hN hQ H5 f with ⟨rfl,rfl,d⟩|⟨hY,rfl,d⟩
   ·right;right;left;X ⟨i2,p,hQ,d,il ⟨hO,rfl,rfl⟩⟩
   ·right;right;right;left
    have hM:k2=j1-1 :=W;X ⟨j1,p,by O,hN,d,il ⟨hO,rfl,by rw[hM]⟩⟩
 ·rcases h2 with ⟨j2,hL,rfl⟩|⟨c2,y,n,rfl⟩|⟨i2,k2,p,hN,hQ,H5,rfl⟩
  ·
   obtain ⟨rfl,d⟩:=q j2 hL c1 hB t (fun x=>by rw[f x,Bool.and_comm])
   right;left;X ⟨j2,hB,t,d,ir ⟨hL,rfl,rfl⟩⟩
  ·
   exfalso;have HM:c1≠c2:=fun h=>hR (by subst h;rfl)
   by_cases H6:c1+2=c2\/c2+2=c1
   ·rcases H6 with h|h
    ·have hv:=f (e1 (c1+1))
     rw[pz,(pu hB t t).2 (ir rfl),
      (pu y n t).2 (il W)] at hv;cases hv
    ·have hv:=f (e1 (c2+1))
     rw[pz,(pu hB t n).2 (il W),
      (pu y n n).2 (ir rfl)] at hv;cases hv
   ·by_cases HP:c1< c2
    ·have hp:=g (e2 (c1-1) (c2+1))
      (by rw[qe hB t];simp[e2]) (by rw[qe y n];simp[e2])
     rw[px] at hp;obtain ⟨u,v,H7,hu,hv⟩:=hp;simp only[e2,decide_eq_true_eq] at hu hv;O
    ·have hp:=g (e2 (c2-1) (c1+1))
      (by rw[qe hB t];simp[e2]) (by rw[qe y n];simp[e2])
     rw[px] at hp;obtain ⟨u,v,H7,hu,hv⟩:=hp;simp only[e2,decide_eq_true_eq] at hu hv;O
  ·
   obtain ⟨rfl,hC⟩:=r c1 hB t i2 k2 p hN hQ H5 f;right;right;right;right;rcases hC with ⟨rfl,hD,d⟩|⟨hY,Hu,d⟩
   ·X ⟨i2,p,hD,d,il ⟨rfl,rfl⟩⟩
   ·Y ⟨i2-2,by O,by O,?_,ir (ir (il ⟨?_,?_⟩))⟩
    ·have:({i2-2,i2-2+1,i2-2+2}:Finset ℕ)={i2-2,i2-1,i2}:=by
      ext e;simp;O
     rw[this];X d
    ·congr 1;O
    ·rw[show i2-2+2=i2 by O,show i2-2+1=c1 by O]
 ·rcases h2 with ⟨j2,hL,rfl⟩|⟨c2,y,n,rfl⟩|⟨i2,k2,p,hN,hQ,H5,rfl⟩
  ·
   rcases hE j2 hL i1 k1 w hV hP Hm (fun x=>by rw[f x,Bool.and_comm]) with
    ⟨rfl,rfl,d⟩|⟨hY,rfl,d⟩
   ·right;right;left;X ⟨i1,w,hP,d,ir ⟨hL,rfl,rfl⟩⟩
   ·right;right;right;left
    have hM:k1=j2-1 :=W;X ⟨j2,w,by O,hV,d,ir ⟨hL,rfl,by rw[hM]⟩⟩
  ·
   obtain ⟨rfl,hC⟩:=r c2 y n i1 k1 w hV hP Hm (fun x=>by rw[f x,Bool.and_comm])
   right;right;right;right;rcases hC with ⟨rfl,hD,d⟩|⟨hY,Hv,d⟩
   ·X ⟨i1,w,hD,d,ir (il ⟨rfl,rfl⟩)⟩
   ·Y ⟨i1-2,by O,by O,?_,ir (ir (ir (il ⟨?_,?_⟩)))⟩
    ·have:({i1-2,i1-2+1,i1-2+2}:Finset ℕ)={i1-2,i1-1,i1}:=by
      ext e;simp;O
     rw[this];X d
    ·congr 1;O
    ·rw[show i1-2+2=i1 by O,show i1-2+1=c2 by O]
  ·
   have Hw:k1≠k2:=fun h=>by
    have hv:=f (e1 k1);rw[pz,(pN hP hP).2 rfl,
     (pN hQ hP).2 h] at hv;cases hv
   have hp:=g (e2 k1 k2)
    (by rw[qh hV hP];simp[e2]) (by rw[qh hN hQ];simp[e2])
   rw[px] at hp;obtain ⟨u,v,H7,hu,hv⟩:=hp;simp only[e2,decide_eq_true_eq] at hu hv;have hA:k1+1=k2\/k2+1=k1 :=W
   have hF:∀(ia ka ib kb:ℕ),ia%2=0->ib%2=0 ->
     ia+1< 2*m->ka< 2*m->ib+1< 2*m->kb< 2*m ->
     ka=ia+2->kb+1=ib->ka+1=kb ->
     (∀x,ph m S x=(qd m ia ka x&&qd m ib kb x))->False:=by
    intro ia ka ib kb _ _ Hx Hy Hz HA Hn Ho HB l
    have z:∀e∈S,e=ka:=by
     intro e hH;have hv:=l (pe e);rw[(pg hS (hS e hH)).2 hH,Bool.true_eq,Bool.and_eq_true] at hv;have ha:=(qo Hx Hy (hS e hH)).1 hv.1;have hb:=(qo Hz HA (hS e hH)).1 hv.2;O
    have hT:=l (e3 ia (ia+1) kb)
    have hK:(qd m ia ka (e3 ia (ia+1) kb)&&qd m ib kb (e3 ia (ia+1) kb))=true:=by
     rw[qh Hx Hy,qh Hz HA];simp[e3]
    rw[hK,po] at hT;obtain ⟨a,b,H3,Hr,H8,Hl⟩:=hT;have hU:=z a.val H3;simp only[e3,decide_eq_true_eq] at H8;O
   have hh:∀(i:ℕ),i%2=0->i+3< 2*m ->
     ∀x,(qd m i (i+2) x&&qd m (i+2) (i+1) x)=ph m {i,i+1,i+2} x:=by
    intro i _ hD x;rw[qh W W,qh hD W]
    have h3:ph m {i,i+1,i+2} x =
      ((ph m {i} x||ph m {i+1} x)||ph m {i+2} x):=by
     rw[qZ,qZ];congr 1;ext e;simp[or_assoc]
    rw[h3,pv W,pv W,pv hD]
    cases x ⟨i,by O⟩<;>cases x ⟨i+1,by O⟩ <;>
     cases x ⟨i+2,by O⟩<;>cases x ⟨i+3,hD⟩<;>rfl
   rcases Hm with rfl|h1k<;>rcases H5 with rfl|h2k
   ·O
   ·rcases hA with h|h
    ·X absurd (hF i1 (i1+2) i2 k2 w p hV hP hN hQ rfl h2k h f) id
    ·have hZ:i2=i1+2 :=W
     have H0:k2=i1+1 :=W;subst hZ;subst H0;right;right;right;right
     X ⟨i1,w,hN,funext fun x=>(f x).trans (hh i1 w hN x),
      ir (ir (ir (ir (il ⟨rfl,rfl⟩))))⟩
   ·rcases hA with h|h
    ·have H1:i1=i2+2 :=W
     have H2:k1=i2+1 :=W;subst H1;subst H2;right;right;right;right
     X ⟨i2,p,hV,funext fun x=>(f x).trans (by rw[Bool.and_comm];X hh i2 p hV x),
      ir (ir (ir (ir (ir ⟨rfl,rfl⟩))))⟩
    ·X absurd (hF i2 (i2+2) i1 k1 p w hN hQ hV hP rfl h1k h
      (fun x=>by rw[f x,Bool.and_comm])) id
   ·O
private lemma qn {m:ℕ} (hm:1<=m) {C:J}
  (s:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (t:qf m C) {k:ℕ} (hk:k< C.size)
  (Ha:(C.gates[k]'hk).op=.and) :
  q1 m (p8 C k) /\
  ∃a1 a2:ℕ,(C.gates[k]'hk).inputs=[a1,a2]/\a1< 2*m+k/\a2< 2*m+k/\a1≠a2 /\
   ¬q1 m (fun x=>p0 C x a1)/\¬q1 m (fun x=>p0 C x a2) /\
   ( (∃e,e+1< 2*m/\p8 C k=ph m {e} /\
     ((a1=e/\a2=e+1)\/(a1=e+1/\a2=e))) \/
    (∃c,1<=c/\c+1< 2*m/\p8 C k=ph m {c-1,c} /\
     ((a1=c/\(fun x=>p0 C x a2)=pP m c) \/
      (a2=c/\(fun x=>p0 C x a1)=pP m c))) \/
    (∃i,i%2=0/\i+2< 2*m/\p8 C k=ph m {i,i+1} /\
     ((a1=i+1/\(fun x=>p0 C x a2)=qd m i (i+2)) \/
      (a2=i+1/\(fun x=>p0 C x a1)=qd m i (i+2)))) \/
    (∃i,i%2=0/\1<=i/\i+1< 2*m/\p8 C k=ph m {i-1,i} /\
     ((a1=i/\(fun x=>p0 C x a2)=qd m i (i-1)) \/
      (a2=i/\(fun x=>p0 C x a1)=qd m i (i-1)))) \/
    (∃i,i%2=0/\i+3< 2*m/\p8 C k=ph m {i,i+1,i+2} /\
     (((fun x=>p0 C x a1)=pP m (i+2)/\(fun x=>p0 C x a2)=qd m i (i+2)) \/
      ((fun x=>p0 C x a2)=pP m (i+2)/\(fun x=>p0 C x a1)=qd m i (i+2)) \/
      ((fun x=>p0 C x a1)=pP m (i+1)/\(fun x=>p0 C x a2)=qd m (i+2) (i+1)) \/
      ((fun x=>p0 C x a2)=pP m (i+1)/\(fun x=>p0 C x a1)=qd m (i+2) (i+1)) \/
      ((fun x=>p0 C x a1)=qd m i (i+2)/\(fun x=>p0 C x a2)=qd m (i+2) (i+1)) \/
      ((fun x=>p0 C x a2)=qd m i (i+2)/\(fun x=>p0 C x a1)=qd m (i+2) (i+1)))) ):=by
 have Hg:∃x1 x2:Fin (2*m)->Bool,cF (2*m) C x1≠cF (2*m) C x2:=by
  rw[hfun];X ps W
 rcases pc s Hg k hk with ⟨hM,_,_,_⟩|⟨_,a1,a2,hN,u,hC,hO⟩
 ·rw[Ha] at hM;cases hM
 ·have z:∀x:Fin (2*m)->Bool,p8 C k x=(p0 C x a1&&p0 C x a2) :=
   fun x=>pm x hk Ha hN u hC
  have hD:∀x:Fin (2*m)->Bool,p8 C k x=true->p0 C x a1=true:=by
   intro x hx;have h:=z x;rw[hx,eq_comm,Bool.and_eq_true] at h;X h.1
  have hP:∀x:Fin (2*m)->Bool,p8 C k x=true->p0 C x a2=true:=by
   intro x hx;have h:=z x;rw[hx,eq_comm,Bool.and_eq_true] at h;X h.2
  have v:¬zM m (p8 C k):=by
   rintro ⟨c,hJ,hE,p⟩
   have h1:=hD (e1 (c-1)) (by rw[p];X (pu hJ hE W).2 (il W))
   have h2:=hD (e1 (c+1)) (by rw[p];X (pu hJ hE hE).2 (ir rfl))
   rcases qE t a1 W with
    ⟨j,hj,_,f⟩|⟨_,_,_,S',_,_,f⟩|⟨_,_,_,c',hh,hA,f⟩|⟨_,_,_,i',k',_,_,hQ,_,f⟩
   ·have Hb:j=c-1:=of_decide_eq_true ((cf f (e1 (c-1))).symm.trans h1)
    have Hc:j=c+1:=of_decide_eq_true ((cf f (e1 (c+1))).symm.trans h2);O
   ·rw[cf f (e1 (c-1)),pz] at h1;cases h1
   ·have Hb:=(pu hh hA W).1 ((cf f (e1 (c-1))).symm.trans h1)
    have Hc:=(pu hh hA hE).1 ((cf f (e1 (c+1))).symm.trans h2);have hZ:c'=c :=W;subst hZ;obtain ⟨x,hx⟩:=py s k hk a1 u;X hx (by rw[cf p x,cf f x])
   ·have Hb:=(pN hQ W).1 ((cf f (e1 (c-1))).symm.trans h1)
    have Hc:=(pN hQ hE).1 ((cf f (e1 (c+1))).symm.trans h2);O
  have hF:¬qb m (p8 C k):=by
   rintro ⟨i,k0,hK,hi,hH,H0,p⟩
   have n:∀a (ha:a< 2*m+k),
     (∀x:Fin (2*m)->Bool,p8 C k x=true->p0 C x a=true) ->
     ∃c',1<=c'/\c'+1< 2*m/\(c'=k0-1\/c'=k0+1) /\
      (fun x=>p0 C x a)=pP m c'/\pP m c' (pe i)=true:=by
    intro a ha hY;have h1:=hY (e1 k0) (by rw[p];X (pN hH hH).2 rfl)
    have h2:=hY (pe i) (by rw[p];X (qo hi hH hi).2 (il rfl))
    rcases qE t a W with
     ⟨j,hj,_,y⟩|⟨_,_,_,S',_,_,y⟩|⟨_,_,_,c',hh,hA,y⟩|⟨_,_,_,i',k',_,hG,hQ,Ht,y⟩
    ·have Hh:j=k0:=of_decide_eq_true ((cf y (e1 k0)).symm.trans h1)
     subst Hh
     have:j=i\/j=i+1:=of_decide_eq_true ((cf y (pe i)).symm.trans h2)
     O
    ·rw[cf y (e1 k0),pz] at h1;cases h1
    ·have Hd:=(pu hh hA hH).1 ((cf y (e1 k0)).symm.trans h1)
     X ⟨c',hh,hA,by O,y,(cf y (pe i)).symm.trans h2⟩
    ·have hR:=(pN hQ hH).1 ((cf y (e1 k0)).symm.trans h1)
     subst hR;have He:=(qo hG hQ hi).1 ((cf y (pe i)).symm.trans h2)
     have:i'=i :=W
     subst this;obtain ⟨x,hx⟩:=py s k hk a ha;X False.elim (hx (by rw[cf p x,cf y x]))
   obtain ⟨c1,H1,H2,Hi,f,Hj⟩:=n a1 u hD;obtain ⟨c2,H3,H4,Hk,H5,Hl⟩:=n a2 hC hP
   have Hm:c1≠c2:=fun h=>by
    subst h;obtain ⟨x,hx⟩:=py s k hk a1 u;X hx (by rw[z x,cf f x,cf H5 x,Bool.and_self])
   have hT:∀c',1<=c'->c'+1< 2*m->pP m c' (pe i)=true ->
     c'-1=i\/c'-1=i+1\/c'+1=i\/c'+1=i+1:=by
    intro c' h1 h2 Hf;rw[qe h1 h2] at Hf;simp only[Bool.or_eq_true,pe,e2,decide_eq_true_eq] at Hf;O
   have Hu:=hT c1 H1 H2 Hj;have Hv:=hT c2 H3 H4 Hl;rcases H0 with rfl|hki<;>O
  have hB:q1 m (p8 C k):=by
   rcases t.2 k hk with h1|h2|h3
   ·X h1
   ·X absurd h2 v
   ·X absurd h3 hF
  obtain ⟨S,hU,hS,p⟩:=hB
  have g:∀w,w< 2*m+k->(∀x:Fin (2*m)->Bool,p8 C k x=true->p0 C x w=true) ->
    ¬q1 m (fun x=>p0 C x w):=by
   rintro w hw hY ⟨Q,_,_,hL⟩
   X qG s t.1 k hk w hw hY fun x Hn=>by
    rw[hfun];X pT (by rw[←cf hL x];X Hn)
  have hV:=g a1 u hD;have hW:=g a2 hC hP
  have H6:(fun x=>p0 C x a1)≠(fun x=>p0 C x a2):=fun Ho=>by
   obtain ⟨x,hx⟩:=py s k hk a1 u;X hx (by rw[z x,←cf Ho x,Bool.and_self])
  have hX:∀w (hw:w< 2*m+k),¬q1 m (fun x=>p0 C x w) ->
    (∃(j:ℕ) (hj:j< 2*m),(fun x=>p0 C x w)=fun x=>x ⟨j,hj⟩) \/
    zM m (fun x=>p0 C x w)\/qb m (fun x=>p0 C x w):=by
   intro w hw Hp;rcases qE t w W with ⟨j,hj,_,hf⟩|⟨_,_,_,hf⟩|⟨_,_,_,hf⟩|⟨_,_,_,hf⟩
   ·X il ⟨j,hj,hf⟩
   ·X absurd hf Hp
   ·X ir (il hf)
   ·X ir (ir hf)
  have b:∀w (hw:w< 2*m+k) (j:ℕ) (hj:j< 2*m),
    (fun x=>p0 C x w)=(fun x=>x ⟨j,hj⟩)->w=j:=by
   intro w hw j hj hL
   rcases qE t w W with
    ⟨j',Hw,rfl,hI⟩|⟨_,_,_,Q,_,_,hI⟩|⟨_,_,_,c,hJ,hE,hI⟩|⟨_,_,_,i,k0,_,hi,hH,hr,hI⟩
   ·have:=cf (hI.symm.trans hL) (e1 j);simp[e1] at this;X this
   ·X absurd (hI.symm.trans hL) (zv hj)
   ·X absurd (hI.symm.trans hL) (jr hJ hE hj)
   ·X absurd (hI.symm.trans hL) (zw hi hH hr hj)
  Y ⟨⟨S,hU,hS,p⟩,a1,a2,hN,u,hC,hO,hV,hW,?_⟩
  rcases kn hU hS H6 (fun x=>by rw[←cf p x,z x])
    (hX a1 u hV) (hX a2 hC hW) with
   ⟨e,he,l,d⟩|⟨c,hJ,hE,l,d⟩|⟨i,hK,Hq,l,d⟩ |
   ⟨i,hK,Hr,hi,l,d⟩|⟨i,hK,Hs,l,d⟩
  ·left;Y ⟨e,he,p.trans l,?_⟩
   rcases d with ⟨H7,H8,q,r⟩|⟨H7,H8,q,r⟩
   ·X il ⟨b a1 u e H7 q,b a2 hC (e+1) H8 r⟩
   ·X ir ⟨b a1 u (e+1) H7 q,b a2 hC e H8 r⟩
  ·right;left;Y ⟨c,hJ,hE,p.trans l,?_⟩
   rcases d with ⟨H9,q,r⟩|⟨H9,r,q⟩
   ·X il ⟨b a1 u c H9 q,r⟩
   ·X ir ⟨b a2 hC c H9 r,q⟩
  ·right;right;left;Y ⟨i,hK,Hq,p.trans l,?_⟩
   rcases d with ⟨hG,q,r⟩|⟨hG,r,q⟩
   ·X il ⟨b a1 u (i+1) hG q,r⟩
   ·X ir ⟨b a2 hC (i+1) hG r,q⟩
  ·right;right;right;left;Y ⟨i,hK,Hr,hi,p.trans l,?_⟩
   rcases d with ⟨hG,q,r⟩|⟨hG,r,q⟩
   ·X il ⟨b a1 u i hG q,r⟩
   ·X ir ⟨b a2 hC i hG r,q⟩
  ·right;right;right;right;X ⟨i,hK,Hs,p.trans l,d⟩
private lemma jA {C:J}
  (c:IsMinimalCircuit 2 C) (hfun:cF 2 C=pq 2) :
  qf 1 C:=by
 have w:C.size=1:=zr (m:=1) le_rfl c hfun;have h0:0< C.size :=W
 have q:∃x1 x2:Fin 2->Bool,cF 2 C x1≠cF 2 C x2:=by
  rw[hfun];X ps le_rfl
 have d:C.output=2:=by
  rcases pY c 0 h0 with heq|⟨t',y,_,_⟩
  ·X heq
  ·O
 have j:(C.gates[0]'h0).op=.and:=by
  rcases pc c q 0 h0 with ⟨l,a,ha,f⟩|⟨e,a1,a2,b,n,s,_⟩
  ·exfalso
   have i:cF 2 C e0=false:=by rw[hfun,zq]
   rw[pb,d,pj C e0 0 h0,l] at i
   cases b:(C.gates[0]'h0).inputs with
   | nil=>rw[b] at ha;simp at ha
   | cons a0 r=>
    rw[b] at ha i;simp at ha;subst ha
    simp only[GateOp.eval,List.map_cons,List.headD_cons,f,↓reduceIte,
     p7 C e0 a0 f] at i;simp[e0] at i
  ·rcases e with hop_and|hop_or
   ·X hop_and
   ·exfalso
    have p:cF 2 C (e1 a1)=false:=by rw[hfun,pW]
    rw[pb,d,p6 (e1 a1) h0 hop_or b n s,
     p7 C _ a1 n] at p
    simp[e1] at p
 Y ⟨?_,?_⟩
 ·intro g hg
  obtain ⟨k,hk,rfl⟩:=List.mem_iff_getElem.1 hg;have u:k=0:=by have:C.gates.length=C.size:=rfl;O
  subst u;change (C.gates[0]'h0).op≠.not;rw[j];intro h;cases h
 ·intro t ht
  have v:t=0 :=W;subst v;left;Y ⟨{0},Finset.singleton_nonempty 0,by simp,funext fun x=>?_⟩
  have h1:p8 C 0 x=pq 2 x:=by
   rw[←cf hfun x,pb,d];R
  rw[h1,jM 1 x]
  have:Finset.range (2*1-1)={0}:=by decide
  rw[this]
private lemma k9 {m:ℕ} (hm:1<=m) {C:J}
  (u:IsMinimalCircuit (2*m+2) C) (hfun:cF (2*m+2) C=pq (2*m+2))
  {f w:ℕ} (hN:f< C.size)
  (hV:∀t (ht:t< C.size),pC (2*m+2) t (2*m+1) (C.gates[t]'ht)↔t=f)
  (Hn:(C.gates[f]'hN).op=.and)
  (HB:w< 2*m+2+f) (_4:w≠2*m+1)
  (_5:(C.gates[f]'hN).inputs=[2*m+1,w]\/(C.gates[f]'hN).inputs=[w,2*m+1]) :
  qf (m+1) C:=by
 have h00:C.size=3*m+1:=by
  have:=zr (m:=m+1) W u hfun
  O
 have HQ:∃x1 x2:Fin (2*m+2)->Bool,cF (2*m+2) C x1≠cF (2*m+2) C x2:=by
  rw[hfun];X ps W
 have H7:∀y:Fin (2*m+1)->Bool,cF (2*m+2) C (Fin.snoc y false)=pq (2*m+1) y:=by
  intro y;rw[hfun,z8]
 have HR:∃y1 y2:Fin (2*m+1)->Bool,
   cF (2*m+2) C (Fin.snoc y1 false)≠cF (2*m+2) C (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,hne⟩:=ps (n:=2*m+1) W;X ⟨y1,y2,by rw[H7,H7];X hne⟩
 have _C:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m+1)->Bool,cF (2*m+1) D y=cF (2*m+2) C (Fin.snoc y false)) ->
   C.size<=D.size+2:=by
  intro D _D _9;have _E:=q9 (2*m+1) W D _D (funext fun y=>(_9 y).trans (H7 y));have _o:(2*m+1)%2≠0 :=W;have _F:(2*m+1)/2=m :=W;simp only[_o,↓reduceIte,_F] at _E;O
 have Ho:(p5 C (2*m+1) false).fc.getD (2*m+2+f) (.const false)=.const false:=by
  have _V:=(pR (n:=2*m+1) (b:=false) u.1 hN).2.1;have _6:=p9 C (2*m+1) false u.1;rcases _5 with g|g
  ·X ((_V Hn (2*m+1) w g W HB).1 (il _6)).1
  ·X ((_V Hn w (2*m+1) g HB W).1 (ir _6)).1
 obtain ⟨hW,h01,r,Hw,hgh,Hp,p,Hq,z,HS,_7,_8,hO⟩ :=
  zh (n:=2*m+1) u false false HR f hN
   ((hV f hN).2 rfl) Ho _C
 simp only[Bool.false_eq_true,↓reduceIte] at Hq;set st:=p5 C (2*m+1) false;set C':=p3 C (2*m+1) false
 have hJ:cF (2*m+1) C'=pq (2*m+1) :=
  funext fun y=>(q6 C (2*m+1) false u.1 HR y).trans (H7 y)
 have hG:zb m C':=k8 m hm C' hW hJ
 have Hr:z0 C:=qK u.1 hG.1 fun t ht _p=>by
  rcases (p t ht).1 _p with rfl|rfl
  ·rw[Hn];intro h;cases h
  ·rw[Hq];intro h;cases h
 have HT:z≠2*m+1:=fun h=>by
  have:=(hV r Hw).1 ⟨by
   rcases _8 with g|g<;>simp[pa,Hq,g,h],by O⟩
  O
 have hR:∀i,i< 2*m+2+C.size->i≠2*m+1->i≠2*m+2+f ->
   ∃i',i'< 2*m+1+C'.size/\st.fc.getD i (.const false)=.wire i':=by
  intro i hi HU _0;by_cases HO:i< 2*m+2
  ·X ⟨i,by O,pd C (2*m+1) false i W⟩
  ·set t:=i-(2*m+2)
   have ht:t< C.size :=W;have HP:t≠f :=W;by_cases H8:t=r
   ·by_cases h02:z< 2*m+2
    ·Y ⟨z,by O,?_⟩
     rw[show i=2*m+2+r by O,hO]
     X pd C (2*m+1) false z W
    ·set tz:=z-(2*m+2)
     have _W:tz< C.size :=W;have _1:=pE u.1 p _W W W;obtain ⟨kz,hkz,_,_q,_,_,_⟩:=p4 u.1 _W _1;Y ⟨2*m+1+kz,Nat.add_lt_add_left hkz _,?_⟩;rw[show i=2*m+2+r by O,hO,show z=2*m+2+tz by O]
     X _q
   ·have q:=pE u.1 p ht HP H8
    obtain ⟨kt,hC,_,hA,_,_,_⟩:=p4 u.1 ht q;X ⟨2*m+1+kt,Nat.add_lt_add_left hC _,by rw[show i=2*m+2+t by O];X hA⟩
 obtain ⟨w',_a,_2⟩:=hR w W _4 W;obtain ⟨z',_G,hM⟩:=hR z W HT _7
 have HC:∀(x:Fin (2*m+2)->Bool) i,i< 2*m+2+r ->
   i≠2*m+1->i≠2*m+2+f ->
   ∀i',st.fc.getD i (.const false)=.wire i' ->
   p0 C x i=p0 C' (pf x) i':=by
  intro x i
  induction i using Nat.strong_induction_on with
  | ind i ih=>
   intro h03 HU _0 i' hD;by_cases HO:i< 2*m+2
   ·rw[pd C (2*m+1) false i W] at hD;cases hD
    rw[p7 C x i HO,p7 C' (pf x) i W];R
   ·set t:=i-(2*m+2)
    have ht:t< C.size :=W;have hX:i=2*m+2+t :=W;rw[hX] at hD ⊢;have q:=pE u.1 p ht W W;obtain ⟨kt,hC,_,hA,hB,hint,_⟩:=p4 u.1 ht q;rw[hD] at hA;injection hA with hi'eq;subst hi'eq;rcases pc u HQ t ht with ⟨H9,_,_,_⟩|⟨l,a1,a2,g,v,hh,_⟩
    ·X absurd H9 (Hr _ (List.getElem_mem ht))
    ·have k:∀a,(a=a1\/a=a2)->a< 2*m+2+t->a≠2*m+1/\a≠2*m+2+f:=by
      intro a Hm hK
      have _b:pC (2*m+2) t a (C.gates[t]'ht):=by
       rcases l with h|h<;>X ⟨by simp[pa,h,g,Hm],hK⟩
      X ⟨fun h=>by have:=(hV t ht).1 (h▸_b);O,
       fun h=>by have:=(Hp t ht).1 (h▸_b);O⟩
     rcases l with d|d
     ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .and a1 a2 (il rfl) d g v hh
      rw[pm x ht d g v hh,
       pm (pf x) hC (hB.trans d) s hY hZ,
       ih a1 W W (k a1 (il rfl) v).1 (k a1 (il rfl) v).2 w1 Hg,
       ih a2 W W (k a2 (ir rfl) hh).1 (k a2 (ir rfl) hh).2 w2 Hh]
     ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .or a1 a2 (ir rfl) d g v hh
      rw[p6 x ht d g v hh,
       p6 (pf x) hC (hB.trans d) s hY hZ,
       ih a1 W W (k a1 (il rfl) v).1 (k a1 (il rfl) v).2 w1 Hg,
       ih a2 W W (k a2 (ir rfl) hh).1 (k a2 (ir rfl) hh).2 w2 Hh]
 have HD:∀x:Fin (2*m+2)->Bool,p0 C x w=p0 C' (pf x) w' :=
  fun x=>HC x w W _4 W w' _2
 have HE:∀x:Fin (2*m+2)->Bool,p0 C x z=p0 C' (pf x) z' :=
  fun x=>HC x z HS HT _7 z' hM
 have H5:∀x:Fin (2*m+2)->Bool,p0 C x (2*m+2+f)=(x ⟨2*m+1,by O⟩&&p0 C' (pf x) w'):=by
  intro x;rcases _5 with g|g
  ·rw[pm x hN Hn g W HB,p7 C x (2*m+1) W,HD x]
  ·rw[pm x hN Hn g HB W,p7 C x (2*m+1) W,HD x,Bool.and_comm]
 have H6:∀x:Fin (2*m+2)->Bool,p0 C x (2*m+2+r)=(p0 C x (2*m+2+f)||p0 C' (pf x) z'):=by
  intro x;rcases _8 with g|g
  ·rw[p6 x Hw Hq g W HS,HE x]
  ·rw[p6 x Hw Hq g HS W,HE x,Bool.or_comm]
 have Hi:∀x:Fin (2*m+2)->Bool,p0 C x (2*m+2+f)=false ->
   ∀i,i< 2*m+2+C.size->i≠2*m+1 ->
   p0 C x i=p0 C (Fin.snoc (pf x) false) i:=by
  intro x _H i
  induction i using Nat.strong_induction_on with
  | ind i ih=>
   intro hi HU;by_cases HO:i< 2*m+2
   ·rw[p7 C x i HO,p7 C _ i HO]
    have:(⟨i,HO⟩:Fin (2*m+2))=Fin.castSucc ⟨i,by O⟩:=Fin.ext rfl
    rw[this,Fin.snoc_castSucc];R
   ·set t:=i-(2*m+2)
    have ht:t< C.size :=W;have hX:i=2*m+2+t :=W;rw[hX];by_cases HP:t=f
    ·rw[HP,_H,H5]
     have:(Fin.snoc (pf x) false:Fin (2*m+2)->Bool) ⟨2*m+1,by O⟩=false:=by
      have:(⟨2*m+1,by O⟩:Fin (2*m+2))=Fin.last (2*m+1):=Fin.ext rfl
      rw[this,Fin.snoc_last]
     rw[this];R
    ·rcases pc u HQ t ht with ⟨H9,_,_,_⟩|⟨l,a1,a2,g,v,hh,_⟩
     ·X absurd H9 (Hr _ (List.getElem_mem ht))
     ·have Hj:∀a,(a=a1\/a=a2)->a< 2*m+2+t->a≠2*m+1:=by
       intro a Hm hK h
       have _b:pC (2*m+2) t a (C.gates[t]'ht):=by
        rcases l with _r|_r<;>X ⟨by simp[pa,_r,g,Hm],hK⟩
       X HP ((hV t ht).1 (h▸_b))
      rcases l with d|d
      ·rw[pm x ht d g v hh,pm _ ht d g v hh,
        ih a1 W W (Hj a1 (il rfl) v),
        ih a2 W W (Hj a2 (ir rfl) hh)]
      ·rw[p6 x ht d g v hh,p6 _ ht d g v hh,
        ih a1 W W (Hj a1 (il rfl) v),
        ih a2 W W (Hj a2 (ir rfl) hh)]
 have H0:C.output≠2*m+1:=fun h=>
  pL u.1 HR (p9 C (2*m+1) false u.1) h
 have Ha:C.output≠2*m+2+f:=fun h=>
  pL u.1 HR Ho h
 have Hb:st.fc.getD C.output (.const false)=.wire C'.output:=q8 u.1 HR
 have Hc:pX m (fun y=>p0 C' y C'.output):=by
  Y ⟨(Finset.range (2*m)).filter (fun c=>c%2=1),
   ⟨1,Finset.mem_filter.2 ⟨Finset.mem_range.2 W,rfl⟩⟩,
   fun c hc=>by simp only[Finset.mem_filter,Finset.mem_range] at hc;X ⟨hc.2,hc.1⟩,
   funext fun y=>?_⟩
  change cF (2*m+1) C' y=_;rw[hJ,zY]
 have _s:∃y1 y2:Fin (2*m+1)->Bool,cF (2*m+1) C' y1≠cF (2*m+1) C' y2:=by
  rw[hJ];X ps W
 have hE:pf (pe (2*m):Fin (2*m+2)->Bool)=(e1 (2*m):Fin (2*m+1)->Bool):=by
  funext j;simp only[pf,pe,e2,e1];apply Bool.eq_iff_iff.2;have:=j.isLt;simp;O
 have HV:pf (e2 (2*m-2) (2*m+1):Fin (2*m+2)->Bool) =
   (e1 (2*m-2):Fin (2*m+1)->Bool):=by
  funext j;simp only[pf,e2,e1];apply Bool.eq_iff_iff.2;have:=j.isLt;simp;O
 have Hk:p0 C' (e1 (2*m):Fin (2*m+1)->Bool) w'=true:=by
  cases hv:p0 C' (e1 (2*m):Fin (2*m+1)->Bool) w' with
  | true=>rfl
  | false=>
   exfalso
   have _H:p0 C (pe (2*m):Fin (2*m+2)->Bool) (2*m+2+f)=false:=by
    rw[H5,hE,hv,Bool.and_false]
   have h1:=Hi (pe (2*m)) _H C.output (pB HQ) H0;change cF (2*m+2) C (pe (2*m))=cF (2*m+2) C (Fin.snoc _ false) at h1;rw[H7,hE,pW,hfun,q0 W] at h1;cases h1
 have _3:(fun y:Fin (2*m+1)->Bool=>p0 C' y w')=(fun y=>y ⟨2*m,by O⟩) \/
   (fun y:Fin (2*m+1)->Bool=>p0 C' y w')=pD m (2*m-1):=by
  rcases qH hG w' _a with ⟨j,hj,_,_c⟩|⟨_,_,_,c,He,Hd,_c⟩|⟨_,_,_,P,_,_,_c⟩
  ·left;have _t:j=2*m:=of_decide_eq_true ((cf _c (e1 (2*m))).symm.trans Hk)
   subst _t;X _c
  ·right;have _X:=(pt W Hd W).1 ((cf _c (e1 (2*m))).symm.trans Hk)
   have:c=2*m-1 :=W
   subst this;X _c
  ·rw[cf _c (e1 (2*m)),q2] at Hk;cases Hk
 have hL:∀(kt:ℕ) (hC:kt< C'.size) (a1 a2:ℕ),
   (C'.gates[kt]'hC).op=.or->(C'.gates[kt]'hC).inputs=[a1,a2] ->
   a1< 2*m+1+kt->a2< 2*m+1+kt->pX m (p8 C' kt) ->
   pX m (fun y=>p0 C' y a1)/\pX m (fun y=>p0 C' y a2):=by
  intro kt hC a1 a2 _r g v hh ⟨P,_,_,Hs⟩
  have Ht:∀a (ha:a< 2*m+1+kt),
    (∀y,p0 C' y a=true->qa m P y=true)->pX m (fun y=>p0 C' y a):=by
   intro a ha _Y;rcases qH hG a W with ⟨j,hj,_,_d⟩|⟨_,_,_,c,He,Hd,_d⟩|⟨_,_,_,hu⟩
   ·have h1:=_Y (e1 j) (by rw[cf _d (e1 j)];simp[e1]);rw[q2] at h1;cases h1
   ·have h1:=_Y (e1 (c-1)) (by rw[cf _d (e1 (c-1))];X (pt W Hd W).2 (il W))
    rw[q2] at h1;cases h1
   ·X hu
  X ⟨Ht a1 v fun y hy=>by
    rw[←cf Hs y];change p0 C' y (2*m+1+kt)=true;rw[p6 y hC _r g v hh,hy];rfl,
   Ht a2 hh fun y hy=>by
    rw[←cf Hs y];change p0 C' y (2*m+1+kt)=true;rw[p6 y hC _r g v hh,hy,Bool.or_true]⟩
 have hH:∀(kt:ℕ) (hC:kt< C'.size) (c:ℕ) (He:c%2=1) (Hd:c< 2*m),
   p8 C' kt=pD m c->∀a,pC (2*m+1) kt a (C'.gates[kt]'hC) ->
   ¬pX m (fun y=>p0 C' y a)/\¬(a< 2*m+1/\a%2=1):=by
  intro kt hC c He Hd Hs a _I
  constructor
  ·intro H2
   rcases qH hG a (by have:=_I.2;O) with
    ⟨j,hj,_,_d⟩|⟨_,_,_,c',_J,_K,_d⟩|⟨ka,hka,_u,_⟩
   ·obtain ⟨P,_,_,hP⟩:=H2;X qt hj (hP.symm.trans _d)
   ·obtain ⟨P,_,_,hP⟩:=H2;X q3 _J _K (_d.symm.trans hP)
   ·have _L:pX m (p8 C' ka):=by rw[_u] at H2;X H2
    obtain ⟨_,⟨P,_,_,hP⟩,_⟩:=zf hm hW hJ hG hka hC _L (_u▸_I);X q3 He Hd (Hs.symm.trans hP)
  ·rintro ⟨hK,_Z⟩
   rcases pc hW _s kt hC with ⟨H9,_,_,_⟩|⟨l,b1,b2,g,hb1,hb2,_⟩
   ·X absurd H9 (hG.1 _ (List.getElem_mem hC))
   ·rcases l with hop_and|hop_or
    ·obtain ⟨_,_,_,_,_,_,_,_,H2,_⟩:=qO hm hW hJ hG hC hop_and
     X q3 He Hd (Hs.symm.trans H2)
    ·have hrm:=_I.1;simp only[pa,hop_or,g,List.mem_cons,List.not_mem_nil,or_false] at hrm
     have h1:p8 C' kt (e1 a:Fin (2*m+1)->Bool)=true:=by
      change p0 C' (e1 a) (2*m+1+kt)=true;rw[p6 _ hC hop_or g hb1 hb2,Bool.or_eq_true];rcases hrm with rfl|rfl<;>[left;right]<;>(rw[p7 C' _ a hK];simp[e1])
     rw[Hs] at h1;have:=(pt W Hd hK).1 h1;O
 have hT:∀(t:ℕ) (ht:t< C.size) (l:(C.gates[t]'ht).op=.and\/(C.gates[t]'ht).op=.or)
   (a1 a2:ℕ),(C.gates[t]'ht).inputs=[a1,a2]->t≠f->t≠r ->
   ∀a,(a=a1\/a=a2)->a< 2*m+2+t->a≠2*m+1/\a≠2*m+2+f:=by
  intro t ht l a1 a2 g HP H8 a Hm hK
  have _b:pC (2*m+2) t a (C.gates[t]'ht):=by
   rcases l with h|h<;>X ⟨by simp[pa,h,g,Hm],hK⟩
  X ⟨fun h=>HP ((hV t ht).1 (h▸_b)),fun h=>H8 ((Hp t ht).1 (h▸_b))⟩
 have HF:p8 C f=ph (m+1) {2*m} ->
   (q1 (m+1) (p8 C r)\/zM (m+1) (p8 C r)\/qb (m+1) (p8 C r)) ->
   (∀t (ht:t< C.size) (kt:ℕ) (hC:kt< C'.size),t≠f->t≠r ->
    st.fc.getD (2*m+2+t) (.const false)=.wire (2*m+1+kt) ->
    ((¬pX m (p8 C' kt)->∀x:Fin (2*m+2)->Bool,p8 C t x=p8 C' kt (pf x)) /\
     (pX m (p8 C' kt) ->
      (∀x:Fin (2*m+2)->Bool,p8 C t x=p8 C' kt (pf x)) \/
      (∀x:Fin (2*m+2)->Bool,p8 C t x=(ph (m+1) {2*m} x||p8 C' kt (pf x)))))) ->
   qf (m+1) C:=by
  intro hF _e HK;Y ⟨Hr,fun t ht=>?_⟩;by_cases HP:t=f
  ·subst HP;left;X ⟨{2*m},Finset.singleton_nonempty _,by simp;O,hF⟩
  ·by_cases H8:t=r
   ·subst H8;X _e
   ·have q:=pE u.1 p ht HP H8
    obtain ⟨kt,hC,_,hA,_,_,_⟩:=p4 u.1 ht q;have hp:=HK t ht kt hC HP H8 hA;rcases hG.2.1 kt hC with ⟨c,He,Hd,Hs⟩|⟨P,_v,HG,Hs⟩
    ·right;left
     Y ⟨c,by O,by O,funext fun x=>?_⟩
     have hU:¬pX m (p8 C' kt):=fun ⟨Q,_,_,hQ⟩=>
      q3 He Hd (Hs.symm.trans hQ)
     rw[hp.1 hU x,cf Hs (pf x),j6 He Hd x]
    ·left
     set S:=P.biUnion fun c=>{c-1,c}
     have _M:S.Nonempty:=by
      obtain ⟨c,hc⟩:=_v;X ⟨c,Finset.mem_biUnion.2 ⟨c,hc,Finset.mem_insert_of_mem (Finset.mem_singleton_self c)⟩⟩
     have hS:∀e∈S,e+1< 2*(m+1):=by
      intro e he;simp only[S,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton] at he;obtain ⟨c,_N,_O⟩:=he
      have:=(HG c _N).2
      rcases _O with rfl|rfl<;>O
     rcases hp.2 ⟨P,_v,HG,Hs⟩ with h1|h2
     ·X ⟨S,_M,hS,funext fun x=>by rw[h1 x,cf Hs (pf x),zH HG x]⟩
     ·Y ⟨{2*m}∪S,⟨2*m,by simp⟩,fun e he=>?_,funext fun x=>?_⟩
      ·rcases Finset.mem_union.1 he with h|h
       ·simp at h;O
       ·X hS e h
      ·rw[h2 x,cf Hs (pf x),zH HG x,qZ]
 have H3:(∀x:Fin (2*m+2)->Bool,(p0 C x (2*m+2+f)=true->pD m (2*m-1) (pf x)=true ->
    cF (2*m+2) C x=true)) ->
   p8 C f=ph (m+1) {2*m}:=by
  intro himp
  have _w:(fun y:Fin (2*m+1)->Bool=>p0 C' y w')=(fun y=>y ⟨2*m,by O⟩):=by
   rcases _3 with h1|h2
   ·X h1
   ·exfalso
    have HH:pD m (2*m-1) (pf (e2 (2*m-2) (2*m+1)))=true:=by
     rw[HV];X (pt W W W).2 (il W)
    have _x:p0 C (e2 (2*m-2) (2*m+1):Fin (2*m+2)->Bool) (2*m+2+f)=true:=by
     rw[H5,cf h2 _,HH];simp[e2]
    have h1:=himp (e2 (2*m-2) (2*m+1)) _x HH;rw[hfun,px] at h1;obtain ⟨a,b,hab,ha,hb⟩:=h1;simp only[e2,decide_eq_true_eq] at ha hb;O
  X funext fun x=>by
   change p0 C x (2*m+2+f)=_;rw[H5 x,cf _w (pf x),pv W,Bool.and_comm];R
 by_cases Hl:¬((z'< 2*m+1/\z'%2=1)\/pX m (fun y=>p0 C' y z'))
 ·exfalso
  have HL:∀i,i< 2*m+2+C.size->i≠2*m+1->i≠2*m+2+f ->
    ∀i',st.fc.getD i (.const false)=.wire i' ->
    ((i'< 2*m+1/\i'%2=1)\/pX m (fun y=>p0 C' y i')) ->
    p0 C (pe (2*m):Fin (2*m+2)->Bool) i=false:=by
   intro i
   induction i using Nat.strong_induction_on with
   | ind i ih=>
    intro hi HU _0 i' hD HW;by_cases HO:i< 2*m+2
    ·rw[pd C (2*m+1) false i W] at hD;cases hD
     rcases HW with ⟨_,_o⟩|⟨P,_,_,hP⟩
     ·rw[p7 C _ i HO];simp only[pe,e2,decide_eq_false_iff_not];O
     ·X absurd (hP.symm.trans (funext fun y=>p7 C' y i W)) (qt W)
    ·set t:=i-(2*m+2)
     have ht:t< C.size :=W;have hX:i=2*m+2+t :=W;rw[hX] at hD ⊢;by_cases H8:t=r
     ·rw[H8,hO,hM] at hD;injection hD with hi'z;subst hi'z
      X absurd HW Hl
     ·have q:=pE u.1 p ht W H8
      obtain ⟨kt,hC,_,hA,hB,hint,_⟩:=p4 u.1 ht q;rw[hD] at hA;injection hA with hi'eq;subst hi'eq
      have H2:pX m (p8 C' kt):=by
       rcases HW with ⟨hlt,_⟩|H2
       ·O
       ·X H2
      rcases pc u HQ t ht with ⟨H9,_,_,_⟩|⟨l,a1,a2,g,v,hh,_⟩
      ·X absurd H9 (Hr _ (List.getElem_mem ht))
      ·have k:=hT t ht l a1 a2 g W H8
       rcases l with d|d
       ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .and a1 a2 (il rfl) d g v hh
        obtain ⟨c,b1,b2,He,Hd,H4,_,_,_,Hf⟩ :=
         qO hm hW hJ hG hC (hB.trans d)
        rw[s] at H4;injection H4 with hw1b hrest;injection hrest with hw2b;subst hw1b;subst hw2b;rw[pm _ ht d g v hh];rcases Hf with ⟨rfl,_⟩|⟨rfl,_⟩
        ·rw[ih a1 W W (k a1 (il rfl) v).1 (k a1 (il rfl) v).2 w1 Hg (il ⟨by O,He⟩)];R
        ·rw[ih a2 W W (k a2 (ir rfl) hh).1 (k a2 (ir rfl) hh).2 w2 Hh (il ⟨by O,He⟩),Bool.and_false]
       ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .or a1 a2 (ir rfl) d g v hh
        obtain ⟨HX,HY⟩:=hL kt hC w1 w2 (hB.trans d) s hY hZ H2
        rw[p6 _ ht d g v hh,
         ih a1 W W (k a1 (il rfl) v).1 (k a1 (il rfl) v).2 w1 Hg (ir HX),
         ih a2 W W (k a2 (ir rfl) hh).1 (k a2 (ir rfl) hh).2 w2 Hh (ir HY)];R
  have _f:=HL C.output (pB HQ) H0 Ha C'.output Hb (ir Hc);change cF (2*m+2) C (pe (2*m))=false at _f;rw[hfun,q0 W] at _f;cases _f
 push Not at Hl;rcases Hl with ⟨hI,_P⟩|⟨Pz,_y,Hx,Hy⟩
 ·
  have Hy:(fun y=>p0 C' y z')=fun y=>y ⟨z',hI⟩ :=
   funext fun y=>p7 C' y z' hI
  have Hu:∀i,i< 2*m+2+C.size->i≠2*m+1->i≠2*m+2+f ->
    ∀i',st.fc.getD i (.const false)=.wire i' ->
    ((i≠2*m+2+r->¬pX m (fun y=>p0 C' y i') ->
      ∀x:Fin (2*m+2)->Bool,p0 C x i=p0 C' (pf x) i') /\
     (pX m (fun y=>p0 C' y i') ->
      (∀x:Fin (2*m+2)->Bool,p0 C x i=p0 C' (pf x) i') \/
      (∀x:Fin (2*m+2)->Bool,p0 C x i=((p0 C x (2*m+2+f)&&pD m z' (pf x)) ||
       p0 C' (pf x) i')))):=by
   intro i
   induction i using Nat.strong_induction_on with
   | ind i ih=>
    intro hi HU _0 i' hD;by_cases HO:i< 2*m+2
    ·rw[pd C (2*m+1) false i W] at hD;cases hD
     Y ⟨fun _ _ x=>by rw[p7 C x i HO,p7 C' _ i W];rfl,fun ⟨P,_,_,hP⟩=>
      absurd (hP.symm.trans (funext fun y=>p7 C' y i W)) (qt W)⟩
    ·set t:=i-(2*m+2)
     have ht:t< C.size :=W;have hX:i=2*m+2+t :=W;rw[hX] at hD ⊢;by_cases H8:t=r
     ·rw[H8,hO,hM] at hD;injection hD with hi'z;subst hi'z
      X ⟨fun h=>absurd (congrArg (2*m+2+·) H8) h,fun ⟨P,_,_,hP⟩=>
       absurd (hP.symm.trans Hy) (qt hI)⟩
     ·have q:=pE u.1 p ht W H8
      obtain ⟨kt,hC,_,hA,hB,hint,_⟩:=p4 u.1 ht q;rw[hD] at hA;injection hA with hi'eq;subst hi'eq;rcases pc u HQ t ht with ⟨H9,_,_,_⟩|⟨l,a1,a2,g,v,hh,_⟩
      ·X absurd H9 (Hr _ (List.getElem_mem ht))
      ·have k:=hT t ht l a1 a2 g W H8
       constructor
       ·intro _ hU x
        rcases hG.2.1 kt hC with ⟨c,He,Hd,Hs⟩|H2
        ·rcases l with d|d
         ·obtain ⟨c',_,_,_g,_h,_,_,_,H2,_⟩:=qO hm hW hJ hG hC (hB.trans d)
          X absurd ⟨{c'},Finset.singleton_nonempty _,by simp[_g,_h],H2⟩ hU
         ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .or a1 a2 (ir rfl) d g v hh
          have _z:∀a wa,(a=a1\/a=a2)->a< 2*m+2+t->st.fc.getD a (.const false)=.wire wa ->
            p0 C x a=p0 C' (pf x) wa:=by
           intro a wa Hm hK Hz
           have _i:=pp u Hr HQ ht q hC hD
            ⟨by simp[pa,d,g,Hm],hK⟩ Hz
           have _A:=hH kt hC c He Hd Hs wa _i
           have HZ:a≠2*m+2+r:=fun h=>by
            rw[h,hO,hM] at Hz;injection Hz with hwz;X _A.2 ⟨by O,by O⟩
           X (ih a W W (k a Hm hK).1 (k a Hm hK).2 wa Hz).1 HZ _A.1 x
          rw[p6 x ht d g v hh,
           p6 (pf x) hC (hB.trans d) s hY hZ,
           _z a1 w1 (il rfl) v Hg,_z a2 w2 (ir rfl) hh Hh]
        ·X absurd H2 hU
       ·intro H2
        rcases l with d|d
        ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .and a1 a2 (il rfl) d g v hh
         obtain ⟨c,b1,b2,He,Hd,H4,_,_,_,Hf⟩ :=
          qO hm hW hJ hG hC (hB.trans d)
         rw[s] at H4;injection H4 with hw1b hrest;injection hrest with hw2b;subst hw1b;subst hw2b
         have Ht:∀a b,(a=a1\/a=a2)->a< 2*m+2+t ->
           st.fc.getD a (.const false)=.wire b ->
           ((fun y=>p0 C' y b)=pD m c->∀x:Fin (2*m+2)->Bool,p0 C x a=pD m c (pf x)) /\
           (b=c->(∀x:Fin (2*m+2)->Bool,p0 C x a=(pf x) ⟨c,by O⟩) \/
            (c=z'/\∀x:Fin (2*m+2)->Bool,p0 C x a=(p0 C x (2*m+2+f)||(pf x) ⟨z',hI⟩))):=by
          intro a b Hm hK HM;Y ⟨fun HH x=>?_,fun hbc=>?_⟩
          ·have HZ:a≠2*m+2+r:=fun h=>by
            rw[h,hO,hM] at HM;injection HM with hwz;subst hwz;X jS He Hd hI (HH.symm.trans Hy)
           have hU:¬pX m (fun y=>p0 C' y b):=fun ⟨P,_,_,hP⟩=>
            q3 He Hd (HH.symm.trans hP)
           rw[(ih a W W (k a Hm hK).1 (k a Hm hK).2 b HM).1 HZ hU x,
            cf HH (pf x)]
          ·subst hbc
           by_cases _Q:a=2*m+2+r
           ·right;rw[_Q,hO,hM] at HM;injection HM with hcz
            X ⟨hcz.symm,fun x=>by rw[_Q,H6 x,cf Hy (pf x)]⟩
           ·left;intro x
            have hU:¬pX m (fun y=>p0 C' y b):=fun ⟨P,_,_,hP⟩=>
             qt W (hP.symm.trans (funext fun y=>p7 C' y b W))
            rw[(ih a W W (k a Hm hK).1 (k a Hm hK).2 b HM).1 _Q hU x,
             p7 C' _ b W]
         have _R:=Ht a1 w1 (il rfl) v Hg;have _S:=Ht a2 w2 (ir rfl) hh Hh
         have _B:∀(hb:Bool) (hxv HH:Bool),((hb||hxv)&&HH)=((hb&&HH)||(hxv&&HH)):=by
          intro a b c;cases a<;>cases b<;>cases c<;>rfl
         rcases Hf with ⟨_j,HI⟩|⟨_k,HJ⟩
         ·rcases _R.2 _j with _l|⟨_m,_l⟩
          ·left;intro x
           rw[pm x ht d g v hh,_l x,_S.1 HI x,
            pm (pf x) hC (hB.trans d) s hY hZ,
            _j,p7 C' _ c W,cf HI (pf x)]
          ·right;subst _m;intro x
           rw[pm x ht d g v hh,_l x,_S.1 HI x,
            pm (pf x) hC (hB.trans d) s hY hZ,
            _j,p7 C' _ c W,cf HI (pf x),_B]
         ·rcases _S.2 _k with _n|⟨_m,_n⟩
          ·left;intro x
           rw[pm x ht d g v hh,_n x,_R.1 HJ x,
            pm (pf x) hC (hB.trans d) s hY hZ,
            _k,p7 C' _ c W,cf HJ (pf x)]
          ·right;subst _m;intro x
           rw[pm x ht d g v hh,_n x,_R.1 HJ x,
            pm (pf x) hC (hB.trans d) s hY hZ,
            _k,p7 C' _ c W,cf HJ (pf x)]
           cases p0 C x (2*m+2+f)<;>cases (pf x) ⟨c,hI⟩ <;>
            cases pD m c (pf x)<;>rfl
        ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .or a1 a2 (ir rfl) d g v hh
         obtain ⟨HX,HY⟩:=hL kt hC w1 w2 (hB.trans d) s hY hZ H2;have ih1:=(ih a1 W W (k a1 (il rfl) v).1 (k a1 (il rfl) v).2 w1 Hg).2 HX;have ih2:=(ih a2 W W (k a2 (ir rfl) hh).1 (k a2 (ir rfl) hh).2 w2 Hh).2 HY;rcases ih1 with h1|h1<;>rcases ih2 with h2|h2
         ·left;intro x;rw[p6 x ht d g v hh,h1 x,h2 x,
           p6 (pf x) hC (hB.trans d) s hY hZ]
         ·right;intro x;rw[p6 x ht d g v hh,h1 x,h2 x,
           p6 (pf x) hC (hB.trans d) s hY hZ]
          cases p0 C x (2*m+2+f)&&pD m z' (pf x) <;>
           cases p0 C' (pf x) w1<;>cases p0 C' (pf x) w2<;>rfl
         ·right;intro x;rw[p6 x ht d g v hh,h1 x,h2 x,
           p6 (pf x) hC (hB.trans d) s hY hZ]
          cases p0 C x (2*m+2+f)&&pD m z' (pf x) <;>
           cases p0 C' (pf x) w1<;>cases p0 C' (pf x) w2<;>rfl
         ·right;intro x;rw[p6 x ht d g v hh,h1 x,h2 x,
           p6 (pf x) hC (hB.trans d) s hY hZ]
          cases p0 C x (2*m+2+f)&&pD m z' (pf x) <;>
           cases p0 C' (pf x) w1<;>cases p0 C' (pf x) w2<;>rfl
  have H1:∀x,cF (2*m+2) C x =
    ((p0 C x (2*m+2+f)&&pD m z' (pf x)) ||
     pq (2*m+1) (pf x)):=by
   rcases (Hu C.output (pB HQ) H0 Ha C'.output Hb).2 Hc with h1|h2
   ·exfalso;have he:=h1 (pe (2*m))
    change cF (2*m+2) C (pe (2*m))=cF (2*m+1) C' _ at he;rw[hfun,hJ,q0 W,hE,pW] at he;cases he
   ·intro x;have:=h2 x;rw[←pb,←pb,hJ] at this;X this
  have HA:z'=2*m-1:=by
   have he:=H1 (pe (2*m));rw[hfun,q0 W,hE,pW,Bool.or_false,eq_comm,Bool.and_eq_true] at he
   have:=(pt W W W).1 he.2
   O
  have hF:p8 C f=ph (m+1) {2*m}:=H3 fun x _x HH=>by
   rw[H1 x,HA,_x,HH];R
  have HN:∀x:Fin (2*m+2)->Bool,(p0 C x (2*m+2+f)&&pD m z' (pf x)) =
    ph (m+1) {2*m} x:=by
   intro x
   rw[HA,show p0 C x (2*m+2+f)=ph (m+1) {2*m} x from cf hF x,
    j6 W W x,qe W W,
    pv W]
   have hs:(⟨2*m-1+1,by O⟩:Fin (2*(m+1)))=⟨2*m,by O⟩:=Fin.ext (by dsimp;O)
   rw[hs];cases x ⟨2*m,by O⟩<;>cases x ⟨2*m+1,by O⟩<;>cases x ⟨2*m-1-1,by O⟩<;>rfl
  Y HF hF ?_ fun t ht kt hC HP H8 hA=>?_
  ·right;right
   Y ⟨2*m,2*m-1,by O,by O,by O,ir W,funext fun x=>?_⟩
   change p0 C x (2*m+2+r)=_
   rw[H6 x,show p0 C x (2*m+2+f)=ph (m+1) {2*m} x from cf hF x,
    cf Hy (pf x),qh W W,pv W]
   have:(⟨z',hI⟩:Fin (2*m+1))=⟨2*m-1,by O⟩:=Fin.ext HA
   rw[this];R
  ·have hp:=Hu (2*m+2+t) W W W (2*m+1+kt) hA
   Y ⟨fun hU=>hp.1 W hU,fun H2=>?_⟩;rcases hp.2 H2 with h1|h2
   ·X il h1
   ·X ir fun x=>by change p0 C x (2*m+2+t)=_;rw[h2 x,HN x];R
 ·
  have Hv:∀i,i< 2*m+2+C.size->i≠2*m+1->i≠2*m+2+f ->
    ∀i',st.fc.getD i (.const false)=.wire i' ->
    ((¬pX m (fun y=>p0 C' y i') ->
      ∀x:Fin (2*m+2)->Bool,p0 C x i=p0 C' (pf x) i') /\
     (pX m (fun y=>p0 C' y i') ->
      (∀x:Fin (2*m+2)->Bool,p0 C x i=p0 C' (pf x) i') \/
      (∀x:Fin (2*m+2)->Bool,p0 C x i=(p0 C x (2*m+2+f)||p0 C' (pf x) i')))):=by
   intro i
   induction i using Nat.strong_induction_on with
   | ind i ih=>
    intro hi HU _0 i' hD;by_cases HO:i< 2*m+2
    ·rw[pd C (2*m+1) false i W] at hD;cases hD
     Y ⟨fun _ x=>by rw[p7 C x i HO,p7 C' _ i W];rfl,fun ⟨P,_,_,hP⟩=>
      absurd (hP.symm.trans (funext fun y=>p7 C' y i W)) (qt W)⟩
    ·set t:=i-(2*m+2)
     have ht:t< C.size :=W;have hX:i=2*m+2+t :=W;rw[hX] at hD ⊢;by_cases H8:t=r
     ·rw[H8,hO,hM] at hD;injection hD with hi'z;subst hi'z
      X ⟨fun hU=>absurd ⟨Pz,_y,Hx,Hy⟩ hU,fun _=>ir fun x=>by rw[H8,H6 x]⟩
     ·have q:=pE u.1 p ht W H8
      obtain ⟨kt,hC,_,hA,hB,hint,_⟩:=p4 u.1 ht q;rw[hD] at hA;injection hA with hi'eq;subst hi'eq;rcases pc u HQ t ht with ⟨H9,_,_,_⟩|⟨l,a1,a2,g,v,hh,_⟩
      ·X absurd H9 (Hr _ (List.getElem_mem ht))
      ·have k:=hT t ht l a1 a2 g W H8
       constructor
       ·intro hU x
        rcases hG.2.1 kt hC with ⟨c,He,Hd,Hs⟩|H2
        ·rcases l with d|d
         ·obtain ⟨c',_,_,_g,_h,_,_,_,H2,_⟩:=qO hm hW hJ hG hC (hB.trans d)
          X absurd ⟨{c'},Finset.singleton_nonempty _,by simp[_g,_h],H2⟩ hU
         ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .or a1 a2 (ir rfl) d g v hh
          have _z:∀a wa,(a=a1\/a=a2)->a< 2*m+2+t->st.fc.getD a (.const false)=.wire wa ->
            p0 C x a=p0 C' (pf x) wa:=by
           intro a wa Hm hK Hz
           have _i:=pp u Hr HQ ht q hC hD
            ⟨by simp[pa,d,g,Hm],hK⟩ Hz
           X (ih a W W (k a Hm hK).1 (k a Hm hK).2 wa Hz).1
            (hH kt hC c He Hd Hs wa _i).1 x
          rw[p6 x ht d g v hh,
           p6 (pf x) hC (hB.trans d) s hY hZ,
           _z a1 w1 (il rfl) v Hg,_z a2 w2 (ir rfl) hh Hh]
        ·X absurd H2 hU
       ·intro H2
        rcases l with d|d
        ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .and a1 a2 (il rfl) d g v hh
         obtain ⟨c,b1,b2,He,Hd,H4,_,_,_,Hf⟩ :=
          qO hm hW hJ hG hC (hB.trans d)
         rw[s] at H4;injection H4 with hw1b hrest;injection hrest with hw2b;subst hw1b;subst hw2b
         have _A:∀w,(w=c\/(fun y=>p0 C' y w)=pD m c)->¬pX m (fun y=>p0 C' y w):=by
          intro w hw ⟨P,_,_,hP⟩;rcases hw with rfl|HH
          ·X qt W (hP.symm.trans (funext fun y=>p7 C' y w W))
          ·X q3 He Hd (HH.symm.trans hP)
         have _T:¬pX m (fun y=>p0 C' y w1):=_A w1 (by rcases Hf with ⟨h,_⟩|⟨_,h⟩<;>[X il h;X ir h])
         have _U:¬pX m (fun y=>p0 C' y w2):=_A w2 (by rcases Hf with ⟨_,h⟩|⟨h,_⟩<;>[X ir h;X il h])
         left;intro x
         rw[pm x ht d g v hh,
          pm (pf x) hC (hB.trans d) s hY hZ,
          (ih a1 W W (k a1 (il rfl) v).1 (k a1 (il rfl) v).2 w1 Hg).1 _T x,
          (ih a2 W W (k a2 (ir rfl) hh).1 (k a2 (ir rfl) hh).2 w2 Hh).1 _U x]
        ·obtain ⟨w1,w2,hY,hZ,Hg,Hh,s⟩:=hint .or a1 a2 (ir rfl) d g v hh
         obtain ⟨HX,HY⟩:=hL kt hC w1 w2 (hB.trans d) s hY hZ H2;have ih1:=(ih a1 W W (k a1 (il rfl) v).1 (k a1 (il rfl) v).2 w1 Hg).2 HX;have ih2:=(ih a2 W W (k a2 (ir rfl) hh).1 (k a2 (ir rfl) hh).2 w2 Hh).2 HY;rcases ih1 with h1|h1<;>rcases ih2 with h2|h2
         ·left;intro x;rw[p6 x ht d g v hh,h1 x,h2 x,
           p6 (pf x) hC (hB.trans d) s hY hZ]
         ·right;intro x;rw[p6 x ht d g v hh,h1 x,h2 x,
           p6 (pf x) hC (hB.trans d) s hY hZ]
          cases p0 C x (2*m+2+f)<;>cases p0 C' (pf x) w1<;>cases p0 C' (pf x) w2<;>rfl
         ·right;intro x;rw[p6 x ht d g v hh,h1 x,h2 x,
           p6 (pf x) hC (hB.trans d) s hY hZ]
          cases p0 C x (2*m+2+f)<;>cases p0 C' (pf x) w1<;>cases p0 C' (pf x) w2<;>rfl
         ·right;intro x;rw[p6 x ht d g v hh,h1 x,h2 x,
           p6 (pf x) hC (hB.trans d) s hY hZ]
          cases p0 C x (2*m+2+f)<;>cases p0 C' (pf x) w1<;>cases p0 C' (pf x) w2<;>rfl
  have H1:∀x,cF (2*m+2) C x =
    (p0 C x (2*m+2+f)||pq (2*m+1) (pf x)):=by
   rcases (Hv C.output (pB HQ) H0 Ha C'.output Hb).2 Hc with h1|h2
   ·exfalso;have he:=h1 (pe (2*m))
    change cF (2*m+2) C (pe (2*m))=cF (2*m+1) C' _ at he;rw[hfun,hJ,q0 W,hE,pW] at he;cases he
   ·intro x;have:=h2 x;rw[←pb,←pb,hJ] at this;X this
  have hF:p8 C f=ph (m+1) {2*m}:=H3 fun x _x _=>by
   rw[H1 x,_x];R
  Y HF hF ?_ fun t ht kt hC HP H8 hA=>?_
  ·left
   set S:=Pz.biUnion fun c=>{c-1,c};Y ⟨{2*m}∪S,⟨2*m,by simp⟩,fun e he=>?_,funext fun x=>?_⟩
   ·rcases Finset.mem_union.1 he with h|h
    ·simp at h;O
    ·simp only[S,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton] at h
     obtain ⟨c,_N,_O⟩:=h
     have:=(Hx c _N).2
     rcases _O with rfl|rfl<;>O
   ·change p0 C x (2*m+2+r)=_
    rw[H6 x,show p0 C x (2*m+2+f)=ph (m+1) {2*m} x from cf hF x,
     cf Hy (pf x),zH Hx x,qZ]
  ·have hp:=Hv (2*m+2+t) W W W (2*m+1+kt) hA
   Y ⟨hp.1,fun H2=>?_⟩;rcases hp.2 H2 with h1|h2
   ·X il h1
   ·X ir fun x=>by change p0 C x (2*m+2+t)=_;rw[h2 x,show p0 C x (2*m+2+f)=ph (m+1) {2*m} x from cf hF x];R
private lemma ko {n:ℕ} {E:J} (e:FanInTwo E)
  (j:∃y1 y2:V n,cF n E y1≠cF n E y2) :
  ∃D:J,FanInTwo D/\D.size=E.size+1 /\
   ∀x:Fin (n+1)->Bool,cF (n+1) D x=(x (Fin.last n)||cF n E (Fin.init x)):=by
 let shift:ℕ->ℕ:=fun w=>if w< n then w else w+1;let gs1:List Gate:=E.gates.map fun g=>({ op:=g.op,inputs:=g.inputs.map shift }:Gate);let D:J:={ gates:=gs1++[⟨.or,[n,shift E.output]⟩],output:=n+1+E.size };Y ⟨D,?_,by simp[D,gs1,Circuit.size],fun x=>?_⟩
 ·intro g hg;simp only[D,gs1,List.mem_append,List.mem_map,List.mem_singleton] at hg
  rcases hg with ⟨g0,p,rfl⟩|rfl
  ·X ⟨(e g0 p).1,by simpa using (e g0 p).2⟩
  ·X ⟨by simp,by simp⟩
 ·have k:∀w,w< n+E.size ->
    (pK gs1 (List.ofFn x)).getD (shift w) false=p0 E (Fin.init x) w:=by
   intro w
   induction w using Nat.strong_induction_on with
   | ind w ih=>
    intro hw;by_cases l:w< n
    ·simp only[shift,l,↓reduceIte]
     rw[q5 _ _ w (by simp;O),List.getD_eq_getElem _ _ (by simp;O),
      List.getElem_ofFn,p7 E _ w l];R
    ·set t:=w-n
     have ht:t< E.size :=W;have f:w=n+t :=W;simp only[shift,l,↓reduceIte];rw[show w+1=n+1+t by O]
     have h:gs1.length=E.size:=by simp[gs1,Circuit.size]
     have m:t< gs1.length :=W
     have c:gs1=gs1.take t++gs1[t]'m::gs1.drop (t+1):=by
      rw[←List.drop_eq_getElem_cons m,List.take_append_drop]
     have b:(pK (gs1.take t) (List.ofFn x)).length=n+1+t:=by
      rw[qm,List.length_ofFn,List.length_take];O
     conv_lhs=>rw[c,ql,qA]
     rw[q5 _ _ (n+1+t) (by rw[List.length_append,b];simp),
      List.getD_eq_getElem _ _ (by rw[List.length_append,b];simp),List.getElem_append_right W]
     simp only[b,Nat.sub_self,List.getElem_singleton];rw[f,pj E (Fin.init x) t ht]
     have i:gs1[t]'m={ op:=(E.gates[t]'ht).op,inputs:=(E.gates[t]'ht).inputs.map shift } :=
      List.getElem_map _
     rw[i,List.map_map];congr 1;apply List.map_congr_left;intro a _;simp only[Function.comp_def];by_cases ha:a< n+t
     ·rw[if_pos ha,←ih a W W]
      have q:shift a< n+1+t:=by simp only[shift];split_ifs<;>O
      conv_rhs=>rw[c,ql]
      X (q5 _ _ _ W).symm
     ·rw[if_neg ha,List.getD_eq_default _ _ (by rw[b];simp only[shift];split_ifs<;>O)]
  have d:(pK gs1 (List.ofFn x)).length=n+1+E.size:=by
   rw[qm,List.length_ofFn];simp[gs1,Circuit.size]
  unfold circuitFun Circuit.eval
  rw[qu];simp only[D,ql,qA,zd]
  rw[List.getD_eq_getElem _ _ (by rw[List.length_append,d];simp),
   List.getElem_append_right (by rw[d])]
  simp only[d,Nat.sub_self,List.getElem_singleton,GateOp.eval,List.map_cons,List.map_nil,
   List.any_cons,List.any_nil,id_eq,Bool.or_false]
  rw[q5 _ _ n (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn,
   k E.output (pB j)];R
private def pU (C:J) (t0:ℕ) (gNew:Gate):J :=
 { gates:=C.gates.set t0 gNew,output:=C.output }
private lemma pS (C:J) (t0:ℕ) (gNew:Gate) :
  (pU C t0 gNew).size=C.size:=List.length_set
private lemma z1 {C:J} (d:FanInTwo C) (t0:ℕ) {gNew:Gate} (hg:Ok gNew) :
  FanInTwo (pU C t0 gNew):=by
 intro g a;obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 a;have b:i< C.gates.length:=by simpa [pU] using hi
 by_cases c:i=t0
 ·subst c;simp only[pU,List.getElem_set_self];X hg
 ·simp only[pU,List.getElem_set_ne (Ne.symm c)];X d _ (List.getElem_mem b)
private lemma zA {C:J} (d:z0 C) (t0:ℕ) {gNew:Gate} (hg:gNew.op≠.not) :
  z0 (pU C t0 gNew):=by
 intro g a;obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 a;have b:i< C.gates.length:=by simpa [pU] using hi
 by_cases c:i=t0
 ·subst c;simp only[pU,List.getElem_set_self];X hg
 ·simp only[pU,List.getElem_set_ne (Ne.symm c)];X d _ (List.getElem_mem b)
private lemma qc (C:J) {n:ℕ} (x:V n) (t0:ℕ) (gNew:Gate)
  (i:ℕ) (hi:i< n+t0) :
  p0 (pU C t0 gNew) x i=p0 C x i:=by
 induction i using Nat.strong_induction_on with
 | ind i ih=>
  by_cases f:i< n
  ·rw[p7 _ x i f,p7 C x i f]
  ·set t:=i-n
   by_cases d:t< C.size
   ·have b:t< (pU C t0 gNew).size:=by rw[pS];X d
    have c:i=n+t :=W;rw[c,pj _ x t b,pj C x t d]
    have e:(pU C t0 gNew).gates[t]'b=C.gates[t]'d :=
     List.getElem_set_ne (by O:t0≠t) _
    rw[e];congr 1;apply List.map_congr_left;intro a _
    split_ifs with ha
    ·X ih a W W
    ·rfl
   ·rw[z3 _ x i (by rw[pS];O),z3 C x i W]
private lemma qg (C:J) {n:ℕ} (x:V n) {t0:ℕ} (d:t0< C.size)
  (gNew:Gate) :
  p0 (pU C t0 gNew) x (n+t0) =
   gNew.op.eval (gNew.inputs.map fun a=>if a< n+t0 then p0 C x a else false):=by
 have b:t0< (pU C t0 gNew).size:=by rw[pS];X d
 rw[pj _ x t0 b];have c:(pU C t0 gNew).gates[t0]'b=gNew:=List.getElem_set_self _;rw[c];congr 1;apply List.map_congr_left;intro a _
 split_ifs with ha
 ·X qc C x t0 gNew a ha
 ·rfl
private lemma qP (C:J) {n:ℕ} {t0:ℕ} (i:t0< C.size)
  (gNew:Gate) (x:V n)
  (b:∀t (ht:t< C.size),t0< t ->
   (C.gates[t]'ht).op.eval ((C.gates[t]'ht).inputs.map fun a=>
    if a< n+t then (if a=n+t0 then p0 (pU C t0 gNew) x (n+t0) else p0 C x a) else false) =
   p0 C x (n+t)) :
  ∀w,w< n+C.size->w≠n+t0->p0 (pU C t0 gNew) x w=p0 C x w:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw j;by_cases g:w< n+t0
  ·X qc C x t0 gNew w g
  ·set t:=w-n
   have e:t< C.size :=W;have h:t0< t :=W;have c:w=n+t :=W;have d:t< (pU C t0 gNew).size:=by rw[pS];X e
   rw[c,pj _ x t d]
   have f:(pU C t0 gNew).gates[t]'d=C.gates[t]'e :=
    List.getElem_set_ne (by O:t0≠t) _
   rw[f,←b t e h];congr 1;apply List.map_congr_left;intro a _
   split_ifs with ha ha0
   ·subst ha0;R
   ·X ih a W W ha0
   ·rfl
private lemma qv (C:J) {n:ℕ} {t0:ℕ} (c:t0< C.size)
  (gNew:Gate) (x:V n)
  (b:p0 (pU C t0 gNew) x (n+t0)=p0 C x (n+t0)) :
  ∀w,w< n+C.size->p0 (pU C t0 gNew) x w=p0 C x w:=by
 intro w hw;by_cases h0:w=n+t0
 ·subst h0;X b
 ·Y qP C c gNew x (fun t ht _=>?_) w hw h0
  rw[pj C x t ht];congr 1;apply List.map_congr_left;intro a _
  split_ifs with ha ha0
  ·subst ha0;X b
  ·rfl
  ·rfl
private lemma qC {n:ℕ} {C:J} (a:IsMinimalCircuit n C)
  {t0:ℕ} (gNew:Gate) (hg:Ok gNew) (hfun:cF n (pU C t0 gNew)=cF n C) :
  IsMinimalCircuit n (pU C t0 gNew) :=
 ⟨z1 a.1 t0 hg,fun E b c=>by
  rw[pS];X a.2 E b (c.trans hfun)⟩
private lemma qy {n:ℕ} {C:J} (a:IsMinimalCircuit n C)
  {t1 t2:ℕ} (h1:t1< C.size) (h2:t2< C.size) (c:t1≠t2) :
  (p8 C t1:(V n)->Bool)≠p8 C t2:=by
 intro b;by_cases d:t1< t2
 ·obtain ⟨x,hx⟩:=py a t2 h2 (n+t1) W
  X hx (cf b.symm x)
 ·obtain ⟨x,hx⟩:=py a t1 h1 (n+t2) W
  X hx (cf b x)
private lemma kx {C:J} (a:z0 C) (n t0 target:ℕ) :
  z0 (qQ C n t0 target):=by
 intro g hg;simp only[qQ,List.mem_append,List.mem_map] at hg;rcases hg with hg|⟨g0,b,rfl⟩
 ·X a g (List.mem_of_mem_take hg)
 ·X a g0 (List.mem_of_mem_drop b)
private lemma qN {n:ℕ} {C:J}
  (b:IsMinimalCircuit n C) (i:z0 C) (hfun:cF n C=pq n)
  {t0 target:ℕ} (d:t0< C.size) (a:target< n+t0)
  (k:∀x:V n,p0 C x target=true->p0 C x (n+t0)=true)
  (c:∀e,e+1< n->pl C (pe e:V n) t0 (p0 C (pe e:V n) target) C.output=true) :
  False:=by
 have l:cF n (qQ C n t0 target)=cF n C:=by
  funext x;rw[hfun,z7 C x t0 target d (il a),if_pos a]
  cases hpx:pq n x with
  | false=>
   cases hv:pl C x t0 (p0 C x target) C.output with
   | false=>rfl
   | true=>
    exfalso;have h2:=jo C b.1 i x t0 d (k x) C.output hv;rw[pV C x t0 d _ rfl,←pb,hfun,hpx] at h2;cases h2
  | true=>
   rw[px] at hpx;obtain ⟨p,q,s,m,r⟩:=hpx
   have f:∀j:Fin n,(pe p.val:V n) j=true->x j=true:=by
    intro j hj;simp only[pe,e2,decide_eq_true_eq] at hj;rcases hj with h|h<;>[X (Fin.ext h:j=p)▸m;X (Fin.ext W:j=q)▸r]
   have h2:=zz (qQ C n t0 target) (qS C b.1 n t0 target)
    (kx i n t0 target) f (qQ C n t0 target).output
    (by
      rw[←pb,z7 C _ t0 target d (il a),if_pos a];X c p.val (by have:=q.isLt;O))
   rw[←pb,z7 C x t0 target d (il a),if_pos a] at h2;X h2
 have g:=b.2 _ (qS C b.1 n t0 target) l;rw[zn C n t0 target d] at g;O
private lemma qz {m:ℕ} {C:J}
  (hfun:cF (2*m) C=pq (2*m)) {v:ℕ}
  (b:qb m (p8 C v)):C.output≠2*m+v:=by
 intro h;obtain ⟨_,k0,_,_,a,_,c⟩:=b
 have h1:pq (2*m) (e1 k0)=true:=by
  rw[←cf hfun _,pb,h,show p0 C (e1 k0) (2*m+v)=qd m _ k0 (e1 k0) from cf c _];X (pN a a).2 rfl
 rw[pW] at h1;cases h1
private lemma jn {m:ℕ} {C:J}
  (hfun:cF (2*m) C=pq (2*m)) {v:ℕ}
  (a:zM m (p8 C v)):C.output≠2*m+v:=by
 intro h;obtain ⟨c,b,d,e⟩:=a
 have h1:pq (2*m) (e1 (c-1))=true:=by
  rw[←cf hfun _,pb,h,show p0 C (e1 (c-1)) (2*m+v)=pP m c (e1 (c-1)) from cf e _];X (pu b d W).2 (il W)
 rw[pW] at h1;cases h1
private lemma zI {m:ℕ} (hm:1<=m) {C:J}
  (e:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (l:qf m C) {v r:ℕ} (hv:v< C.size) (hr:r< C.size)
  (f:zM m (p8 C v)) (b:pC (2*m) r (2*m+v) (C.gates[r]'hr)) :
  (C.gates[r]'hr).op≠.or:=by
 intro a;obtain ⟨c,p,g,q⟩:=f
 have y:∃x1 x2:Fin (2*m)->Bool,cF (2*m) C x1≠cF (2*m) C x2:=by
  rw[hfun];X ps W
 rcases pc e y r hr with ⟨h,_,_,_⟩|⟨_,a1,a2,i,z,hh,_⟩
 ·rw[a] at h;cases h
 ·have s:=b.1;simp only[pa,a,i,List.mem_cons,List.not_mem_nil,or_false] at s
  have t:∀x:Fin (2*m)->Bool,pP m c x=true->p8 C r x=true:=fun x hx=>by
   change p0 C x (2*m+r)=true;rw[p6 x hr a i z hh,Bool.or_eq_true];have u:p0 C x (2*m+v)=true:=by rw[show p0 C x (2*m+v)=pP m c x from cf q x];X hx
   rcases s with rfl|rfl<;>[X il u;X ir u]
  have h1:=t (e1 (c-1)) ((pu p g W).2 (il W));have h2:=t (e1 (c+1)) ((pu p g g).2 (ir rfl));rcases l.2 r hr with ⟨S,_,_,d⟩|⟨c',j,k,d⟩|⟨_,k',_,_,w,_,d⟩
  ·rw[cf d _,pz] at h1;cases h1
  ·have hA:=(pu j k W).1 ((cf d _).symm.trans h1)
   have hB:=(pu j k g).1 ((cf d _).symm.trans h2);have n:c'=c :=W;subst n;X qy e hr hv (by have:=b.2;O) (d.trans q.symm)
  ·have hA:=(pN w W).1 ((cf d _).symm.trans h1)
   have hB:=(pN w g).1 ((cf d _).symm.trans h2);O
private lemma jQ {m i k:ℕ} {S:Finset ℕ} (hi:i+1< 2*m) (hk:k< 2*m)
  (f:i∈S) (hS:∀e∈S,e=i\/e=k\/e+1=k) (x:Fin (2*m)->Bool) :
  (ph m S x||x ⟨k,hk⟩)=qd m i k x:=by
 rw[qh hi hk]
 cases hxk:x ⟨k,hk⟩ with
 | true=>simp
 | false=>
  simp only[Bool.or_false];apply Bool.eq_iff_iff.2;simp only[po,Bool.and_eq_true]
  constructor
  ·rintro ⟨a,b,g,j,c,d⟩
   rcases hS a.val g with h|h|h
   ·X ⟨(Fin.ext h:a=⟨i,by O⟩)▸c,(Fin.ext (by dsimp;O):b=⟨i+1,hi⟩)▸d⟩
   ·have:a=⟨k,hk⟩:=Fin.ext h;rw[this,hxk] at c;cases c
   ·have:b=⟨k,hk⟩:=Fin.ext (by dsimp;O);rw[this,hxk] at d;cases d
  ·rintro ⟨h1,h2⟩;X ⟨⟨i,by O⟩,⟨i+1,hi⟩,f,rfl,h1,h2⟩
private lemma pQ {m:ℕ} (hm:1<=m) {C:J}
  (l:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (i:qf m C) {u r:ℕ} (hu:u< C.size) (hr:r< C.size)
  (e:q1 m (p8 C u)) (f:pC (2*m) r (2*m+u) (C.gates[r]'hr)) :
  (C.gates[r]'hr).op=.or /\
  (q1 m (p8 C r)\/qb m (p8 C r)) /\
  (∀x:Fin (2*m)->Bool,p8 C u x=true->p8 C r x=true):=by
 have hI:∃x1 x2:Fin (2*m)->Bool,cF (2*m) C x1≠cF (2*m) C x2:=by
  rw[hfun];X ps W
 rcases pc l hI r hr with ⟨z,_,_,_⟩|⟨n,a1,a2,b,w,y,_⟩
 ·X absurd z (i.1 _ (List.getElem_mem hr))
 ·rcases n with hop_and|a
  ·exfalso
   obtain ⟨_,b1,b2,k,_,_,_,hh,hA,_⟩:=qn hm l hfun i hr hop_and;rw[b] at k;injection k with h1 hrest;injection hrest with h2;subst h1;subst h2;have p:=f.1;simp only[pa,hop_and,b,List.mem_cons,List.not_mem_nil,or_false] at p;rcases p with rfl|rfl<;>[X hh e;X hA e]
  ·have p:=f.1;simp only[pa,a,b,List.mem_cons,List.not_mem_nil,or_false] at p
   have hJ:∀x:Fin (2*m)->Bool,p8 C u x=true->p8 C r x=true:=fun x hx=>by
    change p0 C x (2*m+r)=true;rw[p6 x hr a b w y,Bool.or_eq_true];rcases p with rfl|rfl<;>[X il hx;X ir hx]
   Y ⟨a,?_,hJ⟩;rcases i.2 r hr with h1|⟨c,hD,q,hB⟩|h3
   ·X il h1
   ·exfalso
    obtain ⟨Su,_,_,hE⟩:=e
    have g:∀d,d< 2*m+r ->
      (∀x:Fin (2*m)->Bool,pP m c x=(ph m Su x||p0 C x d))->False:=by
     intro d hd s;have h1:=s (e1 (c-1));rw[(pu hD q W).2 (il W),pz,Bool.false_or] at h1;have h2:=s (e1 (c+1));rw[(pu hD q q).2 (ir rfl),pz,Bool.false_or] at h2
     rcases qE i d W with
      ⟨j,hj,_,h⟩|⟨_,_,_,Q,_,_,h⟩|⟨_,_,_,c',t,v,h⟩|⟨_,_,_,_,k',_,_,hF,_,h⟩
     ·have hG:j=c-1:=of_decide_eq_true ((cf h _).symm.trans h1.symm)
      have hH:j=c+1:=of_decide_eq_true ((cf h _).symm.trans h2.symm);O
     ·rw[cf h _,pz] at h1;cases h1
     ·have hG:=(pu t v W).1 ((cf h _).symm.trans h1.symm)
      have hH:=(pu t v q).1 ((cf h _).symm.trans h2.symm);have hC:c'=c :=W;subst hC;obtain ⟨x,hx⟩:=py l r hr d hd;X hx (by rw[cf hB x,cf h x])
     ·have hG:=(pN hF W).1 ((cf h _).symm.trans h1.symm)
      have hH:=(pN hF q).1 ((cf h _).symm.trans h2.symm);O
    rcases p with rfl|rfl
    ·X g a2 y fun x=>by
      rw[←cf hB x,←cf hE x];X p6 x hr a b w y
    ·X g a1 w fun x=>by
      rw[←cf hB x,←cf hE x,Bool.or_comm];X p6 x hr a b w y
   ·X ir h3
private lemma qB {m:ℕ} (hm:1<=m) {C:J}
  (l:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (s:qf m C) {v i k:ℕ} (hv:v< C.size)
  (H4:i%2=0) (hi:i+1< 2*m) (hk:k< 2*m) (hK:k=i+2\/k+1=i)
  (hH:p8 C v=qd m i k) :
  (C.gates[v]'hv).op=.or /\
  ∃(u:ℕ) (hu:u< v) (Su:Finset ℕ),Su.Nonempty/\(∀e∈Su,e+1< 2*m) /\
   i∈Su/\(∀e∈Su,e=i\/e=k\/e+1=k) /\
   p8 C u=ph m Su /\
   ((C.gates[v]'hv).inputs=[2*m+u,k]\/(C.gates[v]'hv).inputs=[k,2*m+u]):=by
 have H0:∃x1 x2:Fin (2*m)->Bool,cF (2*m) C x1≠cF (2*m) C x2:=by
  rw[hfun];X ps W
 rcases pc l H0 v hv with ⟨hL,_,_,_⟩|⟨t,a1,a2,w,hM,hU,_⟩
 ·X absurd hL (s.1 _ (List.getElem_mem hv))
 ·rcases t with hop_and|f
  ·exfalso;obtain ⟨⟨S,_,_,hS⟩,_⟩:=qn hm l hfun s hv hop_and
   X qJ hk (hS.symm.trans hH)
  ·have d:∀x:Fin (2*m)->Bool,qd m i k x=(p0 C x a1||p0 C x a2):=fun x=>by
    rw[←cf hH x];X p6 x hv f w hM hU
   have g:∀a (ha:a< 2*m+v),
     (∀x:Fin (2*m)->Bool,p0 C x a=true->qd m i k x=true) ->
     a=k\/∃(u:ℕ) (_:u< v) (Su:Finset ℕ),a=2*m+u/\Su.Nonempty /\
      (∀e∈Su,e+1< 2*m)/\(∀e∈Su,e=i\/e=k\/e+1=k)/\p8 C u=ph m Su:=by
    intro a ha hC
    rcases qE s a W with
     ⟨j,hj,rfl,y⟩|⟨u,hu,rfl,Su,hD,hI,hV⟩|⟨_,_,_,c,hW,hJ,y⟩|⟨_,_,_,i',k',H1,H5,hN,H2,y⟩
    ·left;X (pN hk hj).1 (hC (e1 a) (by rw[cf y _];simp[e1]))
    ·right;Y ⟨u,by O,Su,rfl,hD,hI,fun e hO=>?_,hV⟩
     X (qo hi hk (hI e hO)).1 (hC (pe e) (by rw[cf hV _];X (pg hI (hI e hO)).2 hO))
    ·exfalso
     have h1:=hC (e1 (c-1)) (by rw[cf y _];X (pu hW hJ W).2 (il W))
     have h2:=hC (e1 (c+1)) (by rw[cf y _];X (pu hW hJ hJ).2 (ir rfl))
     have H6:=(pN hk W).1 h1;have H7:=(pN hk hJ).1 h2;O
    ·exfalso
     have hE:k'=k:=(pN hk hN).1 (hC (e1 k') (by rw[cf y _];X (pN hN hN).2 rfl))
     have hF:i'=i:=by rcases hK with rfl|hki<;>rcases H2 with h'|h'<;>O
     subst hE;subst hF;obtain ⟨x,hx⟩:=py l v hv a ha;X hx (by rw[cf hH x,cf y x])
   have h1:=g a1 hM fun x hx=>by rw[d x,hx];R
   have h2:=g a2 hU fun x hx=>by rw[d x,hx,Bool.or_true]
   Y ⟨f,?_⟩;rcases h1 with z|⟨u1,H3,S1,hh,hG,hX,hA,hB⟩
   ·rcases h2 with n|⟨u2,hY,S2,p,r,hP,h,q⟩
    ·exfalso;obtain ⟨x,hx⟩:=py l v hv a1 hM
     X hx (by rw[cf hH x,d x,z,n,Bool.or_self])
    ·have hQ:i∈S2:=by
      have b:=d (pe i)
      rw[(qo hi hk hi).2 (il rfl),z,p7 C _ k hk,p,
       show p0 C (pe i) (2*m+u2)=ph m S2 (pe i) from cf q _] at b
      have hR:(pe i:Fin (2*m)->Bool) ⟨k,hk⟩=false:=by simp only[pe,e2,decide_eq_false_iff_not];O
      rw[hR,Bool.false_or] at b;X (pg hP hi).1 b.symm
     X ⟨u2,hY,S2,r,hP,hQ,h,q,ir (by rw[w,z,p])⟩
   ·rcases h2 with n|⟨u2,hY,S2,p,r,hP,h,q⟩
    ·have hT:i∈S1:=by
      have b:=d (pe i)
      rw[(qo hi hk hi).2 (il rfl),n,p7 C _ k hk,hh,
       show p0 C (pe i) (2*m+u1)=ph m S1 (pe i) from cf hB _] at b
      have hR:(pe i:Fin (2*m)->Bool) ⟨k,hk⟩=false:=by simp only[pe,e2,decide_eq_false_iff_not];O
      rw[hR,Bool.or_false] at b;X (pg hX hi).1 b.symm
     X ⟨u1,H3,S1,hG,hX,hT,hA,hB,il (by rw[w,hh,n])⟩
    ·exfalso
     have hZ:=d (e1 k)
     rw[(pN hk hk).2 rfl,hh,p,
      show p0 C (e1 k) (2*m+u1)=ph m S1 (e1 k) from cf hB _,
      show p0 C (e1 k) (2*m+u2)=ph m S2 (e1 k) from cf q _,
      pz,pz] at hZ;cases hZ
private lemma jc {m:ℕ} (hm:1<=m) {C:J}
  (p:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (hh:qf m C) {u v:ℕ} (hu:u< C.size) (hv:v< C.size)
  (hZ:qb m (p8 C u)) (H0:zM m (p8 C v)) :
  ¬pC (2*m) v (2*m+u) (C.gates[v]'hv):=by
 intro hA
 have H9:∃x1 x2:Fin (2*m)->Bool,cF (2*m) C x1≠cF (2*m) C x2:=by
  rw[hfun];X ps W
 have Hq:u< v:=by have:=hA.2;O
 obtain ⟨i,k0,Hr,hi,hB,Ha,Hj⟩:=hZ;obtain ⟨c,hH,r,hX⟩:=H0
 have hC:∀x:Fin (2*m)->Bool,qd m i k0 x=true->pP m c x=true:=by
  rcases pc p H9 v hv with ⟨hP,_,_,_⟩|⟨f,a1,a2,g,hI,hJ,_⟩
  ·X absurd hP (hh.1 _ (List.getElem_mem hv))
  ·rcases f with d|hop_or
   ·exfalso;obtain ⟨⟨S,_,_,hS⟩,_⟩:=qn hm p hfun hh hv d
    X z6 hH r (hS.symm.trans hX)
   ·intro x hx;rw[←cf hX x];change p0 C x (2*m+v)=true
    rw[p6 x hv hop_or g hI hJ,Bool.or_eq_true];have Hk:p0 C x (2*m+u)=true:=by rw[show p0 C x (2*m+u)=qd m i k0 x from cf Hj x];X hx
    have H1:=hA.1;simp only[pa,hop_or,g,List.mem_cons,List.not_mem_nil,or_false] at H1;rcases H1 with rfl|rfl<;>[X il Hk;X ir Hk]
 have q:(k0=i+2/\c=i+1)\/(k0+1=i/\c=i):=by
  have h1:=(pu hH r hB).1 (hC (e1 k0) ((pN hB hB).2 rfl));have h2:=hC (pe i) ((qo hi hB hi).2 (il rfl));rw[qe hH r] at h2;simp only[Bool.or_eq_true,pe,e2,decide_eq_true_eq] at h2;rcases Ha with hQ|Hb<;>[X il ⟨hQ,by O⟩;X ir ⟨Hb,by O⟩]
 have hK:∀(x:Fin (2*m)->Bool) (w:ℕ),w< 2*m+C.size->w≠2*m+v ->
   pl C x v (p0 C x (2*m+u)) w=p0 C x w:=by
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih=>
   intro hw Hs;by_cases Hl:w< 2*m+v
   ·X pA C x v hv _ w Hl
   ·set t:=w-2*m
    have ht:t< C.size :=W;have Ht:v< t :=W;have H2:w=2*m+t :=W;rw[H2];rcases pc p H9 t ht with ⟨hP,_,_,_⟩|⟨f,a1,a2,g,hI,hJ,hN⟩
    ·X absurd hP (hh.1 _ (List.getElem_mem ht))
    ·by_cases H7:pC (2*m) t (2*m+v) (C.gates[t]'ht)
     ·have d:(C.gates[t]'ht).op=.and:=by
       rcases f with h|h
       ·X h
       ·X absurd h (zI hm p hfun hh hv ht ⟨c,hH,r,hX⟩ H7)
      rw[pF x hv _ ht W d g hI hJ,
       pm x ht d g hI hJ]
      have H1:=H7.1;simp only[pa,d,g,List.mem_cons,List.not_mem_nil,or_false] at H1;obtain ⟨_,b1,b2,hO,_,_,_,_,_,hR⟩:=qn hm p hfun hh ht d;rw[g] at hO;injection hO with hb1 hrest;injection hrest with hb2;subst hb1;subst hb2
      have n:∀b (hb:b< 2*m+t),
        ((a1=2*m+v/\a2=b)\/(a2=2*m+v/\a1=b)) ->
        (p0 C x (2*m+u)&&p0 C x b)=(p0 C x (2*m+v)&&p0 C x b):=by
       intro b hb Hm;have H8:(fun y=>p0 C y (2*m+v))=pP m c:=hX;have hY:∀j (hj:j< 2*m),(2*m+v)≠j:=fun j hj=>by O
       have a:∀i' k',k'< 2*m->(fun y=>p0 C y (2*m+v))≠qd m i' k' :=
        fun i' k' Hn Ho=>qj hH r Hn (H8.symm.trans Ho)
       have hD:b=c \/
         (∃i',i'%2=0/\i'+3< 2*m/\c=i'+2/\(fun y=>p0 C y b)=qd m i' (i'+2)) \/
         (∃i',i'%2=0/\i'+3< 2*m/\c=i'+1/\(fun y=>p0 C y b)=qd m (i'+2) (i'+1)):=by
        have H3:∀p1 p2,((p1=a1/\p2=a2)\/(p1=a2/\p2=a1)) ->
          p1=2*m+v->p2=b ->
          (∀j,j< 2*m->p1≠j) ->
          (∃c',1<=c'/\c'+1< 2*m/\p2=c'/\(fun y=>p0 C y p1)=pP m c') \/
          (∃i',i'%2=0/\i'+3< 2*m /\
           (((fun y=>p0 C y p1)=pP m (i'+2)/\(fun y=>p0 C y p2)=qd m i' (i'+2)) \/
            ((fun y=>p0 C y p1)=pP m (i'+1)/\(fun y=>p0 C y p2)=qd m (i'+2) (i'+1)))):=by
         intro p1 p2 Hc z Hu Hd;have s:(p1=a1/\p2=a2)\/(p1=a2/\p2=a1):=Hc
         rcases hR with
          ⟨e,he,_,⟨h1,h2⟩|⟨h1,h2⟩⟩ |
          ⟨c',hL,hM,_,⟨h1,h2⟩|⟨h2,h1⟩⟩ |
          ⟨i',_,H4,_,⟨h1,h2⟩|⟨h2,h1⟩⟩ |
          ⟨i',_,_,Hv,_,⟨h1,h2⟩|⟨h2,h1⟩⟩ |
          ⟨i',l,k,_,⟨h1,h2⟩|⟨h2,h1⟩|⟨h1,h2⟩|⟨h2,h1⟩|⟨h1,h2⟩|⟨h2,h1⟩⟩
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>O
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>O
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·O
          ·X il ⟨c',hL,hM,h1,h2⟩
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X il ⟨c',hL,hM,h2,h1⟩
          ·O
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·O
          ·X absurd (z▸h2) (a _ _ H4)
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X absurd (z▸h1) (a _ _ H4)
          ·O
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·O
          ·X absurd (z▸h2) (a _ _ W)
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X absurd (z▸h1) (a _ _ W)
          ·O
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X ir ⟨i',l,k,il ⟨h1,h2⟩⟩
          ·X absurd (z▸h2) (a _ _ W)
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X absurd (z▸h1) (a _ _ W)
          ·X ir ⟨i',l,k,il ⟨h2,h1⟩⟩
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X ir ⟨i',l,k,ir ⟨h1,h2⟩⟩
          ·X absurd (z▸h2) (a _ _ W)
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X absurd (z▸h1) (a _ _ W)
          ·X ir ⟨i',l,k,ir ⟨h2,h1⟩⟩
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X absurd (z▸h1) (a _ _ W)
          ·X absurd (z▸h2) (a _ _ W)
         ·rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          ·X absurd (z▸h1) (a _ _ W)
          ·X absurd (z▸h2) (a _ _ W)
        have hE:(∃c',1<=c'/\c'+1< 2*m/\b=c'/\(fun y=>p0 C y (2*m+v))=pP m c') \/
          (∃i',i'%2=0/\i'+3< 2*m /\
           (((fun y=>p0 C y (2*m+v))=pP m (i'+2)/\(fun y=>p0 C y b)=qd m i' (i'+2)) \/
            ((fun y=>p0 C y (2*m+v))=pP m (i'+1)/\(fun y=>p0 C y b)=qd m (i'+2) (i'+1)))):=by
         rcases Hm with ⟨h1,h2⟩|⟨h1,h2⟩
         ·simpa [h1,h2] using H3 a1 a2 (il ⟨rfl,rfl⟩) h1 h2 (fun j hj=>by O)
         ·simpa [h1,h2] using H3 a2 a1 (ir ⟨rfl,rfl⟩) h1 h2 (fun j hj=>by O)
        rcases hE with
         ⟨c',hL,hM,He,Hf⟩|⟨i',l,k,⟨h1,h2⟩|⟨h1,h2⟩⟩
        ·left;rw[He];X (zg hH r hL hM (H8.symm.trans Hf)).symm
        ·right;left;X ⟨i',l,k,zg hH r W k (H8.symm.trans h1),h2⟩
        ·right;right;X ⟨i',l,k,zg hH r W W (H8.symm.trans h1),h2⟩
       rw[show p0 C x (2*m+u)=qd m i k0 x from cf Hj x,
        show p0 C x (2*m+v)=pP m c x from cf hX x,
        qh hi hB,qe hH r]
       rcases hD with rfl|⟨i',l,k,Hg,Hh⟩|⟨i',l,k,Hg,Hh⟩
       ·rw[p7 C x b W]
        rcases q with ⟨hQ,Hg⟩|⟨Hb,Hg⟩
        ·have hT:(⟨b-1,by O⟩:Fin (2*m))=⟨i,by O⟩:=Fin.ext (by dsimp;O)
         have hU:(⟨b+1,r⟩:Fin (2*m))=⟨k0,hB⟩:=Fin.ext (by dsimp;O)
         have hV:(⟨b,by O⟩:Fin (2*m))=⟨i+1,hi⟩:=Fin.ext (by dsimp;O)
         rw[hT,hU,hV];cases x ⟨i,by O⟩<;>cases x ⟨i+1,hi⟩<;>cases x ⟨k0,hB⟩<;>rfl
        ·have hT:(⟨b-1,by O⟩:Fin (2*m))=⟨k0,hB⟩:=Fin.ext (by dsimp;O)
         have hU:(⟨b+1,r⟩:Fin (2*m))=⟨i+1,hi⟩:=Fin.ext (by dsimp;O)
         have hV:(⟨b,by O⟩:Fin (2*m))=⟨i,by O⟩:=Fin.ext (by dsimp;O)
         rw[hT,hU,hV];cases x ⟨k0,hB⟩<;>cases x ⟨i,by O⟩<;>cases x ⟨i+1,hi⟩<;>rfl
       ·rw[cf Hh x,qh W W]
        rcases q with ⟨_,hW⟩|⟨Hb,hW⟩
        ·O
        ·have hT:(⟨i,by O⟩:Fin (2*m))=⟨i'+2,by O⟩:=Fin.ext (by dsimp;O)
         have hU:(⟨c-1,by O⟩:Fin (2*m))=⟨i'+1,by O⟩:=Fin.ext (by dsimp;O)
         have hV:(⟨k0,hB⟩:Fin (2*m))=⟨i'+1,by O⟩:=Fin.ext (by dsimp;O)
         have Hi:(⟨c+1,r⟩:Fin (2*m))=⟨i+1,hi⟩:=Fin.ext (by dsimp;O)
         rw[hT,hU,hV,Hi]
         cases x ⟨i',by O⟩<;>cases x ⟨i'+1,by O⟩ <;>
          cases x ⟨i'+2,by O⟩<;>cases x ⟨i+1,hi⟩<;>rfl
       ·rw[cf Hh x,qh k W]
        rcases q with ⟨hQ,hW⟩|⟨_,hW⟩
        ·have hT:(⟨c-1,by O⟩:Fin (2*m))=⟨i,by O⟩:=Fin.ext (by dsimp;O)
         have hU:(⟨c+1,r⟩:Fin (2*m))=⟨i'+2,by O⟩:=Fin.ext (by dsimp;O)
         have hV:(⟨k0,hB⟩:Fin (2*m))=⟨i'+2,by O⟩:=Fin.ext (by dsimp;O)
         have Hi:(⟨i'+1,by O⟩:Fin (2*m))=⟨i+1,hi⟩:=Fin.ext (by dsimp;O)
         rw[hT,hU,hV,Hi]
         cases x ⟨i,by O⟩<;>cases x ⟨i+1,hi⟩ <;>
          cases x ⟨i'+2,by O⟩<;>cases x ⟨i'+2+1,k⟩<;>rfl
        ·O
      rcases H1 with rfl|rfl
      ·rw[qs C x v hv _,ih a2 W W hN.symm]
       X n a2 hJ (il ⟨rfl,rfl⟩)
      ·rw[qs C x v hv _,ih a1 W W hN,Bool.and_comm]
       conv_rhs=>rw[Bool.and_comm]
       X n a1 hI (ir ⟨rfl,rfl⟩)
     ·have hF:a1≠2*m+v:=fun h=>H7 ⟨by rcases f with H5|H5<;>simp[pa,H5,g,h],h▸hI⟩
      have hG:a2≠2*m+v:=fun h=>H7 ⟨by rcases f with H5|H5<;>simp[pa,H5,g,h],h▸hJ⟩
      rcases f with hop_eq|hop_eq
      ·rw[pF x hv _ ht W hop_eq g hI hJ,
        pm x ht hop_eq g hI hJ,
        ih a1 W W hF,ih a2 W W hG]
      ·rw[pJ x hv _ ht W hop_eq g hI hJ,
        p6 x ht hop_eq g hI hJ,
        ih a1 W W hF,ih a2 W W hG]
 have H6:cF (2*m) (qQ C (2*m) v (2*m+u))=cF (2*m) C:=funext fun x=>by
  rw[z7 C x v (2*m+u) hv (il W),if_pos W];X hK x C.output (pB H9) (jn hfun ⟨c,hH,r,hX⟩)
 have Hp:=p.2 _ (qS C p.1 (2*m) v (2*m+u)) H6;rw[zn C (2*m) v (2*m+u) hv] at Hp;O
private lemma jY {m:ℕ} (hm:1<=m) {C:J}
  (d:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (b:qf m C) {v:ℕ} (hv:v< C.size) (f:zM m (p8 C v)) :
  (C.gates[v]'hv).op=.or/\∃a1 a2,(C.gates[v]'hv).inputs=[a1,a2]/\a1< 2*m/\a2< 2*m:=by
 have r:∃x1 x2:Fin (2*m)->Bool,cF (2*m) C x1≠cF (2*m) C x2:=by
  rw[hfun];X ps W
 obtain ⟨c,h,i,j⟩:=f;rcases pc d r v hv with ⟨l,_,_,_⟩|⟨e,a1,a2,g,s,t,_⟩
 ·X absurd l (b.1 _ (List.getElem_mem hv))
 ·rcases e with hop_and|a
  ·exfalso;obtain ⟨⟨S,_,_,hS⟩,_⟩:=qn hm d hfun b hv hop_and
   X z6 h i (hS.symm.trans j)
  ·have q:∀z,z< 2*m+v->(z=a1\/z=a2)->z< 2*m:=by
    intro z hz u;by_contra x;set gz:=z-2*m;have k:gz< C.size :=W
    have n:pC (2*m) v (2*m+gz) (C.gates[v]'hv) :=
     ⟨by simp[pa,a,g,show 2*m+gz=z by O,u],by O⟩
    rcases b.2 gz k with heo|hst|htb
    ·rcases (pQ hm d hfun b k hv heo n).2 with ⟨S,_,_,hS⟩|⟨_,k',_,_,w,_,p⟩
     ·X z6 h i (hS.symm.trans j)
     ·X qj h i w (j.symm.trans p)
    ·X zI hm d hfun b k hv hst n a
    ·X jc hm d hfun b k hv htb ⟨c,h,i,j⟩ n
   X ⟨a,a1,a2,g,q a1 s (il rfl),q a2 t (ir rfl)⟩
private lemma qr {m:ℕ} (hm:1<=m) {C:J}
  (p:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (q:qf m C) {v r i k:ℕ} (hv:v< C.size) (hr:r< C.size)
  (hN:i%2=0) (hi:i+1< 2*m) (hk:k< 2*m) (t:k=i+2\/k+1=i)
  (z:p8 C v=qd m i k) (f:pC (2*m) r (2*m+v) (C.gates[r]'hr)) :
  (C.gates[r]'hr).op=.and /\
  ((k=i+2 /\
    ((p8 C r=ph m {i,i+1} /\
     ((C.gates[r]'hr).inputs=[2*m+v,i+1]\/(C.gates[r]'hr).inputs=[i+1,2*m+v])) \/
     (i+3< 2*m/\p8 C r=ph m {i,i+1,i+2}))) \/
   (k+1=i /\
    ((p8 C r=ph m {i-1,i} /\
     ((C.gates[r]'hr).inputs=[2*m+v,i]\/(C.gates[r]'hr).inputs=[i,2*m+v])) \/
     (2<=i/\p8 C r=ph m {i-2,i-1,i})))):=by
 have hO:∃x1 x2:Fin (2*m)->Bool,cF (2*m) C x1≠cF (2*m) C x2:=by
  rw[hfun];X ps W
 have g:(C.gates[r]'hr).op=.and:=by
  rcases pc p hO r hr with ⟨hE,_,_,_⟩|⟨u,a1,a2,l,hH,hI,_⟩
  ·X absurd hE (q.1 _ (List.getElem_mem hr))
  ·rcases u with h|hop_or
   ·X h
   ·exfalso
    have n:=f.1;simp only[pa,hop_or,l,List.mem_cons,List.not_mem_nil,or_false] at n
    have hJ:∀x:Fin (2*m)->Bool,qd m i k x=true->p8 C r x=true:=fun x hx=>by
     change p0 C x (2*m+r)=true;rw[p6 x hr hop_or l hH hI,Bool.or_eq_true];have hK:p0 C x (2*m+v)=true:=by rw[show p0 C x (2*m+v)=qd m i k x from cf z x];X hx
     rcases n with rfl|rfl<;>[X il hK;X ir hK]
    rcases q.2 r hr with ⟨S,_,_,j⟩|hst|⟨i',k',w,hh,hF,hP,j⟩
    ·have h1:=hJ (e1 k) ((pN hk hk).2 rfl)
     rw[cf j _,pz] at h1;cases h1
    ·X jc hm p hfun q hv hr ⟨i,k,hN,hi,hk,t,z⟩ hst f
    ·have hA:k=k':=(pN hF hk).1 ((cf j _).symm.trans (hJ (e1 k) ((pN hk hk).2 rfl)))
     have hB:i'=i:=by rcases t with hk0e|hki<;>rcases hP with h'|h'<;>O
     subst hA;subst hB;X qy p hr hv (by have:=f.2;O) (j.trans z.symm)
 Y ⟨g,?_⟩;obtain ⟨_,a1,a2,l,hH,hI,_,_,_,y⟩:=qn hm p hfun q hr g;have n:=f.1;simp only[pa,g,l,List.mem_cons,List.not_mem_nil,or_false] at n
 have b:∀c,1<=c->c+1< 2*m->p8 C v≠pP m c:=fun c h1 h2 hG=>
  qj h1 h2 hk (hG.symm.trans z)
 have a:∀i' k',i'+1< 2*m->k'< 2*m->p8 C v=qd m i' k'->i=i'/\k=k' :=
  fun i' k' hh hF hG=>kG hi hk t hh hF (z.symm.trans hG)
 rcases y with
  ⟨e,he,_,⟨h1,h2⟩|⟨h1,h2⟩⟩ |
  ⟨c,hL,hM,_,⟨h1,h2⟩|⟨h2,h1⟩⟩ |
  ⟨i',w,hC,j,⟨h1,h2⟩|⟨h2,h1⟩⟩ |
  ⟨i',w,hQ,hh,j,⟨h1,h2⟩|⟨h2,h1⟩⟩ |
  ⟨i',w,d,j,hD⟩
 ·rcases n with rfl|rfl<;>O
 ·rcases n with rfl|rfl<;>O
 ·rcases n with rfl|rfl
  ·O
  ·X absurd h2 (b c hL hM)
 ·rcases n with rfl|rfl
  ·X absurd h1 (b c hL hM)
  ·O
 ·rcases n with rfl|rfl
  ·O
  ·obtain ⟨rfl,rfl⟩:=a i' (i'+2) W hC h2
   left;X ⟨rfl,il ⟨j,ir (by rw[l,h1])⟩⟩
 ·rcases n with rfl|rfl
  ·obtain ⟨rfl,rfl⟩:=a i' (i'+2) W hC h1
   left;X ⟨rfl,il ⟨j,il (by rw[l,h2])⟩⟩
  ·O
 ·rcases n with rfl|rfl
  ·O
  ·obtain ⟨rfl,rfl⟩:=a i' (i'-1) hh W h2
   right;X ⟨by O,il ⟨j,ir (by rw[l,h1])⟩⟩
 ·rcases n with rfl|rfl
  ·obtain ⟨rfl,rfl⟩:=a i' (i'-1) hh W h1
   right;X ⟨by O,il ⟨j,il (by rw[l,h2])⟩⟩
  ·O
 ·have s:ph m {i',i'+1,i'+2}=ph m {i'+2-2,i'+2-1,i'+2}:=rfl
  rcases hD with ⟨h1,h2⟩|⟨h2,h1⟩|⟨h1,h2⟩|⟨h2,h1⟩|⟨h1,h2⟩|⟨h2,h1⟩ <;>
  (rcases n with rfl|rfl)
  ·X absurd h1 (b (i'+2) W d)
  ·obtain ⟨rfl,rfl⟩:=a i' (i'+2) W W h2;X il ⟨rfl,ir ⟨d,j⟩⟩
  ·obtain ⟨rfl,rfl⟩:=a i' (i'+2) W W h1;X il ⟨rfl,ir ⟨d,j⟩⟩
  ·X absurd h2 (b (i'+2) W d)
  ·X absurd h1 (b (i'+1) W W)
  ·obtain ⟨rfl,rfl⟩:=a (i'+2) (i'+1) d W h2;X ir ⟨rfl,ir ⟨by O,j.trans s⟩⟩
  ·obtain ⟨rfl,rfl⟩:=a (i'+2) (i'+1) d W h1;X ir ⟨rfl,ir ⟨by O,j.trans s⟩⟩
  ·X absurd h2 (b (i'+1) W W)
  ·obtain ⟨rfl,rfl⟩:=a i' (i'+2) W W h1;X il ⟨rfl,ir ⟨d,j⟩⟩
  ·obtain ⟨rfl,rfl⟩:=a (i'+2) (i'+1) d W h2;X ir ⟨rfl,ir ⟨by O,j.trans s⟩⟩
  ·obtain ⟨rfl,rfl⟩:=a (i'+2) (i'+1) d W h1;X ir ⟨rfl,ir ⟨by O,j.trans s⟩⟩
  ·obtain ⟨rfl,rfl⟩:=a i' (i'+2) W W h2;X il ⟨rfl,ir ⟨d,j⟩⟩
private lemma qU {m:ℕ} (hm:1<=m) {C:J}
  (c:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (f:qf m C) {v w e1 e2 e3:ℕ} (hv:v< C.size) (hw:w< C.size)
  (hC:e1+1< 2*m) (hD:e2+1< 2*m) (hE:e3+1< 2*m)
  (hM:e1≠e2) (hN:e1≠e3) (hO:e2≠e3)
  (j:q1 m (p8 C v))
  (h1:p8 C v (pe e1:Fin (2*m)->Bool)=true) (h2:p8 C v (pe e2:Fin (2*m)->Bool)=true)
  (h3:p8 C v (pe e3:Fin (2*m)->Bool)=true)
  (b:pC (2*m) w (2*m+v) (C.gates[w]'hw)) :
  ¬qb m (p8 C w):=by
 rintro ⟨iw,kw,g,n,p,q,s⟩
 obtain ⟨_,uw,_,Suw,_,i,_,a,d,t⟩ :=
  qB hm c hfun f hw g n p q s
 have u:v=uw:=by
  have hF:=b.1;have y:=(pQ hm c hfun f hv hw j b).1;rcases t with h|h<;>(simp only[pa,y,h,List.mem_cons,List.not_mem_nil,or_false] at hF;O)
 subst u;have hG:e1∈Suw:=(pg i hC).1 (by rw[←cf d _];X h1)
 have hH:e2∈Suw:=(pg i hD).1 (by rw[←cf d _];X h2)
 have hI:e3∈Suw:=(pg i hE).1 (by rw[←cf d _];X h3)
 have k:∀e,(e=iw\/e=kw\/e+1=kw)->e∈Suw:=fun e he=>by
  have:=a e1 hG;have:=a e2 hH;have:=a e3 hI
  have:e=e1\/e=e2\/e=e3 :=W
  rcases this with rfl|rfl|rfl<;>assumption
 rcases pY c w hw with hout|⟨r,hr,hP,hJ⟩
 ·X qz hfun ⟨iw,kw,g,n,p,q,s⟩ hout
 ·obtain ⟨_,hK⟩:=qr hm c hfun f hw hr g n p q s hJ
  X qG c f.1 r hr (2*m+v) (by have:=b.2;O) (fun x hx=>by
   change p8 C v x=true;rw[cf d x,po]
   rcases hK with ⟨z,⟨l,_⟩|⟨_,l⟩⟩|⟨z,⟨l,_⟩|⟨_,l⟩⟩ <;>
    (rw[cf l x,po] at hx;obtain ⟨p',q',hL,hh,hA,hB⟩:=hx;
     X ⟨p',q',k p'.val (by simp only[Finset.mem_insert,Finset.mem_singleton] at hL;O),hh,hA,hB⟩))
   (fun x hx=>by rw[hfun];X pT (by rw[←cf d x];X hx))
private lemma ji {m:ℕ} (hm:1<=m) {C:J}
  (j:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (p:qf m C) {kv a v w i0 k0 e0:ℕ}
  (hN:kv< a) (ha:a<=v) (hv:v< C.size) (hw:w< C.size)
  (hG:i0%2=0) (hO:i0+1< 2*m) (hP:k0< 2*m) (hH:k0=i0+2\/k0+1=i0)
  (hF:(k0=i0+2/\e0=i0)\/(k0+1=i0/\e0=k0))
  (hh:p8 C kv=qd m i0 k0)
  (d:∀x:Fin (2*m)->Bool,ph m {e0,e0+1} x=true->p8 C v x=true)
  (k:q1 m (p8 C v))
  (b:pC (2*m) w (2*m+v) (C.gates[w]'hw)) :
  ¬qb m (p8 C w):=by
 rintro ⟨i',k',s,r,z,hA,t⟩
 have hQ:v< w:=by have:=b.2;O
 obtain ⟨hB,_,f⟩:=pQ hm j hfun p hv hw k b;obtain ⟨_,u,_,Su,_,hI,y,hC,hJ,hD⟩:=qB hm j hfun p hw s r z hA t;have c:e0+2< 2*m:=by rcases hF with ⟨hE,q⟩|⟨hK,q⟩<;>O
 have hL:v=u:=by
  have hM:=b.1;rcases hD with h|h<;>(simp only[pa,hB,h,List.mem_cons,List.not_mem_nil,or_false] at hM;O)
 subst hL;have l:p8 C v (pe e0)=true:=d _ (by rw[zu,pv W];simp[pe,e2])
 have n:p8 C v (pe (e0+1))=true:=d _ (by rw[zu,pv c];simp[pe,e2])
 have hR:=(qo (e:=e0) r z W).1 (by rw[←cf t _];X f _ l)
 have hS:=(qo (e:=e0+1) r z c).1 (by rw[←cf t _];X f _ n)
 have g:¬(i'=i0/\k'=k0):=by
  rintro ⟨rfl,rfl⟩;X qy j hw (by O:kv< C.size) W (t.trans hh.symm)
 have i:i'≠e0/\i'≠e0+1:=by
  rcases hF with ⟨hE,q⟩|⟨hK,q⟩<;>rcases hA with h'|h'
  ·X absurd ⟨by O,by O⟩ g
  ·constructor<;>O
  ·constructor<;>O
  ·X absurd ⟨by O,by O⟩ g
 X qU hm j hfun p hv hw W c r
  W i.1.symm i.2.symm k l n
  (by rw[cf hJ _];X (pg hI r).2 y) b ⟨i',k',s,r,z,hA,t⟩
private lemma zo {m:ℕ} (hm:1<=m) {C D:J}
  (n:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m))
  (z:qf m C) (p:D.size=C.size) (hh:D.output=C.output)
  {kv a skip i0 k0 e0 e:ℕ} (hL:kv< a) (ha:a< C.size) (g:skip< D.size)
  (q:∀t (ht:t< C.size),a<=t->D.gates[t]'(by change t< D.size;rw[p];X ht)=C.gates[t]'ht)
  (hF:i0%2=0) (hM:i0+1< 2*m) (hN:k0< 2*m) (hG:k0=i0+2\/k0+1=i0)
  (hO:(k0=i0+2/\e0=i0)\/(k0+1=i0/\e0=k0))
  (hH:p8 C kv=qd m i0 k0)
  (hA:q1 m (p8 C a))
  (r:∀x:Fin (2*m)->Bool,ph m {e0,e0+1} x=true->p8 C a x=true)
  {v0:Bool}
  (s:pl D (pe e:Fin (2*m)->Bool) skip v0 (2*m+a)=true)
  (h:∀v (hv:v< C.size),a<=v->q1 m (p8 C v) ->
   pl D (pe e:Fin (2*m)->Bool) skip v0 (2*m+v)=true ->
   pC (2*m) skip (2*m+v) (C.gates[skip]'(by change skip< C.size;rw[←p];X g))->v0=true) :
  pl D (pe e:Fin (2*m)->Bool) skip v0 D.output=true:=by
 classical
 let P:ℕ->Prop:=fun v=>∃(hv:v< C.size),a<=v/\q1 m (p8 C v) /\
  (∀x:Fin (2*m)->Bool,ph m {e0,e0+1} x=true->p8 C v x=true) /\
  pl D (pe e:Fin (2*m)->Bool) skip v0 (2*m+v)=true
 set Sset:=(Finset.range C.size).filter P;have i:a∈Sset:=Finset.mem_filter.2 ⟨Finset.mem_range.2 ha,ha,le_rfl,hA,r,s⟩;set vmax:=Sset.max' ⟨a,i⟩;obtain ⟨f,hI,j,k,b⟩:=(Finset.mem_filter.1 (Finset.max'_mem Sset ⟨a,i⟩)).2;rcases pY n vmax f with hout|⟨w,hw,hT,c⟩
 ·rw[hh,hout];X b
 ·exfalso
  obtain ⟨d,l,u⟩:=pQ hm n hfun z f hw j c
  have hB:q1 m (p8 C w):=l.resolve_right
   (ji hm n hfun z hL hI f hw hF hM hN hG hO hH k j c)
  have y:pl D (pe e:Fin (2*m)->Bool) skip v0 (2*m+w)=true:=by
   by_cases hJ:w=skip
   ·subst hJ;rw[qs D _ w g v0];X h vmax f hI j b c
   ·have hP:∃x1 x2:Fin (2*m)->Bool,cF (2*m) C x1≠cF (2*m) C x2:=by
     rw[hfun];X ps W
    rcases pc n hP w hw with ⟨hC,_,_,_⟩|⟨_,a1,a2,hD,hQ,hR,_⟩
    ·rw[d] at hC;cases hC
    ·have hS:w< D.size:=by rw[p];X hw
     have hE:=q w hw W;rw[pJ _ g v0 hS hJ (hE.symm▸d) (hE.symm▸hD) hQ hR,Bool.or_eq_true];have hK:=c.1;simp only[pa,d,hD,List.mem_cons,List.not_mem_nil,or_false] at hK;rcases hK with rfl|rfl<;>[X il b;X ir b]
  have hU:=Finset.le_max' Sset w (Finset.mem_filter.2 ⟨Finset.mem_range.2 hw,hw,by O,hB,fun x hx=>u x (k x hx),y⟩)
  O
private lemma jH {m:ℕ} (hm:1<=m) {d:J}
  (f:IsMinimalCircuit (2*m+1) d) (hO:z0 d)
  (hC:∃x1 x2:Fin (2*m+1)->Bool,cF (2*m+1) d x1≠cF (2*m+1) d x2)
  (q:IsMinimalCircuit (2*m) (p3 d (2*m) false))
  (r:cF (2*m) (p3 d (2*m) false)=pq (2*m))
  (e:qf m (p3 d (2*m) false))
  {hP g:ℕ} (Hd:hP< d.size) (hI:g< (p3 d (2*m) false).size)
  (hh:∀k (hk:k< d.size),pC (2*m+1) k (2*m) (d.gates[k]'hk)↔k=hP)
  (n:∀k (hk:k< d.size),(p5 d (2*m) false).fb[k]'(by rw[(pk d (2*m) false f.1).kept_len];X hk)=false↔k=hP)
  (hJ:(p5 d (2*m) false).fc.getD (2*m+1+hP) (.const false)=.wire (2*m+g))
  (s:q1 m (p8 (p3 d (2*m) false) g))
  {K:ℕ} (hK:K<=d.size)
  (hQ:∀k (hk:k< K),p0 d (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true->(d.gates[k]'(by change k< d.size;O)).op=.or) :
  ∀w,w< 2*m+1+K->w≠2*m ->
   p0 d (e1 (2*m):Fin (2*m+1)->Bool) w=true ->
   ∃w''',w'''< 2*m+(p3 d (2*m) false).size /\
    (p5 d (2*m) false).fc.getD w (.const false)=.wire w''' /\
    (∀y:Fin (2*m)->Bool,p8 (p3 d (2*m) false) g y=true->p0 (p3 d (2*m) false) y w'''=true) /\
    (q1 m (fun y=>p0 (p3 d (2*m) false) y w''') \/
     qb m (fun y=>p0 (p3 d (2*m) false) y w''')):=by
 set hR:=p5 d (2*m) false;set hA:=p3 d (2*m) false;intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  intro hw He hL;by_cases Hf:w< 2*m+1
  ·rw[p7 d _ w Hf] at hL;simp[e1,He] at hL
  ·set k:=w-(2*m+1);have hk:k< d.size :=W
   have hT:w=2*m+1+k :=W;rw[hT] at hL ⊢;by_cases H0:k=hP
   ·subst H0;X ⟨2*m+g,Nat.add_lt_add_left hI _,hJ,fun _ hy=>hy,il s⟩
   ·have t:(d.gates[k]'hk).op=.or:=hQ k W hL
    have hD:=q4 f.1 n hk H0;obtain ⟨v,l,_,hE,H1,H2,_⟩:=p4 f.1 hk hD;rcases pc f hC k hk with ⟨hU,_,_,_⟩|⟨_,a1,a2,hB,H3,H4,_⟩
    ·rw[t] at hU;cases hU
    ·obtain ⟨w1,w2,Hg,Hh,Hb,Hc,H5⟩:=H2 .or a1 a2 (ir rfl) t hB H3 H4
     have hV:∀b,(b=a1\/b=a2)->b< 2*m+1+k->b≠2*m:=fun b hW Hi h=>
      H0 ((hh k hk).1 ⟨by rcases hW with rfl|rfl<;>simp[pa,t,hB,h],h▸Hi⟩)
     rw[p6 _ hk t hB H3 H4,Bool.or_eq_true] at hL
     have hF:∀a wa,(a=a1\/a=a2)->a< 2*m+1+k ->
       hR.fc.getD a (.const false)=.wire wa ->
       p0 d (e1 (2*m):Fin (2*m+1)->Bool) a=true ->
       (∀y:Fin (2*m)->Bool,p8 hA g y=true->p0 hA y (2*m+v)=true) /\
       (q1 m (p8 hA v)\/qb m (p8 hA v)):=by
      intro a wa hW hX u Hj;obtain ⟨Hk,_,hG,hH,x⟩:=ih a W W (hV a hW hX) Hj;rw[u] at hG;cases hG
      Y ⟨fun y hy=>by
       rw[p6 y l (H1.trans t) H5 Hg Hh,Bool.or_eq_true];rcases hW with rfl|rfl
       ·rw[Hb] at u;cases u;X il (hH y hy)
       ·rw[Hc] at u;cases u;X ir (hH y hy),?_⟩
      rcases e.2 v l with h1|hst|h3
      ·X il h1
      ·exfalso
       have p:=pp f hO hC hk hD l hE
        ⟨by rcases hW with rfl|rfl<;>simp[pa,t,hB],hX⟩ u
       rcases qE e wa (by have:=p.2;O) with
        ⟨j,hj,_,z⟩|⟨ka,H6,rfl,H7⟩|⟨_,_,_,c,hM,hN,z⟩|⟨ka,H6,rfl,H8⟩
       ·rcases x with ⟨S,_,_,hS⟩|⟨i,k0,_,hi,hY,H9,hZ⟩
        ·X zv hj (hS.symm.trans z)
        ·X zw hi hY H9 hj (hZ.symm.trans z)
       ·rcases (pQ hm q r e H6 l H7 p).2.1 with ⟨S,_,_,hS⟩|⟨_,k0,_,_,hY,_,hZ⟩
        ·obtain ⟨c,hM,hN,Ha⟩:=hst;X z6 hM hN (hS.symm.trans Ha)
        ·obtain ⟨c,hM,hN,Ha⟩:=hst;X qj hM hN hY (Ha.symm.trans hZ)
       ·rcases x with ⟨S,_,_,hS⟩|⟨_,k0,_,_,hY,_,hZ⟩
        ·X z6 hM hN (hS.symm.trans z)
        ·X qj hM hN hY (z.symm.trans hZ)
       ·X jc hm q r e H6 l H8 hst p
      ·X ir h3
     Y ⟨2*m+v,Nat.add_lt_add_left l _,hE,?_⟩;rcases hL with h1|h2
     ·X hF a1 w1 (il rfl) H3 Hb h1
     ·X hF a2 w2 (ir rfl) H4 Hc h2
private lemma jZ {m:ℕ} (hm:1<=m) {hC:J}
  (hh:IsMinimalCircuit (2*m+1) hC) (Hr:z0 hC)
  (Hg:∃x1 x2:Fin (2*m+1)->Bool,cF (2*m+1) hC x1≠cF (2*m+1) hC x2)
  (f:IsMinimalCircuit (2*m) (p3 hC (2*m) false))
  (l:cF (2*m) (p3 hC (2*m) false)=pq (2*m))
  (n:qf m (p3 hC (2*m) false))
  {_c kz''':ℕ} (_E:_c< hC.size) (_d:kz'''< (p3 hC (2*m) false).size)
  (hI:∀k (hk:k< hC.size),pC (2*m+1) k (2*m) (hC.gates[k]'hk)↔k=_c)
  (hE:∀k (hk:k< hC.size),(p5 hC (2*m) false).fb[k]'(by rw[(pk hC (2*m) false hh.1).kept_len];X hk)=false↔k=_c)
  (_F:(hC.gates[_c]'_E).op=.or)
  (Hs:(p5 hC (2*m) false).fc.getD (2*m+1+_c) (.const false)=.wire (2*m+kz'''))
  (Hn:q1 m (p8 (p3 hC (2*m) false) kz''')) :
  ∀k (hk:k< hC.size),p0 hC (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true ->
   (hC.gates[k]'hk).op=.or:=by
 set Ht:=p5 hC (2*m) false;set b:=p3 hC (2*m) false
 have hT:∃y1 y2:Fin (2*m)->Bool,cF (2*m) b y1≠cF (2*m) b y2:=by
  rw[l];X ps W
 obtain ⟨Sz,HZ,hSz,hF⟩:=Hn
 by_contra HP;push Not at HP;classical
 obtain ⟨k0,Hu,h07,HQ⟩:=HP
 let Q:ℕ->Prop:=fun k=>∃(hk:k< hC.size),
  p0 hC (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true/\(hC.gates[k]'hk).op≠.or
 set Sbad:=(Finset.range hC.size).filter Q;have Hh:k0∈Sbad:=Finset.mem_filter.2 ⟨Finset.mem_range.2 Hu,Hu,h07,HQ⟩;set k:=Sbad.min' ⟨k0,Hh⟩;obtain ⟨hk,_e,_f⟩:=(Finset.mem_filter.1 (Finset.min'_mem Sbad ⟨k0,Hh⟩)).2
 have Hv:∀j (hj:j< k),p0 hC (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+j)=true ->
   (hC.gates[j]'(by change j< hC.size;O)).op=.or:=fun j hj hUj=>by_contra fun hY=>by
  have:=Finset.min'_le Sbad j (Finset.mem_filter.2 ⟨Finset.mem_range.2 W,by O,hUj,hY⟩);O
 have z:(hC.gates[k]'hk).op=.and:=by
  rcases pc hh Hg k hk with ⟨hP,_,_,_⟩|⟨h|h,_,_,_,_,_,_⟩
  ·X absurd hP (Hr _ (List.getElem_mem hk))
  ·X h
  ·X absurd h _f
 have hkq:k≠_c:=fun h=>by subst h;rw[_F] at z;cases z
 have _G:=q4 hh.1 hE hk hkq;obtain ⟨d,s,_,h0p,_H,h08,_⟩:=p4 hh.1 hk _G;have _I:d< b.size:=s;rcases pc hh Hg k hk with ⟨hP,_,_,_⟩|⟨_,a1,a2,HR,_A,_B,_⟩
 ·X absurd hP (Hr _ (List.getElem_mem hk))
 ·obtain ⟨w1,w2,hw1,hw2,he1,he2,_J⟩:=h08 .and a1 a2 (il rfl) z HR _A _B
  rw[pm _ hk z HR _A _B,Bool.and_eq_true] at _e;have H5:a1≠2*m:=fun h=>hkq ((hI k hk).1 ⟨by simp[pa,z,HR,h],h▸_A⟩)
  have H6:a2≠2*m:=fun h=>hkq ((hI k hk).1 ⟨by simp[pa,z,HR,h],h▸_B⟩)
  have HS:=jH hm hh Hr Hg f l n _E _d hI hE Hs ⟨Sz,HZ,hSz,hF⟩ (Nat.le_of_lt hk) Hv;obtain ⟨w1',_,_K,h0v,_L⟩:=HS a1 _A H5 _e.1;obtain ⟨w2',_,_M,h0w,_N⟩:=HS a2 _B H6 _e.2;rw[he1] at _K;cases _K;rw[he2] at _M;cases _M
  obtain ⟨_,b1,b2,_0,_,_,_,Hi,Hj,_g⟩ :=
   qn hm f l n s (_H.trans z)
  rw[_J] at _0;injection _0 with hb1 hrest;injection hrest with hb2;subst hb1;subst hb2;have _h:qb m (fun y=>p0 b y w1):=_L.resolve_left Hi;have _i:qb m (fun y=>p0 b y w2):=_N.resolve_left Hj
  have _1:∀w (hw:w< 2*m+d),qb m (fun y=>p0 b y w) ->
    ∃g,g< b.size/\g< d/\w=2*m+g:=fun w hw ⟨_,k0,_,hi0,Hu,hr0,hf⟩=>by
   have hge:2*m<=w:=by_contra fun _2=>zw hi0 Hu hr0 W
    (hf.symm.trans (funext fun y=>p7 b y w W))
   X ⟨w-2*m,by O,by O,by O⟩
  obtain ⟨_O,_P,Hw,_j⟩:=_1 w1 hw1 _h;obtain ⟨_Q,_R,Hx,_k⟩:=_1 w2 hw2 _i;subst _j;subst _k
  have hJ:∀w,qb m (fun y=>p0 b y w) ->
    ∀c,1<=c->c+1< 2*m->(fun y=>p0 b y w)≠pP m c :=
   fun _ ⟨_,k0,_,_,Hu,_,hf⟩ c H7 H8 heq=>qj H7 H8 Hu (heq.symm.trans hf)
  obtain ⟨i,_3,HT,hA,g1,g2,_4,_5,Hy,Hz,hL,hM,h09⟩ :
    ∃i,i%2=0/\i+3< 2*m/\p8 b d=ph m {i,i+1,i+2} /\
    ∃g1 g2,g1< b.size/\g2< b.size/\g1< d/\g2< d /\
     p8 b g1=qd m i (i+2)/\p8 b g2=qd m (i+2) (i+1) /\
     ((_O=g1/\_Q=g2)\/(_O=g2/\_Q=g1)):=by
   rcases _g with
    ⟨_,_,_,⟨h1,_⟩|⟨h1,_⟩⟩|⟨c,H7,H8,_,⟨h1,_⟩|⟨_,h1⟩⟩ |
    ⟨_,_,_,_,⟨h1,_⟩|⟨_,h1⟩⟩|⟨_,_,_,_,_,⟨h1,_⟩|⟨_,h1⟩⟩ |
    ⟨i',_S,_T,H9,⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,_⟩|⟨h1,h2⟩|⟨h2,h1⟩⟩
   ·O
   ·O
   ·O
   ·O
   ·O
   ·O
   ·O
   ·O
   ·X absurd h1 (hJ _ _h (i'+2) W W)
   ·X absurd h1 (hJ _ _i (i'+2) W W)
   ·X absurd h1 (hJ _ _h (i'+1) W W)
   ·X absurd h1 (hJ _ _i (i'+1) W W)
   ·X ⟨i',_S,_T,H9,_O,_Q,_P,_R,Hw,Hx,h1,h2,il ⟨rfl,rfl⟩⟩
   ·X ⟨i',_S,_T,H9,_Q,_O,_R,_P,Hx,Hw,h2,h1,ir ⟨rfl,rfl⟩⟩
  obtain ⟨_,u1,Ha,S1,h0q,hS1,_l,hU,HA,HB⟩ :=
   qB hm f l n _4 _3 W W (il rfl) hL
  obtain ⟨_,u2,Hb,S2,h0r,hS2,HC,hV,Ho,HD⟩ :=
   qB hm f l n _5 W HT W (ir W) hM
  have hG:∀(g:ℕ) (hg:g< b.size) (ig kg:ℕ) (_U:ig%2=0) (hig:ig+1< 2*m) (hkg:kg< 2*m)
    (hrg:kg=ig+2\/kg+1=ig) (hgf:p8 b g=qd m ig kg) (r:ℕ) (hr:r< b.size)
    (hH:pC (2*m) r (2*m+g) (b.gates[r]'hr)) (HE:r≠d)
    (HF:(ig=i/\kg=i+2)\/(ig=i+2/\kg=i+1)),
    r< d/\p8 b r=ph m (if ig=i then {i,i+1} else {i+1,i+2}):=by
   intro g hg ig kg _U hig hkg hrg hgf r hr hH HE HF;obtain ⟨_,hrc⟩:=qr hm f l n hg hr _U hig hkg hrg hgf hH
   have Hc:p8 b r=ph m (if ig=i then {i,i+1} else {i+1,i+2}) \/
     p8 b r=ph m {i,i+1,i+2}:=by
    rcases HF with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    ·rcases hrc with ⟨_,⟨H9,_⟩|⟨_,H9⟩⟩|⟨HP,_⟩
     ·X il (by simpa using H9)
     ·X ir H9
     ·O
    ·rcases hrc with ⟨HP,_⟩|⟨_,⟨H9,_⟩|⟨_,H9⟩⟩
     ·O
     ·X il (by rw[if_neg W,H9];congr 1)
     ·X ir (by rw[H9];congr 1)
   rcases Hc with H9|H9
   ·Y ⟨by_contra fun hge=>qG f n.1 r hr (2*m+d) W
     (fun x hx=>by
      rw[cf H9 x,po] at hx;rw[show p0 b x (2*m+d)=ph m {i,i+1,i+2} x from cf hA x,po];obtain ⟨p,q,hp,hpq,hxp,hxq⟩:=hx;X ⟨p,q,by split_ifs at hp<;>(simp only[Finset.mem_insert,Finset.mem_singleton] at hp ⊢;O),hpq,hxp,hxq⟩)
     (fun x hx=>by rw[l];X pT (by rw[←cf hA x];X hx)),H9⟩
   ·X absurd (H9.trans hA.symm) (qy f hr s HE)
  have hB:∀(g:ℕ) (hg:g< b.size) (gtb:qb m (p8 b g))
    (_6:∀r (hr:r< b.size),pC (2*m) r (2*m+g) (b.gates[r]'hr)->r=d)
    (gNew:Gate) (hZ:Ok gNew) (H0:¬pC (2*m) d (2*m+g) gNew)
    (H1:∀x:Fin (2*m)->Bool,p0 (pU b d gNew) x (2*m+d)=p8 b d x),
    False:=by
   intro g hg gtb _6 gNew hZ H0 H1;set D:=pU b d gNew
   have _V:=qC f gNew hZ (funext fun x=>
    qv b s gNew x (H1 x) b.output (pB hT))
   rcases pY _V g (by rw[pS];X hg) with hout|⟨r,hr,_,hH⟩
   ·X qz l gtb hout
   ·have _m:r< b.size:=by rw[←pS b d gNew];X hr
    by_cases HE:r=d
    ·subst HE;X H0 ((List.getElem_set_self _:D.gates[r]'hr=gNew)▸hH)
    ·X HE (_6 r _m ((List.getElem_set_ne (Ne.symm HE) _:D.gates[r]'hr=b.gates[r]'_m)▸hH))
  by_cases Hp:∃r1,∃(hr1:r1< b.size),r1≠d/\pC (2*m) r1 (2*m+g1) (b.gates[r1]'hr1)
  ·obtain ⟨r1,hr1,_n,h0a⟩:=Hp
   obtain ⟨h0b,HG⟩:=hG g1 _4 i (i+2) _3 W W (il rfl) hL r1 hr1 h0a _n (il ⟨rfl,rfl⟩);simp only[↓reduceIte] at HG;by_cases H2:∃r2,∃(_7:r2< b.size),r2≠d/\pC (2*m) r2 (2*m+g2) (b.gates[r2]'_7)
   ·
    obtain ⟨r2,_7,Hd,HU⟩:=H2;obtain ⟨_o,H3⟩:=hG g2 _5 (i+2) (i+1) W HT W (ir W) hM r2 _7 HU Hd (ir ⟨rfl,rfl⟩);simp only[show ¬(i+2=i) by O,↓reduceIte] at H3
    Y qN f n.1 l s (by O:2*m+r1< 2*m+d)
     (fun x hx=>by
      rw[show p0 b x (2*m+r1)=ph m {i,i+1} x from cf HG x,po] at hx;rw[show p0 b x (2*m+d)=ph m {i,i+1,i+2} x from cf hA x,po];obtain ⟨p,q,hp,hpq,hxp,hxq⟩:=hx;X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton] at hp ⊢;O,hpq,hxp,hxq⟩)
     (fun e he=>?_)
    by_cases h0c:e=i+2
    ·have HV:pl b (pe e:Fin (2*m)->Bool) d (p0 b (pe e:Fin (2*m)->Bool) (2*m+r1)) (2*m+r2)=true:=by
      rw[pA b _ d s _ (2*m+r2) W,
       show p0 b (pe e) (2*m+r2)=ph m {i+1,i+2} (pe e) from cf H3 _,
       pg (fun e' _p=>by simp at _p;O) he];simp[h0c]
     X zo hm f l n rfl rfl (by have:=HU.2;O) _7 s
      (fun _ _ _=>rfl) W HT W (ir W) (ir ⟨by O,rfl⟩) hM
      ⟨{i+1,i+2},⟨i+1,by simp⟩,fun e' _p=>by simp at _p;O,H3⟩
      (fun y hy=>by rw[cf H3 y];X hy) HV
      (fun v hv _ _8 _ hrv=>False.elim (by
       have h0d:(b.gates[d]'s).op=.and:=_H.trans z;have HW:(b.gates[d]'s).inputs=[2*m+_O,2*m+_Q]:=_J;have hrm:2*m+v∈pa (b.gates[d]'s):=hrv.1;simp only[pa,h0d,HW,List.mem_cons,List.not_mem_nil,or_false] at hrm;rcases hrm with h|h
       ·X Hi (by rw[←h];X _8)
       ·X Hj (by rw[←h];X _8)))
    ·have _W:p0 b (pe e:Fin (2*m)->Bool) (2*m+r1)=p0 b (pe e:Fin (2*m)->Bool) (2*m+d):=by
      rw[show p0 b _ (2*m+r1)=_ from cf HG _,
       show p0 b _ (2*m+d)=_ from cf hA _]
      apply Bool.eq_iff_iff.2
      rw[pg (fun e' _p=>by simp at _p;O) he,
       pg (fun e' _p=>by simp at _p;O) he];simp;O
     rw[pV b _ d s _ _W,←pb,l,q0 he]
   ·
    push Not at H2
    Y hB g2 _5 ⟨i+2,i+1,by O,HT,by O,ir W,hM⟩
     (fun r hr hH=>by_contra fun hY=>H2 r hr hY hH)
     ⟨.or,[2*m+u2,2*m+r1]⟩ ⟨by simp,by simp⟩
     (fun h=>by
      simp only[pC,pa,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h.1 with h1|h1
      ·O
      ·have _q:r1=g2 :=W
       X qJ W ((_q▸HG).symm.trans hM)) fun x=>?_
    rw[qg b x s];simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
     show 2*m+u2< 2*m+d by O,show 2*m+r1< 2*m+d by O,↓reduceIte]
    rw[show p0 b x (2*m+u2)=_ from cf Ho x,
     show p0 b x (2*m+r1)=_ from cf HG x,cf hA x,qZ]
    congr 1;ext e;simp only[Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    constructor
    ·rintro (h|h|h)
     ·have:=hV e h;O
     ·X il h
     ·X ir (il h)
    ·rintro (rfl|rfl|rfl)
     ·X ir (il rfl)
     ·X ir (ir rfl)
     ·X il HC
  ·push Not at Hp
   by_cases H2:∃r2,∃(_7:r2< b.size),r2≠d/\pC (2*m) r2 (2*m+g2) (b.gates[r2]'_7)
   ·
    obtain ⟨r2,_7,Hd,HU⟩:=H2;obtain ⟨_o,H3⟩:=hG g2 _5 (i+2) (i+1) W HT W (ir W) hM r2 _7 HU Hd (ir ⟨rfl,rfl⟩);simp only[show ¬(i+2=i) by O,↓reduceIte] at H3
    Y hB g1 _4 ⟨i,i+2,_3,by O,by O,il rfl,hL⟩
     (fun r hr hH=>by_contra fun hY=>Hp r hr hY hH)
     ⟨.or,[2*m+u1,2*m+r2]⟩ ⟨by simp,by simp⟩
     (fun h=>by
      simp only[pC,pa,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h.1 with h1|h1
      ·O
      ·have _r:r2=g1 :=W
       X qJ W ((_r▸H3).symm.trans hL)) fun x=>?_
    rw[qg b x s];simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
     show 2*m+u1< 2*m+d by O,show 2*m+r2< 2*m+d by O,↓reduceIte]
    rw[show p0 b x (2*m+u1)=_ from cf HA x,
     show p0 b x (2*m+r2)=_ from cf H3 x,cf hA x,qZ]
    congr 1;ext e;simp only[Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    constructor
    ·rintro (h|h|h)
     ·have:=hU e h;O
     ·X ir (il h)
     ·X ir (ir h)
    ·rintro (rfl|rfl|rfl)
     ·X il _l
     ·X ir (il rfl)
     ·X ir (ir rfl)
   ·
    push Not at H2;by_cases h12:i+1∈S1∪S2
    ·Y hB g1 _4 ⟨i,i+2,_3,by O,by O,il rfl,hL⟩
      (fun r hr hH=>by_contra fun hY=>Hp r hr hY hH)
      ⟨.or,[2*m+u1,2*m+u2]⟩ ⟨by simp,by simp⟩
      (fun h=>by
       simp only[pC,pa,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h.1 with h1|h1
       ·O
       ·have _s:u2=g1 :=W
        X qJ W ((_s▸Ho).symm.trans hL)) fun x=>?_
     rw[qg b x s];simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
      show 2*m+u1< 2*m+d by O,show 2*m+u2< 2*m+d by O,↓reduceIte]
     rw[show p0 b x (2*m+u1)=_ from cf HA x,
      show p0 b x (2*m+u2)=_ from cf Ho x,cf hA x,qZ]
     congr 1;ext e;simp only[Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h12 ⊢
     constructor
     ·rintro (h|h)
      ·have:=hU e h;O
      ·have:=hV e h;O
     ·rintro (rfl|rfl|rfl)
      ·X il _l
      ·X h12
      ·X ir HC
    ·obtain ⟨e0,_9⟩:=HZ;have HH:=hSz e0 _9
     have hK:∀(a g u:ℕ) (S:Finset ℕ) (k0:ℕ) (hg:g< b.size),
       a< 2*m+1+k->a≠2*m ->
       p0 hC (e1 (2*m):Fin (2*m+1)->Bool) a=true ->
       Ht.fc.getD a (.const false)=.wire (2*m+g) ->
       qb m (p8 b g)->u< g->k0< 2*m ->
       p8 b u=ph m S ->
       ((b.gates[g]'hg).inputs=[2*m+u,k0]\/(b.gates[g]'hg).inputs=[k0,2*m+u]) ->
       (∀e∈S,e+1< 2*m)->e0∈S:=by
      intro a g u S k0 hg h0s h0t _X _C ⟨_,kg0,_,_,h0e,_,hgf⟩ h0u Hu huf h0f hS
      have h0x:2*m+1<=a:=by_contra fun _2=>by
       rw[pd hC (2*m) false a W] at _C;injection _C with h;O
      set ta:=a-(2*m+1);have _D:ta< hC.size :=W;have _Y:a=2*m+1+ta :=W;rw[_Y] at _C _X
      have HI:ta≠_c:=fun h=>by
       rw[h,Hs] at _C;injection _C with h1;X qJ h0e (hF.symm.trans (show p8 b kz'''=qd m _ kg0 by rw[show kz'''=g by O];X hgf))
      have hW:(hC.gates[ta]'_D).op=.or:=Hv ta W _X;have HX:=q4 hh.1 hE _D HI;obtain ⟨ga,hga,_,_Z,_,h0g,_⟩:=p4 hh.1 _D HX;rw[_C] at _Z;injection _Z with hgae;have _t:ga=g :=W;subst _t;rcases pc hh Hg ta _D with ⟨hP,_,_,_⟩|⟨_,c1,c2,HJ,H7,H8,_⟩
      ·rw[hW] at hP;cases hP
      ·obtain ⟨v1,v2,_,_,h00,h01,_a⟩:=h0g .or c1 c2 (ir rfl) hW HJ H7 H8
       rw[p6 _ _D hW HJ H7 H8,Bool.or_eq_true] at _X
       have Hk:∀c,(c=c1\/c=c2)->c< 2*m+1+ta->c≠2*m:=fun c hm' _2 h=>
        HI ((hI ta _D).1 ⟨by rcases hm' with rfl|rfl<;>simp[pa,hW,HJ,h],h▸_2⟩)
       have H4:∀c,c< 2*m+1+ta->c≠2*m->Ht.fc.getD c (.const false)=.wire k0 ->
         p0 hC (e1 (2*m):Fin (2*m+1)->Bool) c=false:=fun c h0h _u hec=>by
        cases hUc:p0 hC (e1 (2*m):Fin (2*m+1)->Bool) c with
        | false=>rfl
        | true=>
         obtain ⟨w',_,HK,_,hcl⟩:=HS c W _u hUc;rw[hec] at HK;cases HK;rcases hcl with ⟨Q,_,_,hQ⟩|⟨_,k',_,hi',hk',_m,h0i⟩
         ·X absurd (hQ.symm.trans (funext fun y=>p7 b y k0 Hu)) (zv Hu)
         ·X absurd (h0i.symm.trans (funext fun y=>p7 b y k0 Hu)) (zw hi' hk' _m Hu)
       have h02:∀c,c< 2*m+1+ta->c≠2*m->Ht.fc.getD c (.const false)=.wire (2*m+u) ->
         p0 hC (e1 (2*m):Fin (2*m+1)->Bool) c=true->e0∈S:=fun c h0h _u hec hUc=>by
        obtain ⟨w',_,HK,h03,_⟩:=HS c W _u hUc;rw[hec] at HK;cases HK
        X (pg hS HH).1 (by
         rw[←cf huf _];X h03 _ (by rw[cf hF _];X (pg hSz HH).2 _9))
       rcases h0f with h|h<;>rw[h] at _a <;>
        (injection _a with h1' hrest';injection hrest' with h2';subst h1';subst h2')
       ·rcases _X with hU1|hU2
        ·X h02 c1 H7 (Hk c1 (il rfl) H7) h00 hU1
        ·rw[H4 c2 H8 (Hk c2 (ir rfl) H8) h01] at hU2;cases hU2
       ·rcases _X with hU1|hU2
        ·rw[H4 c1 H7 (Hk c1 (il rfl) H7) h00] at hU1;cases hU1
        ·X h02 c2 H8 (Hk c2 (ir rfl) H8) h01 hU2
     have hD:e0∈S1/\e0∈S2:=by
      rcases h09 with ⟨h1e,h2e⟩|⟨h1e,h2e⟩
      ·X ⟨hK a1 g1 u1 S1 (i+2) _4 _A H5 _e.1 (h1e▸he1) ⟨i,i+2,_3,by O,by O,il rfl,hL⟩ Ha W HA HB hS1,
        hK a2 g2 u2 S2 (i+1) _5 _B H6 _e.2 (h2e▸he2) ⟨i+2,i+1,by O,HT,by O,ir W,hM⟩ Hb W Ho HD hS2⟩
      ·X ⟨hK a2 g1 u1 S1 (i+2) _4 _B H6 _e.2 (h2e▸he2) ⟨i,i+2,_3,by O,by O,il rfl,hL⟩ Ha W HA HB hS1,
        hK a1 g2 u2 S2 (i+1) _5 _A H5 _e.1 (h1e▸he1) ⟨i+2,i+1,by O,HT,by O,ir W,hM⟩ Hb W Ho HD hS2⟩
     have hR:∀(gx gy uy:ℕ) (Sy:Finset ℕ),
       gx< b.size->gy< b.size->gx< d->gy< d->gx≠gy->uy< gy ->
       qb m (p8 b gx)->qb m (p8 b gy) ->
       (∀r (hr:r< b.size),pC (2*m) r (2*m+gx) (b.gates[r]'hr)->r=d) ->
       (∀r (hr:r< b.size),pC (2*m) r (2*m+gy) (b.gates[r]'hr)->r=d) ->
       p8 b uy=ph m Sy->i∈Sy->i+2∈Sy->(∀e∈Sy,e=i\/e=i+1\/e=i+2) ->
       False:=by
      intro gx gy uy Sy hgx hgy h0y h0z h0j h0k gxtb gytb Hl HY h04 h0l h05 _v;set D1:=pU b gx ⟨.and,[i+1,i+2]⟩;set D2:=pU D1 d ⟨.or,[2*m+uy,2*m+gx]⟩;have HL:D1.size=b.size:=pS b gx _;have Hm:D2.size=b.size:=(pS D1 d _).trans HL
      have HM:∀x:Fin (2*m)->Bool,∀w,w< 2*m+d->w≠2*m+gx->p0 D1 x w=p0 b x w:=by
       intro x w;induction w using Nat.strong_induction_on with
       | ind w ih=>
        intro hw hY;by_cases _2:w< 2*m+gx
        ·X qc b x gx _ w _2
        ·set t:=w-2*m;have ht:t< b.size :=W
         have htD:t< D1.size:=by rw[HL];X ht
         have HN:w=2*m+t :=W;rw[HN];have hX:D1.gates[t]'htD=b.gates[t]'ht:=List.getElem_set_ne (by O:gx≠t) _
         rw[pj D1 x t htD,hX,pj b x t ht];rcases pc f hT t ht with ⟨hP,_,_,_⟩|⟨hN,c1,c2,hO,H7,H8,_⟩
         ·X absurd hP (n.1 _ (List.getElem_mem ht))
         ·have hnr:¬pC (2*m) t (2*m+gx) (b.gates[t]'ht):=fun hr=>by have:=Hl t ht hr;O
          have He:c1≠2*m+gx:=fun h=>hnr ⟨by rcases hN with HO|HO<;>simp[pa,HO,hO,h],h▸H7⟩
          have Hf:c2≠2*m+gx:=fun h=>hnr ⟨by rcases hN with HO|HO<;>simp[pa,HO,hO,h],h▸H8⟩
          rw[hO];congr 1;simp only[List.map_cons,List.map_nil,H7,H8,↓reduceIte];rw[ih c1 W W He,ih c2 W W Hf]
      have h06:∀x:Fin (2*m)->Bool,p0 D2 x (2*m+d)=p8 b d x:=fun x=>by
       rw[qg D1 x (by rw[HL];X s)]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
        show 2*m+uy< 2*m+d by O,show 2*m+gx< 2*m+d by O,↓reduceIte]
       have _w:2*m+uy≠2*m+gx:=fun h=>by
        have h1:uy=gx :=W;subst h1;obtain ⟨_,kx0,_,_,h0m,_,h0n⟩:=gxtb;X qJ h0m (h04.symm.trans h0n)
       rw[HM x (2*m+uy) W _w,qg b x hgx]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,
        show i+1< 2*m+gx by O,show i+2< 2*m+gx by O,↓reduceIte,
        p7 b x (i+1) W,p7 b x (i+2) W]
       rw[←pv W x,show p0 b x (2*m+uy)=_ from cf h04 x,
        cf hA x,qZ]
       congr 1;ext e;simp only[Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
       constructor
       ·rintro (he|rfl)
        ·X _v e he
        ·X ir (il rfl)
       ·rintro (rfl|rfl|rfl)
        ·X il h0l
        ·X ir rfl
        ·X il h05
      have _x:∀x:Fin (2*m)->Bool,∀w,w< 2*m+b.size->w≠2*m+gx->p0 D2 x w=p0 b x w:=by
       intro x w;induction w using Nat.strong_induction_on with
       | ind w ih=>
        intro hw hY;by_cases _2:w< 2*m+d
        ·rw[qc D1 x d _ w _2];X HM x w _2 hY
        ·by_cases hwk:w=2*m+d
         ·subst hwk;X h06 x
         ·set t:=w-2*m;have ht:t< b.size :=W
          have htD:t< D2.size:=by rw[Hm];X ht
          have HN:w=2*m+t :=W;rw[HN]
          have hX:D2.gates[t]'htD=b.gates[t]'ht :=
           (List.getElem_set_ne (by O:d≠t) _).trans (List.getElem_set_ne (by O:gx≠t) _)
          rw[pj D2 x t htD,hX,pj b x t ht];rcases pc f hT t ht with ⟨hP,_,_,_⟩|⟨hN,c1,c2,hO,H7,H8,_⟩
          ·X absurd hP (n.1 _ (List.getElem_mem ht))
          ·have hnr:¬pC (2*m) t (2*m+gx) (b.gates[t]'ht):=fun hr=>by have:=Hl t ht hr;O
           have He:c1≠2*m+gx:=fun h=>hnr ⟨by rcases hN with HO|HO<;>simp[pa,HO,hO,h],h▸H7⟩
           have Hf:c2≠2*m+gx:=fun h=>hnr ⟨by rcases hN with HO|HO<;>simp[pa,HO,hO,h],h▸H8⟩
           rw[hO];congr 1;simp only[List.map_cons,List.map_nil,H7,H8,↓reduceIte];rw[ih c1 W W He,ih c2 W W Hf]
      have _y:cF (2*m) D2=cF (2*m) b:=funext fun x=>
       _x x b.output (pB hT) (qz l gxtb)
      have _z:IsMinimalCircuit (2*m) D2 :=
       ⟨z1 (z1 f.1 gx ⟨by simp,by simp⟩) d ⟨by simp,by simp⟩,
        fun E h0o hEf=>by rw[Hm];X f.2 E h0o (hEf.trans _y)⟩
      rcases pY _z gy (by rw[Hm];X hgy) with hout|⟨r,hr,_,hH⟩
      ·X qz l gytb hout
      ·have _m:r< b.size:=by rw[←Hm];X hr
       by_cases HE:r=d
       ·subst HE;have hX:D2.gates[r]'hr=⟨.or,[2*m+uy,2*m+gx]⟩:=List.getElem_set_self _
        rw[hX] at hH;simp[pC,pa] at hH;O
       ·by_cases hrx:r=gx
        ·subst hrx
         have hX:D2.gates[r]'hr=⟨.and,[i+1,i+2]⟩ :=
          (List.getElem_set_ne (Ne.symm HE) _).trans (List.getElem_set_self _)
         rw[hX] at hH;simp[pC,pa] at hH;O
        ·have hX:D2.gates[r]'hr=b.gates[r]'_m :=
          (List.getElem_set_ne (Ne.symm HE) _).trans (List.getElem_set_ne (Ne.symm hrx) _)
         X HE (HY r _m (hX▸hH))
     have _b:g1≠g2:=fun h=>by
      have:=cf (hL.symm.trans (h▸hM)) (e1 (i+2))
      rw[(pN W W).2 rfl] at this
      have:=(pN W W).1 this.symm;O
     have Hq:e0=i\/e0=i+2:=by
      have h1:=hU e0 hD.1;have h2:=hV e0 hD.2
      have:e0≠i+1:=fun h=>h12 (Finset.mem_union.2 (il (h▸hD.1)))
      O
     rcases Hq with he0|he0
     ·X hR g1 g2 u2 S2 _4 _5 Hy Hz _b Hb
       ⟨i,i+2,_3,by O,by O,il rfl,hL⟩
       ⟨i+2,i+1,by O,HT,by O,ir W,hM⟩
       (fun r hr hH=>by_contra fun hY=>Hp r hr hY hH)
       (fun r hr hH=>by_contra fun hY=>H2 r hr hY hH)
       Ho (he0▸hD.2) HC (fun e he=>by have:=hV e he;O)
     ·X hR g2 g1 u1 S1 _5 _4 Hz Hy _b.symm Ha
       ⟨i+2,i+1,by O,HT,by O,ir W,hM⟩
       ⟨i,i+2,_3,by O,by O,il rfl,hL⟩
       (fun r hr hH=>by_contra fun hY=>H2 r hr hY hH)
       (fun r hr hH=>by_contra fun hY=>Hp r hr hY hH)
       HA _l (he0▸hD.1) (fun e he=>by have:=hU e he;O)
private lemma kd {m:ℕ} (hm:1<=m) {hB:J}
  (hh:IsMinimalCircuit (2*m+1) hB) (h04:z0 hB)
  (HH:∀x:Fin (2*m+1)->Bool,cF (2*m+1) hB x=(x (Fin.last (2*m))||pq (2*m) (Fin.init x)))
  (l:IsMinimalCircuit (2*m) (p3 hB (2*m) false))
  (s:cF (2*m) (p3 hB (2*m) false)=pq (2*m))
  (u:qf m (p3 hB (2*m) false))
  {q'' kz''':ℕ} (h2l:q''< hB.size) (h0i:kz'''< (p3 hB (2*m) false).size)
  (HR:∀k (hk:k< hB.size),pC (2*m+1) k (2*m) (hB.gates[k]'hk)↔k=q'')
  (hG:∀k (hk:k< hB.size),(p5 hB (2*m) false).fb[k]'(by rw[(pk hB (2*m) false hh.1).kept_len];X hk)=false↔k=q'')
  (H6:(p5 hB (2*m) false).fc.getD (2*m+1+q'') (.const false)=.wire (2*m+kz'''))
  (Hg:q1 m (p8 (p3 hB (2*m) false) kz'''))
  (H1:∀k (hk:k< hB.size),p0 hB (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true->(hB.gates[k]'hk).op=.or) :
  ∀k (hk:k< hB.size),p0 hB (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true ->
   ∃_H,(p5 hB (2*m) false).fc.getD (2*m+1+k) (.const false)=.wire _H /\
    q1 m (fun y=>p0 (p3 hB (2*m) false) y _H):=by
 set Hh:=p5 hB (2*m) false;set f:=p3 hB (2*m) false
 have hD:∃y1 y2:Fin (2*m)->Bool,cF (2*m) f y1≠cF (2*m) f y2:=by
  rw[s];X ps W
 have _I:∃y1 y2:Fin (2*m)->Bool,cF (2*m+1) hB (Fin.snoc y1 false)≠cF (2*m+1) hB (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,hne⟩:=ps (n:=2*m) W;X ⟨y1,y2,by rw[HH,HH,Fin.snoc_last,Fin.snoc_last,Fin.init_snoc,Fin.init_snoc];X hne⟩
 have Hz:∃x1 x2:Fin (2*m+1)->Bool,cF (2*m+1) hB x1≠cF (2*m+1) hB x2:=by
  obtain ⟨y1,y2,hne⟩:=_I;X ⟨Fin.snoc y1 false,Fin.snoc y2 false,hne⟩
 have h1s:=jH hm hh h04 Hz l s u h2l h0i HR hG H6 Hg le_rfl H1;intro k hk hUk;obtain ⟨_H,h1t,Hm,_,h2m⟩:=h1s (2*m+1+k) W W hUk;Y ⟨_H,Hm,?_⟩;rcases h2m with h|_5
 ·X h
 ·exfalso
  have hkq:k≠q'':=fun h=>by
   subst h;rw[H6] at Hm;cases Hm;obtain ⟨_,k0,_,_,hZ,_,_i⟩:=_5;obtain ⟨_,_,_,hkz⟩:=Hg;X qJ hZ (hkz.symm.trans _i)
  have h1u:=q4 hh.1 hG hk hkq;obtain ⟨kv,HA,_,h05,_,h2n,_⟩:=p4 hh.1 hk h1u;rw[Hm] at h05;injection h05 with hweq;subst hweq;obtain ⟨i,k0,_f,hi,hZ,hM,hJ⟩:=_5
  obtain ⟨_,ku,h2o,Su,HB,Hi,H7,hE,hA,h06⟩ :=
   qB hm l s u HA _f hi hZ hM hJ
  have h2p:kv< f.size:=HA;have H0:ku< f.size :=W
  obtain ⟨tu,htu,h2q,h0j⟩:∃tu,∃(_:tu< hB.size),
    p0 hB (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+tu)=true /\
    Hh.fc.getD (2*m+1+tu) (.const false)=.wire (2*m+ku):=by
   have h0k:=H1 k hk hUk;rcases pc hh Hz k hk with ⟨hF,_,_,_⟩|⟨_,c1,c2,HI,H8,H2,_⟩
   ·rw[h0k] at hF;cases hF
   ·obtain ⟨v1,v2,_,_,_J,_K,h07⟩:=h2n .or c1 c2 (ir rfl) h0k HI H8 H2
    rw[p6 _ hk h0k HI H8 H2,Bool.or_eq_true] at hUk
    have HC:∀c,c< 2*m+1+k->Hh.fc.getD c (.const false)=.wire k0 ->
      p0 hB (e1 (2*m):Fin (2*m+1)->Bool) c=false:=fun c _L hec=>by
     have h2r:c≠2*m:=fun h=>by rw[h,p9 hB (2*m) false hh.1] at hec;cases hec
     cases hUc:p0 hB (e1 (2*m):Fin (2*m+1)->Bool) c with
     | false=>rfl
     | true=>
      obtain ⟨w',_,h1v,_,hcl⟩:=h1s c W h2r hUc;rw[hec] at h1v;cases h1v;rcases hcl with ⟨Q,_,_,hQ⟩|⟨_,k',_,hi',_6,_j,_i⟩
      ·X absurd (hQ.symm.trans (funext fun y=>p7 f y k0 hZ)) (zv hZ)
      ·X absurd (_i.symm.trans (funext fun y=>p7 f y k0 hZ)) (zw hi' _6 _j hZ)
    have hmk:∀c,c< 2*m+1+k->Hh.fc.getD c (.const false)=.wire (2*m+ku) ->
      p0 hB (e1 (2*m):Fin (2*m+1)->Bool) c=true ->
      ∃tu,∃(_:tu< hB.size),p0 hB (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+tu)=true /\
       Hh.fc.getD (2*m+1+tu) (.const false)=.wire (2*m+ku):=fun c _L hec hUc=>by
     have h3o:2*m+1<=c:=by_contra fun hlt=>by
      by_cases H2:c=2*m
      ·rw[H2,p9 hB (2*m) false hh.1] at hec;cases hec
      ·rw[pd hB (2*m) false c W] at hec;injection hec with h;O
     X ⟨c-(2*m+1),by O,by rwa[show 2*m+1+(c-(2*m+1))=c by O],
      by rwa[show 2*m+1+(c-(2*m+1))=c by O]⟩
    rcases h06 with h|h<;>rw[h] at h07 <;>
     (injection h07 with _g hrest';injection hrest' with _h;subst _g;subst _h)
    ·rcases hUk with hU1|hU2
     ·X hmk c1 H8 _J hU1
     ·rw[HC c2 H2 _K] at hU2;cases hU2
    ·rcases hUk with hU1|hU2
     ·rw[HC c1 H8 _J] at hU1;cases hU1
     ·X hmk c2 H2 _K hU2
  have hN:f.output≠2*m+ku:=fun _k=>by
   rcases pY l kv HA with h|⟨a,ha,h3p,_E⟩
   ·X qz s ⟨i,k0,_f,hi,hZ,hM,hJ⟩ h
   ·X qG l u.1 a ha (2*m+ku) W (fun x hx=>by
     rw[←_k,←pb,s];obtain ⟨_,HJ⟩:=qr hm l s u HA ha _f hi hZ hM hJ _E
     rcases HJ with ⟨_,⟨hR,_⟩|⟨_,hR⟩⟩|⟨_,⟨hR,_⟩|⟨_,hR⟩⟩ <;>
      X pT (by rw[←cf hR x];X hx))
     (fun x hx=>by rw[s];X pT (by rw[←cf hA x];X hx))
  have hU:∃kr,∃(hS:kr< f.size),
    pC (2*m) kr (2*m+ku) (f.gates[kr]'hS)/\q1 m (p8 f kr):=by
   by_contra _l;push Not at _l
   have Hn:∀r (hr:r< f.size),pC (2*m) r (2*m+ku) (f.gates[r]'hr) ->
     qb m (p8 f r):=fun r hr HS=>
    (pQ hm l s u H0 hr ⟨Su,HB,Hi,hA⟩ HS).2.1.resolve_left (_l r hr HS)
   have h1q:ku≠kz''':=fun h0l=>by
    subst h0l
    have _7:∀w,w< 2*m+1+hB.size->w≠2*m ->
      p0 hB (e1 (2*m):Fin (2*m+1)->Bool) w=true ->
      w=2*m+1+q''\/∃v',Hh.fc.getD w (.const false)=.wire v'/\qb m (fun y=>p0 f y v'):=by
     intro w;induction w using Nat.strong_induction_on with
     | ind w ih=>
      intro hw hne hUw;by_cases hin:w< 2*m+1
      ·rw[p7 hB _ w hin] at hUw;simp[e1,hne] at hUw
      ·set j:=w-(2*m+1);have hj:j< hB.size :=W
       have _m:w=2*m+1+j :=W;rw[_m] at hUw ⊢;by_cases hjq:j=q''
       ·X il (by rw[hjq])
       ·right
        have _8:=H1 j hj hUw;have HT:=q4 hh.1 hG hj hjq;obtain ⟨kj,hkj,_,h1w,h2s,h2t,_⟩:=p4 hh.1 hj HT;rcases pc hh Hz j hj with ⟨hF,_,_,_⟩|⟨_,c1,c2,HI,H8,H2,_⟩
        ·rw[_8] at hF;cases hF
        ·obtain ⟨v1,v2,_,_,_J,_K,_⟩:=h2t .or c1 c2 (ir rfl) _8 HI H8 H2
         rw[p6 _ hj _8 HI H8 H2,Bool.or_eq_true] at hUw
         have h1x:∀c,(c=c1\/c=c2)->c< 2*m+1+j->c≠2*m:=fun c hm' hlt h=>
          hjq ((HR j hj).1 ⟨by rcases hm' with rfl|rfl<;>simp[pa,_8,HI,h],h▸hlt⟩)
         have HD:∀c vc,(c=c1\/c=c2)->c< 2*m+1+j ->
           Hh.fc.getD c (.const false)=.wire vc ->
           p0 hB (e1 (2*m):Fin (2*m+1)->Bool) c=true ->
           qb m (p8 f kj):=fun c vc hm' _L _M hUc=>by
          have h0m:=pp hh h04 Hz hj HT hkj h1w
           ⟨by rcases hm' with rfl|rfl<;>simp[pa,_8,HI],_L⟩ _M
          rcases ih c W W (h1x c hm' _L) hUc with rfl|⟨vc',h08,ic,kc,h1y,hic,hkc,hrc,_9⟩
          ·rw[H6] at _M;injection _M with hvc;subst hvc;X Hn kj hkj h0m
          ·exfalso;rw[_M] at h08;cases h08
           have h2u:2*m<=vc:=by_contra fun hlt=>zw hic hkc hrc W
            (_9.symm.trans (funext fun y=>p7 f y vc W))
           set gv:=vc-2*m;have h2v:kj< f.size:=hkj;have hgv:gv< f.size:=by have:=h0m.2;O
           have _n:vc=2*m+gv :=W
           have ⟨_N,_⟩:=qr hm l s u hgv hkj h1y hic hkc hrc
            (by change (fun y=>p0 f y (2*m+gv))=qd m ic kc;rw[←_n];X _9) (_n▸h0m)
           have:(f.gates[kj]'hkj).op=.or:=h2s.trans _8;rw[_N] at this;cases this
         Y ⟨2*m+kj,h1w,?_⟩;rcases hUw with h1|h2
         ·X HD c1 v1 (il rfl) H8 _J h1
         ·X HD c2 v2 (ir rfl) H2 _K h2
    have _O:hB.output≠2*m:=fun h=>
     pL hh.1 _I (p9 hB (2*m) false hh.1) h
    have h0n:p0 hB (e1 (2*m):Fin (2*m+1)->Bool) hB.output=true:=by
     change cF (2*m+1) hB (e1 (2*m))=true;rw[HH];simp[e1,Fin.last]
    rcases _7 hB.output (pB Hz) _O h0n with hout_q|⟨v',h2w,_i⟩
    ·have h1:=q8 hh.1 _I;rw[hout_q,H6] at h1;injection h1 with h;X hN h.symm
    ·have h1:=q8 hh.1 _I;rw[h2w] at h1;cases h1
     obtain ⟨_,k0',_,_,h1z,_,h2x⟩:=_i
     have h2:pq (2*m) (e1 k0')=true:=by
      rw[←cf s _,pb,cf h2x _];X (pN h1z h1z).2 rfl
     rw[pW] at h2;cases h2
   have _o:tu≠q'':=fun h=>by rw[h,H6] at h0j;injection h0j with h1;O
   have _P:=q4 hh.1 hG htu _o;obtain ⟨ku',h3q,_,_p,h2y,_,_⟩:=p4 hh.1 htu _P;rw[h0j] at _p;injection _p with hku_eq;have _Q:ku'=ku :=W;have hH:(f.gates[ku]'H0).op=.or:=(show (f.gates[ku]'H0).op=(hB.gates[tu]'htu).op by subst _Q;X h2y).trans (H1 tu htu h2q)
   rcases pc l hD ku H0 with ⟨hF,_,_,_⟩|⟨_,p1,p2,H9,hp1,hp2,_⟩
   ·rw[hH] at hF;cases hF
   ·have h09:∀p (hp:p< 2*m+ku),
      (∀y:Fin (2*m)->Bool,p0 f y p=true->ph m Su y=true) ->
      ∃Sp:Finset ℕ,Sp.Nonempty/\(∀e∈Sp,e+1< 2*m)/\(∀e∈Sp,e∈Su) /\
       (fun y=>p0 f y p)=ph m Sp:=fun p hp _R=>by
     rcases qE u p W with
      ⟨j,hj,_,hpf⟩|⟨_,_,_,Sp,h20,hSp,hpf⟩|⟨_,_,_,c,H8,H2,hpf⟩|⟨_,_,_,_,k',_,_,_6,_,hpf⟩
     ·have h1:=_R (e1 j) (by rw[cf hpf _];simp[e1]);rw[pz] at h1;cases h1
     ·X ⟨Sp,h20,hSp,fun e he=>(pg Hi (hSp e he)).1
       (_R _ (by rw[cf hpf _];X (pg hSp (hSp e he)).2 he)),hpf⟩
     ·have h1:=_R (e1 (c-1)) (by rw[cf hpf _];X (pu H8 H2 W).2 (il W))
      rw[pz] at h1;cases h1
     ·have h1:=_R (e1 k') (by rw[cf hpf _];X (pN _6 _6).2 rfl)
      rw[pz] at h1;cases h1
    obtain ⟨Sp1,h0o,h2z,Ho,h0p⟩:=h09 p1 hp1 fun y hy=>by
     rw[←cf hA y];change p0 f y (2*m+ku)=true;rw[p6 y H0 hH H9 hp1 hp2,hy];R
    obtain ⟨Sp2,h30,h31,_S,h21⟩:=h09 p2 hp2 fun y hy=>by
     rw[←cf hA y];change p0 f y (2*m+ku)=true;rw[p6 y H0 hH H9 hp1 hp2,hy,Bool.or_true]
    have _a:∀e,e∈Su->e∈Sp1\/e∈Sp2:=fun e he=>by
     have h1:ph m Su (pe e)=true:=(pg Hi (Hi e he)).2 he
     rw[←cf hA _,show p8 f ku (pe e)=(p0 f (pe e) p1||p0 f (pe e) p2) from
      p6 _ H0 hH H9 hp1 hp2,Bool.or_eq_true,cf h0p _,cf h21 _] at h1
     rcases h1 with h|h
     ·X il ((pg h2z (Hi e he)).1 h)
     ·X ir ((pg h31 (Hi e he)).1 h)
    have h0a:∀i' k',i'+1< 2*m->(_6:k'< 2*m)->i'∈Su->(∀e∈Su,e=i'\/e=k'\/e+1=k') ->
      ∃p',p'< 2*m+ku/\∀x:Fin (2*m)->Bool,(p0 f x p'||x ⟨k',_6⟩)=qd m i' k' x:=by
     intro i' k' hi' _6 h22 h0b;rcases _a i' h22 with h|h
     ·X ⟨p1,hp1,fun x=>by rw[cf h0p x];X jQ hi' _6 h (fun e he=>h0b e (Ho e he)) x⟩
     ·X ⟨p2,hp2,fun x=>by rw[cf h21 x];X jQ hi' _6 h (fun e he=>h0b e (_S e he)) x⟩
    obtain ⟨pi,h32,h0q⟩:=h0a i k0 hi hZ H7 hE;set D1:=pU f kv ⟨.or,[pi,k0]⟩
    have Ha:∀x:Fin (2*m)->Bool,∀w< 2*m+f.size,p0 D1 x w=p0 f x w:=fun x=>
     qv f HA ⟨.or,[pi,k0]⟩ x (by
      rw[qg f x HA];simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
       show pi< 2*m+kv by O,show k0< 2*m+kv by O,↓reduceIte,p7 f x k0 hZ]
      rw[h0q x,←cf hJ x])
    have _q:=qC l ⟨.or,[pi,k0]⟩ ⟨by simp,by simp⟩ (funext fun x=>Ha x f.output (pB hD))
    by_cases HK:∃kv2,∃(Hp:kv2< f.size),kv2≠kv/\pC (2*m) kv2 (2*m+ku) (f.gates[kv2]'Hp)
    ·obtain ⟨kv2,Hp,_r,h0r⟩:=HK
     obtain ⟨i2,k2,h33,hi2,hk2,hr2,HU⟩:=Hn kv2 Hp h0r
     obtain ⟨_,ku2,_,Su2,_,h34,Hq,hV,h23,h0s⟩ :=
      qB hm l s u Hp h33 hi2 hk2 hr2 HU
     have _T:ku=ku2:=by
      have hrm:=h0r.1;have h35:=(pQ hm l s u H0 Hp ⟨Su,HB,Hi,hA⟩ h0r).1;rcases h0s with h|h<;>(simp only[pa,h35,h,List.mem_cons,List.not_mem_nil,or_false] at hrm;O)
     subst _T;have h0t:Su2=Su:=qM h34 Hi (h23.symm.trans hA);rw[h0t] at Hq hV
     have h36:i2≠i:=fun h=>by
      subst h;have h37:k2≠k0:=fun _6=>by subst _6;X qy l Hp HA _r (HU.trans hJ.symm)
      have HV:∀e∈Su,e=i2:=fun e he=>by
       have:=hE e he;have:=hV e he;rcases hM with rfl|_<;>rcases hr2 with rfl|_<;>O
      obtain ⟨x,hx⟩:=py l ku H0 p1 hp1;apply hx;rw[cf hA x,cf h0p x];congr 1;ext e;X ⟨fun he=>by obtain ⟨e',Hr⟩:=h0o;rw[HV e he,←HV e' (Ho e' Hr)];X Hr,Ho e⟩
     obtain ⟨pi2,h2k,_U⟩:=h0a i2 k2 hi2 hk2 Hq hV;set D2:=pU D1 kv2 ⟨.or,[pi2,k2]⟩
     have h0u:∀x:Fin (2*m)->Bool,∀w< 2*m+f.size,p0 D2 x w=p0 f x w:=fun x w hw=>
      (qv D1 (by rw[pS];X Hp) ⟨.or,[pi2,k2]⟩ x (by
       rw[qg D1 x (by rw[pS];X Hp)]
       simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
        show pi2< 2*m+kv2 by O,show k2< 2*m+kv2 by O,↓reduceIte,p7 D1 x k2 hk2]
       rw[Ha x pi2 W,_U x,Ha x (2*m+kv2) W,←cf HU x];rfl)
       w (by rw[pS];X hw)).trans (Ha x w hw)
     have h0v:=qC _q ⟨.or,[pi2,k2]⟩ ⟨by simp,by simp⟩ (funext fun x=>by
      change p0 D2 x f.output=p0 D1 x f.output;rw[h0u x f.output (pB hD),Ha x f.output (pB hD)])
     rcases pY h0v ku (by rw[pS,pS];X H0) with _k|⟨r,hr,_,HS⟩
     ·X hN _k
     ·have _j:r< f.size:=by rw[←pS f kv,←pS D1 kv2];X hr
      by_cases hr1:r=kv
      ·subst hr1
       have hK:D2.gates[r]'hr=⟨.or,[pi,k0]⟩:=(List.getElem_set_ne _r _).trans (List.getElem_set_self _);rw[hK] at HS;simp[pC,pa] at HS;O
      ·by_cases h0w:r=kv2
       ·subst h0w;have hK:D2.gates[r]'hr=⟨.or,[pi2,k2]⟩:=List.getElem_set_self _
        rw[hK] at HS;simp[pC,pa] at HS;O
       ·have hK:D2.gates[r]'hr=f.gates[r]'_j:=(List.getElem_set_ne (Ne.symm h0w) _).trans (List.getElem_set_ne (Ne.symm hr1) _)
        obtain ⟨i3,k3,h38,hi3,hk3,hr3,h0x⟩:=Hn r _j (hK▸HS)
        obtain ⟨_,ku3,_,Su3,_,h39,_s,HW,h24,h25⟩ :=
         qB hm l s u _j h38 hi3 hk3 hr3 h0x
        have _V:ku=ku3:=by
         have hrm:=(hK▸HS).1;have h3a:=(pQ hm l s u H0 _j ⟨Su,HB,Hi,hA⟩ (hK▸HS)).1;rcases h25 with h|h<;>(simp only[pa,h3a,h,List.mem_cons,List.not_mem_nil,or_false] at hrm;O)
        subst _V;have _W:Su3=Su:=qM h39 Hi (h24.symm.trans hA);subst _W
        have h0y:(i3=i/\k3=k0)\/(i3=i2/\k3=k2):=by
         have:=hE i2 Hq;have:=hV i H7;have:=hE i3 _s
         have:=hV i3 _s;have:=HW i H7;have:=HW i2 Hq
         rcases hM with rfl|_<;>rcases hr2 with rfl|_<;>rcases hr3 with rfl|_<;>O
        rcases h0y with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        ·X qy l _j HA hr1 (h0x.trans hJ.symm)
        ·X qy l _j Hp h0w (h0x.trans HU.symm)
    ·push Not at HK
     rcases pY _q ku (by rw[pS];X H0) with _k|⟨r,hr,_,HS⟩
     ·X hN _k
     ·have _j:r< f.size:=by rw[←pS f kv];X hr
      by_cases hr1:r=kv
      ·subst hr1;have hK:D1.gates[r]'hr=⟨.or,[pi,k0]⟩:=List.getElem_set_self _
       rw[hK] at HS;simp[pC,pa] at HS;O
      ·X HK r _j hr1 ((List.getElem_set_ne (Ne.symm hr1) _:D1.gates[r]'hr=f.gates[r]'_j)▸HS)
  obtain ⟨kr,hS,Hs,Ht⟩:=hU;obtain ⟨hO,_,_⟩:=pQ hm l s u H0 hS ⟨Su,HB,Hi,hA⟩ Hs;rcases pc l hD kr hS with ⟨hF,_,_,_⟩|⟨_,d1,d2,Hb,hd1,hd2,h0c⟩
  ·rw[hO] at hF;cases hF
  ·have h0d:=Hs.1;simp only[pa,hO,Hb,List.mem_cons,List.not_mem_nil,or_false] at h0d
   obtain ⟨d,h26,h3n,Hc⟩:∃d,d< 2*m+kr/\d≠2*m+ku /\
     ((f.gates[kr]'hS).inputs=[2*m+ku,d]\/(f.gates[kr]'hS).inputs=[d,2*m+ku]):=by
    rcases h0d with rfl|rfl
    ·X ⟨d2,hd2,h0c.symm,il Hb⟩
    ·X ⟨d1,hd1,h0c,ir Hb⟩
   by_cases hT1:∃a,∃(ha:a< f.size),pC (2*m) a (2*m+kv) (f.gates[a]'ha) /\
     (∀x:Fin (2*m)->Bool,p8 f ku x=true->p8 f a x=true)
   ·
    obtain ⟨a,ha,_E,h0z⟩:=hT1;obtain ⟨hI,HL⟩:=qr hm l s u HA ha _f hi hZ hM hJ _E
    obtain ⟨e0,Hu,h0e,h10⟩:∃e0,((k0=i+2/\e0=i)\/(k0+1=i/\e0=k0)) /\
      q1 m (p8 f a) /\
      (∀x:Fin (2*m)->Bool,ph m {e0,e0+1} x=true->p8 f a x=true):=by
     rcases HL with ⟨hW,⟨hR,_⟩|⟨h3r,hR⟩⟩|⟨_X,⟨hR,_⟩|⟨h3s,hR⟩⟩
     ·X ⟨i,il ⟨hW,rfl⟩,⟨{i,i+1},⟨i,by simp⟩,fun e he=>by simp at he;O,hR⟩,fun x hx=>by rw[cf hR x];X hx⟩
     ·X ⟨i,il ⟨hW,rfl⟩,⟨{i,i+1,i+2},⟨i,by simp⟩,fun e he=>by simp at he;O,hR⟩,fun x hx=>by
       rw[cf hR x,po];rw[po] at hx;obtain ⟨p,q,hp,HM,HN,HO⟩:=hx;X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton] at hp ⊢;O,HM,HN,HO⟩⟩
     ·X ⟨k0,ir ⟨_X,rfl⟩,⟨{i-1,i},⟨i,by simp⟩,fun e he=>by simp at he;O,hR⟩,fun x hx=>by
       rw[cf hR x];convert hx using 2;ext e;simp;O⟩
     ·X ⟨k0,ir ⟨_X,rfl⟩,⟨{i-2,i-1,i},⟨i,by simp⟩,fun e he=>by simp at he;O,hR⟩,fun x hx=>by
       rw[cf hR x,po];rw[po] at hx;obtain ⟨p,q,hp,HM,HN,HO⟩:=hx;X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton] at hp ⊢;O,HM,HN,HO⟩⟩
    Y qN l u.1 s hS h26 (fun x hx=>by
     rw[p6 x hS hO Hb hd1 hd2,Bool.or_eq_true];rcases Hc with h|h<;>rw[Hb] at h<;>(injection h with _g hrest';injection hrest' with _h;rw[_g,_h])
     ·X ir hx
     ·X il hx) fun e he=>?_
    by_cases hpu:p8 f ku (pe e:Fin (2*m)->Bool)=false
    ·have h27:p0 f (pe e:Fin (2*m)->Bool) d=p0 f (pe e:Fin (2*m)->Bool) (2*m+kr):=by
      rw[p6 _ hS hO Hb hd1 hd2];rcases Hc with h|h<;>rw[Hb] at h<;>(injection h with _g hrest';injection hrest' with _h;subst _g;subst _h)
      ·change _=(p8 f ku (pe e)||_);rw[hpu];R
      ·change _=(_||p8 f ku (pe e));rw[hpu,Bool.or_false]
     rw[pV f _ kr hS _ h27,←pb,s,q0 he]
    ·have h11:p8 f ku (pe e:Fin (2*m)->Bool)=true:=by cases h:p8 f ku (pe e);X absurd h hpu;R
     have h28:p8 f a (pe e:Fin (2*m)->Bool)=true:=h0z _ h11;have hpS:e∈Su:=(pg Hi he).1 (by rw[←cf hA _];X h11)
     have h12:pl f (pe e:Fin (2*m)->Bool) kr (p0 f (pe e:Fin (2*m)->Bool) d) (2*m+a)=true:=by
      by_cases h3t:a< kr
      ·rw[pA f _ kr hS _ (2*m+a) W];X h28
      ·have h13:a≠kr:=fun h=>by subst h;rw[hO] at hI;cases hI
       have hX:pl f (pe e:Fin (2*m)->Bool) kr (p0 f (pe e:Fin (2*m)->Bool) d) (2*m+kv)=true:=by
        have h14:kv≠kr:=fun h=>by subst h;obtain ⟨_,_,_,He⟩:=Ht;X qJ hZ (He.symm.trans hJ)
        have h15:=(qB hm l s u HA _f hi hZ hM hJ).1
        rcases h06 with h|h<;>rw[pJ _ hS _ HA h14 h15 h W W,
         pA f _ kr hS _ (2*m+ku) W,show p0 f (pe e) (2*m+ku)=true from h11]<;>simp
       obtain ⟨_,c1,c2,HX,H8,H2,h3b,h16,h17,_⟩:=qn hm l s u ha hI;have h29:=_E.1;simp only[pa,hI,HX,List.mem_cons,List.not_mem_nil,or_false] at h29;rw[pF _ hS _ ha h13 hI HX H8 H2,Bool.and_eq_true]
       have Hj:p0 f (pe e:Fin (2*m)->Bool) c1=true/\p0 f (pe e:Fin (2*m)->Bool) c2=true:=by
        have h1:=pm (pe e:Fin (2*m)->Bool) ha hI HX H8 H2;change p8 f a (pe e)=_ at h1;rw[h28,eq_comm,Bool.and_eq_true] at h1;X h1
       have hY:∀b (hb:b< 2*m+a),((c1=2*m+kv/\c2=b)\/(c2=2*m+kv/\c1=b)) ->
         p0 f (pe e:Fin (2*m)->Bool) b=true->¬q1 m (fun y=>p0 f y b) ->
         pl f (pe e:Fin (2*m)->Bool) kr (p0 f (pe e:Fin (2*m)->Bool) d) b=true:=by
        intro b hb h0f hbp h3c;by_cases h3d:b< 2*m+kr
        ·rw[pA f _ kr hS _ b h3d];X hbp
        ·rcases qE u b W with
          ⟨j,_,rfl,_⟩|⟨_,_,_,heo⟩|⟨tb,_5,rfl,hst⟩|⟨tb,_5,rfl,ib,kb,h2a,hib,_b,hrb,hbf⟩
         ·O
         ·X absurd heo h3c
         ·obtain ⟨hP,x1,x2,h0g,_F,_G⟩:=jY hm l s u _5 hst
          have Hv:tb≠kr:=fun h=>by
           subst h;obtain ⟨_,_,_,He⟩:=Ht;obtain ⟨cb,h18,h19,h3e⟩:=hst;X z6 h18 h19 (He.symm.trans h3e)
          rw[pJ _ hS _ _5 Hv hP h0g W W,
           pA f _ kr hS _ x1 W,pA f _ kr hS _ x2 W]
          rwa[p6 _ _5 hP h0g W W] at hbp
         ·have Hv:tb≠kr:=fun h=>by
           subst h;obtain ⟨_,_,_,He⟩:=Ht;X qJ _b (He.symm.trans hbf)
          obtain ⟨hP,ub,h3f,Sub,_,h3u,_,_,h3v,HY⟩ :=
           qB hm l s u _5 h2a hib _b hrb hbf
          by_cases h1a:(pe e:Fin (2*m)->Bool) ⟨kb,_b⟩=true
          ·rcases HY with h|h<;>rw[pJ _ hS _ _5 Hv hP h W W,
            pA f _ kr hS _ kb W,p7 f _ kb _b,h1a]<;>simp
          ·cases hmod_ub:pl f (pe e:Fin (2*m)->Bool) kr (p0 f (pe e:Fin (2*m)->Bool) d) (2*m+ub) with
           | true=>rcases HY with h|h<;>rw[pJ _ hS _ _5 Hv hP h W W,hmod_ub]<;>simp
           | false=>
            exfalso
            have HZ:e=ib:=by
             have h1:=(qo hib _b he).1 ((cf hbf _).symm.trans hbp);simp only[pe,e2,decide_eq_true_eq] at h1a;O
            have HE:ib≠i:=fun h=>by
             subst h;have _c:tb≠kv:=fun heq=>h3b (by rcases h0f with ⟨h1,h2⟩|⟨h1,h2⟩<;>rw[h1,h2,heq])
             have h3g:kb≠k0:=fun _6=>by subst _6;X qy l _5 HA _c (hbf.trans hJ.symm)
             have h0h:pq (2*m) (e2 k0 kb)=true:=by
              obtain ⟨S_a,_,_,hSa⟩:=h0e
              Y pT (S:=S_a) (by
               rw[←cf hSa (e2 k0 kb:Fin (2*m)->Bool)];change p0 f (e2 k0 kb:Fin (2*m)->Bool) (2*m+a)=true;rw[pm _ ha hI HX H8 H2,Bool.and_eq_true]
               have _g:p0 f (e2 k0 kb:Fin (2*m)->Bool) (2*m+kv)=true:=by
                rw[show p0 f _ (2*m+kv)=_ from cf hJ _,qh hi hZ];simp[e2]
               have _h:p0 f (e2 k0 kb:Fin (2*m)->Bool) (2*m+tb)=true:=by
                rw[show p0 f _ (2*m+tb)=_ from cf hbf _,qh hib _b];simp[e2]
               rcases h0f with ⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>[X ⟨_g,_h⟩;X ⟨_h,_g⟩])
             rw[px] at h0h;obtain ⟨u1,v1,h3w,hu1,hv1⟩:=h0h;simp only[e2,decide_eq_true_eq] at hu1 hv1;rcases hM with rfl|_<;>rcases hrb with rfl|_<;>O
            have _t:p8 f ub (pe e:Fin (2*m)->Bool)=true:=by
             have h2b:(pe e:Fin (2*m)->Bool) ⟨kb,_b⟩=false:=by
              cases h':(pe e:Fin (2*m)->Bool) ⟨kb,_b⟩
              ·rfl
              ·X absurd h' h1a
             change p0 f (pe e:Fin (2*m)->Bool) (2*m+ub)=true
             rcases HY with h|h<;>rw[p6 _ _5 hP h W W,
              p7 f _ kb _b,h2b] at hbp<;>simpa using hbp
            obtain ⟨Skr,h1b,_d,He⟩:=Ht
            have hC:∀e'∈Su,e'∈Skr:=fun e' Hr=>(pg _d (Hi e' Hr)).1 (by
             rw[←cf He _]
             X (pQ hm l s u H0 hS ⟨Su,HB,Hi,hA⟩ Hs).2.2 _
              (by rw[cf hA _];X (pg Hi (Hi e' Hr)).2 Hr))
            obtain ⟨e1',Hw,H3⟩:∃e1',e1'∈Skr/\e1'∉Su:=by
             by_contra h2c;push Not at h2c
             X qy l hS H0 (by have:=Hs.2;O)
              (He.trans (by rw[hA];congr 1;ext e';X ⟨h2c e',hC e'⟩))
            have _u:∀w,w< 2*m+f.size ->
              pl f (pe e:Fin (2*m)->Bool) kr (p0 f (pe e:Fin (2*m)->Bool) d) w≠p0 f (pe e:Fin (2*m)->Bool) w ->
              ∃g,∃(_:g< f.size),w=2*m+g/\q1 m (p8 f g) /\
               (∀e'∈Skr,p8 f g (pe e':Fin (2*m)->Bool)=true):=by
             intro w;induction w using Nat.strong_induction_on with
             | ind w ih=>
              intro hw _v;by_cases hlt:w< 2*m+kr
              ·X absurd (pA f _ kr hS _ w hlt) _v
              ·by_cases heq:w=2*m+kr
               ·X ⟨kr,hS,heq,⟨Skr,h1b,_d,He⟩,fun e' Hr=>by rw[cf He _];X (pg _d (_d e' Hr)).2 Hr⟩
               ·set g:=w-2*m;have hg:g< f.size :=W
                have _m:w=2*m+g :=W;rw[_m] at _v ⊢;rcases pc l hD g hg with ⟨hF,_,_,_⟩|⟨Hd,x1,x2,HF,_F,_G,_⟩
                ·X absurd hF (u.1 _ (List.getElem_mem hg))
                ·have hch:pl f (pe e:Fin (2*m)->Bool) kr (p0 f (pe e:Fin (2*m)->Bool) d) x1≠p0 f (pe e:Fin (2*m)->Bool) x1 \/
                   pl f (pe e:Fin (2*m)->Bool) kr (p0 f (pe e:Fin (2*m)->Bool) d) x2≠p0 f (pe e:Fin (2*m)->Bool) x2:=by
                  by_contra hsame;push Not at hsame;apply _v
                  rcases Hd with hop_eq|hop_eq
                  ·rw[pF _ hS _ hg W hop_eq HF _F _G,pm _ hg hop_eq HF _F _G,hsame.1,hsame.2]
                  ·rw[pJ _ hS _ hg W hop_eq HF _F _G,p6 _ hg hop_eq HF _F _G,hsame.1,hsame.2]
                 have HD:∀x0,(x0=x1\/x0=x2)->x0< 2*m+g ->
                   pl f (pe e:Fin (2*m)->Bool) kr (p0 f (pe e:Fin (2*m)->Bool) d) x0≠p0 f (pe e:Fin (2*m)->Bool) x0 ->
                   ∃g',∃(_:g'< f.size),2*m+g=2*m+g'/\q1 m (p8 f g') /\
                    (∀e'∈Skr,p8 f g' (pe e':Fin (2*m)->Bool)=true):=fun x0 hm' hx0 h3h=>by
                  obtain ⟨gx,hgx,rfl,_w,H4⟩:=ih x0 W W h3h
                  have h2d:pC (2*m) g (2*m+gx) (f.gates[g]'hg) :=
                   ⟨by rcases Hd with hop|hop<;>rcases hm' with rfl|rfl<;>simp[pa,hop,HF],hx0⟩
                  obtain ⟨_,h3i|h3j,h2e⟩:=pQ hm l s u hgx hg _w h2d
                  ·X ⟨g,hg,rfl,h3i,fun e' Hr=>h2e _ (H4 e' Hr)⟩
                  ·X absurd h3j (qU hm l s u hgx hg hi hib (_d e1' Hw)
                    HE.symm (fun h=>H3 (h▸H7)) (fun h=>H3 (h▸HZ▸hpS)) _w
                    (H4 i (hC i H7)) (H4 ib (hC ib (HZ▸hpS))) (H4 e1' Hw) h2d)
                 rcases hch with h|h<;>[X HD x1 (il rfl) _F h;X HD x2 (ir rfl) _G h]
            obtain ⟨g',hg',hK,h1c,Hx⟩:=_u (2*m+ub) W (by rw[hmod_ub,show p0 f (pe e) (2*m+ub)=true from _t];decide)
            have h1d:ub=g' :=W;subst h1d
            X qU hm l s u hg' _5 hi hib (_d e1' Hw)
             HE.symm (fun h=>H3 (h▸H7)) (fun h=>H3 (h▸HZ▸hpS)) h1c
             (Hx i (hC i H7)) (Hx ib (hC ib (HZ▸hpS))) (Hx e1' Hw)
             ⟨by rcases HY with h|h<;>simp[pa,hP,h],by O⟩ ⟨ib,kb,h2a,hib,_b,hrb,hbf⟩
       rcases h29 with rfl|rfl
       ·X ⟨hX,hY c2 H2 (il ⟨rfl,rfl⟩) Hj.2 h17⟩
       ·X ⟨hY c1 H8 (ir ⟨rfl,rfl⟩) Hj.1 h16,hX⟩
     X zo hm l s u rfl rfl (by have:=_E.2;O) ha hS
      (fun _ _ _=>rfl) _f hi hZ hM Hu hJ h0e h10 h12
      (fun v hv hav _ h1e hrv=>by
       have hrm:2*m+v∈pa (f.gates[kr]'hS):=hrv.1
       have hvd:2*m+v=d:=by
        have HG:2*m+v≠2*m+ku:=by have:=_E.2;O
        rcases Hc with h|h
        ·simp only[pa,hO,h,List.mem_cons,List.not_mem_nil,or_false] at hrm
         rcases hrm with h1|h2;X absurd h1 HG;X h2
        ·simp only[pa,hO,h,List.mem_cons,List.not_mem_nil,or_false] at hrm
         rcases hrm with h1|h2;X h1;X absurd h2 HG
       rw[←hvd,←pA f _ kr hS _ (2*m+v) hrv.2];X h1e)
   ·
    have _0:∀a (ha:a< f.size),pC (2*m) a (2*m+kv) (f.gates[a]'ha) ->
      (f.gates[a]'ha).op=.and /\
      ((k0=i+2/\p8 f a=ph m {i,i+1} /\
       ((f.gates[a]'ha).inputs=[2*m+kv,i+1]\/(f.gates[a]'ha).inputs=[i+1,2*m+kv])) \/
       (k0+1=i/\p8 f a=ph m {i-1,i} /\
       ((f.gates[a]'ha).inputs=[2*m+kv,i]\/(f.gates[a]'ha).inputs=[i,2*m+kv]))):=by
     intro a ha _E;obtain ⟨hI,HL⟩:=qr hm l s u HA ha _f hi hZ hM hJ _E;Y ⟨hI,?_⟩;rcases HL with ⟨hW,⟨hR,h1f⟩|⟨_,hR⟩⟩|⟨_X,⟨hR,h1f⟩|⟨_,hR⟩⟩
     ·X il ⟨hW,hR,h1f⟩
     ·X absurd ⟨a,ha,_E,fun x _x=>by
       rw[cf hA x,po] at _x;rw[cf hR x,po];obtain ⟨p,q,hp,HM,HN,HO⟩:=_x;have:=hE p.val hp;X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton];O,HM,HN,HO⟩⟩ hT1
     ·X ir ⟨_X,hR,h1f⟩
     ·X absurd ⟨a,ha,_E,fun x _x=>by
       rw[cf hA x,po] at _x;rw[cf hR x,po];obtain ⟨p,q,hp,HM,HN,HO⟩:=_x;have:=hE p.val hp;X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton];O,HM,HN,HO⟩⟩ hT1
    obtain ⟨a0,ha0,h2f,h1g⟩:∃a0,∃(_:a0< f.size),kv< a0/\pC (2*m) a0 (2*m+kv) (f.gates[a0]'‹_›) :=
     (pY l kv HA).resolve_left (qz s ⟨i,k0,_f,hi,hZ,hM,hJ⟩)
    obtain ⟨_1,Hy⟩:=_0 a0 ha0 h1g
    obtain ⟨efar,Hk,z⟩:∃efar,((k0=i+2/\efar=i+2)\/(k0+1=i/\efar=i-2))/\Su={i,efar}:=by
     rcases Hy with ⟨hW,_y,_⟩|⟨_X,_y,_⟩
     ·have h1h:i+2∈Su:=by_contra fun h3k=>hT1 ⟨a0,ha0,h1g,fun x _x=>by
       rw[cf hA x,po] at _x;rw[cf _y x,po];obtain ⟨p,q,hp,HM,HN,HO⟩:=_x;have:=hE p.val hp
       have:p.val≠i+2:=fun h=>h3k (h▸hp)
       X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton];O,HM,HN,HO⟩⟩
      have _Y:i+1∉Su:=fun hi1=>qG l u.1 a0 ha0 (2*m+ku) W
       (fun x hx=>by
        rw[cf _y x,po] at hx;rw[show p0 f x (2*m+ku)=_ from cf hA x,po];obtain ⟨p,q,hp,HM,HN,HO⟩:=hx;simp only[Finset.mem_insert,Finset.mem_singleton] at hp;X ⟨p,q,by rcases hp with h|h<;>rw[h];X H7;X hi1,HM,HN,HO⟩)
       (fun x hx=>by rw[s];X pT (by rw[←cf hA x];X hx))
      Y ⟨i+2,il ⟨hW,rfl⟩,?_⟩;ext e;simp only[Finset.mem_insert,Finset.mem_singleton]
      constructor
      ·intro he;have:=hE e he
       by_cases h:e=i+1
       ·X absurd (h▸he) _Y
       ·O
      ·rintro (rfl|rfl);X H7;X h1h
     ·have _Z:i-2∈Su:=by_contra fun h2g=>hT1 ⟨a0,ha0,h1g,fun x _x=>by
       rw[cf hA x,po] at _x;rw[cf _y x,po];obtain ⟨p,q,hp,HM,HN,HO⟩:=_x;have:=hE p.val hp
       have:p.val≠i-2:=fun h=>h2g (h▸hp)
       X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton];O,HM,HN,HO⟩⟩
      have _z:i-1∉Su:=fun h3l=>qG l u.1 a0 ha0 (2*m+ku) W
       (fun x hx=>by
        rw[cf _y x,po] at hx;rw[show p0 f x (2*m+ku)=_ from cf hA x,po];obtain ⟨p,q,hp,HM,HN,HO⟩:=hx;simp only[Finset.mem_insert,Finset.mem_singleton] at hp;X ⟨p,q,by rcases hp with h|h<;>rw[h];X h3l;X H7,HM,HN,HO⟩)
       (fun x hx=>by rw[s];X pT (by rw[←cf hA x];X hx))
      Y ⟨i-2,ir ⟨_X,rfl⟩,?_⟩;ext e;simp only[Finset.mem_insert,Finset.mem_singleton]
      constructor
      ·intro he;have:=hE e he
       by_cases h:e=i-1
       ·X absurd (h▸he) _z
       ·O
      ·rintro (rfl|rfl);X H7;X _Z
    have hH:(f.gates[ku]'H0).op=.or:=by
     rcases pc l hD ku H0 with ⟨hF,_,_,_⟩|⟨h|h,_,_,_,_,_,_⟩
     ·X absurd hF (u.1 _ (List.getElem_mem H0))
     ·exfalso
      obtain ⟨_,_,_,_,_,_,_,_,_,HJ⟩:=qn hm l s u H0 h;have h1r:i+2=efar\/efar+2=i:=by have:=(ky _f hi hZ hM).1;rcases Hk with ⟨rfl,rfl⟩|⟨_,rfl⟩<;>O
      have _2:∀(T:Finset ℕ),(∀e∈T,e+1< 2*m)->p8 f ku=ph m T->i∈T/\efar∈T:=fun T hT heq=>by
       have hEq:=qM Hi hT (hA.symm.trans heq);rw[z] at hEq;X ⟨hEq▸by simp,hEq▸by simp⟩
      rcases HJ with ⟨e,he,hgf,_⟩|⟨c,H8,H2,hgf,_⟩|⟨i',_,h3x,hgf,_⟩|⟨i',_,h3y,hi',hgf,_⟩|⟨i',_,h3z,hgf,_⟩
      ·have ⟨h1,h2⟩:=_2 {e} (by simp[he]) hgf;simp at h1 h2;O
      ·have ⟨h1,h2⟩:=_2 {c-1,c} (fun x hx=>by simp at hx;O) hgf;simp at h1 h2;O
      ·have ⟨h1,h2⟩:=_2 {i',i'+1} (fun x hx=>by simp at hx;O) hgf;simp at h1 h2;O
      ·have ⟨h1,h2⟩:=_2 {i'-1,i'} (fun x hx=>by simp at hx;O) hgf;simp at h1 h2;O
      ·have hEq:=qM Hi (fun x hx=>by simp at hx;O) (hA.symm.trans hgf);rw[z] at hEq
       have h1:i'∈({i,efar}:Finset ℕ):=hEq.symm▸by simp
       have h2:i'+1∈({i,efar}:Finset ℕ):=hEq.symm▸by simp
       have h3:i'+2∈({i,efar}:Finset ℕ):=hEq.symm▸by simp
       simp at h1 h2 h3;O
     ·X h
    obtain ⟨p2,h1i,_3⟩:∃p2,p2< 2*m+ku/\(fun x=>p0 f x p2)=ph m {efar}:=by
     rcases pc l hD ku H0 with ⟨hF,_,_,_⟩|⟨_,c1,c2,H9,H8,H2,_⟩
     ·rw[hH] at hF;cases hF
     ·have _A:∀c (hc:c< 2*m+ku),
        (∀y:Fin (2*m)->Bool,p0 f y c=true->ph m {i,efar} y=true) ->
        (fun y=>p0 f y c)=ph m {i}\/(fun y=>p0 f y c)=ph m {efar}:=fun c hc _R=>by
       rcases qE u c W with
        ⟨j,hj,_,_9⟩|⟨_,_,_,Sc,h2h,hSc,_9⟩|⟨_,_,_,cb,h18,h19,_9⟩|⟨_,_,_,_,kb,_,_,_b,_,_9⟩
       ·have h1:=_R (e1 j) (by rw[cf _9 _];simp[e1]);rw[pz] at h1;cases h1
       ·have H5:∀e∈Sc,e=i\/e=efar:=fun e he=>by
         simpa using (pg (by rw[←z];X Hi) (hSc e he)).1
          (_R _ (by rw[cf _9 _];X (pg hSc (hSc e he)).2 he))
        by_cases h00:i∈Sc
        ·by_cases _4:efar∈Sc
         ·exfalso;obtain ⟨x,hx⟩:=py l ku H0 c hc
          apply hx;rw[cf hA x,z,cf _9 x];congr 1;ext e;simp only[Finset.mem_insert,Finset.mem_singleton];X ⟨fun h=>by rcases h with rfl|rfl;X h00;X _4,H5 e⟩
         ·left;rw[_9];congr 1;ext e;simp only[Finset.mem_singleton]
          X ⟨fun h=>by rcases H5 e h with rfl|rfl;R;X absurd h _4,fun h=>by rw[h];X h00⟩
        ·right;obtain ⟨e',Hr⟩:=h2h
         have _4:efar∈Sc:=by rcases H5 e' Hr with rfl|rfl;X absurd Hr h00;X Hr
         rw[_9];congr 1;ext e;simp only[Finset.mem_singleton];X ⟨fun h=>by rcases H5 e h with rfl|rfl;X absurd h h00;rfl,fun h=>by rw[h];X _4⟩
       ·have h1:=_R (e1 (cb-1)) (by rw[cf _9 _];X (pu h18 h19 W).2 (il W))
        rw[pz] at h1;cases h1
       ·have h1:=_R (e1 kb) (by rw[cf _9 _];X (pN _b _b).2 rfl)
        rw[pz] at h1;cases h1
      have h1:=_A c1 H8 fun y hy=>by
       rw[←z,←cf hA y];change p0 f y (2*m+ku)=true;rw[p6 y H0 hH H9 H8 H2,hy];R
      have h2:=_A c2 H2 fun y hy=>by
       rw[←z,←cf hA y];change p0 f y (2*m+ku)=true;rw[p6 y H0 hH H9 H8 H2,hy,Bool.or_true]
      rcases h1 with h1|h1
      ·rcases h2 with h2|h2
       ·exfalso;obtain ⟨x,hx⟩:=py l ku H0 c1 H8
        X hx (by change p0 f x (2*m+ku)=_;rw[p6 x H0 hH H9 H8 H2,cf h1 x,cf h2 x,Bool.or_self])
       ·X ⟨c2,H2,h2⟩
      ·X ⟨c1,H8,h1⟩
    let gStar:Gate:=if k0=i+2 then ⟨.or,[i,i+2]⟩ else ⟨.or,[i-1,i+1]⟩;have _e:Ok gStar:=by unfold gStar;split_ifs<;>X ⟨by simp,by simp⟩
    set D:=pU f kv gStar;have h01:D.size=f.size:=pS f kv gStar
    have HP:∀x:Fin (2*m)->Bool,∀w< 2*m+f.size,w≠2*m+kv->p0 D x w=p0 f x w:=fun x=>
     qP f HA gStar x fun t ht _=>by
      rcases pc l hD t ht with ⟨hF,_,_,_⟩|⟨Hd,x1,x2,Hl,_F,_G,_⟩
      ·X absurd hF (u.1 _ (List.getElem_mem ht))
      ·by_cases hrt:pC (2*m) t (2*m+kv) (f.gates[t]'ht)
       ·obtain ⟨h1j,h1k⟩:=_0 t ht hrt
        rw[pj f x t ht,h1j,Hl];simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,_F,_G,↓reduceIte]
        have hL:p0 (pU f kv gStar) x (2*m+kv)=if hW:k0=i+2 then (x ⟨i,by O⟩||x ⟨i+2,by O⟩) else (x ⟨i-1,by O⟩||x ⟨i+1,hi⟩):=by
         rw[qg f x HA];unfold gStar
         split_ifs with hW
         ·simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
           show i< 2*m+kv by O,show i+2< 2*m+kv by O,↓reduceIte,
           p7 f x i W,p7 f x (i+2) W]
         ·simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
           show i-1< 2*m+kv by O,show i+1< 2*m+kv by O,↓reduceIte,
           p7 f x (i-1) W,p7 f x (i+1) hi]
        rcases h1k with ⟨hW,_,_B⟩|⟨_X,_,_B⟩
        ·rw[dif_pos hW] at hL
         have _C:p0 f x (2*m+kv)=((x ⟨i,by O⟩&&x ⟨i+1,hi⟩)||x ⟨i+2,by O⟩):=by
          rw[show p0 f x (2*m+kv)=qd m i k0 x from cf hJ x,qh hi hZ]
          have:(⟨k0,hZ⟩:Fin (2*m))=⟨i+2,by O⟩:=Fin.ext hW;rw[this]
         rcases _B with h|h<;>rw[Hl] at h <;>
          (injection h with _g hrest';injection hrest' with _h;rw[_g,_h];
           simp only[↓reduceIte,show i+1≠2*m+kv by O,hL,_C,p7 f x (i+1) hi];
           cases x ⟨i,by O⟩<;>cases x ⟨i+1,hi⟩<;>cases x ⟨i+2,by O⟩<;>rfl)
        ·rw[dif_neg (by O:k0≠i+2)] at hL
         have _C:p0 f x (2*m+kv)=((x ⟨i,by O⟩&&x ⟨i+1,hi⟩)||x ⟨i-1,by O⟩):=by
          rw[show p0 f x (2*m+kv)=qd m i k0 x from cf hJ x,qh hi hZ]
          have:(⟨k0,hZ⟩:Fin (2*m))=⟨i-1,by O⟩:=Fin.ext (by dsimp;O);rw[this]
         rcases _B with h|h<;>rw[Hl] at h <;>
          (injection h with _g hrest';injection hrest' with _h;rw[_g,_h];
           simp only[↓reduceIte,show i≠2*m+kv by O,hL,_C,p7 f x i W];
           cases x ⟨i-1,by O⟩<;>cases x ⟨i,by O⟩<;>cases x ⟨i+1,hi⟩<;>rfl)
       ·have h1l:x1≠2*m+kv:=fun h=>hrt ⟨by rcases Hd with hop|hop<;>simp[pa,hop,Hl,h],h▸_F⟩
        have h1m:x2≠2*m+kv:=fun h=>hrt ⟨by rcases Hd with hop|hop<;>simp[pa,hop,Hl,h],h▸_G⟩
        rw[pj f x t ht,Hl];simp only[List.map_cons,List.map_nil,_F,_G,h1l,h1m,↓reduceIte]
    have _D:cF (2*m) D=pq (2*m):=funext fun x=>
     (HP x f.output (pB hD) (qz s ⟨i,k0,_f,hi,hZ,hM,hJ⟩)).trans (cf s x)
    have h2i:=qC l gStar _e (_D.trans s.symm);have h3m:z0 D:=zA u.1 kv (by unfold gStar;split_ifs<;>(intro h;cases h))
    have Hf:ku< D.size:=by rw[h01];X H0
    Y qN h2i h3m _D Hf h1i (fun x h1=>by
     rw[qc f x kv gStar p2 W,cf _3 x] at h1
     rw[qc f x kv gStar (2*m+ku) W,
      show p0 f x (2*m+ku)=_ from cf hA x,z,zu,h1,Bool.or_true]) fun e he=>?_
    by_cases hpi:e=i
    ·have hX:pl D (pe e:Fin (2*m)->Bool) ku (p0 D (pe e:Fin (2*m)->Bool) p2) (2*m+kv)=true:=by
      have h2j:kv< D.size:=by rw[h01];X HA
      have hK:D.gates[kv]'h2j=gStar:=List.getElem_set_self _;rw[zs D _ ku Hf _ kv h2j W,hK];unfold gStar
      split_ifs with hW
      ·simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
        show i< 2*m+kv by O,show i+2< 2*m+kv by O,↓reduceIte]
       rw[pA D (pe e:Fin (2*m)->Bool) ku Hf _ i W,
        p7 D (pe e:Fin (2*m)->Bool) i W,hpi];simp[pe,e2]
      ·simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
        show i-1< 2*m+kv by O,show i+1< 2*m+kv by O,↓reduceIte]
       rw[pA D (pe e:Fin (2*m)->Bool) ku Hf _ (i+1) W,
        p7 D (pe e:Fin (2*m)->Bool) (i+1) hi,hpi];simp[pe,e2]
     have h02:pl D (pe e:Fin (2*m)->Bool) ku (p0 D (pe e:Fin (2*m)->Bool) p2) (2*m+a0)=true:=by
      have h1n:a0< D.size:=by rw[h01];X ha0
      have hK:D.gates[a0]'h1n=f.gates[a0]'ha0:=List.getElem_set_ne (by O:kv≠a0) _
      rcases Hy with ⟨_,_,HQ⟩|⟨_,_,HQ⟩
      ·rcases HQ with h|h<;>rw[pF _ Hf _ h1n W (hK.symm▸_1) (hK.symm▸h) W W,
        hX,pA D _ ku Hf _ (i+1) W,p7 D _ (i+1) hi,hpi]<;>simp[pe,e2]
      ·rcases HQ with h|h<;>rw[pF _ Hf _ h1n W (hK.symm▸_1) (hK.symm▸h) W W,
        hX,pA D _ ku Hf _ i W,p7 D _ i W,hpi]<;>simp[pe,e2]
     obtain ⟨e0,Hu,h1o,h03⟩:∃e0,((k0=i+2/\e0=i)\/(k0+1=i/\e0=k0)) /\
       q1 m (p8 f a0) /\
       (∀y:Fin (2*m)->Bool,ph m {e0,e0+1} y=true->p8 f a0 y=true):=by
      rcases Hy with ⟨hW,hR,_⟩|⟨_X,hR,_⟩
      ·X ⟨i,il ⟨hW,rfl⟩,⟨{i,i+1},⟨i,by simp⟩,fun e' Hr=>by simp at Hr;O,hR⟩,fun y hy=>by rw[cf hR y];X hy⟩
      ·X ⟨k0,ir ⟨_X,rfl⟩,⟨{i-1,i},⟨i,by simp⟩,fun e' Hr=>by simp at Hr;O,hR⟩,fun y hy=>by rw[cf hR y];convert hy using 2;ext e';simp;O⟩
     X zo hm l s u h01 rfl h2f ha0 Hf
      (fun t ht hat=>List.getElem_set_ne (by O:kv≠t) _) _f hi hZ hM Hu hJ h1o h03 h02
      (fun _ _ _ _ _ hrv=>by have:=hrv.2;O)
    ·have h1p:p0 D (pe e:Fin (2*m)->Bool) p2=p0 D (pe e:Fin (2*m)->Bool) (2*m+ku):=by
      rw[qc f _ kv gStar p2 W,qc f _ kv gStar (2*m+ku) W,
       cf _3 _,show p0 f _ (2*m+ku)=_ from cf hA _,z]
      apply Bool.eq_iff_iff.2
      rw[pg (by simp;have:=(ky _f hi hZ hM).2;rcases Hk with ⟨rfl,rfl⟩|⟨_,rfl⟩<;>O) he,
       pg (by rw[←z];X Hi) he];simp[hpi]
     rw[pV D _ ku Hf _ h1p,←pb,_D,q0 he]
private lemma ke {m:ℕ} (hm:1<=m) {e:J}
  (d:IsMinimalCircuit (2*m+1) e)
  (l:∀x:Fin (2*m+1)->Bool,
   cF (2*m+1) e x=(x (Fin.last (2*m))||pq (2*m) (Fin.init x)))
  (t:qf m (p3 e (2*m) false)) :
  let p:=p3 e (2*m) false;let v:=p5 e (2*m) false
  z0 e/\IsMinimalCircuit (2*m) p/\p.size+1=e.size /\
  cF (2*m) p=pq (2*m) /\
  (∃hE:ℕ,∃(hD:hE< e.size),
   (∀k (hk:k< e.size),pC (2*m+1) k (2*m) (e.gates[k]'hk)↔k=hE) /\
   (∀k (hk:k< e.size),v.fb[k]'(by rw[(pk e (2*m) false d.1).kept_len];X hk)=false↔k=hE) /\
   (e.gates[hE]'hD).op=.or /\
   ∃hJ:ℕ,hJ< 2*m+1+hE/\hJ≠2*m /\
    ((e.gates[hE]'hD).inputs=[2*m,hJ]\/(e.gates[hE]'hD).inputs=[hJ,2*m]) /\
    ∃g:ℕ,g< p.size /\
     v.fc.getD (2*m+1+hE) (.const false)=.wire (2*m+g) /\
     v.fc.getD hJ (.const false)=.wire (2*m+g) /\
     q1 m (p8 p g)) /\
  (∀k (hk:k< e.size),p0 e (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true ->
   (e.gates[k]'hk).op=.or) /\
  (∀k (hk:k< e.size),p0 e (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true ->
   ∃w''',v.fc.getD (2*m+1+k) (.const false)=.wire w''' /\
    q1 m (fun y=>p0 p y w''')):=by
 have q:∀y:Fin (2*m)->Bool,cF (2*m+1) e (Fin.snoc y false)=pq (2*m) y:=fun y=>by
  rw[l,Fin.snoc_last,Fin.init_snoc];R
 have He:∃y:Fin (2*m)->Bool,cF (2*m+1) e (Fin.snoc y false)≠cF (2*m+1) e (Fin.snoc y true) :=
  ⟨e0,by rw[q,l,Fin.snoc_last,zq];simp⟩
 have hO:∃y1 y2:Fin (2*m)->Bool,cF (2*m+1) e (Fin.snoc y1 false)≠cF (2*m+1) e (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,hX⟩:=ps (n:=2*m) W;X ⟨y1,y2,by rw[q,q];X hX⟩
 have hK:∃x1 x2:Fin (2*m+1)->Bool,cF (2*m+1) e x1≠cF (2*m+1) e x2:=by
  obtain ⟨y1,y2,hX⟩:=hO;X ⟨Fin.snoc y1 false,Fin.snoc y2 false,hX⟩
 have Hl:e.size=3*m-1:=by
  have Hv:=zl (pq (2*m)) (ps W) (fun _ _ _ _ h=>h) (3*m-2)
   (fun E Hf Ho=>by
    have h:=q9 (2*m) W E Hf Ho;simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left m (by O:0< 2)] at h;X h)
   e d.1 l
  obtain ⟨D0,hY,hZ,H0⟩:=ko (jq m)
   (by rw[zS m hm];X ps W)
  have Hw:=d.2 D0 hY (funext fun x=>by rw[H0 x,zS m hm,l x])
  rw[jf m hm] at hZ;O
 have Hg:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m)->Bool,cF (2*m) D y=cF (2*m+1) e (Fin.snoc y false)) ->
   e.size<=D.size+1:=fun D Hh hS=>by
  have Hi:=q9 (2*m) W D Hh (funext fun y=>(hS y).trans (q y));simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left m (by O:0< 2)] at Hi;O
 obtain ⟨hh,hT,hE,hD,u,f,hF,hJ,H1,H2,H3,hL⟩ :=
  zV (n:=2*m) d false He hO Hg
 simp only[Bool.false_eq_true,↓reduceIte] at hF;set v:=p5 e (2*m) false;set p:=p3 e (2*m) false
 have hA:cF (2*m) p=pq (2*m) :=
  funext fun y=>(q6 e (2*m) false d.1 hO y).trans (q y)
 have hG:z0 e:=qK d.1 t.1 fun k hk H4=>by
  have Ha:=(f k hk).1 H4;subst Ha;rw[hF];intro h;cases h
 obtain ⟨hP,hM,r⟩:∃w''',w'''< 2*m+p.size/\v.fc.getD hJ (.const false)=.wire w''':=by
  by_cases Hp:hJ< 2*m+1
  ·X ⟨hJ,by O,pd e (2*m) false hJ W⟩
  ·set kz:=hJ-(2*m+1);have Hb:kz< e.size :=W
   have H5:=q4 d.1 f Hb W;obtain ⟨g,w,_,H6,_,_,_⟩:=p4 d.1 Hb H5;X ⟨2*m+g,Nat.add_lt_add_left w _,by rw[show hJ=2*m+1+kz by O];X H6⟩
 have z:∀a< 2*m,p0 p (e1 a:Fin (2*m)->Bool) hP=false:=fun a ha=>by
  cases hv:p0 p (e1 a:Fin (2*m)->Bool) hP with
  | false=>rfl
  | true=>
   exfalso
   have H7:p0 e (Fin.snoc (e1 a:Fin (2*m)->Bool) false) (2*m+1+hE)=true:=by
    have Hm:=pH e (2*m) false d.1 (e1 a:Fin (2*m)->Bool) (2*m+1+hE);rw[hL,r] at Hm;X Hm.symm.trans hv
   have H8:∀i,i< 2*m+1+e.size->i≠2*m ->
     p0 e (e1 (2*m):Fin (2*m+1)->Bool) i=true ->
     p0 e (Fin.snoc (e1 a:Fin (2*m)->Bool) false) i=true:=by
    intro i;induction i using Nat.strong_induction_on with
    | ind i ih=>
     intro hi hX h1;by_cases Hq:i< 2*m+1
     ·rw[p7 e _ i Hq] at h1;simp[e1,hX] at h1
     ·set k:=i-(2*m+1);have hk:k< e.size :=W
      have H9:i=2*m+1+k :=W;rw[H9] at h1 ⊢;by_cases Ha:k=hE
      ·rw[Ha];X H7
      ·rcases pc d hK k hk with ⟨Hj,_,_,_⟩|⟨hN,a1,a2,hU,Hc,Hd,_⟩
       ·X absurd Hj (hG _ (List.getElem_mem hk))
       ·have hH:∀b,(b=a1\/b=a2)->b< 2*m+1+k->b≠2*m:=fun b Hr Hs h=>
         Ha ((u k hk).1 ⟨by rcases hN with Hn|Hn<;>rcases Hr with rfl|rfl<;>simp[pa,Hn,hU,h],h▸Hs⟩)
        rcases hN with hop_eq|hop_eq
        ·rw[pm _ hk hop_eq hU Hc Hd,Bool.and_eq_true] at h1 ⊢
         X ⟨ih a1 W W (hH a1 (il rfl) Hc) h1.1,
          ih a2 W W (hH a2 (ir rfl) Hd) h1.2⟩
        ·rw[p6 _ hk hop_eq hU Hc Hd,Bool.or_eq_true] at h1 ⊢
         rcases h1 with h|h<;>[X il (ih a1 W W (hH a1 (il rfl) Hc) h);
          X ir (ih a2 W W (hH a2 (ir rfl) Hd) h)]
   have hQ:e.output≠2*m:=fun h=>
    pL d.1 hO (p9 e (2*m) false d.1) h
   have hV:=H8 e.output (pB hK) hQ (by change cF (2*m+1) e (e1 (2*m))=true;rw[l];simp[e1,Fin.last])
   change cF (2*m+1) e (Fin.snoc (e1 a) false)=true at hV;rw[q,pW] at hV;cases hV
 obtain ⟨g,w,hC,s⟩:∃g,g< p.size/\hP=2*m+g/\q1 m (p8 p g):=by
  rcases qE t hP hM with
   ⟨j,hj,_,hW⟩|⟨kz,Hb,rfl,hW⟩|⟨_,_,_,c,Ht,Hu,hW⟩|⟨_,_,_,_,k0,_,_,Hk,_,hW⟩
  ·have:=z j hj;rw[cf hW _] at this;simp[e1] at this
  ·X ⟨kz,Hb,rfl,hW⟩
  ·have:=z (c-1) W;rw[cf hW _,(pu Ht Hu W).2 (il W)] at this;cases this
  ·have:=z k0 Hk;rw[cf hW _,(pN Hk Hk).2 rfl] at this;cases this
 have hB:v.fc.getD (2*m+1+hE) (.const false)=.wire (2*m+g) :=
  hL.trans (r.trans (by rw[hC]))
 have hI:=jZ hm d hG hK hh hA t hD w u f hF hB s;have hR:=kd hm d hG l hh hA t hD w u f hB s hI
 X ⟨hG,hh,hT,hA,
  ⟨hE,hD,u,f,hF,hJ,H1,H2,H3,g,w,hB,r.trans (by rw[hC]),s⟩,
  hI,hR⟩
private structure zB (m:ℕ) (C:J) where
 hm:1<=m
 f0:IsMinimalCircuit (2*m+2) C
 fd:cF (2*m+2) C=pq (2*m+2)
 fJ:z0 C
 fn:∃x1 x2:Fin (2*m+2)->Bool,cF (2*m+2) C x1≠cF (2*m+2) C x2
 f3:ℕ
 f4:ℕ
 w:ℕ
 u:ℕ
 f9:f3< C.size
 fa:f4< C.size
 fP:f3< f4
 fi:∀t (ht:t< C.size),pC (2*m+2) t (2*m+1) (C.gates[t]'ht)↔t=f3
 fl:(C.gates[f3]'f9).op=.or
 fs:w< 2*m+2+f3
 fM:w≠2*m+1
 ft:(C.gates[f3]'f9).inputs=[2*m+1,w]\/(C.gates[f3]'f9).inputs=[w,2*m+1]
 fh:(p5 C (2*m+1) true).fc.getD (2*m+2+f3) (.const false)=.const true
 fe:∀t (ht:t< C.size),
  (p5 C (2*m+1) true).fb[t]'(by rw[(pk C (2*m+1) true f0.1).kept_len];X ht)=false ↔
  (t=f3\/t=f4)
 fj:∀t (ht:t< C.size),pC (2*m+2) t (2*m+2+f3) (C.gates[t]'ht)↔t=f4
 fm:(C.gates[f4]'fa).op=.and
 fu:u< 2*m+2+f4
 fU:u≠2*m+2+f3
 fy:(C.gates[f4]'fa).inputs=[2*m+2+f3,u]\/(C.gates[f4]'fa).inputs=[u,2*m+2+f3]
 fz:(p5 C (2*m+1) true).fc.getD (2*m+2+f4) (.const false) =
      (p5 C (2*m+1) true).fc.getD u (.const false)
 f7:IsMinimalCircuit (2*m+1) (p3 C (2*m+1) true)
 fr:∀y:Fin (2*m+1)->Bool,
  cF (2*m+1) (p3 C (2*m+1) true) y=(y (Fin.last (2*m))||pq (2*m) (Fin.init y))
 fC:z0 (p3 C (2*m+1) true)
 fq:∃y1 y2:Fin (2*m+1)->Bool,
  cF (2*m+1) (p3 C (2*m+1) true) y1≠cF (2*m+1) (p3 C (2*m+1) true) y2
 fO:∃y1 y2:Fin (2*m)->Bool,
  cF (2*m+1) (p3 C (2*m+1) true) (Fin.snoc y1 false) ≠
   cF (2*m+1) (p3 C (2*m+1) true) (Fin.snoc y2 false)
 fN:∃y1 y2:Fin (2*m+1)->Bool,
  cF (2*m+2) C (Fin.snoc y1 true)≠cF (2*m+2) C (Fin.snoc y2 true)
 f5:IsMinimalCircuit (2*m) (p3 (p3 C (2*m+1) true) (2*m) false)
 f8:cF (2*m) (p3 (p3 C (2*m+1) true) (2*m) false)=pq (2*m)
 f6:qf m (p3 (p3 C (2*m+1) true) (2*m) false)
 fv:ℕ
 fD:fv< (p3 C (2*m+1) true).size
 fB:∀k (hk:k< (p3 C (2*m+1) true).size),
  pC (2*m+1) k (2*m) ((p3 C (2*m+1) true).gates[k]'hk)↔k=fv
 ff:∀k (hk:k< (p3 C (2*m+1) true).size),
  (p5 (p3 C (2*m+1) true) (2*m) false).fb[k]'(by rw[(pk (p3 C (2*m+1) true) (2*m) false f7.1).kept_len];X hk)=false↔k=fv
 fI:((p3 C (2*m+1) true).gates[fv]'fD).op=.or
 z'':ℕ
 fg:ℕ
 fA:fg< (p3 (p3 C (2*m+1) true) (2*m) false).size
 fw:z''< 2*m+1+fv
 fR:z''≠2*m
 fK:((p3 C (2*m+1) true).gates[fv]'fD).inputs=[2*m,z''] \/
      ((p3 C (2*m+1) true).gates[fv]'fD).inputs=[z'',2*m]
 fx:(p5 (p3 C (2*m+1) true) (2*m) false).fc.getD (2*m+1+fv) (.const false) =
       .wire (2*m+fg)
 fL:(p5 (p3 C (2*m+1) true) (2*m) false).fc.getD z'' (.const false) =
       .wire (2*m+fg)
 fF:q1 m (p8 (p3 (p3 C (2*m+1) true) (2*m) false) fg)
 fk:∀k (hk:k< (p3 C (2*m+1) true).size),
  p0 (p3 C (2*m+1) true) (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true ->
  ((p3 C (2*m+1) true).gates[k]'hk).op=.or
 fS:∀k (hk:k< (p3 C (2*m+1) true).size),
  p0 (p3 C (2*m+1) true) (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+k)=true ->
  ∃w''':ℕ,
   (p5 (p3 C (2*m+1) true) (2*m) false).fc.getD (2*m+1+k) (.const false)=.wire w''' /\
   q1 m (fun y=>p0 (p3 (p3 C (2*m+1) true) (2*m) false) y w''')
 fp:∀k (hk:k< (p3 C (2*m+1) true).size),
  ((p3 C (2*m+1) true).gates[k]'hk).op=.and ->
  ∀a,pC (2*m+1) k a ((p3 C (2*m+1) true).gates[k]'hk) ->
   p0 (p3 C (2*m+1) true) (e1 (2*m):Fin (2*m+1)->Bool) a=false
 fo:zG C (2*m+1) C.output
 fH:zG C (2*m+1) u
 fT:zG C (2*m+1) (2*m+2+f4)
 fE:¬zG C (2*m+1) w
private lemma kA {m:ℕ} (hm:1<=m) {C:J}
  (p:IsMinimalCircuit (2*m+2) C) (hfun:cF (2*m+2) C=pq (2*m+2))
  {d w:ℕ} (c:d< C.size)
  (s:∀t (ht:t< C.size),pC (2*m+2) t (2*m+1) (C.gates[t]'ht)↔t=d)
  (hF:(C.gates[d]'c).op=.or)
  (hG:w< 2*m+2+d) (H4:w≠2*m+1)
  (hQ:(C.gates[d]'c).inputs=[2*m+1,w]\/(C.gates[d]'c).inputs=[w,2*m+1])
  (HN:∀D:J,IsMinimalCircuit (2*m) D->cF (2*m) D=pq (2*m)->qf m D) :
  Nonempty (zB m C):=by
 have HO:C.size=3*m+1:=by have:=zr (m:=m+1) W p hfun;O
 have Hj:∃x1 x2:Fin (2*m+2)->Bool,cF (2*m+2) C x1≠cF (2*m+2) C x2:=by
  rw[hfun];X ps W
 have l:∀y:Fin (2*m+1)->Bool,
   cF (2*m+2) C (Fin.snoc y true)=(y (Fin.last (2*m))||pq (2*m) (Fin.init y)):=fun y=>by
  rw[hfun,qT (2*m+1) W y];R
 have hR:∃y1 y2:Fin (2*m+1)->Bool,
   cF (2*m+2) C (Fin.snoc y1 true)≠cF (2*m+2) C (Fin.snoc y2 true):=by
  Y ⟨e0,e1 (2*m),?_⟩;rw[l,l];have h0:(e0:Fin (2*m+1)->Bool) (Fin.last (2*m))=false:=rfl;have h1:(e1 (2*m):Fin (2*m+1)->Bool) (Fin.last (2*m))=true:=by simp[e1]
  have HP:Fin.init (e0:Fin (2*m+1)->Bool)=e0:=rfl;rw[h0,h1,HP,zq];simp
 have i:(p5 C (2*m+1) true).fc.getD (2*m+2+d) (.const false)=.const true:=by
  have HH:=(pR (n:=2*m+1) (b:=true) p.1 c).2.2 hF;have H5:=p9 C (2*m+1) true p.1;rcases hQ with hins|hins
  ·X ((HH (2*m+1) w hins W hG).1 (il H5)).1
  ·X ((HH w (2*m+1) hins hG W).1 (ir H5)).1
 have Hv:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m+1)->Bool,cF (2*m+1) D y=cF (2*m+2) C (Fin.snoc y true)) ->
   C.size<=D.size+2:=fun D Hc Hw=>by
  have HQ:=zl (pq (2*m)) (ps W) (fun _ _ _ _ h=>h) (3*m-2)
   (fun E Hx HR=>by
    have h:=q9 (2*m) W E Hx HR;simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left m (by O:0< 2)] at h;X h)
   D Hc (fun y=>(Hw y).trans (l y))
  O
 obtain ⟨f,HI,H6,hK,Hy,hH,q,hI,u,hS,Hk,hT,hA⟩ :=
  zh (n:=2*m+1) p true true hR d c ((s d c).2 rfl) i Hv
 simp only[↓reduceIte] at hI;set x:=p3 C (2*m+1) true
 have g:∀y:Fin (2*m+1)->Bool,
   cF (2*m+1) x y=(y (Fin.last (2*m))||pq (2*m) (Fin.init y)):=fun y=>by
  rw[q6 C (2*m+1) true p.1 hR y,l]
 have H7:∃y1 y2:Fin (2*m+1)->Bool,cF (2*m+1) x y1≠cF (2*m+1) x y2:=by
  obtain ⟨y1,y2,Hz⟩:=hR;X ⟨y1,y2,by rw[g,g,←l,←l];X Hz⟩
 have e:∀y:Fin (2*m)->Bool,cF (2*m+1) x (Fin.snoc y false)=pq (2*m) y:=fun y=>by
  rw[g,Fin.snoc_last,Fin.init_snoc];R
 have Hd:∃y:Fin (2*m)->Bool,
   cF (2*m+1) x (Fin.snoc y false)≠cF (2*m+1) x (Fin.snoc y true) :=
  ⟨e0,by rw[e,g,Fin.snoc_last,zq];simp⟩
 have hL:∃y1 y2:Fin (2*m)->Bool,
   cF (2*m+1) x (Fin.snoc y1 false)≠cF (2*m+1) x (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,Hz⟩:=ps (n:=2*m) W;X ⟨y1,y2,by rw[e,e];X Hz⟩
 have He:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m)->Bool,cF (2*m) D y=cF (2*m+1) x (Fin.snoc y false)) ->
   x.size<=D.size+1:=fun D Hc Hw=>by
  have h:=q9 (2*m) W D Hc (funext fun y=>(Hw y).trans (e y));simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left m (by O:0< 2)] at h;O
 obtain ⟨hB,_,_,_,_,_,_,_,_,_,_,_⟩:=zV f false Hd hL He;set hU:=p3 x (2*m) false
 have hC:cF (2*m) hU=pq (2*m) :=
  funext fun y=>(q6 x (2*m) false f.1 hL y).trans (e y)
 have hD:qf m hU:=HN hU hB hC
 obtain ⟨hV,_,_,_,⟨HJ,HA,z,j,hM,HS,hZ,H0,H1,
   Hl,Hf,hW,hX,hP⟩,hE,hN⟩ :=
  ke hm f g hD
 have hJ:∀k (hk:k< x.size),(x.gates[k]'hk).op=.and ->
   ∀a,pC (2*m+1) k a (x.gates[k]'hk) ->
    p0 x (e1 (2*m):Fin (2*m+1)->Bool) a=false:=fun k hk r a HB=>by
  cases hUa:p0 x (e1 (2*m):Fin (2*m+1)->Bool) a with
  | false=>rfl
  | true=>
   exfalso;have HK:k≠HJ:=fun h=>by subst h;rw[hM] at r;cases r
   have Hm:a≠2*m:=fun h=>HK ((z k hk).1 (h▸HB))
   have HL:2*m+1<=a:=by_contra fun HW=>by
    rw[p7 x _ a W] at hUa;simp[e1,Hm] at hUa
   set ka:=a-(2*m+1);have HT:ka< x.size:=by have:=HB.2;O
   have H8:a=2*m+1+ka :=W;obtain ⟨Hn,Hg,hh⟩:=hN ka HT (H8▸hUa);have H9:=q4 f.1 j hk HK;obtain ⟨Ho,hO,_,Hp,Hq,_,_⟩:=p4 f.1 hk H9;have Hh:=pp f hV H7 hk H9 hO Hp HB (H8▸Hg);obtain ⟨_,a1,a2,H2,_,_,_,HC,HD,_⟩:=qn hm hB hC hD hO (Hq.trans r);have HE:(hU.gates[Ho]'hO).op=.and:=Hq.trans r;have HM:Hn∈pa (hU.gates[Ho]'hO):=Hh.1;simp[pa,HE,H2] at HM;rcases HM with rfl|rfl<;>[X HC hh;X HD hh]
 have HF:z0 C:=qK p.1 hV fun t ht Hr=>by
  rcases (q t ht).1 Hr with rfl|rfl
  ·rw[hF];intro h;cases h
  ·rw[hI];intro h;cases h
 have v:zG C (2*m+1) C.output :=
  ⟨x.output,q8 p.1 hR,by rw[←pb,g];simp[e1]⟩
 have Ha:cF (2*m+2) C (e1 (2*m))=false:=by rw[hfun];X pW _ _
 have hY:zG C (2*m+1) u:=by_contra fun Hs=>by
  have h1:=qL p HF W Hj c hK Hy q
   i hI hT hS hA hE (e1 (2*m)) (by simp only[e1,decide_eq_true_eq];O) (ir Hs)
   C.output (pB Hj) v
  rw[←pb,Ha] at h1;cases h1
 have Hi:zG C (2*m+1) (2*m+2+H6):=by
  obtain ⟨wu,HU,HG⟩:=hY;X ⟨wu,hA.trans HU,HG⟩
 have H3:¬zG C (2*m+1) w:=fun HV=>by
  have Ht:=qI p.1 s hH (e1 (2*m):Fin (2*m+1)->Bool)
   w W H4 W
  rw[jy (2*m),jL (2*m)] at Ht;have Hb:p0 C (e1 (2*m):Fin (2*m+2)->Bool) w=true:=Ht.trans (jK p.1 W HV)
  have Hu:p0 C (e1 (2*m):Fin (2*m+2)->Bool) (2*m+2+d)=true:=by
   rcases hQ with hins|hins
   ·rw[p6 _ c hF hins W hG,Hb,Bool.or_true]
   ·rw[p6 _ c hF hins hG W,Hb,Bool.true_or]
  have h1:=qL p HF W Hj c hK Hy q
   i hI hT hS hA hE (e1 (2*m)) (by simp only[e1,decide_eq_true_eq];O) (il Hu)
   C.output (pB Hj) v
  rw[←pb,Ha] at h1;cases h1
 X ⟨⟨
  hm,p,hfun,HF,Hj,d,H6,w,u,c,hK,Hy,s,hF,hG,H4,
  hQ,i,q,hH,hI,hS,Hk,hT,hA,f,g,hV,H7,
  hL,hR,hB,hC,hD,HJ,HA,z,j,hM,HS,Hl,
  Hf,hZ,H0,H1,hW,hX,hP,hE,hN,hJ,
  v,hY,Hi,H3
 ⟩⟩
private lemma qR {m:ℕ} {C:J} (d:zB m C) :
  let hI:=p5 C (2*m+1) true;let hC:=p3 C (2*m+1) true;let hD:=p5 hC (2*m) false;let p:=p3 hC (2*m) false
  ∀i< 2*m+2+C.size,i≠2*m+1->i≠2*m+2+d.f3->¬zG C (2*m+1) i ->
   ∃i'' i''':ℕ,i''< 2*m+1+hC.size/\i'''< 2*m+p.size /\
    hI.fc.getD i (.const false)=.wire i'' /\
    hD.fc.getD i'' (.const false)=.wire i''' /\
    (2*m+2<=i->2*m<=i''') /\
    (∀x:Fin (2*m+2)->Bool,p0 C x i=p0 p (qq x) i'''):=by
 dsimp only;set hI:=p5 C (2*m+1) true;set hC:=p3 C (2*m+1) true;set hD:=p5 hC (2*m) false;set p:=p3 hC (2*m) false;intro i
 induction i using Nat.strong_induction_on with
 | ind i ih=>
  intro H7 hJ hK c;by_cases Hf:i< 2*m+2
  ·have hE:i< 2*m:=by_contra fun Hg=>
    c (show i=2*m by O▸zE (C:=C) (n:=2*m+1) W)
   Y ⟨i,i,by O,by O,
    pd C (2*m+1) true i W,
    pd hC (2*m) false i hE,by O,fun x=>?_⟩
   rw[p7 C x i W,p7 p (qq x) i hE];R
  ·set t:=i-(2*m+2);have ht:t< C.size :=W
   have hL:i=2*m+2+t :=W;rw[hL] at hK c ⊢;have H3:t≠d.f3 :=W;have H4:t≠d.f4:=fun h=>c (h▸d.fT);have j:=pE d.f0.1 d.fe ht H3 H4;obtain ⟨hV,hH,_,q,k,hF,_⟩:=p4 d.f0.1 ht j;have hU:hV< hC.size:=hH
   have l:hV≠d.fv:=fun H8=>
    c ((pM (H8▸q)).2 (jh d.fD d.fI d.fK d.fw))
   have r:=q4 d.f7.1 d.ff hH l;obtain ⟨hM,hN,_,hB,s,u,_⟩:=p4 d.f7.1 hH r;have e:hM< p.size:=hN;Y ⟨2*m+1+hV,2*m+hM,by O,by O,q,hB,by O,fun x=>?_⟩
   rcases pc d.f0 d.fn t ht with ⟨hW,_,_,_⟩|⟨v,a1,a2,w,hO,hP,_⟩
   ·X absurd hW (d.fJ _ (List.getElem_mem ht))
   ·have hG:∀a,(a=a1\/a=a2)->a< 2*m+2+t ->
      a≠2*m+1/\a≠2*m+2+d.f3/\¬zG C (2*m+1) a:=fun a hX hY=>by
     have f:pC (2*m+2) t a (C.gates[t]'ht) :=
      ⟨by rcases v with h|h<;>rcases hX with rfl|rfl<;>simp[pa,h,w],hY⟩
     X ⟨fun h=>H3 ((d.fi t ht).1 (h▸f)),
         fun h=>H4 ((d.fj t ht).1 (h▸f)),
         j3 d.f0 d.fJ d.fn d.fp ht j c f⟩
    obtain ⟨H9,Ha,Hb⟩:=hG a1 (il rfl) hO;obtain ⟨Hc,Hd,He⟩:=hG a2 (ir rfl) hP;obtain ⟨b1,c1,_,_,hQ,hR,_,H5⟩:=ih a1 W W H9 Ha Hb;obtain ⟨b2,c2,_,_,hS,hT,_,H6⟩:=ih a2 W W Hc Hd He;rcases v with hop_eq|hop_eq
    ·obtain ⟨w1,w2,hZ,H0,y,z,g⟩:=hF .and a1 a2 (il rfl) hop_eq w hO hP
     obtain ⟨u1,u2,H1,H2,hh,hA,b⟩:=u .and w1 w2 (il rfl) (k.trans hop_eq) g hZ H0;rw[hQ] at y;cases y;rw[hS] at z;cases z;rw[hR] at hh;cases hh;rw[hT] at hA;cases hA
     rw[pm x ht hop_eq w hO hP,
      pm (qq x) e (s.trans (k.trans hop_eq)) b H1 H2,H5 x,H6 x]
    ·obtain ⟨w1,w2,hZ,H0,y,z,g⟩:=hF .or a1 a2 (ir rfl) hop_eq w hO hP
     obtain ⟨u1,u2,H1,H2,hh,hA,b⟩:=u .or w1 w2 (ir rfl) (k.trans hop_eq) g hZ H0;rw[hQ] at y;cases y;rw[hS] at z;cases z;rw[hR] at hh;cases hh;rw[hT] at hA;cases hA
     rw[p6 x ht hop_eq w hO hP,
      p6 (qq x) e (s.trans (k.trans hop_eq)) b H1 H2,H5 x,H6 x]
private lemma zQ {m:ℕ} {C:J} (d:zB m C)
  {b a'' a''':ℕ} (a:b< (p3 C (2*m+1) true).size)
  (c:p0 (p3 C (2*m+1) true) (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+b)=true)
  (e:pC (2*m+1) b a'' ((p3 C (2*m+1) true).gates[b]'a))
  (f:(p5 (p3 C (2*m+1) true) (2*m) false).fc.getD a'' (.const false)=.wire a''') :
  ∀y:Fin (2*m)->Bool,
   p0 (p3 (p3 C (2*m+1) true) (2*m) false) y a'''=true ->
   pq (2*m) y=true:=fun y hy=>by
 set i:=p3 C (2*m+1) true;set j:=p3 i (2*m) false;obtain ⟨q,k,S,_,_,t⟩:=d.fS b a c
 Y pT (S:=S) (by
  rw[←cf t y]
  have l:p0 j y a'''=p0 i (Fin.snoc y false) a'':=by
   have h:=pH i (2*m) false d.f7.1 y a'';rw[f] at h;X h
  have r:p0 j y q=p0 i (Fin.snoc y false) (2*m+1+b):=by
   have h:=pH i (2*m) false d.f7.1 y (2*m+1+b);rw[k] at h;X h
  have g:=d.fk b a c;rcases pc d.f7 d.fq b a with ⟨n,_,_,_⟩|⟨_,b1,b2,p,u,v,_⟩
  ·rw[g] at n;cases n
  ·have s:=e.1;simp only[pa,g,p,List.mem_cons,List.not_mem_nil,or_false] at s
   rw[r,p6 _ a g p u v,Bool.or_eq_true];rcases s with rfl|rfl<;>[X il (l.symm.trans hy);X ir (l.symm.trans hy)])
private lemma kp {m:ℕ} {C:J} (d:zB m C):d.w=2*m-1:=by
 set hR:=p3 C (2*m+1) true;set p:=p3 hR (2*m) false;have hB:d.w< 2*m+2+C.size:=by have:=d.fs;have:=d.f9;O
 have hC:d.w≠2*m+2+d.f3:=by have:=d.fs;O
 obtain ⟨H3,q,_,r,hH,hD,k,y⟩ :=
  qR d d.w hB d.fM hC d.fE
 have b:qq (e2 (2*m-1) (2*m):Fin (2*m+2)->Bool) =
   (e1 (2*m-1):Fin (2*m)->Bool):=by
  funext j;simp only[qq,e2,e1];apply Bool.eq_iff_iff.2;have:=j.isLt;simp;O
 have c:p0 p (e1 (2*m-1):Fin (2*m)->Bool) q=true:=by
  cases u:p0 p (e1 (2*m-1):Fin (2*m)->Bool) q with
  | true=>rfl
  | false=>
   exfalso
   have hM:p0 C (e2 (2*m-1) (2*m):Fin (2*m+2)->Bool) (2*m+2+d.f3)=false:=by
    have z:p0 C (e2 (2*m-1) (2*m):Fin (2*m+2)->Bool) (2*m+1)=false:=by
     rw[p7 C _ (2*m+1) W];simp[e2];O
    have hI:p0 C (e2 (2*m-1) (2*m):Fin (2*m+2)->Bool) d.w=false:=by
     rw[y,b];X u
    rcases d.ft with hins|hins
    ·rw[p6 _ d.f9 d.fl hins W d.fs,z,hI];R
    ·rw[p6 _ d.f9 d.fl hins d.fs W,hI,z];R
   have v:∀t (ht:t< C.size),zG C (2*m+1) (2*m+2+t)->t≠d.f3->t≠d.f4 ->
     ∀a,pC (2*m+2) t a (C.gates[t]'ht)->¬zG C (2*m+1) a ->
      p0 C (e2 (2*m-1) (2*m):Fin (2*m+2)->Bool) a=false:=by
    intro t ht hY hS hT a e hE
    obtain ⟨H4,hN,_,_,hJ,hF,_,hZ⟩ :=
     qR d a (by have:=e.2;O) (fun h=>hS ((d.fi t ht).1 (h▸e)))
      (fun h=>hT ((d.fj t ht).1 (h▸e))) hE
    rw[hZ,b];have l:=pE d.f0.1 d.fe ht hS hT;obtain ⟨H0,hh,_,g,_,_,_⟩:=p4 d.f0.1 ht l;have s:=pp d.f0 d.fJ d.fn ht l hh g e hJ
    cases hv:p0 p (e1 (2*m-1):Fin (2*m)->Bool) hN with
    | false=>rfl
    | true=>
     have hp:=zQ d hh ((pM g).1 hY) s hF _ hv;rw[pW] at hp;cases hp
   have f:=j8 d.f0 d.fJ (by have:=d.hm;O) d.fn d.f9 d.fa d.fP
    d.fe d.fh d.fm d.fy d.fu d.fk hM v C.output (pB d.fn) d.fo
   have hG:(e2 (2*m-1) (2*m):Fin (2*m+2)->Bool)=pe (2*m-1):=by
    funext j;simp only[pe,e2];have:=d.hm;congr 1;simp;O
   change cF (2*m+2) C (e2 (2*m-1) (2*m))=cF (2*m+2) C (e1 (2*m)) at f;rw[hG,d.fd,pW,q0 (by have:=d.hm;O)] at f;cases f
 have i:∀a< 2*m-1,p0 p (e1 a:Fin (2*m)->Bool) q=false:=fun a ha=>by
  cases hv:p0 p (e1 a:Fin (2*m)->Bool) q with
  | false=>rfl
  | true=>
   exfalso
   have hK:qq (e2 a (2*m):Fin (2*m+2)->Bool)=(e1 a:Fin (2*m)->Bool):=by
    funext j;simp only[qq,e2,e1];apply Bool.eq_iff_iff.2;have:=j.isLt;simp;O
   have hM:p0 C (e2 a (2*m):Fin (2*m+2)->Bool) (2*m+2+d.f3)=true:=by
    have hI:p0 C (e2 a (2*m):Fin (2*m+2)->Bool) d.w=true:=by rw[y,hK];X hv
    rcases d.ft with hins|hins
    ·rw[p6 _ d.f9 d.fl hins W d.fs,hI,Bool.or_true]
    ·rw[p6 _ d.f9 d.fl hins d.fs W,hI,Bool.true_or]
   have hA:=qL d.f0 d.fJ W d.fn d.f9 d.fa d.fP
    d.fe d.fh d.fm d.fy d.fu d.fz d.fk (e2 a (2*m))
    (by simp only[e2,decide_eq_true_eq];O) (il hM)
    C.output (pB d.fn) d.fo
   rw[←pb,d.fd,jC W W] at hA;cases hA
 rcases qE d.f6 q r with
  ⟨j,hj,hL,u⟩|⟨_,_,_,_,_,_,u⟩|⟨_,_,_,c',hO,hP,u⟩|⟨_,_,_,i',H5,H1,H6,hQ,H7,u⟩
 ·have hU:j=2*m-1:=of_decide_eq_true (by have h:=cf u (e1 (2*m-1));rw[c] at h;X h.symm)
  have hV:d.w< 2*m+2:=by_contra fun H2=>by have:=k W;O
  have x:d.w< 2*m:=by_contra fun H2=>
   d.fE (show d.w=2*m by have:=d.fM;O▸zE (C:=C) (n:=2*m+1) W)
  have hW:=pd C (2*m+1) true d.w W;have hX:=pd hR (2*m) false d.w x;rw[hH] at hW;cases hW;rw[hD] at hX;cases hX;O
 ·have h1:=cf u (e1 (2*m-1));rw[c,pz] at h1;cases h1
 ·have h1:=cf u (e1 (c'-1))
  rw[i (c'-1) W,(pu hO hP W).2 (il W)] at h1;cases h1
 ·have h1:=cf u (e1 (2*m-1))
  rw[c,eq_comm,pN hQ (by have:=d.hm;O)] at h1;O
private lemma z2 {m:ℕ} {C:J} (d:zB m C)
  {t:ℕ} (ht:t< C.size) (hD:t< d.f4) (hF:t≠d.f3)
  (hG:zG C (2*m+1) (2*m+2+t)) :
  let u:=p5 C (2*m+1) true;let g:=p3 C (2*m+1) true;let r:=p5 g (2*m) false;let f:=p3 g (2*m) false
  ∃b a:ℕ,b< g.size/\a< f.size /\
   u.fc.getD (2*m+2+t) (.const false)=.wire (2*m+1+b) /\
   r.fc.getD (2*m+1+b) (.const false)=.wire (2*m+a) /\
   q1 m (p8 f a) /\
   ∀x:Fin (2*m+2)->Bool,
    p8 C t x=(x ⟨2*m,by O⟩||p8 f a (qq x)):=by
 dsimp only;set u:=p5 C (2*m+1) true;set g:=p3 C (2*m+1) true;set r:=p5 g (2*m) false;set f:=p3 g (2*m) false;have q:=pE d.f0.1 d.fe ht hF W;obtain ⟨b,i,_,e,_,_,_⟩:=p4 d.f0.1 ht q
 have k:p0 g (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+b)=true :=
  (pM e).1 hG
 obtain ⟨l,n,v⟩:=d.fS b i k;have w:b< g.size:=i;have z:l< 2*m+f.size:=zW d.f7.1 W n
 have hh:2*m<=l:=by_contra fun hI=>by
  obtain ⟨S,_,_,hH⟩:=v;X zv W (hH.symm.trans (funext fun y=>p7 f y l W))
 set a:=l-2*m;have s:a< f.size :=W;have c:l=2*m+a :=W
 Y ⟨b,a,i,s,e,c▸n,
  by change q1 m (fun y=>p0 f y (2*m+a));rw[←c];X v,fun x=>?_⟩
 have hB:p0 C x (2*m+2+t)=p0 C (Fin.snoc (Fin.init x) true) (2*m+2+t):=by
  have hE:x=Fin.snoc (Fin.init x) (x (Fin.last (2*m+1))):=(Fin.snoc_init_self x).symm
  cases hb:x (Fin.last (2*m+1)) with
  | true=>conv_lhs=>rw[hE,hb]
  | false=>
   conv_lhs=>rw[hE,hb]
   X qI d.f0.1 d.fi d.fj (Fin.init x)
    (2*m+2+t) W W W
 have hC:p0 C (Fin.snoc (Fin.init x) true) (2*m+2+t)=p0 g (Fin.init x) (2*m+1+b):=by
  have h:=pH C (2*m+1) true d.f0.1 (Fin.init x) (2*m+2+t);rw[e] at h;X h.symm
 change p0 C x (2*m+2+t)=_;rw[hB,hC]
 cases hx2m:x ⟨2*m,by O⟩ with
 | true=>
  simp only[Bool.true_or]
  X zz g d.f7.1 d.fC (fun j hj=>by
   simp only[e1,decide_eq_true_eq] at hj
   have:j=Fin.last (2*m):=Fin.ext (by simp[hj])
   rw[this];X hx2m) (2*m+1+b) k
 | false=>
  simp only[Bool.false_or]
  have p:Fin.init x=Fin.snoc (qq x) false:=by
   funext j;by_cases hj:j.val< 2*m
   ·have:j=Fin.castSucc ⟨j.val,hj⟩:=Fin.ext rfl;rw[this,Fin.snoc_castSucc];R
   ·have:j=Fin.last (2*m):=Fin.ext (by have:=j.isLt;simp;O)
    rw[this,Fin.snoc_last];X hx2m
  have hA:=pH g (2*m) false d.f7.1 (qq x) (2*m+1+b);rw[n,c] at hA;rw[p,←hA];R
private lemma jN {m:ℕ} {C:J} (d:zB m C) (hw:d.w=2*m-1)
  {tu:ℕ} (HH:tu< d.f4) (hu:d.u=2*m+2+tu) :
  let HD:=p5 C (2*m+1) true;let Hp:=p3 (p3 C (2*m+1) true) (2*m) false
  HD.fc.getD (2*m+2+tu) (.const false)=.wire (2*m+1+d.fv) /\
  ∃Su:Finset ℕ,Su.Nonempty/\(∀e∈Su,e+1< 2*m)/\(2*m-2)∈Su /\
   p8 Hp d.fg=ph m Su:=by
 dsimp only;set HD:=p5 C (2*m+1) true;set _R:=p3 C (2*m+1) true;set _T:=p5 _R (2*m) false;set Hp:=p3 _R (2*m) false;have hN:tu< C.size:=by have:=d.fa;O
 have _4:tu≠d.f3:=by have:=d.fU;O
 have _j:cF (2*m+2) C (e1 (2*m))=false:=by rw[d.fd];X pW _ _
 have _s:∀a,pC (2*m+2) d.f3 a (C.gates[d.f3]'d.f9)->¬zG C (2*m+1) a:=fun a hr=>by
  have hrm:=hr.1
  rcases d.ft with g|g <;>
   (simp only[pa,d.fl,g,List.mem_cons,List.not_mem_nil,or_false] at hrm;
    rcases hrm with rfl|rfl;
    first|X pI (p9 C (2*m+1) true d.f0.1)|X d.fE;
    first|X pI (p9 C (2*m+1) true d.f0.1)|X d.fE)
 obtain ⟨_,_,_5⟩:=qW d.f0 d.fJ W d.fn _j
  d.f9 d.fa d.fP d.fi d.fj d.fe d.fh _s d.fm d.fy d.fu d.fp
 have hR:∀t (ht:t< C.size),pC (2*m+2) t (2*m+2+tu) (C.gates[t]'ht)↔t=d.f4 :=
  fun t ht=>hu▸_5 tu HH hu d.fH t ht
 obtain ⟨Hq,Hb,hS,HI,z,hT,⟨Su,_U,hSu,H3⟩,r⟩ :=
  z2 d hN HH _4 (hu▸d.fH)
 have hU:C.output≠2*m+2+tu:=fun _t=>by
  have h1:=r (e1 (2*m));change p0 C (e1 (2*m)) (2*m+2+tu)=_ at h1;rw[←_t,←pb,_j] at h1;simp[e1] at h1
 have hD:∀e,e+3<=2*m ->
   p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+d.f3)=false:=fun e he=>by
  have h1:p0 C (pe e:Fin (2*m+2)->Bool) (2*m+1)=false:=by
   rw[p7 C _ (2*m+1) W];simp only[pe,e2,decide_eq_false_iff_not];O
  have h2:p0 C (pe e:Fin (2*m+2)->Bool) (2*m-1)=false:=by
   rw[p7 C _ (2*m-1) W];simp only[pe,e2,decide_eq_false_iff_not];O
  rcases d.ft with g|g
  ·rw[p6 _ d.f9 d.fl (hw▸g) W W,h1,h2];R
  ·rw[p6 _ d.f9 d.fl (hw▸g) W W,h2,h1];R
 have v:∀(e:ℕ) (he:e+3<=2*m) (v0:Bool),
   pl C (pe e:Fin (2*m+2)->Bool) tu v0 C.output=true:=fun e he v0=>by
  have h0l:∀w< 2*m+2+C.size,w≠2*m+2+tu ->
    pl C (pe e:Fin (2*m+2)->Bool) tu v0 w=p0 C (pe e:Fin (2*m+2)->Bool) w:=by
   intro w;induction w using Nat.strong_induction_on with
   | ind w ih=>
    intro hw hne;by_cases hlt:w< 2*m+2+tu
    ·X pA C _ tu hN v0 w hlt
    ·set t:=w-(2*m+2);have ht:t< C.size :=W
     have HJ:w=2*m+2+t :=W;have _k:t≠tu :=W;rw[HJ];by_cases _V:t=d.f4
     ·rw[_V]
      have _W:p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+d.f3)=false:=hD e he
      have hgM:pl C (pe e:Fin (2*m+2)->Bool) tu v0 (2*m+2+d.f3)=false :=
       (ih (2*m+2+d.f3) (by have:=d.fP;O) (by have:=d.f9;O) W).trans _W
      have hgh:=d.fP;rcases d.fy with g|g
      ·rw[pF _ hN v0 d.fa W d.fm g W d.fu,
        pm _ d.fa d.fm g W d.fu,hgM,_W];R
      ·rw[pF _ hN v0 d.fa W d.fm g d.fu W,
        pm _ d.fa d.fm g d.fu W,hgM,_W,Bool.and_false,Bool.and_false]
     ·rcases pc d.f0 d.fn t ht with ⟨hV,_,_,_⟩|⟨hK,a1,a2,g,Hr,Hs,_⟩
      ·X absurd hV (d.fJ _ (List.getElem_mem ht))
      ·have hW:∀a,(a=a1\/a=a2)->a< 2*m+2+t->a≠2*m+2+tu:=fun a hm' _u h=>
        _V ((hR t ht).1 ⟨by rcases hK with _X|_X<;>rcases hm' with rfl|rfl<;>simp[pa,_X,g,h],h▸_u⟩)
       rcases hK with hop_eq|hop_eq
       ·rw[pF _ hN v0 ht _k hop_eq g Hr Hs,pm _ ht hop_eq g Hr Hs,
         ih a1 W W (hW a1 (il rfl) Hr),ih a2 W W (hW a2 (ir rfl) Hs)]
       ·rw[pJ _ hN v0 ht _k hop_eq g Hr Hs,p6 _ ht hop_eq g Hr Hs,
         ih a1 W W (hW a1 (il rfl) Hr),ih a2 W W (hW a2 (ir rfl) Hs)]
  rw[h0l C.output (pB d.fn) hU,←pb,d.fd,q0 W]
 have hA:∀e,e+1< 2*m ->
   qq (pe e:Fin (2*m+2)->Bool)=(pe e:Fin (2*m)->Bool):=fun e he=>by
  funext j;simp only[qq,pe,e2]
 have HA:2*m-2∈Su:=by_contra fun h0m=>
  qN d.f0 d.fJ d.fd hN (by O:2*m< 2*m+2+tu)
   (fun x hx=>by
    rw[p7 C x (2*m) W] at hx
    change p8 C tu x=true;rw[r x,hx];rfl) fun e he=>by
   by_cases _Y:e=2*m\/e=2*m-1
   ·have HK:p0 C (pe e:Fin (2*m+2)->Bool) (2*m)=p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+tu):=by
     have hQ:(pe e:Fin (2*m+2)->Bool) ⟨2*m,by O⟩=true:=by
      simp only[pe,e2,decide_eq_true_eq];rcases _Y with rfl|rfl<;>O
     rw[p7 C _ (2*m) W,hQ];change _=p8 C tu _;rw[r,hQ];R
    rw[pV C _ tu hN _ HK,←pb,d.fd,q0 he]
   ·by_cases HL:e=2*m-2
    ·have HK:p0 C (pe e:Fin (2*m+2)->Bool) (2*m)=p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+tu):=by
      have hQ:(pe e:Fin (2*m+2)->Bool) ⟨2*m,by O⟩=false:=by
       simp only[pe,e2,decide_eq_false_iff_not];O
      rw[p7 C _ (2*m) W,hQ];change false=p8 C tu _;rw[r,hQ,Bool.false_or,hA e (by have:=d.hm;O),H3]
      cases _6:ph m Su (pe e) with
      | false=>rfl
      | true=>X absurd (HL▸(pg hSu (by have:=d.hm;O)).1 _6) h0m
     rw[pV C _ tu hN _ HK,←pb,d.fd,q0 he]
    ·X v e (by have:=d.hm;O) _
 have Ht:Hq=d.fv:=by_contra fun HM=>by
  have H2:=pE d.f0.1 d.fe hN _4 W;obtain ⟨_Z,h0n,_,HB,_v,_w,_⟩:=p4 d.f0.1 hN H2;rw[z] at HB;injection HB with hku_eq_2;have _7:_Z=Hq :=W;rcases _7.symm with rfl
  have _x:p0 _R (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+Hq)=true :=
   (pM z).1 (hu▸d.fH)
  have H4:(_R.gates[Hq]'hS).op=(C.gates[tu]'hN).op:=_v;have hB:(C.gates[tu]'hN).op=.or:=H4.symm.trans (d.fk Hq hS _x);have Hu:=q4 d.f7.1 d.ff hS HM;obtain ⟨_y,h0f,_,Hc,_8,_9,_⟩:=p4 d.f7.1 hS Hu;rw[hT] at Hc;injection Hc with hku3_eq;have HN:_y=Hb :=W;rcases HN.symm with rfl;have _a:(Hp.gates[Hb]'HI).op=(_R.gates[Hq]'hS).op:=_8;rcases pc d.f0 d.fn tu hN with ⟨hV,_,_,_⟩|⟨_,b1,b2,Hd,hb1,hb2,_⟩
  ·rw[hB] at hV;cases hV
  ·obtain ⟨h00,h01,h02,h03,_z,_A,_B⟩:=_w .or b1 b2 (ir rfl) hB Hd hb1 hb2
   obtain ⟨h04,h05,_C,_D,_b,_c,_d⟩:=_9 .or h00 h01 (ir rfl) (H4.trans hB) _B h02 h03
   have hX:p0 Hp (pe (2*m-2):Fin (2*m)->Bool) (2*m+Hb)=true:=by
    change p8 Hp Hb _=true;rw[H3];X (pg hSu (by have:=d.hm;O)).2 HA
   rw[p6 _ HI (_a.trans (H4.trans hB)) _d _C _D,Bool.or_eq_true] at hX
   obtain ⟨b,H5,He,_E,HO,Hv,H6,hO⟩ :
     ∃b,(b=b1\/b=b2)/\b< 2*m+2+tu /\
      ∃_E HO,
       HD.fc.getD b (.const false)=.wire _E /\
       _T.fc.getD _E (.const false)=.wire HO /\
       p0 Hp (pe (2*m-2):Fin (2*m)->Bool) HO=true:=by
    rcases hX with h1|h2
    ·X ⟨b1,il rfl,hb1,h00,h04,_z,_b,h1⟩
    ·X ⟨b2,ir rfl,hb2,h01,h05,_A,_c,h2⟩
   have _F:b≠2*m+1:=fun h=>_4 ((d.fi tu hN).1 ⟨by rcases H5 with rfl|rfl<;>simp[pa,hB,Hd,h],h▸He⟩)
   have _G:b≠2*m+2+d.f3:=fun h=>by
    have:=(d.fj tu hN).1 ⟨by rcases H5 with rfl|rfl<;>simp[pa,hB,Hd,h],h▸He⟩;O
   have h0g:b≠2*m:=fun h=>HM ((d.fB Hq hS).1
    (pp d.f0 d.fJ d.fn hN H2 hS z
     ⟨by rcases H5 with rfl|rfl<;>simp[pa,hB,Hd,h],h▸He⟩
     (pd C (2*m+1) true (2*m) W)))
   have hI:∀x:Fin (2*m+2)->Bool,p0 C x b=true->p0 C x (2*m+2+tu)=true:=fun x hx=>by
    rw[p6 x hN hB Hd hb1 hb2,Bool.or_eq_true];rcases H5 with rfl|rfl<;>[X il hx;X ir hx]
   by_cases hUb:zG C (2*m+1) b
   ·
    have h0v:2*m+2<=b:=by_contra fun hlt=>by
     have:b< 2*m :=W
     have h1:=pd C (2*m+1) true b W;obtain ⟨wb',h06,_6⟩:=hUb;rw[h1] at h06;cases h06;rw[p7 _R _ b W] at _6;simp[e1] at _6;O
    set tb:=b-(2*m+2);have htb:tb< C.size :=W;have HC:b=2*m+2+tb :=W
    obtain ⟨h0w,h07,_,_,_H,_e,_,Hf⟩ :=
     z2 d htb W W (HC▸hUb)
    rw[HC,_H] at Hv;injection Hv with hwb_eq;subst hwb_eq;rw[_e] at H6;injection H6 with hvb_eq;subst hvb_eq;Y qN d.f0 d.fJ d.fd hN He hI fun e he=>?_;by_cases _Y:e=2*m\/e=2*m-1
    ·have hQ:(pe e:Fin (2*m+2)->Bool) ⟨2*m,by O⟩=true:=by
      simp only[pe,e2,decide_eq_true_eq];rcases _Y with rfl|rfl<;>O
     have HK:p0 C (pe e:Fin (2*m+2)->Bool) b=p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+tu):=by
      rw[HC];change p8 C tb _=p8 C tu _;rw[Hf,r,hQ];R
     rw[pV C _ tu hN _ HK,←pb,d.fd,q0 he]
    ·by_cases HL:e=2*m-2
     ·have HK:p0 C (pe e:Fin (2*m+2)->Bool) b=p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+tu):=by
       have hbt:p0 C (pe e:Fin (2*m+2)->Bool) b=true:=by
        rw[HC];change p8 C tb _=true;rw[Hf,hA e (by have:=d.hm;O),HL,show p8 Hp h07 (pe (2*m-2))=true from hO,Bool.or_true]
       rw[hbt,hI _ hbt]
      rw[pV C _ tu hN _ HK,←pb,d.fd,q0 he]
     ·X v e (by have:=d.hm;O) _
   ·
    obtain ⟨b'',h0x,_,_,_l,HP,_,Hw⟩ :=
     qR d b W _F _G hUb
    rw[Hv] at _l;cases _l;rw[H6] at HP;cases HP;set D:=pU C tu ⟨.or,[2*m,b]⟩;have HQ:D.size=C.size:=pS C tu _;have hJ:FanInTwo D:=z1 d.f0.1 tu ⟨by simp,by simp⟩
    have _I:z0 D:=zA d.fJ tu (by intro h;cases h)
    have hL:∀x:Fin (2*m+2)->Bool,p0 D x (2*m+2+tu)=(x ⟨2*m,by O⟩||p0 C x b):=fun x=>by
     rw[qg C x hN]
     simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
      show 2*m< 2*m+2+tu by O,He,↓reduceIte,p7 C x (2*m) W]
    have _f:∀x:Fin (2*m+2)->Bool,∀w< 2*m+2+C.size,
      p0 D x w=true->p0 C x w=true:=fun x w=>by
     induction w using Nat.strong_induction_on with
     | ind w ih=>
      intro hw _g;by_cases hlt:w< 2*m+2+tu
      ·rwa[qc C x tu _ w hlt] at _g
      ·by_cases HK:w=2*m+2+tu
       ·subst HK;rw[hL x,Bool.or_eq_true] at _g
        rcases _g with hQ|hxb
        ·change p8 C tu x=true;rw[r x,hQ];R
        ·X hI x hxb
       ·set t:=w-(2*m+2);have ht:t< C.size :=W
        have htD:t< D.size:=by rw[HQ];X ht
        have HJ:w=2*m+2+t :=W;rw[HJ] at _g ⊢;have HE:D.gates[t]'htD=C.gates[t]'ht:=List.getElem_set_ne (by O:tu≠t) _
        rcases pc d.f0 d.fn t ht with ⟨hV,_,_,_⟩|⟨hK,a1,a2,g,Hr,Hs,_⟩
        ·X absurd hV (d.fJ _ (List.getElem_mem ht))
        ·rcases hK with hop_eq|hop_eq
         ·rw[pm x htD (HE.symm▸hop_eq) (HE.symm▸g) Hr Hs,Bool.and_eq_true] at _g
          rw[pm x ht hop_eq g Hr Hs,Bool.and_eq_true];X ⟨ih a1 W W _g.1,ih a2 W W _g.2⟩
         ·rw[p6 x htD (HE.symm▸hop_eq) (HE.symm▸g) Hr Hs,Bool.or_eq_true] at _g
          rw[p6 x ht hop_eq g Hr Hs,Bool.or_eq_true];rcases _g with h1|h2<;>[X il (ih a1 W W h1);X ir (ih a2 W W h2)]
    have HR:∀e,e+1< 2*m+2->cF (2*m+2) D (pe e)=true:=fun e he=>by
     by_cases _Y:e=2*m\/e=2*m-1
     ·have hQ:(pe e:Fin (2*m+2)->Bool) ⟨2*m,by O⟩=true:=by
       simp only[pe,e2,decide_eq_true_eq];rcases _Y with rfl|rfl<;>O
      have HS:p0 D (pe e:Fin (2*m+2)->Bool) (2*m+2+tu)=p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+tu):=by
       rw[hL,hQ];change true=p8 C tu _;rw[r,hQ];R
      change p0 D (pe e:Fin (2*m+2)->Bool) C.output=true
      rw[qv C hN _ _ HS C.output (pB d.fn),
       ← pb,d.fd,q0 he]
     ·by_cases HL:e=2*m-2
      ·have hbt:p0 C (pe e:Fin (2*m+2)->Bool) b=true:=by
        rw[Hw,hA e (by have:=d.hm;O),HL];X hO
       have HS:p0 D (pe e:Fin (2*m+2)->Bool) (2*m+2+tu)=p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+tu):=by
        rw[hL,hbt,Bool.or_true,hI _ hbt]
       change p0 D (pe e:Fin (2*m+2)->Bool) C.output=true
       rw[qv C hN _ _ HS C.output (pB d.fn),
        ← pb,d.fd,q0 he]
      ·have HT:∀w< 2*m+2+C.size,w≠2*m+2+tu ->
         p0 D (pe e:Fin (2*m+2)->Bool) w=p0 C (pe e:Fin (2*m+2)->Bool) w :=
        qP C hN ⟨.or,[2*m,b]⟩ (pe e) fun t ht _=>by
         rcases pc d.f0 d.fn t ht with ⟨hV,_,_,_⟩|⟨hK,a1,a2,g,Hr,Hs,_⟩
         ·X absurd hV (d.fJ _ (List.getElem_mem ht))
         ·by_cases _V:t=d.f4
          ·subst _V
           have _W:=hD e (by have:=d.hm;O)
           rw[pj C _ d.f4 ht,d.fm,g];simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,Hr,Hs,↓reduceIte]
           rcases d.fy with h|h<;>rw[g] at h <;>
            (injection h with h1' hrest';injection hrest' with h2';rw[h1',h2'];
             simp only[show 2*m+2+d.f3≠2*m+2+tu by O,↓reduceIte,_W,Bool.false_and,Bool.and_false])
          ·have hW:∀a,(a=a1\/a=a2)->a< 2*m+2+t->a≠2*m+2+tu:=fun a hm' _u h=>
            _V ((hR t ht).1 ⟨by rcases hK with _X|_X<;>rcases hm' with rfl|rfl<;>simp[pa,_X,g,h],h▸_u⟩)
           rw[pj C _ t ht,g];simp only[List.map_cons,List.map_nil,Hr,Hs,hW a1 (il rfl) Hr,hW a2 (ir rfl) Hs,↓reduceIte]
       change p0 D (pe e:Fin (2*m+2)->Bool) C.output=true
       rw[HT C.output (pB d.fn) hU,
        ← pb,d.fd,q0 he]
    have Hg:cF (2*m+2) D=pq (2*m+2):=funext fun x=>by
     apply Bool.eq_iff_iff.2;constructor
     ·intro hDx;rw[←d.fd];X _f x C.output (pB d.fn) hDx
     ·intro hpx;rw[px] at hpx;obtain ⟨p,q,hpq,hxp,hxq⟩:=hpx
      X zz D hJ _I (fun j hj=>by
       simp only[pe,e2,decide_eq_true_eq] at hj;rcases hj with h|h
       ·have:j=p:=Fin.ext h;rw[this];X hxp
       ·have:j=q:=Fin.ext W;rw[this];X hxq) C.output (HR p.val W)
    have _m:IsMinimalCircuit (2*m+2) D:=qC d.f0 _ ⟨by simp,by simp⟩ (Hg.trans d.fd.symm)
    have h08:∃x1 x2:Fin (2*m+2)->Bool,cF (2*m+2) D x1≠cF (2*m+2) D x2:=by
     rw[Hg];X ps W
    have _n:∃y1 y2:Fin (2*m+1)->Bool,cF (2*m+2) D (Fin.snoc y1 true)≠cF (2*m+2) D (Fin.snoc y2 true):=by
     obtain ⟨y1,y2,hne⟩:=d.fN;X ⟨y1,y2,by rw[Hg,←d.fd];X hne⟩
    set s:=p5 D (2*m+1) true;set H7:=p3 D (2*m+1) true;have f:=pk D (2*m+1) true hJ;have h0y:C.size=3*m+1:=by have:=zr (m:=m+1) W d.f0 d.fd;O
    have hh:d.f3< D.size:=by rw[HQ];X d.f9
    have hC:d.f4< D.size:=by rw[HQ];X d.fa
    have Hh:tu< D.size:=by rw[HQ];X hN
    have H8:D.gates[d.f3]'hh=C.gates[d.f3]'d.f9:=List.getElem_set_ne (by O:tu≠d.f3) _
    have _J:D.gates[d.f4]'hC=C.gates[d.f4]'d.fa:=List.getElem_set_ne (by O:tu≠d.f4) _
    have HF:s.fc.getD (2*m+2+d.f3) (.const false)=.const true:=by
     have hev:=(pR (n:=2*m+1) (b:=true) hJ hh).2.2 (H8.symm▸d.fl);have _o:=p9 D (2*m+1) true hJ;rcases d.ft with g|g
     ·X ((hev (2*m+1) d.w (H8.symm▸g) W d.fs).1 (il _o)).1
     ·X ((hev d.w (2*m+1) (H8.symm▸g) d.fs W).1 (ir _o)).1
    have Hi:s.fb[d.f3]'(by rw[f.kept_len];X hh)=false:=by
     have h1:=pw (n:=2*m+1) (b:=true) hJ hh
      (H8.symm▸(d.fi d.f3 d.f9).2 rfl) (p9 D (2*m+1) true hJ)
     rwa[List.getD_eq_getElem _ _ (by rw[f.kept_len];X hh)] at h1
    have Hj:s.fb[d.f4]'(by rw[f.kept_len];X hC)=false:=by
     have h1:=pw (n:=2*m+1) (b:=true) hJ hC
      (_J.symm▸(d.fj d.f4 d.fa).2 rfl) HF
     rwa[List.getD_eq_getElem _ _ (by rw[f.kept_len];X hC)] at h1
    have h0h:3*m-1<=H7.size:=by
     have HU:∀y:Fin (2*m+1)->Bool,
       cF (2*m+1) H7 y=(y (Fin.last (2*m))||pq (2*m) (Fin.init y)):=fun y=>by
      rw[q6 D (2*m+1) true hJ _n y,Hg,qT (2*m+1) W y];R
     have hlb:=zl (pq (2*m)) (ps W) (fun _ _ _ _ h=>h) (3*m-2)
      (fun E h0o hEf=>by
       have h:=q9 (2*m) W E h0o hEf;simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left m (by O:0< 2)] at h;X h)
      H7 (qi D (2*m+1) true hJ) HU
     have:=d.hm;O
    have _K:H7.size<=3*m-1:=by
     have h0z:=za (i:=d.f3) (j:=d.f4)
      (by rw[f.kept_len];X hh) (by rw[f.kept_len];X hC) (by have:=d.fP;O) Hi Hj
     have h0p:=qk s.fb;have _t:H7.size=s.fb.count true:=f.gates_len;have h09:s.fb.length=D.size:=f.kept_len
     have:=d.hm;O
    obtain ⟨tq,_S,hM,Hk⟩:=zD d.f0.1 d.fv d.fD
    have HV:tq≠d.f3:=fun h=>by
     have h1:=(d.fe d.f3 d.f9).2 (il rfl);have h2:HD.fb[d.f3]'(by rw[(pk C (2*m+1) true d.f0.1).kept_len];X d.f9)=true:=h▸hM
     rw[h1] at h2;cases h2
    have HW:tq≠d.f4:=fun h=>by
     have h1:=(d.fe d.f4 d.fa).2 (ir rfl);have h2:HD.fb[d.f4]'(by rw[(pk C (2*m+1) true d.f0.1).kept_len];X d.fa)=true:=h▸hM
     rw[h1] at h2;cases h2
    have Hl:tq≠tu:=fun h=>HM (by rw[←h,Hk] at z;injection z with h1;O)
    have Hx:tq< D.size:=by rw[HQ];X _S
    have _L:D.gates[tq]'Hx=C.gates[tq]'_S:=List.getElem_set_ne (Ne.symm Hl) _
    have H9:pC (2*m+2) tq (2*m) (C.gates[tq]'_S):=by
     obtain ⟨q',hq',_,HX,h0a,h0b,_⟩:=p4 d.f0.1 _S hM;rw[Hk] at HX;injection HX with hq_eq;have _M:q'=d.fv :=W;subst _M;have Ha:(C.gates[tq]'_S).op=.or:=h0a.symm.trans d.fI;rcases pc d.f0 d.fn tq _S with ⟨hV,_,_,_⟩|⟨_,c1,c2,HY,hc1,hc2,_⟩
     ·rw[Ha] at hV;cases hV
     ·obtain ⟨u1,u2,_,_,h0q,h0r,_p⟩:=h0b .or c1 c2 (ir rfl) Ha HY hc1 hc2
      have Hm:∀c,c< 2*m+2+tq->HD.fc.getD c (.const false)=.wire (2*m)->c=2*m:=fun c h10 _3=>by
       by_cases h11:c< 2*m+2
       ·by_cases hc1:c=2*m+1
        ·rw[hc1,p9 C (2*m+1) true d.f0.1] at _3;cases _3
        ·rw[pd C (2*m+1) true c W] at _3;injection _3
       ·exfalso;set tc:=c-(2*m+2);have htc:tc< C.size :=W
        have HZ:c=2*m+2+tc :=W;by_cases h0c:tc=d.f3
        ·rw[HZ,h0c,d.fh] at _3;cases _3
        ·by_cases h0d:tc=d.f4
         ·rw[HZ,h0d,d.fz,hu,z] at _3;injection _3 with h1;O
         ·have hkc:=pE d.f0.1 d.fe htc h0c h0d
          obtain ⟨h12,_,_,h0s,_,_,_⟩:=p4 d.f0.1 htc hkc;rw[HZ,h0s] at _3;injection _3 with h1;O
      rcases d.fK with h|h<;>rw[h] at _p <;>
       (injection _p with h1' hrest';injection hrest' with h2')
      ·have:=Hm c1 hc1 (h1'▸h0q);subst this;X ⟨by simp[pa,Ha,HY],hc1⟩
      ·have:=Hm c2 hc2 (h2'▸h0r);subst this;X ⟨by simp[pa,Ha,HY],hc2⟩
    have hY:pC (2*m+2) tu (2*m) (D.gates[tu]'Hh):=by
     have HE:D.gates[tu]'Hh=⟨.or,[2*m,b]⟩:=List.getElem_set_self _;rw[HE];X ⟨by simp[pa],by O⟩
    have hP:∀(t3:ℕ) (ht3:t3< D.size),t3≠d.f3->t3≠d.f4 ->
      s.fb[t3]'(by rw[f.kept_len];X ht3)=false->False:=fun t3 ht3 h0t h0u _N=>by
     have h13:=zR (i:=d.f3) (j:=d.f4) (k:=t3)
      (by rw[f.kept_len];X hh) (by rw[f.kept_len];X hC)
      (by rw[f.kept_len];X ht3) (by have:=d.fP;O) h0t.symm h0u.symm Hi Hj _N
     have h0p:=qk s.fb;have _t:H7.size=s.fb.count true:=f.gates_len;have h09:s.fb.length=D.size:=f.kept_len
     have:=d.hm;O
    have hE:s.fb[tu]'(by rw[f.kept_len];X Hh)=true:=by
     cases hk:s.fb[tu]'(by rw[f.kept_len];X Hh) with
     | true=>rfl
     | false=>X absurd hk (hP tu Hh _4 W)
    have hF:s.fb[tq]'(by rw[f.kept_len];X Hx)=true:=by
     cases hk:s.fb[tq]'(by rw[f.kept_len];X Hx) with
     | true=>rfl
     | false=>X absurd hk (hP tq Hx HV HW)
    obtain ⟨_q,hZ,_,Hn,_,_,_⟩:=p4 hJ Hh hE;obtain ⟨_r,H0,_,Ho,_,_,_⟩:=p4 hJ Hx hF
    have _h:_q≠_r:=fun HK=>Hl.symm
     (pO hJ Hh Hx hE hF (HK▸Hn) Ho)
    have _0:s.fc.getD (2*m) (.const false)=.wire (2*m) :=
     pd D (2*m+1) true (2*m) W
    have _O:=pp _m _I h08 Hh hE hZ Hn hY _0;have _P:=pp _m _I h08 Hx hF H0 Ho (_L.symm▸H9) _0;have hG:FanInTwo H7:=qi D (2*m+1) true hJ;set H1:=p5 H7 (2*m) false;set _Q:=p3 H7 (2*m) false;have l:=pk H7 (2*m) false hG
    have Hy:H1.fb[_q]'(by rw[l.kept_len];X hZ)=false:=by
     have h1:=pw (n:=2*m) (b:=false) hG hZ _O
      (p9 H7 (2*m) false hG)
     rwa[List.getD_eq_getElem _ _ (by rw[l.kept_len];X hZ)] at h1
    have Hz:H1.fb[_r]'(by rw[l.kept_len];X H0)=false:=by
     have h1:=pw (n:=2*m) (b:=false) hG H0 _P
      (p9 H7 (2*m) false hG)
     rwa[List.getD_eq_getElem _ _ (by rw[l.kept_len];X H0)] at h1
    have h0i:=za (by rw[l.kept_len];X hZ) (by rw[l.kept_len];X H0) _h Hy Hz
    have h0j:=qk H1.fb;have h0k:_Q.size=H1.fb.count true:=l.gates_len;have h0e:H1.fb.length=H7.size:=l.kept_len
    have HG:cF (2*m) _Q=pq (2*m):=funext fun y=>by
     have hH:∀y':Fin (2*m)->Bool,cF (2*m+1) H7 (Fin.snoc y' false)=pq (2*m) y':=fun y'=>by
      have h0:∀y:Fin (2*m+1)->Bool,cF (2*m+1) H7 y=(y (Fin.last (2*m))||pq (2*m) (Fin.init y)):=fun y=>by
       rw[q6 D (2*m+1) true hJ _n y,Hg,qT (2*m+1) W y];R
      rw[h0 (Fin.snoc y' false),Fin.snoc_last,Fin.init_snoc];R
     have _1:∃y1 y2:Fin (2*m)->Bool,
       cF (2*m+1) H7 (Fin.snoc y1 false)≠cF (2*m+1) H7 (Fin.snoc y2 false):=by
      obtain ⟨y1,y2,hne⟩:=ps (n:=2*m) W;X ⟨y1,y2,by rw[hH,hH];X hne⟩
     X (q6 H7 (2*m) false hG _1 y).trans (hH y)
    have _2:=q9 (2*m) W _Q (qi H7 (2*m) false hG) HG;simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left m (by O:0< 2)] at _2
    have:=d.hm;O
 subst Ht;rw[d.fx] at hT;injection hT with hkz_eq;have _i:Hb=d.fg :=W;subst _i;X ⟨z,Su,_U,hSu,HA,H3⟩
private lemma jU {m:ℕ} {C:J} (d:zB m C) (_W:2<=m) (hw:d.w=2*m-1)
  {tu:ℕ} (Hp:tu< d.f4) (hu:d.u=2*m+2+tu)
  (hU:(p5 C (2*m+1) true).fc.getD (2*m+2+tu) (.const false)=.wire (2*m+1+d.fv))
  {Su:Finset ℕ} (_2:Su.Nonempty) (_e:∀e∈Su,e+1< 2*m) (_f:2*m-2∈Su)
  (hV:p8 (p3 (p3 C (2*m+1) true) (2*m) false) d.fg=ph m Su) :
  let b:=p3 (p3 C (2*m+1) true) (2*m) false
  ∃r0:ℕ,∃(hA:r0< b.size),
   (b.gates[r0]'hA).op=.or/\d.fg< r0 /\
   ∃HA:Finset ℕ,HA.Nonempty/\(∀e∈HA,e+1< 2*m)/\p8 b r0=ph m HA /\
    (∀e∈Su,e∈HA)/\(∃e3∈HA,e3∉Su) /\
   ∃d0:ℕ,d0< 2*m+r0/\d0≠2*m+d.fg /\
    ((b.gates[r0]'hA).inputs=[2*m+d.fg,d0]\/(b.gates[r0]'hA).inputs=[d0,2*m+d.fg]) /\
    (∀e,e+3<=2*m ->
     pl b (pe e:Fin (2*m)->Bool) r0 (p0 b (pe e:Fin (2*m)->Bool) d0) b.output=true) /\
    p0 b (pe (2*m-2):Fin (2*m)->Bool) d0=false /\
    pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false b.output=false:=by
 dsimp only;set HK:=p5 C (2*m+1) true;set Ha:=p3 C (2*m+1) true;set HE:=p5 Ha (2*m) false;set b:=p3 Ha (2*m) false;have _3:tu< C.size:=by have:=d.fa;O
 have _4:tu≠d.f3:=by have:=d.fU;O
 have HF:cF (2*m+2) C (e1 (2*m))=false:=by rw[d.fd];X pW _ _
 have HL:∃y1 y2:Fin (2*m)->Bool,cF (2*m) b y1≠cF (2*m) b y2:=by
  rw[d.f8];X ps W
 have HM:∀a,pC (2*m+2) d.f3 a (C.gates[d.f3]'d.f9)->¬zG C (2*m+1) a:=fun a hr=>by
  have Hq:=hr.1
  rcases d.ft with c|c <;>
   (simp only[pa,d.fl,c,List.mem_cons,List.not_mem_nil,or_false] at Hq;
    rcases Hq with rfl|rfl;
    first|X pI (p9 C (2*m+1) true d.f0.1)|X d.fE;
    first|X pI (p9 C (2*m+1) true d.f0.1)|X d.fE)
 obtain ⟨_,_,HB⟩:=qW d.f0 d.fJ W d.fn HF
  d.f9 d.fa d.fP d.fi d.fj d.fe d.fh HM d.fm d.fy d.fu d.fp
 have Hb:∀t (ht:t< C.size),pC (2*m+2) t (2*m+2+tu) (C.gates[t]'ht)↔t=d.f4 :=
  fun t ht=>hu▸HB tu Hp hu d.fH t ht
 have hB:=pE d.f0.1 d.fe _3 _4 W
 have z:∀e,e+3<=2*m ->
   p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+d.f3)=false:=fun e he=>by
  have h1:p0 C (pe e:Fin (2*m+2)->Bool) (2*m+1)=false:=by
   rw[p7 C _ (2*m+1) W];simp only[pe,e2,decide_eq_false_iff_not];O
  have h2:p0 C (pe e:Fin (2*m+2)->Bool) (2*m-1)=false:=by
   rw[p7 C _ (2*m-1) W];simp only[pe,e2,decide_eq_false_iff_not];O
  rcases d.ft with c|c
  ·rw[p6 _ d.f9 d.fl (hw▸c) W W,h1,h2];R
  ·rw[p6 _ d.f9 d.fl (hw▸c) W W,h2,h1];R
 have j:∀e,e+3<=2*m ->
   p0 C (pe e:Fin (2*m+2)->Bool) (2*m+2+d.f4)=false:=fun e he=>by
  have _X:=d.fP;rcases d.fy with c|c
  ·rw[pm _ d.fa d.fm c W d.fu,z e he];R
  ·rw[pm _ d.fa d.fm c d.fu W,z e he,Bool.and_false]
 have hJ:C.output≠2*m+2+tu:=fun HN=>by
  obtain ⟨_,_,_,_,_,_,_,HO⟩:=z2 d _3 Hp _4 (hu▸d.fH);have h1:=HO (e1 (2*m));change p0 C (e1 (2*m)) (2*m+2+tu)=_ at h1;rw[←HN,←pb,HF] at h1;simp[e1] at h1
 have hS:Ha.output≠2*m+1+d.fv:=fun HN=>by
  have h1:=q8 d.f0.1 d.fN;rw[HN] at h1;have _g:=pB d.fn;by_cases _L:C.output< 2*m+2
  ·by_cases _5:C.output=2*m+1
   ·rw[_5,p9 C (2*m+1) true d.f0.1] at h1;cases h1
   ·rw[pd C (2*m+1) true C.output W] at h1;injection h1 with h2;O
  ·set vo:=C.output-(2*m+2);have _G:vo< C.size :=W
   have Hc:C.output=2*m+2+vo :=W;by_cases _6:vo=d.f3
   ·rw[Hc,_6,d.fh] at h1;cases h1
   ·by_cases _7:vo=d.f4
    ·have h0:=j 0 W
     rw[←_7,←Hc,←pb,d.fd,q0 W] at h0;cases h0
    ·have _M:=pE d.f0.1 d.fe _G _6 _7
     have:=pO d.f0.1 _G _3 _M hB (Hc▸h1) hU
     X hJ W
 obtain ⟨r,g,_8,hW⟩:∃r,∃(g:r< Ha.size),d.fv< r /\
   pC (2*m+1) r (2*m+1+d.fv) (Ha.gates[r]'g) :=
  (pY d.f7 d.fv d.fD).resolve_left hS
 have Hr:p0 Ha (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+r)=true:=by
  have hK:(Ha.gates[r]'g).op=.or:=by
   rcases pc d.f7 d.fq r g with ⟨hX,_,_,_⟩|⟨h|h,_,_,_,_,_,_⟩
   ·X absurd hX (d.fC _ (List.getElem_mem g))
   ·X absurd (jh d.fD d.fI d.fK d.fw) (by rw[d.fp r g h _ hW];decide)
   ·X h
  rcases pc d.f7 d.fq r g with ⟨hX,_,_,_⟩|⟨_,x1,x2,c,_k,_l,_⟩
  ·rw[hK] at hX;cases hX
  ·have hT:(Ha.gates[r]'g).inputs=[x1,x2]:=c
   have Hq:2*m+1+d.fv∈pa (Ha.gates[r]'g):=hW.1;simp[pa,hK,hT] at Hq;rw[p6 _ g hK hT _k _l,Bool.or_eq_true];rcases Hq with rfl|rfl<;>[X il (jh d.fD d.fI d.fK d.fw);X ir (jh d.fD d.fI d.fK d.fw)]
 have n:=q4 d.f7.1 d.ff g W;obtain ⟨r0,hA,_,Hd,_9,_,_⟩:=p4 d.f7.1 g n;have _m:r0< b.size:=hA;have p:(b.gates[r0]'hA).op=.or:=_9.trans (d.fk r g Hr)
 have HP:q1 m (p8 b r0):=by
  obtain ⟨w',_H,_n⟩:=d.fS r g Hr;rw[Hd] at _H;cases _H;X _n
 obtain ⟨HA,HQ,_a,HR⟩:=HP
 have HS:pC (2*m) r0 (2*m+d.fg) (b.gates[r0]'hA) :=
  pp d.f7 d.fC d.fq g n hA Hd hW d.fx
 obtain ⟨d0,s,He,hY⟩:∃d0,d0< 2*m+r0/\d0≠2*m+d.fg /\
   ((b.gates[r0]'hA).inputs=[2*m+d.fg,d0]\/(b.gates[r0]'hA).inputs=[d0,2*m+d.fg]):=by
  rcases pc d.f5 HL r0 hA with ⟨hX,_,_,_⟩|⟨_,x1,x2,c,_k,_l,_I⟩
  ·rw[p] at hX;cases hX
  ·have hT:(b.gates[r0]'hA).inputs=[x1,x2]:=c
   have Hq:2*m+d.fg∈pa (b.gates[r0]'hA):=HS.1;simp[pa,p,hT] at Hq;rcases Hq with rfl|rfl
   ·X ⟨x2,_l,_I.symm,il hT⟩
   ·X ⟨x1,_k,_I,ir hT⟩
 have Hl:d.fg< r0:=by have:=HS.2;O
 have hH:∀e∈Su,e∈HA:=fun e he=>(pg _a (_e e he)).1 (by
  rw[←cf HR _]
  X (pQ d.hm d.f5 d.f8 d.f6 d.fA hA ⟨Su,_2,_e,hV⟩ HS).2.2 _
   (by rw[cf hV _];X (pg _e (_e e he)).2 he))
 obtain ⟨e3,HT,HU⟩:∃e3∈HA,e3∉Su:=by
  by_contra h;push Not at h
  X qy d.f5 hA d.fA W
   (HR.trans (by rw[hV];congr 1;ext e;X ⟨h e,hH e⟩))
 have HG:∀e,e+3<=2*m ->
   pl b (pe e:Fin (2*m)->Bool) r0 (p0 b (pe e:Fin (2*m)->Bool) d0) b.output=true:=by
  intro e he;set xe:Fin (2*m+2)->Bool:=pe e;set ye:Fin (2*m)->Bool:=pe e
  have _o:∀i< 2*m+2+C.size,i≠2*m+1->i≠2*m->i≠2*m+2+d.f3->i≠2*m+2+tu ->
    ∀_p HV,HK.fc.getD i (.const false)=.wire _p->HE.fc.getD _p (.const false)=.wire HV ->
     p0 C xe i=true->pl b ye r0 (p0 b ye d0) HV=true:=by
   intro i;induction i using Nat.strong_induction_on with
   | ind i ih=>
    intro _N _O _J _q HH _p HV H3 Hf hC;by_cases _L:i< 2*m+2
    ·have HI:i< 2*m :=W
     have h1:=pd C (2*m+1) true i W;have h2:=pd Ha (2*m) false i HI;rw[H3] at h1;cases h1;rw[Hf] at h2;cases h2;rw[p7 C xe i W] at hC;rw[pA b ye r0 hA _ i W,p7 b ye i HI];X hC
    ·set v:=i-(2*m+2);have hv:v< C.size :=W
     have _b:i=2*m+2+v :=W;rw[_b] at _q HH H3 hC;by_cases _h:v=d.f4
     ·rw[_h,j e he] at hC;cases hC
     ·have hD:=pE d.f0.1 d.fe hv W _h
      obtain ⟨Hm,hI,_,Hh,y,Hg,_⟩:=p4 d.f0.1 hv hD;rw[H3] at Hh;cases Hh
      have H4:Hm≠d.fv:=fun h=>HH (by
       have:=pO d.f0.1 hv _3 hD hB (h▸H3) hU;O)
      have hL:=q4 d.f7.1 d.ff hI H4;obtain ⟨_c,Hs,_,H5,hZ,H0,_⟩:=p4 d.f7.1 hI hL;rw[Hf] at H5;cases H5;rcases pc d.f0 d.fn v hv with ⟨hX,_,_,_⟩|⟨Ht,a1,a2,c,Hu,Hv,_⟩
      ·X absurd hX (d.fJ _ (List.getElem_mem hv))
      ·have hM:∀a,(a=a1\/a=a2)->a< 2*m+2+v ->
         a≠2*m+1/\a≠2*m/\a≠2*m+2+d.f3/\a≠2*m+2+tu:=fun a _r HC=>by
        have _i:pC (2*m+2) v a (C.gates[v]'hv) :=
         ⟨by rcases Ht with h|h<;>rcases _r with rfl|rfl<;>simp[pa,h,c],HC⟩
        X ⟨fun h=>by have:=(d.fi v hv).1 (h▸_i);O,
            fun h=>H4 ((d.fB Hm hI).1 (pp d.f0 d.fJ d.fn hv hD hI H3
             (h▸_i) (pd C (2*m+1) true (2*m) W))),
            fun h=>_h ((d.fj v hv).1 (h▸_i)),
            fun h=>_h ((Hb v hv).1 (h▸_i))⟩
       by_cases HW:_c=r0
       ·rcases HW.symm with rfl
        have HX:Hm=r:=pO d.f7.1 hI g hL n Hf Hd;have Hi:(C.gates[v]'hv).op=.or:=y.symm.trans (hZ.symm.trans p);obtain ⟨hN,hO,H6,H7,hE,hF,hG⟩:=Hg .or a1 a2 (ir rfl) Hi c Hu Hv;obtain ⟨hP,hQ,H1,H2,k,l,hh⟩:=H0 .or hN hO (ir rfl) (y.trans Hi) hG H6 H7;rw[p6 xe hv Hi c Hu Hv,Bool.or_eq_true] at hC
        have Hj:∀a,a< 2*m+2+v->a≠2*m+2+tu ->
          HK.fc.getD a (.const false)=.wire (2*m+1+d.fv)->a=2*m+2+d.f4:=fun a HC _s HY=>by
         by_cases _P:a< 2*m+2
         ·by_cases _t:a=2*m+1
          ·rw[_t,p9 C (2*m+1) true d.f0.1] at HY;cases HY
          ·rw[pd C (2*m+1) true a W] at HY;injection HY with h;O
         ·set ta:=a-(2*m+2);have _K:ta< C.size :=W
          have HJ:a=2*m+2+ta :=W;by_cases _d:ta=d.f3
          ·rw[HJ,_d,d.fh] at HY;cases HY
          ·by_cases _u:ta=d.f4
           ·O
           ·have _Q:=pE d.f0.1 d.fe _K _d _u
            have:=pO d.f0.1 _K _3 _Q hB (HJ▸HY) hU
            O
        have H8:∀a _j HZ,(a=a1\/a=a2)->a< 2*m+2+v ->
          HK.fc.getD a (.const false)=.wire _j->HE.fc.getD _j (.const false)=.wire HZ ->
          p0 C xe a=true->HZ=d0 ->
          pl b ye r0 (p0 b ye d0) (2*m+r0)=true:=fun a _j HZ _r HC _R _S _T _U=>by
         obtain ⟨h1,h2,h3,h4⟩:=hM a _r HC;have Hk:=ih a W W h1 h2 h3 h4 _j d0 _R (_U▸_S) _T;rw[pA b ye r0 hA _ d0 s] at Hk;rw[qs b ye r0 hA _];X Hk
        have HD:[hP,hQ]=[2*m+d.fg,d0]\/[hP,hQ]=[d0,2*m+d.fg]:=by
         rw[←hh];X hY
        have H9:hN=2*m+1+d.fv\/hO=2*m+1+d.fv:=by
         have Hq:2*m+1+d.fv∈pa (Ha.gates[Hm]'hI):=by subst HX;X hW.1
         have _0:(Ha.gates[Hm]'hI).op=.or:=y.trans Hi;have Hn:(Ha.gates[Hm]'hI).inputs=[hN,hO]:=hG;simp[pa,_0,Hn] at Hq;X Hq.imp Eq.symm Eq.symm
        have Hw:hN=2*m+1+d.fv->p0 C xe a1=false:=fun _v=>by
         have:=Hj a1 Hu (hM a1 (il rfl) Hu).2.2.2 (_v▸hE)
         rw[this];X j e he
        have Hx:hO=2*m+1+d.fv->p0 C xe a2=false:=fun _w=>by
         have:=Hj a2 Hv (hM a2 (ir rfl) Hv).2.2.2 (_w▸hF)
         rw[this];X j e he
        rcases HD with h|h<;>(injection h with h1' hrest';injection hrest' with h2')
        ·rcases H9 with hq1|hq2
         ·rcases hC with hv1|hv2
          ·rw[Hw hq1] at hv1;cases hv1
          ·X H8 a2 hO hQ (ir rfl) Hv hF l hv2 h2'
         ·rw[hq2,d.fx] at l;injection l with _1;X absurd (_1.trans h2') He.symm
        ·rcases H9 with hq1|hq2
         ·rw[hq1,d.fx] at k;injection k with _1;X absurd (_1.trans h1') He.symm
         ·rcases hC with hv1|hv2
          ·X H8 a1 hN hP (il rfl) Hu hE k hv1 h1'
          ·rw[Hx hq2] at hv2;cases hv2
       ·rcases Ht with hop_eq|hop_eq
        ·obtain ⟨hN,hO,H6,H7,hE,hF,hG⟩:=Hg .and a1 a2 (il rfl) hop_eq c Hu Hv
         obtain ⟨hP,hQ,H1,H2,k,l,hh⟩:=H0 .and hN hO (il rfl) (y.trans hop_eq) hG H6 H7;rw[pm xe hv hop_eq c Hu Hv,Bool.and_eq_true] at hC;rw[pF ye hA _ Hs HW (hZ.trans (y.trans hop_eq)) hh H1 H2,Bool.and_eq_true];obtain ⟨_x,_y,_z,_A⟩:=hM a1 (il rfl) Hu;obtain ⟨_B,_C,_D,_E⟩:=hM a2 (ir rfl) Hv
         X ⟨ih a1 W W _x _y _z _A hN hP hE k hC.1,
          ih a2 W W _B _C _D _E hO hQ hF l hC.2⟩
        ·obtain ⟨hN,hO,H6,H7,hE,hF,hG⟩:=Hg .or a1 a2 (ir rfl) hop_eq c Hu Hv
         obtain ⟨hP,hQ,H1,H2,k,l,hh⟩:=H0 .or hN hO (ir rfl) (y.trans hop_eq) hG H6 H7;rw[p6 xe hv hop_eq c Hu Hv,Bool.or_eq_true] at hC;rw[pJ ye hA _ Hs HW (hZ.trans (y.trans hop_eq)) hh H1 H2,Bool.or_eq_true];rcases hC with h1|h2
         ·obtain ⟨_x,_y,_z,_A⟩:=hM a1 (il rfl) Hu
          X il (ih a1 W W _x _y _z _A hN hP hE k h1)
         ·obtain ⟨_B,_C,_D,_E⟩:=hM a2 (ir rfl) Hv
          X ir (ih a2 W W _B _C _D _E hO hQ hF l h2)
  have Hy:C.output≠2*m+1:=fun h=>
   pL d.f0.1 d.fN (p9 C (2*m+1) true d.f0.1) h
  have Hz:C.output≠2*m+2+d.f3:=fun h=>
   pL d.f0.1 d.fN d.fh h
  have Ho:C.output≠2*m:=fun h=>by
   have h1:=q8 d.f0.1 d.fN;rw[h,pd C (2*m+1) true (2*m) W] at h1;injection h1 with h2;X pL d.f7.1 d.fO (p9 Ha (2*m) false d.f7.1) h2.symm
  X _o C.output (pB d.fn) Hy Ho Hz hJ Ha.output b.output
   (q8 d.f0.1 d.fN) (q8 d.f7.1 d.fO)
   (by change cF (2*m+2) C xe=true;rw[d.fd];X q0 W)
 have f:pl b (pe (2*m-2):Fin (2*m)->Bool) r0
   (p0 b (pe (2*m-2):Fin (2*m)->Bool) d0) b.output=false:=by
  cases h:pl b (pe (2*m-2):Fin (2*m)->Bool) r0
    (p0 b (pe (2*m-2):Fin (2*m)->Bool) d0) b.output with
  | false=>rfl
  | true=>
   exfalso
   Y qN d.f5 d.f6.1 d.f8 hA s (fun x hx=>by
    rcases hY with c|c
    ·rw[p6 x hA p c W s,hx,Bool.or_true]
    ·rw[p6 x hA p c s W,hx];rfl) fun e he=>?_
   by_cases _F:e=2*m-2
   ·subst _F;X h
   ·X HG e W
 have q:p0 b (pe (2*m-2):Fin (2*m)->Bool) d0=false:=by
  cases hd0v:p0 b (pe (2*m-2):Fin (2*m)->Bool) d0 with
  | false=>rfl
  | true=>
   exfalso
   have _V:p0 b (pe (2*m-2):Fin (2*m)->Bool) d0 =
     p0 b (pe (2*m-2):Fin (2*m)->Bool) (2*m+r0):=by
    rw[hd0v];rcases hY with c|c
    ·rw[p6 _ hA p c W s,hd0v,Bool.or_true]
    ·rw[p6 _ hA p c s W,hd0v];R
   rw[pV b _ r0 hA _ _V,←pb,d.f8,q0 W] at f;cases f
 have hR:pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false b.output=false:=by
  conv_lhs=>rw[←q]
  X f
 X ⟨r0,hA,p,Hl,HA,HQ,_a,HR,hH,⟨e3,HT,HU⟩,
  d0,s,He,hY,HG,q,hR⟩
private lemma jT {m:ℕ} (_q:2<=m) {b:J}
  (c:IsMinimalCircuit (2*m) b) (f:cF (2*m) b=pq (2*m))
  (i:qf m b)
  {kz r0:ℕ} (hQ:r0< b.size) (hG:(b.gates[r0]'hQ).op=.or) (HB:kz< r0)
  {Su Hc:Finset ℕ} (_f:∀e∈Su,e+1< 2*m) (hR:2*m-2∈Su)
  {e':ℕ} (hW:e'∈Su) (Hh:e'≠2*m-2)
  (Hi:Hc.Nonempty) (H4:∀e∈Hc,e+1< 2*m) (HD:p8 b r0=ph m Hc)
  (s:∀e∈Su,e∈Hc) {e3:ℕ} (hX:e3∈Hc) (hY:e3∉Su)
  {d0:ℕ} (Hj:(b.gates[r0]'hQ).inputs=[2*m+kz,d0]\/(b.gates[r0]'hQ).inputs=[d0,2*m+kz])
  (hD:p0 b (pe (2*m-2):Fin (2*m)->Bool) d0=false)
  (k:pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false b.output=false) :
  (∀(x:Fin (2*m)->Bool) (v0:Bool) (a:ℕ) (ha:a< b.size),
   (b.gates[a]'ha).op=.and->pl b x r0 v0 (2*m+a)=p0 b x (2*m+a)) /\
  (∀(w:ℕ) (hw:w< b.size),p8 b w=qd m (2*m-4) (2*m-2) ->
   (∀a (ha:a< b.size),pC (2*m) a (2*m+w) (b.gates[a]'ha) ->
    (b.gates[a]'ha).op=.and /\
    ((b.gates[a]'ha).inputs=[2*m+w,2*m-3]\/(b.gates[a]'ha).inputs=[2*m-3,2*m+w])) ->
   ∀(x:Fin (2*m)->Bool) (u:ℕ),u< 2*m+b.size->u≠2*m+w ->
    p0 (pU b w ⟨.or,[2*m-4,2*m-2]⟩) x u=p0 b x u) /\
  (∀v (hv:v< b.size),kz< v->v≠r0->q1 m (p8 b v) ->
   pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false (2*m+v)=false):=by
 have hm:1<=m :=W
 have hh:∃y1 y2:Fin (2*m)->Bool,cF (2*m) b y1≠cF (2*m) b y2:=by
  rw[f];X ps W
 have hZ:∀(x:Fin (2*m)->Bool) (v0:Bool) (w:ℕ),w< 2*m+b.size ->
   pl b x r0 v0 w≠p0 b x w ->
   ∃g,∃(_:g< b.size),w=2*m+g/\q1 m (p8 b g) /\
    (∀e∈Hc,p8 b g (pe e:Fin (2*m)->Bool)=true):=fun x v0 w=>by
  induction w using Nat.strong_induction_on with
  | ind w ih=>
   intro hw hI;by_cases HR:w< 2*m+r0
   ·X absurd (pA b x r0 hQ v0 w HR) hI
   ·by_cases HS:w=2*m+r0
    ·X ⟨r0,hQ,HS,⟨Hc,Hi,H4,HD⟩,fun e he=>by rw[cf HD _];X (pg H4 (H4 e he)).2 he⟩
    ·set g:=w-2*m;have hg:g< b.size :=W
     have H0:w=2*m+g :=W;rw[H0] at hI ⊢;rcases pc c hh g hg with ⟨hJ,_,_,_⟩|⟨p,x1,x2,n,hM,hN,_⟩
     ·X absurd hJ (i.1 _ (List.getElem_mem hg))
     ·have _g:pl b x r0 v0 x1≠p0 b x x1\/pl b x r0 v0 x2≠p0 b x x2:=by
       by_contra hsame;push Not at hsame;apply hI
       rcases p with hop_eq|hop_eq
       ·rw[pF x hQ v0 hg W hop_eq n hM hN,pm x hg hop_eq n hM hN,hsame.1,hsame.2]
       ·rw[pJ x hQ v0 hg W hop_eq n hM hN,p6 x hg hop_eq n hM hN,hsame.1,hsame.2]
      have Hd:∀x0,(x0=x1\/x0=x2)->x0< 2*m+g->pl b x r0 v0 x0≠p0 b x x0 ->
        ∃g',∃(_:g'< b.size),2*m+g=2*m+g'/\q1 m (p8 b g') /\
         (∀e∈Hc,p8 b g' (pe e:Fin (2*m)->Bool)=true):=fun x0 _h _i HT=>by
       obtain ⟨gx,_8,rfl,H1,z⟩:=ih x0 W W HT
       have HE:pC (2*m) g (2*m+gx) (b.gates[g]'hg) :=
        ⟨by rcases p with He|He<;>rcases _h with rfl|rfl<;>simp[pa,He,n],_i⟩
       obtain ⟨_,Hk|HU,HF⟩:=pQ hm c f i _8 hg H1 HE
       ·X ⟨g,hg,rfl,Hk,fun e he=>HF _ (z e he)⟩
       ·X absurd HU (qU hm c f i _8 hg
         (by O:(2*m-2)+1< 2*m) (_f e' hW) (H4 e3 hX)
         Hh.symm (fun h=>hY (h▸hR)) (fun h=>hY (h▸hW)) H1
         (z (2*m-2) (s (2*m-2) hR))
         (z e' (s e' hW)) (z e3 hX) HE)
      rcases _g with h|h<;>[X Hd x1 (il rfl) hM h;X Hd x2 (ir rfl) hN h]
 have j:∀(x:Fin (2*m)->Bool) (v0:Bool) (w:ℕ),w< 2*m+b.size ->
   ¬q1 m (fun y=>p0 b y w)->pl b x r0 v0 w=p0 b x w:=fun x v0 w hw HV=>by
  by_contra hI
  obtain ⟨g,_,rfl,Hk,_⟩:=hZ x v0 w hw hI;X HV Hk
 have l:∀(x:Fin (2*m)->Bool) (v0:Bool) (a:ℕ) (ha:a< b.size),
   (b.gates[a]'ha).op=.and->pl b x r0 v0 (2*m+a)=p0 b x (2*m+a):=fun x v0 a ha d=>by
  have HG:a≠r0:=fun h=>by subst h;rw[hG] at d;cases d
  obtain ⟨_,c1,c2,Hf,_9,_a,_,HW,HX,_⟩:=qn hm c f i ha d
  rw[pF x hQ v0 ha HG d Hf _9 _a,pm x ha d Hf _9 _a,
   j x v0 c1 W HW,j x v0 c2 W HX]
 have hA:∀(w:ℕ) (hw:w< b.size),p8 b w=qd m (2*m-4) (2*m-2) ->
   (∀a (ha:a< b.size),pC (2*m) a (2*m+w) (b.gates[a]'ha) ->
    (b.gates[a]'ha).op=.and /\
    ((b.gates[a]'ha).inputs=[2*m+w,2*m-3]\/(b.gates[a]'ha).inputs=[2*m-3,2*m+w])) ->
   ∀(x:Fin (2*m)->Bool) (u:ℕ),u< 2*m+b.size->u≠2*m+w ->
    p0 (pU b w ⟨.or,[2*m-4,2*m-2]⟩) x u=p0 b x u:=fun w hw H2 HY x=>
  qP b hw ⟨.or,[2*m-4,2*m-2]⟩ x fun t ht _=>by
   rcases pc c hh t ht with ⟨hJ,_,_,_⟩|⟨p,x1,x2,hK,hM,hN,_⟩
   ·X absurd hJ (i.1 _ (List.getElem_mem ht))
   ·by_cases HZ:pC (2*m) t (2*m+w) (b.gates[t]'ht)
    ·obtain ⟨Hl,HH⟩:=HY t ht HZ
     have H5:p0 (pU b w ⟨.or,[2*m-4,2*m-2]⟩) x (2*m+w) =
       (x ⟨2*m-4,by O⟩||x ⟨2*m-2,by O⟩):=by
      rw[qg b x hw]
      simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
       show 2*m-4< 2*m+w by O,show 2*m-2< 2*m+w by O,↓reduceIte,
       p7 b x (2*m-4) W,p7 b x (2*m-2) W]
     have _0:p0 b x (2*m+w)=((x ⟨2*m-4,by O⟩&&x ⟨2*m-3,by O⟩)||x ⟨2*m-2,by O⟩):=by
      rw[show p0 b x (2*m+w)=qd m (2*m-4) (2*m-2) x from cf H2 x,qh W W]
      have:(⟨2*m-4+1,by O⟩:Fin (2*m))=⟨2*m-3,by O⟩:=Fin.ext (by dsimp;O)
      rw[this]
     rw[pj b x t ht,Hl,hK];simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,hM,hN,↓reduceIte]
     rcases HH with h|h<;>rw[hK] at h <;>
      (injection h with h1' hrest';injection hrest' with h2';rw[h1',h2'];
       simp only[↓reduceIte,show 2*m-3≠2*m+w by O,H5,_0,p7 b x (2*m-3) W];
       cases x ⟨2*m-4,by O⟩<;>cases x ⟨2*m-3,by O⟩<;>cases x ⟨2*m-2,by O⟩<;>rfl)
    ·have Hm:x1≠2*m+w:=fun h=>HZ ⟨by rcases p with He|He<;>simp[pa,He,hK,h],h▸hM⟩
     have Hn:x2≠2*m+w:=fun h=>HZ ⟨by rcases p with He|He<;>simp[pa,He,hK,h],h▸hN⟩
     rw[pj b x t ht,hK];simp only[List.map_cons,List.map_nil,hM,hN,Hm,Hn,↓reduceIte]
 have q:∀w< 2*m+b.size,
   pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false w=true ->
   p0 b (pe (2*m-2):Fin (2*m)->Bool) w=true:=by
  intro w;induction w using Nat.strong_induction_on with
  | ind w ih=>
   intro hw H6;by_cases HR:w< 2*m+r0
   ·rwa[pA b _ r0 hQ false w HR] at H6
   ·by_cases HS:w=2*m+r0
    ·rw[HS,qs b _ r0 hQ false] at H6;cases H6
    ·set g:=w-2*m;have hg:g< b.size :=W
     have H0:w=2*m+g :=W;rw[H0] at H6 ⊢;rcases pc c hh g hg with ⟨hJ,_,_,_⟩|⟨p,x1,x2,n,hM,hN,_⟩
     ·X absurd hJ (i.1 _ (List.getElem_mem hg))
     ·rcases p with hop_eq|hop_eq
      ·rw[pF _ hQ false hg W hop_eq n hM hN,Bool.and_eq_true] at H6
       rw[pm _ hg hop_eq n hM hN,Bool.and_eq_true];X ⟨ih x1 W W H6.1,ih x2 W W H6.2⟩
      ·rw[pJ _ hQ false hg W hop_eq n hM hN,Bool.or_eq_true] at H6
       rw[p6 _ hg hop_eq n hM hN,Bool.or_eq_true];rcases H6 with h1|h2<;>[X il (ih x1 W W h1);X ir (ih x2 W W h2)]
 Y ⟨l,hA,?_⟩
 by_contra H7;push Not at H7;classical
 obtain ⟨v0,_b,Ho,Hp,Hq,H8⟩:=H7
 have HI:pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false (2*m+v0)=true:=by
  cases h:pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false (2*m+v0)
  ·X absurd h H8
  ·rfl
 let P1:ℕ->Prop:=fun v=>∃(_:v< b.size),kz< v/\v≠r0/\q1 m (p8 b v) /\
  pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false (2*m+v)=true
 set S1:=(Finset.range b.size).filter P1;have hS:v0∈S1:=Finset.mem_filter.2 ⟨Finset.mem_range.2 _b,_b,Ho,Hp,Hq,HI⟩;set v:=S1.max' ⟨v0,hS⟩;obtain ⟨hv,_c,_d,HJ,hB⟩:=(Finset.mem_filter.1 (Finset.max'_mem S1 ⟨v0,hS⟩)).2
 have hO:∀u (hu:u< b.size),v< u->u≠r0->q1 m (p8 b u) ->
   pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false (2*m+u)=true->False:=fun u hu _r _j _k _l=>by
  have:=Finset.le_max' S1 u (Finset.mem_filter.2 ⟨Finset.mem_range.2 hu,hu,by O,_j,_k,_l⟩);O
 have hE:b.output≠2*m+v:=fun Hr=>by rw[Hr,hB] at k;cases k
 obtain ⟨Sv,HK,_1,_m⟩:=HJ;have Hs:p8 b v=ph m Sv:=_m;have Ht:2*m-2∈Sv:=(pg _1 W).1 (by rw[←cf Hs _];X q (2*m+v) W hB)
 have hF:∀w (hw:w< b.size),pC (2*m) w (2*m+v) (b.gates[w]'hw) ->
   p8 b w=qd m (2*m-4) (2*m-2) /\
   (∀a (ha:a< b.size),pC (2*m) a (2*m+w) (b.gates[a]'ha) ->
    (b.gates[a]'ha).op=.and /\
    ((b.gates[a]'ha).inputs=[2*m+w,2*m-3]\/(b.gates[a]'ha).inputs=[2*m-3,2*m+w])):=by
  intro w hw Hu;have _n:v< w:=by have:=Hu.2;O
  have hL:w≠r0:=fun h=>by
   subst h;have Hv:2*m+v∈pa (b.gates[w]'hQ):=Hu.1
   have _o:2*m+v=d0:=by
    rcases Hj with H3|H3<;>(simp[pa,hG,H3] at Hv;rcases Hv with h1|h2<;>first|O|X h1|X h2)
   have _e:=q (2*m+v) W hB;rw[_o,hD] at _e;cases _e
  obtain ⟨hT,_2|⟨iw,kw,H9,HO,HP,hH,H2⟩,_⟩ :=
   pQ hm c f i hv hw ⟨Sv,HK,_1,Hs⟩ Hu
  ·exfalso
   rcases pc c hh w hw with ⟨hJ,_,_,_⟩|⟨_,x1,x2,H3,hM,hN,_⟩
   ·rw[hT] at hJ;cases hJ
   ·have Hv:2*m+v∈pa (b.gates[w]'hw):=Hu.1
    simp[pa,hT,H3] at Hv
    have Hw:pl b (pe (2*m-2):Fin (2*m)->Bool) r0 false (2*m+w)=true:=by
     rw[pJ _ hQ false hw hL hT H3 hM hN,Bool.or_eq_true];rcases Hv with rfl|rfl<;>[X il hB;X ir hB]
    X hO w hw _n hL _2 Hw
  ·obtain ⟨_,kuw,_,Sw,_,_p,_,Hx,HL,_3⟩ :=
    qB hm c f i hw H9 HO HP hH H2
   have Ha:v=kuw:=by
    have Hv:2*m+v∈pa (b.gates[w]'hw):=Hu.1;rcases _3 with h|h<;>(simp[pa,hT,h] at Hv;O)
   have Hy:Sv=Sw:=qM _1 _p (Hs.symm.trans (Ha▸HL));have HC:=Hx (2*m-2) (Hy▸Ht)
   have hV:(iw=2*m-2/\kw=2*m-3)\/(iw=2*m-4/\kw=2*m-2):=by
    rcases hH with rfl|_<;>O
   rcases hV with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·exfalso
    obtain ⟨a,ha,_s,HQ⟩:=(pY c w hw).resolve_left (qz f ⟨2*m-2,2*m-3,H9,HO,HP,hH,H2⟩);obtain ⟨d,hP⟩:=qr hm c f i hw ha H9 HO HP hH H2 HQ;have hC:a≠r0:=fun h=>by subst h;rw[hG] at d;cases d
    have hU:q1 m (p8 b a)/\p8 b a (pe (2*m-2):Fin (2*m)->Bool)=true:=by
     rcases hP with ⟨H7,_⟩|⟨_,⟨Hg,_⟩|⟨_,Hg⟩⟩
     ·O
     ·X ⟨⟨{2*m-2-1,2*m-2},⟨2*m-2,by simp⟩,fun e he=>by simp at he;O,Hg⟩,
       by rw[cf Hg _,pg (fun e he=>by simp at he;O) W];simp⟩
     ·X ⟨⟨{2*m-2-2,2*m-2-1,2*m-2},⟨2*m-2,by simp⟩,fun e he=>by simp at he;O,Hg⟩,
       by rw[cf Hg _,pg (fun e he=>by simp at he;O) W];simp⟩
    X hO a ha W hC hU.1 ((l _ false a ha d).trans hU.2)
   ·Y ⟨H2,fun a ha HQ=>?_⟩
    obtain ⟨d,hP⟩:=qr hm c f i hw ha H9 HO HP hH H2 HQ;have hC:a≠r0:=fun h=>by subst h;rw[hG] at d;cases d
    rcases hP with ⟨_,⟨_,_4⟩|⟨_,Hg⟩⟩|⟨H7,_⟩
    ·Y ⟨d,?_⟩;rwa[show 2*m-4+1=2*m-3 by O] at _4
    ·exfalso
     have HM:q1 m (p8 b a):=⟨{2*m-4,2*m-4+1,2*m-4+2},⟨2*m-4,by simp⟩,fun e he=>by simp at he;O,Hg⟩
     have _5:p8 b a (pe (2*m-2):Fin (2*m)->Bool)=true:=by
      rw[cf Hg _,pg (fun e he=>by simp at he;O) W];simp;O
     X hO a ha (by have:=HQ.2;O) hC HM ((l _ false a ha d).trans _5)
    ·O
 obtain ⟨w,hw,_,Hu⟩:=(pY c v hv).resolve_left hE;obtain ⟨H2,HN⟩:=hF w hw Hu;set Dw:=pU b w ⟨.or,[2*m-4,2*m-2]⟩;have Hz:=hA w hw H2 HN
 have Hb:=qC c ⟨.or,[2*m-4,2*m-2]⟩ ⟨by simp,by simp⟩
  (funext fun x=>Hz x b.output (pB hh) (qz f ⟨2*m-4,2*m-2,by O,by O,by O,il W,H2⟩))
 rcases pY Hb v (by rw[pS];X hv) with Hr|⟨r,hr,_,_6⟩
 ·X hE Hr
 ·have _7:r< b.size:=by rw[←pS b w];X hr
  by_cases hH:r=w
  ·subst hH;have HA:Dw.gates[r]'hr=⟨.or,[2*m-4,2*m-2]⟩:=List.getElem_set_self _
   rw[HA] at _6;simp[pC,pa] at _6;O
  ·have HA:Dw.gates[r]'hr=b.gates[r]'_7:=List.getElem_set_ne (Ne.symm hH) _
   X qy c _7 hw hH ((hF r _7 (HA▸_6)).1.trans H2.symm)
private lemma jO {m:ℕ} (hm2:2<=m) {d:J}
  (f:IsMinimalCircuit (2*m) d) (i:cF (2*m) d=pq (2*m))
  (s:qf m d)
  {kz r0:ℕ} (HY:kz< d.size) (H5:r0< d.size) (hB:(d.gates[r0]'H5).op=.or) (HQ:kz< r0)
  {Su Sr0:Finset ℕ} (_X:Su.Nonempty) (_0:∀e∈Su,e+1< 2*m) (hh:2*m-2∈Su)
  {e':ℕ} (_B:e'∈Su) (_H:e'≠2*m-2) (k:p8 d kz=ph m Su)
  (_I:Sr0.Nonempty) (h0d:∀e∈Sr0,e+1< 2*m) (_Y:p8 d r0=ph m Sr0)
  (Hn:∀e∈Su,e∈Sr0) {e3:ℕ} (_J:e3∈Sr0) (_K:e3∉Su)
  {d0:ℕ} (hI:d0< 2*m+r0) (_1:d0≠2*m+kz)
  (H7:(d.gates[r0]'H5).inputs=[2*m+kz,d0]\/(d.gates[r0]'H5).inputs=[d0,2*m+kz])
  (_C:∀e,e+3<=2*m ->
   pl d (pe e:Fin (2*m)->Bool) r0 (p0 d (pe e:Fin (2*m)->Bool) d0) d.output=true)
  (He:p0 d (pe (2*m-2):Fin (2*m)->Bool) d0=false)
  (H8:pl d (pe (2*m-2):Fin (2*m)->Bool) r0 false d.output=false) :
  False:=by
 have hm:1<=m :=W
 have hZ:∃y1 y2:Fin (2*m)->Bool,cF (2*m) d y1≠cF (2*m) d y2:=by
  rw[i];X ps W
 obtain ⟨hG,Ht,hN⟩ :=
  jT hm2 f i s H5 hB HQ _0 hh _B _H
   _I h0d _Y Hn _J _K H7 He H8
 have H9:∀w (hw:w< d.size),w≠r0->pC (2*m) w (2*m+kz) (d.gates[w]'hw) ->
   p8 d w=qd m (2*m-4) (2*m-2) /\
   (∀a (ha:a< d.size),pC (2*m) a (2*m+w) (d.gates[a]'ha) ->
    (d.gates[a]'ha).op=.and /\
    ((d.gates[a]'ha).inputs=[2*m+w,2*m-3]\/(d.gates[a]'ha).inputs=[2*m-3,2*m+w])):=by
  intro w hw hH _L;have _M:kz< w:=by have:=_L.2;O
  obtain ⟨HF,h0e|⟨iw,kw,_v,hiw,hkw,_2,_s⟩,_⟩ :=
   pQ hm f i s HY hw ⟨Su,_X,_0,k⟩ _L
  ·exfalso
   rcases pc f hZ w hw with ⟨hP,_,_,_⟩|⟨_,x1,x2,l,hU,hV,_⟩
   ·rw[HF] at hP;cases hP
   ·have Hg:2*m+kz∈pa (d.gates[w]'hw):=_L.1
    simp[pa,HF,l] at Hg
    have HG:pl d (pe (2*m-2):Fin (2*m)->Bool) r0 false (2*m+kz)=true:=by
     rw[pA d _ r0 H5 false (2*m+kz) W];change p8 d kz _=true;rw[k];X (pg _0 W).2 hh
    have _3:pl d (pe (2*m-2):Fin (2*m)->Bool) r0 false (2*m+w)=true:=by
     rw[pJ _ H5 false hw hH HF l hU hV,Bool.or_eq_true];rcases Hg with rfl|rfl<;>[X il HG;X ir HG]
    rw[hN w hw _M hH h0e] at _3;cases _3
  ·obtain ⟨_,kuw,_,Sw,_,hSw,_,_N,_Z,h0f⟩ :=
    qB hm f i s hw _v hiw hkw _2 _s
   have _w:kz=kuw:=by
    have Hg:2*m+kz∈pa (d.gates[w]'hw):=_L.1;rcases h0f with h|h<;>(simp[pa,HF,h] at Hg;O)
   have _O:Su=Sw:=qM _0 hSw (k.symm.trans (_w▸_Z));have _W:=_N (2*m-2) (_O▸hh)
   have HR:(iw=2*m-2/\kw=2*m-3)\/(iw=2*m-4/\kw=2*m-2):=by
    rcases _2 with rfl|_<;>O
   rcases HR with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·exfalso
    obtain ⟨a,ha,hwa,hra⟩:=(pY f w hw).resolve_left (qz i ⟨2*m-2,2*m-3,_v,hiw,hkw,_2,_s⟩);obtain ⟨hL,Hu⟩:=qr hm f i s hw ha _v hiw hkw _2 _s hra;have Ha:a≠r0:=fun h=>by subst h;rw[hB] at hL;cases hL
    have HH:q1 m (p8 d a)/\p8 d a (pe (2*m-2):Fin (2*m)->Bool)=true:=by
     rcases Hu with ⟨h00,_⟩|⟨_,⟨Hs,_⟩|⟨_,Hs⟩⟩
     ·O
     ·X ⟨⟨{2*m-2-1,2*m-2},⟨2*m-2,by simp⟩,fun e he=>by simp at he;O,Hs⟩,
       by rw[cf Hs _,pg (fun e he=>by simp at he;O) W];simp⟩
     ·X ⟨⟨{2*m-2-2,2*m-2-1,2*m-2},⟨2*m-2,by simp⟩,fun e he=>by simp at he;O,Hs⟩,
       by rw[cf Hs _,pg (fun e he=>by simp at he;O) W];simp⟩
    have Hb:=(hG _ false a ha hL).trans HH.2;rw[hN a ha W Ha HH.1] at Hb;cases Hb
   ·Y ⟨_s,fun a ha hra=>?_⟩
    obtain ⟨hL,Hu⟩:=qr hm f i s hw ha _v hiw hkw _2 _s hra;have Ha:a≠r0:=fun h=>by subst h;rw[hB] at hL;cases hL
    rcases Hu with ⟨_,⟨_,h0g⟩|⟨_,Hs⟩⟩|⟨h00,_⟩
    ·Y ⟨hL,?_⟩;rwa[show 2*m-4+1=2*m-3 by O] at h0g
    ·exfalso
     have h01:q1 m (p8 d a):=⟨{2*m-4,2*m-4+1,2*m-4+2},⟨2*m-4,by simp⟩,fun e he=>by simp at he;O,Hs⟩
     have h0h:p8 d a (pe (2*m-2):Fin (2*m)->Bool)=true:=by
      rw[cf Hs _,pg (fun e he=>by simp at he;O) W];simp;O
     have Hb:=(hG _ false a ha hL).trans h0h;rw[hN a ha (by have:=hra.2;O) Ha h01] at Hb;cases Hb
    ·O
 obtain ⟨D,hD,_4,hQ,Ho,hR,n,Hh,Hv,z,Hc,HI⟩ :
   ∃D:J,∃(hD:D.size=d.size),D.output=d.output /\
    IsMinimalCircuit (2*m) D/\z0 D/\cF (2*m) D=pq (2*m) /\
    D.gates[r0]'(by change r0< D.size;rw[hD];X H5)=d.gates[r0]'H5 /\
    D.gates[kz]'(by change kz< D.size;rw[hD];X HY)=d.gates[kz]'HY /\
    (∀t (ht:t< d.size),
     D.gates[t]'(by change t< D.size;rw[hD];X ht)=d.gates[t]'ht \/
     D.gates[t]'(by change t< D.size;rw[hD];X ht)=⟨.or,[2*m-4,2*m-2]⟩) /\
    (∀x:Fin (2*m)->Bool,∀u< 2*m+d.size,(fun y=>p0 d y u)≠qd m (2*m-4) (2*m-2) ->
     p0 D x u=p0 d x u) /\
    (∀t (ht:t< D.size),pC (2*m) t (2*m+kz) (D.gates[t]'ht)->t=r0) /\
    (∀e,e+3<=2*m ->
     pl D (pe e:Fin (2*m)->Bool) r0 (p0 D (pe e:Fin (2*m)->Bool) d0) D.output=true):=by
  by_cases _P:∃w,∃(hw:w< d.size),w≠r0/\pC (2*m) w (2*m+kz) (d.gates[w]'hw)
  ·obtain ⟨w,hw,hH,_L⟩:=_P
   obtain ⟨_s,_5⟩:=H9 w hw hH _L;set D:=pU d w ⟨.or,[2*m-4,2*m-2]⟩;have hD:D.size=d.size:=pS d w _;have Hp:=Ht w hw _s _5;have Hi:=qz i ⟨2*m-4,2*m-2,by O,by O,by O,il W,_s⟩
   have hR:cF (2*m) D=pq (2*m):=funext fun x=>
    (Hp x d.output (pB hZ) Hi).trans (cf i x)
   have hQ:=qC f ⟨.or,[2*m-4,2*m-2]⟩ ⟨by simp,by simp⟩ (hR.trans i.symm)
   have Ho:z0 D:=zA s.1 w (by intro h;cases h)
   have _6:w≠kz:=by have:=_L.2;O
   have _7:d0≠2*m+w:=fun h=>by
    have h0i:pC (2*m) r0 (2*m+w) (d.gates[r0]'H5):=by
     rcases H7 with l|l<;>X ⟨by simp[pa,hB,l,h],h▸hI⟩
    have:=(_5 r0 H5 h0i).1;rw[hB] at this;cases this
   Y ⟨D,hD,rfl,hQ,Ho,hR,List.getElem_set_ne hH _,List.getElem_set_ne _6 _,
    fun t ht=>by
     by_cases _D:t=w
     ·subst _D;X ir (List.getElem_set_self _)
     ·X il (List.getElem_set_ne (Ne.symm _D) _),
    fun x u hu hne=>Hp x u hu (fun h=>hne (by rw[h];X _s)),
    fun t ht _t=>by
     have Hl:t< d.size:=by rw[←hD];X ht
     by_cases _D:t=w
     ·subst _D;have v:D.gates[t]'ht=⟨.or,[2*m-4,2*m-2]⟩:=List.getElem_set_self _
      rw[v] at _t;simp[pC,pa] at _t;O
     ·by_contra H6
      have v:D.gates[t]'ht=d.gates[t]'Hl:=List.getElem_set_ne (Ne.symm _D) _;X qy f Hl hw _D ((H9 t Hl H6 (v▸_t)).1.trans _s.symm),
    fun e he=>?_⟩
   have h02:p0 D (pe e:Fin (2*m)->Bool) d0=p0 d (pe e:Fin (2*m)->Bool) d0 :=
    Hp _ d0 W _7
   have HS:∀u< 2*m+d.size,u≠2*m+w ->
     pl D (pe e:Fin (2*m)->Bool) r0 (p0 D (pe e:Fin (2*m)->Bool) d0) u =
     pl d (pe e:Fin (2*m)->Bool) r0 (p0 d (pe e:Fin (2*m)->Bool) d0) u:=by
    intro u;induction u using Nat.strong_induction_on with
    | ind u ih=>
     intro hu hne;by_cases HT:u< 2*m+r0
     ·rw[pA D _ r0 (by rw[hD];X H5) _ u HT,pA d _ r0 H5 _ u HT];X Hp _ u hu hne
     ·by_cases hur:u=2*m+r0
      ·rw[hur,qs D _ r0 (by rw[hD];X H5) _,qs d _ r0 H5 _,h02]
      ·set t:=u-2*m;have ht:t< d.size :=W
       have htD:t< D.size:=by rw[hD];X ht
       have hW:u=2*m+t :=W;have _D:t≠w :=W;have H6:t≠r0 :=W;rw[hW];have v:D.gates[t]'htD=d.gates[t]'ht:=List.getElem_set_ne (Ne.symm _D) _;rcases pc f hZ t ht with ⟨hP,_,_,_⟩|⟨hC,x1,x2,l,hU,hV,_⟩
       ·X absurd hP (s.1 _ (List.getElem_mem ht))
       ·by_cases _t:pC (2*m) t (2*m+w) (d.gates[t]'ht)
        ·obtain ⟨Hw,h03⟩:=_5 t ht _t
         have h0c:2*m+w< 2*m+t:=_t.2
         have _8:pl D (pe e:Fin (2*m)->Bool) r0 (p0 D (pe e:Fin (2*m)->Bool) d0) (2*m+w) =
           p0 D (pe e:Fin (2*m)->Bool) (2*m+w):=by
          have hwD:w< D.size:=by rw[hD];X hw
          have hgw:D.gates[w]'hwD=⟨.or,[2*m-4,2*m-2]⟩:=List.getElem_set_self _;rw[zs D _ r0 (by rw[hD];X H5) _ w hwD hH,pj D _ w hwD,hgw]
          simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,
           show 2*m-4< 2*m+w by O,show 2*m-2< 2*m+w by O,↓reduceIte]
          rw[pA D _ r0 (by rw[hD];X H5) _ (2*m-4) W,
           pA D _ r0 (by rw[hD];X H5) _ (2*m-2) W]
         rw[hG _ _ t ht Hw,←Hp _ (2*m+t) W W]
         rcases h03 with h|h<;>rw[pF _ (by rw[hD];X H5) _ htD H6 (v.symm▸Hw) (v.symm▸h) W W,
          pm _ htD (v.symm▸Hw) (v.symm▸h) W W,_8,
          pA D _ r0 (by rw[hD];X H5) _ (2*m-3) W]
        ·have _9:x1≠2*m+w:=fun h=>_t ⟨by rcases hC with _E|_E<;>simp[pa,_E,l,h],h▸hU⟩
         have _a:x2≠2*m+w:=fun h=>_t ⟨by rcases hC with _E|_E<;>simp[pa,_E,l,h],h▸hV⟩
         rcases hC with hop_eq|hop_eq
         ·rw[pF _ (by rw[hD];X H5) _ htD H6 (v.symm▸hop_eq) (v.symm▸l) hU hV,
           pF _ H5 _ ht H6 hop_eq l hU hV,
           ih x1 W W _9,ih x2 W W _a]
         ·rw[pJ _ (by rw[hD];X H5) _ htD H6 (v.symm▸hop_eq) (v.symm▸l) hU hV,
           pJ _ H5 _ ht H6 hop_eq l hU hV,
           ih x1 W W _9,ih x2 W W _a]
   change pl D (pe e:Fin (2*m)->Bool) r0 (p0 D (pe e:Fin (2*m)->Bool) d0) d.output=true;rw[HS d.output (pB hZ) Hi];X _C e he
  ·push Not at _P
   X ⟨d,rfl,rfl,f,s.1,i,rfl,rfl,fun _ _=>il rfl,fun _ _ _ _=>rfl,
    fun t ht _t=>by_contra fun hne=>_P t ht hne _t,_C⟩
 have Hd:D.output≠2*m+kz:=fun HU=>by
  have h04:d.output=2*m+kz:=_4.symm.trans HU
  X qG f s.1 r0 H5 (2*m+kz) W
   (fun x hx=>by
    rw[←h04,←pb,i];X pT (by rw[←cf _Y x];X hx))
   (fun x hx=>by rw[i];X pT (by rw[←cf k x];X hx))
 have hM:r0< D.size:=by rw[hD];X H5
 have HV:kz< D.size:=by rw[hD];X HY
 have Hf:∃y1 y2:Fin (2*m)->Bool,cF (2*m) D y1≠cF (2*m) D y2:=by
  rw[hR];X ps W
 have hX:∀p,p< 2*m+r0->p≠2*m+kz ->
   (∀x:Fin (2*m)->Bool,p0 D x p=true->p0 D x (2*m+kz)=true) ->
   p0 D (pe (2*m-2):Fin (2*m)->Bool) p=true->False:=fun p hp h05 HJ Hx=>by
  set D':=pU D r0 ⟨.or,[p,d0]⟩;have hT:D'.size=D.size:=pS D r0 _;have _b:FanInTwo D':=z1 hQ.1 r0 ⟨by simp,by simp⟩
  have _c:z0 D':=zA Ho r0 (by intro h;cases h)
  have H0:∀x:Fin (2*m)->Bool,p0 D' x (2*m+r0)=(p0 D x p||p0 D x d0):=fun x=>by
   rw[qg D x hM];simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,hp,hI,↓reduceIte]
  have Hy:∀x:Fin (2*m)->Bool,∀u< 2*m+D.size,p0 D' x u=true->p0 D x u=true:=fun x u=>by
   induction u using Nat.strong_induction_on with
   | ind u ih=>
    intro hu h1;by_cases HT:u< 2*m+r0
    ·rwa[qc D x r0 _ u HT] at h1
    ·by_cases heq:u=2*m+r0
     ·subst heq;rw[H0 x,Bool.or_eq_true] at h1
      rcases H7 with l|l
      ·rw[p6 x hM (n.symm▸hB) (n.symm▸l) W hI,Bool.or_eq_true]
       rcases h1 with h|h<;>[X il (HJ x h);X ir h]
      ·rw[p6 x hM (n.symm▸hB) (n.symm▸l) hI W,Bool.or_eq_true]
       rcases h1 with h|h<;>[X ir (HJ x h);X il h]
     ·set t:=u-2*m;have ht:t< D.size :=W
      have Hl:t< D'.size:=by rw[hT];X ht
      have hW:u=2*m+t :=W;rw[hW] at h1 ⊢;have v:D'.gates[t]'Hl=D.gates[t]'ht:=List.getElem_set_ne (by O:r0≠t) _
      rcases pc hQ Hf t ht with ⟨hP,_,_,_⟩|⟨hC,x1,x2,l,hU,hV,_⟩
      ·X absurd hP (Ho _ (List.getElem_mem ht))
      ·rcases hC with hop_eq|hop_eq
       ·rw[pm x Hl (v.symm▸hop_eq) (v.symm▸l) hU hV,Bool.and_eq_true] at h1
        rw[pm x ht hop_eq l hU hV,Bool.and_eq_true];X ⟨ih x1 W W h1.1,ih x2 W W h1.2⟩
       ·rw[p6 x Hl (v.symm▸hop_eq) (v.symm▸l) hU hV,Bool.or_eq_true] at h1
        rw[p6 x ht hop_eq l hU hV,Bool.or_eq_true];rcases h1 with ha|hb<;>[X il (ih x1 W W ha);X ir (ih x2 W W hb)]
  have H1:∀e,e+1< 2*m->cF (2*m) D' (pe e)=true:=fun e he=>by
   by_cases _Q:e=2*m-2
   ·subst _Q
    have _d:p0 D' (pe (2*m-2):Fin (2*m)->Bool) (2*m+r0) =
      p0 D (pe (2*m-2):Fin (2*m)->Bool) (2*m+r0):=by
     rw[H0,Hx,Bool.true_or];rcases H7 with l|l
     ·rw[p6 _ hM (n.symm▸hB) (n.symm▸l) W hI,HJ _ Hx];R
     ·rw[p6 _ hM (n.symm▸hB) (n.symm▸l) hI W,HJ _ Hx,Bool.or_true]
    change p0 D' (pe (2*m-2):Fin (2*m)->Bool) D.output=true
    rw[qv D hM _ _ _d D.output (pB Hf),
     ← pb,hR,q0 he]
   ·have H2:∀u< 2*m+D.size,
      pl D (pe e:Fin (2*m)->Bool) r0 (p0 D (pe e:Fin (2*m)->Bool) d0) u=true ->
      p0 D' (pe e:Fin (2*m)->Bool) u=true:=by
     intro u;induction u using Nat.strong_induction_on with
     | ind u ih=>
      intro hu h1;by_cases HT:u< 2*m+r0
      ·rw[qc D _ r0 _ u HT];rwa[pA D _ r0 hM _ u HT] at h1
      ·by_cases heq:u=2*m+r0
       ·subst heq;rw[qs D _ r0 hM _] at h1;rw[H0,h1,Bool.or_true]
       ·set t:=u-2*m;have ht:t< D.size :=W
        have Hl:t< D'.size:=by rw[hT];X ht
        have hW:u=2*m+t :=W;rw[hW] at h1 ⊢;have v:D'.gates[t]'Hl=D.gates[t]'ht:=List.getElem_set_ne (by O:r0≠t) _
        rcases pc hQ Hf t ht with ⟨hP,_,_,_⟩|⟨hC,x1,x2,l,hU,hV,_⟩
        ·X absurd hP (Ho _ (List.getElem_mem ht))
        ·rcases hC with hop_eq|hop_eq
         ·rw[pF _ hM _ ht W hop_eq l hU hV,Bool.and_eq_true] at h1
          rw[pm _ Hl (v.symm▸hop_eq) (v.symm▸l) hU hV,Bool.and_eq_true];X ⟨ih x1 W W h1.1,ih x2 W W h1.2⟩
         ·rw[pJ _ hM _ ht W hop_eq l hU hV,Bool.or_eq_true] at h1
          rw[p6 _ Hl (v.symm▸hop_eq) (v.symm▸l) hU hV,Bool.or_eq_true];rcases h1 with ha|hb<;>[X il (ih x1 W W ha);X ir (ih x2 W W hb)]
    X H2 D.output (pB Hf) (HI e W)
  have Hz:cF (2*m) D'=cF (2*m) D:=funext fun x=>by
   rw[hR];apply Bool.eq_iff_iff.2;constructor
   ·intro h1;rw[←hR];X Hy x D.output (pB Hf) h1
   ·intro hpx;rw[px] at hpx;obtain ⟨a,b,hab,hxa,hxb⟩:=hpx
    X zz D' _b _c (fun j hj=>by
     simp only[pe,e2,decide_eq_true_eq] at hj;rcases hj with h|h
     ·have:j=a:=Fin.ext h;rw[this];X hxa
     ·have:j=b:=Fin.ext W;rw[this];X hxb) D.output (H1 a.val W)
  have HA:=qC hQ ⟨.or,[p,d0]⟩ ⟨by simp,by simp⟩ Hz
  rcases pY HA kz (by rw[hT];X HV) with HU|⟨r,hr,_,_u⟩
  ·X Hd HU
  ·have hrD:r< D.size:=by rw[←hT];X hr
   by_cases _e:r=r0
   ·subst _e;have v:D'.gates[r]'hr=⟨.or,[p,d0]⟩:=List.getElem_set_self _
    rw[v] at _u;simp[pC,pa] at _u;rcases _u.1 with h|h<;>[X h05 h.symm;X _1 h.symm]
   ·have v:D'.gates[r]'hr=D.gates[r]'hrD:=List.getElem_set_ne (Ne.symm _e) _
    X _e (Hc r hrD (v▸_u))
 rcases pc f hZ kz HY with ⟨hP,_,_,_⟩|⟨_x|HB,p1,p2,_f,hp1,hp2,_⟩
 ·X absurd hP (s.1 _ (List.getElem_mem HY))
 ·
  obtain ⟨_,a1,a2,h0q,ha1,ha2,_,_,_,_R⟩:=qn hm f i s HY _x
  have H3:(Su={2*m-3,2*m-2} /\
    ∃hJ,∃(_:hJ< d.size),hJ< kz /\
     (p8 d hJ=pP m (2*m-2)\/p8 d hJ=qd m (2*m-2) (2*m-3))) \/
    (Su={2*m-4,2*m-3,2*m-2} /\
    ∃hJ,∃(_:hJ< d.size),hJ< kz /\
     (p8 d hJ=pP m (2*m-2)\/p8 d hJ=qd m (2*m-2) (2*m-3))):=by
   have Hm:∀a,a< 2*m+kz->(fun y=>p0 d y a)=pP m (2*m-2) ->
     ∃g,∃(_:g< d.size),g< kz/\p8 d g=pP m (2*m-2):=fun a ha Hs=>by
    have hge:2*m<=a:=by_contra fun HT=>jr W W W
     (Hs.symm.trans (funext fun y=>p7 d y a W))
    X ⟨a-2*m,by O,by O,by change (fun y=>p0 d y (2*m+(a-2*m)))=_;rwa[show 2*m+(a-2*m)=a by O]⟩
   have H4:∀a,a< 2*m+kz->(fun y=>p0 d y a)=qd m (2*m-2) (2*m-3) ->
     ∃g,∃(_:g< d.size),g< kz/\p8 d g=qd m (2*m-2) (2*m-3):=fun a ha Hs=>by
    have hge:2*m<=a:=by_contra fun HT=>zw W W (ir W) W
     (Hs.symm.trans (funext fun y=>p7 d y a W))
    X ⟨a-2*m,by O,by O,by change (fun y=>p0 d y (2*m+(a-2*m)))=_;rwa[show 2*m+(a-2*m)=a by O]⟩
   rcases _R with
    ⟨e0,he0,HC,_⟩|⟨c,hc1,hc2,HC,Hq⟩|⟨i0,h06,h0j,HC,_⟩ |
    ⟨i0,h06,h0k,hi0,HC,Hq⟩|⟨i0,h06,h0l,HC,Hq⟩
   ·exfalso;have HW:=qM _0 (by simp[he0]) (k.symm.trans HC)
    have h1:2*m-2∈({e0}:Finset ℕ):=HW▸hh;have h2:e'∈({e0}:Finset ℕ):=HW▸_B;simp at h1 h2;O
   ·have HW:=qM _0 (fun e he=>by simp at he;O) (k.symm.trans HC)
    have h1:2*m-2∈({c-1,c}:Finset ℕ):=HW▸hh;simp at h1;have h07:c=2*m-2 :=W;subst h07;left;Y ⟨by rw[HW];ext e;simp;O,?_⟩
    rcases Hq with ⟨_,HZ⟩|⟨_,HZ⟩
    ·obtain ⟨g,hg,hF,hK⟩:=Hm a2 ha2 HZ;X ⟨g,hg,hF,il hK⟩
    ·obtain ⟨g,hg,hF,hK⟩:=Hm a1 ha1 HZ;X ⟨g,hg,hF,il hK⟩
   ·exfalso;have HW:=qM _0 (fun e he=>by simp at he;O) (k.symm.trans HC)
    have h1:2*m-2∈({i0,i0+1}:Finset ℕ):=HW▸hh;simp at h1;O
   ·have HW:=qM _0 (fun e he=>by simp at he;O) (k.symm.trans HC)
    have h1:2*m-2∈({i0-1,i0}:Finset ℕ):=HW▸hh;simp at h1;have _g:i0=2*m-2 :=W;subst _g;left;Y ⟨by rw[HW];ext e;simp;O,?_⟩
    rcases Hq with ⟨_,HD⟩|⟨_,HD⟩
    ·obtain ⟨g,hg,hF,hK⟩:=H4 a2 ha2 (by convert HD using 2);X ⟨g,hg,hF,ir hK⟩
    ·obtain ⟨g,hg,hF,hK⟩:=H4 a1 ha1 (by convert HD using 2);X ⟨g,hg,hF,ir hK⟩
   ·have HW:=qM _0 (fun e he=>by simp at he;O) (k.symm.trans HC)
    have h1:2*m-2∈({i0,i0+1,i0+2}:Finset ℕ):=HW▸hh;simp at h1;have _g:i0=2*m-4 :=W;subst _g;right;Y ⟨by rw[HW];ext e;simp;O,?_⟩
    rcases Hq with ⟨HZ,_⟩|⟨HZ,_⟩|⟨_,HD⟩|⟨_,HD⟩|⟨_,HD⟩|⟨_,HD⟩
    ·obtain ⟨g,hg,hF,hK⟩:=Hm a1 ha1 (by convert HZ using 2;O);X ⟨g,hg,hF,il hK⟩
    ·obtain ⟨g,hg,hF,hK⟩:=Hm a2 ha2 (by convert HZ using 2;O);X ⟨g,hg,hF,il hK⟩
    ·obtain ⟨g,hg,hF,hK⟩:=H4 a2 ha2 (by convert HD using 2<;>O);X ⟨g,hg,hF,ir hK⟩
    ·obtain ⟨g,hg,hF,hK⟩:=H4 a1 ha1 (by convert HD using 2<;>O);X ⟨g,hg,hF,ir hK⟩
    ·obtain ⟨g,hg,hF,hK⟩:=H4 a2 ha2 (by convert HD using 2<;>O);X ⟨g,hg,hF,ir hK⟩
    ·obtain ⟨g,hg,hF,hK⟩:=H4 a1 ha1 (by convert HD using 2<;>O);X ⟨g,hg,hF,ir hK⟩
  obtain ⟨hJ,_h,h0r,_i,_y⟩:∃hJ,∃(_:hJ< d.size),hJ< kz /\
    (p8 d hJ=pP m (2*m-2)\/p8 d hJ=qd m (2*m-2) (2*m-3)) /\
    (Su={2*m-3,2*m-2}\/Su={2*m-4,2*m-3,2*m-2}):=by
   rcases H3 with ⟨hS,g,hg,hF,hgc⟩|⟨hS,g,hg,hF,hgc⟩
   ·X ⟨g,hg,hF,hgc,il hS⟩
   ·X ⟨g,hg,hF,hgc,ir hS⟩
  by_cases HE:∃a2,∃(hY:a2< d.size),a2≠kz/\pC (2*m) a2 (2*m+hJ) (d.gates[a2]'hY)
  ·obtain ⟨a2,hY,_j,_S⟩:=HE
   have _k:(d.gates[a2]'hY).op=.and /\
     (p8 d a2=ph m {2*m-3,2*m-2}\/p8 d a2=ph m {2*m-4,2*m-3,2*m-2}):=by
    rcases _i with HZ|HD
    ·have hE:(d.gates[a2]'hY).op=.and:=by
      rcases pc f hZ a2 hY with ⟨hP,_,_,_⟩|⟨h|h,_,_,_,_,_,_⟩
      ·X absurd hP (s.1 _ (List.getElem_mem hY))
      ·X h
      ·X absurd h (zI hm f i s _h hY ⟨2*m-2,by O,by O,HZ⟩ _S)
     Y ⟨hE,?_⟩;obtain ⟨_,b1,b2,h08,_,_,_,_,_,h0m⟩:=qn hm f i s hY hE;have Hg:2*m+hJ∈pa (d.gates[a2]'hY):=_S.1;simp[pa,hE,h08] at Hg;have hA:(fun y=>p0 d y (2*m+hJ))=pP m (2*m-2):=HZ
     rcases h0m with
      ⟨_,_,_,⟨h1,h2⟩|⟨h1,h2⟩⟩|⟨c,hc1,hc2,HC,⟨h1,h2⟩|⟨h1,h2⟩⟩ |
      ⟨i0,_,h0j,_,⟨h1,h2⟩|⟨h1,h2⟩⟩|⟨i0,_,h0k,hi0,_,⟨h1,h2⟩|⟨h1,h2⟩⟩ |
      ⟨i0,_,h0l,HC,⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩⟩
     ·rcases Hg with h|h<;>O
     ·rcases Hg with h|h<;>O
     ·rcases Hg with h|h
      ·O
      ·have:c=2*m-2:=zg hc1 hc2 W W (h2.symm.trans (h▸hA))
       left;rw[HC,this];congr 1
     ·rcases Hg with h|h
      ·have:c=2*m-2:=zg hc1 hc2 W W (h2.symm.trans (h▸hA))
       left;rw[HC,this];congr 1
      ·O
     ·rcases Hg with h|h
      ·O
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
     ·rcases Hg with h|h
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
      ·O
     ·rcases Hg with h|h
      ·O
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
     ·rcases Hg with h|h
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
      ·O
     ·rcases Hg with h|h
      ·have:i0+2=2*m-2:=zg W W W W (h1.symm.trans (h▸hA))
       right;rw[HC];congr 1;ext e;simp;O
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
     ·rcases Hg with h|h
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
      ·have:i0+2=2*m-2:=zg W W W W (h1.symm.trans (h▸hA))
       right;rw[HC];congr 1;ext e;simp;O
     ·rcases Hg with h|h
      ·have:i0+1=2*m-2:=zg W W W W (h1.symm.trans (h▸hA));O
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
     ·rcases Hg with h|h
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
      ·have:i0+1=2*m-2:=zg W W W W (h1.symm.trans (h▸hA));O
     ·rcases Hg with h|h
      ·X absurd ((h▸hA).symm.trans h1) (qj W W W)
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
     ·rcases Hg with h|h
      ·X absurd ((h▸hA).symm.trans h2) (qj W W W)
      ·X absurd ((h▸hA).symm.trans h1) (qj W W W)
    ·obtain ⟨hE,_z⟩:=qr hm f i s _h hY W W W (ir W) HD _S
     Y ⟨hE,?_⟩;rcases _z with ⟨h00,_⟩|⟨_,⟨Hs,_⟩|⟨_,Hs⟩⟩
     ·O
     ·left;X Hs
     ·right;X Hs
   obtain ⟨hE,HK⟩:=_k;have HX:a2≠r0:=fun h=>by subst h;rw[hB] at hE;cases hE
   by_cases _T:kz< a2
   ·have Hr:q1 m (p8 d a2)/\p8 d a2 (pe (2*m-2):Fin (2*m)->Bool)=true:=by
     rcases HK with h|h
     ·X ⟨⟨{2*m-3,2*m-2},⟨2*m-2,by simp⟩,fun e he=>by simp at he;O,h⟩,
       by rw[cf h _,pg (fun e he=>by simp at he;O) W];simp⟩
     ·X ⟨⟨{2*m-4,2*m-3,2*m-2},⟨2*m-2,by simp⟩,fun e he=>by simp at he;O,h⟩,
       by rw[cf h _,pg (fun e he=>by simp at he;O) W];simp⟩
    have HL:=(hG _ false a2 hY hE).trans Hr.2;rw[hN a2 hY _T HX Hr.1] at HL;cases HL
   ·have h0n:a2< kz :=W
    rcases _y with h09|h0a<;>rcases HK with HM|_l
    ·X qy f hY HY _j (HM.trans (h09▸k).symm)
    ·X qG f s.1 kz HY (2*m+a2) W
      (fun x hx=>by
       rw[cf k x,h09,po] at hx;rw[show p0 d x (2*m+a2)=_ from cf _l x,po];obtain ⟨p,q,hp,hpq,hxp,hxq⟩:=hx;X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton] at hp ⊢;O,hpq,hxp,hxq⟩)
      (fun x hx=>by rw[i];X pT (by rw[←cf _l x];X hx))
    ·have Hj:(fun y=>p0 d y (2*m+a2))≠qd m (2*m-4) (2*m-2):=fun h=>
      qJ W (HM.symm.trans h)
     have hO:(fun y=>p0 d y (2*m+kz))≠qd m (2*m-4) (2*m-2):=fun h=>
      qJ W (k.symm.trans h)
     X hX (2*m+a2) W W (fun x hx=>by
      rw[z x (2*m+a2) W Hj,show p0 d x (2*m+a2)=_ from cf HM x,po] at hx;rw[z x (2*m+kz) W hO,show p0 d x (2*m+kz)=_ from cf k x,h0a,po];obtain ⟨p,q,hp,hpq,hxp,hxq⟩:=hx;X ⟨p,q,by simp only[Finset.mem_insert,Finset.mem_singleton] at hp ⊢;O,hpq,hxp,hxq⟩)
      (by
        rw[z _ (2*m+a2) W Hj,show p0 d _ (2*m+a2)=_ from cf HM _,
        pg (fun e he=>by simp at he;O) W];simp)
    ·X qy f hY HY _j (_l.trans (h0a▸k).symm)
  ·
   push Not at HE;set D':=pU D kz ⟨.and,[2*m-2,2*m-1]⟩;have hT:D'.size=D.size:=pS D kz _;have _b:FanInTwo D':=z1 hQ.1 kz ⟨by simp,by simp⟩
   have _c:z0 D':=zA Ho kz (by intro h;cases h)
   have hO:(fun y=>p0 d y (2*m+kz))≠qd m (2*m-4) (2*m-2):=fun h=>
    qJ W (k.symm.trans h)
   have Hk:∀x:Fin (2*m)->Bool,p0 D' x (2*m+kz)=ph m {2*m-2} x:=fun x=>by
    rw[qg D x HV,pv W]
    simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,
     show 2*m-2< 2*m+kz by O,show 2*m-1< 2*m+kz by O,↓reduceIte,
     p7 D x (2*m-2) W,p7 D x (2*m-1) W]
    have:(⟨2*m-2+1,by O⟩:Fin (2*m))=⟨2*m-1,by O⟩:=Fin.ext (by dsimp;O)
    rw[this]
   have Hy:∀x:Fin (2*m)->Bool,∀u< 2*m+D.size,p0 D' x u=true->p0 D x u=true:=fun x u=>by
    induction u using Nat.strong_induction_on with
    | ind u ih=>
     intro hu h1;by_cases HT:u< 2*m+kz
     ·rwa[qc D x kz _ u HT] at h1
     ·by_cases heq:u=2*m+kz
      ·subst heq;rw[Hk x,po] at h1
       rw[z x (2*m+kz) W hO,
        show p0 d x (2*m+kz)=_ from cf k x,po]
       obtain ⟨p,q,hp,hpq,hxp,hxq⟩:=h1;simp at hp;X ⟨p,q,hp▸hh,hpq,hxp,hxq⟩
      ·set t:=u-2*m;have ht:t< D.size :=W
       have Hl:t< D'.size:=by rw[hT];X ht
       have hW:u=2*m+t :=W;rw[hW] at h1 ⊢;have v:D'.gates[t]'Hl=D.gates[t]'ht:=List.getElem_set_ne (by O:kz≠t) _
       rcases pc hQ Hf t ht with ⟨hP,_,_,_⟩|⟨hC,x1,x2,l,hU,hV,_⟩
       ·X absurd hP (Ho _ (List.getElem_mem ht))
       ·rcases hC with hop_eq|hop_eq
        ·rw[pm x Hl (v.symm▸hop_eq) (v.symm▸l) hU hV,Bool.and_eq_true] at h1
         rw[pm x ht hop_eq l hU hV,Bool.and_eq_true];X ⟨ih x1 W W h1.1,ih x2 W W h1.2⟩
        ·rw[p6 x Hl (v.symm▸hop_eq) (v.symm▸l) hU hV,Bool.or_eq_true] at h1
         rw[p6 x ht hop_eq l hU hV,Bool.or_eq_true];rcases h1 with ha|hb<;>[X il (ih x1 W W ha);X ir (ih x2 W W hb)]
   have H1:∀e,e+1< 2*m->cF (2*m) D' (pe e)=true:=fun e he=>by
    by_cases _Q:e=2*m-2
    ·subst _Q
     have _d:p0 D' (pe (2*m-2):Fin (2*m)->Bool) (2*m+kz) =
       p0 D (pe (2*m-2):Fin (2*m)->Bool) (2*m+kz):=by
      rw[Hk,z _ (2*m+kz) W hO,
       show p0 d _ (2*m+kz)=_ from cf k _,
       (pg (by simp;O) W).2 (by simp),
       (pg _0 W).2 hh]
     change p0 D' (pe (2*m-2):Fin (2*m)->Bool) D.output=true
     rw[qv D HV _ _ _d D.output (pB Hf),
      ← pb,hR,q0 he]
    ·have H2:∀u< 2*m+D.size,u≠2*m+kz ->
       pl D (pe e:Fin (2*m)->Bool) r0 (p0 D (pe e:Fin (2*m)->Bool) d0) u=true ->
       p0 D' (pe e:Fin (2*m)->Bool) u=true:=by
      intro u;induction u using Nat.strong_induction_on with
      | ind u ih=>
       intro hu h0o h1;by_cases HT:u< 2*m+kz
       ·rw[qc D _ kz _ u HT];rwa[pA D _ r0 hM _ u W] at h1
       ·set t:=u-2*m;have ht:t< D.size :=W
        have Hl:t< D'.size:=by rw[hT];X ht
        have hW:u=2*m+t :=W;have h0p:t≠kz :=W;rw[hW] at h1 ⊢;have v:D'.gates[t]'Hl=D.gates[t]'ht:=List.getElem_set_ne h0p.symm _;by_cases H6:t=r0
        ·have _m:r0< D'.size:=by rw[hT];X hM
         have HN:D'.gates[r0]'_m=D.gates[r0]'hM:=List.getElem_set_ne (by O:kz≠r0) _
         rw[H6] at h1 ⊢;rw[qs D _ r0 hM _] at h1
         have _n:p0 D' (pe e:Fin (2*m)->Bool) d0=true :=
          ih d0 W W _1 (by rw[pA D _ r0 hM _ d0 hI];X h1)
         rcases H7 with l|l
         ·rw[p6 _ _m (HN.symm▸n.symm▸hB) (HN.symm▸n.symm▸l) W hI,_n,Bool.or_true]
         ·rw[p6 _ _m (HN.symm▸n.symm▸hB) (HN.symm▸n.symm▸l) hI W,_n];R
        ·rcases pc hQ Hf t ht with ⟨hP,_,_,_⟩|⟨hC,x1,x2,l,hU,hV,_⟩
         ·X absurd hP (Ho _ (List.getElem_mem ht))
         ·have HO:∀x0,(x0=x1\/x0=x2)->x0< 2*m+t->x0≠2*m+kz:=fun x0 hm' hx0 h=>
           H6 (Hc t ht ⟨by rcases hC with _E|_E<;>rcases hm' with rfl|rfl<;>simp[pa,_E,l,h],h▸hx0⟩)
          rcases hC with hop_eq|hop_eq
          ·rw[pF _ hM _ ht H6 hop_eq l hU hV,Bool.and_eq_true] at h1
           rw[pm _ Hl (v.symm▸hop_eq) (v.symm▸l) hU hV,Bool.and_eq_true]
           X ⟨ih x1 W W (HO x1 (il rfl) hU) h1.1,
            ih x2 W W (HO x2 (ir rfl) hV) h1.2⟩
          ·rw[pJ _ hM _ ht H6 hop_eq l hU hV,Bool.or_eq_true] at h1
           rw[p6 _ Hl (v.symm▸hop_eq) (v.symm▸l) hU hV,Bool.or_eq_true];rcases h1 with ha|hb
           ·X il (ih x1 W W (HO x1 (il rfl) hU) ha)
           ·X ir (ih x2 W W (HO x2 (ir rfl) hV) hb)
     X H2 D.output (pB Hf) Hd (HI e W)
   have Hz:cF (2*m) D'=cF (2*m) D:=funext fun x=>by
    rw[hR];apply Bool.eq_iff_iff.2;constructor
    ·intro h1;rw[←hR];X Hy x D.output (pB Hf) h1
    ·intro hpx;rw[px] at hpx;obtain ⟨a,b,hab,hxa,hxb⟩:=hpx
     X zz D' _b _c (fun j hj=>by
      simp only[pe,e2,decide_eq_true_eq] at hj;rcases hj with h|h
      ·have:j=a:=Fin.ext h;rw[this];X hxa
      ·have:j=b:=Fin.ext W;rw[this];X hxb) D.output (H1 a.val W)
   have HA:=qC hQ ⟨.and,[2*m-2,2*m-1]⟩ ⟨by simp,by simp⟩ Hz
   rcases pY HA hJ (by rw[hT,hD];X _h) with HU|⟨r,hr,_,_u⟩
   ·rcases _i with HZ|HD
    ·X jn i ⟨2*m-2,by O,by O,HZ⟩ (_4.symm.trans HU)
    ·X qz i ⟨2*m-2,2*m-3,by O,by O,by O,ir W,HD⟩ (_4.symm.trans HU)
   ·have hr':r< d.size:=by rw[←hD,←hT];X hr
    by_cases _U:r=kz
    ·subst _U;have v:D'.gates[r]'hr=⟨.and,[2*m-2,2*m-1]⟩:=List.getElem_set_self _
     rw[v] at _u;simp[pC,pa] at _u;O
    ·have hrD:r< D.size:=by rw[hD];X hr'
     have _F:D'.gates[r]'hr=D.gates[r]'hrD:=List.getElem_set_ne (Ne.symm _U) _;rcases Hv r hr' with _o|_o
     ·X HE r hr' _U (_o▸_F▸_u)
     ·have _V:D.gates[r]'hrD=⟨.or,[2*m-4,2*m-2]⟩:=_o
      rw[_F,_V] at _u;simp[pC,pa] at _u;O
 ·
  have HP:p0 d (pe (2*m-2):Fin (2*m)->Bool) (2*m+kz)=true:=by
   change p8 d kz _=true;rw[k];X (pg _0 W).2 hh
  rw[p6 _ HY HB _f hp1 hp2,Bool.or_eq_true] at HP;have _p:(D.gates[kz]'HV).op=.or:=Hh.symm▸HB;have _q:(D.gates[kz]'HV).inputs=[p1,p2]:=Hh.symm▸_f
  have _G:∀p,(p=p1\/p=p2)->p< 2*m+kz ->
    p0 d (pe (2*m-2):Fin (2*m)->Bool) p=true->False:=fun p h0b h0s _A=>by
   have _r:(fun y=>p0 d y p)≠qd m (2*m-4) (2*m-2):=fun h=>by
    have h1:p0 d (e1 (2*m-2):Fin (2*m)->Bool) (2*m+kz)=true:=by
     rw[p6 _ HY HB _f hp1 hp2,Bool.or_eq_true]
     have ht:p0 d (e1 (2*m-2):Fin (2*m)->Bool) p=true:=by
      rw[cf h _,(pN W W).2 rfl]
     rcases h0b with rfl|rfl<;>[X il ht;X ir ht]
    change p8 d kz _=true at h1;rw[k,pz] at h1;cases h1
   X hX p W W (fun x hx=>by
    rw[p6 x HV _p _q hp1 hp2,Bool.or_eq_true];rcases h0b with rfl|rfl<;>[X il hx;X ir hx])
    ((z _ p W _r).trans _A)
  rcases HP with h1|h2
  ·X _G p1 (il rfl) hp1 h1
  ·X _G p2 (ir rfl) hp2 h2
private lemma jI {m:ℕ} {C:J} (d:zB m C) (hw:d.w=2*m-1)
  {tu:ℕ} (j:tu< d.f4) (hu:d.u=2*m+2+tu)
  (g:(p5 C (2*m+1) true).fc.getD (2*m+2+tu) (.const false)=.wire (2*m+1+d.fv))
  {Su:Finset ℕ} (i:Su.Nonempty) (s:∀e∈Su,e+1< 2*m) (a:2*m-2∈Su)
  (c:p8 (p3 (p3 C (2*m+1) true) (2*m) false) d.fg=ph m Su) :
  Su={2*m-2}:=by
 by_cases z:m=1
 ·ext e;simp only[Finset.mem_singleton]
  X ⟨fun he=>by have:=s e he;O,fun h=>by rw[h];X a⟩
 have x:2<=m:=by have:=d.hm;O
 by_contra hne_sing
 obtain ⟨e',r,k⟩:∃e'∈Su,e'≠2*m-2:=by
  by_contra h;push Not at h;apply hne_sing;ext e;simp only[Finset.mem_singleton]
  X ⟨h e,fun he=>by rw[he];X a⟩
 obtain ⟨r0,y,l,f,hh,n,t,v,b,⟨e3,p,q⟩,
  d0,hd0_lt,hd0_ne,hr0_in,hclub,hd0_2m2_false,hmod_out_false⟩ :=
  jU d x hw j hu g i s a c
 X jO x d.f5 d.f8 d.f6 d.fA y l f
  i s a r k c n t v b p q
  hd0_lt hd0_ne hr0_in hclub hd0_2m2_false hmod_out_false
private lemma kf {m:ℕ} (hm:1<=m) {C:J}
  (Ht:IsMinimalCircuit (2*m+2) C) (hfun:cF (2*m+2) C=pq (2*m+2))
  {l w:ℕ} (n:l< C.size)
  (hG:∀t (ht:t< C.size),pC (2*m+2) t (2*m+1) (C.gates[t]'ht)↔t=l)
  (H8:(C.gates[l]'n).op=.or)
  (H9:w< 2*m+2+l) (Ha:w≠2*m+1)
  (Hb:(C.gates[l]'n).inputs=[2*m+1,w]\/(C.gates[l]'n).inputs=[w,2*m+1])
  (HV:∀D:J,IsMinimalCircuit (2*m) D->cF (2*m) D=pq (2*m)->qf m D) :
  qf (m+1) C:=by
 obtain ⟨d⟩:=kA hm Ht hfun n hG H8 H9 Ha Hb HV;have hw:d.w=2*m-1:=kp d;set HW:=p5 C (2*m+1) true;set Hu:=p3 C (2*m+1) true;set HN:=p5 Hu (2*m) false;set hX:=p3 Hu (2*m) false;have Hc:cF (2*m+2) C (e1 (2*m))=false:=by rw[d.fd];X pW _ _
 have H1:∀a,pC (2*m+2) d.f3 a (C.gates[d.f3]'d.f9)->¬zG C (2*m+1) a:=fun a hr=>by
  have HO:=hr.1
  rcases d.ft with i|i <;>
   (simp only[pa,d.fl,i,List.mem_cons,List.not_mem_nil,or_false] at HO;
    rcases HO with rfl|rfl;
    first|X pI (p9 C (2*m+1) true d.f0.1)|X d.fE;
    first|X pI (p9 C (2*m+1) true d.f0.1)|X d.fE)
 obtain ⟨k,z,_⟩:=qW d.f0 d.fJ W d.fn Hc
  d.f9 d.fa d.fP d.fi d.fj d.fe d.fh H1 d.fm d.fy d.fu d.fp
 have f:p8 C d.f3=pP (m+1) (2*m):=by
  funext x;change p0 C x (2*(m+1)+d.f3)=_
  rw[qe W W];have h1:=p7 C x (2*m+1) W;have h2:=p7 C x (2*m-1) W;rcases d.ft with i|i
  ·rw[p6 x d.f9 d.fl (hw▸i) W W,h1,h2,Bool.or_comm]
  ·rw[p6 x d.f9 d.fl (hw▸i) W W,h1,h2]
 have q:∀x:Fin (2*m+2)->Bool,p8 C d.f4 x =
   (pP (m+1) (2*m) x&&p0 C x d.u):=fun x=>by
  change p0 C x (2*m+2+d.f4)=_;have _a:=d.fP;rcases d.fy with i|i
  ·rw[pm x d.fa d.fm i W d.fu,
    show p0 C x (2*m+2+d.f3)=_ from cf f x]
  ·rw[pm x d.fa d.fm i d.fu W,
    show p0 C x (2*m+2+d.f3)=_ from cf f x,Bool.and_comm]
 have r:q1 (m+1) (p8 C d.f4) /\
   ∀t (ht:t< C.size),t< d.f4->zG C (2*m+1) (2*m+2+t) ->
    qb (m+1) (p8 C t):=by
  by_cases Hv:d.u=2*m
  ·Y ⟨⟨{2*m-1,2*m},⟨2*m,by simp⟩,fun e he=>by simp at he;O,funext fun x=>?_⟩,
    fun t ht H2 hF=>by have:=z t ht H2 hF;O⟩
   rw[q x,Hv,p7 C x (2*m) W,qe W W,
    zu,pv W,pv W]
   have Hw:(⟨2*m-1+1,by O⟩:Fin (2*m+2))=⟨2*m,by O⟩:=Fin.ext (by dsimp;O)
   rw[Hw];cases x ⟨2*m-1,by O⟩<;>cases x ⟨2*m,by O⟩<;>cases x ⟨2*m+1,by O⟩<;>rfl
  ·have HP:2*m+2<=d.u:=by_contra fun H2=>by
    by_cases HX:d.u=2*m+1
    ·X pI (p9 C (2*m+1) true d.f0.1) (HX▸d.fH)
    ·obtain ⟨wu,HQ,Hd⟩:=d.fH
     rw[pd C (2*m+1) true d.u W] at HQ;cases HQ;rw[p7 Hu _ d.u W] at Hd;simp[e1] at Hd;O
   set tu:=d.u-(2*m+2);have y:tu< d.f4:=by have:=d.fu;O
   have Hx:tu< C.size:=by have:=d.fa;O
   have He:tu≠d.f3:=by have:=d.fU;O
   have hh:d.u=2*m+2+tu :=W;obtain ⟨p,Su,Hf,HY,hY,hA⟩:=jN d hw y hh;have hH:=jI d hw y hh p Hf HY hY hA;obtain ⟨Hy,Hg,_,_,hB,s,_,hI⟩:=z2 d Hx y He (hh▸d.fH);rw[p] at hB;injection hB with hkq;have Hz:Hy=d.fv :=W;rw[Hz,d.fx] at s;injection s with hkz;have HA:Hg=d.fg :=W
   have hJ:p8 C tu=qd (m+1) (2*m-2) (2*m):=funext fun x=>by
    rw[hI x,HA,cf hA _,hH,js (by simp;O),
     qh W W,pv W,Bool.or_comm]
   have v:∀t (ht:t< C.size),t< d.f4->zG C (2*m+1) (2*m+2+t)->t=tu:=fun t ht H2 hF=>by
    have _b:=z t ht H2 hF;by_contra hne;have hK:t< tu :=W;have H6:t≠d.f3:=fun h=>by subst h;X pI d.fh hF
    have b:=pE d.f0.1 d.fe ht H6 W;have hD:=pE d.f0.1 d.fe Hx He W;obtain ⟨hL,hC,_,g,_,_,_⟩:=p4 d.f0.1 ht b
    have Hh:hL< d.fv :=
     zm d.f0.1 ht Hx hK b hD g p
    have Hi:p0 (p3 C (2*m+1) true) (e1 (2*m):Fin (2*m+1)->Bool) (2*m+1+hL)=true :=
     (pM g).1 hF
    rw[jV d.fD d.f7 d.fq d.fB d.fk (2*m+1+hL) W W] at Hi;cases Hi
   Y ⟨⟨{2*m-2,2*m-1,2*m},⟨2*m,by simp⟩,fun e he=>by simp at he;O,funext fun x=>?_⟩,
    fun t ht H2 hF=>⟨2*m-2,2*m,by O,by O,by O,il W,(v t ht H2 hF)▸hJ⟩⟩
   rw[q x,hh,show p0 C x (2*m+2+tu)=_ from cf hJ x,
    qe W W,qh W W,
    jb,pv W,pv W,pv W]
   have HZ:(⟨2*m-2+1,by O⟩:Fin (2*m+2))=⟨2*m-1,by O⟩:=Fin.ext (by dsimp;O)
   have _0:(⟨2*m-1+1,by O⟩:Fin (2*m+2))=⟨2*m,by O⟩:=Fin.ext (by dsimp;O)
   rw[HZ,_0];cases x ⟨2*m-2,by O⟩<;>cases x ⟨2*m-1,by O⟩<;>cases x ⟨2*m,by O⟩<;>cases x ⟨2*m+1,by O⟩<;>rfl
 have hE:∀t (ht:t< C.size),
   (zG C (2*m+1) (2*m+2+t)/\d.f4<=t->q1 (m+1) (p8 C t)) /\
   (q1 (m+1) (p8 C t)\/zM (m+1) (p8 C t)\/qb (m+1) (p8 C t)):=by
  intro t;induction t using Nat.strong_induction_on with
  | ind t ih=>
   intro ht;by_cases H6:t=d.f3
   ·Y ⟨fun h=>absurd (H6▸h.1) (pI d.fh),ir (il ⟨2*m,by O,by O,H6▸f⟩)⟩
   ·by_cases hF:zG C (2*m+1) (2*m+2+t)
    ·by_cases _1:t< d.f4
     ·X ⟨fun h=>by O,ir (ir (r.2 t ht _1 hF))⟩
     ·by_cases HB:t=d.f4
      ·have HR:=HB▸r.1;X ⟨fun _=>HR,il HR⟩
      ·have _2:d.f4< t :=W
       have b:=pE d.f0.1 d.fe ht H6 W;obtain ⟨hL,hC,_,g,H3,_,_⟩:=p4 d.f0.1 ht b;have hM:=(pM g).1 hF;have hN:(C.gates[t]'ht).op=.or:=H3.symm.trans (d.fk hL hC hM);rcases pc d.f0 d.fn t ht with ⟨Hj,_,_,_⟩|⟨_,a1,a2,i,HS,HT,_⟩
       ·rw[hN] at Hj;cases Hj
       ·have hO:∀a,(a=a1\/a=a2)->a< 2*m+2+t->q1 (m+1) (fun x=>p0 C x a):=fun a _3 HC=>by
         have Hq:pC (2*m+2) t a (C.gates[t]'ht):=⟨by rcases _3 with rfl|rfl<;>simp[pa,hN,i],HC⟩
         by_cases HD:zG C (2*m+1) a
         ·have HU:2*m+2+d.f4<=a:=by_contra fun H2=>k t ht _2 a Hq W HD
          set ta:=a-(2*m+2);have H0:a=2*m+2+ta :=W;rw[H0];X (ih ta W W).1 ⟨H0▸HD,by O⟩
         ·obtain ⟨_c,HE,_,hP,Hk,H4,_,_4⟩ :=
           qR d a W (fun h=>H6 ((d.fi t ht).1 (h▸Hq)))
            (fun h=>by have:=(d.fj t ht).1 (h▸Hq);O) HD
          have hR:=pp d.f0 d.fJ d.fn ht b hC g Hq Hk;have hT:=zQ d hC hM hR H4
          rcases qE d.f6 HE hP with
           ⟨j,hj,_,H5⟩|⟨_,_,_,Q,HF,hQ,H5⟩|⟨_,_,_,c,Hr,HG,H5⟩|⟨_,_,_,_,k0,_,_,Hs,_,H5⟩
          ·have hp:=hT (e1 j) (by rw[cf H5 _];simp[e1]);rw[pW] at hp;cases hp
          ·X ⟨Q,HF,fun e he=>by have:=hQ e he;O,
            funext fun x=>(_4 x).trans ((cf H5 (qq x)).trans (js hQ x))⟩
          ·have hp:=hT (e1 (c-1)) (by rw[cf H5 _];X (pu Hr HG W).2 (il W))
           rw[pW] at hp;cases hp
          ·have hp:=hT (e1 k0) (by rw[cf H5 _];X (pN Hs Hs).2 rfl)
           rw[pW] at hp;cases hp
        obtain ⟨S1,Hl,_5,HH⟩:=hO a1 (il rfl) HS;obtain ⟨S2,_,_6,HI⟩:=hO a2 (ir rfl) HT
        have Hm:q1 (m+1) (p8 C t):=⟨S1∪S2,Hl.mono Finset.subset_union_left,
         fun e he=>by rcases Finset.mem_union.1 he with h|h<;>[X _5 e h;X _6 e h],
         funext fun x=>by
          change p0 C x (2*(m+1)+t)=_;rw[p6 x ht hN i HS HT,cf HH x,cf HI x,qZ]⟩
        X ⟨fun _=>Hm,il Hm⟩
    ·Y ⟨fun h=>absurd h.1 hF,?_⟩
     obtain ⟨_,hZ,_,hU,_,_,_7,HJ⟩ :=
      qR d (2*m+2+t) W W W hF
     have Hn:2*m<=hZ:=_7 W;have H7:hZ< 2*m+hX.size:=hU;set hV:=hZ-2*m;have Ho:hV< hX.size :=W;have hW:hZ=2*m+hV :=W
     have HK:∀x:Fin (2*m+2)->Bool,p8 C t x=p8 hX hV (qq x):=fun x=>by
      change p0 C x (2*m+2+t)=p0 hX (qq x) (2*m+hV);rw[HJ x,hW]
     rcases d.f6.2 hV Ho with ⟨S,HL,hS,Hp⟩|⟨c,Hr,HG,Hp⟩|⟨i0,k0,HM,_8,Hs,_9,Hp⟩
     ·X il ⟨S,HL,fun e he=>by have:=hS e he;O,funext fun x=>(HK x).trans ((cf Hp _).trans (js hS x))⟩
     ·X ir (il ⟨c,Hr,by O,funext fun x=>(HK x).trans ((cf Hp _).trans (kD Hr HG x))⟩)
     ·X ir (ir ⟨i0,k0,HM,by O,by O,_9,funext fun x=>(HK x).trans ((cf Hp _).trans (kF _8 Hs x))⟩)
 X ⟨d.fJ,fun t ht=>(hE t ht).2⟩
private lemma jB {m:ℕ} (hm:1<=m) {C:J}
  (q:IsMinimalCircuit (2*(m+1)) C) (hfun:cF (2*(m+1)) C=pq (2*(m+1)))
  (hD:∀D:J,IsMinimalCircuit (2*m) D->cF (2*m) D=pq (2*m)->qf m D) :
  qf (m+1) C:=by
 have e:IsMinimalCircuit (2*m+2) C:=q;have c:cF (2*m+2) C=pq (2*m+2):=hfun;have hE:C.size=3*m+1:=by have:=zr (m:=m+1) W e c;O
 have a:∀y:Fin (2*m+1)->Bool,cF (2*m+2) C (Fin.snoc y false)=pq (2*m+1) y:=fun y=>by
  rw[c,z8]
 have b:∀y:Fin (2*m+1)->Bool,
   cF (2*m+2) C (Fin.snoc y true)=(y (Fin.last (2*m))||pq (2*m) (Fin.init y)):=fun y=>by
  rw[c,qT (2*m+1) W y];R
 have r:∃y:Fin (2*m+1)->Bool,cF (2*m+2) C (Fin.snoc y false)≠cF (2*m+2) C (Fin.snoc y true) :=
  ⟨e1 (2*m),by rw[a,b,pW];simp[e1]⟩
 have s:∃y1 y2:Fin (2*m+1)->Bool,cF (2*m+2) C (Fin.snoc y1 false)≠cF (2*m+2) C (Fin.snoc y2 false):=by
  obtain ⟨y1,y2,hF⟩:=ps (n:=2*m+1) W;X ⟨y1,y2,by rw[a,a];X hF⟩
 have t:∃y1 y2:Fin (2*m+1)->Bool,cF (2*m+2) C (Fin.snoc y1 true)≠cF (2*m+2) C (Fin.snoc y2 true):=by
  Y ⟨e0,e1 (2*m),?_⟩;rw[b,b];have h0:(e0:Fin (2*m+1)->Bool) (Fin.last (2*m))=false:=rfl;have h1:(e1 (2*m):Fin (2*m+1)->Bool) (Fin.last (2*m))=true:=by simp[e1]
  have hG:Fin.init (e0:Fin (2*m+1)->Bool)=e0:=rfl;rw[h0,h1,hG,zq];simp
 have u:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m+1)->Bool,cF (2*m+1) D y=cF (2*m+2) C (Fin.snoc y false)) ->
   C.size<=D.size+2:=fun D k v=>by
  have x:=q9 (2*m+1) W D k (funext fun y=>(v y).trans (a y));have z:(2*m+1)%2≠0 :=W;have hh:(2*m+1)/2=m :=W;simp only[z,↓reduceIte,hh] at x;O
 have hA:∀D:J,FanInTwo D ->
   (∀y:Fin (2*m+1)->Bool,cF (2*m+1) D y=cF (2*m+2) C (Fin.snoc y true)) ->
   C.size<=D.size+2:=fun D k v=>by
  have hH:=zl (pq (2*m)) (ps W) (fun _ _ _ _ h=>h) (3*m-2)
   (fun E hB hI=>by
    have h:=q9 (2*m) W E hB hI;simp only[Nat.mul_mod_right,↓reduceIte,Nat.mul_div_cancel_left m (by O:0< 2)] at h;X h)
   D k (fun y=>(v y).trans (b y))
  O
 obtain ⟨hC,f,d,l|p,w,g,i,j⟩ :=
  jJ (n:=2*m+1) e r s t u hA
 ·X k9 hm e c f d l g i j
 ·X kf hm e c f d p g i j hD
private lemma k4 {m:ℕ} (hm:1<=m) {C:J}
  (a:IsMinimalCircuit (2*m) C) (hfun:cF (2*m) C=pq (2*m)) :
  qf m C:=by
 induction m generalizing C with
 | zero=>O
 | succ k ih=>
  cases k with
  | zero=>X jA a hfun
  | succ k'=>X jB W a hfun (fun D b c=>ih W b c)

end PEqualNP.Outside.Meta172

theorem PEqualNP.Outside.L_meta_172 :
    ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), 1 ≤ m →
      PEqualNP.MetaComplexity.IsMinimalCircuit (2 * m) C →
      PEqualNP.MetaComplexity.circuitFun (2 * m) C =
        (fun x : Fin (2 * m) → Bool =>
          decide (∃ i j : Fin (2 * m), i.val + 1 = j.val ∧ x i = true ∧ x j = true)) →
      (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      ∀ t : ℕ, t < C.size →
        ((∃ S : Finset ℕ, S.Nonempty ∧ (∀ i ∈ S, i + 1 < 2 * m) ∧
            ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + t) false =
              decide (∃ i j : Fin (2 * m), i.val ∈ S ∧ i.val + 1 = j.val ∧ x i = true ∧ x j = true)) ∨
         (∃ c : Fin (2 * m), 1 ≤ c.val ∧ c.val + 1 < 2 * m ∧
            ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + t) false =
              decide (∃ k : Fin (2 * m), (k.val + 1 = c.val ∨ k.val = c.val + 1) ∧ x k = true)) ∨
         (∃ i j k : Fin (2 * m), i.val % 2 = 0 ∧ i.val + 1 = j.val ∧ (k.val = j.val + 1 ∨ k.val + 1 = i.val) ∧
            ∀ x : Fin (2 * m) → Bool, (C.wires (List.ofFn x)).getD (2 * m + t) false = ((x i && x j) || x k))) := by
  intro m C hm hmin hfun
  have hinv := PEqualNP.Outside.Meta172.k4 hm hmin hfun
  refine ⟨hinv.1, fun t ht => ?_⟩
  rcases hinv.2 t ht with ⟨S, hSne, hS, htf⟩ | ⟨c, hc1, hc2, htf⟩ | ⟨i, k, hie, hi, hk, hrel, htf⟩
  · exact Or.inl ⟨S, hSne, hS, fun x => congrFun htf x⟩
  · exact Or.inr (Or.inl ⟨⟨c, by omega⟩, hc1, hc2, fun x => congrFun htf x⟩)
  · refine Or.inr (Or.inr ⟨⟨i, by omega⟩, ⟨i + 1, hi⟩, ⟨k, hk⟩, hie, rfl, hrel, fun x => ?_⟩)
    exact (congrFun htf x).trans (PEqualNP.Outside.Meta172.qh hi hk x)
