import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8457_aux
abbrev Q:=Bool
abbrev K:=Nat×Nat
abbrev J:=List K
abbrev V:=List (Nat×Nat×Nat×Nat)
abbrev Y:=List (Nat×Nat×Nat×Nat×Nat×Nat)
abbrev M:=List Nat
abbrev I:=List Q
abbrev F (n:Nat):=Fin n->Q
open Nat (land lor xor shiftRight shiftLeft beq ble blt)
lemma bFT:(false=true)=False:=Bool.false_eq_true
lemma bTA {b:Q}:(true&&b)=b:=Bool.true_and b
lemma bOT {a b:Q}:((a||b)=true)=(a=true\/b=true):=Bool.or_eq_true a b
lemma bAT {a b:Q}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma bNF:(!false)=true:=Bool.not_false
lemma bNT {b:Q}:((!b)=true)=(b=false):=Bool.not_eq_true' b
lemma lAA {α:Type _} (l1 l2 l3:List α):(l1++l2)++l3=l1++(l2++l3):=List.append_assoc l1 l2 l3
lemma lMC {α β:Type _} {f : α->β} {a : α} {l:List α}:(a::l).map f=f a::l.map f:=List.map_cons
lemma lMM {α:Type _} {a b : α} {l:List α}:a∈b::l↔a=b\/a∈l:=List.mem_cons
lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma lRC {α:Type _} {a : α} {l:List α}:(a::l).reverse=l.reverse++[a]:=List.reverse_cons
lemma lFC {α β:Type _} {f : α->β->β} {b : β} {a : α} {l:List α}:(a::l).foldr f b=f a (l.foldr f b):=List.foldr_cons
lemma lAL {α:Type _} {p : α->Q} {l:List α}:l.all p=true↔∀ x∈l,p x=true:=List.all_eq_true
lemma lAN {α:Type _} {p : α->Q} {l:List α}:l.any p=true↔∃ x∈l,p x=true:=List.any_eq_true
lemma nTB {n i:Nat}:(2 ^ n - 1).testBit i=decide (i < n):=by simp [Nat.testBit_two_pow_sub_one]
lemma nEQ {x y:Nat} (h:∀ i,x.testBit i=y.testBit i):x=y:=Nat.eq_of_testBit_eq h
lemma nTO {x y i:Nat}:(x|||y).testBit i=(x.testBit i||y.testBit i):=by simp [Nat.testBit_or]
lemma nTA {x y i:Nat}:(x&&&y).testBit i=(x.testBit i&&y.testBit i):=by simp [Nat.testBit_and]
lemma nTX {x y i:Nat}:(x^^^y).testBit i=(x.testBit i ^^ y.testBit i):=by simp [Nat.testBit_xor]
lemma nTS {x k i:Nat}:(x >>> k).testBit i=x.testBit (k+i):=by simp [Nat.testBit_shiftRight]
lemma nLO {x y:Nat}:Nat.lor x y=x|||y:=Nat.lor_eq
lemma nLA {x y:Nat}:Nat.land x y=x&&&y:=Nat.land_eq
lemma nXO {x y:Nat}:Nat.xor x y=x^^^y:=Nat.xor_eq
lemma nZT {i:Nat}:(0:Nat).testBit i=false:=Nat.zero_testBit i
lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma lMA {α β:Type _} {f : α->β} {l1 l2:List α}:(l1++l2).map f=l1.map f++l2.map f:=List.map_append
lemma lLM {α β:Type _} (f : α->β) {l:List α}:(l.map f).length=l.length:=List.length_map f
lemma lRR {α:Type _} {l:List α}:l.reverse.reverse=l:=List.reverse_reverse l
lemma lANil {α:Type _} {l:List α}:l++[]=l:=List.append_nil l
lemma lSA {α:Type _} {a : α} {l:List α}:[a]++l=a::l:=List.singleton_append
lemma lCA {α:Type _} {a : α} {l1 l2:List α}:(a::l1)++l2=a::(l1++l2):=List.cons_append
lemma lPM {α:Type _} {a : α} {l₁ l₂:List α}:(l₁++a::l₂).Perm (a::(l₁++l₂)):=List.perm_middle
lemma nAC (a b:Nat):a+b=b+a:=Nat.add_comm a b
lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma nAZ {a:Nat}:a+0=a:=Nat.add_zero a
lemma nZL (a:Nat):0<=a:=Nat.zero_le a
lemma bOS {a:Q}:(a||a)=a:=Bool.or_self a
lemma bOTR {a:Q}:(a||true)=true:=Bool.or_true a
lemma bTOR {a:Q}:(true||a)=true:=Bool.true_or a
lemma bATR {a:Q}:(a&&true)=a:=Bool.and_true a
lemma bBT {a:Q}:(a ^^ true)=!a:=Bool.bne_true a
lemma dTR {p:Prop} [Decidable p] (h:p):decide p=true:=decide_eq_true h
lemma n2P (n:Nat):0 < 2 ^ n:=Nat.two_pow_pos n
lemma lMp {α β:Type _} {f : α->β} {b : β} {l:List α}:b∈l.map f↔∃ a∈l,f a=b:=List.mem_map
lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma fCD {α β γ:Type _} (f : β->γ) (g : α->β):f ∘ g=fun x=>f (g x):=Function.comp_def f g
lemma lPR {α:Type _} (l:List α):l.Perm l:=List.Perm.refl l
lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
lemma lPC {α:Type _} (x : α) {l1 l2:List α} (h:l1.Perm l2):(x::l1).Perm (x::l2):=List.Perm.cons x h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev G:=Gate
abbrev U:=List G
open Sum
open Function (update)
open List (ofFn range finRange)
abbrev HCS:=HasCircuitSize
lemma lMCM {α:Type _} {a:α} (b:α) {l:List α} (h:a∈l):a∈b::l:=List.mem_cons_of_mem b h
lemma lMN {α β:Type _} {f:α->β}:([] :List α).map f=[]:=List.map_nil
lemma lNA {α:Type _} {l:List α}:[]++l=l:=List.nil_append l
lemma nBE {a b:Nat}:(ble a b=true)=(a<=b):=Nat.ble_eq
lemma nBL {a b:Nat}:(blt a b=true)=(a < b):=Nat.blt_eq
lemma nBQ {a b:Nat}:(beq a b=true)=(a=b):=Nat.beq_eq
lemma nBR {a:Nat}:beq a a=true:=Nat.beq_refl a
lemma bOF {a b:Q}:((a||b)=false)↔(a=false/\b=false):=Bool.or_eq_false_iff
lemma bAF {a b:Q}:((a&&b)=false)↔(a=false\/b=false):=Bool.and_eq_false_iff
lemma nTD {n i:Nat}:n.testBit i=decide (n / 2 ^ i % 2=1):=Nat.testBit_eq_decide_div_mod_eq
lemma nT2 {i j:Nat}:(2 ^ i).testBit j=decide (i=j):=Nat.testBit_two_pow
lemma nT2S {i:Nat}:(2 ^ i).testBit i=true:=Nat.testBit_two_pow_self
lemma nTFL {x i:Nat} (h:x < 2 ^ i):x.testBit i=false:=Nat.testBit_eq_false_of_lt h
lemma nPLR {a b c:Nat} (h:0 < a) (hbc:b<=c):a ^ b<=a ^ c:=Nat.pow_le_pow_right h hbc
lemma nLPT {x n:Nat} (h:∀ i ≥ n,x.testBit i=false):x < 2 ^ n:=Nat.lt_pow_two_of_testBit x h
lemma nAE {a b:Nat}:Nat.add a b=a+b:=Nat.add_eq
lemma nSE {a b:Nat}:Nat.sub a b=a - b:=Nat.sub_eq
lemma lNMN {α:Type _} {a:α}:¬a∈([] :List α):=List.not_mem_nil
lemma lMAp {α:Type _} {a:α} {l1 l2:List α}:a∈l1++l2↔a∈l1\/a∈l2:=List.mem_append
lemma lMOF {α:Type _} {n:Nat} {f:Fin n->α} {a:α}:a∈List.ofFn f↔∃ i,f i=a:=List.mem_ofFn
lemma lMRG {n i:Nat}:i∈List.range n↔i < n:=List.mem_range
lemma lMFR {n:Nat} (i:Fin n):i∈List.finRange n:=List.mem_finRange i
lemma lLO {α:Type _} {n:Nat} {f:Fin n->α}:(List.ofFn f).length=n:=List.length_ofFn
lemma lLR {n:Nat}:(List.range n).length=n:=List.length_range
lemma lMI {α:Type _} (l:List α):l.map id=l:=List.map_id l
lemma lMCL {α β:Type _} {f g:α->β} {l:List α} (h:∀ a∈l,f a=g a):l.map f=l.map g:=List.map_congr_left h
lemma lGES {α:Type _} {l:List α} {i:Nat} {a:α}:l[i]?=some a↔∃ h:i < l.length,l[i]=a:=List.getElem?_eq_some_iff
lemma lGEQ {α:Type _} {l:List α} {i:Nat} (h:i < l.length):l[i]?=some l[i]:=List.getElem?_eq_getElem h
lemma lGDE {α:Type _} (l:List α) (d:α) {i:Nat} (h:i < l.length):l.getD i d=l[i]:=List.getD_eq_getElem l d h
lemma lLT {α:Type _} {i:Nat} {l:List α}:(l.take i).length=min i l.length:=List.length_take
lemma lLN {α:Type _}:([] :List α).length=0:=List.length_nil
abbrev u7 (n:Nat):=(Fin n->Bool)->Bool
def q3 (gs:U) (w:I):I:=
 gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
lemma zd (gs gs':U) (w:I) :q3 (gs++gs') w=q3 gs' (q3 gs w):=by simp [q3,List.foldl_append]
lemma y1 (gs:U):∀ w:I, ∃ t:I,q3 gs w=w++t/\t.length=gs.length:=by
 induction gs with
 | nil=>intro w;exact ⟨[],by simp [q3],rfl⟩
 | cons g gs ih =>
  intro w;obtain ⟨t,b,c⟩:=ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
  refine ⟨g.op.eval (g.inputs.map fun i=>w.getD i false)::t,?_,by simp [c]⟩
  have:q3 (g::gs) w
   = q3 gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
  rw [this,b];simp
lemma qu (gs:U) (w:I) :(q3 gs w).length=w.length+gs.length:=by obtain ⟨t,b,c⟩:=y1 gs w;rw [b];simp [c]
lemma ve (gs:U) (w:I) (i:Nat) (h:i < w.length) :(q3 gs w).getD i false=w.getD i false:=by obtain ⟨t,b,_⟩:=y1 gs w;rw [b,List.getD_append _ _ _ _ h]
def Ok (g:G):Prop:=
 g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
lemma q8 {α:Type} (L:List α) (S d : α) (j:Nat) (h:j≠L.length) :(L++[S]).getD j d=L.getD j d:=by
 by_cases b:j < L.length
 . exact List.getD_append _ _ _ _ b
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]
lemma z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by simp
lemma z2 {α:Type} (L:List α) (S d : α) (k:Nat) (h:L.length=k) :(L++[S]).getD k d=S:=by subst h;simp
def yb {n:Nat} (L:List (Finset (Fin n))) (g:G):Finset (Fin n):=
 (g.inputs.map fun a=>L.getD a ∅).foldr (· ∪ ·) ∅
lemma q71 {n:Nat} (l:M) (F:Nat->Finset (Fin n)) (i:Fin n) :i∈(l.map F).foldr (· ∪ ·) ∅↔∃ a∈l,i∈F a:=by
 induction l with
 | nil=>simp
 | cons b l ih=>simp [ih]
lemma kf {n:Nat} (L:List (Finset (Fin n))) (g:G) (i:Fin n) :i∈yb L g↔∃ a∈g.inputs,i∈L.getD a ∅:=
 q71 _ _ _
def zb {n:Nat} (gs:U) (L:List (Finset (Fin n))):List (Finset (Fin n)):=
 gs.foldl (fun L g=>L++[yb L g]) L
def qr (n:Nat):List (Finset (Fin n)):=ofFn fun i:Fin n=>{i}
def ay {n:Nat} (x y:F n) (L:List (Finset (Fin n))) (w w':I):Prop:=
 L.length=w.length/\w.length=w'.length /\
  ∀ j:Nat,(∀ i∈L.getD j ∅,x i=y i)->w.getD j false=w'.getD j false
lemma k6 {n:Nat} (x y:F n) (gs:U) :∀ (L:List (Finset (Fin n))) (w w':I),ay x y L w w' -> ay x y (zb gs L) (q3 gs w) (q3 gs w'):=by
 induction gs with
 | nil=>intro L w w' h;exact h
 | cons g gs ih =>
  intro L w w' h;obtain ⟨c,d,e⟩:=h;apply ih (L++[yb L g])
    (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
    (w'++[g.op.eval (g.inputs.map fun i=>w'.getD i false)])
  refine ⟨by simp [c],by simp [d],?_⟩
  intro j b;by_cases s:j=L.length
  . subst s;rw [z0] at b;rw [c,z0,d,z0];congr 1
    apply lMCL
    intro a t;exact e a (fun i u=>b i ((kf L g i).2 ⟨a,t,u⟩))
  . rw [q8 _ _ _ _ s] at b;rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)];exact e j b
lemma j4 {n:Nat} (x y:F n) :ay x y (qr n) (ofFn x) (ofFn y):=by
 refine ⟨by simp [qr],by simp,?_⟩
 intro j c;by_cases b:j < n
 . have d:x ⟨j,b⟩=y ⟨j,b⟩:=c _ (by simp [qr,b]);simp [b,d]
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
def fk {n:Nat} (t:Nat) (L:List (Finset (Fin n))):Prop:=
 ∀ W:Finset Nat,(W.biUnion fun j=>L.getD j ∅).card<=t+W.card
lemma ld {n:Nat}:fk 0 (qr n):=by
 intro W;refine le_trans Finset.card_biUnion_le ?_
 rw [zero_add,Finset.card_eq_sum_ones];apply Finset.sum_le_sum
 intro j _;by_cases b:j < n
 . simp [qr,b]
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma jc {n:Nat} (t:Nat) (L:List (Finset (Fin n))) (g:G) (u:g.inputs.length<=2) (h:fk t L):fk (t+1) (L++[yb L g]):=by
 intro W;by_cases c:L.length∈W
 . have v:(W.biUnion fun j=>(L++[yb L g]).getD j ∅)
      ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j=>L.getD j ∅):=by
    intro i s;rw [Finset.mem_biUnion] at s ⊢;obtain ⟨j,w,b⟩:=s;by_cases d:j=L.length
    . subst d;rw [z0] at b;obtain ⟨a,x,y⟩:=(kf L g i).1 b;exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 x),y⟩
    . rw [q8 _ _ _ _ d] at b;exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨d,w⟩),b⟩
   have hc1:(W.erase L.length ∪ g.inputs.toFinset).card<=(W.card - 1)+2:=by
    refine le_trans (Finset.card_union_le _ _) ?_
    rw [Finset.card_erase_of_mem c];exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) u) _
   have hWpos:1<=W.card:=Finset.card_pos.2 ⟨_,c⟩
   have:=h (W.erase L.length ∪ g.inputs.toFinset)
   have:=Finset.card_le_card v
   omega
 . have z:(W.biUnion fun j=>(L++[yb L g]).getD j ∅)
      = (W.biUnion fun j=>L.getD j ∅):=by
    apply Finset.biUnion_congr rfl
    intro j hj;exact q8 _ _ _ _ (fun e=>c (e ▸ hj))
   rw [z]
   have:=h W
   omega
lemma nh {n:Nat} (gs:U):∀ (t:Nat) (L:List (Finset (Fin n))), (∀ g∈gs,Ok g)->fk t L->fk (t+gs.length) (zb gs L):=by
 induction gs with
 | nil=>intro t L _ h;exact h
 | cons g gs ih =>
  intro t L b h
  have:=ih (t+1) (L++[yb L g]) (fun g' c' => b g' (lMCM _ c'))
   (jc t L g (b g List.mem_cons_self).2 h)
  rw [lLC,show t+(gs.length+1)=t+1+gs.length by omega]
  exact this
lemma nj (n:Nat) (f:(F n)->Q) (T:Finset (Fin n)) (d:∀ i∈T,∃ x:F n,f (update x i (!x i))≠f x) (s:Nat) (h:HCS n f s):T.card<=s+1:=by
 obtain ⟨C,ok,b,hev⟩:=h;have b':C.gates.length<=s:=b;set S:=(zb C.gates (qr n)).getD C.output ∅ with g
 have j:T ⊆ S:=by
  intro i t;by_contra u;obtain ⟨x,v⟩:=d i t;apply v
  have w:=(k6 (update x i (!x i)) x C.gates _ _ _
   (j4 _ _)).2.2 C.output (by
    intro k y
    have:k≠i:=fun e=>u (e ▸ y)
    simp [fUN this])
  rw [<- hev,<- hev];exact w
 have c:=nh C.gates 0 (qr n) ok ld {C.output};simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at c;rw [<- g] at c
 have:=Finset.card_le_card j
 omega
def vg (g:G):G:=
 match g.op with
 | GateOp.not=>⟨GateOp.not,g.inputs.take 1⟩
 | _=>g
lemma nr (g:G) (F:Nat->Q) :(vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
 obtain ⟨op,inputs⟩:=g;cases op<;>simp only [vg]
 cases inputs<;>simp [GateOp.eval]
def tq (g:G):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
lemma xq (g:G) (h:Ok g):tq (vg g):=by
 obtain ⟨op,inputs⟩:=g;obtain ⟨b,hlen⟩:=h;rcases b with h|h|h
 . have:op=GateOp.and:=h
   subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
 . have:op=GateOp.or:=h
   subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
 . have:op=GateOp.not:=h
   subst this;refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩<;>simp [vg]<;>omega
lemma jd (gs:U):∀ w:I, q3 (gs.map vg) w=q3 gs w:=by
 induction gs with
 | nil=>intro w;rfl
 | cons g gs ih =>
  intro w;have b:q3 ((g::gs).map vg) w=q3 (gs.map vg)
   (w++[(vg g).op.eval ((vg g).inputs.map fun i=>w.getD i false)]):=rfl
  have c:q3 (g::gs) w
   = q3 gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
  rw [b,c,nr,ih]
abbrev e8:=Sum Bool Nat
def ze (w:I):e8->Q
 | inl c=>c
 | inr j=>w.getD j false
def qn (m:Nat):e8->Prop
 | inl _=>True
 | inr j=>j < m
def wr (m:Nat):List e8->Option G×e8
 | []=>(none,inl true)
 | inl c::_=>(none,inl (!c))
 | inr j::_=>(some ⟨GateOp.not,[j]⟩,inr m)
def ko (m:Nat):List e8->Option G×e8
 | []=>(none,inl true)
 | [inl c]=>(none,inl c)
 | [inr j]=>(none,inr j)
 | [inl c,inl d]=>(none,inl (c&&d))
 | [inl c,inr j]=>(none,bif c then inr j else inl false)
 | [inr j,inl c]=>(none,bif c then inr j else inl false)
 | [inr j,inr k]=>(some ⟨GateOp.and,[j,k]⟩,inr m)
 | _=>(none,inl false)
def ji (m:Nat):List e8->Option G×e8
 | []=>(none,inl false)
 | [inl c]=>(none,inl c)
 | [inr j]=>(none,inr j)
 | [inl c,inl d]=>(none,inl (c||d))
 | [inl c,inr j]=>(none,bif c then inl true else inr j)
 | [inr j,inl c]=>(none,bif c then inl true else inr j)
 | [inr j,inr k]=>(some ⟨GateOp.or,[j,k]⟩,inr m)
 | _=>(none,inl false)
def qg (op:GateOp) (m:Nat) (b:List e8):Option G×e8:=
 match op with
 | GateOp.and=>ko m b
 | GateOp.or=>ji m b
 | GateOp.not=>wr m b
 | _=>(none,inl false)
def mv (m:Nat) (g:G):Prop:=
 (g.op=GateOp.not/\∃ j,j < m/\g.inputs=[j]) \/
 ((g.op=GateOp.and\/g.op=GateOp.or)/\∃ j k,j < m/\k < m/\g.inputs=[j,k])
lemma j2 {m:Nat} {g:G} (h:mv m g):∀ a∈g.inputs,a < m:=by
 rcases h with ⟨_,j,d,c⟩|⟨_,j,k,d,hk,c⟩
 . intro a b;simp [c] at b;omega
 . intro a b;simp [c] at b;rcases b with rfl|rfl<;>omega
def yq (n:Nat) (gs:U):Prop:=
 ∀ p g,gs[p]?=some g->mv (n+p) g
lemma lm (op:GateOp) (m:Nat) (e:List e8) :∀ g∈(qg op m e).1,Ok g:=by
 intro g d;cases op<;>simp only [qg] at d
 . rcases e with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp [ko] at d<;>(subst d;simp [Ok])
 . rcases e with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp [ji] at d<;>(subst d;simp [Ok])
 . rcases e with _|⟨a,l⟩<;>(try cases a) <;>
    simp [wr] at d<;>(subst d;simp [Ok])
 . simp at d
 . simp at d
lemma q80 (op:GateOp) (m:Nat) (e:List e8) (h:∀ s∈e,qn m s) :∀ g∈(qg op m e).1,mv m g:=by
 intro g d;cases op<;>simp only [qg] at d
 . rcases e with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp [ko] at d
   subst d;exact Or.inr ⟨Or.inl rfl,_,_,h (inr _) (by simp),h (inr _) (by simp),rfl⟩
 . rcases e with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp [ji] at d
   subst d;exact Or.inr ⟨Or.inr rfl,_,_,h (inr _) (by simp),h (inr _) (by simp),rfl⟩
 . rcases e with _|⟨a,l⟩<;>(try cases a)<;>simp [wr] at d
   subst d;exact Or.inl ⟨rfl,_,h (inr _) (by simp),rfl⟩
 . simp at d
 . simp at d
lemma jh (op:GateOp) (m:Nat) (e:List e8) (h:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:e.length<=2) (i:op=GateOp.not->e.length<=1) (g:∃ c,inl c∈e) :(qg op m e).1=none:=by
 obtain ⟨c,g⟩:=g;rcases h with rfl|rfl|rfl
 . rcases e with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp_all [qg,ko]
 . rcases e with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp_all [qg,ji]
 . have:=i rfl
   rcases e with _|⟨a,_|⟨b,l⟩⟩<;>(try cases a)<;>simp_all [qg,wr]
lemma kn (op:GateOp) (h:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (w:I) (g:List e8) (hlen:g.length<=2) (hv:∀ s∈g,qn w.length s) :qn (w.length+(qg op w.length g).1.toList.length) (qg op w.length g).2 /\ ze (q3 (qg op w.length g).1.toList w) (qg op w.length g).2 = op.eval (g.map (ze w)):=by
 rcases h with rfl|rfl|rfl
 . rcases g with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩
   . simp [qg,ko,qn,ze,GateOp.eval]
   . cases a<;>simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . cases a<;>cases b<;>(try rename_i c e;cases c)<;>(try cases e) <;>
      simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases g with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a<;>simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a<;>cases b<;>(try rename_i c e;cases c)<;>(try cases e) <;>
      simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases g with _|⟨a,l⟩
   . simp [qg,wr,qn,ze,GateOp.eval]
   . cases a<;>simp_all [qg,wr,qn,ze,GateOp.eval,q3]
def qa (n:Nat) (b:List e8×U) (g:G):List e8×U:=
 (b.1++[(qg g.op (n+b.2.length)
   (g.inputs.map fun i=>b.1.getD i (inl false))).2],
  b.2++(qg g.op (n+b.2.length)
   (g.inputs.map fun i=>b.1.getD i (inl false))).1.toList)
def u2 (n:Nat) (gs:U) (b:List e8×U):List e8×U:=
 gs.foldl (qa n) b
lemma k4 (n:Nat) (g:G) (gs:U) (b:List e8×U) :u2 n (g::gs) b=u2 n gs (qa n b g):=rfl
lemma jz (n:Nat) (b c:U) (d:List e8×U) :u2 n (b++c) d=u2 n c (u2 n b d):=by simp [u2,List.foldl_append]
lemma fs (n:Nat) (gs:U):∀ b:List e8×U, (u2 n gs b).1.length=b.1.length+gs.length:=by
 induction gs with
 | nil=>intro b;rfl
 | cons g gs ih => intro b;rw [k4,ih];simp only [qa,lLA,lLC,lLN];omega
lemma wy (n k:Nat) (d:e8) (gs:U):∀ b:List e8×U, k < b.1.length->(u2 n gs b).1.getD k d=b.1.getD k d:=by
 induction gs with
 | nil=>intro b _;rfl
 | cons g gs ih =>
  intro b hk;rw [k4,ih (qa n b g) (by simp [qa];omega)]
  exact q8 _ _ _ _ (by omega)
lemma y2 {α:Type} (o:Option α):o.toList.length<=1:=by cases o<;>simp
lemma mb (n:Nat) (gs:U):∀ b:List e8×U, (∀ g∈b.2,Ok g)->∀ g∈(u2 n gs b).2,Ok g:=by
 induction gs with
 | nil=>intro b h;exact h
 | cons g gs ih =>
  intro b h;apply ih (qa n b g)
  intro g' d';rcases lMAp.1 d' with c|c
  . exact h g' c
  . exact lm _ _ _ g' (by simpa using c)
lemma cm (n:Nat) (gs:U):∀ b:List e8×U, (u2 n gs b).2.length<=b.2.length+gs.length:=by
 induction gs with
 | nil=>intro b;simp [u2]
 | cons g gs ih =>
  intro b;have h1:=ih (qa n b g);have h2:(qa n b g).2.length<=b.2.length+1:=by
   simp only [qa,lLA]
   have:=y2 (qg g.op (n+b.2.length)
    (g.inputs.map fun i=>b.1.getD i (inl false))).1
   omega
  rw [k4,lLC];omega
lemma zt (n k:Nat) (gs:U):∀ b:List e8×U, (∀ g∈gs,tq g)->k < b.1.length->(∃ c,b.1.getD k (inl false)=inl c) -> (∃ g∈gs,k∈g.inputs)->(u2 n gs b).2.length+1<=b.2.length+gs.length:=by
 induction gs with
 | nil=>intro b _ _ _ h;obtain ⟨g,e,_⟩:=h;simp at e
 | cons g gs ih =>
  intro b u j d s;rw [k4,lLC];by_cases v:k∈g.inputs
  . obtain ⟨c,d⟩:=d;have t:=u g List.mem_cons_self;have w:(qg g.op (n+b.2.length)
       (g.inputs.map fun i=>b.1.getD i (inl false))).1=none:=by
     apply jh
     . exact t.1.1
     . simpa using t.1.2
     . intro h;simpa using t.2 h
     . exact ⟨c,lMp.2 ⟨k,v,d⟩⟩
    have x:(qa n b g).2.length=b.2.length:=by
     show (b.2++(qg g.op (n+b.2.length)
       (g.inputs.map fun i=>b.1.getD i (inl false))).1.toList).length=_
     rw [w];simp
    have:=cm n gs (qa n b g)
    omega
  . have s':∃ g'∈gs,k∈g'.inputs:=by
     obtain ⟨g',e',j'⟩:=s;rcases lMM.1 e' with rfl|h
     . exact absurd j' v
     . exact ⟨g',h,j'⟩
    have h1:=ih (qa n b g) (fun g' e' => u g' (lMCM _ e'))
     (by simp [qa];omega)
     (by
       obtain ⟨c,d⟩:=d;refine ⟨c,?_⟩
       simp only [qa];rw [q8 _ _ _ _ (by omega)];exact d)
     s'
    have x:(qa n b g).2.length<=b.2.length+1:=by
     simp only [qa,lLA]
     have:=y2 (qg g.op (n+b.2.length)
       (g.inputs.map fun i=>b.1.getD i (inl false))).1
     omega
    omega
lemma km {m m' : Nat} (h:m<=m'):∀ s:e8,qn m s->qn m' s
 | inl _,_=>trivial
 | inr _,hj=>lt_of_lt_of_le hj h
lemma jg (w t:I):∀ s:e8,qn w.length s ->
  ze (w++t) s=ze w s
 | inl _,_=>rfl
 | inr _,hj=>List.getD_append _ _ _ _ hj
def ej (n:Nat) (y:I) (w:I) (b:List e8×U):Prop:=
 b.1.length=w.length/\∀ i:Nat,
  qn (n+b.2.length) (b.1.getD i (inl false)) /\
  ze (q3 b.2 y) (b.1.getD i (inl false))=w.getD i false
lemma j7 (n:Nat) (y:I) (hy:y.length=n) (gs:U) :∀ (w:I) (b:List e8×U),(∀ g∈gs,Ok g)->ej n y w b -> ej n y (q3 gs w) (u2 n gs b):=by
 induction gs with
 | nil=>intro w b _ h;exact h
 | cons g gs ih =>
  intro w b u h;apply ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) (qa n b g)
    (fun g' hg' => u g' (lMCM _ hg'))
  obtain ⟨v,c⟩:=h;set w':=q3 b.2 y with hw'
  have e':w'.length=n+b.2.length:=by rw [hw',qu,hy]
  set j:=g.inputs.map fun i=>b.1.getD i (inl false) with x
  have z:=u g List.mem_cons_self;have d:=kn g.op z.1 w' j (by simpa [x] using z.2)
    (by
     intro s d;obtain ⟨a,_,rfl⟩:=lMp.1 d;rw [e'];exact (c a).1)
  rw [e'] at d;set r:=qg g.op (n+b.2.length) j with hr
  have h1:j.map (ze w')=g.inputs.map fun i=>w.getD i false:=by
    rw [x,lMMp];apply lMCL
    intro a _;exact (c a).2
  have h2:q3 (b.2++r.1.toList) y=q3 r.1.toList w':=by rw [zd]
  obtain ⟨t,ht,_⟩:=y1 r.1.toList w';refine ⟨by simp [qa,v],?_⟩
  intro i
  show qn (n+(b.2++r.1.toList).length) ((b.1++[r.2]).getD i (inl false)) /\
    ze (q3 (b.2++r.1.toList) y) ((b.1++[r.2]).getD i (inl false))=_
  rw [h2,lLA,<- nAA];by_cases h0:i=b.1.length
  . subst h0;rw [z0,v,z0];exact ⟨d.1,by rw [d.2,h1]⟩
  . rw [q8 _ _ _ _ h0,q8 _ _ _ _ (by omega)];refine ⟨km (by omega) _ (c i).1,?_⟩
    rw [ht,jg _ _ _ (by rw [e'];exact (c i).1)]
    exact (c i).2
lemma bh (n:Nat) (gs:U):∀ b:List e8×U, (∀ g∈gs,Ok g)->(∀ i,qn (n+b.2.length) (b.1.getD i (inl false))) -> yq n b.2->yq n (u2 n gs b).2:=by
 induction gs with
 | nil=>intro b _ _ e;exact e
 | cons g gs ih =>
  intro b j h e;have v:=ih (qa n b g) (fun g' w' => j g' (lMCM _ w'))
  apply v
  . intro i;set x:=g.inputs.map fun i=>b.1.getD i (inl false) with y
    have t:=j g List.mem_cons_self;have d:=kn g.op t.1 (List.replicate (n+b.2.length) false) x
      (by simpa [y] using t.2)
      (by
       intro s d;obtain ⟨a,_,rfl⟩:=lMp.1 d;simpa using h a)
    simp only [List.length_replicate] at d
    show qn (n+(b.2++_).length) ((b.1++[_]).getD i (inl false))
    rw [lLA,<- nAA];by_cases u:i=b.1.length
    . subst u;rw [z0];exact d.1
    . rw [q8 _ _ _ _ u];exact km (by omega) _ (h i)
  . intro p g' c;simp only [qa] at c;by_cases z:p < b.2.length
    . rw [List.getElem?_append_left z] at c;exact e p g' c
    . rw [List.getElem?_append_right (by omega)] at c;set r:=qg g.op (n+b.2.length)
       (g.inputs.map fun i=>b.1.getD i (inl false)) with hr
      cases ho:r.1 with
      | none=>simp [ho] at c
      | some g0 =>
       rw [ho] at c;have h0:p - b.2.length=0:=by
        have:=(lGES.1 c).1
        simp at this;omega
       have h1:p=b.2.length:=by omega
       rw [h0] at c;simp at c;subst c;rw [h1];exact q80 g.op (n+b.2.length) _ (by
        intro s d;obtain ⟨a,_,rfl⟩:=lMp.1 d;exact h a) g0 (by rw [<- hr,ho];rfl)
def qd (n:Nat) (b:Q):List e8:=
 ofFn (fun i:Fin n=>inr (i:Nat))++[inl b]
lemma kp (n:Nat) (b:Q) :(qd n b).getD n (inl false)=inl b:=
 z2 _ _ _ _ (by simp)
lemma gy (n:Nat) (b:Q) (y:F n) :ej n (ofFn y) (ofFn y++[b]) (qd n b,[]):=by
 refine ⟨by simp [qd],?_⟩
 intro i;have c:(ofFn (fun i:Fin n=>(inr (i:Nat):e8))).length=n:=by simp
 have d:(ofFn y).length=n:=by simp
 by_cases e:i=n
 . subst e;simp only [qd];rw [z2 _ _ _ _ c,z2 _ _ _ _ d];exact ⟨trivial,rfl⟩
 . simp only [qd];rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)];by_cases g:i < n
   . simp [g,qn,ze,q3]
   . rw [lGD _ _ (by omega),lGD _ _ (by omega)];exact ⟨trivial,rfl⟩
lemma rf (n:Nat) (y:F n) (b:Q) :ofFn (Fin.snoc y b:Fin (n+1)->Q)=ofFn y++[b]:=by rw [List.ofFn_succ'];simp
lemma jr (n:Nat) (gs:U):∀ L:List (Finset (Fin (n+1))), (∀ g∈gs,n ∉ g.inputs)->(∀ j:Nat,j≠n->Fin.last n ∉ L.getD j ∅) -> ∀ j:Nat,j≠n->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil=>intro L _ h;exact h
 | cons g gs ih =>
  intro L b h;apply ih (L++[yb L g]) (fun g' d' => b g' (lMCM _ d'))
  intro j i;by_cases c:j=L.length
  . subst c;rw [z0];intro s;obtain ⟨a,t,u⟩:=(kf L g _).1 s;exact h a (fun e=>b g List.mem_cons_self (e ▸ t)) u
  . rw [q8 _ _ _ _ c];exact h j i
lemma q74 (m j:Nat) (h:j < m) :(qr m).getD j ∅={⟨j,h⟩}:=by simp [qr,h]
lemma yi (n:Nat):∀ j:Nat,j≠n -> Fin.last n ∉ (qr (n+1)).getD j ∅:=by
 intro j c;by_cases b:j < n+1
 . have e:(qr (n+1)).getD j ∅={⟨j,b⟩}:=q74 (n+1) j b;rw [e,Finset.mem_singleton];intro e';exact c (by have:=congrArg Fin.val e';simpa using this.symm)
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma nk (n:Nat) (f:(Fin (n+1)->Q)->Q) (b:Q) (s:Nat) (h3:∃ x:Fin (n+1)->Q,f (update x (Fin.last n) (!x (Fin.last n)))≠f x) (h4:∃ y y':F n,f (Fin.snoc y b)≠f (Fin.snoc y' b)) (h:HCS (n+1) f s) :∃ s',s'+1<=s/\HCS n (fun y:F n=>f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,z,hev⟩:=h;have z':C.gates.length<=s:=z;set gs:=C.gates.map vg with h0
 have h1:∀ g∈gs,tq g:=by intro g t;obtain ⟨g0,h5,rfl⟩:=lMp.1 t;exact xq g0 (ok g0 h5)
 have u:∀ x:Fin (n+1)->Q,(q3 gs (ofFn x)).getD C.output false=f x:=by intro x;rw [h0,jd,<- hev x];rfl
 set d:=u2 n gs (qd n b,[]) with h2
 have h6:∀ y:F n,
   ej n (ofFn y) (q3 gs (ofFn (Fin.snoc y b:Fin (n+1)->Q))) d:=by
  intro y;rw [rf];exact j7 n _ (by simp) gs _ _ (fun g t=>(h1 g t).1) (gy n b y)
 have v:∀ y:F n,
   ze (q3 d.2 (ofFn y)) (d.1.getD C.output (inl false))
     = f (Fin.snoc y b):=by
  intro y;rw [((h6 y).2 C.output).2,u]
 cases i:d.1.getD C.output (inl false) with
 | inl c =>
  exfalso;obtain ⟨y,y',h7⟩:=h4;apply h7
  rw [<- v y,<- v y',i];rfl
 | inr j =>
  have hlen:d.2.length+1<=s:=by
   by_cases w:∃ g∈gs,n∈g.inputs
   . have:=zt n n gs (qd n b,[]) h1 (by simp [qd])
      ⟨b,z2 _ _ _ _ (by simp)⟩ w
     rw [<- h2] at this;have hl:gs.length=C.gates.length:=by simp [h0]
     simp only [lLN,zero_add] at this;omega
   . exfalso
     push Not at w
     have h8:C.output≠n:=by
      intro e;rw [e,h2,wy n n _ gs _ (by simp [qd])] at i;have hb:(qd n b).getD n (inl false)=inl b:=
       z2 _ _ _ _ (by simp)
      rw [show ((qd n b,([]:U))).1=qd n b from rfl,hb] at i;cases i
     obtain ⟨x,hx⟩:=h3;apply hx
     have h9:=jr n gs (qr (n+1)) w (yi n) C.output h8;have x2:=(k6 (update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠Fin.last n:=fun e=>h9 (e ▸ hk)
       simp [fUN this])
     rw [<- u,<- u];exact x2
  refine ⟨d.2.length,hlen,⟨d.2,j⟩,mb n gs _ (by simp),le_refl _,?_⟩
  intro y
  have:=v y
  rw [i] at this;exact this
lemma q79 (op:GateOp) (m:Nat) (g:List e8) (h:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:g.length<=2) (i:op=GateOp.not->g.length<=1) (b:Q) (j:op=GateOp.and->b=false) (s:op=GateOp.or->b=true) (hc:inl b∈g):∃ c,(qg op m g).2=inl c:=by
 rcases h with rfl|rfl|rfl
 . have:=j rfl
   subst this;rcases g with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩<;>(try cases a)<;>(try cases d) <;>
    simp_all [qg,ko]
 . have:=s rfl
   subst this;rcases g with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩<;>(try cases a)<;>(try cases d) <;>
    simp_all [qg,ji]
 . have:=i rfl
   rcases g with _|⟨a,_|⟨d,l⟩⟩<;>(try cases a)<;>simp_all [qg,wr]
lemma vs (n:Nat) (b:List e8×U) (g:G) (d:tq g) (k:Nat) (e:k∈g.inputs) (c:Q) (j:b.1.getD k (inl false)=inl c) :(qa n b g).2.length=b.2.length:=by
 have s:(qg g.op (n+b.2.length)
    (g.inputs.map fun i=>b.1.getD i (inl false))).1=none:=by
  apply jh
  . exact d.1.1
  . simpa using d.1.2
  . intro h;simpa using d.2 h
  . exact ⟨c,lMp.2 ⟨k,e,j⟩⟩
 show (b.2++(qg g.op (n+b.2.length)
  (g.inputs.map fun i=>b.1.getD i (inl false))).1.toList).length=_
 rw [s];simp
def wl (g:G):Q:=
 match g.op with
 | GateOp.or=>true
 | _=>false
lemma q90 (n:Nat) (b:List e8×U) (g:G) (d:tq g) (k:Nat) (j:k∈g.inputs) (s:b.1.getD k (inl false)=inl (wl g)) :∃ c,(qa n b g).1.getD b.1.length (inl false)=inl c:=by
 have e:(qa n b g).1.getD b.1.length (inl false)
    = (qg g.op (n+b.2.length)
     (g.inputs.map fun i=>b.1.getD i (inl false))).2:=z0 _ _ _
 rw [e];apply q79 _ _ _ d.1.1 (by simpa using d.1.2) (fun h=>by simpa using d.2 h)
   (wl g)
 . intro h;simp [wl,h]
 . intro h;simp [wl,h]
 . exact lMp.2 ⟨k,j,s⟩
lemma q53 {n:Nat} (b c:U) (L:List (Finset (Fin n))) :zb (b++c) L=zb c (zb b L):=by simp [zb,List.foldl_append]
lemma q54 {n:Nat} (gs:U):∀ L:List (Finset (Fin n)), (zb gs L).length=L.length+gs.length:=by
 induction gs with
 | nil=>intro L;rfl
 | cons g gs ih => intro L;have h:zb (g::gs) L=zb gs (L++[yb L g]):=rfl;rw [h,ih];simp only [lLA,lLC,lLN];omega
lemma ly (n:Nat) (D:Nat->Prop) (gs:U) :∀ L:List (Finset (Fin (n+1))), (∀ g∈gs,∀ a∈g.inputs,¬ D a)->(∀ j:Nat,¬ D j->Fin.last n ∉ L.getD j ∅) -> ∀ j:Nat,¬ D j->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil=>intro L _ h;exact h
 | cons g gs ih =>
  intro L b h;apply ih (L++[yb L g]) (fun g' d' => b g' (lMCM _ d'))
  intro j e;by_cases c:j=L.length
  . subst c;rw [z0];intro i;obtain ⟨a,s,t⟩:=(kf L g _).1 i;exact h a (b g List.mem_cons_self a s) t
  . rw [q8 _ _ _ _ c];exact h j e
lemma la (n:Nat) (gs:U) (v:∀ g∈gs,tq g) (o:Nat) (w:Fin.last n∈(zb gs (qr (n+1))).getD o ∅) (h5:∀ b c,(u2 n gs (qd n b,[])).1.getD o (inl false)≠inl c) :∃ b,(u2 n gs (qd n b,[])).2.length+2<=gs.length:=by
 have h6:o≠n:=by
   intro e;apply h5 false false
   rw [e,wy n n _ gs _ (by simp [qd])];exact kp n false
 by_cases x:∃ g∈gs,n∈g.inputs
 swap
 . exfalso
   push Not at x
   exact jr n gs (qr (n+1)) x (yi n) o h6 w
 obtain ⟨g,s,h7⟩:=x;obtain ⟨d,i,rfl⟩:=List.append_of_mem s;have h8:tq g:=v g s;have x3:∀ g'∈d,tq g':=fun g' h=>v g' (List.mem_append_left _ h)
 have h9:∀ g'∈i,tq g':=
   fun g' h=>v g' (List.mem_append_right _ (lMCM _ h))
 have u:∀ b,u2 n (d++g::i) (qd n b,[])
     = u2 n i (qa n (u2 n d (qd n b,[])) g):=
   fun b=>by rw [jz,k4]
 have y:∀ b,(u2 n d (qd n b,[])).1.getD n (inl false)=inl b:=by intro b;rw [wy n n _ d _ (by simp [qd])];exact kp n b
 have z:∀ b,(u2 n d (qd n b,[])).1.length=n+1+d.length:=by intro b;rw [fs];simp [qd]
 have x2:∀ b,(u2 n d (qd n b,[])).2.length<=0+d.length:=
   fun b=>cm n d (qd n b,[])
 have h0:=fun b=>vs n (u2 n d (qd n b,[])) g h8 n h7 b (y b)
 have h4:∀ b,(qa n (u2 n d (qd n b,[])) g).1.length
     = n+1+d.length+1:=by
   intro b;simp [qa,z b]
 have a2:∀ b,(qa n (u2 n d (qd n b,[])) g).1.getD n (inl false)
     = inl b:=by
   intro b
   show ((u2 n d (qd n b,[])).1++[_]).getD n _=_
   rw [q8 _ _ _ _ (by rw [z b];omega)]
   exact y b
 have hF:=fun b=>cm n i (qa n (u2 n d (qd n b,[])) g)
 have hlen:(d++g::i).length=d.length+i.length+1:=by simp only [lLA,lLC];omega
 by_cases h1:∃ g'∈d,n∈g'.inputs
 . refine ⟨false,?_⟩
   have a1:(u2 n d (qd n false,[])).2.length+1<=0+d.length:=
     zt n n d (qd n false,[]) x3 (by simp [qd])
       ⟨false,kp n false⟩ h1
   have:=hF false
   have:=h0 false
   rw [u,hlen];omega
 by_cases h2:∃ g'∈i,n∈g'.inputs
 . refine ⟨false,?_⟩
   have a1:=zt n n i (qa n (u2 n d (qd n false,[])) g) h9
     (by rw [h4];omega) ⟨false,a2 false⟩ h2
   have:=x2 false
   have:=h0 false
   rw [u,hlen];omega
 obtain ⟨c,hc⟩:=q90 n (u2 n d (qd n (wl g),[])) g h8 n h7
   (y (wl g))
 rw [z (wl g)] at hc;refine ⟨wl g,?_⟩
 by_cases h3:∃ g'∈i,(n+1+d.length)∈g'.inputs
 . have a1:=zt n (n+1+d.length) i
     (qa n (u2 n d (qd n (wl g),[])) g) h9
     (by rw [h4];omega) ⟨c,hc⟩ h3
   have:=x2 (wl g)
   have:=h0 (wl g)
   rw [u,hlen];omega
 . exfalso;have b1:o≠n+1+d.length:=by
     intro e;apply h5 (wl g) c
     rw [u,e,wy n _ _ i _ (by rw [h4];omega)]
     exact hc
   push Not at h1 h2 h3
   have hs:zb (d++g::i) (qr (n+1))
       = zb i (zb d (qr (n+1))
         ++ [yb (zb d (qr (n+1))) g]):=by
     rw [q53];rfl
   rw [hs] at w;have hL:=jr n d (qr (n+1)) h1 (yi n);have hb:(zb d (qr (n+1))).length=n+1+d.length:=by rw [q54];simp [qr]
   refine ly n (fun j=>j=n\/j=n+1+d.length) i _ ?_ ?_ o
     (by simp [h6,b1]) w
   . intro g' s' a ha hD;rcases hD with rfl|rfl
     . exact h2 g' s' ha
     . exact h3 g' s' ha
   . intro j t;have t':j≠n/\j≠n+1+d.length:=by
       constructor
       . exact fun e=>t (Or.inl e)
       . exact fun e=>t (Or.inr e)
     rw [q8 _ _ _ _ (by rw [hb];exact t'.2)]
     exact hL j t'.1
lemma nm (n:Nat) (f:(Fin (n+1)->Q)->Q) (s:Nat) (h1:∃ x:Fin (n+1)->Q,f (update x (Fin.last n) (!x (Fin.last n)))≠f x) (h2:∀ b:Q,∃ y y':F n,f (Fin.snoc y b)≠f (Fin.snoc y' b)) (h:HCS (n+1) f s) :∃ (b:Q) (s' : Nat),s'+2<=s /\ HCS n (fun y:F n=>f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,v,hev⟩:=h;have v':C.gates.length<=s:=v;set gs:=C.gates.map vg with w
 have hl:gs.length=C.gates.length:=by simp [w]
 have z:∀ g∈gs,tq g:=by intro g i;obtain ⟨g0,h3,rfl⟩:=lMp.1 i;exact xq g0 (ok g0 h3)
 have t:∀ x:Fin (n+1)->Q,(q3 gs (ofFn x)).getD C.output false=f x:=by intro x;rw [w,jd,<- hev x];rfl
 have h4:∀ (b:Q) (y:F n),
   ej n (ofFn y) (q3 gs (ofFn (Fin.snoc y b:Fin (n+1)->Q)))
    (u2 n gs (qd n b,[])):=by
  intro b y;rw [rf];exact j7 n _ (by simp) gs _ _ (fun g i=>(z g i).1) (gy n b y)
 have u:∀ (b:Q) (y:F n),
   ze (q3 (u2 n gs (qd n b,[])).2 (ofFn y))
    ((u2 n gs (qd n b,[])).1.getD C.output (inl false))=f (Fin.snoc y b):=by
  intro b y;rw [((h4 b y).2 C.output).2,t]
 have h0:∀ b c,
   (u2 n gs (qd n b,[])).1.getD C.output (inl false)≠inl c:=by
  intro b c d;obtain ⟨y,y',h5⟩:=h2 b;apply h5
  rw [<- u b y,<- u b y',d];rfl
 have h6:Fin.last n∈(zb gs (qr (n+1))).getD C.output ∅:=by
  by_contra h7;obtain ⟨x,hx⟩:=h1;apply hx
  have h8:=(k6 (update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
   (j4 _ _)).2.2 C.output (by
    intro k hk
    have:k≠Fin.last n:=fun e=>h7 (e ▸ hk)
    simp [fUN this])
  rw [<- t,<- t];exact h8
 obtain ⟨b,hb⟩:=la n gs z C.output h6 h0;cases d:(u2 n gs (qd n b,[])).1.getD C.output (inl false) with
 | inl c=>exact absurd d (h0 b c)
 | inr j =>
  refine ⟨b,(u2 n gs (qd n b,[])).2.length,by omega,
   ⟨(u2 n gs (qd n b,[])).2,j⟩,mb n gs _ (by simp),le_refl _,?_⟩
  intro y
  have:=u b y
  rw [d] at this;exact this
def ov (n m:Nat) (π:Fin n->Fin m) (w:Nat):Nat:=
 if h:w < n then (π ⟨w,h⟩ : Nat) else w - n+m
def jt (n m:Nat) (π:Fin n->Fin m) (g:G):G:=
 ⟨g.op,g.inputs.map (ov n m π)⟩
def gv (n m:Nat) (π:Fin n->Fin m) (C:Circuit):Circuit:=
 ⟨C.gates.map (jt n m π),ov n m π C.output⟩
def da (w:I) (g:G):I:=
 w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
def fj (n m:Nat) (π:Fin n->Fin m) (W W':I):Prop:=
 n<=W.length/\W'.length+n=W.length+m /\
  ∀ w:Nat,W'.getD (ov n m π w) false=W.getD w false
lemma kr (n m:Nat) (π:Fin n->Fin m) (W W':I) (g:G) (h:fj n m π W W'):fj n m π (da W g) (da W' (jt n m π g)):=by
 obtain ⟨h1,h2,c⟩:=h;have d:(jt n m π g).op.eval
    ((jt n m π g).inputs.map fun i=>W'.getD i false)
    = g.op.eval (g.inputs.map fun i=>W.getD i false):=by
   simp only [jt,lMMp];congr 1
   apply lMCL
   intro a _;exact c a
 refine ⟨by simp [da];omega,by simp [da];omega,?_⟩
 intro w;simp only [da,d];rcases Nat.lt_trichotomy w W.length with b|b|b
 . have e:ov n m π w < W'.length:=by
    unfold ov
    split
    . have:=(π ⟨w,by assumption⟩).2;omega
    . omega
   rw [List.getD_append _ _ _ _ e,List.getD_append _ _ _ _ b];exact c w
 . have j:ov n m π w=W'.length:=by
    unfold ov
    split
    . omega
    . omega
   rw [j,b,z0,z0]
 . have hge:W'.length+1<=ov n m π w:=by
    unfold ov
    split
    . omega
    . omega
   rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
lemma ke (n m:Nat) (π:Fin n->Fin m) (gs:U) :∀ W W':I,fj n m π W W' -> fj n m π (gs.foldl da W) ((gs.map (jt n m π)).foldl da W'):=by
 induction gs with
 | nil=>intro W W' h;exact h
 | cons g gs ih => intro W W' h;exact ih _ _ (kr n m π W W' g h)
lemma kk (n m:Nat) (π:Fin n->Fin m) (x:F m) :fj n m π (ofFn (x ∘ π)) (ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w;unfold ov
 split
 . rename_i b
   rw [lGDE _ _ (by simp),lGDE _ _ (by simpa using b)];simp
 . rename_i b
   rw [lGD _ _ (by simp),lGD _ _ (by simp;omega)]
lemma yn {n m:Nat} (π:Fin n->Fin m) (h:(F n)->Q) (s:Nat) (c:HCS n h s):HCS m (fun x=>h (x ∘ π)) s:=by
 obtain ⟨C,ok,d,hev⟩:=c;refine ⟨gv n m π C,?_,?_,?_⟩
 . intro g e;obtain ⟨g0,b,rfl⟩:=lMp.1 e;exact ⟨(ok g0 b).1,by simpa [jt] using (ok g0 b).2⟩
 . simpa [gv,Circuit.size] using d
 . intro x
   show _=h (x ∘ π)
   rw [<- hev (x ∘ π)]
   have:=(ke n m π C.gates _ _ (kk n m π x)).2.2 C.output
   exact this
lemma ks (n:Nat) (p:Fin (n+1)) (x:Fin (n+1)->Q) (b:Q) :(Fin.snoc (fun j:Fin n=>x (Equiv.swap p (Fin.last n) j.castSucc)) b :Fin (n+1)->Q) ∘ (Equiv.swap p (Fin.last n)) = update x p b:=by
 funext j;simp only [Function.comp_apply];by_cases c:j=p
 . subst c;rw [Equiv.swap_apply_left,Fin.snoc_last,fUS]
 . have g:Equiv.swap p (Fin.last n) j≠Fin.last n:=by
    intro e;apply c
    have:=congrArg (Equiv.swap p (Fin.last n)) e
    rwa [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
   obtain ⟨t,d⟩:=Fin.exists_castSucc_eq.2 g;rw [<- d,Fin.snoc_castSucc,d,Equiv.swap_apply_self,fUN c]
lemma xj (n:Nat) (f:(Fin (n+1)->Q)->Q) (p:Fin (n+1)) (b:Q) (s:Nat) (c:∃ x:Fin (n+1)->Q,f (update x p (!x p))≠f x) (d:∃ x y:Fin (n+1)->Q, f (update x p b)≠f (update y p b)) (h:HCS (n+1) f s) :∃ s' : Nat,s'+1<=s /\ HCS (n+1) (fun x=>f (update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have g:HCS (n+1) (fun x=>f (x ∘ σ)) s:=yn (⇑σ) f s h
 have i:∀ x:Fin (n+1)->Q,(x ∘ σ) ∘ σ=x:=by intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have t : σ.symm (Fin.last n)=p:=by rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have c':∃ x:Fin (n+1)->Q,
   (fun x=>f (x ∘ σ)) (update x (Fin.last n) (!x (Fin.last n)))
    ≠ (fun x=>f (x ∘ σ)) x:=by
  obtain ⟨x0,u⟩:=c;refine ⟨x0 ∘ σ,?_⟩
  simp only;rw [Function.update_comp_equiv,t,i]
  have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
  rw [this];exact u
 have d':∃ y y':F n,
   (fun x=>f (x ∘ σ)) (Fin.snoc y b)≠(fun x=>f (x ∘ σ)) (Fin.snoc y' b):=by
  obtain ⟨x,y,v⟩:=d;refine ⟨fun j=>x (σ j.castSucc),fun j=>y (σ j.castSucc),?_⟩
  simp only;rw [ks,ks];exact v
 obtain ⟨s',w,h'⟩:=nk n _ b s c' d' g;refine ⟨s',w,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Q =>
   (fun y:F n=>(fun x=>f (x ∘ σ)) (Fin.snoc y b))
    (x ∘ fun j:Fin n => σ j.castSucc))
   = fun x=>f (update x p b):=by
  funext x;simp only;exact congrArg f (ks n p x b)
 rw [e] at h'';exact h''
lemma lv (n:Nat) (f:(Fin (n+1)->Q)->Q) (p:Fin (n+1)) (s:Nat) (c:∃ x:Fin (n+1)->Q,f (update x p (!x p))≠f x) (d:∀ b:Q,∃ x y:Fin (n+1)->Q, f (update x p b)≠f (update y p b)) (h:HCS (n+1) f s) :∃ (b:Q) (s' : Nat),s'+2<=s /\ HCS (n+1) (fun x=>f (update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have g:HCS (n+1) (fun x=>f (x ∘ σ)) s:=yn (⇑σ) f s h
 have i:∀ x:Fin (n+1)->Q,(x ∘ σ) ∘ σ=x:=by intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have t : σ.symm (Fin.last n)=p:=by rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have c':∃ x:Fin (n+1)->Q,
   (fun x=>f (x ∘ σ)) (update x (Fin.last n) (!x (Fin.last n)))
    ≠ (fun x=>f (x ∘ σ)) x:=by
  obtain ⟨x0,u⟩:=c;refine ⟨x0 ∘ σ,?_⟩
  simp only;rw [Function.update_comp_equiv,t,i]
  have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
  rw [this];exact u
 have d':∀ b:Q,∃ y y':F n,
   (fun x=>f (x ∘ σ)) (Fin.snoc y b)≠(fun x=>f (x ∘ σ)) (Fin.snoc y' b):=by
  intro b;obtain ⟨x,y,v⟩:=d b;refine ⟨fun j=>x (σ j.castSucc),fun j=>y (σ j.castSucc),?_⟩
  simp only;rw [ks,ks];exact v
 obtain ⟨b,s',w,h'⟩:=nm n _ s c' d' g;refine ⟨b,s',w,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Q =>
   (fun y:F n=>(fun x=>f (x ∘ σ)) (Fin.snoc y b))
    (x ∘ fun j:Fin n => σ j.castSucc))
   = fun x=>f (update x p b):=by
  funext x;simp only;exact congrArg f (ks n p x b)
 rw [e] at h'';exact h''
def e3 (gs:U) (n:Nat) (a:Nat):u7 n:=
 fun x=>(q3 gs (ofFn x)).getD a false
lemma lc (gs:U) (n:Nat) (i:Fin n):e3 gs n i=fun x=>x i:=by funext x;unfold e3;rw [ve _ _ _ (by simp)];simp
lemma aw {α:Type} (gs:List α) (p:Nat) (g : α) (b:gs[p]?=some g) :∃ pre post,gs=pre++g::post/\pre.length=p:=by
 have c:p < gs.length:=(lGES.1 b).1;have d:gs[p]=g:=(lGES.1 b).2;refine ⟨gs.take p,gs.drop (p+1),?_,by simp;omega⟩
 have e:gs=gs.take p++gs.drop p:=(List.take_append_drop p gs).symm;have h:gs.drop p=gs[p]::gs.drop (p+1):=List.drop_eq_getElem_cons c;exact e.trans (by rw [h,d])
lemma oa (n:Nat) (gs:U) (p:Nat) (g:G) (e:gs[p]?=some g) (h:∀ a∈g.inputs,a < n+p) (x:F n) :e3 gs n (n+p) x=g.op.eval (g.inputs.map fun a=>e3 gs n a x):=by
 obtain ⟨b,c,rfl,hlen⟩:=aw gs p g e;unfold e3;have j:q3 (b++g::c) (ofFn x)=q3 c
   (q3 b (ofFn x) ++
    [g.op.eval (g.inputs.map fun i=>(q3 b (ofFn x)).getD i false)]):=by
  rw [zd];rfl
 have d:(q3 b (ofFn x)).length=n+p:=by rw [qu];simp [hlen]
 rw [j,ve _ _ _ (by simp [d]),z2 _ _ _ _ d];congr 1
 apply lMCL
 intro a s;have hal:=h a s;have t:=ve c (q3 b (ofFn x) ++
    [g.op.eval (g.inputs.map fun i=>(q3 b (ofFn x)).getD i false)]) a
    (by simp [d];omega)
 rw [t,List.getD_append _ _ _ _ (by omega)]
def vi (n:Nat):List e8:=ofFn fun i:Fin n=>inr (i:Nat)
lemma lf (n:Nat) (y:F n) :ej n (ofFn y) (ofFn y) (vi n,[]):=by
 refine ⟨by simp [vi],?_⟩
 intro i;by_cases b:i < n
 . simp [vi,b,qn,ze,q3]
 . rw [lGD _ _ (by simp [vi];omega),
    lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
lemma xn (n:Nat) (f:u7 n) (s:Nat) (u:∃ y y':F n,f y≠f y') (h:HCS n f s) :∃ gs o,yq n gs/\gs.length<=s/\o < n+gs.length/\∀ x,e3 gs n o x=f x:=by
 obtain ⟨C,ok,v,hev⟩:=h;have v':C.gates.length<=s:=v;set b:=u2 n C.gates (vi n,[]) with z
 have e:∀ y:F n,ej n (ofFn y) (q3 C.gates (ofFn y)) b:=
  fun y=>j7 n _ (by simp) C.gates _ _ ok (lf n y)
 have hcl:yq n b.2:=by
  apply bh n C.gates (vi n,[]) ok
  . intro i;by_cases h0:i < n
    . simp [vi,h0,qn]
    . rw [lGD _ _ (by simp [vi];omega)];trivial
  . intro p g hp;simp at hp
 have hlen:b.2.length<=s:=by
  have:=cm n C.gates (vi n,[])
  rw [<- z] at this;simp only [lLN,zero_add] at this;omega
 cases t:b.1.getD C.output (inl false) with
 | inl c =>
  exfalso;obtain ⟨y,y',h3⟩:=u;apply h3
  have d:=((e y).2 C.output).2;have w:=((e y').2 C.output).2;rw [t] at d w;have h1:(q3 C.gates (ofFn y)).getD C.output false=f y:=hev y;have h2:(q3 C.gates (ofFn y')).getD C.output false=f y':=hev y';rw [<- h1,<- h2,<- d,<- w];rfl
 | inr j =>
  have hj:j < n+b.2.length:=by
    obtain ⟨y,_,_⟩:=u
    have:=((e y).2 C.output).1
    rw [t] at this;exact this
  refine ⟨b.2,j,hcl,hlen,hj,?_⟩
  intro x;have d:=((e x).2 C.output).2;rw [t] at d;exact d.trans (hev x)
def qk {α:Type} (b:Q) (x : α) (c:List α):List α:=
 if b then x::c else c
def Run {α:Type} (inv : α->α) (meet join : α->α->α) (y : α) (t:Nat) (d:List α):Prop:=
 ∀ P:Nat->List α->Prop,P 0 [y] ->
  (∀ {s xs zs},List.Perm xs zs->P s xs->P s zs) ->
  (∀ {s a r} (neg save:Q),P s ((if neg then inv a else a)::qk save a r) ->
   P (s+1) (a::r)) ->
  (∀ {s a b r} (c ka kb:Q),
   P s ((if c then meet a b else join a b)::qk ka a (qk kb b r)) ->
   P (s+1) (a::b::r))->P t d
lemma Run.done {α inv meet join y} : @Run α inv meet join y 0 [y]:=fun _ d _ _ _=>d
lemma Run.perm {α inv meet join y s xs zs} (p:List.Perm xs zs) (h : @Run α inv meet join y s xs):Run inv meet join y s zs:=
 fun P d q u b=>q p (h P d q u b)
lemma Run.one {α inv meet join y s a r} (c e:Q) (h : @Run α inv meet join y s ((if c then inv a else a)::qk e a r)) :Run inv meet join y (s+1) (a::r):=fun P d q u b=>u c e (h P d q u b)
lemma Run.two {α inv meet join y s a b r} (c e g:Q) (h : @Run α inv meet join y s ((if c then meet a b else join a b)::qk e a (qk g b r))) :Run inv meet join y (s+1) (a::b::r):=fun P d q u v=>v c e g (h P d q u v)
lemma Run.fold {α inv meet join y} {P:∀ t ws,@Run α inv meet join y t ws->Prop} (done:P 0 [y] Run.done) (perm:∀ {s xs zs} (d:List.Perm xs zs) (h:Run inv meet join y s xs), P s xs h->P s zs (Run.perm d h)) (one:∀ {s a r} (e g:Q) (h:Run inv meet join y s ((if e then inv a else a)::qk g a r)), P _ _ h->P _ _ (Run.one e g h)) (two:∀ {s a b r} (c i j:Q) (h:Run inv meet join y s ((if c then meet a b else join a b)::qk i a (qk j b r))), P _ _ h->P _ _ (Run.two c i j h)) {t ws} (h:Run inv meet join y t ws):P t ws h:=by
 have u:=h (fun s xs => ∃ h':Run inv meet join y s xs,P s xs h')
  ⟨Run.done,done⟩
  (fun d ⟨h',ih⟩ => ⟨Run.perm d h',perm d h' ih⟩)
  (fun n k ⟨h',ih⟩ => ⟨Run.one n k h',one n k h' ih⟩)
  (fun c a b ⟨h',ih⟩ => ⟨Run.two c a b h',two c a b h' ih⟩)
 exact u.elim fun _ d=>d
lemma wd {α β:Type} (e : α->β) (b:Q) (x : α) (c:List α) :(qk b x c).map e=qk b (e x) (c.map e):=by cases b<;>simp [qk]
lemma wa {α:Type} (b:Q) (x a : α) (c:List α) :a∈qk b x c↔(b=true/\a=x)\/a∈c:=by cases b<;>simp [qk]
lemma cj {α:Type} (b:Q) (x : α) (c:List α) (h:c.Nodup) (d:x ∉ c) :(qk b x c).Nodup:=by
 cases b
 . simpa [qk] using h
 . simpa [qk] using And.intro d h
lemma Run.map {α β:Type} (e : α->β) {inv : α->α} {meet join : α->α->α} {inv' : β->β} {meet' join' : β->β->β} (g:∀ a,e (inv a)=inv' (e a)) (i:∀ a b,e (meet a b)=meet' (e a) (e b)) (j:∀ a b,e (join a b)=join' (e a) (e b)) {y : α} {s:Nat} {d:List α} (h:Run inv meet join y s d) :Run inv' meet' join' (e y) s (d.map e):=by
 induction h using Run.fold with
 | done=>exact Run.done
 | perm t _ ih=>exact Run.perm (t.map e) ih
 | @one s a rest neg save _ ih =>
  have c:((if neg then inv a else a)::qk save a rest).map e
    = (if neg then inv' (e a) else e a)::qk save (e a) (rest.map e):=by
   cases neg<;>simp [wd,g]
  rw [c] at ih;exact Run.one neg save ih
 | @two s a b rest conj ka kb _ ih =>
  have c:((if conj then meet a b else join a b)::qk ka a (qk kb b rest)).map e
    = (if conj then meet' (e a) (e b) else join' (e a) (e b))
     :: qk ka (e a) (qk kb (e b) (rest.map e)):=by
   cases conj<;>simp [wd,i,j]
  rw [c] at ih;exact Run.two conj ka kb ih
def wn (n:Nat) (gs:U) (o a:Nat):Prop:=
 ∀ P:Nat->Prop,P o ->
  (∀ q g,gs[q]?=some g->P (n+q)->∀ u∈g.inputs,P u)->P a
lemma it (n:Nat) (gs:U) (o:Nat):wn n gs o o:=
 fun _ ho _=>ho
lemma iu {n:Nat} {gs:U} {o q u:Nat} {g:G} (b:gs[q]?=some g) (c:wn n gs o (n+q)) (d:u∈g.inputs) :wn n gs o u:=
 fun P ho hs=>hs q g b (c P ho hs) u d
lemma xk {n:Nat} {gs:U} {o a:Nat} (h:wn n gs o a) :a=o\/∃ q g,gs[q]?=some g/\a∈g.inputs/\wn n gs o (n+q):=by
 apply h (fun x=>x=o\/∃ q g,gs[q]?=some g/\x∈g.inputs/\wn n gs o (n+q))
 . exact Or.inl rfl
 . intro q g b c u d;refine Or.inr ⟨q,g,b,d,?_⟩
   rcases c with rfl|⟨q',g',b',e',i'⟩
   . exact it n gs (n+q)
   . exact iu b' i' e'
def m6 (n:Nat) (gs:U) (o p a:Nat):Prop:=
 a=o\/∃ q,p<=q/\∃ g,gs[q]?=some g/\a∈g.inputs/\wn n gs o (n+q)
open Classical in
noncomputable def liveList (gs:U) (n o p:Nat):M:=
 (range (n+p)).filter (fun a=>decide (m6 n gs o p a))
lemma qw (gs:U) (n o p a:Nat) :a∈liveList gs n o p↔a < n+p/\m6 n gs o p a:=by simp [liveList]
lemma vy (gs:U) (n o p:Nat):(liveList gs n o p).Nodup:=
 List.Nodup.filter _ List.nodup_range
abbrev invF {n:Nat}:u7 n->u7 n:=fun a x=>!a x
abbrev meetF {n:Nat}:u7 n->u7 n->u7 n:=fun a b x=>a x&&b x
abbrev joinF {n:Nat}:u7 n->u7 n->u7 n:=fun a b x=>a x||b x
lemma ip (n:Nat) (gs:U) (o:Nat) (hcl:yq n gs) (p:Nat) (g:G) (b:gs[p]?=some g) (i:wn n gs o (n+p)) (a:Nat) :a∈liveList gs n o (p+1) ↔ a=n+p\/(a∈liveList gs n o p/\(a∈g.inputs->m6 n gs o (p+1) a)):=by
 rw [qw,qw];constructor
 . rintro ⟨j,e⟩
   by_cases s:a=n+p
   . exact Or.inl s
   . refine Or.inr ⟨⟨by omega,?_⟩,fun _=>e⟩
     rcases e with h|⟨q,t,g',b',c,d⟩
     . exact Or.inl h
     . exact Or.inr ⟨q,by omega,g',b',c,d⟩
 . rintro (rfl|⟨⟨j,e⟩,u⟩)
   . refine ⟨by omega,?_⟩
     rcases xk i with h|⟨q,g',b',c,d⟩
     . exact Or.inl h
     . refine Or.inr ⟨q,?_,g',b',c,d⟩
       have:=j2 (hcl q g' b') _ c
       omega
   . refine ⟨by omega,?_⟩
     rcases e with h|⟨q,t,g',b',c,d⟩
     . exact Or.inl h
     . by_cases v:q=p
       . subst v;rw [b] at b';cases b'
         exact u c
       . exact Or.inr ⟨q,by omega,g',b',c,d⟩
def d4 {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)):u7 n:=
 fun x=>A.any (fun a=>x a)||E.any (fun e=>x e.1&&x e.2)
def j9 {α:Type} [BEq α]:List α->List α->List α
 | [],acc=>acc.reverse
 | a::t,acc=>if acc.contains a then j9 t acc else j9 t (a::acc)
def az {α:Type} [BEq α] (l:List α):List α:=j9 l []
lemma ww {α:Type} [DecidableEq α]:∀ (l b:List α) (x : α),
  x∈j9 l b↔x∈l\/x∈b
 | [],b,x=>by simp [j9]
 | a::t,b,x=>by
  simp only [j9]
  by_cases h:b.contains a=true
  . simp only [h,↓reduceIte,ww,lMM]
    have e:a∈b:=by simpa using h
    constructor
    . rintro (c|d)
      . exact Or.inl (Or.inr c)
      . exact Or.inr d
    . rintro ((rfl|c)|d)
      . exact Or.inr e
      . exact Or.inl c
      . exact Or.inr d
  . simp only [h,bFT,↓reduceIte,ww,lMM]
    tauto
lemma fv {α:Type} [DecidableEq α] (l:List α) (x : α) :x∈az l↔x∈l:=by simpa [az] using ww l [] x
def eg {n:Nat} (A:List (Fin n)) (p:Fin n):List (Fin n):=
 A.filter (·!=p)
def g9 {n:Nat} (E:List (Fin n×Fin n)) (p:Fin n):List (Fin n×Fin n):=
 E.filter (fun e=>e.1!=p&&e.2!=p)
def bk {n:Nat} (E:List (Fin n×Fin n)) (p:Fin n):List (Fin n):=
 E.filterMap (fun e=>if e.1==p then some e.2 else if e.2==p then some e.1 else none)
def j6 {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n):List (Fin n):=
 az (A++bk E p)
def ef {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n):List (Fin n×Fin n):=
 let A1:=j6 A E p
 E.filter (fun e=>e.1!=p&&e.2!=p&&!A1.contains e.1&&!A1.contains e.2)
def f4 {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n):Q:=
 A.contains p ||
  (E.all (fun e=>e.1!=e.2) &&
   E.any (fun e=>(e.1==p&&!A.contains e.2)||(e.2==p&&!A.contains e.1)))
def un {n k:Nat} (E:List (Fin n×Fin n)) (Eb:List (Fin k×Fin k)) (π:Fin n->Fin k):Q:=
 E.all (fun e=>Eb.any (fun e' => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1))) &&
 Eb.all (fun e' => E.any (fun e=>(π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1)))
lemma kv {n:Nat} (A:List (Fin n)) (b:A.Nodup) :∀ s:Nat,HCS n (d4 A []) s->A.length - 1<=s:=by
 intro s h;have c:=nj n (d4 A []) A.toFinset (by
  intro i d;have e:i∈A:=List.mem_toFinset.1 d;refine ⟨fun _=>false,?_⟩
  have g:d4 A [] (fun _=>false)=false:=by simp [d4]
  have j:d4 A [] (update (fun _=>false) i true)=true:=by simp only [d4,List.any_nil,Bool.or_false,lAN];exact ⟨i,e,by simp⟩
  simpa [g,j]) s h
 rw [List.toFinset_card_of_nodup b] at c;omega
lemma ch {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (h:(!A.isEmpty||!E.isEmpty)=true) :∃ x y:F n,d4 A E x≠d4 A E y:=by
 refine ⟨fun _=>false,fun _=>true,?_⟩
 have b:d4 A E (fun _=>false)=false:=by simp [d4]
 have c:d4 A E (fun _=>true)=true:=by
  cases A with
  | cons a t=>simp [d4]
  | nil =>
   cases E with
   | nil=>simp at h
   | cons e t=>simp [d4]
 rw [b,c];decide
lemma bd {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n) (h:f4 A E p=true) :∃ x:F n,d4 A E (update x p (!x p))≠d4 A E x:=by
 simp only [f4,bOT,bAT,List.contains_eq_mem,decide_eq_true_eq,
   lAL,lAN,bne_iff_ne,beq_iff_eq,bNT,
   decide_eq_false_iff_not] at h
 rcases h with y|⟨g,⟨e,j,⟨rfl,s⟩|⟨rfl,s⟩⟩⟩
 . refine ⟨fun _=>false,?_⟩
   have c:d4 A E (fun _=>false)=false:=by simp [d4]
   have b:d4 A E (update (fun _=>false) p true)=true:=by simp only [d4,bOT,lAN];exact Or.inl ⟨p,y,by simp⟩
   simpa [c,b]
 . have d:e.1≠e.2:=g e j;refine ⟨fun i=>decide (i=e.2),?_⟩
   have c:d4 A E (fun i=>decide (i=e.2))=false:=by
    simp only [d4,bOF,List.any_eq_false,decide_eq_true_eq,bAT];refine ⟨fun a t u=>s (u ▸ t),fun e' v' => ?_⟩
    intro ⟨b,w⟩;exact g e' v' (b.trans w.symm)
   have b:d4 A E (update (fun i=>decide (i=e.2)) e.1 (!decide (e.1=e.2)))=true:=by
    simp only [d4,bOT,lAN,bAT];refine Or.inr ⟨e,j,?_,?_⟩
    . simp [d]
    . simp [fUN (Ne.symm d)]
   rw [c,b];decide
 . have d:e.1≠e.2:=g e j;refine ⟨fun i=>decide (i=e.1),?_⟩
   have c:d4 A E (fun i=>decide (i=e.1))=false:=by
    simp only [d4,bOF,List.any_eq_false,decide_eq_true_eq,bAT];refine ⟨fun a t u=>s (u ▸ t),fun e' v' => ?_⟩
    intro ⟨b,w⟩;exact g e' v' (b.trans w.symm)
   have b:d4 A E (update (fun i=>decide (i=e.1)) e.2 (!decide (e.2=e.1)))=true:=by
    simp only [d4,bOT,lAN,bAT];refine Or.inr ⟨e,j,?_,?_⟩
    . simp [fUN d]
    . simp [Ne.symm d]
   rw [c,b];decide
lemma zo {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n) :(fun x=>d4 A E (update x p false))=d4 (eg A p) (g9 E p):=by
 funext x;apply Bool.eq_iff_iff.2
 simp only [d4,eg,g9,bOT,lAN,List.mem_filter,
   bAT,bne_iff_ne]
 constructor
 . rintro (⟨a,j,i⟩|⟨e,s,b,c⟩)
   . by_cases d:a=p
     . subst d;simp at i
     . exact Or.inl ⟨a,⟨j,d⟩,by simpa [fUN d] using i⟩
   . by_cases g:e.1=p
     . rw [g,fUS] at b;cases b
     . by_cases h:e.2=p
       . rw [h,fUS] at c;cases c
       . exact Or.inr ⟨e,⟨s,g,h⟩,
          by simpa [fUN g] using b,
          by simpa [fUN h] using c⟩
 . rintro (⟨a,⟨j,d⟩,i⟩|⟨e,⟨s,g,h⟩,b,c⟩)
   . exact Or.inl ⟨a,j,by simpa [fUN d] using i⟩
   . exact Or.inr ⟨e,s,
       by simpa [fUN g] using b,
       by simpa [fUN h] using c⟩
lemma bg {n:Nat} (E:List (Fin n×Fin n)) (p q:Fin n) :q∈bk E p↔∃ e∈E,(e.1=p/\e.2=q)\/(e.1≠p/\e.2=p/\e.1=q):=by
 simp only [bk,List.mem_filterMap,beq_iff_eq];constructor
 . rintro ⟨e,c,h⟩
   split_ifs at h with b d
   . cases h;exact ⟨e,c,Or.inl ⟨b,rfl⟩⟩
   . cases h;exact ⟨e,c,Or.inr ⟨b,d,rfl⟩⟩
 . rintro ⟨e,c,⟨b,d⟩|⟨b,d,g⟩⟩
   . exact ⟨e,c,by rw [if_pos b,d]⟩
   . exact ⟨e,c,by rw [if_neg b,if_pos d,g]⟩
lemma kx {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n) (h3 : !A.contains p=true) (h4:E.all (fun e=>e.1!=e.2)=true) :(fun x=>d4 A E (update x p true))=d4 (j6 A E p) (ef A E p):=by
 have w:p ∉ A:=by simpa [List.contains_eq_mem] using h3
 have y:∀ e∈E,e.1≠e.2:=by simpa [lAL,bne_iff_ne] using h4
 funext x;apply Bool.eq_iff_iff.2
 simp only [d4,ef,bOT,lAN,bAT,List.mem_filter,
   bne_iff_ne,bNT,List.contains_eq_mem,decide_eq_false_iff_not]
 constructor
 . rintro (⟨a,i,j⟩|⟨e,b,g,s⟩)
   . have v:a≠p:=fun h=>w (h ▸ i)
     refine Or.inl ⟨a,?_,by simpa [fUN v] using j⟩
     rw [j6,fv];exact List.mem_append_left _ i
   . by_cases d:e.1=p
     . have c:e.2≠p:=fun h=>y e b (d.trans h.symm)
       refine Or.inl ⟨e.2,?_,by simpa [fUN c] using s⟩
       rw [j6,fv];exact List.mem_append_right _ ((bg E p e.2).2 ⟨e,b,Or.inl ⟨d,rfl⟩⟩)
     . by_cases c:e.2=p
       . refine Or.inl ⟨e.1,?_,by simpa [fUN d] using g⟩
         rw [j6,fv];exact List.mem_append_right _ ((bg E p e.1).2 ⟨e,b,Or.inr ⟨d,c,rfl⟩⟩)
       . have t:x e.1=true:=by simpa [fUN d] using g
         have u:x e.2=true:=by simpa [fUN c] using s
         by_cases m1:e.1∈j6 A E p
         . exact Or.inl ⟨e.1,m1,t⟩
         . by_cases z:e.2∈j6 A E p
           . exact Or.inl ⟨e.2,z,u⟩
           . exact Or.inr ⟨e,⟨b,⟨⟨d,c⟩,m1⟩,z⟩,t,u⟩
 . rintro (⟨a,i,j⟩|⟨e,⟨b,⟨⟨d,c⟩,_⟩,_⟩,t,u⟩)
   . rw [j6,fv,lMAp] at i;rcases i with h0|h5
     . have v:a≠p:=fun h=>w (h ▸ h0)
       exact Or.inl ⟨a,h0,by simpa [fUN v] using j⟩
     . obtain ⟨e,b,⟨g,rfl⟩|⟨g,s,rfl⟩⟩:=(bg E p a).1 h5
       . have c:e.2≠p:=fun h=>y e b (g.trans h.symm)
         exact Or.inr ⟨e,b,by simp [g],by simpa [fUN c] using j⟩
       . exact Or.inr ⟨e,b,by simpa [fUN g] using j,by simp [s]⟩
   . exact Or.inr ⟨e,b,
       by simpa [fUN d] using t,
       by simpa [fUN c] using u⟩
lemma jq {n:Nat} (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1)×Fin (n+1))) (k:Nat) (d:f4 A E p=true) (e:A'=eg A p) (g:E'=g9 E p) (b:(!A'.isEmpty||!E'.isEmpty)=true) (i:∀ s,HCS (n+1) (d4 A' E') s->k<=s) :∀ s,HCS (n+1) (d4 A E) s->k+1<=s:=by
 intro s h;have c:(fun x=>d4 A E (update x p false))=d4 A' E':=by rw [e,g];exact zo A E p
 have b':∃ x y,d4 A E (update x p false)≠d4 A E (update y p false):=by obtain ⟨x,y,j⟩:=ch A' E' b;exact ⟨x,y,by simpa [congrFun c] using j⟩
 obtain ⟨s',hs',h'⟩:=xj n (d4 A E) p false s (bd A E p d) b' h;rw [c] at h'
 have:=i s' h'
 omega
lemma js {n:Nat} (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1)×Fin (n+1))) (k:Nat) (d:f4 A E p=true) (g : !A.contains p=true) (i:E.all (fun e=>e.1!=e.2)=true) (j:A'=j6 A E p) (t:E'=ef A E p) (b:(!A'.isEmpty||!E'.isEmpty)=true) (u:∀ s,HCS (n+1) (d4 A' E') s->k<=s) :∀ s,HCS (n+1) (d4 A E) s->k+1<=s:=by
 intro s h;have c:(fun x=>d4 A E (update x p true))=d4 A' E':=by rw [j,t];exact kx A E p g i
 have b':∃ x y,d4 A E (update x p true)≠d4 A E (update y p true):=by obtain ⟨x,y,v⟩:=ch A' E' b;exact ⟨x,y,by simpa [congrFun c] using v⟩
 obtain ⟨s',hs',h'⟩:=xj n (d4 A E) p true s (bd A E p d) b' h;rw [c] at h'
 have:=u s' h'
 omega
lemma lj {n:Nat} (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (p:Fin (n+1)) (A0:List (Fin (n+1))) (E0:List (Fin (n+1)×Fin (n+1))) (A1:List (Fin (n+1))) (E1:List (Fin (n+1)×Fin (n+1))) (k:Nat) (i:f4 A E p=true) (j : !A.contains p=true) (t:E.all (fun e=>e.1!=e.2)=true) (u:A0=eg A p) (v:E0=g9 E p) (w:A1=j6 A E p) (z:E1=ef A E p) (h0:(!A0.isEmpty||!E0.isEmpty)=true) (h1:(!A1.isEmpty||!E1.isEmpty)=true) (h2:∀ s,HCS (n+1) (d4 A0 E0) s->k<=s) (h3:∀ s,HCS (n+1) (d4 A1 E1) s->k<=s) :∀ s,HCS (n+1) (d4 A E) s->k+2<=s:=by
 intro s h;have d:(fun x=>d4 A E (update x p false))=d4 A0 E0:=by rw [u,v];exact zo A E p
 have g:(fun x=>d4 A E (update x p true))=d4 A1 E1:=by rw [w,z];exact kx A E p j t
 have h4:∀ b:Q,∃ x y,d4 A E (update x p b)≠d4 A E (update y p b):=by
  intro b;cases b with
  | false => obtain ⟨x,y,c⟩:=ch A0 E0 h0;exact ⟨x,y,by simpa [congrFun d] using c⟩
  | true => obtain ⟨x,y,c⟩:=ch A1 E1 h1;exact ⟨x,y,by simpa [congrFun g] using c⟩
 obtain ⟨b,s',hs',h'⟩:=lv n (d4 A E) p s (bd A E p i) h4 h;cases b with
 | false=>rw [d] at h';have:=h2 s' h';omega
 | true=>rw [g] at h';have:=h3 s' h';omega
lemma iz {n k:Nat} (E:List (Fin n×Fin n)) (Eb:List (Fin k×Fin k)) (π:Fin n->Fin k) (h:un E Eb π=true) :(fun y:F k=>d4 [] E (y ∘ π))=d4 [] Eb:=by
 simp only [un,bAT,lAL,lAN,
   bOT,beq_iff_eq] at h
 obtain ⟨i,j⟩:=h;funext y;apply Bool.eq_iff_iff.2
 simp only [d4,List.any_nil,Bool.false_or,lAN,bAT,Function.comp_apply];constructor
 . rintro ⟨e,c,d,g⟩
   obtain ⟨e',c',⟨a,b⟩|⟨a,b⟩⟩:=i e c
   . exact ⟨e',c',a ▸ d,b ▸ g⟩
   . exact ⟨e',c',b ▸ g,a ▸ d⟩
 . rintro ⟨e',c',d,g⟩
   obtain ⟨e,c,⟨a,b⟩|⟨a,b⟩⟩:=j e' c'
   . exact ⟨e,c,a.symm ▸ d,b.symm ▸ g⟩
   . exact ⟨e,c,a.symm ▸ g,b.symm ▸ d⟩
lemma jf {n k e3:Nat} (E:List (Fin n×Fin n)) (Eb:List (Fin k×Fin k)) (π:Fin n->Fin k) (b:un E Eb π=true) (c:∀ s:Nat,HCS k (d4 [] Eb) s->e3<=s) :∀ s:Nat,HCS n (d4 [] E) s->e3<=s:=by intro s h;have h':=yn π (d4 [] E) s h;rw [iz E Eb π b] at h';exact c s h'
lemma tn {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :xs.length<=s+1:=by
 induction h using Run.fold with
 | done=>simp
 | perm b _ ih=>rwa [<- b.length_eq]
 | one neg save h ih=>cases save<;>simp_all [qk]<;>omega
 | two conj ka kb h ih=>cases ka<;>cases kb<;>simp_all [qk]<;>omega
lemma w5 {m:Nat} {g:G} (h:mv m g):tq g:=by
 rcases h with ⟨c,j,_,d⟩|⟨c,j,k,_,_,d⟩
 . exact ⟨⟨by simp [c],by simp [d]⟩,fun _=>by simp [d]⟩
 . refine ⟨⟨?_,by simp [d]⟩,fun e => ?_⟩
   . rcases c with b|b<;>simp [b]
   . rcases c with b|b<;>rw [b] at e<;>cases e
lemma ja {n:Nat} {gs:U} (h:yq n gs):∀ g∈gs,tq g:=by intro g b;obtain ⟨p,c,rfl⟩:=List.getElem_of_mem b;exact w5 (h p gs[p] (lGEQ c))
lemma lh {n:Nat} {gs:U} (h:yq n gs) (p:Nat):yq n (gs.take p):=by
 intro q g b;have c:q < (gs.take p).length:=(lGES.1 b).1;have d:q < p:=by simp at c;omega
 rw [List.getElem?_take_of_lt d] at b;exact h q g b
def cg (R:Nat->Prop) (n:Nat) (y:I) (w:I) (b:List e8×U):Prop:=
 b.1.length=w.length /\
 (∀ i:Nat,qn (n+b.2.length) (b.1.getD i (inl false))) /\
 (∀ i:Nat,R i->ze (q3 b.2 y) (b.1.getD i (inl false))=w.getD i false)
lemma kz (R:Nat->Prop) (n:Nat) (y:I) (hy:y.length=n) (gs:U) :∀ (w:I) (b:List e8×U),(∀ g∈gs,Ok g) -> (∀ q g,gs[q]?=some g->R (b.1.length+q)->∀ a∈g.inputs,R a) -> cg R n y w b -> cg R n y (q3 gs w) (u2 n gs b):=by
 induction gs with
 | nil=>intro w b _ _ h;exact h
 | cons g gs ih =>
  intro w b v x h;apply ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) (qa n b g)
    (fun g' hg' => v g' (lMCM _ hg'))
  . intro q g' hq z a e;have hlen:(qa n b g).1.length=b.1.length+1:=by simp [qa]
    rw [hlen] at z;exact x (q+1) g' (by simpa using hq) (by simpa [nAA,nAC 1 q] using z) a e
  . obtain ⟨hl,j,he⟩:=h;set w':=q3 b.2 y with hw'
    have u':w'.length=n+b.2.length:=by rw [hw',qu,hy]
    set h0:=g.inputs.map fun i=>b.1.getD i (inl false) with h1
    have h2:=v g List.mem_cons_self;have c:=kn g.op h2.1 w' h0 (by simpa [h1] using h2.2)
      (by
        intro s c;obtain ⟨a,_,rfl⟩:=lMp.1 c;rw [u'];exact j a)
    rw [u'] at c;set r:=qg g.op (n+b.2.length) h0 with hr
    have h3:q3 (b.2++r.1.toList) y=q3 r.1.toList w':=by rw [zd]
    obtain ⟨t,ht,_⟩:=y1 r.1.toList w';refine ⟨by simp [qa,hl],?_,?_⟩
    . intro i
      show qn (n+(b.2++r.1.toList).length) ((b.1++[r.2]).getD i (inl false))
      rw [lLA,<- nAA];by_cases d:i=b.1.length
      . subst d;rw [z0];exact c.1
      . rw [q8 _ _ _ _ d];exact km (by omega) _ (j i)
    . intro i hi
      show ze (q3 (b.2++r.1.toList) y) ((b.1++[r.2]).getD i (inl false))=_
      rw [h3];by_cases d:i=b.1.length
      . subst d;rw [z0,hl,z0,c.2];congr 1
        rw [h1,lMMp];apply lMCL
        intro a e;exact he a (x 0 g rfl (by simpa using hi) a e)
      . rw [q8 _ _ _ _ d,q8 _ _ _ _ (by omega)];rw [ht,jg _ _ _ (by rw [u'];exact j i)]
        exact he i hi
lemma y7 (n:Nat) (f:u7 n) (b d:U) (g:G) (o:Nat) (hcl:yq n (b++g::d)) (ho:o < n+(b++g::d).length) (hev:∀ x,e3 (b++g::d) n o x=f x) (h9:∃ y y':F n,f y≠f y') (st:e8) (b1:qn (n+b.length) st) (hb:(∀ x,ze (q3 b (ofFn x)) st=e3 (b++g::d) n (n+b.length) x) \/ ¬ wn n (b++g::d) o (n+b.length)) :∃ gs' o',yq n gs'/\gs'.length<=b.length+d.length /\ o' < n+gs'.length/\∀ x,e3 gs' n o' x=f x:=by
 set gs:=b++g::d with h2
 set p:=b.length with z
 set h:List e8×U:=(vi (n+p)++[st],b) with t
 set s:=u2 n d h with hc
 have h3:∀ g'∈d,Ok g':=fun g' hg' =>
  (ja hcl g' (List.mem_append_right _ (lMCM _ hg'))).1
 have hd:yq n b:=by
  have:b=gs.take p:=by simp [h2,z]
  rw [this];exact lh hcl p
 have h4:∀ i,qn (n+h.2.length) (h.1.getD i (inl false)):=by
  intro i;simp only [t,z];by_cases h5:i=n+b.length
  . subst h5;rw [z2 _ _ _ _ (by simp [vi])];exact b1
  . rw [q8 _ _ _ _ (by simp [vi];omega)]
    by_cases u:i < n+b.length
    . simp [vi,u,qn]
    . rw [lGD _ _ (by simp [vi];omega)];trivial
 have hcl':yq n s.2:=bh n d h h3 h4 hd;have hlen':s.2.length<=b.length+d.length:=by simpa [hc,t] using cm n d h
 have h0:∀ x:F n,
    qn (n+s.2.length) (s.1.getD o (inl false)) /\
    ze (q3 s.2 (ofFn x)) (s.1.getD o (inl false))=f x:=by
  intro x;have h6:q3 gs (ofFn x)=q3 d (q3 (b++[g]) (ofFn x)):=by
    have:gs=(b++[g])++d:=by simp [h2]
    rw [this,zd]
  have x2:(q3 (b++[g]) (ofFn x)).length=n+p+1:=by rw [qu];simp [z];omega
  have x3:∀ i < n+p,(q3 (b++[g]) (ofFn x)).getD i false =
      (q3 b (ofFn x)).getD i false:=by
    intro i hi;rw [zd,ve _ _ _ (by rw [qu];simp;omega)]
  rcases hb with he|hf
  . have h7:ej n (ofFn x) (q3 (b++[g]) (ofFn x)) h:=by
      refine ⟨by simp [t,vi,x2],?_⟩
      intro i;refine ⟨h4 i,?_⟩
      simp only [t];by_cases h5:i=n+p
      . subst h5;rw [z2 _ _ _ _ (by simp [vi])];have v:=he x;unfold e3 at v;rw [h6,ve _ _ _ (by omega)] at v;exact v
      . rw [q8 _ _ _ _ (by simp [vi];omega)]
        by_cases u:i < n+p
        . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,u,↓reduceDIte,
            Option.getD_some,ze]
          exact (x3 i u).symm
        . rw [lGD _ _ (by simp [vi];omega),
             lGD _ _ (by omega)];rfl
    have w:=j7 n (ofFn x) (by simp) d _ h h3 h7;rw [<- h6] at w;have v:=w.2 o;exact ⟨v.1,v.2.trans (hev x)⟩
  . have h7:cg (wn n gs o) n (ofFn x) (q3 (b++[g]) (ofFn x)) h:=by
      refine ⟨by simp [t,vi,x2],h4,?_⟩
      intro i hi;simp only [t];have a1:i≠n+p:=fun e=>hf (e ▸ hi)
      rw [q8 _ _ _ _ (by simp [vi];omega)]
      by_cases u:i < n+p
      . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,u,↓reduceDIte,
          Option.getD_some,ze]
        exact (x3 i u).symm
      . rw [lGD _ _ (by simp [vi];omega),
            lGD _ _ (by omega)];rfl
    have hR:∀ q g',d[q]?=some g'->wn n gs o (h.1.length+q)->∀ a∈g'.inputs,wn n gs o a:=by
      intro q g' hq a2 a ha;have hh:gs[p+1+q]?=some g':=by
        have:gs=(b++[g])++d:=by simp [h2]
        rw [this,List.getElem?_append_right (by simp [z])];simpa [z,Nat.add_sub_cancel_left] using hq
      have hk:h.1.length=n+p+1:=by simp [t,vi]
      rw [hk] at a2;exact iu hh (by simpa [nAA] using a2) ha
    have w:=kz (wn n gs o) n (ofFn x) (by simp) d _ h h3 hR h7;rw [<- h6] at w;exact ⟨w.2.1 o,(w.2.2 o (it n gs o)).trans (hev x)⟩
 cases h8:s.1.getD o (inl false) with
 | inl c =>
  exfalso;obtain ⟨y,y',a1⟩:=h9;apply a1
  have e1:=(h0 y).2;have e2:=(h0 y').2;rw [h8] at e1 e2;exact e1.symm.trans e2
 | inr j =>
  obtain ⟨y,_,_⟩:=h9;have hj:=(h0 y).1;rw [h8] at hj;refine ⟨s.2,j,hcl',hlen',hj,?_⟩
  intro x;have e:=(h0 x).2;rw [h8] at e;exact e
structure MinClean (n:Nat) (f:u7 n) (gs:U) (o:Nat):Prop where
 hcl:yq n gs
 ho:o < n+gs.length
 hev:∀ x,e3 gs n o x=f x
 hreach:∀ p < gs.length,wn n gs o (n+p)
 hncG:∀ p < gs.length,∀ c:Q,e3 gs n (n+p)≠fun _=>c
 hndup:∀ p < gs.length,∀ u < n+p,e3 gs n (n+p)≠e3 gs n u
open Classical in
lemma fr (n:Nat) (f:u7 n) (s:Nat) (b:∃ y y':F n,f y≠f y') (h:HCS n f s) :∃ gs o,MinClean n f gs o/\gs.length<=s:=by
 have v:∃ k,∃ gs o,yq n gs/\gs.length=k/\o < n+gs.length/\∀ x,e3 gs n o x=f x:=by obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=xn n f s b h;exact ⟨gs.length,gs,o,hcl,rfl,ho,hev⟩
 set k:=Nat.find v with hk
 obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=Nat.find_spec v;have hle:k<=s:=by obtain ⟨ow,o0,z,h0,ho0,h1⟩:=xn n f s b h;exact le_trans (Nat.find_min' v ⟨ow,o0,z,rfl,ho0,h1⟩) h0
 have w:∀ gs' o',yq n gs'->o' < n+gs'.length->(∀ x,e3 gs' n o' x=f x)->gs.length<=gs'.length:=by intro gs' o' hcl' ho' hev';rw [hlen];exact Nat.find_min' v ⟨gs',o',hcl',rfl,ho',hev'⟩
 refine ⟨gs,o,⟨hcl,ho,hev,?_,?_,?_⟩,by omega⟩
 . intro p d;by_contra h2;obtain ⟨g0,e⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],lGEQ d⟩;obtain ⟨g,i,j,t⟩:=aw gs p g0 e;subst t;subst j;obtain ⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f g i g0 o hcl ho hev b (inl false) trivial (Or.inr h2)
   have:=w gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p d c h3;obtain ⟨g0,e⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],lGEQ d⟩;obtain ⟨g,i,j,t⟩:=aw gs p g0 e;subst t;subst j;obtain ⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f g i g0 o hcl ho hev b (inl c) trivial
     (Or.inl fun x=>by rw [h3];rfl)
   have:=w gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p d u hu h4;obtain ⟨g0,e⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],lGEQ d⟩;obtain ⟨g,i,j,t⟩:=aw gs p g0 e;subst t;subst j;obtain ⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f g i g0 o hcl ho hev b (inr u) hu
     (Or.inl fun x=>by
      rw [h4];unfold e3;rw [zd,ve _ _ _ (by rw [qu];simp;omega)];rfl)
   have:=w gs' o' hcl' ho' hev'
   simp at this;omega
def wf (n:Nat) (v:Fin n):List e8:=
 ofFn fun i:Fin n=>if i=v then inl false else inr (i:Nat)
lemma re (n:Nat) (v:Fin n) (x:F n) :ej n (ofFn x) (ofFn (update x v false)) (wf n v,[]):=by
 refine ⟨by simp [wf],?_⟩
 intro i;by_cases b:i < n
 . by_cases c:(⟨i,b⟩:Fin n)=v
   . subst c;simp [wf,b,qn,ze]
   . simp [wf,b,c,qn,ze,q3,fUN c]
 . rw [lGD _ _ (by simp [wf];omega),
      lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
lemma wz (n:Nat) (f:u7 n) (gs:U) (o:Nat) (v:Fin n) (B:Nat) (hcl:yq n gs) (hev:∀ x,e3 gs n o x=f x) (i:∃ x y:F n,f (update x v false)≠f (update y v false)) (t:∀ s',HCS n (fun x=>f (update x v false)) s'->B<=s') :(∀ c,(u2 n gs (wf n v,[])).1.getD o (inl false)≠inl c) /\ B<=(u2 n gs (wf n v,[])).2.length:=by
 set b:=u2 n gs (wf n v,[]) with hacc
 have u:∀ x,ej n (ofFn x) (q3 gs (ofFn (update x v false))) b:=
  fun x=>j7 n _ (by simp) gs _ _ (fun g w=>(ja hcl g w).1) (re n v x)
 have d:∀ x,ze (q3 b.2 (ofFn x)) (b.1.getD o (inl false))
   = f (update x v false):=fun x=>((u x).2 o).2.trans (hev _)
 have e:∀ c,b.1.getD o (inl false)≠inl c:=by
  intro c z;obtain ⟨x,y,h0⟩:=i;apply h0
  rw [<- d x,<- d y,z];rfl
 refine ⟨e,?_⟩
 cases h:b.1.getD o (inl false) with
 | inl c=>exact absurd h (e c)
 | inr j =>
  apply t b.2.length
  refine ⟨⟨b.2,j⟩,mb n gs _ (by simp),le_refl _,?_⟩
  intro x;have:=d x;rw [h] at this;exact this
lemma k3 (n u w:Nat) (gs:U):∀ b:List e8×U, (∀ g∈gs,tq g)->u < b.1.length->w < b.1.length -> (∃ cu,b.1.getD u (inl false)=inl cu) -> (∃ cw,b.1.getD w (inl false)=inl cw) -> (∃ g₁∈gs,u∈g₁.inputs) -> (∃ g₂∈gs,w∈g₂.inputs) -> (∀ g∈gs,¬ (u∈g.inputs/\w∈g.inputs)) -> (u2 n gs b).2.length+2<=b.2.length+gs.length:=by
 induction gs with
 | nil=>intro b _ _ _ _ _ y _ _;obtain ⟨g,c,_⟩:=y;simp at c
 | cons g gs ih =>
  intro b h5 s t d e v x h6;rw [k4,lLC];have h7:tq g:=h5 g List.mem_cons_self;have h4:∀ g'∈gs,tq g':=fun g' c' => h5 g' (lMCM _ c')
  by_cases z:u∈g.inputs
  . have h3:w ∉ g.inputs:=fun h=>h6 g List.mem_cons_self ⟨z,h⟩
    obtain ⟨cu,d⟩:=d;have h0:=vs n b g h7 u z cu d;have x':∃ g'∈gs,w∈g'.inputs:=by
      obtain ⟨g',c',t'⟩:=x;rcases lMM.1 c' with rfl|j
      . exact absurd t' h3
      . exact ⟨g',j,t'⟩
    have y:=zt n w gs (qa n b g) h4 (by simp [qa];omega)
      (by obtain ⟨cw,e⟩:=e;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact e⟩)
      x'
    omega
  . by_cases h3:w∈g.inputs
    . obtain ⟨cw,e⟩:=e;have h0:=vs n b g h7 w h3 cw e;have v':∃ g'∈gs,u∈g'.inputs:=by
        obtain ⟨g',c',s'⟩:=v;rcases lMM.1 c' with rfl|j
        . exact absurd s' z
        . exact ⟨g',j,s'⟩
      have y:=zt n u gs (qa n b g) h4 (by simp [qa];omega)
        (by obtain ⟨cu,d⟩:=d;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact d⟩)
        v'
      omega
    . have v':∃ g'∈gs,u∈g'.inputs:=by
        obtain ⟨g',c',s'⟩:=v;rcases lMM.1 c' with rfl|j
        . exact absurd s' z
        . exact ⟨g',j,s'⟩
      have x':∃ g'∈gs,w∈g'.inputs:=by
        obtain ⟨g',c',t'⟩:=x;rcases lMM.1 c' with rfl|j
        . exact absurd t' h3
        . exact ⟨g',j,t'⟩
      have y:=ih (qa n b g) h4 (by simp [qa];omega) (by simp [qa];omega)
        (by obtain ⟨cu,d⟩:=d;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact d⟩)
        (by obtain ⟨cw,e⟩:=e;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact e⟩)
        v' x' (fun g' c' => h6 g' (lMCM _ c'))
      have h2:(qa n b g).2.length<=b.2.length+1:=by
        simp only [qa,lLA]
        have:=y2 (qg g.op (n+b.2.length)
          (g.inputs.map fun i=>b.1.getD i (inl false))).1
        omega
      omega
inductive TagRun {α:Type} (inv : α->α) (meet join : α->α->α) (zero one goal : α) :
  Nat->List (α×Nat)->Prop where
 | done (tg:Nat):TagRun inv meet join zero one goal 0 [(goal,tg)]
 | perm {s xs zs}:List.Perm xs zs ->
   TagRun inv meet join zero one goal s xs ->
   TagRun inv meet join zero one goal s zs
 | uNot {s a ta r} (save:Q) :
   ta≠1->ta≠2->(ta=3->save=false) ->
   inv a≠zero->inv a≠one->inv a≠a->(∀ x∈r,x.1≠inv a) ->
   TagRun inv meet join zero one goal s
    ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
   TagRun inv meet join zero one goal (s+1) ((a,ta)::r)
 | bOr {s a ta b tb r} (ka kb:Q) :
   ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
   join a b≠zero->join a b≠one ->
   join a b≠a->join a b≠b->(∀ x∈r,x.1≠join a b) ->
   TagRun inv meet join zero one goal s
    ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
   TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
 | bAnd {s a ta b tb r} (ka kb:Q) :
   ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
   meet a b≠zero->meet a b≠one ->
   meet a b≠a->meet a b≠b->(∀ x∈r,x.1≠meet a b) ->
   TagRun inv meet join zero one goal s
    ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
   TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
lemma TagRun.toRun {α:Type} {inv : α->α} {meet join : α->α->α} {zero one c : α} {s:Nat} {d:List (α×Nat)} (h:TagRun inv meet join zero one c s d) :Run inv meet join c s (d.map Prod.fst):=by
 induction h with
 | done _=>exact Run.done
 | perm g _ ih=>exact Run.perm (g.map Prod.fst) ih
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
  have e:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map Prod.fst)
    = (if true then inv a else a)::qk save a (r.map Prod.fst):=by
   cases save<;>simp [qk]
  rw [e] at ih;exact Run.one true save ih
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map Prod.fst)
    = (if false then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
   cases ka<;>cases kb<;>simp [qk]
  rw [e] at ih;exact Run.two false ka kb ih
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map Prod.fst)
    = (if true then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
   cases ka<;>cases kb<;>simp [qk]
  rw [e] at ih;exact Run.two true ka kb ih
lemma TagRun.len_le {α:Type} {inv : α->α} {meet join : α->α->α} {zero one c : α} {s:Nat} {b:List (α×Nat)} (h:TagRun inv meet join zero one c s b) :b.length<=s+1:=by
 have:=tn h.toRun
 simpa using this
lemma TagRun.map {α β:Type} (e : α->β) (c:Function.Injective e) {inv : α->α} {meet join : α->α->α} {zero one i : α} {inv' : β->β} {meet' join' : β->β->β} {zero' one' i' : β} (h0:e zero=zero') (h1:e one=one') (hg:e i=i') (j:∀ a,e (inv a)=inv' (e a)) (d:∀ a b,e (meet a b)=meet' (e a) (e b)) (g:∀ a b,e (join a b)=join' (e a) (e b)) {s:Nat} {ws:List (α×Nat)} (h:TagRun inv meet join zero one i s ws) :TagRun inv' meet' join' zero' one' i' s (ws.map fun p=>(e p.1,p.2)):=by
 induction h with
 | done tg=>rw [<- hg];exact TagRun.done tg
 | perm hp _ ih=>exact TagRun.perm (hp.map _) ih
 | @uNot s a ta r save t u v w z h2 h3 _ ih =>
  have e1:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map fun p=>(e p.1,p.2))
     = (inv' (e a),if ta=3 then 2 else 0)::qk save (e a,0) (r.map fun p=>(e p.1,p.2)):=by
    cases save<;>simp [qk,j]
  rw [e1] at ih;refine TagRun.uNot save t u v ?_ ?_ ?_ ?_ ih
  . rw [<- j,<- h0];exact fun h=>w (c h)
  . rw [<- j,<- h1];exact fun h=>z (c h)
  . rw [<- j];exact fun h=>h2 (c h)
  . intro x hx;obtain ⟨y,hy,rfl⟩:=lMp.1 hx;rw [<- j];exact fun h=>h3 y hy (c h)
 | @bOr s a ta b tb r ka kb t u v h4 w z h2 h5 h3 _ ih =>
  have e1:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fun p=>(e p.1,p.2))
     = (join' (e a) (e b),0)::qk ka (e a,if ta=3 then 1 else 0) (qk kb (e b,if tb=3 then 1 else 0) (r.map fun p=>(e p.1,p.2))):=by
    cases ka<;>cases kb<;>simp [qk,g]
  rw [e1] at ih;refine TagRun.bOr ka kb t u v h4 ?_ ?_ ?_ ?_ ?_ ih
  . rw [<- g,<- h0];exact fun h=>w (c h)
  . rw [<- g,<- h1];exact fun h=>z (c h)
  . rw [<- g];exact fun h=>h2 (c h)
  . rw [<- g];exact fun h=>h5 (c h)
  . intro x hx;obtain ⟨y,hy,rfl⟩:=lMp.1 hx;rw [<- g];exact fun h=>h3 y hy (c h)
 | @bAnd s a ta b tb r ka kb t u v h4 w z h2 h5 h3 _ ih =>
  have e1:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fun p=>(e p.1,p.2))
     = (meet' (e a) (e b),if ta=3\/tb=3 then 1 else 0)::qk ka (e a,0) (qk kb (e b,0) (r.map fun p=>(e p.1,p.2))):=by
    cases ka<;>cases kb<;>simp [qk,d]
  rw [e1] at ih;refine TagRun.bAnd ka kb t u v h4 ?_ ?_ ?_ ?_ ?_ ih
  . rw [<- d,<- h0];exact fun h=>w (c h)
  . rw [<- d,<- h1];exact fun h=>z (c h)
  . rw [<- d];exact fun h=>h2 (c h)
  . rw [<- d];exact fun h=>h5 (c h)
  . intro x hx;obtain ⟨y,hy,rfl⟩:=lMp.1 hx;rw [<- d];exact fun h=>h3 y hy (c h)
def v3 (n:Nat) (gs:U) (v:Fin n) (p:Nat):List e8×U:=
 u2 n (gs.take p) (wf n v,[])
lemma vb (n:Nat) (gs:U) (v:Fin n) (p:Nat) (b:p<=gs.length) :(v3 n gs v p).1.length=n+p:=by unfold v3;rw [fs];simp [wf,lLT,Nat.min_eq_left b]
lemma ax (n:Nat) (gs:U) (v:Fin n) (p:Nat) (g:G) (b:gs[p]?=some g) :v3 n gs v (p+1)=qa n (v3 n gs v p) g:=by unfold v3;have c:p < gs.length:=(lGES.1 b).1;have d:gs[p]=g:=(lGES.1 b).2;rw [List.take_succ_eq_append_getElem c,d,jz,k4];rfl
lemma zj (n:Nat) (gs:U) (v:Fin n) (p:Nat) :u2 n (gs.drop p) (v3 n gs v p)=u2 n gs (wf n v,[]):=by unfold v3;rw [<- jz,List.take_append_drop]
def yf (n:Nat) (gs:U) (f:u7 n) (p a b:Nat):Prop:=
 match b with
 | 0=>True
 | 1 => ∃ v:Fin n,
  (∃ x y,f (update x v false)≠f (update y v false)) /\
  (v3 n gs v p).1.getD a (inl false)=inl false /\
  (v3 n gs v p).2.length+(gs.drop p).length<=(u2 n (gs.drop p) (v3 n gs v p)).2.length+1
 | 2 => ∃ v:Fin n,
  (∃ x y,f (update x v false)≠f (update y v false)) /\
  (v3 n gs v p).1.getD a (inl false)=inl true /\
  (v3 n gs v p).2.length+(gs.drop p).length<=(u2 n (gs.drop p) (v3 n gs v p)).2.length+1
 | 3 => ∃ v:Fin n,
  (∃ x y,f (update x v false)≠f (update y v false)) /\
  (v3 n gs v p).1.getD a (inl false)=inl false /\
  (v3 n gs v p).2.length+(gs.drop p).length<=(u2 n (gs.drop p) (v3 n gs v p)).2.length+2
 | _=>False
lemma xx {n:Nat} {gs:U} {f:u7 n} {p a b:Nat} (h:yf n gs f p a b):b<=3:=by
 match b with
 | 0 | 1 | 2 | 3=>omega
 | _+4=>exact False.elim h
lemma vv {n:Nat} {gs:U} {f:u7 n} {p a j:Nat} {g:G} (s:gs[p]?=some g) (ha:a < n+p) (h:yf n gs f p a j) :yf n gs f (p+1) a j:=by
 have w:p < gs.length:=(lGES.1 s).1;have x:gs[p]=g:=(lGES.1 s).2;have y:gs.drop p=g::gs.drop (p+1):=by rw [List.drop_eq_getElem_cons w,x]
 have t:∀ v c B,
    (v3 n gs v p).1.getD a (inl false)=inl c ->
    (v3 n gs v p).2.length+(gs.drop p).length<=(u2 n (gs.drop p) (v3 n gs v p)).2.length+B ->
    (v3 n gs v (p+1)).1.getD a (inl false)=inl c /\
    (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length <=
     (u2 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
  intro v c B b d;have u:=ax n gs v p g s;have hfl:=vb n gs v p (by omega);constructor
  . rw [u];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact b
  . have z:u2 n (gs.drop (p+1)) (v3 n gs v (p+1))=u2 n (gs.drop p) (v3 n gs v p):=by
     rw [zj,zj]
    have hlen2:(v3 n gs v (p+1)).2.length<=(v3 n gs v p).2.length+1:=by
     rw [u];simp only [qa,lLA]
     have:=y2 (qg g.op (n+(v3 n gs v p).2.length)
      (g.inputs.map fun i=>(v3 n gs v p).1.getD i (inl false))).1
     omega
    have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [y];simp
    rw [z];omega
 match j with
 | 0=>trivial
 | 1=>obtain ⟨v,e,b,d⟩:=h;exact ⟨v,e,t v false 1 b d⟩
 | 2=>obtain ⟨v,e,b,d⟩:=h;exact ⟨v,e,t v true 1 b d⟩
 | 3=>obtain ⟨v,e,b,d⟩:=h;exact ⟨v,e,t v false 2 b d⟩
 | _+4=>exact False.elim h
lemma zr {n:Nat} {gs:U} {o p u:Nat} {f:u7 n} {v:Fin n} {c:Q} (d:MinClean n f gs o) (j:p<=gs.length) (s:u∈liveList gs n o p) (t:∃ x y,f (update x v false)≠f (update y v false)) (w:(v3 n gs v p).1.getD u (inl false)=inl c) :∃ g'∈gs.drop p,u∈g'.inputs:=by
 have ⟨hlt,z⟩:=(qw gs n o p u).1 s;rcases z with rfl|⟨q,hq,g',b',h0,_⟩
 . exfalso;have hfl:=vb n gs v p j;have h1:(u2 n gs (wf n v,[])).1.getD u (inl false)=inl c:=by
    rw [<- zj n gs v p,wy n u _ _ _ (by omega)];exact w
   have e:∀ x,ej n (ofFn x) (q3 gs (ofFn (update x v false))) (u2 n gs (wf n v,[])):=
    fun x=>j7 n _ (by simp) gs _ _ (fun g b=>(ja d.hcl g b).1) (re n v x)
   obtain ⟨x,y,h2⟩:=t;apply h2
   have h:=((e x).2 u).2.trans (d.hev _);have i:=((e y).2 u).2.trans (d.hev _);rw [h1] at h i;exact h.symm.trans i
 . have hqlt:q < gs.length:=(lGES.1 b').1;have h3:gs[q]=g':=(lGES.1 b').2;refine ⟨g',?_,h0⟩
   have:g'=(gs.drop p)[q - p]'(by simp;omega):=by rw [List.getElem_drop];simp [show p+(q - p)=q by omega,h3]
   rw [this];exact List.getElem_mem _
lemma xu {n:Nat} {gs:U} {o p j:Nat} {f:u7 n} (v:MinClean n f gs o) (hp:p < gs.length) (i:∀ x,e3 gs n (n+p) x=!(e3 gs n j x)) :∀ g'∈gs.drop (p+1),¬ (j∈g'.inputs/\(n+p)∈g'.inputs):=by
 intro g' hg' ⟨d,h⟩;obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg';have w:p+1+r < gs.length:=by simp at hr;omega
 have h4:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop;rw [h4] at d h;set q:=p+1+r with hq
 have z:gs[q]?=some gs[q]:=lGEQ w;have h2:=v.hcl q gs[q] z;have h3:=oa n gs q gs[q] z (j2 h2);have s:j≠n+p:=by
   intro e;have y:=i (fun _=>false);rw [e] at y
   cases hv:e3 gs n (n+p) (fun _=>false)<;>rw [hv] at y<;>cases y
 rcases h2 with ⟨_,a,_,t⟩|⟨u,a,b,_,_,t⟩
 . rw [t] at d h;simp at d h;exact s (d.trans h.symm)
 . rw [t] at d h;simp at d h;rcases u with u|u
   . apply v.hncG q w false
     funext x;rw [h3 x,u,t];simp only [lMC,lMN,GateOp.eval];rcases d with rfl|rfl<;>rcases h with c|c
     . exact absurd c.symm s
     . rw [<- c,i x];cases e3 gs n j x<;>rfl
     . rw [<- c,i x];cases e3 gs n j x<;>rfl
     . exact absurd c.symm s
   . apply v.hncG q w true
     funext x;rw [h3 x,u,t];simp only [lMC,lMN,GateOp.eval];rcases d with rfl|rfl<;>rcases h with c|c
     . exact absurd c.symm s
     . rw [<- c,i x];cases e3 gs n j x<;>rfl
     . rw [<- c,i x];cases e3 gs n j x<;>rfl
     . exact absurd c.symm s
lemma xt {n:Nat} {gs:U} {o p j k:Nat} {f:u7 n} (u:MinClean n f gs o) (hp:p < gs.length) (hjlt:j < n+p) (s:∀ x,e3 gs n (n+p) x=(e3 gs n j x&&e3 gs n k x)) :∀ g'∈gs.drop (p+1),¬ (j∈g'.inputs/\(n+p)∈g'.inputs):=by
 intro g' hg' ⟨d,e⟩;obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg';have v:p+1+r < gs.length:=by simp at hr;omega
 have h0:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop;rw [h0] at d e;set q:=p+1+r with hq
 have w:gs[q]?=some gs[q]:=lGEQ v;have y:=u.hcl q gs[q] w;have z:=oa n gs q gs[q] w (j2 y);have t:j≠n+p:=by omega
 rcases y with ⟨_,a,_,h⟩|⟨i,a,b,_,_,h⟩
 . rw [h] at d e;simp at d e;omega
 . rw [h] at d e;simp at d e;rcases i with i|i
   . apply u.hndup q v (n+p) (by omega)
     funext x;rw [z x,i,h];simp only [lMC,lMN,GateOp.eval];rcases d with rfl|rfl<;>rcases e with c|c
     . exact absurd c.symm t
     . rw [<- c,s x];cases e3 gs n j x<;>cases e3 gs n k x<;>rfl
     . rw [<- c,s x];cases e3 gs n j x<;>cases e3 gs n k x<;>rfl
     . exact absurd c.symm t
   . apply u.hndup q v j (by omega)
     funext x;rw [z x,i,h];simp only [lMC,lMN,GateOp.eval];rcases d with rfl|rfl<;>rcases e with c|c
     . exact absurd c.symm t
     . rw [<- c,s x];cases e3 gs n j x<;>cases e3 gs n k x<;>rfl
     . rw [<- c,s x];cases e3 gs n j x<;>cases e3 gs n k x<;>rfl
     . exact absurd c.symm t
lemma gt {n:Nat} {gs:U} (hcl:yq n gs) (p:Nat) :∀ g∈gs.drop p,tq g:=fun g hg=>ja hcl g (List.mem_of_mem_drop hg)
open Classical in
lemma rg (n:Nat) (f:u7 n) (gs:U) (o:Nat) (hm:MinClean n f gs o) :∀ d p,p+d=gs.length -> ∀ b:Nat->Nat,(∀ a∈liveList gs n o p,yf n gs f p a (b a)) -> TagRun (invF (n:=n)) meetF joinF (fun _=>false) (fun _=>true) f d
       ((liveList gs n o p).map fun a=>(e3 gs n a,b a)):=by
 intro d
 induction d with
 | zero =>
  intro p hp b _
  have h38:[o].Perm (liveList gs n o p):=by
   refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (vy _ _ _ _)).2 ?_
   intro a
   rw [qw,List.mem_singleton]
   constructor
   . rintro rfl;exact ⟨by have:=hm.ho;omega,Or.inl rfl⟩
   . rintro ⟨_,h|⟨q,hq,g',hg',_,_⟩⟩
     . exact h
     . have:=(lGES.1 hg').1;omega
  have hf:e3 gs n o=f:=funext hm.hev
  have w:([(f,b o)]).Perm ((liveList gs n o p).map fun a=>(e3 gs n a,b a)):=by
   rw [<- hf];exact h38.map (fun a=>(e3 gs n a,b a))
  exact TagRun.perm w (TagRun.done (b o))
 | succ d ih =>
  intro p hp b h6
  have b1:p < gs.length:=by omega
  obtain ⟨g,hg⟩:∃ g,gs[p]?=some g:=⟨gs[p],lGEQ b1⟩
  have hr:wn n gs o (n+p):=hm.hreach p b1
  have hb:=ip n gs o hm.hcl p g hg hr
  have hin:∀ a∈g.inputs,a∈liveList gs n o p:=fun a ha =>
   (qw _ _ _ _ _).2 ⟨j2 (hm.hcl p g hg) a ha,Or.inr ⟨p,le_rfl,g,hg,ha,hr⟩⟩
  have hc:∀ a∈liveList gs n o p,a≠n+p:=fun a ha =>
   Nat.ne_of_lt ((qw _ _ _ _ _).1 ha).1
  have hvg:=oa n gs p g hg (j2 (hm.hcl p g hg))
  have hv:=vy gs n o p
  have h30:gs.drop p=g::gs.drop (p+1):=by
   rw [List.drop_eq_getElem_cons b1];have hge:gs[p]=g:=(lGES.1 hg).2;rw [hge]
  have hgn:tq g:=w5 (hm.hcl p g hg)
  have hy:=gt hm.hcl (p+1)
  have hnz:e3 gs n (n+p)≠fun _=>false:=hm.hncG p b1 false
  have hno:e3 gs n (n+p)≠fun _=>true:=hm.hncG p b1 true
  have hd:∀ a∈liveList gs n o p,e3 gs n a≠e3 gs n (n+p):=fun a ha e =>
   hm.hndup p b1 a ((qw _ _ _ _ _).1 ha).1 e.symm
  rcases hm.hcl p g hg with ⟨x2,j,hj,h5⟩|⟨x2,j,k,hj,hk,h5⟩
  .
   have h7:j∈liveList gs n o p:=hin j (by simp [h5])
   have h8:e3 gs n (n+p)=invF (e3 gs n j):=by
     funext x;rw [hvg x,x2,h5];simp [GateOp.eval]
   have h22:∀ v c B,
       (∃ x y,f (update x v false)≠f (update y v false)) ->
       (v3 n gs v p).1.getD j (inl false)=inl c ->
       (v3 n gs v p).2.length+(gs.drop p).length<=(u2 n (gs.drop p) (v3 n gs v p)).2.length+B ->
       2<=B /\
       (v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl (!c) /\
       (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
         (u2 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
       (m6 n gs o (p+1) j->3<=B):=by
     intro v c B s t z
     have a1:=ax n gs v p g hg
     have hfl:=vb n gs v p (by omega)
     have h34:=vb n gs v (p+1) (by omega)
     have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
       rw [a1];exact vs n _ g hgn j (by simp [h5]) c t
     have xs:(v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl (!c):=by
       rw [a1];simp only [qa]
       rw [z2 _ _ _ _ hfl,x2,h5]
       simp only [lMC,lMN,t,qg,wr]
     have h12:u2 n (gs.drop (p+1)) (v3 n gs v (p+1))=u2 n (gs.drop p) (v3 n gs v p):=by
       rw [zj,zj]
     have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [h30];simp
     have h10:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
         (u2 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
       rw [h12,h0];omega
     have h13:n+p∈liveList gs n o (p+1):=(hb (n+p)).2 (Or.inl rfl)
     have hz:=zr hm (by omega) h13 s xs
     have h23:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hy
       (by omega) ⟨!c,xs⟩ hz
     refine ⟨by omega,xs,h10,?_⟩
     intro he
     have h39:j∈liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,he⟩
     have h35:(v3 n gs v (p+1)).1.getD j (inl false)=inl c:=by
       rw [a1];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact t
     have h40:=zr hm (by omega) h39 s h35
     have h31:=xu hm b1 (fun x=>congrFun h8 x)
     have h41:=k3 n j (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
       hy (by omega) (by omega) ⟨c,h35⟩ ⟨!c,xs⟩ h40 hz h31
     omega
   have ht1:b j≠1:=by
     intro w;have i:=h6 j h7;rw [w] at i
     obtain ⟨v,s,t,z⟩:=i
     have:=(h22 v false 1 s t z).1;omega
   have ht2:b j≠2:=by
     intro h2;have i:=h6 j h7;rw [h2] at i
     obtain ⟨v,s,t,z⟩:=i
     have:=(h22 v true 1 s t z).1;omega
   have ht3:b j=3->decide (m6 n gs o (p+1) j)=false:=by
     intro h3;simp only [decide_eq_false_iff_not];intro he
     have i:=h6 j h7;rw [h3] at i
     obtain ⟨v,s,t,z⟩:=i
     have:=(h22 v false 2 s t z).2.2.2 he;omega
   set b' : Nat->Nat:=fun a =>
     if a=n+p then (if b j=3 then 2 else 0)
     else if a=j then 0
     else b a
   have h6':∀ a∈liveList gs n o (p+1),yf n gs f (p+1) a (b' a):=by
     intro a ha
     simp only [b']
     by_cases a2:a=n+p
     . subst a2;simp only [↓reduceIte]
       by_cases h3:b j=3
       . simp only [h3,↓reduceIte]
         have i:=h6 j h7;rw [h3] at i
         obtain ⟨v,s,t,z⟩:=i
         obtain ⟨_,xs,h10,_⟩:=h22 v false 2 s t z
         exact ⟨v,s,xs,by omega⟩
       . simp only [h3,↓reduceIte];trivial
     . simp only [a2,↓reduceIte]
       by_cases h9:a=j
       . simp only [h9,↓reduceIte];trivial
       . simp only [h9,↓reduceIte]
         have hi:a∈liveList gs n o p:=by
           rcases (hb a).1 ha with rfl|⟨w,_⟩
           . exact absurd rfl a2
           . exact w
         exact vv hg ((qw _ _ _ _ _).1 hi).1 (h6 a hi)
   have IH:=ih (p+1) (by omega) b' h6'
   have hp1:(liveList gs n o p).Perm (j::(liveList gs n o p).erase j):=List.perm_cons_erase h7
   have hnr:((liveList gs n o p).erase j).Nodup:=hv.erase j
   have hp2:(liveList gs n o (p+1)).Perm
       ((n+p)::qk (decide (m6 n gs o (p+1) j)) j ((liveList gs n o p).erase j)):=by
     refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
     . refine List.nodup_cons.2 ⟨?_,cj _ _ _ hnr (by simp [hv.mem_erase_iff])⟩
       rw [wa];rintro (⟨_,h⟩|h)
       . exact hc j h7 h.symm
       . exact hc _ (List.mem_of_mem_erase h) rfl
     . intro a
       rw [hb a,lMM,wa,hv.mem_erase_iff,h5,List.mem_singleton]
       simp only [decide_eq_true_eq]
       constructor
       . rintro (h|⟨w,h2⟩)
         . exact Or.inl h
         . by_cases h9:a=j
           . exact Or.inr (Or.inl ⟨h9 ▸ h2 h9,h9⟩)
           . exact Or.inr (Or.inr ⟨h9,w⟩)
       . rintro (h|⟨w,rfl⟩|⟨w,h2⟩)
         . exact Or.inl h
         . exact Or.inr ⟨h7,fun _=>w⟩
         . exact Or.inr ⟨h2,fun h=>absurd h w⟩
   have h14:((liveList gs n o p).erase j).map (fun a=>(e3 gs n a,b' a)) =
       ((liveList gs n o p).erase j).map (fun a=>(e3 gs n a,b a)):=by
     apply lMCL
     intro a ha
     have w:a≠j:=(hv.mem_erase_iff.1 ha).1
     have h2:a≠n+p:=hc a (List.mem_of_mem_erase ha)
     simp [b',w,h2]
   have h15:(qk (decide (m6 n gs o (p+1) j)) j ((liveList gs n o p).erase j)).map (fun a=>(e3 gs n a,b' a)) =
       qk (decide (m6 n gs o (p+1) j)) (e3 gs n j,0) (((liveList gs n o p).erase j).map fun a=>(e3 gs n a,b a)):=by
     rw [wd,h14]
     have h16:j≠n+p:=by omega
     simp [b',h16]
   have IH':=TagRun.perm (hp2.map fun a=>(e3 gs n a,b' a)) IH
   rw [lMC,h15,h8] at IH'
   have h17:b' (n+p)=(if b j=3 then 2 else 0):=by simp [b']
   rw [h17] at IH'
   refine TagRun.perm (hp1.map fun a=>(e3 gs n a,b a)).symm ?_
   refine TagRun.uNot (decide (m6 n gs o (p+1) j)) ht1 ht2 ht3
     (h8 ▸ hnz) (h8 ▸ hno) (fun e=>hd j h7 (h8 ▸ e.symm)) ?_ IH'
   intro x hx
   obtain ⟨a,ha,rfl⟩:=lMp.1 hx
   exact h8 ▸ hd a (List.mem_of_mem_erase ha)
  .
   have hjk:j≠k:=by
     intro e;subst e
     apply hm.hndup p b1 j hj
     funext x;rw [hvg x,h5]
     rcases x2 with x2|x2<;>rw [x2]<;>simp [GateOp.eval]
   have h7:=hin j (by simp [h5])
   have x3:=hin k (by simp [h5])
   have hke:k∈(liveList gs n o p).erase j:=(hv.mem_erase_iff).2 ⟨fun e=>hjk e.symm,x3⟩
   have hnr:((liveList gs n o p).erase j).Nodup:=hv.erase j
   have h42:(((liveList gs n o p).erase j).erase k).Nodup:=hnr.erase k
   have hp1:(liveList gs n o p).Perm (j::k::((liveList gs n o p).erase j).erase k):=
     (List.perm_cons_erase h7).trans ((List.perm_cons_erase hke).cons j)
   have hn:∀ a,a∈((liveList gs n o p).erase j).erase k↔a≠k/\a≠j/\a∈liveList gs n o p:=by
     intro a;rw [hnr.mem_erase_iff,hv.mem_erase_iff]
   have hp2:(liveList gs n o (p+1)).Perm
       ((n+p)::qk (decide (m6 n gs o (p+1) j)) j
         (qk (decide (m6 n gs o (p+1) k)) k
           (((liveList gs n o p).erase j).erase k))):=by
     refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
     . refine List.nodup_cons.2 ⟨?_,cj _ _ _ (cj _ _ _ h42 ?_) ?_⟩
       . rw [wa,wa]
         rintro (⟨_,h⟩|⟨_,h⟩|h)
         . exact hc j h7 h.symm
         . exact hc k x3 h.symm
         . exact hc _ ((hn _).1 h).2.2 rfl
       . rw [hn];simp
       . rw [wa,hn]
         rintro (⟨_,h⟩|h)
         . exact hjk h
         . exact h.2.1 rfl
     . intro a
       rw [hb a,lMM,wa,wa,hn a]
       simp only [decide_eq_true_eq,h5,lMM,lNMN,or_false]
       constructor
       . rintro (h|⟨w,h2⟩)
         . exact Or.inl h
         . by_cases h9:a=j
           . exact Or.inr (Or.inl ⟨h9 ▸ h2 (Or.inl h9),h9⟩)
           . by_cases xi:a=k
             . exact Or.inr (Or.inr (Or.inl ⟨xi ▸ h2 (Or.inr xi),xi⟩))
             . exact Or.inr (Or.inr (Or.inr ⟨xi,h9,w⟩))
       . rintro (h|⟨w,rfl⟩|⟨w,rfl⟩|⟨w,h2,h3⟩)
         . exact Or.inl h
         . exact Or.inr ⟨h7,fun _=>w⟩
         . exact Or.inr ⟨x3,fun _=>w⟩
         . exact Or.inr ⟨h3,fun h=>by rcases h with h|h<;>contradiction⟩
   rcases x2 with x2|x2
   .
     have h8:e3 gs n (n+p)=meetF (e3 gs n j) (e3 gs n k):=by
       funext x;rw [hvg x,x2,h5];simp [GateOp.eval]
     have hs:∀ (u w_other:Nat) (hu:u∈g.inputs) (h24:u < n+p)
         (hval_u:∀ x,e3 gs n (n+p) x=(e3 gs n u x&&e3 gs n w_other x))
         (v:Fin n) (c:Q) (B:Nat),
         (∃ x y,f (update x v false)≠f (update y v false)) ->
         (v3 n gs v p).1.getD u (inl false)=inl c ->
         (v3 n gs v p).2.length+(gs.drop p).length<=(u2 n (gs.drop p) (v3 n gs v p)).2.length+B ->
         (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u2 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
         (c=false ->
           2<=B /\
           (v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl false /\
           (m6 n gs o (p+1) u->3<=B)) /\
         (c=true->m6 n gs o (p+1) u->2<=B):=by
       intro u wo hu h24 h43 v c B s t z
       have a1:=ax n gs v p g hg
       have hfl:=vb n gs v p (by omega)
       have h34:=vb n gs v (p+1) (by omega)
       have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
         rw [a1];exact vs n _ g hgn u hu c t
       have h12:u2 n (gs.drop (p+1)) (v3 n gs v (p+1))=u2 n (gs.drop p) (v3 n gs v p):=by
         rw [zj,zj]
       have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [h30];simp
       have h10:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u2 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
         rw [h12,h0];omega
       have ht:(v3 n gs v (p+1)).1.getD u (inl false)=inl c:=by
         rw [a1];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact t
       refine ⟨h10,?_,?_⟩
       . intro hcf;subst hcf
         have h25:(v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl false:=by
           rw [a1];simp only [qa];rw [z2 _ _ _ _ hfl,x2,h5]
           rw [h5] at hu;simp only [lMM,lNMN,or_false] at hu
           rcases hu with rfl|rfl
           . simp only [lMC,lMN,t,qg]
             cases (v3 n gs v p).1.getD k (inl false)<;>simp [ko]
           . simp only [lMC,lMN,t,qg]
             cases (v3 n gs v p).1.getD j (inl false)<;>simp [ko]
         have h13:n+p∈liveList gs n o (p+1):=(hb (n+p)).2 (Or.inl rfl)
         have hz:=zr hm (by omega) h13 s h25
         have h23:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hy
           (by omega) ⟨false,h25⟩ hz
         refine ⟨by omega,h25,?_⟩
         intro h18
         have h19:u∈liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,h18⟩
         have h20:=zr hm (by omega) h19 s ht
         have h31:=xt hm b1 h24 h43
         have h41:=k3 n u (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
           hy (by omega) (by omega) ⟨false,ht⟩ ⟨false,h25⟩ h20 hz h31
         omega
       . intro hct h18;subst hct
         have h19:u∈liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,h18⟩
         have h20:=zr hm (by omega) h19 s ht
         have h23:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hy
           (by omega) ⟨true,ht⟩ h20
         omega
     have h21:∀ x,e3 gs n (n+p) x=(e3 gs n j x&&e3 gs n k x):=fun x=>congrFun h8 x
     have h26:∀ x,e3 gs n (n+p) x=(e3 gs n k x&&e3 gs n j x):=fun x=>by
       rw [h21 x,Bool.and_comm]
     have h27:b j≠1:=by
       intro w;have i:=h6 j h7;rw [w] at i
       obtain ⟨v,s,t,z⟩:=i
       have:=(hs j k (by simp [h5]) hj h21 v false 1 s t z).2.1 rfl
       omega
     have h28:b k≠1:=by
       intro w;have i:=h6 k x3;rw [w] at i
       obtain ⟨v,s,t,z⟩:=i
       have:=(hs k j (by simp [h5]) hk h26 v false 1 s t z).2.1 rfl
       omega
     have h44:b j=1\/b j=2\/b j=3->decide (m6 n gs o (p+1) j)=false:=by
       intro h32;simp only [decide_eq_false_iff_not];intro he
       rcases h32 with w|h2|h3
       . exact h27 w
       . have i:=h6 j h7;rw [h2] at i
         obtain ⟨v,s,t,z⟩:=i
         have:=(hs j k (by simp [h5]) hj h21 v true 1 s t z).2.2 rfl he;omega
       . have i:=h6 j h7;rw [h3] at i
         obtain ⟨v,s,t,z⟩:=i
         have:=((hs j k (by simp [h5]) hj h21 v false 2 s t z).2.1 rfl).2.2 he;omega
     have h45:b k=1\/b k=2\/b k=3->decide (m6 n gs o (p+1) k)=false:=by
       intro h32;simp only [decide_eq_false_iff_not];intro h29
       rcases h32 with w|h2|h3
       . exact h28 w
       . have i:=h6 k x3;rw [h2] at i
         obtain ⟨v,s,t,z⟩:=i
         have:=(hs k j (by simp [h5]) hk h26 v true 1 s t z).2.2 rfl h29;omega
       . have i:=h6 k x3;rw [h3] at i
         obtain ⟨v,s,t,z⟩:=i
         have:=((hs k j (by simp [h5]) hk h26 v false 2 s t z).2.1 rfl).2.2 h29;omega
     set b' : Nat->Nat:=fun a =>
       if a=n+p then (if b j=3\/b k=3 then 1 else 0)
       else if a=j\/a=k then 0
       else b a
     have h6':∀ a∈liveList gs n o (p+1),yf n gs f (p+1) a (b' a):=by
       intro a ha
       simp only [b']
       by_cases a2:a=n+p
       . subst a2;simp only [↓reduceIte]
         by_cases h3:b j=3\/b k=3
         . simp only [h3,↓reduceIte]
           rcases h3 with hj3|hk3
           . have i:=h6 j h7;rw [hj3] at i
             obtain ⟨v,s,t,z⟩:=i
             have hh:=hs j k (by simp [h5]) hj h21 v false 2 s t z
             exact ⟨v,s,(hh.2.1 rfl).2.1,by omega⟩
           . have i:=h6 k x3;rw [hk3] at i
             obtain ⟨v,s,t,z⟩:=i
             have hh:=hs k j (by simp [h5]) hk h26 v false 2 s t z
             exact ⟨v,s,(hh.2.1 rfl).2.1,by omega⟩
         . simp only [h3,↓reduceIte];trivial
       . simp only [a2,↓reduceIte]
         by_cases h36:a=j\/a=k
         . simp only [h36,↓reduceIte];trivial
         . simp only [h36,↓reduceIte]
           have hi:a∈liveList gs n o p:=by
             rcases (hb a).1 ha with rfl|⟨w,_⟩
             . exact absurd rfl a2
             . exact w
           exact vv hg ((qw _ _ _ _ _).1 hi).1 (h6 a hi)
     have IH:=ih (p+1) (by omega) b' h6'
     have h14:(((liveList gs n o p).erase j).erase k).map (fun a=>(e3 gs n a,b' a)) =
         (((liveList gs n o p).erase j).erase k).map (fun a=>(e3 gs n a,b a)):=by
       apply lMCL
       intro a ha
       have ⟨w,h2,h3⟩:=(hn a).1 ha
       have h4:a≠n+p:=hc a h3
       simp [b',w,h2,h4]
     have h15:(qk (decide (m6 n gs o (p+1) j)) j
         (qk (decide (m6 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
           (fun a=>(e3 gs n a,b' a)) =
         qk (decide (m6 n gs o (p+1) j)) (e3 gs n j,0)
           (qk (decide (m6 n gs o (p+1) k)) (e3 gs n k,0)
             ((((liveList gs n o p).erase j).erase k).map fun a=>(e3 gs n a,b a))):=by
       rw [wd,wd,h14]
       have h16:j≠n+p:=by omega
       have h33:k≠n+p:=by omega
       simp [b',h16,h33]
     have IH':=TagRun.perm (hp2.map fun a=>(e3 gs n a,b' a)) IH
     rw [lMC,h15,h8] at IH'
     have h17:b' (n+p)=(if b j=3\/b k=3 then 1 else 0):=by simp [b']
     rw [h17] at IH'
     have hjle3:=xx (h6 j h7)
     have hkle3:=xx (h6 k x3)
     refine TagRun.perm (hp1.map fun a=>(e3 gs n a,b a)).symm ?_
     refine TagRun.bAnd (decide (m6 n gs o (p+1) j)) (decide (m6 n gs o (p+1) k))
       h27 h28 (fun h=>h44 (by omega)) (fun h=>h45 (by omega))
       (h8 ▸ hnz) (h8 ▸ hno)
       (fun e=>hd j h7 (h8 ▸ e.symm)) (fun e=>hd k x3 (h8 ▸ e.symm)) ?_ IH'
     intro x hx
     obtain ⟨a,ha,rfl⟩:=lMp.1 hx
     exact h8 ▸ hd a ((hn a).1 ha).2.2
   .
     have h8:e3 gs n (n+p)=joinF (e3 gs n j) (e3 gs n k):=by
       funext x;rw [hvg x,x2,h5];simp [GateOp.eval]
     have h11:∀ (u:Nat) (hu:u∈g.inputs) (h24:u < n+p)
         (v:Fin n) (c:Q) (B:Nat),
         (∃ x y,f (update x v false)≠f (update y v false)) ->
         (v3 n gs v p).1.getD u (inl false)=inl c ->
         (v3 n gs v p).2.length+(gs.drop p).length<=(u2 n (gs.drop p) (v3 n gs v p)).2.length+B ->
         (v3 n gs v (p+1)).1.getD u (inl false)=inl c /\
         (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u2 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
         (c=true->2<=B) /\
         (c=false->m6 n gs o (p+1) u->2<=B):=by
       intro u hu h24 v c B s t z
       have a1:=ax n gs v p g hg
       have hfl:=vb n gs v p (by omega)
       have h34:=vb n gs v (p+1) (by omega)
       have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
         rw [a1];exact vs n _ g hgn u hu c t
       have h12:u2 n (gs.drop (p+1)) (v3 n gs v (p+1))=u2 n (gs.drop p) (v3 n gs v p):=by
         rw [zj,zj]
       have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [h30];simp
       have h10:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u2 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
         rw [h12,h0];omega
       have ht:(v3 n gs v (p+1)).1.getD u (inl false)=inl c:=by
         rw [a1];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact t
       refine ⟨ht,h10,?_,?_⟩
       . intro hct;subst hct
         have h37:(v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl true:=by
           rw [a1];simp only [qa];rw [z2 _ _ _ _ hfl,x2,h5]
           rw [h5] at hu;simp only [lMM,lNMN,or_false] at hu
           rcases hu with rfl|rfl
           . simp only [lMC,lMN,t,qg]
             cases (v3 n gs v p).1.getD k (inl false)<;>simp [ji]
           . simp only [lMC,lMN,t,qg]
             cases (v3 n gs v p).1.getD j (inl false)<;>simp [ji]
         have h13:n+p∈liveList gs n o (p+1):=(hb (n+p)).2 (Or.inl rfl)
         have hz:=zr hm (by omega) h13 s h37
         have h23:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hy
           (by omega) ⟨true,h37⟩ hz
         omega
       . intro hcf h18;subst hcf
         have h19:u∈liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,h18⟩
         have h20:=zr hm (by omega) h19 s ht
         have h23:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hy
           (by omega) ⟨false,ht⟩ h20
         omega
     have h46:b j≠2:=by
       intro h2;have i:=h6 j h7;rw [h2] at i
       obtain ⟨v,s,t,z⟩:=i
       have:=(h11 j (by simp [h5]) hj v true 1 s t z).2.2.1 rfl;omega
     have h47:b k≠2:=by
       intro h2;have i:=h6 k x3;rw [h2] at i
       obtain ⟨v,s,t,z⟩:=i
       have:=(h11 k (by simp [h5]) hk v true 1 s t z).2.2.1 rfl;omega
     have h27:b j=1->decide (m6 n gs o (p+1) j)=false:=by
       intro w;simp only [decide_eq_false_iff_not];intro he
       have i:=h6 j h7;rw [w] at i
       obtain ⟨v,s,t,z⟩:=i
       have:=(h11 j (by simp [h5]) hj v false 1 s t z).2.2.2 rfl he;omega
     have h28:b k=1->decide (m6 n gs o (p+1) k)=false:=by
       intro w;simp only [decide_eq_false_iff_not];intro h29
       have i:=h6 k x3;rw [w] at i
       obtain ⟨v,s,t,z⟩:=i
       have:=(h11 k (by simp [h5]) hk v false 1 s t z).2.2.2 rfl h29;omega
     set b' : Nat->Nat:=fun a =>
       if a=n+p then 0
       else if a=j then (if b j=3 then 1 else 0)
       else if a=k then (if b k=3 then 1 else 0)
       else b a
     have h6':∀ a∈liveList gs n o (p+1),yf n gs f (p+1) a (b' a):=by
       intro a ha
       simp only [b']
       by_cases a2:a=n+p
       . simp [a2,yf]
       . simp only [a2,↓reduceIte]
         by_cases h9:a=j
         . rw [h9];simp only [↓reduceIte]
           by_cases hj3:b j=3
           . simp only [hj3,↓reduceIte]
             have i:=h6 j h7;rw [hj3] at i
             obtain ⟨v,s,t,z⟩:=i
             have hh:=h11 j (by simp [h5]) hj v false 2 s t z
             exact ⟨v,s,hh.1,by omega⟩
           . simp only [hj3,↓reduceIte];trivial
         . simp only [h9,↓reduceIte]
           by_cases xi:a=k
           . rw [xi];simp only [↓reduceIte]
             by_cases hk3:b k=3
             . simp only [hk3,↓reduceIte]
               have i:=h6 k x3;rw [hk3] at i
               obtain ⟨v,s,t,z⟩:=i
               have hh:=h11 k (by simp [h5]) hk v false 2 s t z
               exact ⟨v,s,hh.1,by omega⟩
             . simp only [hk3,↓reduceIte];trivial
           . simp only [xi,↓reduceIte]
             have hi:a∈liveList gs n o p:=by
               rcases (hb a).1 ha with rfl|⟨w,_⟩
               . exact absurd rfl a2
               . exact w
             exact vv hg ((qw _ _ _ _ _).1 hi).1 (h6 a hi)
     have IH:=ih (p+1) (by omega) b' h6'
     have h14:(((liveList gs n o p).erase j).erase k).map (fun a=>(e3 gs n a,b' a)) =
         (((liveList gs n o p).erase j).erase k).map (fun a=>(e3 gs n a,b a)):=by
       apply lMCL
       intro a ha
       have ⟨w,h2,h3⟩:=(hn a).1 ha
       have h4:a≠n+p:=hc a h3
       simp [b',w,h2,h4]
     have h15:(qk (decide (m6 n gs o (p+1) j)) j
         (qk (decide (m6 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
           (fun a=>(e3 gs n a,b' a)) =
         qk (decide (m6 n gs o (p+1) j)) (e3 gs n j,if b j=3 then 1 else 0)
           (qk (decide (m6 n gs o (p+1) k)) (e3 gs n k,if b k=3 then 1 else 0)
             ((((liveList gs n o p).erase j).erase k).map fun a=>(e3 gs n a,b a))):=by
       rw [wd,wd,h14]
       have h16:j≠n+p:=by omega
       have h33:k≠n+p:=by omega
       have hkj:k≠j:=fun e=>hjk e.symm
       simp [b',h16,h33,hkj]
     have IH':=TagRun.perm (hp2.map fun a=>(e3 gs n a,b' a)) IH
     rw [lMC,h15,h8] at IH'
     have h17:b' (n+p)=0:=by simp [b']
     rw [h17] at IH'
     refine TagRun.perm (hp1.map fun a=>(e3 gs n a,b a)).symm ?_
     refine TagRun.bOr (decide (m6 n gs o (p+1) j)) (decide (m6 n gs o (p+1) k))
       h46 h47 h27 h28
       (h8 ▸ hnz) (h8 ▸ hno)
       (fun e=>hd j h7 (h8 ▸ e.symm)) (fun e=>hd k x3 (h8 ▸ e.symm)) ?_ IH'
     intro x hx
     obtain ⟨a,ha,rfl⟩:=lMp.1 hx
     exact h8 ▸ hd a ((hn a).1 ha).2.2
lemma be {n:Nat} {gs:U} {o:Nat} {f:u7 n} (hev:∀ x,e3 gs n o x=f x) (v:Fin n) (w:∃ x:F n,f (update x v (!x v))≠f x) :(v:Nat)∈liveList gs n o 0:=by
 rw [qw];refine ⟨by omega,?_⟩
 by_contra j;have z:¬ wn n gs o (v:Nat):=by
  intro b;rcases xk b with h0|⟨q,g,hg,h1,h2⟩
  . exact j (Or.inl h0)
  . exact j (Or.inr ⟨q,nZL q,g,hg,h1,h2⟩)
 obtain ⟨x,s⟩:=w;apply s
 rw [<- hev,<- hev];have h3:∀ (p:Nat),∀ i < n+p,wn n gs o i ->
    (q3 (gs.take p) (ofFn (update x v (!x v)))).getD i false =
    (q3 (gs.take p) (ofFn x)).getD i false:=by
  intro p;induction p with
  | zero =>
    intro i hi b;simp only [List.take_zero,q3,List.foldl_nil];have c:i < n:=by omega
    have h4:(⟨i,c⟩:Fin n)≠v:=fun e=>z (by simpa [<- e] using b)
    simp [c,fUN h4]
  | succ p ih =>
    intro i hi b;by_cases t:p < gs.length
    . have d:gs.take (p+1)=gs.take p++[gs[p]]:=List.take_succ_eq_append_getElem t;rw [d,zd,zd];have h5:(q3 (gs.take p) (ofFn (update x v (!x v)))).length=n+p:=by
        rw [qu];simp [lLT,Nat.min_eq_left (by omega:p<=gs.length)]
      have h6:(q3 (gs.take p) (ofFn x)).length=n+p:=by rw [qu];simp [lLT,Nat.min_eq_left (by omega:p<=gs.length)]
      by_cases h7:i=n+p
      . subst h7
        show (q3 (gs.take p) _++[_]).getD (n+p) false=(q3 (gs.take p) _++[_]).getD (n+p) false
        rw [z2 _ _ _ _ h5,z2 _ _ _ _ h6];congr 1
        apply lMCL
        intro a ha;have h8:wn n gs o a:=iu (lGEQ t) b ha;by_cases h9:a < n+p
        . exact ih a h9 h8
        . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
      . show (q3 (gs.take p) _++[_]).getD i false=(q3 (gs.take p) _++[_]).getD i false
        rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)];exact ih i (by omega) b
    . have d:gs.take (p+1)=gs.take p:=by
        rw [List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
      rw [d];by_cases c:i < n+p
      . exact ih i c b
      . have hl1:(q3 (gs.take p) (ofFn (update x v (!x v)))).length=n+gs.length:=by
          rw [qu,List.take_of_length_le (by omega)];simp
        have hl2:(q3 (gs.take p) (ofFn x)).length=n+gs.length:=by rw [qu,List.take_of_length_le (by omega)];simp
        rw [lGD _ _ (by omega),lGD _ _ (by omega)]
 have x2:o < n+gs.length:=by
  by_contra hge;have u:∀ y:F n,e3 gs n o y=false:=fun y =>
    lGD _ _ (by rw [qu];simp;omega)
  exact s (by rw [<- hev,<- hev,u,u])
 have h:=h3 gs.length o x2 (it n gs o);rw [List.take_length] at h;exact h
open Classical in
lemma q88 {n:Nat} (f:u7 n) (d:Nat) (c:Fin n->Nat) (h4:∃ y y':F n,f y≠f y') (h5:∀ v:Fin n,∃ x:F n,f (update x v (!x v))≠f x) (h6:∀ v:Fin n,c v=0 \/ (c v=1/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->d - 1<=s') \/ (c v=3/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->d - 2<=s')) (s:Nat) (hs:s<=d) (hc:HCS n f s) :∃ s',s'<=d /\ TagRun (invF (n:=n)) meetF joinF (fun _=>false) (fun _=>true) f s'
      (ofFn fun i:Fin n=>((fun x:F n=>x i),c i)):=by
 obtain ⟨gs,o,e,hlen⟩:=fr n f s h4 hc
 have w:liveList gs n o 0=range n:=by
  have z:=(List.filter_sublist (l:=range (n+0)) (p:=fun a=>decide (m6 n gs o 0 a)))
  simp only [nAZ] at z
  refine List.Sublist.eq_of_length z ?_
  have h7:(range n).Perm (liveList gs n o 0):=by
    refine (List.perm_ext_iff_of_nodup List.nodup_range (vy gs n o 0)).2 ?_
    intro a
    rw [lMRG]
    constructor
    . intro b;exact be e.hev ⟨a,b⟩ (h5 ⟨a,b⟩)
    . intro b;exact by simpa using ((qw gs n o 0 a).1 b).1
  exact h7.length_eq.symm
 set g:Nat->Nat:=fun a=>if h:a < n then c ⟨a,h⟩ else 0
 have h8:∀ a∈liveList gs n o 0,yf n gs f 0 a (g a):=by
  intro a b
  rw [w,lMRG] at b
  have h9:g a=c ⟨a,b⟩:=by simp [g,b]
  rw [h9]
  rcases h6 ⟨a,b⟩ with h0|⟨h1,j,t⟩|⟨h3,j,t⟩
  . rw [h0];trivial
  . rw [h1]
    have x2:=(wz n f gs o ⟨a,b⟩ (d - 1) e.hcl e.hev j t).2
    refine ⟨⟨a,b⟩,j,?_,?_⟩
    . simp [v3,u2,wf,b]
    . simp only [v3,List.take_zero,List.drop_zero,lLN,zero_add]
      have u:u2 n [] (wf n ⟨a,b⟩,[])=(wf n ⟨a,b⟩,[]):=rfl
      rw [u];simp only [lLN,zero_add];omega
  . rw [h3]
    have x2:=(wz n f gs o ⟨a,b⟩ (d - 2) e.hcl e.hev j t).2
    refine ⟨⟨a,b⟩,j,?_,?_⟩
    . simp [v3,u2,wf,b]
    . simp only [v3,List.take_zero,List.drop_zero,lLN,zero_add]
      have u:u2 n [] (wf n ⟨a,b⟩,[])=(wf n ⟨a,b⟩,[]):=rfl
      rw [u];simp only [lLN,zero_add];omega
 have x3:=rg n f gs o e gs.length 0 (by omega) g h8
 refine ⟨gs.length,by omega,?_⟩
 have a1:(liveList gs n o 0).map (fun a=>(e3 gs n a,g a)) =
    ofFn fun i:Fin n=>((fun x:F n=>x i),c i):=by
  rw [w]
  apply List.ext_getElem
  . simp
  . intro i h1 h2
    have hi:i < n:=by simpa using h2
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact Prod.ext (lc gs n ⟨i,hi⟩) (by simp [g,hi])
 rw [<- a1]
 exact x3
def zm {α:Type} (x:Nat) (f:Nat->α) : α:=
 match x with
 | 0=>f 0
 | n+1=>f (Nat.succ n)
lemma v5 {α:Type} (x:Nat) (f:Nat->α):zm x f=f x:=by cases x<;>rfl
structure Cfg where
 k:Nat
 sh0:Nat
 sh1:Nat
 shTT:Nat
 all1v:Nat
 goalv:Nat
 lok:Nat
 m0all:Nat
 m0:Nat
 a29_0:Nat
 b5_0:Nat
 m1:Nat
 m12:Nat
 a29_1:Nat
 b5_1:Nat
def im (b:Nat×Nat×Nat×Nat) (w:Nat):Nat:=
 let (d,m01,m10,mEq):=b
 lor (lor (land w mEq) (shiftRight (land w m01) d))
  (shiftLeft (land w m10) d)
def ym:V->Nat->Nat
 | [],w=>w
 | sw::rest,w=>ym rest (im sw w)
def sz (sh:Nat):J->J
 | []=>[]
 | (w,tg)::rest=>zm (shiftRight w sh) fun v=>(v,tg)::sz sh rest
def wx (g:V):J->J
 | []=>[]
 | (w,tg)::rest=>zm (ym g w) fun v=>(v,tg)::wx g rest
def qh:Nat:=0x9e3779b97f4a7c15f39cc0605cedc835
def iv:Nat:=0x517cc1b727220a95b3650d1e9a87c3f1
def iw:Nat:=0xbf58476d1ce4e5b994d049bb133111eb
def ix:Nat:=0x2545f4914f6cdd1d6c62272e07bb0142
def iy (b w c:Nat):Nat:=
 let s:=match c with
  | 0=>b
  | 1=>xor b iv
  | 2=>xor b iw
  | _=>xor b ix
 zm (xor (xor w (shiftRight w 61)) s) fun x =>
 shiftRight (Nat.mul x (xor x qh)) 104
def gp (salt:Nat):Nat->J->Nat
 | acc,[]=>acc
 | acc,(w,tg)::rest=>zm (Nat.add acc (iy salt w tg)) fun acc' => gp salt acc' rest
def av (salt:Nat) (ws:J):Nat:=land (gp salt 0 ws) 0xFFFFFF
def ba (T i:Nat):Nat:=land (shiftRight T (Nat.mul 24 i)) 0xFFFFFF
def sa (T i:Nat):Nat:=land (shiftRight T (Nat.mul 32 i)) 0xFFFFFFFF
def sc (T h:Nat):Nat->Nat->Nat->Nat
 | 0,lo,_=>lo
 | fuel+1,lo,hi =>
  if ble (Nat.add lo 2) hi then
   zm (Nat.div (Nat.add lo hi) 2) fun mid =>
   if ble (ba T mid) h then sc T h fuel mid hi else sc T h fuel lo mid
  else lo
def dz (NN FL HT:Nat->Nat) (s h:Nat):Nat:=
 let n:=NN s
 if beq n 0 then 999999
 else
  let b:=HT s
  zm (sc b h (FL s) 0 n) fun j =>
  if beq (ba b j) h then j else 999999
def mq (a b:K):Q:=beq a.1 b.1&&beq a.2 b.2
def jy (x:K):J->Option (J)
 | []=>none
 | a::rest =>
  if mq x a then some rest
  else match jy x rest with
   | none=>none
   | some r=>some (a::r)
def jk:J->J->Q
 | [],[]=>true
 | a::as,bs=>match jy a bs with
  | none=>false
  | some bs' => jk as bs'
 | _,_=>false
def ct (a b:K):Q:=
 if beq a.1 b.1 then blt a.2 b.2 else blt a.1 b.1
def fp (x:K):J->J
 | []=>[x]
 | a::rest=>if ct x a then x::a::rest else a::fp x rest
def me:J->J
 | []=>[]
 | a::rest=>fp a (me rest)
def gz:J->J->Q
 | [],_=>false
 | _,[]=>false
 | a::as,b::bs =>
  if mq a b then gz as bs else ct a b
def gh (g:V) (b:J):J:=
 let b':=me (wx g b)
 if gz b' b then b' else b
def ck:List (V)->J->J
 | [],ws=>ws
 | g::rest,ws=>ck rest (gh g ws)
def sb (b:List (V)) (d:J):J:=
 let c:=me d
 match b with
 | []=>c
 | [g]=>gh g c
 | _=>ck b (ck b c)
def qi (m0 d:Nat):Nat:=
 zm (land d m0) fun a =>
 zm (land (shiftRight d 1) m0) fun b =>
 zm (land (shiftRight d 2) m0) fun c =>
 zm (xor m0 (land (shiftRight d 3) m0)) fun nd =>
 zm (xor m0 (land (shiftRight d 4) m0)) fun ne =>
 zm (xor m0 (land (shiftRight d 5) m0)) fun nf =>
 Nat.sub (Nat.add (Nat.add (land nd b) (land nd c)) (Nat.add (land a ne) (land a nf)))
  (land (land a nd) (land (lor b c) (lor ne nf)))
def yg (sh1 m1 m12 w:Nat):Nat:=
 zm (shiftRight w sh1) fun w0 =>
 zm (land w0 m1) fun a =>
 zm (land (shiftRight w0 1) m1) fun b =>
 zm (land (shiftRight w0 2) m1) fun c =>
 zm (land (shiftRight w0 3) m1) fun d =>
 zm (land (shiftRight w0 4) m1) fun e =>
 zm (land (shiftRight w0 5) m1) fun f =>
 zm (xor m1 d) fun nd =>
 zm (xor m1 e) fun ne =>
 zm (xor m1 f) fun nf =>
 zm (xor m1 a) fun na =>
 zm (xor m1 b) fun nb =>
 zm (xor m1 c) fun nc =>
 zm (Nat.sub (Nat.add (Nat.add (land nd b) (land nd c)) (Nat.add (land a ne) (land a nf)))
  (land (land a nd) (land (lor b c) (lor ne nf)))) fun v1 =>
 zm (Nat.sub (Nat.add (Nat.add (land d nb) (land d nc)) (Nat.add (land na e) (land na f)))
  (land (land na d) (land (lor nb nc) (lor e f)))) fun v2 =>
 zm (lor v1 v2) fun u =>
 zm (land u m12) fun hi =>
 lor hi (lor (lor (land v1 (shiftRight v1 1)) (land v2 (shiftRight v2 1)))
   (land (land u m1) (xor m1 (shiftRight hi 1))))
def qb (c:Cfg) (b d:Nat):Q:=
 beq (land (Nat.add (Nat.add b d) c.a29_0) c.b5_0) c.b5_0
def z3 (c:Cfg) (b:Nat):Q:=
 beq (land (Nat.add b c.a29_1) c.b5_1) c.b5_1
def gj (b:Nat):Nat->Nat->K
 | 0,j=>(0,j)
 | fuel+1,j =>
  let t:=Nat.div (Nat.mul (Nat.add j 1) j) 2
  if ble t b then gj b fuel (Nat.add j 1)
  else (Nat.sub b (Nat.div (Nat.mul j (Nat.sub j 1)) 2),j)
def jw:Nat->J->K
 | _,[]=>(0,0)
 | 0,a::_=>a
 | k+1,_::rest=>jw k rest
def ms:Nat->J->J
 | _,[]=>[]
 | 0,_::rest=>rest
 | k+1,a::rest=>a::ms k rest
def bb (all1v g:Nat) (d:J):J:=
 if ble g 32 then
  zm (Nat.sub g 1) fun c =>
  zm (shiftRight c 1) fun i =>
  let u:=beq (land c 1) 1
  let (a,ta):=jw i d
  let e:=if beq ta 3 then 2 else 0
  zm (xor a all1v) fun w =>
  let r:=ms i d
  if u then (w,e)::(a,0)::r else (w,e)::r
 else
  zm (Nat.sub g 33) fun rem =>
  let s:=beq (land rem 1) 1
  let t:=beq (land (shiftRight rem 1) 1) 1
  let v:=beq (land (shiftRight rem 2) 1) 1
  let (i,j):=gj (shiftRight rem 3) 16 1
  let (a,ta):=jw i d
  let (b,tb):=jw j d
  let r:=ms i (ms j d)
  if v then
   let e:=if beq ta 3||beq tb 3 then 1 else 0
   zm (land a b) fun w =>
   let r1:=if s then (b,0)::r else r
   let h:=if t then (a,0)::r1 else r1
   (w,e)::h
  else
   zm (lor a b) fun w =>
   let r1:=if s then (b,if beq tb 3 then 1 else 0)::r else r
   let h:=if t then (a,if beq ta 3 then 1 else 0)::r1 else r1
   (w,0)::h
def mx (all1v:Nat) (xs:J) (PT:Nat->Nat):Nat->Nat->Nat->J
 | 0,_,_=>xs
 | d+1,s,j =>
  zm (sa (PT s) j) fun e =>
  zm (land e 1023) fun code =>
  if beq code 0 then xs
  else zm (land (shiftRight e 10) 8191) fun pidx =>
   bb all1v code (mx all1v xs PT d (Nat.add s 1) pidx)
def a8 (all1v b:Nat) (c:J) (PT:Nat->Nat) (s j:Nat):J:=
 mx all1v c PT (Nat.sub b s) s j
def p4 (shTT c:Nat) (Rtt:Nat->Nat->J) (NN FL HT:Nat->Nat) (s:Nat) (d:J):Q:=
 let b:=sz shTT d
 zm (av c b) fun h =>
 zm (dz NN FL HT s h) fun j =>
 !(beq j 999999)&&jk b (Rtt s j)
def k9 (shTT c:Nat) (e:V) (Rtt:Nat->Nat->J) (NN FL HT:Nat->Nat) (s:Nat) (g:J):Q:=
 let b:=sz shTT g
 zm (av c b) fun h0 =>
 zm (dz NN FL HT s h0) fun j0 =>
 if !(beq j0 999999)&&jk b (Rtt s j0) then true
 else
  let d:=wx e b
  zm (av c d) fun h1 =>
  zm (dz NN FL HT s h1) fun j1 =>
  !(beq j1 999999)&&jk d (Rtt s j1)
def vm (salt:Nat) (Rtt:Nat->Nat->J) (NN FL HT:Nat->Nat)
  (s:Nat):List (V)->J->Q
 | [],ztt =>
  zm (av salt ztt) fun h =>
  zm (dz NN FL HT s h) fun j =>
  !(beq j 999999)&&jk ztt (Rtt s j)
 | g::rest,ztt =>
  zm (av salt ztt) fun h =>
  zm (dz NN FL HT s h) fun j =>
  if !(beq j 999999)&&jk ztt (Rtt s j) then true
  else vm salt Rtt NN FL HT s rest (wx g ztt)
def r9 (shTT b:Nat) (c:List (V)) (Rtt:Nat->Nat->J) (NN FL HT:Nat->Nat) (s:Nat) (d:J):Q:=
 vm b Rtt NN FL HT s c (sz shTT d)
def c4 (shTT c:Nat) (d:List (V)) (e:Nat->V) (Rtt:Nat->Nat->J) (NN FL HT PT:Nat->Nat) (s:Nat) (g:J):Q:=
 let b:=sb d (sz shTT g)
 zm (av c b) fun h =>
 zm (dz NN FL HT s h) fun j =>
 if beq j 999999 then false
 else
  zm (shiftRight (sa (PT s) j) 23) fun aidx =>
  jk b (wx (e aidx) (Rtt s j))
def o5 (c:Cfg):J->Nat×Nat×Y
 | []=>(0,0,[])
 | (w,tg)::rest =>
  let (sC,sU,rs):=o5 c rest
  zm (land w c.lok) fun alo =>
  zm (land (shiftRight w c.k) c.lok) fun ahi =>
  zm (xor alo ahi) fun cw =>
  zm (land cw ahi) fun uw =>
  (lor cw sC,lor uw sU,(w,tg,cw,uw,sC,sU)::rs)
def ez (c:Cfg):J->Nat
 | []=>0
 | (w,_)::rest =>
  Nat.add (qi c.m0 (land (shiftRight w c.sh0) c.m0all)) (ez c rest)
def ey (c:Cfg):J->Nat
 | []=>0
 | (w,_)::rest =>
  Nat.add (yg c.sh1 c.m1 c.m12 w) (ey c rest)
def t3 (z:Nat):J->Q
 | []=>false
 | (w,_)::rest=>beq w z||t3 z rest
def k1 (c:Cfg) (g h s i:Nat) (d:Unit->J) (e:J->Q):Q:=
 if blt (Nat.add g 1) h then true
 else if beq g 0 then
  let b:=d ()
  match b with
  | [(w,_)]=>if beq w c.goalv then e b else true
  | _=>true
 else if !(beq s c.lok) then true
 else if ble h 11 then
  let j:=Nat.sub (Nat.add g 1) h
  if beq j 0 then
   if !(beq i c.lok) then true
   else
    let b:=d ()
    if !(qb c (ez c b) 0) then true else e b
  else if beq j 1 then
   let b:=d ()
   if beq i c.lok||z3 c (ey c b) then e b else true
  else e (d ())
 else e (d ())
def l8 (c:Cfg) (d e:Nat) (g:J->Q) (z h a t u v b w x y i j:Nat) (h0 h1:Q) (s:Unit->J):Q:=
 zm (land z c.lok) fun zlo =>
 zm (land (shiftRight z c.k) c.lok) fun zhi =>
 zm (xor zlo zhi) fun cz =>
 zm (land cz zhi) fun uz =>
 let h2:=k1 c d (Nat.sub e 1) (lor cz i) (lor uz j) (fun ()=>(z,h)::s ()) g
 let h3:=if h2&&h1 then k1 c d e (lor cz (lor x i)) (lor uz (lor y j)) (fun ()=>(z,h)::(b,w)::s ()) g else h2
 let h4:=if h3&&h0 then k1 c d e (lor cz (lor u i)) (lor uz (lor v j)) (fun ()=>(z,h)::(a,t)::s ()) g else h3
 if h4&&h0&&h1 then k1 c d (Nat.add e 1) (lor cz (lor u (lor x i))) (lor uz (lor v (lor y j))) (fun ()=>(z,h)::(a,t)::(b,w)::s ()) g else h4
def a5 (c:Cfg) (b d t:Nat) (u:J) (e:J->Q) (g:Q) (a ta v w h i:Nat) (j:Unit->J):Q:=
 if (if g then beq ta 0||beq ta 3 else !(beq ta 1)&&!(beq ta 2)) then
  zm (xor a c.all1v) fun z =>
  if beq z 0||beq z c.all1v||t3 z u then true
  else
   zm (land z c.lok) fun zlo =>
   zm (land (shiftRight z c.k) c.lok) fun zhi =>
   zm (xor zlo zhi) fun cz =>
   zm (land cz zhi) fun uz =>
   let s:=if beq ta 3 then 2 else 0
   let x:=k1 c b d (lor cz h) (lor uz i) (fun ()=>(z,s)::j ()) e
   if !x then false
   else if (if g then beq ta 0 else !(beq ta 3))&&ble 2 t then
    k1 c b (Nat.add d 1) (lor cz (lor v h)) (lor uz (lor w i))
     (fun ()=>(z,s)::(a,0)::j ()) e
   else true
 else true
def a4 (nf:Nat->Nat->Nat->Nat->Nat->Nat->(Unit->J)->Q)
  (preC preU:Nat) (pre:J):Y->Q
 | []=>true
 | (a,ta,ca,ua,sC,sU)::suf =>
  nf a ta ca ua (lor preC sC) (lor preU sU) (fun ()=>pre++suf.map (fun t=>(t.1,t.2.1))) &&
  a4 nf (lor preC ca) (lor preU ua) (pre++[(a,ta)]) suf
def f5 (c:Cfg) (e g:Nat) (h:J) (i:J->Q) (a ta j s b d t u v w:Nat) (x:Unit->J):Q:=
 let y:=
  if !(beq ta 2)&&!(beq d 2) then
   zm (lor a b) fun z =>
   if beq z 0||beq z c.all1v||t3 z h then true
   else
    l8 c e g i z 0 a (if beq ta 3 then 1 else 0) j s b (if beq d 3 then 1 else 0) t u v w
     (!(beq ta 1)) (!(beq d 1)) x
  else true
 if !y then false
 else if !(beq ta 1)&&!(beq d 1) then
  zm (land a b) fun z =>
  if beq z 0||beq z c.all1v||t3 z h then true
  else
   l8 c e g i z (if beq ta 3||beq d 3 then 1 else 0) a 0 j s b 0 t u v w
    (beq ta 0) (beq d 0) x
 else true
def t7 (pf:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->(Unit->J)->Q)
  (a ta ca ua pmC pmU:Nat) (pre:J):Y->Q
 | []=>true
 | (b,tb,cb,ub,sC,sU)::suf =>
  pf a ta ca ua b tb cb ub (lor pmC sC) (lor pmU sU)
   (fun ()=>pre++suf.map (fun t=>(t.1,t.2.1))) &&
  t7 pf a ta ca ua (lor pmC cb) (lor pmU ub) (pre++[(b,tb)]) suf
def m4 (pf:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->(Unit->J)->Q)
  (preC preU:Nat) (pre:J):Y->Q
 | []=>true
 | (a,ta,ca,ua,_,_)::suf =>
  t7 pf a ta ca ua preC preU pre suf &&
  m4 pf (lor preC ca) (lor preU ua) (pre++[(a,ta)]) suf
def p9 (c:Cfg) (g:J->Q) (d:Nat) (b:J):Q:=
 let e:=b.length
 let h:=Nat.sub (Nat.add d 2) e
 let (_,_,cu):=o5 c b
 (if ble 1 h then a4 (a5 c d e h b g false) 0 0 [] cu else true) &&
 m4 (f5 c d e b g) 0 0 [] cu
def s5 (c:Cfg):Nat->J->Q
 | 0,ws=>match ws with | [(w,_)]=>!(beq w c.goalv) | _=>true
 | ns+1,ws=>p9 c (fun _=>false) ns ws
def bar (c:Cfg) (findFn:Nat->J->Q) (R:Nat->Nat->J):Nat->Nat->Q
 | 0,i=>match R 0 i with | [(w,_)]=>!(beq w c.goalv) | _=>true
 | ns+1,i =>
  p9 c (fun nxt =>
   if findFn ns nxt then true
   else if beq ns 0 then false
   else s5 c ns nxt) ns (R (Nat.add ns 1) i)
def span (f:Nat->Q):Nat->Nat->Q
 | 0,_=>true
 | n+1,i=>f i&&span f n (Nat.add i 1)
def q1 (n r:Nat):F n:=fun i=>r.testBit i.val
def v7 {n:Nat} (x:F n):Nat:=
 (finRange n).foldr (fun i acc=>if x i then acc|||(1 <<< i.val) else acc) 0
lemma qp {m:Nat} (hm:m≠0):(1:Nat).testBit m=false:=by
 cases m with
 | zero=>contradiction
 | succ k=>simp [Nat.testBit_succ]
lemma z7 {x m:Nat} (h:x.testBit m=true) :(x / 2 ^ m) % 2=1:=by rw [nTD] at h;exact of_decide_eq_true h
lemma z5 {x m:Nat} (h:x.testBit m=false) :(x / 2 ^ m) % 2=0:=by
 rw [nTD] at h
 have:=of_decide_eq_false h
 omega
lemma zg {x m:Nat} (h:x.testBit m=true):2 ^ m<=x:=by
 have b:=z7 h;have c:1<=x / 2 ^ m:=by generalize x / 2 ^ m=q at b ⊢;omega
 have h3:=Nat.mul_le_mul_right (2 ^ m) c;have h4:=Nat.div_mul_le_self x (2 ^ m);omega
lemma vz {y m:Nat} (h:y.testBit m=false) :y % 2 ^ (m+1) < 2 ^ m:=by
 have b:(y / 2 ^ m) % 2=0:=z5 h;have c:y % 2 ^ (m+1) / 2 ^ m=(y / 2 ^ m) % 2:=by rw [Nat.pow_succ,Nat.mod_mul_right_div_self]
 have d:y % 2 ^ (m+1) / 2 ^ m=0:=by rw [c,b]
 exact (Nat.div_eq_zero_iff.1 d).resolve_left (Nat.ne_of_gt (n2P m))
lemma vk {y m:Nat} (h:y.testBit m=false) (k:Nat) :(y+2 ^ m).testBit k=if k=m then true else y.testBit k:=by
 by_cases c:k=m
 . subst c;have h0:=z5 h;rw [nTD,Nat.add_div_right _ (n2P k)];simp;omega
 . simp only [c,↓reduceIte];by_cases d:k < m
   . have e:2 ^ m=2 ^ k*2 ^ (m - k):=by
      rw [<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt d)]
     have b:1<=m - k:=by omega
     have hev:2 ^ (m - k) % 2=0:=by obtain ⟨q,g⟩:=Nat.exists_eq_add_of_le' b;rw [g,Nat.pow_succ];omega
     rw [nTD,nTD,e,
       Nat.mul_comm (2 ^ k),Nat.add_mul_div_right _ _ (n2P k)]
     have:(y / 2 ^ k+2 ^ (m - k)) % 2=(y / 2 ^ k) % 2:=by omega
     rw [this]
   . have b:m+1<=k:=by omega
     have i:y % 2 ^ (m+1)+2 ^ m < 2 ^ (m+1):=by have hltm:=vz h;have hpw:2 ^ (m+1)=2 ^ m*2:=Nat.pow_succ 2 m;omega
     have j:(y+2 ^ m) / 2 ^ (m+1)=y / 2 ^ (m+1):=by
      have s:y=2 ^ (m+1)*(y / 2 ^ (m+1))+y % 2 ^ (m+1):=
       (Nat.div_add_mod y (2 ^ (m+1))).symm
      conv_lhs=>rw [s,nAA]
      rw [Nat.mul_add_div (n2P (m+1)),Nat.div_eq_of_lt i,nAZ]
     have t:2 ^ k=2 ^ (m+1)*2 ^ (k - (m+1)):=by rw [<- Nat.pow_add,Nat.add_sub_cancel' b]
     rw [nTD,nTD,t,
       <- Nat.div_div_eq_div_mul,<- Nat.div_div_eq_div_mul,j]
lemma qs {y m:Nat} (h:y.testBit m=false) :y+2 ^ m=y^^^2 ^ m:=by
 apply nEQ;intro k;rw [vk h,nTX,nT2];by_cases b:k=m
 . subst b;simp [h]
 . simp [b,Ne.symm b]
lemma jl {n:Nat} (x:F n) (k:Nat) :(v7 x).testBit k=if h:k < n then x ⟨k,h⟩ else false:=by
 have s:∀ (l:List (Fin n)),l.Nodup ->
   (l.foldr (fun i acc=>if x i then acc|||(1 <<< i.val) else acc) 0).testBit k =
   if h:k < n then (if ⟨k,h⟩∈l then x ⟨k,h⟩ else false) else false:=by
  intro l u;induction l with
  | nil=>simp
  | cons a t ih =>
   obtain ⟨v,w⟩:=List.nodup_cons.1 u;simp only [lFC];have g:=ih w;by_cases d:x a=true
   . simp only [d,↓reduceIte,nTO,Nat.testBit_shiftLeft,g];by_cases b:k < n
     . simp only [b,↓reduceDIte,lMM];by_cases c:(⟨k,b⟩:Fin n)=a
       . subst c;simp [d]
       . have y:k≠a.val:=fun e=>c (Fin.ext e)
         have z:(decide (a.val<=k)&&(1:Nat).testBit (k - a.val))=false:=by
          cases j:decide (a.val<=k)
          . simp
          . have j':a.val<=k:=of_decide_eq_true j;simp [qp (by omega:k - a.val≠0)]
         simp [c,z]
     . have y:a.val < k:=by omega
       simp [b,qp (by omega:k - a.val≠0)]
   . simp only [d,bFT,↓reduceIte,g];by_cases b:k < n
     . simp only [b,↓reduceDIte,lMM];by_cases c:(⟨k,b⟩:Fin n)=a
       . rw [c];simp [v,d]
       . simp [c]
     . simp [b]
 have h:=s (finRange n) (List.nodup_finRange n);simpa [v7,lMFR] using h
lemma ku {n:Nat} (x:F n):v7 x < 2 ^ n:=by
 apply nLPT
 intro k hk;rw [jl];simp [show ¬ k < n by omega]
lemma q57 {n:Nat} (x:F n):q1 n (v7 x)=x:=by funext i;simp [q1,jl,i.isLt]
def d7 {n:Nat} (b:M) (f:u7 n):Nat:=
 b.foldr (fun r acc=>acc*2+if f (q1 n r) then 1 else 0) 0
def u9 (n:Nat) (f:u7 n):Nat:=d7 (range (2 ^ n)) f
lemma z8 {n:Nat} (b:M) (f:u7 n) (i:Nat) :(d7 b f).testBit i=match b[i]? with | some r=>f (q1 n r) | none=>false:=by
 induction b generalizing i with
 | nil=>simp [d7]
 | cons r rest ih =>
  have c:d7 (r::rest) f=d7 rest f*2+if f (q1 n r) then 1 else 0:=rfl
  rw [c];cases i with
  | zero => cases h:f (q1 n r)<;>simp [h,Nat.testBit_zero]
  | succ k =>
   rw [Nat.testBit_succ];have d:(d7 rest f*2+if f (q1 n r) then 1 else 0) / 2=d7 rest f:=by cases h:f (q1 n r)<;>simp only [h,↓reduceIte,bFT]<;>omega
   rw [d];exact ih k
lemma gk {n:Nat} (b:M):d7 (n:=n) b (fun _=>false)=0:=by apply nEQ;intro i;rw [z8];cases b[i]?<;>simp
lemma bc {n:Nat} (b:M):d7 (n:=n) b (fun _=>true)=2 ^ b.length - 1:=by
 apply nEQ;intro i;rw [z8,nTB];by_cases c:i < b.length
 . rw [lGEQ c];simp [c]
 . rw [List.getElem?_eq_none (by omega)];simp [c]
lemma gx {n:Nat} (b:M) (f:u7 n) :d7 b (invF f)=xor (d7 b f) (2 ^ b.length - 1):=by
 apply nEQ;intro i;rw [nXO,nTX,z8,z8,nTB];by_cases c:i < b.length
 . rw [lGEQ c];simp [c,invF]
 . rw [List.getElem?_eq_none (by omega)];simp [c]
lemma ls {n:Nat} (b:M) (f g:u7 n) :d7 b (meetF f g)=land (d7 b f) (d7 b g):=by apply nEQ;intro i;rw [nLA,nTA,z8,z8,z8];cases b[i]?<;>simp [meetF]
lemma lr {n:Nat} (b:M) (f g:u7 n) :d7 b (joinF f g)=lor (d7 b f) (d7 b g):=by apply nEQ;intro i;rw [nLO,nTO,z8,z8,z8];cases b[i]?<;>simp [joinF]
lemma vr {n:Nat} (f:u7 n) (r:Nat) :(u9 n f).testBit r=if r < 2 ^ n then f (q1 n r) else false:=by
 unfold u9;rw [z8];by_cases b:r < 2 ^ n
 . rw [lGEQ (by simp [b])];simp [b]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [b]
lemma yc {n:Nat}:Function.Injective (u9 n):=by
 intro f g h;funext x;have b:=congrArg (fun m=>m.testBit (v7 x)) h
 rw [vr,vr] at b;simp only [ku x,↓reduceIte,q57] at b;exact b
lemma my {n:Nat} (b:M) (f:u7 n) :shiftRight (d7 (b++range (2 ^ n)) f) b.length=u9 n f:=by
 apply nEQ;intro i;change ((d7 (b++range (2 ^ n)) f) >>> b.length).testBit i=(u9 n f).testBit i;rw [Nat.shiftRight_eq_div_pow,Nat.testBit_div_two_pow,z8,vr];rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel];by_cases c:i < 2 ^ n
 . rw [lGEQ (by simp [c])];simp [c]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [c]
lemma ik {n:Nat} (b:M) :Function.Injective (d7 (n:=n) (b++range (2 ^ n))):=by
 intro f g h;apply yc
 rw [<- my b f,<- my b g,h]
def yh {n:Nat} (i j:Fin n) (x:F n):F n:=
 fun k=>x (if k=i then j else if k=j then i else k)
lemma nt {n:Nat} (i j:Fin n) (x:F n) :yh i j (yh i j x)=x:=by
 funext k;unfold yh;by_cases c:k=i
 . rw [c];by_cases b:j=i<;>simp [b]
 . by_cases b:k=j
   . rw [b];simp [Ne.symm c]
   . simp [c,b]
def yu (i j r:Nat):Nat:=
 let b:=r.testBit i
 let c:=r.testBit j
 if b==c then r else xor r (lor (1 <<< i) (1 <<< j))
lemma lg {n i j r:Nat} (hi:i < n) (hj:j < n) (b:r < 2 ^ n) :yu i j r < 2 ^ n:=by
 unfold yu;dsimp only
 split
 . exact b
 . apply nLPT
   intro k c;rw [nXO,nTX,nLO,nTO,
    Nat.testBit_shiftLeft,Nat.testBit_shiftLeft]
   have d:r.testBit k=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le b (nPLR (by omega) c));simp [d,qp (by omega:k - i≠0),qp (by omega:k - j≠0)]
lemma z9 {n i j r:Nat} (g:i < n) (h:j < n) :q1 n (yu i j r)=yh ⟨i,g⟩ ⟨j,h⟩ (q1 n r):=by
 funext k;simp only [q1,yh,yu];by_cases d:r.testBit i=r.testBit j
 . simp only [d,beq_self_eq_true,↓reduceIte];by_cases b:k=⟨i,g⟩
   . rw [b];simp [d]
   . by_cases c:k=⟨j,h⟩
     . rw [c];split<;>simp [d]
     . simp [b,c]
 . have w:(r.testBit i==r.testBit j)=false:=beq_false_of_ne d;simp only [w,bFT,↓reduceIte,nXO,nTX,nLO,
     nTO,Nat.testBit_shiftLeft]
   by_cases b:k=⟨i,g⟩
   . subst b;simp only [↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero];cases s:r.testBit i<;>cases t:r.testBit j<;>simp_all
   . by_cases c:k=⟨j,h⟩
     . subst c;simp only [b,↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero];cases s:r.testBit i<;>cases t:r.testBit j<;>simp_all
     . have s:k.val≠i:=fun e=>b (Fin.ext e)
       have t:k.val≠j:=fun e=>c (Fin.ext e)
       have u:∀ m,k.val≠m->(decide (m<=k.val)&&(1:Nat).testBit (k.val - m))=false:=by
        intro m hne;cases v:decide (m<=k.val)
        . simp
        . have v':m<=k.val:=of_decide_eq_true v;simp [qp (by omega:k.val - m≠0)]
       simp [b,c,u i s,u j t]
def w9 (n i j:Nat):Nat×Nat×Nat×Nat:=
 let d:=2 ^ j - 2 ^ i
 let N:=2 ^ n
 let b:=(range N).foldr (fun x acc=>acc*2+if !(x.testBit i)&&x.testBit j then 1 else 0) 0
 let c:=(range N).foldr (fun x acc=>acc*2+if x.testBit i&&!(x.testBit j) then 1 else 0) 0
 let e:=(range N).foldr (fun x acc=>acc*2+if x.testBit i==x.testBit j then 1 else 0) 0
 (d,b,c,e)
lemma jx (N:Nat) (P:Nat->Q) (r:Nat) :((range N).foldr (fun x acc=>acc*2+if P x then 1 else 0) 0).testBit r = if r < N then P r else false:=by
 have c:∀ (l:M) (r:Nat),
    (l.foldr (fun x acc=>acc*2+if P x then 1 else 0) 0).testBit r =
    match l[r]? with | some x=>P x | none=>false:=by
   intro l;induction l with
   | nil=>intro r;simp
   | cons a t ih =>
    intro r;simp only [lFC];cases r with
    | zero=>cases h:P a<;>simp [h,Nat.testBit_zero]
    | succ k =>
     rw [Nat.testBit_succ];have d:((t.foldr (fun x acc=>acc*2+if P x then 1 else 0) 0)*2+if P a then 1 else 0) / 2
       = t.foldr (fun x acc=>acc*2+if P x then 1 else 0) 0:=by
      cases P a<;>simp only [↓reduceIte,bFT]<;>omega
     rw [d];exact ih k
 rw [c];by_cases b:r < N
 . rw [lGEQ (by simp [b])];simp [b]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [b]
lemma j3 {n i j:Nat} (h6:i < j) (s:j < n) (g:u7 n) :im (w9 n i j) (u9 n g) = u9 n (fun x=>g (yh ⟨i,by omega⟩ ⟨j,s⟩ x)):=by
 have v:i < n:=by omega
 have hpow:2 ^ i < 2 ^ j:=Nat.pow_lt_pow_right (by omega) h6;have ht:∀ x m,x.testBit m=true->x - 2 ^ m+2 ^ m=x/\(x - 2 ^ m).testBit m=false:=by
   intro x m hm;have h:2 ^ m<=x:=zg hm;refine ⟨Nat.sub_add_cancel h,?_⟩
   rw [nTD];have hd:(x - 2 ^ m) / 2 ^ m=x / 2 ^ m - 1:=by
     have u:x=(x - 2 ^ m)+2 ^ m:=(Nat.sub_add_cancel h).symm;have t:((x - 2 ^ m)+2 ^ m) / 2 ^ m=(x - 2 ^ m) / 2 ^ m+1:=
       Nat.add_div_right (x - 2 ^ m) (n2P m)
     rw [<- u] at t;rw [t];simp
   have he:=z7 hm;rw [hd];simp;generalize x / 2 ^ m=q at he ⊢;omega
 have h12:∀ (a b:Nat),a < b->b < n->∀ x < 2 ^ n,
     (x.testBit a=false->x.testBit b=true->x - (2 ^ b - 2 ^ a)=yu a b x) /\
     (x.testBit a=true->x.testBit b=false->x+(2 ^ b - 2 ^ a)=yu a b x):=by
   intro a b hf hbn x _;have hu:2 ^ a < 2 ^ b:=Nat.pow_lt_pow_right (by omega) hf;have b1:∀ (m k:Nat),(decide (m<=k)&&(1:Nat).testBit (k - m))=decide (m=k):=by
     intro m k;by_cases hg:m=k
     . subst hg;simp
     . cases h:decide (m<=k)
       . simp [hg]
       . have h':m<=k:=of_decide_eq_true h;simp [hg,qp (by omega:k - m≠0)]
   constructor
   . intro hv hw;have ⟨h4,h7⟩:=ht x b hw;have h13:(x - 2 ^ b).testBit a=false:=by
       have t:=qs h7;rw [h4] at t;have h5:=congrArg (fun z=>z.testBit a) t
       rw [nTX,nT2,hv] at h5;have hba:b≠a:=by omega
       simp [hba] at h5;exact h5
     have t:x - (2 ^ b - 2 ^ a)=(x - 2 ^ b)+2 ^ a:=by
       conv_lhs=>rw [<- h4]
       rw [Nat.add_sub_assoc (Nat.sub_le _ _),Nat.sub_sub_self (le_of_lt hu)]
     rw [t];apply nEQ;intro k;have u:x=(x - 2 ^ b)^^^2 ^ b:=by rw [<- qs h7,h4]
     have h3:(x - 2 ^ b)+2 ^ a=(x - 2 ^ b)^^^2 ^ a:=qs h13;unfold yu;dsimp only;simp only [hv,hw];change ((x - 2 ^ b)+2 ^ a).testBit k=(xor x (lor (1 <<< a) (1 <<< b))).testBit k;rw [h3];conv_rhs=>rw [u]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,nT2,
         nT2,b1 a k,b1 b k]
     by_cases h8:a=k<;>by_cases h9:b=k<;>try omega
     . subst h8;simp [show b≠a by omega]
     . subst h9;simp [show a≠b by omega]
     . simp [h8,h9]
   . intro hx hy;have ⟨h4,h7⟩:=ht x a hx;have h14:(x - 2 ^ a).testBit b=false:=by
       have t:=qs h7;rw [h4] at t;have h5:=congrArg (fun z=>z.testBit b) t
       rw [nTX,nT2,hy] at h5;have hf':a≠b:=by omega
       simp [hf'] at h5;exact h5
     have t:x+(2 ^ b - 2 ^ a)=(x - 2 ^ a)+2 ^ b:=by
       conv_lhs=>rw [<- h4]
       rw [nAA,Nat.add_sub_cancel' (le_of_lt hu)]
     rw [t];apply nEQ;intro k;have u:x=(x - 2 ^ a)^^^2 ^ a:=by rw [<- qs h7,h4]
     have h3:(x - 2 ^ a)+2 ^ b=(x - 2 ^ a)^^^2 ^ b:=qs h14;unfold yu;dsimp only;simp only [hx,hy];change ((x - 2 ^ a)+2 ^ b).testBit k=(xor x (lor (1 <<< a) (1 <<< b))).testBit k;rw [h3];conv_rhs=>rw [u]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,nT2,
         nT2,b1 a k,b1 b k]
     by_cases h8:a=k<;>by_cases h9:b=k<;>try omega
     . subst h8;simp [show b≠a by omega]
     . subst h9;simp [show a≠b by omega]
     . simp [h8,h9]
 have xi:(2 ^ (j - i) - 1) % 2=1:=by
   have xs:1<=j - i:=by omega
   have hev:2 ^ (j - i) % 2=0:=by obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' xs;rw [hm,Nat.pow_succ];omega
   have h15:2<=2 ^ (j - i):=by have:=nPLR (by omega:0 < 2) xs;simpa using this
   omega
 have h10:∀ r,(r+(2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r;have ha:2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by rw [Nat.mul_sub,Nat.mul_one,<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt h6)]
   have u:(r+(2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i+(2 ^ (j - i) - 1):=by rw [ha,Nat.mul_comm,Nat.add_mul_div_right _ _ (n2P i)]
   rw [nTD,nTD,u];generalize r / 2 ^ i=q;generalize 2 ^ (j - i) - 1=c at xi ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hh:∀ r,2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r h;have ha:2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by rw [Nat.mul_sub,Nat.mul_one,<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt h6)]
   have u:(r - (2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i - (2 ^ (j - i) - 1):=by
     have t:r=(r - (2 ^ j - 2 ^ i))+(2 ^ j - 2 ^ i):=(Nat.sub_add_cancel h).symm;have h3:((r - (2 ^ j - 2 ^ i))+2 ^ i*(2 ^ (j - i) - 1)) / 2 ^ i
         = (r - (2 ^ j - 2 ^ i)) / 2 ^ i+(2 ^ (j - i) - 1):=by
       rw [Nat.mul_comm (2 ^ i),Nat.add_mul_div_right _ _ (n2P i)]
     rw [<- ha,<- t] at h3;rw [h3,Nat.add_sub_cancel]
   have hb:2 ^ (j - i) - 1<=r / 2 ^ i:=by rw [ha] at h;exact (Nat.le_div_iff_mul_le (n2P i)).2 (by rw [Nat.mul_comm];exact h)
   rw [nTD,nTD,u];generalize r / 2 ^ i=q at hb ⊢;generalize 2 ^ (j - i) - 1=c at xi hb ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have h16:∀ (x d k:Nat),(shiftLeft x d).testBit k=(decide (d<=k)&&x.testBit (k - d)):=by intro x d k;change (x <<< d).testBit k=_;rw [Nat.testBit_shiftLeft]
 apply nEQ
 intro r;unfold im w9;simp only [nLO,nLA,Nat.shiftRight_eq,Nat.shiftRight_eq_div_pow,
   nTO,nTA,Nat.testBit_div_two_pow,h16,
   jx,vr]
 by_cases hr:r < 2 ^ n
 . simp only [hr,↓reduceIte];have hsw:=h12 i j h6 s r hr;cases w:r.testBit i<;>cases y:r.testBit j
   .
     have h17:yh ⟨i,v⟩ ⟨j,s⟩ (q1 n r)=q1 n r:=by rw [<- z9 v s];unfold yu;simp [w,y]
     rw [h17];have h18:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [h10,w];rfl
     have x2:2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=true:=by intro h;rw [hh r h,w];rfl
     have hj:2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
       intro h;have u:(r - (2 ^ j - 2 ^ i))+2 ^ j=r+2 ^ i:=by omega
       have hb:1<=r / 2 ^ j:=by
         have h19:r / 2 ^ j≠0:=by
           intro hz;have hlt:r < 2 ^ j:=(Nat.div_eq_zero_iff.1 hz).resolve_left (Nat.ne_of_gt (n2P j));have x3:r - (2 ^ j - 2 ^ i) < 2 ^ i:=by omega
           have hbi:(r - (2 ^ j - 2 ^ i)).testBit i=false:=Nat.testBit_lt_two_pow x3
           have:=x2 h;rw [hbi] at this;cases this
         generalize r / 2 ^ j=q at h19 ⊢;omega
       have h20:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=r / 2 ^ j - 1:=by
         have t:(r+2 ^ i) / 2 ^ j=r / 2 ^ j:=by
           have h21:r % 2 ^ j+2 ^ i < 2 ^ j:=by
            have hm0:(r % 2 ^ j).testBit i=false:=by rw [Nat.testBit_mod_two_pow];simp [h6,w]
            have h22:r % 2 ^ j < 2 ^ j:=Nat.mod_lt r (n2P j);apply nLPT;intro k hk;rw [vk hm0];have hne:k≠i:=by omega
            simp only [hne,↓reduceIte];exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h22 (nPLR (by omega) hk))
           have h11:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm;conv_lhs=>rw [h11,nAA]
           rw [Nat.mul_add_div (n2P j),Nat.div_eq_of_lt h21,nAZ]
         have h3:((r - (2 ^ j - 2 ^ i))+2 ^ j) / 2 ^ j=(r - (2 ^ j - 2 ^ i)) / 2 ^ j+1:=
           Nat.add_div_right _ (n2P j)
         rw [u,t] at h3;omega
       have h23:=z5 y;rw [nTD,h20];simp
       generalize r / 2 ^ j=q at hb h23 ⊢;omega
     have a1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split<;>simp [h18]
     have a2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases h:2 ^ j - 2 ^ i<=r
       . simp [h,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hj h]
       . simp [h]
     rw [a1,a2];simp
   .
     have h24:2 ^ j<=r:=zg y;have h:2 ^ j - 2 ^ i<=r:=le_trans (Nat.sub_le _ _) h24;have h0:r - (2 ^ j - 2 ^ i)=yu i j r:=hsw.1 w y;have hn:r - (2 ^ j - 2 ^ i) < 2 ^ n:=by omega
     have hp:(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       rw [h0];have:=congrFun (z9 v s (r:=r)) ⟨i,v⟩
       simpa [q1,yh,y] using this
     have hs:(r - (2 ^ j - 2 ^ i)).testBit j=false:=by
       rw [h0];have:=congrFun (z9 v s (r:=r)) ⟨j,s⟩
       simpa [q1,yh,show (⟨j,s⟩:Fin n)≠⟨i,v⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,w] using this
     have h25:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [h10,w];rfl
     have a1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split<;>simp [h25]
     rw [a1];simp [h,hn,hp,hs];rw [h0,z9 v s]
   .
     have h0:r+(2 ^ j - 2 ^ i)=yu i j r:=hsw.2 w y;have hn:r+(2 ^ j - 2 ^ i) < 2 ^ n:=by rw [h0];exact lg v s hr
     have hp:(r+(2 ^ j - 2 ^ i)).testBit i=false:=by
       rw [h0];have:=congrFun (z9 v s (r:=r)) ⟨i,v⟩
       simpa [q1,yh,y] using this
     have hs:(r+(2 ^ j - 2 ^ i)).testBit j=true:=by
       rw [h0];have:=congrFun (z9 v s (r:=r)) ⟨j,s⟩
       simpa [q1,yh,show (⟨j,s⟩:Fin n)≠⟨i,v⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,w] using this
     have x2:2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by intro h;rw [hh r h,w];rfl
     have a2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases h:2 ^ j - 2 ^ i<=r
       . simp [h,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,x2 h]
       . simp [h]
     rw [a2];simp [hn,hp,hs];rw [h0,z9 v s]
   .
     have h26:yh ⟨i,v⟩ ⟨j,s⟩ (q1 n r)=q1 n r:=by rw [<- z9 v s];unfold yu;simp [w,y]
     rw [h26];have h27:(r+(2 ^ j - 2 ^ i)).testBit j=false:=by
       have hle_i:2 ^ i<=r:=zg w;have h28:(r - 2 ^ i) / 2 ^ j=r / 2 ^ j:=by
         have he:(r % 2 ^ j).testBit i=true:=by rw [Nat.testBit_mod_two_pow];simp [h6,w]
         have hmod_i:2 ^ i<=r % 2 ^ j:=zg he;have h11:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm;have h29:r - 2 ^ i=2 ^ j*(r / 2 ^ j)+(r % 2 ^ j - 2 ^ i):=by omega
         have hlt:r % 2 ^ j - 2 ^ i < 2 ^ j:=lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt r (n2P j));rw [h29,Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hlt,nAZ]
       have u:r+(2 ^ j - 2 ^ i)=(r - 2 ^ i)+2 ^ j:=by omega
       rw [nTD,u,Nat.add_div_right _ (n2P j),h28];have hr1:=z7 y;simp;omega
     have x2:2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by intro h;rw [hh r h,w];rfl
     have a1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split<;>simp [h27]
     have a2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases h:2 ^ j - 2 ^ i<=r
       . simp [h,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,x2 h]
       . simp [h]
     rw [a1,a2];simp
 .
   have hc:¬ (r+(2 ^ j - 2 ^ i) < 2 ^ n):=by omega
   simp only [hr,hc,↓reduceIte,Bool.and_false,Bool.false_or];by_cases h:2 ^ j - 2 ^ i<=r
   . by_cases x3:r - (2 ^ j - 2 ^ i) < 2 ^ n
     . have hj:(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
         have hge_q:2 ^ (n - j) - 1<=(r - (2 ^ j - 2 ^ i)) / 2 ^ j:=by
           have u:2 ^ j*(2 ^ (n - j) - 1)=2 ^ n - 2 ^ j:=by rw [Nat.mul_sub,Nat.mul_one,<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt s)]
           have t:2 ^ n - 2 ^ j<=r - (2 ^ j - 2 ^ i):=
            le_trans (Nat.sub_le_sub_left (Nat.sub_le _ _) _) (Nat.sub_le_sub_right (by omega:2 ^ n<=r) _)
           exact (Nat.le_div_iff_mul_le (n2P j)).2 (by rw [Nat.mul_comm,u];exact t)
         have hlt_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j < 2 ^ (n - j):=by
           have u:2 ^ n=2 ^ j*2 ^ (n - j):=by rw [<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt s)]
           exact (Nat.div_lt_iff_lt_mul (n2P j)).2 (by rw [Nat.mul_comm,<- u];exact x3)
         have h30:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=2 ^ (n - j) - 1:=by omega
         rw [nTD,h30];have hc' : 1<=n - j:=by omega
         have hev:2 ^ (n - j) % 2=0:=by obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hc';rw [hm,Nat.pow_succ];omega
         have h15:2<=2 ^ (n - j):=by have:=nPLR (by omega:0 < 2) hc';simpa using this
         simp;omega
       simp [h,x3,hj]
     . simp [h,x3]
   . simp [h]
def de (n:Nat) (b:J):V:=
 b.map fun p=>w9 n p.1 p.2
def kq (n:Nat) (b:J):Q:=
 b.all fun p=>decide (p.1 < p.2)&&decide (p.2 < n)
def zc {n:Nat}:J->(F n)->(F n)
 | [],x=>x
 | (i,j)::rest,x =>
  if h:i < n/\j < n then yh ⟨i,h.1⟩ ⟨j,h.2⟩ (zc rest x)
  else zc rest x
lemma wv {n:Nat} (c:J) (x:F n) :zc c.reverse (zc c x)=x:=by
 have d:∀ (a b:J) (y:F n),
    zc (a++b) y=zc a (zc b y):=by
  intro a;induction a with
  | nil=>intro b y;rfl
  | cons p t ih =>
    intro b y;rcases p with ⟨i,j⟩
    simp only [lCA,zc];split<;>rw [ih]
 induction c generalizing x with
 | nil=>rfl
 | cons p t ih =>
  rcases p with ⟨i,j⟩
  simp only [lRC,d,zc]
  split
  . rename_i h
    rw [nt,ih]
  . exact ih x
lemma jm {n:Nat} (b:J) (c:kq n b=true) (g:u7 n) :ym (de n b) (u9 n g)=u9 n (fun x=>g (zc b x)):=by
 induction b generalizing g with
 | nil=>rfl
 | cons p rest ih =>
  rcases p with ⟨i,j⟩
  simp only [kq,List.all_cons,bAT,decide_eq_true_eq] at c;obtain ⟨⟨d,e⟩,h⟩:=c;change ym (w9 n i j::de n rest) (u9 n g)=_;simp only [ym];rw [j3 d e g,ih h];congr 1;funext x;have hlt:i < n/\j < n:=by omega
  simp only [zc]
  split
  . rfl
  . contradiction
def vh {n:Nat} (f:u7 n) (b:V):Prop:=
 ∃ π:(F n)->(F n),
  Function.Bijective π/\(∀ x,f (π x)=f x) /\
  ∀ g:u7 n,ym b (u9 n g)=u9 n (fun x=>g (π x))
lemma kw {n:Nat} (f:u7 n) (b:J) (c:kq n b=true) (d:ym (de n b) (u9 n f)=u9 n f) :vh f (de n b):=by
 refine ⟨zc b,?_,?_,fun g=>jm b c g⟩
 . constructor
   . intro x y h
     have:=congrArg (zc b.reverse) h
     simpa [wv] using this
   . intro y;refine ⟨zc b.reverse y,?_⟩
     have:=wv b.reverse y
     simpa using this
 . intro x;rw [jm b c f] at d;exact congrFun (yc d) x
lemma lx {n:Nat} (f:u7 n):vh f []:=
 ⟨id,Function.bijective_id,fun _=>rfl,fun _=>rfl⟩
lemma wp {n:Nat} {f:u7 n} {s:Nat} {b:List (u7 n×Nat)} (π:(F n)->(F n)) (c:Function.Bijective π) (d:∀ x,f (π x)=f x) (h:TagRun (invF (n:=n)) meetF joinF (fun _=>false) (fun _=>true) f s b) :
  TagRun (invF (n:=n)) meetF joinF (fun _=>false) (fun _=>true) f s
   (b.map fun p=>((fun x=>p.1 (π x)),p.2)):=by
 let φ:u7 n->u7 n:=fun g x=>g (π x)
 have hφ:Function.Injective φ:=by
  intro g1 g2 e;funext y
  obtain ⟨x,rfl⟩:=c.2 y
  exact congrFun e x
 exact @TagRun.map (u7 n) (u7 n) φ hφ
  invF meetF joinF (fun _=>false) (fun _=>true) f
  invF meetF joinF (fun _=>false) (fun _=>true) f
  rfl rfl (funext d) (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) s b h
def z6 (x i:Nat):Nat:=(x / 64 ^ i) % 64
lemma kd (i:Nat):64 ^ i=2 ^ (6*i):=by rw [show (64:Nat)=2 ^ 6 by decide,<- Nat.pow_mul]
lemma qo (x i k:Nat) :(z6 x i).testBit k=if k < 6 then x.testBit (6*i+k) else false:=by
 unfold z6;rw [kd,show (64:Nat)=2 ^ 6 by decide,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
 by_cases b:k < 6
 . simp [b,nAC]
 . simp [b]
lemma wg {x y:Nat} (h:∀ i,z6 x i=z6 y i):x=y:=by
 apply nEQ;intro k;have b:=congrArg (fun z=>z.testBit (k % 6)) (h (k / 6))
 have c:k % 6 < 6:=Nat.mod_lt k (by decide);rw [qo,qo] at b;simp only [c,↓reduceIte,Nat.div_add_mod] at b;exact b
lemma z1 (x i:Nat):z6 (x / 64) i=z6 x (i+1):=by unfold z6;rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm (64 ^ i) 64]
lemma xr:∀ {x y:Nat},(∀ i,z6 y i<=z6 x i)->y<=x:=by
 intro x y h;induction hn:x+y using Nat.strong_induction_on generalizing x y with
 | _ n ih =>
  have h0:y % 64<=x % 64:=by simpa [z6] using h 0
  by_cases hq:x / 64+y / 64 < x+y
  . have hdiv:y / 64<=x / 64:=
     ih (x / 64+y / 64) (by omega) (fun i=>by rw [z1,z1];exact h (i+1)) rfl
    omega
  . omega
lemma gn {x y:Nat} (h:∀ j,z6 x j+z6 y j < 64) (i:Nat) :z6 (x+y) i=z6 x i+z6 y i:=by
 induction i generalizing x y with
 | zero =>
  have b:x % 64+y % 64 < 64:=by simpa [z6] using h 0
  simp only [z6,Nat.pow_zero,Nat.div_one];omega
 | succ i ih =>
  have b:x % 64+y % 64 < 64:=by simpa [z6] using h 0
  have c:(x+y) / 64=x / 64+y / 64:=by omega
  rw [<- z1,c,<- z1,<- z1];exact ih (fun j=>by rw [z1,z1];exact h (j+1))
lemma kc {x y:Nat} (h:∀ j,z6 y j<=z6 x j) (i:Nat) :z6 (x - y) i=z6 x i - z6 y i:=by
 induction i generalizing x y with
 | zero =>
  have b:y % 64<=x % 64:=by simpa [z6] using h 0
  have c:y<=x:=xr h;simp only [z6,Nat.pow_zero,Nat.div_one];omega
 | succ i ih =>
  have b:y % 64<=x % 64:=by simpa [z6] using h 0
  have c:y<=x:=xr h;have d:(x - y) / 64=x / 64 - y / 64:=by omega
  rw [<- z1,d,<- z1,<- z1];exact ih (fun j=>by rw [z1,z1];exact h (j+1))
lemma v9 (x y i:Nat):z6 (land x y) i=land (z6 x i) (z6 y i):=by apply nEQ;intro k;rw [nLA,nLA,nTA,qo,qo,qo];by_cases b:k < 6<;>simp [b,nTA]
lemma wb (x y i:Nat):z6 (lor x y) i=lor (z6 x i) (z6 y i):=by apply nEQ;intro k;rw [nLO,nLO,nTO,qo,qo,qo];by_cases b:k < 6<;>simp [b,nTO]
lemma bf (x y i:Nat):z6 (xor x y) i=xor (z6 x i) (z6 y i):=by apply nEQ;intro k;rw [nXO,nXO,nTX,qo,qo,qo];by_cases b:k < 6<;>simp [b,nTX]
def qe (m e3:Nat):Nat:=
 match m with
 | 0=>0
 | m'+1=>e3+64*qe m' e3
lemma v0 (m e3 i:Nat) (hv:e3 < 64) :z6 (qe m e3) i=if i < m then e3 else 0:=by
 induction m generalizing i with
 | zero=>simp [qe,z6]
 | succ m ih =>
  cases i with
  | zero=>simp only [qe,z6,Nat.pow_zero,Nat.div_one,Nat.zero_lt_succ,↓reduceIte];omega
  | succ k =>
   rw [<- z1];have b:qe (m+1) e3 / 64=qe m e3:=by simp only [qe];omega
   rw [b,ih k];by_cases h:k < m<;>simp [h,show k+1 < m+1↔k < m by omega]
def v6 (a b c d e f:Q):Nat:=
 let g:=!d;let h:=!e;let i:=!f
 (if g&&b then 1 else 0)+(if g&&c then 1 else 0) +
 (if a&&h then 1 else 0)+(if a&&i then 1 else 0) -
 (if (a&&g)&&((b||c)&&(h||i)) then 1 else 0)
def zq (a b c d e f:Q):Nat:=
 max (v6 a b c d e f) (v6 (!a) (!b) (!c) (!d) (!e) (!f))
lemma lz:v6 true true true false false false=3:=by decide
lemma yr:∀ a b c d e f:Q,v6 a b c d e f<=3:=by decide
lemma q52:∀ a b c d e f:Q,zq a b c d e f<=3:=by decide
lemma k7:∀ a b c d e f:Q,v6 a b c d e f<=zq a b c d e f:=by decide
lemma jp:∀ a b c d e f:Q,zq (!a) (!b) (!c) (!d) (!e) (!f)=zq a b c d e f:=by decide
lemma w4:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Q, v6 (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <= v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma kl:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Q, v6 (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <= v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma q14 (b c c1 d e f1 g b2 h i j s:Q) :zq (b||g) (c||b2) (c1||h) (d||i) (e||j) (f1||s) <= zq b c c1 d e f1+zq g b2 h i j s:=by unfold zq;have h1:=w4 b c c1 d e f1 g b2 h i j s;have h2:=kl (!b) (!c) (!c1) (!d) (!e) (!f1) (!g) (!b2) (!h) (!i) (!j) (!s);simp only [Bool.not_or];omega
lemma je (b c c1 d e f1 g b2 h i j s:Q) :zq (b&&g) (c&&b2) (c1&&h) (d&&i) (e&&j) (f1&&s) <= zq b c c1 d e f1+zq g b2 h i j s:=by unfold zq;have h1:=kl b c c1 d e f1 g b2 h i j s;have h2:=w4 (!b) (!c) (!c1) (!d) (!e) (!f1) (!g) (!b2) (!h) (!i) (!j) (!s);simp only [Bool.not_and];omega
lemma wc (w s m i:Nat) :z6 (land (shiftRight w s) (qe m 1)) i = if i < m then (if w.testBit (6*i+s) then 1 else 0) else 0:=by
 rw [v9,v0 m 1 i (by decide)];by_cases b:i < m
 . simp only [b,↓reduceIte];apply nEQ;intro k;rw [nLA,nTA,qo];cases k with
   | zero => simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR];change (w >>> s).testBit (6*i)=_;rw [nTS,nAC s (6*i)];cases h:w.testBit (6*i+s)<;>simp [h]
   | succ k' => rw [qp (by omega),Bool.and_false];cases w.testBit (6*i+s)<;>simp [qp (by omega:k'+1≠0)]
 . simp [b,nLA]
lemma yy (m d i:Nat) :z6 (qi (qe m 1) d) i = if i < m then v6 (d.testBit (6*i)) (d.testBit (6*i+1)) (d.testBit (6*i+2)) (d.testBit (6*i+3)) (d.testBit (6*i+4)) (d.testBit (6*i+5)) else 0:=by
 unfold qi;simp only [v5];have x:∀ s j,z6 (land (shiftRight d s) (qe m 1)) j =
     if j < m then (if d.testBit (6*j+s) then 1 else 0) else 0:=fun s j=>wc d s m j
 have h3:∀ j,z6 (land d (qe m 1)) j =
     if j < m then (if d.testBit (6*j) then 1 else 0) else 0:=fun j=>by
   have:=x 0 j;simpa using this
 have w:∀ s j,z6 (xor (qe m 1) (land (shiftRight d s) (qe m 1))) j =
     if j < m then (if !(d.testBit (6*j+s)) then 1 else 0) else 0:=by
   intro s j;rw [bf,v0 m 1 j (by decide),x s j];by_cases e:j < m
   . simp only [e,↓reduceIte];cases d.testBit (6*j+s)<;>decide
   . simp [e]
 set a:=land d (qe m 1);set b:=land (shiftRight d 1) (qe m 1);set c:=land (shiftRight d 2) (qe m 1);set g:=xor (qe m 1) (land (shiftRight d 3) (qe m 1));set h:=xor (qe m 1) (land (shiftRight d 4) (qe m 1));set t:=xor (qe m 1) (land (shiftRight d 5) (qe m 1));have y:∀ u v:Q,
     land (if u then 1 else 0) (if v then 1 else 0)=if u&&v then 1 else 0:=by
   intro u v;cases u<;>cases v<;>decide
 have h8:∀ u v:Q,
     lor (if u then 1 else 0) (if v then 1 else 0)=if u||v then 1 else 0:=by
   intro u v;cases u<;>cases v<;>decide
 have hL:∀ j,z6 (land g b) j=if j < m then (if !(d.testBit (6*j+3))&&d.testBit (6*j+1) then 1 else 0) else 0:=by
   intro j;rw [v9,w 3 j,x 1 j];by_cases e:j < m
   . simp only [e,↓reduceIte];exact y _ _
   . simp [e]
 have h0:∀ j,z6 (land g c) j=if j < m then (if !(d.testBit (6*j+3))&&d.testBit (6*j+2) then 1 else 0) else 0:=by
   intro j;rw [v9,w 3 j,x 2 j];by_cases e:j < m
   . simp only [e,↓reduceIte];exact y _ _
   . simp [e]
 have h1:∀ j,z6 (land a h) j=if j < m then (if d.testBit (6*j)&&!(d.testBit (6*j+4)) then 1 else 0) else 0:=by
   intro j;rw [v9,h3 j,w 4 j];by_cases e:j < m
   . simp only [e,↓reduceIte];exact y _ _
   . simp [e]
 have h2:∀ j,z6 (land a t) j=if j < m then (if d.testBit (6*j)&&!(d.testBit (6*j+5)) then 1 else 0) else 0:=by
   intro j;rw [v9,h3 j,w 5 j];by_cases e:j < m
   . simp only [e,↓reduceIte];exact y _ _
   . simp [e]
 have h4:∀ j,z6 (land (land a g) (land (lor b c) (lor h t))) j =
     if j < m then (if (d.testBit (6*j)&&!(d.testBit (6*j+3))) &&
      ((d.testBit (6*j+1)||d.testBit (6*j+2)) &&
       (!(d.testBit (6*j+4))||!(d.testBit (6*j+5)))) then 1 else 0) else 0:=by
   intro j;rw [v9 (land a g),v9 a g,v9 (lor b c),wb b c,wb h t,
      h3 j,w 3 j,x 1 j,x 2 j,w 4 j,w 5 j]
   by_cases e:j < m
   . simp only [e,↓reduceIte,y,h8]
   . simp [e]
 have h5:∀ j,z6 (Nat.add (land g b) (land g c)) j =
     z6 (land g b) j+z6 (land g c) j:=fun j =>
   gn (fun l=>by rw [hL l,h0 l];by_cases z:l < m<;>simp [z]<;>split<;>split<;>omega) j
 have h6:∀ j,z6 (Nat.add (land a h) (land a t)) j =
     z6 (land a h) j+z6 (land a t) j:=fun j =>
   gn (fun l=>by rw [h1 l,h2 l];by_cases z:l < m<;>simp [z]<;>split<;>split<;>omega) j
 have h7:∀ j,z6 (Nat.add (Nat.add (land g b) (land g c)) (Nat.add (land a h) (land a t))) j =
     z6 (land g b) j+z6 (land g c) j+(z6 (land a h) j+z6 (land a t) j):=by
   intro j;have h9:∀ l,z6 (Nat.add (land g b) (land g c)) l+z6 (Nat.add (land a h) (land a t)) l < 64:=by intro l;rw [h5 l,h6 l,hL l,h0 l,h1 l,h2 l];by_cases z:l < m<;>simp [z]<;>split<;>split<;>split<;>split<;>omega
   change z6 (_+_) j=_;rw [gn h9 j,h5 j,h6 j]
 have x2:∀ j,z6 (land (land a g) (land (lor b c) (lor h t))) j <=
     z6 (Nat.add (Nat.add (land g b) (land g c)) (Nat.add (land a h) (land a t))) j:=by
   intro j;rw [h7 j,h4 j,hL j,h0 j,h1 j,h2 j];by_cases e:j < m
   . simp only [e,↓reduceIte];cases d.testBit (6*j)<;>cases d.testBit (6*j+1)<;>cases d.testBit (6*j+2) <;>
      cases d.testBit (6*j+3)<;>cases d.testBit (6*j+4)<;>cases d.testBit (6*j+5)<;>decide
   . simp [e]
 change z6 (_ - _) i=_;rw [kc x2 i,h7 i,h4 i,hL i,h0 i,h1 i,h2 i];by_cases hi:i < m
 . simp only [hi,↓reduceIte,v6];omega
 . simp [hi]
lemma q51:∀ b c:Nat,b<=3->c<=3 -> let u:=lor b c
  let d:=land u 2
  lor d (lor (lor (land b (shiftRight b 1)) (land c (shiftRight c 1)))
   (land (land u 1) (xor 1 (shiftRight d 1))))=max b c:=by
 intro b c h1 h2
 interval_cases b<;>interval_cases c<;>decide
lemma ya {v:Nat} (d:∀ j,z6 v j<=3) (i:Nat) :z6 (land v (shiftRight v 1)) i=land (z6 v i) (shiftRight (z6 v i) 1):=by
 apply nEQ;intro k;rw [nLA,nLA,nTA,qo,qo];by_cases c:k < 6
 . simp only [c,↓reduceIte,nTA];change (v.testBit (6*i+k)&&(v >>> 1).testBit (6*i+k)) =
     (v.testBit (6*i+k)&&((z6 v i) >>> 1).testBit k)
   rw [nTS,nTS,qo];by_cases hk5:k < 5
   . have e:1+k < 6:=by omega
     simp only [e,↓reduceIte]
     have:1+(6*i+k)=6*i+(1+k):=by omega
     rw [this]
   . have g:k=5:=by omega
     subst g;have h:z6 v i < 4:=by have:=d i;omega
     have b:(z6 v i).testBit 5=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le h (by decide));rw [qo] at b;simp only [show 5 < 6 by decide,↓reduceIte] at b
     simp [b]
 . simp [c]
lemma jv {b:Nat} (d:∀ j,z6 b j=0\/z6 b j=2) (i:Nat) :z6 (land (shiftRight b 1) (qe m 1)) i = if i < m then shiftRight (z6 b i) 1 else 0:=by
 rw [v9,v0 m 1 i (by decide)];by_cases c:i < m
 . simp only [c,↓reduceIte];apply nEQ;intro k;rw [nLA,nTA,qo];cases k with
   | zero => simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR];change (b >>> 1).testBit (6*i)=((z6 b i) >>> 1).testBit 0;rw [nTS,nTS,qo];simp [nAC]
   | succ k' =>
    rw [qp (by omega),Bool.and_false];rcases d i with e|g
    . rw [e];simp
    . rw [g];change false=((2 >>> 1:Nat).testBit (k'+1));simp [qp (by omega:k'+1≠0)]
 . simp [c,nLA]
lemma kh (sh1 m w i:Nat) :z6 (yg sh1 (qe m 1) (qe m 2) w) i = if i < m then zq (w.testBit (sh1+6*i)) (w.testBit (sh1+6*i+1)) (w.testBit (sh1+6*i+2)) (w.testBit (sh1+6*i+3)) (w.testBit (sh1+6*i+4)) (w.testBit (sh1+6*i+5)) else 0:=by
 unfold yg;simp only [v5];set g:=shiftRight w sh1;have x2:∀ k,g.testBit k=w.testBit (sh1+k):=fun k=>by
   change (w >>> sh1).testBit k=_;rw [nTS,nAC]
 set a:=land g (qe m 1);set b:=land (shiftRight g 1) (qe m 1);set c:=land (shiftRight g 2) (qe m 1);set d:=land (shiftRight g 3) (qe m 1);set e:=land (shiftRight g 4) (qe m 1);set f:=land (shiftRight g 5) (qe m 1);set nd:=xor (qe m 1) d;set ne:=xor (qe m 1) e;set nf:=xor (qe m 1) f;set na:=xor (qe m 1) a;set nb:=xor (qe m 1) b;set nc:=xor (qe m 1) c;set h:=Nat.sub (Nat.add (Nat.add (land nd b) (land nd c)) (Nat.add (land a ne) (land a nf)))
          (land (land a nd) (land (lor b c) (lor ne nf)))
 set t:=Nat.sub (Nat.add (Nat.add (land d nb) (land d nc)) (Nat.add (land na e) (land na f)))
          (land (land na d) (land (lor nb nc) (lor e f)))
 have x3:h=qi (qe m 1) g:=by unfold qi;simp only [v5];rfl
 have h3:∀ j,z6 h j=if j < m then
     v6 (g.testBit (6*j)) (g.testBit (6*j+1)) (g.testBit (6*j+2))
        (g.testBit (6*j+3)) (g.testBit (6*j+4)) (g.testBit (6*j+5)) else 0:=by
   intro j;rw [x3,yy]
 have a1:t=qi (qe m 1) (xor g (2 ^ (6*m) - 1)):=by
   have h0:∀ s,s < 6->land (shiftRight (xor g (2 ^ (6*m) - 1)) s) (qe m 1) =
       xor (qe m 1) (land (shiftRight g s) (qe m 1)):=by
     intro s hs;apply wg;intro j;rw [wc,bf,v0 m 1 j (by decide),wc];by_cases v:j < m
     . have a2:6*j+s < 6*m:=by omega
       simp only [v,↓reduceIte,nXO,nTX,nTB,a2,decide_true];cases g.testBit (6*j+s)<;>decide
     . simp [v]
   have b1:land (xor g (2 ^ (6*m) - 1)) (qe m 1) =
       xor (qe m 1) (land g (qe m 1)):=by
     have:=h0 0 (by decide);simpa using this
   have h4:∀ x,xor (qe m 1) (xor (qe m 1) x)=x:=by intro x;apply nEQ;intro k;rw [nXO,nXO,nTX,nTX];cases (qe m 1).testBit k<;>cases x.testBit k<;>decide
   unfold qi;simp only [v5];rw [b1,h0 1 (by decide),h0 2 (by decide),
       h0 3 (by decide),h0 4 (by decide),h0 5 (by decide),
       h4,h4,h4]
 have h5:∀ j,z6 t j=if j < m then
     v6 (!(g.testBit (6*j))) (!(g.testBit (6*j+1))) (!(g.testBit (6*j+2)))
        (!(g.testBit (6*j+3))) (!(g.testBit (6*j+4))) (!(g.testBit (6*j+5))) else 0:=by
   intro j;rw [a1,yy];by_cases v:j < m
   . simp only [v,↓reduceIte,nXO,nTX,nTB];simp only [show 6*j < 6*m by omega,show 6*j+1 < 6*m by omega,
       show 6*j+2 < 6*m by omega,show 6*j+3 < 6*m by omega,
       show 6*j+4 < 6*m by omega,show 6*j+5 < 6*m by omega,
       decide_true,bBT]
   . simp [v]
 have h6:∀ j,z6 h j<=3:=fun j=>by
   rw [h3 j];split;exact yr _ _ _ _ _ _;omega
 have h7:∀ j,z6 t j<=3:=fun j=>by
   rw [h5 j];split;exact yr _ _ _ _ _ _;omega
 set u:=lor h t;set z:=land u (qe m 2);have h8:∀ j,z6 z j=if j < m then land (lor (z6 h j) (z6 t j)) 2 else 0:=by intro j;rw [v9,wb,v0 m 2 j (by decide)];by_cases v:j < m<;>simp [v,nLA]
 have ha:∀ j,z6 z j=0\/z6 z j=2:=by
   intro j;rw [h8 j]
   split
   . have h1:=h6 j;have h2:=h7 j;generalize z6 h j=x at h1;generalize z6 t j=y at h2
     interval_cases x<;>interval_cases y<;>decide
   . left;rfl
 have hb:z6 (land (land u (qe m 1)) (xor (qe m 1) (shiftRight z 1))) i =
     if i < m then land (land (lor (z6 h i) (z6 t i)) 1) (xor 1 (shiftRight (z6 z i) 1)) else 0:=by
   have hc:land (land u (qe m 1)) (xor (qe m 1) (shiftRight z 1)) =
       land (land u (qe m 1)) (xor (qe m 1) (land (shiftRight z 1) (qe m 1))):=by
     apply nEQ;intro k;simp only [nLA,nXO,nTA,nTX];cases (qe m 1).testBit k<;>simp
   rw [hc,v9,v9,wb,bf,v0 m 1 i (by decide),
       jv (m:=m) ha i]
   by_cases hm:i < m<;>simp [hm,nLA]
 rw [wb,wb,wb,ya h6 i,
     ya h7 i,hb,h8 i]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte];have h9:=q51 (z6 h i) (z6 t i) (h6 i) (h7 i);simp only at h9;rw [h9,h3 i,h5 i];simp only [hm,↓reduceIte,x2,zq];have hd:sh1+(6*i+1)=sh1+6*i+1:=by omega
   have he:sh1+(6*i+2)=sh1+6*i+2:=by omega
   have hf:sh1+(6*i+3)=sh1+6*i+3:=by omega
   have hg:sh1+(6*i+4)=sh1+6*i+4:=by omega
   have hh:sh1+(6*i+5)=sh1+6*i+5:=by omega
   rw [hd,he,hf,hg,hh]
 . simp only [hm,↓reduceIte,h3 i,h5 i];decide
lemma xp {α:Type} (f : α->Nat) (m:Nat) (e:∀ x i,z6 (f x) i<=(if i < m then 3 else 0)) (b:List α) (hlen:b.length<=11) (i:Nat) :z6 (b.foldr (fun x acc=>Nat.add (f x) acc) 0) i=(b.map fun x=>z6 (f x) i).sum /\ (b.map fun x=>z6 (f x) i).sum<=if i < m then 3*b.length else 0:=by
 induction b generalizing i with
 | nil=>simp [z6]
 | cons a t ih =>
  simp only [lLC] at hlen;have g:∀ j,z6 (t.foldr (fun x acc=>Nat.add (f x) acc) 0) j =
     (t.map fun x=>z6 (f x) j).sum /\
     (t.map fun x=>z6 (f x) j).sum<=if j < m then 3*t.length else 0:=
    fun j=>ih (by omega) j
  have h:∀ j,z6 (f a) j+z6 (t.foldr (fun x acc=>Nat.add (f x) acc) 0) j < 64:=by intro j;have s:=e a j;have ⟨c,d⟩:=g j;rw [c];by_cases u:j < m<;>simp only [u,↓reduceIte] at s d<;>omega
  simp only [lFC,lMC,List.sum_cons,lLC];have v:=gn h i;have w:=e a i;have ⟨c,d⟩:=g i;refine ⟨?_,?_⟩
  . change z6 (_+_) i=_;rw [v,c]
  . by_cases y:i < m<;>simp only [y,↓reduceIte] at w d ⊢<;>omega
lemma ky (S m:Nat) (d:∀ i,z6 S i<=if i < m then 33 else 0) (e:∀ i < m,3<=z6 S i) :beq (land (Nat.add S (qe m 29)) (qe m 32)) (qe m 32)=true:=by
 rw [nBQ];apply wg;intro i;have g:∀ j,z6 S j+z6 (qe m 29) j < 64:=by intro j;rw [v0 m 29 j (by decide)];have c:=d j;by_cases h:j < m<;>simp only [h,↓reduceIte] at c ⊢<;>omega
 rw [v9];change land (z6 (S+qe m 29) i) (z6 (qe m 32) i)=z6 (qe m 32) i;rw [gn g i,v0 m 29 i (by decide),v0 m 32 i (by decide)];by_cases b:i < m
 . simp only [b,↓reduceIte];have c:=d i;simp only [b,↓reduceIte] at c;have hge:=e i b;have s:32<=z6 S i+29:=by omega
   have t:z6 S i+29 < 64:=by omega
   generalize z6 S i+29=v at s t
   interval_cases v<;>decide
 . simp [b,nLA]
def j5 (n c:Nat):Nat->Nat->M
 | 0,_=>[]
 | m+1,idx =>
  let b:=if ble n 7 then 7 else 8
  let d:=if ble n 7 then 127 else 255
  land (shiftRight c (Nat.mul b idx)) d::j5 n c m (Nat.add idx 1)
lemma q32 (n c m b:Nat):(j5 n c m b).length=m:=by
 induction m generalizing b with
 | zero=>rfl
 | succ m ih=>simp [j5,ih]
def n8 (n b shTT:Nat):M:=j5 n b shTT 0
def e6 (n b shTT:Nat):M:=n8 n b shTT++range (2 ^ n)
lemma jj (n b shTT:Nat):(n8 n b shTT).length=shTT:=
 q32 n b shTT 0
lemma zl (n b shTT:Nat):(e6 n b shTT).length=shTT+2 ^ n:=by simp [e6,jj]
structure CfgOk (n:Nat) (f:u7 n) (rp:Nat) (c:Cfg):Prop where
 sh0_eq:c.sh0=2*c.k
 sh0_le:c.sh0<=c.sh1
 sh1_le:c.sh1<=c.shTT
 p0_dvd:(c.sh1 - c.sh0) % 6=0
 p1_dvd:(c.shTT - c.sh1) % 6=0
 all1v_eq:c.all1v=2 ^ (c.shTT+2 ^ n) - 1
 goalv_eq:c.goalv=d7 (e6 n rp c.shTT) f
 lok_eq:c.lok=2 ^ c.k - 1
 m0all_eq:c.m0all=2 ^ (6*((c.sh1 - c.sh0) / 6)) - 1
 m0_eq:c.m0=qe ((c.sh1 - c.sh0) / 6) 1
 a29_0_eq:c.a29_0=qe ((c.sh1 - c.sh0) / 6) 29
 b5_0_eq:c.b5_0=qe ((c.sh1 - c.sh0) / 6) 32
 m1_eq:c.m1=qe ((c.shTT - c.sh1) / 6) 1
 m12_eq:c.m12=qe ((c.shTT - c.sh1) / 6) 2
 a29_1_eq:c.a29_1=qe ((c.shTT - c.sh1) / 6) 29
 b5_1_eq:c.b5_1=qe ((c.shTT - c.sh1) / 6) 32
 cov_ok:∀ i < c.k,
  f (q1 n ((e6 n rp c.shTT).getD i 0))=false /\
  f (q1 n ((e6 n rp c.shTT).getD (c.k+i) 0))=true
 p0_ok:∀ i < (c.sh1 - c.sh0) / 6,
  f (q1 n ((e6 n rp c.shTT).getD (c.sh0+6*i) 0))=true /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh0+6*i+1) 0))=true /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh0+6*i+2) 0))=true /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh0+6*i+3) 0))=false /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh0+6*i+4) 0))=false /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh0+6*i+5) 0))=false
 p1_ok:∀ i < (c.shTT - c.sh1) / 6,
  f (q1 n ((e6 n rp c.shTT).getD (c.sh1+6*i) 0))=true /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh1+6*i+1) 0))=true /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh1+6*i+2) 0))=true /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh1+6*i+3) 0))=false /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh1+6*i+4) 0))=false /\
  f (q1 n ((e6 n rp c.shTT).getD (c.sh1+6*i+5) 0))=false
def w3 (n:Nat) (f:u7 n) (e:Nat) (c:Cfg):Q:=
 let d:=(c.sh1 - c.sh0) / 6
 let b:=(c.shTT - c.sh1) / 6
 beq c.sh0 (2*c.k) &&
 ble c.sh0 c.sh1 &&
 ble c.sh1 c.shTT &&
 beq ((c.sh1 - c.sh0) % 6) 0 &&
 beq ((c.shTT - c.sh1) % 6) 0 &&
 beq c.all1v (2 ^ (c.shTT+2 ^ n) - 1) &&
 beq c.goalv (d7 (e6 n e c.shTT) f) &&
 beq c.lok (2 ^ c.k - 1) &&
 beq c.m0all (2 ^ (6*d) - 1) &&
 beq c.m0 (qe d 1) &&
 beq c.a29_0 (qe d 29) &&
 beq c.b5_0 (qe d 32) &&
 beq c.m1 (qe b 1) &&
 beq c.m12 (qe b 2) &&
 beq c.a29_1 (qe b 29) &&
 beq c.b5_1 (qe b 32) &&
 beq (land c.goalv c.lok) 0 &&
 beq (land (shiftRight c.goalv c.k) c.lok) c.lok &&
 beq (land (shiftRight c.goalv c.sh0) c.m0all) (qe d 7) &&
 beq (land (shiftRight c.goalv c.sh1) (2 ^ (6*b) - 1)) (qe b 7)
lemma qm {n:Nat} (b:M) (f:u7 n) {c:Nat} (h:c < b.length) :(d7 b f).testBit c=f (q1 n (b.getD c 0)):=by rw [z8,lGEQ h,lGDE _ _ h]
lemma jn (n:Nat) (f:u7 n) (d:Nat) (c:Cfg) (h:w3 n f d c=true):CfgOk n f d c:=by
 unfold w3 at h;simp only [bAT,nBQ,nBE] at h;rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h3,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,x⟩,u⟩,y⟩,
   hm0⟩,h9⟩,x2⟩,x3⟩,a1⟩,a2⟩,b1⟩,ha⟩,hb⟩,hc⟩,hd⟩
 have hlen:(e6 n d c.shTT).length=c.shTT+2 ^ n:=zl n d c.shTT;have v:∀ w < c.shTT,c.goalv.testBit w=f (q1 n ((e6 n d c.shTT).getD w 0)):=by intro w he;rw [x,qm _ _ (by rw [hlen];exact Nat.lt_add_right (2 ^ n) he)]
 have h0:∀ (e m:Nat),e+6*m<=c.shTT ->
     land (shiftRight c.goalv e) (2 ^ (6*m) - 1)=qe m 7 ->
     ∀ i < m,
      f (q1 n ((e6 n d c.shTT).getD (e+6*i) 0))=true /\
      f (q1 n ((e6 n d c.shTT).getD (e+6*i+1) 0))=true /\
      f (q1 n ((e6 n d c.shTT).getD (e+6*i+2) 0))=true /\
      f (q1 n ((e6 n d c.shTT).getD (e+6*i+3) 0))=false /\
      f (q1 n ((e6 n d c.shTT).getD (e+6*i+4) 0))=false /\
      f (q1 n ((e6 n d c.shTT).getD (e+6*i+5) 0))=false:=by
   intro e m hbound hf i t;have j:∀ g < 6,f (q1 n ((e6 n d c.shTT).getD (e+6*i+g) 0))=(7:Nat).testBit g:=by
     intro g hg;have b:=congrArg (fun z=>z6 z i) hf
     rw [v0 m 7 i (by decide)] at b;simp only [t,↓reduceIte] at b;have s:=congrArg (fun z=>z.testBit g) b
     rw [qo] at s;simp only [hg,↓reduceIte,nLA,nTA,nTB,
      show 6*i+g < 6*m by omega,decide_true,bATR] at s
     change (c.goalv >>> e).testBit (6*i+g)=_ at s;rw [nTS,<- nAA] at s;rw [<- v (e+6*i+g) (by omega)];exact s
   exact ⟨by simpa using j 0 (by decide),j 1 (by decide),j 2 (by decide),
       j 3 (by decide),j 4 (by decide),j 5 (by decide)⟩
 refine ⟨h3,h4,h5,h6,h7,h8,x,u,y,hm0,h9,x2,x3,a1,a2,b1,?_,?_,?_⟩
 . intro i t;constructor
   . have b:=congrArg (fun z=>z.testBit i) ha
     rw [nLA,nTA,u,nTB,nZT] at b;simp only [t,decide_true,bATR] at b;rw [<- v i (by omega)];exact b
   . have b:=congrArg (fun z=>z.testBit i) hb
     rw [nLA,nTA,u,nTB] at b;simp only [t,decide_true,bATR] at b;change (c.goalv >>> c.k).testBit i=true at b;rw [nTS] at b;rw [<- v (c.k+i) (by omega)];exact b
 . apply h0 c.sh0 ((c.sh1 - c.sh0) / 6) (by omega)
   rw [<- y];exact hc
 . apply h0 c.sh1 ((c.shTT - c.sh1) / 6) (by omega) hd
def AllTagsLe3 {α:Type} (b:List (α×Nat)):Prop:=∀ p∈b,p.2<=3
lemma AllTagsLe3.perm {α:Type} {b c:List (α×Nat)} (d:b.Perm c) (h:AllTagsLe3 b):AllTagsLe3 c:=
 fun p hm=>h p (d.symm.subset hm)
lemma TagRun.inv_zero {α:Type} {inv : α->α} {meet join : α->α->α} {zero one c : α} {d:List (α×Nat)} (h:TagRun inv meet join zero one c 0 d) :∃ tg,d=[(c,tg)]:=by
 generalize b:(0:Nat)=s at h
 induction h with
 | done tg=>exact ⟨tg,rfl⟩
 | perm e _ ih => obtain ⟨tg,rfl⟩:=ih b;exact ⟨tg,List.perm_singleton.1 e.symm⟩
 | uNot _ _ _ _ _ _ _ _ _=>cases b
 | bOr _ _ _ _ _ _ _ _ _ _ _ _=>cases b
 | bAnd _ _ _ _ _ _ _ _ _ _ _ _=>cases b
lemma TagRun.inv_succ {α:Type} {inv : α->α} {meet join : α->α->α} {zero one y : α} {s:Nat} {z:List (α×Nat)} (h:TagRun inv meet join zero one y (s+1) z) :(∃ a ta r save,z.Perm ((a,ta)::r) /\ ta≠1/\ta≠2/\(ta=3->save=false) /\ inv a≠zero/\inv a≠one/\inv a≠a/\(∀ x∈r,x.1≠inv a) /\ TagRun inv meet join zero one y s ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r)) \/ (∃ a ta b tb r ka kb,z.Perm ((a,ta)::(b,tb)::r) /\ ta≠2/\tb≠2/\(ta=1->ka=false)/\(tb=1->kb=false) /\ join a b≠zero/\join a b≠one/\join a b≠a/\join a b≠b/\(∀ x∈r,x.1≠join a b) /\ TagRun inv meet join zero one y s ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r))) \/ (∃ a ta b tb r ka kb,z.Perm ((a,ta)::(b,tb)::r) /\ ta≠1/\tb≠1/\(ta≠0->ka=false)/\(tb≠0->kb=false) /\ meet a b≠zero/\meet a b≠one/\meet a b≠a/\meet a b≠b/\(∀ x∈r,x.1≠meet a b) /\ TagRun inv meet join zero one y s ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r))):=by
 generalize d:s+1=s' at h
 induction h with
 | done _=>cases d
 | perm c _ ih =>
  rcases ih d with ⟨a,ta,r,save,c',rest⟩|⟨a,ta,b,tb,r,ka,kb,c',rest⟩|⟨a,ta,b,tb,r,ka,kb,c',rest⟩
  . exact Or.inl ⟨a,ta,r,save,c.symm.trans c',rest⟩
  . exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,c.symm.trans c',rest⟩)
  . exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,c.symm.trans c',rest⟩)
 | @uNot s0 a ta r save e g i j t u v w _ =>
  cases d
  exact Or.inl ⟨a,ta,r,save,lPR _,e,g,i,j,t,u,v,w⟩
 | @bOr s0 a ta b tb r ka kb e g i j t u v h8 h9 w _ =>
  cases d
  exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,lPR _,e,g,i,j,t,u,v,h8,h9,w⟩)
 | @bAnd s0 a ta b tb r ka kb e g i j t u v h8 h9 w _ =>
  cases d
  exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,lPR _,e,g,i,j,t,u,v,h8,h9,w⟩)
lemma iq {α:Type} {d:List α} {a : α} {r:List α} (e:d.Perm (a::r)) :∃ b c,d=b++a::c/\r.Perm (b++c):=by
 have h:a∈d:=e.symm.subset (by simp);obtain ⟨b,c,g⟩:=List.append_of_mem h;refine ⟨b,c,g,?_⟩
 rw [g] at e;exact (List.perm_cons a).1 (e.symm.trans lPM)
lemma fn {α:Type} {h:List α} {a b : α} {r:List α} (u:h.Perm (a::b::r)) :(∃ d c e,h=d++a::c++b::e/\r.Perm (d++c++e)) \/ (∃ d c e,h=d++b::c++a::e/\r.Perm (d++c++e)):=by
 obtain ⟨p1,s1,j,g⟩:=iq u;have v:b∈p1++s1:=g.subset (by simp);rcases lMAp.1 v with w|x
 . obtain ⟨d,c,s⟩:=List.append_of_mem w;right;refine ⟨d,c,s1,by rw [j,s,lAA,lCA],?_⟩
   rw [s,lAA] at g;have i:(d++b::(c++s1)).Perm (b::(d++(c++s1))):=lPM;have y:=(List.perm_cons b).1 (g.trans i);simpa [lAA] using y
 . obtain ⟨c,e,t⟩:=List.append_of_mem x;left;refine ⟨p1,c,e,by simp [j,t,lAA],?_⟩
   rw [t] at g;have i:((p1++c)++b::e).Perm (b::((p1++c)++e)):=lPM;rw [<- lAA] at g;exact (List.perm_cons b).1 (g.trans i)
lemma z4 {α:Type} (k:Q) (a : α) (r:List α) (x : α) :x∈qk k a r↔(k=true/\x=a)\/x∈r:=by cases k<;>simp [qk]
abbrev aR (n b:Nat) (c:Cfg):=e6 n b c.shTT
abbrev TR {n:Nat} (f:u7 n):=TagRun (invF (n:=n)) meetF joinF (fun _=>false) (fun _=>true) f
lemma TR.toRun {n s:Nat} {f:u7 n} {c:List (u7 n×Nat)} (h:TR f s c) :Run (invF (n:=n)) meetF joinF f s (c.map Prod.fst):=by
 induction h with
 | done _=>exact Run.done
 | perm d _ ih=>exact Run.perm (d.map Prod.fst) ih
 | @uNot _ a ta r save _ _ _ _ _ _ _ _ ih =>
  have e:(((invF a,if ta=3 then 2 else 0)::qk save (a,0) r).map Prod.fst) =
    (if true then invF a else a)::qk save a (r.map Prod.fst):=by cases save<;>simp [qk]
  rw [e] at ih;exact Run.one true save ih
 | @bOr _ a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map Prod.fst) =
    (if false then meetF a b else joinF a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
   cases ka<;>cases kb<;>simp [qk]
  rw [e] at ih;exact Run.two false ka kb ih
 | @bAnd _ a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map Prod.fst) =
    (if true then meetF a b else joinF a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
   cases ka<;>cases kb<;>simp [qk]
  rw [e] at ih;exact Run.two true ka kb ih
lemma tk {n:Nat} {f:u7 n} {c:List (u7 n)} (d:Run (invF (n:=n)) meetF joinF f 0 c):c=[f]:=by
 generalize b:0=s at d
 induction d using Run.fold with
 | done=>rfl
 | perm e _ ih=>exact List.perm_singleton.1 ((ih b) ▸ e.symm)
 | one _ _ _ _=>cases b
 | two _ _ _ _ _=>cases b
lemma w6 {n:Nat} {f:u7 n} {s:Nat} {j:List (u7 n)} (t:Run (invF (n:=n)) meetF joinF f s j) {x y:F n}
  (hsep:f x≠f y):∃ g∈j,g x≠g y:=by
 induction t using Run.fold with
 | done=>exact ⟨f,by simp,hsep⟩
 | perm u _ ih=>obtain ⟨g,c,d⟩:=ih;exact ⟨g,u.mem_iff.1 c,d⟩
 | @one _ a r neg save _ ih =>
  obtain ⟨g,c,d⟩:=ih
  rcases lMM.1 c with rfl|c
  . refine ⟨a,by simp,fun v=>d ?_⟩;cases neg<;>simp [invF,v]
  . rcases (z4 _ _ _ _).1 c with ⟨_,e⟩|c
    . exact ⟨g,by simp [e],d⟩
    . exact ⟨g,lMCM _ c,d⟩
 | @two _ a b r conj ka kb _ ih =>
  obtain ⟨g,c,d⟩:=ih
  rcases lMM.1 c with rfl|c
  . by_cases h:a x≠a y
    . exact ⟨a,by simp,h⟩
    . by_cases i:b x≠b y
      . exact ⟨b,lMCM _ (by simp),i⟩
      . push Not at h i;exfalso;apply d;cases conj<;>simp [meetF,joinF,h,i]
  . rcases (z4 _ _ _ _).1 c with ⟨_,e⟩|w
    . exact ⟨g,by simp [e],d⟩
    . rcases (z4 _ _ _ _).1 w with ⟨_,z⟩|h0
      . exact ⟨g,lMCM _ (by simp [z]),d⟩
      . exact ⟨g,lMCM _ (lMCM _ h0),d⟩
lemma th {n:Nat} {a b:u7 n} {r:List (u7 n)} {e i j:Q} {u v:F n} (h:∃ g∈(if e then meetF a b else joinF a b)::qk i a (qk j b r),g u=false/\g v=true) :∃ g∈a::b::r,g u=false/\g v=true:=by
 obtain ⟨g,s,c,d⟩:=h;rcases lMM.1 s with rfl|t
 . cases e
   . simp only [bFT,↓reduceIte,joinF,bOF,bOT] at c d;rcases d with w|x
     . exact ⟨a,by simp,c.1,w⟩
     . exact ⟨b,by simp,c.2,x⟩
   . simp only [↓reduceIte,meetF,bAF,bAT] at c d;rcases c with y|z
     . exact ⟨a,by simp,y,d.1⟩
     . exact ⟨b,by simp,z,d.2⟩
 . rcases (z4 _ _ _ _).1 t with ⟨_,h0⟩|h1
   . exact ⟨g,by simp [h0],c,d⟩
   . rcases (z4 _ _ _ _).1 h1 with ⟨_,h2⟩|h3
     . exact ⟨g,by simp [h2],c,d⟩
     . exact ⟨g,by simp [h3],c,d⟩
lemma tj {n:Nat} {f:u7 n} {s:Nat} {d:List (u7 n)} (j:Run (invF (n:=n)) meetF joinF f s d) (hlen:d.length=s+1) :
  ∀ u v:F n,f u=false->f v=true->∃ g∈d,g u=false/\g v=true:=by
 induction j using Run.fold with
 | done=>intro u v b c;exact ⟨f,by simp,b,c⟩
 | perm i _ ih =>
  intro u v b c
  obtain ⟨g,t,w,x⟩:=ih (by rw [i.length_eq];exact hlen) u v b c
  exact ⟨g,i.mem_iff.1 t,w,x⟩
 | one neg save e _ =>
  have h:=tn e;cases save<;>simp [qk] at hlen h<;>omega
 | two conj ka kb e ih =>
  have h:=tn e
  cases ka<;>cases kb<;>simp [qk] at hlen h<;>try omega
  intro u v b c
  exact th (ih (by simp [qk];omega) u v b c)
lemma dc {n:Nat} {f:u7 n} {s:Nat} {c:List (u7 n)} (j:Run (invF (n:=n)) meetF joinF f s c) (hlen:c.length=s+1)
  (r0 r1 r2 r3 r4 r5:F n)
  (h0:f r0=true) (h1:f r1=true) (h2:f r2=true)
  (h3:f r3=false) (h4:f r4=false) (h5:f r5=false) :
  3<=(c.map fun g=>v6 (g r0) (g r1) (g r2) (g r3) (g r4) (g r5)).sum:=by
 induction j using Run.fold with
 | done=>simp [h0,h1,h2,h3,h4,h5,lz]
 | perm h _ ih =>
  rw [<- (h.map _).sum_eq];exact ih (by rw [h.length_eq];exact hlen)
 | one neg save d _ =>
  have e:=tn d;cases save<;>simp [qk] at hlen e<;>omega
 | @two s a b r conj ka kb d ih =>
  have e:=tn d
  cases ka<;>cases kb<;>simp [qk] at hlen e<;>try omega
  have i:=ih (by simp [qk];omega)
  cases conj
  . simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at i ⊢
    have:=w4 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5) (b r0) (b r1) (b r2) (b r3) (b r4) (b r5);omega
  . simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at i ⊢
    have:=kl (a r0) (a r1) (a r2) (a r3) (a r4) (a r5) (b r0) (b r1) (b r2) (b r3) (b r4) (b r5);omega
lemma ds {n:Nat} {f:u7 n} {s:Nat} {ws:List (u7 n)} (hr:Run (invF (n:=n)) meetF joinF f s ws) (hlen:ws.length=s) :
  (∀ u v:F n,f u=false->f v=true->∃ g∈ws,g u=false/\g v=true) \/
  (∀ r0 r1 c d e h:F n,
    f r0=true->f r1=true->f c=true->f d=false->f e=false->f h=false ->
    3<=(ws.map fun g=>zq (g r0) (g r1) (g c) (g d) (g e) (g h)).sum):=by
 induction hr using Run.fold with
 | done=>simp at hlen
 | perm hp _ ih =>
  rcases ih (by rw [hp.length_eq];exact hlen) with h6|h7
  . left;intro u v w j;obtain ⟨g,hm,i,y⟩:=h6 u v w j;exact ⟨g,hp.mem_iff.1 hm,i,y⟩
  . right;intro r0 r1 c d e h h0 i y h3 h4 h5
    rw [<- (hp.map _).sum_eq];exact h7 r0 r1 c d e h h0 i y h3 h4 h5
 | @one s a r neg save z _ =>
  have h8:=tn z
  cases save
  . right;intro r0 r1 c d e h h0 i y h3 h4 h5
    have j:=dc z (by simp [qk] at hlen ⊢;omega) r0 r1 c d e h h0 i y h3 h4 h5
    have h9:∀ l:List (u7 n),
        (l.map fun g=>v6 (g r0) (g r1) (g c) (g d) (g e) (g h)).sum <=
        (l.map fun g=>zq (g r0) (g r1) (g c) (g d) (g e) (g h)).sum:=by
      intro l;induction l with
      | nil=>simp
      | cons x t iht=>simp only [lMC,List.sum_cons];have:=k7 (x r0) (x r1) (x c) (x d) (x e) (x h);omega
    have hs:=le_trans j (h9 _)
    cases neg<;>simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs ⊢<;>exact hs
  . simp [qk] at hlen h8;omega
 | @two s a b r conj ka kb z ih =>
  have h8:=tn z
  cases ka<;>cases kb
  . rcases ih (by simp [qk] at hlen ⊢;omega) with h6|h7
    . left;intro u v w j;exact th (h6 u v w j)
    . right;intro r0 r1 c d e h h0 i y h3 h4 h5
      have i:=h7 r0 r1 c d e h h0 i y h3 h4 h5
      cases conj
      . simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at i ⊢
        have:=q14 (a r0) (a r1) (a c) (a d) (a e) (a h) (b r0) (b r1) (b c) (b d) (b e) (b h);omega
      . simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at i ⊢
        have:=je (a r0) (a r1) (a c) (a d) (a e) (a h) (b r0) (b r1) (b c) (b d) (b e) (b h);omega
  . left;intro u v w j;exact th (tj z (by simp [qk] at hlen ⊢;omega) u v w j)
  . left;intro u v w j;exact th (tj z (by simp [qk] at hlen ⊢;omega) u v w j)
  . simp [qk] at hlen h8;omega
lemma qz {a b:Nat} (h:a=b):beq a b=true:=Eq.mpr nBQ h
lemma q0 (a:Nat):beq a a=true:=Eq.mpr nBQ rfl
lemma q2 {a b:Nat} (h:a≠b):beq a b=false:=by
 cases c:beq a b
 . rfl
 . exact absurd (Eq.mp nBQ c) h
lemma y3 {a b:Nat} (h:beq a b=false):a≠b:=
 fun e=>by subst e;rw [q0] at h;cases h
lemma zh {a b:Nat}:(beq a b=false)↔a≠b:=
 ⟨y3,q2⟩
lemma q4 {b e:Q} (h:e=true):(if b=true then true else e)=true:=by cases b<;>simp [h]
lemma q5 {b e:Q} (h:b=true):(if b=true then true else e)=true:=by rw [h];rfl
lemma v8 (a b:Nat):Nat.add a b=a+b:=rfl
def e4 {n:Nat} (b:M) (c:List (u7 n×Nat)):J:=
 c.map fun p=>(d7 b p.1,p.2)
abbrev eW {n:Nat} (b:Nat) (c:Cfg) (d:List (u7 n×Nat)):=e4 (aR n b c) d
abbrev eL {n:Nat} (b:Nat) (c:Cfg) (g:u7 n):=d7 (aR n b c) g
def u4 (n:Nat) (b:List (u7 n×Nat)):J:=
 b.map fun p=>(u9 n p.1,p.2)
lemma qy {n:Nat} (b:M) (p:u7 n×Nat) (c:List (u7 n×Nat)) :e4 b (p::c)=(d7 b p.1,p.2)::e4 b c:=rfl
lemma kj {n:Nat} (b:M) (c d:List (u7 n×Nat)) :e4 b (c++d)=e4 b c++e4 b d:=lMA
lemma ir {n:Nat} (p:u7 n×Nat) (b:List (u7 n×Nat)) :u4 n (p::b)=(u9 n p.1,p.2)::u4 n b:=rfl
lemma qc {n:Nat} (c:M) (a b:u7 n) :d7 c (joinF a b)=lor (d7 c a) (d7 c b):=lr c a b
lemma q9 {n:Nat} (c:M) (a b:u7 n) :d7 c (meetF a b)=land (d7 c a) (d7 c b):=ls c a b
lemma rd {n:Nat} (b:M) (a:u7 n) :d7 b (invF a)=xor (d7 b a) (2 ^ b.length - 1):=gx b a
lemma qv {n:Nat} {f:u7 n} {b:Nat} {c:Cfg} (d:CfgOk n f b c) (a:u7 n) :eL b c (invF a)=xor (eL b c a) c.all1v:=by unfold eL;rw [gx,zl,<- d.all1v_eq]
def wi (c:Cfg) (w:Nat):Nat:=land w c.lok
def ag (c:Cfg) (w:Nat):Nat:=land (shiftRight w c.k) c.lok
def wC (c:Cfg) (w:Nat):Nat:=xor (wi c w) (ag c w)
def wU (c:Cfg) (w:Nat):Nat:=land (wC c w) (ag c w)
def fm (c:Cfg) (w:Nat):Nat:=land (shiftRight w c.sh0) c.m0all
def mh (c:Cfg) (w:Nat):Nat:=qi c.m0 (fm c w)
def sv (c:Cfg) (w:Nat):Nat:=yg c.sh1 c.m1 c.m12 w
def yx (c:Cfg) (b:J):Nat:=b.foldr (fun p acc=>lor (wC c p.1) acc) 0
def v4 (c:Cfg) (b:J):Nat:=b.foldr (fun p acc=>lor (wU c p.1) acc) 0
def zf (c:Cfg) (b:J):Nat:=b.foldr (fun p acc=>Nat.add (mh c p.1) acc) 0
def va (c:Cfg) (b:J):Nat:=b.foldr (fun p acc=>Nat.add (sv c p.1) acc) 0
lemma qq (a b d:Nat):lor (lor a b) d=lor a (lor b d):=by apply nEQ;intro i;simp [nLO,nTO,Bool.or_assoc]
lemma q7 (a b:Nat):lor a b=lor b a:=by apply nEQ;intro i;simp [nLO,nTO,Bool.or_comm]
lemma ah (a:Nat):lor 0 a=a:=by apply nEQ;intro i;simp [nLO,nTO]
lemma yp (c:Cfg) (p:K) (b:J):yx c (p::b)=lor (wC c p.1) (yx c b):=rfl
lemma w1 (c:Cfg) (p:K) (b:J):va c (p::b)=Nat.add (sv c p.1) (va c b):=rfl
lemma vc (c:Cfg) (b d:J):yx c (b++d)=lor (yx c b) (yx c d):=by induction b with|nil=>simp [yx,ah]|cons a t ih=>simp only [lCA,yx,lFC] at ih ⊢;rw [ih,qq]
lemma zu (c:Cfg) (b d:J):v4 c (b++d)=lor (v4 c b) (v4 c d):=by induction b with|nil=>simp [v4,ah]|cons a t ih=>simp only [lCA,v4,lFC] at ih ⊢;rw [ih,qq]
lemma lp (c:Cfg) (b:J) (i:Nat) :(yx c b).testBit i=b.any (fun p=>(wC c p.1).testBit i):=by
 induction b with
 | nil=>simp [yx]
 | cons _ _ ih=>simp only [yx,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]
lemma lq (c:Cfg) (b:J) (i:Nat) :(v4 c b).testBit i=b.any (fun p=>(wU c p.1).testBit i):=by
 induction b with
 | nil=>simp [v4]
 | cons _ _ ih=>simp only [v4,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]
lemma zw {n:Nat} {f:u7 n} {b:Nat} {c:Cfg} (d:CfgOk n f b c) (w i:Nat) :(wi c w).testBit i=if i < c.k then w.testBit i else false:=by unfold wi;rw [nLA,nTA,d.lok_eq,nTB];by_cases e:i < c.k<;>simp [e]
lemma vl {n:Nat} {f:u7 n} {b:Nat} {c:Cfg} (d:CfgOk n f b c) (w i:Nat) :(ag c w).testBit i=if i < c.k then w.testBit (c.k+i) else false:=by unfold ag;rw [nLA,nTA,d.lok_eq,nTB];change ((w >>> c.k).testBit i&&decide (i < c.k))=_;rw [nTS];by_cases e:i < c.k<;>simp [e]
lemma vp {n:Nat} {f:u7 n} {d:Nat} {c:Cfg} (b:CfgOk n f d c) (w i:Nat) :(wC c w).testBit i=if i < c.k then (w.testBit i ^^ w.testBit (c.k+i)) else false:=by unfold wC;rw [nXO,nTX,zw b,vl b];by_cases e:i < c.k<;>simp [e]
lemma vd {n:Nat} {f:u7 n} {e:Nat} {c:Cfg} (b:CfgOk n f e c) (w i:Nat) :(wU c w).testBit i=if i < c.k then (!(w.testBit i)&&w.testBit (c.k+i)) else false:=by
 unfold wU;rw [nLA,nTA,vp b,vl b];by_cases d:i < c.k
 . simp only [d,↓reduceIte];cases w.testBit i<;>cases w.testBit (c.k+i)<;>decide
 . simp [d]
lemma zz {n:Nat} {f:u7 n} {d:Nat} {c:Cfg} (b:CfgOk n f d c) {g:List (u7 n×Nat)} (s:∀ u v:F n,f u=false->f v=true->∃ p∈g,p.1 u≠p.1 v) :yx c (eW d c g)=c.lok:=by
 have h2n:=n2P n;have hlen:=zl n d c.shTT;have hk_le:2*c.k<=c.shTT:=by have:=b.sh0_eq;have:=b.sh0_le;have:=b.sh1_le;omega
 apply nEQ;intro i;rw [lp,b.lok_eq,nTB];by_cases e:i < c.k
 . simp only [e,decide_true,lAN];obtain ⟨t,w⟩:=b.cov_ok i e;obtain ⟨p,x,hne⟩:=s _ _ t w;refine ⟨(eL d c p.1,p.2),lMp.2 ⟨p,x,rfl⟩,?_⟩
   rw [vp b,if_pos e,qm _ _ (by rw [hlen];omega),
     qm _ _ (by rw [hlen];omega)]
   cases h1:p.1 (q1 n ((aR n d c).getD i 0)) <;>
    cases h2:p.1 (q1 n ((aR n d c).getD (c.k+i) 0))<;>simp_all
 . simp only [e,decide_false];rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,j⟩:=lAN.1 h;rw [vp b,if_neg e] at j;cases j
lemma q6 {n:Nat} {f:u7 n} {e:Nat} {c:Cfg} (b:CfgOk n f e c) {g:List (u7 n×Nat)} (s:∀ u v:F n,f u=false->f v=true->∃ p∈g,p.1 u=false/\p.1 v=true) :v4 c (eW e c g)=c.lok:=by
 have h2n:=n2P n;have hlen:=zl n e c.shTT;have hk_le:2*c.k<=c.shTT:=by have:=b.sh0_eq;have:=b.sh0_le;have:=b.sh1_le;omega
 apply nEQ;intro i;rw [lq,b.lok_eq,nTB];by_cases d:i < c.k
 . simp only [d,decide_true,lAN];obtain ⟨t,w⟩:=b.cov_ok i d;obtain ⟨p,x,y,z⟩:=s _ _ t w;refine ⟨(eL e c p.1,p.2),lMp.2 ⟨p,x,rfl⟩,?_⟩
   rw [vd b,if_pos d,qm _ _ (by rw [hlen];omega),
    qm _ _ (by rw [hlen];omega),y,z];rfl
 . simp only [d,decide_false];rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,j⟩:=lAN.1 h;rw [vd b,if_neg d] at j;cases j
lemma np {n:Nat} {f:u7 n} {b:Nat} {c:Cfg} (h:CfgOk n f b c) (g:u7 n) (i:Nat) :z6 (mh c (eL b c g)) i = if i < (c.sh1 - c.sh0) / 6 then let d:=aR n b c
     v6 (g (q1 n (d.getD (c.sh0+6*i) 0)))
      (g (q1 n (d.getD (c.sh0+6*i+1) 0)))
      (g (q1 n (d.getD (c.sh0+6*i+2) 0)))
      (g (q1 n (d.getD (c.sh0+6*i+3) 0)))
      (g (q1 n (d.getD (c.sh0+6*i+4) 0)))
      (g (q1 n (d.getD (c.sh0+6*i+5) 0)))
    else 0:=by
 have h2n:=n2P n
 have hlen:=zl n b c.shTT
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT:=by
   have:=h.sh0_le;have:=h.sh1_le;have:=h.p0_dvd;omega
 unfold mh;rw [h.m0_eq,yy]
 by_cases s:i < (c.sh1 - c.sh0) / 6
 . simp only [s,↓reduceIte]
   have e:∀ j < 6,(fm c (eL b c g)).testBit (6*i+j) =
     g (q1 n ((aR n b c).getD (c.sh0+6*i+j) 0)):=by
    intro j hoff;unfold fm
    rw [nLA,nTA,h.m0all_eq,nTB]
    simp only [show 6*i+j < 6*((c.sh1 - c.sh0) / 6) by omega,decide_true,bATR]
    change ((eL b c g) >>> c.sh0).testBit (6*i+j)=_
    rw [nTS,<- nAA,qm _ _ (by rw [hlen];omega)]
   rw [show 6*i=6*i+0 by omega,e 0 (by decide),e 1 (by decide),e 2 (by decide),
     e 3 (by decide),e 4 (by decide),e 5 (by decide)]
   simp only [nAZ]
 . simp [s]
lemma nq {n:Nat} {f:u7 n} {d:Nat} {c:Cfg} (e:CfgOk n f d c) (g:u7 n) (i:Nat) :z6 (sv c (eL d c g)) i = if i < (c.shTT - c.sh1) / 6 then let b:=aR n d c
     zq (g (q1 n (b.getD (c.sh1+6*i) 0)))
      (g (q1 n (b.getD (c.sh1+6*i+1) 0)))
      (g (q1 n (b.getD (c.sh1+6*i+2) 0)))
      (g (q1 n (b.getD (c.sh1+6*i+3) 0)))
      (g (q1 n (b.getD (c.sh1+6*i+4) 0)))
      (g (q1 n (b.getD (c.sh1+6*i+5) 0)))
    else 0:=by
 have h2n:=n2P n
 have hlen:=zl n d c.shTT
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT:=by
   have:=e.sh1_le;have:=e.p1_dvd;omega
 unfold sv;rw [e.m1_eq,e.m12_eq,kh]
 by_cases h:i < (c.shTT - c.sh1) / 6
 . simp only [h,↓reduceIte]
   rw [qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
     qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
     qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega)]
 . simp [h]
lemma vt {n:Nat} {f:u7 n} {s:Nat} {c:Cfg} (e:CfgOk n f s c) {d:List (u7 n×Nat)} (hlen:d.length<=11) (u:∀ r0 r1 r2 r3 r4 r5:F n, f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false -> 3<=(d.map fun p=>zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :z3 c (va c (eW s c d))=true:=by
 set b:=aR n s c;set m:=(c.shTT - c.sh1) / 6;unfold z3;rw [e.a29_1_eq,e.b5_1_eq];have v:∀ (p:K) (i:Nat),z6 (sv c p.1) i<=if i < m then 3 else 0:=by intro p i;unfold sv;rw [e.m1_eq,e.m12_eq,kh];split;exact q52 _ _ _ _ _ _;omega
 have t:=fun i=>xp (fun p:K=>sv c p.1) m v (e4 b d) (by rw [e4,lLM];omega) i
 apply ky _ m
 . intro i;have ⟨g,h⟩:=t i;change z6 ((e4 b d).foldr (fun p acc=>Nat.add (sv c p.1) acc) 0) i<=_
   have w:(e4 b d).length=d.length:=lLM _;rw [g];rw [w] at h;by_cases j:i < m<;>simp only [j,↓reduceIte] at h ⊢<;>omega
 . intro i j;have ⟨g,_⟩:=t i;change 3<=z6 ((e4 b d).foldr (fun p acc=>Nat.add (sv c p.1) acc) 0) i
   rw [g];have x:((e4 b d).map fun p=>z6 (sv c p.1) i) =
     d.map fun p =>
      zq (p.1 (q1 n (b.getD (c.sh1+6*i) 0)))
       (p.1 (q1 n (b.getD (c.sh1+6*i+1) 0)))
       (p.1 (q1 n (b.getD (c.sh1+6*i+2) 0)))
       (p.1 (q1 n (b.getD (c.sh1+6*i+3) 0)))
       (p.1 (q1 n (b.getD (c.sh1+6*i+4) 0)))
       (p.1 (q1 n (b.getD (c.sh1+6*i+5) 0))):=by
    simp only [e4,lMMp];apply lMCL
    intro p _;dsimp only [Function.comp];rw [nq e p.1 i,if_pos j]
   rw [x];obtain ⟨y,g',h',z',h4',h5'⟩:=e.p1_ok i j;exact u _ _ _ _ _ _ y g' h' z' h4' h5'
def ki {n:Nat}:Nat->List (u7 n×Nat)->u7 n×Nat
 | _,[]=>((fun _=>false),0)
 | 0,a::_=>a
 | k+1,_::rest=>ki k rest
def yl {n:Nat}:Nat->List (u7 n×Nat)->List (u7 n×Nat)
 | _,[]=>[]
 | 0,_::rest=>rest
 | k+1,a::rest=>a::yl k rest
def md {n:Nat} (h:Nat) (d:List (u7 n×Nat)):List (u7 n×Nat):=
 if ble h 32 then
  let c:=Nat.sub h 1;let i:=shiftRight c 1;let v:=beq (land c 1) 1
  let (a,ta):=ki i d;let e:=if beq ta 3 then 2 else 0
  let w:=invF a;let r:=yl i d
  if v then (w,e)::(a,0)::r else (w,e)::r
 else
  let g:=Nat.sub h 33
  let t:=beq (land g 1) 1
  let u:=beq (land (shiftRight g 1) 1) 1
  let x:=beq (land (shiftRight g 2) 1) 1
  let (i,j):=gj (shiftRight g 3) 16 1
  let (a,ta):=ki i d;let (b,tb):=ki j d
  let r:=yl i (yl j d)
  if x then
   let e:=if beq ta 3||beq tb 3 then 1 else 0
   let r1:=if t then (b,0)::r else r
   let s:=if u then (a,0)::r1 else r1
   (meetF a b,e)::s
  else
   let r1:=if t then (b,if beq tb 3 then 1 else 0)::r else r
   let s:=if u then (a,if beq ta 3 then 1 else 0)::r1 else r1
   (joinF a b,0)::s
def gm {n:Nat} (b:List (u7 n×Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (u7 n×Nat)
 | 0,_,_=>b
 | d+1,s,j =>
  let e:=sa (PT s) j;let c:=land e 1023
  if beq c 0 then b
  else md c (gm b PT d (Nat.add s 1) (land (shiftRight e 10) 8191))
def eh {n:Nat} (b:Nat) (c:List (u7 n×Nat)) (PT:Nat->Nat) (s j:Nat):List (u7 n×Nat):=
 gm c PT (Nat.sub b s) s j
lemma fu {n:Nat} (c:M) (i:Nat) (b:List (u7 n×Nat)) :jw i (e4 c b)=(d7 c (ki i b).1,(ki i b).2):=by
 induction i generalizing b with
 | zero=>cases b with | nil=>simp [jw,ki,e4,gk] | cons _ _=>rfl
 | succ k ih=>cases b with | nil=>simp [jw,ki,e4,gk] | cons _ t=>exact ih t
lemma ft {n:Nat} (c:M) (i:Nat) (b:List (u7 n×Nat)) :ms i (e4 c b)=e4 c (yl i b):=by
 induction i generalizing b with
 | zero=>cases b<;>rfl
 | succ k ih=>cases b with | nil=>rfl | cons p t=>simp only [qy,ms,yl,ih]
lemma lk {n:Nat} (c:M) (b:Nat) (d:List (u7 n×Nat)) :bb (2 ^ c.length - 1) b (e4 c d)=e4 c (md b d):=by
 unfold bb md;simp only [v5]
 split
 . simp only [fu,ft];split<;>simp [e4,rd]
 . simp only [fu,ft]
   split
   . cases beq (land (Nat.sub b 33) 1) 1<;>cases beq (land (shiftRight (Nat.sub b 33) 1) 1) 1<;>simp [e4,q9]
   . cases beq (land (Nat.sub b 33) 1) 1<;>cases beq (land (shiftRight (Nat.sub b 33) 1) 1) 1<;>simp [e4,qc]
lemma ng {n:Nat} (b:M) (c:List (u7 n×Nat)) (PT:Nat->Nat) (d s j:Nat) :mx (2 ^ b.length - 1) (e4 b c) PT d s j=e4 b (gm c PT d s j):=by
 induction d generalizing s j with
 | zero=>rfl
 | succ d ih=>simp only [mx,gm,v5];split;rfl;rw [ih,lk]
lemma rh {n:Nat} (b:M) (c:Nat) (d:List (u7 n×Nat)) (PT:Nat->Nat) (s j:Nat) :a8 (2 ^ b.length - 1) c (e4 b d) PT s j=e4 b (eh c d PT s j):=
 ng b d PT (Nat.sub c s) s j
lemma ln {n:Nat} (b:Nat) (c:List (u7 n×Nat)) (PT:Nat->Nat) (s j:Nat) :a8 (2 ^ (2 ^ n) - 1) b (u4 n c) PT s j=u4 n (eh b c PT s j):=by have hlen:(range (2 ^ n)).length=2 ^ n:=lLR;simpa [u4,e4,u9,hlen] using rh (range (2 ^ n)) b c PT s j
lemma wm {n:Nat} (i:Nat) (b:List (u7 n×Nat)):(yl i b).Sublist b:=by
 induction i generalizing b with
 | zero=>cases b with | nil=>exact List.Sublist.slnil | cons a t=>exact List.Sublist.cons a (List.Sublist.refl t)
 | succ k ih=>cases b with | nil=>exact List.Sublist.slnil | cons a t=>exact List.Sublist.cons_cons a (ih t)
lemma vj {α:Type} (b:Q) (x : α×Nat) (l:List (α×Nat)) (e:x.2<=3) (c:AllTagsLe3 l):AllTagsLe3 (if b then x::l else l):=by
 intro p d;cases b
 . exact c p d
 . rcases lMM.1 d with rfl|h'
   . exact e
   . exact c p h'
lemma vn {α:Type} (x : α×Nat) (l:List (α×Nat)) (b:x.2<=3) (c:AllTagsLe3 l):AllTagsLe3 (x::l):=by intro p d;rcases lMM.1 d with rfl|h';exact b;exact c p h'
lemma q43 {n:Nat} (g:Nat) {b:List (u7 n×Nat)} (h:AllTagsLe3 b) :AllTagsLe3 (md g b):=by
 unfold md;have c:∀ i,AllTagsLe3 (yl i b):=fun i p d=>h p ((wm i b).subset d)
 have e:∀ i j,AllTagsLe3 (yl i (yl j b)):=fun i j p d=>c j p ((wm i _).subset d)
 split
 . dsimp only;split
   . exact vn _ _ (by split<;>omega) (vn _ _ (by omega) (c _))
   . exact vn _ _ (by split<;>omega) (c _)
 . dsimp only;split
   . exact vn _ _ (by split<;>omega)
      (vj _ _ _ (by omega) (vj _ _ _ (by omega) (e _ _)))
   . exact vn _ _ (by omega)
      (vj _ _ _ (by split<;>omega) (vj _ _ _ (by split<;>omega) (e _ _)))
lemma q59 {n:Nat} (b:Nat) {c:List (u7 n×Nat)} (h:AllTagsLe3 c) (PT:Nat->Nat) (s j:Nat):AllTagsLe3 (eh b c PT s j):=by
 unfold eh;generalize Nat.sub b s=d
 induction d generalizing s j with
 | zero=>exact h
 | succ d ih=>simp only [gm];split;exact h;exact q43 _ (ih _ _)
lemma jb (T h fuel lo hi:Nat) (b:lo < hi):sc T h fuel lo hi < hi:=by
 induction fuel generalizing lo hi with
 | zero=>exact b
 | succ fuel ih =>
  simp only [sc,v5];split
  . rename_i c;have c':lo+2<=hi:=Eq.mp nBE c;have d:Nat.div (Nat.add lo hi) 2=(lo+hi) / 2:=rfl;have e:Nat.div (Nat.add lo hi) 2 < hi:=by rw [d];omega
    have g:lo < Nat.div (Nat.add lo hi) 2:=by rw [d];omega
    split;exact ih _ hi e;exact lt_trans (ih lo _ g) e
  . exact b
lemma j8 (NN FL HT:Nat->Nat) (s h:Nat) (b:dz NN FL HT s h≠999999) :dz NN FL HT s h < NN s:=by
 unfold dz at b ⊢;simp only [v5] at b ⊢;cases c:beq (NN s) 0
 . rw [c] at b;simp only [bFT,↓reduceIte] at b ⊢;have d:0 < NN s:=by have:=y3 c;omega
   cases e:beq (ba (HT s) (sc (HT s) h (FL s) 0 (NN s))) h
   . rw [e] at b;simp only [bFT,↓reduceIte] at b;exact absurd rfl b
   . simp only [↓reduceIte];exact jb (HT s) h (FL s) 0 (NN s) d
 . rw [c] at b;exact absurd rfl b
lemma kt (a b:K):mq a b=true↔a=b:=by rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩;simp [mq,nBQ]
lemma lu (x:K) (b b':J) (h:jy x b=some b'):b.Perm (x::b'):=by
 induction b generalizing b' with
 | nil=>simp [jy] at h
 | cons a t ih =>
  simp only [jy] at h;split at h
  . rename_i d;cases h;rw [(kt x a).1 d]
  . cases c:jy x t with
    | none=>rw [c] at h;cases h
    | some r=>rw [c] at h;cases h;exact (lPC a (ih r c)).trans (List.Perm.swap x a r)
lemma y5 (c b:J) (h:jk c b=true):c.Perm b:=by
 induction c generalizing b with
 | nil=>cases b with | nil=>exact List.Perm.nil | cons _ _=>simp [jk] at h
 | cons a t ih =>
  simp only [jk] at h;cases d:jy a b with
  | none=>rw [d] at h;cases h
  | some b' => rw [d] at h;exact (lPC a (ih b' h)).trans (lu a b b' d).symm
lemma nn (x:K) (b:J):(fp x b).Perm (x::b):=by induction b with|nil=>exact lPR _|cons a t ih=>simp only [fp];split;exact lPR _;exact (lPC a ih).trans (List.Perm.swap x a t)
lemma xm (b:J):(me b).Perm b:=by induction b with|nil=>exact List.Perm.nil|cons a t ih=>exact (nn a (me t)).trans (lPC a ih)
lemma kg {n:Nat} (b shTT:Nat) (c:List (u7 n×Nat)) :sz shTT (e4 (e6 n b shTT) c)=u4 n c:=by
 induction c with
 | nil=>rfl
 | cons p t ih =>
  rcases p with ⟨g,tg⟩;simp only [qy,ir,sz,v5,ih]
  have d:=my (n:=n) (n8 n b shTT) g;rw [jj n b shTT] at d;rw [e6,d]
lemma yk {n:Nat} {f:u7 n} {g:V} (c:vh f g) (b:List (u7 n×Nat)) :∃ π:(F n)->(F n),Function.Bijective π/\(∀ x,f (π x)=f x) /\ wx g (u4 n b)=u4 n (b.map fun p=>((fun x=>p.1 (π x)),p.2)):=by
 obtain ⟨π,d,e,i⟩:=c;refine ⟨π,d,e,?_⟩
 induction b with|nil=>rfl|cons p t ih=>rcases p with ⟨h,tg⟩;simp only [ir,lMC,wx,v5,i,ih]
lemma yv {α β:Type} {f : α->β} (d:Function.Injective f) :
  ∀ {c b:List α},(c.map f).Perm (b.map f)->c.Perm b
 | [],b,hp=>by cases b with | nil=>exact List.Perm.nil | cons _ _=>exact absurd hp.length_eq (by simp)
 | x::c,b,hp=>by
  have e:f x∈b.map f:=hp.subset (by simp)
  obtain ⟨y,hy,g⟩:=lMp.1 e
  have h:y=x:=d g;subst h
  obtain ⟨l1,l2,rfl⟩:=List.append_of_mem hy
  have i:(f y::c.map f).Perm (f y::(l1++l2).map f):=
   hp.trans (by simpa [lMA] using (lPM (a:=f y) (l₁:=l1.map f) (l₂:=l2.map f)))
  exact (lPC y (yv d (List.Perm.cons_inv i))).trans lPM.symm
lemma zv {n:Nat} (c d:List (u7 n×Nat)):(u4 n c).Perm (u4 n d)↔c.Perm d:=by
 constructor
 . intro b;have g:Function.Injective (fun p:u7 n×Nat=>(u9 n p.1,p.2)):=fun ⟨_,_⟩ ⟨_,_⟩ e=>by
    simp only [Prod.mk.injEq] at e;exact Prod.ext (yc e.1) e.2
   exact yv g b
 . exact fun b=>b.map _
lemma xw {n:Nat} {f:u7 n} {g:V} (h:vh f g) (c:J) (b:List (u7 n×Nat)) (d:c.Perm (u4 n b)) :∃ π:(F n)->(F n),Function.Bijective π/\(∀ x,f (π x)=f x) /\ (gh g c).Perm (u4 n (b.map fun p=>((fun x=>p.1 (π x)),p.2))):=by
 unfold gh;dsimp only;split
 . obtain ⟨π,i,j,s⟩:=yk h b;refine ⟨π,i,j,?_⟩
   have e:∀ l,wx g l=l.map (fun p=>(ym g p.1,p.2)):=fun l=>by
    induction l with|nil=>rfl|cons p t ih=>simp [wx,v5,ih]
   have u:(wx g c).Perm (wx g (u4 n b)):=by rw [e,e];exact d.map _
   exact (xm _).trans (u.trans (by rw [s]))
 . exact ⟨id,Function.bijective_id,fun _=>rfl,by simpa using d⟩
lemma xv {n:Nat} {f:u7 n} (d:List (V)) (e:∀ g∈d,vh f g) (b:J) (c:List (u7 n×Nat)) (h:b.Perm (u4 n c)) :∃ π:(F n)->(F n),Function.Bijective π/\(∀ x,f (π x)=f x) /\ (ck d b).Perm (u4 n (c.map fun p=>((fun x=>p.1 (π x)),p.2))):=by
 induction d generalizing b c with
 | nil=>exact ⟨id,Function.bijective_id,fun _=>rfl,by simpa [ck] using h⟩
 | cons g rest ih =>
  obtain ⟨π1,i,j,s⟩:=xw (e g (by simp)) b c h;obtain ⟨π2,t,u,v⟩:=ih (fun g' w=>e g' (lMCM g w)) (gh g b) _ s
  exact ⟨π1 ∘ π2,i.comp t,fun x=>by simp [j,u],by simpa [ck,lMMp,fCD] using v⟩
lemma rb {n:Nat} {f:u7 n} (c:List (V)) (d:∀ g∈c,vh f g) (b:List (u7 n×Nat)) :∃ π:(F n)->(F n),Function.Bijective π/\(∀ x,f (π x)=f x) /\ (sb c (u4 n b)).Perm (u4 n (b.map fun p=>((fun x=>p.1 (π x)),p.2))):=by
 unfold sb;have e:=xm (u4 n b);cases c with
 | nil=>exact ⟨id,Function.bijective_id,fun _=>rfl,by simpa using e⟩
 | cons g rest =>
  cases rest with
  | nil=>exact xw (d g (by simp)) _ b e
  | cons g2 rest2 => obtain ⟨π1,h,i,j⟩:=xv (g::g2::rest2) d _ b e;obtain ⟨π2,s,t,u⟩:=xv (g::g2::rest2) d _ _ j;exact ⟨π1 ∘ π2,h.comp s,fun x=>by simp [i,t],by simpa [lMMp,fCD] using u⟩
def w2 {n:Nat} (f:u7 n) (b:M) (NN:Nat->Nat) (R_bfn:Nat->Nat->List (u7 n×Nat)) (c:Nat->J->Q):Prop:=
 ∀ s zs_b,c s (e4 b zs_b)=true ->
  ∃ j < NN s,∃ π:(F n)->(F n),
   Function.Bijective π/\(∀ x,f (π x)=f x) /\
   (zs_b.map fun p=>((fun x=>p.1 (π x)),p.2)).Perm (R_bfn s j)
lemma q87 {n:Nat} (f:u7 n) (c shTT d:Nat) (NN FL HT:Nat->Nat) (R_bfn:Nat->Nat->List (u7 n×Nat)) (Rtt:Nat->Nat->J) (e:∀ s j,Rtt s j=u4 n (R_bfn s j)) :w2 f (e6 n c shTT) NN R_bfn (p4 shTT d Rtt NN FL HT):=by
 intro s g h;unfold p4 at h;simp only [v5,kg,bAT,bNT,zh] at h;obtain ⟨i,b⟩:=h;rw [e] at b;exact ⟨_,j8 NN FL HT s _ i,id,Function.bijective_id,fun _=>rfl,
  by simpa using (zv g (R_bfn s _)).1 (y5 _ _ b)⟩
lemma q86 {n:Nat} (f:u7 n) (t shTT u:Nat) (d:V) (v:vh f d) (NN FL HT:Nat->Nat) (R_bfn:Nat->Nat->List (u7 n×Nat)) (Rtt:Nat->Nat->J) (e:∀ s j,Rtt s j=u4 n (R_bfn s j)) :w2 f (e6 n t shTT) NN R_bfn (k9 shTT u d Rtt NN FL HT):=by
 intro s g h;unfold k9 at h;simp only [v5,kg] at h
 split at h
 . rename_i i;simp only [bAT,bNT,zh] at i;obtain ⟨c,b⟩:=i;rw [e] at b;exact ⟨_,j8 NN FL HT s _ c,id,Function.bijective_id,fun _=>rfl,
    by simpa using (zv g (R_bfn s _)).1 (y5 _ _ b)⟩
 . simp only [bAT,bNT,zh] at h;obtain ⟨c,b⟩:=h;obtain ⟨π,w,x,y⟩:=yk v g;rw [y] at c b;rw [e] at b;exact ⟨_,j8 NN FL HT s _ c,π,w,x,(zv _ _).1 (y5 _ _ b)⟩
lemma q37 {n:Nat} (f:u7 n) (w shTT i:Nat) (d:List (V)) (y:∀ g∈d,vh f g) (NN FL HT:Nat->Nat) (R_bfn:Nat->Nat->List (u7 n×Nat)) (Rtt:Nat->Nat->J) (t:∀ s j,Rtt s j=u4 n (R_bfn s j)) :w2 f (e6 n w shTT) NN R_bfn (r9 shTT i d Rtt NN FL HT):=by
 have z:∀ p:List (V),(∀ g∈p,vh f g)->∀ s (b:List (u7 n×Nat)),
   vm i Rtt NN FL HT s p (u4 n b)=true ->
   ∃ j < NN s,∃ π:(F n)->(F n),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (b.map fun q=>((fun x=>q.1 (π x)),q.2)).Perm (R_bfn s j):=by
  intro p;induction p with
  | nil =>
   intro _ s b h;simp only [vm,v5,bAT,bNT,zh] at h;obtain ⟨e,c⟩:=h;rw [t] at c;exact ⟨_,j8 NN FL HT s _ e,id,Function.bijective_id,fun _=>rfl,
     by simpa using (zv b (R_bfn s _)).1 (y5 _ _ c)⟩
  | cons g rest ih =>
   intro u s b h;simp only [vm,v5] at h
   split at h
   . rename_i v;simp only [bAT,bNT,zh] at v;obtain ⟨e,c⟩:=v;rw [t] at c;exact ⟨_,j8 NN FL HT s _ e,id,Function.bijective_id,fun _=>rfl,
      by simpa using (zv b (R_bfn s _)).1 (y5 _ _ c)⟩
   . obtain ⟨π1,h1,h2,h3⟩:=yk (u g (by simp)) b;rw [h3] at h;obtain ⟨j,hj,π2,h4,h5,h6⟩:=ih (fun g' hm=>u g' (lMCM g hm)) s _ h
     exact ⟨j,hj,π1 ∘ π2,h1.comp h4,fun x=>by simp [h2,h5],by simpa [lMMp,fCD] using h6⟩
 intro s b h;unfold r9 at h;rw [kg] at h;exact z d y s b h
lemma q55 {n:Nat} (f:u7 n) (u shTT d:Nat) (b:List (V)) (v:∀ g∈b,vh f g) (e:Nat->V) (w:∀ k,vh f (e k)) (NN FL HT PT:Nat->Nat) (R_bfn:Nat->Nat->List (u7 n×Nat)) (Rtt:Nat->Nat->J) (y:∀ s j,Rtt s j=u4 n (R_bfn s j)) :w2 f (e6 n u shTT) NN R_bfn (c4 shTT d b e Rtt NN FL HT PT):=by
 intro s i h;unfold c4 at h;simp only [v5,kg] at h
 split at h;. cases h
 . rename_i z
   have h0:=y3 (Bool.eq_false_iff.2 z);set j:=dz NN FL HT s (av d (sb b (u4 n i)));have hj:j < NN s:=j8 NN FL HT s _ h0;set h1:=shiftRight (sa (PT s) j) 23;obtain ⟨π1,h2,h3,h4⟩:=rb b v i;obtain ⟨π2,h5,h6,h7⟩:=yk (w h1) (R_bfn s j);rw [y,h7] at h;have h8:=(zv _ _).1 (h4.symm.trans (y5 _ _ h));obtain ⟨π2_inv,h9,c⟩:=Function.bijective_iff_has_inverse.1 h5
   have x2:Function.Bijective π2_inv:=Function.bijective_iff_has_inverse.2 ⟨π2,c,h9⟩;have x3:∀ x,f (π2_inv x)=f x:=fun x=>by have:=h6 (π2_inv x);rw [c x] at this;exact this.symm
   refine ⟨j,hj,π1 ∘ π2_inv,h2.comp x2,fun x=>by simp [h3,x3],?_⟩
   have t:=h8.map (fun p:u7 n×Nat=>((fun x=>p.1 (π2_inv x)),p.2))
   have a1:(((R_bfn s j).map fun p=>((fun x=>p.1 (π2 x)),p.2)).map fun p=>((fun x=>p.1 (π2_inv x)),p.2))=R_bfn s j:=by
    rw [lMMp];have a2:((fun p:u7 n×Nat=>((fun x=>p.1 (π2_inv x)),p.2)) ∘ fun p:u7 n×Nat=>((fun x=>p.1 (π2 x)),p.2))=id:=by funext ⟨g,tg⟩;simp only [fCD,id];congr 1;funext x;exact congrArg g (c x)
    rw [a2,lMI]
   rw [a1] at t;simpa [lMMp,fCD] using t
lemma span_sound (P:Nat->Q) (c b:Nat) (h:span P c b=true) :∀ i,b<=i->i < b+c->P i=true:=by
 induction c generalizing b with
 | zero=>intro i d e;omega
 | succ m ih =>
  simp only [span,bAT] at h;intro i d e;by_cases g:i=b
  . subst g;exact h.1
  . exact ih (b+1) h.2 i (by omega) (by omega)
lemma k5 (c:Cfg) (b:J) :(o5 c b).1=yx c b /\ (o5 c b).2.1=v4 c b /\ ((o5 c b).2.2.map fun t=>(t.1,t.2.1))=b:=by
 induction b with
 | nil=>simp [o5,yx,v4]
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩
  obtain ⟨d,e,g⟩:=ih;unfold o5;rw [show o5 c rest=(yx c rest,v4 c rest,(o5 c rest).2.2) from Prod.ext d (Prod.ext e rfl)];simp only [v5,lMC,yx,v4,lFC,wC,wU,wi,ag,g,and_self]
lemma d5 (c:Cfg) (w d:Nat) (b:J) :(o5 c ((w,d)::b)).2.2 = (w,d,wC c w,wU c w,yx c b,v4 c b)::(o5 c b).2.2:=by
 obtain ⟨e,g,_⟩:=k5 c b;conv_lhs=>unfold o5
 rw [show o5 c b=(yx c b,v4 c b,(o5 c b).2.2) from Prod.ext e (Prod.ext g rfl)];simp only [v5,wC,wU,wi,ag]
lemma dy (c:Cfg) (b:J):ez c b=zf c b:=by
 induction b with
 | nil=>rfl
 | cons p rest ih=>rcases p with ⟨w,tg⟩;simp only [ez,ih,zf,lFC,mh,fm]
lemma dx (c:Cfg) (b:J):ey c b=va c b:=by
 induction b with
 | nil=>rfl
 | cons p rest ih=>rcases p with ⟨w,tg⟩;simp only [ey,ih,va,lFC,sv]
lemma y8 (z:Nat) (b:J) :t3 z b=false↔∀ p∈b,p.1≠z:=by
 induction b with
 | nil=>simp [t3]
 | cons a t ih=>rcases a with ⟨w,tg⟩;simp only [t3,bOF,zh,ih,lMM,forall_eq_or_imp]
lemma o7 {n b:Nat} {c:Cfg} {g:u7 n} {d:List (u7 n×Nat)} (h:∀ p∈d,p.1≠g):t3 (eL b c g) (eW b c d)=false:=by
 rw [y8];intro p i;rcases lMp.1 i with ⟨q,j,rfl⟩
 exact fun e=>h q j (ik (n8 n b c.shTT) e)
lemma c5 {n b:Nat} {c:Cfg} {g:u7 n} (d:g≠fun _=>false):eL b c g≠0:=by intro e;rw [<- gk (n:=n) (aR n b c)] at e;exact d (ik (n8 n b c.shTT) e)
lemma a3 {n b:Nat} {f:u7 n} {c:Cfg} (d:CfgOk n f b c) {g:u7 n} (h:g≠fun _=>true):eL b c g≠c.all1v:=by intro e;have hlen:=zl n b c.shTT;rw [d.all1v_eq,<- hlen,<- bc (n:=n) (aR n b c)] at e;exact h (ik (n8 n b c.shTT) e)
lemma td {n s:Nat} {f:u7 n} {c:Cfg} (e:CfgOk n f s c) {d:List (u7 n×Nat)} (hlen:d.length<=11) (u:∀ r0 r1 r2 r3 r4 r5:F n, f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false -> 3<=(d.map fun p=>v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :qb c (zf c (eW s c d)) 0=true:=by
 set b:=aR n s c;set m:=(c.sh1 - c.sh0) / 6;unfold qb;simp only [v8,nAZ];rw [e.a29_0_eq,e.b5_0_eq];have v:∀ (p:K) (i:Nat),z6 (mh c p.1) i<=if i < m then 3 else 0:=by intro p i;unfold mh;rw [e.m0_eq,yy];split;exact yr _ _ _ _ _ _;omega
 have t:=fun i=>xp (fun p:K=>mh c p.1) m v (e4 b d) (by rw [e4,lLM];omega) i
 apply ky _ m
 . intro i;have ⟨g,h⟩:=t i;change z6 ((e4 b d).foldr (fun p acc=>Nat.add (mh c p.1) acc) 0) i<=_
   have w:(e4 b d).length=d.length:=lLM _;rw [g];rw [w] at h;by_cases j:i < m<;>simp only [j,↓reduceIte] at h ⊢<;>omega
 . intro i j;have ⟨g,_⟩:=t i;change 3<=z6 ((e4 b d).foldr (fun p acc=>Nat.add (mh c p.1) acc) 0) i
   rw [g];have x:((e4 b d).map fun p=>z6 (mh c p.1) i) =
     d.map fun p =>
      v6 (p.1 (q1 n (b.getD (c.sh0+6*i) 0))) (p.1 (q1 n (b.getD (c.sh0+6*i+1) 0)))
       (p.1 (q1 n (b.getD (c.sh0+6*i+2) 0))) (p.1 (q1 n (b.getD (c.sh0+6*i+3) 0)))
       (p.1 (q1 n (b.getD (c.sh0+6*i+4) 0))) (p.1 (q1 n (b.getD (c.sh0+6*i+5) 0))):=by
    simp only [e4,lMMp];apply lMCL
    intro p _;dsimp only [Function.comp];rw [np e p.1 i,if_pos j]
   rw [x];obtain ⟨y,g',h',z',h4',h5'⟩:=e.p0_ok i j;exact u _ _ _ _ _ _ y g' h' z' h4' h5'
lemma o1 {n x:Nat} {f:u7 n} {c:Cfg} (hc:CfgOk n f x c) {ns d x2 h8:Nat} {hd:Unit->J} {he:J->Q} {b:List (u7 n×Nat)} (hlen_eq:d=b.length) (h6:hd ()=eW x c b) (hi:x2=yx c (eW x c b)) (hf:h8=v4 c (eW x c b)) (hr:Run (invF (n:=n)) meetF joinF f ns (b.map Prod.fst))
  (hcu:k1 c ns d x2 h8 hd he=true) :
  he (eW x c b)=true:=by
 have hlen_le:b.length<=ns+1:=by have:=tn hr;simpa using this
 unfold k1 at hcu
 have hj:blt (Nat.add ns 1) d=false:=by
  rw [Bool.eq_false_iff];intro h;rw [nBL] at h;change ns+1 < d at h;omega
 simp only [hj,bFT,↓reduceIte] at hcu
 cases ns with
 | zero =>
  have w:=tk hr
  cases b with
  | nil=>cases w
  | cons p rest =>
    cases rest with
    | nil =>
      rcases p with ⟨g,tg⟩;simp only [lMC,lMN,List.cons.injEq] at w
      rcases w with ⟨rfl,_⟩
      simp only [nBR,↓reduceIte,h6,eW,e4,lMC,lMN,hc.goalv_eq] at hcu ⊢
      exact hcu
    | cons _ _=>simp at w
 | succ s' =>
  have hk:beq (s'+1) 0=false:=q2 (Nat.succ_ne_zero s')
  have hm:∀ u v:F n,f u=false->f v=true->∃ p∈b,p.1 u≠p.1 v:=by
    intro u v hu hv
    obtain ⟨g,hg,hn⟩:=w6 hr (show f u≠f v by rw [hu,hv];decide)
    obtain ⟨p,hp,rfl⟩:=lMp.1 hg;exact ⟨p,hp,hn⟩
  have hq:x2=c.lok:=hi.trans (zz hc hm)
  simp only [hk,hq,nBR,Bool.not_true,bFT,↓reduceIte] at hcu
  cases x3:ble d 11
  . simp only [x3,bFT,↓reduceIte,h6] at hcu;exact hcu
  . simp only [x3,↓reduceIte] at hcu
    have hh:b.length<=11:=by rw [nBE] at x3;omega
    by_cases a1:Nat.sub (Nat.add (s'+1) 1) d=0
    . have h9:(b.map Prod.fst).length=(s'+1)+1:=by
        rw [lLM];change (s'+1)+1 - d=0 at a1;omega
      have h7:∀ u v,f u=false->f v=true->∃ p∈b,p.1 u=false/\p.1 v=true:=by
        intro u v hu hv;obtain ⟨g,hg,y,z⟩:=tj hr h9 u v hu hv
        obtain ⟨p,hp,rfl⟩:=lMp.1 hg;exact ⟨p,hp,y,z⟩
      have a2:∀ r0 r1 e i j t,f r0=true->f r1=true->f e=true->f i=false->f j=false->f t=false ->
         3<=(b.map fun p=>v6 (p.1 r0) (p.1 r1) (p.1 e) (p.1 i) (p.1 j) (p.1 t)).sum:=by
        intro r0 r1 e i j t w y z h3 h4 h5
        have:=dc hr h9 r0 r1 e i j t w y z h3 h4 h5
        rwa [lMMp] at this
      have h7' : h8=c.lok:=hf.trans (q6 hc h7)
      have a2' : qb c (ez c (eW x c b)) 0=true:=by rw [dy];exact td hc hh a2
      simp only [qz a1,h7',nBR,Bool.not_true,bFT,↓reduceIte,h6,a2'] at hcu
      exact hcu
    . simp only [q2 a1,bFT,↓reduceIte] at hcu
      by_cases b1' : Nat.sub (Nat.add (s'+1) 1) d=1
      . have h9:(b.map Prod.fst).length=s'+1:=by
         rw [lLM];change (s'+1)+1 - d=1 at b1';omega
        have ht:(beq h8 c.lok||z3 c (ey c (eW x c b)))=true:=by
         rcases ds hr h9 with hu|hs
         . have h7:∀ u v,f u=false->f v=true->∃ p∈b,p.1 u=false/\p.1 v=true:=by
            intro u v y z;obtain ⟨g,hg,ha,hb⟩:=hu u v y z
            obtain ⟨p,hp,rfl⟩:=lMp.1 hg;exact ⟨p,hp,ha,hb⟩
           simp [hf.trans (q6 hc h7)]
         . have hw:∀ r0 r1 e i j t,f r0=true->f r1=true->f e=true->f i=false->f j=false->f t=false ->
             3<=(b.map fun p=>zq (p.1 r0) (p.1 r1) (p.1 e) (p.1 i) (p.1 j) (p.1 t)).sum:=by
            intro r0 r1 e i j t w y z h3 h4 h5
            have:=hs r0 r1 e i j t w y z h3 h4 h5;rwa [lMMp] at this
           rw [dx,vt hc hh hw];simp
        simp only [qz b1',↓reduceIte,h6,ht] at hcu
        exact hcu
      . simp only [q2 b1',bFT,↓reduceIte,h6] at hcu;exact hcu
lemma o8 {b c:Q} (h:(if !b then false else c)=true):b=true/\c=true:=by cases b<;>cases c<;>simp_all
lemma dp (b b2 c0 c1 c d:Q) (h:(let e:=if c0&&b2 then c1 else c0
   let g:=if e&&b then c else e
   if g&&b&&b2 then d else g)=true) :
  c0=true/\(b2=true->c1=true)/\(b=true->c=true)/\(b=true->b2=true->d=true):=by
 cases b<;>cases b2<;>cases c0<;>cases c1<;>cases c<;>cases d<;>simp_all
lemma b0 {n d:Nat} {f:u7 n} {c:Cfg} (h:CfgOk n f d c) {v w:Nat} {x:J->Q} {z a b:u7 n} {s t u:Nat} {y h0 i j:Q} {g:List (u7 n×Nat)} (hlen:w=g.length+2) (h1:i=true->y=true) (h2:j=true->h0=true) (e:Run (invF (n:=n)) meetF joinF f v (((z,s)::qk i (a,t) (qk j (b,u) g)).map Prod.fst))
   (h4:l8 c v w x (eL d c z) s (eL d c a) t (wC c (eL d c a)) (wU c (eL d c a))
    (eL d c b) u (wC c (eL d c b)) (wU c (eL d c b))
    (yx c (eW d c g)) (v4 c (eW d c g)) y h0 (fun ()=>eW d c g)=true) :
   x (eW d c ((z,s)::qk i (a,t) (qk j (b,u) g)))=true:=by
 unfold l8 at h4;simp only [v5] at h4
 have ⟨h3,h5,h6,h7⟩:=dp _ _ _ _ _ _ h4
 cases i<;>cases j
 . simp only [qk,bFT,↓reduceIte] at e ⊢
   exact o1 h (by simp [hlen,nSE]) rfl rfl rfl e h3
 . simp only [qk,bFT,↓reduceIte] at e ⊢
   exact o1 h (by simp [hlen]) rfl rfl rfl e (h5 (h2 rfl))
 . simp only [qk,bFT,↓reduceIte] at e ⊢
   exact o1 h (by simp [hlen]) rfl rfl rfl e (h6 (h1 rfl))
 . simp only [qk,↓reduceIte] at e ⊢
   exact o1 h (by simp [hlen,nAE]) rfl rfl rfl e (h7 (h1 rfl) (h2 rfl))
lemma uf {α : Type _} {c d:Q} {z a b : α} {r r' : List α} (h:r.Perm r') :(z::qk c a (qk d b r)).Perm (z::qk c a (qk d b r')):=by
 apply lPC;cases c<;>cases d<;>simp only [qk,bFT,↓reduceIte]
 . exact h
 . exact lPC _ h
 . exact lPC _ h
 . exact lPC _ (lPC _ h)
lemma c9 {α : Type _} {c d:Q} {z a b : α} {r r' : List α} (h:r.Perm r') :(z::qk d b (qk c a r)).Perm (z::qk c a (qk d b r')):=by
 apply lPC;cases c<;>cases d<;>simp only [qk,bFT,↓reduceIte]
 . exact h
 . exact lPC _ h
 . exact lPC _ h
 . exact (List.Perm.swap _ _ _).trans (lPC _ (lPC _ h))
lemma k0 (c:Cfg) (g:Nat->Nat->Nat->Nat->Nat->Nat->(Unit->J)->Q) (b d e:J) (a ta:Nat) (h:a4 g (yx c b) (v4 c b) b (o5 c (d++(a,ta)::e)).2.2=true) :g a ta (wC c a) (wU c a) (yx c ((b++d)++e)) (v4 c ((b++d)++e)) (fun ()=>(b++d)++e)=true:=by
 induction d generalizing b with
 | nil => simp only [lNA] at h;simp only [lANil];rw [d5] at h;unfold a4 at h;have i:=(Eq.mp (bAT) h).1;have s:=(k5 c e).2.2;rw [s,<- vc,<- zu] at i;exact i
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩;simp only [lCA] at h
  rw [d5] at h;unfold a4 at h;have j:=(Eq.mp (bAT) h).2;have t:lor (yx c b) (wC c w)=yx c (b++[(w,tg)]):=by rw [vc];simp [yx,q7,ah]
  have u:lor (v4 c b) (wU c w)=v4 c (b++[(w,tg)]):=by rw [zu];simp [v4,q7,ah]
  rw [t,u] at j;simpa [lAA] using ih (b++[(w,tg)]) j
lemma l6 (c:Cfg) (i:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->(Unit->J)->Q) (a ta:Nat) (d e g:J) (b j:Nat) (h:t7 i a ta (wC c a) (wU c a) (yx c d) (v4 c d) d (o5 c (e++(b,j)::g)).2.2=true) :i a ta (wC c a) (wU c a) b j (wC c b) (wU c b) (yx c ((d++e)++g)) (v4 c ((d++e)++g)) (fun ()=>(d++e)++g)=true:=by
 induction e generalizing d with
 | nil => simp only [lNA] at h;simp only [lANil];rw [d5] at h;unfold t7 at h;have s:=(Eq.mp (bAT) h).1;have u:=(k5 c g).2.2;rw [u,<- vc,<- zu] at s;exact s
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩;simp only [lCA] at h
  rw [d5] at h;unfold t7 at h;have t:=(Eq.mp (bAT) h).2;have v:lor (yx c d) (wC c w)=yx c (d++[(w,tg)]):=by rw [vc];simp [yx,q7,ah]
  have x:lor (v4 c d) (wU c w)=v4 c (d++[(w,tg)]):=by rw [zu];simp [v4,q7,ah]
  rw [v,x] at t;simpa [lAA] using ih (d++[(w,tg)]) t
lemma t9 (c:Cfg) (j:Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->Nat->(Unit->J)->Q) (d e g i:J) (a ta b s:Nat) (h:m4 j (yx c d) (v4 c d) d (o5 c (e++(a,ta)::g++(b,s)::i)).2.2=true) :j a ta (wC c a) (wU c a) b s (wC c b) (wU c b) (yx c (((d++e)++g)++i)) (v4 c (((d++e)++g)++i)) (fun ()=>((d++e)++g)++i)=true:=by
 induction e generalizing d with
 | nil => simp only [lNA,lCA] at h;simp only [lANil];rw [d5] at h;unfold m4 at h;exact l6 c j a ta d g i b s (Eq.mp (bAT) h).1
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩;simp only [lCA] at h
  rw [d5] at h;unfold m4 at h;have t:=(Eq.mp (bAT) h).2;have u:lor (yx c d) (wC c w)=yx c (d++[(w,tg)]):=by rw [vc];simp [yx,q7,ah]
  have v:lor (v4 c d) (wU c w)=v4 c (d++[(w,tg)]):=by rw [zu];simp [v4,q7,ah]
  rw [u,v] at t;simpa [lAA] using ih (d++[(w,tg)]) t
lemma n5 {n d:Nat} {f:u7 n} {c:Cfg} (hc:CfgOk n f d c) {v:Nat} {h8:J->Q} {g:List (u7 n×Nat)} (hn:p9 c h8 v (eW d c g)=true) (hx:TR f (v+1) g) :∃ nxt_b,TR f v nxt_b/\h8 (eW d c nxt_b)=true:=by
 unfold p9 at hn;obtain ⟨hq,hr⟩:=Eq.mp (bAT) hn;rcases hx.inv_succ with
   ⟨a,ta,r,save,y,x2,x3,hy,z,u',a1,a2,s⟩ |
   ⟨a,ta,b,tb,r,ka,kb,y,x3,hd,h4,h5,z,u',a1,hh,a2,s⟩ |
   ⟨a,ta,b,tb,r,ka,kb,y,x2,he,h4,h5,z,u',a1,hh,a2,s⟩
 . obtain ⟨i,j,w,h6⟩:=iq y;have s' : TR f v ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (i++j)):=
     TagRun.perm (lPC _ (by cases save<;>simp [qk,h6])) s
   have hs:=s'.len_le;have ht:g.length=i.length+j.length+1:=by have:=congrArg List.length w;simp at this;omega
   have hf:(eW d c g).length=g.length:=lLM _;have hz:ble 1 (Nat.sub (Nat.add v 2) (eW d c g).length)=true:=by rw [hf,nBE];change 1<=v+2 - g.length;cases save<;>simp [qk] at hs<;>omega
   simp only [hz,↓reduceIte] at hq;have b1:eW d c g=eW d c i++(eL d c a,ta)::eW d c j:=by rw [w];simp [eW,e4]
   have hg:=k0 c (a5 c v (eW d c g).length (Nat.sub (Nat.add v 2) (eW d c g).length) (eW d c g) h8 false)
     [] (eW d c i) (eW d c j) (eL d c a) ta (by rw [<- b1];exact hq)
   unfold a5 at hg;have h3:∀ p∈g,p.1≠invF a:=fun p ha=>by
     rcases lMM.1 (y.subset ha) with rfl|xi;exact a1.symm;exact a2 p xi
   have hb:(beq (eL d c (invF a)) 0||beq (eL d c (invF a)) c.all1v ||
       t3 (eL d c (invF a)) (eW d c g))=false:=by
     simp [q2 (c5 z),q2 (a3 hc u'),o7 h3]
   simp only [q2 x2,q2 x3,bNF,bTA,↓reduceIte,v5,(qv hc a).symm,hb,bFT,lNA,<- kj] at hg;have hi:(if beq ta 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [nBQ]
   rw [hi] at hg;have ⟨xs,hu⟩:=o8 hg;cases save
   . simp only [qk,bFT,↓reduceIte] at s';exact ⟨_,s',o1 hc (by rw [hf,ht];simp) rfl rfl rfl s'.toRun xs⟩
   . have h10:ta≠3:=fun e=>by have:=hy e;cases this
     have h11:ble 2 (Nat.sub (Nat.add v 2) (eW d c g).length)=true:=by rw [hf,nBE];change 2<=v+2 - g.length;simp [qk] at hs;omega
     simp only [q2 h10,bNF,h11,bTA,↓reduceIte] at hu;simp only [qk,↓reduceIte] at s';exact ⟨_,s',o1 hc (by rw [hf,ht];simp [nAE]) rfl rfl rfl s'.toRun hu⟩
 . have hv:∀ a' ta' b' tb' ka' kb' i t j,
      g=i++(a',ta')::t++(b',tb')::j ->
      ta'≠2->tb'≠2->(ta'=1->ka'=false)->(tb'=1->kb'=false) ->
      joinF a' b'≠(fun _=>false)->joinF a' b'≠(fun _=>true) ->
      (∀ p∈g,p.1≠joinF a' b') ->
      TR f v ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (i++t++j))) ->
      ∃ nxt_b,TR f v nxt_b/\h8 (eW d c nxt_b)=true:=by
     intro a' ta' b' tb' ka' kb' i t j w x3' hd' h4' h5' z' u'' h3 s';have b1:eW d c g=eW d c i++(eL d c a',ta')::eW d c t++(eL d c b',tb')::eW d c j:=by rw [w];simp [eW,e4,lAA]
     have h9:=t9 c (f5 c v (eW d c g).length (eW d c g) h8) []
      (eW d c i) (eW d c t) (eW d c j) (eL d c a') ta' (eL d c b') tb' (by rw [<- b1];exact hr)
     simp only [lNA,<- kj] at h9;unfold f5 at h9;have hj:=(o8 h9).1;have hb:(beq (eL d c (joinF a' b')) 0||beq (eL d c (joinF a' b')) c.all1v ||
        t3 (eL d c (joinF a' b')) (eW d c g))=false:=by
      simp [q2 (c5 z'),q2 (a3 hc u''),o7 h3]
     simp only [q2 x3',q2 hd',bNF,bTA,↓reduceIte,v5,(qc _ a' b').symm,hb,bFT] at hj;have h12:(if beq ta' 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [nBQ]
     have h13:(if beq tb' 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [nBQ]
     rw [h12,h13] at hj;refine ⟨_,s',b0 hc ?_ (fun h=>by simp [q2 (fun e=>by have:=h4' e;rw [h] at this;cases this)])
      (fun h=>by simp [q2 (fun e=>by have:=h5' e;rw [h] at this;cases this)]) s'.toRun hj⟩
     unfold eW e4;rw [lLM,w];simp;omega
   have h3:∀ p∈g,p.1≠joinF a b:=fun p ha=>by
     rcases lMM.1 (y.subset ha) with rfl|u'';exact a1.symm
     rcases lMM.1 u'' with rfl|h2';exact hh.symm;exact a2 p h2'
   rcases fn y with ⟨i,t,j,w,h6⟩|⟨i,t,j,w,h6⟩
   . exact hv a ta b tb ka kb i t j w x3 hd h4 h5 z u' h3 (TagRun.perm (uf h6) s)
   . have h7:joinF b a=joinF a b:=by funext x;exact Bool.or_comm _ _
     exact hv b tb a ta kb ka i t j w hd x3 h5 h4 (h7 ▸ z) (h7 ▸ u')
      (fun p y' => h7 ▸ h3 p y') (h7 ▸ TagRun.perm (c9 h6) s)
 . have hw:∀ a' ta' b' tb' ka' kb' i t j,
      g=i++(a',ta')::t++(b',tb')::j ->
      ta'≠1->tb'≠1->(ta'≠0->ka'=false)->(tb'≠0->kb'=false) ->
      meetF a' b'≠(fun _=>false)->meetF a' b'≠(fun _=>true) ->
      (∀ p∈g,p.1≠meetF a' b') ->
      TR f v ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (i++t++j))) ->
      ∃ nxt_b,TR f v nxt_b/\h8 (eW d c nxt_b)=true:=by
     intro a' ta' b' tb' ka' kb' i t j w x2' he' h4' h5' z' u'' h3 s';have b1:eW d c g=eW d c i++(eL d c a',ta')::eW d c t++(eL d c b',tb')::eW d c j:=by rw [w];simp [eW,e4,lAA]
     have h9:=t9 c (f5 c v (eW d c g).length (eW d c g) h8) []
      (eW d c i) (eW d c t) (eW d c j) (eL d c a') ta' (eL d c b') tb' (by rw [<- b1];exact hr)
     simp only [lNA,<- kj] at h9;unfold f5 at h9;have hk:=(o8 h9).2;have hb:(beq (eL d c (meetF a' b')) 0||beq (eL d c (meetF a' b')) c.all1v ||
        t3 (eL d c (meetF a' b')) (eW d c g))=false:=by
      simp [q2 (c5 z'),q2 (a3 hc u''),o7 h3]
     simp only [q2 x2',q2 he',bNF,bTA,↓reduceIte,v5,(q9 _ a' b').symm,hb,bFT] at hk;have hi:(if (beq ta' 3||beq tb' 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [nBQ]
     rw [hi] at hk;refine ⟨_,s',b0 hc ?_
      (fun h=>qz (Classical.byContradiction fun hm=>by have:=h4' hm;rw [h] at this;cases this))
      (fun h=>qz (Classical.byContradiction fun hm=>by have:=h5' hm;rw [h] at this;cases this)) s'.toRun hk⟩
     unfold eW e4;rw [lLM,w];simp;omega
   have h3:∀ p∈g,p.1≠meetF a b:=fun p ha=>by
     rcases lMM.1 (y.subset ha) with rfl|u'';exact a1.symm
     rcases lMM.1 u'' with rfl|h2';exact hh.symm;exact a2 p h2'
   rcases fn y with ⟨i,t,j,w,h6⟩|⟨i,t,j,w,h6⟩
   . exact hw a ta b tb ka kb i t j w x2 he h4 h5 z u' h3 (TagRun.perm (uf h6) s)
   . have h7:meetF b a=meetF a b:=by funext x;exact Bool.and_comm _ _
     have h14:(if tb=3\/ta=3 then 1 else 0)=(if ta=3\/tb=3 then 1 else 0):=by by_cases u'' : ta=3<;>by_cases h2'' : tb=3<;>simp [u'',h2'']
     exact hw b tb a ta kb ka i t j w he x2 h5 h4 (h7 ▸ z) (h7 ▸ u')
      (fun p y' => h7 ▸ h3 p y') (h7 ▸ h14 ▸ TagRun.perm (c9 h6) s)
lemma c8 {n e:Nat} {f:u7 n} {c:Cfg} (g:CfgOk n f e c) {s:Nat} {h:List (u7 n×Nat)} (b:s5 c s (eW e c h)=true):¬ TR f s h:=by
 cases s with
 | zero => intro d;obtain ⟨tg,rfl⟩:=d.inv_zero;simp only [s5,eW,e4,lMC,lMN,g.goalv_eq,nBR] at b;cases b
 | succ ns=>intro d;obtain ⟨_,_,i⟩:=n5 g b d;cases i
lemma gu {n:Nat} {f:u7 n} {d:Nat} {c:Cfg} (h:CfgOk n f d c) (e:Nat) (_hcap:e<=11) (NN:Nat->Nat) (R_bfn:Nat->Nat->List (u7 n×Nat)) (R:Nat->Nat->J) (w:∀ s j,R s j=eW d c (R_bfn s j)) (_hTags:∀ s j,AllTagsLe3 (R_bfn s j)) (t:Nat->J->Q) (h0:w2 f (aR n d c) NN R_bfn t) (x:∀ s≤ e,∀ i < NN s,bar c t R s i=true) :∀ s≤ e,∀ i < NN s,¬ TR f s (R_bfn s i):=by
 intro s;induction s with
 | zero => intro _ i u v;have b:=x 0 (nZL e) i u;obtain ⟨tg,h1⟩:=v.inv_zero;simp only [bar,w,h1,eW,e4,lMC,lMN,h.goalv_eq,nBR] at b;cases b
 | succ ns ih =>
  intro hs i u v;have h2:=ih (by omega);have b:=x (ns+1) hs i u;simp only [bar,v8,w] at b;obtain ⟨y,z,g⟩:=n5 h b v;cases hf:t ns (eW d c y)
  . simp only [hf,bFT,↓reduceIte] at g;cases ns with
    | zero=>simp at g
    | succ s' => simp only [q2 (Nat.succ_ne_zero s'),bFT,↓reduceIte] at g;exact c8 h g z
  . obtain ⟨j,hj,π,h3,h4,h5⟩:=h0 ns y hf;exact h2 j hj (TagRun.perm h5 (wp π h3 h4 z))
def d0 (n:Nat) (f:u7 n):List (V)->List (J)->Q
 | [],[]=>true
 | sw::sws,ps::pss =>
  kq n ps&&(de n ps==sw)&&(ym sw (u9 n f)==u9 n f)&&d0 n f sws pss
 | _,_=>false
lemma ye (n:Nat) (f:u7 n) (b:List (V)) (c:List (J)) (h:d0 n f b c=true) :∀ sw∈b,vh f sw:=by
 induction b generalizing c with
 | nil=>intro _ e;cases e
 | cons sw sws ih =>
  cases c with
  | nil=>simp [d0] at h
  | cons ps pss =>
   simp only [d0,bAT,beq_iff_eq] at h;obtain ⟨⟨⟨i,j⟩,d⟩,s⟩:=h;intro g t;rcases lMM.1 t with rfl|u
   . rw [<- j] at d ⊢;exact kw f ps i d
   . exact ih pss s g u
def oq (n:Nat) (f:u7 n) (b:Nat->V) (c:List (J)):Q:=
 (range c.length).all fun i =>
  let d:=c.getD i []
  kq n d&&(de n d==b i)&&(ym (b i) (u9 n f)==u9 n f)
lemma q58 (n:Nat) (f:u7 n) (c:Nat->V) (b:List (J)) (h:oq n f c b=true) (g:∀ i≥ b.length,c i=[]) :∀ i,vh f (c i):=by
 intro i;by_cases j:i < b.length
 . have d:=lAL.1 h i (lMRG.2 j);simp only [bAT,beq_iff_eq] at d;obtain ⟨⟨s,t⟩,e⟩:=d;rw [<- t] at e ⊢;exact kw f (b.getD i []) s e
 . rw [g i (by omega)];exact lx f
def w8 (n:Nat) (f:u7 n):Q:=
 let t:=u9 n f;!(beq t 0)&&!(beq t (2 ^ (2 ^ n) - 1))
lemma ju (n:Nat) (f:u7 n) (h:w8 n f=true) :∃ y y':F n,f y≠f y':=by
 unfold w8 at h;simp only [bAT,bNT,zh] at h;obtain ⟨d,e⟩:=h;have g:∃ r < 2 ^ n,f (q1 n r)=true:=by by_contra b;push Not at b;apply d;apply nEQ;intro r;rw [vr,nZT];split;exact Bool.eq_false_iff.2 (b r ‹_›);rfl
 have i:∃ r < 2 ^ n,f (q1 n r)=false:=by
  by_contra b;push Not at b;apply e;apply nEQ;intro r;rw [vr,nTB];split
  . rename_i c;have:f (q1 n r)=true:=by cases j:f (q1 n r);exact absurd j (b r c);rfl
    simp [c,this]
  . rename_i c;simp [c]
 obtain ⟨r1,_,s⟩:=g;obtain ⟨r0,_,t⟩:=i;exact ⟨q1 n r1,q1 n r0,by rw [s,t];decide⟩
def xh (n:Nat) (f:u7 n):Q:=
 (finRange n).all fun v =>
  (range (2 ^ n)).any fun r=>let x:=q1 n r;f (update x v (!x v))!=f x
lemma q44 (n:Nat) (f:u7 n) (h:xh n f=true) :∀ v:Fin n,∃ x:F n,f (update x v (!x v))≠f x:=by intro v;have b:=lAL.1 h v (lMFR v);obtain ⟨r,_,c⟩:=lAN.1 b;exact ⟨q1 n r,bne_iff_ne.1 c⟩
def rc (c:Cfg) (e:Nat->J->Q) (d:J) (b:Nat):Q:=
 e b d||(!(beq b 0)&&s5 c b d)
def b7 (n b:Nat) (f:u7 n) (d:Nat) (c:Cfg) (e:Fin n->Nat) (g j:J) (s:Nat->J->Q):Q:=
 let t:=aR n d c
 let h:=ofFn fun i:Fin n=>((fun x:F n=>x i),e i)
 ble b 11&&w3 n f d c&&w8 n f&&xh n f &&
 ((finRange n).all fun i=>ble (e i) 3) &&
 (g==e4 t h)&&(j==u4 n h) &&
 ((range (b+1)).all fun s0=>blt (Nat.add s0 1) n||rc c s g s0)
lemma n1 {n b:Nat} (f:u7 n) (e:Nat) (c:Cfg) (d:Fin n->Nat) (g h7:J) (NN PT:Nat->Nat) (h:Nat->J->Q) (w:b7 n b f e c d g h7 h=true) (h2:w2 f (aR n e c) NN (eh b (ofFn fun i:Fin n=>((fun x:F n=>x i),d i)) PT) h) (h8:∀ s≤ b,∀ i < NN s,bar c h (a8 c.all1v b g PT) s i=true) (h9:∀ v:Fin n,d v=0 \/ (d v=1/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 1<=s') \/ (d v=3/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 2<=s')) :∀ t:Nat,HCS n f t->b+1<=t:=by
 unfold b7 at w;simp only [bAT,nBE,beq_iff_eq] at w;rcases w with ⟨⟨⟨⟨⟨⟨⟨x2,x3⟩,a1⟩,a2⟩,b1⟩,z⟩,hxstt⟩,ha⟩
 have hc:=jn n f e c x3;have hb:=ju n f a1;have hd:=q44 n f a2;set u:List (u7 n×Nat):=ofFn fun i:Fin n=>((fun x:F n=>x i),d i)
 have he:AllTagsLe3 u:=fun p hp=>by
   rw [lMOF] at hp;obtain ⟨i,rfl⟩:=hp;exact Eq.mp nBE (lAL.1 b1 i (lMFR i))
 have hf:=zl n e c.shTT;have hR:∀ s j,a8 c.all1v b g PT s j=eW e c (eh b u PT s j):=fun s j=>by
   rw [z,hc.all1v_eq,<- hf,rh]
 have hg:=gu hc b x2 NN (eh b u PT) (a8 c.all1v b g PT) hR
   (fun s j=>q59 b he PT s j) h h2 h8
 intro t hh;by_contra hlt;have hi:t<=b:=by omega
 obtain ⟨s0,hk,h0⟩:=q88 f b d hb hd h9 t hi hh;have h3:=lAL.1 ha s0 (lMRG.2 (by omega));simp only [bOT] at h3;rcases h3 with hm|h1
 . have hlt_n:s0+1 < n:=by simpa [nBL,v8] using hm
   have htr_len:n<=s0+1:=by simpa using h0.len_le
   omega
 . unfold rc at h1;simp only [bOT] at h1;rcases h1 with h4|h5
   . rw [z] at h4;obtain ⟨j,hj,π,hn,hq,hr⟩:=h2 s0 u h4;exact hg s0 hk j hj (TagRun.perm hr (wp π hn hq h0))
   . simp only [bAT,bNT,zh] at h5;obtain ⟨_,h6⟩:=h5;rw [z] at h6;exact c8 hc h6 h0
lemma a0 {n d b:Nat} (g:d=2 ^ 2 ^ n - 1) (c:List (u7 n×Nat)) (e:J) (h:e=u4 n c) (PT:Nat->Nat) (s j:Nat) :a8 d b e PT s j=u4 n (eh b c PT s j):=by rw [g,h];exact ln b c PT s j
lemma d8 {P:Nat->Nat->Q} {b:Nat} {NN:Nat->Nat} (h:(range (b+1)).all (fun s=>span (P s) (NN s) 0)=true) :∀ s≤ b,∀ i < NN s,P s i=true:=fun s hs i hi =>
 span_sound (P s) (NN s) 0 (lAL.1 h s (lMRG.2 (by omega))) i (nZL _) (by omega)
lemma span_chunk3 {P:Nat->Q} {a b d:Nat} (c:span P a 0=true) (e:span P b a=true) (g:span P (d - (a+b)) (a+b)=true) :∀ i < d,P i=true:=fun i hi=>by
 by_cases h1i:i < a
 . exact span_sound P a 0 c i (nZL _) (by omega)
 . by_cases h2i:i < a+b
   . exact span_sound P b a e i (by omega) (by omega)
   . exact span_sound P (d - (a+b)) (a+b) g i (by omega) (by omega)
lemma n3 {n:Nat} (f g:u7 n) (h:beq (u9 n f) (u9 n g)=true):f=g:=
 yc (Eq.mp nBQ h)
lemma tv {n b g:Nat} (f:u7 n) (h j:Nat) (c:Cfg) (d:Fin n->Nat) (u e:J) (NN FL HT PT:Nat->Nat) (w:g=2 ^ 2 ^ n - 1) (z:e=u4 n (ofFn fun i:Fin n=>((fun x:F n=>x i),d i))) (h0:b7 n b f h c d u e (p4 c.shTT j (a8 g b e PT) NN FL HT)=true) (h1:∀ s≤ b,∀ i < NN s,bar c (p4 c.shTT j (a8 g b e PT) NN FL HT) (a8 c.all1v b u PT) s i=true) (h2:∀ v:Fin n,d v=0 \/ (d v=1/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 1<=s') \/ (d v=3/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 2<=s')) :∀ t:Nat,HCS n f t->b+1<=t:=
 n1 f h c d u e NN PT _ h0
  (q87 f h c.shTT j NN FL HT _ _ (a0 w _ e z PT)) h1 h2
lemma ec {n b h:Nat} (f:u7 n) (j u:Nat) (c:Cfg) (d:Fin n->Nat) (w e:J) (g:V) (z:J) (NN FL HT PT:Nat->Nat) (h0:h=2 ^ 2 ^ n - 1) (h1:e=u4 n (ofFn fun i:Fin n=>((fun x:F n=>x i),d i))) (h2:d0 n f [g] [z]=true) (h3:b7 n b f j c d w e (k9 c.shTT u g (a8 h b e PT) NN FL HT)=true) (h4:∀ s≤ b,∀ i < NN s,bar c (k9 c.shTT u g (a8 h b e PT) NN FL HT) (a8 c.all1v b w PT) s i=true) (h5:∀ v:Fin n,d v=0 \/ (d v=1/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 1<=s') \/ (d v=3/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 2<=s')) :∀ t:Nat,HCS n f t->b+1<=t:=
 n1 f j c d w e NN PT _ h3
  (q86 f j c.shTT u g (ye n f [g] [z] h2 g (by simp))
   NN FL HT _ _ (a0 h0 _ e h1 PT)) h4 h5
lemma ob {n b j:Nat} (f:u7 n) (u w:Nat) (c:Cfg) (d:Fin n->Nat) (z e:J) (h0 h:List (V)) (h1:List (J)) (NN FL HT PT:Nat->Nat) (h2:j=2 ^ 2 ^ n - 1) (h3:e=u4 n (ofFn fun i:Fin n=>((fun x:F n=>x i),d i))) (h4:d0 n f h0 h1=true) (h5:h.all (fun g=>h0.contains g)=true) (h6:b7 n b f u c d z e (r9 c.shTT w h (a8 j b e PT) NN FL HT)=true) (h7:∀ s≤ b,∀ i < NN s,bar c (r9 c.shTT w h (a8 j b e PT) NN FL HT) (a8 c.all1v b z PT) s i=true) (h8:∀ v:Fin n,d v=0 \/ (d v=1/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 1<=s') \/ (d v=3/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 2<=s')) :∀ t:Nat,HCS n f t->b+1<=t:=by
 have hg:=ye n f h0 h1 h4;have hp:∀ g∈h,vh f g:=fun g h9 =>
  hg g (List.contains_iff_mem.1 (lAL.1 h5 g h9))
 exact n1 f u c d z e NN PT _ h6
  (q37 f u c.shTT w h hp NN FL HT _ _ (a0 h2 _ e h3 PT)) h7 h8
lemma w7 {n b j:Nat} (f:u7 n) (u w:Nat) (c:Cfg) (d:Fin n->Nat) (z e:J) (h:List (V)) (h1:List (J)) (g:Nat->V) (h0:List (J)) (NN FL HT PT:Nat->Nat) (h2:j=2 ^ 2 ^ n - 1) (h3:e=u4 n (ofFn fun i:Fin n=>((fun x:F n=>x i),d i))) (h4:d0 n f h h1=true) (h5:oq n f g h0=true) (h6:∀ i≥ h0.length,g i=[]) (h7:b7 n b f u c d z e (c4 c.shTT w h g (a8 j b e PT) NN FL HT PT)=true) (h8:∀ s≤ b,∀ i < NN s,bar c (c4 c.shTT w h g (a8 j b e PT) NN FL HT PT) (a8 c.all1v b z PT) s i=true) (h9:∀ v:Fin n,d v=0 \/ (d v=1/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 1<=s') \/ (d v=3/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS n (fun x=>f (update x v false)) s'->b - 2<=s')) :∀ t:Nat,HCS n f t->b+1<=t:=
 n1 f u c d z e NN PT _ h7
  (q55 f u c.shTT w h (ye n f h h1 h4)
   g (q58 n f g h0 h5 h6) NN FL HT PT _ _ (a0 h2 _ e h3 PT)) h8 h9
structure BaseEntry where
 k:Nat
 E:List (Fin k×Fin k)
 lb:Nat
def a6 (c:List BaseEntry):Prop:=
 ∀ b∈c,∀ s:Nat,HCS b.k (d4 [] b.E) s->b.lb<=s
def fq {n:Nat}:List (Fin n)->Q
 | []=>true
 | a::t=>!t.contains a&&fq t
lemma q83 {n:Nat} (l:List (Fin n)) (h:fq l=true):l.Nodup:=by
 induction l with
 | nil=>exact List.nodup_nil
 | cons a t ih => simp only [fq,bAT,bNT] at h;exact List.nodup_cons.2 ⟨by simpa [List.contains_eq_mem] using h.1,ih h.2⟩
inductive GTree (n:Nat) where
 | emp
 | base (idx:Nat) (π:M)
 | f0 (p:Fin n) (t:GTree n)
 | f1 (p:Fin n) (t:GTree n)
 | b2 (p:Fin n) (t0 t1:GTree n)
def t2 (d:List BaseEntry) (n:Nat)
  (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (c:Nat):GTree (n+1)->Q
 | GTree.emp=>E.isEmpty&&fq A&&ble c (A.length - 1)
 | GTree.base idx π =>
  match d[idx]? with
  | none=>false
  | some b =>
   if h:0 < b.k then
    A.isEmpty&&ble c b.lb &&
    un E b.E (fun i=>⟨π.getD i.1 0 % b.k,Nat.mod_lt _ h⟩)
   else false
 | GTree.f0 p t =>
  let A':=eg A p;let E':=g9 E p
  f4 A E p&&(!A'.isEmpty||!E'.isEmpty)&&t2 d n A' E' (c - 1) t
 | GTree.f1 p t =>
  let A':=j6 A E p;let E':=ef A E p
  f4 A E p&&!A.contains p&&E.all (fun e=>e.1!=e.2) &&
   (!A'.isEmpty||!E'.isEmpty)&&t2 d n A' E' (c - 1) t
 | GTree.b2 p t0 t1 =>
  let A0:=eg A p;let E0:=g9 E p
  let A1:=j6 A E p;let E1:=ef A E p
  f4 A E p&&!A.contains p&&E.all (fun e=>e.1!=e.2) &&
   (!A0.isEmpty||!E0.isEmpty)&&(!A1.isEmpty||!E1.isEmpty) &&
   t2 d n A0 E0 (c - 2) t0&&t2 d n A1 E1 (c - 2) t1
lemma l7 (g:List BaseEntry) (h0:a6 g) {n:Nat} (t:GTree (n+1)) (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (d:Nat) (h:t2 g n A E d t=true) :∀ s:Nat,HCS (n+1) (d4 A E) s->d<=s:=by
 induction t generalizing A E d with
 | emp =>
  simp only [t2,bAT,List.isEmpty_iff] at h;rcases h with ⟨⟨rfl,h3⟩,u⟩
  intro s c;have j:=kv A (q83 A h3) s c;have h2:d<=A.length - 1:=Eq.mp nBE u;omega
 | base idx π =>
  unfold t2 at h;cases v:g[idx]? with
  | none=>rw [v] at h;cases h
  | some b =>
   rw [v] at h;dsimp only at h
   split at h
   . rename_i hk
     simp only [bAT,List.isEmpty_iff] at h;rcases h with ⟨⟨rfl,u⟩,h4⟩
     have h5:b∈g:=List.mem_of_getElem? v;intro s c;have j:=jf E b.E (fun i=>⟨π.getD i.1 0 % b.k,Nat.mod_lt _ hk⟩) h4 (h0 b h5) s c
     have h2:d<=b.lb:=Eq.mp nBE u;omega
   . cases h
 | f0 p t ih =>
  simp only [t2,bAT] at h;rcases h with ⟨⟨e,w⟩,x⟩
  intro s c;have j:=jq A E p (eg A p) (g9 E p) (d - 1) e rfl rfl w (ih _ _ _ x) s c;omega
 | f1 p t ih =>
  simp only [t2,bAT] at h;rcases h with ⟨⟨⟨⟨e,y⟩,z⟩,w⟩,x⟩
  intro s c;have j:=js A E p (j6 A E p) (ef A E p) (d - 1) e y z rfl rfl w (ih _ _ _ x) s c;omega
 | b2 p t0 t1 ih0 ih1 =>
  simp only [t2,bAT] at h;rcases h with ⟨⟨⟨⟨⟨⟨e,y⟩,z⟩,h6⟩,h7⟩,h8⟩,h9⟩
  intro s c;have j:=lj A E p (eg A p) (g9 E p) (j6 A E p) (ef A E p) (d - 2)
   e y z rfl rfl rfl rfl h6 h7 (ih0 _ _ _ h8) (ih1 _ _ _ h9) s c;omega
def sm (c:List BaseEntry) (n d:Nat) (E:List (Fin (n+1)×Fin (n+1))) (g:Fin (n+1)->Nat) (h:List (GTree (n+1))):Q:=
 (finRange (n+1)).all fun v =>
  let b:=g v
  let E0:=g9 E v
  let e:=h.getD v.1 GTree.emp
  beq b 0 ||
  (beq b 1&&!E0.isEmpty&&t2 c n [] E0 (d - 1) e) ||
  (beq b 3&&!E0.isEmpty&&t2 c n [] E0 (d - 2) e)
lemma f8 (e:List BaseEntry) (w:a6 e) {n c:Nat} (f:u7 (n+1)) (E:List (Fin (n+1)×Fin (n+1))) (g:Fin (n+1)->Nat) (h2:List (GTree (n+1))) (hf:beq (u9 (n+1) f) (u9 (n+1) (d4 [] E))=true) (h:sm e n c E g h2=true) :∀ v:Fin (n+1),g v=0 \/ (g v=1/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS (n+1) (fun x=>f (update x v false)) s'->c - 1<=s') \/ (g v=3/\(∃ x y,f (update x v false)≠f (update y v false)) /\ ∀ s',HCS (n+1) (fun x=>f (update x v false)) s'->c - 2<=s'):=by
 have i:f=d4 [] E:=n3 _ _ hf;intro v;have z:=lAL.1 h v (lMFR v);simp only [bOT,bAT] at z;rcases z with (h0|⟨⟨h1,j⟩,t⟩)|⟨⟨h3,j⟩,t⟩
 . exact Or.inl (Eq.mp nBQ h0)
 . refine Or.inr (Or.inl ⟨Eq.mp nBQ h1,?_,?_⟩)
   . have b:(fun x=>f (update x v false))=d4 [] (g9 E v):=by
      rw [i];exact zo [] E v
     obtain ⟨x,y,u⟩:=ch [] (g9 E v) (by simp [j]);exact ⟨x,y,by simpa [congrFun b] using u⟩
   . intro s' d';have b:(fun x=>f (update x v false))=d4 [] (g9 E v):=by
      rw [i];exact zo [] E v
     rw [b] at d';exact l7 e w _ [] (g9 E v) (c - 1) t s' d'
 . refine Or.inr (Or.inr ⟨Eq.mp nBQ h3,?_,?_⟩)
   . have b:(fun x=>f (update x v false))=d4 [] (g9 E v):=by
      rw [i];exact zo [] E v
     obtain ⟨x,y,u⟩:=ch [] (g9 E v) (by simp [j]);exact ⟨x,y,by simpa [congrFun b] using u⟩
   . intro s' d';have b:(fun x=>f (update x v false))=d4 [] (g9 E v):=by
      rw [i];exact zo [] E v
     rw [b] at d';exact l7 e w _ [] (g9 E v) (c - 2) t s' d'
lemma b5 (b:BaseEntry) (c:List BaseEntry) (d:∀ s:Nat,HCS b.k (d4 [] b.E) s->b.lb<=s) (e:a6 c):a6 (b::c):=fun x hx=>by
 rcases lMM.1 hx with rfl|hx2;exact d;exact e x hx2
lemma ot {k lb:Nat} (f:u7 k) (E:List (Fin k×Fin k)) (b:beq (u9 k f) (u9 k (d4 [] E))=true) (h:∀ s:Nat,HCS k f s->lb<=s) :∀ s:Nat,HCS k (d4 [] E) s->lb<=s:=by rw [<- n3 _ _ b];exact h
def px:=0xff
def pv:=0xffffffff
def i1:=0xffffffffffffffff
def fh:=0xffffffffffffffffffffffffffffffff
def xe:=0xaaaaaaaaaaaaaaaa
def xd:=0xcccccccccccccccc
def xc:=0xf0f0f0f0f0f0f0f0
def xb:=0xff00ff00ff00ff00
def xa:=0xffff0000ffff0000
def wu:=0xffffffff00000000
def wq:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def wk:=0xcccccccccccccccccccccccccccccccc
def wj:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def wh:=0xff00ff00ff00ff00ff00ff00ff00ff00
def cy:=0xffff0000ffff0000ffff0000ffff0000
def cx:=0xffffffff00000000ffffffff00000000
def cv:=0xffffffffffffffff0000000000000000
def sw0:Nat×Nat×Nat×Nat:=(2,0x30,0xc,0xc3)
def sw1:Nat×Nat×Nat×Nat:=(1,0x44,0x22,0x99)
def sw2:Nat×Nat×Nat×Nat:=(4,0xf000f00,0xf000f0,0xf00ff00f)
def sw3:Nat×Nat×Nat×Nat:=(14,0x33330000,0xcccc,0xcccc3333)
def sw4:Nat×Nat×Nat×Nat:=(12,0xf0f0000,0xf0f0,0xf0f00f0f)
def zy:Nat×Nat×Nat×Nat:=(1,0x44444444,0x22222222,0x99999999)
def xg:Nat×Nat×Nat×Nat:=(16,0xffff00000000,0xffff0000,0xffff00000000ffff)
def ge:Nat×Nat×Nat×Nat:=(2,0x3030303030303030,0xc0c0c0c0c0c0c0c,0xc3c3c3c3c3c3c3c3)
def ij:Nat×Nat×Nat×Nat:=(8,0xff000000ff0000,0xff000000ff00,0xff0000ffff0000ff)
def ig:Nat×Nat×Nat×Nat:=(1,0x4444444444444444,0x2222222222222222,0x9999999999999999)
def gd:Nat×Nat×Nat×Nat:=(28,0xf0f0f0f00000000,0xf0f0f0f0,0xf0f0f0f00f0f0f0f)
def ar:Nat×Nat×Nat×Nat:=(7,0x5500550055005500,0xaa00aa00aa00aa,0xaa55aa55aa55aa55)
def gc:Nat×Nat×Nat×Nat:=(14,0x3333000033330000,0xcccc0000cccc,0xcccc3333cccc3333)
def ie:Nat×Nat×Nat×Nat:=(12,0xf0f00000f0f0000,0xf0f00000f0f0,0xf0f00f0ff0f00f0f)
def ic:Nat×Nat×Nat×Nat:=(30,0x3333333300000000,0xcccccccc,0xcccccccc33333333)
def ib:Nat×Nat×Nat×Nat:=(7,0x55005500550055005500550055005500,0xaa00aa00aa00aa00aa00aa00aa00aa,0xaa55aa55aa55aa55aa55aa55aa55aa55)
def ia:Nat×Nat×Nat×Nat:=(60,0xf0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f)
def fz:Nat×Nat×Nat×Nat:=(30,0x33333333000000003333333300000000,0xcccccccc00000000cccccccc,0xcccccccc33333333cccccccc33333333)
def sq:=0x9e3779b97f4a7c15f39cc0605cedc835
def mk1:=0x3fffffffff
def mk2:=0x1ff
def mk3:=0x3f
def pj:=0x1
def pb:=0x1d
def nz:=0x20
def xz:=0x2
def mk8:=0xffffffffffffffffffffffffffffffffffffffffff
def mk9:=0x3ffffffffffff
def fc:=0x3fffffff
def ry:=0x1041041
def rx:=0x1d75d75d
def rv:=0x20820820
def pt:=0xffffffffffffffffff
def pq:=0x1041041041041
def pp:=0x1d75d75d75d75d
def pn:=0x20820820820820
def bm:=0x3fffffffffffffffffffffffff
def pm:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def pk:=0xffffffffffffffffffffff
def ru:=0x1041
def rt:=0x2082
def rr:=0x1d75d
def rq:=0x20820
def ph:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def pe:=0x41041041041041041
def pd:=0x75d75d75d75d75d75d
def pc:=0x820820820820820820
def rn:=0x1041041041041041041041041
def rm:=0x1d75d75d75d75d75d75d75d75d
def rj:=0x20820820820820820820820820
def pa:=0x7fffffffffffffffffffffffffffffffffff
def ny:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def nx:=0x41041041041041
def nw:=0x82082082082082
def nv:=0x75d75d75d75d75d
def nu:=0x820820820820820
def fb:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def fa:=0x1ffffffffffffffffffffffffffffffffffffff
def rz:=0x2082082082082
def E0:List (Fin 3×Fin 3):=[(0,1),(0,2),(1,2)]
abbrev f0:=d4 [] E0
def r0:=0x101081828304042060a0c1850c18286061418404041010804202
def x0:=[(0x2a934f2e54,0),(0x332596daa1,0),(0x3c0e39f50a,0)]
def vw:=[(0xaa,0),(0xcc,0),(0xf0,0)]
def c0:Cfg:=⟨9,18,24,30,mk1,0x3a071ffe00,mk2,mk3,pj,pb,nz,pj,xz,pb,nz⟩
def N0:Nat->Nat
 | 3=>1
 | _=>0
def L0:Nat->Nat
 | 3=>0
 | _=>0
def H0:Nat->Nat
 | 3=>0x790df1
 | _=>0
def P0:Nat->Nat
 | 3=>0x0
 | _=>0
def ac:=[sw0]
def br:=[sw1]
def ow:=[ac,br]
def xy:=[ac,br,ac,br,ac]
lemma fg:(range 4).all (fun s=>span ((bar c0 (r9 c0.shTT sq xy (a8 px 3 vw P0) N0 L0 H0) (a8 c0.all1v 3 x0 P0)) s) (N0 s) 0)=true:=by decide +kernel
lemma lb0:∀ t,HCS 3 f0 t->4<=t:=ob f0 r0 sq c0 (fun _=>0) x0 vw ow xy [[(1,2)],[(0,1)]] N0 L0 H0 P0 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (d8 fg) (fun _=>Or.inl rfl)
def E1:List (Fin 5×Fin 5):=[(0,1),(0,4),(1,2),(2,3),(3,4)]
abbrev f1:=d4 [] E1
def r1:=0x404a162a0c8080a446180404a110c0c404246030c20045180644282123018622606060644c0c0c0c8981818191303030322606060668c982a44e1a30346161c346062c2c3860654991160ca142850a122448912142850a142448912242850a1428a1220281284880508485091008a090a100942440502
def x1:=[(0xaaaaaaaa4cc5404ea8c6318ac446fc0007feb111a0,0),(0xcccccccc9408ca29318c631c119fac1ff80104640b,0),(0xf0f0f0f038a293025318c630a7fb43e0003e2982d0,0),(0xff00ff0001302530c6318c673ee40800ffc1c03902,0),(0xffff00003a530c940c6318c7f90873ff00000e421c,0)]
def vu:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def c1:Cfg:=⟨50,100,130,136,mk8,0xffeaf8c81c71c71c7ffffffffffffc000000000000,mk9,fc,ry,rx,rv,pj,xz,pb,nz⟩
def N1:Nat->Nat
 | 5=>1
 | 6=>1
 | _=>0
def L1:Nat->Nat
 | 5=>0
 | 6=>0
 | _=>0
def H1:Nat->Nat
 | 5=>0x6ed0be
 | 6=>0x6ed0be
 | _=>0
def P1:Nat->Nat
 | 5=>0x0
 | 6=>0x0
 | _=>0
def yt:=[[sw2,sw3],[sw4,zy]]
def za:Nat->V
 | 0=>[]
 | _=>[]
def ap1:List (J):=[[]]
lemma ff:(range 7).all (fun s=>span ((bar c1 (c4 c1.shTT sq yt za (a8 pv 6 vu P1) N1 L1 H1 P1) (a8 c1.all1v 6 x1 P1)) s) (N1 s) 0)=true:=by decide +kernel
lemma lb1:∀ t,HCS 5 f1 t->7<=t:=w7 f1 r1 sq c1 (fun _=>0) x1 vu yt [[(2,3),(1,4)],[(2,4),(0,1)]] za ap1 N1 L1 H1 P1 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 1<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (d8 ff) (fun _=>Or.inl rfl)
def E6:List (Fin 6×Fin 6):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)]
abbrev f6:=d4 [] E6
def r6:=0x804106061500822c4ca820090b1464820202141861804506061501014a093040208b012a1121481828360a090612141b050483090a0d828241848506c14120c2428360a090612141b050483090a0de3868c582c54a1a3262c0d1258a94a832253252a383054c8cf1a2c4c90e0c0d2a33a64a8d162428348912244891222448912244890a142850a14270e1c3870e1c2244891224488a142850a1428e18284480c1421222428050248890a0220512122281014884e18284480c08052223860a0c1420202
def x6:=[(0xaaaaaaaaaaaaaaaa4ce38e4c02930e1c3870e1c4082d9447ff0003f80fe004082d944400,0),(0xcccccccccccccccc3804d338a0253264c993264093426ffd0901fc00001fc09342600109,0),(0xf0f0f0f0f0f0f0f094002594000e142850a142a92083fa9ab2fe0007f0002920800a9ab2,0),(0xff00ff00ff00ff00013000a0c4c0489122448931c2fc4310dc000007f01ff1c2004310dc,0),(0xffff0000ffff000000e940013300a142850a143e3f0883e0e0000007ffe03e000883e0e0,0),(0xffffffff00000000025380025978c183060c183ffcf30c0300fffff80000003cf30c0300,0)]
def vq:=[(xe,0),(xd,0),(xc,0),(xb,0),(xa,0),(wu,0)]
def c6:Cfg:=⟨88,176,206,224,pm,0xffffffe8eeeceae81c71c71c71c7ffffffffffffffffffffff0000000000000000000000,pk,fc,ry,rx,rv,ru,rt,rr,rq⟩
def N6:Nat->Nat
 | 6=>1
 | 7=>14
 | 8=>1
 | _=>0
def L6:Nat->Nat
 | 6=>0
 | 7=>4
 | 8=>0
 | _=>0
def H6:Nat->Nat
 | 6=>0x3a0f39
 | 7=>0xfebd69fa694af58505f36e68e0d75cb6bc27974b798d306b4aeee2418be33aef8a3a85243a0f39001f92
 | 8=>0x3a0f39
 | _=>0
def P6:Nat->Nat
 | 6=>0x0
 | 7=>0x5000000040000000280000000700000030000000900000006c000000740000007000000005000000010000000b0000000000000024
 | 8=>0x0
 | _=>0
def g6:=[ij,ig]
lemma fe:(range 9).all (fun s=>span ((bar c6 (k9 c6.shTT sq g6 (a8 i1 8 vq P6) N6 L6 H6) (a8 c6.all1v 8 x6 P6)) s) (N6 s) 0)=true:=by decide +kernel
lemma lb6:∀ t,HCS 6 f6 t->9<=t:=ec f6 r6 sq c6 (fun _=>0) x6 vq g6 [(3,4),(0,1)] N6 L6 H6 P6 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (d8 fe) (fun _=>Or.inl rfl)
def bz:List BaseEntry:=[⟨3,E0,4⟩,⟨5,E1,7⟩,⟨6,E6,9⟩]
lemma yj:a6 bz:=b5 _ _ lb0 (b5 _ _ lb1 (b5 _ _ lb6 (fun _ h=>by cases h)))
def E7:List (Fin 6×Fin 6):=[(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)]
def f7:u7 6:=fun x=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 3&&x 4)||(x 3&&x 5)||(x 4&&x 5)
def r7:=0x10108182830808085061890a44c951a2208a060a0d201441818514046060a0c60114181852228918062490128182832421130506100820c0c280808085061908a44a01892804906061501010a0c3060a0c0612141b050603090a0d828301848506c14180c2428360a0c0612141b050603090a0d828301848506c14180c2428368c98b058a943464c581c346162a52a0e1a32604a64a58a8e0c153232c4c706069519526345890a0d22448912244889122448912242850a142850942850a142850912244891224448912244891183060c183060a142850a1428a12224060a1091121403050848890a02848890028909222281014884a1118100a4445090c1420202
def x7:=[(0x2aaaaaaaaaaaaaaa933808d34d38d30003a34c00e1c3870e1c38720408aa54ffc000fe0007f000081022a95200,0),(0x3333333333333333254ff54e94e6a5a004da380122448912244894489115bfaa407f0003f8001fd122445600a9,3),(0x3c3c3c3c3c3c3c3c0e9403a53a500e000940940142850a142850a891221feb54bf8001fc000fe022448800ad52,3),(0x3fc03fc03fc03fc000013000a285404d301500e68d1a3468d1a340e1ffe1020700000000000fffc3870004081c,0),(0x3fffc0003fffc00000025a00000b2894e000a13a142850a142850f1fc3c60c18000001fffff0003c000f183060,3),(0x3fffffffc00000000000e0280000003a502c025c183060c183060ffe3c1830603ffffe000000000078f060c180,3)]
def vf:=[(xe,0),(xd,3),(xc,3),(xb,0),(xa,3),(wu,3)]
def c7:Cfg:=⟨102,204,276,294,ph,0x3ffffffa3ffa3aba071c71c71c71c71c71c71c7fffffffffffffffffffffffffc0000000000000000000000000,bm,pt,pe,pd,pc,ru,rt,rr,rq⟩
def N7:Nat->Nat
 | 5=>2
 | 6=>8
 | 7=>29
 | 8=>10
 | 9=>1
 | _=>0
def L7:Nat->Nat
 | 5=>1
 | 6=>3
 | 7=>5
 | 8=>4
 | 9=>0
 | _=>0
def H7:Nat->Nat
 | 5=>0xdb6fbcb59fba
 | 6=>0xff4208b8920aa522bf75dad66127d83e4ab5329e30073865
 | 7=>0xf6a0f1cdee20cc92b8cb3eaabe18aeb8920aabab409e48b08bb10987d58b7fd1897e822678ec1b73bbc36127d854ce3551601750a3d94acccc477f9a42f4983e088739321e2aff512322a72181e91a87070e618f0260cc
 | 8=>0xf6a0f1be18ae9f3eed73bbc36127d842f49840121b2181e91a870713d354
 | 9=>0x6127d8
 | _=>0
def P7:Nat->Nat
 | 5=>0x1c3d01000839
 | 6=>0x1801c4a01000c3900002c3d0080542d000000000000043d0080489900805441
 | 7=>0x145c00800c7a000000720080105601001403010008390000107200801042000010520180104a00801876008018a20100083b008014540000000000801c720000243e000008010200184a01001001000014240180103d0000003e0000083a010024a20000144000801401010010620080189a
 | 8=>0x5c01000003008000020080005400000000000000240000003c000000400080000100000034
 | 9=>0x0
 | _=>0
def xf:Fin 6->Nat|0=>0|1=>3|2=>3|3=>0|4=>3|5=>3
def bq:=[[xg],[ge],[gd,gc,ar]]
def yz:Nat->V
 | 0=>[]
 | 1=>[gd,gc,ar]
 | 2=>[ie,ic,ar]
 | 3=>[ge]
 | 4=>[xg]
 | _=>[]
def ap7:List (J):=[[],[(2,5),(1,4),(0,3)],[(2,4),(1,5),(0,3)],[(1,2)],[(4,5)]]
lemma fd:(range 10).all (fun s=>span ((bar c7 (c4 c7.shTT sq bq yz (a8 i1 9 vf P7) N7 L7 H7 P7) (a8 c7.all1v 9 x7 P7)) s) (N7 s) 0)=true:=by decide +kernel
lemma lb7:∀ t,HCS 6 f7 t->10<=t:=w7 f7 r7 sq c7 xf x7 vf bq [[(4,5)],[(1,2)],[(2,5),(1,4),(0,3)]] yz ap7 N7 L7 H7 P7 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 5<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (d8 fd) (f8 bz yj f7 E7 xf [.emp,.b2 2 (.f0 0 (.base 0 [0,0,0,0,1,2])) (.f0 0 (.base 0 [0,0,0,0,1,2])),.b2 1 (.f0 0 (.base 0 [0,0,0,0,1,2])) (.f0 0 (.base 0 [0,0,0,0,1,2])),.emp,.b2 5 (.f0 3 (.base 0 [0,1,2])) (.f0 3 (.base 0 [0,1,2])),.b2 4 (.f0 3 (.base 0 [0,1,2])) (.f0 3 (.base 0 [0,1,2]))] (by decide +kernel) (by decide))
def bw:List BaseEntry:=[⟨6,E7,10⟩]++bz
lemma yd:a6 bw:=b5 _ _ (ot f7 E7 (by decide +kernel) lb7) yj
def E12:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5)]
def af:u7 7:=fun x=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)
def r12:=0x88061460614101489928344852264a0c1013068c83404052a34c0202021418640208b132a02010418185100522c4a2480248d131240208b012a1084441818544052060a0d20144181852228c12120c20202141861406148062488ca9202891804506061501014a093022090b0064a121c81828348090850619208a9218283046a480a26201841818528092300c4984850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0ee58992a474e3c1e3868c582c54a3a72e3c293464c581a25b3569d172cd8992a4c858a94a83227365ab1a2a64a547060b9b1d6a74a3434c8cf1a2c4c90e0c0f2e3ab161a54674c951a2c4850793264c993264c98b162c58b162c5870e1c3870e1c352a54a952a54a9468d1a3468d1a270e1c3870e1c382850a142850a1470c0c1422a51a070c14224060a1193161c1092224280502c98b0e0a94684485060244485011038b0d185051212228101c986a51a1120a44270c142240604039315489092223860a0c1420202
def we:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4d34d300e3934c02a34d38ce4e34c0a933804d3001c1c1c1c1c1c1c0840841222daca9447fff80007f807f800001081082445b5952888000,0),(0xcccccccccccccccccccccccccccccccc3a596539300e01300e94e553a8038a4e54c000e4c64646464646464400929a0442537fffd284807f800000007f880125340884a600002509,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f094e38002502538e0153a502501a94000e9682a5a82828282828282a92921044883ffd2a9ad597f80007f807f8052524208910000a5535ab2,3),(0xff00ff00ff00ff00ff00ff00ff00ff0000000e3804c09404c0000680955a0c0000159400191919191919193e31c017fffc020031006e00000000007ffffc638020000004006200dc,0),(0xffff0000ffff0000ffff0000ffff000000000e4c0380025300000b0002801394000ae0096424242424242431fe3ff87008841c3e08700000007fffff8063fc0000e01108387c10e0,3),(0xffffffff00000000ffffffff0000000000ef8094094038e968a28000000025318a2300032828282828282801fffde780f31860c031807fffff8000000000007bcf01e630c1806300,3),(0xffffffffffffffff0000000000000000b0000000000000000000000030c00002800c3280101010101010103fc03e07ff03e07f003e007fffffffff800003807c0ffe07c0fe007c00,1)]
def cr:=[(wq,0),(wk,0),(wj,3),(wh,0),(cy,3),(cx,3),(cv,1)]
def fx:Cfg:=⟨143,286,388,448,ny,0xffffffe8ffecffe8ffffffe8eeeceae81c71c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000,pa,bm,rn,rm,rj,nx,nw,nv,nu⟩
def qf:Nat->Nat
 | 5=>1
 | 6=>14
 | 7=>62
 | 8=>185
 | 9=>30
 | 10=>1
 | _=>0
def zn:Nat->Nat
 | 5=>0
 | 6=>4
 | 7=>6
 | 8=>8
 | 9=>5
 | 10=>0
 | _=>0
def zx:Nat->Nat
 | 5=>0xabbcf4
 | 6=>0xfd9644ee0520ec3af6b8f06bb1c310961b578dd4be8b46ef5c6eed55edfd398e2e3566be1db5880c21de
 | 7=>0xea85b8ea4027dd9b21d8badfd87400d63ce8d42c6dd17089cec13acc90dbcafdd7c842e0c615b3bd0202b82e8aaf909eae483da3908c9d60bf9535d293b7f08ff8168f18c587ff2b7deb467c13767bd65a7a8bab79253773df616bd79268deb867f68c644e2d6314315c6eed5bef72547c6e4b87c14a7bcb43e1cd3fde703b62eb3aea473a3df8353cfb3188722d19e12c43922687f623ec91223f3f1f454319a49a17f8d814444f12a39312a1d11234420b600109cd9e046e43
 | 8=>0xfd37a4fbcbdffb7fb6f9dddbf8acdef62538f59073f4144af270aff20ddaf10b1deeb900eb2050ea841eea4027ea2f7eea0ca4e817c4e7c76ee6b6e2e62416e6167ee2148fe0c41adf7d9cdee409deb6abde25c4dc2b13dbfe4cdb2f80db2421da840dda6e41d97758d88031d51216d4ff0fd458cad33db8d18d10d17089d160f1d05bb1d04610cf82facf0a82cea0e8ce82edcdcd3ecbfe65cac509c9dca2c71080c66292c49434c45b10c378ccc3718ac30567c2e63bc19e5bbe5cbabdf320ba490aba3e97b9b4b4b865feb82e8ab6a424b6002bb5df20b35495b1eca7afa00cae483daa0651a8afaba70c53a6febba3f93da34f68a2a034a065d99fef519e14f19d8b649bbd4d9744e893932a91ecaa8db26e8ae37788e66888c23287f4ba87945184403183ce7881440880832b7ffb537d6ff77c11e27aed3b79bb6e785eed77d11575775d741c8c73333a72d17c6c93646c8d496c47216b7da86a72b26a5d296a0c0f65b7c564df9961f8dc610fc060e43a5f62d15efd095d5b375a4104586e49585f78568c7b5604c9547c6e50827d500b4a4fae134f733f4e2b974cdecb4cac034c05fa475df44637d34590cc437f47422c4540fdd540cc3e3fcabe3dc85d3d72f839df8c37af9137325b36157f353cfb35130d318872304f372687f625ab6a2469812271e121f2431fe0891ef2a71bebe51b03ca188cb7159dfa157d0f14444f13d51013aced13a228136ba30e7a390d39eb0b19370a93f30a8a4309bb22097d9f057a55031c98
 | 9=>0xf270afe3f118db2f80d9e775c71080c38c44c2e63bbfbd01baa831ba3e97b6002bafa00caa1aa3a9bc56a651c89e1055872eee84403179bb6e785d59781fd6741c8c5d5b37568c7b42dea63fcabe3e12a0353cfb31887205aeb5
 | 10=>0x318872
 | _=>0
def pz:Nat->Nat
 | 5=>0x3075
 | 6=>0x509d0000684a000064510000682b0000ac7a000068230000943d0000683b0000b4750000489d00000c76000068730000685300008c51
 | 7=>0x2609d0001f0760000649b0001e43d000260d10000649a0002242d000268d10001f855000224d10002a89b00004cc90002503d000218550001dcd900009451000090c90001b4820000649900006453000158550002a8530002389d0002a83a00014cd10000f8cd0000d0760002a839000298c30001b4760001e83d000264c9000104560000643b00011c2d0001b4750000b0550000d8d90000b02d00026cc900016c3d0001b44a000088d10000647a0000642b00006c9b000000000000647300025451000074560002a83b00028c9b00017c5100000c550000e4cd0000d89d00003026000154c3000034a90000882d0002a8730002a82b
 | 8=>0x89c0000103e0000007600003c9a0000207a000074d30000585200004c56000004400000200100004c3b00001cfb0000604a0000702e00005c7600004ccb000054620000603e0000745100001caa00007471000074990000183e0000589a000074c900006cd30000189f0000205600000c3e00006ca20000043c000010760000549a000018010000143e0000583e000058820000705200001c010000543e00004c7100006cd10000104a0000608200000c4a000020720000548200001ca20000503e0000540100005494000064db00000802000004080000740100005c40000060a2000028720000084c0000209a000004c300004c9a00000864000008bc0000642a0000048c00004cd300000056000050d9000034720000042800006062000048a30000082c00000407000010c90000086800007453000074730000749b00005c020000203d0000204a000074cb0000209400002052000020620000285600001862000014560000489b0000287a000034d300000c6200004c99000030a300004c5300000403000074fb0000743900001062000054a2000034d10000086c000008010000040100001c9d000020d30000085800000424000020420000643e00004c3900006cfb00005c78000018aa0000246200000c560000649a00004cc90000643a000010cb000008940000705600005c3c00003c3a0000046c000008ac000064fb00006c010000047c00004c73000018d9000028a20000349a00001482000060760000642e00006c4a0000608c000054fb00004cfb00006c3e00004c01000010d30000743b000048c30000283e000004740000003e000024a200006c7200003cfb0000243e000014760000049b000010820000000000005c2c0000085600001876000068560000683e00005c01000028010000749a00000830000014a2000034fb000030c30000689e0000189d000064c900000c72000050010000547200001c3e00004c9b00002cc300006c6200001c56000028fb000024fb000020fb00004c51
 | 9=>0x40000000040000003c000000940000000800000054000000c300000034000000440000008c0000002800000007000000050000000b00000048000000090000000200000003000000010000004c0000005c000000240000006c0000007c00000064000000740000002c0000009b0000000000000084
 | 10=>0x0
 | _=>0
def gb:Fin 7->Nat|0=>0|1=>0|2=>3|3=>0|4=>3|5=>3|6=>1
lemma ce:(range 11).all (fun s=>span ((bar fx (p4 fx.shTT sq (a8 fh 10 cr pz) qf zn zx) (a8 fx.all1v 10 we pz)) s) (qf s) 0)=true:=by decide +kernel
lemma lb12:∀ t,HCS 7 af t->11<=t:=tv af r12 sq fx gb we cr qf zn zx pz rfl (by decide +kernel) (by decide +kernel) (d8 ce) (f8 bw yd af E12 gb [.emp,.emp,.f0 6 (.base 2 [0,1,0,4,2,3]),.emp,.f0 5 (.b2 6 (.f0 3 (.base 1 [0,1,2])) (.f0 3 (.base 1 [0,1,2]))),.f0 4 (.b2 6 (.f0 3 (.base 1 [0,1,2])) (.f0 3 (.base 1 [0,1,2]))),.base 3 [0,1,2,3,4,5]] (by decide +kernel) (by decide))
def E20:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)]
def bt:u7 7:=fun x=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)||(x 5&&x 6)
def r20:=0x202225418648890a546982020214186100522c4a2480242c519220092344c4a008418144848851264695010858a93088061060615121481828342212280a26008418144808088920a18202021418685062060a0e08843804c82222a480a26242821418618045090c16208498144822090b006492214418185404052824c110a858a52a28092300c4b03090a090612141e061214120c24283c0c24282418485078184850483090a0f03090a090612141e061214120c24283c0c24282418485078184850483090a0f262c382e58992a474e3c3262c381e3868c582c54a293464c581a2572cd8992a4c858a94a83226ac68a992951c182d6a74a3434c8cf1a2c4c90e0c0eac5869519d325468b12141d4a952a54a952a54a3468d1a3468d1a30a142850a1428509224489122448912224489122448912242850a142850a14270e1c3870e1c387050a142850a1428524448501c3030508a946844850601c3050890182844248890a0140aa51a112141809112140440d185051212228101a946844829109c305089018100d489092223860a0c1420202
def vx:=[(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8e38e4ce0004c04d38c028e4ea8ce540a93000000e070381c0e070381c8088404222eb29447ffe00ff8000000ff8000040442021117594a22000,0),(0x33333333333333333333333333333333134d30134c038e3a50005539400132804ce2bf4c32190c86432190c86504100a984414dfffca1200007fc01ff00003fe8208054c220a60000509,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c2596538038094094e2808e53802a58e8025000a8140a05028140a0502a29229104883ff2a9b565ff00003fe00007fc011491488244000954dab2,3),(0x3fc03fc03fc03fc03fc03fc03fc03fc000000940013000000553000013540b1300031300c86432190c864321903e031c17ffc0803101b800000000000007fffe1f018e080000401880dc,0),(0x3fffc0003fffc0003fffc0003fffc0000c000025940013000000300000a000009404c09520904824120904824031c3e3ff00a11c3e21c1ffff8000000007fc0018e1f00380508e1f10e0,1),(0x3fffffffc00000003fffffffc000000000fc038e38efe5038b0e00000c00000e3389653341a0d068341a0d0683c1fffde00f0600c006000000003ffffff80001e00000f0078300600300,0),(0x3fffffffffffffffc0000000000000000000000002500ea00025000e2533802500000e028140a05028140a0503fffc0207f0381f003801ffffffc0000000000000fe0103f81c0f801c00,3)]
def cq:=[(wq,0),(wk,0),(wj,3),(wh,0),(cy,1),(cx,0),(cv,3)]
def fw:Cfg:=⟨153,306,408,462,fb,0x3ffffffffffb3ffa3ffffffa3bbb3aba071c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000,fa,bm,rn,rm,rj,pq,rz,pp,pn⟩
def sp:Nat->Nat
 | 6=>1
 | 7=>51
 | 8=>557
 | 9=>410
 | 10=>19
 | 11=>1
 | _=>0
def zk:Nat->Nat
 | 6=>0
 | 7=>6
 | 8=>10
 | 9=>9
 | 10=>5
 | 11=>0
 | _=>0
def zp:Nat->Nat
 | 6=>0xa42216
 | 7=>0xf516ddf3d698f3b005ef2d88ef296dec3ef7e16af5dac726d875c4cfaf00cbee06ca61babe5151bba5feb88817b15ee4b07008b008d0a860e9a1a97d9f95879b582c800dd478105a72a6956d10426ab7766655f663c4b9604d3a60096c55fd9f5544855101a64b7aac411bdc38e87e32dd1431e16028d5d72515fa21f0eb1e016f1ab779168c3610bf0810a6890b76a30a4dfd08ccdf07c914
 | 8=>0xff685cff5216ff0ad8fe2f92fdb975fc3e2cfbb49ffb9938fb937cfa5699fa2f5ff9f2a7f9b957f9a091f94e2af8b624f842bcf83bccf724cbf6262ef5938cf52b62f5275af516ddf4c749f46d38f441e4f3e634f334b2f32c8af2c99df29fe5f29ceaf1b87df185e9f180e0f1640bf15542f0fea8f00069ef296def07adef0623ee81c9ee2129ee0febed95d0ed331ded0541ed01e4eccbcaea706be7f1c1e7a100e78497e74fc3e6953fe68025e4ca19e4c4f3e47cc3e4734ee3c687e38b28e2d928e1ee0be1df9ee17396e04f8adfb725df95daddec46dde6dedd364bdc85c9dbfe57dabde3d9b5f8d98160d9180ed90713d8e425d7ff38d794c6d77473d77233d75052d73b4fd59ce5d5795fd54188d52279d47a8bd446aad40458d3db94d3b9ebd3a916d396a6d2dffad1fcf6d1cdfad17648d164fcd139c3cffefacff265cfdbb1ce8aa1ce7a52ccd9b9cc502ccb7d46cb6aabcb66dacb0f9ccaf976cacb81ca54ecca3468ca2998ca1e98c9c1e7c955dbc94ac1c9164ec8e865c8c647c8b151c8a19ac80bdbc77833c74bbfc6fa90c5e5b9c5de98c5aa60c52214c4f355c4c196c42305c3d1dbc377d8c2e192c2d7f7c2b03cc1d951c1051ec0e5e8c0a75abebcb6be48f4be3bbabc8344bc0d67bbe807bb4706bb3bc2bb0b38bab9b6ba7fb8ba48abb9eab3b8ce66b85a99b7ab30b6ebe4b6e0c5b6d6ebb66270b65919b647aab63bddb6371cb5e572b5445fb510b1b4bed5b49842b49233b42eb8b42640b3be8fb35943b341dab304f9b150c3b0e950b05e5ab03167afb85eaf7b04af6086af573caf307aaecacfaea15cadc0c7ad8218ad2734ab6656aaacaeaa16bea97513a8d44ea8d348a8b59aa88036a668a4a64576a643ffa63f3ea55c51a44eada30978a2eb0fa2e154a2dd36a2008ba1f802a1ef869f849f9f29f19deaaa9d47be9d234b9cec8d9bf9249b85819b03ef9afee799a8559921f197388296c20c94b4b1947de693fe82939b0992fc6d92a5ab9299989232be90d61e90a3a8904d1f8fe90a8fe5e08fa9028f9d6f8f22948ee9918d8d598ced928ce5578cd87f8c40cd8b49f78a34e989d00e898348897fa989720c895bcf8787dc875c4d8665fb861ee585e15b8564ef84991f83a7c482d2b58281ff8224cb808650808003804ae8801a157f94d77ee5727eb1827e6c877cc3227c962c7c786c7c25d17bba547b54917a7b2c7a2b9f7a145c79b84578d2b378b64778a7a8788c94784e517827be77fcca77d99c778e5376018d75b15075732274fc9b74f3c174a8aa74757a74559474313d73b56f73725772a6957294a87288ed7278ce715c0f7102a270f10d70b6b06f8d6f6f2a1b6db44f6d17a56cd7686c94f46c32b26bddbe6a90e66a8faa6a23e76a007969fab369eec469ce666943f568f76868f39a68a7c968a1e567ccf066c3df6570e86485ac648505647f27640ef9640e7964015a63178d63015362fe0962495c6091f2608554604d3a5f23bb5ebf325e78525e38c85e31915de4045dd4f35db8b05d66005d50fb5c96445c40695b33ef5b255d5b085a5ac4f15a80d35a6cd059205058117a56cc11568be95670a755c3a35542b9553b24532f7951be16519a5a51828050d0ef50a09a505eba50496d5002704ffc104fac374ed9734de47e4dc0d24c951a4b01b84ac4784a5d2e49e27749e1ca4971aa48cbc6483d904811f1475340468e5746849e46242b45e9ba44e2f0442dab4422d4441ac34418754406444346e342c0b24265c5423fb34102bd4014fd3fe5ee3fab7b3e3d5f3e17223dfe443d72643c09943aab7f3a562a3a37cd39f202399cd438e85237231a36dd09369cc2366ab235f94535c4ea35872c35513f34de4a34827d348089342b7233fef03276de3225e431dcff2fdffe2fdbaf2f249f2ecba22cd8a22ccc202ca71b2ca31a2c27262ba30b2b3de52b2f652b145b2b027e2ad2112a8f88295a7b2947d7278a25273009271fad27191d26292325abc82536e925254e24cbef24980b2490f4245423243e652435b02414d022d91222b4d422adbe22998922892821e0b221df9c21357720e10820d2a21fcfe51fca2b1fafef1f58181e9fbe1e50781c9ad81c3e221bd16e1b64001aa7681a75361a472c19b1e419117118e64f18c2e017ce0817446c172c5e16d09616a483169f7d15bb5314ccfb142c1613fdd913e1e113d423134c8a12e9a91011100ec9ed0e20070deace0de10a0cea8c0bdfb70aefdb0a5a88094b7007def207b9290744f907386e06c33806aaf00699e10665f50616a30606a405af4c03f97203bcf00346ff03000e02253d0184e301259900f5b10038a8
 | 9=>0xff0ad8fdb133fcc89dfb37f5fa5875f9d9e0f8cd4df887d0f842bcf7bfadf6e301f5f727f59913f5275af4d0f0f4b35cf3d698f18a60f14f21f03db3ef551def12edee81c9ed6843ed0cf3ecfb84eba7d3eb22aceb1450ea706bea4c2de9b63be6c4c8e4c4f3e4c15ce4182ee3d54ae3c14fe395fbe37165e358abe260c1e1a0bee19f6de12971de9c43de7035de2178dd283cdd2197dc8127dbe84fdb46d3da1874d9ce8cd9cc9cd9c84dd8df6bd88f5bd857eed82a2cd77babd77473d6a4aed639c7d56931d51664d4f1ced4e616d466a4d3b9ebd39e1dd33d78d21430d164fcd105ccd0a1f4cffefacf79b4cdc98dccd9b9cca9d3cc96eecc502ccc3036cbb18ccb4ef5cae46ecadc85cab08fc955dbc8c647c7a826c6667fc5458cc28d5dc27de4bf8f27bebcb6bda4e7bcdae1bc5ceeba48abb8fa36b8f425b7ab30b728cfb65919b647aab62c7db60f97b5f3b6b50a64b4f735b42b2cb36c11b312dfb304f9b0e24db0bdb7b0b031b03167b008d0b0050eaf6b82af6a06af573caf503baf374faea15cad149dac617eab4737a9be1ea88e92a88036a8587aa83053a80ab7a750cba72577a71adea700e1a6cf61a668a4a5ad30a387aba2f6fea2e154a23268a1f802a1dcbba0ea6f9f75999f38d49dd3b79d5e089d1d989c4a9e9c3dd99c1dbe9bd59f9b582c99c7a8996c719921f19875929834d59828d7977714973882972d9996abbc95d1769595fb95781d9425b593d61b92dd87927ae591da388ff2248fa9028ead988e6c018d926f8d79a28d75ee8c4a768c40cd8be4848aa29e89309088c72f88049d877f368724408665fb83df2283af9983a7c48311fa82bf4482b1728193ba80f06580ba0680a97e80661280026e7fb3177d77557cc3227c0df77a1f8d79e4e17913b878543a784e51782fa477f8d0778e5376dbf37680c7766ba275657d7540e774fc9b74f65d74559473ed367339ed72f98272f292723f977173b470f10d6e8ccb6de4b26d53b06cd7686c71616c37b26c00a56b9e0e6b75926ae0ba6abc246a8faa6a20496a007969a4556982a5696873695e0f685c5c683968680a90679f3066b598665c426633ed6541d8651d4263c9916366bc6307db62c38a622ae961aade61194b605b20604d3a5f9ac45eff705e59895e1b235d57245d1a6d5cac075c30d55b7a695b54af5ae8dc5ad2c059a9bf598e49598ac758096e5691f3567b965629ab5549fa5481d753ee075303f252274450ff4a50496d4f7ea64d23ce4c88624b7bc44ae9214951d44786ba467a874511f64428454399af426fa24230ae4211a84139884102bd40dba540da583fd1a13fc4b23f13753e4d2a3e08443c472c3c24b83a6b6f37cf72377cb23749c436b4c5366211351a1834827d31e160319ff53115e330cb4e2fbcf92f884c2f13562ddf022dbfa52cf7ef2c998f2c58802c27262c01132b99da2b972a2abf962abd0c2a61762a0c9b27ce4f27590d2697d025707d243e6522d91222adbe22a9522289282214cc21f0eb21357721126720d2a22088071fcfe51f400e1ea3a91d53001d498c1c9ad81c75ea1c0a431be5ad1b73851a91fc1a492f19e58d19b1e41948e618e64f17aaaa168c36167e7614a84a13fdd913d42312b5e00fb9b70f6dd30cea8c0c12650b192c0aefdb0ad1b909f44809515a09381208ab75086d9e08096107c9140744f907292b0703e306804803c3d70350cd
 | 10=>0xee81c9e4c4f3d8df6bb5f3b6b304f9a88036a2e15482b1726cd768604d3a59a9bf2abf9622adbe22892821357718e64f13fdd912b5e009f448
 | 11=>0x604d3a
 | _=>0
def py:Nat->Nat
 | 6=>0xb02f
 | 7=>0x80c90007c47100011899000068d10002189d000118510003cc390001dc510003a47a0003cc230005c027000118c90007402e0008109b0003a46a0003cc3b000810730000fc390001b8510003cc9b000000cd0007c4390002ac790003cc5300061c3d0007e83d0003cc730002ec5500046cd1000000000001bc55000154790007cc510001b8710001b8c90003cc3a000030490002acd10007c4510008102b000154590007c499000810530003a4270000fc510002c0550008103b0002aca10007403a000154d10007c4c9
 | 8=>0x46ccb0005d0990002a44a0000bc54000428c90005245a0005185a00046cca000018c0000314d20002d05200064d0500013401000544d20003285600056cd30003383e000270390003ec5100007c350003d49a00038c9e0000b801000054c9000284520005283500013480000364560003ecc90004843d0001a43600046c730001b8510004ac750003b4710004bc290000a85b0002f476000154510005307600017c9d0000343d000524ca000224340004dc8a00014c390003b501000624880006242800038c3600040c5a00006c3e00006440000624980003447a0004dc2d0000fc55000064280003342900022428000438d10005dc5600025451000110390000bc60000474610005bc710000a8a30000142b0003f03d0004808a0000e0510001a49e000480ca000014c90004c90900001471000070560003887a0005d0790000387300002028000280290004407a0000b8530005183d000004ca0003285a0001e4a20004c899000038cb0001389b00040c410002ccc90003645a0002d0ca0000c4ce0002d03f000134280000208c0002cc9900026c3d0000149b0004144a0003507a0000583e0004c9010001a4d20002f4320004f88a00041452000414620003288a0004289900040c6a000478560005d0a10001fc9a0004390900003899000018a80000643c000270c90000b87300017c0100049c7600063052000058d2000018600000389e0002fca6000270990000a8d3000428510000843d000540900006305700046c9900030c8a00003c760002450100040c2d000284d2000438990004f85a00001453000244c900036c320003ec990003bc8a000030d20006248400046c0100042839000488550002d03a0003b4c900053c2e00029c29000470550002a0cd0000c43e0000449e0004dc5a0005fc3d0002a462000228760001c85a0003b451000438a10005e0530000f43e0000d09b000624800004807a0004103d000388d2000624600005d0c900064ccd0001903d0001bc5a0000b09e0000a87b00025051000224030004a0560005c05100046cc9000030a20003b0760001347800064c59000058760000b0560000d0530000f4010001483d000410550005d0710004ac790004ec3d0004785a000340d20006303a0006243c00043c9e000224010005e09b0001e4520004ccce0003b89900047cc40000d83d0004a00100047c3c000224240001e45a0003dc3c000414420000385300015c760003bcca000624300004aca1000038430003bc5a00057c390003b05a0004207100064c750000d09e0002a4560004149a000038010003dc8800009c560002847a00025071000540480003103d0002405d0002b4d300033c3d00042871000070360002b4a30002743d00005056000624580003dc900002d09a00038c530000d0cb000420990005bc510005e0cb0005d1010004789e0001c8d20002d0cf0004603e000018580003448a00015471000094d20000c4620003ec7100030c760004c8c900014c510000f4d20001bc0100005473000064010005b4cd0003b4990001083d0004c03e00056c7b0002b4a600005c5e0001e4d200006c6200013853000054010006443b0004ac5500030c5600004ca20004c03f000110510001bc8a00023cc90001a45a00053c2d0000e8360005e073000438c90004b8a30001343c00006c76000568cd000038a2000004320000303e0001f43d00014c990000e0710005e00100030c5a0003bc01000624780004c03d0005343500060436000014520000bc58000544560000b83b000438710000a8a60000945200003871000018a00002242c0000bc010002ec710001fc320005943d0000584a00011099000338560005e83d000038c9000014990002cc51000054ca000088510001709a00004cd20005249a000388760005445a0000747a0000e0c90000fc3d00023d010000d43200003cd200058c3d00036c560003c43d0000103d0005183f0003d02e000000000001fc2e000270510003dc010003885600038c510000a85e0004b8d30003dc800006240100047c01000150360003dc480005404c0002cc71000014510000204000014cc900022832000244710004cc2e0001983d000540380005dc5a0000386a0001c8760006383d00004c5200047c280000545300043c36000544a20002707100000051000414ca00008039000110c90006303f00043901000424d30003b85100001801000244990000d0010000e1010004b87b00006061000328ca0000200100046c530003405600048c3d00014c710001e45600018c3200064c790004ac59000014cb0002d09f0005d10900064c550002390100043c9a00052401000014730003dc40000058ca000074d20003642e0003bc7600004c5a00005c6a0000140100003841000110710006246c0003b4390003442d0002fca300003c5a0001c8ce000100550000049a000038510000e09900064cd10002cc390000389b000054cb000664520005e09e0004205100040c42000360510001c87a0005c071000304c900043451000094ce0000382b0002183d0004c8710002d89e0003ec390004f87a00006cce0003d432000134880005a8510003d0730006449b0004703d0002d0570004c05a000290560000542b0002b45b0001bc760002d49e000188290001a4a60001387300009c9e0006343d000138010000903d0005903d0004a89a0003142d0000382e0005e05600017032000224780004dc7a0002249c0004806a00038c42000224400003885a000414010005e03b0002fcd3000138cb0004f86a000018280001e49e0000c44a0002f4ca00064d090003643200018c2e0001e83d0005f43d000058620002b47b000224a400050c3d0006643e0003b0d20005449e00004c9e000440560005f09b0003b07e0003407600046c9b000224740004787a0000c476000214010004883d0003d03b00038c73000134740000549b0003607100041456000064c40002a43e0006643d0002405100064ca1000350ce00060c3e00053c520004805a0003dc3000017c9e00040c2e0004b8a6000421010002ec51000350d2000420c9000038560003dc280000887100032876000018b00000d0730005408c
 | 9=>0x284a00003c5800003c6c0000340300002c010000384c0000440200003c3400002c3e00003c0e000018400000286c00000432000010010000380c000008cc000044710000187800004444000034400000344c00003c5400002434000020010000049e000014e4000010b4000030a000003c3200000c3e0000340c0000306c00002002000024280000285200003cbc000048fc00001040000010a8000010d400001cd400003840000028700000343c0000388c000038240000084c000044b0000004a40000289e0000443c0000382c000018e4000044fc000010e40000309c00002c5800002405000044c000003ce400002840000044cc000010530000348c000008d4000038ac000004b0000004dc000010a4000000b4000014ce00000468000010520000303d0000304a000030bc0000103c0000083e00001801000044540000305200004090000008e400003062000000d400000430000004d4000034ac000000380000387400001073000008d200003037000004ac000030e4000000e400003c4400003834000000d2000000a400000c78000004640000143e000044a0000048a400002862000014020000445300001c3e00000454000010020000240200003c420000489a0000203a000000370000389c000024030000186c0000146c000004ec000000a200001039000018ca000030440000106c0000087600003cb0000044ac00001c0100000874000004a600003cfc00003cc00000309e00002401000038c40000187200003c5600004458000044a8000048d4000044d4000038900000449b000044600000342c00004856000024240000086c000030420000348000000444000004a00000143c000034c4000044dc0000088c00003490000030b0000014ec0000045c000044390000404800003c5200002856000044a4000030fc0000006c000018900000309a00000438000030c00000449a00000c3c00003c2c0000105400000801000030cc00000cec00001802000014cc00000456000018520000445c000008640000400d00003c30000004b4000044cb0000042a0000349c0000043a000008900000342400000460000000010000146200003c0d0000084000001cd200002052000044ec000024ac00000c020000380b00001c400000289a00003cac0000342800003ca0000004a200000c62000020ec000028ca00003c9c00001c0200003ca80000447300003cd40000049a00000c7600003c600000003c0000340b00003880000038a40000003e000028010000440100003848000048540000444c0000347c0000347800000cd00000103b00003cdc00004464000030ac0000242c000034740000480200003828000004d2000048ca00003ca600003cd20000084a00002c0200002c5600003ca40000189400003c5e0000149400003c060000140100002c400000380d0000387c00002858000028b8000030a8000030d400003060000030020000087800001478000028fc00001c3c000034a4000004ca0000000000003c5c0000489e000044b40000303a000040380000340d0000384400003ca2000030dc00003c3a000034040000089400002480000044680000046c0000443a000030a40000383c00004840000004340000040e00003cec000044ca00003c5a000038b4000030ca0000305800001cec0000305c00003c0a0000083c0000445200000802000034b4000018ec00003c4c000010ec00003cca000028020000045800000442000008ca000030ec000004bc00003c2a0000387800003c640000042c0000340800000c010000045a00003c3800003c2e00000436000028b400003434000008ec000004e40000449e00004451000034440000304c0000000200000c4000003cb4000028d4000020400000286000003c3600003884000000ec00000cce000030640000446c000038050000247c00003c680000049c00003c9e0000045e0000303800003407000028e400003c9a0000445600002478000014d00000249c0000348400004499000024400000340500003001000028a40000443b0000044c0000004000004801000034480000144a000030b400001850000014e800004034000010b80000449c00003036000008620000042e000024a400003068000010510000285c0000303f0000247400001476000024040000103a0000305400003056000004a80000183a0000283e000028ec0000243c000008dc0000144000003c0500001071000004fc000044c90000483e000044e40000408c000004c000000452000000b8
 | 10=>0x34000000280000000500000002000000030000000100000024000000ac0000002c00000000000000800000007c000000780000009c00000040000000a400000074000000040000003c
 | 11=>0x0
 | _=>0
def ga:Fin 7->Nat|0=>0|1=>0|2=>3|3=>0|4=>1|5=>0|6=>3
def yw:=[ia,fz,ib]
abbrev bf20:=bar fw (k9 fw.shTT sq yw (a8 fh 11 cq py) sp zk zp) (a8 fw.all1v 11 vx py)
lemma b20_sm:([6,7,10,11]).all (fun s=>span (bf20 s) (sp s) 0)=true:=by decide +kernel
abbrev S:=span
lemma sp0 {P:Nat->Q} {b:Nat} (h:S P b 0=true):∀ i < b,P i=true:=fun i hi=>span_sound P b 0 h i (nZL _) (by omega)
lemma spB {P:Nat->Q} {a b:Nat} (h1:∀ i < a,P i=true) (h2:S P b a=true):∀ i < a+b,P i=true:=fun i hi=>by by_cases h:i < a;exact h1 i h;exact span_sound P b a h2 i (by omega) (by omega)
abbrev B8:=bf20 8
lemma b8_0:S B8 56 0=true:=by decide +kernel
lemma b8_1:S B8 56 56=true:=by decide +kernel
lemma b8_2:S B8 56 112=true:=by decide +kernel
lemma b8_3:S B8 56 168=true:=by decide +kernel
lemma b8_4:S B8 56 224=true:=by decide +kernel
lemma b8_5:S B8 56 280=true:=by decide +kernel
lemma b8_6:S B8 56 336=true:=by decide +kernel
lemma b8_7:S B8 56 392=true:=by decide +kernel
lemma b8_8:S B8 56 448=true:=by decide +kernel
lemma b8_9:S B8 53 504=true:=by decide +kernel
abbrev B9:=bf20 9
lemma b9_0:S B9 20 0=true:=by decide +kernel
lemma b9_1:S B9 20 20=true:=by decide +kernel
lemma b9_2:S B9 20 40=true:=by decide +kernel
lemma b9_3:S B9 20 60=true:=by decide +kernel
lemma b9_4:S B9 20 80=true:=by decide +kernel
lemma b9_5:S B9 20 100=true:=by decide +kernel
lemma b9_6:S B9 20 120=true:=by decide +kernel
lemma b9_7:S B9 20 140=true:=by decide +kernel
lemma b9_8:S B9 20 160=true:=by decide +kernel
lemma b9_9:S B9 20 180=true:=by decide +kernel
lemma b9_10:S B9 20 200=true:=by decide +kernel
lemma b9_11:S B9 20 220=true:=by decide +kernel
lemma b9_12:S B9 20 240=true:=by decide +kernel
lemma b9_13:S B9 20 260=true:=by decide +kernel
lemma b9_14:S B9 20 280=true:=by decide +kernel
lemma b9_15:S B9 20 300=true:=by decide +kernel
lemma b9_16:S B9 20 320=true:=by decide +kernel
lemma b9_17:S B9 20 340=true:=by decide +kernel
lemma b9_18:S B9 20 360=true:=by decide +kernel
lemma b9_19:S B9 20 380=true:=by decide +kernel
lemma b9_20:S B9 10 400=true:=by decide +kernel
lemma lb20:∀ t,HCS 7 bt t->12<=t:=ec bt r20 sq fw ga vx cq yw [(2,6),(1,5),(0,3)] sp zk zp py rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp [sp] at hi | 1,_=>fun i hi=>by simp [sp] at hi | 2,_=>fun i hi=>by simp [sp] at hi | 3,_=>fun i hi=>by simp [sp] at hi | 4,_=>fun i hi=>by simp [sp] at hi | 5,_=>fun i hi=>by simp [sp] at hi | 6,_=>fun i hi=>span_sound (bf20 6) (sp 6) 0 (lAL.1 b20_sm 6 (by decide)) i (nZL _) (by omega) | 7,_=>fun i hi=>span_sound (bf20 7) (sp 7) 0 (lAL.1 b20_sm 7 (by decide)) i (nZL _) (by omega) | 8,_=>fun i hi=>(spB (spB (spB (spB (spB (spB (spB (spB (spB (sp0 b8_0) b8_1) b8_2) b8_3) b8_4) b8_5) b8_6) b8_7) b8_8) b8_9) i (by dsimp [sp] at hi;omega) | 9,_=>fun i hi=>(spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (sp0 b9_0) b9_1) b9_2) b9_3) b9_4) b9_5) b9_6) b9_7) b9_8) b9_9) b9_10) b9_11) b9_12) b9_13) b9_14) b9_15) b9_16) b9_17) b9_18) b9_19) b9_20) i (by dsimp [sp] at hi;omega) | 10,_=>fun i hi=>span_sound (bf20 10) (sp 10) 0 (lAL.1 b20_sm 10 (by decide)) i (nZL _) (by omega) | 11,_=>fun i hi=>span_sound (bf20 11) (sp 11) 0 (lAL.1 b20_sm 11 (by decide)) i (nZL _) (by omega) | _+12,hs=>by omega) (f8 bw yd bt E20 ga [.emp,.emp,.base 3 [3,5,0,0,4,1,2],.emp,.base 0 [0,1,2,3,0,4,5],.emp,.base 3 [0,1,2,3,4,5]] (by decide +kernel) (by decide))
def db:Nat:=0xf39cc0605cedc835
def sn : Nat := 0x81000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000004080000000000000000000000000000000000000000000000000000000000000000000000020400000000000000000000000000000000000000000000000010400000181020408102040102000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000802000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000040100000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000810040044081020408102002004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010200000000000000000000000000000000000000000000000000000000000000000000000080040000000000000000000000000000000002000000000000000000000000000000000000000003f80000000000000408000810000000000000000000000000000000000000000000000102000000000000000000000000000000080080000002000080000000000000000000000000000007f00000000000020404000800000000000000000002000000000000000000000000000000000fe00000000001020204000000000000000000200000200000000000000000000000000000000000000000008100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000081000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000100042000002204081020408100004040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000408000000000000000000000000000000000000000000000000000000000000000000000002001000000000000000000000000000000002000000080000008000000000000000000000000000000001fc0000002000080020400000000000000000000000000000000000000000000004080000000000000000000000000000020000000220800000200000000000000000000000000000000003f800001000041000200000080000080000000000000000000000000000000000000000000007f0000800020810000000000000000000800001000000000000000000000000000000000000000004000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010200000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000220000000000000000000000000000000000000000000000000fe0020400000810000000000000000000000000000000000000000000000002000000000000000000000000000001000080840000001000000000000000000000000000000000000000001fc1020004000800000000000040000001000081020408102040000020000100000000000000000000000000000000000000004100000080000000000000000000000000000000000000000081000000040000000000000000000000000000000000000000000000000000000000000000000000000004040104104004000040100102040810204080000000810000000000000000000000000000021000810810020001000400408102040810200000004000800000000000000000000000000880000000000000080000000000000000000000000000000000000000000000000000040201080042042081000082080020408102040810000000008040000000000000000000000000204004000000000004000000000000000000000000000000000000000000000000000200011020001041001000020040000000000000000000000000000000000000000000000081020000000000000000000000000000000000000000000000000000000000000000000000000000
def mz:Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def os (m:Nat):Nat:=land (shiftRight sn (Nat.mul 296 m)) mz
def dw:Nat:=0xffffffe8ffe8eae8
def Nf7:Nat->Nat
 | 4=>10
 | 5=>204
 | 6=>490
 | 7=>686
 | 8=>298
 | 9=>10
 | _=>0
def qj:Nat->Nat
 | 4=>5
 | 5=>9
 | 6=>10
 | 7=>11
 | 8=>10
 | 9=>5
 | _=>0
def qt:Nat->Nat
 | 4=>0xf435e0ceb882bfc3e274e6bf73f1e36add435ef8dd3211f22fbe741e50e7
 | 5 => 0xff02a3fec4e5febf9cfe0b5efd1636f958adf88577f8783ff3a3e5f2fd2af09853eff735eda305ec636debcbb7e95e99e6cca8e6710ce5c828e449b4e37089dfe12cde63a7ddb392dd00d1dbbd62db84f0d91ba0d7a547d74f3ed56bcad4f395d477cdd3938ad2dce4d06eb8ce6477cbced7c9e629c9c41cc905adc86194c6e5b0c69949c5e7d4c54f0ec51777c2ebe3c0c879bddbb2bb492eb984e2b8e72eb884e1b86930b760e4b6cb6db00a77ae88a2ab193da84dc7a5964ea39bc0a1bb93a106439ff4809fabf598c5e7980f7b96d11296955a93cf3d9365a192e43691e4bb9171778d36ec8ccdbe8cc5288cbc568ba8db8a7ff386e72986687c7ee2a47d532c7d223c7c55617b146e7a359879d500799f57796401760e7374f0cd74ce0d73e6ad7391427372986f145b6ba51a6b04e26656da63a6c3621d555fe6035dae915ccd6359a8fe5930c4586540583c40576ef15622df5407ea51c863514455511c6550b3c24f5f634e5be04e47424dfcbf4d2a514c8b474b80564b6d774aaa59490fb248812247968f47268c4700bd46253a44a8904326d74299ff41db2940acef4028de4009cc3fa5f03f8a9c3d58d83c89d83c24523a81733a4a663a173038aed2389e953882fc38692d37bb5635066a34ee15339bea334da932d67e32ba7130878c2e14432df9ef2de0da2db180285eb226a3fb269667253dc6250c2722162e22026221a997215fce2078e91c92651c45ef1be99519cc481993c2193a3617768d16770815f864159209150d401444391300b812c483121cae1118fd10d4070fae2d0e0ceb0ca4680c47bb0bb12f0b5e0e0b53d50b18c50a9fa6070305037a00026e44
 | 6 => 0xffcf85ff8c1bfe70f8fd1979fcf058fcc022fc0960fbf4d4fbaccffab708fa9928fa82e4fa5060fa472cf8aec7f7e4d9f7598df69531f679e2f521a1f4f5fcf4905bf3b3c5f37a80f31e3ff29eb0f25076f1e9c8f076faef2570edb07fed5fdfec8963ec1c55eb8ba2eb30f9eb1f80ea8398ea4dcaea0b30e99fc1e9652fe8d466e7b7c7e644eae5c2cfe41cfae3b801e2e6ffe16fe4e0982fe07339e01e0cdf9ae1dec693de58b1ddfa93dd57efdd5129dca8d9dc666fdc31bedb7155db34ded97ec5d8e6f0d8c56dd8c40fd8ab80d89152d7246ad609afd5e36ed59a91d58ac6d4c835d2c62dd27e98d2590bd20b76d18aecd11026cf6d4bcec0bbce6837cd6736cd34afcd0cb5ccef11cc7620cba8e3c8d830c818d4c7f0fcc7bf00c772abc709adc6de08c6d127c6b39ac69d51c697efc54835c5339dc463f3c291c6c282e4c1420cc0f71ec02ce7be9c35be1bf8bda446bda26abcaf75bc4012bbee12bbbc41b97ec7b924d0b7aa80b72cb7b5dc91b5a54db5a00db4f627b4709eb447bdb41585b406eab3c6dbb312afb2684db1d474b0eac8b0b501b0801badfd26adf1eead1d41aba898ab331daacea0a87b34a87648a7ed8ba7bc67a6ec5aa5d581a4c545a44dfda396c6a357c2a2a63ba25be0a23e10a23a05a06fbe9fed089e1b5a9dfc389d9b6c9cf08a9c85809acac49a7131997755990d9b97d5a497d3d097869696ff7b959193957adf95599f937a069275d791428e90bcc98fc6a98f66a88f41d78f19c88eaf0d8e8e078d7b348d39b78d34778d07f18cf2698bc2858ba7ea8b66458b0cdc8aa71389927e89607088395a87c94e87ae5187329f872938870ec286df33866aaa864075860c5b85b264854cdc84352c8433f4841fa183f15f82e8118235c4814bcc8044377ff7c17f50697e68247e65e67e193f7d9d137d81bf7ccc9b7cb3ff7c53257b548b7ab8c27a34547a010678aea2785d16783d9377f60b77c4847781b276fecf7660507646e0762d2c75a95c74e5e773539d7336b071c87f71968370b5f770b194708594706048703f386ee9746e1c1a6dc8756c063d6bd96e6b728a6b19506ab0426a99a06a019c6a01696984716902f168b15a6895d46848c967c20b67b7d767a22867997a6762d4669cad66662665f65b64b9d564b109641669640440629b726263436106696034b45fcf995fa4495f9a3f5f56f15eb8d85e492b5dd1e15b7ac45b696d5aee215a89885a64c35a51965a3d1259fcc659f94959f6a959114458d8be58aca857c36b57b4de579a7057895057675c570d31552bc954eb0254b0f7549db0548939540d34530e38526ca150ee0350de464f4e6c4f3d544ed6314dc61c4d28b74c446b4bef904aa5824a5ed84a4c764979fa493e19487c1a48738748484e46a3ee46475d45c3724580824564c345633944cf2044c3974472e1446b7d42c6f9426c9a4149764140b14053503fddf13fdc543f5d1f3f36c23e62d93e41da3df29c3d879f3d48013d1c833cdb9e3cc1ca3c8d7f3b6d2a3ae5af3aa11e3962ad393a3c3849b838001e37eff43712e63647543515a3350a0e34fc9c34d67134bf67344c7734208a33e8e0335f7d33457733409e3284a9325c2732164931a014312e4531209030dfac309c2d3056242df6172d3c952baa912b9d152af5562ab09a2a808629ecc629db6729c2da278f1a2755bc2713d52701bd26fa5226ee1d26d2c92632f525819d25750524a91323b6b9239877239876238e6d2377132322f922f74b21bf4421b84b20c93e20c14320421e1f340f1ee0cb1ebca41e64301deb401da68e1c99001c968d1af7f41aa7f71aa1571a57e519bee119a57f197c1319105918724117ac43170f02164a3c13844a1377c513318213037712f8fc12b78012905612032510ef180f7d660ee3c10e99b00e7c580e51440d475b0d40ca0d24060c67b50c3beb0b6ff10a6cbc0a52c5099e3d08938c08284f06e1e106d8200672cc060ca90608b505924d054789043f54041b2303fdfa03525302f342023998018f2001837f0125c500dc9f00ce2c006b92
 | 7 => 0xffa88bff782bfd9df5fd8d3afbf718fbef96f9738df8b395f83faef7f94cf7f139f7734cf75f8df7221af70aaff6c901f67a21f5fac5f5565bf499cbf31ca7f11502f0d009f01700efe32befcb97efc85eef7d29ef4701ef3cb4eed979ee5424ed99b8ed18ffed1242ecd942ec4082ebfb76ebeeb6ebcc6beba26ceb9dc6eb7b20eb7907eac99cea44b4e9c892e99623e932dbe8d68ae8b670e8add6e87d25e78a66e6ab6ee6a720e6503fe64f32e6456ee644eae61a00e5cacfe56b3ae49224e323d4e3023be2ec7ee1cb11e18492e14ee5e134d7e128c5e04a3ee03d67e004f7dfc03bdf5942df387bdf06cbdec951dcf833dcc679dafc24dacf4ddab0bbda6bb7d9c59ed9a5b3d97c38d9761ad8bf31d6db99d6d385d6bd29d64842d5d8f3d4c835d47ed0d43766d3fac7d356cfd31e7fd30ecfd302b6d3005cd2fd92d2e058d20f4ed20b66d1fac6d17aa9d14a9ed04776cfbfc4cfae50cf7014cf4f02cf38face2ca6cdc382cd3e85cd1ba7cc8735cc75e4cc61eacc35d2cc2829cbf21ac93e82c92299c90779c903ffc8bae2c85cb7c7c5adc7969cc7475cc73afec72351c6eb5ec6b6eac69324c657ddc64615c619e2c601a1c5650ac52826c4e92bc4cec5c472aec37ffac33b9fc2ecdac2c868c2b3cac2812dc280b7c1ba52c1a1ecc19a85c02ce7bfe4e4bed76cbec271be3b5abdeee4bdc727bd0d37bc8587bc4452bbbaf0bb24ecb8cc0bb8ad56b850edb82cdcb7b60fb7394fb71d6db6d439b5c168b5ab10b58231b5084db491d1b49018b4567fb42353b3f832b3e281b32bedb27ba0b1f567b1b4deb10757b0eb86b0e6abb0da89af0826aee965aec095ad790aac8bc0ac601bac33beaba6bbab529caa93f0aa8e76a9f92fa89fa5a88834a8602ca824b3a7c84aa7c630a78866a77a9fa76038a758d6a7475aa6d88fa6c92da6b0e8a6725fa5e397a5d6b0a5c2aaa5c275a578c0a57389a45d49a3d4c2a38f1ba35ee6a23cc3a0739ca013d0a0060ca0011f9f48259f005f9ee9e19ee04c9e97819df2419b22209b15e89adb289ac90d9aa7979a5da59a4aed99925099030d98bbe098b7a79880ac982e2197e52797086796c091969d6f969c3e95ff9495d1cb95aad19591939551e6950b8f95045494fb6b94ac1594a3ef944e0793e040937a06932bf992fbaf92b2119257b2921a0891ccf09187ea917a809110b491003190ea338fdc548f09278e9b3d8e626c8e4ae48e0d8d8df52e8d42518cf27a8cb88b8ca30b8c11838b878c8b70578b44268b3ecb8b3a068ac6758ab7cc8ab38f8a9fef8a67728a50488a232e89285b88e0f988825e88396b87fa1487f44187f39387310386eea2866aaa86616a86319c86206585361f8520ba849b1183f461835be6834aea833e8e81a81d8129eb80cea38097fb8062db80485f7ff7b67fca1f7f2b357e59c97e48197e21f27e07087dd5147d80d67d2de57d05b37cb4a27be6917b62327b43a57a007d795c84783c3677d26677c4ea775170774d337684ad7660507640db76303f760cf575f77f75eb5e75dfd675b4f7744e0273f852732992730c4f72da2771faad715bda70d0e87047346ffaa86f57756ec3b56e1e8e6dd9136dcb366d500f6d06ab6ce9186cb3166c233f6b7aec6a82316a58db69441f68910c6872186859066856e2675ec066d5ab66cfcc66bbb966abfe65ac3d6540f2650bbc650af864a15f645d93641d6462f4c962b119626612622ab4621d59618f9a61630e6157a8611a085ff6be5e0f515dd8b95d37935d05505cb3c75b73405b0f105b01dd5aee6a5a89885a551a5a2e9b5a2bb45a1dbe5a17ad59c75759a412599ad5597a6558f3b85857d5584077581ac958087157c36b572bfa56e56a56b09856a63f56035e55e73855686c54bb6154b861548665543de5543a7a5430af54260f54098453f77a53eb0353a38e5378cd531a50524d0452347e5128a55067295065f05027f75006b14f87944f769e4ec72e4ebba14e1ac44de9574dbd024d4a154d07d84bc9624b62154ab4ed4aa58d4a84684a61ac4a5ed849f0b349aea749ac1a489160487bae487b00482a5148034247e00947c36847a5644756e146e61045ea1845d68445c7a445c4c744aec844a7e244516c44190943cfde438dcf433eac42dc374260724207d241ac654194e24149764100783f67a93eeeb13ec54f3eb3983e93573e8d5e3e66253e57af3dec373dc28a3d8a843d64563d5e743d2d3f3d0f873d05be3c81993c46083c0cc33bd4ec3bb1af3b8ca63b2b923ae77b3a27c339d85439998b3995403956b7394e1d394dcb38fc69389051387a0738423038362e37de5937c5cd3665d0353cbe34b5b834969c3417b233e7bb337f1e331f1d32709b3217ca320aad31c05831485331156230f4ae30e42830e1312f2a212eac8d2e9a942e6dbf2e3def2e1e812e03bd2dd6802db2f32da0582d199a2ba2ce2b68422b57022ae6d62a861f2a80862a2c8d29a51a28d79e287ae628630128599326b8d526aeb4264a3f2432812424992404a623630622943e224e0721b7c220142e1fd3c11f59861f2bfa1efb9d1ddb361dac481d827a1c9ae01bf47f1ae8901ae1171a98d81a59e81a58841a487a1a16fc1a01b7183a1b17587b173a231727d816f60716bb3215447b14b618149c9a149702141a3c13a8c913859613318212ec28121826120d21119a11116a05114201109e6c10502e0f34c40f14ca0dffc30d765e0c9d7c0c95e80bcfe50b07e80ae20d0a9ba20a6d430a2efc098753096928091a8a091a8908f06a0867e7086041081bf006be6f0679630608160500d004f91904f34e04d52b044d5303fdfa03c6340270c1026f7e026d8e02663500d7c200b80c006b3e005f97003d5a
 | 8 => 0xffddcafe01a2fd3b6efcf67cfcb4dffc7d08fa41a7f9c9acf923bff8b395f85a3ff7ffd9f7734cf4c8c0f31ca7f2081ff0fc93f07b2ef01141efcb97ee10b2ec4962eba613eb6e3ce932dbe8d68ae766bae756e5e72402e6df12e6c849e640d4e44f26e14b8de0cdc1e0ba2ae0504de0258cdee809ddca7fddc48adcf28ddc2c5cdb1252daf60adab0bcd9f85dd976f8d6db64d6781dd62544d5cb2bd5452cd4328acfc413cea7dfcd5914cc61eaca819eca49c7ca2345c9e73ec90779c8f3abc80e66c52826c2927ac055fbbfbc8bbf210ebe3b5abdd6b4bdc97fbd9913bd91a8ba29d1b850edb7f68db5084db4a423b491d1b422b9b41b6cb3e281b249d5b1f3abb1ef75b1d550b19b29b0ccf0adafffad3bd0ad03caacdb93ac1e93ab8e33a6da9fa67719a42899a39eb4a34535a05d6e9f8ccd9f66749f3cc99e74d99dc7689c749e9c42239c40469c06ac9ad9909a601c99fc3d97eb3f97acc095ff949504549456dc93feeb92fbaf914b8f8feb338f60508e40838b3a068962fe89593889515088cdfb88396b87d6b88539f985243e83c600838e29835be6833e8e82f01f8152c88056c77f16a77edece7ed8c87e7d8a7e320e7b90a07b8ed47ad5a179781378f56678cca97893d0785432775a9b7640db762a4d757e5674747073c2df732f2b724d1a72329f72159e701c3a6f637b6f264a6dda856d16206bb46d69da35690f42682cdb680c336796b266d5ab66abfe651b816402e9628c2661cbaa618f9a6037be5bb9c85b74bc5a772b5a3a6c58f3b8578710572fbd56e5ac56a63f55d8c955589755138b54855c545e0153a59e53197f52981a5270bd522e2d51b1625128a55109cb4f7e3d4e664e4e0d844d94104ae0b44a779e4963a6494d9b493d71492ba0491d0c48e53545510f453bb24535c445144944b90b447086445a2d43f70c42d7163e811f3e49483cf3093c85443c0bd83aaff1396aac387a07386e20386ded38423037882f373eed36bf8a3618bb3498ad31efee303aea2e8f842bc7c42b57022b486e2b109728072b25b9cc254992232be222e92a21713d1f2bfa1e78301e39db1c144a1b94181b60cf1b4f0c1b100c1a16fc19f84919a8471973b41971e817454c16bb3212e9dc12b02110a2c610741f10502e0f58bc0f588d0f20b60eedbc0ea8b00c79750b77330a6d070989990924d2090ea508ab5e086a92064585049cd50454b104347d02b231027a5a026f7e026db2021fc70159b5
 | 9=>0xd62544cfc413c52826bf210eb1ef7595ff948959384470863842300a6d07
 | _=>0
def bv : Nat := 0xddddddddddddddddfcfcccccfcfccccc0f0f0f0f0f0f0f0ff0f00000f0f00000afafafafafafafafaaaaaaaafffffffff0f0f0f0000000000f0f0f0fffffffffffff0000ffffffff0055005500550055fcccfcccfcccfccccccccc00cccccc00aaffaaffaaffaaffcccccccccccc0000ffff00ffffff00ff0000ffff0000fffff000f000f000f0000fff0fff0fff0fff5555555555555555ccccccccffffffff00000000aa00aa008888888888880000000000000000aaaa0fff0fffffffffffc0c0c0c0ffffffff0000000000aa00aaeeccaa00eeccaa0000c000c000c000c0cccccccc0000000000000000ccccccccaaaaa8a8aaaaa8a8dfdfdfdfdfdfdfdf8f8f8f8f8f8f8f8feca0eca0eca0eca0fcf0fcf0fcf0fcf0f5f5f5f5f5f5f5f5aaaaaa00aaaaaa00ccccc000ccccc000c8c88888c8c88888ffccf0c0ffccf0c0ffffccffffffccffddffddffddffddffeeeaeeeaeeeaeeeafffffffff8f8f8f8eeeecccceeeecccc0f0fffffffffffffeeaaeeaaeeaaeeaa0000000000cc00cca8a80000a8a80000cccc0000c0c00000aa008800aa008800000000000a0a0a0affffffff55555555feeefeeefeeefeee000000005f5f5f5fffaacc88ffaacc8800ff00ff55ff55fffefeeeeefefeeeeeffff0000aaaa0000eeeeeeeeffffffffcfcfcfcfcfcfcfcfaaaa8888aaaa0000ffaaff00ff00ff00aa00aa00aaaaaaaa00000000ffffaaaa888088808880888000000000000000ff0000000055ff55ffcceecceecceecceeffccff00ff00ff00cccc000000000000aaaa0000aa00000000000000000f000fffc0ff00ffc0ff00c0ccc0ccc0ccc0cc88ff88ff88ff88fffffffffffcfcfcfcaaffaaffffffffffaaaaaaaa0000000000ff0000ffff0000cccc8888cccc0000aa00aa00ffffffffccc0cc00ccc0cc0000aa00aaaaaaaaaaeaeac0c0eaeac0c000000000c0c0c0c0eeeee0e0eeeee0e0ffffffff0000aaaaaaaaaaaaaaaa0000000000000f0f0f0fffff00ff00ff00ffffeaffeaffeaffeaaaaa00008888000000cc00ccccccccccffff0000ffffaaaa88000000880000000055005555555555fcfcf0f0fcfcf0f0cccc8080cccc8080ccccc0c0cccc0000ffffffffffcccccccccc8800cccc880055ff55ff55ff55fffcfcfcfcffffffffffffffeeffffffeeff00ff0000000000ffffffffaa000000c0c0c000c0c0c0000000000000005555c080c080c080c080ccc00000ccc0000088888888aaaaaaaaffffffff0f0f0f0fffffffffc0c00000c0c00000c0c00000ff0fff0fff0fff0faaaa8800aaaa8800eeffeeffeeffeeffa8a88888a8a88888ececa0a0ececa0a0fffff0c0fffff0c0fffafffafffafffaccffccffccffccff00ff00ff00ffffff00000000ff000000ffffececffffecec8888000000000000c8c80000c8c8000000000000ff00ff00c0c0000000000000eeeeececeeeeecec88888888ffffffffff55ff55ff55ff55fff00000fff00000ff00ff00ffffffffccffccffffffffff00ff000000ff0000cfffcfffcfffcfff8888808088888080a800a800a800a8000000000000ffffffcc00cc00cc00cc00aaaaaa00aaaa00000000000055555555f8f0f8f0f8f0f8f0ffaaffaaaaaaaaaacc880000cc8800003fff3fff3fff3fffaa88aa00aa88aa00c0c0c0c0c0c00000cccccc00cccc0000efefefefefefefefeeeeaaaaeeeeaaaaffffffffffffeeeef1f1f1f1f1f1f1f1ffccff00ffccff00fcfc0000fcfc0000fefefefefefefefeeecceecceecceeccfff0fff0f0f0f0f0aaaa0000aaaaaaaa000000ffffffffff0000000000ff00ff00aa00aa00aa00aafafaf0f0f0f0f0f0aaaa00000000000000000000ffffff00ff88ff00ff88ff0055ff55ffffffffff8080000080800000800080008000800044cc44cc44cc44cc0000ffffffffffff0000000000550055fffffffcfffffffcff00f000ff00f0000088008800880088ff008800ff008800aa880000aa880000fffffffffafafafaffffffff88880000ff00cc00ff00cc008800880088008800ffaaff00ffaaff00a888a888a888a8888888880088888800ffffffffcc00cc00eee0eee0eee0eee0ccc8ccc8ccc8ccc8aaaa0000aaaa0000c0ffc0ffc0ffc0ffffffffffffccffcc8080808080808080f8f8f0f0f8f8f0f08888000088880000ffffffff0000ffffcc88cc00cc88cc00fffffffffffff0f0000000008888888800ff00ffffffffffcccc0000cccc0000c0c08080c0c08080c888c888c888c88800000000aaaaaaaaffffffff88008800000000000000ccccffffff00aaaaaa00ffccccccff888888faf8f8f8faf8f8f8ffffffffaa888888ffeeffeeffeeffeeaaa0aaa0aaa0aaa0fcfca8a8fcfca8a8ffeeaaaaffeeaaaaffffaa00aa00aa00f0a0f0a0f0a0f0a0ffffffffeeeeeeee00000000ffff0000ccc0ccc0ccc0ccc0ffccffccffccccccaa88aa88aa888888fffffafafffffafaccccc8c8ccccc8c8ffaa0000ffaa0000ff00ff00ff000000fff0f8f0fff0f8f0ffffffffcccc0000ffc80000ffc80000ffff0000ffaa0000ffff0000ff880000fca8fca8fca8fca800fc00fc00fc00fcffffffaaffffffaaffeeccccffeeccccffffffffffffccccffffffff00ff00ffc8c8c0c0c8c8c0c0ffecffecffecffecffffa8a8ffffa8a8ff000000ff00000000000000fffffffffffffffafffffffaffffff0088888800ffffffffaaaa0000ffffffffff880000ffffffffff008800ffccccccffc0c0c0ffff0000fff00000ffffffffffeeeeeeffc0ffc0ffc0ffc0eeeeeaeaeeeeeaea00ff000000000000fdfdfdfdfdfdfdfdff88ff88ff888888ff88f888ff88f888fffffcfcfffffcfcffff0000f0f00000fefcfefcfefcfefccc888888cc888888fff0aaa0fff0aaa0ffffaa00ffffaa00aaaaaa88aaaaaa88fcfcececfcfcececcc88cc88cc88cc88ffffffffa0a0a0a0ffffa0a0ffffa0a0fffffffffffffafafffffff0fffffff0ffffffffff888888ffffffffa8a8a8a8ccccc0c0ccccc0c0aaaa8888aaaa8888ffffffffffc8ffc8ffa0a0a0ffa0a0a0ffffcc00cc00cc00ffffccccffffcccc00cc00cc00cc00ccfaf8faf8faf8faf8ffffffc8ffffffc8fcecfcecfcecfcecffffaa88ffffaa88fffffffff0f0f0f0ffccccccffccccccaa888888aa888888ffffffffccccccccfffff0f0fffff0f0ffffc0c0ffffc0c0fffcfffcfffcfffcffaaffaaffaaffaa000000000000ffffccfcccfcccfcccfc00ff00ff00ff00ffff880000ff880000fffff0f0f8f8f0f0fff8fff8fff8fff8fffceeecfffceeecececececececececffffffffff88aa88ffa00000ffa00000ffcc0000ffcc0000ffffffffffc80000ffccffc0ffc0ffc0ffffff00aa00aa00cccc8888cccc8888eae0eae0eae0eae0ffffffffff00c800fff8faf8fff8faf8ffccaa88ffccaa88ffeeeeeeffeeeeeeccc8c0c0ccc8c0c0ffeaaaaaffeaaaaafff0fff0fff0f0f0ccc0ccc0ccc0c0c0faf0faf0faf0faf0eeeaeaeaeeeaeaeafff8f8f8fff8f8f8ffffffc0c0c0c0c0fffffcfcfffcfcfcfffffff0fff0fff0fffffff0f0f0f0f0ffe8ffe8ffe8ffe8e8e8e8e8e8e8e8e8ffff0000c8c80000fffcfefcfffcfefcffecececffecececfffffff0fff0f0f0ffff000088880000ccc0c0c0ccc0c0c0ffffffffaaaaaaaaffffaaaaffffaaaaffffeeeeffffeeeeccccc0c0ccc0c0c0fffff0f0f0f0f0f0ffa80000ffa80000ffaaffaaffaaaaaafffff0f0fff0f0f0ffffffffffa80000ffffffffaaa8aaa8ffe00000ffe00000ffffff00ffffaa00ffcceeccffcceeccffffff00c8c8c800eeeeeeeeeeeeeeeef0e0e0e0f0e0e0e0ffffffffff00ff00ffffffffffffaaaaffff8888ffff8888ffffffff88888888ffffff88ff88ff88fff0fff0fff0faf0ffccffccffcceeccffff0000ffc80000ffa8ffa8ffa8ffa8cccc8888cc888888ffffffffc0c0c0c0ffffffccffffffccffffffffaa00aa00fff0f0f0fff0f0f0ffffffffffe0ffe0ffffff88ffffff88ffffaaaaaaaaaaaaffffc8c8ffffc8c8ffffffffff88ff88c8c0c8c0c8c0c8c0ffffffffff00aa00fff0faf0fff0faf0ffffc0c0c0c0c0c0ffffff00ff88ff00f8f8f8f8f8f8f8f8aa88aa88aa88aa88ffeaeaeaffeaeaeaffffff00ffffff00ffc0c0c0ffc0c0c0ffffe0e0ffffe0e0ffffccccffccccccffffaaaaffaaaaaaaaaa8888aa888888ffccffccffccffccfffcfcfcfffcfcfcffffffccccccccccffffffffff000000fff8f0f0fff8f0f0ffffffffaaa0aaa0ffffff00ff000000aa00aa00aa00aa00ffffffe0ffffffe0ffffffffc8c8c8c8fff0fff0fff0fff0ffc8ffc8ffc8ffc8ff88ff88ff88ff88aaa8aaa8aaa8aaa8ffffffffffff8888ffffffffffffaa00ffa8a8a8ffa8a8a8ffff0000ff000000ffe0e0e0ffe0e0e0eac0eac0eac0eac0a8a8a8a8a8a8a8a8ffffffffffa00000ffa0ffa0ffa0ffa0fafafafafafafafaffffff0000000000ff888888ff888888ffffffffffaaaaaaffffffffffc8c8c8ffaaaaaaffaaaaaae0e0e0e0e0e0e0e08888888888888888ffffff00ffff0000ffff888888888888ffffffaaffffaaaaffffffffaa88aa88ffff000000000000ffffffffffff0000ffffffc8ffc8ffc8ffffffaaaaaaaaaaffffff00ff00ff00fcfcfcfcfcfcfcfcc0c0c0c0c0c0c0c0ffffe0e0e0e0e0e0ff00ff00ff00ff00ffffffffffffc8c8ffffff00ffc8ff00c8c8c8c8c8c8c8c8ffffffff00000000eaeaeaeaeaeaeaeaffffffaaffaaaaaaf0f0f0f0f0f0f0f0fffffff0fff0faf0ffffff00ff00aa00ffffffffffffe0e0ffff0000e0e00000ffe0ffe0ffe0ffe0ffffffffe0e0e0e0ffffffe0ffe0ffe0ffff0000ffff0000ccccccccccccccccaaaaaaaaaaaaaaaa
def au:Nat->Nat
 | 4=>49
 | 5=>58
 | 6=>67
 | 7=>76
 | 8=>76
 | 9=>67
 | _=>0
def qx:Nat->Nat
 | 4=>0xe190280400a180b8281c0050b054041409a81c2411008014200f0503800a0d01808180150002c100a00a00012080080100e060280400a040180802005
 | 5 => 0x6808643c2080186690010441c006068ac220a0700181a1501114020060c03404050600581a42100c0140160c0ac221409801800330123c620050683c040a070018da6936044021e600174c40a0080141a0224044be1e6000882a3e0500546656088281c0061c8087611370018720213004260060006804110f9114302b088281c006068091c11098018b4592d828020063b0e80411000798000d010441c2f5020d08011008018ba1d18028020061c808221f0007986c1105004001e61c808228d098019180208828020060014404110f87945c1918028020062d118044500801800151b02802005068084c8b0700181a02450443e4461c8ac22140980181a02280c026006000340411098bd41a0220898020060019004550500540033010981c005020d004050080191202188281c0060200832050080181a6615a20020060c0108011008018008715828020050e854145f0080184e0213004260061c8ac220a0700189242050050c006000340475070014000d010450a1e5068087030098019084c088281c0060680906300080182073088281c00606808ce3005005800180a9f00200536854d80a2f80581a56088281c0061c8082214070018b415011140200606855040a0080181a0215044001e60383404050080181a02280c0dc0060001004110f91141a02408441444606808703040001872020885026006068ac643c0980181a2b188281c006001882a0a0080143a1505004001e60685c040a0700183019181140200606808fe31050398482008828021e6000340455098bd4da15360280213606808fc3c3e80185c1c0882802006001743a7c0080141a0228044f61e606808f411370018000d010143e4453c808220a008018da1536028021e60003404050603943a150a02802006069e056110980181a77010f026006020d00411008018ec1601044021e6000340431070bd4000d011d4e80050c1cc220a070018000d010c03e44506808e4110980181a023884426006001c06c110080145c6f18028020061c8082214370018da15360501401624908d60a0080181a661f844d4006020080a6300801800492108014015069a40431070018000d01014181e5069987e11000f581a022a9a0260060e864600a008018326708828021e6000d8cc11008014ca022a82802006001900411098bd41a0228044be446069000a6300801800493102802005000348448308014c002088281c006069640445008018ba0401014020060b054040a0084d8ba1d08914020060c054145f0080181a02190f0401360c11814010007981a0210044bc1e6020480411008018305d2111402006000340426060394005c0a828020052496c220a0080180004200f022005171181401000798b45901028020060003404582b80141a56188281c006198ac220a07001872020884c002861c808aa0a0080181a151f028025462994804321e00182c1501028021e60693404321e04d8005101044262850685456450080181a0228044181e62781004050080181a4e100c0140161c80822450700181a4d010c4140e61c930220a070018660f010281c00625874600a0080183019190f026006000340411250bd4720213094020060c064620a070018004921120020050691c04321e00181a4601114020060003404110f91140e0420044020060680886110507981a4201014180160684804050080181a401504402006068088211000a18000420044001e506854400a008798720208828181e6068fc7c11050f587202190f0260061c8087611098018741601044141e61c808620a0700181a021c0c41c0060c05414010007981a021009802136000dc042612805400360500400355068d004050600580033010c862005000340430098bd40e040101402006170541401000798002d0a828020050680858110980181a2b0885026006068080a2a008018000d01044522850001004050007944e0213094020061208c220a00801800220a8801401510808220a0700181a02100443e1e60e870220a008018001b0a828020050d054040a00801808020301402006
 | 6 => 0x1a026a04402000f38342ac605004001e70003404261297c02c002eb9c040a0080187202280440213003800a602190f0260060696c60910500400e1806808224507001cb41c01044140100383404d2088281c0072d1a40411008003ce3901044280a00801d82021802802000f383456321e028020071ca88d8110500400e00568084c01098018b44e2d8441401003800ba6d211b0140160680832321e04c00e000680840300500581a02100448a010f3800da1501028020060680832310503800e5a48008220100079c720208828026e0038001a02190441c00606809cc110500400e002d054040a008018000d01154140117b03404da08828001e736834d8021802802e39010f12a0a00801c72022804402000f38340450089b8001e70003404113e03800c000210004110080181a6c010c92a0109b8001a020887c6a1e600000da153602802a0056808228d0980181a2b0882802001eb8343a110500400a672d0084011050043ce0d01104220a00079c000d01044280e0030001a0208914022f606b40220a008003ce0d2d880220a00879c1acd01044140e00392cda020882802007000582a020500400c0d0126c22e500269c300d010c878130038343a11050054e0070680936110500088e0006808a030008018000d0104568130030601a02188281c007069dc043c0500400e0d360092c1109801c1a150102802000f3968046f1802802007068093630050003ce0d01140227b00801c000d01044181f0f3035300219044022f77200936110500134e390138c220a00801cb44d0104414010f38347e2b08828001e706808e4110500400e00068091e110700181a021926c2213003801805b0882802006000e43a110500400c000680822140980181a02388441401003800301551028020061c808220a00a1800e5a01140220100079c000d0104426e20f303456110500400a670003404117084c00c5d2d008600a00801c1a027004414010f38001a025e050260060006804115000400c1019808220a07001c1a5b2804402000f38e4045008804dc00706809ac110503800e00069000405008018000d010444a0117b000a2020885026006000001a020a03124a0d21208220a00801c0039010c014010030e4041122804001e70003404381800400c000c37c220a008018000d01045bc0e0030e4b402088280200754808220a008003cec001044140100079c1a421184414010038b8ba0208828020070016804110f8003cc5d36808789505005c00180a8441401003034042308828020070003404964a84c00c000d008600a008018000d010c0145f223060de1105004001e7068084c8b1280400e000680860450700181a022a9a014010038e5ba0208828020070680902110500134e0d0126c401105269c0033010448a0e0030b8de1105004001e70014404110503800c00068541401003718725b0882802000f3800c80208828022f660808220a008003ce0019930220a0700181a42010c014010038001a0228098020062d118040a008003ce3321008220a07001c000d0104414db17b0e4041105005b6007000340411098019cc0019930220a0080181a026d04414006cb8001a02028300200606b6004320883800e0006808643c060018000d010c92a0e003170b402088280200700034041122b5c00c0d2d8c0460a00801c000d0ab581401003034cc2b088042600736854043c0500400e0d27008604500801c1aa2010c878130038001a0202894020060003404110a1b800c1d0c844140100079c720208828020014386422d505004001e706808a09b0880134e0d2db50220100079c00490104414010031b41a6c012f0140170c16804112280400e5a2d870220a00801c0051010441401143034561105004260070034c2a020500400c0d1f808220a00079cb44e010c01401003974340208828020071716804112280400e0019808620a07001800180a8280200493000ba1d0882802006069985611008003ce180c8c8780a00801c1a024d84414000f3800660218828020060690804110a03800e000c174840a008018965a010448a01003800a6021904402006000342a661580400c0d010c5a40a07001c1ad10882802000f38001a0219044181e60003404110700050c182d16c220a00801c000d010448aa700303404500883002007000602a0a008006ac0d15844140100079cda6c0c84414010f380008020887c001e60803404110503800e5a68044140100079c48020882802005338e4049b08828009a72eaa004110500400e1819808220a07001c000d010459e130030b8b45b0882802007000340413002499cc0006808643107001800000c0541401002834042018028021e7000340411500045ec5a66808220a00801c000d0a8ac1401003034047e0897c02007068090211050003ce0d0126c401105079c302b08828021300383404cc08828001e70003404321e29c00c2e06808600a00801cb4150102802000f38001a0208850181e61c80846110500400e0056ab022250080187202190f014010038e4043b088280200706808a09b0884c00e0d4f808220a07001c000d010984a8d003001500208850260060003404110980050c0006808aa0a0080180015120ac1401003060ba0208914020070016804110a04c00c0006808621407001800cb0c05414010030001a460102802006000602a950500400ca92d008220a00801c660239844140e00380194150102802006000340430050045ec0006808220a2f91180000068080a0c00a800a60208850260060003404112283800c0006809780a0600581a0240880220a0f38001a0208851920060c0ac220a008003ce0d01099160109801c000d0a808f8010030348402088281c0070003404110523488c3a0b008220a00801c000d010984a010030001a02640442600606808a030008003ce005431c220a0080181a022826c22000f3800301515828020060c064220a008014ce0006808643c070018300d01044280e003834b69b08828009a700034048f1883800c2408b18140100079c000d010143e000f300000020885018c5506b1004110503800e0d4c008641107001d86020882802000f3801841501028020060680914110503800e0060808600a0080181a42010c08a01003968042308828020076016c220a008003ce0d012fc220a00801c1a2b1e25414010038001a0219254180161c80902110500400e0028808224500801800040101422010030343a11050050c007001743a0a008006ac0006a5c04321e00181a5b118441401003800a69708828020060001004320880400c0d5f044140100079c009c4c808643c0030e456110500426007068f85611050043ce0006808220a0607980039211402201003000301536028020060690860910500400e0d33008220100079c000d0101402130030001a02089f0022f60003404321e04c00cbd1c808220a00801c000029808643c0028001a021d844260060694804110517c88e000680860a00080180053012f014010030e4043005004001e7068087030008003ce0006808220a5d8798000d010c4140e003060ba420517c020071c8093611050003ce761d008220a00801c000d01044f85f0f30e404110500400a670680840110517c3ce5a27008220a00801c000d0a99804010030340419181140200706808c211050003ce0d011f8220100079c1a690104402000f3800b85d210280200600060220a0080174c0d510092c1109801c1a023d04402000f38e4561105004001e706808a09b089b800e0d26008641107001c000d0104426351430001a15348080200606a400411008003ce0d0a8ac145f00801c000d0a8081401003000a6021925402006068091c110500400e0d0126c224500079cb4020c8c01401003800721515828020060c03404110503800e3901044140100269c000d01045721300303404b80882802007069084011050043ce3901044145f00801c000d0aa28140100303404b708828020070680890112f80400e0d5b0092c1109801c1a025a844140e0038001a020882818a160003404115a12800c0d01080220a00879c00ad010984a01003000000420044020051c808220a00acc00e6d0aa88040a00801c1a025904402130038e40411052340200706808a0112f8003ce1806808604500801c0049588441401003000a215010280200612008220a0080160e5a0126c220a00079c000d010443e0e003034a402190f0260072e96804112280400e0006808fc3c008018000d010455e130030003a1508828020062e034043c4a82802e0006808221425001872020882802ae003834b69b08828001e7002b558110084c00c0d011cc220a07001c00182105414010032ac1a02088281c0070003404264684c00c0d1f8ac220a000f5c0039010448a01003168561105004001e75480846110500400e0d01140600a00801c0033010c8220e003034042008828261e706aa804110503800e0054808220a008018000d010144a5f00b034322008828021e7000340411050045ec0d36008643c09801c000d011548a010030349a0208828021e70006804110517c88c0036854560a0080180033010c82201003174da5b0882802007069a4043c4a80400e2e2d008600a00801c1a02100c01401003800000401014020050003404114984c00c0d01140220100079c30190882802000f39743a1105004001e700034043b089b800c00198082214070018000d0109802130030e404110517c001e70003404321804c00c0006808643c06005800a801044260014300150022a828020062e8cc04110503800e182e908140100079c1a42010448a0e00392cb4021802802007000342a022800400c3901044140109801c00392d84414010030347c0208828021e717064220a008003ce000c054320a0080181a02240440213003800b44601028020060014404110517c3cc0036854d80a008018000d010c014a70030342a020500400a67528cc04110503800e0d01290220109801c720228044be010039b4d2021e044020070016804112283800c0d01228220a2f911c1a021c0c0140100383404500884c001e70003404110f8003cc000680860140980181a022808022010f380030a3088280200624a88d8110500400e0006808140c492858000d010451a130030001a02190f01813606854560a008003ce000680822a0070018000d01258220e0030001a0218828180e60003404551280400c0d4f808620a07001c72020882802000f38001a0208914181e6068087011008003ce0006808620a0600581a022404402000f38001a0208a7826006000693a110500400c9c06a60041107001c1a024d8c014004d38342a020517c020074c9b42a020500400e000680822850080181a02182448a0100383404501e044dc00700174841d0500400c001c854040a0080181a460102802000f38001a02189141c00600034048f1804c00c5d06908044500801c1a42010c878130038001a02180281c00629a6004320880400e002d008220a0607981a42010c4140e0038352e02190f0260070680860230500400e0d01104220a00801c000d0125822130030e404110504c001e70687404300500400e180c8f12a0a00801c003301044140e0030e4042008828021e706808ce11050043ce00000541401002514000d0124c26004930001a0208850189262d00860910500400e00000742a0a008014720218044140100383404321e22826007
 | 7 => 0x175840208828020070003404110500401a170003404110500401a0700034040a0980124a1736834049b088280200800034041105004019f7000348415010280200700168041105004001e700034041105004019e706a60043208804001e8000000411050073a00600034041105004011370026584020882802007000001a0208829ae00606809141105004001e80000004110503002c5600000724201028020060690804110500400b080001004110517c0200700034041105004019c70003404110500400ff7000340411050029f0a706ad8049508828020080003404110517e501e7003d8da02088280200700034041105005b6007000cc0411128281c0070003404110566c0200700034054c050040135700034041105004019a70003404113e0049400700034041105664019870003404e3050040092706808321105004001e8000340411678280200700034234c050040166700060b402088280200700168041105005da0070000004112280400c560003404110a04c00c5706808609105004001e806908d811050050c00800034040a0080124ce778034041105004001e80016804110504c001e70003404110500401977000340411056580200700034049608829b600706a60043c08828020080003404110500401917000340411a6028036272e834840205004001e806a88043c0882800448000001a02088040195600034041105650020070014c041105005da0070016804300882802007000342a020c828020070014404110500400ff7000001a02088501c006000340411c980426007000b8b40208828020070003404110a04c00927069b0049508828021e806a88043c0882800a6806808a09b088280200800034041112829ae007002a004110a0280200700034561105004016e700034041105004002871c80822c605004001e80014404113e004003574e1b54402088280200800034043005004004470016804110a02802007000340411c900426007000353002190f00200700090041105004019170003404110545c004470012cb4020882802007000340411a60280158706a8804320880426008002b5440208828020070003404110a04c0035700000b6110500400c5606908043c4a82802008000340411055ac0092700034041105007200070003484110500400dc7003ecda02088280200706808230005004001e8000340411050071e0072e9b5440208828020080c034041105004001e800034058e0882802007001741a028d02802007000001a02088502600600174a20208828020070003404c808828020070000162110500400c560003404110503800927001b5e4020882802007000371a02088280200700034041105630020070003404110562c020070003404050517c02007068096a1105004001e80003404110a0941c007000001a2b050040092600034041105004011470003404110536c001e700628b402088280200717034041105004001e800034041105624001e7000342a0205005da00700034041105004018870003404110561c021e70003404300500400f8700034053c1e028020070003404112280400f3700060ba42088280200700034041105004018670009004110500400c57000e544020882802007000340411050068600700264a2020882802007000340411228281c00700034d8021e25414017000e4da020882802007000001a020882ad600600060ba02088280200700034049b08828009a7000340411050380035700090041105004011472e264da020882802008000340495088502600706808323c4a828020080003404110500401857000340411050070800700034041105004018372d00822c605004001e80696c230405004001e80003432110500400dc70003404200882802c572eb74da02088280200800034041105004940070003456110500400f87000340411050040035700270da0219044020070000005240882802c560003404110500401827000002a020500400c5600034048208828020070014404110500400927000b4a2020882802007000001a02088281c006001b702020882802007000340411c00280200706aa8041105004001e80016804110500400f370696c22c605004001e800034042308828020070003404200882802927000001a023e004009260003404950882802ea70003404321e0280200700034043b08828020070003404bc050040035700271f602088280200700034b6110500400f3700000041105004017f600034057e0882802007000340432088054e0070003404110a029b6007000001a021811402006001440411050040035700034043c1802802007000340411050301c0072e83404110500400a6800034041105004017d72e034043c0882802008000340411be0280200706a6004300882802008000340495088281c0070003404110500400ee700034d602088280200706a8804960882802008000cc0411050041c007000340411050300200700168b602088280200700034049b08828020070003405160880400ee706808a0110517c02008000369a02088280200700034043212804009270680af61105004001e80c034043c4a82802008000340411055e802007000340411050046a287000340411055e4001e70006032110500400c57001b4b4020882802007000340411052ec0200700000b402180280200600168041122804001e70003404113e17c02007000001a020a04c00926000340411050040178700034057705004011070003404bc4a828020070003404115c82802007001741a1515828020070006032110500400927000340411050040176706ad8049608828020082d108041105004001e8000e404200882802007000340411050040175700034041105005ae007069ac049508828020080003404110500401747000340411050040173700000041105004017260003404112280400ff7068093695088280200800034051a4a82802007000340411055c40200700034057005006de00706809221105004001e8000e40411050040129700034041105004016e72ea64da020882802008000340481088280200700034041105004016d706b3404110517c02008001747202088280200706a60043c4a828020080694804321e0280200800034041192804001e700034056c0500686007000001a02055ac0092606a88043c08828001e80003404110a04c00f870003404260517c0200706908041105005b600800034041157828020074e035300208804001e800168b61105004001e7000e532020882802007000001a0205004016a600088720208828020070016804110500400ff70003404110500400447005a4da020882802007000001a0205038009260003404110a17c26007000340426052340200700034041105006d00070006032110500400947000e404110500400c57000001a69010040092600034043005004001e700271320219044020070003404110a0041c00706a60043208805b6008000001a0205004009260003404110545c001e7000342aa2010280200700034049b08828001e7069b004321e0280200800034041105006ceea70003404110500400a6700034041122804002870003404110503002c572d008321105004001e80003404321e044260070003404324a8940200700000305d210280200600034220a00801dd667000340411054ec02007001741a42158280200700270b402088280200700034041105006ca007000e404110500400927000340431088281c007000340432088042600700000041105004016460003422c605004012d700034041105006c600700009c6110500400c5700034041105005dd62700034041105584020070003404110524c02007000340411050300292700034043c088294e00700034043108828020070c17404110517c020080003404110500401607003a4041105004001e7000003a110500400c560696c0430088280200800174da02088280200700034d60205004009270003404110557c0200700034d2020880400f87000340411050054e00700002bc02088280200600060321105004015d70003404321802802007002a0041105004002870003404113e0042600700034043005005da0070003404110517d5c00700000a202050040092600174b40208828020074e264041105004015c800034041105004014f700170ba02088280200700034043c08850260070027132980104402007000e4041105004003570003404110517c1c007000001a151582802006001741a027f02802007000001b5b0102802006000001a02100280292600034055a08828020070003404110a0042600700034041105004009a700034041105004015970003404110517c0200700034041105001dd58700264da02088280200700002ae110500400c56000007202088280200606808de1105004001e800264b4020882802007000340411050040156706808a01105004001e8000001a020882803556000340411aa0042600700034041105006a60070003404300a028020070c168041105004001e80000004300500400c5600035b002088281c007000340411050056600700034041105006a40070003404110523402007005447202088280200700034041105006a0007000353002180280200700144041105004014f700264a60208828020070003404113e004001e706809361105004009a8000003402088280200617168041105004001e806808401105004001e80003404111280400287000340411a7028020070014404110517c02007000001a02089141c006000340411050055c00706d3404110517c020084c9b404950882802008000001a4d0102802926000e4049b088280200700034043c088281c0070003404114f028020070000056110500400c56000e4049508828020070003404320884c001e7000340411050041c00700034046108828020070014c0411050040092706b34041105004001e825968041105004001e800174054c0500400c570052c04110500400357000001a022800400926000003019050040092600034048f1802802007000340411050069400700034041105004014970690804321e0280200800034041105006900070003404110529c001e70016804110500400357000340411050068e00700034041105004014670003404110500400f57002728a0208828020070003404960882802007069b00432088042600800001500208828020060003404320084c00927000340411052b8260070014c0411050040035700271320208828020070003404110a04c001e7005100411050068600700000b402088280200600034050e05004001e700034040a49804009270680860c605004001e80003404110517c001e7000340432a102802007000001a0208829f200606808643c450280200800034041105004014170003404500880400f8700174da020500400927000340411129141c0070006032110500400f870003404110500426007000342a020500400c5700000a60208828020060000004113e00400c560003404300500400f3700000005d0e8280200506a5c04950882802008000340411055000200700034041105004013f70003404500897c02007000340411054f8020070c174041105004001e8000342a02050040092706cf4043c0882802008000001a02190f0260064c9b4d80208828020080003404bc05004260070680832321e0280200806809ac1105004001e80003404110a3b4260070034cda0208828020074e2640495088280200800034043048828020070016804950882802007000340411050040110700034053c088281c007000e4d8020882802007000340411054ec00a170000072020500400926000001a02188281c00600034049508829f200700404041105004001e70003404950882802447001741a42010280200700034041105004013a7000340411050040139700034d602088290c00700034041105038001e70014404110500426007000001a0205030029260003404321e094020070003404110a0294e007000001a0218828020060014c0495088280200700145621105004003570000864111280400c57002b404110517c02007000367002088280200700068041105004004470003404110503a6c00700034b602180280200706808461105004001e800034041105004001e706874041105004001e8000342a02050040035700034041112829f20070003404110500401377000340411050066c0070680822d505004001e800034840205004013570003404110500668007000340411054cc020070000004110a04c00c56002b40411052340200700034041105005ee00700000041105004013260003404959882802007000e404110500400f8700034043022804001e70680a601105004001e80003404324a80426007001741a029782802007000001a150102802006069b004610882802008000340411054b802007000001a022280400926000601a1105004012d70003404117a004001e70003404110517c00a174e1b4043c0882802008000340411053b41c0070003404110503002f87000340411054b00200700034041105004012b700034041105004012a70003404110500400b0706809361105004001e80000004110500401296000340411054a000a17000340411050040127765834041105004001e8001740411050040126700144041105004001e70690804110500400a680c03404321e02802008000340431128281c0070003404110504c001e7002b4043c08828020070c17404110a028020080003404119280400ff70003404115a028020070003405240882802ee700034042008828021e7000340411050064600706938041105004001e8000340411050040122700034043008828020072e9b4043c088280200800168043005004001e70003404321e029b6007000340411050040121700060ba4201028020074e264d802088280200800168d802088280200700000b4020500400926000340411050064000700271a6020882802007000342a024a828020070003404bc05005da0070003404112280400f87000340411050063e00700034041105478020070003404110a0281c0070000004110503800c5600034041105474021e78e03404110517c020080003404118d97c02007000340450088042600700000d2020880400c5636834d80208828021e8000353002088281c00706808649b08828020080003404328d028020070003404110a46426007000012e110500400c560003404300500400ff70003404118c050260070003404110a028020070000004110500400c5600000a602050040092600060a20208828020070003404110545c00ff70000005160880400c5600034041105005c41e700034041105004011570003404110517c6a1e7000000411050040114600175a6020882802007000345611050040113700034041170828020070690804110517c02008000340411050046b12706a600432088054e0080003404118880401107000342a02158280200700034041105004dc0070680832110500400a680016804110500400f870000004bc0500400c5600000041105004010f6003a404110500400ff700034050e0500400f3700034041105004010d700034041105004010c700034041105004010b7000340411050006b0a70003404110500401097001ac04110500400c5706b60043c088280200800034041105004010870014404110a0280200700068043c088280200700034043c4a828020070016804110517c02007000343a110500400c5700034045008804001e706a6004320897c02008000360e02088280200706808230605004001e8000340411050a4020070000004200882802c562d008de1105004001e8000340411228041c0070003404110504c00a1700034041105004010570003404110517d0c00706808230405004001e800034041105004010370690822c605004001e800409320208828020070003404964a82802007002b4041105004001e700035440208850260070040404110500400f3700034040a2f80124a170680822c605004001e80003530021925402007000349802088281c0077803404110517c020080003404e3088295c0070680823000500400a680003404113e00400ff72e968041105004001e82e83484020517c020080c03404110500400a6800034041112828be1e700000b402089140200600034980208828020070003404110500400f374e264043c0882802008000009a020882802c5600034043c7f028020070003404110500400fd70003404110500400fc700061f60208828020070003404e30882802007000340411053e80200700034041105005f20070003404110500400ce7000342a020500400f870003404110500400ba7000356c020885026007000001a0205005ee006000e4041105004001e700000321105004009467b174da0208828020080016804110500400f570000004500880400c560003404117a00400f370680822c60504c001e800061e4020882802007000340411050050c007001759402088280200700034041105005e2007000354402088281c0070003404da088280200778034043c08828020080016804110517c001e7000345611050040092700034043005004003570003404321e004260070000864110084c00c5700034045008804dc0070003404110500400ef706a8804321e02802008000343a110500400ee7001680411050042600700000b45b08828020060c03404110517c0200800034041122838001e706a6004320880426008000340431050041c0070006072020882802007000e4041105005da0074c835440208828001e8000001a02180280200600034041105005d800706a60043c088294e00800034041122804001e700034041105005d6007000006602088281c0060014c0411050042600700034041105005920070003404110500400ea7069b0043c4a82802008000340411052182600700174da420102802007003a40411050040035700000660208828020060003404110500400e8706908041105004001e8
 | 8 => 0x69ad44020882802008000356c02088280200706a880495088280200800008220a00e6400c570680822140517c0200800008220a2f80400c5706a6004110517c0200800008220a00ca000c5706808220a008006aff800168041105004001e72e83404110500400c5806808643c0882802008000340411050040113706808220a00ec000c580003404110500400ff700008220a0080366c5706808220a008018b98806808220a008018b3584c83404110500400c5800034041105005b6007000340411056240200706808220a008018adc80680878110a028020080000878110500400c5706a60043c08828020080003404110500401917069b00411050050c0080010804110500400c570680823180517c0200806808220a00bb42600806808220a0080124c580003404110500401ae706808220a00801f0f38000354402050040092700034041105004015c706eb404110500400c5806a8804110500400a6800034041105474020070003404110517c021e7000340411056d402007000340411050076000700008220a0080346c5706808220a008006ac580000a5e110500400c5706809c6110517c0200800008220a0084c00c570003404110500401987000340411050040135706808641105004001e806808220a00bb4001e80003404110500400c5706808220a008006a9280003404110500400dc70000832110500400c57000340411050040092706a8804110517c02008000340411055e402007000340411050068600706808221405004001e800008220a008003cc5706808641105005da00806809c63c088280200800060ba020882802007068092a110500400c5806a60041105004001e80003404110500400357068092a11050040092800034041105004012670003404110500400947000001a0208828020060003404321e028020070006004110500400c5706808221405005da00806a88043c088280200800008220a00bb400c5706808220a8b804003580014404110500400357068092a1105004003580003404110500400ee706808220a00ca000ff800034d60208828020070003404110545c020070003404110500401a4700034049b088280200700000a202088280200600034041105004015d7000340495088280200706808220ad7805da0080000822140500400c5706808220a008034cc5806808220ad2804001e8069b004110500400c5800034040a0080124c5706a880411050042600806808220a008003cf382e83404110500400f88069b0041105004009280000004110500746c560680822c60500400c5806808220a9d804009284c83404110500400f8806808220a00801f0c580c0340411050075000806808220a00bb400f3806808220a00802cec580696c041105004001e80680822c6050040092806a88041105004001e80680823180a028020080000004110080366c5600034040a008006a92706808220a00e6400c5806808220a2f80400c5806808220a00801f0928069080411050040191806808220a00ca000c58000001a0205004009260003404110500400a67000340411da0280200706808220a2f80400928000340411054ec0200706808220a00ca00092806808220a0080366c5806808220a00801f035806808220a008006b4f8000340411050054e00706808220a2f804003580003404110500400f870680878110500400c58000340495050040092700034041105004014f700008234c0500400c570690804110500400c5806808220a008003cff806a8804110a028020080028804110500400c570003404110517c0200700264da020882802007068087811050040092806a6144020882802008001b404110500400c57000001a6c0882802f8606808220ad9004001e8069080411050040092806808220a00801252d8000340495050040035700008220a008018aea700008220ad100400c5706808220a0080346c5800034041105007620070680a5e110500400c58069ac04110517c0200806808220a0084c00c58068087811050040035806ad804110a02802008000340411050055c007068092a110517c0200806808641105005b600806808220a00803469280003404110561c0200706808220a008012512800034043c088280200706808220a0084c009280680832110500400c584e034041105005da00800034041105007540070680822250517c0200800034041105004012d700034d8020500400927068083211050040092800034040a9d80400927068092a11050055c00806808220a008003cc5800000220a008034cc5606808220a0084c00358002713202088280200700000b402088280200606808789508828020080003404c60500400927000340411050040112706808220a008003c928000340411050042600700034040a00801f09270c03404110500400c5806808220a00bb400c580017404110500400c5700034040a2f80400927000340411050040110700034040a00ca00092706808220a008006a1e800008220a00ec000c57001741a42010280200706808220a00ea4009280c0340411050040092806808220a00bb40092806948043c0882802008068092a11050042600806808220ad780401ae800008220a008018b98700008220a008018b35706808220a00802cef880026404110500400c5706808220a00bb68600800034041105004001e706e9c041105004009280680822140500400c5800008220a008018adc706808220a00e6400f8806808220a2f80400f8806808220a00ca000f8806808220a00bb400358069b0043c088280200806ad9440208828020080003404110500401ac700034043c0500400927068082214050040092800008220a0080124c570c0340411050040094806808220a0080124a180003404110500752007000348402050040092700034040a00801252d700034041105005da0070003404110500746c57068092a1105004001e8006b404110500400c57068082214050040035800008220a008006ac5706808222505004001e80680878110500400f88068092a110500401ac800034040a008034692700034040a00801251270003404110a0280200700034040a0084c009270690804110500400f880000004110500400c560c034041105004015d8068092a1105005da008000340411d5828020074e035440208828020080003404110500400a17000340419050040092706808222505005da008000001a0208828be1e606808220a0084c00f8800034043c4a82802007068092a110a02802008000092a110500400c5700034040a008003c92706808234c0500400c580680832110500400f8806808220a00801f11080003404118c0280200706a8804110500400c580680822c605004001e806908041105007540083683404110500400c5800034040a00ea400927000601a02050040092706808220a00801f01e800034040a00bb40092706a88041105004009280003404110500400f3700034041105007500072e8340411050040113806808220a008018aea806808220ad100400c58000374e0205004009270003404e3088280200700008220a008034cc5706808220a00ca0001e806808220ad280401a4806a8804110500400358000340411050050c007001b004110500400c57000340414050040092700000040a0080124c560c03404110500400f8806808220a00bb400f884e034041105004015c800034040a0080124a17000354402088280200706809c695088280200806808220a00e65da0080680864110517c0200806808220a2f805da00836834041105004012680000822c60500400c5706808234c0500400ee806808781105004001e8000001a0205007469260680822140500400f8800008220a00801f0c570003404110500400ea7000340411056880200706a600411050054e00800008220a00802cec57
 | 9=>0x1a0208828020062b8340411050040092706808220a008006ae0006808220a0080181a024a84414010038001a02050040092606808220a00801f0e0d01044140176801c000208828020062b03544020882802007
 | _=>0
def sx (x0:Nat):Nat:=
 zm (land (Nat.mul x0 0xff51afd7ed558ccd) i1) fun x1 =>
 zm (xor x1 (shiftRight x1 33)) fun x2 =>
 zm (land (Nat.mul x2 0xc4ceb9fe1a85ec53) i1) fun x3 =>
 land (xor x3 (shiftRight x3 33)) 0xFFFFFF
def sg (b w:Nat):Nat:=
 sx (xor (xor w (shiftRight w 33)) b)
def p3 (salt:Nat):Nat->J->Nat
 | acc,[]=>acc
 | acc,(w,_)::rest=>zm (Nat.add acc (sg salt w)) fun acc' => p3 salt acc' rest
def oh (salt:Nat) (ws:J):Nat:=
 land (p3 salt 0 ws) 0xFFFFFF
def ue (packed:Nat):Nat->J
 | 0=>[]
 | k+1 =>
  (land (shiftRight bv (Nat.mul 64 (land packed 511))) i1,0) ::
  ue (shiftRight packed 9) k
def i0 (s j:Nat):J:=
 zm (shiftRight (qx s) (Nat.mul (au s) j)) fun sl =>
 ue (shiftRight sl 4) (land sl 15)
def dg (k v:Nat):Nat:=
 if beq v 0 then 0
 else
  lor
   (lor (if beq (land v 1) 0 then 0 else os (Nat.mul 4 k))
    (if beq (land v 2) 0 then 0 else os (Nat.add (Nat.mul 4 k) 1)))
   (lor (if beq (land v 4) 0 then 0 else os (Nat.add (Nat.mul 4 k) 2))
    (if beq (land v 8) 0 then 0 else os (Nat.add (Nat.mul 4 k) 3)))
def t6 (tt:Nat):Nat->Nat
 | 0=>0
 | k+1=>lor (dg k (land (shiftRight tt (Nat.mul 4 k)) 15)) (t6 tt k)
def o6 (b:Nat):Nat:=
 lor (t6 b 14) (shiftLeft (land b i1) c7.shTT)
def getF7Enc (s j:Nat):J:=
 (i0 s j).map fun p=>(o6 p.1,0)
def r8 (s:Nat) (c:J):Q:=
 let b:=sb bq c
 zm (oh db b) fun h =>
 zm (dz Nf7 qj qt s h) fun j =>
 !(beq j 999999)&&jk b (i0 s j)
def findF7 (s:Nat) (b:J):Q:=
 r8 s (sz c7.shTT b)
lemma mw {n r:Nat} (c:r < 2 ^ n):v7 (q1 n r)=r:=by
 apply nEQ;intro k;rw [jl];by_cases b:k < n
 . simp [q1,b]
 . simp only [b,↓reduceDIte];have d:2 ^ n<=2 ^ k:=nPLR (by omega) (by omega);exact (nTFL (Nat.lt_of_lt_of_le c d)).symm
lemma s9 {n w:Nat} (c:w < 2 ^ (2 ^ n)) :u9 n (fun x=>w.testBit (v7 x))=w:=by
 apply nEQ;intro r;rw [vr];by_cases b:r < 2 ^ n
 . simp only [b,↓reduceIte,mw b]
 . simp only [b,↓reduceIte];have d:2 ^ (2 ^ n)<=2 ^ r:=nPLR (by omega) (by omega);exact (nTFL (Nat.lt_of_lt_of_le c d)).symm
lemma cd:(range 56).all (fun m=>beq (shiftRight (os m) 294) 0)=true:=by decide +kernel
lemma ty:(range 294).all (fun idx => let r:=(n8 6 r7 294).getD idx 0
  blt r 56&&(range 56).all (fun m=>(os m).testBit idx == beq m r))=true:=by
 decide +kernel
lemma uk (a b:Nat):beq a b=decide (a=b):=by
 cases h:beq a b
 . symm;rw [decide_eq_false_iff_not];intro c;rw [c,nBR] at h;cases h
 . symm;rw [decide_eq_true_eq];exact nBQ.mp h
lemma b4 {m b:Nat} (c:m < 56) (hidx:294<=b) :(os m).testBit b=false:=by
 have d:=lAL.1 cd m (lMRG.2 c);have e:shiftRight (os m) 294=0:=by simpa [nBQ] using d
 have g:(os m).testBit (294+(b - 294))=false:=by rw [<- nTS];change (shiftRight (os m) 294).testBit (b - 294)=false;rw [e];simp
 rwa [show 294+(b - 294)=b by omega] at g
lemma b3 {m b:Nat} (e:m < 56) (g:b < 294) :(os m).testBit b=decide (m=(n8 6 r7 294).getD b 0):=by have c:=lAL.1 ty b (lMRG.2 g);simp only [bAT] at c;have d:=lAL.1 c.2 m (lMRG.2 e);rw [beq_iff_eq,uk] at d;exact d
lemma dd {b:Nat} (d:b < 294):(n8 6 r7 294).getD b 0 < 56:=by have c:=lAL.1 ty b (lMRG.2 d);simp only [bAT] at c;exact of_decide_eq_true (by simpa [nBL] using c.1)
lemma f9 {c k b:Nat} (hb:b < 4) :(land (shiftRight c (Nat.mul 4 k)) 15).testBit b=c.testBit (4*k+b):=by
 rw [nLA,nTA];have d:(15:Nat).testBit b=true:=by interval_cases b<;>decide
 rw [d,bATR];change (c >>> (4*k)).testBit b=c.testBit (4*k+b);rw [nTS]
lemma t5 (v b a c:Nat) :(if beq (land v (2 ^ b)) 0 then 0 else a).testBit c=(v.testBit b&&a.testBit c):=by
 by_cases d:v.testBit b=true
 . have s:land v (2 ^ b)≠0:=by
    intro t;have e:=congrArg (fun z=>z.testBit b) t
    rw [nLA,nTA,d,nT2S] at e;simp at e
   rw [if_neg (by rw [nBQ];exact s),d,bTA]
 . have g:v.testBit b=false:=by cases h:v.testBit b<;>simp_all
   have u:land v (2 ^ b)=0:=by
    apply nEQ;intro j;rw [nLA,nTA,nT2];by_cases i:b=j
    . subst i;simp [g]
    . simp [i]
   rw [if_pos (by rw [nBQ];exact u),g,Bool.false_and,Nat.zero_testBit]
lemma n9 (k v b:Nat) :(dg k v).testBit b = ((v.testBit 0&&(os (4*k)).testBit b) || (v.testBit 1&&(os (4*k+1)).testBit b) || (v.testBit 2&&(os (4*k+2)).testBit b) || (v.testBit 3&&(os (4*k+3)).testBit b)):=by
 unfold dg;by_cases c:v=0
 . subst c;simp
 . rw [if_neg (by rw [nBQ];exact c)]
   simp only [nLO,nTO,Nat.mul_eq,nAE];have d:(if beq (land v 1) 0 then 0 else os (4*k)).testBit b =
      (v.testBit 0&&(os (4*k)).testBit b):=t5 v 0 _ b
   have e:(if beq (land v 2) 0 then 0 else os (4*k+1)).testBit b =
      (v.testBit 1&&(os (4*k+1)).testBit b):=t5 v 1 _ b
   have g:(if beq (land v 4) 0 then 0 else os (4*k+2)).testBit b =
      (v.testBit 2&&(os (4*k+2)).testBit b):=t5 v 2 _ b
   have h:(if beq (land v 8) 0 then 0 else os (4*k+3)).testBit b =
      (v.testBit 3&&(os (4*k+3)).testBit b):=t5 v 3 _ b
   rw [d,e,g,h];simp only [Bool.or_assoc]
lemma l5 (d k c:Nat) (hk:k<=14) (b:294<=c) :(t6 d k).testBit c=false:=by
 induction k with
 | zero=>simp [t6]
 | succ k ih =>
  unfold t6;rw [nLO,nTO,ih (by omega),Bool.or_false];rw [n9 k _ c];rw [b4 (by omega) b,b4 (by omega) b,
   b4 (by omega) b,b4 (by omega) b]
  simp
lemma l4 (i k b:Nat) (hk:k<=14) (c:b < 294) :(t6 i k).testBit b = (decide ((n8 6 r7 294).getD b 0 < 4*k)&&i.testBit ((n8 6 r7 294).getD b 0)):=by
 induction k with
 | zero=>simp [t6]
 | succ k ih =>
  unfold t6;rw [nLO,nTO,ih (by omega)];rw [n9 k _ b];rw [f9 (by omega:0 < 4),f9 (by omega:1 < 4),
      f9 (by omega:2 < 4),f9 (by omega:3 < 4)]
  rw [b3 (by omega) c,b3 (by omega) c,
      b3 (by omega) c,b3 (by omega) c]
  simp only [nAZ];generalize (n8 6 r7 294).getD b 0=r
  by_cases j:r < 4*k
  . have d:4*k≠r:=by omega
    have e:4*k+1≠r:=by omega
    have g:4*k+2≠r:=by omega
    have h:4*k+3≠r:=by omega
    have s:r < 4*(k+1):=by omega
    simp [j,d,e,g,h,s]
  . by_cases t:r < 4*(k+1)
    . have u:r=4*k\/r=4*k+1\/r=4*k+2\/r=4*k+3:=by omega
      rcases u with rfl|rfl|rfl|rfl <;>
       simp [show ¬ 4*k < 4*k by omega,show 4*k < 4*(k+1) by omega,
        show ¬ 4*k+1 < 4*k by omega,show 4*k+1 < 4*(k+1) by omega,
        show ¬ 4*k+2 < 4*k by omega,show 4*k+2 < 4*(k+1) by omega,
        show ¬ 4*k+3 < 4*k by omega,show 4*k+3 < 4*(k+1) by omega]
    . have d:4*k≠r:=by omega
      have e:4*k+1≠r:=by omega
      have g:4*k+2≠r:=by omega
      have h:4*k+3≠r:=by omega
      simp [j,t,d,e,g,h]
lemma x4 (g:u7 6) :o6 (u9 6 g)=d7 (aR 6 r7 c7) g:=by
 apply nEQ;intro b;unfold o6 aR e6;have h:c7.shTT=294:=rfl;rw [nLO,nTO,h];have i:land (u9 6 g) i1=u9 6 g:=by
   apply nEQ;intro j;rw [nLA,nTA,vr];have s:i1=2 ^ 64 - 1:=by decide
   rw [s,nTB];by_cases t:j < 64<;>simp [t]
 rw [i,z8];by_cases c:b < 294
 . rw [l4 _ 14 b le_rfl c];have hr:=dd c;simp only [show (n8 6 r7 294).getD b 0 < 4*14 by omega,decide_true,bTA]
   have u:(shiftLeft (u9 6 g) 294).testBit b=false:=by change (u9 6 g <<< 294).testBit b=false;rw [Nat.testBit_shiftLeft];simp [show ¬ 294<=b by omega]
   rw [u,Bool.or_false,vr];have v:(n8 6 r7 294).getD b 0 < 2 ^ 6:=by omega
   simp only [v,↓reduceIte];have d:(n8 6 r7 294).length=294:=jj 6 r7 294;rw [List.getElem?_append_left (by omega),lGEQ (by omega)];rw [lGDE _ _ (by omega)]
 . rw [l5 _ 14 b le_rfl (by omega),Bool.false_or];change (u9 6 g <<< 294).testBit b=_;rw [Nat.testBit_shiftLeft];simp only [show 294<=b by omega,decide_true,bTA,vr]
   have d:(n8 6 r7 294).length=294:=jj 6 r7 294;rw [List.getElem?_append_right (by omega),d];by_cases e:b - 294 < 64
   . rw [lGEQ (by simp;omega)];simp [e]
   . rw [List.getElem?_eq_none (by simp;omega)];simp [e]
def g7 (s j:Nat):List (u7 6×Nat):=
 (i0 s j).map fun p=>((fun x=>p.1.testBit (v7 x)),0)
lemma n7 (c k:Nat) :∀ p∈ue c k,p.1 < 2 ^ 64/\p.2=0:=by
 induction k generalizing c with
 | zero=>intro p b;simp [ue] at b
 | succ k ih =>
  intro p b;simp only [ue,lMM] at b;rcases b with rfl|b'
  . refine ⟨?_,rfl⟩
    rw [nLA];have d:i1=2 ^ 64 - 1:=by decide
    rw [d];exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
  . exact ih _ p b'
lemma dn (s j:Nat):i0 s j=u4 6 (g7 s j):=by
 unfold g7 u4;rw [lMMp];have b:∀ p∈i0 s j,p.1 < 2 ^ 64/\p.2=0:=by unfold i0;simp only [v5];exact n7 _ _
 conv_lhs=>rw [<- lMI (i0 s j)]
 apply lMCL
 intro p c;obtain ⟨d,e⟩:=b p c;simp only [Function.comp,id,s9 (n:=6) d];exact Prod.ext rfl e
lemma tw (s j:Nat):getF7Enc s j=eW r7 c7 (g7 s j):=by
 unfold getF7Enc g7 eW e4;rw [lMMp];have b:∀ p∈i0 s j,p.1 < 2 ^ 64/\p.2=0:=by unfold i0;simp only [v5];exact n7 _ _
 apply lMCL
 intro p c;obtain ⟨d,_⟩:=b p c;simp only [Function.comp];rw [<- x4,s9 (n:=6) d]
lemma aa (s j:Nat):AllTagsLe3 (g7 s j):=by intro p b;unfold g7 at b;rcases lMp.1 b with ⟨_,_,rfl⟩;omega
lemma pu:∀ g∈bq,vh f7 g:=
 ye 6 f7 bq [[(4,5)],[(1,2)],[(2,5),(1,4),(0,3)]] (by decide +kernel)
lemma tf:∀ s (b:List (u7 6×Nat)), r8 s (u4 6 b)=true -> ∃ j < Nf7 s,∃ π : (F 6)->(F 6), Function.Bijective π/\(∀ x,f7 (π x)=f7 x) /\ (b.map fun p=>((fun x=>p.1 (π x)),p.2)).Perm (g7 s j):=by
 intro s b h;unfold r8 at h;simp only [v5,bAT,bNT,zh] at h;obtain ⟨d,c⟩:=h;set j:=dz Nf7 qj qt s (oh db (sb bq (u4 6 b)));have e:j < Nf7 s:=j8 Nf7 qj qt s _ d;obtain ⟨π,g,i,t⟩:=rb bq pu b;rw [dn s j] at c;have u:=(zv _ _).1 (t.symm.trans (y5 _ _ c));exact ⟨j,e,π,g,i,u⟩
lemma ab:w2 f7 (aR 6 r7 c7) Nf7 g7 findF7:=by intro s b h;unfold findF7 at h;change r8 s (sz c7.shTT (eW r7 c7 b))=true at h;rw [eW,aR,kg] at h;exact tf s b h
lemma bp:CfgOk 6 f7 r7 c7:=jn 6 f7 r7 c7 (by decide +kernel)
lemma et (b:∀ s≤ 9,∀ i < Nf7 s,bar c7 findF7 getF7Enc s i=true) :∀ s≤ 9,∀ i < Nf7 s,¬ TR f7 s (g7 s i):=
 gu bp 9 (by omega) Nf7 g7 getF7Enc tw aa findF7 ab b
lemma p8:c7.lok=2 ^ 102 - 1:=by decide
lemma am (w:Nat):wC c7 w < 2 ^ 102:=by
 apply nLPT;intro i hi;unfold wC wi ag;rw [nXO,nTX,nLA,nLA,nTA,nTA,p8,nTB];have b:¬ (i < 102):=by omega
 simp [b]
lemma eu (b:J):yx c7 b < 2 ^ 102:=by
 induction b with
 | nil=>simp [yx]
 | cons p rest ih =>
  rw [yp];apply nLPT;intro i c;rw [nLO,nTO,
   nTFL (Nat.lt_of_lt_of_le (am p.1) (nPLR (by omega) c)),
   nTFL (Nat.lt_of_lt_of_le ih (nPLR (by omega) c))]
  rfl
lemma i8 (b:J) (i:Nat) :(yx c7 b).testBit i=b.any (fun p=>(wC c7 p.1).testBit i):=by
 induction b with
 | nil=>simp [yx]
 | cons p rest ih=>rw [yp,nLO,nTO,ih];simp
def u1 (b:M):J:=b.map fun w=>(o6 w,0)
lemma n4 (L0:List (u7 6)) :u1 (L0.map (u9 6))=eW r7 c7 (L0.map (·,0)):=by unfold u1 eW e4;simp only [lMMp];apply lMCL;intro g _;simp [Function.comp,x4]
lemma n6 {a b:M} (h:a.Sublist b) (i:Nat) :(yx c7 (u1 a)).testBit i=true->(yx c7 (u1 b)).testBit i=true:=by
 rw [i8,i8,lAN,lAN]
 rintro ⟨p,c,d⟩
 exact ⟨p,(h.map _).subset c,d⟩
lemma ts {s:Nat} {L0:List (u7 6)} (b:TR f7 s (L0.map (·,0))) :yx c7 (u1 (L0.map (u9 6)))=c7.lok:=by
 rw [n4];apply zz bp
 intro u v c d;have e:Run (invF (n:=6)) meetF joinF f7 s L0:=by
  have h:=b.toRun;have i:(L0.map (·,0)).map Prod.fst=L0:=by rw [lMMp];exact lMI L0
  rwa [i] at h
 obtain ⟨g,j,t⟩:=w6 e (show f7 u≠f7 v by rw [c,d];decide)
 exact ⟨(g,0),lMp.2 ⟨g,j,rfl⟩,t⟩
lemma s4 {a b c:Nat} (e:a < 2 ^ 102) (h:c < 2 ^ 102) (j:∀ i,b.testBit i=true->c.testBit i=true) (s:lor a b=c7.lok):lor a c=c7.lok:=by
 apply nEQ;intro i;rw [nLO,nTO,p8,nTB];by_cases g:i < 102
 . simp only [g,decide_true];have d:=congrArg (fun z=>z.testBit i) s
   rw [nLO,nTO,p8,nTB] at d;simp only [g,decide_true] at d;cases e' : a.testBit i
   . simp only [e',Bool.false_or] at d ⊢;exact j i d
   . simp
 . simp only [g,decide_false];rw [nTFL (Nat.lt_of_lt_of_le e (nPLR (by omega) (by omega))),
      nTFL (Nat.lt_of_lt_of_le h (nPLR (by omega) (by omega)))]
   rfl
def t4:M->Nat×List (Nat×Nat×Nat×Nat×Nat×Nat×Nat)
 | []=>(0,[])
 | w::rest =>
  let (sC,rs):=t4 rest
  zm (o6 w) fun ew =>
  zm (land ew c7.lok) fun elo =>
  zm (land (shiftRight ew c7.k) c7.lok) fun ehi =>
  zm (xor elo ehi) fun cw =>
  zm (land cw ehi) fun uw =>
  zm (qi c7.m0 (land (shiftRight ew c7.sh0) c7.m0all)) fun v0w =>
  zm (yg c7.sh1 c7.m1 c7.m12 ew) fun v1w =>
  (lor cw sC,(w,ew,cw,uw,v0w,v1w,sC)::rs)
lemma x5 (b:M):(t4 b).1=yx c7 (u1 b):=by
 induction b with
 | nil=>rfl
 | cons w rest ih=>simp [t4,u1,yx,wC,wi,ag,v5,ih]
def b9 (b e g h i:Nat) (c d:J):Q:=
 match c with
 | []=>true
 | _ =>
  if beq b 0 then
   match c with
   | [(w,_)]=>!(beq w dw)
   | _=>true
  else if beq e (Nat.add b 1) then
   if !(beq g c7.lok)||!(qb c7 h 0) then true
   else r8 b c||s5 c7 b d
  else if beq e b then
   if !(beq g c7.lok)&&!(z3 c7 i) then true
   else r8 b c||s5 c7 b d
  else
   r8 b c||s5 c7 b d
def s8 (b:Nat):List (Nat×Nat×Nat×Nat×Nat×Nat×Nat)->Nat->Nat->Nat->Nat->Nat->J->J->Q
 | [],len,cc,cu,sv0,sv1,curTT,curEnc =>
  !(beq cc c7.lok)||b9 b len cu sv0 sv1 curTT curEnc
 | (w,ew,cw,uw,v0w,v1w,sC)::rest,len,cc,cu,sv0,sv1,curTT,curEnc =>
  if beq len (Nat.add b 1) then
   !(beq cc c7.lok)||b9 b len cu sv0 sv1 curTT curEnc
  else
   let c:=
    zm (lor cw cc) fun cc1 =>
    if beq (lor cc1 sC) c7.lok then
     s8 b rest (Nat.add len 1) cc1 (lor uw cu) (Nat.add v0w sv0) (Nat.add v1w sv1) ((w,0)::curTT) ((ew,0)::curEnc)
    else true
   if !c then false
   else if beq (lor cc sC) c7.lok then
    s8 b rest len cc cu sv0 sv1 curTT curEnc
   else true
lemma er (g:Nat) (i:M) :∀ (b sub:M), sub.Sublist i -> b.length+sub.length<=g+1 -> lor (yx c7 (u1 b)) (yx c7 (u1 sub))=c7.lok -> s8 g (t4 i).2 b.length (yx c7 (u1 b)) (v4 c7 (u1 b)) (zf c7 (u1 b)) (va c7 (u1 b)) (b.map (·,0)) (u1 b)=true -> ∃ L',L'.Perm (sub++b) /\ b9 g L'.length (v4 c7 (u1 L')) (zf c7 (u1 L')) (va c7 (u1 L')) (L'.map (·,0)) (u1 L')=true:=by
 induction i with
 | nil =>
  intro b sub c _ d e;cases c
  rw [show yx c7 (u1 [])=0 from rfl,nLO,Nat.or_zero] at d;simp only [t4,s8,d,nBR,Bool.not_true,Bool.false_or] at e;exact ⟨b,lPR _,e⟩
 | cons w rest ih =>
  intro b sub c hlen d e;simp only [t4,v5,x5] at e;unfold s8 at e;by_cases t:b.length=g+1
  . have x:sub=[]:=List.eq_nil_of_length_eq_zero (by omega);subst x;rw [show yx c7 (u1 [])=0 from rfl,nLO,Nat.or_zero] at d;have j:beq b.length (Nat.add g 1)=true:=by rw [nBQ];exact t
    simp only [j,↓reduceIte,d,nBR,Bool.not_true,Bool.false_or] at e;exact ⟨b,lPR _,e⟩
  . have j:beq b.length (Nat.add g 1)=false:=q2 t;simp only [j,bFT,↓reduceIte] at e;obtain ⟨h,u⟩:=o8 e;cases c with
    | cons _ c' =>
     have s:lor (yx c7 (u1 b)) (yx c7 (u1 rest))=c7.lok:=
      s4 (eu _) (eu _) (n6 c') d
     simp only [s,nBR,↓reduceIte] at u;exact ih b sub c' hlen d u
    | cons_cons _ c' =>
     rename_i sub'
     have v:lor (yx c7 (u1 (w::b))) (yx c7 (u1 sub'))=c7.lok:=by simp only [u1,lMC,yx,lFC,nLO] at d ⊢;rw [Nat.or_comm (wC c7 (o6 w)),Nat.or_assoc];exact d
     have s:lor (yx c7 (u1 (w::b))) (yx c7 (u1 rest))=c7.lok:=
      s4 (eu _) (eu _) (n6 c') v
     have y:lor (xor (land (o6 w) c7.lok) (land (shiftRight (o6 w) c7.k) c7.lok)) (yx c7 (u1 b)) =
       yx c7 (u1 (w::b)):=rfl
     have z:lor (land (xor (land (o6 w) c7.lok) (land (shiftRight (o6 w) c7.k) c7.lok))
       (land (shiftRight (o6 w) c7.k) c7.lok)) (v4 c7 (u1 b))=v4 c7 (u1 (w::b)):=rfl
     have h0:Nat.add (qi c7.m0 (land (shiftRight (o6 w) c7.sh0) c7.m0all)) (zf c7 (u1 b))=zf c7 (u1 (w::b)):=rfl;have h1:Nat.add (yg c7.sh1 c7.m1 c7.m12 (o6 w)) (va c7 (u1 b))=va c7 (u1 (w::b)):=rfl;simp only [v5,y,s,nBR,↓reduceIte,z,h0,h1] at h;have hlen' : (w::b).length+sub'.length<=g+1:=by simp at hlen ⊢;omega
     have h' : s8 g (t4 rest).2 (w::b).length (yx c7 (u1 (w::b)))
       (v4 c7 (u1 (w::b))) (zf c7 (u1 (w::b))) (va c7 (u1 (w::b)))
       ((w::b).map (·,0)) (u1 (w::b))=true:=by
      simpa [lLC,nAE,u1] using h
     obtain ⟨L',h2,h3⟩:=ih (w::b) sub' c' hlen' v h';exact ⟨L',h2.trans lPM,h3⟩
lemma tx:u9 6 f7=dw:=by decide +kernel
lemma ux (he:∀ s≤ 9,∀ i < Nf7 s,bar c7 findF7 getF7Enc s i=true) {y:Nat} (hf:y<=9) {L0:List (u7 6)} {L' : M} (h7:L'.Perm (L0.map (u9 6))) (b:b9 y L'.length (v4 c7 (u1 L')) (zf c7 (u1 L')) (va c7 (u1 L')) (L'.map (·,0)) (u1 L')=true) :¬ TR f7 y (L0.map (·,0)):=by
 intro c;have hh:L0≠[]:=by intro h8;subst h8;have a1:=ts c;rw [show yx c7 (u1 ([].map (u9 6)))=0 from rfl,p8] at a1;exact absurd a1 (by decide)
 have hi:L'≠[]:=by intro h8;subst h8;have hlen:=h7.length_eq;simp at hlen;exact hh (List.eq_nil_of_length_eq_zero hlen.symm)
 have hk:∃ L0' : List (u7 6),L0'.Perm L0/\L0'.map (u9 6)=L':=by
  have a2:∀ w∈L',w < 2 ^ 64:=by
    intro w z;rcases lMp.1 (h7.mem_iff.1 z) with ⟨g,_,rfl⟩
    apply nLPT;intro r hr;rw [vr,if_neg (by omega)]
  refine ⟨L'.map (fun w (x:F 6)=>w.testBit (v7 x)),?_,?_⟩
  . have hm:(L'.map (fun w (x:F 6)=>w.testBit (v7 x))).map (u9 6)=L':=by
      rw [lMMp];conv_rhs=>rw [<- lMI L']
      apply lMCL;intro w z;simp [Function.comp,s9 (n:=6) (a2 w z)]
    have hn:(u4 6 ((L'.map (fun w (x:F 6)=>w.testBit (v7 x))).map (·,0))).Perm
              (u4 6 (L0.map (·,0))):=by
      have d:=(show ((L'.map (fun w (x:F 6)=>w.testBit (v7 x))).map (u9 6)).Perm (L0.map (u9 6)) by rw [hm];exact h7).map (fun w=>(w,0))
      have hL:u4 6 ((L'.map (fun w (x:F 6)=>w.testBit (v7 x))).map (·,0)) =
          ((L'.map (fun w (x:F 6)=>w.testBit (v7 x))).map (u9 6)).map (fun w=>(w,0)):=by
        unfold u4;simp [lMMp,Function.comp]
      have hR:u4 6 (L0.map (·,0))=(L0.map (u9 6)).map (fun w=>(w,0)):=by unfold u4;simp [lMMp,Function.comp]
      rw [hL,hR];exact d
    have hq:=((zv _ _).1 hn).map Prod.fst;have h9:((L'.map (fun w (x:F 6)=>w.testBit (v7 x))).map (·,0)).map Prod.fst =
        L'.map (fun w (x:F 6)=>w.testBit (v7 x)):=by rw [lMMp];exact lMI _
    have ht:(L0.map (·,0)).map Prod.fst=L0:=by rw [lMMp];exact lMI _
    rwa [h9,ht] at hq
  . rw [lMMp];conv_rhs=>rw [<- lMI L']
    apply lMCL;intro w z;simp [Function.comp,s9 (n:=6) (a2 w z)]
 obtain ⟨L0',hx,e⟩:=hk;have c' : TR f7 y (L0'.map (·,0)):=TagRun.perm (hx.symm.map (·,0)) c;cases y with
 | zero =>
  obtain ⟨tg,h⟩:=c'.inv_zero;have hy' : L0'=[f7]:=by
    have:=congrArg (List.map Prod.fst) h
    have h9:(L0'.map (·,0)).map Prod.fst=L0':=by rw [lMMp];exact lMI _
    simpa [h9] using this
  rw [hy'] at e;simp only [lMC,lMN,tx] at e;rw [<- e] at b;simp [b9] at b
 | succ s' =>
  cases hL' : L' with
  | nil=>exact absurd hL' hi
  | cons w0 ws0 =>
    rw [hL'] at b e;have hz:(w0::ws0).map (fun w=>(w,0))=u4 6 (L0'.map (·,0)):=by rw [<- e];unfold u4;simp [lMMp,Function.comp]
    have xi:u1 (w0::ws0)=eW r7 c7 (L0'.map (·,0)):=by rw [<- e];exact n4 L0'
    have hlenL:(w0::ws0).length=L0'.length:=by rw [<- e];simp
    have b1:(L0'.map (·,0)).length<=11:=by have:=c'.len_le;simp at this ⊢;omega
    have x2' : Run (invF (n:=6)) meetF joinF f7 (s'+1) ((L0'.map (·,0)).map Prod.fst):=c'.toRun;have h6:(L0'.map (·,0)).map Prod.fst=L0':=by rw [lMMp];exact lMI _
    simp only [b9,lMC,nBQ,Nat.succ_ne_zero,↓reduceIte,xi] at b;have hc:(r8 (s'+1) ((w0::ws0).map (·,0))||s5 c7 (s'+1) (eW r7 c7 (L0'.map (·,0))))=true:=by
      by_cases d:(w0::ws0).length=s'+1+1
      . have h:((L0'.map (·,0)).map Prod.fst).length=(s'+1)+1:=by rw [h6];omega
        have x3:v4 c7 (eW r7 c7 (L0'.map (·,0)))=c7.lok:=q6 bp fun u v hu hv=>by
          obtain ⟨g,hg,ha,hb⟩:=tj x2' h u v hu hv;rw [h6] at hg;exact ⟨(g,0),lMp.2 ⟨g,hg,rfl⟩,ha,hb⟩
        have xs:qb c7 (zf c7 (eW r7 c7 (L0'.map (·,0)))) 0=true:=td bp b1 fun r0 r1 r2 r3 r4 r5 h0 d' t h3 h4 h5=>by
          have:=dc x2' h r0 r1 r2 r3 r4 r5 h0 d' t h3 h4 h5;rwa [lMMp] at this
        simp only [d,nAE,↓reduceIte,x3,nBR,Bool.not_true,xs,Bool.or_self,bFT] at b;exact b
      . simp only [d,nAE,↓reduceIte] at b;by_cases t:(w0::ws0).length=s'+1
        . have h:((L0'.map (·,0)).map Prod.fst).length=s'+1:=by rw [h6];omega
          have h10:(!(beq (v4 c7 (eW r7 c7 (L0'.map (·,0)))) c7.lok)&&!(z3 c7 (va c7 (eW r7 c7 (L0'.map (·,0))))))=false:=by
           rcases ds x2' h with hu|hs
           . have x3:v4 c7 (eW r7 c7 (L0'.map (·,0)))=c7.lok:=q6 bp fun u v ha hb=>by
               obtain ⟨g,hg,hga,hgb⟩:=hu u v ha hb;rw [h6] at hg;exact ⟨(g,0),lMp.2 ⟨g,hg,rfl⟩,hga,hgb⟩
             simp [x3]
           . have h11:z3 c7 (va c7 (eW r7 c7 (L0'.map (·,0))))=true:=vt bp b1 fun r0 r1 r2 r3 r4 r5 h0 d' t' h3 h4 h5=>by
               have:=hs r0 r1 r2 r3 r4 r5 h0 d' t' h3 h4 h5;rwa [lMMp] at this
             simp [h11]
          simp only [t,↓reduceIte,h10,bFT] at b;exact b
        . simp only [t,↓reduceIte] at b;exact b
    rw [bOT] at hc;rcases hc with hd|h12
    . rw [hz] at hd;obtain ⟨j,hj,π,h13,h14,hp⟩:=tf (s'+1) (L0'.map (·,0)) hd;exact et he (s'+1) hf j hj (TagRun.perm hp (wp π h13 h14 c'))
    . exact c8 bp h12 c'
lemma oc (h5:∀ s≤ 9,∀ i < Nf7 s,bar c7 findF7 getF7Enc s i=true) {e:Nat} (h6:e<=9) (b:M) (h7:b.Nodup) (y : !(beq (t4 b).1 c7.lok)||s8 e (t4 b).2 0 0 0 0 0 [] []=true) {L0:List (u7 6)} (h8:L0.Nodup) (h9:∀ g∈L0,u9 6 g∈b) :¬ TR f7 e (L0.map (·,0)):=by
 intro t;let d:=L0.map (u9 6);have x2:d.Nodup:=h8.map (fun _ _ h=>yc h)
 let sub:=b.filter (fun w=>decide (w∈d))
 have z:sub.Sublist b:=List.filter_sublist;have x3:sub.Nodup:=h7.filter _;have u:sub.Perm d:=by
   refine (List.perm_ext_iff_of_nodup x3 x2).2 ?_
   intro w;simp only [sub,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp];intro hw;rcases lMp.1 hw with ⟨g,hg,rfl⟩
   exact h9 g hg
 have a1:yx c7 (u1 d)=c7.lok:=ts t;have h0:yx c7 (u1 sub)=c7.lok:=by
   apply nEQ;intro i;rw [i8,<- a1,i8];have h3:(u1 sub).Perm (u1 d):=u.map _;cases h:(u1 sub).any (fun p=>(wC c7 p.1).testBit i)
   . symm;rw [Bool.eq_false_iff];intro j;rw [lAN] at j;rcases j with ⟨p,c,v⟩
     have:(u1 sub).any (fun p=>(wC c7 p.1).testBit i)=true:=
      lAN.2 ⟨p,h3.mem_iff.2 c,v⟩
     rw [h] at this;cases this
   . symm;rw [lAN] at h ⊢;rcases h with ⟨p,c,v⟩
     exact ⟨p,h3.mem_iff.1 c,v⟩
 simp only [bOT,bNT,x5] at y;rcases y with h4|a2
 . have b1:yx c7 (u1 b)=c7.lok:=by
     have x:=s4 (a:=0) (by decide) (eu _) (n6 z)
      (by simpa [nLO] using h0)
     simpa [nLO] using x
   rw [b1,nBR] at h4;cases h4
 . have hlen:([]:M).length+sub.length<=e+1:=by
     have x:=t.len_le;have j:=u.length_eq;simp [d] at x j ⊢;omega
   obtain ⟨L',c',ha⟩:=er e b [] sub z hlen
     (by simpa [u1,yx,nLO] using h0) a2
   have c'' : L'.Perm (L0.map (u9 6)):=by simpa using c'.trans (by simpa using u)
   exact ux h5 h6 c'' ha t
def fG:u7 8:=fun x:F 8 =>
 (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4) ||
 (x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)||(x 4&&x 7)||(x 5&&x 6)
def m8 (x:F 6):F 8
 | ⟨0,_⟩ => x 0
 | ⟨1,_⟩ => x 1
 | ⟨2,_⟩ => x 2
 | ⟨3,_⟩ => x 3
 | ⟨4,_⟩ => false
 | ⟨5,_⟩ => x 4
 | ⟨6,_⟩ => x 5
 | ⟨7,_⟩ => true
def y6 (x:F 6):F 8
 | ⟨0,_⟩ => x 0
 | ⟨1,_⟩ => x 1
 | ⟨2,_⟩ => x 2
 | ⟨3,_⟩ => x 3
 | ⟨4,_⟩ => false
 | ⟨5,_⟩ => x 4
 | ⟨6,_⟩ => x 5
 | ⟨7,_⟩ => false
def m7 (g:u7 8):u7 6:=fun x=>g (m8 x)
def u3:List e8:=
 [inr 0,inr 1,inr 2,inr 3,inl false,inr 4,inr 5,inl true]
def a7:List e8:=
 [inr 0,inr 1,inr 2,inr 3,inl false,inr 4,inr 5,inl false]
def t8:List e8:=
 [inr 0,inr 1,inr 2,inr 3,inr 4,inr 5,inr 6,inl true]
def i2:List e8:=
 [inr 0,inr 1,inr 2,inr 3,inr 4,inr 5,inr 6,inl false]
def i5 (x:F 7):F 8
 | ⟨0,_⟩ => x 0
 | ⟨1,_⟩ => x 1
 | ⟨2,_⟩ => x 2
 | ⟨3,_⟩ => x 3
 | ⟨4,_⟩ => x 4
 | ⟨5,_⟩ => x 5
 | ⟨6,_⟩ => x 6
 | ⟨7,_⟩ => false
def mn:List e8:=
 [inr 4,inr 5,inl false,inr 1,inr 3,inr 0,inr 2,inr 6]
def y4 (x:F 7):F 8
 | ⟨0,_⟩ => x 4
 | ⟨1,_⟩ => x 5
 | ⟨2,_⟩ => false
 | ⟨3,_⟩ => x 1
 | ⟨4,_⟩ => x 3
 | ⟨5,_⟩ => x 0
 | ⟨6,_⟩ => x 2
 | ⟨7,_⟩ => x 6
def mm:List e8:=
 [inr 1,inr 0,inr 2,inr 4,inr 3,inr 5,inl false,inr 6]
def y0 (x:F 7):F 8
 | ⟨0,_⟩ => x 1
 | ⟨1,_⟩ => x 0
 | ⟨2,_⟩ => x 2
 | ⟨3,_⟩ => x 4
 | ⟨4,_⟩ => x 3
 | ⟨5,_⟩ => x 5
 | ⟨6,_⟩ => false
 | ⟨7,_⟩ => x 6
lemma f3 (x:F 6):fG (m8 x)=f7 x:=by simp only [fG,m8,f7,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or]
lemma ea (x:F 6):fG (y6 x)=f7 x:=by simp only [fG,y6,f7,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or]
lemma l0 (x:F 7):fG (i5 x)=bt x:=by simp only [fG,i5,bt,Bool.and_false,Bool.or_false]
lemma sk (x:F 7):fG (y4 x)=af x:=by simp only [fG,y4,af];cases x 0<;>cases x 1<;>cases x 2<;>cases x 3<;>cases x 4<;>cases x 5<;>cases x 6<;>rfl
lemma sj (x:F 7):fG (y0 x)=af x:=by simp only [fG,y0,af];cases x 0<;>cases x 1<;>cases x 2<;>cases x 3<;>cases x 4<;>cases x 5<;>cases x 6<;>rfl
lemma m9 (x:F 6):ej 6 (ofFn x) (ofFn (m8 x)) (u3,[]):=by
 refine ⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with b|b
 . interval_cases i<;>simp [u3,m8,qn,ze,q3]
 . rw [lGD _ _ (by simp [u3];omega),lGD _ _ (by simp;omega)];exact ⟨trivial,rfl⟩
lemma og (x:F 6):ej 6 (ofFn x) (ofFn (y6 x)) (a7,[]):=by
 refine ⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with b|b
 . interval_cases i<;>simp [a7,y6,qn,ze,q3]
 . rw [lGD _ _ (by simp [a7];omega),lGD _ _ (by simp;omega)];exact ⟨trivial,rfl⟩
lemma p6 (x:F 8) :ej 8 (ofFn x) (ofFn (update x 7 true)) (t8,[]):=by
 refine ⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with b|b
 . interval_cases i<;>simp [t8,qn,ze,q3,update]
 . rw [lGD _ _ (by simp [t8];omega),lGD _ _ (by simp;omega)];exact ⟨trivial,rfl⟩
lemma p0 (x:F 7):ej 7 (ofFn x) (ofFn (i5 x)) (i2,[]):=by
 refine ⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with b|b
 . interval_cases i<;>simp [i2,i5,qn,ze,q3]
 . rw [lGD _ _ (by simp [i2];omega),lGD _ _ (by simp;omega)];exact ⟨trivial,rfl⟩
lemma mg (x:F 7):ej 7 (ofFn x) (ofFn (y4 x)) (mn,[]):=by
 refine ⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with b|b
 . interval_cases i<;>simp [mn,y4,qn,ze,q3]
 . rw [lGD _ _ (by simp [mn];omega),lGD _ _ (by simp;omega)];exact ⟨trivial,rfl⟩
lemma mf (x:F 7):ej 7 (ofFn x) (ofFn (y0 x)) (mm,[]):=by
 refine ⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with b|b
 . interval_cases i<;>simp [mm,y0,qn,ze,q3]
 . rw [lGD _ _ (by simp [mm];omega),lGD _ _ (by simp;omega)];exact ⟨trivial,rfl⟩
lemma i6:∃ x y:F 6,f7 x≠f7 y:=
 ⟨fun _=>false,fun _=>true,by decide⟩
lemma dv:∃ x y:F 7,af x≠af y:=
 ⟨fun _=>false,fun _=>true,by decide⟩
lemma ur:∃ x y:F 7,bt x≠bt y:=
 ⟨fun _=>false,fun _=>true,by decide⟩
lemma bn:∃ x y:F 8,fG x≠fG y:=
 ⟨fun _=>false,fun _=>true,by decide⟩
lemma o9 {n m B:Nat} {f:u7 n} {g:u7 m} {gs:U} {o:Nat} (init:List e8) (d:(F m)->(F n)) (hcl:yq n gs) (hev:∀ x,e3 gs n o x=f x) (t:∀ x,ej m (ofFn x) (ofFn (d x)) (init,[])) (u:∀ x,f (d x)=g x) (v:∃ x y,g x≠g y) (w:∀ s',HCS m g s'->B<=s') :(∀ c,(u2 m gs (init,[])).1.getD o (inl false)≠inl c) /\ B<=(u2 m gs (init,[])).2.length:=by
 set b:=u2 m gs (init,[]);have z:∀ x,ej m (ofFn x) (q3 gs (ofFn (d x))) b:=
  fun x=>j7 m _ (by simp) gs _ _ (fun g' hg' => (ja hcl g' hg').1) (t x)
 have e:∀ x,ze (q3 b.2 (ofFn x)) (b.1.getD o (inl false))=g x:=
  fun x=>((z x).2 o).2.trans ((hev (d x)).trans (u x))
 have h:∀ c,b.1.getD o (inl false)≠inl c:=by
  intro c hc;obtain ⟨x,y,h0⟩:=v;apply h0
  rw [<- e x,<- e y,hc];rfl
 refine ⟨h,?_⟩
 cases i:b.1.getD o (inl false) with
 | inl c=>exact absurd i (h c)
 | inr j =>
  apply w b.2.length
  refine ⟨⟨b.2,j⟩,mb m gs _ (by simp),le_refl _,?_⟩
  intro x;have:=e x;rw [i] at this;exact this
lemma d6 {n m s:Nat} {f:u7 n} {g:u7 m} (init:List e8) (d:(F m)->(F n)) (w:∀ x,ej m (ofFn x) (ofFn (d x)) (init,[])) (e:∀ x,f (d x)=g x) (i:∃ x y,g x≠g y) (z:HCS n f s):HCS m g s:=by
 have h0:∃ x y,f x≠f y:=by obtain ⟨x,y,t⟩:=i;exact ⟨d x,d y,by rwa [e,e]⟩
 obtain ⟨gs,o,u,hlen⟩:=fr n f s h0 z;set b:=u2 m gs (init,[]);have h2:∀ x,ej m (ofFn x) (q3 gs (ofFn (d x))) b:=
  fun x=>j7 m _ (by simp) gs _ _ (fun g' hg' => (ja u.hcl g' hg').1) (w x)
 have h:∀ x,ze (q3 b.2 (ofFn x)) (b.1.getD o (inl false))=g x:=
  fun x=>((h2 x).2 o).2.trans ((u.hev (d x)).trans (e x))
 cases v:b.1.getD o (inl false) with
 | inl c =>
  exfalso;obtain ⟨x,y,t⟩:=i;apply t
  rw [<- h x,<- h y,v];rfl
 | inr j =>
  have h3:b.2.length<=s:=by
   have h1:b.2.length<=gs.length:=by simpa [b] using cm m gs (init,[])
   omega
  refine ⟨⟨b.2,j⟩,mb m gs _ (by simp),h3,?_⟩
  intro x;have:=h x;rw [v] at this;exact this
lemma cn:∀ s,HCS 8 (fun x=>fG (update x 7 false)) s->12<=s:=by
 intro s b;apply lb20 s
 apply d6 i2 i5 p0 _ ur b
 intro x
 have:update (i5 x) 7 false=i5 x:=by funext i;fin_cases i<;>rfl
 rw [this];exact l0 x
lemma se:∀ s,HCS 8 (fun x=>fG (update x 2 false)) s->11<=s:=by
 intro s b;apply lb12 s
 apply d6 mn y4 mg _ dv b
 intro x
 have:update (y4 x) 2 false=y4 x:=by funext i;fin_cases i<;>rfl
 rw [this];exact sk x
lemma sd:∀ s,HCS 8 (fun x=>fG (update x 6 false)) s->11<=s:=by
 intro s b;apply lb12 s
 apply d6 mm y0 mf _ dv b
 intro x
 have:update (y0 x) 6 false=y0 x:=by funext i;fin_cases i<;>rfl
 rw [this];exact sj x
lemma te:∀ s,HCS 8 (fun x=>fG (update x 7 true)) s->11<=s:=by
 intro s e;have j:∃ x y:F 8,fG (update x 7 true)≠fG (update y 7 true):=
  ⟨fun _=>false,fun _=>true,by decide⟩
 obtain ⟨gs,o,b,hlen⟩:=fr 8 _ s j e;have t:(4:Nat)∈liveList gs 8 o 0:=
  be b.hev 4 ⟨fun _=>false,by decide⟩
 have u:(4:Nat)≠o:=by
  intro v;have c:=b.hev (fun i:Fin 8=>i=0||i=1)
  rw [<- v] at c;have w:e3 gs 8 4 (fun i:Fin 8=>i=0||i=1)=false:=by unfold e3;rw [ve _ _ _ (by simp)];simp
  rw [w] at c;revert c;decide
 have z:∃ g∈gs,(4:Nat)∈g.inputs:=by
  rcases ((qw gs 8 o 0 4).1 t).2 with h|⟨q,_,g,d,h0,_⟩
  . exact absurd h u
  . exact ⟨g,List.mem_of_getElem? d,h0⟩
 have hlb10:=(o9 u3 m8 b.hcl b.hev m9
  (fun x=>by
    have:update (m8 x) 7 true=m8 x:=by funext i;fin_cases i<;>rfl
    rw [this];exact f3 x)
  i6 lb7).2
 have h3:=zt 6 4 gs (u3,[]) (fun g d=>ja b.hcl g d) (by simp [u3])
  ⟨false,by simp [u3]⟩ z
 simp at h3;omega
lemma od {n:Nat} {f:u7 n} {gs:U} {o:Nat} (hcl:yq n gs) (ho:o < n+gs.length) (hev:∀ x,e3 gs n o x=f x) (t:∃ x y,f x≠f y) (w:∀ s,HCS n f s->gs.length<=s) :MinClean n f gs o:=by
 have v:∀ gs' o',yq n gs'->o' < n+gs'.length->(∀ x,e3 gs' n o' x=f x) ->
    gs.length<=gs'.length:=by
   intro gs' o' hcl' ho' hev';apply w gs'.length
   exact ⟨⟨gs',o'⟩,fun g z=>(ja hcl' g z).1,le_refl _,hev'⟩
 refine ⟨hcl,ho,hev,?_,?_,?_⟩
 . intro p b;by_contra h0;obtain ⟨g0,d⟩ : ∃ g0,gs[p]?=some g0:=⟨gs[p],lGEQ b⟩;obtain ⟨e,h,i,j⟩:=aw gs p g0 d;subst j;subst i;obtain ⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f e h g0 o hcl ho hev t (inl false) trivial (Or.inr h0)
   have:=v gs' o' hcl' ho' hev';simp at this;omega
 . intro p b c h1;obtain ⟨g0,d⟩ : ∃ g0,gs[p]?=some g0:=⟨gs[p],lGEQ b⟩;obtain ⟨e,h,i,j⟩:=aw gs p g0 d;subst j;subst i;obtain ⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f e h g0 o hcl ho hev t (inl c) trivial (Or.inl fun x=>by rw [h1];rfl)
   have:=v gs' o' hcl' ho' hev';simp at this;omega
 . intro p b u hu h2;obtain ⟨g0,d⟩ : ∃ g0,gs[p]?=some g0:=⟨gs[p],lGEQ b⟩;obtain ⟨e,h,i,j⟩:=aw gs p g0 d;subst j;subst i;obtain ⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f e h g0 o hcl ho hev t (inr u) hu
     (Or.inl fun x=>by
      rw [h2];unfold e3;rw [zd,ve _ _ _ (by rw [qu];simp;omega)];rfl)
   have:=v gs' o' hcl' ho' hev';simp at this;omega
def u0 (m:Nat) (gs:U) (init:List e8) (p:Nat):List e8×U:=
 u2 m (gs.take p) (init,[])
lemma tc (m:Nat) (gs:U) (init:List e8) (p:Nat) (b:p<=gs.length) :(u0 m gs init p).1.length=init.length+p:=by unfold u0;rw [fs,lLT,Nat.min_eq_left b]
lemma b8 (m:Nat) (gs:U) (init:List e8) (p:Nat) (g:G) (b:gs[p]?=some g) :u0 m gs init (p+1)=qa m (u0 m gs init p) g:=by unfold u0;have c:p < gs.length:=(lGES.1 b).1;have d:gs[p]=g:=(lGES.1 b).2;rw [List.take_succ_eq_append_getElem c,d,jz,k4];rfl
lemma ev (m:Nat) (gs:U) (init:List e8) (p:Nat) :u2 m (gs.drop p) (u0 m gs init p)=u2 m gs (init,[]):=by unfold u0;rw [<- jz,List.take_append_drop]
lemma eb {m:Nat} {gs:U} {o p u:Nat} (init:List e8) (b:(F m)->(F 8)) {d:u7 m} (e:MinClean 8 fG gs o) (hinit_len:init.length=8) (v:∀ x,ej m (ofFn x) (ofFn (b x)) (init,[])) (i:∀ x,fG (b x)=d x) (w:∃ x y,d x≠d y) (z:p<=gs.length) (h0:u∈liveList gs 8 o p) {c:Q} (h1:(u0 m gs init p).1.getD u (inl false)=inl c) :∃ q,p<=q/\∃ g',gs[q]?=some g'/\u∈g'.inputs:=by
 have ⟨hlt,hl⟩:=(qw gs 8 o p u).1 h0;rcases hl with rfl|⟨q,hq,g',h',h2,_⟩
 . exfalso;have hfl:=tc m gs init p z;have h3:(u2 m gs (init,[])).1.getD u (inl false)=inl c:=by
    rw [<- ev m gs init p,wy m u _ _ _ (by omega)];exact h1
   have j:∀ x,ej m (ofFn x) (q3 gs (ofFn (b x))) (u2 m gs (init,[])):=
    fun x=>j7 m _ (by simp) gs _ _ (fun g h=>(ja e.hcl g h).1) (v x)
   obtain ⟨x,y,h4⟩:=w;apply h4
   have s:=(((j x).2 u).2.trans (e.hev _)).trans (i x);have t:=(((j y).2 u).2.trans (e.hev _)).trans (i y);rw [h3] at s t;exact s.symm.trans t
 . exact ⟨q,hq,g',h',h2⟩
lemma e5 {m:Nat} {gs:U} {init:List e8} {p:Nat} {g:G} (b:gs[p]?=some g) (d:tq g) {u:Nat} (e:u∈g.inputs) {c:Q} (h:(u0 m gs init p).1.getD u (inl false)=inl c) :(u0 m gs init (p+1)).2.length=(u0 m gs init p).2.length:=by rw [b8 m gs init p g b];exact vs m _ g d u e c h
lemma k2 {m:Nat} {gs:U} {init:List e8} {p:Nat} {g:G} (b:gs[p]?=some g) :(u0 m gs init (p+1)).2.length<=(u0 m gs init p).2.length+1:=by
 rw [b8 m gs init p g b];simp only [qa,lLA]
 have:=y2 (qg g.op (m+(u0 m gs init p).2.length)
  (g.inputs.map fun i=>(u0 m gs init p).1.getD i (inl false))).1
 omega
lemma ox (m:Nat) (gs:U) (init:List e8) :∀ k≤ gs.length, (u0 m gs init k).2.length + ((range k).filter (fun q=>decide ((u0 m gs init (q+1)).2.length=(u0 m gs init q).2.length))).length=k:=by
 intro k;induction k with
 | zero=>intro _;simp [u0,u2]
 | succ k ih =>
  intro hk;have hih:=ih (by omega);have d:k < gs.length:=by omega
  obtain ⟨g,b⟩ : ∃ g,gs[k]?=some g:=⟨gs[k],lGEQ d⟩;have hstep_le:=k2 (m:=m) (init:=init) b;have hstep_ge:(u0 m gs init k).2.length<=(u0 m gs init (k+1)).2.length:=by rw [b8 m gs init k g b];simp [qa]
  rw [List.range_succ,List.filter_append,lLA];simp only [List.filter_cons,List.filter_nil];by_cases c:(u0 m gs init (k+1)).2.length=(u0 m gs init k).2.length
  . simp only [c,decide_true,↓reduceIte,List.length_singleton];omega
  . simp only [c,decide_false,bFT,↓reduceIte,lLN];omega
lemma e7 {m:Nat} {gs:U} {init:List e8} (S:M) (g:S.Nodup) (h:∀ q∈S,q < gs.length/\(u0 m gs init (q+1)).2.length=(u0 m gs init q).2.length) :(u2 m gs (init,[])).2.length+S.length<=gs.length:=by
 have i:=ox m gs init gs.length le_rfl;have j:u0 m gs init gs.length=u2 m gs (init,[]):=by unfold u0;rw [List.take_length]
 rw [j] at i;set F:=(range gs.length).filter (fun q=>decide ((u0 m gs init (q+1)).2.length=(u0 m gs init q).2.length))
 have s:∀ q∈S,q∈F:=by intro q t;simp only [F,List.mem_filter,lMRG,decide_eq_true_eq];exact h q t
 have hle:S.length<=F.length:=by
  have u:∀ (A B:M),A.Nodup->(∀ x∈A,x∈B)->A.length<=B.length:=by
   intro A;induction A with
   | nil=>intro _ _ _;simp
   | cons a rest ih =>
    intro B v b;obtain ⟨w,y⟩:=List.nodup_cons.1 v;have z:a∈B:=b a (List.mem_cons_self ..);have c:=List.perm_cons_erase z;have h0:∀ x∈rest,x∈B.erase a:=by
     intro x d;have h3:x≠a:=fun e=>w (e ▸ d)
     have h4:x∈B:=b x (lMCM _ d);exact (lMM.1 (c.mem_iff.1 h4)).resolve_left h3
    have h1:=ih (B.erase a) y h0;have h2:=c.length_eq;simp at h2 ⊢;omega
  exact u S F g s
 omega
lemma g8 {gs:U} {o b:Nat} (d:MinClean 8 fG gs o) (hpg_lt:b < gs.length) (s:∀ x:F 8,x 7=true->e3 gs 8 (8+b) x=true) (B:Nat->Prop) (h0:B 4) (hBpg:¬ B (8+b)) (h3:∀ q < gs.length,∀ g,gs[q]?=some g -> (∃ u∈g.inputs,B u)->q=b\/B (8+q)) (h4:¬ B o):False:=by
 let x0:F 8:=fun i=>i=7
 let x1:F 8:=fun i=>i=7||i=4
 have h5:fG x0=false:=by decide
 have h6:fG x1=true:=by decide
 have h7:∀ p≤ gs.length,∀ i < 8+p,¬ B i ->
   (q3 (gs.take p) (ofFn x0)).getD i false =
   (q3 (gs.take p) (ofFn x1)).getD i false:=by
  intro p;induction p with
  | zero =>
   intro _ i hi e;simp only [List.take_zero,q3,List.foldl_nil];have hne4:i≠4:=fun h=>e (h ▸ h0)
   interval_cases i<;>simp [x0,x1] at *
  | succ p ih =>
   intro hp i hi e;have j:p < gs.length:=by omega
   have t:gs.take (p+1)=gs.take p++[gs[p]]:=List.take_succ_eq_append_getElem j;rw [t,zd,zd];have h8:(q3 (gs.take p) (ofFn x0)).length=8+p:=by rw [qu];simp [lLT,Nat.min_eq_left (by omega:p<=gs.length)]
   have h9:(q3 (gs.take p) (ofFn x1)).length=8+p:=by rw [qu];simp [lLT,Nat.min_eq_left (by omega:p<=gs.length)]
   by_cases x2:i=8+p
   . subst x2;by_cases v:p=b
     . subst v;have w:(q3 (gs.take (p+1)) (ofFn x0)).getD (8+p) false=e3 gs 8 (8+p) x0:=by
        unfold e3;conv_rhs=>rw [<- List.take_append_drop (p+1) gs,zd]
        symm;exact ve (gs.drop (p+1)) _ (8+p) (by rw [qu];simp [lLT,Nat.min_eq_left (by omega:p+1<=gs.length)])
       have y:(q3 (gs.take (p+1)) (ofFn x1)).getD (8+p) false=e3 gs 8 (8+p) x1:=by
        unfold e3;conv_rhs=>rw [<- List.take_append_drop (p+1) gs,zd]
        symm;exact ve (gs.drop (p+1)) _ (8+p) (by rw [qu];simp [lLT,Nat.min_eq_left (by omega:p+1<=gs.length)])
       rw [t,zd] at w y;rw [w,y,s x0 (by decide),s x1 (by decide)]
     . show (q3 (gs.take p) (ofFn x0)++[_]).getD (8+p) false =
           (q3 (gs.take p) (ofFn x1)++[_]).getD (8+p) false
       rw [z2 _ _ _ _ h8,z2 _ _ _ _ h9];congr 1
       apply lMCL
       intro u z;have x3:u < 8+p:=j2 (d.hcl p gs[p] (lGEQ j)) u z;have a1:¬ B u:=by
        intro a2;rcases h3 p j gs[p] (lGEQ j) ⟨u,z,a2⟩ with c|h2
        . exact v c
        . exact e h2
       exact ih (by omega) u x3 a1
   . show (q3 (gs.take p) (ofFn x0)++[_]).getD i false =
          (q3 (gs.take p) (ofFn x1)++[_]).getD i false
     rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)];exact ih (by omega) i (by omega) e
 have c:=h7 gs.length le_rfl o d.ho h4;rw [List.take_length] at c;have e0:e3 gs 8 o x0=fG x0:=d.hev x0;have e1:e3 gs 8 o x1=fG x1:=d.hev x1;unfold e3 at e0 e1;rw [e0,e1,h5,h6] at c;cases c
lemma u6 {m:Nat} {gs:U} {init:List e8} {p q a:Nat} (b:p<=q) (hq:q<=gs.length) (c:a < init.length+p) :(u0 m gs init q).1.getD a (inl false)=(u0 m gs init p).1.getD a (inl false):=by
 have d:(gs.take q).take p=gs.take p:=by rw [List.take_take,Nat.min_eq_left b]
 have e:gs.take q=gs.take p++(gs.take q).drop p:=by rw [<- d];exact (List.take_append_drop p (gs.take q)).symm
 unfold u0;conv_lhs=>rw [e,jz]
 apply wy
 rw [fs,lLT,Nat.min_eq_left (by omega)];exact c
lemma u5 {m:Nat} {gs:U} {init:List e8} {p:Nat} {g:G} (c:init.length=8) (b:gs[p]?=some g) :(u0 m gs init (p+1)).1.getD (8+p) (inl false) = (qg g.op (m+(u0 m gs init p).2.length) (g.inputs.map fun i=>(u0 m gs init p).1.getD i (inl false))).2:=by
 have hlt:p < gs.length:=(lGES.1 b).1;rw [b8 m gs init p g b];simp only [qa];have d:(u0 m gs init p).1.length=8+p:=by rw [tc m gs init p (by omega),c]
 rw [z2 _ _ _ _ d]
lemma mr (b:Nat) (c:Q) :(qg GateOp.not b [inl c]).2=inl (!c):=rfl
lemma s3 (b:Nat) (s:e8) :(qg GateOp.and b [inl false,s]).2=inl false:=by cases s<;>rfl
lemma d9 (c:Nat) (s:e8) :(qg GateOp.and c [s,inl false]).2=inl false:=by cases s with|inl b=>cases b<;>rfl|inr _=>rfl
lemma i9 (b:Nat) (c:Q) :(qg GateOp.and b [inl true,inl c]).2=inl c /\ (qg GateOp.and b [inl c,inl true]).2=inl c:=by cases c<;>exact ⟨rfl,rfl⟩
lemma n0 (c:Nat) (s:e8) :(qg GateOp.or c [inl true,s]).2=inl true:=by cases s with|inl b=>cases b<;>rfl|inr _=>rfl
lemma l9 (c:Nat) (s:e8) :(qg GateOp.or c [s,inl true]).2=inl true:=by cases s with|inl b=>cases b<;>rfl|inr _=>rfl
lemma dt (b:Nat) :(qg GateOp.or b [inl false,inl false]).2=inl false:=rfl
lemma u8 {m:Nat} {gs:U} {o p u:Nat} (init:List e8) (d:(F m)->(F 8)) {e:u7 m} (h:MinClean 8 fG gs o) (v:init.length=8) (w:∀ x,ej m (ofFn x) (ofFn (d x)) (init,[])) (z:∀ x,fG (d x)=e x) (h0:∃ x y,e x≠e y) (hp:p<=gs.length) (i:u∈liveList gs 8 o p) {c:Q} (j:(u0 m gs init p).1.getD u (inl false)=inl c) :∃ q,p<=q/\q < gs.length/\∃ g',gs[q]?=some g'/\u∈g'.inputs /\ (u0 m gs init (q+1)).2.length=(u0 m gs init q).2.length:=by
 obtain ⟨q,s,g',b',t⟩:=eb init d h v w z h0 hp i j;have h1:q < gs.length:=(lGES.1 b').1;have hult:u < 8+p:=((qw gs 8 o p u).1 i).1;have h2:(u0 m gs init q).1.getD u (inl false)=inl c:=by rw [u6 s (by omega) (by omega)];exact j
 exact ⟨q,s,h1,g',b',t,e5 b' (w5 (h.hcl q g' b')) t h2⟩
lemma o4 {n:Nat} {f:u7 n} {gs:U} {o p:Nat} (b:MinClean n f gs o) (c:p < gs.length) :n+p∈liveList gs n o (p+1):=by obtain ⟨g,d⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],lGEQ c⟩;exact (ip n gs o b.hcl p g d (b.hreach p c) (n+p)).2 (Or.inl rfl)
lemma n2 {gs:U} {o:Nat} (b:MinClean 8 fG gs o) (v:Fin 8) (c:∃ x:F 8,fG (update x v (!x v))≠fG x) :(v:Nat)∈liveList gs 8 o 0:=
 be b.hev v c
structure StructG (gs:U) (o:Nat):Type where
 hlen:gs.length=13
 pg:Nat
 pr:Nat
 pw:Nat
 caseA:Q
 hpg_lt:pg < 13
 hpr_lt:pr < 13
 hpw_lt:pw < 13
 hpg_pr:pg < pr
 hpw_ne_pg:pw≠pg
 hpw_ne_pr:pw≠pr
 hcaseA_lt:caseA=true->pr < pw
 ho_ne_7:o≠7
 ho_ne_4:o≠4
 ho_ne_pg:o≠8+pg
 ho_ne_pr:caseA=true->o≠8+pr
 h7_read:∀ q g,gs[q]?=some g->(7:Nat)∈g.inputs->q=pg
 hpg_or:∃ g h,gs[pg]?=some g/\g.op=GateOp.or/\(g.inputs=[7,h]\/g.inputs=[h,7])/\h≠7/\h≠4
 hpg_read:∀ q g,gs[q]?=some g->8+pg∈g.inputs->q=pr
 hpr_and:∃ g u,gs[pr]?=some g/\g.op=GateOp.and/\(g.inputs=[8+pg,u]\/g.inputs=[u,8+pg])/\u≠8+pg/\(caseA=true↔u=4)
 h4_read:∀ q g,gs[q]?=some g->(4:Nat)∈g.inputs->q=if caseA then pr else pw
 hpr_read:caseA=true->∀ q g,gs[q]?=some g->8+pr∈g.inputs->q=pw
 hpw_or:∃ g v,gs[pw]?=some g/\g.op=GateOp.or /\
  (let src:=if caseA then 8+pr else 4
   (g.inputs=[src,v]\/g.inputs=[v,src])/\v≠src)
 h10_len:(u2 6 gs (u3,[])).2.length=10
 h10_elim_iff:∀ q < 13,
  (u0 6 gs u3 (q+1)).2.length=(u0 6 gs u3 q).2.length↔(q=pg\/q=pr\/q=pw)
 h10_7:∀ p≤ 13,(u0 6 gs u3 p).1.getD 7 (inl false)=inl true
 h10_4:∀ p≤ 13,(u0 6 gs u3 p).1.getD 4 (inl false)=inl false
 h10_pg:∀ p≤ 13,pg < p->(u0 6 gs u3 p).1.getD (8+pg) (inl false)=inl true
 h10_pr:caseA=true->∀ p≤ 13,pr < p->(u0 6 gs u3 p).1.getD (8+pr) (inl false)=inl false
 o0:Nat
 ho0:(u2 6 gs (u3,[])).1.getD o (inl false)=inr o0
 hm0:MinClean 6 f7 (u2 6 gs (u3,[])).2 o0
lemma oy {gs:U} {o:Nat} (e:MinClean 8 fG gs o) (hle:gs.length<=13) :Nonempty (StructG gs o):=by
 have hlb_70:12<=(u2 7 gs (i2,[])).2.length:=
  (o9 i2 i5 e.hcl e.hev p0 l0 ur lb20).2
 have hlb_71:11<=(u2 8 gs (t8,[])).2.length:=
  (o9 t8 (fun x=>update x 7 true) e.hcl e.hev p6
    (fun _=>rfl) ⟨fun _=>false,fun _=>true,by decide⟩ te).2
 have b1:=o9 u3 m8 e.hcl e.hev m9 f3 i6 lb7;have h33:=o9 a7 y6 e.hcl e.hev og ea i6 lb7;have h56:(7:Nat)∈liveList gs 8 o 0:=
  n2 e 7 ⟨fun i=>i=4,by decide⟩
 have h57:(u0 7 gs i2 0).1.getD 7 (inl false)=inl false:=rfl;obtain ⟨pg,_,h4,gg,h5,hb,h20⟩:=
  u8 i2 i5 e rfl p0 l0 ur (by omega) h56 h57
 have h34:gs.length=13:=by
  have h3:=e7 (m:=7) (init:=i2) [pg] (by simp) (fun x b=>by simp at b;subst b;exact ⟨h4,h20⟩)
  simp at h3;omega
 have hpg_lt:pg < 13:=by omega
 have ho_ne_7:o≠7:=by
  intro h7;have hno:=(o9 i2 i5 e.hcl e.hev p0 l0 ur lb20).1 false;have hr:(u2 7 gs (i2,[])).1.getD 7 (inl false)=inl false:=by
    have:=u6 (m:=7) (gs:=gs) (init:=i2) (p:=0) (q:=gs.length) (a:=7) (by omega) le_rfl (by simp [i2])
    unfold u0 at this;rw [List.take_length] at this;exact this
  exact hno (h7 ▸ hr)
 have h7_read:∀ q g,gs[q]?=some g->(7:Nat)∈g.inputs->q=pg:=by
  intro q g z h7q;by_contra hne;have a2:q < gs.length:=(lGES.1 z).1;have hq7:(u0 7 gs i2 q).1.getD 7 (inl false)=inl false:=
    u6 (p:=0) (by omega) (by omega) (by simp [i2])
  have x3:=e5 z (w5 (e.hcl q g z)) h7q hq7;have h3:=e7 (m:=7) (init:=i2) [pg,q] (by simp [Ne.symm hne])
    (by
        intro x b;rcases lMM.1 b with rfl|b
        . exact ⟨h4,h20⟩
        . simp at b;subst b;exact ⟨a2,x3⟩)
  simp at h3;omega
 have h58:∃ h,gg.op=GateOp.or/\(gg.inputs=[7,h]\/gg.inputs=[h,7])/\h≠7:=by
  have h21:(u0 7 gs i2 pg).1.getD 7 (inl false)=inl false:=
    u6 (p:=0) (by omega) (by omega) (by simp [i2])
  have h12:∀ c:Q,(u0 7 gs i2 (pg+1)).1.getD (8+pg) (inl false)≠inl c:=by
    intro c hc;have h59:8+pg∈liveList gs 8 o (pg+1):=o4 e h4;obtain ⟨q,h60,a2,gq,hy,hd,x3⟩:=
      u8 i2 i5 e rfl p0 l0 ur (by omega) h59 hc
    have h3:=e7 (m:=7) (init:=i2) [pg,q] (by simp;omega)
      (by
          intro x b;rcases lMM.1 b with rfl|b
          . exact ⟨h4,h20⟩
          . simp at b;subst b;exact ⟨a2,x3⟩)
    simp at h3;omega
  rcases e.hcl pg gg h5 with ⟨t,j,hj,d⟩|⟨t,j,k,hj,hk,d⟩
  . have hj7:j=7:=by simp [d] at hb;exact hb.symm
    exfalso;apply h12 true
    have h0:=u5 (m:=7) (init:=i2) rfl h5;rw [h0,t,d,hj7];simp only [lMC,lMN,h21];rfl
  . have hjk:j≠k:=by
      intro h7;subst h7;apply e.hndup pg h4 j hj
      funext x;rw [oa 8 gs pg gg h5 (j2 (e.hcl pg gg h5)) x,d];rcases t with t|t<;>rw [t]<;>simp [GateOp.eval]
    rcases t with t|t
    . exfalso;apply h12 false
      have h0:=u5 (m:=7) (init:=i2) rfl h5;rw [h0,t,d];simp only [lMC,lMN];rw [d] at hb;simp only [lMM,lNMN,or_false] at hb;rcases hb with w|w
      . rw [<- w,h21];exact s3 _ _
      . rw [<- w,h21];exact d9 _ _
    . rw [d] at hb;simp only [lMM,lNMN,or_false] at hb;rcases hb with w|w
      . exact ⟨k,t,Or.inl (by rw [w];exact d),by omega⟩
      . exact ⟨j,t,Or.inr (by rw [w];exact d),by omega⟩
 obtain ⟨h35,hz,hv,h61⟩:=h58;have h36:(u0 8 gs t8 (pg+1)).2.length=(u0 8 gs t8 pg).2.length:=by
  have h7p:(u0 8 gs t8 pg).1.getD 7 (inl false)=inl true:=
    u6 (p:=0) (by omega) (by omega) (by simp [t8])
  exact e5 h5 (w5 (e.hcl pg gg h5)) hb h7p
 have h17:(u0 8 gs t8 (pg+1)).1.getD (8+pg) (inl false)=inl true:=by
  have h7p:(u0 8 gs t8 pg).1.getD 7 (inl false)=inl true:=
    u6 (p:=0) (by omega) (by omega) (by simp [t8])
  have h0:=u5 (m:=8) (init:=t8) rfl h5;rw [h0,hz];rcases hv with d|d<;>rw [d]<;>simp only [lMC,lMN,h7p]
  . exact n0 _ _
  . exact l9 _ _
 have h22:∃ x y:F 8,fG (update x 7 true)≠fG (update y 7 true):=
  ⟨fun _=>false,fun _=>true,by decide⟩
 obtain ⟨pr,hpr_ge,h8,gr,h9,he,h37⟩:=
  u8 t8 (fun x=>update x 7 true) e rfl p6 (fun _=>rfl) h22
    (by omega) (o4 e h4) h17
 have hpr_lt:pr < 13:=by omega
 have hpg_pr:pg < pr:=by omega
 have ho_ne_pg:o≠8+pg:=by
  intro h7;have hno:=(o9 t8 (fun x=>update x 7 true) e.hcl e.hev p6
    (fun _=>rfl) h22 te).1 true
  have hr:(u2 8 gs (t8,[])).1.getD (8+pg) (inl false)=inl true:=by
    have:=u6 (m:=8) (gs:=gs) (init:=t8) (p:=pg+1) (q:=gs.length)
      (a:=8+pg) (by omega) le_rfl (by simp [t8])
    unfold u0 at this;rw [List.take_length] at this;rw [this];exact h17
  exact hno (h7 ▸ hr)
 have hpg_read:∀ q g,gs[q]?=some g->8+pg∈g.inputs->q=pr:=by
  intro q g z hd;by_contra hne;have a2:q < gs.length:=(lGES.1 z).1;have h38:pg < q:=by have:=j2 (e.hcl q g z) (8+pg) hd;omega
  have hcq:(u0 8 gs t8 q).1.getD (8+pg) (inl false)=inl true:=by rw [u6 (p:=pg+1) (by omega) (by omega) (by simp [t8])];exact h17
  have x3:=e5 z (w5 (e.hcl q g z)) hd hcq;have h3:=e7 (m:=8) (init:=t8) [pg,pr,q]
    (by simp;omega)
    (by
        intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,h36⟩
        rcases lMM.1 b with rfl|b;. exact ⟨h8,h37⟩
        simp at b;subst b;exact ⟨a2,x3⟩)
  simp at h3;omega
 have h62:∃ u,gr.op=GateOp.and/\(gr.inputs=[8+pg,u]\/gr.inputs=[u,8+pg])/\u≠8+pg:=by
  have hw:(u0 8 gs t8 pr).1.getD (8+pg) (inl false)=inl true:=by rw [u6 (p:=pg+1) (by omega) (by omega) (by simp [t8])];exact h17
  have h12:∀ c:Q,(u0 8 gs t8 (pr+1)).1.getD (8+pr) (inl false)≠inl c:=by
    intro c hc;obtain ⟨q,h60,a2,gq,hy,hd,x3⟩:=
      u8 t8 (fun x=>update x 7 true) e rfl p6 (fun _=>rfl) h22
        (by omega) (o4 e h8) hc
    have h3:=e7 (m:=8) (init:=t8) [pg,pr,q] (by simp;omega)
      (by
          intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,h36⟩
          rcases lMM.1 b with rfl|b;. exact ⟨h8,h37⟩
          simp at b;subst b;exact ⟨a2,x3⟩)
    simp at h3;omega
  rcases e.hcl pr gr h9 with ⟨t,j,hj,d⟩|⟨t,j,k,hj,hk,d⟩
  . have h23:j=8+pg:=by simp [d] at he;exact he.symm
    exfalso;apply h12 false
    have h0:=u5 (m:=8) (init:=t8) rfl h9;rw [h0,t,d,h23];simp only [lMC,lMN,hw];rfl
  . have hjk:j≠k:=by
      intro h7;subst h7;apply e.hndup pr h8 j hj
      funext x;rw [oa 8 gs pr gr h9 (j2 (e.hcl pr gr h9)) x,d];rcases t with t|t<;>rw [t]<;>simp [GateOp.eval]
    rcases t with t|t
    . rw [d] at he;simp only [lMM,lNMN,or_false] at he;rcases he with w|w
      . exact ⟨k,t,Or.inl (by rw [w];exact d),by omega⟩
      . exact ⟨j,t,Or.inr (by rw [w];exact d),by omega⟩
    . exfalso;apply h12 true
      have h0:=u5 (m:=8) (init:=t8) rfl h9;rw [h0,t,d];simp only [lMC,lMN];rw [d] at he;simp only [lMM,lNMN,or_false] at he;rcases he with w|w
      . rw [<- w,hw];exact n0 _ _
      . rw [<- w,hw];exact l9 _ _
 obtain ⟨h13,h14,ht,h63⟩:=h62;have h39:∀ x:F 8,x 7=true->e3 gs 8 (8+pg) x=true:=by
  intro x hx7;rw [oa 8 gs pg gg h5 (j2 (e.hcl pg gg h5)) x,hz];have hv7:e3 gs 8 7 x=true:=by unfold e3;rw [ve _ _ _ (by simp)];simp [hx7]
  rcases hv with d|d<;>rw [d]<;>simp [GateOp.eval,hv7]
 have ho_ne_4:o≠4:=by
  intro h7;have hr:(u2 6 gs (u3,[])).1.getD 4 (inl false)=inl false:=by
    have:=u6 (m:=6) (gs:=gs) (init:=u3) (p:=0) (q:=gs.length) (a:=4) (by omega) le_rfl (by simp [u3])
    unfold u0 at this;rw [List.take_length] at this;exact this
  exact b1.1 false (h7 ▸ hr)
 have h24:h35≠4:=by
  intro h64;subst h64;have h40:(u0 6 gs a7 pg).1.getD 7 (inl false)=inl false:=
    u6 (p:=0) (by omega) (by omega) (by simp [a7])
  have h18:∀ p≤ 13,(u0 6 gs a7 p).1.getD 4 (inl false)=inl false:=
    fun p hp=>u6 (p:=0) (by omega) (by omega) (by simp [a7])
  have h41:(u0 6 gs a7 (pg+1)).2.length=(u0 6 gs a7 pg).2.length:=
    e5 h5 (w5 (e.hcl pg gg h5)) hb h40
  have h65:(u0 6 gs a7 (pg+1)).1.getD (8+pg) (inl false)=inl false:=by have h0:=u5 (m:=6) (init:=a7) rfl h5;rw [h0,hz];rcases hv with d|d<;>rw [d]<;>simp only [lMC,lMN,h40,h18 pg (by omega)]<;>rfl
  have h42:(u0 6 gs a7 pr).1.getD (8+pg) (inl false)=inl false:=by rw [u6 (p:=pg+1) (by omega) (by omega) (by simp [a7])];exact h65
  have h43:(u0 6 gs a7 (pr+1)).2.length=(u0 6 gs a7 pr).2.length:=
    e5 h9 (w5 (e.hcl pr gr h9)) he h42
  have h44:(u0 6 gs a7 (pr+1)).1.getD (8+pr) (inl false)=inl false:=by
    have h0:=u5 (m:=6) (init:=a7) rfl h9;rw [h0,h14];rcases ht with d|d<;>rw [d]<;>simp only [lMC,lMN,h42]
    . exact s3 _ _
    . exact d9 _ _
  obtain ⟨q3,hq3_ge,h25,g3,hg3,xi,h45⟩:=
    u8 a7 y6 e rfl og ea i6
      (by omega) (o4 e h8) h44
  have h66:∃ q4 < 13,q4≠pg/\∃ g4,gs[q4]?=some g4/\(4:Nat)∈g4.inputs:=by
    by_contra h46;push Not at h46
    apply g8 e h4 h39 (fun i=>i=4) rfl (by omega) _ ho_ne_4
    intro q hq g z ⟨u,hu,hbu⟩;subst hbu;by_cases xs:q=pg
    . exact Or.inl xs
    . exact absurd hu (h46 q (by omega) xs g z)
  obtain ⟨q4,h10,hq4_ne_pg,g4,hg4,hs⟩:=h66;have hq4_ne_pr:q4≠pr:=by
    intro h7;rw [h7,h9] at hg4;cases hg4
    have hu4:h13=4:=by rcases ht with d|d<;>rw [d] at hs<;>simp only [lMM,lNMN,or_false] at hs<;>omega
    apply e.hndup pr h8 4 (by omega)
    funext x;have h67:e3 gs 8 (8+pg) x=(e3 gs 8 7 x||e3 gs 8 4 x):=by rw [oa 8 gs pg gg h5 (j2 (e.hcl pg gg h5)) x,hz];rcases hv with d|d<;>rw [d]<;>simp [GateOp.eval,Bool.or_comm]
    rw [oa 8 gs pr gr h9 (j2 (e.hcl pr gr h9)) x,h14];rcases ht with d|d<;>rw [d,hu4] <;>
      (simp only [lMC,lMN,GateOp.eval,h67];cases e3 gs 8 7 x<;>cases e3 gs 8 4 x<;>rfl)
  have h68:(u0 6 gs a7 (q4+1)).2.length=(u0 6 gs a7 q4).2.length:=
    e5 hg4 (w5 (e.hcl q4 g4 hg4)) hs (h18 q4 (by omega))
  by_cases h69:q4=q3
  . subst h69;rw [hg3] at hg4;cases hg4
    have h47:(u0 6 gs a7 q4).1.getD (8+pr) (inl false)=inl false:=by rw [u6 (p:=pr+1) (by omega) (by omega) (by simp [a7])];exact h44
    have h70:(u0 6 gs a7 (q4+1)).1.getD (8+q4) (inl false)=inl false:=by
      have h0:=u5 (m:=6) (init:=a7) rfl hg3;rw [h0];rcases e.hcl q4 g3 hg3 with ⟨t,j,_,d⟩|⟨t,j,k,_,_,d⟩
      . rw [d] at xi hs;simp at xi hs;omega
      . rw [d] at xi hs;simp only [lMM,lNMN,or_false] at xi hs;have hjb:(u0 6 gs a7 q4).1.getD j (inl false)=inl false:=by
          rcases xi with w|w
          . rw [<- w];exact h47
          . rcases hs with h2|h2
            . rw [<- h2];exact h18 q4 (by omega)
            . omega
        have hkb:(u0 6 gs a7 q4).1.getD k (inl false)=inl false:=by
          rcases xi with w|w
          . rcases hs with h2|h2
            . omega
            . rw [<- h2];exact h18 q4 (by omega)
          . rw [<- w];exact h47
        rw [d];simp only [lMC,lMN,hjb,hkb];rcases t with t|t<;>rw [t]<;>rfl
    obtain ⟨q5,hq5_ge,h71,_,_,_,h72⟩:=
      u8 a7 y6 e rfl og ea i6
        (by omega) (o4 e h25) h70
    have h3:=e7 (m:=6) (init:=a7) [pg,pr,q4,q5] (by simp;omega)
      (by
          intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,h41⟩
          rcases lMM.1 b with rfl|b;. exact ⟨h8,h43⟩
          rcases lMM.1 b with rfl|b;. exact ⟨h25,h45⟩
          simp at b;subst b;exact ⟨h71,h72⟩)
    have:=h33.2;simp at h3;omega
  . have h3:=e7 (m:=6) (init:=a7) [pg,pr,q3,q4] (by simp;omega)
      (by
          intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,h41⟩
          rcases lMM.1 b with rfl|b;. exact ⟨h8,h43⟩
          rcases lMM.1 b with rfl|b;. exact ⟨h25,h45⟩
          simp at b;subst b;exact ⟨by omega,h68⟩)
    have:=h33.2;simp at h3;omega
 have h10_7:∀ p≤ 13,(u0 6 gs u3 p).1.getD 7 (inl false)=inl true:=
  fun p hp=>u6 (p:=0) (by omega) (by omega) (by simp [u3])
 have h10_4:∀ p≤ 13,(u0 6 gs u3 p).1.getD 4 (inl false)=inl false:=
  fun p hp=>u6 (p:=0) (by omega) (by omega) (by simp [u3])
 have hf:(u0 6 gs u3 (pg+1)).2.length=(u0 6 gs u3 pg).2.length:=
  e5 h5 (w5 (e.hcl pg gg h5)) hb (h10_7 pg (by omega))
 have h73:(u0 6 gs u3 (pg+1)).1.getD (8+pg) (inl false)=inl true:=by
  have h0:=u5 (m:=6) (init:=u3) rfl h5;rw [h0,hz];rcases hv with d|d<;>rw [d]<;>simp only [lMC,lMN,h10_7 pg (by omega)]
  . exact n0 _ _
  . exact l9 _ _
 have h10_pg:∀ p≤ 13,pg < p->(u0 6 gs u3 p).1.getD (8+pg) (inl false)=inl true:=by intro p hp hlt;rw [u6 (p:=pg+1) (by omega) (by omega) (by simp [u3])];exact h73
 have hh:(u0 6 gs u3 (pr+1)).2.length=(u0 6 gs u3 pr).2.length:=
  e5 h9 (w5 (e.hcl pr gr h9)) he (h10_pg pr (by omega) hpg_pr)
 have h26:∀ g,gs[pg]?=some g->(4:Nat) ∉ g.inputs:=by
  intro g z h6;rw [h5] at z;cases z
  rcases hv with d|d<;>rw [d] at h6<;>simp at h6
  . exact h24 h6.symm
  . exact h24 h6.symm
 have h48:∀ (pw:Nat) (caseA:Q),
    pw < 13->pw≠pg->pw≠pr->(caseA=true->pr < pw) ->
    (caseA=true->o≠8+pr) ->
    (caseA=true↔h13=4) ->
    (∀ q g,gs[q]?=some g->(4:Nat)∈g.inputs->q=if caseA then pr else pw) ->
    (caseA=true->∀ q g,gs[q]?=some g->8+pr∈g.inputs->q=pw) ->
    (∃ g v,gs[pw]?=some g/\g.op=GateOp.or /\
      (let src:=if caseA then 8+pr else 4
      (g.inputs=[src,v]\/g.inputs=[v,src])/\v≠src)) ->
    (u0 6 gs u3 (pw+1)).2.length=(u0 6 gs u3 pw).2.length ->
    (caseA=true->∀ p≤ 13,pr < p->(u0 6 gs u3 p).1.getD (8+pr) (inl false)=inl false) ->
    Nonempty (StructG gs o):=by
  intro pw caseA hpw_lt h74 h75 hcaseA_lt ho_ne_pr h76 h11 h27 hpw_or h28 h10_pr;have h77:=e7 (m:=6) (init:=u3) [pg,pr,pw] (by simp;omega)
    (by
        intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
        rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
        simp at b;subst b;exact ⟨by omega,h28⟩)
  have h10_len:(u2 6 gs (u3,[])).2.length=10:=by have:=b1.2;simp at h77;omega
  have h10_elim_iff:∀ q < 13,
      (u0 6 gs u3 (q+1)).2.length=(u0 6 gs u3 q).2.length↔(q=pg\/q=pr\/q=pw):=by
    intro q hq;constructor
    . intro hqe;by_contra h78;push Not at h78
      have h79:=e7 (m:=6) (init:=u3) [pg,pr,pw,q] (by simp;omega)
        (by
            intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
            rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
            rcases lMM.1 b with rfl|b;. exact ⟨by omega,h28⟩
            simp at b;subst b;exact ⟨by omega,hqe⟩)
      simp at h79;omega
    . rintro (rfl|rfl|rfl)
      . exact hf
      . exact hh
      . exact h28
  cases h19:(u2 6 gs (u3,[])).1.getD o (inl false) with
  | inl c=>exact absurd h19 (b1.1 c)
  | inr o0 =>
    have h49:∀ x,ej 6 (ofFn x) (q3 gs (ofFn (m8 x))) (u2 6 gs (u3,[])):=
      fun x=>j7 6 _ (by simp) gs _ _ (fun g hg=>(ja e.hcl g hg).1) (m9 x)
    have h80:o0 < 6+(u2 6 gs (u3,[])).2.length:=by have:=((h49 (fun _=>false)).2 o).1;rw [h19] at this;exact this
    have h81:yq 6 (u2 6 gs (u3,[])).2:=by
      apply bh 6 gs (u3,[]) (fun g hg=>(ja e.hcl g hg).1) _ (fun p g hp=>by simp at hp)
      intro i;exact ((m9 (fun _=>false)).2 i).1
    have h82:∀ x,e3 (u2 6 gs (u3,[])).2 6 o0 x=f7 x:=by
      intro x
      have:=((h49 x).2 o).2.trans ((e.hev (m8 x)).trans (f3 x))
      rw [h19] at this;exact this
    have hm0:MinClean 6 f7 (u2 6 gs (u3,[])).2 o0:=
      od h81 h80 h82 i6 (fun s hc=>by rw [h10_len];exact lb7 s hc)
    exact ⟨⟨h34,pg,pr,pw,caseA,hpg_lt,hpr_lt,hpw_lt,hpg_pr,h74,h75,
            hcaseA_lt,ho_ne_7,ho_ne_4,ho_ne_pg,ho_ne_pr,h7_read,
            ⟨gg,h35,h5,hz,hv,h61,h24⟩,hpg_read,
            ⟨gr,h13,h9,h14,ht,h63,h76⟩,h11,h27,hpw_or,
            h10_len,h10_elim_iff,h10_7,h10_4,h10_pg,h10_pr,o0,h19,hm0⟩⟩
 by_cases hu4:h13=4
 .
  have h50:(u0 6 gs u3 (pr+1)).1.getD (8+pr) (inl false)=inl false:=by
    have h0:=u5 (m:=6) (init:=u3) rfl h9;rw [h0,h14];rcases ht with d|d<;>rw [d,hu4]<;>simp only [lMC,lMN,h10_4 pr (by omega)]
    . exact d9 _ _
    . exact s3 _ _
  have h10_pr:∀ p≤ 13,pr < p->(u0 6 gs u3 p).1.getD (8+pr) (inl false)=inl false:=by intro p hp hlt;rw [u6 (p:=pr+1) (by omega) (by omega) (by simp [u3])];exact h50
  have ho_ne_pr:o≠8+pr:=by
    intro h7;have hr:(u2 6 gs (u3,[])).1.getD (8+pr) (inl false)=inl false:=by
      have:=h10_pr 13 le_rfl (by omega)
      unfold u0 at this;rw [<- h34,List.take_length] at this;exact this
    exact b1.1 false (h7 ▸ hr)
  obtain ⟨pw,hpw_ge,ha,gw,x2,a1,hi⟩:=
    u8 u3 m8 e rfl m9 f3 i6
      (by omega) (o4 e h8) h50
  have hpw_lt:pw < 13:=by omega
  have h27:∀ q g,gs[q]?=some g->8+pr∈g.inputs->q=pw:=by
    intro q g z hd;by_contra hne;have a2:q < gs.length:=(lGES.1 z).1;have h38:pr < q:=by have:=j2 (e.hcl q g z) (8+pr) hd;omega
    have x3:=e5 z (w5 (e.hcl q g z)) hd (h10_pr q (by omega) h38);have h3:=e7 (m:=6) (init:=u3) [pg,pr,pw,q] (by simp;omega)
      (by
          intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
          rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
          rcases lMM.1 b with rfl|b;. exact ⟨ha,hi⟩
          simp at b;subst b;exact ⟨a2,x3⟩)
    have:=b1.2;simp at h3;omega
  have h11:∀ q g,gs[q]?=some g->(4:Nat)∈g.inputs->q=pr:=by
    intro q g z h6;by_contra hne;have a2:q < gs.length:=(lGES.1 z).1;have h83:q≠pg:=fun h=>h26 g (h ▸ z) h6
    have x3:=e5 z (w5 (e.hcl q g z)) h6 (h10_4 q (by omega));by_cases hqw:q=pw
    . rw [hqw,x2] at z;cases z
      have h84:(u0 6 gs u3 (pw+1)).1.getD (8+pw) (inl false)=inl false:=by
        have h0:=u5 (m:=6) (init:=u3) rfl x2;rw [h0];rcases e.hcl pw gw x2 with ⟨t,j,_,d⟩|⟨t,j,k,_,_,d⟩
        . rw [d] at a1 h6;simp at a1 h6;omega
        . rw [d] at a1 h6;simp only [lMM,lNMN,or_false] at a1 h6;have hjb:(u0 6 gs u3 pw).1.getD j (inl false)=inl false:=by
            rcases a1 with w|w
            . rw [<- w];exact h10_pr pw (by omega) (by omega)
            . rcases h6 with h2|h2
              . rw [<- h2];exact h10_4 pw (by omega)
              . omega
          have hkb:(u0 6 gs u3 pw).1.getD k (inl false)=inl false:=by
            rcases a1 with w|w
            . rcases h6 with h2|h2
              . omega
              . rw [<- h2];exact h10_4 pw (by omega)
            . rw [<- w];exact h10_pr pw (by omega) (by omega)
          rw [d];simp only [lMC,lMN,hjb,hkb];rcases t with t|t<;>rw [t]<;>rfl
      obtain ⟨q4,h51,h10,_,_,_,h15⟩:=
        u8 u3 m8 e rfl m9 f3 i6
          (by omega) (o4 e ha) h84
      have h3:=e7 (m:=6) (init:=u3) [pg,pr,pw,q4] (by simp;omega)
        (by
            intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
            rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
            rcases lMM.1 b with rfl|b;. exact ⟨ha,hi⟩
            simp at b;subst b;exact ⟨h10,h15⟩)
      have:=b1.2;simp at h3;omega
    . have h3:=e7 (m:=6) (init:=u3) [pg,pr,pw,q] (by simp;omega)
        (by
            intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
            rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
            rcases lMM.1 b with rfl|b;. exact ⟨ha,hi⟩
            simp at b;subst b;exact ⟨a2,x3⟩)
      have:=b1.2;simp at h3;omega
  have hpw_or:∃ v,gw.op=GateOp.or/\(gw.inputs=[8+pr,v]\/gw.inputs=[v,8+pr])/\v≠8+pr:=by
    have h16:∀ c:Q,(u0 6 gs u3 (pw+1)).1.getD (8+pw) (inl false)≠inl c:=by
      intro c hc;obtain ⟨q4,h51,h10,_,_,_,h15⟩:=
        u8 u3 m8 e rfl m9 f3 i6
          (by omega) (o4 e ha) hc
      have h3:=e7 (m:=6) (init:=u3) [pg,pr,pw,q4] (by simp;omega)
        (by
            intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
            rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
            rcases lMM.1 b with rfl|b;. exact ⟨ha,hi⟩
            simp at b;subst b;exact ⟨h10,h15⟩)
      have:=b1.2;simp at h3;omega
    have hw:=h10_pr pw (by omega) (by omega);rcases e.hcl pw gw x2 with ⟨t,j,_,d⟩|⟨t,j,k,hj,hk,d⟩
    . have h23:j=8+pr:=by simp [d] at a1;exact a1.symm
      exfalso;apply h16 true
      have h0:=u5 (m:=6) (init:=u3) rfl x2;rw [h0,t,d,h23];simp only [lMC,lMN,hw];rfl
    . have hjk:j≠k:=by
        intro h7;subst h7;apply e.hndup pw ha j hj
        funext x;rw [oa 8 gs pw gw x2 (j2 (e.hcl pw gw x2)) x,d];rcases t with t|t<;>rw [t]<;>simp [GateOp.eval]
      rcases t with t|t
      . exfalso;apply h16 false
        have h0:=u5 (m:=6) (init:=u3) rfl x2;rw [h0,t,d];simp only [lMC,lMN];rw [d] at a1;simp only [lMM,lNMN,or_false] at a1;rcases a1 with w|w
        . rw [<- w,hw];exact s3 _ _
        . rw [<- w,hw];exact d9 _ _
      . rw [d] at a1;simp only [lMM,lNMN,or_false] at a1;rcases a1 with w|w
        . exact ⟨k,t,Or.inl (by rw [w];exact d),by omega⟩
        . exact ⟨j,t,Or.inr (by rw [w];exact d),by omega⟩
  obtain ⟨h29,h30,h31,h32⟩:=hpw_or;exact h48 pw true hpw_lt (by omega) (by omega) (fun _=>by omega) (fun _=>ho_ne_pr)
    (by simp [hu4]) (by simpa using h11) (fun _=>h27)
    ⟨gw,h29,x2,h30,h31,h32⟩ hi (fun _=>h10_pr)
 .
  have h52:(4:Nat) ∉ gr.inputs:=by intro h6;rcases ht with d|d<;>rw [d] at h6<;>simp only [lMM,lNMN,or_false] at h6<;>omega
  have h85:(4:Nat)∈liveList gs 8 o 0:=
    n2 e 4 ⟨fun i=>i=7,by decide⟩
  obtain ⟨pw,_,ha,gw,x2,hn,hi⟩:=
    u8 u3 m8 e rfl m9 f3 i6
      (by omega) h85 (h10_4 0 (by omega))
  have hpw_lt:pw < 13:=by omega
  have hpw_ne_pg:pw≠pg:=fun h=>h26 gw (h ▸ x2) hn
  have hpw_ne_pr:pw≠pr:=fun h=>h52 (by rw [h,h9] at x2;cases x2;exact hn)
  have h11:∀ q g,gs[q]?=some g->(4:Nat)∈g.inputs->q=pw:=by
    intro q g z h6;by_contra hne;have a2:q < gs.length:=(lGES.1 z).1;have h83:q≠pg:=fun h=>h26 g (h ▸ z) h6
    have hq_ne_pr:q≠pr:=fun h=>h52 (by rw [h,h9] at z;cases z;exact h6)
    have x3:=e5 z (w5 (e.hcl q g z)) h6 (h10_4 q (by omega));have h3:=e7 (m:=6) (init:=u3) [pg,pr,pw,q] (by simp;omega)
      (by
          intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
          rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
          rcases lMM.1 b with rfl|b;. exact ⟨ha,hi⟩
          simp at b;subst b;exact ⟨a2,x3⟩)
    have:=b1.2;simp at h3;omega
  have hpw_or:∃ v,gw.op=GateOp.or/\(gw.inputs=[4,v]\/gw.inputs=[v,4])/\v≠4:=by
    have h16:∀ c:Q,(u0 6 gs u3 (pw+1)).1.getD (8+pw) (inl false)≠inl c:=by
      intro c hc;have h86:∀ q < 13,pw < q->q≠pg->∀ gq,gs[q]?=some gq->8+pw∈gq.inputs->False:=by
        intro q hq h53 xs gq hy hd;have h54:(u0 6 gs u3 q).1.getD (8+pw) (inl false)=inl c:=by rw [u6 (p:=pw+1) (by omega) (by omega) (by simp [u3])];exact hc
        by_cases h55:q=pr
        . rw [h55,h9] at hy;cases hy
          have h87:h13=8+pw:=by rcases ht with d|d<;>rw [d] at hd<;>simp only [lMM,lNMN,or_false] at hd<;>omega
          have h88:(u0 6 gs u3 (pr+1)).1.getD (8+pr) (inl false)=inl c:=by
            have h0:=u5 (m:=6) (init:=u3) rfl h9;rw [h0,h14];rcases ht with d|d<;>rw [d,h87] <;>
              simp only [lMC,lMN,h10_pg pr (by omega) hpg_pr,h55 ▸ h54]
            . exact (i9 _ c).1
            . exact (i9 _ c).2
          obtain ⟨q4,h51,h10,_,_,_,h15⟩:=
            u8 u3 m8 e rfl m9 f3 i6
              (by omega) (o4 e h8) h88
          have h3:=e7 (m:=6) (init:=u3) [pg,pr,pw,q4] (by simp;omega)
            (by
                intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
                rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
                rcases lMM.1 b with rfl|b;. exact ⟨ha,hi⟩
                simp at b;subst b;exact ⟨h10,h15⟩)
          have:=b1.2;simp at h3;omega
        . have x3:=e5 hy (w5 (e.hcl q gq hy)) hd h54;have h3:=e7 (m:=6) (init:=u3) [pg,pr,pw,q] (by simp;omega)
            (by
                intro x b;rcases lMM.1 b with rfl|b;. exact ⟨h4,hf⟩
                rcases lMM.1 b with rfl|b;. exact ⟨h8,hh⟩
                rcases lMM.1 b with rfl|b;. exact ⟨ha,hi⟩
                simp at b;subst b;exact ⟨by omega,x3⟩)
          have:=b1.2;simp at h3;omega
      have h89:o≠8+pw:=by
        intro h7;have hr:(u2 6 gs (u3,[])).1.getD (8+pw) (inl false)=inl c:=by
          have:=u6 (m:=6) (gs:=gs) (init:=u3) (p:=pw+1) (q:=gs.length)
            (a:=8+pw) (by omega) le_rfl (by simp [u3])
          unfold u0 at this;rw [List.take_length] at this;rw [this];exact hc
        exact b1.1 c (h7 ▸ hr)
      apply g8 e h4 h39 (fun i=>i=4\/i=8+pw)
        (Or.inl rfl) (by omega) _ (by rintro (h|h);exact ho_ne_4 h;exact h89 h)
      intro q hq g z ⟨u,hu,hbu⟩;rcases hbu with rfl|rfl
      . exact Or.inr (Or.inr (by rw [h11 q g z hu]))
      . by_cases xs:q=pg
        . exact Or.inl xs
        . have h53:pw < q:=by have:=j2 (e.hcl q g z) (8+pw) hu;omega
          exact False.elim (h86 q (by omega) h53 xs g z hu)
    have hc4:=h10_4 pw (by omega);rcases e.hcl pw gw x2 with ⟨t,j,_,d⟩|⟨t,j,k,hj,hk,d⟩
    . have hj4:j=4:=by simp [d] at hn;exact hn.symm
      exfalso;apply h16 true
      have h0:=u5 (m:=6) (init:=u3) rfl x2;rw [h0,t,d,hj4];simp only [lMC,lMN,hc4];rfl
    . have hjk:j≠k:=by
        intro h7;subst h7;apply e.hndup pw ha j hj
        funext x;rw [oa 8 gs pw gw x2 (j2 (e.hcl pw gw x2)) x,d];rcases t with t|t<;>rw [t]<;>simp [GateOp.eval]
      rcases t with t|t
      . exfalso;apply h16 false
        have h0:=u5 (m:=6) (init:=u3) rfl x2;rw [h0,t,d];simp only [lMC,lMN];rw [d] at hn;simp only [lMM,lNMN,or_false] at hn;rcases hn with w|w
        . rw [<- w,hc4];exact s3 _ _
        . rw [<- w,hc4];exact d9 _ _
      . rw [d] at hn;simp only [lMM,lNMN,or_false] at hn;rcases hn with w|w
        . exact ⟨k,t,Or.inl (by rw [w];exact d),by omega⟩
        . exact ⟨j,t,Or.inr (by rw [w];exact d),by omega⟩
  obtain ⟨h29,h30,h31,h32⟩:=hpw_or;exact h48 pw false hpw_lt hpw_ne_pg hpw_ne_pr (by simp) (by simp)
    (by simp [hu4]) (by simpa using h11) (by simp)
    ⟨gw,h29,x2,h30,h31,h32⟩ hi (by simp)
lemma ug (op:GateOp) (i:Nat) (e:List e8) (g' : G) (r:e8) (h:qg op i e=(some g',r)) :r=inr i/\∀ b∈g'.inputs,inr b∈e:=by
 cases op with
 | not =>
  match e with
  | []=>simp [qg,wr] at h
  | inl c::tl=>simp [qg,wr] at h
  | inr j::tl => simp only [qg,wr,Prod.mk.injEq,Option.some.injEq] at h;obtain ⟨rfl,rfl⟩:=h;exact ⟨rfl,fun b d=>by simp at d;subst d;simp⟩
 | and =>
  match e with
  | []=>simp [qg,ko] at h
  | [inl _] | [inr _]=>simp [qg,ko] at h
  | [inl _,inl _] | [inl _,inr _] | [inr _,inl _]=>simp [qg,ko] at h
  | [inr j1,inr j2] => simp only [qg,ko,Prod.mk.injEq,Option.some.injEq] at h;obtain ⟨rfl,rfl⟩:=h;exact ⟨rfl,fun b d=>by simp at d;rcases d with rfl|rfl<;>simp⟩
  | _::_::_::_=>simp [qg,ko] at h
 | or =>
  match e with
  | []=>simp [qg,ji] at h
  | [inl _] | [inr _]=>simp [qg,ji] at h
  | [inl _,inl _] | [inl _,inr _] | [inr _,inl _]=>simp [qg,ji] at h
  | [inr j1,inr j2] => simp only [qg,ji,Prod.mk.injEq,Option.some.injEq] at h;obtain ⟨rfl,rfl⟩:=h;exact ⟨rfl,fun b d=>by simp at d;rcases d with rfl|rfl<;>simp⟩
  | _::_::_::_=>simp [qg,ji] at h
 | mod | maj=>simp [qg] at h
lemma tu (op:GateOp) (e:Nat) (d:List e8) (b:Nat) (h:qg op e d=(none,inr b)):inr b∈d:=by
 cases op with
 | not =>
  match d with
  | [] | inl _::_ | inr _::_=>simp [qg,wr] at h
 | and =>
  match d with
  | [] | [inl _] | [inl _,inl _] | [inr _,inr _] | _::_::_::_ => simp [qg,ko] at h
  | [inr j]=>simp [qg,ko] at h;subst h;simp
  | [inl c,inr j]=>cases c<;>simp [qg,ko] at h;subst h;simp
  | [inr j,inl c]=>cases c<;>simp [qg,ko] at h;subst h;simp
 | or =>
  match d with
  | [] | [inl _] | [inl _,inl _] | [inr _,inr _] | _::_::_::_ => simp [qg,ji] at h
  | [inr j]=>simp [qg,ji] at h;subst h;simp
  | [inl c,inr j]=>cases c<;>simp [qg,ji] at h;subst h;simp
  | [inr j,inl c]=>cases c<;>simp [qg,ji] at h;subst h;simp
 | mod | maj=>simp [qg] at h
lemma i3 (m:Nat) (gs:U) (init:List e8) :∀ p≤ gs.length,∃ t,(u2 m gs (init,[])).2=(u0 m gs init p).2++t:=by
 intro p _;have c:=(ev m gs init p).symm;have d:∀ (l:U) (b:List e8×U),∃ t,(u2 m l b).2=b.2++t:=by
  intro l;induction l with
  | nil=>intro b;exact ⟨[],by simp [u2]⟩
  | cons g rest ih =>
   intro b;rw [k4];obtain ⟨t,e⟩:=ih (qa m b g);exact ⟨(qg g.op (m+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1.toList++t,
    by rw [e];simp [qa,lAA]⟩
 rw [c];exact d (gs.drop p) (u0 m gs init p)
lemma k8 (m:Nat) (gs:U) (init:List e8) {p q:Nat} (hpq:p<=q) :(u0 m gs init p).2.length<=(u0 m gs init q).2.length:=by
 induction q with
 | zero =>
  have b:p=0:=by omega
  subst b;exact le_rfl
 | succ q ih =>
  by_cases h:p=q+1
  . subst h;exact le_rfl
  . have c:=ih (by omega);by_cases d:q < gs.length
    . obtain ⟨g,e⟩ : ∃ g,gs[q]?=some g:=⟨gs[q],lGEQ d⟩;have hstep:(u0 m gs init q).2.length<=(u0 m gs init (q+1)).2.length:=by
       rw [b8 m gs init q g e];simp only [qa,lLA];omega
      omega
    . have:gs.take (q+1)=gs.take q:=by
       rw [List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
      have i:u0 m gs init (q+1)=u0 m gs init q:=by unfold u0;rw [this]
      rw [i];exact c
lemma oj {gs:U} {p j:Nat} {y:G} (hp:p<=gs.length) (hj_ge:(u0 6 gs u3 p).2.length<=j) (b:(u2 6 gs (u3,[])).2[j]?=some y) :∃ q,p<=q/\q < gs.length /\ (u0 6 gs u3 q).2.length=j /\ ∃ g,gs[q]?=some g /\ (qg g.op (6+j) (g.inputs.map fun i=>(u0 6 gs u3 q).1.getD i (inl false))).1=some y:=by
 have z:j < (u2 6 gs (u3,[])).2.length:=(lGES.1 b).1;have h0:(u0 6 gs u3 gs.length).2=(u2 6 gs (u3,[])).2:=by unfold u0;rw [List.take_length]
 have h5:∃ q,p<=q/\q < gs.length/\(u0 6 gs u3 q).2.length=j /\
   (u0 6 gs u3 (q+1)).2.length=j+1:=by
  suffices ∀ k,p+k<=gs.length->j < (u0 6 gs u3 (p+k)).2.length ->
     ∃ q,p<=q/\q < p+k/\(u0 6 gs u3 q).2.length=j /\
     (u0 6 gs u3 (q+1)).2.length=j+1 by
   obtain ⟨q,s,h2,u,v⟩:=this (gs.length - p) (by omega)
     (by rw [show p+(gs.length - p)=gs.length by omega,h0];exact z)
   exact ⟨q,s,by omega,u,v⟩
  intro k;induction k with
  | zero=>intro _ c;simp at c;omega
  | succ k ih =>
   intro hpk c;by_cases h6:j < (u0 6 gs u3 (p+k)).2.length
   . obtain ⟨q,s,h2,u,v⟩:=ih (by omega) h6;exact ⟨q,s,by omega,u,v⟩
   . have d:p+k < gs.length:=by omega
     obtain ⟨g,e⟩ : ∃ g,gs[p+k]?=some g:=⟨gs[p+k],lGEQ d⟩;have hle:=k2 (m:=6) (init:=u3) e;have c' : j < (u0 6 gs u3 (p+k+1)).2.length:=by simpa [nAA] using c
     have h7:(u0 6 gs u3 (p+k)).2.length=j:=by omega
     have h8:(u0 6 gs u3 (p+k+1)).2.length=j+1:=by omega
     exact ⟨p+k,by omega,by omega,h7,h8⟩
 obtain ⟨q,h9,d,w,h⟩:=h5;obtain ⟨g,e⟩ : ∃ g,gs[q]?=some g:=⟨gs[q],lGEQ d⟩;refine ⟨q,h9,d,w,g,e,?_⟩
 have x2:=b8 6 gs u3 q g e;obtain ⟨t,ht⟩:=i3 6 gs u3 (q+1) (by omega);rw [ht,List.getElem?_append_left (by omega)] at b;rw [x2] at b h;simp only [qa] at b h;cases x:(qg g.op (6+(u0 6 gs u3 q).2.length)
   (g.inputs.map fun i=>(u0 6 gs u3 q).1.getD i (inl false))).1 with
 | none => rw [x] at h;simp at h;omega
 | some g' => rw [x] at b;rw [List.getElem?_append_right (by omega),w,Nat.sub_self] at b;simp at b;subst b;rw [<- w];exact x
lemma su:u3.length=8:=rfl
lemma o3 {gs:U} {p a:Nat} (c:p<=gs.length) (d:a < 8+p) :(u2 6 gs (u3,[])).1.getD a (inl false)=(u0 6 gs u3 p).1.getD a (inl false):=by
 have b:=u6 (m:=6) (gs:=gs) (init:=u3) (p:=p) (q:=gs.length) (a:=a)
  c le_rfl (by rw [su];exact d)
 unfold u0 at b;rw [List.take_length] at b;exact b
lemma oe {gs:U} {o p b:Nat} (d:MinClean 8 fG gs o) (S:StructG gs o) (hp:p<=13) (z:b∈liveList (u2 6 gs (u3,[])).2 6 S.o0 (u0 6 gs u3 p).2.length) :∃ a∈liveList gs 8 o p,(u0 6 gs u3 p).1.getD a (inl false)=inr b:=by
 have hlen13:=S.hlen;have hblt:b < 6+(u0 6 gs u3 p).2.length:=((qw _ _ _ _ _).1 z).1;have h7:m6 6 (u2 6 gs (u3,[])).2 S.o0 (u0 6 gs u3 p).2.length b:=((qw _ _ _ _ _).1 z).2;have h8:∃ a' < 8+13,m6 8 gs o p a'/\(u2 6 gs (u3,[])).1.getD a' (inl false)=inr b:=by
  rcases h7 with rfl|⟨j,h9,g0,x2,x3,_⟩
  . exact ⟨o,by have:=d.ho;omega,Or.inl rfl,S.ho0⟩
  . obtain ⟨q,h,s,hlenq,g,c,a1⟩:=oj (by omega) h9 x2;have u:=ug g.op (6+j) _ g0 _ (Prod.ext a1 rfl);have v:inr b∈g.inputs.map (fun i=>(u0 6 gs u3 q).1.getD i (inl false)):=
     u.2 b x3
    obtain ⟨a',h0,w⟩:=lMp.1 v;have h4:a' < 8+q:=j2 (d.hcl q g c) a' h0;have a2:(u2 6 gs (u3,[])).1.getD a' (inl false)=inr b:=by rw [o3 (by omega) h4];exact w
    exact ⟨a',by omega,Or.inr ⟨q,h,g,c,h0,d.hreach q s⟩,a2⟩
 suffices ∀ n a',a'<=n->a' < 8+13->m6 8 gs o p a' ->
    (u2 6 gs (u3,[])).1.getD a' (inl false)=inr b ->
    ∃ a∈liveList gs 8 o p,(u0 6 gs u3 p).1.getD a (inl false)=inr b by
  obtain ⟨a',h1,h2,h3⟩:=h8;exact this a' a' le_rfl h1 h2 h3
 intro n;induction n with
 | zero =>
  intro a' ha'0 _ x t;have e:a' < 8+p:=by omega
  exact ⟨a',(qw gs 8 o p a').2 ⟨e,x⟩,by rw [<- o3 (by omega) e];exact t⟩
 | succ n ih =>
  intro a' ha'n h4 x t;by_cases e:a' < 8+p
  . exact ⟨a',(qw gs 8 o p a').2 ⟨e,x⟩,by rw [<- o3 (by omega) e];exact t⟩
  . set q:=a' - 8;have h:p<=q:=by omega
    have s:q < gs.length:=by omega
    have w:a'=8+q:=by omega
    obtain ⟨g,c⟩ : ∃ g,gs[q]?=some g:=⟨gs[q],lGEQ s⟩;have b1:(u0 6 gs u3 (q+1)).1.getD (8+q) (inl false)=inr b:=by rw [<- o3 (by omega) (by omega),<- w];exact t
    have y:=u5 (m:=6) (init:=u3) rfl c;rw [b1] at y;cases h5:(qg g.op (6+(u0 6 gs u3 q).2.length)
      (g.inputs.map fun i=>(u0 6 gs u3 q).1.getD i (inl false))).1 with
    | some g' =>
     have u:=ug _ _ _ g' _ (Prod.ext h5 y.symm);have hbeq:b=6+(u0 6 gs u3 q).2.length:=by cases u.1;rfl
     have hmono:=k8 6 gs u3 h;omega
    | none =>
     have v:inr b∈g.inputs.map (fun i=>(u0 6 gs u3 q).1.getD i (inl false)):=
      tu _ _ _ b (Prod.ext h5 y.symm)
     obtain ⟨a'',h6,ha⟩:=lMp.1 v;have hc:a'' < 8+q:=j2 (d.hcl q g c) a'' h6;have hd:(u2 6 gs (u3,[])).1.getD a'' (inl false)=inr b:=by rw [o3 (by omega) hc];exact ha
     exact ih a'' (by omega) (by omega) (Or.inr ⟨q,h,g,c,h6,d.hreach q s⟩) hd
lemma uv {gs:U} {o p a b:Nat} (c:MinClean 8 fG gs o) (d:p<=gs.length) (e:a < 8+p) (h:(u0 6 gs u3 p).1.getD a (inl false)=inr b) :m7 (e3 gs 8 a)=e3 (u2 6 gs (u3,[])).2 6 b:=by
 funext x;have i:ej 6 (ofFn x) (q3 gs (ofFn (m8 x))) (u2 6 gs (u3,[])):=
  j7 6 _ (by simp) gs _ _ (fun g j=>(ja c.hcl g j).1) (m9 x)
 have hev:=((i.2 a).2).symm;rw [o3 d e,h] at hev;exact hev
lemma s7 {n:Nat} (gs:U) {a:Nat} (b:a < n) (x:F n) :e3 gs n a x=x ⟨a,b⟩:=by unfold e3;rw [ve gs (ofFn x) a (by simp [b])];simp [b]
lemma uy {n:Nat} {f:u7 n} {gs:U} {o:Nat} (j:MinClean n f gs o) {a b:Nat} (ha:a < n+gs.length) (hb:b < n+gs.length) (d:e3 gs n a=e3 gs n b):a=b:=by
 by_contra e;rcases Nat.lt_or_gt_of_ne e with hlt|hgt
 . by_cases g:b < n
   . have h:a < n:=by omega
     have c:=congrFun d (fun i:Fin n=>decide (i.val=a))
     rw [s7 gs h,s7 gs g] at c;simp at c;exact e c.symm
   . exact j.hndup (b - n) (by omega) a (by omega) (by rw [show n+(b - n)=b by omega];exact d.symm)
 . by_cases h:a < n
   . have g:b < n:=by omega
     have c:=congrFun d (fun i:Fin n=>decide (i.val=b))
     rw [s7 gs h,s7 gs g] at c;simp at c;exact e c
   . exact j.hndup (a - n) (by omega) b (by omega) (by rw [show n+(a - n)=a by omega];exact d)
lemma b6 {n:Nat} {f:u7 n} {gs:U} {o:Nat} (d:MinClean n f gs o) {a:Nat} (ha:a < n+gs.length) (c:Q):e3 gs n a≠fun _=>c:=by
 by_cases e:a < n
 . intro g;have b:=congrFun g (fun _:Fin n=>!c)
   rw [s7 gs e] at b;cases c<;>cases b
 . have:=d.hncG (a - n) (by omega) c
   rwa [show n+(a - n)=a by omega] at this
def e9 {α : Type}:List (α×Nat)->Nat
 | []=>0
 | (_,tg)::rest =>
  (if tg=4 then 2 else if tg=6\/tg=7\/tg=8 then 1 else 0)+e9 rest
lemma tm {α : Type} {b c:List (α×Nat)} (h:b.Perm c) :e9 b=e9 c:=by
 induction h with
 | nil=>rfl
 | cons x _ ih=>simp [e9,ih]
 | swap x y l=>simp [e9];omega
 | trans _ _ ih1 ih2=>exact ih1.trans ih2
lemma ek {α β : Type} (f : α->β) (b:List (α×Nat)) :e9 (b.map fun p=>(f p.1,p.2))=e9 b:=by
 induction b with
 | nil=>rfl
 | cons p rest ih=>simp [e9,ih]
def F7Ok (s:Nat) (b:List (u7 8×Nat)):Prop:=
 e9 b<=s /\
 ∃ L0:List (u7 6),
  L0.Nodup /\
  (∀ g∈L0,g≠(fun _=>false)/\g≠(fun _=>true)) /\
  (∀ g∈L0,∃ p∈b,p.2≠4/\p.2≠6/\p.2≠7/\p.2≠8/\m7 p.1=g) /\
  TR f7 (s - e9 b) (L0.map (·,0))
lemma F7Ok.perm {s:Nat} {b c:List (u7 8×Nat)} (d:b.Perm c) (h:F7Ok s b) :F7Ok s c:=by
 obtain ⟨e,L0,j,t,u,i⟩:=h;rw [tm d] at e i;refine ⟨e,L0,j,t,?_,i⟩
 intro g v;obtain ⟨p,w,x,y,z,h8,h0⟩:=u g v;exact ⟨p,d.mem_iff.1 w,x,y,z,h8,h0⟩
inductive JointRun:Nat->List (u7 8×Nat)->Prop where
 | done (tg:Nat) :
  F7Ok 0 [(fG,tg)] ->
  JointRun 0 [(fG,tg)]
 | perm {s xs zs}:xs.Perm zs->JointRun s xs->JointRun s zs
 | uNot {s a ta r} (save:Q) :
  F7Ok (s+1) ((a,ta)::r) ->
  (ta=0\/ta=3)->(ta=3->save=false) ->
  invF a≠(fun _=>false)->invF a≠(fun _=>true) ->
  invF a≠a->(∀ x∈r,x.1≠invF a) ->
  JointRun s ((invF a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
  JointRun (s+1) ((a,ta)::r)
 | bOr {s a ta b tb r} (ka kb:Q) :
  F7Ok (s+1) ((a,ta)::(b,tb)::r) ->
  ta≠2->tb≠2->ta≠7->tb≠7 ->
  ¬ (ta=4/\tb=6)->¬ (ta=6/\tb=4) ->
  (ka=true->ta=0\/ta=3)->(kb=true->tb=0\/tb=3) ->
  joinF a b≠(fun _=>false)->joinF a b≠(fun _=>true) ->
  joinF a b≠a->joinF a b≠b->(∀ x∈r,x.1≠joinF a b) ->
  JointRun s ((joinF a b,if ta=4\/tb=4 then 7 else 0) ::
   qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
  JointRun (s+1) ((a,ta)::(b,tb)::r)
 | bAnd {s a ta b tb r} (ka kb:Q) :
  F7Ok (s+1) ((a,ta)::(b,tb)::r) ->
  ta≠1->tb≠1->ta≠4->tb≠4->ta≠8->tb≠8 ->
  (ta=6->tb=7)->(tb=6->ta=7) ->
  (ka=true->ta=0)->(kb=true->tb=0) ->
  meetF a b≠(fun _=>false)->meetF a b≠(fun _=>true) ->
  meetF a b≠a->meetF a b≠b->(∀ x∈r,x.1≠meetF a b) ->
  JointRun s ((meetF a b,if ta=6\/tb=6 then 8 else if ta=3\/tb=3 then 1 else 0) ::
   qk ka (a,0) (qk kb (b,0) r)) ->
  JointRun (s+1) ((a,ta)::(b,tb)::r)
lemma JointRun.f7Ok {s:Nat} {c:List (u7 8×Nat)} (h:JointRun s c):F7Ok s c:=by
 induction h with
 | done _ b=>exact b
 | perm d _ ih=>exact ih.perm d
 | uNot _ b _ _ _ _ _ _ _ _=>exact b
 | bOr _ _ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=>exact b
 | bAnd _ _ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=>exact b
lemma JointRun.toRun {s:Nat} {c:List (u7 8×Nat)} (h:JointRun s c) :Run (invF (n:=8)) meetF joinF fG s (c.map Prod.fst):=by
 induction h with
 | done _ _=>exact Run.done
 | perm d _ ih=>exact Run.perm (d.map Prod.fst) ih
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
  have e:(((invF a,if ta=3 then 2 else 0)::qk save (a,0) r).map Prod.fst) =
    (if true then invF a else a)::qk save a (r.map Prod.fst):=by cases save<;>simp [qk]
  rw [e] at ih;exact Run.one true save ih
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((joinF a b,if ta=4\/tb=4 then 7 else 0) ::
    qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map Prod.fst) =
    (if false then meetF a b else joinF a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
   cases ka<;>cases kb<;>simp [qk]
  rw [e] at ih;exact Run.two false ka kb ih
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((meetF a b,if ta=6\/tb=6 then 8 else if ta=3\/tb=3 then 1 else 0) ::
    qk ka (a,0) (qk kb (b,0) r)).map Prod.fst) =
    (if true then meetF a b else joinF a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
   cases ka<;>cases kb<;>simp [qk]
  rw [e] at ih;exact Run.two true ka kb ih
lemma JointRun.len_le {s:Nat} {b:List (u7 8×Nat)} (h:JointRun s b) :b.length<=s+1:=by have:=tn h.toRun;simpa using this
lemma JointRun.inv_zero {c:List (u7 8×Nat)} (h:JointRun 0 c) :∃ tg,c=[(fG,tg)]:=by
 generalize b:0=s at h
 induction h with
 | done tg _=>exact ⟨tg,rfl⟩
 | perm d _ ih => obtain ⟨tg,rfl⟩:=ih b;exact ⟨tg,List.perm_singleton.1 d.symm⟩
 | uNot _ _ _ _ _ _ _ _ _ _=>cases b
 | bOr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=>cases b
 | bAnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=>cases b
def d3 (x:F 8):F 8
 | ⟨0,_⟩ => x 3
 | ⟨1,_⟩ => x 5
 | ⟨2,_⟩ => x 6
 | ⟨3,_⟩ => x 0
 | ⟨4,_⟩ => x 4
 | ⟨5,_⟩ => x 1
 | ⟨6,_⟩ => x 2
 | ⟨7,_⟩ => x 7
def x9 (x:F 6):F 6
 | ⟨0,_⟩ => x 3
 | ⟨1,_⟩ => x 4
 | ⟨2,_⟩ => x 5
 | ⟨3,_⟩ => x 0
 | ⟨4,_⟩ => x 1
 | ⟨5,_⟩ => x 2
lemma x8 (x:F 8):d3 (d3 x)=x:=by funext i;fin_cases i<;>rfl
lemma i4 (x:F 6):x9 (x9 x)=x:=by funext i;fin_cases i<;>rfl
lemma gf:Function.Bijective d3:=
 Function.bijective_iff_has_inverse.2 ⟨d3,x8,x8⟩
lemma sy:Function.Bijective x9:=
 Function.bijective_iff_has_inverse.2 ⟨x9,i4,i4⟩
lemma ad (x:F 8):fG (d3 x)=fG x:=by
 simp only [fG,d3];cases x 0<;>cases x 1<;>cases x 2<;>cases x 3 <;>
 cases x 4<;>cases x 5<;>cases x 6<;>cases x 7<;>rfl
lemma ae (x:F 6):f7 (x9 x)=f7 x:=by simp only [f7,x9];cases x 0<;>cases x 1<;>cases x 2<;>cases x 3<;>cases x 4<;>cases x 5<;>rfl
lemma dk (x:F 6):m8 (x9 x)=d3 (m8 x):=by funext i;fin_cases i<;>rfl
lemma ep (g:u7 8):m7 (fun x=>g (d3 x))=(fun x=>m7 g (x9 x)):=by funext x;simp [m7,dk]
lemma F7Ok.map_sig8 {s:Nat} {c:List (u7 8×Nat)} (h:F7Ok s c) :F7Ok s (c.map fun p=>((fun x=>p.1 (d3 x)),p.2)):=by
 obtain ⟨t,L0,u,v,w,d⟩:=h;unfold F7Ok;rw [ek (fun g x=>g (d3 x)) c]
 refine ⟨t,L0.map (fun g x=>g (x9 x)),?_,?_,?_,?_⟩
 . refine u.map ?_
   intro a b y;funext x
   have:=congrFun y (x9 x);dsimp only at this;rwa [i4] at this
 . intro g e;rcases lMp.1 e with ⟨g0,i,rfl⟩
   obtain ⟨z,ht⟩:=v g0 i;constructor
   . intro j;apply z;funext x;have:=congrFun j (x9 x);rwa [i4] at this
   . intro j;apply ht;funext x;have:=congrFun j (x9 x);rwa [i4] at this
 . intro g e;rcases lMp.1 e with ⟨g0,i,rfl⟩
   obtain ⟨p,hp,h4,h6,h7,h8,h0⟩:=w g0 i;refine ⟨((fun x=>p.1 (d3 x)),p.2),lMp.2 ⟨p,hp,rfl⟩,h4,h6,h7,h8,?_⟩
   rw [ep,h0]
 . have d':=wp x9 sy ae d;have h1:((L0.map (·,0)).map fun p=>((fun x=>p.1 (x9 x)),p.2)) =
      (L0.map (fun g x=>g (x9 x))).map (·,0):=by
     simp [lMMp,Function.comp]
   rwa [h1] at d'
lemma JointRun.map_sig8 {s:Nat} {ws:List (u7 8×Nat)} (h:JointRun s ws) :JointRun s (ws.map fun p=>((fun x=>p.1 (d3 x)),p.2)):=by
 have d:∀ a b:u7 8,(fun x=>a (d3 x))=(fun x=>b (d3 x))->a=b:=by intro a b x2;funext x;have:=congrFun x2 (d3 x);rwa [x8] at this
 induction h with
 | done tg c =>
  have hf:(fun x=>fG (d3 x))=fG:=funext ad
  have c':=c.map_sig8;simp only [lMC,lMN,hf] at c' ⊢;exact JointRun.done tg c'
 | perm g _ ih=>exact JointRun.perm (g.map _) ih
 | @uNot s a ta r save c x3 a1 i j t u _ ih =>
  have c':=c.map_sig8;simp only [lMC] at c' ih ⊢;have a2:(fun x=>invF a (d3 x))=invF (fun x=>a (d3 x)):=rfl
  have v:(qk save (a,0) r).map (fun p=>((fun x=>p.1 (d3 x)),p.2)) =
    qk save ((fun x=>a (d3 x)),0) (r.map fun p=>((fun x=>p.1 (d3 x)),p.2)):=by
   cases save<;>simp [qk]
  rw [a2,v] at ih;refine JointRun.uNot save c' x3 a1
   (fun e=>i (d _ _ e)) (fun e=>j (d _ _ e))
   (fun e=>t (d _ _ e)) ?_ ih
  intro x w;rcases lMp.1 w with ⟨p,g,rfl⟩
  exact fun e=>u p g (d _ _ e)
 | @bOr s a ta b tb r ka kb c y z h3 h4 h5 h6 h7 h8 i j t h0 u _ ih =>
  have c':=c.map_sig8;simp only [lMC] at c' ih ⊢;have b1:(fun x=>joinF a b (d3 x))=joinF (fun x=>a (d3 x)) (fun x=>b (d3 x)):=rfl
  have v:(qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map
    (fun p=>((fun x=>p.1 (d3 x)),p.2)) =
    qk ka ((fun x=>a (d3 x)),if ta=3 then 1 else 0)
     (qk kb ((fun x=>b (d3 x)),if tb=3 then 1 else 0) (r.map fun p=>((fun x=>p.1 (d3 x)),p.2))):=by
   cases ka<;>cases kb<;>simp [qk]
  rw [b1,v] at ih;refine JointRun.bOr ka kb c' y z h3 h4 h5 h6 h7 h8
   (fun e=>i (d _ _ e)) (fun e=>j (d _ _ e))
   (fun e=>t (d _ _ e)) (fun e=>h0 (d _ _ e)) ?_ ih
  intro x w;rcases lMp.1 w with ⟨p,g,rfl⟩
  exact fun e=>u p g (d _ _ e)
 | @bAnd s a ta b tb r ka kb c y z h3 h4 h5 h6 h7 h8 h9 ha i j t h0 u _ ih =>
  have c':=c.map_sig8;simp only [lMC] at c' ih ⊢;have hb:(fun x=>meetF a b (d3 x))=meetF (fun x=>a (d3 x)) (fun x=>b (d3 x)):=rfl
  have v:(qk ka (a,0) (qk kb (b,0) r)).map
    (fun p=>((fun x=>p.1 (d3 x)),p.2)) =
    qk ka ((fun x=>a (d3 x)),0)
     (qk kb ((fun x=>b (d3 x)),0) (r.map fun p=>((fun x=>p.1 (d3 x)),p.2))):=by
   cases ka<;>cases kb<;>simp [qk]
  rw [hb,v] at ih;refine JointRun.bAnd ka kb c' y z h3 h4 h5 h6 h7 h8 h9 ha
   (fun e=>i (d _ _ e)) (fun e=>j (d _ _ e))
   (fun e=>t (d _ _ e)) (fun e=>h0 (d _ _ e)) ?_ ih
  intro x w;rcases lMp.1 w with ⟨p,g,rfl⟩
  exact fun e=>u p g (d _ _ e)
def p7 (i:Fin 8):Nat:=
 match i.val with
 | 2=>3
 | 4=>6
 | 6=>3
 | 7=>4
 | _=>0
def g5:List (u7 8×Nat):=
 ofFn fun i:Fin 8=>((fun x:F 8=>x i),p7 i)
def dr {gs:U} {o:Nat} (S:StructG gs o) (p:Nat) (b:Nat->Nat):Prop:=
 (∀ a∈liveList gs 8 o p,
  match b a with
  | 0 | 1 | 2 | 3 =>
   yf 8 gs fG p a (b a)/\a≠7/\a≠4/\a≠8+S.pg/\(S.caseA=true->a≠8+S.pr)
  | 4=>a=7
  | 6=>a=4
  | 7=>a=8+S.pg
  | 8=>S.caseA=true/\a=8+S.pr
  | _=>False) /\
 (7∈liveList gs 8 o p->b 7=4) /\
 (4∈liveList gs 8 o p->b 4=6) /\
 (8+S.pg∈liveList gs 8 o p->b (8+S.pg)=7) /\
 (S.caseA=true->8+S.pr∈liveList gs 8 o p->b (8+S.pr)=8)
lemma dh {gs:U} {o p:Nat} (c:MinClean 8 fG gs o) (S:StructG gs o) :7∈liveList gs 8 o p↔p<=S.pg:=by
 rw [qw];constructor
 . rintro ⟨_,h|⟨q,b,g,d,e,_⟩⟩
   . exact absurd h.symm S.ho_ne_7
   . rw [S.h7_read q g d e] at b;exact b
 . intro i;obtain ⟨g,h_in,j,_,s,_,_⟩:=S.hpg_or;have t:(7:Nat)∈g.inputs:=by rcases s with h|h<;>rw [h]<;>simp
   exact ⟨by omega,Or.inr ⟨S.pg,i,g,j,t,c.hreach S.pg (by rw [S.hlen];exact S.hpg_lt)⟩⟩
lemma ee {gs:U} {o p:Nat} (c:MinClean 8 fG gs o) (S:StructG gs o) :8+S.pg∈liveList gs 8 o p↔S.pg < p/\p<=S.pr:=by
 rw [qw];constructor
 . rintro ⟨hlt,h|⟨q,d,g,e,b,_⟩⟩
   . exact absurd h.symm S.ho_ne_pg
   . rw [S.hpg_read q g e b] at d;omega
 . rintro ⟨h1,i⟩
   obtain ⟨g,u,j,_,s,_,_⟩:=S.hpr_and;have b:8+S.pg∈g.inputs:=by rcases s with h|h<;>rw [h]<;>simp
   exact ⟨by omega,Or.inr ⟨S.pr,i,g,j,b,c.hreach S.pr (by rw [S.hlen];exact S.hpr_lt)⟩⟩
lemma dj {gs:U} {o p:Nat} (i:MinClean 8 fG gs o) (S:StructG gs o) :4∈liveList gs 8 o p↔p<=(if S.caseA then S.pr else S.pw):=by
 rw [qw];constructor
 . rintro ⟨_,h|⟨q,j,g,s,b,_⟩⟩
   . exact absurd h.symm S.ho_ne_4
   . rw [S.h4_read q g s b] at j;exact j
 . intro c;cases d:S.caseA
   . simp only [d,bFT,↓reduceIte] at c;obtain ⟨g,v,t,_,e,_⟩:=S.hpw_or;simp only [d,bFT,↓reduceIte] at e;have b:(4:Nat)∈g.inputs:=by rcases e with h|h<;>rw [h]<;>simp
     exact ⟨by omega,Or.inr ⟨S.pw,c,g,t,b,i.hreach S.pw (by rw [S.hlen];exact S.hpw_lt)⟩⟩
   . simp only [d,↓reduceIte] at c;obtain ⟨g,u,w,_,e,_,x⟩:=S.hpr_and;have y:u=4:=x.1 d;have b:(4:Nat)∈g.inputs:=by rcases e with h|h<;>rw [h,y]<;>simp
     exact ⟨by omega,Or.inr ⟨S.pr,c,g,w,b,i.hreach S.pr (by rw [S.hlen];exact S.hpr_lt)⟩⟩
lemma ed {gs:U} {o p:Nat} (e:MinClean 8 fG gs o) (S:StructG gs o) (b:S.caseA=true) :8+S.pr∈liveList gs 8 o p↔S.pr < p/\p<=S.pw:=by
 rw [qw];constructor
 . rintro ⟨hlt,h|⟨q,i,g,j,c,_⟩⟩
   . exact absurd h.symm (S.ho_ne_pr b)
   . rw [S.hpr_read b q g j c] at i;omega
 . rintro ⟨h1,s⟩
   obtain ⟨g,v,t,_,d,_⟩:=S.hpw_or;simp only [b,↓reduceIte] at d;have c:8+S.pr∈g.inputs:=by rcases d with h|h<;>rw [h]<;>simp
   exact ⟨by omega,Or.inr ⟨S.pw,s,g,t,c,e.hreach S.pw (by rw [S.hlen];exact S.hpw_lt)⟩⟩
lemma em {gs:U} {o p:Nat} (t:MinClean 8 fG gs o) (S:StructG gs o) {u:Nat->Nat} (h5:dr S p u) :e9 ((liveList gs 8 o p).map fun a=>(e3 gs 8 a,u a)) = (if p<=S.pg then 1 else 0)+(if p<=S.pr then 1 else 0)+(if p<=S.pw then 1 else 0):=by
 let L:=liveList gs 8 o p;have j:L.Nodup:=vy gs 8 o p;let w:Nat->Nat:=fun a =>
   (if a=7 then 2 else 0) +
   (if a=8+S.pg then 1 else 0) +
   (if a=4 then 1 else 0) +
   (if a=8+S.pr then (if S.caseA then 1 else 0) else 0)
 have hpg_pr:=S.hpg_pr;have h6:∀ (b:M),(∀ a∈b,a∈L) ->
    e9 (b.map fun a=>(e3 gs 8 a,u a))=(b.map w).sum:=by
   intro b h3;induction b with
   | nil=>rfl
   | cons a rest ih =>
    simp only [lMC,e9,List.sum_cons,ih (fun x hx=>h3 x (lMCM _ hx))]
    congr 1
    have h8:a∈L:=h3 a (List.mem_cons_self ..);have d:=h5.1 a h8
    match i:u a with
    | 0 | 1 | 2 | 3 =>
      rw [i] at d;obtain ⟨_,v,s,y,h0⟩:=d;have h9:(if a=8+S.pr then (if S.caseA=true then 1 else 0) else 0)=0:=by
       split_ifs with x2 g
       . exact absurd x2 (h0 g)
       . rfl
       . rfl
      dsimp only [w];rw [if_neg v,if_neg y,if_neg s,h9];decide
    | 4 =>
      rw [i] at d;subst d;dsimp only [w]
      split_ifs<;>omega
    | 6 =>
      rw [i] at d;subst d;dsimp only [w]
      split_ifs<;>omega
    | 7 =>
      rw [i] at d;subst d;dsimp only [w]
      split_ifs<;>omega
    | 8 => rw [i] at d;obtain ⟨g,rfl⟩:=d;dsimp only [w];simp [g];omega
    | 5=>rw [i] at d;exact False.elim d
    | _+9=>rw [i] at d;exact False.elim d
 rw [h6 L (fun _ h=>h)]
 have z:∀ (b:M) (x:Nat) (c:Nat),b.Nodup ->
    (b.map fun a=>if a=x then c else 0).sum=if x∈b then c else 0:=by
   intro b x c j';induction b with
   | nil=>simp
   | cons a rest ih =>
    obtain ⟨ha,x3⟩:=List.nodup_cons.1 j';simp only [lMC,List.sum_cons,ih x3,lMM];by_cases h1:a=x
    . subst h1;simp [ha]
    . have a1:x≠a:=fun e=>h1 e.symm
      simp [h1,a1]
 have h2:∀ (f1 f2:Nat->Nat) (b:M),
    (b.map fun a=>f1 a+f2 a).sum=(b.map f1).sum+(b.map f2).sum:=by
   intro f1 f2 b;induction b with|nil=>simp|cons _ _ ih=>simp [ih];omega
 dsimp only [w];rw [h2,h2,h2,
    z L 7 2 j,z L (8+S.pg) 1 j,
    z L 4 1 j,z L (8+S.pr) (if S.caseA then 1 else 0) j]
 have v:(7∈L)↔p<=S.pg:=dh (p:=p) t S;have y:(8+S.pg∈L)↔S.pg < p/\p<=S.pr:=ee (p:=p) t S;have s:(4∈L)↔p<=(if S.caseA then S.pr else S.pw):=dj (p:=p) t S
 cases g:S.caseA
 . simp only [g,bFT,↓reduceIte] at s ⊢;simp only [v,y,s];split_ifs<;>omega
 . have h0:(8+S.pr∈L)↔S.pr < p/\p<=S.pw:=ed (p:=p) t S g;have hpr_pw:=S.hcaseA_lt g;simp only [g,↓reduceIte] at s ⊢;simp only [v,y,s,h0];split_ifs<;>omega
lemma ex {gs:U} {o:Nat} (S:StructG gs o) :∀ p≤ 13, (u0 6 gs u3 p).2.length + ((if S.pg < p then 1 else 0)+(if S.pr < p then 1 else 0)+(if S.pw < p then 1 else 0))=p:=by
 intro p;induction p with
 | zero=>intro _;simp [u0,u2]
 | succ p ih =>
  intro hp;have c:=ih (by omega);have e:p < gs.length:=by rw [S.hlen];omega
  obtain ⟨g,i⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],lGEQ e⟩;have hle:=k2 (m:=6) (init:=u3) i;have hge:(u0 6 gs u3 p).2.length<=(u0 6 gs u3 (p+1)).2.length:=
    k8 6 gs u3 (by omega)
  have d:=S.h10_elim_iff p (by omega);have h1:=S.hpg_pr;have h2:=S.hpw_ne_pg;have h3:=S.hpw_ne_pr;by_cases b:p=S.pg\/p=S.pr\/p=S.pw
  . have heq:=d.2 b;rcases b with rfl|rfl|rfl<;>(split_ifs at c ⊢<;>omega)
  . have hne:(u0 6 gs u3 (p+1)).2.length≠(u0 6 gs u3 p).2.length:=fun h=>b (d.1 h)
    have hsucc:(u0 6 gs u3 (p+1)).2.length=(u0 6 gs u3 p).2.length+1:=by omega
    push Not at b
    split_ifs at c ⊢<;>omega
lemma ut {gs:U} {o p:Nat} (i:MinClean 8 fG gs o) (S:StructG gs o) (e:p<=13) {j:Nat->Nat} (s:dr S p j) :F7Ok (13 - p) ((liveList gs 8 o p).map fun a=>(e3 gs 8 a,j a)):=by
 have w:=em i S s;have x:=ex S p e;have hpg_lt:=S.hpg_lt;have hpr_lt:=S.hpr_lt;have hpw_lt:=S.hpw_lt;set ow:=(u2 6 gs (u3,[])).2;set kp:=(u0 6 gs u3 p).2.length;have hgs0_len:ow.length=10:=S.h10_len;have hkp_le:kp<=ow.length:=by
   obtain ⟨t,ht⟩:=i3 6 gs u3 p (by rw [S.hlen];exact e)
   change kp<=ow.length;rw [show ow=(u0 6 gs u3 p).2++t from ht];simp [kp]
 have hkp_le10:(u0 6 gs u3 p).2.length<=10:=by change kp<=10;omega
 have h3:e9 ((liveList gs 8 o p).map fun a=>(e3 gs 8 a,j a))<=13 - p:=by rw [w];split_ifs at x ⊢<;>omega
 have h5:13 - p - e9 ((liveList gs 8 o p).map fun a=>(e3 gs 8 a,j a)) =
     10 - kp:=by
   rw [w];change 13 - p - _=10 - (u0 6 gs u3 p).2.length
   split_ifs at x ⊢<;>omega
 let L0:=(liveList ow 6 S.o0 kp).map (e3 ow 6);refine ⟨h3,L0,?_,?_,?_,?_⟩
 . have h9:=vy ow 6 S.o0 kp;refine h9.map_on ?_
   intro y x2 b2 x3 a1;have h1:=((qw ow 6 S.o0 kp y).1 x2).1;have h2:=((qw ow 6 S.o0 kp b2).1 x3).1;exact uy S.hm0 (by change y < 6+ow.length;omega) (by change b2 < 6+ow.length;omega) a1
 . intro g u;rcases lMp.1 u with ⟨b,v,rfl⟩
   have hblt:=((qw ow 6 S.o0 kp b).1 v).1;exact ⟨b6 S.hm0 (by change b < 6+ow.length;omega) false,b6 S.hm0 (by change b < 6+ow.length;omega) true⟩
 . intro g u;rcases lMp.1 u with ⟨b,v,rfl⟩
   obtain ⟨a,h,d⟩:=oe i S e v;have a2:=((qw gs 8 o p a).1 h).1;have ha:=uv i (by rw [S.hlen];exact e) a2 d
   refine ⟨(e3 gs 8 a,j a),lMp.2 ⟨a,h,rfl⟩,?_,?_,?_,?_,ha⟩
   . intro z;simp only at z;have c:=s.1 a h;rw [z] at c;subst c;rw [S.h10_7 p e] at d;cases d
   . intro h6;simp only at h6;have c:=s.1 a h;rw [h6] at c;subst c;rw [S.h10_4 p e] at d;cases d
   . intro h7;simp only at h7;have c:=s.1 a h;rw [h7] at c;subst c;have hc:S.pg < p:=((ee i S).1 h).1;rw [S.h10_pg p e hc] at d;cases d
   . intro h8;simp only at h8;have c:=s.1 a h;rw [h8] at c;obtain ⟨h0,rfl⟩:=c;have hd:S.pr < p:=((ed i S h0).1 h).1;rw [S.h10_pr h0 p e hd] at d;cases d
 . rw [h5];have he:=rg 6 f7 ow S.o0 S.hm0 (10 - kp) kp (by omega) (fun _=>0) (fun _ _=>trivial)
   have hf:((liveList ow 6 S.o0 kp).map fun a=>(e3 ow 6 a,0))=L0.map (·,0):=by simp [L0,lMMp,Function.comp]
   rwa [hf] at he
open Classical in
lemma y9 {gs:U} {o:Nat} (hm:MinClean 8 fG gs o) (S:StructG gs o) :∀ d p,p+d=13->∀ b:Nat->Nat,dr S p b -> JointRun d ((liveList gs 8 o p).map fun a=>(e3 gs 8 a,b a)):=by
 intro d;induction d with
 | zero =>
  intro p hp b t;have h79:p=13:=by omega
  subst h79;have h80:[o].Perm (liveList gs 8 o 13):=by
   refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (vy _ _ _ _)).2 ?_
   intro a;rw [qw,List.mem_singleton];constructor
   . rintro rfl;exact ⟨by have:=hm.ho;rw [S.hlen] at this;exact this,Or.inl rfl⟩
   . rintro ⟨_,h|⟨q,hq,g',s',_,_⟩⟩
     . exact h
     . have:=(lGES.1 s').1;rw [S.hlen] at this;omega
  have hf:e3 gs 8 o=fG:=funext hm.hev;have z:[(fG,b o)].Perm ((liveList gs 8 o 13).map fun a=>(e3 gs 8 a,b a)):=by rw [<- hf];exact h80.map (fun a=>(e3 gs 8 a,b a))
  have hf7:F7Ok 0 [(fG,b o)]:=(ut hm S le_rfl t).perm z.symm;exact JointRun.perm z (JointRun.done (b o) hf7)
 | succ d ih =>
  intro p hp b t;have h19:p < gs.length:=by rw [S.hlen];omega
  obtain ⟨g,s⟩ : ∃ g,gs[p]?=some g:=⟨gs[p],lGEQ h19⟩;have hr:wn 8 gs o (8+p):=hm.hreach p h19;have h28:=ip 8 gs o hm.hcl p g s hr;have hy:∀ u,u≠8+p->u∈liveList gs 8 o (p+1)->u∈liveList gs 8 o p:=
   fun u hne hu=>((h28 u).1 hu).resolve_left hne |>.1
  have hin:∀ a∈g.inputs,a∈liveList gs 8 o p:=fun a ha =>
   (qw _ _ _ _ _).2 ⟨j2 (hm.hcl p g s) a ha,Or.inr ⟨p,le_rfl,g,s,ha,hr⟩⟩
  have h20:∀ a∈liveList gs 8 o p,a≠8+p:=fun a ha =>
   Nat.ne_of_lt ((qw _ _ _ _ _).1 ha).1
  have hvg:=oa 8 gs p g s (j2 (hm.hcl p g s));have h23:=vy gs 8 o p;have h53:gs.drop p=g::gs.drop (p+1):=by rw [List.drop_eq_getElem_cons h19];have hge:gs[p]=g:=(lGES.1 s).2;rw [hge]
  have hgn:tq g:=w5 (hm.hcl p g s);have h24:=gt hm.hcl (p+1);have hnz:e3 gs 8 (8+p)≠fun _=>false:=hm.hncG p h19 false
  have hno:e3 gs 8 (8+p)≠fun _=>true:=hm.hncG p h19 true
  have hnd:∀ a∈liveList gs 8 o p,e3 gs 8 a≠e3 gs 8 (8+p):=fun a ha e =>
   hm.hndup p h19 a ((qw _ _ _ _ _).1 ha).1 e.symm
  have h65:F7Ok (d+1) ((liveList gs 8 o p).map fun a=>(e3 gs 8 a,b a)):=by
   have:=ut hm S (by omega) t
   rwa [show 13 - p=d+1 by omega] at this
  have h14:∀ a∈liveList gs 8 o p,b a<=3->yf 8 gs fG p a (b a):=by
   intro a ha hle;have i:=t.1 a ha
   match ht:b a with
   | 0 | 1 | 2 | 3=>rw [ht] at i;exact i.1
   | _+4=>omega
  have h34:∀ u,(∀ q g',gs[q]?=some g'->u∈g'.inputs->q=p)->u≠o ->
     ¬ m6 8 gs o (p+1) u:=by
   intro u h81 h82 h83;rcases h83 with h|⟨q,hq,g',s',hin',_⟩
   . exact h82 h
   . have:=h81 q g' s' hin';omega
  rcases hm.hcl p g s with ⟨hc,j,hj,x2⟩|⟨hc,j,k,hj,hk,x2⟩
  .
   have b1:j∈liveList gs 8 o p:=hin j (by simp [x2]);have he:e3 gs 8 (8+p)=invF (e3 gs 8 j):=by funext x;rw [hvg x,hc,x2];simp [GateOp.eval]
   have h21:b j<=3:=by
     have i:=t.1 j b1
     match ht:b j with
     | 0 | 1 | 2 | 3=>omega
     | 4 => rw [ht] at i;subst i;have h5:=S.h7_read p g s (by simp [x2]);obtain ⟨gg,_,hs,h9,_,_,_⟩:=S.hpg_or;rw [h5,hs] at s;cases s;rw [hc] at h9;cases h9
     | 6 =>
       rw [ht] at i;subst i;have h5:=S.h4_read p g s (by simp [x2]);cases a2:S.caseA
       . simp only [a2,bFT,↓reduceIte] at h5;obtain ⟨gw,_,hgw,h9,_⟩:=S.hpw_or;rw [h5,hgw] at s;cases s;rw [hc] at h9;cases h9
       . simp only [a2,↓reduceIte] at h5;obtain ⟨gr,_,hn,h9,_⟩:=S.hpr_and;rw [h5,hn] at s;cases s;rw [hc] at h9;cases h9
     | 7 => rw [ht] at i;subst i;have h5:=S.hpg_read p g s (by simp [x2]);obtain ⟨gr,_,hn,h9,_⟩:=S.hpr_and;rw [h5,hn] at s;cases s;rw [hc] at h9;cases h9
     | 8 => rw [ht] at i;obtain ⟨a2,rfl⟩:=i;have h5:=S.hpr_read a2 p g s (by simp [x2]);obtain ⟨gw,_,hgw,h9,_⟩:=S.hpw_or;rw [h5,hgw] at s;cases s;rw [hc] at h9;cases h9
     | 5=>rw [ht] at i;exact False.elim i
     | _+9=>rw [ht] at i;exact False.elim i
   have h46:∀ v c B,
       (∃ x y,fG (update x v false)≠fG (update y v false)) ->
       (v3 8 gs v p).1.getD j (inl false)=inl c ->
       (v3 8 gs v p).2.length+(gs.drop p).length<=(u2 8 (gs.drop p) (v3 8 gs v p)).2.length+B ->
       2<=B /\
       (v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl (!c) /\
       (v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
         (u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B /\
       (m6 8 gs o (p+1) j->3<=B):=by
     intro v c B x3 a1 hb;have h11:=ax 8 gs v p g s;have hfl:=vb 8 gs v p (by omega);have h66:=vb 8 gs v (p+1) (by omega);have h0:(v3 8 gs v (p+1)).2.length=(v3 8 gs v p).2.length:=by rw [h11];exact vs 8 _ g hgn j (by simp [x2]) c a1
     have h29:(v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl (!c):=by rw [h11];simp only [qa];rw [z2 _ _ _ _ hfl,hc,x2];simp only [lMC,lMN,a1,qg,wr]
     have h35:u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))=u2 8 (gs.drop p) (v3 8 gs v p):=by rw [zj,zj]
     have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [h53];simp
     have h30:(v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
         (u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B:=by rw [h35,h0];omega
     have h36:8+p∈liveList gs 8 o (p+1):=(h28 (8+p)).2 (Or.inl rfl);have h25:=zr hm (by omega) h36 x3 h29;have h47:=zt 8 (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1)) h24 (by omega) ⟨!c,h29⟩ h25;refine ⟨by omega,h29,h30,?_⟩
     intro h54;have h84:j∈liveList gs 8 o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,h54⟩;have h67:(v3 8 gs v (p+1)).1.getD j (inl false)=inl c:=by rw [h11];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact a1
     have h85:=zr hm (by omega) h84 x3 h67;have h55:=xu hm h19 (fun x=>congrFun he x)
     have h86:=k3 8 j (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1))
       h24 (by omega) (by omega) ⟨c,h67⟩ ⟨!c,h29⟩ h85 h25 h55
     omega
   have ht1:b j≠1:=by intro z;have hw:=h14 j b1 h21;rw [z] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have:=(h46 v false 1 x3 a1 hb).1;omega
   have ht2:b j≠2:=by intro h2;have hw:=h14 j b1 h21;rw [h2] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have:=(h46 v true 1 x3 a1 hb).1;omega
   have h03:b j=0\/b j=3:=by omega
   have ht3:b j=3->decide (m6 8 gs o (p+1) j)=false:=by intro h3;simp only [decide_eq_false_iff_not];intro h54;have hw:=h14 j b1 h21;rw [h3] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have:=(h46 v false 2 x3 a1 hb).2.2.2 h54;omega
   have h87:p≠S.pg:=by intro heq;obtain ⟨gg,_,hs,h9,_,_,_⟩:=S.hpg_or;rw [heq,hs] at s;cases s;rw [hc] at h9;cases h9
   have h88:p≠S.pr:=by intro heq;obtain ⟨gr,_,hn,h9,_⟩:=S.hpr_and;rw [heq,hn] at s;cases s;rw [hc] at h9;cases h9
   set b' : Nat->Nat:=fun a =>
     if a=8+p then (if b j=3 then 2 else 0)
     else if a=j then 0
     else b a
   have t' : dr S (p+1) b':=by
     refine ⟨?_,?_,?_,?_,?_⟩
     . intro a ha;simp only [b'];by_cases h12:a=8+p
       . subst h12;simp only [↓reduceIte];by_cases h3:b j=3
         . simp only [h3,↓reduceIte];have hw:=h14 j b1 h21;rw [h3] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;obtain ⟨_,h29,h30,_⟩:=h46 v false 2 x3 a1 hb;exact ⟨⟨v,x3,h29,by omega⟩,by omega,by omega,by omega,fun _=>by omega⟩
         . simp only [h3,↓reduceIte];exact ⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
       . simp only [h12,↓reduceIte];by_cases hz:a=j
         . subst hz;simp only [↓reduceIte];have h48:=t.1 a b1;rcases h03 with h0|h3
           . rw [h0] at h48;exact ⟨trivial,h48.2⟩
           . rw [h3] at h48;exact ⟨trivial,h48.2⟩
         . simp only [hz,↓reduceIte];have ha0:a∈liveList gs 8 o p:=hy a h12 ha;have i:=t.1 a ha0
           match ht:b a with
           | 0 | 1 | 2 | 3=>rw [ht] at i;exact ⟨vv s ((qw _ _ _ _ _).1 ha0).1 i.1,i.2⟩
           | 4 | 6 | 7 | 8=>rw [ht] at i;exact i
           | 5=>rw [ht] at i;exact False.elim i
           | _+9=>rw [ht] at i;exact False.elim i
     . intro h7;have h15:=hy 7 (by omega) h7;have h26:(7:Nat)≠j:=by intro e;rw [<- e,t.2.1 h15] at h21;omega
       simp only [b',show (7:Nat)≠8+p by omega,h26,↓reduceIte];exact t.2.1 h15
     . intro h4;have h16:=hy 4 (by omega) h4;have h26:(4:Nat)≠j:=by intro e;rw [<- e,t.2.2.1 h16] at h21;omega
       simp only [b',show (4:Nat)≠8+p by omega,h26,↓reduceIte];exact t.2.2.1 h16
     . intro hpg;have h17:=hy (8+S.pg) (by omega) hpg;have h26:8+S.pg≠j:=by intro e;rw [<- e,t.2.2.2.1 h17] at h21;omega
       simp only [b',show 8+S.pg≠8+p by omega,h26,↓reduceIte];exact t.2.2.2.1 h17
     . intro a2 hpr;have h18:=hy (8+S.pr) (by omega) hpr;have h26:8+S.pr≠j:=by intro e;rw [<- e,t.2.2.2.2 a2 h18] at h21;omega
       simp only [b',show 8+S.pr≠8+p by omega,h26,↓reduceIte];exact t.2.2.2.2 a2 h18
   have IH:=ih (p+1) (by omega) b' t';have hp1:(liveList gs 8 o p).Perm (j::(liveList gs 8 o p).erase j):=List.perm_cons_erase b1;have hnr:((liveList gs 8 o p).erase j).Nodup:=h23.erase j;have hp2:(liveList gs 8 o (p+1)).Perm
       ((8+p)::qk (decide (m6 8 gs o (p+1) j)) j ((liveList gs 8 o p).erase j)):=by
     refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
     . refine List.nodup_cons.2 ⟨?_,cj _ _ _ hnr (by simp [h23.mem_erase_iff])⟩
       rw [wa];rintro (⟨_,h⟩|h)
       . exact h20 j b1 h.symm
       . exact h20 _ (List.mem_of_mem_erase h) rfl
     . intro a;rw [h28 a,lMM,wa,h23.mem_erase_iff];simp only [decide_eq_true_eq,x2,lMM,lNMN,or_false];constructor
       . rintro (h|⟨z,h2⟩)
         . exact Or.inl h
         . by_cases hz:a=j
           . exact Or.inr (Or.inl ⟨hz ▸ h2 hz,hz⟩)
           . exact Or.inr (Or.inr ⟨hz,z⟩)
       . rintro (h|⟨z,rfl⟩|⟨z,h2⟩)
         . exact Or.inl h
         . exact Or.inr ⟨b1,fun _=>z⟩
         . exact Or.inr ⟨h2,fun h=>absurd h z⟩
   have h37:((liveList gs 8 o p).erase j).map (fun a=>(e3 gs 8 a,b' a)) =
       ((liveList gs 8 o p).erase j).map (fun a=>(e3 gs 8 a,b a)):=by
     apply lMCL;intro a ha;have z:a≠j:=(h23.mem_erase_iff.1 ha).1;have h2:a≠8+p:=h20 a (List.mem_of_mem_erase ha);simp [b',z,h2]
   have h38:(qk (decide (m6 8 gs o (p+1) j)) j ((liveList gs 8 o p).erase j)).map (fun a=>(e3 gs 8 a,b' a)) =
       qk (decide (m6 8 gs o (p+1) j)) (e3 gs 8 j,0) (((liveList gs 8 o p).erase j).map fun a=>(e3 gs 8 a,b a)):=by
     rw [wd,h37];simp [b',show j≠8+p by omega]
   have IH':=JointRun.perm (hp2.map fun a=>(e3 gs 8 a,b' a)) IH
   rw [lMC,h38,he] at IH';have h39:b' (8+p)=(if b j=3 then 2 else 0):=by simp [b']
   rw [h39] at IH';have hf7':=h65.perm (hp1.map fun a=>(e3 gs 8 a,b a))
   rw [lMC] at hf7';refine JointRun.perm (hp1.map fun a=>(e3 gs 8 a,b a)).symm ?_
   refine JointRun.uNot (decide (m6 8 gs o (p+1) j)) hf7' h03 ht3
     (he ▸ hnz) (he ▸ hno) (fun e=>hnd j b1 (he ▸ e.symm)) ?_ IH'
   intro x hx;obtain ⟨a,ha,rfl⟩:=lMp.1 hx;exact he ▸ hnd a (List.mem_of_mem_erase ha)
  .
   have hjk:j≠k:=by
     intro e;subst e;apply hm.hndup p h19 j hj
     funext x;rw [hvg x,x2];rcases hc with hc|hc<;>rw [hc]<;>simp [GateOp.eval]
   have b1:=hin j (by simp [x2]);have hd:=hin k (by simp [x2]);have hke:k∈(liveList gs 8 o p).erase j:=(h23.mem_erase_iff).2 ⟨fun e=>hjk e.symm,hd⟩
   have hnr:((liveList gs 8 o p).erase j).Nodup:=h23.erase j;have h89:(((liveList gs 8 o p).erase j).erase k).Nodup:=hnr.erase k;have hp1:(liveList gs 8 o p).Perm (j::k::((liveList gs 8 o p).erase j).erase k):=
     (List.perm_cons_erase b1).trans ((List.perm_cons_erase hke).cons j)
   have hmr:∀ a,a∈((liveList gs 8 o p).erase j).erase k↔a≠k/\a≠j/\a∈liveList gs 8 o p:=by intro a;rw [hnr.mem_erase_iff,h23.mem_erase_iff]
   have hp2:(liveList gs 8 o (p+1)).Perm
       ((8+p)::qk (decide (m6 8 gs o (p+1) j)) j
         (qk (decide (m6 8 gs o (p+1) k)) k
           (((liveList gs 8 o p).erase j).erase k))):=by
     refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
     . refine List.nodup_cons.2 ⟨?_,cj _ _ _ (cj _ _ _ h89 ?_) ?_⟩
       . rw [wa,wa];rintro (⟨_,h⟩|⟨_,h⟩|h)
         . exact h20 j b1 h.symm
         . exact h20 k hd h.symm
         . exact h20 _ ((hmr _).1 h).2.2 rfl
       . rw [hmr];simp
       . rw [wa,hmr];rintro (⟨_,h⟩|h)
         . exact hjk h
         . exact h.2.1 rfl
     . intro a;rw [h28 a,lMM,wa,wa,hmr a];simp only [decide_eq_true_eq,x2,lMM,lNMN,or_false];constructor
       . rintro (h|⟨z,h2⟩)
         . exact Or.inl h
         . by_cases hz:a=j
           . exact Or.inr (Or.inl ⟨hz ▸ h2 (Or.inl hz),hz⟩)
           . by_cases hak:a=k
             . exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak),hak⟩))
             . exact Or.inr (Or.inr (Or.inr ⟨hak,hz,z⟩))
       . rintro (h|⟨z,rfl⟩|⟨z,rfl⟩|⟨z,h2,h3⟩)
         . exact Or.inl h
         . exact Or.inr ⟨b1,fun _=>z⟩
         . exact Or.inr ⟨hd,fun _=>z⟩
         . exact Or.inr ⟨h3,fun h=>by rcases h with h|h<;>contradiction⟩
   have hf7':=h65.perm (hp1.map fun a=>(e3 gs 8 a,b a))
   rw [lMC,lMC] at hf7';rcases hc with hc|hc
   .
     have he:e3 gs 8 (8+p)=meetF (e3 gs 8 j) (e3 gs 8 k):=by funext x;rw [hvg x,hc,x2];simp [GateOp.eval]
     have h27:∀ (u w_other:Nat) (hu:u∈g.inputs) (h13:u < 8+p)
         (hval_u:∀ x,e3 gs 8 (8+p) x=(e3 gs 8 u x&&e3 gs 8 w_other x))
         (v:Fin 8) (c:Q) (B:Nat),
         (∃ x y,fG (update x v false)≠fG (update y v false)) ->
         (v3 8 gs v p).1.getD u (inl false)=inl c ->
         (v3 8 gs v p).2.length+(gs.drop p).length<=(u2 8 (gs.drop p) (v3 8 gs v p)).2.length+B ->
         (v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B /\
         (c=false->2<=B/\(v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl false /\
           (m6 8 gs o (p+1) u->3<=B)) /\
         (c=true->m6 8 gs o (p+1) u->2<=B):=by
       intro u wo hu h13 h40 v c B x3 a1 hb;have h11:=ax 8 gs v p g s;have hfl:=vb 8 gs v p (by omega);have h66:=vb 8 gs v (p+1) (by omega);have h0:(v3 8 gs v (p+1)).2.length=(v3 8 gs v p).2.length:=by rw [h11];exact vs 8 _ g hgn u hu c a1
       have h35:u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))=u2 8 (gs.drop p) (v3 8 gs v p):=by rw [zj,zj]
       have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [h53];simp
       have h30:(v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B:=by rw [h35,h0];omega
       have h22:(v3 8 gs v (p+1)).1.getD u (inl false)=inl c:=by rw [h11];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact a1
       refine ⟨h30,?_,?_⟩
       . intro hcf;subst hcf;have h49:(v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl false:=by
           rw [h11];simp only [qa];rw [z2 _ _ _ _ hfl,hc,x2];rw [x2] at hu;simp only [lMM,lNMN,or_false] at hu;rcases hu with rfl|rfl
           . simp only [lMC,lMN,a1,qg];cases (v3 8 gs v p).1.getD k (inl false)<;>simp [ko]
           . simp only [lMC,lMN,a1,qg];cases (v3 8 gs v p).1.getD j (inl false)<;>simp [ko]
         have h36:8+p∈liveList gs 8 o (p+1):=(h28 (8+p)).2 (Or.inl rfl);have h25:=zr hm (by omega) h36 x3 h49;have h47:=zt 8 (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1)) h24 (by omega) ⟨false,h49⟩ h25;refine ⟨by omega,h49,?_⟩
         intro xi;have h41:u∈liveList gs 8 o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,xi⟩;have h42:=zr hm (by omega) h41 x3 h22;have h55:=xt hm h19 h13 h40;have h86:=k3 8 u (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1))
           h24 (by omega) (by omega) ⟨false,h22⟩ ⟨false,h49⟩ h42 h25 h55
         omega
       . intro hct xi;subst hct;have h41:u∈liveList gs 8 o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,xi⟩;have h42:=zr hm (by omega) h41 x3 h22;have h47:=zt 8 u (gs.drop (p+1)) (v3 8 gs v (p+1)) h24 (by omega) ⟨true,h22⟩ h42;omega
     have h50:∀ x,e3 gs 8 (8+p) x=(e3 gs 8 j x&&e3 gs 8 k x):=fun x=>congrFun he x
     have h56:∀ x,e3 gs 8 (8+p) x=(e3 gs 8 k x&&e3 gs 8 j x):=fun x=>by rw [h50 x,Bool.and_comm]
     have h90:b j≠1:=by intro z;have hw:=h14 j b1 (by omega);rw [z] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have:=(h27 j k (by simp [x2]) hj h50 v false 1 x3 a1 hb).2.1 rfl;omega
     have h91:b k≠1:=by intro z;have hw:=h14 k hd (by omega);rw [z] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have:=(h27 k j (by simp [x2]) hk h56 v false 1 x3 a1 hb).2.1 rfl;omega
     have h68:b j≠4:=by intro h4;have i:=t.1 j b1;rw [h4] at i;subst i;have h5:=S.h7_read p g s (by simp [x2]);obtain ⟨gg,_,hs,h9,_,_,_⟩:=S.hpg_or;rw [h5,hs] at s;cases s;rw [hc] at h9;cases h9
     have h69:b k≠4:=by intro h4;have i:=t.1 k hd;rw [h4] at i;subst i;have h5:=S.h7_read p g s (by simp [x2]);obtain ⟨gg,_,hs,h9,_,_,_⟩:=S.hpg_or;rw [h5,hs] at s;cases s;rw [hc] at h9;cases h9
     have h70:b j≠8:=by intro h8;have i:=t.1 j b1;rw [h8] at i;obtain ⟨a2,rfl⟩:=i;have h5:=S.hpr_read a2 p g s (by simp [x2]);obtain ⟨gw,_,hgw,h9,_⟩:=S.hpw_or;rw [h5,hgw] at s;cases s;rw [hc] at h9;cases h9
     have h71:b k≠8:=by intro h8;have i:=t.1 k hd;rw [h8] at i;obtain ⟨a2,rfl⟩:=i;have h5:=S.hpr_read a2 p g s (by simp [x2]);obtain ⟨gw,_,hgw,h9,_⟩:=S.hpw_or;rw [h5,hgw] at s;cases s;rw [hc] at h9;cases h9
     have h31:∀ u w,u∈liveList gs 8 o p->w∈liveList gs 8 o p ->
         (g.inputs=[u,w]\/g.inputs=[w,u])->b u=6 ->
         S.caseA=true/\p=S.pr/\w=8+S.pg/\b w=7:=by
       intro u w huL hwL hgi h6;have i:=t.1 u huL;rw [h6] at i;subst i;have hv:(4:Nat)∈g.inputs:=by rcases hgi with h|h<;>rw [h]<;>simp
       have h5:=S.h4_read p g s hv;cases a2:S.caseA
       . simp only [a2,bFT,↓reduceIte] at h5;obtain ⟨gw,_,hgw,h9,_⟩:=S.hpw_or;rw [h5,hgw] at s;cases s;rw [hc] at h9;cases h9
       . simp only [a2,↓reduceIte] at h5;obtain ⟨gr,h57,hn,_,h58,_,h59⟩:=S.hpr_and;rw [h5,hn] at s;cases s
         have hu4:h57=4:=h59.1 a2;have h92:w=8+S.pg:=by rcases hgi with z|z<;>rcases h58 with h2|h2<;>rw [z,hu4] at h2<;>simp at h2<;>omega
         subst h92;exact ⟨rfl,h5,rfl,t.2.2.2.1 hwL⟩
     have h93:b j=6->b k=7:=fun h6=>(h31 j k b1 hd (Or.inl x2) h6).2.2.2
     have h94:b k=6->b j=7:=fun h6=>(h31 k j hd b1 (Or.inr x2) h6).2.2.2
     have h72:∀ u w,u∈liveList gs 8 o p->u < 8+p->u∈g.inputs ->
         (∀ x,e3 gs 8 (8+p) x=(e3 gs 8 u x&&e3 gs 8 w x)) ->
         decide (m6 8 gs o (p+1) u)=true->b u=0:=by
       intro u w huL h13 hv h40 h60;have xi:m6 8 gs o (p+1) u:=of_decide_eq_true h60;have i:=t.1 u huL
       match ht:b u with
       | 0=>rfl
       | 1 =>
         rw [ht] at i;obtain ⟨v,x3,a1,hb⟩:=i.1
         have:=(h27 u w hv h13 h40 v false 1 x3 a1 hb).2.1 rfl;omega
       | 2 =>
         rw [ht] at i;obtain ⟨v,x3,a1,hb⟩:=i.1
         have:=(h27 u w hv h13 h40 v true 1 x3 a1 hb).2.2 rfl xi;omega
       | 3 =>
         rw [ht] at i;obtain ⟨v,x3,a1,hb⟩:=i.1
         have:=((h27 u w hv h13 h40 v false 2 x3 a1 hb).2.1 rfl).2.2 xi;omega
       | 4 => rw [ht] at i;subst i;have h5:=S.h7_read p g s hv;obtain ⟨gg,_,hs,h9,_,_,_⟩:=S.hpg_or;rw [h5,hs] at s;cases s;rw [hc] at h9;cases h9
       | 6 =>
         rw [ht] at i;subst i;have h5:=S.h4_read p g s hv;cases a2:S.caseA
         . simp only [a2,bFT,↓reduceIte] at h5;obtain ⟨gw,_,hgw,h9,_⟩:=S.hpw_or;rw [h5,hgw] at s;cases s;rw [hc] at h9;cases h9
         . simp only [a2,↓reduceIte] at h5;exfalso;apply h34 4 _ S.ho_ne_4.symm xi
           intro q' g' s' h95';rw [S.h4_read q' g' s' h95'];simp [a2,h5]
       | 7 =>
         rw [ht] at i;subst i;have h5:=S.hpg_read p g s hv;exfalso;apply h34 (8+S.pg) _ S.ho_ne_pg.symm xi
         intro q' g' s' hin';rw [S.hpg_read q' g' s' hin'];exact h5.symm
       | 8 => rw [ht] at i;obtain ⟨a2,rfl⟩:=i;have h5:=S.hpr_read a2 p g s hv;obtain ⟨gw,_,hgw,h9,_⟩:=S.hpw_or;rw [h5,hgw] at s;cases s;rw [hc] at h9;cases h9
       | 5=>rw [ht] at i;exact False.elim i
       | _+9=>rw [ht] at i;exact False.elim i
     have h51:decide (m6 8 gs o (p+1) j)=true->b j=0:=
       h72 j k b1 hj (by simp [x2]) h50
     have h52:decide (m6 8 gs o (p+1) k)=true->b k=0:=
       h72 k j hd hk (by simp [x2]) h56
     have h87:p≠S.pg:=by intro heq;obtain ⟨gg,_,hs,h9,_,_,_⟩:=S.hpg_or;rw [heq,hs] at s;cases s;rw [hc] at h9;cases h9
     have h73:S.caseA=true->(p=S.pr↔b j=6\/b k=6):=by
       intro a2;constructor
       . intro h5;obtain ⟨gr,h57,hn,_,h58,_,h59⟩:=S.hpr_and;have hu4:h57=4:=h59.1 a2;rw [h5,hn] at s;cases s
         have h61:(4:Nat)∈g.inputs:=by rcases h58 with h|h<;>rw [h,hu4]<;>simp
         rw [x2] at h61;simp only [lMM,lNMN,or_false] at h61;rcases h61 with h|h
         . exact Or.inl (h ▸ t.2.2.1 (h ▸ b1))
         . exact Or.inr (h ▸ t.2.2.1 (h ▸ hd))
       . rintro (h6|h6)
         . exact (h31 j k b1 hd (Or.inl x2) h6).2.1
         . exact (h31 k j hd b1 (Or.inr x2) h6).2.1
     set b' : Nat->Nat:=fun a =>
       if a=8+p then (if b j=6\/b k=6 then 8 else if b j=3\/b k=3 then 1 else 0)
       else if a=j\/a=k then 0
       else b a
     have t' : dr S (p+1) b':=by
       refine ⟨?_,?_,?_,?_,?_⟩
       . intro a ha;simp only [b'];by_cases h12:a=8+p
         . subst h12;simp only [↓reduceIte];by_cases h6:b j=6\/b k=6
           . simp only [h6,↓reduceIte];rcases h6 with hj6|hk6
             . obtain ⟨a2,h5,_,_⟩:=h31 j k b1 hd (Or.inl x2) hj6;exact ⟨a2,by omega⟩
             . obtain ⟨a2,h5,_,_⟩:=h31 k j hd b1 (Or.inr x2) hk6;exact ⟨a2,by omega⟩
           . simp only [h6,↓reduceIte];have h74:S.caseA=true->8+p≠8+S.pr:=by
               intro a2 heq;exact h6 ((h73 a2).1 (by omega))
             by_cases h3:b j=3\/b k=3
             . simp only [h3,↓reduceIte];refine ⟨?_,by omega,by omega,by omega,h74⟩
               rcases h3 with hj3|hk3
               . have hw:=h14 j b1 (by omega);rw [hj3] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have hh:=h27 j k (by simp [x2]) hj h50 v false 2 x3 a1 hb;exact ⟨v,x3,(hh.2.1 rfl).2.1,by omega⟩
               . have hw:=h14 k hd (by omega);rw [hk3] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have hh:=h27 k j (by simp [x2]) hk h56 v false 2 x3 a1 hb;exact ⟨v,x3,(hh.2.1 rfl).2.1,by omega⟩
             . simp only [h3,↓reduceIte];exact ⟨trivial,by omega,by omega,by omega,h74⟩
         . simp only [h12,↓reduceIte];by_cases h62:a=j\/a=k
           . simp only [h62,↓reduceIte];have h32:m6 8 gs o (p+1) a:=((qw _ _ _ _ _).1 ha).2;rcases h62 with rfl|rfl
             . have ht0:=h51 (decide_eq_true h32);have i:=t.1 a b1;rw [ht0] at i;exact ⟨trivial,i.2⟩
             . have ht0:=h52 (decide_eq_true h32);have i:=t.1 a hd;rw [ht0] at i;exact ⟨trivial,i.2⟩
           . simp only [h62,↓reduceIte];have ha0:=hy a h12 ha;have i:=t.1 a ha0
             match ht:b a with
             | 0 | 1 | 2 | 3=>rw [ht] at i;exact ⟨vv s ((qw _ _ _ _ _).1 ha0).1 i.1,i.2⟩
             | 4 | 6 | 7 | 8=>rw [ht] at i;exact i
             | 5=>rw [ht] at i;exact False.elim i
             | _+9=>rw [ht] at i;exact False.elim i
       . intro h7;have h15:=hy 7 (by omega) h7;have xs:(7:Nat)≠j:=fun e=>h68 (e ▸ t.2.1 h15)
         have h10:(7:Nat)≠k:=fun e=>h69 (e ▸ t.2.1 h15)
         simp only [b',show (7:Nat)≠8+p by omega,xs,h10,or_self,↓reduceIte];exact t.2.1 h15
       . intro h4;have h16:=hy 4 (by omega) h4;have xs:(4:Nat)≠j:=by
           intro e;have z:=h51 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h4)).2);rw [<- e,t.2.2.1 h16] at z;cases z
         have h10:(4:Nat)≠k:=by intro e;have z:=h52 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h4)).2);rw [<- e,t.2.2.1 h16] at z;cases z
         simp only [b',show (4:Nat)≠8+p by omega,xs,h10,or_self,↓reduceIte];exact t.2.2.1 h16
       . intro hpg;have h17:=hy (8+S.pg) (by omega) hpg;have xs:8+S.pg≠j:=by
           intro e;have z:=h51 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ hpg)).2);rw [<- e,t.2.2.2.1 h17] at z;cases z
         have h10:8+S.pg≠k:=by intro e;have z:=h52 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ hpg)).2);rw [<- e,t.2.2.2.1 h17] at z;cases z
         simp only [b',show 8+S.pg≠8+p by omega,xs,h10,or_self,↓reduceIte];exact t.2.2.2.1 h17
       . intro a2 hpr;by_cases h5:p=S.pr
         . subst h5;have h6:=(h73 a2).1 rfl;simp only [b',h6,↓reduceIte]
         . have h18:=hy (8+S.pr) (by omega) hpr;have xs:8+S.pr≠j:=fun e=>h70 (e ▸ t.2.2.2.2 a2 h18)
           have h10:8+S.pr≠k:=fun e=>h71 (e ▸ t.2.2.2.2 a2 h18)
           simp only [b',show 8+S.pr≠8+p by omega,xs,h10,or_self,↓reduceIte];exact t.2.2.2.2 a2 h18
     have IH:=ih (p+1) (by omega) b' t';have h37:(((liveList gs 8 o p).erase j).erase k).map (fun a=>(e3 gs 8 a,b' a)) =
         (((liveList gs 8 o p).erase j).erase k).map (fun a=>(e3 gs 8 a,b a)):=by
       apply lMCL;intro a ha;have ⟨z,h2,h3⟩:=(hmr a).1 ha;have h4:=h20 a h3;simp [b',z,h2,h4]
     have h38:(qk (decide (m6 8 gs o (p+1) j)) j
         (qk (decide (m6 8 gs o (p+1) k)) k (((liveList gs 8 o p).erase j).erase k))).map (fun a=>(e3 gs 8 a,b' a)) =
         qk (decide (m6 8 gs o (p+1) j)) (e3 gs 8 j,0)
           (qk (decide (m6 8 gs o (p+1) k)) (e3 gs 8 k,0)
             ((((liveList gs 8 o p).erase j).erase k).map fun a=>(e3 gs 8 a,b a))):=by
       rw [wd,wd,h37];simp [b',show j≠8+p by omega,show k≠8+p by omega]
     have IH':=JointRun.perm (hp2.map fun a=>(e3 gs 8 a,b' a)) IH
     rw [lMC,h38,he] at IH';have h39:b' (8+p)=(if b j=6\/b k=6 then 8 else if b j=3\/b k=3 then 1 else 0):=by simp [b']
     rw [h39] at IH';refine JointRun.perm (hp1.map fun a=>(e3 gs 8 a,b a)).symm ?_
     refine JointRun.bAnd (decide (m6 8 gs o (p+1) j)) (decide (m6 8 gs o (p+1) k)) hf7'
       h90 h91 h68 h69 h70 h71 h93 h94 h51 h52
       (he ▸ hnz) (he ▸ hno) (fun e=>hnd j b1 (he ▸ e.symm)) (fun e=>hnd k hd (he ▸ e.symm)) ?_ IH'
     intro x hx;obtain ⟨a,ha,rfl⟩:=lMp.1 hx;exact he ▸ hnd a ((hmr a).1 ha).2.2
   .
     have he:e3 gs 8 (8+p)=joinF (e3 gs 8 j) (e3 gs 8 k):=by funext x;rw [hvg x,hc,x2];simp [GateOp.eval]
     have h33:∀ (u:Nat) (hu:u∈g.inputs) (h13:u < 8+p) (v:Fin 8) (c:Q) (B:Nat),
         (∃ x y,fG (update x v false)≠fG (update y v false)) ->
         (v3 8 gs v p).1.getD u (inl false)=inl c ->
         (v3 8 gs v p).2.length+(gs.drop p).length<=(u2 8 (gs.drop p) (v3 8 gs v p)).2.length+B ->
         (v3 8 gs v (p+1)).1.getD u (inl false)=inl c /\
         (v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B /\
         (c=true->2<=B)/\(c=false->m6 8 gs o (p+1) u->2<=B):=by
       intro u hu h13 v c B x3 a1 hb;have h11:=ax 8 gs v p g s;have hfl:=vb 8 gs v p (by omega);have h66:=vb 8 gs v (p+1) (by omega);have h0:(v3 8 gs v (p+1)).2.length=(v3 8 gs v p).2.length:=by rw [h11];exact vs 8 _ g hgn u hu c a1
       have h35:u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))=u2 8 (gs.drop p) (v3 8 gs v p):=by rw [zj,zj]
       have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [h53];simp
       have h30:(v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u2 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B:=by rw [h35,h0];omega
       have h22:(v3 8 gs v (p+1)).1.getD u (inl false)=inl c:=by rw [h11];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact a1
       refine ⟨h22,h30,?_,?_⟩
       . intro hct;subst hct;have h75:(v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl true:=by
           rw [h11];simp only [qa];rw [z2 _ _ _ _ hfl,hc,x2];rw [x2] at hu;simp only [lMM,lNMN,or_false] at hu;rcases hu with rfl|rfl
           . simp only [lMC,lMN,a1,qg];cases (v3 8 gs v p).1.getD k (inl false)<;>simp [ji]
           . simp only [lMC,lMN,a1,qg];cases (v3 8 gs v p).1.getD j (inl false)<;>simp [ji]
         have h36:8+p∈liveList gs 8 o (p+1):=(h28 (8+p)).2 (Or.inl rfl);have h25:=zr hm (by omega) h36 x3 h75;have h47:=zt 8 (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1)) h24 (by omega) ⟨true,h75⟩ h25;omega
       . intro hcf xi;subst hcf;have h41:u∈liveList gs 8 o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,xi⟩;have h42:=zr hm (by omega) h41 x3 h22;have h47:=zt 8 u (gs.drop (p+1)) (v3 8 gs v (p+1)) h24 (by omega) ⟨false,h22⟩ h42;omega
     have h96:b j≠2:=by intro h2;have hw:=h14 j b1 (by omega);rw [h2] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have:=(h33 j (by simp [x2]) hj v true 1 x3 a1 hb).2.2.1 rfl;omega
     have h97:b k≠2:=by intro h2;have hw:=h14 k hd (by omega);rw [h2] at hw;obtain ⟨v,x3,a1,hb⟩:=hw;have:=(h33 k (by simp [x2]) hk v true 1 x3 a1 hb).2.2.1 rfl;omega
     have h76:b j≠7:=by intro h7;have i:=t.1 j b1;rw [h7] at i;subst i;have h5:=S.hpg_read p g s (by simp [x2]);obtain ⟨gr,_,hn,h9,_⟩:=S.hpr_and;rw [h5,hn] at s;cases s;rw [hc] at h9;cases h9
     have h77:b k≠7:=by intro h7;have i:=t.1 k hd;rw [h7] at i;subst i;have h5:=S.hpg_read p g s (by simp [x2]);obtain ⟨gr,_,hn,h9,_⟩:=S.hpr_and;rw [h5,hn] at s;cases s;rw [hc] at h9;cases h9
     have h98:¬ (b j=4/\b k=6):=by
       rintro ⟨h4,h6⟩
       have hi1:=t.1 j b1;rw [h4] at hi1;subst hi1;have hi2:=t.1 k hd;rw [h6] at hi2;subst hi2;have h5:=S.h7_read p g s (by simp [x2]);obtain ⟨gg,h_in,hs,_,h43,_,hh4⟩:=S.hpg_or;rw [h5,hs] at s;cases s
       rcases h43 with z|z<;>rw [x2] at z<;>simp at z
       exact hh4 z.symm
     have hno64:¬ (b j=6/\b k=4):=by
       rintro ⟨h6,h4⟩
       have hi1:=t.1 j b1;rw [h6] at hi1;subst hi1;have hi2:=t.1 k hd;rw [h4] at hi2;subst hi2;have h5:=S.h7_read p g s (by simp [x2]);obtain ⟨gg,h_in,hs,_,h43,_,hh4⟩:=S.hpg_or;rw [h5,hs] at s;cases s
       rcases h43 with z|z<;>rw [x2] at z<;>simp at z
       exact hh4 z.symm
     have h78:∀ u,u∈liveList gs 8 o p->u < 8+p->u∈g.inputs ->
         decide (m6 8 gs o (p+1) u)=true->b u=0\/b u=3:=by
       intro u huL h13 hv h60;have xi:m6 8 gs o (p+1) u:=of_decide_eq_true h60;have i:=t.1 u huL
       match ht:b u with
       | 0=>exact Or.inl rfl
       | 3=>exact Or.inr rfl
       | 1 =>
         rw [ht] at i;obtain ⟨v,x3,a1,hb⟩:=i.1
         have:=(h33 u hv h13 v false 1 x3 a1 hb).2.2.2 rfl xi;omega
       | 2 =>
         rw [ht] at i;obtain ⟨v,x3,a1,hb⟩:=i.1
         have:=(h33 u hv h13 v true 1 x3 a1 hb).2.2.1 rfl;omega
       | 4 =>
         rw [ht] at i;subst i;have h5:=S.h7_read p g s hv;exfalso;apply h34 7 _ S.ho_ne_7.symm xi
         intro q' g' s' hin';rw [S.h7_read q' g' s' hin'];exact h5.symm
       | 6 =>
         rw [ht] at i;subst i;have h5:=S.h4_read p g s hv;cases a2:S.caseA
         . simp only [a2,bFT,↓reduceIte] at h5;exfalso;apply h34 4 _ S.ho_ne_4.symm xi
           intro q' g' s' hin';rw [S.h4_read q' g' s' hin'];simp [a2,h5]
         . simp only [a2,↓reduceIte] at h5;obtain ⟨gr,_,hn,h9,_⟩:=S.hpr_and;rw [h5,hn] at s;cases s;rw [hc] at h9;cases h9
       | 7 => rw [ht] at i;subst i;have h5:=S.hpg_read p g s hv;obtain ⟨gr,_,hn,h9,_⟩:=S.hpr_and;rw [h5,hn] at s;cases s;rw [hc] at h9;cases h9
       | 8 =>
         rw [ht] at i;obtain ⟨a2,rfl⟩:=i;have h5:=S.hpr_read a2 p g s hv;exfalso;apply h34 (8+S.pr) _ (S.ho_ne_pr a2).symm xi
         intro q' g' s' hin';rw [S.hpr_read a2 q' g' s' hin'];exact h5.symm
       | 5=>rw [ht] at i;exact False.elim i
       | _+9=>rw [ht] at i;exact False.elim i
     have h44:decide (m6 8 gs o (p+1) j)=true->b j=0\/b j=3:=h78 j b1 hj (by simp [x2]);have h45:decide (m6 8 gs o (p+1) k)=true->b k=0\/b k=3:=h78 k hd hk (by simp [x2]);have h88:p≠S.pr:=by intro heq;obtain ⟨gr,_,hn,h9,_⟩:=S.hpr_and;rw [heq,hn] at s;cases s;rw [hc] at h9;cases h9
     have h63:p=S.pg↔b j=4\/b k=4:=by
       constructor
       . intro h5;obtain ⟨gg,_,hs,_,h43,_,_⟩:=S.hpg_or;rw [h5,hs] at s;cases s
         have h64:(7:Nat)∈g.inputs:=by rcases h43 with h|h<;>rw [h]<;>simp
         rw [x2] at h64;simp only [lMM,lNMN,or_false] at h64;rcases h64 with h|h
         . exact Or.inl (h ▸ t.2.1 (h ▸ b1))
         . exact Or.inr (h ▸ t.2.1 (h ▸ hd))
       . rintro (h4|h4)
         . have i:=t.1 j b1;rw [h4] at i;subst i;exact S.h7_read p g s (by simp [x2])
         . have i:=t.1 k hd;rw [h4] at i;subst i;exact S.h7_read p g s (by simp [x2])
     set b' : Nat->Nat:=fun a =>
       if a=8+p then (if b j=4\/b k=4 then 7 else 0)
       else if a=j then (if b j=3 then 1 else 0)
       else if a=k then (if b k=3 then 1 else 0)
       else b a
     have t' : dr S (p+1) b':=by
       refine ⟨?_,?_,?_,?_,?_⟩
       . intro a ha;simp only [b'];by_cases h12:a=8+p
         . subst h12;simp only [↓reduceIte];by_cases h4:b j=4\/b k=4
           . simp only [h4,↓reduceIte];have:=h63.2 h4;omega
           . simp only [h4,↓reduceIte];have hne_pg:p≠S.pg:=fun e=>h4 (h63.1 e)
             exact ⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
         . simp only [h12,↓reduceIte];by_cases hz:a=j
           . subst hz;simp only [↓reduceIte];have h32:=((qw _ _ _ _ _).1 ha).2;have h03:=h44 (decide_eq_true h32);by_cases h3:b a=3
             . simp only [h3,↓reduceIte];have i:=t.1 a b1;rw [h3] at i;obtain ⟨v,x3,a1,hb⟩:=i.1;have hh:=h33 a (by simp [x2]) hj v false 2 x3 a1 hb;exact ⟨⟨v,x3,hh.1,by omega⟩,i.2⟩
             . simp only [h3,↓reduceIte];have h0:b a=0:=by omega
               have i:=t.1 a b1;rw [h0] at i;exact ⟨trivial,i.2⟩
           . simp only [hz,↓reduceIte];by_cases hak:a=k
             . subst hak;simp only [↓reduceIte];have h32:=((qw _ _ _ _ _).1 ha).2;have h03:=h45 (decide_eq_true h32);by_cases h3:b a=3
               . simp only [h3,↓reduceIte];have i:=t.1 a hd;rw [h3] at i;obtain ⟨v,x3,a1,hb⟩:=i.1;have hh:=h33 a (by simp [x2]) hk v false 2 x3 a1 hb;exact ⟨⟨v,x3,hh.1,by omega⟩,i.2⟩
               . simp only [h3,↓reduceIte];have h0:b a=0:=by omega
                 have i:=t.1 a hd;rw [h0] at i;exact ⟨trivial,i.2⟩
             . simp only [hak,↓reduceIte];have ha0:=hy a h12 ha;have i:=t.1 a ha0
               match ht:b a with
               | 0 | 1 | 2 | 3=>rw [ht] at i;exact ⟨vv s ((qw _ _ _ _ _).1 ha0).1 i.1,i.2⟩
               | 4 | 6 | 7 | 8=>rw [ht] at i;exact i
               | 5=>rw [ht] at i;exact False.elim i
               | _+9=>rw [ht] at i;exact False.elim i
       . intro h7;have h15:=hy 7 (by omega) h7;have xs:(7:Nat)≠j:=by
           intro e;have z:=h44 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h7)).2);rw [<- e,t.2.1 h15] at z;omega
         have h10:(7:Nat)≠k:=by intro e;have z:=h45 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h7)).2);rw [<- e,t.2.1 h15] at z;omega
         simp only [b',show (7:Nat)≠8+p by omega,xs,h10,↓reduceIte];exact t.2.1 h15
       . intro h4;have h16:=hy 4 (by omega) h4;have xs:(4:Nat)≠j:=by
           intro e;have z:=h44 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h4)).2);rw [<- e,t.2.2.1 h16] at z;omega
         have h10:(4:Nat)≠k:=by intro e;have z:=h45 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h4)).2);rw [<- e,t.2.2.1 h16] at z;omega
         simp only [b',show (4:Nat)≠8+p by omega,xs,h10,↓reduceIte];exact t.2.2.1 h16
       . intro hpg;by_cases h5:p=S.pg
         . subst h5;have h4:=h63.1 rfl;simp only [b',h4,↓reduceIte]
         . have h17:=hy (8+S.pg) (by omega) hpg;have xs:8+S.pg≠j:=fun e=>h76 (e ▸ t.2.2.2.1 h17)
           have h10:8+S.pg≠k:=fun e=>h77 (e ▸ t.2.2.2.1 h17)
           simp only [b',show 8+S.pg≠8+p by omega,xs,h10,↓reduceIte];exact t.2.2.2.1 h17
       . intro a2 hpr;have h18:=hy (8+S.pr) (by omega) hpr;have xs:8+S.pr≠j:=by
           intro e;have z:=h44 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ hpr)).2);rw [<- e,t.2.2.2.2 a2 h18] at z;omega
         have h10:8+S.pr≠k:=by intro e;have z:=h45 (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ hpr)).2);rw [<- e,t.2.2.2.2 a2 h18] at z;omega
         simp only [b',show 8+S.pr≠8+p by omega,xs,h10,↓reduceIte];exact t.2.2.2.2 a2 h18
     have IH:=ih (p+1) (by omega) b' t';have h37:(((liveList gs 8 o p).erase j).erase k).map (fun a=>(e3 gs 8 a,b' a)) =
         (((liveList gs 8 o p).erase j).erase k).map (fun a=>(e3 gs 8 a,b a)):=by
       apply lMCL;intro a ha;have ⟨z,h2,h3⟩:=(hmr a).1 ha;have h4:=h20 a h3;simp [b',z,h2,h4]
     have h38:(qk (decide (m6 8 gs o (p+1) j)) j
         (qk (decide (m6 8 gs o (p+1) k)) k (((liveList gs 8 o p).erase j).erase k))).map (fun a=>(e3 gs 8 a,b' a)) =
         qk (decide (m6 8 gs o (p+1) j)) (e3 gs 8 j,if b j=3 then 1 else 0)
           (qk (decide (m6 8 gs o (p+1) k)) (e3 gs 8 k,if b k=3 then 1 else 0)
             ((((liveList gs 8 o p).erase j).erase k).map fun a=>(e3 gs 8 a,b a))):=by
       rw [wd,wd,h37];simp [b',show j≠8+p by omega,show k≠8+p by omega,hjk.symm]
     have IH':=JointRun.perm (hp2.map fun a=>(e3 gs 8 a,b' a)) IH
     rw [lMC,h38,he] at IH';have h39:b' (8+p)=(if b j=4\/b k=4 then 7 else 0):=by simp [b']
     rw [h39] at IH';refine JointRun.perm (hp1.map fun a=>(e3 gs 8 a,b a)).symm ?_
     refine JointRun.bOr (decide (m6 8 gs o (p+1) j)) (decide (m6 8 gs o (p+1) k)) hf7'
       h96 h97 h76 h77 h98 hno64 h44 h45
       (he ▸ hnz) (he ▸ hno) (fun e=>hnd j b1 (he ▸ e.symm)) (fun e=>hnd k hd (he ▸ e.symm)) ?_ IH'
     intro x hx;obtain ⟨a,ha,rfl⟩:=lMp.1 hx;exact he ▸ hnd a ((hmr a).1 ha).2.2
open Classical in
lemma uu {t:Nat} (v:HCS 8 fG t) (ht:t<=13) :JointRun 13 g5:=by
 obtain ⟨gs,o,c,hlen⟩:=fr 8 fG t bn v;obtain ⟨S⟩:=oy c (by omega);have w:∀ i:Fin 8,(i:Nat)∈liveList gs 8 o 0:=by
  intro i;apply n2 c i
  fin_cases i
  . exact ⟨fun j=>j=1,by decide⟩
  . exact ⟨fun j=>j=0,by decide⟩
  . exact ⟨fun j=>j=0,by decide⟩
  . exact ⟨fun j=>j=0,by decide⟩
  . exact ⟨fun j=>j=7,by decide⟩
  . exact ⟨fun j=>j=3,by decide⟩
  . exact ⟨fun j=>j=3,by decide⟩
  . exact ⟨fun j=>j=4,by decide⟩
 have g:liveList gs 8 o 0=range 8:=by unfold liveList;simp only [nAZ];rw [List.filter_eq_self];intro a e;simp only [lMRG] at e;exact decide_eq_true ((qw gs 8 o 0 a).1 (w ⟨a,e⟩)).2
 let d:Nat->Nat:=fun a=>if h:a < 8 then p7 ⟨a,h⟩ else 0
 have z:dr S 0 d:=by
  refine ⟨?_,?_,?_,?_,?_⟩
  . intro a e;rw [g,lMRG] at e
    interval_cases a
    . exact ⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
    . exact ⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
    . have s:∃ x y:F 8,fG (update x 2 false)≠fG (update y 2 false):=
       ⟨fun _=>false,fun _=>true,by decide⟩
      have h8:=(wz 8 fG gs o 2 11 c.hcl c.hev s se).2;refine ⟨⟨2,s,by simp [v3,u2,wf],?_⟩,by omega,by omega,by omega,fun _=>by omega⟩
      simp only [v3,List.take_zero,List.drop_zero,show u2 8 [] (wf 8 2,[])=(wf 8 2,[]) from rfl,
         lLN,Nat.zero_add]
      rw [S.hlen];omega
    . exact ⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
    . simp [d,p7]
    . exact ⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
    . have u:∃ x y:F 8,fG (update x 6 false)≠fG (update y 6 false):=
       ⟨fun _=>false,fun _=>true,by decide⟩
      have h8:=(wz 8 fG gs o 6 11 c.hcl c.hev u sd).2;refine ⟨⟨6,u,by simp [v3,u2,wf],?_⟩,by omega,by omega,by omega,fun _=>by omega⟩
      simp only [v3,List.take_zero,List.drop_zero,show u2 8 [] (wf 8 6,[])=(wf 8 6,[]) from rfl,
         lLN,Nat.zero_add]
      rw [S.hlen];omega
    . simp [d,p7]
  . intro _;rfl
  . intro _;rfl
  . intro h9;have:=((qw gs 8 o 0 (8+S.pg)).1 h9).1;omega
  . intro _ x2;have:=((qw gs 8 o 0 (8+S.pr)).1 x2).1;omega
 have x3:=y9 c S 13 0 (by omega) d z;have a1:(liveList gs 8 o 0).map (fun a=>(e3 gs 8 a,d a))=g5:=by
  rw [g];have b:∀ (i:Fin 8),e3 gs 8 i.val=fun x=>x i:=fun i=>funext (s7 gs i.isLt)
  have a2:range 8=[0,1,2,3,4,5,6,7]:=by decide
  rw [a2];have h0:e3 gs 8 0=fun x=>x 0:=b 0
  have h1:e3 gs 8 1=fun x=>x 1:=b 1
  have h2:e3 gs 8 2=fun x=>x 2:=b 2
  have h3:e3 gs 8 3=fun x=>x 3:=b 3
  have h4:e3 gs 8 4=fun x=>x 4:=b 4
  have h5:e3 gs 8 5=fun x=>x 5:=b 5
  have h6:e3 gs 8 6=fun x=>x 6:=b 6
  have h7:e3 gs 8 7=fun x=>x 7:=b 7
  simp only [g5,List.ofFn_succ,List.ofFn_zero,lMC,lMN,
        h0,h1,h2,h3,h4,h5,h6,h7]
  rfl
 rwa [a1] at x3
def rG : Nat := 0x801222a23090201181a1903084020602848180a8c9c8e1a2111c1e1d1310c2444644c2c241c8c2c94340201181a1903082124280509140211051206a1a2a4a6a5a30a0142480309a2c28acaaae28aa2c2e2caaa41444246434520180a2812301851545815191102213003120c4424642c4c1c0a8c980e1a2151c1619131e4d4ccc6c5e2d2cac6c3e1d1c9c5c3e0d0c8e4b4aca6a5e2b2aaa6a3e1b1a9a5a3e0b0a8ccac9c8e8dcaaa9a8e8bc8a898899486859286839189858390d4745c5655d171595553d0705852644c464562524a464361494543604864342c262562322a262361312925236030289c5c3c1e1d9858381a199434161591311915139030124c2c0e0d4a2a1a0e0b4828090605120603090503c4c4c4c4c4c2c2c2c2c2c1c1c1c1c1c0c0c0a4a4a4a4a4a2a2a2a2a2a1a1a1a1a1a0a0a08c8c8c8c8c8a8a8a8a8a88888888848484828282818181818054545454545151515151505050504444444442424242424141414140402424242424222222222221212121212020201c1c1c1c1c18181818181414141411111111111010100c0c0c0c0a0a0a0a0a0808080404020202010101
def cG : Cfg := ⟨150,300,396,426,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffa3ffffffa3ffffaba3ffffffffffb3ffa3ffffffa3bbb3aba071c71c71c71c71c71c71c71c71c71c7fffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000,0x3fffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffff,0x41041041041041041041041,0x75d75d75d75d75d75d75d75d,0x820820820820820820820820,0x1041041,0x2082082,0x1d75d75d,0x20820820⟩
def xG : List (Nat × Nat) := [(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa934c003f0004d33234c0023013a8003f087e021f808449f07e021f021f80847e04253c00f8003e000003c0f8003c003e0000f800007,0),(0x33333333333333333333333333333333333333333333333333333333333333330e9404c00009404d5abffce2804c04c017c205f0817c17108225f105f08108824be2e41f0007c001f01c000007c007c00000000f838,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c00000380fff00a94e00001500a03fa80f8843e210f883a27c41e223e210f83c43c434be000f8003e00e01f007800f8003e0f00f00c0,3),(0x3fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc0253a3fc08dc3a500094e8c0725023fc0210848421fffc04108484448421ffc083ffc10000000003fff000000000000003ff000fff00,0),(0x3fffc0003fffc0003fffc0003fffc0003fffc0003fffc0003fffc0003fffc00000380953013380a800000004ff940953421090842210a48fffe08010842fffffc08080000000000000001fff800000003fffff00000,6),(0x3fffffffc00000003fffffffc00000003fffffffc00000003fffffffc00000000e00e02556501c03f02354094030e02584213ffff4210002109108bffff211109108000000ffffc0000000000000ffffc0000000000,0),(0x3fffffffffffffffc0000000000000003fffffffffffffffc0000000000000000001500e3800000003153bf01c01501cffffe10848420007ffffffe108442000221003ffff00000000001fffffff000000000000000,3),(0x3fffffffffffffffffffffffffffffffc00000000000000000000000000000000000038e00a00003f03ffc000000030afffffffffffffffc2100000000084221000003ffffffffffffffe0000000000000000000000,4)]
def fy : List (Nat × Nat) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,3),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,6),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,3),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,4)]
def aq:Nat×Nat×Nat×Nat:=(7,0x5500550055005500550055005500550055005500550055005500550055005500,0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55)
def ap:Nat×Nat×Nat×Nat:=(30,0x3333333300000000333333330000000033333333000000003333333300000000,0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333)
def an:Nat×Nat×Nat×Nat:=(60,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f)
def gG:V:=[aq,ap,an]
def NG:Nat->Nat
 | 5=>2
 | 6=>31
 | 7=>140
 | 8=>396
 | 9=>558
 | 10=>316
 | 11=>59
 | 12=>7
 | 13=>1
 | _=>0
def LG:Nat->Nat
 | 5=>2
 | 6=>6
 | 7=>9
 | 8=>10
 | 9=>11
 | 10=>10
 | 11=>7
 | 12=>4
 | 13=>1
 | _=>0
def HG:Nat->Nat
 | 5=>0xbf794e9f6cbc
 | 6=>0xf61ca4ecf4a1e73467df6b26dd565bd356cfc97a04c63fbdbd49c9bd1887babedab196d7ae7220a08dde9c9fee97fd388cefd77c8307744d0e6dbbb36ac9266530145726244d9ecc48599e484e14455e1c3d77242500df0ed1f206160e
 | 7 => 0xfbaf52fb9f0df6c5daf6c13af5efd0f5cf38f51be2f1c155f034c4ef0422edc079ebc163e774dde6a89de49876e291e0e146eadfc0e3de8cefdd671cd8d535d70efbd4ea29d4df48d17e2cd09ef4d079b0cf1902cb17fdc9fd84c9527fc7e9e2c688c5c5821dc1657cc099cac04143bfeb50bf000ebde392bca762bbf60ebae8a0b9bef0b85afbb7f613b7c462b6fd3bb69f1ab262afb20802b0fb6aae31d0aa598faa5793a93aaca8ca97a7263da034b1a01e679f0e6e9ea75c9e97559c52849acbb99a45b09a175799207698b7719831b3957b0194fcfc9443c3934012928b099151368cd15f898c5082f1897f8ad67f63ca7c935c7b8b0679a36478a1ac7501a76ed6246be62c6a912169a89368506b67e51f67446f655f88639eb4626cfb62359c5f6def5f43e55d68a85cd3e95c9e055ac87c542c105314535090b74d0b444a9aff444adf3ff1e93fed6c3eb31f3d1eb93d01f13bc68a3337722c98132b448629532927889e2596c023ee5d22abec2288f11e3d121e2c1f1ddaf01ca4b41a01ba15935a1508e514e25a13b06e13986d0c37820949ec08ee6407ebc70675c705f336
 | 8 => 0xff8f9cfefceafe6cf3fe6959fd8704fceca2fc8ac8fc79d5fa529cf91bb2f89542f87e42f7fdaff7063cf69b56f6943df4c39ef17f9ef0c79bef659def1effee3fd1ee0dafed195cecafb0ec34d4ec2172eba5cbeb52d7eb0af3ea5404e97e49e8ed06e8de1ee83a6ce6ffc1e52287e4a92be3c122e23d29e1eb57e1c087e1623ae0d5afded781de94b1dc2cf6dc1558dbfd92da3a56da17c3d8fbbad8dab8d871dfd806cad7fc48d7dec2d6c4f0d65ed7d60bc2d5fe63d5c58ad579e4d5451dd4dc06d393b7d34f5cd30b60d0b872d03ec0cfcaafcf851ecf4f81cd9116cb3f43ca8347ca5fc5c99385c987f7c945d1c7b4e7c6f97fc5e66bc5a3c4c56eddc5440dc3da0ac3c8f9c2cccdc1274bc0e64dc03c39c01e69bfdcd5bf9cfcbdf4e4bcdc73bcb9c2bc6ad6bbf565bb8e24ba8985b9f002b6d5f1b6d319b66465b49c9eb4545ab44a6fb3de15b28c75b28aecb12a4eb0c925afeec9af99e8af3ff0af1520ae3357ae32e8ae0cb1ad66b8aca059ac3d67abebadabc755aaaa01aa5373aa177fa9fce5a96e0fa8e4caa892d7a74c7fa72787a68ad5a672b1a66289a63798a5c678a49bf7a489e3a40e60a3a1efa371e9a195d3a14a78a14183a13c0ba0b7aaa0b13ea05e65a04f1ca035789d45839c5bff9b45e39a99b999a55d998a02991312982f1a97d2a7977d1196e2f1963b2a92b5dd911d92911cb8904b3f900dba8fe0568fa1668f6f338f1cc98e122b8dd6f98dd2938d73028d1ed68c90ca8bb57f8b62908b1b8b8b0f0a8a682c8a2ede88a745889cb0855c7c83f50982a84e81f95681a3ba81924481201e8061967f28667ec59d7e6c1d7d032f7c905e7c0b5e7ba2597b75257b15ea7aa8967a830679f65879176178436477e7e477c55c77a80c774832772eab75f493743c1e737f4871fbae718c6e7037667018cc6dc4586d86da6c77386c12716bb8b06a401d68bc046896b06714c566fa646669f265f12d651d3f6454e963f06463438f60eb8460932d605bd46055515f7e445f3fdf5f21015e99705e75ee5dc39d5daaca5c8e4c5b4af15a10c459e9df5973cc5829cc5722bf56ba0e56748d54fc7654e39b5488b95452625432c753f25853dc4552fe1751c10c5198c1518d2e5148475023294fc2404f570e4ed1144e049f4df2014daa5e4c71b04c45714b6c804a266448fcf1488b3248825d486a834860984839fa4818bd47ff2f47fa6947f6494794b04788ba45e2ba45bb5f43e44e43e1d7431e0742a82f42a19a41e83a413491408b214053904001d63db3643d09743cf7523ca9003b195a38c48138bf3637d5b236740436447f353d9334dbb9337be5335a5832b044320dc231d04231a851312de430b5312ff62c2fb3cd2f6de52f21932f10f32f01182ecfe92dc9822ccdbb2c4e612b2a1f28f6c9275ea026d7d226c865245612243be823e7da23d2e023855c22959421e38d21527220fcc7209c021eb1721cff6b1c88451c393b1bded51b60eb1b5c3e1afef71a791f1a1cbf16a251152bd715227a151c5e14ca88148de613afe412fa0111c5a80f458b0e2aa20dcde90cc9620c74a60c54d70c53e10c533a0b83d80acf8d0a35940a08a409ceeb099a980964df0886d70881a807f3b40573d9053bec04c3220435b700ee5400ddba00bdc30082f1
 | 9 => 0xff8fc1fefdaffe511bfd8a16fd011dfc5ad2fc4cb8fbdf21fbd69bfbb472fb7326fb275dfb168efaf86dfaccf6fa78b5f9429df94031f8f8f7f86a98f816bff7bda5f7b803f778cef72714f6e8a8f621e7f49870f46c33f3ce3ef2e7e7f1d1acf13f9af1253cf1157df0b8d1f07462f054a8ef7a1def3fbfeeb3adee9a0aedb5b5ed8518ed74a3ed286dec4fc7ec3454eba549eb51d0eaad8aeaac83ea17e4e91868e8df0ee76faee61dcbe53c02e53861e50dd6e4f870e4a2c6e449c8e3ac8ce313b0e31144e2d000e29ec1e26b85e15441e10d9ce0bed7e092eee03e29dff2fadf9b82df6a58ded45cde9017de8accde0348dda2f6daee5cdaaa9adaa897d9f124d994c3d95c7dd94b30d8fa83d8e8b9d84fa6d849ebd82213d81bf6d757c7d7562bd74fc1d66b4fd60567d5b5a0d3f7e8d3e8f7d25904d21a7bd16e9bd14fcad0cf73d031f7d01e8acf5b99cf288fcf1392ce3dbfccdb41cc6931cc36afcb847ecadeafcad33eca8feaca8ae6c94aaec8612ac8232fc80114c7f6cac73430c6e34fc6aa11c4f9c1c4bf6fc47badc45c66c450f6c365d6c35694c32d90c30b8fc27602c1ed09c1c269c01b97bfaff0bf51fdbf1d2cbe7ec1be2c1dbdc8fbbd02abbbe6a2bb7d0cbb1bd7bab2b3ba2220b93398b8f6aab87951b8748bb7d1d5b7d007b6965db65cdcb607c2b5cbe8b5838bb44e37b3d9c4b3a210b38869b2df1fb2c9e3b27dd0b23a69b19698b07bfeb0507baff20faec5bfaec28dae8fd9adbef7ad7174ad6e2facdca2ac7993ac72dfab7583ab6af5ab31a9aa1ebaa9ecaaa93ea3a87d47a82ef5a7fd30a75e79a6ca3ea6a031a637c2a5f988a578e3a4eceaa4bc0ba3f17aa39ff4a32721a31a26a2d937a287e4a27627a26d91a23dcfa1a8069fa4aa9f9cfb9f1d129f00929ee04d9ead679e36399de9ab9db1b49d8f649d73239d597c9ced4b9cb71e9cb0329b12ea9a218e99fead98e5c59895d7985312981d7a9735579660a296572196488a962c2394c12f941bc893054992a3b1928a4e924e5a91427d8fca9b8fc40a8fbf2a8f16db8ef9098d94e98d7d388d23a18d222b8ca3818c3ea48b27b08afb038a94fd8a377f89e5ad8966c988d1a588b69788074c872b7886d1d7868cd7868831865cd185a5f9853b6584b3098481df815a338124e28031b57efef47ebf467e63397e2e0d7e12137dbfe07cd65c7c74c47c694b7c67487c5b617c316d7b91207b14527b139079daa779d66979b0da79898d78ca1c77bf8376be957473e574121f73ee4d73b1ab73829d734790730410725a1b71d9c97140da70fd1370fc8b70a52470a2ea7056e16ee37b6eab366d88616d69336bf3836a6bd96973ed695cc06844a968368f68056567ff2067f3af67ec85677d0067452c66ebb7663a5e6630a4655826653dc0650df16434b363d66663c4aa63abba63a77c635aa063570c6256e961a7f85feace5f5a025f15f85f0d035ece375e87d15d6dee5d5bb55d18a35cd5235cb10d5cae825b85155b80f15a85425a28a159f86b5972b058df7b587c4958728f586539573a4657153156661d5476405422e853a760536f615303b45288fb524db25207a251d67850d0a450af405035104f96634f952a4f89ab4d79ee4cf7734c8f7a4be63049bbe14990294975dc48e70b48dc15488b664817f048082747b8394761694685e4464e3645e94b45dcb745cd7645986d45423d453fd944cae644c9ca445655440bea43f9b4438582437e15435b684343c343403943111941dd7141dad54191454184584132943ee8303e988e3e429c3cfbac3c1ec53c1bce3bc7fa3ba8963b74a23afd693aceb43a317b39a4f638c5183807a3373d4a372ae6372a0836c886360c8135e8ff35be2f345f25326aaa326282323d5d323b2831894c317ddb30584f30171e2fdae42fac842ed2a52e9add2e5fd92d33e42c6f872bc5732ba45e2b741a2b4b802b07032aad222a4412296cd128cda2284e6c26de87266673263d16255e5b249fc7247d1324028e237ffc23050e22d033216d622130ba20fbf91fe23a1fdd941eb7041e31d21deee91da26f1d23701c7c7a1b7a4b1b799e1b2f131aaf96195eec193c9c18c93218a3b817c6a11774e717580417546316658515beae15bcab159b2c15705c15452d148d67141c111418cc13ab9f133de413300a121f7f12159211e35f11c49a11bad10f7bc30f5e8d0f2f6e0f27e40f0f1b0dec920d17950d03dc0c21b40bf31c0b62470b3de50b1cd00b1b710b01cd0a448109d382084cc908244b08009907bffc077382073f8d067564067044064d8d06008d0586b805002604e29a0215fa01a4ff0180bd00dc77
 | 10 => 0xff732bfd56a3fac2a2f8f1eef8a996f87045f7a59af74bf9f625d7f5e31ff56285f1f7cdf085bcf03c43f0027def5bbfef2ce1eea82fee21d7edc80fed3c93ed2f69ece36decc420ec9e3dec7361ec0540eb0b6feae6dbeaaabbea54c9ea508bea03afe98b9be727b6e64f87e5cb38e55fa3e493b5e3c1b2e37e32e2c301e28590e27e2ee1abb2e16eccdf37a0df2558dde355dc99ebdc597bdbc8e0daeef0d935b3d8b0b1d87f87d69533d623e5d47bced444cbd3bfc9d33f90d2ae64d064f0d0209acf901acf30b6cd5fcccaff64cad318caa2c3ca06f6c9ecd2c99a8cc8e850c7b2cbc72cb8c601b4c5a287c373dfc2c7d4c2aa12c0fb39bfc515be8ffabe840cbe3bb6be15debd9582bd90dcbd7195bb0cfbba7bcfb89befb8325bb831b4b758e3b543ecb36ff3b0fdcbb0e352b0171dafd2c7ad63eaab48d6aaab9da99628a8d6cda8551fa7e449a7a508a74d12a70b60a6d426a686a3a48ab2a32833a26d029f4cc79d23c29d09b29bee3c9b3d5e9ab46599e6f398c88e97e4889734fd96f37995d87d95ca0792123a91aadc90dc738f3a1b8ed8cb8e690b8e4c518e1c918df4708d32b78cf69c8ba9358ae8d88a7d198a57ac880e38875735869256868a6d8686538638d084c891843cdf83aa2c825d8181eb7a816d9d80c48c807a4c7fa2067f6f167ec0e47e66b47d91b77be34d7bdbc47a535a7a21c279992078a9de787abb75c1db758aaa755cbc74b9eb7428bf73757671fadf71df4b715699714504705b806fcdc36d9f346d4bdc6cc6da6c51b16ba17f6b53156af2d76ad8b86a09d969bcbf69ba536940296891f768868667c065669c096441e464246d635c5962ad09621c76620fae5ff43f5f54335dff3a5cae765c845c5b42e15a9206593624584ad155ecfb53daec52a623523c035191785187be5138f94f0a394cb5c34b939e4b687e4b53364b24bc4b21774a707d4a0ee549d69f496c80491e3d48961846308f459db84513f444720a42241c421be44173983efe7a3e5af83df8713de0153cb0d13c5d983af32436065a3385b133616f31cb0a3139eb3095b93001a22f6ecb2ea63f2db65b2b95f92a6f44284845282c0b27c98426f6d22665a626460a26286325a03a242437241c3224028b238b7623594122820021639b20ca9d20094b1f9e401eb0a71ea6191d92421c16811b9c1d1a15ce18f7691878121673aa1583c614aec912e7b310e65d0ff9760ff1640fee050f7ab40eb05b0e586c0d31400c53130b34ae0ad98709b8e607273506dac40450c403e3ec03ce5f037f6b031dd303047002cc0102342d01bc9f0115c800d9d1
 | 11=>0xff52edfb62fafad1cef8885af7048ff4c9a1efe938ef3b06eacd7ce3ef98db935dda83fbd83a87cf2ecacbbd03c8c4f3bf16e3b8ffddb6aab1b617daaed51aae7293a8e7f6a2452c9f0eb79b98e096a28592fc2291ddbd88dfca8569f374cae672ae4f718fea6dd0c56b3cc4696c10667e626271ef5d3e425b24dd56c9a955d9c5504f7544beed4439eb37a6da367bd631755b303f372efe2e291611215d741dde0c1950ef1785820af88e076d9b028c5c
 | 12=>0xdf64b6d6f8847b72b03fa8ec2f91050f88d90c1302
 | 13=>0x4fded8
 | _=>0
def PG:Nat->Nat
 | 5=>0x142600003829
 | 6=>0x1147b000228a10001a83100005ca100019ca90000c459000088510001d4a100009451000050a1000008a100019ca1000228a9000184a90000e83b0000dc3900022c5500010c590001ac71000184a1000178a10000f0a1000128590000b861000058a900011479000104a100004871000008a90001148b00005431
 | 7 => 0x3ac6a0003603b0000bc550001c49900055cd10005e071000554d9000190510002c4d100024c75000360a30005e8260004fce10004f8d90003609b000618d1000200a3000288bb0002582500002055000260bb0000d4d10002883b000230d100022471000464d100022cbb0004e02d000200bb0000a499000440e1000404410000d82d000340990002582d00018cd10002003b00040899000590410002889b000580390003bcd100047451000160d10003bcd900046051000510810000782d0003b0e100062cd100053041000388d100038ce1000340310001f0710002009b000358e10003e026000164390003104100005c75000324d900039851000300d1000474610001e89900010459000304d9000300d9000474d9000360390002e0e10000503b0001c0c9000344510000fc3900037c750002a8e1000030bb0002602b000144260005bc55000250e10005bc570002042600059475000200a100002c510002609b0001a041000104990005343900001439000474d100048cc9000460d1000308d10002d0590003d0d100016ce10002d0d10001f0990004f475000134d1000544d10000e0260000503a000358d10003389b000360a1000388590000a47100026831000344d10000b0e1000224310000d451000300590002249900033873000024d90000902d000368d100001ce100061431000610410003407100062cd900005053000600d10000e83d0001a4710005bc5600039cd10001e8590005c8d90005e09900062c51000360bb0005a8d9
 | 8 => 0x65c3f000470f300021c250007a1110003b83900081853000678c900021851000818cb00020d0900024c260002847100057909000761190006f05600015d09000370d3000708d10003f9090001e82e00013c2e00001c79000330f30006e90900031c39000200550000804100001d0900048c6a00077d010003d4f30006e911000045090002fc510003c0f30002ccda000640530003910900045c92000080c90000bd09000648aa0006783100005c55000680d1000860c90002545100029cd30000982e0001d42d0006611100065cd1000284390000650900027851000830a1000330eb000218990006d8c9000645090005dc820006ccd10001287500008051000314db0001402d000304f3000238e3000210eb00083109000518730003c0cb000601190005f9110000d4260005d9190001bca20007a079000380920006e42e00087c510007a1090008609900050c410001bcdb0005ad190006b09d0008590900028cbb00054899000178a200057d190008410900026cf3000570d100074909000238f300055d110001e42e00054d110005c026000210f3000508c9000779090002d42600014cf30004c42e0001e8fb00048cac0003d02e0003c03f00077c99000060530004c84100072c5300028c300001bcf30001b8d300019d090004707a0002e0260005842d0000a5090000d8a20000d4da00074cc90004c1190007751900028c9b00006073000194bb0000e8d30000acaa0000d8db00026ccb00017cf30007449900052c3d0003a4c9000178f30006f855000304d30008447900047d19000420560006cd0900008cf3000040d10004f0c900082c7900045441000178530000509900013109000224a100012cdb00068053000009090007203d0003d47a00048c260000f509000040f30005c45500002cc9000194300000e8f30000d8f30006007100072c2b00088ccd000790790001b89a0003e11900066ccb0003d4d90008aceb00066c730000acf300028c2f000374790000d8530003dcc900008ceb0003a4410000809900026c3f0005605600038d0900063c3900002d090000e50900082875000040eb0005703f00056471000178cb0003189900080875000218c9000541090003c05b0006e8790006803b0001b85a0002ccaa000304d100048cbc0003c0d300007c3d0003dc990002b8790002e9090008acdb000380260008182b0002fd1100008829000390c9000674750000d099000630530002d1090002b9190003c4cd0004c07100046ca10000d8cb0004bc310004f051000818f3000254c900049c4100072c29000285090002791100046d0900022909000218410006bd0900048cc40004bcc9000229110006f0550005c8260007a511000215190001bc7a00088892000508710006f0570004290900020111000794f30004b9090004cc510003c0590001dd110001b8560001787a000678990003c0d10001d1190003b07900074c99000425090001bcd9000680390003b10900027c3d000680d30001946000072cf30006403f0007fc3900077c710001502e000648da000548c9000210d300065cd3000708f30005a03d0004842e00070c390006f4d300048c840006e10900014841000640d300000105000050c90006f0f30006d909000155110002809d000390510006d0f30006282e0004082e00045c260005dcaa000794cb0006b8f30000d87a0000d4aa0005cc7500019cc9000119190000ac82000680f300077cc9000778a100066cdb0000e8d10001909900065cf30000d8d90003045b000064790000bd19000570d3000640fb000375090000a919000630730008182a00062cf300007c2d0006642d00029c3f000824250005387500014ccb000050410005605a0007c42e0006f49a00029c53000210d10005dcf3000868490007943f000205090000d0c9000025190005b4db0001947c00028c9400072ccb00088026000858790002b90900065ccb0006f42e000570f3000708d300022509000560fb00080049000470a200026026000865110002ac71000845090007dc410008591900003d41000868cd00082d090000949d000310750005c0920007202d0004cd0900042055000680cb00031c710008882e000254710003d9090001c8c90005189b00030459000420570004bc990002fc71000194940003d4a2000774e10003ec750004f039000791090006d03e000040d30003d4db
 | 9 => 0x29133000044b4000450cd000118ac0002853b00006cc9000435590000b0c40000ad490002813b0000b0740001fcd30002dd0900042d1100021ccf0001f52b0001e90b0000a0fc00026d33000324740002e4710001389d0002c94900004c3b0001610b00025d330001d0eb000010f40004d03c0004947b00009901000241330004ecbc000470730002cc530002c4920000b959000074fc0001b52b0001ac55000235330000a8520004bccd0002b0920002dd0b0003249c0001ac570001a91b0003b82e0002251300021d130003b0e100019d230004d0a4000050a2000184c90002050b0001d94900019c82000044c40001fcf30000dd490001f52300006c990001e9330001e50b00005901000409010004d49c0001043c00017d23000299010003d45100025c530001d0e3000160da000370e100003871000398c00001743b0003b1050003c0710001691b00038d59000010fc00004c520001552b000151130001b5230002cd03000374760003d4730000bc75000074ac000460f4000130c90001ad330004ecc40003cc550001a9330003d5030001352300019d3b00036909000324a40002d50100008c750004d053000334aa000320dc0000a9030004d0c40003247a0001fc6a0000447c0001e853000114db0001d85100017d13000284ce000179130004d03a0001749b0001751300025d030003e9030000c4cb0002cc510003343e000204ca0004dd4900016933000161330002f8ac00006899000155230004814900015133000104e3000010ac0001453b000368550000f52300041476000018940004ec8400017439000460fc000135330002e4990001043a0004ad490000e11b00004d0300017452000495090000f4520004707100021ccd0000b09c0000a8d20000102600025c51000114f30000c52b000260720001e9030004d4940000b5230000b0db0002e55100049c710002047a00007c550003490300000099000398ec0003c099000290aa0000b4820002a0a10004394900029079000078d2000104f30003b4a1000150920004310900017cca0002c511000408710000f533000174990000791300026ca20000e90b000418990004504a00011454000314cb000071230002b4d20000e1330003b549000050da0002014900004cd200016873000309030001e851000174ca0000651b00004430000044a20004b4990000c5230004887500027d590002e43900017c3e00004d130002609b00044d0900010c920000b53b0000b0f30004104a00026d110000a933000098c900009d3b0003ec2e0004950b0002dd03000050d20003a8550001fcac000398fc000320ec0004402e0002610300021c3700036c4100029941000018eb0000152b0000793300000923000071130003b159000144ce000185010004ece300026c3f000204760002907b0002350b00005549000065330004310b000058c9000008da00036d0100038d4900020159000051330001fcd100004d330004d4eb0001e9090001b0a1000044f30001ac560000a851000260730004b91200037159000494da0001510900002d0b00013101000468c9000324c40004a92300044d0b0002190900001d13000018e30001b159000320fc0000153b0001a87b000174cb0000746a000009330002a4ec0004710b0003542e00046d2b0004ecf300019101000169030001a90b0001d90100018441000160aa000060920004512300044d2b00042cd20003843e0003e8cb00004c510004d4fb0002f8c40004d0f3000070ca0001043b000431230003cc5600042d130000f45300022503000118dc0002809e000278c900015d59000411230004a91300009cce0002cc7300034c940001710500015111000495330003247c0000a85300026099000038c9000320ac00013041000444990004753b0004713b00046d3b0004147a00034c9c0002cc520002a4fc0001510b0003e92b0001d0cb0004c5490002b4d10001fcbc00031d490004511300044d230003cc5700037c3d000174c900031494000298990003d5230004d03b0001114900036856000431330002f8840001b50300042d3300025c73000198cd00023509000208c90002a14900046d090003d452000291090003ad2b0004153b0004113b00025c5200004c53000450cf0002789900024c550000448c0000687100038523000260710000a8a20003f10b00021949000104390003e923000110750004a8ca000284420003685700037523000175030000f451000148cd000249490002b50900046d0b0004083900002c9e000480d1000241090003690b0003dd13000074dc0003d5330001a8790001fcc40001cd490003cd330001e873000174530004d0cb0002395900019c76000078a2000104530002b4d3000104cb0000f4730001e8520003ad23000334da0001a9090000f50300020899000324a200034ceb0003492b00000071000044a4000050aa00004ca200007d590000709e0003853b0000791100004c710000447a0004a88200016ca100036cc90004c5090002910b00037513000474ce000408c90004d0390000c83d00032912000314eb00036933000010dc00025c710000a82900004d110001b1490003092b0001fc840004ecac00016d490000a8730002fd230004b4710002f8e300046cd1000469010002b50b0002e92300034ce30002410b0003314900046cd2000174510001d094000470720002dd2b000335330004dca1000324f30000c50300016509000001510002c51300041d010002b91b00019071000055010002b52b000290da0001e87100046cd30004b8da0003090900004c39000161090004d080000039010004aca10004dd59000118fc00004c73000494aa0003090b000114c40004947900026cd2000224cb0002fd33000285230002f8f3000374ca000281230003e8c900027075000178530004a8760002e93300026d1300049d010002610b0004b551000280aa0000a82b0004602e000104c4000468410003c5010000b4760002c951000074ec0004709b0001d09b0003a546000241230002cd330002c533000410ce00030d4900042ca20002b9330003d453000165490002b5230002351b000471030001b4cb0002252b000398bc
 | 10 => 0xb8790000616b00005d6b000059230000a07300009cbc000050990000c83d00002cac00005caa000060cb00005123000081020000350300004c570000d943000034540000207c00006d5300009477000098ce0000e4ec0000343b00004d4b0000e0d4000024940000697b0000d85300006533000049630000dcb4000030550000509b0000009e00006183000044db000048aa0000411300005d8300007874000024cb0000591b0000947600002d0b00009cdc0000bca30000a0d20000b87b0000a0990000c8d4000080aa0000513b00006cce00003057000034d20000789c00004d7b00009cc0000049830000395b0000a1510000e4fc0000e0fc0000dcc4000044f30000589e000041330000c12c0000d8510000250300008c3e0000b8ec00009c6a00006143000058a000008c400000314b00002d1b000040540000649c0000d1010000c8fc0000b52c0000252300007cdc000020db000051030000397b0000a09b00003533000078a40000e4ac0000e0ac00001d6b0000dc7c000064cc0000809e0000204c0000c13c000031830000a92c0000b8fc00002d330000155300002499000061010000251b000054f4000020f300009cec0000343a000061020000b53c0000bd49000034510000b9090000d10300001d63000050c9000064dc00006103000050ca0000c0dc00001983000068a1000064790000b8ac0000157b0000a93c0000443c00009c5000000163000050cb00000d4b00001cce0000e96b0000c83e000050cc0000149900009cfc000000aa000040520000249b0000e50b0000d1430000e11b0000dcdb0000343c000034bc000054f80000bd4b0000345300007cec0000b90b0000e0d2000044a40000a072000030560000054b000014920000a0510000d16b0000cd630000b0550000c83f000001830000387200004d4900008cfc000068a30000e9530000647b00009cac00002c54000040730000e5330000e1330000853c00006ccd0000dcf30000208c0000d8cb0000d953000034d4000041030000b057000034a20000149b0000e47100006ccf0000d0c900007cfc0000bd6300004c55000078c40000d1630000cd53000019060000b91b0000589d0000389b0000c9330000bd120000a1430000d85200002cdc0000589f0000a0530000e46a00004053000039430000b14b000020a40000e9020000552c00000cce0000bd7b00007cac00005c9e0000b9330000787c0000d8c9000020900000e09c00003873000094750000d0cb000034730000a10a0000d902000024ca0000e473000064fc0000cd02000044bc0000a15300009d1b00007494000044540000489e0000ad830000e0cc000069490000553c0000955b000065090000407100009c6c00001551000034ec00008c3d0000154300008d23000064ac00008c3f0000a17b00009d33000044c4000040fc00003899000024cc00002cf40000994b0000957b0000e4dc0000e0dc00001ccd000081630000589400002c740000dca4000040510000d90300009c4f00007d1b000078db000020b40000e89e00001ccf0000694b000050940000650b000034fc00008d330000a0520000a0710000e5090000447c0000b0560000c840000038710000e503000081530000cc9e0000ad06000034520000203800002cfc0000343900007d33000078f30000c8a80000d1020000c114000020c400006d6b000034a40000b8dc0000d901000024c9000060c900002d09000069630000bca10000651b00004c56
 | 11=>0xca400000c3e0000085200000839000014c00000113b00000478000008a400001462000000fc00000903000008540000083b00000d1b0000046c000014ec0000091300000d33000014380000143f000014fc000000540000093300000c620000051b0000010b000014a40000083a000008510000051300000133000010cc0000083c000008530000107800000cd4000004ca000015130000107600001464000008d4000008710000003e0000153300000040000014370000106c0000087300000cec000004760000143d000004cc000008ec00000c40000014bc00000cfc0000111b000008fc000014d4
 | 12=>0xd3000000240000009c0000002c000000280000007400000034
 | 13=>0x0
 | _=>0
lemma mj:CfgOk 8 fG rG cG:=jn 8 fG rG cG (by decide +kernel)
def cf:Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
lemma bu (g:u7 8):shiftRight (eL rG cG g) cG.shTT=u9 8 g:=by have h:=my (n:=8) (n8 8 rG cG.shTT) g;rw [jj 8 rG cG.shTT] at h;exact h
def ma (all1v g:Nat) (e:J):J:=
 if ble g 32 then
  zm (Nat.sub g 1) fun c =>
  zm (shiftRight c 1) fun i =>
  let u:=beq (land c 1) 1
  let (a,ta):=jw i e
  let d:=if beq ta 3 then 2 else 0
  zm (xor a all1v) fun w =>
  let r:=ms i e
  if u then (w,d)::(a,0)::r else (w,d)::r
 else
  zm (Nat.sub g 33) fun rem =>
  let s:=beq (land rem 1) 1
  let t:=beq (land (shiftRight rem 1) 1) 1
  let v:=beq (land (shiftRight rem 2) 1) 1
  let (i,j):=gj (shiftRight rem 3) 16 1
  let (a,ta):=jw i e
  let (b,tb):=jw j e
  let r:=ms i (ms j e)
  if v then
   let d:=if beq ta 6||beq tb 6 then 8 else if beq ta 3||beq tb 3 then 1 else 0
   zm (land a b) fun w =>
   let r1:=if s then (b,0)::r else r
   let h:=if t then (a,0)::r1 else r1
   (w,d)::h
  else
   let d:=if beq ta 4||beq tb 4 then 7 else 0
   zm (lor a b) fun w =>
   let r1:=if s then (b,if beq tb 3 then 1 else 0)::r else r
   let h:=if t then (a,if beq ta 3 then 1 else 0)::r1 else r1
   (w,d)::h
def du (all1v:Nat) (xs:J) (PT:Nat->Nat):Nat->Nat->Nat->J
 | 0,_,_=>xs
 | d+1,s,j =>
  zm (sa (PT s) j) fun e =>
  zm (land e 1023) fun code =>
  if beq code 0 then xs
  else zm (land (shiftRight e 10) 8191) fun pidx =>
   ma all1v code (du all1v xs PT d (Nat.add s 1) pidx)
def ou (all1v:Nat) (b:J) (s j:Nat):J:=
 du all1v b PG (Nat.sub 13 s) s j
def sf (salt w tg:Nat):Nat:=
 zm (land w i1) fun w0 =>
 zm (land (shiftRight w 64) i1) fun w1 =>
 zm (land (shiftRight w 128) i1) fun w2 =>
 zm (land (shiftRight w 192) i1) fun w3 =>
 zm (land (Nat.mul w1 0x9e3779b97f4a7c15) i1) fun m1 =>
 zm (land (Nat.mul w2 0xbf58476d1ce4e5b9) i1) fun m2 =>
 zm (land (Nat.mul w3 0x94d049bb133111eb) i1) fun m3 =>
 zm (xor (xor w0 m1) (xor m2 m3)) fun wf =>
 zm (xor salt (land (Nat.mul tg 0x517cc1b727220a95) i1)) fun s =>
 sx (xor (xor wf (shiftRight wf 33)) s)
def p2 (salt:Nat):Nat->J->Nat
 | acc,[]=>acc
 | acc,(w,tg)::rest=>zm (Nat.add acc (sf salt w tg)) fun acc' => p2 salt acc' rest
def dm (salt:Nat) (ws:J):Nat:=
 land (p2 salt 0 ws) 0xFFFFFF
def om (s:Nat) (b:J):Q:=
 zm (dm db b) fun h =>
 zm (dz NG LG HG s h) fun j =>
 !(beq j 999999)&&jk b (ou cf fy s j)
def uh (tt:Nat):Nat:=
 lor
  (lor (land (shiftRight tt 128) 0xFFFF)
   (shiftLeft (land (shiftRight tt 160) 0xFFFF) 16))
  (lor (shiftLeft (land (shiftRight tt 192) 0xFFFF) 32)
   (shiftLeft (land (shiftRight tt 224) 0xFFFF) 48))
def a9 (w:Nat):M->M
 | []=>[w]
 | a::rest =>
  if beq w a then a::rest
  else if blt w a then w::a::rest
  else a::a9 w rest
def o2:J->Nat×M
 | []=>(0,[])
 | (w,tg)::rest =>
  let (rk,acc):=o2 rest
  if beq tg 4 then (Nat.add rk 2,acc)
  else if beq tg 6||beq tg 7||beq tg 8 then (Nat.add rk 1,acc)
  else
   zm (uh (shiftRight w cG.shTT)) fun p =>
   if beq p 0||beq p i1 then (rk,acc)
   else (rk,a9 p acc)
def p5 (s:Nat) (b:J):Q:=
 let (rk,cl):=o2 b
 if blt s rk then true
 else
  zm (Nat.sub s rk) fun s6 =>
  if ble 10 s6 then false
  else
   let (stot,items):=t4 cl
   if !(beq stot c7.lok) then true
   else s8 s6 items 0 0 0 0 0 [] []
def uj (b:Nat) (c:J):Q:=
 let d:=sz cG.shTT c
 if om b d then true
 else if p5 b c then true
 else om b (wx gG d)
def i7 (d e:Nat) (g:J) (a ta h i b c j s t u:Nat) (v:Unit->J):Q:=
 let w:=uj d
 let x:=
  if !(beq ta 2)&&!(beq c 2)&&!(beq ta 7)&&!(beq c 7) &&
    !((beq ta 4&&beq c 6)||(beq ta 6&&beq c 4)) then
   zm (lor a b) fun z =>
   if beq z 0||beq z cG.all1v||t3 z g then true
   else
     l8 cG d e w z (if beq ta 4||beq c 4 then 7 else 0)
      a (if beq ta 3 then 1 else 0) h i b (if beq c 3 then 1 else 0) j s t u
      (beq ta 0||beq ta 3) (beq c 0||beq c 3) v
  else true
 if !x then false
 else if !(beq ta 1)&&!(beq c 1)&&!(beq ta 4)&&!(beq c 4)&&!(beq ta 8)&&!(beq c 8) &&
      !((beq ta 6&&!(beq c 7))||(beq c 6&&!(beq ta 7))) then
  zm (land a b) fun z =>
  if beq z 0||beq z cG.all1v||t3 z g then true
  else
   l8 cG d e w z (if beq ta 6||beq c 6 then 8 else if beq ta 3||beq c 3 then 1 else 0)
     a 0 h i b 0 j s t u (beq ta 0) (beq c 0) v
 else true
def barG:Nat->Nat->Q
 | 0,i=>match ou cG.all1v xG 0 i with | [(w,_)]=>!(beq w cG.goalv) | _=>true
 | ns+1,i =>
  let b:=ou cG.all1v xG (Nat.add ns 1) i
  let c:=b.length
  let d:=Nat.sub (Nat.add ns 2) c
  let (_,_,cu):=o5 cG b
  (if ble 1 d then a4 (a5 cG ns c d b (uj ns) true) 0 0 [] cu else true) &&
  m4 (i7 ns c b) 0 0 [] cu
lemma JointRun.inv_succ {s:Nat} {w:List (u7 8×Nat)} (h:JointRun (s+1) w) :
  (∃ a ta r save,w.Perm ((a,ta)::r) /\
    (ta=0\/ta=3)/\(ta=3->save=false) /\
    invF a≠(fun _=>false)/\invF a≠(fun _=>true) /\
    invF a≠a/\(∀ x∈r,x.1≠invF a) /\
    JointRun s ((invF a,if ta=3 then 2 else 0)::qk save (a,0) r)) \/
  (∃ a ta b tb r ka kb,w.Perm ((a,ta)::(b,tb)::r) /\
    ta≠2/\tb≠2/\ta≠7/\tb≠7 /\
    ¬ (ta=4/\tb=6)/\¬ (ta=6/\tb=4) /\
    (ka=true->ta=0\/ta=3)/\(kb=true->tb=0\/tb=3) /\
    joinF a b≠(fun _=>false)/\joinF a b≠(fun _=>true) /\
    joinF a b≠a/\joinF a b≠b/\(∀ x∈r,x.1≠joinF a b) /\
    JointRun s ((joinF a b,if ta=4\/tb=4 then 7 else 0) ::
     qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r))) \/
  (∃ a ta b tb r ka kb,w.Perm ((a,ta)::(b,tb)::r) /\
    ta≠1/\tb≠1/\ta≠4/\tb≠4/\ta≠8/\tb≠8 /\
    (ta=6->tb=7)/\(tb=6->ta=7) /\
    (ka=true->ta=0)/\(kb=true->tb=0) /\
    meetF a b≠(fun _=>false)/\meetF a b≠(fun _=>true) /\
    meetF a b≠a/\meetF a b≠b/\(∀ x∈r,x.1≠meetF a b) /\
    JointRun s ((meetF a b,if ta=6\/tb=6 then 8 else if ta=3\/tb=3 then 1 else 0) ::
     qk ka (a,0) (qk kb (b,0) r))):=by
 generalize d:s+1=s' at h
 induction h with
 | done _ _=>cases d
 | perm c _ ih =>
  rcases ih d with ⟨a,ta,r,save,c',rest⟩|⟨a,ta,b,tb,r,ka,kb,c',rest⟩|⟨a,ta,b,tb,r,ka,kb,c',rest⟩
  . exact Or.inl ⟨a,ta,r,save,c.symm.trans c',rest⟩
  . exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,c.symm.trans c',rest⟩)
  . exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,c.symm.trans c',rest⟩)
 | @uNot s0 a ta r save _ e g i j t u v _ =>
  cases d
  exact Or.inl ⟨a,ta,r,save,lPR _,e,g,i,j,t,u,v⟩
 | @bOr s0 a ta b tb r ka kb _ e g i j t u y z h9 h0 x2 x3 a1 v _ =>
  cases d
  exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,lPR _,e,g,i,j,t,u,y,z,h9,h0,x2,x3,a1,v⟩)
 | @bAnd s0 a ta b tb r ka kb _ e g i j t u y z h9 h0 x2 x3 a1 a2 b1 v _ =>
  cases d
  exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,lPR _,e,g,i,j,t,u,y,z,h9,h0,x2,x3,a1,a2,b1,v⟩)
lemma tp:∀ r:Fin 64, m8 (q1 6 r.val)=q1 8 (128+r.val % 16+32*(r.val / 16)):=by decide
lemma um {r:Nat} (b:r < 64) :m8 (q1 6 r)=q1 8 (128+r % 16+32*(r / 16)):=
 tp ⟨r,b⟩
lemma df (g:u7 8):uh (u9 8 g)=u9 6 (m7 g):=by
 apply nEQ;intro r;unfold uh;simp only [nLO,nTO];have t:(0xFFFF:Nat)=2 ^ 16 - 1:=by decide
 rw [t];have s:∀ (e k:Nat),
     (shiftLeft (land (shiftRight (u9 8 g) e) (2 ^ 16 - 1)) k).testBit r =
     (decide (k<=r)&&decide (r - k < 16)&&(u9 8 g).testBit (e+(r - k))):=by
   intro e k;change (((u9 8 g >>> e) &&& (2 ^ 16 - 1)) <<< k).testBit r=_;rw [Nat.testBit_shiftLeft,nTA,nTB,nTS];by_cases b:k<=r<;>by_cases i:r - k < 16<;>simp [b,i]
 have u :
     (land (shiftRight (u9 8 g) 128) (2 ^ 16 - 1)).testBit r =
     (decide (r < 16)&&(u9 8 g).testBit (128+r)):=by
   change ((u9 8 g >>> 128) &&& (2 ^ 16 - 1)).testBit r=_;rw [nTA,nTB,nTS];by_cases h:r < 16<;>simp [h]
 rw [u,s 160 16,s 192 32,s 224 48,vr];by_cases b:r < 16
 . have i:¬ 16<=r:=by omega
   have j:¬ 32<=r:=by omega
   have d:¬ 48<=r:=by omega
   have c:r < 2 ^ 6:=by omega
   simp only [b,i,j,d,c,decide_true,decide_false,bTA,Bool.false_and,
          Bool.or_false,↓reduceIte,vr,show 128+r < 2 ^ 8 by omega,m7]
   rw [um (by omega:r < 64)];congr 2;omega
 . by_cases i:r < 32
   . have j:¬ 32<=r:=by omega
     have d:¬ 48<=r:=by omega
     have c:r < 2 ^ 6:=by omega
     simp only [b,show 16<=r by omega,show r - 16 < 16 by omega,j,d,c,
           decide_true,decide_false,bTA,Bool.false_and,Bool.false_or,
           Bool.or_false,↓reduceIte,vr,show 160+(r - 16) < 2 ^ 8 by omega,m7]
     rw [um (by omega:r < 64)];congr 2;omega
   . by_cases j:r < 48
     . have d:¬ 48<=r:=by omega
       have c:r < 2 ^ 6:=by omega
       simp only [b,show ¬ r - 16 < 16 by omega,show 32<=r by omega,show r - 32 < 16 by omega,
            d,c,decide_true,decide_false,bTA,Bool.false_and,Bool.and_false,
            Bool.false_or,Bool.or_false,↓reduceIte,vr,show 192+(r - 32) < 2 ^ 8 by omega,m7]
       rw [um (by omega:r < 64)];congr 2;omega
     . by_cases d:r < 64
       . have c:r < 2 ^ 6:=by omega
         simp only [b,show ¬ r - 16 < 16 by omega,show ¬ r - 32 < 16 by omega,
             show 48<=r by omega,show r - 48 < 16 by omega,c,
             decide_true,decide_false,bTA,Bool.false_and,Bool.and_false,
             Bool.false_or,Bool.or_false,↓reduceIte,vr,show 224+(r - 48) < 2 ^ 8 by omega,m7]
         rw [um (by omega:r < 64)];congr 2;omega
       . simp only [b,show ¬ r - 16 < 16 by omega,show ¬ r - 32 < 16 by omega,
             show ¬ r - 48 < 16 by omega,decide_false,Bool.false_and,Bool.and_false,
             Bool.or_false,vr,show ¬ r < 2 ^ 6 by omega,↓reduceIte]
lemma uq (w x:Nat) (b:M):x∈a9 w b↔x=w\/x∈b:=by
 induction b with
 | nil=>simp [a9]
 | cons a rest ih =>
  unfold a9;by_cases c:w=a
  . subst c;simp [nBR]
  . simp only [q2 c,bFT,↓reduceIte];by_cases d:blt w a=true
    . simp only [d,↓reduceIte,lMM]
    . simp only [d,bFT,↓reduceIte,lMM,ih];tauto
lemma up (w:Nat) {d:M} (h:d.Pairwise (· < ·)) :(a9 w d).Pairwise (· < ·):=by
 induction d with
 | nil=>simp [a9]
 | cons a rest ih =>
  rcases List.pairwise_cons.1 h with ⟨e,g⟩
  unfold a9;by_cases i:w=a
  . subst i;simpa [nBR] using h
  . simp only [q2 i,bFT,↓reduceIte];by_cases c:blt w a=true
    . have j:w < a:=by simpa [nBL] using c
      simp only [c,↓reduceIte,List.pairwise_cons,lMM];refine ⟨?_,e,g⟩
      rintro x (rfl|b)
      . exact j
      . exact Nat.lt_trans j (e x b)
    . have s:a < w:=by
        have:¬ w < a:=fun t=>c (by simpa [nBL] using t)
        omega
      simp only [c,bFT,↓reduceIte,List.pairwise_cons];refine ⟨?_,ih g⟩
      intro x b;rcases (uq w x rest).1 b with rfl|b'
      . exact s
      . exact e x b'
lemma uc (g:u7 6):u9 6 g=0↔g=(fun _=>false):=by
 constructor
 . intro h;rw [<- gk (n:=6) (range (2 ^ 6))] at h;exact yc h
 . rintro rfl;exact gk (n:=6) (range (2 ^ 6))
lemma ud (g:u7 6):u9 6 g=i1↔g=(fun _=>true):=by
 have b:i1=2 ^ (range (2 ^ 6)).length - 1:=by decide
 constructor
 . intro h;rw [b,<- bc (n:=6) (range (2 ^ 6))] at h;exact yc h
 . rintro rfl;rw [b];exact bc (n:=6) (range (2 ^ 6))
lemma en (t:List (u7 8×Nat)) :(o2 (eW rG cG t)).1=e9 t /\ (o2 (eW rG cG t)).2.Pairwise (· < ·) /\ (∀ p∈t,p.2≠4->p.2≠6->p.2≠7->p.2≠8 -> m7 p.1≠(fun _=>false)->m7 p.1≠(fun _=>true) -> u9 6 (m7 p.1)∈(o2 (eW rG cG t)).2):=by
 induction t with
 | nil=>simp [eW,e4,o2,e9]
 | cons p rest ih =>
  rcases p with ⟨g,tg⟩
  obtain ⟨h6,u,v⟩:=ih;have h7:o2 (eW rG cG ((g,tg)::rest)) =
      let w:=e9 rest;let x:=(o2 (eW rG cG rest)).2
      if beq tg 4 then (Nat.add w 2,x)
      else if beq tg 6||beq tg 7||beq tg 8 then (Nat.add w 1,x)
      else
        zm (uh (shiftRight (eL rG cG g) cG.shTT)) fun p =>
        if beq p 0||beq p i1 then (w,x)
        else (w,a9 p x):=by
    change o2 ((eL rG cG g,tg)::eW rG cG rest)=_;conv_lhs=>unfold o2
    rw [show o2 (eW rG cG rest)=(e9 rest,(o2 (eW rG cG rest)).2)
        from Prod.ext h6 rfl]
  rw [h7];simp only [e9];by_cases z:tg=4
  . subst z;simp only [nBR,↓reduceIte,v8,lMM];refine ⟨by omega,u,?_⟩
    intro q e b h i j c d;rcases e with rfl|s
    . exact absurd rfl b
    . exact v q s b h i j c d
  . simp only [q2 z,z,bFT,↓reduceIte];by_cases y:tg=6\/tg=7\/tg=8
    . have h2:(beq tg 6||beq tg 7||beq tg 8)=true:=by
        rcases y with rfl|rfl|rfl<;>decide
      simp only [h2,y,↓reduceIte,v8,lMM];refine ⟨by omega,u,?_⟩
      intro q e b h i j c d;rcases e with rfl|s
      . rcases y with rfl|rfl|rfl<;>contradiction
      . exact v q s b h i j c d
    . have h2:(beq tg 6||beq tg 7||beq tg 8)=false:=by
        simp [bOF,zh];tauto
      simp only [h2,y,bFT,↓reduceIte,v5];have h8:uh (shiftRight (eL rG cG g) cG.shTT)=u9 6 (m7 g):=by rw [bu,df]
      rw [h8];by_cases h5:u9 6 (m7 g)=0\/u9 6 (m7 g)=i1
      . have h3:(beq (u9 6 (m7 g)) 0||beq (u9 6 (m7 g)) i1)=true:=by
          rcases h5 with h0|h1
          . simp [qz h0]
          . simp [qz h1]
        simp only [h3,↓reduceIte,lMM];refine ⟨by omega,u,?_⟩
        intro q e b h i j c d;rcases e with rfl|s
        . rcases h5 with h0|h1
          . exact absurd ((uc _).1 h0) c
          . exact absurd ((ud _).1 h1) d
        . exact v q s b h i j c d
      . have h3:(beq (u9 6 (m7 g)) 0||beq (u9 6 (m7 g)) i1)=false:=by
          simp [bOF,zh];tauto
        simp only [h3,bFT,↓reduceIte,lMM];refine ⟨by omega,up _ u,?_⟩
        intro q e b h i j c d;rw [uq];rcases e with rfl|s
        . exact Or.inl rfl
        . exact Or.inr (v q s b h i j c d)
lemma es (v:∀ s≤ 9,∀ i < Nf7 s,bar c7 findF7 getF7Enc s i=true) {c:Nat} {b:List (u7 8×Nat)} (w:F7Ok c b) (d:p5 c (eW rG cG b)=true):False:=by
 obtain ⟨hle,L0,x,y,z,h0⟩:=w;obtain ⟨h1,h2,h3⟩:=en b;unfold p5 at d;rw [show o2 (eW rG cG b)=(e9 b,(o2 (eW rG cG b)).2)
    from Prod.ext h1 rfl] at d
 have h5:blt c (e9 b)=false:=by rw [Bool.eq_false_iff];intro hc;rw [nBL] at hc;omega
 simp only [h5,bFT,↓reduceIte,v5] at d;cases j:ble 10 (Nat.sub c (e9 b))
 . simp only [j,bFT,↓reduceIte] at d;have h9:c - e9 b<=9:=by
    by_contra hlt;have x2:10<=c - e9 b:=by omega
    have ht:ble 10 (Nat.sub c (e9 b))=true:=Eq.mpr nBE x2;rw [ht] at j;cases j
   set e:=(o2 (eW rG cG b)).2;have x3:e.Nodup:=h2.imp (fun h=>Nat.ne_of_lt h)
   have a1:(!(beq (t4 e).1 c7.lok)||s8 (c - e9 b) (t4 e).2 0 0 0 0 0 [] [])=true:=by
    cases t:beq (t4 e).1 c7.lok
    . simp
    . simp only [t,Bool.not_true,bFT,↓reduceIte] at d;simpa [t] using d
   have a2:∀ g∈L0,u9 6 g∈e:=by intro g u;obtain ⟨p,hp,h4,h6,h7,h8,rfl⟩:=z g u;obtain ⟨b1,ha⟩:=y (m7 p.1) u;exact h3 p hp h4 h6 h7 h8 b1 ha
   exact oc v h9 e x3 a1 x a2 h0
 . simp only [j,↓reduceIte] at d;cases d
def mc {n:Nat} (h:Nat) (e:List (u7 n×Nat)):List (u7 n×Nat):=
 if ble h 32 then
  let c:=Nat.sub h 1;let i:=shiftRight c 1;let v:=beq (land c 1) 1
  let (a,ta):=ki i e;let d:=if beq ta 3 then 2 else 0
  let w:=invF a;let r:=yl i e
  if v then (w,d)::(a,0)::r else (w,d)::r
 else
  let g:=Nat.sub h 33
  let t:=beq (land g 1) 1
  let u:=beq (land (shiftRight g 1) 1) 1
  let x:=beq (land (shiftRight g 2) 1) 1
  let (i,j):=gj (shiftRight g 3) 16 1
  let (a,ta):=ki i e;let (b,tb):=ki j e
  let r:=yl i (yl j e)
  if x then
   let d:=if beq ta 6||beq tb 6 then 8 else if beq ta 3||beq tb 3 then 1 else 0
   let r1:=if t then (b,0)::r else r
   let s:=if u then (a,0)::r1 else r1
   (meetF a b,d)::s
  else
   let d:=if beq ta 4||beq tb 4 then 7 else 0
   let r1:=if t then (b,if beq tb 3 then 1 else 0)::r else r
   let s:=if u then (a,if beq ta 3 then 1 else 0)::r1 else r1
   (joinF a b,d)::s
def mt {n:Nat} (b:List (u7 n×Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (u7 n×Nat)
 | 0,_,_=>b
 | d+1,s,j =>
  let e:=sa (PT s) j;let c:=land e 1023
  if beq c 0 then b
  else mc c (mt b PT d (Nat.add s 1) (land (shiftRight e 10) 8191))
def m5 (s j:Nat):List (u7 8×Nat):=
 mt g5 PG (Nat.sub 13 s) s j
lemma ra {n:Nat} (c:M) (b:Nat) (d:List (u7 n×Nat)) :ma (2 ^ c.length - 1) b (e4 c d)=e4 c (mc b d):=by
 unfold ma mc;simp only [v5]
 split
 . simp only [fu,ft];split<;>simp [e4,rd]
 . simp only [fu,ft]
   split
   . cases beq (land (Nat.sub b 33) 1) 1 <;>
     cases beq (land (shiftRight (Nat.sub b 33) 1) 1) 1 <;>
     simp [e4,q9]
   . cases beq (land (Nat.sub b 33) 1) 1 <;>
     cases beq (land (shiftRight (Nat.sub b 33) 1) 1) 1 <;>
     simp [e4,qc]
lemma aj {n:Nat} (b:M) (c:List (u7 n×Nat)) (PT:Nat->Nat) (d s j:Nat) :du (2 ^ b.length - 1) (e4 b c) PT d s j=e4 b (mt c PT d s j):=by
 induction d generalizing s j with
 | zero=>rfl
 | succ d ih=>simp only [du,mt,v5];split;rfl;rw [ih,ra]
lemma cs:xG=eW rG cG g5:=by decide +kernel
lemma ak:fy=u4 8 g5:=by decide +kernel
lemma tz (s j:Nat):ou cG.all1v xG s j=eW rG cG (m5 s j):=by
 unfold ou m5;have b:cG.all1v=2 ^ (aR 8 rG cG).length - 1:=by rw [zl,mj.all1v_eq]
 rw [b,cs];exact aj (aR 8 rG cG) g5 PG (Nat.sub 13 s) s j
lemma oz (s j:Nat):ou cf fy s j=u4 8 (m5 s j):=by
 unfold ou m5;have b:cf=2 ^ (range (2 ^ 8)).length - 1:=by rw [lLR];decide
 rw [b,ak];exact aj (range (2 ^ 8)) g5 PG (Nat.sub 13 s) s j
lemma mu:de 8 [(0,3),(1,5),(2,6)]=gG:=by decide +kernel
lemma cp (x:F 8):zc [(0,3),(1,5),(2,6)] x=d3 x:=by funext i;fin_cases i<;>rfl
lemma sr (g:u7 8):ym gG (u9 8 g)=u9 8 (fun x=>g (d3 x)):=by rw [<- mu,jm [(0,3),(1,5),(2,6)] (by decide) g];congr 1;funext x;rw [cp]
lemma ss (b:List (u7 8×Nat)) :wx gG (u4 8 b)=u4 8 (b.map fun p=>((fun x=>p.1 (d3 x)),p.2)):=by
 induction b with
 | nil=>rfl
 | cons p t ih=>rcases p with ⟨h,tg⟩;simp only [ir,lMC,wx,v5,sr,ih]
lemma us {s:Nat} {b:List (u7 8×Nat)} (h:om s (u4 8 b)=true) :∃ j < NG s,b.Perm (m5 s j):=by unfold om at h;simp only [v5,bAT,bNT,zh] at h;obtain ⟨d,c⟩:=h;rw [oz] at c;exact ⟨_,j8 NG LG HG s _ d,(zv _ _).1 (y5 _ _ c)⟩
lemma dq (h24:∀ s≤ 9,∀ i < Nf7 s,bar c7 findF7 getF7Enc s i=true) (h16:∀ s≤ 13,∀ i < NG s,barG s i=true) :∀ s≤ 13,∀ i < NG s,¬ JointRun s (m5 s i):=by
 intro s;induction s with
 | zero => intro _ i hi h11;have hb:=h16 0 (nZL 13) i hi;obtain ⟨tg,heq⟩:=h11.inv_zero;simp only [barG,tz,heq,eW,e4,lMC,lMN,mj.goalv_eq,nBR] at hb;cases hb
 | succ ns ih =>
  intro hs i hi h11;have hih:∀ j < NG ns,¬ JointRun ns (m5 ns j):=ih (by omega);have hf:∀ a1:List (u7 8×Nat),
      JointRun ns a1->uj ns (eW rG cG a1)=true->False:=by
    intro a1 d x2;unfold uj at x2;dsimp only at x2;have hq:sz cG.shTT (eW rG cG a1)=u4 8 a1:=by rw [eW,aR,kg]
    rw [hq] at x2;cases c:om ns (u4 8 a1)
    . rw [c] at x2;simp only [bFT,↓reduceIte] at x2;cases x3:p5 ns (eW rG cG a1)
      . rw [x3] at x2;simp only [bFT,↓reduceIte,ss] at x2;obtain ⟨j,hj,h12⟩:=us x2;exact hih j hj (JointRun.perm h12 d.map_sig8)
      . exact es h24 d.f7Ok x3
    . obtain ⟨j,hj,h12⟩:=us c;exact hih j hj (JointRun.perm h12 d)
  have hb:=h16 (ns+1) hs i hi;simp only [barG,v8,tz,bAT] at hb;obtain ⟨h17,h18⟩:=hb;set e:=m5 (ns+1) i;rcases h11.inv_succ with
    ⟨a,ta,r,save,w,h19,h25,y,c,b1,x3,d⟩ |
    ⟨a,ta,b,tb,r,ka,kb,w,hg,hh,hk,hm,hn,hr,h5,h7,y,c,b1,hnb,x3,d⟩ |
    ⟨a,ta,b,tb,r,ka,kb,w,ht,hu,hv,hw,hx,hy,hz,xi,h5,h7,y,c,b1,hnb,x3,d⟩
  . obtain ⟨g,t,v,h8⟩:=iq w;have d' : JointRun ns ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (g++t)):=
      JointRun.perm (lPC _ (by cases save<;>simp [qk,h8])) d
    have h20:=d'.len_le;have h21:e.length=g.length+t.length+1:=by have:=congrArg List.length v;simp at this;omega
    have xs:(eW rG cG e).length=e.length:=lLM _;have h26:ble 1 (Nat.sub (ns+2) (eW rG cG e).length)=true:=by rw [xs,nBE,nSE];cases save<;>simp [qk] at h20<;>omega
    simp only [h26,↓reduceIte] at h17;have ha:eW rG cG e=eW rG cG g++(eL rG cG a,ta)::eW rG cG t:=by rw [v];simp [eW,e4]
    have h10:=k0 cG (a5 cG ns (eW rG cG e).length (Nat.sub (ns+2) (eW rG cG e).length) (eW rG cG e) (uj ns) true)
      [] (eW rG cG g) (eW rG cG t) (eL rG cG a) ta (by rw [<- ha];exact h17)
    unfold a5 at h10;have h27:(beq ta 0||beq ta 3)=true:=by rcases h19 with rfl|rfl<;>decide
    have z:∀ p∈e,p.1≠invF a:=fun p hc=>by
      rcases lMM.1 (w.subset hc) with rfl|hpr;exact b1.symm;exact x3 p hpr
    have hd:(beq (eL rG cG (invF a)) 0||beq (eL rG cG (invF a)) cG.all1v ||
           t3 (eL rG cG (invF a)) (eW rG cG e))=false:=by
      simp [q2 (c5 y),q2 (a3 mj c),o7 z]
    simp only [h27,↓reduceIte,v5,(qv mj a).symm,hd,bFT,lNA,<- kj] at h10;have he:(if beq ta 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [nBQ]
    rw [he] at h10;have ⟨hc0,hc1⟩:=o8 h10;cases save
    . simp only [qk,bFT,↓reduceIte] at d';exact hf _ d' (o1 mj (by rw [xs,h21];simp) rfl rfl rfl d'.toRun hc0)
    . have h28:ta=0:=by rcases h19 with h|h;exact h;exact absurd (h25 h) (by decide)
      subst h28;have h29:ble 2 (Nat.sub (ns+2) (eW rG cG e).length)=true:=by rw [xs,nBE,nSE];simp [qk] at h20;omega
      simp only [nBR,h29,bTA,↓reduceIte] at hc1;simp only [qk,↓reduceIte] at d';exact hf _ d' (o1 mj (by rw [xs,h21];simp [nAE]) rfl rfl rfl d'.toRun hc1)
  . have h22:∀ a' ta' b' tb' ka' kb' g u t,
        e=g++(a',ta')::u++(b',tb')::t ->
        ta'≠2->tb'≠2->ta'≠7->tb'≠7 ->
        ¬ (ta'=4/\tb'=6)->¬ (ta'=6/\tb'=4) ->
        (ka'=true->ta'=0\/ta'=3)->(kb'=true->tb'=0\/tb'=3) ->
        joinF a' b'≠(fun _=>false)->joinF a' b'≠(fun _=>true) ->
        (∀ p∈e,p.1≠joinF a' b') ->
        JointRun ns ((joinF a' b',if ta'=4\/tb'=4 then 7 else 0) ::
          qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (g++u++t))) ->
        False:=by
      intro a' ta' b' tb' ka' kb' g u t v hg' hh' hk' hm' hn' hr' h5' h7' y' c' z d';have ha:eW rG cG e =
          eW rG cG g++(eL rG cG a',ta')::eW rG cG u++(eL rG cG b',tb')::eW rG cG t:=by
        rw [v];simp [eW,e4,lAA]
      have a2:=t9 cG (i7 ns (eW rG cG e).length (eW rG cG e)) []
        (eW rG cG g) (eW rG cG u) (eW rG cG t) (eL rG cG a') ta' (eL rG cG b') tb' (by rw [<- ha];exact h18)
      simp only [lNA,<- kj] at a2;unfold i7 at a2;have h13:=(o8 a2).1;have h14:(!(beq ta' 2)&&!(beq tb' 2)&&!(beq ta' 7)&&!(beq tb' 7) &&
          !((beq ta' 4&&beq tb' 6)||(beq ta' 6&&beq tb' 4)))=true:=by
        simp only [bAT,bNT,bOF,bAF,zh];refine ⟨⟨⟨⟨hg',hh'⟩,hk'⟩,hm'⟩,?_,?_⟩
        . by_cases h4:ta'=4;right;intro h6;exact hn' ⟨h4,h6⟩;left;exact h4
        . by_cases h6:ta'=6;right;intro h4;exact hr' ⟨h6,h4⟩;left;exact h6
      have hd:(beq (eL rG cG (joinF a' b')) 0||beq (eL rG cG (joinF a' b')) cG.all1v ||
            t3 (eL rG cG (joinF a' b')) (eW rG cG e))=false:=by
        simp [q2 (c5 y'),q2 (a3 mj c'),o7 z]
      simp only [h14,↓reduceIte,v5,(qc _ a' b').symm,hd,bFT] at h13;have he:(if beq ta' 4||beq tb' 4 then 7 else 0)=(if ta'=4\/tb'=4 then 7 else 0):=by simp [bOT,nBQ]
      have h30:(if beq ta' 3 then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [nBQ]
      have h31:(if beq tb' 3 then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [nBQ]
      rw [he,h30,h31] at h13;exact hf _ d' (b0 mj (by unfold eW e4;rw [lLM,v];simp;omega)
        (fun h=>by rcases h5' h with rfl|rfl<;>decide) (fun h=>by rcases h7' h with rfl|rfl<;>decide)
        d'.toRun h13)
    have z:∀ p∈e,p.1≠joinF a b:=fun p hc=>by
      rcases lMM.1 (w.subset hc) with rfl|c';exact b1.symm
      rcases lMM.1 c' with rfl|h2';exact hnb.symm;exact x3 p h2'
    rcases fn w with ⟨g,u,t,v,h8⟩|⟨g,u,t,v,h8⟩
    . exact h22 a ta b tb ka kb g u t v hg hh hk hm hn hr h5 h7 y c z (JointRun.perm (uf h8) d)
    . have h9:joinF b a=joinF a b:=by funext x;exact Bool.or_comm _ _
      have h32:(if tb=4\/ta=4 then 7 else 0)=(if ta=4\/tb=4 then 7 else 0):=by by_cases c' : ta=4<;>by_cases h2' : tb=4<;>simp [c',h2']
      exact h22 b tb a ta kb ka g u t v hh hg hm hk
        (fun ⟨c',h2'⟩ => hr ⟨h2',c'⟩) (fun ⟨c',h2'⟩ => hn ⟨h2',c'⟩) h7 h5
        (h9 ▸ y) (h9 ▸ c) (fun p w' => h9 ▸ z p w')
        (h9 ▸ h32 ▸ JointRun.perm (c9 h8) d)
  . have h23:∀ a' ta' b' tb' ka' kb' g u t,
        e=g++(a',ta')::u++(b',tb')::t ->
        ta'≠1->tb'≠1->ta'≠4->tb'≠4->ta'≠8->tb'≠8 ->
        (ta'=6->tb'=7)->(tb'=6->ta'=7) ->
        (ka'=true->ta'=0)->(kb'=true->tb'=0) ->
        meetF a' b'≠(fun _=>false)->meetF a' b'≠(fun _=>true) ->
        (∀ p∈e,p.1≠meetF a' b') ->
        JointRun ns ((meetF a' b',if ta'=6\/tb'=6 then 8 else if ta'=3\/tb'=3 then 1 else 0) ::
          qk ka' (a',0) (qk kb' (b',0) (g++u++t))) ->
        False:=by
      intro a' ta' b' tb' ka' kb' g u t v ht' hu' hv' hw' hx' hy' hz' xi' h5' h7' y' c' z d';have ha:eW rG cG e =
          eW rG cG g++(eL rG cG a',ta')::eW rG cG u++(eL rG cG b',tb')::eW rG cG t:=by
        rw [v];simp [eW,e4,lAA]
      have a2:=t9 cG (i7 ns (eW rG cG e).length (eW rG cG e)) []
        (eW rG cG g) (eW rG cG u) (eW rG cG t) (eL rG cG a') ta' (eL rG cG b') tb' (by rw [<- ha];exact h18)
      simp only [lNA,<- kj] at a2;unfold i7 at a2;have h15:=(o8 a2).2;have h14:(!(beq ta' 1)&&!(beq tb' 1)&&!(beq ta' 4)&&!(beq tb' 4) &&
          !(beq ta' 8)&&!(beq tb' 8) &&
          !((beq ta' 6&&!(beq tb' 7))||(beq tb' 6&&!(beq ta' 7))))=true:=by
        simp only [bAT,bNT,bOF,bAF,Bool.not_eq_false',nBQ,zh];refine ⟨⟨⟨⟨⟨⟨ht',hu'⟩,hv'⟩,hw'⟩,hx'⟩,hy'⟩,?_,?_⟩
        . by_cases h6:ta'=6;right;exact hz' h6;left;exact h6
        . by_cases h6:tb'=6;right;exact xi' h6;left;exact h6
      have hd:(beq (eL rG cG (meetF a' b')) 0||beq (eL rG cG (meetF a' b')) cG.all1v ||
            t3 (eL rG cG (meetF a' b')) (eW rG cG e))=false:=by
        simp [q2 (c5 y'),q2 (a3 mj c'),o7 z]
      simp only [h14,↓reduceIte,v5,(q9 _ a' b').symm,hd,bFT] at h15;have he:(if beq ta' 6||beq tb' 6 then 8 else if beq ta' 3||beq tb' 3 then 1 else 0) =
          (if ta'=6\/tb'=6 then 8 else if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,nBQ]
      rw [he] at h15;exact hf _ d' (b0 mj (by unfold eW e4;rw [lLM,v];simp;omega)
        (fun h=>qz (h5' h)) (fun h=>qz (h7' h)) d'.toRun h15)
    have z:∀ p∈e,p.1≠meetF a b:=fun p hc=>by
      rcases lMM.1 (w.subset hc) with rfl|c';exact b1.symm
      rcases lMM.1 c' with rfl|h2';exact hnb.symm;exact x3 p h2'
    rcases fn w with ⟨g,u,t,v,h8⟩|⟨g,u,t,v,h8⟩
    . exact h23 a ta b tb ka kb g u t v ht hu hv hw hx hy hz xi h5 h7 y c z (JointRun.perm (uf h8) d)
    . have h9:meetF b a=meetF a b:=by funext x;exact Bool.and_comm _ _
      have h33:(if tb=6\/ta=6 then 8 else if tb=3\/ta=3 then 1 else 0) =
          (if ta=6\/tb=6 then 8 else if ta=3\/tb=3 then 1 else 0):=by
        by_cases c' : ta=6<;>by_cases h2' : tb=6 <;>
        by_cases h3' : ta=3<;>by_cases h4' : tb=3<;>simp [c',h2',h3',h4']
      exact h23 b tb a ta kb ka g u t v hu ht hw hv hy hx xi hz h7 h5
        (h9 ▸ y) (h9 ▸ c) (fun p w' => h9 ▸ z p w')
        (h9 ▸ h33 ▸ JointRun.perm (c9 h8) d)
lemma main_8457_of_bars (c:∀ s≤ 9,∀ i < Nf7 s,bar c7 findF7 getF7Enc s i=true) (d:∀ s≤ 13,∀ i < NG s,barG s i=true) :∀ t:Nat,HCS 8 fG t->14<=t:=by
 intro t e;by_contra hlt;have g:t<=13:=by omega
 have b:JointRun 13 g5:=uu e g;have h:m5 13 0=g5:=rfl;rw [<- h] at b;exact dq c d 13 le_rfl 0 (by decide) b
abbrev bfF7:=bar c7 findF7 getF7Enc
lemma f7_49:([4,9]).all (fun s=>S (bfF7 s) (Nf7 s) 0)=true:=by decide +kernel
lemma f5_0:S (bfF7 5) 204 0=true:=by decide +kernel
abbrev F6:=bfF7 6
lemma f6_0:S F6 82 0=true:=by decide +kernel
lemma f6_1:S F6 82 82=true:=by decide +kernel
lemma f6_2:S F6 82 164=true:=by decide +kernel
lemma f6_3:S F6 82 246=true:=by decide +kernel
lemma f6_4:S F6 82 328=true:=by decide +kernel
lemma f6_5:S F6 80 410=true:=by decide +kernel
abbrev F7:=bfF7 7
lemma f7_0:S F7 43 0=true:=by decide +kernel
lemma f7_1:S F7 43 43=true:=by decide +kernel
lemma f7_2:S F7 43 86=true:=by decide +kernel
lemma f7_3:S F7 43 129=true:=by decide +kernel
lemma f7_4:S F7 43 172=true:=by decide +kernel
lemma f7_5:S F7 43 215=true:=by decide +kernel
lemma f7_6:S F7 43 258=true:=by decide +kernel
lemma f7_7:S F7 43 301=true:=by decide +kernel
lemma f7_8:S F7 43 344=true:=by decide +kernel
lemma f7_9:S F7 43 387=true:=by decide +kernel
lemma f7_10:S F7 43 430=true:=by decide +kernel
lemma f7_11:S F7 43 473=true:=by decide +kernel
lemma f7_12:S F7 43 516=true:=by decide +kernel
lemma f7_13:S F7 43 559=true:=by decide +kernel
lemma f7_14:S F7 43 602=true:=by decide +kernel
lemma f7_15:S F7 41 645=true:=by decide +kernel
abbrev F8:=bfF7 8
lemma f8_0:S F8 25 0=true:=by decide +kernel
lemma f8_1:S F8 25 25=true:=by decide +kernel
lemma f8_2:S F8 25 50=true:=by decide +kernel
lemma f8_3:S F8 25 75=true:=by decide +kernel
lemma f8_4:S F8 25 100=true:=by decide +kernel
lemma f8_5:S F8 25 125=true:=by decide +kernel
lemma f8_6:S F8 25 150=true:=by decide +kernel
lemma f8_7:S F8 25 175=true:=by decide +kernel
lemma f8_8:S F8 25 200=true:=by decide +kernel
lemma f8_9:S F8 25 225=true:=by decide +kernel
lemma f8_10:S F8 25 250=true:=by decide +kernel
lemma f8_11:S F8 23 275=true:=by decide +kernel
lemma hBarF7:∀ s ≤ 9,∀ i < Nf7 s,bfF7 s i=true:=fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp [Nf7] at hi | 1,_=>fun i hi=>by simp [Nf7] at hi | 2,_=>fun i hi=>by simp [Nf7] at hi | 3,_=>fun i hi=>by simp [Nf7] at hi | 4,_=>fun i hi=>span_sound (bfF7 4) (Nf7 4) 0 (lAL.1 f7_49 4 (by decide)) i (nZL _) (by omega) | 5,_=>fun i hi=>sp0 f5_0 i (by dsimp [Nf7] at hi;omega) | 6,_=>fun i hi=>(spB (spB (spB (spB (spB (sp0 f6_0) f6_1) f6_2) f6_3) f6_4) f6_5) i (by dsimp [Nf7] at hi;omega) | 7,_=>fun i hi=>(spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (sp0 f7_0) f7_1) f7_2) f7_3) f7_4) f7_5) f7_6) f7_7) f7_8) f7_9) f7_10) f7_11) f7_12) f7_13) f7_14) f7_15) i (by dsimp [Nf7] at hi;omega) | 8,_=>fun i hi=>(spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (sp0 f8_0) f8_1) f8_2) f8_3) f8_4) f8_5) f8_6) f8_7) f8_8) f8_9) f8_10) f8_11) i (by dsimp [Nf7] at hi;omega) | 9,_=>fun i hi=>span_sound (bfF7 9) (Nf7 9) 0 (lAL.1 f7_49 9 (by decide)) i (nZL _) (by omega) | _+10,hs=>by omega
lemma g_sm:([5,6,12,13]).all (fun s=>S (barG s) (NG s) 0)=true:=by decide +kernel
lemma g7_0:S (barG 7) 140 0=true:=by decide +kernel
abbrev G8:=barG 8
lemma g8_0:S G8 80 0=true:=by decide +kernel
lemma g8_1:S G8 80 80=true:=by decide +kernel
lemma g8_2:S G8 80 160=true:=by decide +kernel
lemma g8_3:S G8 80 240=true:=by decide +kernel
lemma g8_4:S G8 76 320=true:=by decide +kernel
abbrev G9:=barG 9
lemma g9_0:S G9 43 0=true:=by decide +kernel
lemma g9_1:S G9 43 43=true:=by decide +kernel
lemma g9_2:S G9 43 86=true:=by decide +kernel
lemma g9_3:S G9 43 129=true:=by decide +kernel
lemma g9_4:S G9 43 172=true:=by decide +kernel
lemma g9_5:S G9 43 215=true:=by decide +kernel
lemma g9_6:S G9 43 258=true:=by decide +kernel
lemma g9_7:S G9 43 301=true:=by decide +kernel
lemma g9_8:S G9 43 344=true:=by decide +kernel
lemma g9_9:S G9 43 387=true:=by decide +kernel
lemma g9_10:S G9 43 430=true:=by decide +kernel
lemma g9_11:S G9 43 473=true:=by decide +kernel
lemma g9_12:S G9 42 516=true:=by decide +kernel
abbrev G10:=barG 10
lemma g10_0:S G10 20 0=true:=by decide +kernel
lemma g10_1:S G10 20 20=true:=by decide +kernel
lemma g10_2:S G10 20 40=true:=by decide +kernel
lemma g10_3:S G10 20 60=true:=by decide +kernel
lemma g10_4:S G10 20 80=true:=by decide +kernel
lemma g10_5:S G10 20 100=true:=by decide +kernel
lemma g10_6:S G10 20 120=true:=by decide +kernel
lemma g10_7:S G10 20 140=true:=by decide +kernel
lemma g10_8:S G10 20 160=true:=by decide +kernel
lemma g10_9:S G10 20 180=true:=by decide +kernel
lemma g10_10:S G10 20 200=true:=by decide +kernel
lemma g10_11:S G10 20 220=true:=by decide +kernel
lemma g10_12:S G10 20 240=true:=by decide +kernel
lemma g10_13:S G10 20 260=true:=by decide +kernel
lemma g10_14:S G10 20 280=true:=by decide +kernel
lemma g10_15:S G10 16 300=true:=by decide +kernel
abbrev G11:=barG 11
lemma g11_0:S G11 8 0=true:=by decide +kernel
lemma g11_1:S G11 8 8=true:=by decide +kernel
lemma g11_2:S G11 8 16=true:=by decide +kernel
lemma g11_3:S G11 8 24=true:=by decide +kernel
lemma g11_4:S G11 8 32=true:=by decide +kernel
lemma g11_5:S G11 8 40=true:=by decide +kernel
lemma g11_6:S G11 8 48=true:=by decide +kernel
lemma g11_7:S G11 3 56=true:=by decide +kernel
lemma hBarG:∀ s ≤ 13,∀ i < NG s,barG s i=true:=fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp [NG] at hi | 1,_=>fun i hi=>by simp [NG] at hi | 2,_=>fun i hi=>by simp [NG] at hi | 3,_=>fun i hi=>by simp [NG] at hi | 4,_=>fun i hi=>by simp [NG] at hi | 5,_=>fun i hi=>span_sound (barG 5) (NG 5) 0 (lAL.1 g_sm 5 (by decide)) i (nZL _) (by omega) | 6,_=>fun i hi=>span_sound (barG 6) (NG 6) 0 (lAL.1 g_sm 6 (by decide)) i (nZL _) (by omega) | 7,_=>fun i hi=>sp0 g7_0 i (by dsimp [NG] at hi;omega) | 8,_=>fun i hi=>(spB (spB (spB (spB (sp0 g8_0) g8_1) g8_2) g8_3) g8_4) i (by dsimp [NG] at hi;omega) | 9,_=>fun i hi=>(spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (sp0 g9_0) g9_1) g9_2) g9_3) g9_4) g9_5) g9_6) g9_7) g9_8) g9_9) g9_10) g9_11) g9_12) i (by dsimp [NG] at hi;omega) | 10,_=>fun i hi=>(spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (spB (sp0 g10_0) g10_1) g10_2) g10_3) g10_4) g10_5) g10_6) g10_7) g10_8) g10_9) g10_10) g10_11) g10_12) g10_13) g10_14) g10_15) i (by dsimp [NG] at hi;omega) | 11,_=>fun i hi=>(spB (spB (spB (spB (spB (spB (spB (sp0 g11_0) g11_1) g11_2) g11_3) g11_4) g11_5) g11_6) g11_7) i (by dsimp [NG] at hi;omega) | 12,_=>fun i hi=>span_sound (barG 12) (NG 12) 0 (lAL.1 g_sm 12 (by decide)) i (nZL _) (by omega) | 13,_=>fun i hi=>span_sound (barG 13) (NG 13) 0 (lAL.1 g_sm 13 (by decide)) i (nZL _) (by omega) | _+14,hs=>by omega
lemma main_8457:∀ t:ℕ,HasCircuitSize 8 fG t->14<=t:=main_8457_of_bars hBarF7 hBarG
end PEqualNP.Outside.L_meta_8457_aux
theorem PEqualNP.Outside.L_meta_8457 :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 5 && x 6)) t → 14 ≤ t :=
  PEqualNP.Outside.L_meta_8457_aux.main_8457
