import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_287_aux
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
namespace As
abbrev Fn (n:ℕ):=(Fin n→Bool)→Bool
def nT {n} (u:Fn n):Fn n:=fun x=> !(u x)
def eP {n} (u v:Fn n):Fn n:=fun x=>u x && v x
def ext {n} (P:Fn n→Prop) (g h:Fn n):=P h∨h=g∨h=nT g
def iT (n:ℕ) (h:Fn n):=(∃b:Bool,h=fun _=>b)∨∃i:Fin n,h=(fun x=>x i)∨h=nT (fun x=>x i)
def Build {n:ℕ} (P:Fn n→Prop) (f:Fn n):ℕ→Prop
 | 0=>P f
 | s+1=>P f∨∃u v,P u∧P v∧Build (ext P (eP u v)) f s
lemma Build.oN {n:ℕ} {P:Fn n→Prop} {f:Fn n} {s:ℕ} (a:P f):
  Build P f s:=by
 cases s with
 | zero=>exact a
 | succ s=>exact Or.inl a
lemma Build.mF {n:ℕ} {P:Fn n→Prop} {u v f:Fn n} {s:ℕ}
  (a:P u) (b:P v) (h:Build (ext P (eP u v)) f s):Build P f (s+1):=
 Or.inr ⟨u,v,a,b,h⟩
lemma Build.mG {n:ℕ}
  {a:(P:Fn n→Prop)→(f:Fn n)→(s:ℕ)→Build P f s→Prop}
  (oN:∀{P f s},(h:P f)→a P f s (Build.oN h))
  (mF:∀{P u v f s} (b:P u) (c:P v) (h:Build (ext P (eP u v)) f s),
    a _ f s h→a P f (s+1) (Build.mF b c h))
  {P f s} (h:Build P f s):a P f s h:=by
 induction s generalizing P with
 | zero=>exact oN h
 | succ s ih=>
   rcases h with d|⟨u,v,b,c,h⟩
   ·exact oN d
   ·exact mF b c h (ih h)
def dO (n:ℕ) (f:Fn n) (s:ℕ):=Build (iT n) f s
variable {n : ℕ}
def R (p:Fin n) (b:Bool) (f:Fn n):Fn n:=fun x=>f (Function.update x p b)
def cI (p:Fin n) (f:Fn n):=∀b,R p b f=f
def nU (f:Fn n):=∃b:Bool,f=fun _=>b
def gY (P:Fn n→Prop):=(∀b:Bool,P (fun _=>b))∧∀u,P u→P (nT u)
@[local simp] lemma neg_neg (u : Fn n) : nT (nT u) = u := by funext x; simp [nT]
lemma gZ {P:Fn n→Prop} (a:gY P) (u:Fn n):gY (ext P u):=by
 refine⟨fun b=>Or.inl (a.1 b),?_⟩;rintro v (hv|rfl|rfl)
 ·exact Or.inl (a.2 _ hv)
 ·exact Or.inr (Or.inr rfl)
 ·exact Or.inr (Or.inl (neg_neg _))
lemma iU (n:ℕ):gY (iT n):=by
 refine⟨fun b=>Or.inl ⟨b,rfl⟩,?_⟩;rintro v (⟨b,rfl⟩|⟨i,rfl|rfl⟩)
 ·exact Or.inl ⟨!b,rfl⟩
 ·exact Or.inr ⟨i,Or.inr rfl⟩
 ·exact Or.inr ⟨i,Or.inl (neg_neg _)⟩
lemma nV {p:Fin n} {u v:Fn n} (a:cI p u) (c:cI p v):
  cI p (eP u v):=by
 intro b;exact congrArg₂ eP (a b) (c b)
lemma hF {p:Fin n} {u:Fn n} (a:cI p u):cI p (nT u):=fun b=>congrArg nT (a b)
lemma vJ {P Q:Fn n→Prop} {u:Fn n} {p:Fin n} {b:Bool}
  (h:∀v,P v→Q (R p b v)):
  ∀v,ext P u v→ext Q (R p b u) (R p b v):=by
 rintro v (hv|rfl|rfl)
 ·exact Or.inl (h _ hv)
 ·exact Or.inr (Or.inl rfl)
 ·exact Or.inr (Or.inr rfl)
lemma yS {P:Fn n→Prop} {f:Fn n} {s} (h:Build P f s)
  (p:Fin n) (b:Bool) {Q:Fn n→Prop} (a:∀v,P v→Q (R p b v)):
  Build Q (R p b f) s:=by
 induction h using Build.mG generalizing Q with
 | oN hf=>exact .oN (a _ hf)
 | mF hu hv _ ih=>exact .mF (a _ hu) (a _ hv) (ih (vJ a))
lemma Build.mono {P:Fn n→Prop} {f:Fn n} {s t} (h:Build P f s) (a:s≤t):
  Build P f t:=by
 induction h using Build.mG generalizing t with
 | oN hf=>exact .oN hf
 | mF hu hv _ ih=>
   cases t with
   | zero=>omega
   | succ t=>exact .mF hu hv (ih (by omega))
lemma pB {P Q:Fn n→Prop} {u:Fn n} {p:Fin n} {b:Bool} (c:gY Q)
  (h:∀v,P v→Q (R p b v)) (a:Q (R p b u)):
  ∀v,ext P u v→Q (R p b v):=by
 rintro v (hv|rfl|rfl)
 ·exact h _ hv
 ·exact a
 ·exact c.2 _ a
lemma rG (u:Fn n):eP (fun _=>false) u=fun _=>false:=by funext x;change(false && u x)=false;cases u x<;>rfl
lemma yT (u:Fn n):eP (fun _=>true) u=u:=by funext x;change(true && u x)=u x;cases u x<;>rfl
lemma rH (u:Fn n):eP u (fun _=>false)=fun _=>false:=by funext x;change(u x && false)=false;cases u x<;>rfl
lemma yU (u:Fn n):eP u (fun _=>true)=u:=by funext x;change(u x && true)=u x;cases u x<;>rfl
lemma vK {Q:Fn n→Prop} {u v:Fn n} (a:gY Q)
  (c:Q u) (d:Q v) (h:nU u∨nU v):Q (eP u v):=by
 rcases h with⟨b,rfl⟩|⟨b,rfl⟩
 ·cases b
  ·rw[rG];exact a.1 false
  ·rw[yT];exact d
 ·cases b
  ·rw[rH];exact a.1 false
  ·rw[yU];exact c
lemma mH {P:Fn n→Prop} {f:Fn n} {s} (h:Build P f s)
  (p:Fin n) (b:Bool) {Q:Fn n→Prop} (g:gY Q)
  (c:∀v,P v→Q (R p b v))
  (a:∀v,P v→¬cI p v→nU (R p b v))
  (i:¬cI p f) (e:¬nU (R p b f)):
  ∃t,t+1≤ s∧Build Q (R p b f) t:=by
 classical
 induction h using Build.mG generalizing Q with
 | oN hf=>exact(e (a _ hf i)).elim
 | @mF P u v f s hu hv h ih=>
   by_cases d:cI p u∧cI p v
   ·have hs:=nV d.1 d.2;obtain⟨t,ht,hh⟩:=ih (gZ g _) (vJ c) (by
     rintro w (hw|rfl|rfl) hn
     ·exact a _ hw hn
     ·exact(hn hs).elim
     ·exact(hn (hF hs)).elim) i e
    exact⟨t+1,by omega,.mF (c _ hu) (c _ hv) hh⟩
   ·have k:Q (R p b (eP u v)):=by
     apply vK g (c _ hu) (c _ hv);by_cases j:cI p u
     ·exact Or.inr (a _ hv (fun l=>d ⟨j,l⟩))
     ·exact Or.inl (a _ hu j)
    exact⟨s,by omega,yS h p b (pB g c k)⟩
lemma sB {P:Fn n→Prop} {f:Fn n} {s} (h:Build P f s)
  (p:Fin n) {Q:Bool→Fn n→Prop} (g:∀b,gY (Q b))
  (i:∀b v,P v→Q b (R p b v))
  (a:∀v,P v→¬cI p v→
    (∀b,nU (R p b v))∧∃b,R p b v=fun _=>false)
  (k:¬cI p f) (d:∀b,¬nU (R p b f)):
  ∃b t,t+2≤ s∧Build (Q b) (R p b f) t:=by
 classical
 induction h using Build.mG generalizing Q with
 | oN hf=>exact(d false ((a _ hf k).1 false)).elim
 | @mF P u v f s hu hv h ih=>
   by_cases e:cI p u∧cI p v
   ·have hs:=nV e.1 e.2;obtain⟨b,t,ht,hh⟩:=ih (fun b=>gZ (g b) (R p b (eP u v)))
     (fun b=>vJ (i b)) (by
       rintro w (hw|rfl|rfl) hn
       ·exact a _ hw hn
       ·exact(hn hs).elim
       ·exact(hn (hF hs)).elim) k d
    exact⟨b,t+1,by omega,.mF (i b _ hu) (i b _ hv) hh⟩
   ·have j:∃b,R p b (eP u v)=fun _=>false:=by
     by_cases l:cI p u
     ·obtain⟨b,c⟩:=(a _ hv (fun o=>e ⟨l,o⟩)).2;refine⟨b,?_⟩;change eP (R p b u) (R p b v)=_;rw[c,rH]
     ·obtain⟨b,c⟩:=(a _ hu l).2;refine⟨b,?_⟩;change eP (R p b u) (R p b v)=_;rw[c,rG]
    obtain⟨b,c⟩:=j;have m:Q b (R p b (eP u v)):=c▸(g b).1 false;obtain⟨t,ht,hh⟩:=mH h p b (g b) (pB (g b) (i b) m) (by
     rintro w (hw|rfl|rfl) hn
     ·exact(a _ hw hn).1 b
     ·exact⟨false,c⟩
     ·exact⟨true,congrArg nT c⟩) k (d b)
    exact⟨b,t,by omega,hh⟩
lemma dZ {i p:Fin n} (a:i≠p):cI p (fun x=>x i):=by intro b;funext x;exact Function.update_of_ne a _ _
lemma cQ (i:Fin n) (b:Bool):R i b (fun x=>x i)=fun _=>b:=by funext x;exact Function.update_self _ _ _
lemma wP (p:Fin n) (b:Bool):∀v,iT n v→iT n (R p b v):=by
 rintro v (⟨k,rfl⟩|⟨i,rfl|rfl⟩)
 ·exact Or.inl ⟨k,rfl⟩
 ·by_cases a:i=p
  ·subst i;exact Or.inl ⟨b,cQ p b⟩
  ·exact Or.inr ⟨i,Or.inl (dZ a b)⟩
 ·by_cases a:i=p
  ·subst i;exact Or.inl ⟨!b,congrArg nT (cQ p b)⟩
  ·exact Or.inr ⟨i,Or.inr (hF (dZ a) b)⟩
lemma wQ (p:Fin n):∀v,iT n v→¬cI p v→
  (∀b,nU (R p b v))∧∃b,R p b v=fun _=>false:=by
 rintro v (⟨c,rfl⟩|⟨i,rfl|rfl⟩) hn
 ·exact(hn (fun _=>rfl)).elim
 ·by_cases a:i=p
  ·subst i;exact⟨fun b=>⟨b,cQ p b⟩,false,cQ p false⟩
  ·exact(hn (dZ a)).elim
 ·by_cases a:i=p
  ·subst i;exact⟨fun b=>⟨!b,congrArg nT (cQ p b)⟩,true,congrArg nT (cQ p true)⟩
  ·exact(hn (hF (dZ a))).elim
lemma rI {p:Fin n} {f:Fn n}
  (h:∃x,f (Function.update x p (!x p))≠f x):¬cI p f:=by
 obtain⟨x,a⟩:=h;exact fun hs=>a (congrFun (hs (!x p)) x)
lemma tQ {f:Fn n} (h:∃x y,f x≠f y):¬nU f:=by obtain⟨x,y,hh⟩:=h;rintro⟨k,rfl⟩;exact hh rfl
lemma eI (n:ℕ) (f:Fn (n+1)) (p:Fin (n+1)) (b:Bool) (s:ℕ)
  (a:∃x,f (Function.update x p (!x p))≠f x)
  (c:∃x y,f (Function.update x p b)≠f (Function.update y p b))
  (h:dO (n+1) f (s+1)):
  dO (n+1) (fun x=>f (Function.update x p b)) s:=by
 obtain⟨t,ht,hh⟩:=mH h p b (iU _) (wP p b)
  (fun v e d=>(wQ p v e d).1 b) (rI a) (tQ c)
 exact hh.mono (by omega)
lemma dG (n:ℕ) (f:Fn (n+1)) (p:Fin (n+1)) (s:ℕ)
  (a:∃x,f (Function.update x p (!x p))≠f x)
  (c:∀b:Bool,∃x y,f (Function.update x p b)≠f (Function.update y p b))
  (h:dO (n+1) f s):
  ∃b s',s'+2≤ s∧dO (n+1) (fun x=>f (Function.update x p b)) s':=
 sB h p (Q:=fun _=>iT (n+1)) (fun _=>iU _) (wP p) (wQ p) (rI a) (fun b=>tQ (c b))
end As
namespace As
variable {n : ℕ}
def oO (T:Finset (Fn n)) (f:Fn n):Prop:=∀x y,(∀w∈T,w x=w y)→f x=f y
lemma kG {P:Fn n→Prop} {f:Fn n} {s:ℕ}
  (h:Build P f s):
  ∃T:Finset (Fn n),T.card≤ s+1∧(∀w∈T,P w)∧oO T f:=by
 classical
 induction h using Build.mG with
 | @oN P f s hf=>
   refine⟨{f},by simp,?_,?_⟩
   ·simpa using hf
   ·intro x y d;exact d _ (Finset.mem_singleton_self _)
 | @mF P u v f s hu hv _ ih=>
   obtain⟨T,E,m,o⟩:=ih
   let g:=eP u v
   by_cases e:g∈T∨nT g∈T
   ·let U:=(T.erase g).erase (nT g)
    have F:U.card+1≤T.card:=by
     rcases e with e|e
     ·have r:U.card≤(T.erase g).card:=
       Finset.card_le_card (Finset.erase_subset _ _)
      have j:=Finset.card_erase_add_one e;omega
     ·have q:U⊆T.erase (nT g):=by
       intro w a;have b:=Finset.mem_erase.mp a;exact Finset.mem_erase.mpr ⟨b.1,(Finset.mem_erase.mp b.2).2⟩
      have r:=Finset.card_le_card q;have j:=Finset.card_erase_add_one e;omega
    refine⟨insert u (insert v U),?_,?_,?_⟩
    ·have A:=Finset.card_insert_le u (insert v U);have B:=Finset.card_insert_le v U;omega
    ·intro w a;rcases Finset.mem_insert.mp a with rfl|a
     ·exact hu
     rcases Finset.mem_insert.mp a with rfl|a
     ·exact hv
     have b:=Finset.mem_erase.mp a;have i:=Finset.mem_erase.mp b.2;rcases m w i.2 with a|c|c
     ·exact a
     ·exact(i.1 c).elim
     ·exact(b.1 c).elim
    ·intro x y d;have t:=d u (Finset.mem_insert_self _ _);have z:=d v (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _));have p:g x=g y:=congrArg₂ (· && ·) t z;apply o x y;intro w a;by_cases k:w=g
     ·simpa only[k] using p
     by_cases l:w=nT g
     ·simpa only[l,nT] using congrArg (! ·) p
     exact d w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨l,Finset.mem_erase.mpr ⟨k,a⟩⟩)))
   ·refine⟨T,by omega,?_,o⟩;intro w a;rcases m w a with C|k|l
    ·exact C
    ·exact(e (Or.inl (by simpa only[←k,g] using a))).elim
    ·exact(e (Or.inr (by simpa only[←l,g] using a))).elim
lemma pC {w:Fn n} (a:iT n w):
  ∃
   A:Finset (Fin n),A.card≤1∧
   ∀x y:Fin n→Bool,(∀i∈A,x i=y i)→w x=w y:=by
 classical
 rcases a with⟨b,rfl⟩|⟨i,rfl|rfl⟩
 ·exact⟨∅,by simp,fun _ _ _=>rfl⟩
 ·exact⟨{i},by simp,fun _ _ h=>h i (Finset.mem_singleton_self i)⟩
 ·exact⟨{i},by simp,fun _ _ h=>congrArg (! ·) (h i (Finset.mem_singleton_self i))⟩
lemma lJ (T:Finset (Fn n)) (f:∀w∈T,iT n w):
  ∃
   A:Finset (Fin n),A.card≤T.card∧
   ∀x y:Fin n→Bool,(∀i∈A,x i=y i)→∀w∈T,w x=w y:=by
 classical
 induction T using Finset.induction_on with
 | empty=>
   refine⟨∅,le_rfl,?_⟩;simp
 | @insert w T hw ih=>
   obtain⟨A,h,d⟩:=ih (fun z a=>f z (Finset.mem_insert_of_mem a));obtain⟨B,j,e⟩:=pC (f w (Finset.mem_insert_self _ _));refine⟨A∪B,?_,?_⟩
   ·rw[Finset.card_insert_of_notMem hw];have g:=Finset.card_union_le A B;omega
   ·intro x y b z a;rcases Finset.mem_insert.mp a with rfl|a
    ·exact e x y (fun i c=>b i (Finset.mem_union_right A c))
    ·exact d x y (fun i c=>b i (Finset.mem_union_left B c)) z a
lemma kH {f:Fn n} {s:ℕ} (h:dO n f s):
  ∃
   A:Finset (Fin n),A.card≤ s+1∧
   ∀x y:Fin n→Bool,(∀i∈A,x i=y i)→f x=f y:=by
 obtain⟨T,d,c,e⟩:=kG h;obtain⟨A,a,b⟩:=lJ T c;exact⟨A,a.trans d,fun x y g=>e x y (b x y g)⟩
lemma cD (n:ℕ) (f:Fn n) (T:Finset (Fin n))
  (a:∀i∈T,∃x:Fin n→Bool,f (Function.update x i (!x i))≠f x)
  (s:ℕ) (h:dO n f s):T.card≤ s+1:=by
 classical
 obtain⟨A,b,c⟩:=kH h;refine(Finset.card_le_card ?_).trans b;intro i g;by_contra d;obtain⟨x,l⟩:=a i g;apply l;apply c;intro j k;exact Function.update_of_ne (by intro e;exact d (e▸k)) _ _
end As
namespace PEqualNP.MetaComplexity.Aa.Ak
open SimpleGraph
lemma kI {V:Type*} [Fintype V] (G:SimpleGraph V) [Nonempty V]:
  ∃
   (a b:V) (P:G.Walk a b),P.IsPath∧
   ∀(c d:V) (Q:G.Walk c d),Q.IsPath→Q.length≤P.length:=by
 by_contra e
 push Not at e
 have g:∀k:ℕ,∃(a b:V) (P:G.Walk a b),P.IsPath∧k≤P.length:=by
  intro k
  induction k with
  | zero=>
    obtain⟨v⟩:= ‹Nonempty V›;exact⟨v,v,Walk.nil,Walk.IsPath.nil,le_refl _⟩
  | succ k ih=>
    obtain⟨a,b,P,f,g⟩:=ih;obtain⟨c,d,Q,h,j⟩:=e a b P f;exact⟨c,d,Q,h,by omega⟩
 obtain⟨a,b,P,f,i⟩:=g (Fintype.card V);have:=f.length_lt;omega
lemma gM {V:Type*} [Fintype V] (G:SimpleGraph V) (r:G.IsAcyclic)
  (J:∃u v:V,G.Adj u v):
  ∃
   l p:V,G.Adj l p∧(∀w,G.Adj l w→w=p)∧
   ((∃q:V,∀w,G.Adj p w→w=l∨w=q)∨
     (∃f:V,f≠l∧G.Adj p f∧∀w,G.Adj f w→w=p)):=by
 classical
 obtain⟨F,K,y⟩:=J
 have:Nonempty V:=⟨F⟩
 obtain⟨l,z,P,A,k⟩:=kI G
 have H:1≤P.length:=by
  have:=k F K (Walk.cons y Walk.nil) (by simp[Walk.cons_isPath_iff,y.ne])
  simpa using this
 cases P with
 | nil=>simp at H
 | @cons _ p _ hlp P'=>
   rw[Walk.cons_isPath_iff] at A
   obtain⟨j,s⟩:=A
   have g:∀(c d:V) (Q:G.Walk c d),Q.IsPath→Q.length≤P'.length+1:=by
    intro c d Q i
    have:=k c d Q i
    simpa using this
   have b:(Walk.cons hlp P').IsPath:=(Walk.cons_isPath_iff _ _).2 ⟨j,s⟩
   have n:∀w,G.Adj l w→w=p:=by
    intro w a
    by_cases e:w∈(Walk.cons hlp P').support
    ·have:=r.eq_snd_of_adj_start b a e
     simpa using this
    ·exfalso
     have i:(Walk.cons a.symm (Walk.cons hlp P')).IsPath:=
      (Walk.cons_isPath_iff _ _).2 ⟨b,e⟩
     have:=g _ _ _ i
     simp at this
   refine⟨l,p,hlp,n,?_⟩
   have t:∀w,G.Adj p w→w∉(Walk.cons hlp P').support→
     ∀u,G.Adj w u→u=p:=by
    intro w a E u C
    have x:w∉P'.support:=by
     intro h;exact E (by simp[h])
    have i:(Walk.cons a.symm P').IsPath:=(Walk.cons_isPath_iff _ _).2 ⟨j,x⟩
    by_cases e:u∈(Walk.cons a.symm P').support
    ·have:=r.eq_snd_of_adj_start i C e
     simpa using this
    ·exfalso
     have B:(Walk.cons C.symm (Walk.cons a.symm P')).IsPath:=
      (Walk.cons_isPath_iff _ _).2 ⟨i,e⟩
     have:=g _ _ _ B
     simp at this
   by_cases o:∃f:V,f≠l∧G.Adj p f∧∀w,G.Adj f w→w=p
   ·exact Or.inr o
   ·left
    refine⟨P'.snd,fun w a=> ?_⟩
    by_cases m:w=l
    ·exact Or.inl m
    ·right
     by_cases e:w∈P'.support
     ·exact r.eq_snd_of_adj_start j a e
     ·exfalso
      apply o
      refine⟨w,m,a,t w a ?_⟩
      simp[m,e]
end PEqualNP.MetaComplexity.Aa.Ak
namespace PEqualNP.MetaComplexity.Aa.Ak
open SimpleGraph
noncomputable def F {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (x:Fin n→Bool):
  Bool:=
 @decide ((∃a∈A,x a=true)∨∃i j:Fin n,G.Adj i j∧x i=true∧x j=true)
  (Classical.propDecidable _)
lemma hK {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (x:Fin n→Bool):
  F
   G A x=true↔
   ((∃a∈A,x a=true)∨∃i j:Fin n,G.Adj i j∧x i=true∧x j=true):=by
 unfold F;exact @decide_eq_true_iff _ (Classical.propDecidable _)
lemma aCh {n:ℕ} (G G':SimpleGraph (Fin n)) (A A':Finset (Fin n)) (x y:Fin n→Bool)
  (h:((∃a∈A,x a=true)∨∃i j:Fin n,G.Adj i j∧x i=true∧x j=true)↔
    ((∃a∈A',y a=true)∨∃i j:Fin n,G'.Adj i j∧y i=true∧y j=true)):
  F G A x=F G' A' y:=by
 rw[Bool.eq_iff_iff,hK,hK];exact h
lemma yV {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)):
  F G A (fun _=>false)=false:=by
 rw[Bool.eq_false_iff,ne_eq,hK];simp
lemma aBy {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n))
  (h:A.Nonempty∨∃i j:Fin n,G.Adj i j):
  ∃x y:Fin n→Bool,F G A x≠F G A y:=by
 refine⟨fun _=>true,fun _=>false,?_⟩;rw[yV];have:F G A (fun _=>true)=true:=by
  rw[hK];rcases h with⟨a,c⟩|⟨i,j,b⟩
  ·exact Or.inl ⟨a,c,rfl⟩
  ·exact Or.inr ⟨i,j,b,rfl,rfl⟩
 rw[this];simp
lemma yW {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (u v:Fin n)
  (d:G.Adj u v) (l:v∉A):
  ∃x:Fin n→Bool,F G A (Function.update x u (!x u))≠F G A x:=by
 have c:u≠v:=d.ne;refine⟨Function.update (fun _=>false) v true,?_⟩;have g:F G A (Function.update (Function.update (fun _=>false) v true) u
   (!(Function.update (fun _=>false) v true u)))=true:=by
  rw[hK];right;refine⟨u,v,d,?_,?_⟩
  ·simp[Function.update_of_ne c]
  ·simp[Function.update_of_ne c.symm]
 have k:F G A (Function.update (fun _=>false) v true)=false:=by
  rw[Bool.eq_false_iff,ne_eq,hK];rintro(⟨a,ha,hx⟩|⟨i,j,hij,hi,hj⟩)
  ·by_cases b:a=v
   ·exact l (b▸ha)
   ·simp[Function.update_of_ne b] at hx
  ·have e:i=v:=by
    by_contra h;simp[Function.update_of_ne h] at hi
   have f:j=v:=by by_contra h;simp[Function.update_of_ne h] at hj
   exact hij.ne (e.trans f.symm)
 rw[g,k];simp
lemma aAz {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (a:Fin n)
  (b:a∈A):
  ∃x:Fin n→Bool,F G A (Function.update x a (!x a))≠F G A x:=by
 refine⟨fun _=>false,?_⟩;rw[yV];have:F G A (Function.update (fun _=>false) a (!false))=true:=by rw[hK];exact Or.inl ⟨a,b,by simp⟩
 rw[this];simp
lemma iV {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (l p:Fin n)
  (m:l∉A) (f:∀w,G.Adj l w→w=p) (x:Fin n→Bool):
  F G A (Function.update x l false)=F (G.deleteEdges {s(l,p)}) A x:=by
 apply aCh;apply or_congr
 ·constructor
  ·rintro⟨a,g,h⟩;have k:a≠l:=fun e=>m (e▸g)
   exact⟨a,g,by rwa [Function.update_of_ne k] at h⟩
  ·rintro⟨a,g,h⟩;have k:a≠l:=fun e=>m (e▸g)
   exact⟨a,g,by rwa [Function.update_of_ne k]⟩
 ·constructor
  ·rintro⟨i,j,b,q,r⟩;have c:i≠l:=by rintro rfl;simp at q
   have d:j≠l:=by rintro rfl;simp at r
   refine⟨i,j,?_,by rwa [Function.update_of_ne c] at q,by rwa [Function.update_of_ne d] at r⟩;rw[deleteEdges_adj];refine⟨b,?_⟩;simp[c,d]
  ·rintro⟨i,j,b,q,r⟩;rw[deleteEdges_adj] at b;obtain⟨b,o⟩:=b;have c:i≠l:=by
    rintro rfl;have:=f j b;subst this;exact o rfl
   have d:j≠l:=by rintro rfl;have:=f i b.symm;subst this;exact o (Sym2.eq_swap)
   exact⟨i,j,b,by rwa [Function.update_of_ne c],by rwa [Function.update_of_ne d]⟩
lemma kT {n:ℕ} (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (l p q:Fin n)
  (z:l∉A) (o:G.Adj l p) (d:∀w,G.Adj l w→w=p)
  (B:∀w,G.Adj p w→w=l∨w=q) (x:Fin n→Bool):
  F G A (Function.update x l true)=F (G.deleteEdges {s(p,l),s(p,q)}) (insert p A) x:=by
 have k:p≠l:=o.ne.symm
 have r:∀a∈A,Function.update x l true a=x a:=fun a c=>
  Function.update_of_ne (by rintro rfl;exact z c) _ _
 have m:∀i j,(G.deleteEdges {s(p,l),s(p,q)}).Adj i j→i≠p∧i≠l:=by
  intro i j b
  rw[deleteEdges_adj] at b
  obtain⟨b,g⟩:=b
  constructor
  ·rintro rfl
   rcases B j b with rfl|rfl
   ·exact g (by simp)
   ·exact g (by simp)
  ·rintro rfl
   have:=d j b
   subst this
   exact g (by simp[Sym2.eq_swap])
 apply aCh
 constructor
 ·rintro(⟨a,c,h⟩|⟨i,j,b,hi,hj⟩)
  ·exact Or.inl ⟨a,Finset.mem_insert_of_mem c,by rwa [r a c] at h⟩
  ·by_cases e:i=p
   ·subst e
    exact Or.inl ⟨i,Finset.mem_insert_self _ _,by rwa [Function.update_of_ne k] at hi⟩
   by_cases f:j=p
   ·subst f
    exact Or.inl ⟨j,Finset.mem_insert_self _ _,by rwa [Function.update_of_ne k] at hj⟩
   have u:i≠l:=by
    rintro rfl;exact f (d j b)
   have y:j≠l:=by
    rintro rfl;exact e (d i b.symm)
   right
   refine⟨i,j,?_,by rwa [Function.update_of_ne u] at hi,
    by rwa [Function.update_of_ne y] at hj⟩
   rw[deleteEdges_adj]
   refine⟨b,?_⟩
   simp[e,f]
 ·rintro(⟨a,c,h⟩|⟨i,j,b,hi,hj⟩)
  ·rcases Finset.mem_insert.1 c with rfl|c
   ·right
    exact⟨l,a,o,by simp,by rwa [Function.update_of_ne k]⟩
   ·exact Or.inl ⟨a,c,by rwa [r a c]⟩
  ·right
   have t:=m i j b
   have v:=m j i b.symm
   rw[deleteEdges_adj] at b
   exact⟨i,j,b.1,by rwa [Function.update_of_ne t.2],
    by rwa [Function.update_of_ne v.2]⟩
def yX {n:ℕ} (G:SimpleGraph (Fin n)) (T:Finset (Fin n)):Prop:=∀i j,G.Adj i j→i∈T∨j∈T
lemma lK {n:ℕ} (G:SimpleGraph (Fin n)) (S:Set (Sym2 (Fin n))) (p:Fin n)
  (c:∀e∈S,p∈e) (T:Finset (Fin n)) (d:yX (G.deleteEdges S) T):
  yX G (insert p T):=by
 intro i j b;by_cases a:s(i,j)∈S
 ·have:=c _ a;rcases Sym2.mem_iff.1 this with rfl|rfl
  ·exact Or.inl (Finset.mem_insert_self _ _)
  ·exact Or.inr (Finset.mem_insert_self _ _)
 ·rcases d i j ((deleteEdges_adj).2 ⟨b,a⟩) with h|h
  ·exact Or.inl (Finset.mem_insert_of_mem h)
  ·exact Or.inr (Finset.mem_insert_of_mem h)
lemma tR {n:ℕ} (G:SimpleGraph (Fin n)) (l p a:Fin n) (k:ℕ)
  (v:a≠l) (g:G.Adj p a) (b:∀w,G.Adj a w→w=p)
  (z:∀T,yX G T→k≤T.card) (T:Finset (Fin n))
  (o:yX (G.deleteEdges {s(l,p)}) T):k≤T.card:=by
 have B:∀e∈({s(l,p)}:Set (Sym2 (Fin n))),p∈e:=by intro e y;rw[Set.mem_singleton_iff] at y;subst y;exact Sym2.mem_mk_right _ _
 by_cases m:p∈T
 ·have:=z _ (lK G _ p B T o);rwa [Finset.insert_eq_of_mem m] at this
 ·have u:a∈T:=by
   have x:p≠a:=g.ne;rcases o p a ((deleteEdges_adj).2 ⟨g,by simp[v,x.symm]⟩) with h|h
   ·exact absurd h m
   ·exact h
  have q:yX G (insert p (T.erase a)):=by
   intro i j c;by_cases d:i=p
   ·exact Or.inl (d▸Finset.mem_insert_self _ _)
   by_cases f:j=p
   ·exact Or.inr (f▸Finset.mem_insert_self _ _)
   have A:(G.deleteEdges {s(l,p)}).Adj i j:=(deleteEdges_adj).2 ⟨c,by simp[d,f]⟩;rcases o i j A with h | h
   ·have r:i≠a:=by
     rintro rfl;exact f (b j c)
    exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨r,h⟩))
   ·have t:j≠a:=by
     rintro rfl;exact d (b i c.symm)
    exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨t,h⟩))
  have C:=z _ q;have E:=Finset.card_insert_le p (T.erase a);have F:=Finset.card_erase_add_one u;omega
lemma fG {n:ℕ} (G:SimpleGraph (Fin n)) (l p:Fin n) (h:G.Adj l p):
  (G.deleteEdges {s(l,p)}).edgeSet.ncard+1=G.edgeSet.ncard:=by
 rw[edgeSet_deleteEdges];exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)
lemma pD {n:ℕ} (G:SimpleGraph (Fin n)) (l p q:Fin n) (h:G.Adj l p):
  G.edgeSet.ncard≤(G.deleteEdges {s(p,l),s(p,q)}).edgeSet.ncard+2∧(G.deleteEdges {s(p,l),s(p,q)}).edgeSet.ncard<G.edgeSet.ncard:=by
 rw[edgeSet_deleteEdges];constructor
 ·have g:=Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p,l),s(p,q)}:Set (Sym2 (Fin n)));have d:=Set.ncard_insert_le (s(p,l)) ({s(p,q)}:Set (Sym2 (Fin n)));rw[Set.ncard_singleton] at d;omega
 ·have b:s(l,p)∈G.edgeSet:=G.mem_edgeSet.2 h;have c:G.edgeSet \ {s(p,l),s(p,q)}⊆G.edgeSet \ {s(l,p)}:=by
   intro e f;refine⟨f.1,?_⟩;intro a;apply f.2;rw[Set.mem_singleton_iff] at a;rw[a,Sym2.eq_swap];exact Set.mem_insert _ _
  have g:=Set.ncard_le_ncard c;have d:=Set.ncard_sdiff_singleton_lt_of_mem b;omega
lemma hM {n:ℕ} (G:SimpleGraph (Fin n)) (h:∀i j,¬G.Adj i j):
  G.edgeSet.ncard=0:=by
 have:G.edgeSet= ∅ :=by
  apply Set.eq_empty_iff_forall_notMem.2;intro e
  induction e using Sym2.ind with
  | _ i j=>exact fun a=>h i j (G.mem_edgeSet.1 a)
 rw[this,Set.ncard_empty]
lemma xO {n:ℕ} (G:SimpleGraph (Fin n)) (l p q:Fin n)
  (c:∀w,G.Adj p w→w=l∨w=q) (i j:Fin n)
  (a:(G.deleteEdges {s(p,l),s(p,q)}).Adj i j):i≠p:=by
 rw[deleteEdges_adj] at a;obtain⟨a,b⟩:=a;rintro rfl;rcases c j a with rfl|rfl
 ·exact b (by simp)
 ·exact b (by simp)
end PEqualNP.MetaComplexity.Aa.Ak
namespace As
open PEqualNP.MetaComplexity.Aa.Ak
open SimpleGraph
section
variable
    (dO : (n : ℕ) → ((Fin n → Bool) → Bool) → ℕ → Prop)
    (eI : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool)
      (p : Fin (n + 1)) (b : Bool) (s : ℕ),
      (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) →
      (∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) →
      dO (n + 1) f (s + 1) → dO (n + 1) (fun x => f (Function.update x p b)) s)
    (dG : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool)
      (p : Fin (n + 1)) (s : ℕ),
      (∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x) →
      (∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b)) →
      dO (n + 1) f s →
      ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
        dO (n + 1) (fun x => f (Function.update x p b)) s')
    (cD : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n)),
      (∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) →
      ∀ (s : ℕ), dO n f s → T.card ≤ s + 1)
include eI dG cD
lemma iQ:
  ∀
   (m n:ℕ) (G:SimpleGraph (Fin n)) (A:Finset (Fin n)) (k s:ℕ),
   G.edgeSet.ncard=m→G.IsAcyclic→(∀i j,G.Adj i j→i∉A)→
   (∀T,yX G T→k≤T.card)→(A.Nonempty∨∃i j,G.Adj i j)→
   dO n (F G A) s→A.card+m+k≤ s+1:=by
 intro m
 induction m using Nat.strong_induction_on with
 | _ m ih=>
 intro n G A k s hm M o O b6 X;by_cases Z:∃i j,G.Adj i j;swap
 ·push Not at Z
  have u:k≤(∅ :Finset (Fin n)).card:=O ∅ (fun i j h=>absurd h (Z i j));have b4:m=0:=by rw[←hm];exact hM G Z
  have:=cD n (F G A) A (fun a ha=>aAz G A a ha) s X;simp at u;omega
 obtain⟨l,p,c,C,a0⟩:=gM G M Z;obtain⟨r,rfl⟩:∃r,n=r+1:=⟨n-1,by have:=l.2;omega⟩
 have R:l∉A:=o l p c;have a3:p∉A:=o p l c.symm;have g:=yW G A l p c a3;have a1:=yW G A p l c.symm R;have c0:2≤ s+1:=by
  have:=cD _ (F G A) {l,p} (by
   intro i t;rcases Finset.mem_insert.1 t with rfl|t
   ·exact g
   ·rw[Finset.mem_singleton] at t;subst t;exact a1) s X
  rwa [Finset.card_pair c.ne] at this
 set G0:=G.deleteEdges {s(l,p)} with b7
 have b4:G0.edgeSet.ncard+1=m:=by rw[←hm];exact fG G l p c
 have N:G0.IsAcyclic:=M.anti (deleteEdges_le _);have B:∀i j,G0.Adj i j→i∉A:=fun i j h=>o i j ((deleteEdges_adj).1 h).1
 have a8:∀e∈({s(l,p)}:Set (Sym2 (Fin (r+1)))),p∈e:=by intro e w;rw[Set.mem_singleton_iff] at w;subst w;exact Sym2.mem_mk_right _ _
 have f:(fun x=>F G A (Function.update x l false))=F G0 A:=funext (iV G A l p R C);rcases a0 with⟨q,hq⟩|⟨l',Q,z,S⟩
 ·set G1:=G.deleteEdges {s(p,l),s(p,q)} with a7
  by_cases V:A.Nonempty∨∃i j,G0.Adj i j
  ·have U:(fun x=>F G A (Function.update x l true))=F G1 (insert p A):=
    funext (kT G A l p q R c C hq)
   have b5:∀b:Bool,∃x y:Fin (r+1)→Bool,
     F G A (Function.update x l b)≠F G A (Function.update y l b):=by
    intro b
    cases b
    ·obtain⟨x,y,v⟩:=aBy G0 A V;refine⟨x,y,?_⟩;have H:=congrFun f x;have J:=congrFun f y;rw[H,J];exact v
    ·obtain⟨x,y,v⟩:=aBy G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _));refine⟨x,y,?_⟩;have H:=congrFun U x;have J:=congrFun U y;rw[H,J];exact v
   obtain⟨b,s',b9,d⟩:=dG r (F G A) l s g b5 X
   cases b
   ·rw[f] at d;have u:∀T,yX G0 T→k-1≤T.card:=fun T hT=>by
     have:=O _ (lK G _ p a8 T hT);have:=Finset.card_insert_le p T;omega
    have:=ih G0.edgeSet.ncard (by omega) _ G0 A (k-1) s' rfl N B u V d;omega
   ·rw[U] at d;have a9:∀e∈({s(p,l),s(p,q)}:Set (Sym2 (Fin (r+1)))),p∈e:=by
     intro e w;rcases w with rfl|w
     ·exact Sym2.mem_mk_left _ _
     ·rw[Set.mem_singleton_iff] at w;subst w;exact Sym2.mem_mk_left _ _
    have P:∀T,yX G1 T→k-1≤T.card:=fun T hT=>by have:=O _ (lK G _ p a9 T hT);have:=Finset.card_insert_le p T;omega
    have a4:G1.IsAcyclic:=M.anti (deleteEdges_le _);have a2:∀i j,G1.Adj i j→i∉insert p A:=by
     intro i j h t;rcases Finset.mem_insert.1 t with b2|t
     ·exact xO G l p q hq i j h b2
     ·exact o i j ((deleteEdges_adj).1 h).1 t
    obtain⟨b0,b1⟩:=pD G l p q c;rw[←a7] at b0 b1;have:=ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k-1) s' rfl a4 a2
     P (Or.inl (Finset.insert_nonempty _ _)) d
    rw[Finset.card_insert_of_notMem a3] at this;omega
  ·push Not at V
   obtain⟨a6,K⟩:=V;have b8:m=1:=by have:=hM G0 K;omega
   have P:k≤({p}:Finset (Fin (r+1))).card:=by
    apply O;intro i j b3;have h1:=K i j;rw[deleteEdges_adj] at h1
    push Not at h1
    have h2:=h1 b3;rw[Set.mem_singleton_iff,Sym2.eq_iff] at h2;rcases h2 with⟨_,rfl⟩|⟨rfl,_⟩
    ·exact Or.inr (Finset.mem_singleton_self _)
    ·exact Or.inl (Finset.mem_singleton_self _)
   rw[Finset.card_singleton] at P;subst a6;simp only[Finset.card_empty];omega
 ·obtain⟨s0,rfl⟩:∃s0,s=s0+1:=⟨s-1,by omega⟩
  have E:G0.Adj p l':=(deleteEdges_adj).2 ⟨z,by simp[Q,z.ne.symm]⟩;have a5:∃x y:Fin (r+1)→Bool,
    F G A (Function.update x l false)≠F G A (Function.update y l false):=by
   obtain⟨x,y,v⟩:=aBy G0 A (Or.inr ⟨p,l',E⟩);refine⟨x,y,?_⟩;have H:=congrFun f x;have J:=congrFun f y;rw[H,J];exact v
  have d:=eI r (F G A) l false s0 g a5 X;rw[f] at d;have u:∀T,yX G0 T→k≤T.card:=tR G l p l' k Q z S O;have:=ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl N B u
   (Or.inr ⟨p,l',E⟩) d
  omega
lemma sC
  (n t s:ℕ) (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] (A:Finset (Fin n))
  (d:K.IsAcyclic)
  (h:∀a∈A,∀v:Fin n,¬K.Adj a v)
  (b:A.Nonempty∨∃u v:Fin n,K.Adj u v)
  (e:∀S:Finset (Fin n),K.IsVertexCover (S:Set (Fin n))→t≤S.card)
  (c:dO n (fun x:Fin n→Bool=>
    decide ((∃a∈A,x a=true)∨∃u v:Fin n,K.Adj u v∧x u=true∧x v=true)) s):
  A.card+K.edgeFinset.card+t≤ s+1:=by
 have j:(fun x:Fin n→Bool=>
   decide ((∃a∈A,x a=true)∨∃u v:Fin n,K.Adj u v∧x u=true∧x v=true))=
   F K A:=by
  funext x;rw[Bool.eq_iff_iff,decide_eq_true_iff,hK]
 rw[j] at c;have g:K.edgeFinset.card=K.edgeSet.ncard:=by rw[←Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
 rw[g];exact iQ dO eI dG cD
  _ _ K A t s rfl d (fun u v f k=>h u k v f)
  (fun S i=>e S (fun _ _ f=>i _ _ f)) b c
end
end As
namespace As
lemma eV
  (n t s:ℕ) (K:SimpleGraph (Fin n)) [DecidableRel K.Adj] (A:Finset (Fin n))
  (c:K.IsAcyclic)
  (f:∀a∈A,∀v:Fin n,¬K.Adj a v)
  (b:A.Nonempty∨∃u v:Fin n,K.Adj u v)
  (d:∀S:Finset (Fin n),K.IsVertexCover (S:Set (Fin n))→t≤S.card)
  (e:dO n (fun x:Fin n→Bool=>
    decide ((∃a∈A,x a=true)∨∃u v:Fin n,K.Adj u v∧x u=true∧x v=true)) s):
  A.card+K.edgeFinset.card+t≤ s+1:=
 sC dO eI dG cD
  n t s K A c f b d e
end As
namespace Ap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity As
def iI (g:Gate):Bool:=
 match g.op with
 | .not=>true
 | _=>false
@[local simp] lemma isNot_iff (g : Gate) : iI g = true ↔ g.op = .not := by
 rcases g with⟨op,a⟩
 cases op<;>simp[iI]
def eJ (C:Circuit):ℕ:=C.gates.countP (fun g=> !iI g)
lemma fH (C:Circuit):
  C.size=eJ C+C.gates.countP iI:=by
 simpa[Circuit.size,eJ] using(List.length_eq_countP_add_countP (fun g=> !iI g) (l:=C.gates))
lemma nC {α:Type} {P:α→Prop} {w:List α} {d:α}
  (b:∀u∈w,P u) (a:P d) (i:ℕ):P (w.getD i d):=by
 rw[List.getD_eq_getElem?_getD]
 cases h:w[i]? with
 | none=>exact a
 | some u=>exact b u (List.mem_of_getElem? h)
def cB {n} (w:List (Fn n)) (i:ℕ):Fn n:=w.getD i (fun _=>false)
def yY {n} (w:List (Fn n)) (a:List ℕ) (j:ℕ) (d:Bool):Fn n:=(a.map (cB w)).getD j (fun _=>d)
lemma iW {n} {w:List (Fn n)} {P:Fn n→Prop}
  (a:gY P) (c:∀u∈w,P u) (e:List ℕ) (j:ℕ) (d:Bool):
  P (yY w e j d):=by
 apply nC _ (a.1 d);intro u b;obtain⟨i,-,rfl⟩:=List.mem_map.mp b;exact nC c (a.1 false) i
def eX {n} (w:List (Fn n)) (g:Gate):Fn n:=fun x=>g.op.eval (g.inputs.map (fun i=>cB w i x))
lemma tS {n} (w:List (Fn n)) (a:List ℕ) (b:a.length≤2):
  eX w ⟨.and,a⟩=eP (yY w a 0 true) (yY w a 1 true):=by
 funext x;rcases a with _|⟨i,_|⟨j,_|⟨k,a⟩⟩⟩
 ·rfl
 ·simp[eX,GateOp.eval,eP,yY]
 ·simp[eX,GateOp.eval,eP,yY]
 ·simp at b
lemma vL {n} (w:List (Fn n)) (a:List ℕ) (b:a.length≤2):
  eX w ⟨.or,a⟩=nT (eP (nT (yY w a 0 false)) (nT (yY w a 1 false))):=by
 funext x;rcases a with _|⟨i,_|⟨j,_|⟨k,a⟩⟩⟩
 ·rfl
 ·simp[eX,GateOp.eval,eP,nT,yY]
 ·simp[eX,GateOp.eval,eP,nT,yY]
 ·simp at b
lemma tT {n} (w:List (Fn n)) (a:List ℕ):
  eX w ⟨.not,a⟩=nT (yY w a 0 false):=by
 funext x
 cases a<;>rfl
def step (w:List Bool) (g:Gate):List Bool:=w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma tU {n} (w:List (Fn n)) (g:Gate) (x:Fin n→Bool):
  step (w.map fun u=>u x) g=(w++[eX w g]).map fun u=>u x:=by
 simp only[step,List.map_append,List.map_cons,List.map_nil,eX];congr 3;apply List.map_congr_left;intro i _;exact List.getD_map w (fun _=>false) (fun u:Fn n=>u x)
lemma iX {n} {w:List (Fn n)} {P:Fn n→Prop} {u:Fn n}
  (b:∀v∈w,P v) (c:P u):∀v∈w++[u],P v:=by
 intro v a;rcases List.mem_append.mp a with h|h
 ·exact b v h
 ·rwa [List.mem_singleton.mp h]
lemma vM {n} (gs:List Gate) (out:ℕ)
  (i:FanInTwo (⟨gs,out⟩:Circuit)) (w:List (Fn n)) (P:Fn n→Prop)
  (a:gY P) (b:∀u∈w,P u):
  Build P (fun x=>(gs.foldl step (w.map fun u=>u x)).getD out false) (gs.countP (fun g=> !iI g)):=by
 induction gs generalizing w P with
 | nil=>
   apply Build.oN;change P (fun x=>(w.map fun u=>u x).getD out false);have h:(fun x:Fin n→Bool=>(w.map fun u=>u x).getD out false)=cB w out:=by funext x;exact List.getD_map w (fun _=>false) (fun u:Fn n=>u x)
   rw[h];exact nC b (a.1 false) out
 | cons g gs ih=>
   have ht:FanInTwo (⟨gs,out⟩:Circuit):=fun g h=>i g (List.mem_cons_of_mem _ h)
   obtain⟨e,d⟩:=i g List.mem_cons_self;simp only[List.foldl_cons,tU,List.countP_cons];rcases g with⟨op,c⟩
   change op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) at e;change c.length≤2 at d
   cases op with
   | and=>
     simp only[iI,Bool.not_false,↓reduceIte,tS w c d];refine Build.mF (iW a b c 0 true) (iW a b c 1 true)
      (ih ht _ _ (gZ a _) (iX (fun v f=>Or.inl (b v f)) ?_))
     exact Or.inr (Or.inl rfl)
   | or=>
     simp only[iI,Bool.not_false,↓reduceIte,vL w c d];refine Build.mF (a.2 _ (iW a b c 0 false)) (a.2 _ (iW a b c 1 false))
      (ih ht _ _ (gZ a _) (iX (fun v f=>Or.inl (b v f)) ?_))
     exact Or.inr (Or.inr rfl)
   | not=>
     simpa only[iI,Bool.not_true,Bool.false_eq_true,↓reduceIte,Nat.add_zero,
      tT] using
      ih ht (w++[nT (yY w c 0 false)]) P a
       (iX b (a.2 _ (iW a b c 0 false)))
   | mod m=>simp at e
   | maj=>simp at e
lemma pE (n:ℕ) (C:Circuit) (h:FanInTwo C):
  dO n (circuitFun n C) (eJ C):=by
 let w:List (Fn n):=List.ofFn (fun i:Fin n=>fun x=>x i)
 have b:∀u∈w,iT n u:=by intro u a;obtain⟨i,rfl⟩:=List.mem_ofFn.mp a;exact Or.inr ⟨i,Or.inl rfl⟩
 change Build (iT n) (fun x=>(C.gates.foldl step (List.ofFn x)).getD C.output false) (C.gates.countP (fun g=> !iI g));simpa only[w,List.map_ofFn,Function.comp_def] using vM C.gates C.output h w (iT n) (iU n) b
end Ap
namespace L287_proof
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def mstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mval {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl mstep (List.ofFn x)).getD i false

lemma mfold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl mstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, mstep, List.length_append, List.length_nil]
    omega

lemma mfold_append (gs1 gs2 : List Gate) (w : List Bool) :
    (gs1 ++ gs2).foldl mstep w = gs2.foldl mstep (gs1.foldl mstep w) := by
  simp [List.foldl_append]

lemma mfold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl mstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [mstep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma mval_append_lt {n : ℕ} (gs1 gs2 : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs1.length) :
    mval (gs1 ++ gs2) x i = mval gs1 x i := by
  unfold mval
  rw [mfold_append]
  exact mfold_getD_lt gs2 _ i (by rw [mfold_len]; simp; omega)

lemma mval_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    mval (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => mval gs x j)
      else mval gs x i := by
  unfold mval
  rw [mfold_append]
  simp only [List.foldl_cons, List.foldl_nil, mstep]
  have hl : (gs.foldl mstep (List.ofFn x)).length = n + gs.length := by
    rw [mfold_len]; simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    exact List.getD_append _ _ _ _ (by omega)
  · rw [ite_eq_left (by omega)]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_default _ _ (by simp [hl]; omega),
      List.getD_eq_default _ _ (by omega)]

lemma mval_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    mval gs x i.val = x i := by
  unfold mval
  rw [mfold_getD_lt gs (List.ofFn x) i.val (by simp)]
  simp

lemma mval_oob {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    mval gs x i = false := by
  unfold mval
  exact List.getD_eq_default _ _ (by rw [mfold_len]; simp; omega)

lemma mval_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    mval gs x (n + j) = (gs[j]).op.eval ((gs[j]).inputs.map fun r =>
      if r < n + j then mval gs x r else false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    rw [List.append_assoc, List.cons_append, List.nil_append, ← List.drop_eq_getElem_cons hj,
      List.take_append_drop]
  have hlen : (gs.take j).length = j := List.length_take_of_le hj.le
  have heq1 : mval gs x (n + j) = mval (gs.take j ++ [gs[j]]) x (n + j) := by
    conv_lhs => rw [hsplit]
    exact mval_append_lt _ _ x (n + j) (by rw [List.length_append, hlen]; simp)
  rw [heq1, mval_snoc, ite_eq_left (by omega)]
  congr 1
  apply List.map_congr_left
  intro r _
  by_cases hr : r < n + j
  · rw [ite_eq_left hr]
    conv_rhs => rw [hsplit, List.append_assoc]
    rw [mval_append_lt (gs.take j) _ x r (by omega)]
  · rw [ite_eq_right hr]
    exact mval_oob (gs.take j) x r (by omega)

lemma list_any_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

def orChainAux (n : ℕ) : List ℕ → List Gate × ℕ → List Gate × ℕ
  | [], acc => acc
  | w :: ws, (gs, cur) =>
      orChainAux n ws (gs ++ [⟨GateOp.or, [cur, w]⟩], n + gs.length)

lemma orChainAux_spec (n : ℕ) (ws : List ℕ) : ∀ (gs : List Gate) (cur : ℕ),
    cur < n + gs.length → (∀ w ∈ ws, w < n + gs.length) →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    let res := orChainAux n ws (gs, cur)
    res.1.length = gs.length + ws.length ∧
    res.2 < n + res.1.length ∧
    (∃ t, res.1 = gs ++ t) ∧
    (∀ g ∈ res.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ x : Fin n → Bool, mval res.1 x res.2 =
      (mval gs x cur || ws.any (fun w => mval gs x w))) := by
  induction ws with
  | nil =>
    intro gs cur hcur _ hok
    exact ⟨by simp [orChainAux], hcur, ⟨[], by simp [orChainAux]⟩, hok,
      fun x => by simp [orChainAux]⟩
  | cons w ws ih =>
    intro gs cur hcur hws hok
    have hw : w < n + gs.length := hws w List.mem_cons_self
    let gs1 := gs ++ [⟨GateOp.or, [cur, w]⟩]
    have hlen1 : gs1.length = gs.length + 1 := by simp [gs1]
    have hok1 : ∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hok g hg
      · rw [List.mem_singleton.mp hg]; simp
    obtain ⟨h1, h2, ⟨t, ht⟩, h4, h5⟩ := ih gs1 (n + gs.length) (by omega)
      (fun u hu => by have := hws u (List.mem_cons_of_mem _ hu); omega) hok1
    refine ⟨?_, h2,
      ⟨⟨GateOp.or, [cur, w]⟩ :: t, by simpa [orChainAux, gs1, List.append_assoc] using ht⟩,
      h4, ?_⟩
    · change (orChainAux n ws (gs1, n + gs.length)).1.length = gs.length + (w :: ws).length
      rw [h1, hlen1, List.length_cons]; omega
    · intro x
      change mval (orChainAux n ws (gs1, n + gs.length)).1 x
        (orChainAux n ws (gs1, n + gs.length)).2 = _
      rw [h5 x]
      have hcur' : mval gs1 x (n + gs.length) = (mval gs x cur || mval gs x w) := by
        rw [mval_snoc, ite_eq_left rfl]
        simp [GateOp.eval]
      have hany : ws.any (fun u => mval gs1 x u) = ws.any (fun u => mval gs x u) := by
        apply list_any_congr
        intro u hu
        exact mval_append_lt gs _ x u (hws u (List.mem_cons_of_mem _ hu))
      rw [hcur', hany, List.any_cons, Bool.or_assoc]

def orChain (n : ℕ) (ws : List ℕ) (gs : List Gate) : List Gate × ℕ :=
  match ws with
  | [] => (gs, n + gs.length)
  | w :: rest => orChainAux n rest (gs, w)

lemma orChain_spec (n : ℕ) (ws : List ℕ) (hne : ws ≠ []) (gs : List Gate)
    (hws : ∀ w ∈ ws, w < n + gs.length)
    (hok : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    let res := orChain n ws gs
    res.1.length + 1 = gs.length + ws.length ∧
    res.2 < n + res.1.length ∧
    (∃ t, res.1 = gs ++ t) ∧
    (∀ g ∈ res.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ x : Fin n → Bool, mval res.1 x res.2 = ws.any (fun w => mval gs x w)) := by
  cases ws with
  | nil => exact False.elim (hne rfl)
  | cons w rest =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := orChainAux_spec n rest gs w
      (hws w List.mem_cons_self) (fun u hu => hws u (List.mem_cons_of_mem _ hu)) hok
    exact ⟨by simp [orChain, h1]; omega, h2, h3, h4,
      fun x => by simpa [orChain, List.any_cons] using h5 x⟩

def buildTerms {n : ℕ} (N : Fin n → List (Fin n)) : List (Fin n) → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | s :: rest, gs =>
      let r1 := orChain n ((N s).map Fin.val) gs
      let gs2 := r1.1 ++ [⟨GateOp.and, [s.val, r1.2]⟩]
      let w := n + r1.1.length
      let r2 := buildTerms N rest gs2
      (r2.1, w :: r2.2)

lemma buildTerms_spec {n : ℕ} (N : Fin n → List (Fin n)) (L : List (Fin n)) :
    ∀ (gs : List Gate),
    (∀ s ∈ L, N s ≠ []) →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    let res := buildTerms N L gs
    res.1.length = gs.length + (L.map (fun s => (N s).length)).sum ∧
    res.2.length = L.length ∧
    (∀ w ∈ res.2, w < n + res.1.length) ∧
    (∃ t, res.1 = gs ++ t) ∧
    (∀ g ∈ res.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ x : Fin n → Bool, res.2.any (fun w => mval res.1 x w) =
      decide (∃ s ∈ L, x s = true ∧ ∃ v ∈ N s, x v = true)) := by
  induction L with
  | nil =>
    intro gs _ hok
    exact ⟨by simp [buildTerms], by simp [buildTerms], by simp [buildTerms],
      ⟨[], by simp [buildTerms]⟩, hok, fun x => by simp [buildTerms]⟩
  | cons s rest ih =>
    intro gs hne hok
    have hns : (N s).map Fin.val ≠ [] := by
      intro h; exact hne s List.mem_cons_self (List.map_eq_nil_iff.mp h)
    obtain ⟨h1, h2, ⟨t1, ht1⟩, h4, h5⟩ := orChain_spec n ((N s).map Fin.val) hns gs
      (fun w hw => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw; omega) hok
    let r1 := orChain n ((N s).map Fin.val) gs
    let gs2 := r1.1 ++ [⟨GateOp.and, [s.val, r1.2]⟩]
    have hok2 : ∀ g ∈ gs2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h4 g hg
      · rw [List.mem_singleton.mp hg]; simp
    obtain ⟨k1, k2, k3, ⟨t2, ht2⟩, k5, k6⟩ := ih gs2
      (fun u hu => hne u (List.mem_cons_of_mem _ hu)) hok2
    have hgs2_len : gs2.length = gs.length + (N s).length := by
      have : r1.1.length + 1 = gs.length + (N s).length := by
        simpa [r1, List.length_map] using h1
      simp [gs2]; omega
    refine ⟨?_, ?_, ?_, ?_, k5, ?_⟩
    · change (buildTerms N rest gs2).1.length = gs.length + ((s :: rest).map fun s => (N s).length).sum
      rw [k1, hgs2_len, List.map_cons, List.sum_cons, Nat.add_assoc]
    · change ((n + r1.1.length) :: (buildTerms N rest gs2).2).length = (s :: rest).length
      simp [k2]
    · intro w hw
      change w ∈ (n + r1.1.length) :: (buildTerms N rest gs2).2 at hw
      change w < n + (buildTerms N rest gs2).1.length
      rcases List.mem_cons.mp hw with rfl | hw
      · have hle : gs2.length ≤ (buildTerms N rest gs2).1.length := by rw [ht2]; simp
        have hgs2 : gs2.length = r1.1.length + 1 := by simp [gs2]
        omega
      · exact k3 w hw
    · refine ⟨t1 ++ [⟨GateOp.and, [s.val, r1.2]⟩] ++ t2, ?_⟩
      change (buildTerms N rest gs2).1 = _
      rw [ht2]
      simp [gs2, r1, ht1, List.append_assoc]
    · intro x
      change (mval (buildTerms N rest gs2).1 x (n + r1.1.length) ||
        (buildTerms N rest gs2).2.any (fun w => mval (buildTerms N rest gs2).1 x w)) = _
      rw [k6 x]
      have hterm : mval (buildTerms N rest gs2).1 x (n + r1.1.length) =
          (x s && decide (∃ v ∈ N s, x v = true)) := by
        rw [ht2, mval_append_lt gs2 t2 x (n + r1.1.length) (by simp [gs2])]
        rw [mval_snoc, ite_eq_left rfl]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, mval_input]
        congr 1
        rw [h5 x]
        rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨w, hw, hvw⟩
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
          exact ⟨v, hv, by rwa [mval_input] at hvw⟩
        · rintro ⟨v, hv, hxv⟩
          exact ⟨v.val, List.mem_map.mpr ⟨v, hv, rfl⟩, by rwa [mval_input]⟩
      rw [hterm]
      rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        decide_eq_true_eq, decide_eq_true_eq]
      simp [exists_eq_or_imp]

lemma cover_upper {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A S : Finset (Fin n))
    (hNe : A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v)
    (hScov : CoverPromise.IsVertexCover G S) (hScard : S.card = t)
    (hMin : ∀ S' : Finset (Fin n), CoverPromise.IsVertexCover G S' → t ≤ S'.card) :
    ∃ C : Circuit, FanInTwo C ∧ C.size + 1 = A.card + G.edgeFinset.card + t ∧
      circuitFun n C = (fun x : Fin n → Bool =>
        decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) := by
  classical
  let Nset (s : Fin n) : Finset (Fin n) :=
    Finset.univ.filter fun v => G.Adj s v ∧ (v ∈ S → s < v)
  have hNne : ∀ s ∈ S, (Nset s).Nonempty := by
    intro s hs
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hcov' : CoverPromise.IsVertexCover G (S.erase s) := by
      intro u v huv
      rcases hScov u v huv with hu | hv
      · by_cases hus : u = s
        · subst hus
          by_cases hvS : v ∈ S
          · exact Or.inr (Finset.mem_erase.mpr ⟨huv.ne.symm, hvS⟩)
          · have : v ∈ Nset u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, fun h => False.elim (hvS h)⟩
            rw [hemp] at this; simp at this
        · exact Or.inl (Finset.mem_erase.mpr ⟨hus, hu⟩)
      · by_cases hvs : v = s
        · subst hvs
          by_cases huS : u ∈ S
          · exact Or.inl (Finset.mem_erase.mpr ⟨huv.ne, huS⟩)
          · have : u ∈ Nset v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, fun h => False.elim (huS h)⟩
            rw [hemp] at this; simp at this
        · exact Or.inr (Finset.mem_erase.mpr ⟨hvs, hv⟩)
    have hle := hMin (S.erase s) hcov'
    have hlt : (S.erase s).card < S.card := Finset.card_erase_lt_of_mem hs
    omega
  have hNsum : ∑ s ∈ S, (Nset s).card = G.edgeFinset.card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · rintro ⟨s, v⟩ hp
      simp only [Finset.mem_sigma, Nset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact SimpleGraph.mem_edgeFinset.mpr hp.2.1
    · rintro ⟨s1, v1⟩ h1 ⟨s2, v2⟩ h2 heq
      simp only [Finset.mem_sigma, Nset, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · have hlt1 : s1 < v1 := h1.2.2 h2.1
        have hlt2 : v1 < s1 := h2.2.2 h1.1
        exact False.elim (lt_asymm hlt1 hlt2)
    · intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        rcases hScov u v huv with hu | hv
        · by_cases hv : v ∈ S
          · rcases lt_or_gt_of_ne huv.ne with hlt | hgt
            · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨hu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, fun _ => hlt⟩⟩, rfl⟩
            · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, fun _ => hgt⟩⟩, Sym2.eq_swap⟩
          · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨hu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, fun h => False.elim (hv h)⟩⟩, rfl⟩
        · by_cases hu : u ∈ S
          · rcases lt_or_gt_of_ne huv.ne with hlt | hgt
            · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨hu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, fun _ => hlt⟩⟩, rfl⟩
            · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, fun _ => hgt⟩⟩, Sym2.eq_swap⟩
          · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, fun h => False.elim (hu h)⟩⟩, Sym2.eq_swap⟩
  let Nlist (s : Fin n) : List (Fin n) := (Nset s).toList
  obtain ⟨b1, b2, b3, -, b5, b6⟩ := buildTerms_spec Nlist S.toList []
    (fun s hs => by
      have hsS : s ∈ S := Finset.mem_toList.mp hs
      intro h
      obtain ⟨v, hv⟩ := hNne s hsS
      have hv' : v ∈ Nlist s := Finset.mem_toList.mpr hv
      rw [h] at hv'
      simp at hv')
    (by simp)
  let rT := buildTerms Nlist S.toList []
  let topWires := A.toList.map Fin.val ++ rT.2
  have htopNe : topWires ≠ [] := by
    intro hemp
    rcases List.append_eq_nil_iff.mp hemp with ⟨hA, hR⟩
    rcases hNe with ⟨a, ha⟩ | ⟨u, v, huv⟩
    · have : a.val ∈ A.toList.map Fin.val := List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩
      rw [hA] at this; simp at this
    · have hSne : S.Nonempty := by
        rcases hScov u v huv with hu | hv
        · exact ⟨u, hu⟩
        · exact ⟨v, hv⟩
      have hlen : rT.2.length = S.card := by
        simpa [rT, Finset.length_toList] using b2
      have hlen0 : rT.2.length = 0 := by rw [hR]; rfl
      have hpos := hSne.card_pos
      omega
  obtain ⟨c1, -, ⟨tTop, htTop⟩, c4, c5⟩ := orChain_spec n topWires htopNe rT.1
    (fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hw; omega
      · exact b3 w hw)
    b5
  let rTop := orChain n topWires rT.1
  refine ⟨⟨rTop.1, rTop.2⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop, hlen⟩ := c4 g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h <;> simp [h]
  · have hsumL : (S.toList.map fun s => (Nlist s).length).sum = G.edgeFinset.card := by
      rw [← hNsum]
      have h1 : (S.toList.map fun s => (Nlist s).length).sum =
          (S.toList.map fun s => (Nset s).card).sum := by
        congr 1; apply List.map_congr_left; intro s _; exact Finset.length_toList (Nset s)
      rw [h1]
      change (Multiset.map (fun s => (Nset s).card) (S.toList : Multiset (Fin n))).sum = _
      rw [Finset.coe_toList]
      rfl
    have hrTlen : rT.1.length = G.edgeFinset.card := by
      simpa [rT, hsumL] using b1
    have htopLen : topWires.length = A.card + t := by
      simp only [topWires, List.length_append, List.length_map, Finset.length_toList]
      have hb2 : rT.2.length = S.card := by simpa [rT, Finset.length_toList] using b2
      omega
    change rTop.1.length + 1 = _
    rw [c1, hrTlen, htopLen]
    omega
  · funext x
    change mval rTop.1 x rTop.2 = _
    rw [c5 x, List.any_append, b6 x]
    have hAany : (A.toList.map Fin.val).any (fun w => mval rT.1 x w) =
        decide (∃ a ∈ A, x a = true) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨w, hw, hvw⟩
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
        exact ⟨a, Finset.mem_toList.mp ha, by rwa [mval_input] at hvw⟩
      · rintro ⟨a, ha, hxa⟩
        exact ⟨a.val, List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩, by rwa [mval_input]⟩
    rw [hAany, Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      decide_eq_true_eq]
    constructor
    · rintro (h | ⟨s, hs, hxs, v, hv, hxv⟩)
      · exact Or.inl h
      · have hv' : v ∈ Nset s := Finset.mem_toList.mp hv
        exact Or.inr ⟨s, v, (Finset.mem_filter.mp hv').2.1, hxs, hxv⟩
    · rintro (h | ⟨u, v, huv, hxu, hxv⟩)
      · exact Or.inl h
      · right
        rcases hScov u v huv with hu | hv
        · by_cases hv : v ∈ S
          · rcases lt_or_gt_of_ne huv.ne with hlt | hgt
            · exact ⟨u, Finset.mem_toList.mpr hu, hxu, v, Finset.mem_toList.mpr
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, fun _ => hlt⟩), hxv⟩
            · exact ⟨v, Finset.mem_toList.mpr hv, hxv, u, Finset.mem_toList.mpr
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, fun _ => hgt⟩), hxu⟩
          · exact ⟨u, Finset.mem_toList.mpr hu, hxu, v, Finset.mem_toList.mpr
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, fun h => False.elim (hv h)⟩), hxv⟩
        · by_cases hu : u ∈ S
          · rcases lt_or_gt_of_ne huv.ne with hlt | hgt
            · exact ⟨u, Finset.mem_toList.mpr hu, hxu, v, Finset.mem_toList.mpr
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, fun _ => hlt⟩), hxv⟩
            · exact ⟨v, Finset.mem_toList.mpr hv, hxv, u, Finset.mem_toList.mpr
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, fun _ => hgt⟩), hxu⟩
          · exact ⟨v, Finset.mem_toList.mpr hv, hxv, u, Finset.mem_toList.mpr
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, fun h => False.elim (hu h)⟩), hxu⟩

abbrev MStat := Bool ⊕ ℕ

def msVal (w : List Bool) : MStat → Bool
  | Sum.inl b => b
  | Sum.inr i => w.getD i false

def msValid (k : ℕ) : MStat → Prop
  | Sum.inl _ => True
  | Sum.inr i => i < k

def simpAndM (m : ℕ) : List MStat → Option Gate × MStat
  | [] => (none, Sum.inl true)
  | [s] => (none, s)
  | [Sum.inl false, _] => (none, Sum.inl false)
  | [_, Sum.inl false] => (none, Sum.inl false)
  | [Sum.inl true, s] => (none, s)
  | [s, Sum.inl true] => (none, s)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOrM (m : ℕ) : List MStat → Option Gate × MStat
  | [] => (none, Sum.inl false)
  | [s] => (none, s)
  | [Sum.inl true, _] => (none, Sum.inl true)
  | [_, Sum.inl true] => (none, Sum.inl true)
  | [Sum.inl false, s] => (none, s)
  | [s, Sum.inl false] => (none, s)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpM (op : GateOp) (m : ℕ) (ins : List MStat) : Option Gate × MStat :=
  match op with
  | GateOp.and => simpAndM m ins
  | GateOp.or => simpOrM m ins
  | _ => (none, Sum.inl false)

def mOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma simpM_ok (op : GateOp) (m : ℕ) (ins : List MStat) :
    ∀ g ∈ (simpM op m ins).1, mOk g := by
  intro g hg
  cases op <;> simp only [simpM] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAndM] at hg
    · simp [simpAndM] at hg
    · rcases a with ba | ja <;> rcases b with bb | jb <;>
        (try cases ba) <;> (try cases bb) <;>
        simp [simpAndM] at hg <;> (subst hg; simp [mOk])
    · simp [simpAndM] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOrM] at hg
    · simp [simpOrM] at hg
    · rcases a with ba | ja <;> rcases b with bb | jb <;>
        (try cases ba) <;> (try cases bb) <;>
        simp [simpOrM] at hg <;> (subst hg; simp [mOk])
    · simp [simpOrM] at hg
  · simp at hg
  · simp at hg
  · simp at hg

lemma simpM_op (op : GateOp) (m : ℕ) (ins : List MStat) :
    ∀ g ∈ (simpM op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simpM] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAndM] at hg
    · simp [simpAndM] at hg
    · rcases a with ba | ja <;> rcases b with bb | jb <;>
        (try cases ba) <;> (try cases bb) <;>
        simp [simpAndM] at hg <;> (subst hg; rfl)
    · simp [simpAndM] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOrM] at hg
    · simp [simpOrM] at hg
    · rcases a with ba | ja <;> rcases b with bb | jb <;>
        (try cases ba) <;> (try cases bb) <;>
        simp [simpOrM] at hg <;> (subst hg; rfl)
    · simp [simpOrM] at hg
  · simp at hg
  · simp at hg
  · simp at hg

lemma simpM_and_false (m : ℕ) (ins : List MStat) (hlen : ins.length ≤ 2)
    (hf : Sum.inl false ∈ ins) : (simpM GateOp.and m ins).2 = Sum.inl false := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hf
  · simp only [List.mem_singleton] at hf; subst hf; rfl
  · rcases a with ba | ja <;> rcases b with bb | jb <;>
      (try cases ba) <;> (try cases bb) <;> simp_all [simpM, simpAndM]
  · simp at hlen

lemma simpM_or_true (m : ℕ) (ins : List MStat) (hlen : ins.length ≤ 2)
    (ht : Sum.inl true ∈ ins) : (simpM GateOp.or m ins).2 = Sum.inl true := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at ht
  · simp only [List.mem_singleton] at ht; subst ht; rfl
  · rcases a with ba | ja <;> rcases b with bb | jb <;>
      (try cases ba) <;> (try cases bb) <;> simp_all [simpM, simpOrM]
  · simp at hlen

lemma simpM_none_of_const (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (ins : List MStat) (hlen : ins.length ≤ 2) (b : Bool) (hb : Sum.inl b ∈ ins) :
    (simpM op m ins).1 = none := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, l⟩⟩⟩
    · simp at hb
    · rfl
    · rcases a with ba | ja <;> rcases c with bc | jc <;>
        (try cases ba) <;> (try cases bc) <;> simp_all [simpM, simpAndM]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, l⟩⟩⟩
    · simp at hb
    · rfl
    · rcases a with ba | ja <;> rcases c with bc | jc <;>
        (try cases ba) <;> (try cases bc) <;> simp_all [simpM, simpOrM]
    · simp at hlen

lemma simpM_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List MStat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, msValid w.length s) :
    msValid (w.length + (simpM op w.length ins).1.toList.length) (simpM op w.length ins).2 ∧
    msVal ((simpM op w.length ins).1.toList.foldl mstep w) (simpM op w.length ins).2 =
      op.eval (ins.map (msVal w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpM, simpAndM, msValid, msVal, GateOp.eval]
    · rcases a with ba | ja <;> simp_all [simpM, simpAndM, msValid, msVal, GateOp.eval]
    · rcases a with ba | ja <;> rcases b with bb | jb <;>
        (try cases ba) <;> (try cases bb) <;>
        simp_all [simpM, simpAndM, msValid, msVal, GateOp.eval, mstep]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpM, simpOrM, msValid, msVal, GateOp.eval]
    · rcases a with ba | ja <;> simp_all [simpM, simpOrM, msValid, msVal, GateOp.eval]
    · rcases a with ba | ja <;> rcases b with bb | jb <;>
        (try cases ba) <;> (try cases bb) <;>
        simp_all [simpM, simpOrM, msValid, msVal, GateOp.eval, mstep]
    · simp at hlen

def elimStepM (n : ℕ) (acc : List MStat × List Gate) (g : Gate) : List MStat × List Gate :=
  let r := simpM g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimM (n : ℕ) (gs : List Gate) (acc : List MStat × List Gate) : List MStat × List Gate :=
  gs.foldl (elimStepM n) acc

def initStat {n : ℕ} (ρ : Fin n → Option Bool) : List MStat :=
  List.ofFn fun i : Fin n => match ρ i with | some b => Sum.inl b | none => Sum.inr i.val

def applySubst {n : ℕ} (ρ : Fin n → Option Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => match ρ i with | some b => b | none => x i

lemma elimM_getD_lt (n : ℕ) (gs : List Gate) : ∀ (acc : List MStat × List Gate) (k : ℕ),
    k < acc.1.length → (elimM n gs acc).1.getD k (Sum.inl false) = acc.1.getD k (Sum.inl false) := by
  induction gs with
  | nil => intro acc k _; rfl
  | cons g gs ih =>
    intro acc k hk
    change (elimM n gs (elimStepM n acc g)).1.getD k _ = _
    rw [ih _ k (by simp [elimStepM]; omega)]
    exact List.getD_append _ _ _ _ hk

lemma elimM_len1 (n : ℕ) (gs : List Gate) : ∀ acc : List MStat × List Gate,
    (elimM n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elimM]
  | cons g gs ih =>
    intro acc
    change (elimM n gs (elimStepM n acc g)).1.length = _
    rw [ih]; simp [elimStepM]; omega

lemma elimM_ok (n : ℕ) (gs : List Gate) : ∀ acc : List MStat × List Gate,
    (∀ g ∈ acc.2, mOk g) → ∀ g ∈ (elimM n gs acc).2, mOk g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih
    intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact h g' hg'
    · exact simpM_ok _ _ _ g' (Option.mem_toList.mp hg')

noncomputable def countOp (op : GateOp) (gs : List Gate) : ℕ :=
  open Classical in gs.countP (fun g => decide (g.op = op))

lemma elimM_countOp_le (n : ℕ) (op : GateOp) (gs : List Gate) :
    ∀ acc : List MStat × List Gate,
    countOp op (elimM n gs acc).2 ≤ countOp op acc.2 + countOp op gs := by
  classical
  induction gs with
  | nil => intro acc; simp [elimM, countOp]
  | cons g gs ih =>
    intro acc
    change countOp op (elimM n gs (elimStepM n acc g)).2 ≤ _
    have h1 := ih (elimStepM n acc g)
    have h2 : countOp op (elimStepM n acc g).2 ≤
        countOp op acc.2 + (if g.op = op then 1 else 0) := by
      simp only [elimStepM, countOp, List.countP_append]
      cases hopt : (simpM g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
      | none => simp
      | some g' =>
        have hgop : g'.op = g.op := simpM_op g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) g' hopt
        simp only [Option.toList_some, List.countP_cons, List.countP_nil, hgop]
        by_cases h : g.op = op <;> simp [h]
    have h3 : countOp op (g :: gs) = countOp op gs + (if g.op = op then 1 else 0) := by
      simp only [countOp, List.countP_cons]
      by_cases h : g.op = op <;> simp [h]
    omega

lemma elimM_sound {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (acc : List MStat × List Gate) (w : List Bool),
    (∀ g ∈ gs, mOk g) →
    acc.1.length = w.length →
    (∀ s ∈ acc.1, msValid (n + acc.2.length) s) →
    (∀ k < acc.1.length, msVal (acc.2.foldl mstep (List.ofFn x)) (acc.1.getD k (Sum.inl false)) =
      w.getD k false) →
    (∀ k < (elimM n gs acc).1.length,
      msVal ((elimM n gs acc).2.foldl mstep (List.ofFn x))
        ((elimM n gs acc).1.getD k (Sum.inl false)) =
      (gs.foldl mstep w).getD k false) := by
  induction gs with
  | nil =>
    intro acc w _ _ _ hag k hk
    exact hag k hk
  | cons g gs ih =>
    intro acc w hok hlen hval hag
    have hgok : mOk g := hok g List.mem_cons_self
    let W := acc.2.foldl mstep (List.ofFn x)
    have hWlen : W.length = n + acc.2.length := by
      simp [W, mfold_len]
    let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    have hinsVal : ∀ s ∈ ins, msValid W.length s := by
      intro s hs
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
      rw [hWlen]
      by_cases hi : i < acc.1.length
      · rw [List.getD_eq_getElem _ _ hi]; exact hval _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; trivial
    obtain ⟨hnewV, hnewEq⟩ := simpM_sound g.op hgok.1 W ins
      (by simpa [ins] using hgok.2) hinsVal
    have hinsEq : ins.map (msVal W) = g.inputs.map (fun i => w.getD i false) := by
      simp only [ins, List.map_map]
      apply List.map_congr_left
      intro i _
      change msVal W (acc.1.getD i (Sum.inl false)) = w.getD i false
      by_cases hi : i < acc.1.length
      · exact hag i hi
      · rw [List.getD_eq_default acc.1 (Sum.inl false) (by omega),
          List.getD_eq_default w false (by omega)]
        rfl
    let acc1 := elimStepM n acc g
    have hacc1_eq : acc1.2.foldl mstep (List.ofFn x) =
        (simpM g.op W.length ins).1.toList.foldl mstep W := by
      simp only [acc1, elimStepM, mfold_append, W, hWlen, ins]
    apply ih acc1 (mstep w g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [acc1, elimStepM, mstep, hlen])
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · have hv := hval s hs
        cases s with
        | inl b => trivial
        | inr j => simp only [msValid, acc1, elimStepM, List.length_append] at hv ⊢; omega
      · rw [List.mem_singleton.mp hs]
        have hlenEq : n + acc1.2.length = W.length + (simpM g.op W.length ins).1.toList.length := by
          simp only [acc1, elimStepM, List.length_append, hWlen, ins]; omega
        rw [hlenEq]
        simpa only [hWlen, ins] using hnewV
    · intro k hk
      simp only [acc1, elimStepM, List.length_append, List.length_cons, List.length_nil] at hk
      by_cases hk1 : k < acc.1.length
      · have h1 : acc1.1.getD k (Sum.inl false) = acc.1.getD k (Sum.inl false) :=
          List.getD_append _ _ _ _ hk1
        have h2 : (mstep w g).getD k false = w.getD k false :=
          List.getD_append _ _ _ _ (by omega)
        rw [h1, h2, hacc1_eq]
        have hs := hag k hk1
        have hsv : msValid W.length (acc.1.getD k (Sum.inl false)) := by
          rw [hWlen, List.getD_eq_getElem _ _ hk1]; exact hval _ (List.getElem_mem hk1)
        cases hst : acc.1.getD k (Sum.inl false) with
        | inl b =>
          rw [hst] at hs
          simpa [msVal] using hs
        | inr j =>
          rw [hst] at hsv hs
          simp only [msVal] at hs ⊢
          rw [mfold_getD_lt _ W j hsv]
          exact hs
      · have hkeq : k = acc.1.length := by omega
        subst hkeq
        have h1 : acc1.1.getD acc.1.length (Sum.inl false) = (simpM g.op W.length ins).2 := by
          simp only [acc1, elimStepM, hWlen, ins]
          rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
        have h2 : (mstep w g).getD acc.1.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [mstep, hlen]
        rw [h1, h2, hacc1_eq, ← hinsEq]
        exact hnewEq

lemma elimM_sound_init {n : ℕ} (gs : List Gate) (hok : ∀ g ∈ gs, mOk g)
    (ρ : Fin n → Option Bool) (x : Fin n → Bool) (k : ℕ)
    (hk : k < (elimM n gs (initStat ρ, [])).1.length) :
    msVal ((elimM n gs (initStat ρ, [])).2.foldl mstep (List.ofFn x))
      ((elimM n gs (initStat ρ, [])).1.getD k (Sum.inl false)) =
    mval gs (applySubst ρ x) k := by
  apply elimM_sound gs x (initStat ρ, []) (List.ofFn (applySubst ρ x)) hok
    (by simp [initStat])
  · intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    cases ρ i <;> simp [msValid]
  · intro j hj
    have hjn : j < n := by simpa [initStat] using hj
    have h1 : (initStat ρ).getD j (Sum.inl false) =
        match ρ ⟨j, hjn⟩ with | some b => Sum.inl b | none => Sum.inr j := by
      rw [List.getD_eq_getElem _ _ (by simp [initStat, hjn])]
      simp [initStat]
    have h2 : (List.ofFn (applySubst ρ x)).getD j false = applySubst ρ x ⟨j, hjn⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp [hjn])]
      simp
    rw [List.foldl_nil, h1, h2]
    unfold applySubst
    cases ρ ⟨j, hjn⟩ with
    | none =>
      simp only [msVal]
      rw [List.getD_eq_getElem _ _ (by simp [hjn])]
      simp
    | some b => rfl
  · exact hk

lemma elimM_step_at {n : ℕ} (gs : List Gate) (ρ : Fin n → Option Bool) (j : ℕ) (hj : j < gs.length) :
    let pre := elimM n (gs.take j) (initStat ρ, [])
    let r := simpM (gs[j]).op (n + pre.2.length)
      ((gs[j]).inputs.map fun i => pre.1.getD i (Sum.inl false))
    (elimM n gs (initStat ρ, [])).1.getD (n + j) (Sum.inl false) = r.2 ∧
    (r.1 = none → countOp (gs[j]).op (elimM n gs (initStat ρ, [])).2 + 1 ≤
      countOp (gs[j]).op gs) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  let pre := elimM n (gs.take j) (initStat ρ, [])
  have hlenPre : pre.1.length = n + j := by
    dsimp only [pre]; rw [elimM_len1]; simp [initStat, List.length_take_of_le hj.le]
  let mid := elimStepM n pre (gs[j])
  have hfold : elimM n gs (initStat ρ, []) = elimM n (gs.drop (j + 1)) mid := by
    calc elimM n gs (initStat ρ, [])
        = elimM n (gs.take j ++ gs[j] :: gs.drop (j + 1)) (initStat ρ, []) := by rw [← hsplit]
      _ = elimM n (gs.drop (j + 1)) mid := by
          simp only [elimM, List.foldl_append, List.foldl_cons, pre, mid]
  constructor
  · have hlt : n + j < mid.1.length := by
      simp only [mid, elimStepM, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hfold, elimM_getD_lt n (gs.drop (j + 1)) mid (n + j) hlt]
    change (pre.1 ++ [_]).getD (n + j) (Sum.inl false) = _
    rw [List.getD_append_right _ _ _ _ (by omega), hlenPre, Nat.sub_self, List.getD_cons_zero]
  · intro hnone
    rw [hfold]
    set op := (gs[j]).op with hopDef
    have h1 := elimM_countOp_le n op (gs.drop (j + 1)) mid
    have h2 : countOp op mid.2 = countOp op pre.2 := by
      dsimp only [mid, elimStepM]
      have hnone' : (simpM gs[j].op (n + pre.2.length)
          (List.map (fun i => pre.1.getD i (Sum.inl false)) gs[j].inputs)).1 = none := by
        simpa only [← hopDef, pre] using hnone
      rw [hnone']
      simp [countOp]
    have h3 := elimM_countOp_le n op (gs.take j) (initStat ρ, [])
    have h3' : countOp op pre.2 ≤ countOp op (gs.take j) := by
      simpa [pre, countOp] using h3
    have h4 : countOp op gs =
        countOp op (gs.take j) + 1 + countOp op (gs.drop (j + 1)) := by
      classical
      calc countOp op gs
          = countOp op (gs.take j ++ gs[j] :: gs.drop (j + 1)) := by rw [← hsplit]
        _ = countOp op (gs.take j) + 1 + countOp op (gs.drop (j + 1)) := by
            simp only [countOp, List.countP_append, List.countP_cons, ← hopDef, decide_true, ↓reduceIte]
            omega
    omega

lemma path_elim_const {n : ℕ} (gs : List Gate) (hok : ∀ g ∈ gs, mOk g)
    (ρ : Fin n → Option Bool) (b : Bool) (u : Fin n) (hρu : ρ u = some b)
    (x1 x2 : Fin n → Bool) (hagree : ∀ v : Fin n, v ≠ u → x1 v = x2 v) :
    ∀ w : ℕ, mval gs x1 w ≠ mval gs x2 w →
      (elimM n gs (initStat ρ, [])).1.getD w (Sum.inl false) ≠ Sum.inl b →
      countOp (if b then GateOp.and else GateOp.or) (elimM n gs (initStat ρ, [])).2 + 1 ≤
        countOp (if b then GateOp.and else GateOp.or) gs := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hdiff hne
    by_cases hwn : w < n
    · have hwu : (⟨w, hwn⟩ : Fin n) = u := by
        by_contra h
        apply hdiff
        rw [mval_input gs x1 ⟨w, hwn⟩, mval_input gs x2 ⟨w, hwn⟩]
        exact hagree ⟨w, hwn⟩ h
      exfalso
      apply hne
      rw [elimM_getD_lt n gs (initStat ρ, []) w (by simp [initStat, hwn])]
      rw [List.getD_eq_getElem _ _ (by simp [initStat, hwn])]
      simp [initStat, hwu, hρu]
    by_cases hw : w < n + gs.length
    · let j := w - n
      have hj : j < gs.length := by omega
      have hwj : w = n + j := by omega
      have hdiff' : ∃ r ∈ (gs[j]).inputs, r < w ∧ mval gs x1 r ≠ mval gs x2 r := by
        by_contra hall
        push_neg at hall
        apply hdiff
        rw [hwj, mval_gate gs x1 j hj, mval_gate gs x2 j hj]
        congr 1
        apply List.map_congr_left
        intro r hr
        by_cases hrw : r < n + j
        · rw [ite_eq_left hrw, ite_eq_left hrw]
          exact hall r hr (by omega)
        · rw [ite_eq_right hrw, ite_eq_right hrw]
      obtain ⟨r, hrIn, hrlt, hrdiff⟩ := hdiff'
      by_cases hrb : (elimM n gs (initStat ρ, [])).1.getD r (Sum.inl false) = Sum.inl b
      · obtain ⟨hstat, hdrop⟩ := elimM_step_at gs ρ j hj
        have hpreLen : (elimM n (gs.take j) (initStat ρ, [])).1.length = n + j := by
          rw [elimM_len1]; simp [initStat, List.length_take_of_le hj.le]
        have hrPre : (elimM n (gs.take j) (initStat ρ, [])).1.getD r (Sum.inl false) = Sum.inl b := by
          have h1 : (elimM n gs (initStat ρ, [])).1.getD r (Sum.inl false) =
              (elimM n (gs.take j) (initStat ρ, [])).1.getD r (Sum.inl false) := by
            have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
            have hfold' : elimM n gs (initStat ρ, []) =
                elimM n (gs.drop j) (elimM n (gs.take j) (initStat ρ, [])) := by
              calc elimM n gs (initStat ρ, [])
                  = elimM n (gs.take j ++ gs.drop j) (initStat ρ, []) := by rw [← hsplit]
                _ = elimM n (gs.drop j) (elimM n (gs.take j) (initStat ρ, [])) := by
                    simp only [elimM, List.foldl_append]
            rw [hfold']
            exact elimM_getD_lt n (gs.drop j) (elimM n (gs.take j) (initStat ρ, [])) r (by omega)
          rw [← h1, hrb]
        have hmemB : Sum.inl b ∈ (gs[j]).inputs.map
            (fun i => (elimM n (gs.take j) (initStat ρ, [])).1.getD i (Sum.inl false)) :=
          List.mem_map.mpr ⟨r, hrIn, hrPre⟩
        have hgjOk : mOk (gs[j]) := hok _ (List.getElem_mem hj)
        have hnone := simpM_none_of_const (gs[j]).op hgjOk.1
          (n + (elimM n (gs.take j) (initStat ρ, [])).2.length) _
          (by simpa using hgjOk.2) b hmemB
        have hgop : (gs[j]).op = (if b then GateOp.and else GateOp.or) := by
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rcases hgjOk.1 with h | h
            · exfalso
              apply hne
              rw [hwj, hstat, h]
              exact simpM_and_false _ _ (by simpa using hgjOk.2) hmemB
            · exact h
          · simp only [↓reduceIte]
            rcases hgjOk.1 with h | h
            · exact h
            · exfalso
              apply hne
              rw [hwj, hstat, h]
              exact simpM_or_true _ _ (by simpa using hgjOk.2) hmemB
        rw [← hgop]
        exact hdrop hnone
      · exact ih r hrlt hrdiff hrb
    · exfalso
      apply hdiff
      rw [mval_oob gs x1 w (by omega), mval_oob gs x2 w (by omega)]

lemma elimM_circuit {n : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, mOk g)
    (ρ : Fin n → Option Bool) (hnotT : (elimM n C.gates (initStat ρ, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl true) :
    ∃ C' : Circuit, (∀ g ∈ C'.gates, mOk g) ∧
      C'.gates = (elimM n C.gates (initStat ρ, [])).2 ∧
      (∀ x : Fin n → Bool, mval C'.gates x C'.output = mval C.gates (applySubst ρ x) C.output) := by
  let res := elimM n C.gates (initStat ρ, [])
  by_cases hout : C.output < res.1.length
  · cases hst : res.1.getD C.output (Sum.inl false) with
    | inl b =>
      cases b
      · refine ⟨⟨res.2, n + res.2.length⟩, elimM_ok n C.gates _ (by simp), rfl, ?_⟩
        intro x
        have hs := elimM_sound_init C.gates hok ρ x C.output hout
        change msVal _ (res.1.getD C.output (Sum.inl false)) = _ at hs
        rw [hst] at hs
        rw [mval_oob _ x _ (le_refl _), ← hs]
        rfl
      · exact False.elim (hnotT hst)
    | inr j =>
      refine ⟨⟨res.2, j⟩, elimM_ok n C.gates _ (by simp), rfl, ?_⟩
      intro x
      have hs := elimM_sound_init C.gates hok ρ x C.output hout
      change msVal _ (res.1.getD C.output (Sum.inl false)) = _ at hs
      rw [hst] at hs
      exact hs
  · refine ⟨⟨res.2, n + res.2.length⟩, elimM_ok n C.gates _ (by simp), rfl, ?_⟩
    intro x
    have hlen : res.1.length = n + C.gates.length := by
      dsimp only [res]; rw [elimM_len1]; simp [initStat]
    rw [mval_oob _ x _ (le_refl _), mval_oob C.gates _ C.output (by omega)]

def graphF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (x : Fin n → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

lemma and_lower {n : ℕ} : ∀ (e : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (t : ℕ) (C : Circuit),
    G.edgeFinset.card = e →
    G.IsAcyclic →
    (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
    (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) →
    (∀ g ∈ C.gates, mOk g) →
    (∀ x : Fin n → Bool, mval C.gates x C.output = graphF G A x) →
    t ≤ countOp GateOp.and C.gates := by
  intro e
  induction e using Nat.strong_induction_on with
  | ind e ih =>
    intro G dec A t C he hAcyc hIso hMin hok hfun
    by_cases hEdge : ∃ u v : Fin n, G.Adj u v
    · obtain ⟨l, p, hlp, hleaf, -⟩ := PEqualNP.MetaComplexity.Aa.Ak.gM G hAcyc hEdge
      have hlNotA : l ∉ A := fun h => hIso l h p hlp
      let ρ : Fin n → Option Bool := fun i =>
        if i = l then some true else if i = p then some false else none
      have hρl : ρ l = some true := by simp [ρ]
      have hnotT : (elimM n C.gates (initStat ρ, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl true := by
        intro hT
        by_cases hout : C.output < (elimM n C.gates (initStat ρ, [])).1.length
        · have hv := elimM_sound_init C.gates hok ρ (fun _ => false) C.output hout
          rw [hT] at hv
          have hf := hfun (applySubst ρ (fun _ => false))
          have heq : mval C.gates (applySubst ρ (fun _ => false)) C.output = true := hv.symm
          rw [hf] at heq
          simp only [graphF, decide_eq_true_eq] at heq
          rcases heq with ⟨a, ha, hxa⟩ | ⟨u, v, huv, hxu, hxv⟩
          · have hal : a = l := by
              by_contra h
              simp [applySubst, ρ, h] at hxa
              split_ifs at hxa <;> simp at hxa
            exact hlNotA (hal ▸ ha)
          · have hul : u = l := by
              by_contra h
              simp [applySubst, ρ, h] at hxu
              split_ifs at hxu <;> simp at hxu
            have hvl : v = l := by
              by_contra h
              simp [applySubst, ρ, h] at hxv
              split_ifs at hxv <;> simp at hxv
            exact huv.ne (hul.trans hvl.symm)
        · rw [List.getD_eq_default _ _ (by omega)] at hT
          cases hT
      let x1 : Fin n → Bool := fun i => decide (i = p)
      let x2 : Fin n → Bool := fun i => decide (i = p ∨ i = l)
      have hdiff : mval C.gates x1 C.output ≠ mval C.gates x2 C.output := by
        rw [hfun x1, hfun x2]
        have h1 : graphF G A x1 = false := by
          simp only [graphF, decide_eq_false_iff_not, not_or, not_exists, not_and]
          refine ⟨fun a ha hxa => ?_, fun u v huv hxu hxv => ?_⟩
          · have : a = p := of_decide_eq_true hxa
            exact hIso a ha l (this ▸ hlp.symm)
          · have hu : u = p := of_decide_eq_true hxu
            have hv : v = p := of_decide_eq_true hxv
            exact huv.ne (hu.trans hv.symm)
        have h2 : graphF G A x2 = true := by
          simp only [graphF, decide_eq_true_eq]
          exact Or.inr ⟨l, p, hlp, by simp [x2], by simp [x2]⟩
        rw [h1, h2]; decide
      have hdrop := path_elim_const C.gates hok ρ true l hρl x1 x2
        (fun v hv => by simp [x1, x2, hv]) C.output hdiff hnotT
      simp only [↓reduceIte] at hdrop
      obtain ⟨C', hok', hgates', hfun'⟩ := elimM_circuit C hok ρ hnotT
      let G' : SimpleGraph (Fin n) := G.deleteIncidenceSet p
      haveI : DecidableRel G'.Adj := Classical.decRel _
      have hAcyc' : G'.IsAcyclic := hAcyc.anti (SimpleGraph.deleteIncidenceSet_le G p)
      have hIso' : ∀ a ∈ A, ∀ v : Fin n, ¬ G'.Adj a v :=
        fun a ha v hv => hIso a ha v (SimpleGraph.deleteIncidenceSet_le G p hv)
      have hltE : G'.edgeFinset.card < e := by
        rw [← he]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨s(l, p), SimpleGraph.mem_edgeFinset.mpr hlp, ?_⟩
          intro hm
          have := (SimpleGraph.deleteIncidenceSet_adj.mp (SimpleGraph.mem_edgeFinset.mp hm)).2.2
          exact this rfl
        · intro x hx
          exact SimpleGraph.mem_edgeFinset.mpr
            (SimpleGraph.edgeSet_mono (SimpleGraph.deleteIncidenceSet_le G p)
              (SimpleGraph.mem_edgeFinset.mp hx))
      have hMin' : ∀ S' : Finset (Fin n), CoverPromise.IsVertexCover G' S' → t - 1 ≤ S'.card := by
        intro S' hS'
        have hcov : CoverPromise.IsVertexCover G (insert p S') := by
          intro u v huv
          by_cases hu : u = p
          · exact Or.inl (hu ▸ Finset.mem_insert_self p S')
          by_cases hv : v = p
          · exact Or.inr (hv ▸ Finset.mem_insert_self p S')
          have huv' : G'.Adj u v := SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huv, hu, hv⟩
          rcases hS' u v huv' with h | h
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr (Finset.mem_insert_of_mem h)
        have h1 := hMin (insert p S') hcov
        have h2 := Finset.card_insert_le p S'
        omega
      have hfunG' : ∀ x : Fin n → Bool, mval C'.gates x C'.output = graphF G' A x := by
        intro x
        rw [hfun' x, hfun (applySubst ρ x), Bool.eq_iff_iff]
        simp only [graphF, decide_eq_true_eq]
        constructor
        · rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hxu, hxv⟩)
          · left
            have hal : a ≠ l := fun h => hlNotA (h ▸ ha)
            have hap : a ≠ p := fun h => hIso a ha l (h ▸ hlp.symm)
            exact ⟨a, ha, by simpa [applySubst, ρ, hal, hap] using hxa⟩
          · right
            have hup : u ≠ p := by
              intro h; subst h
              simp [applySubst, ρ, hlp.ne.symm] at hxu
            have hvp : v ≠ p := by
              intro h; subst h
              simp [applySubst, ρ, hlp.ne.symm] at hxv
            have hul : u ≠ l := fun h => hvp (hleaf v (h ▸ huv))
            have hvl : v ≠ l := fun h => hup (hleaf u (h ▸ huv.symm))
            refine ⟨u, v, SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huv, hup, hvp⟩,
              by simpa [applySubst, ρ, hul, hup] using hxu,
              by simpa [applySubst, ρ, hvl, hvp] using hxv⟩
        · rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv', hxu, hxv⟩)
          · left
            have hal : a ≠ l := fun h => hlNotA (h ▸ ha)
            have hap : a ≠ p := fun h => hIso a ha l (h ▸ hlp.symm)
            exact ⟨a, ha, by simpa [applySubst, ρ, hal, hap] using hxa⟩
          · right
            obtain ⟨huv, hup, hvp⟩ := SimpleGraph.deleteIncidenceSet_adj.mp huv'
            have hul : u ≠ l := fun h => hvp (hleaf v (h ▸ huv))
            have hvl : v ≠ l := fun h => hup (hleaf u (h ▸ huv.symm))
            exact ⟨u, v, huv, by simpa [applySubst, ρ, hul, hup] using hxu,
              by simpa [applySubst, ρ, hvl, hvp] using hxv⟩
      have hih := ih G'.edgeFinset.card hltE G' A (t - 1) C' rfl hAcyc' hIso' hMin' hok' hfunG'
      rw [hgates'] at hih
      omega
    · have ht0 : t ≤ 0 := by
        simpa using hMin ∅ (fun u v huv => False.elim (hEdge ⟨u, v, huv⟩))
      omega

lemma or_lower {n : ℕ} : ∀ (m : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit),
    A.card + G.edgeFinset.card = m →
    G.IsAcyclic →
    (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
    (∀ g ∈ C.gates, mOk g) →
    (∀ x : Fin n → Bool, mval C.gates x C.output = graphF G A x) →
    A.card + G.edgeFinset.card ≤ countOp GateOp.or C.gates + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro G dec A C hm hAcyc hIso hok hfun
    by_cases hm1 : m ≤ 1
    · omega
    have hge2 : 2 ≤ A.card + G.edgeFinset.card := by omega
    have hstep : ∀ (u : Fin n) (G' : SimpleGraph (Fin n)) [DecidableRel G'.Adj] (A' : Finset (Fin n)),
        G'.IsAcyclic →
        (∀ a ∈ A', ∀ v : Fin n, ¬ G'.Adj a v) →
        A'.card + G'.edgeFinset.card + 1 = A.card + G.edgeFinset.card →
        (∃ x1 x2 : Fin n → Bool, (∀ v ≠ u, x1 v = x2 v) ∧ graphF G A x1 ≠ graphF G A x2) →
        (∀ x : Fin n → Bool, graphF G A (Function.update x u false) = graphF G' A' x) →
        A.card + G.edgeFinset.card ≤ countOp GateOp.or C.gates + 1 := by
      intro u G' dec' A' hAcyc' hIso' hcard' ⟨x1, x2, hag, hdiffF⟩ hrestr
      let ρ : Fin n → Option Bool := fun i => if i = u then some false else none
      have hρu : ρ u = some false := by simp [ρ]
      have hsub : ∀ x : Fin n → Bool, applySubst ρ x = Function.update x u false := by
        intro x; funext i
        by_cases hi : i = u <;> simp [applySubst, ρ, Function.update, hi]
      have hnotF : (elimM n C.gates (initStat ρ, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl false := by
        intro hF
        have hne' : A'.Nonempty ∨ ∃ a b : Fin n, G'.Adj a b := by
          by_cases hA' : A'.Nonempty
          · exact Or.inl hA'
          · rw [Finset.not_nonempty_iff_eq_empty] at hA'
            have hEpos : 0 < G'.edgeFinset.card := by rw [hA', Finset.card_empty] at hcard'; omega
            obtain ⟨e, he⟩ := Finset.card_pos.mp hEpos
            induction e using Sym2.ind with
            | _ a b => exact Or.inr ⟨a, b, SimpleGraph.mem_edgeFinset.mp he⟩
        obtain ⟨x0, hx0⟩ : ∃ x0 : Fin n → Bool, graphF G' A' x0 = true := by
          rcases hne' with ⟨a, ha⟩ | ⟨a, b, hab⟩
          · exact ⟨fun _ => true, by simp [graphF]; exact Or.inl ⟨a, ha⟩⟩
          · exact ⟨fun _ => true, by simp [graphF]; exact Or.inr ⟨a, b, hab⟩⟩
        by_cases hout : C.output < (elimM n C.gates (initStat ρ, [])).1.length
        · have hv := elimM_sound_init C.gates hok ρ x0 C.output hout
          rw [hF] at hv
          have hf := hfun (applySubst ρ x0)
          rw [hsub, hrestr, hx0] at hf
          change false = mval C.gates (applySubst ρ x0) C.output at hv
          rw [hsub, hf] at hv; cases hv
        · have hlen : (elimM n C.gates (initStat ρ, [])).1.length = n + C.gates.length := by
            rw [elimM_len1]; simp [initStat]
          have hf := hfun (applySubst ρ x0)
          rw [hsub, hrestr, hx0, mval_oob C.gates _ C.output (by omega)] at hf
          cases hf
      have hnotT : (elimM n C.gates (initStat ρ, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl true := by
        intro hT
        by_cases hout : C.output < (elimM n C.gates (initStat ρ, [])).1.length
        · have hv := elimM_sound_init C.gates hok ρ (fun _ => false) C.output hout
          rw [hT] at hv
          have hf := hfun (applySubst ρ (fun _ => false))
          rw [hsub, hrestr] at hf
          have h0 : graphF G' A' (fun _ => false) = false := by simp [graphF]
          rw [h0] at hf
          change true = mval C.gates (applySubst ρ (fun _ => false)) C.output at hv
          rw [hsub, hf] at hv; cases hv
        · rw [List.getD_eq_default _ _ (by omega)] at hT; cases hT
      have hdiff : mval C.gates x1 C.output ≠ mval C.gates x2 C.output := by
        rw [hfun x1, hfun x2]; exact hdiffF
      have hdrop := path_elim_const C.gates hok ρ false u hρu x1 x2 hag C.output hdiff hnotF
      simp only [Bool.false_eq_true, ↓reduceIte] at hdrop
      obtain ⟨C', hok', hgates', hfun'⟩ := elimM_circuit C hok ρ hnotT
      have hfunC' : ∀ x : Fin n → Bool, mval C'.gates x C'.output = graphF G' A' x := by
        intro x; rw [hfun' x, hfun (applySubst ρ x), hsub, hrestr]
      have hih := ih (A'.card + G'.edgeFinset.card) (by omega) G' A' C' rfl hAcyc' hIso' hok' hfunC'
      rw [hgates'] at hih
      omega
    by_cases hA : A.Nonempty
    · obtain ⟨a, ha⟩ := hA
      apply hstep a G (A.erase a) hAcyc (fun b hb v => hIso b (Finset.mem_of_mem_erase hb) v)
        (by have := Finset.card_erase_add_one ha; omega)
      · refine ⟨fun _ => false, fun i => decide (i = a), fun v hv => by simp [hv], ?_⟩
        have h1 : graphF G A (fun _ => false) = false := by simp [graphF]
        have h2 : graphF G A (fun i => decide (i = a)) = true := by
          simp only [graphF, decide_eq_true_eq]
          exact Or.inl ⟨a, ha, by simp⟩
        rw [h1, h2]; decide
      · intro x
        rw [Bool.eq_iff_iff]
        simp only [graphF, decide_eq_true_eq]
        constructor
        · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
          · by_cases hba : b = a
            · subst hba; simp [Function.update] at hxb
            · exact Or.inl ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, by simpa [Function.update, hba] using hxb⟩
          · have hua : u ≠ a := fun h => hIso a ha v (h ▸ huv)
            have hva : v ≠ a := fun h => hIso a ha u (h ▸ huv.symm)
            exact Or.inr ⟨u, v, huv, by simpa [Function.update, hua] using hxu,
              by simpa [Function.update, hva] using hxv⟩
        · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
          · obtain ⟨hba, hbA⟩ := Finset.mem_erase.mp hb
            exact Or.inl ⟨b, hbA, by simpa [Function.update, hba] using hxb⟩
          · have hua : u ≠ a := fun h => hIso a ha v (h ▸ huv)
            have hva : v ≠ a := fun h => hIso a ha u (h ▸ huv.symm)
            exact Or.inr ⟨u, v, huv, by simpa [Function.update, hua] using hxu,
              by simpa [Function.update, hva] using hxv⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      have hEdge : ∃ u v : Fin n, G.Adj u v := by
        have hpos : 0 < G.edgeFinset.card := by rw [hA, Finset.card_empty] at hge2; omega
        obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
        induction e using Sym2.ind with
        | _ u v => exact ⟨u, v, SimpleGraph.mem_edgeFinset.mp he⟩
      obtain ⟨l, p, hlp, hleaf, -⟩ := PEqualNP.MetaComplexity.Aa.Ak.gM G hAcyc hEdge
      let G' : SimpleGraph (Fin n) := G.deleteEdges {s(l, p)}
      have : DecidableRel G'.Adj := Classical.decRel _
      have hcardE : G'.edgeFinset.card + 1 = G.edgeFinset.card := by
        have hset : G'.edgeFinset = G.edgeFinset.erase s(l, p) := by
          ext e
          induction e using Sym2.ind with
          | _ u v =>
            simp only [G', SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeSet,
              SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
            exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, h2⟩⟩
        rw [hset]
        exact Finset.card_erase_add_one (SimpleGraph.mem_edgeFinset.mpr hlp)
      apply hstep l G' A (hAcyc.anti (SimpleGraph.deleteEdges_le _))
        (fun a ha v hv => hIso a ha v (SimpleGraph.deleteEdges_le _ hv)) (by omega)
      · refine ⟨fun i => decide (i = p), fun i => decide (i = p ∨ i = l), fun v hv => by simp [hv], ?_⟩
        have h1 : graphF G A (fun i => decide (i = p)) = false := by
          simp only [graphF, hA, Finset.notMem_empty, false_and, exists_false, false_or,
            decide_eq_false_iff_not, not_exists, not_and]
          intro u v huv hu hv
          exact huv.ne ((of_decide_eq_true hu).trans (of_decide_eq_true hv).symm)
        have h2 : graphF G A (fun i => decide (i = p ∨ i = l)) = true := by
          simp only [graphF, decide_eq_true_eq]
          exact Or.inr ⟨l, p, hlp, by simp, by simp⟩
        rw [h1, h2]; decide
      · intro x
        rw [Bool.eq_iff_iff]
        simp only [graphF, hA, Finset.notMem_empty, false_and, exists_false, false_or,
          decide_eq_true_eq]
        constructor
        · rintro ⟨u, v, huv, hxu, hxv⟩
          have hul : u ≠ l := by intro h; subst h; simp [Function.update] at hxu
          have hvl : v ≠ l := by intro h; subst h; simp [Function.update] at hxv
          refine ⟨u, v, SimpleGraph.deleteEdges_adj.mpr ⟨huv, ?_⟩,
            by simpa [Function.update, hul] using hxu,
            by simpa [Function.update, hvl] using hxv⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or]
          exact ⟨fun h => hul h.1, fun h => hvl h.2⟩
        · rintro ⟨u, v, huv', hxu, hxv⟩
          obtain ⟨huv, hne⟩ := SimpleGraph.deleteEdges_adj.mp huv'
          have hul : u ≠ l := by
            intro h; subst h
            have hvp : v = p := hleaf v huv
            subst hvp; exact hne rfl
          have hvl : v ≠ l := by
            intro h; subst h
            have hup : u = p := hleaf u huv.symm
            subst hup; exact hne Sym2.eq_swap
          exact ⟨u, v, huv, by simpa [Function.update, hul] using hxu,
            by simpa [Function.update, hvl] using hxv⟩

lemma countOp_eq_ncard (op : GateOp) (gs : List Gate) :
    Set.ncard {j : Fin gs.length | (gs.get j).op = op} = countOp op gs := by
  classical
  have h1 : {j : Fin gs.length | (gs.get j).op = op} =
      ((Finset.univ.filter fun j : Fin gs.length => (gs.get j).op = op) : Set (Fin gs.length)) := by
    ext j; simp
  rw [h1, Set.ncard_coe_finset]
  clear h1
  unfold countOp
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.countP_cons, ← ih]
    have hlen : (Finset.univ.filter fun j : Fin (g :: gs).length => ((g :: gs).get j).op = op).card =
        (Finset.univ.filter fun j : Fin (gs.length + 1) =>
          ((g :: gs)[j.val]'(by simpa using j.isLt)).op = op).card := rfl
    rw [hlen, Finset.card_filter, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ, ← Finset.card_filter]
    have htail : (Finset.univ.filter fun j : Fin gs.length => (gs[j.val]'j.isLt).op = op).card =
        (Finset.univ.filter fun j : Fin gs.length => (gs.get j).op = op).card := rfl
    rw [htail]
    by_cases h : g.op = op <;> simp [h, Nat.add_comm]

lemma main_287 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), G.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ Set.ncard {j : Fin C.gates.length | (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and} = t ∧ Set.ncard {j : Fin C.gates.length | (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or} + 1 = A.card + G.edgeFinset.card := by
  classical
  intro n t G dec A C hAcyc hIso hNe ⟨S, hScov, hScard⟩ hMin hCmin hCfun
  obtain ⟨C0, hC0fan, hC0sz, hC0fun⟩ := cover_upper G A S hNe hScov hScard hMin
  have hleSize : C.size ≤ C0.size := hCmin.2 C0 hC0fan (hC0fun.trans hCfun.symm)
  have hbuild := Ap.pE n C hCmin.1
  rw [hCfun] at hbuild
  have hlb := As.eV n t (Ap.eJ C) G A hAcyc hIso hNe
    (fun S' hS' => hMin S' (fun u v huv => hS' huv)) hbuild
  have hsplit := Ap.fH C
  have hNotZero : C.gates.countP Ap.iI = 0 := by omega
  have hnoNot : ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
    intro g hg hop
    have hpos : 0 < C.gates.countP Ap.iI := List.countP_pos_iff.mpr ⟨g, hg, by simp [Ap.iI, hop]⟩
    omega
  have hmok : ∀ g ∈ C.gates, mOk g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hCmin.1 g hg
    refine ⟨?_, hlen⟩
    have hnn := hnoNot g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnn h)
  have hpart : countOp GateOp.and C.gates + countOp GateOp.or C.gates = C.gates.length := by
    unfold countOp
    have heq : C.gates.countP (fun g => open Classical in decide (g.op = GateOp.or)) =
        C.gates.countP (fun g => open Classical in decide (¬ decide (g.op = GateOp.and) = true)) :=
      List.countP_congr (fun g hg => by rcases (hmok g hg).1 with h | h <;> simp [h])
    rw [heq]
    exact (List.length_eq_countP_add_countP (fun g => open Classical in decide (g.op = GateOp.and)) (l := C.gates)).symm
  have hfunC : ∀ x : Fin n → Bool, mval C.gates x C.output = graphF G A x := by
    intro x
    exact congrFun hCfun x
  have hAndLb : t ≤ countOp GateOp.and C.gates :=
    and_lower G.edgeFinset.card G A t C rfl hAcyc hIso hMin hmok hfunC
  have hOrLb : A.card + G.edgeFinset.card ≤ countOp GateOp.or C.gates + 1 :=
    or_lower (A.card + G.edgeFinset.card) G A C rfl hAcyc hIso hmok hfunC
  have hCszEq : C.gates.length + 1 = A.card + G.edgeFinset.card + t := by
    change C.size + 1 = _
    omega
  refine ⟨hnoNot, ?_, ?_⟩
  · rw [countOp_eq_ncard]; omega
  · rw [countOp_eq_ncard]; omega

end L287_proof

end PEqualNP.Outside.L_meta_287_aux

theorem PEqualNP.Outside.L_meta_287 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), G.IsAcyclic → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.IsMinimalCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ Set.ncard {j : Fin C.gates.length | (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and} = t ∧ Set.ncard {j : Fin C.gates.length | (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or} + 1 = A.card + G.edgeFinset.card :=
  PEqualNP.Outside.L_meta_287_aux.L287_proof.main_287
