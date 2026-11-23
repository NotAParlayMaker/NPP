import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_540_aux
namespace L540.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wF (gs: List Gate) (w: List Bool): List Bool :=
 gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem wires_eq (C: Circuit) (x: List Bool): C.wires x=wF C.gates x := rfl
theorem wiresFrom_append (gs gs' : List Gate) (w: List Bool) :
  wF (gs ++ gs') w=wF gs' (wF gs w):=by
 simp[wF,List.foldl_append]
theorem wiresFrom_prefix (gs: List Gate): ∀ w: List Bool,
  ∃ t: List Bool,wF gs w=w ++ t∧t.length=gs.length:=by
 induction gs with
 | nil => intro w;exact ⟨[],by simp[wF],rfl⟩
 | cons g gs ih =>
  intro w
  obtain ⟨t,ht,hl⟩:=ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
  refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,?_,by simp[hl]⟩
  have: wF (g :: gs) w
    = wF gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
  rw[this,ht];simp
theorem length_wiresFrom (gs: List Gate) (w: List Bool) :
  (wF gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=wiresFrom_prefix gs w;rw[ht];simp[hl]
theorem getD_wiresFrom (gs: List Gate) (w: List Bool) (i: ℕ) (h: i < w.length) :
  (wF gs w).getD i false=w.getD i false:=by
 obtain ⟨t,ht,_⟩:=wiresFrom_prefix gs w;rw[ht,List.getD_append _ _ _ _ h]
theorem final_gates (v: List Bool) (k o0 o1: ℕ) (hk: k < v.length) (h0: o0 < v.length)
  (h1: o1 < v.length) :
  (wF [⟨GateOp.not,[k]⟩,⟨GateOp.and,[v.length,o0]⟩,⟨GateOp.and,[k,o1]⟩,
   ⟨GateOp.or,[v.length+1,v.length+2]⟩] v).getD (v.length+3) false
   = ((!(v.getD k false)&&v.getD o0 false)||(v.getD k false&&v.getD o1 false)) := by
 have A: ∀ (t: List Bool) (i: ℕ),i < v.length→(v ++ t)[i]?.getD false=v[i]?.getD false:=by
  intro t i h;rw[List.getElem?_append_left h]
 simp[wF,GateOp.eval,A _ _ hk,A _ _ h0,A _ _ h1]
def Ok (g: Gate): Prop :=
 g.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp)∧g.inputs.length ≤ 2
theorem shannon (k: ℕ): ∀ (f: (Fin k→Bool)→Bool) (m: ℕ),k ≤ m →
  ∃ (gs: List Gate) (out: ℕ),(∀ g∈gs,Ok g)∧gs.length+4 ≤ 5 * 2 ^ k ∧
   out < m+gs.length ∧
   ∀ w: List Bool,w.length=m →
    (wF gs w).getD out false=f (fun i: Fin k => w.getD i false):=by
 induction k with
 | zero =>
  intro f m _
  refine ⟨[⟨if f (fun i => i.elim0)=true then GateOp.and else GateOp.or,[]⟩],m,?_,by simp,
   by simp,?_⟩
  ·intro g hg;simp only[List.mem_singleton] at hg;subst hg
   refine ⟨?_,by simp⟩
   by_cases h: f (fun i => i.elim0)=true <;> simp[h]
  ·intro w hw
   have hf: (fun i: Fin 0 => w.getD i false)=(fun i => i.elim0):=Subsingleton.elim _ _
   rw[hf]
   by_cases h: f (fun i => i.elim0)=true <;>
    simp[wF,h,←hw,GateOp.eval]
 | succ k ih =>
  intro f m hm
  obtain ⟨gs0,o0,ok0,len0,ho0,ev0⟩ :=
   ih (fun y => f (Fin.snoc y false)) m (by omega)
  obtain ⟨gs1,o1,ok1,len1,ho1,ev1⟩ :=
   ih (fun y => f (Fin.snoc y true)) (m+gs0.length) (by omega)
  let M:=m+gs0.length+gs1.length
  refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not,[k]⟩,⟨GateOp.and,[M,o0]⟩,⟨GateOp.and,[k,o1]⟩,
   ⟨GateOp.or,[M+1,M+2]⟩],M+3,?_,?_,?_,?_⟩
  ·intro g hg;simp only[List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
   rcases hg with (hg|hg)|hg|hg|hg|hg
   ·exact ok0 g hg
   ·exact ok1 g hg
   all_goals (subst hg;simp[Ok])
  ·simp only[List.length_append,List.length_cons,List.length_nil];rw[pow_succ];omega
  ·simp only[List.length_append,List.length_cons,List.length_nil];omega
  ·intro w hw;rw[wiresFrom_append,wiresFrom_append];set w1:=wF gs0 w with hw1;set w2:=wF gs1 w1 with hw2
   have l1: w1.length=m+gs0.length:=by rw[hw1,length_wiresFrom,hw]
   have l2: w2.length=M:=by rw[hw2,length_wiresFrom,l1]
   have e0: w2.getD o0 false=f (Fin.snoc (fun i: Fin k => w.getD i false) false):=by
    rw[hw2,getD_wiresFrom _ _ _ (by omega)];exact ev0 w hw
   have e1: w2.getD o1 false=f (Fin.snoc (fun i: Fin k => w.getD i false) true):=by
    rw[ev1 w1 l1]
    congr 2;funext i
    exact getD_wiresFrom _ _ _ (by have := i.isLt;omega)
   have ek: w2.getD k false=w.getD k false:=by
    rw[hw2,getD_wiresFrom _ _ _ (by omega),hw1,getD_wiresFrom _ _ _ (by omega)]
   have hx: (fun i: Fin (k+1) => w.getD i false)
     = Fin.snoc (fun i: Fin k => w.getD i false) (w.getD k false) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
   rw[hx]
   have hk2: k < w2.length:=by omega
   have h02: o0 < w2.length:=by omega
   have h12: o1 < w2.length:=by omega
   rw[show M=w2.length from l2.symm,final_gates w2 k o0 o1 hk2 h02 h12,ek,e0,e1]
   cases w.getD k false <;> simp
end L540.Helpers
namespace L540.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n : ℕ}
theorem getD_snoc_ne {α : Type} (L: List α) (S d: α) (j: ℕ) (h: j≠L.length) :
  (L ++ [S]).getD j d=L.getD j d:=by
 by_cases hj: j < L.length
 ·exact List.getD_append _ _ _ _ hj
 ·rw[List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L: List α) (S d: α): (L ++ [S]).getD L.length d=S:=by
 simp
end L540.Helpers
namespace L540.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def NOk (g: Gate): Prop := Ok g∧(g.op=GateOp.not → g.inputs.length ≤ 1)
inductive Stat: Type
 | const (c: Bool)
 | wire (j: ℕ)
def Stat.val (w: List Bool): Stat→Bool
 | Stat.const c => c
 | Stat.wire j => w.getD j false
def Stat.Valid (m: ℕ): Stat→Prop
 | Stat.const _ => True
 | Stat.wire j => j < m
def sN0 (m: ℕ): List Stat→Option Gate × Stat
 | [] => (none,Stat.const true)
 | Stat.const c :: _ => (none,Stat.const (!c))
 | Stat.wire j :: _ => (some ⟨GateOp.not,[j]⟩,Stat.wire m)
def sA0 (m: ℕ): List Stat→Option Gate × Stat
 | [] => (none,Stat.const true)
 | [Stat.const c] => (none,Stat.const c)
 | [Stat.wire j] => (none,Stat.wire j)
 | [Stat.const c,Stat.const d] => (none,Stat.const (c&&d))
 | [Stat.const c,Stat.wire j] => (none,bif c then Stat.wire j else Stat.const false)
 | [Stat.wire j,Stat.const c] => (none,bif c then Stat.wire j else Stat.const false)
 | [Stat.wire j,Stat.wire k] => (some ⟨GateOp.and,[j,k]⟩,Stat.wire m)
 | _ => (none,Stat.const false)
def sO0 (m: ℕ): List Stat→Option Gate × Stat
 | [] => (none,Stat.const false)
 | [Stat.const c] => (none,Stat.const c)
 | [Stat.wire j] => (none,Stat.wire j)
 | [Stat.const c,Stat.const d] => (none,Stat.const (c||d))
 | [Stat.const c,Stat.wire j] => (none,bif c then Stat.const true else Stat.wire j)
 | [Stat.wire j,Stat.const c] => (none,bif c then Stat.const true else Stat.wire j)
 | [Stat.wire j,Stat.wire k] => (some ⟨GateOp.or,[j,k]⟩,Stat.wire m)
 | _ => (none,Stat.const false)
def smp (op: GateOp) (m: ℕ) (ins: List Stat): Option Gate × Stat :=
 match op with
 | GateOp.and => sA0 m ins
 | GateOp.or => sO0 m ins
 | GateOp.not => sN0 m ins
 | _ => (none,Stat.const false)
theorem smC (op: GateOp) (m: ℕ) (ins: List Stat)
  (hop: op=GateOp.and∨op=GateOp.or∨op=GateOp.not) (hlen: ins.length ≤ 2)
  (hnot: op=GateOp.not → ins.length ≤ 1) (hc: ∃ c,Stat.const c∈ins) :
  (smp op m ins).1=none:=by
 obtain ⟨c,hc⟩:=hc
 rcases hop with rfl|rfl|rfl
 ·rcases ins with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
   simp_all [smp,sA0]
 ·rcases ins with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
   simp_all [smp,sO0]
 ·have:=hnot rfl
  rcases ins with _|⟨a,_|⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [smp,sN0]
theorem smS (op: GateOp) (hop: op=GateOp.and∨op=GateOp.or∨op=GateOp.not)
  (w: List Bool) (ins: List Stat) (hlen: ins.length ≤ 2)
  (hv: ∀ s∈ins,s.Valid w.length) :
  ((smp op w.length ins).2).Valid (w.length+(smp op w.length ins).1.toList.length) ∧
  ((smp op w.length ins).2).val (wF (smp op w.length ins).1.toList w)
   = op.eval (ins.map (Stat.val w)) := by
 rcases hop with rfl|rfl|rfl
 ·rcases ins with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩
  ·simp[smp,sA0,Stat.Valid,Stat.val,GateOp.eval]
  ·cases a <;> simp_all [smp,sA0,Stat.Valid,Stat.val,GateOp.eval,wF]
  ·cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
    simp_all [smp,sA0,Stat.Valid,Stat.val,GateOp.eval,wF]
  ·simp at hlen
 ·rcases ins with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩
  ·simp[smp,sO0,Stat.Valid,Stat.val,GateOp.eval]
  ·cases a <;> simp_all [smp,sO0,Stat.Valid,Stat.val,GateOp.eval,wF]
  ·cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
    simp_all [smp,sO0,Stat.Valid,Stat.val,GateOp.eval,wF]
  ·simp at hlen
 ·rcases ins with _|⟨a,l⟩
  ·simp[smp,sN0,Stat.Valid,Stat.val,GateOp.eval]
  ·cases a <;> simp_all [smp,sN0,Stat.Valid,Stat.val,GateOp.eval,wF]
def eSt (n: ℕ) (acc: List Stat × List Gate) (g: Gate): List Stat × List Gate :=
 (acc.1 ++ [(smp g.op (n+acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
  acc.2 ++ (smp g.op (n+acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)
def elim (n: ℕ) (gs: List Gate) (acc: List Stat × List Gate): List Stat × List Gate :=
 gs.foldl (eSt n) acc
theorem getD_snoc_len {α : Type} (L: List α) (S d: α) (k: ℕ) (h: L.length=k) :
  (L ++ [S]).getD k d=S:=by
 subst h;simp
theorem elim_getD (n k: ℕ) (d: Stat) (gs: List Gate): ∀ acc: List Stat × List Gate,
  k < acc.1.length→(elim n gs acc).1.getD k d=acc.1.getD k d:=by
 induction gs with
 | nil => intro acc _;rfl
 | cons g gs ih =>
  intro acc hk;have h3: elim n (g :: gs) acc=elim n gs (eSt n acc g):=rfl;rw[h3,ih (eSt n acc g) (by simp[eSt];omega)];exact getD_snoc_ne _ _ _ _ (by omega)
theorem toList_length_le {α : Type} (o: Option α): o.toList.length ≤ 1:=by
 cases o <;> simp
theorem elim_len (n: ℕ) (gs: List Gate): ∀ acc: List Stat × List Gate,
  (elim n gs acc).2.length ≤ acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc;simp[elim]
 | cons g gs ih =>
  intro acc;have h1:=ih (eSt n acc g)
  have h2: (eSt n acc g).2.length ≤ acc.2.length+1:=by
   simp only[eSt,List.length_append]
   have:=toList_length_le (smp g.op (n+acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
   omega
  have h3: elim n (g :: gs) acc=elim n gs (eSt n acc g):=rfl;rw[h3,List.length_cons];omega
theorem Stat.valid_mono {m m' : ℕ} (h: m ≤ m'): ∀ s: Stat,s.Valid m → s.Valid m'
 | Stat.const _,_ => trivial
 | Stat.wire _,hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t: List Bool): ∀ s: Stat,s.Valid w.length →
  s.val (w ++ t)=s.val w
 | Stat.const _,_ => rfl
 | Stat.wire _,hj => List.getD_append _ _ _ _ hj
def Inv (n: ℕ) (y: List Bool) (w: List Bool) (acc: List Stat × List Gate): Prop :=
 acc.1.length=w.length ∧ ∀ i: ℕ,
  (acc.1.getD i (Stat.const false)).Valid (n+acc.2.length) ∧
  (acc.1.getD i (Stat.const false)).val (wF acc.2 y)=w.getD i false
theorem inv_elim (n: ℕ) (y: List Bool) (hy: y.length=n) (gs: List Gate) :
  ∀ (w: List Bool) (acc: List Stat × List Gate),(∀ g∈gs,Ok g)→Inv n y w acc →
   Inv n y (wF gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ h;exact h
 | cons g gs ih =>
  intro w acc hok h
  apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (eSt n acc g)
   (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
  obtain ⟨hl,hi⟩:=h;set w' := wF acc.2 y with hw'
  have lw' : w'.length=n+acc.2.length:=by rw[hw',length_wiresFrom,hy]
  set ins:=g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
  have hgok:=hok g List.mem_cons_self
  have hs:=smS g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
   (by
    intro s hs;obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
    rw[lw'];exact (hi a).1)
  rw[lw'] at hs;set r:=smp g.op (n+acc.2.length) ins with hr
  have hvals: ins.map (Stat.val w')=g.inputs.map fun i => w.getD i false:=by
   rw[hins,List.map_map];apply List.map_congr_left;intro a _;exact (hi a).2
  have hnew: wF (acc.2 ++ r.1.toList) y=wF r.1.toList w' := by
   rw[wiresFrom_append]
  obtain ⟨t,ht,htl⟩:=wiresFrom_prefix r.1.toList w'
  refine ⟨by simp[eSt,hl],?_⟩
  intro i
  show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n+(acc.2 ++ r.1.toList).length) ∧
   ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wF (acc.2 ++ r.1.toList) y)=_
  rw[hnew,List.length_append,←Nat.add_assoc]
  by_cases hil: i=acc.1.length
  ·subst hil;rw[getD_snoc_eq,hl,getD_snoc_eq];exact ⟨hs.1,by rw[hs.2,hvals]⟩
  ·rw[getD_snoc_ne _ _ _ _ hil,getD_snoc_ne _ _ _ _ (by omega)]
   refine ⟨Stat.valid_mono (by omega) _ (hi i).1,?_⟩
   rw[ht,Stat.val_append _ _ _ (by rw[lw'];exact (hi i).1)];exact (hi i).2
end L540.Helpers
namespace L540.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem elim_cons (n: ℕ) (g: Gate) (gs: List Gate) (acc: List Stat × List Gate) :
  elim n (g :: gs) acc=elim n gs (eSt n acc g) := rfl
theorem elim_append (n: ℕ) (pre post: List Gate) (acc: List Stat × List Gate) :
  elim n (pre ++ post) acc=elim n post (elim n pre acc):=by
 simp[elim,List.foldl_append]
theorem elim_fst_len (n: ℕ) (gs: List Gate): ∀ acc: List Stat × List Gate,
  (elim n gs acc).1.length=acc.1.length+gs.length:=by
 induction gs with
 | nil => intro acc;rfl
 | cons g gs ih =>
  intro acc;rw[elim_cons,ih];simp only[eSt,List.length_append,List.length_cons,List.length_nil];omega
theorem smK (op: GateOp) (m: ℕ) (ins: List Stat)
  (hop: op=GateOp.and∨op=GateOp.or∨op=GateOp.not) (hlen: ins.length ≤ 2)
  (hnot: op=GateOp.not → ins.length ≤ 1) (b: Bool)
  (hand: op=GateOp.and → b=false) (hor: op=GateOp.or → b=true)
  (hc: Stat.const b∈ins): ∃ c,(smp op m ins).2=Stat.const c:=by
 rcases hop with rfl|rfl|rfl
 ·have:=hand rfl
  subst this
  rcases ins with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
   simp_all [smp,sA0]
 ·have:=hor rfl
  subst this
  rcases ins with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
   simp_all [smp,sO0]
 ·have:=hnot rfl
  rcases ins with _|⟨a,_|⟨d,l⟩⟩ <;> (try cases a) <;> simp_all [smp,sN0]
theorem elimStep_none (n: ℕ) (acc: List Stat × List Gate) (g: Gate) (hg: NOk g) (k: ℕ)
  (hk: k∈g.inputs) (c: Bool) (hc: acc.1.getD k (Stat.const false)=Stat.const c) :
  (eSt n acc g).2.length=acc.2.length:=by
 have hnone: (smp g.op (n+acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1=none:=by
  apply smC
  ·exact hg.1.1
  ·simpa using hg.1.2
  ·intro h;simpa using hg.2 h
  ·exact ⟨c,List.mem_map.2 ⟨k,hk,hc⟩⟩
 show (acc.2 ++ (smp g.op (n+acc.2.length)
  (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length=_
 rw[hnone];simp
def fixBit (g: Gate): Bool :=
 match g.op with
 | GateOp.or => true
 | _ => false
theorem elimStep_const (n: ℕ) (acc: List Stat × List Gate) (g: Gate) (hg: NOk g) (k: ℕ)
  (hk: k∈g.inputs) (hc: acc.1.getD k (Stat.const false)=Stat.const (fixBit g)) :
  ∃ c,(eSt n acc g).1.getD acc.1.length (Stat.const false)=Stat.const c:=by
 have e: (eSt n acc g).1.getD acc.1.length (Stat.const false)
   = (smp g.op (n+acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
 rw[e]
 apply smK _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
  (fixBit g)
 ·intro h;simp[fixBit,h]
 ·intro h;simp[fixBit,h]
 ·exact List.mem_map.2 ⟨k,hk,hc⟩
end L540.Helpers
namespace L540.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def CG (m: ℕ) (g: Gate): Prop :=
 (g.op=GateOp.not ∧ ∃ j,j < m∧g.inputs=[j]) ∨
 ((g.op=GateOp.and∨g.op=GateOp.or) ∧ ∃ j k,j < m∧k < m∧g.inputs=[j,k])
def CL (m: ℕ) (gs: List Gate): Prop :=
 ∀ (p: ℕ) (g: Gate),gs[p]? = some g→CG (m+p) g
theorem CG.nok {m: ℕ} {g: Gate} (h: CG m g): NOk g:=by
 rcases h with ⟨h1,j,_,h2⟩ | ⟨h1|h1,j,k,_,_,h2⟩
 ·refine ⟨⟨?_,?_⟩,?_⟩
  ·rw[h1];exact Or.inr (Or.inr rfl)
  ·rw[h2];simp
  ·intro _;rw[h2];simp
 ·refine ⟨⟨?_,?_⟩,?_⟩
  ·rw[h1];exact Or.inl rfl
  ·rw[h2];simp
  ·intro h;rw[h1] at h;cases h
 ·refine ⟨⟨?_,?_⟩,?_⟩
  ·rw[h1];exact Or.inr (Or.inl rfl)
  ·rw[h2];simp
  ·intro h;rw[h1] at h;cases h
theorem CG.lt {m: ℕ} {g: Gate} (h: CG m g): ∀ a∈g.inputs,a < m:=by
 intro a ha
 rcases h with ⟨_,j,hj,h2⟩ | ⟨_,j,k,hj,hk,h2⟩
 ·rw[h2] at ha
  simp at ha
  subst ha;exact hj
 ·rw[h2] at ha
  simp at ha
  rcases ha with rfl|rfl
  ·exact hj
  ·exact hk
theorem clean_nok (m: ℕ) (gs: List Gate) (h: CL m gs): ∀ g∈gs,NOk g:=by
 intro g hg;obtain ⟨p,hp⟩:=List.mem_iff_getElem?.1 hg;exact (h p g hp).nok
theorem smL (op: GateOp) (m: ℕ) (ins: List Stat) (hv: ∀ s∈ins,s.Valid m) :
  ∀ g∈(smp op m ins).1,CG m g:=by
 intro g hg
 cases op <;> simp only[smp] at hg
 ·rcases ins with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
   simp[sA0] at hg
  subst hg
  refine Or.inr ⟨Or.inl rfl,_,_,?_,?_,rfl⟩
  ·exact hv _ List.mem_cons_self
  ·exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
 ·rcases ins with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
   simp[sO0] at hg
  subst hg
  refine Or.inr ⟨Or.inr rfl,_,_,?_,?_,rfl⟩
  ·exact hv _ List.mem_cons_self
  ·exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
 ·rcases ins with _|⟨a,l⟩ <;> (try cases a) <;> simp[sN0] at hg
  subst hg
  refine Or.inl ⟨rfl,_,?_,rfl⟩
  exact hv _ List.mem_cons_self
 ·simp at hg
 ·simp at hg
theorem toList_getElem? {α : Type} (o: Option α) (k: ℕ) (a: α)
  (h: o.toList[k]? = some a): k=0∧a∈o:=by
 cases o with
 | none => simp at h
 | some b =>
  cases k with
  | zero => simp at h;simp[h]
  | succ k => simp at h
theorem clean_elim (n: ℕ) (y: List Bool) (hy: y.length=n) (gs: List Gate) :
  ∀ (w: List Bool) (acc: List Stat × List Gate),(∀ g∈gs,Ok g)→Inv n y w acc →
   CL n acc.2→CL n (elim n gs acc).2:=by
 induction gs with
 | nil => intro w acc _ _ h;exact h
 | cons g gs ih =>
  intro w acc hok hinv hcl
  have hinv' : Inv n y (wF [g] w) (eSt n acc g) :=
   inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg';simp[hg'])) hinv
  refine ih _ (eSt n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
  intro p g' hp
  have hp' : (acc.2 ++ (smp g.op (n+acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
  by_cases hlt: p < acc.2.length
  ·rw[List.getElem?_append_left hlt] at hp';exact hcl p g' hp'
  ·rw[List.getElem?_append_right (by omega)] at hp';obtain ⟨h0,hmem⟩:=toList_getElem? _ _ _ hp'
   have hpl: p=acc.2.length:=by omega
   rw[hpl]
   exact smL _ _ _ (fun s hs => by
    obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
    exact (hinv.2 a).1) g' hmem
def idS (n: ℕ): List Stat := List.ofFn (fun i: Fin n => Stat.wire i)
theorem inv_id (n: ℕ) (y: Fin n→Bool) :
  Inv n (List.ofFn y) (List.ofFn y) (idS n,[]):=by
 refine ⟨by simp[idS],?_⟩
 intro i
 by_cases hlt: i < n
 ·simp[idS,hlt,Stat.Valid,Stat.val,wF]
 ·rw[List.getD_eq_default _ _ (by simp[idS];omega),
   List.getD_eq_default _ _ (by simp;omega)]
  exact ⟨trivial,rfl⟩
theorem getD_ofFn {α : Type} (m: ℕ) (F: Fin m → α) (d: α) (j: Fin m) :
  (List.ofFn F).getD j d=F j:=by
 simp
def stA (n: ℕ) (i: Fin (n+1)) (b: Bool): List Stat :=
 List.ofFn (Fin.insertNth i (Stat.const b) (fun k: Fin n => Stat.wire k): Fin (n+1)→Stat)
theorem statAt_length (n: ℕ) (i: Fin (n+1)) (b: Bool): (stA n i b).length=n+1:=by
 simp[stA]
theorem statAt_at (n: ℕ) (i: Fin (n+1)) (b: Bool) :
  (stA n i b).getD i (Stat.const false)=Stat.const b:=by
 rw[stA,getD_ofFn,Fin.insertNth_apply_same]
theorem statAt_above (n: ℕ) (i: Fin (n+1)) (b: Bool) (k: Fin n) :
  (stA n i b).getD (i.succAbove k) (Stat.const false)=Stat.wire k:=by
 rw[stA,getD_ofFn,Fin.insertNth_apply_succAbove]
theorem inv_at (n: ℕ) (i: Fin (n+1)) (b: Bool) (y: Fin n→Bool) :
  Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y: Fin (n+1)→Bool))
   (stA n i b,[]):=by
 refine ⟨by simp[stA],?_⟩
 have key: ∀ j: Fin (n+1),
   ((stA n i b).getD j (Stat.const false)).Valid (n+0) ∧
   ((stA n i b).getD j (Stat.const false)).val (List.ofFn y)
    = (List.ofFn (Fin.insertNth i b y: Fin (n+1)→Bool)).getD j false := by
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl|⟨k,rfl⟩
  ·rw[statAt_at,getD_ofFn,Fin.insertNth_apply_same];exact ⟨trivial,rfl⟩
  ·rw[statAt_above,getD_ofFn,Fin.insertNth_apply_succAbove]
   refine ⟨?_,?_⟩
   ·show (k: ℕ) < n+0
    have:=k.isLt
    omega
   ·show (List.ofFn y).getD k false=y k
    exact getD_ofFn n y false k
 intro j
 by_cases hlt: j < n+1
 ·exact key ⟨j,hlt⟩
 ·show ((stA n i b).getD j (Stat.const false)).Valid (n+0) ∧
   ((stA n i b).getD j (Stat.const false)).val (List.ofFn y)
    = (List.ofFn (Fin.insertNth i b y: Fin (n+1)→Bool)).getD j false
  rw[List.getD_eq_default _ _ (by rw[statAt_length];omega),
   List.getD_eq_default _ _ (by simp;omega)]
  exact ⟨trivial,rfl⟩
def stF (n: ℕ) (gs: List Gate) (i: Fin (n+1)) (b: Bool) (a: ℕ): Stat :=
 (elim n gs (stA n i b,[])).1.getD a (Stat.const false)
theorem stF_self (n: ℕ) (gs: List Gate) (i: Fin (n+1)) (b: Bool) :
  stF n gs i b i=Stat.const b:=by
 show (elim n gs (stA n i b,[])).1.getD i (Stat.const false)=_
 rw[elim_getD n i _ gs _ (by
  show (i: ℕ) < (stA n i b).length
  rw[statAt_length];exact i.isLt)]
 exact statAt_at n i b
theorem split_at {α : Type}: ∀ (l: List α) (p: ℕ) (g: α),l[p]? = some g →
  ∃ pre post,l=pre ++ g :: post∧pre.length=p:=by
 intro l
 induction l with
 | nil => intro p g h;simp at h
 | cons x l ih =>
  intro p g h
  cases p with
  | zero =>
   simp at h
   subst h;exact ⟨[],l,rfl,rfl⟩
  | succ p =>
   simp at h
   obtain ⟨pre,post,rfl,rfl⟩:=ih p g h;exact ⟨x :: pre,post,rfl,rfl⟩
theorem elim_split_getD (n: ℕ) (pre: List Gate) (g: Gate) (post: List Gate)
  (acc: List Stat × List Gate) (a: ℕ) (d: Stat) (h: a ≤ acc.1.length+pre.length) :
  (elim n (pre ++ g :: post) acc).1.getD a d=(eSt n (elim n pre acc) g).1.getD a d:=by
 rw[elim_append,elim_cons,elim_getD n a d post _ (by
  show a < ((elim n pre acc).1 ++ [_]).length
  rw[List.length_append,elim_fst_len,List.length_singleton];omega)]
theorem elim_split_getD_lt (n: ℕ) (pre: List Gate) (g: Gate) (post: List Gate)
  (acc: List Stat × List Gate) (a: ℕ) (d: Stat) (h: a < acc.1.length+pre.length) :
  (elim n (pre ++ g :: post) acc).1.getD a d=(elim n pre acc).1.getD a d:=by
 rw[elim_split_getD n pre g post acc a d (le_of_lt h)]
 show ((elim n pre acc).1 ++ [_]).getD a d=_
 exact getD_snoc_ne _ _ _ _ (by rw[elim_fst_len];omega)
theorem const_of_read (n: ℕ) (gs: List Gate) (acc: List Stat × List Gate) (p: ℕ) (g: Gate)
  (hp: gs[p]? = some g) (hg: NOk g) (a: ℕ) (ha: a∈g.inputs)
  (hlt: a < acc.1.length+p)
  (hc: (elim n gs acc).1.getD a (Stat.const false)=Stat.const (fixBit g)) :
  ∃ c,(elim n gs acc).1.getD (acc.1.length+p) (Stat.const false)=Stat.const c:=by
 obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp;rw[elim_split_getD_lt n pre g post acc a _ hlt] at hc;obtain ⟨c,hc'⟩:=elimStep_const n (elim n pre acc) g hg a ha hc
 refine ⟨c,?_⟩
 rw[elim_split_getD n pre g post acc _ _ (le_refl _)];rw[elim_fst_len] at hc';exact hc'
theorem elim_count (n: ℕ) (acc: List Stat × List Gate): ∀ gs: List Gate,
  (∀ g∈gs,NOk g)→∀ S: Finset ℕ,
  (∀ p∈S,∃ g,gs[p]? = some g ∧ ∃ a∈g.inputs,a < acc.1.length+p ∧
    ∃ c,(elim n gs acc).1.getD a (Stat.const false)=Stat.const c) →
   (elim n gs acc).2.length+S.card ≤ acc.2.length+gs.length:=by
 intro gs
 induction gs using List.reverseRecOn with
 | nil =>
  intro _ S hS
  have hE: S = ∅ := by
   apply Finset.eq_empty_of_forall_notMem;intro p hp;obtain ⟨g,hg,_⟩:=hS p hp
   simp at hg
  subst hE;simp[elim]
 | append_singleton gs g ih =>
  intro hok S hS
  have hstep: elim n (gs ++ [g]) acc=eSt n (elim n gs acc) g:=by
   rw[elim_append];rfl
  have hpre: ∀ (a: ℕ) (d: Stat),a < acc.1.length+gs.length →
    (elim n (gs ++ [g]) acc).1.getD a d=(elim n gs acc).1.getD a d :=
   fun a d h => elim_split_getD_lt n gs g [] acc a d h
  have hok' : ∀ g' ∈ gs,NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
  have ih' := ih hok' (S.erase gs.length) (by
   intro p hp;obtain ⟨hne,hpS⟩:=Finset.mem_erase.1 hp;obtain ⟨g',hg',a,ha,hlt,c,hc⟩:=hS p hpS
   have hpl: p < gs.length:=by
    obtain ⟨h1,_⟩:=List.getElem?_eq_some_iff.1 hg';rw[List.length_append,List.length_singleton] at h1;omega
   rw[List.getElem?_append_left hpl] at hg';rw[hpre a _ (by omega)] at hc
   exact ⟨g',hg',a,ha,hlt,c,hc⟩)
  rw[hstep,List.length_append,List.length_singleton]
  by_cases hin: gs.length∈S
  ·obtain ⟨g',hg',a,ha,hlt,c,hc⟩:=hS _ hin
   have hgg: g' = g:=by
    rw[List.getElem?_concat_length] at hg';exact (Option.some.inj hg').symm
   subst hgg;rw[hpre a _ hlt] at hc;have h2:=elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
   have hcard:=Finset.card_erase_of_mem hin
   have hpos: 1 ≤ S.card:=Finset.card_pos.2 ⟨_,hin⟩;omega
  ·have h2: (eSt n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length+1:=by
    simp only[eSt,List.length_append]
    have:=toList_length_le (smp g.op (n+(elim n gs acc).2.length)
     (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
    omega
   rw[Finset.erase_eq_of_notMem hin] at ih';omega
def RC (n: ℕ) (gs: List Gate) (i: Fin (n+1)) (b: Bool) (p: ℕ): Prop :=
 ∃ g,gs[p]? = some g ∧ ∃ a∈g.inputs,∃ c,stF n gs i b a=Stat.const c
end L540.Helpers
namespace L540.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def vl {k: ℕ} (gs: List Gate) (u: Fin k→Bool) (j: ℕ): Bool :=
 (wF gs (List.ofFn u)).getD j false
theorem vli {k: ℕ} (gs: List Gate) (u: Fin k→Bool) (j: ℕ) (h: j < k) :
  vl gs u j=u ⟨j,h⟩ := by
 unfold vl;rw[getD_wiresFrom gs _ j (by simpa using h)];exact getD_ofFn k u false ⟨j,h⟩
theorem vlg {k: ℕ} (gs: List Gate) (hcl: CL k gs) (u: Fin k→Bool) (p: ℕ)
  (g: Gate) (hp: gs[p]? = some g) :
  vl gs u (k+p)=g.op.eval (g.inputs.map (vl gs u)):=by
 have hlt:=(hcl p g hp).lt;obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp
 have hwl: (wF pre (List.ofFn u)).length=k+pre.length:=by
  rw[length_wiresFrom];simp
 have e: wF (pre ++ g :: post) (List.ofFn u)
   = wF post (wF pre (List.ofFn u) ++
    [g.op.eval (g.inputs.map fun i => (wF pre (List.ofFn u)).getD i false)]):=by
  rw[wiresFrom_append];rfl
 have full: ∀ j,j < k+pre.length →
   (wF (pre ++ g :: post) (List.ofFn u)).getD j false
    = (wF pre (List.ofFn u)).getD j false := by
  intro j hj;rw[e,getD_wiresFrom _ _ j (by simp[hwl];omega),getD_snoc_ne _ _ _ _ (by omega)]
 have top: (wF (pre ++ g :: post) (List.ofFn u)).getD (k+pre.length) false
   = g.op.eval (g.inputs.map fun i => (wF pre (List.ofFn u)).getD i false) := by
  rw[e,getD_wiresFrom _ _ _ (by simp[hwl]),getD_snoc_len _ _ _ _ hwl]
 show (wF (pre ++ g :: post) (List.ofFn u)).getD (k+pre.length) false
  = g.op.eval (g.inputs.map fun j => (wF (pre ++ g :: post) (List.ofFn u)).getD j false)
 rw[top]
 congr 1
 apply List.map_congr_left;intro a ha;exact (full a (hlt a ha)).symm
theorem drop_core (k: ℕ) (pre: List Gate) (g: Gate) (post: List Gate)
  (hcl: CL k (pre ++ g :: post)) (o: ℕ) (S: Stat)
  (hS: ∀ y: Fin k→Bool,S.Valid (k+(elim k pre (idS k,[])).2.length) ∧
   S.val (wF (elim k pre (idS k,[])).2 (List.ofFn y))
    = vl (pre ++ g :: post) y (k+pre.length))
  (hnc: ∃ y y' : Fin k→Bool,vl (pre ++ g :: post) y o≠vl (pre ++ g :: post) y' o) :
  ∃ gs' o',CL k gs' ∧ gs'.length+1 ≤ (pre ++ g :: post).length ∧
   ∀ y: Fin k→Bool,vl gs' y o' = vl (pre ++ g :: post) y o:=by
 have hok: ∀ g' ∈ pre ++ g :: post,Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
 have hokpre: ∀ g' ∈ pre,Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
 have hokpost: ∀ g' ∈ post,Ok g' :=
  fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have inv1: ∀ y: Fin k→Bool,Inv k (List.ofFn y) (wF pre (List.ofFn y))
   (elim k pre (idS k,[])) :=
  fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
 have hwl: ∀ y: Fin k→Bool,(wF pre (List.ofFn y)).length=k+pre.length:=by
  intro y;rw[length_wiresFrom];simp
 have hfull: ∀ y: Fin k→Bool,wF (pre ++ g :: post) (List.ofFn y)
   = wF post (wF pre (List.ofFn y) ++
    [g.op.eval (g.inputs.map fun a => (wF pre (List.ofFn y)).getD a false)]):=by
  intro y;rw[wiresFrom_append];rfl
 have hgv: ∀ y: Fin k→Bool,vl (pre ++ g :: post) y (k+pre.length)
   = g.op.eval (g.inputs.map fun a => (wF pre (List.ofFn y)).getD a false) := by
  intro y
  show (wF (pre ++ g :: post) (List.ofFn y)).getD (k+pre.length) false=_
  rw[hfull,getD_wiresFrom _ _ _ (by simp[hwl y]),getD_snoc_len _ _ _ _ (hwl y)]
 have inv2: ∀ y: Fin k→Bool,Inv k (List.ofFn y)
   (wF pre (List.ofFn y) ++
    [g.op.eval (g.inputs.map fun a => (wF pre (List.ofFn y)).getD a false)])
   ((elim k pre (idS k,[])).1 ++ [S],(elim k pre (idS k,[])).2):=by
  intro y;obtain ⟨hl,hi⟩:=inv1 y
  refine ⟨by simp[hl],?_⟩
  intro a
  show (((elim k pre (idS k,[])).1 ++ [S]).getD a (Stat.const false)).Valid
    (k+(elim k pre (idS k,[])).2.length) ∧
   (((elim k pre (idS k,[])).1 ++ [S]).getD a (Stat.const false)).val
    (wF (elim k pre (idS k,[])).2 (List.ofFn y))=_
  by_cases hal: a=(elim k pre (idS k,[])).1.length
  ·rw[hal,getD_snoc_eq,hl,getD_snoc_eq];exact ⟨(hS y).1,by rw[(hS y).2,hgv]⟩
  ·rw[getD_snoc_ne _ _ _ _ hal,getD_snoc_ne _ _ _ _ (by omega)];exact hi a
 have inv3: ∀ y: Fin k→Bool,Inv k (List.ofFn y)
   (wF (pre ++ g :: post) (List.ofFn y))
   (elim k post ((elim k pre (idS k,[])).1 ++ [S],(elim k pre (idS k,[])).2)):=by
  intro y;rw[hfull];exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
 have hc1: CL k (elim k pre (idS k,[])).2 :=
  clean_elim k (List.ofFn fun _: Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
   (by intro p g' hp;simp at hp)
 have hc3: CL k
   (elim k post ((elim k pre (idS k,[])).1 ++ [S],(elim k pre (idS k,[])).2)).2 :=
  clean_elim k (List.ofFn fun _: Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
 have hlen: (elim k post ((elim k pre (idS k,[])).1 ++ [S],
   (elim k pre (idS k,[])).2)).2.length+1 ≤ (pre ++ g :: post).length:=by
  have h1: (elim k post ((elim k pre (idS k,[])).1 ++ [S],
    (elim k pre (idS k,[])).2)).2.length
    ≤ (elim k pre (idS k,[])).2.length+post.length := elim_len k post _
  have h2: (elim k pre (idS k,[])).2.length ≤ 0+pre.length :=
   elim_len k pre (idS k,[])
  simp only[List.length_append,List.length_cons];omega
 have hval: ∀ y: Fin k→Bool,
   ((elim k post ((elim k pre (idS k,[])).1 ++ [S],
    (elim k pre (idS k,[])).2)).1.getD o (Stat.const false)).val
    (wF (elim k post ((elim k pre (idS k,[])).1 ++ [S],
     (elim k pre (idS k,[])).2)).2 (List.ofFn y))
   = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
 cases hst: (elim k post ((elim k pre (idS k,[])).1 ++ [S],
   (elim k pre (idS k,[])).2)).1.getD o (Stat.const false) with
 | const c =>
  exfalso
  obtain ⟨y,y',hne⟩:=hnc;apply hne;rw[←hval y,←hval y',hst];rfl
 | wire j =>
  refine ⟨_,j,hc3,hlen,?_⟩
  intro y;have h:=hval y;rw[hst] at h;exact h
theorem drop_alias (k: ℕ) (gs: List Gate) (hcl: CL k gs) (o p j: ℕ) (hp: p < gs.length)
  (hj: j < k+p) (heq: ∀ y: Fin k→Bool,vl gs y (k+p)=vl gs y j)
  (hnc: ∃ y y' : Fin k→Bool,vl gs y o≠vl gs y' o) :
  ∃ gs' o',CL k gs' ∧ gs'.length+1 ≤ gs.length ∧
   ∀ y: Fin k→Bool,vl gs' y o' = vl gs y o:=by
 obtain ⟨g,hg⟩ : ∃ g,gs[p]? = some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩;obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hg
 apply drop_core k pre g post hcl o ((elim k pre (idS k,[])).1.getD j (Stat.const false))
  ?_ hnc
 intro y
 have hokpre: ∀ g' ∈ pre,Ok g' :=
  fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
 have inv1:=inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
 refine ⟨(inv1.2 j).1,?_⟩
 rw[(inv1.2 j).2,heq y]
 show (wF pre (List.ofFn y)).getD j false
  = (wF (pre ++ g :: post) (List.ofFn y)).getD j false
 rw[wiresFrom_append,getD_wiresFrom (g :: post) (wF pre (List.ofFn y)) j
  (by rw[length_wiresFrom];simp;omega)]
abbrev ins {n: ℕ} (i: Fin (n+1)) (b: Bool) (y: Fin n→Bool): Fin (n+1)→Bool :=
 Fin.insertNth i b y
def passG (n: ℕ) (gs: List Gate) (i: Fin (n+1)) (b: Bool): List Gate :=
 (elim n gs (stA n i b,[])).2
def IsC (n: ℕ) (gs: List Gate) (i: Fin (n+1)) (b: Bool) (a: ℕ): Prop :=
 ∃ c,stF n gs i b a=Stat.const c
theorem inv_stF (n: ℕ) (gs: List Gate) (hcl: CL (n+1) gs) (i: Fin (n+1)) (b: Bool)
  (y: Fin n→Bool) :
  Inv n (List.ofFn y) (wF gs (List.ofFn (ins i b y))) (elim n gs (stA n i b,[])) :=
 inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)
theorem st_val_const (n: ℕ) (gs: List Gate) (hcl: CL (n+1) gs) (i: Fin (n+1))
  (b: Bool) (j: ℕ) (c: Bool) (h: stF n gs i b j=Stat.const c) (y: Fin n→Bool) :
  vl gs (ins i b y) j=c:=by
 have h1:=((inv_stF n gs hcl i b y).2 j).2;rw[show (elim n gs (stA n i b,[])).1.getD j (Stat.const false)=Stat.const c from h] at h1;exact h1.symm
theorem st_val_wire (n: ℕ) (gs: List Gate) (hcl: CL (n+1) gs) (i: Fin (n+1))
  (b: Bool) (j q: ℕ) (h: stF n gs i b j=Stat.wire q) (y: Fin n→Bool) :
  vl gs (ins i b y) j=vl (passG n gs i b) y q:=by
 have h1:=((inv_stF n gs hcl i b y).2 j).2;rw[show (elim n gs (stA n i b,[])).1.getD j (Stat.const false)=Stat.wire q from h] at h1;exact h1.symm
theorem st_gate (n: ℕ) (gs: List Gate) (hcl: CL (n+1) gs) (i: Fin (n+1)) (b: Bool)
  (p: ℕ) (g: Gate) (hp: gs[p]? = some g) :
  ∃ t,stF n gs i b (n+1+p)
   = (smp g.op (n+t) (g.inputs.map (stF n gs i b))).2 := by
 have hlt:=(hcl p g hp).lt;obtain ⟨pre,post,rfl,rfl⟩:=split_at gs p g hp;have hL: (stA n i b,([]: List Gate)).1.length=n+1:=statAt_length n i b
 refine ⟨(elim n pre (stA n i b,[])).2.length,?_⟩
 have e1: stF n (pre ++ g :: post) i b (n+1+pre.length)
   = (eSt n (elim n pre (stA n i b,[])) g).1.getD (n+1+pre.length)
    (Stat.const false) :=
  elim_split_getD n pre g post _ _ _ (by rw[hL])
 have e2: (eSt n (elim n pre (stA n i b,[])) g).1.getD (n+1+pre.length)
    (Stat.const false)
   = (smp g.op (n+(elim n pre (stA n i b,[])).2.length)
     (g.inputs.map fun a => (elim n pre (stA n i b,[])).1.getD a (Stat.const false))).2 :=
  getD_snoc_len _ _ _ _ (by rw[elim_fst_len,hL])
 have e3: (g.inputs.map fun a => (elim n pre (stA n i b,[])).1.getD a (Stat.const false))
   = g.inputs.map (stF n (pre ++ g :: post) i b) :=
  List.map_congr_left (fun a ha =>
   (elim_split_getD_lt n pre g post _ a _ (by rw[hL];exact hlt a ha)).symm)
 rw[e1,e2,e3]
theorem simp_allconst (op: GateOp) (t: ℕ) (ins: List Stat)
  (hop: op=GateOp.and∨op=GateOp.or∨op=GateOp.not) (hlen: ins.length ≤ 2)
  (h: ∀ s∈ins,∃ c,s=Stat.const c): ∃ c,(smp op t ins).2=Stat.const c:=by
 rcases hop with rfl|rfl|rfl
 ·rcases ins with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩
  ·exact ⟨_,rfl⟩
  ·obtain ⟨c,rfl⟩:=h a (by simp);exact ⟨_,rfl⟩
  ·obtain ⟨c,rfl⟩:=h a (by simp);obtain ⟨c',rfl⟩:=h d (by simp);exact ⟨_,rfl⟩
  ·simp at hlen
 ·rcases ins with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩
  ·exact ⟨_,rfl⟩
  ·obtain ⟨c,rfl⟩:=h a (by simp);exact ⟨_,rfl⟩
  ·obtain ⟨c,rfl⟩:=h a (by simp);obtain ⟨c',rfl⟩:=h d (by simp);exact ⟨_,rfl⟩
  ·simp at hlen
 ·rcases ins with _|⟨a,l⟩
  ·exact ⟨_,rfl⟩
  ·obtain ⟨c,rfl⟩:=h a (by simp);exact ⟨_,rfl⟩
theorem st_allconst (n: ℕ) (gs: List Gate) (hcl: CL (n+1) gs) (i: Fin (n+1))
  (b: Bool) (p: ℕ) (g: Gate) (hp: gs[p]? = some g)
  (h: ∀ a∈g.inputs,IsC n gs i b a): IsC n gs i b (n+1+p):=by
 obtain ⟨t,ht⟩:=st_gate n gs hcl i b p g hp;have hn:=(hcl p g hp).nok
 obtain ⟨c,hc⟩:=simp_allconst g.op (n+t) (g.inputs.map (stF n gs i b)) hn.1.1
  (by
    simpa using hn.1.2) (by
   intro s hs;obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hs
   exact h a ha)
 exact ⟨c,by rw[ht];exact hc⟩
theorem const_read (n: ℕ) (gs: List Gate) (hcl: CL (n+1) gs) (i: Fin (n+1))
  (b: Bool) (p: ℕ) (g: Gate) (hp: gs[p]? = some g) (a: ℕ) (ha: a∈g.inputs)
  (hc: stF n gs i b a=Stat.const (fixBit g)): IsC n gs i b (n+1+p):=by
 have hL: (stA n i b,([]: List Gate)).1.length=n+1:=statAt_length n i b
 have h:=const_of_read n gs (stA n i b,[]) p g hp ((hcl p g hp).nok) a ha
  (by rw[hL];exact (hcl p g hp).lt a ha) hc
 rw[hL] at h;exact h
end L540.Helpers
namespace L540.Helpers.PermInputs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wmap (n m: ℕ) (π : Fin n→Fin m) (w: ℕ): ℕ :=
 if h: w < n then (π ⟨w,h⟩ : ℕ) else w - n+m
def relGate (n m: ℕ) (π : Fin n→Fin m) (g: Gate): Gate :=
 ⟨g.op,g.inputs.map (wmap n m π)⟩
def relabel (n m: ℕ) (π : Fin n→Fin m) (C: Circuit): Circuit :=
 ⟨C.gates.map (relGate n m π),wmap n m π C.output⟩
def step (w: List Bool) (g: Gate): List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m: ℕ) (π : Fin n→Fin m) (W W' : List Bool): Prop :=
 n ≤ W.length ∧ W'.length+n=W.length+m ∧
  ∀ w: ℕ,W'.getD (wmap n m π w) false=W.getD w false
theorem rel_step (n m: ℕ) (π : Fin n→Fin m) (W W' : List Bool) (g: Gate)
  (h: Rel n m π W W'): Rel n m π (step W g) (step W' (relGate n m π g)):=by
 obtain ⟨h1,h2,h3⟩:=h
 have hv: (relGate n m π g).op.eval
   ((relGate n m π g).inputs.map fun i => W'.getD i false)
   = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  simp only[relGate,List.map_map]
  congr 1
  apply List.map_congr_left;intro a _;exact h3 a
 refine ⟨by simp[step];omega,by simp[step];omega,?_⟩
 intro w;simp only[step,hv]
 rcases Nat.lt_trichotomy w W.length with hw|hw|hw
 ·have hlt: wmap n m π w < W'.length:=by
   unfold wmap
   split
   ·have:=(π ⟨w,by assumption⟩).2;omega
   ·omega
  rw[List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw];exact h3 w
 ·have he: wmap n m π w = W'.length:=by
   unfold wmap
   split
   ·omega
   ·omega
  rw[he,hw,getD_snoc_eq,getD_snoc_eq]
 ·have hge: W'.length+1 ≤ wmap n m π w:=by
   unfold wmap
   split
   ·omega
   ·omega
  rw[List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
theorem rel_fold (n m: ℕ) (π : Fin n→Fin m) (gs: List Gate) :
  ∀ W W' : List Bool,Rel n m π W W' →
   Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W'):=by
 induction gs with
 | nil => intro W W' h;exact h
 | cons g gs ih =>
  intro W W' h;exact ih _ _ (rel_step n m π W W' g h)
theorem rel_init (n m: ℕ) (π : Fin n→Fin m) (x: Fin m→Bool) :
  Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w;unfold wmap
 split
 ·rename_i hw
  rw[List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)];simp
 ·rename_i hw
  rw[List.getD_eq_default _ _ (by simp),List.getD_eq_default _ _ (by simp;omega)]
theorem relabel_size {n m: ℕ} (π : Fin n→Fin m) (h: (Fin n→Bool)→Bool) (s: ℕ)
  (hc: HasCircuitSize n h s): HasCircuitSize m (fun x => h (x ∘ π)) s:=by
 obtain ⟨C,ok,hsz,hev⟩:=hc
 refine ⟨relabel n m π C,?_,?_,?_⟩
 ·intro g hg;obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg;exact ⟨(ok g0 hg0).1,by simpa [relGate] using (ok g0 hg0).2⟩
 ·simpa [relabel,Circuit.size] using hsz
 ·intro x
  show _=h (x ∘ π)
  rw[←hev (x ∘ π)]
  have:=(rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
  exact this
end L540.Helpers.PermInputs
namespace L540.Helpers.Forest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open L540.Helpers.PermInputs
end L540.Helpers.Forest
namespace L540.Helpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity L540.Helpers
open L540.Helpers.PermInputs
def Drop {m: ℕ} (f: (Fin m→Bool)→Bool) (y: Fin m) (b: Bool) (k s: ℕ): Prop :=
 ∃ s' : ℕ,s' + k ≤ s∧HasCircuitSize m (fun x => f (Function.update x y b)) s'
structure Least (m: ℕ) (f: (Fin m→Bool)→Bool) (gs: List Gate) (o: ℕ): Prop where
 hcl: CL m gs
 hev: ∀ x: Fin m→Bool,vl gs x o=f x
 hmin: ∀ (gs' : List Gate) (o' : ℕ),CL m gs' → (∀ x: Fin m→Bool,vl gs' x o' = f x) →
  gs.length ≤ gs'.length
def Reads (gs: List Gate) (p w: ℕ): Prop := ∃ g,gs[p]? = some g∧w∈g.inputs
theorem has_of_clean (k: ℕ) (gs: List Gate) (o: ℕ) (hcl: CL k gs) :
  HasCircuitSize k (fun y => vl gs y o) gs.length:=by
 refine ⟨⟨gs,o⟩,?_,le_refl _,fun y => rfl⟩
 intro g hg;exact (clean_nok k gs hcl g hg).1
theorem reads_lt {k: ℕ} {gs: List Gate} (hcl: CL k gs) {q w: ℕ} (h: Reads gs q w) :
  w < k+q:=by
 obtain ⟨g,hg,hw⟩:=h;exact (hcl q g hg).lt w hw
theorem vl_beyond {k: ℕ} (gs: List Gate) (u: Fin k→Bool) (w: ℕ) (h: k+gs.length ≤ w) :
  vl gs u w=false:=by
 unfold vl;exact List.getD_eq_default _ _ (by rw[length_wiresFrom];simp;omega)
theorem vl_not {k: ℕ} (gs: List Gate) (hcl: CL k gs) (u: Fin k→Bool) (q: ℕ) (g: Gate)
  (hq: gs[q]? = some g) (j: ℕ) (hop: g.op=GateOp.not) (hin: g.inputs=[j]) :
  vl gs u (k+q) = !vl gs u j:=by
 rw[vlg gs hcl u q g hq,hop,hin];rfl
theorem drop_dead (k: ℕ) (gs: List Gate) (hcl: CL k gs) (o p: ℕ) (hp: p < gs.length)
  (ho: o≠k+p) (hno: ∀ q,¬ Reads gs q (k+p))
  (hnc: ∃ y y' : Fin k→Bool,vl gs y o≠vl gs y' o) :
  ∃ gs' o',CL k gs' ∧ gs'.length+1 ≤ gs.length ∧
   ∀ y: Fin k→Bool,vl gs' y o' = vl gs y o:=by
 obtain ⟨g,hg⟩ : ∃ g,gs[p]? = some g:=⟨gs[p],List.getElem?_eq_getElem hp⟩
 have hpos: 0 < k+p:=by
  rcases hcl p g hg with ⟨_,j,hj,_⟩ | ⟨_,j,_,hj,_,_⟩ <;> omega
 let g0: Gate:=⟨GateOp.and,[0,0]⟩;let gs' := gs.set p g0
 have hlen: gs'.length=gs.length:=by simp[gs']
 have hget_p: gs'[p]? = some g0:=by simp[gs',hp]
 have hget_ne: ∀ r,r≠p → gs'[r]? = gs[r]? := by
  intro r hr;simp[gs',Ne.symm hr]
 have hcl' : CL k gs' := by
  intro r g' hr'
  by_cases hrp: r=p
  ·subst hrp;rw[hget_p] at hr'
   cases hr'
   exact Or.inr ⟨Or.inl rfl,0,0,hpos,hpos,rfl⟩
  ·rw[hget_ne r hrp] at hr';exact hcl r g' hr'
 have hagree: ∀ y: Fin k→Bool,∀ w,w≠k+p → vl gs' y w=vl gs y w:=by
  intro y w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
   intro hw
   by_cases hwk: w < k
   ·rw[vli gs' y w hwk,vli gs y w hwk]
   ·obtain ⟨r,rfl⟩ : ∃ r,w=k+r:=⟨w - k,by omega⟩
    have hrp: r≠p:=fun e => hw (by rw[e])
    cases hr: gs[r]? with
    | none =>
     have hl: gs.length ≤ r:=List.getElem?_eq_none_iff.1 hr;rw[vl_beyond gs' y _ (by omega),vl_beyond gs y _ (by omega)]
    | some g' =>
     have hr' : gs'[r]? = some g' := by rw[hget_ne r hrp];exact hr
     rw[vlg gs' hcl' y r g' hr',vlg gs hcl y r g' hr]
     congr 1
     apply List.map_congr_left;intro a ha;have hlt:=(hcl r g' hr).lt a ha
     exact ih a hlt (fun e => hno r ⟨g',hr,e ▸ ha⟩)
 have halias: ∀ y: Fin k→Bool,vl gs' y (k+p)=vl gs' y 0:=by
  intro y;rw[vlg gs' hcl' y p g0 hget_p];simp[g0,GateOp.eval]
 have hnc' : ∃ y y' : Fin k→Bool,vl gs' y o≠vl gs' y' o:=by
  obtain ⟨y,y',h⟩:=hnc;exact ⟨y,y',by rw[hagree y o ho,hagree y' o ho];exact h⟩
 obtain ⟨gs'',o'',hc'',hl'',he''⟩ :=
  drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
 exact ⟨gs'',o'',hc'',by omega,fun y => by rw[he'' y,hagree y o ho]⟩
section
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.ncv (L: Least m f gs o) (hnc: ∃ x y: Fin m→Bool,f x≠f y) :
  ∃ y y' : Fin m→Bool,vl gs y o≠vl gs y' o:=by
 obtain ⟨x,y,h⟩:=hnc;exact ⟨x,y,by rw[L.hev,L.hev];exact h⟩
theorem Least.no_alias (L: Least m f gs o) (hnc: ∃ x y: Fin m→Bool,f x≠f y) (p: ℕ)
  (hp: p < gs.length) (j: ℕ) (hj: j < m+p) :
  ¬ ∀ u: Fin m→Bool,vl gs u (m+p)=vl gs u j:=by
 intro hall;obtain ⟨gs',o',hc',hl',he'⟩:=drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
 have:=L.hmin gs' o' hc' (fun x => by rw[he' x];exact L.hev x)
 omega
theorem Least.live (L: Least m f gs o) (hnc: ∃ x y: Fin m→Bool,f x≠f y) (p: ℕ)
  (hp: p < gs.length) (ho: o≠m+p): ∃ q,p < q∧Reads gs q (m+p):=by
 by_contra hno
 have hno' : ∀ q,¬ Reads gs q (m+p):=by
  intro q hq
  by_cases hpq: p < q
  ·exact hno ⟨q,hpq,hq⟩
  ·have:=reads_lt L.hcl hq
   omega
 obtain ⟨gs',o',hc',hl',he'⟩:=drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
 have:=L.hmin gs' o' hc' (fun x => by rw[he' x];exact L.hev x)
 omega
end
theorem upd_ins {n: ℕ} (i: Fin (n+1)) (b: Bool) (x: Fin (n+1)→Bool) :
  Function.update x i b=ins i b (Fin.removeNth i x) :=
 (Fin.insertNth_removeNth i b x).symm
theorem restr_const {n: ℕ} {f: (Fin (n+1)→Bool)→Bool} {gs: List Gate} {o: ℕ}
  (hcl: CL (n+1) gs) (hev: ∀ x: Fin (n+1)→Bool,vl gs x o=f x)
  (i: Fin (n+1)) (b c: Bool) (h: stF n gs i b o=Stat.const c) (x: Fin (n+1)→Bool) :
  f (Function.update x i b)=c:=by
 rw[upd_ins,←hev];exact st_val_const n gs hcl i b o c h _
theorem save (n: ℕ) (f: (Fin (n+1)→Bool)→Bool) (gs: List Gate) (o: ℕ)
  (hcl: CL (n+1) gs) (hev: ∀ x: Fin (n+1)→Bool,vl gs x o=f x)
  (i: Fin (n+1)) (b: Bool)
  (hnc: ∃ x y: Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (S: Finset ℕ) (hS: ∀ p∈S,RC n gs i b p): Drop f i b S.card gs.length:=by
 have hL: (stA n i b,([]: List Gate)).1.length=n+1:=statAt_length n i b
 have hcount:=elim_count n (stA n i b,[]) gs (clean_nok _ gs hcl) S (by
  intro p hp;obtain ⟨g,hg,a,ha,c,hc⟩:=hS p hp
  refine ⟨g,hg,a,ha,?_,c,hc⟩
  rw[hL]
  exact (hcl p g hg).lt a ha)
 simp only[List.length_nil,zero_add] at hcount
 cases hst: stF n gs i b o with
 | const c =>
  exfalso
  obtain ⟨x,y,hxy⟩:=hnc;exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
 | wire j =>
  have hc: CL n (passG n gs i b) :=
   clean_elim n (List.ofFn fun _: Fin n => false) (by simp) gs _ _
    (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp;simp at hp)
  have h2:=relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
  have e: (fun x: Fin (n+1)→Bool => f (Function.update x i b))
    = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
   funext x
   rw[upd_ins,←hev,st_val_wire n gs hcl i b o j hst];rfl
  refine ⟨(passG n gs i b).length,hcount,?_⟩
  rw[e];exact h2
section
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem Least.save (L: Least (n+1) f gs o) (i: Fin (n+1)) (b: Bool)
  (hnc: ∃ x y: Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (S: Finset ℕ) (hS: ∀ p∈S,RC n gs i b p): Drop f i b S.card gs.length :=
 L540.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS
theorem Least.save3 (L: Least (n+1) f gs o) (i: Fin (n+1)) (b: Bool)
  (hnc: ∃ x y: Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (p1 p2 p3: ℕ) (h12: p1≠p2) (h13: p1≠p3) (h23: p2≠p3)
  (h1: RC n gs i b p1) (h2: RC n gs i b p2) (h3: RC n gs i b p3) :
  Drop f i b 3 gs.length:=by
 have:=L.save i b hnc {p1,p2,p3} (by
  intro p hp;simp only[Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl <;> assumption)
 rwa[Finset.card_eq_three.2 ⟨p1,p2,p3,h12,h13,h23,rfl⟩] at this
theorem rc_input {gs: List Gate} {q: ℕ} {i: Fin (n+1)} (b: Bool) (h: Reads gs q i) :
  RC n gs i b q:=by
 obtain ⟨g,hg,hin⟩:=h;exact ⟨g,hg,i,hin,b,stF_self n gs i b⟩
theorem rc_of_reads {gs: List Gate} {q w: ℕ} {i: Fin (n+1)} {b: Bool} (h: Reads gs q w)
  (hc: IsC n gs i b w): RC n gs i b q:=by
 obtain ⟨g,hg,hin⟩:=h;obtain ⟨c,hc⟩:=hc;exact ⟨g,hg,w,hin,c,hc⟩
theorem Least.next (L: Least (n+1) f gs o) (i: Fin (n+1)) (b: Bool)
  (hnc: ∃ x y: Fin (n+1)→Bool,f (Function.update x i b)≠f (Function.update y i b))
  (p: ℕ) (hp: p < gs.length) (hc: IsC n gs i b (n+1+p)) :
  ∃ q,p < q∧Reads gs q (n+1+p)∧RC n gs i b q:=by
 have hfnc: ∃ x y: Fin (n+1)→Bool,f x≠f y:=by
  obtain ⟨x,y,h⟩:=hnc;exact ⟨_,_,h⟩
 have ho: o≠n+1+p:=by
  intro e;obtain ⟨c,hc'⟩:=hc;obtain ⟨x,y,hxy⟩:=hnc;rw[←e] at hc';exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
 obtain ⟨q,hpq,hr⟩:=L.live hfnc p hp ho;exact ⟨q,hpq,hr,rc_of_reads hr hc⟩
end
end L540.Helpers.Readers
namespace L540.Helpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity L540.Helpers
theorem gate_cases {k: ℕ} (gs: List Gate) (hcl: CL k gs) (q: ℕ) (g: Gate)
  (hq: gs[q]? = some g) (a: ℕ) (ha: a∈g.inputs) :
  (g.op=GateOp.not∧g.inputs=[a] ∧ ∀ u: Fin k→Bool,vl gs u (k+q) = !vl gs u a) ∨
  ∃ w,(g.inputs=[a,w]∨g.inputs=[w,a]) ∧
   ((g.op=GateOp.and ∧ ∀ u: Fin k→Bool,vl gs u (k+q)=(vl gs u a&&vl gs u w)) ∨
   (g.op=GateOp.or ∧ ∀ u: Fin k→Bool,vl gs u (k+q)=(vl gs u a||vl gs u w))):=by
 rcases hcl q g hq with ⟨hop,j,_,hin⟩ | ⟨hop,j,j',_,_,hin⟩
 ·left
  have e: a=j:=by rw[hin] at ha;simpa using ha
  subst e
  exact ⟨hop,hin,fun u => vl_not gs hcl u q g hq a hop hin⟩
 ·right
  have e: a=j∨a = j' := by rw[hin] at ha;simpa using ha
  rcases e with e|e
  ·subst e
   refine ⟨j',Or.inl hin,?_⟩
   rcases hop with hop|hop
   ·exact Or.inl ⟨hop,fun u => by rw[vlg gs hcl u q g hq,hop,hin];simp[GateOp.eval]⟩
   ·exact Or.inr ⟨hop,fun u => by rw[vlg gs hcl u q g hq,hop,hin];simp[GateOp.eval]⟩
  ·subst e
   refine ⟨j,Or.inr hin,?_⟩
   rcases hop with hop|hop
   ·refine Or.inl ⟨hop,fun u => ?_⟩
    rw[vlg gs hcl u q g hq,hop,hin]
    simp only[GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id,
     Bool.and_true]
    exact Bool.and_comm _ _
   ·refine Or.inr ⟨hop,fun u => ?_⟩
    rw[vlg gs hcl u q g hq,hop,hin]
    simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id,
     Bool.or_false]
    exact Bool.or_comm _ _
section
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
end
section
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
theorem isC_reader (hcl: CL (n+1) gs) (i: Fin (n+1)) (p: ℕ) (gp: Gate)
  (hgp: gs[p]? = some gp) (hip: (i: ℕ)∈gp.inputs) (b: Bool)
  (h: gp.op=GateOp.not∨b=fixBit gp): IsC n gs i b (n+1+p):=by
 rcases h with h|rfl
 ·apply st_allconst n gs hcl i b p gp hgp;intro a ha
  rcases hcl p gp hgp with ⟨_,j,_,hin⟩ | ⟨hop,_⟩
  ·rw[hin] at ha hip
   simp at ha hip
   rw[ha,←hip];exact ⟨b,stF_self n gs i b⟩
  ·rcases hop with hop|hop <;> rw[hop] at h <;> cases h
 ·exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)
end
end L540.Helpers.Readers
namespace L540.Helpers.NotFreeCor
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity L540.Helpers
def nB0 (n: ℕ) (F: (Fin n→Bool)→Bool) (s: ℕ): Prop :=
 ∀ m,n ≤ m→∃ (gs: List Gate) (out: ℕ),(∀ g∈gs,Ok g)∧(∀ g∈gs,g.op≠GateOp.not)∧gs.length ≤ s ∧
  out < m+gs.length ∧ ∀ w: List Bool,w.length=m →
   (wF gs w).getD out false=F (fun i => w.getD i false)
theorem nfc_bld_mono {n: ℕ} {F: (Fin n→Bool)→Bool} {s s' : ℕ} (h: nB0 n F s) (hs: s ≤ s') :
  nB0 n F s' := by
 intro m hm;obtain ⟨gs,out,ok,nn,len,ho,ev⟩:=h m hm;exact ⟨gs,out,ok,nn,le_trans len hs,ho,ev⟩
theorem nfc_bld_congr {n: ℕ} {F H: (Fin n→Bool)→Bool} {s: ℕ} (h: nB0 n F s)
  (e: ∀ x,F x=H x): nB0 n H s:=by
 intro m hm;obtain ⟨gs,out,ok,nn,len,ho,ev⟩:=h m hm
 exact ⟨gs,out,ok,nn,len,ho,fun w hw => by rw[ev w hw,e]⟩
theorem nfc_bld_var {n: ℕ} (i: Fin n): nB0 n (fun x => x i) 0:=by
 intro m hm
 refine ⟨[],i,by simp,by simp,le_rfl,by simp;omega,?_⟩
 intro w _;simp[wF]
theorem nfc_bld_bin {n: ℕ} (op: GateOp) (hop: op=GateOp.and∨op=GateOp.or)
  (c: Bool→Bool→Bool) (hc: ∀ a b,op.eval [a,b]=c a b)
  {F H: (Fin n→Bool)→Bool} {s1 s2: ℕ} (h1: nB0 n F s1) (h2: nB0 n H s2) :
  nB0 n (fun x => c (F x) (H x)) (s1+s2+1):=by
 intro m hm;obtain ⟨gs1,o1,ok1,nn1,len1,ho1,ev1⟩:=h1 m hm;obtain ⟨gs2,o2,ok2,nn2,len2,ho2,ev2⟩:=h2 (m+gs1.length) (by omega)
 refine ⟨gs1 ++ gs2 ++ [⟨op,[o1,o2]⟩],m+gs1.length+gs2.length,?_,?_,?_,?_,?_⟩
 ·intro g hg;simp only[List.mem_append,List.mem_singleton] at hg
  rcases hg with (hg|hg)|hg
  ·exact ok1 g hg
  ·exact ok2 g hg
  ·subst hg;rcases hop with h|h <;> simp[Ok,h]
 ·intro g hg;simp only[List.mem_append,List.mem_singleton] at hg
  rcases hg with (hg|hg)|hg
  ·exact nn1 g hg
  ·exact nn2 g hg
  ·subst hg;rcases hop with h|h <;> simp[h]
 ·simp;omega
 ·simp;omega
 ·intro w hw;rw[wiresFrom_append,wiresFrom_append];set v:=wF gs1 w with hv
  have lv: v.length=m+gs1.length:=by rw[hv,length_wiresFrom,hw]
  set u:=wF gs2 v with hu
  have lu: u.length=m+gs1.length+gs2.length:=by rw[hu,length_wiresFrom,lv]
  have step: wF [⟨op,[o1,o2]⟩] u
    = u ++ [op.eval ([o1,o2].map fun i => u.getD i false)] := rfl
  rw[step,←lu,getD_snoc_eq];simp only[List.map_cons,List.map_nil,hc]
  have e1: u.getD o1 false=F (fun i => w.getD i false):=by
   rw[hu,getD_wiresFrom _ _ _ (by omega),hv,ev1 w hw]
  have e2: u.getD o2 false=H (fun i => w.getD i false):=by
   rw[hu,ev2 v lv]
   congr 1
   funext i
   rw[hv,getD_wiresFrom _ _ _ (by have := i.2;omega)]
  rw[e1,e2]
theorem nfc_bld_or {n: ℕ} {F H: (Fin n→Bool)→Bool} {s1 s2: ℕ} (h1: nB0 n F s1)
  (h2: nB0 n H s2): nB0 n (fun x => F x||H x) (s1+s2+1) :=
 nfc_bld_bin GateOp.or (Or.inr rfl) (·||·) (by intro a b;simp[GateOp.eval]) h1 h2
theorem nfc_bld_and {n: ℕ} {F H: (Fin n→Bool)→Bool} {s1 s2: ℕ} (h1: nB0 n F s1)
  (h2: nB0 n H s2): nB0 n (fun x => F x&&H x) (s1+s2+1) :=
 nfc_bld_bin GateOp.and (Or.inl rfl) (·&&·) (by intro a b;simp[GateOp.eval]) h1 h2
theorem nfc_bld_circuit {n: ℕ} {F: (Fin n→Bool)→Bool} {s: ℕ} (h: nB0 n F s) :
  ∃ D: Circuit,FanInTwo D∧(∀ g∈D.gates,g.op≠GateOp.not) ∧
   circuitFun n D=F∧D.size ≤ s:=by
 obtain ⟨gs,out,ok,nn,len,_,ev⟩:=h n le_rfl
 refine ⟨⟨gs,out⟩,ok,nn,?_,len⟩
 funext x
 have e:=ev (List.ofFn x) (by simp);simp only[circuitFun,Circuit.eval,wires_eq,e]
 congr 1
 funext i
 simp
theorem nfc_bld_anyList {n: ℕ} (vs: List (Fin n)): ∀ v: Fin n,
  nB0 n (fun x => (v :: vs).any fun j => x j) vs.length:=by
 induction vs with
 | nil => intro v;exact nfc_bld_congr (nfc_bld_var v) (by intro x;simp)
 | cons w ws ih =>
  intro v
  have:=nfc_bld_or (nfc_bld_var v) (ih w)
  refine nfc_bld_congr (nfc_bld_mono this (by simp)) ?_
  intro x;simp
theorem nfc_bld_anyFinset {n: ℕ} (S: Finset (Fin n)) (hS: S.Nonempty) :
  nB0 n (fun x => decide (∃ v∈S,x v=true)) (S.card - 1):=by
 obtain ⟨v,vs,hl⟩ : ∃ v vs,S.toList=v :: vs:=by
  cases h: S.toList with
  | nil => simp at h;exact absurd h hS.ne_empty
  | cons v vs => exact ⟨v,vs,rfl⟩
 have hc: S.card=vs.length+1:=by rw[←Finset.length_toList,hl];rfl
 refine nfc_bld_congr (nfc_bld_mono (nfc_bld_anyList vs v) (by omega)) ?_
 intro x;rw[Bool.eq_iff_iff,decide_eq_true_iff,←hl,List.any_eq_true];simp
open Classical in
theorem nfc_bld_edges (n: ℕ) (T: Finset (Fin n)): ∀ E: Finset (Sym2 (Fin n)),E.Nonempty →
  (∀ e∈E,∃ t∈T,t∈e) →
  nB0 n (fun x => decide (∃ e∈E,∀ v∈e,x v=true)) (E.card+T.card - 1):=by
 induction T using Finset.induction_on with
 | empty =>
  intro E hE hc;obtain ⟨e,he⟩:=hE;obtain ⟨t,ht,_⟩:=hc e he
  simp at ht
 | @insert t T0 htT ih =>
  intro E hE hc
  set E1:=E.filter (fun e => t∈e) with hE1
  set E2:=E.filter (fun e => t∉e) with hE2
  have hsplit: E1.card+E2.card=E.card:=Finset.card_filter_add_card_filter_not _;have hcard: (insert t T0).card=T0.card+1:=Finset.card_insert_of_notMem htT
  have c2: ∀ e∈E2,∃ t' ∈ T0,t' ∈ e:=by
   intro e he;rw[hE2,Finset.mem_filter] at he;obtain ⟨t',ht',hte⟩:=hc e he.1
   rcases Finset.mem_insert.1 ht' with h|h
   ·subst h;exact absurd hte he.2
   ·exact ⟨t',h,hte⟩
  set S:=Finset.univ.filter (fun v: Fin n => s(t,v)∈E1) with hS
  have hSc: S.card ≤ E1.card:=by
   refine Finset.card_le_card_of_injOn (fun v => s(t,v)) ?_ ?_
   ·intro v hv;simp only[hS,Finset.coe_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq] at hv;exact hv
   ·intro a _ b _ hab;exact Sym2.congr_right.1 hab
  have star: E1.Nonempty → nB0 n (fun x => decide (∃ e∈E1,∀ v∈e,x v=true))
    E1.card:=by
   intro h1
   have hSne: S.Nonempty:=by
    obtain ⟨e,he⟩:=h1;have he' := he;rw[hE1,Finset.mem_filter] at he';obtain ⟨b,hb⟩:=Sym2.mem_iff_exists.1 he'.2;exact ⟨b,by simp[hS,←hb,he]⟩
   have:=nfc_bld_and (nfc_bld_var t) (nfc_bld_anyFinset S hSne)
   have hpos:=hSne.card_pos
   refine nfc_bld_congr (nfc_bld_mono this (by omega)) ?_
   intro x;rw[Bool.eq_iff_iff,Bool.and_eq_true,decide_eq_true_iff,decide_eq_true_iff]
   constructor
   ·rintro ⟨ht,v,hv,hxv⟩
    refine ⟨s(t,v),(Finset.mem_filter.1 hv).2,?_⟩
    intro u hu
    rcases Sym2.mem_iff.1 hu with rfl|rfl <;> assumption
   ·rintro ⟨e,he,hall⟩
    have he' := he;rw[hE1,Finset.mem_filter] at he';obtain ⟨b,hb⟩:=Sym2.mem_iff_exists.1 he'.2;subst hb
    exact ⟨hall t (Sym2.mem_mk_left _ _),b,by simp[hS,he],
     hall b (Sym2.mem_mk_right _ _)⟩
  have key: ∀ x: Fin n→Bool,decide (∃ e∈E,∀ v∈e,x v=true)
    = (decide (∃ e∈E1,∀ v∈e,x v=true)||decide (∃ e∈E2,∀ v∈e,x v=true)) := by
   intro x;rw[Bool.eq_iff_iff];simp only[Bool.or_eq_true,decide_eq_true_iff,hE1,hE2,Finset.mem_filter]
   constructor
   ·rintro ⟨e,he,h⟩
    by_cases hte: t∈e
    ·exact Or.inl ⟨e,⟨he,hte⟩,h⟩
    ·exact Or.inr ⟨e,⟨he,hte⟩,h⟩
   ·rintro (⟨e,⟨he,_⟩,h⟩ | ⟨e,⟨he,_⟩,h⟩) <;> exact ⟨e,he,h⟩
  rw[hcard]
  by_cases h1: E1.Nonempty
  ·by_cases h2: E2.Nonempty
   ·have:=nfc_bld_or (star h1) (ih E2 h2 c2)
    have hp:=h2.card_pos
    refine nfc_bld_congr (nfc_bld_mono this (by omega)) ?_
    intro x;rw[key]
   ·rw[Finset.not_nonempty_iff_eq_empty] at h2
    refine nfc_bld_congr (nfc_bld_mono (star h1) (by omega)) ?_
    intro x;rw[key,h2];simp
  ·rw[Finset.not_nonempty_iff_eq_empty] at h1
   have h2: E2.Nonempty:=by
    by_contra h2
    rw[Finset.not_nonempty_iff_eq_empty] at h2
    have:=hE.card_pos
    rw[h1,h2] at hsplit
    simp at hsplit
    omega
   refine nfc_bld_congr (nfc_bld_mono (ih E2 h2 c2) (by omega)) ?_
   intro x;rw[key,h1];simp
end L540.Helpers.NotFreeCor
namespace L540.NCC
open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open L540.Helpers L540.Helpers.PermInputs L540.Helpers.Forest L540.Helpers.Readers L540.Helpers.NotFreeCor
lemma length_eq_sum_count (l: List ℕ) (S: Finset ℕ) (h: ∀ i∈l,i∈S) :
  l.length = ∑ w∈S,l.count w:=by
 induction l with
 | nil => simp
 | cons a l ih =>
  have ha: a∈S:=h a (by simp)
  have ih' := ih (fun i hi => h i (by simp[hi]))
  simp only[List.length_cons,List.count_cons,Finset.sum_add_distrib];rw[←ih'];simp[ha]
lemma tree_card (n: ℕ) (C: Circuit) (G L: Finset ℕ) (ρ : ℕ) (h: IsOrTree n C G L ρ) :
  L.card=G.card+1:=by
 obtain ⟨hg,hl,hgg,hroot⟩:=h
 by_cases hG: G = ∅
 ·simp only[hG,↓reduceIte] at hroot;rw[hroot,hG];simp
 ·simp only[hG,↓reduceIte] at hroot;obtain ⟨j0,hj0,hρ⟩:=hroot
  have hρL: ρ ∉ L:=by
   intro hin
   apply (hl ρ hin).1;rw[hρ];exact ⟨Nat.le_add_right _ _,by simpa using hj0⟩
  have hdisj: Disjoint L (G.image (fun k => n+k)):=by
   rw[disjoint_left];intro w hw hw';obtain ⟨k,hk,rfl⟩:=mem_image.mp hw';apply (hl _ hw).1;exact ⟨Nat.le_add_right _ _,by simpa using hk⟩
  have hsum: ∑ j∈G,(gateAt C j).inputs.length=2 * G.card:=by
   rw[sum_congr rfl (fun j hj => (hg j hj).2.1)]
   simp[Nat.mul_comm]
  have hlen: ∀ j∈G,(gateAt C j).inputs.length
    = ∑ w∈L ∪ G.image (fun k => n+k),(gateAt C j).inputs.count w := by
   intro j hj;apply length_eq_sum_count;intro i hi
   rcases (hg j hj).2.2 i hi with h1|⟨h1,h2⟩
   ·exact Finset.mem_union_left _ h1
   ·apply Finset.mem_union_right;exact mem_image.mpr ⟨i - n,h2,by omega⟩
  have h1: ∑ j∈G,(gateAt C j).inputs.length
    = ∑ w∈L ∪ G.image (fun k => n+k),readsIn C G w := by
   rw[sum_congr rfl hlen,Finset.sum_comm];rfl
  have h2: ∑ w∈L,readsIn C G w=L.card:=by
   rw[sum_congr rfl (fun w hw => show readsIn C G w=1 by
    rw[(hl w hw).2];have hne: w ≠ ρ := fun e => hρL (e ▸ hw);simp[hne])]
   simp
  have h3: ∑ w∈G.image (fun k => n+k),readsIn C G w+1=G.card:=by
   rw[sum_image (fun a _ b _ hab => by omega)]
   rw[sum_congr rfl (fun k hk => hgg k hk)]
   have e: ∀ k∈G,(if n+k = ρ then 0 else 1)=(if k=j0 then 0 else 1):=by
    intro k _
    by_cases hk: k=j0
    ·simp[hk,hρ]
    ·have: n+k ≠ ρ := by omega
     simp[hk,this]
   rw[sum_congr rfl e];rw[←add_sum_erase G _ hj0,if_pos rfl]
   have her: ∑ k∈G.erase j0,(if k=j0 then 0 else 1)=(G.erase j0).card:=by
    calc ∑ k∈G.erase j0,(if k=j0 then 0 else 1)
      = ∑ _k∈G.erase j0,1 := sum_congr rfl fun k hk => if_neg (Finset.ne_of_mem_erase hk)
     _ = (G.erase j0).card := by simp
   rw[her,Nat.zero_add];exact Finset.card_erase_add_one hj0
  rw[h1,Finset.sum_union hdisj,h2] at hsum;omega
lemma bw_spec {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)} {C: Circuit}
  {d: NCCData n} (hv: Valid n K A C d) (t: Fin n) (ht: t∈d.cover) :
  ∃ j < C.gates.length,d.bw t=n+j∧d.role j=(Kind.b,t.val):=by
 obtain ⟨j,hj,h1,h2,_⟩:=(hv.2.2.2.2.2.1 t ht).1;exact ⟨j,hj,h1,h2⟩
lemma bw_injOn {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)} {C: Circuit}
  {d: NCCData n} (hv: Valid n K A C d) (S: Finset (Fin n)) (hS: S⊆d.cover) :
  Set.InjOn d.bw (S: Set (Fin n)):=by
 intro s hs t ht h;obtain ⟨j,_,h1,h2⟩:=bw_spec hv s (hS hs);obtain ⟨j',_,h1',h2'⟩:=bw_spec hv t (hS ht)
 have hj: j = j' := by omega
 subst hj;rw[h2] at h2';exact Fin.ext (Prod.ext_iff.mp h2').2
lemma zLeaves_card {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)} {C: Circuit}
  {d: NCCData n} (hv: Valid n K A C d) (t: Fin n) :
  (zLeaves d t).card=(d.cover.filter (fun s => d.tie s=some t)).card+1:=by
 unfold zLeaves
 rw[card_insert_of_notMem,card_image_of_injOn
  (bw_injOn hv _ (filter_subset _ _))]
 intro hin
 obtain ⟨s,hs,hst⟩:=mem_image.mp hin
 obtain ⟨j,_,h1,_⟩:=bw_spec hv s (mem_filter.mp hs).1
 have:=t.isLt
 omega
lemma topLeaves_card {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)} {C: Circuit}
  {d: NCCData n} (hv: Valid n K A C d) :
  (topLeaves d A).card=A.card+(d.cover.filter (fun t => d.tie t=none)).card:=by
 unfold topLeaves
 rw[card_union_of_disjoint,card_image_of_injective _ Fin.val_injective,
  card_image_of_injOn (bw_injOn hv _ (filter_subset _ _))]
 rw[disjoint_left];intro w hw hw';obtain ⟨a,_,rfl⟩:=mem_image.mp hw;obtain ⟨s,hs,hst⟩:=mem_image.mp hw';obtain ⟨j,_,h1,_⟩:=bw_spec hv s (mem_filter.mp hs).1
 have:=a.isLt
 omega
lemma oLeaves_card {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)} {C: Circuit}
  {d: NCCData n} (hv: Valid n K A C d) (t: Fin n) (ht: t∈d.cover) :
  (oLeaves d t).card=(Finset.univ.filter (fun r => d.owns t r=true)).card:=by
 unfold oLeaves;apply card_image_of_injOn;intro r hr r' hr' h;have hr1: d.owns t r=true:=(mem_filter.mp hr).2;have hr1' : d.owns t r' = true:=(mem_filter.mp hr').2
 have key: ∀ q: Fin n,d.owns t q=true →
   d.lam t q=q.val ∨ ∃ j,d.lam t q=n+j∧d.role j=(Kind.z,q.val):=by
  intro q hq;have hl:=(hv.2.2.2.2.2.1 t ht).2.2.2 q hq;unfold LamOK at hl
  split_ifs at hl
  ·rcases hl.2.1 with h1|⟨j,_,h1,h2⟩
   ·exact Or.inl h1
   ·exact Or.inr ⟨j,h1,h2⟩
  ·exact Or.inl hl
 have hlt:=r.isLt;have hlt' := r'.isLt
 rcases key r hr1 with h1|⟨j,h1,h2⟩ <;> rcases key r' hr1' with h1' | ⟨j',h1',h2'⟩
 ·exact Fin.ext (by omega)
 ·omega
 ·omega
 ·have hj: j = j' := by omega
  subst hj;rw[h2] at h2';exact Fin.ext (Prod.ext_iff.mp h2').2
lemma bGates_card {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)} {C: Circuit}
  {d: NCCData n} (hv: Valid n K A C d) (t: Fin n) (ht: t∈d.cover) :
  (gatesOf d C Kind.b t.val).card=1:=by
 obtain ⟨j,hj,h1,h2⟩:=bw_spec hv t ht;rw[Finset.card_eq_one]
 refine ⟨j,?_⟩
 ext j'
 simp only[gatesOf,mem_filter,mem_range,mem_singleton]
 constructor
 ·rintro ⟨hj',hr⟩
  rcases hv.2.2.2.2.1 j' hj' with htop|⟨t',_,e1,e2⟩
  ·rw[hr] at htop;simp at htop
  ·rw[hr] at e1 e2
   have: t' = t := Fin.ext e1.symm
   subst this
   have:=e2 rfl
   omega
 ·rintro rfl;exact ⟨hj,h2⟩
lemma gates_split {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)} {C: Circuit}
  {d: NCCData n} (hv: Valid n K A C d) :
  C.gates.length=(topGates d C).card + ∑ t∈d.cover,
   ((gatesOf d C Kind.z t.val).card+(gatesOf d C Kind.o t.val).card
    + (gatesOf d C Kind.b t.val).card):=by
 have h0:=Finset.card_filter_add_card_filter_not
  (s := Finset.range C.gates.length) (fun j => (d.role j).1=Kind.top)
 rw[Finset.card_range] at h0
 have hkeys: ∀ j∈(Finset.range C.gates.length).filter (fun j => ¬ (d.role j).1=Kind.top),
   d.role j∈({Kind.z,Kind.o,Kind.b}: Finset Kind) ×ˢ d.cover.image Fin.val:=by
  intro j hj;rw[mem_filter,mem_range] at hj
  rcases hv.2.2.2.2.1 j hj.1 with htop|⟨t,ht,e1,_⟩
  ·exact absurd htop hj.2
  ·rw[Finset.mem_product]
   refine ⟨?_,mem_image.mpr ⟨t,ht,e1.symm⟩⟩
   have hne:=hj.2
   generalize (d.role j).1=k at hne
   cases k <;> simp at hne ⊢
 have h1:=Finset.card_eq_sum_card_fiberwise hkeys
 have hfib: ∀ k∈({Kind.z,Kind.o,Kind.b}: Finset Kind) ×ˢ d.cover.image Fin.val,
   (((Finset.range C.gates.length).filter (fun j => ¬ (d.role j).1=Kind.top)).filter
    (fun j => d.role j=k)).card=(gatesOf d C k.1 k.2).card:=by
  intro k hk
  congr 1
  ext j
  simp only[gatesOf,mem_filter,mem_range]
  constructor
  ·rintro ⟨⟨hj,_⟩,hr⟩;exact ⟨hj,hr⟩
  ·rintro ⟨hj,hr⟩
   refine ⟨⟨hj,?_⟩,hr⟩
   rw[hr];have hk1:=(Finset.mem_product.mp hk).1;intro e;simp only at e;rw[e] at hk1;simp at hk1
 rw[sum_congr rfl hfib,Finset.sum_product] at h1
 dsimp only at h1
 have h2: ∑ k∈({Kind.z,Kind.o,Kind.b}: Finset Kind),∑ v∈d.cover.image Fin.val,
   (gatesOf d C k v).card
   = ∑ t∈d.cover,((gatesOf d C Kind.z t.val).card+(gatesOf d C Kind.o t.val).card
    + (gatesOf d C Kind.b t.val).card):=by
  rw[sum_insert (by decide),sum_insert (by decide),sum_singleton]
  simp only[sum_image (fun a _ b _ h => Fin.val_injective h)]
  rw[←Finset.sum_add_distrib,←Finset.sum_add_distrib];apply sum_congr rfl;intro t _;omega
 have h3: ((Finset.range C.gates.length).filter (fun j => (d.role j).1=Kind.top)).card
   = (topGates d C).card := rfl
 omega
lemma tie_split {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)} {C: Circuit}
  {d: NCCData n} (hv: Valid n K A C d) :
  d.cover.card=(d.cover.filter (fun t => d.tie t=none)).card
   + ∑ t∈d.cover,(d.cover.filter (fun s => d.tie s=some t)).card:=by
 have hkeys: ∀ s∈d.cover,d.tie s∈insert none (d.cover.image some):=by
  intro s _
  cases hs: d.tie s with
  | none => simp
  | some t =>
   have h1:=(hv.2.2.2.1 s t hs).2;have h2:=(hv.2.2.1.1 t s h1).2;simp[h2]
 rw[Finset.card_eq_sum_card_fiberwise hkeys,sum_insert (by simp),
  sum_image (fun a _ b _ h => Option.some_injective _ h)]
lemma owned_card {n: ℕ} {K: SimpleGraph (Fin n)} [DecidableRel K.Adj] {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d) :
  ∑ t∈d.cover,(Finset.univ.filter (fun r => d.owns t r=true)).card
   = K.edgeFinset.card := by
 have hown:=hv.2.2.1
 have hP: ∀ p∈(Finset.univ.filter (fun p: Fin n × Fin n => d.owns p.1 p.2=true)),
   p.1∈d.cover := fun p hp => (hown.1 p.1 p.2 (mem_filter.mp hp).2).2
 have h1:=Finset.card_eq_sum_card_fiberwise hP
 have hfib: ∀ t∈d.cover,
   ((Finset.univ.filter (fun p: Fin n × Fin n => d.owns p.1 p.2=true)).filter
    (fun p => p.1=t)).card=(Finset.univ.filter (fun r => d.owns t r=true)).card:=by
  intro t _
  symm
  apply Finset.card_bij (fun r _ => (t,r))
  ·intro r hr;simp only[mem_filter,mem_univ,true_and] at hr ⊢;exact ⟨hr,trivial⟩
  ·intro a _ b _ h;exact (Prod.ext_iff.mp h).2
  ·rintro ⟨u,v⟩ hp
   simp only[mem_filter,mem_univ,true_and] at hp;obtain ⟨h1,h2⟩:=hp;subst h2;exact ⟨v,by simpa using h1,rfl⟩
 rw[sum_congr rfl hfib] at h1;rw[←h1]
 apply Finset.card_bij (fun p _ => s(p.1,p.2))
 ·intro p hp;rw[SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet];exact (hown.1 p.1 p.2 (mem_filter.mp hp).2).1
 ·rintro ⟨u,v⟩ hp ⟨u',v'⟩ hp' h
  have e1: d.owns u v=true:=(mem_filter.mp hp).2;have e2: d.owns u' v' = true:=(mem_filter.mp hp').2
  rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  ·exact Prod.ext h1 h2
  ·exfalso
   simp only at h1 h2;subst h1;subst h2
   exact hown.2 u v (hown.1 u v e1).1 (by rw[e1,e2])
 ·intro e he
  induction e using Sym2.ind with
  | _ a b =>
   rw[SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at he;have hne:=hown.2 a b he
   cases hab: d.owns a b with
   | true => exact ⟨(a,b),by simp[hab],rfl⟩
   | false =>
    have hba: d.owns b a=true:=by
     rw[hab] at hne
     cases h: d.owns b a with
     | true => rfl
     | false => exact absurd h.symm hne
    exact ⟨(b,a),by simp[hba],Sym2.eq_swap⟩
lemma ncc_size {n: ℕ} {K: SimpleGraph (Fin n)} [DecidableRel K.Adj]
  {A: Finset (Fin n)} {C: Circuit} {d: NCCData n} (hv: Valid n K A C d) :
  C.size+1=A.card+K.edgeFinset.card+d.cover.card:=by
 have hSz: C.size=C.gates.length:=rfl;have hsplit:=gates_split hv;have htop:=tree_card n C _ _ _ hv.2.2.2.2.2.2;rw[topLeaves_card hv] at htop
 have hper: ∀ u∈d.cover,(gatesOf d C Kind.z u.val).card+(gatesOf d C Kind.o u.val).card
   + (gatesOf d C Kind.b u.val).card
   = (d.cover.filter (fun s => d.tie s=some u)).card
    + (Finset.univ.filter (fun r => d.owns u r=true)).card:=by
  intro u hu;have hz:=tree_card n C _ _ _ (hv.2.2.2.2.2.1 u hu).2.1;have ho:=tree_card n C _ _ _ (hv.2.2.2.2.2.1 u hu).2.2.1;rw[zLeaves_card hv u] at hz;rw[oLeaves_card hv u hu] at ho;have hb:=bGates_card hv u hu;omega
 rw[sum_congr rfl hper,Finset.sum_add_distrib,owned_card hv] at hsplit;have htie:=tie_split hv;omega
lemma ncc_fanInTwo {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d): FanInTwo C:=by
 intro g hg;obtain ⟨j,hj,rfl⟩:=List.getElem_of_mem hg
 have hgat: gateAt C j=C.gates[j]:=by simp[gateAt,List.getD,hj]
 rcases hv.2.2.2.2.1 j hj with htop|⟨t,ht,e1,e2⟩
 ·have hmem: j∈topGates d C:=mem_filter.mpr ⟨mem_range.mpr hj,htop⟩;obtain ⟨hop,hlen,_⟩:=hv.2.2.2.2.2.2.1 j hmem;rw[hgat] at hop hlen;exact ⟨by simp[hop],by omega⟩
 ·cases hk: (d.role j).1 with
  | top =>
   have hmem: j∈topGates d C:=mem_filter.mpr ⟨mem_range.mpr hj,hk⟩;obtain ⟨hop,hlen,_⟩:=hv.2.2.2.2.2.2.1 j hmem;rw[hgat] at hop hlen;exact ⟨by simp[hop],by omega⟩
  | z =>
   have hrole: d.role j=(Kind.z,t.val):=Prod.ext hk e1;have hmem: j∈gatesOf d C Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩;obtain ⟨hop,hlen,_⟩:=(hv.2.2.2.2.2.1 t ht).2.1.1 j hmem;rw[hgat] at hop hlen;exact ⟨by simp[hop],by omega⟩
  | o =>
   have hrole: d.role j=(Kind.o,t.val):=Prod.ext hk e1;have hmem: j∈gatesOf d C Kind.o t.val:=mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩;obtain ⟨hop,hlen,_⟩:=(hv.2.2.2.2.2.1 t ht).2.2.1.1 j hmem;rw[hgat] at hop hlen;exact ⟨by simp[hop],by omega⟩
  | b =>
   have hbw:=e2 hk;obtain ⟨j',hj',hbw',_,hop,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
   have hjj: j = j' := by omega
   subst hjj
   rw[hgat] at hop hin
   exact ⟨by simp[hop],by rcases hin with h|h <;> simp[h]⟩
lemma ncc_clean {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d): CL n C.gates:=by
 intro j g hj;have hjlen: j < C.gates.length:=(List.getElem?_eq_some_iff.1 hj).1
 have hgat: gateAt C j=g:=by simp[gateAt,List.getD,hj]
 have hlt:=hv.1 j hjlen;rw[hgat] at hlt
 have hbin: ∀ (op: GateOp),(op=GateOp.and∨op=GateOp.or) → g.op=op →
   g.inputs.length=2 →
   (g.op=GateOp.not ∧ ∃ a < n+j,g.inputs=[a]) ∨
   ((g.op=GateOp.and∨g.op=GateOp.or) ∧ ∃ a b,a < n+j∧b < n+j∧g.inputs=[a,b]):=by
  intro op hop hgop hlen;right
  rcases List.length_eq_two.mp hlen with ⟨a,b,hab⟩
  exact ⟨hgop ▸ hop,a,b,hlt a (by simp[hab]),hlt b (by simp[hab]),hab⟩
 rcases hv.2.2.2.2.1 j hjlen with htop|⟨t,ht,e1,e2⟩
 ·have hmem: j∈topGates d C:=mem_filter.mpr ⟨mem_range.mpr hjlen,htop⟩;obtain ⟨hop,hlen,_⟩:=hv.2.2.2.2.2.2.1 j hmem;rw[hgat] at hop hlen;exact hbin GateOp.or (Or.inr rfl) hop hlen
 ·cases hk: (d.role j).1 with
  | top =>
   have hmem: j∈topGates d C:=mem_filter.mpr ⟨mem_range.mpr hjlen,hk⟩;obtain ⟨hop,hlen,_⟩:=hv.2.2.2.2.2.2.1 j hmem;rw[hgat] at hop hlen;exact hbin GateOp.or (Or.inr rfl) hop hlen
  | z =>
   have hmem: j∈gatesOf d C Kind.z t.val :=
    mem_filter.mpr ⟨mem_range.mpr hjlen,Prod.ext hk e1⟩
   obtain ⟨hop,hlen,_⟩:=(hv.2.2.2.2.2.1 t ht).2.1.1 j hmem;rw[hgat] at hop hlen;exact hbin GateOp.or (Or.inr rfl) hop hlen
  | o =>
   have hmem: j∈gatesOf d C Kind.o t.val :=
    mem_filter.mpr ⟨mem_range.mpr hjlen,Prod.ext hk e1⟩
   obtain ⟨hop,hlen,_⟩:=(hv.2.2.2.2.2.1 t ht).2.2.1.1 j hmem;rw[hgat] at hop hlen;exact hbin GateOp.or (Or.inr rfl) hop hlen
  | b =>
   have hbw:=e2 hk;obtain ⟨j',hj',hbw',_,hop,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
   have hjj: j = j' := by omega
   subst hjj
   rw[hgat] at hop hin
   exact hbin GateOp.and (Or.inl rfl) hop (by rcases hin with h|h <;> simp[h])
lemma ncc_no_not {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d) :
  ∀ j < C.gates.length,(gateAt C j).op≠GateOp.not:=by
 intro j hj
 rcases hv.2.2.2.2.1 j hj with htop|⟨t,ht,e1,e2⟩
 ·have hmem: j∈topGates d C:=mem_filter.mpr ⟨mem_range.mpr hj,htop⟩;rw[(hv.2.2.2.2.2.2.1 j hmem).1];intro h;cases h
 ·cases hk: (d.role j).1 with
  | top =>
   have hmem: j∈topGates d C:=mem_filter.mpr ⟨mem_range.mpr hj,hk⟩;rw[(hv.2.2.2.2.2.2.1 j hmem).1];intro h;cases h
  | z =>
   have hmem: j∈gatesOf d C Kind.z t.val :=
    mem_filter.mpr ⟨mem_range.mpr hj,Prod.ext hk e1⟩
   rw[((hv.2.2.2.2.2.1 t ht).2.1.1 j hmem).1];intro h;cases h
  | o =>
   have hmem: j∈gatesOf d C Kind.o t.val :=
    mem_filter.mpr ⟨mem_range.mpr hj,Prod.ext hk e1⟩
   rw[((hv.2.2.2.2.2.1 t ht).2.2.1.1 j hmem).1];intro h;cases h
  | b =>
   have hbw:=e2 hk;obtain ⟨j',_,hbw',_,hop,_⟩:=(hv.2.2.2.2.2.1 t ht).1
   have hjj: j = j' := by omega
   subst hjj;rw[hop];intro h;cases h
lemma orTree_rt_lt {n: ℕ} {C: Circuit} {G L: Finset ℕ} {ρ : ℕ}
  (ht: IsOrTree n C G L ρ) (hGlt: ∀ j∈G,j < C.gates.length)
  (hLlt: ∀ w∈L,w < n+C.gates.length): ρ < n+C.gates.length:=by
 by_cases hG: G = ∅
 ·have h:=ht.2.2.2;simp[hG] at h;exact hLlt ρ (by rw[h];simp)
 ·have h:=ht.2.2.2;simp[hG] at h;obtain ⟨j,hj,rfl⟩:=h
  have:=hGlt j hj;omega
lemma orTree_lt_root {n: ℕ} {C: Circuit} (hcl: CL n C.gates)
  {G L: Finset ℕ} {ρ : ℕ} (ht: IsOrTree n C G L ρ)
  (hGlt: ∀ j∈G,j < C.gates.length) :
  ∀ m w,n+C.gates.length - w=m→(w∈L ∨ ∃ j∈G,w=n+j) → w ≤ ρ := by
 intro m
 induction m using Nat.strong_induction_on with
 | _ m ih =>
  intro w hm hw
  by_cases hwr: w = ρ
  ·omega
  ·have hreads: readsIn C G w=1:=by
    rcases hw with hwL|⟨j,hjG,rfl⟩
    ·have:=(ht.2.1 w hwL).2;simp[hwr] at this;exact this
    ·have:=ht.2.2.1 j hjG;simp[hwr] at this;exact this
   have hex: ∃ q∈G,w∈(gateAt C q).inputs:=by
    by_contra hno;push Not at hno
    have hz: readsIn C G w=0:=sum_eq_zero (fun q hq => List.count_eq_zero.mpr (hno q hq))
    omega
   obtain ⟨q,hqG,hwq⟩:=hex;have hqlen: q < C.gates.length:=hGlt q hqG
   have hqg: C.gates[q]? = some (gateAt C q):=by simp[gateAt,List.getD,hqlen]
   have hlt: w < n+q:=(hcl q _ hqg).lt w hwq;have hle:=ih (n+C.gates.length - (n+q)) (by omega) (n+q) rfl (Or.inr ⟨q,hqG,rfl⟩);omega
lemma orTree_eval_of_true {n: ℕ} {C: Circuit} (hcl: CL n C.gates)
  {G L: Finset ℕ} {ρ : ℕ} (ht: IsOrTree n C G L ρ)
  (hGlt: ∀ j∈G,j < C.gates.length) (x: Fin n→Bool) :
  ∀ m w,n+C.gates.length - w=m→(w∈L ∨ ∃ j∈G,w=n+j) →
   vl C.gates x w=true → vl C.gates x ρ = true:=by
 intro m
 induction m using Nat.strong_induction_on with
 | _ m ih =>
  intro w hm hw hval
  by_cases hwr: w = ρ
  ·exact hwr ▸ hval
  ·have hreads: readsIn C G w=1:=by
    rcases hw with hwL|⟨j,hjG,rfl⟩
    ·have:=(ht.2.1 w hwL).2;simp[hwr] at this;exact this
    ·have:=ht.2.2.1 j hjG;simp[hwr] at this;exact this
   have hex: ∃ q∈G,w∈(gateAt C q).inputs:=by
    by_contra hno;push Not at hno
    have hz: readsIn C G w=0:=sum_eq_zero (fun q hq => List.count_eq_zero.mpr (hno q hq))
    omega
   obtain ⟨q,hqG,hwq⟩:=hex;have hqlen: q < C.gates.length:=hGlt q hqG
   have hqg: C.gates[q]? = some (gateAt C q):=by simp[gateAt,List.getD,hqlen]
   have hlt: w < n+q:=(hcl q _ hqg).lt w hwq;obtain ⟨hop,hlen,_⟩:=ht.1 q hqG
   rcases List.length_eq_two.mp hlen with ⟨a,b,hab⟩
   have hqval: vl C.gates x (n+q)=true:=by
    rw[vlg C.gates hcl x q _ hqg,hop,hab];rw[hab] at hwq;simp only[List.mem_cons,List.not_mem_nil,or_false] at hwq
    rcases hwq with rfl|rfl <;> simp[GateOp.eval,hval]
   exact ih (n+C.gates.length - (n+q)) (by omega) (n+q) rfl (Or.inr ⟨q,hqG,rfl⟩) hqval
def cfStep (n: ℕ) (d: NCCData n) (w: List Bool) (g: Gate): List Bool :=
 w ++ [decide ((d.role (w.length - n)).1=Kind.z)&&g.inputs.any (fun i => w.getD i false)]
lemma cf_fold_len (n: ℕ) (d: NCCData n) (gs: List Gate) (w: List Bool) :
  (gs.foldl (cfStep n d) w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw[List.foldl_cons,ih];simp[cfStep];omega
lemma cf_fold_keep (n: ℕ) (d: NCCData n) (gs: List Gate) (w: List Bool)
  (i: ℕ) (hi: i < w.length) :
  (gs.foldl (cfStep n d) w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  rw[List.foldl_cons,ih (cfStep n d w g) (by simp[cfStep];omega)];exact List.getD_append _ _ _ _ hi
lemma cfi {n: ℕ} (C: Circuit) (d: NCCData n) (i: Fin n) :
  IsCentred n C d i.val↔i∈d.cover:=by
 unfold IsCentred centreFlags
 change (C.gates.foldl (cfStep n d) (List.ofFn fun j: Fin n => decide (j∈d.cover))).getD i.val false=true↔_
 rw[cf_fold_keep n d C.gates _ i.val (by simp)];simp[List.getD,i.isLt]
lemma cfg {n: ℕ} (C: Circuit) (d: NCCData n) (hrb: ReadsBack n C)
  (j: ℕ) (hj: j < C.gates.length) :
  IsCentred n C d (n+j) ↔
   (d.role j).1=Kind.z ∧ ∃ i∈(gateAt C j).inputs,IsCentred n C d i:=by
 have hsplit: C.gates=C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1):=by
  have h1:=List.take_append_drop j C.gates;have h2: C.gates.drop j=C.gates[j] :: C.gates.drop (j+1):=List.drop_eq_getElem_cons hj;rw[h2] at h1;exact h1.symm
 let w0: List Bool:=List.ofFn fun i: Fin n => decide (i∈d.cover)
 let pre:=(C.gates.take j).foldl (cfStep n d) w0
 have hpre_len: pre.length=n+j:=by
  simp only[pre,cf_fold_len,w0,List.length_ofFn,List.length_take];omega
 have hcf: centreFlags n C d=(C.gates.drop (j+1)).foldl (cfStep n d) (cfStep n d pre C.gates[j]):=by
  unfold centreFlags;change C.gates.foldl (cfStep n d) w0=_
  conv_lhs => rw[hsplit]
  rw[List.foldl_append,List.foldl_cons]
 have hpre_eq: ∀ i < n+j,(centreFlags n C d).getD i false=pre.getD i false:=by
  intro i hi;rw[hcf,cf_fold_keep n d _ _ i (by simp[cfStep,hpre_len];omega)];exact List.getD_append _ _ _ _ (by omega)
 have hgat: gateAt C j=C.gates[j]:=by simp[gateAt,List.getD,hj]
 have hlhs: IsCentred n C d (n+j) ↔
   (decide ((d.role j).1=Kind.z)&&C.gates[j].inputs.any fun i => pre.getD i false)=true:=by
  unfold IsCentred;rw[hcf,cf_fold_keep n d _ _ (n+j) (by simp[cfStep,hpre_len])];simp only[cfStep,hpre_len,Nat.add_sub_cancel_left]
  have hsnoc: (pre ++ [decide ((d.role j).1=Kind.z) &&
    C.gates[j].inputs.any fun i => pre.getD i false]).getD pre.length false =
    (decide ((d.role j).1=Kind.z)&&C.gates[j].inputs.any fun i => pre.getD i false) :=
   getD_snoc_eq _ _ false
  rw[←hpre_len,hsnoc]
 rw[hlhs,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true,hgat]
 constructor
 ·rintro ⟨hr,i,hi,hpi⟩
  refine ⟨hr,i,hi,?_⟩
  have hilt: i < n+j:=hrb j hj i (by rw[hgat];exact hi);unfold IsCentred;rw[hpre_eq i hilt];exact hpi
 ·rintro ⟨hr,i,hi,hci⟩
  refine ⟨hr,i,hi,?_⟩
  have hilt: i < n+j:=hrb j hj i (by rw[hgat];exact hi);unfold IsCentred at hci;rw[←hpre_eq i hilt];exact hci
lemma ncx {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d) (r: Fin n) (hr: r∈d.cover)
  (x: Fin n→Bool) (hxr: x r=true) :
  ∀ w,IsCentred n C d w →
   (w=r.val ∨ ∃ j < C.gates.length,w=n+j∧d.role j=(Kind.z,r.val)) →
   vl C.gates x w=true:=by
 have hcl:=ncc_clean hv;intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hcen hw
  rcases hw with rfl|⟨j,hj,rfl,hrole⟩
  ·rw[vli C.gates x r.val r.isLt];exact hxr
  ·obtain ⟨_,i,hi,hci⟩:=(cfg C d hv.1 j hj).mp hcen;have hjG: j∈gatesOf d C Kind.z r.val:=mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩;have hZt:=(hv.2.2.2.2.2.1 r hr).2.1;have hilt: i < n+j:=hv.1 j hj i hi
   have hival: vl C.gates x i=true:=by
    rcases (hZt.1 j hjG).2.2 i hi with hiL|⟨hin,hiG⟩
    ·simp only[zLeaves,mem_insert,mem_image,mem_filter] at hiL
     rcases hiL with rfl|⟨s,⟨hs,_⟩,rfl⟩
     ·rw[vli C.gates x r.val r.isLt];exact hxr
     ·obtain ⟨jb,hjb,hbw,hrb_s⟩:=bw_spec hv s hs;rw[hbw] at hci;have hkz:=((cfg C d hv.1 jb hjb).mp hci).1;rw[hrb_s] at hkz;simp at hkz
    ·have hiG' := mem_filter.mp hiG;have hj'lt: i - n < C.gates.length:=mem_range.mp hiG'.1;exact ih i hilt hci (Or.inr ⟨i - n,hj'lt,by omega,hiG'.2⟩)
   have hqg: C.gates[j]? = some (gateAt C j):=by simp[gateAt,List.getD,hj]
   obtain ⟨hop,hlen,_⟩:=hZt.1 j hjG
   rcases List.length_eq_two.mp hlen with ⟨a,b,hab⟩
   rw[vlg C.gates hcl x j _ hqg,hop,hab];rw[hab] at hi;simp only[List.mem_cons,List.not_mem_nil,or_false] at hi
   rcases hi with rfl|rfl <;> simp[GateOp.eval,hival]
lemma ncc_z_of_x {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d) (t: Fin n) (ht: t∈d.cover)
  (x: Fin n→Bool) (hxt: x t=true) :
  vl C.gates x (d.zroot t)=true:=by
 have hcl:=ncc_clean hv;have hZt:=(hv.2.2.2.2.2.1 t ht).2.1
 have hGlt: ∀ j∈gatesOf d C Kind.z t.val,j < C.gates.length:=fun j hj =>
  mem_range.mp (mem_filter.mp hj).1
 apply orTree_eval_of_true hcl hZt hGlt x _ t.val rfl (Or.inl (by simp[zLeaves]));rw[vli C.gates x t.val t.isLt];exact hxt
lemma ncc_o_of_x {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d) (t r: Fin n) (ht: t∈d.cover)
  (hown: d.owns t r=true) (x: Fin n→Bool) (hxr: x r=true) :
  vl C.gates x (d.oroot t)=true:=by
 have hcl:=ncc_clean hv;have hOt:=(hv.2.2.2.2.2.1 t ht).2.2.1
 have hGlt: ∀ j∈gatesOf d C Kind.o t.val,j < C.gates.length:=fun j hj =>
  mem_range.mp (mem_filter.mp hj).1
 have hmem: d.lam t r∈oLeaves d t :=
  mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ r,hown⟩,rfl⟩
 apply orTree_eval_of_true hcl hOt hGlt x _ (d.lam t r) rfl (Or.inl hmem);have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r hown;unfold LamOK at hlam
 by_cases hr: r∈d.cover
 ·simp only[hr,↓reduceIte] at hlam;exact ncx hv r hr x hxr (d.lam t r) hlam.1 hlam.2.1
 ·simp only[hr,↓reduceIte] at hlam;rw[hlam,vli C.gates x r.val r.isLt];exact hxr
lemma ncc_tie_up {n: ℕ} {K: SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d) (x: Fin n→Bool) :
  ∀ m (t: Fin n),t∈d.cover → n+C.gates.length - d.bw t=m →
   vl C.gates x (d.zroot t)=true → vl C.gates x (d.bw t)=true →
   vl C.gates x C.output=true:=by
 have hcl:=ncc_clean hv;intro m
 induction m using Nat.strong_induction_on with
 | _ m ih =>
  intro t ht hm hz hb
  cases htie: d.tie t with
  | none =>
   have hTop:=hv.2.2.2.2.2.2
   have hGlt: ∀ j∈topGates d C,j < C.gates.length:=fun j hj =>
    mem_range.mp (mem_filter.mp hj).1
   have hmem: d.bw t∈topLeaves d A :=
    Finset.mem_union_right _ (mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,htie⟩,rfl⟩)
   exact orTree_eval_of_true hcl hTop hGlt x _ (d.bw t) rfl (Or.inl hmem) hb
  | some s =>
   have hs_own: d.owns s t=true:=(hv.2.2.2.1 t s htie).2;have hs: s∈d.cover:=(hv.2.2.1.1 s t hs_own).2;have hZs:=(hv.2.2.2.2.2.1 s hs).2.1;have hOs:=(hv.2.2.2.2.2.1 s hs).2.2.1
   have hZlt: ∀ j∈gatesOf d C Kind.z s.val,j < C.gates.length:=fun j hj =>
    mem_range.mp (mem_filter.mp hj).1
   have hOlt: ∀ j∈gatesOf d C Kind.o s.val,j < C.gates.length:=fun j hj =>
    mem_range.mp (mem_filter.mp hj).1
   have hbw_mem: d.bw t∈zLeaves d s :=
    mem_insert_of_mem (mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,htie⟩,rfl⟩)
   have hz_s: vl C.gates x (d.zroot s)=true :=
    orTree_eval_of_true hcl hZs hZlt x _ (d.bw t) rfl (Or.inl hbw_mem) hb
   have hlam_eq: d.lam s t=d.zroot t:=by
    have hlam:=(hv.2.2.2.2.2.1 s hs).2.2.2 t hs_own;unfold LamOK at hlam;simp only[ht,↓reduceIte] at hlam;exact hlam.2.2 htie
   have ho_mem: d.lam s t∈oLeaves d s :=
    mem_image.mpr ⟨t,mem_filter.mpr ⟨mem_univ t,hs_own⟩,rfl⟩
   have ho_s: vl C.gates x (d.oroot s)=true :=
    orTree_eval_of_true hcl hOs hOlt x _ (d.lam s t) rfl (Or.inl ho_mem) (hlam_eq ▸ hz)
   obtain ⟨js,hjs,hbws,_,hops,hins⟩:=(hv.2.2.2.2.2.1 s hs).1
   have hgs: C.gates[js]? = some (gateAt C js):=by simp[gateAt,List.getD,hjs]
   have hb_s: vl C.gates x (d.bw s)=true:=by
    rw[hbws,vlg C.gates hcl x js _ hgs,hops]
    rcases hins with hin|hin <;> rw[hin] <;> simp[GateOp.eval,hz_s,ho_s]
   have hbw_lt_z: d.bw t ≤ d.zroot s:=orTree_lt_root hcl hZs hZlt _ (d.bw t) rfl (Or.inl hbw_mem)
   have hz_lt_b: d.zroot s < d.bw s:=by
    rw[hbws]
    exact hv.1 js hjs (d.zroot s) (by rcases hins with hin|hin <;> simp[hin])
   obtain ⟨jt,hjt,hbwt,_⟩:=bw_spec hv t ht;exact ih (n+C.gates.length - d.bw s) (by omega) s hs rfl hz_s hb_s
lemma ncc_eval {n: ℕ} {K: SimpleGraph (Fin n)} [DecidableRel K.Adj] {A: Finset (Fin n)}
  {C: Circuit} {d: NCCData n} (hv: Valid n K A C d) :
  circuitFun n C=graphFun K A:=by
 have hcl:=ncc_clean hv
 funext x
 change vl C.gates x C.output=graphFun K A x;apply Bool.eq_iff_iff.mpr
 constructor
 ·intro hout
  by_contra hgf
  have hgf' : graphFun K A x=false:=Bool.eq_false_iff.mpr hgf;simp only[graphFun,Bool.or_eq_false_iff,decide_eq_false_iff_not] at hgf';obtain ⟨hnoA,hnoE⟩ := hgf'
  push Not at hnoA hnoE
  have hinv: ∀ w < n+C.gates.length,
    (∀ j,w=n+j → j < C.gates.length→(d.role j).1=Kind.top → vl C.gates x w=false) ∧
    (∀ t∈d.cover,w=d.bw t → vl C.gates x w=false) ∧
    (∀ t∈d.cover,(w=t.val ∨ ∃ j < C.gates.length,w=n+j∧d.role j=(Kind.z,t.val)) →
     vl C.gates x w=true → x t=true) ∧
    (∀ t∈d.cover,(w∈oLeaves d t ∨ ∃ j < C.gates.length,w=n+j∧d.role j=(Kind.o,t.val)) →
     vl C.gates x w=true→∃ r,d.owns t r=true∧x r=true):=by
   intro w
   induction w using Nat.strong_induction_on with
   | _ w ih =>
    intro hw
    have hB: ∀ t∈d.cover,w=d.bw t → vl C.gates x w=false:=by
     intro t ht hwt;obtain ⟨j,hj,hbw,_,hop,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
     have hgj: C.gates[j]? = some (gateAt C j):=by simp[gateAt,List.getD,hj]
     have hzl: d.zroot t < w:=by rw[hwt,hbw];exact hv.1 j hj _ (by rcases hin with h|h <;> simp[h])
     have hol: d.oroot t < w:=by rw[hwt,hbw];exact hv.1 j hj _ (by rcases hin with h|h <;> simp[h])
     rw[hwt,hbw,vlg C.gates hcl x j _ hgj,hop]
     cases hzv: vl C.gates x (d.zroot t)
     ·rcases hin with h|h <;> simp[h,GateOp.eval,hzv]
     ·cases hov: vl C.gates x (d.oroot t)
      ·rcases hin with h|h <;> simp[h,GateOp.eval,hzv,hov]
      ·exfalso
       have hZt:=(hv.2.2.2.2.2.1 t ht).2.1;have hOt:=(hv.2.2.2.2.2.1 t ht).2.2.1
       have hxt: x t=true:=by
        have hzr_mem: d.zroot t=t.val ∨ ∃ jz < C.gates.length,d.zroot t=n+jz∧d.role jz=(Kind.z,t.val):=by
         by_cases hG: gatesOf d C Kind.z t.val = ∅
         ·have hr:=hZt.2.2.2;simp only[hG,↓reduceIte] at hr
          have hmem: d.zroot t∈zLeaves d t:=by rw[hr];simp
          simp only[zLeaves,mem_insert,mem_image,mem_filter] at hmem
          rcases hmem with h|⟨s,⟨hs,_⟩,hbw_s⟩
          ·exact Or.inl h
          ·exfalso
           have hf:=(ih (d.zroot t) hzl (by omega)).2.1 s hs hbw_s.symm;rw[hf] at hzv;cases hzv
         ·have hr:=hZt.2.2.2;simp only[hG,↓reduceIte] at hr;obtain ⟨jz,hjz,heq⟩:=hr;have hjz' := mem_filter.mp hjz;exact Or.inr ⟨jz,mem_range.mp hjz'.1,heq,hjz'.2⟩
        exact (ih (d.zroot t) hzl (by omega)).2.2.1 t ht hzr_mem hzv
       have hxr: ∃ r,d.owns t r=true∧x r=true:=by
        have hor_mem: d.oroot t∈oLeaves d t ∨ ∃ jo < C.gates.length,d.oroot t=n+jo∧d.role jo=(Kind.o,t.val):=by
         by_cases hG: gatesOf d C Kind.o t.val = ∅
         ·have hr:=hOt.2.2.2;simp only[hG,↓reduceIte] at hr;exact Or.inl (by rw[hr];simp)
         ·have hr:=hOt.2.2.2;simp only[hG,↓reduceIte] at hr;obtain ⟨jo,hjo,heq⟩:=hr;have hjo' := mem_filter.mp hjo;exact Or.inr ⟨jo,mem_range.mp hjo'.1,heq,hjo'.2⟩
        exact (ih (d.oroot t) hol (by omega)).2.2.2 t ht hor_mem hov
       obtain ⟨r,hown,hxr⟩:=hxr;have hadj:=(hv.2.2.1.1 t r hown).1;exact hnoE t r hadj hxt hxr
    have hZ: ∀ t∈d.cover,(w=t.val ∨ ∃ j < C.gates.length,w=n+j∧d.role j=(Kind.z,t.val)) →
      vl C.gates x w=true → x t=true:=by
     intro t ht hwz hval
     rcases hwz with rfl|⟨j,hj,rfl,hrole⟩
     ·rw[vli C.gates x t.val t.isLt] at hval;exact hval
     ·have hjG: j∈gatesOf d C Kind.z t.val:=mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩;have hZt:=(hv.2.2.2.2.2.1 t ht).2.1;obtain ⟨hop,hlen,hin⟩:=hZt.1 j hjG
      have hgj: C.gates[j]? = some (gateAt C j):=by simp[gateAt,List.getD,hj]
      rcases List.length_eq_two.mp hlen with ⟨a,b,hab⟩
      rw[vlg C.gates hcl x j _ hgj,hop,hab] at hval
      simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,
       Bool.or_false,Bool.or_eq_true] at hval
      have hex: ∃ i∈(gateAt C j).inputs,vl C.gates x i=true:=by
       rcases hval with ha|hb
       ·exact ⟨a,by simp[hab],ha⟩
       ·exact ⟨b,by simp[hab],hb⟩
      obtain ⟨i,hi,hival⟩:=hex;have hilt: i < n+j:=hv.1 j hj i hi
      rcases hin i hi with hiL|⟨_,hiG⟩
      ·simp only[zLeaves,mem_insert,mem_image,mem_filter] at hiL
       rcases hiL with rfl|⟨s,⟨hs,_⟩,rfl⟩
       ·rw[vli C.gates x t.val t.isLt] at hival;exact hival
       ·have hf:=(ih (d.bw s) hilt (by omega)).2.1 s hs rfl;rw[hf] at hival;cases hival
      ·have hiG' := mem_filter.mp hiG
       exact (ih i hilt (by omega)).2.2.1 t ht
        (Or.inr ⟨i - n,mem_range.mp hiG'.1,by omega,hiG'.2⟩) hival
    have hO: ∀ t∈d.cover,(w∈oLeaves d t ∨ ∃ j < C.gates.length,w=n+j∧d.role j=(Kind.o,t.val)) →
      vl C.gates x w=true→∃ r,d.owns t r=true∧x r=true:=by
     intro t ht hwo hval
     rcases hwo with hwL|⟨j,hj,rfl,hrole⟩
     ·simp only[oLeaves,mem_image,mem_filter,mem_univ,true_and] at hwL;obtain ⟨r,hown,rfl⟩:=hwL
      refine ⟨r,hown,?_⟩
      have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r hown;unfold LamOK at hlam
      by_cases hr: r∈d.cover
      ·simp only[hr,↓reduceIte] at hlam;exact hZ r hr hlam.2.1 hval
      ·simp only[hr,↓reduceIte] at hlam;rw[hlam,vli C.gates x r.val r.isLt] at hval;exact hval
     ·have hjG: j∈gatesOf d C Kind.o t.val:=mem_filter.mpr ⟨mem_range.mpr hj,hrole⟩;have hOt:=(hv.2.2.2.2.2.1 t ht).2.2.1;obtain ⟨hop,hlen,hin⟩:=hOt.1 j hjG
      have hgj: C.gates[j]? = some (gateAt C j):=by simp[gateAt,List.getD,hj]
      rcases List.length_eq_two.mp hlen with ⟨a,b,hab⟩
      rw[vlg C.gates hcl x j _ hgj,hop,hab] at hval
      simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,
       Bool.or_false,Bool.or_eq_true] at hval
      have hex: ∃ i∈(gateAt C j).inputs,vl C.gates x i=true:=by
       rcases hval with ha|hb
       ·exact ⟨a,by simp[hab],ha⟩
       ·exact ⟨b,by simp[hab],hb⟩
      obtain ⟨i,hi,hival⟩:=hex;have hilt: i < n+j:=hv.1 j hj i hi
      rcases hin i hi with hiL|⟨_,hiG⟩
      ·exact (ih i hilt (by omega)).2.2.2 t ht (Or.inl hiL) hival
      ·have hiG' := mem_filter.mp hiG
       exact (ih i hilt (by omega)).2.2.2 t ht
        (Or.inr ⟨i - n,mem_range.mp hiG'.1,by omega,hiG'.2⟩) hival
    have hT: ∀ j,w=n+j → j < C.gates.length→(d.role j).1=Kind.top → vl C.gates x w=false:=by
     intro j rfl hj htop;have hjG: j∈topGates d C:=mem_filter.mpr ⟨mem_range.mpr hj,htop⟩;have hTop:=hv.2.2.2.2.2.2;obtain ⟨hop,hlen,hin⟩:=hTop.1 j hjG
     have hgj: C.gates[j]? = some (gateAt C j):=by simp[gateAt,List.getD,hj]
     rcases List.length_eq_two.mp hlen with ⟨a,b,hab⟩
     have hif: ∀ i∈(gateAt C j).inputs,vl C.gates x i=false:=by
      intro i hi;have hilt: i < n+j:=hv.1 j hj i hi
      rcases hin i hi with hiL|⟨_,hiG⟩
      ·simp only[topLeaves,mem_union,mem_image,mem_filter] at hiL
       rcases hiL with ⟨u,huA,rfl⟩ | ⟨t,⟨ht,_⟩,rfl⟩
       ·rw[vli C.gates x u.val u.isLt];exact Bool.eq_false_iff.mpr (hnoA u huA)
       ·exact (ih (d.bw t) hilt (by omega)).2.1 t ht rfl
      ·have hiG' := mem_filter.mp hiG;exact (ih i hilt (by omega)).1 (i - n) (by omega) (mem_range.mp hiG'.1) hiG'.2
     rw[vlg C.gates hcl x j _ hgj,hop,hab];simp[GateOp.eval,hif a (by simp[hab]),hif b (by simp[hab])]
    exact ⟨hT,hB,hZ,hO⟩
  have hTop:=hv.2.2.2.2.2.2
  by_cases hG: topGates d C = ∅
  ·have hr:=hTop.2.2.2;simp only[hG,↓reduceIte] at hr
   have hmem: C.output∈topLeaves d A:=by rw[hr];simp
   simp only[topLeaves,mem_union,mem_image,mem_filter] at hmem
   rcases hmem with ⟨u,huA,hcu⟩ | ⟨t,⟨ht,_⟩,hcb⟩
   ·rw[←hcu,vli C.gates x u.val u.isLt] at hout;exact hnoA u huA hout
   ·obtain ⟨j,hj,hbw,_⟩:=bw_spec hv t ht;have hf:=(hinv C.output (by omega)).2.1 t ht hcb.symm;rw[hf] at hout;cases hout
  ·have hr:=hTop.2.2.2;simp only[hG,↓reduceIte] at hr;obtain ⟨j,hj,hco⟩:=hr;have hj' := mem_filter.mp hj;have hjlt: j < C.gates.length:=mem_range.mp hj'.1;have hf:=(hinv C.output (by omega)).1 j hco hjlt hj'.2;rw[hf] at hout;cases hout
 ·intro hgf;simp only[graphFun,Bool.or_eq_true,decide_eq_true_eq] at hgf
  rcases hgf with ⟨a,haA,hxa⟩ | ⟨u,v,huv,hxu,hxv⟩
  ·have hTop:=hv.2.2.2.2.2.2
   have hGlt: ∀ j∈topGates d C,j < C.gates.length:=fun j hj =>
    mem_range.mp (mem_filter.mp hj).1
   have hmem: a.val∈topLeaves d A :=
    Finset.mem_union_left _ (mem_image.mpr ⟨a,haA,rfl⟩)
   apply orTree_eval_of_true hcl hTop hGlt x _ a.val rfl (Or.inl hmem);rw[vli C.gates x a.val a.isLt];exact hxa
  ·have hne:=hv.2.2.1.2 u v huv
   have hown: (d.owns u v=true∧u∈d.cover)∨(d.owns v u=true∧v∈d.cover):=by
    cases h1: d.owns u v
    ·have h2: d.owns v u=true:=by
      rw[h1] at hne;cases h: d.owns v u <;> simp_all
     exact Or.inr ⟨h2,(hv.2.2.1.1 v u h2).2⟩
    ·exact Or.inl ⟨rfl,(hv.2.2.1.1 u v h1).2⟩
   rcases hown with ⟨huv',hu⟩ | ⟨hvu',hv'⟩
   ·have hz:=ncc_z_of_x hv u hu x hxu;have ho:=ncc_o_of_x hv u v hu huv' x hxv;obtain ⟨j,hj,hbw,_,hop,hin⟩:=(hv.2.2.2.2.2.1 u hu).1
    have hgj: C.gates[j]? = some (gateAt C j):=by simp[gateAt,List.getD,hj]
    have hb: vl C.gates x (d.bw u)=true:=by
     rw[hbw,vlg C.gates hcl x j _ hgj,hop]
     rcases hin with h|h <;> rw[h] <;> simp[GateOp.eval,hz,ho]
    exact ncc_tie_up hv x _ u hu rfl hz hb
   ·have hz:=ncc_z_of_x hv v hv' x hxv;have ho:=ncc_o_of_x hv v u hv' hvu' x hxu;obtain ⟨j,hj,hbw,_,hop,hin⟩:=(hv.2.2.2.2.2.1 v hv').1
    have hgj: C.gates[j]? = some (gateAt C j):=by simp[gateAt,List.getD,hj]
    have hb: vl C.gates x (d.bw v)=true:=by
     rw[hbw,vlg C.gates hcl x j _ hgj,hop]
     rcases hin with h|h <;> rw[h] <;> simp[GateOp.eval,hz,ho]
    exact ncc_tie_up hv x _ v hv' rfl hz hb
lemma nfc_graph_upper {n: ℕ} (K: SimpleGraph (Fin n)) [DecidableRel K.Adj]
  (A T: Finset (Fin n)) (hE: ∃ u v: Fin n,K.Adj u v)
  (hcov: K.IsVertexCover (T: Set (Fin n))) :
  HasCircuitSize n (graphFun K A) (A.card+K.edgeFinset.card+T.card - 1):=by
 obtain ⟨u0,v0,huv0⟩:=hE;have hEne: K.edgeFinset.Nonempty:=⟨s(u0,v0),by simpa using huv0⟩;have hEpos:=hEne.card_pos
 have hcov' : ∀ e∈K.edgeFinset,∃ t∈T,t∈e:=by
  intro e
  refine Sym2.ind (fun a b => ?_) e
  intro he;rw[SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at he
  rcases hcov he with ha|hb
  ·exact ⟨a,ha,Sym2.mem_mk_left _ _⟩
  ·exact ⟨b,hb,Sym2.mem_mk_right _ _⟩
 have hTne: T.Nonempty:=by
  obtain ⟨t,ht,_⟩ := hcov' s(u0,v0) (by simpa using huv0);exact ⟨t,ht⟩
 have hTpos:=hTne.card_pos;have hEdges:=nfc_bld_edges n T K.edgeFinset hEne hcov'
 have hEdges_eq: ∀ x: Fin n→Bool,
   decide (∃ e∈K.edgeFinset,∀ v∈e,x v=true) =
   decide (∃ u v: Fin n,K.Adj u v∧x u=true∧x v=true):=by
  intro x;rw[decide_eq_decide]
  constructor
  ·rintro ⟨e,he,h⟩
   revert he h
   refine Sym2.ind (fun a b => ?_) e
   intro he h;rw[SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at he;exact ⟨a,b,he,h a (Sym2.mem_mk_left _ _),h b (Sym2.mem_mk_right _ _)⟩
  ·rintro ⟨a,b,hab,ha,hb⟩
   refine ⟨s(a,b),by simpa using hab,?_⟩
   intro w hw;rcases Sym2.mem_iff.1 hw with rfl|rfl <;> assumption
 by_cases hA: A.Nonempty
 ·have hApos:=hA.card_pos;have hBld:=nfc_bld_or (nfc_bld_anyFinset A hA) hEdges
  have hBld' := nfc_bld_congr (H:=graphFun K A)
   (nfc_bld_mono (s' := A.card+K.edgeFinset.card+T.card - 1) hBld (by omega))
   (fun x => by simp only[graphFun,hEdges_eq])
  obtain ⟨D,hfan,_,hcf,hsz⟩:=nfc_bld_circuit hBld'
  exact ⟨D,hfan,hsz,fun x => congrFun hcf x⟩
 ·rw[not_nonempty_iff_eq_empty] at hA
  have hBld' := nfc_bld_congr (H:=graphFun K A)
   (nfc_bld_mono (s' := A.card+K.edgeFinset.card+T.card - 1) hEdges (by rw[hA,Finset.card_empty,Nat.zero_add]))
   (fun x => by rw[hEdges_eq,graphFun,hA];simp)
  obtain ⟨D,hfan,_,hcf,hsz⟩:=nfc_bld_circuit hBld'
  exact ⟨D,hfan,hsz,fun x => congrFun hcf x⟩
end L540.NCC
namespace L540.Main
open Finset
lemma mF {α} {s:Finset α} {p:α→Prop} [DecidablePred p] {a}: a∈s.filter p↔a∈s∧p a := mem_filter
lemma mI {α β} [DecidableEq β] {f:α→β} {s:Finset α} {b}: b∈s.image f↔∃ a∈s,f a=b := mem_image
lemma mN {α} [DecidableEq α] {a b:α} {s:Finset α}: a∈insert b s↔a=b∨a∈s := mem_insert
lemma mS {α} {a b:α}: a∈({b}:Finset α)↔a=b := mem_singleton
lemma mU {α} [DecidableEq α] {a:α} {s t:Finset α}: a∈s∪t↔a∈s∨a∈t := mem_union
lemma mE {α} [DecidableEq α] {a b:α} {s:Finset α}: a∈s.erase b↔a≠b∧a∈s := mem_erase
lemma mR {n m:ℕ}: m∈Finset.range n↔m<n := mem_range
lemma mV {α} [Fintype α] (x:α): x∈(Finset.univ:Finset α) := mem_univ x
lemma mNs {α} [DecidableEq α] (a:α) (s:Finset α): a∈insert a s := mem_insert_self a s
lemma mNo {α} [DecidableEq α] {a b:α} {s:Finset α} (h:a∈s): a∈insert b s := mem_insert_of_mem h
lemma mEo {α} [DecidableEq α] {a b:α} {s:Finset α} (h:a∈s.erase b): a∈s := mem_of_mem_erase h
lemma mC {α} {a:α} {s:Finset α}: a∈(s:Set α)↔a∈s := mem_coe
lemma ascl (n m:ℕ): n+m-n=m := Nat.add_sub_cancel_left n m
lemma lmm {α β} {f:α→β} {l:List α} {b}: b∈l.map f↔∃ a∈l,f a=b := List.mem_map
lemma lcpi {α} [BEq α] [LawfulBEq α] {a:α} {l:List α}: 0<l.count a↔a∈l := List.count_pos_iff
lemma lcz {α} [BEq α] [LawfulBEq α] {a:α} {l:List α}: l.count a=0↔a∉l := List.count_eq_zero
lemma llm {α β} {f:α→β} {l:List α}: (l.map f).length=l.length := by simp
lemma ll2 {α} {l:List α}: l.length=2↔∃ a b,l=[a,b] := List.length_eq_two
lemma lmp {α β γ} {g:β→γ} {f:α→β} {l:List α}: (l.map f).map g=l.map (g∘f) := by simp
lemma lmc {α} {a b:α} {l:List α}: a∈b::l↔a=b∨a∈l := List.mem_cons
lemma lnn {α} {a:α}: a∉([]: List α) := List.not_mem_nil
lemma lcj {α} {a b:α} {l1 l2:List α}: (a::l1=b::l2)=(a=b∧l1=l2) := by simp
lemma lmC {α β} {f:α→β} {a:α} {l:List α}: (a::l).map f=f a::l.map f := rfl
lemma lmN {α β} {f:α→β}: ([]: List α).map f=[] := rfl
lemma laC {α} {p:α→Bool} {a:α} {l:List α}: (a::l).all p=(p a&&l.all p) := rfl
lemma laN {α} {p:α→Bool}: ([]: List α).all p=true := rfl
lemma lyC {α} {p:α→Bool} {a:α} {l:List α}: (a::l).any p=(p a||l.any p) := rfl
lemma lyN {α} {p:α→Bool}: ([]: List α).any p=false := rfl
lemma laT {α} {p:α→Bool} {l:List α}: l.all p=true↔∀ x∈l,p x=true := List.all_eq_true
lemma laF {α} {p:α→Bool} {l:List α}: l.all p=false↔∃ x∈l,p x=false := by simp
lemma lyT {α} {p:α→Bool} {l:List α}: l.any p=true↔∃ x∈l,p x=true := List.any_eq_true
lemma lyF {α} {p:α→Bool} {l:List α}: l.any p=false↔∀ x∈l,p x=false := by simp
lemma pei {α β} {p q:α×β}: p=q↔p.1=q.1∧p.2=q.2 := Prod.ext_iff
lemma osi {α} {a b:α} (h:some a=some b): a=b := Option.some.inj h
lemma boT {a b:Bool}: ((a||b)=true)=(a=true∨b=true) := Bool.or_eq_true a b
lemma baT {a b:Bool}: ((a&&b)=true)=(a=true∧b=true) := Bool.and_eq_true a b
lemma boF {a b:Bool}: (a||b)=false↔a=false∧b=false := by simp
lemma dTe {p:Prop} [Decidable p]: (decide p=true)=p := decide_eq_true_eq
lemma dFn {p:Prop} [Decidable p]: decide p=false↔¬p := decide_eq_false_iff_not
lemma fupn {α β} [DecidableEq α] {a a':α} (h:a'≠a) (b:β) (f:α→β): Function.update f a b a'=f a' := Function.update_of_ne h b f
lemma gdD {α} (l:List α) (d:α) {i:ℕ} (h:l.length ≤ i): l.getD i d=d := List.getD_eq_default l d h
lemma gEs {α} {l:List α} {i:ℕ} {a:α}: l[i]? = some a ↔ ∃ h: i < l.length,l[i]=a := List.getElem?_eq_some_iff
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Library.Subdivision
open L540.Helpers L540.Helpers.PermInputs L540.Helpers.Forest L540.Helpers.Readers L540.Helpers.NotFreeCor
open L540.NCC
def rd (N p a w: ℕ): ℕ := if w < N+p then w else if w=N+p then a else w - 1
def rdel (N p a: ℕ) (gs: List Gate): List Gate :=
 gs.take p ++ (gs.drop (p+1)).map fun g => ⟨g.op,g.inputs.map (rd N p a)⟩
lemma rd_lt (N p a w: ℕ) (hw: w < N+p): rd N p a w=w := by simp[rd,hw]
lemma rd_eq (N p a: ℕ): rd N p a (N+p)=a := by simp[rd]
lemma rd_gt (N p a w: ℕ) (hw: N+p < w): rd N p a w=w - 1:=by
 unfold rd;split_ifs <;> omega
lemma rdel_length (N p a: ℕ) (gs: List Gate) (hp: p < gs.length) :
  (rdel N p a gs).length+1=gs.length := by simp[rdel];omega
lemma rdel_get_lt (N p a: ℕ) (gs: List Gate) (hp: p < gs.length) (j: ℕ) (hj: j < p) :
  (rdel N p a gs)[j]? = gs[j]? := by
 unfold rdel;rw[List.getElem?_append_left (by simp;omega),List.getElem?_take_of_lt hj]
lemma rdel_get_ge (N p a: ℕ) (gs: List Gate) (hp: p < gs.length) (j: ℕ) (hj: p ≤ j) :
  (rdel N p a gs)[j]? =
   (gs[j+1]?).map fun g => (⟨g.op,g.inputs.map (rd N p a)⟩ : Gate):=by
 unfold rdel;rw[List.getElem?_append_right (by simp;omega)];simp only[List.length_take,List.getElem?_map,List.getElem?_drop]
 congr 2;omega
lemma rdel_clean (N p a: ℕ) (gs: List Gate) (hcl: CL N gs) (hp: p < gs.length)
  (ha: a < N+p): CL N (rdel N p a gs):=by
 intro j g hj
 by_cases hjp: j < p
 ·rw[rdel_get_lt N p a gs hp j hjp] at hj;exact hcl j g hj
 ·rw[rdel_get_ge N p a gs hp j (by omega)] at hj;obtain ⟨g0,hg0,rfl⟩:=Option.map_eq_some_iff.1 hj;have hc:=hcl (j+1) g0 hg0
  have hmap: ∀ i,i < N+(j+1) → rd N p a i < N+j:=by
   intro i hi;unfold rd;split_ifs <;> omega
  rcases hc with ⟨h1,i,hi,h2⟩ | ⟨h1,i,k,hi,hk,h2⟩
  ·exact Or.inl ⟨h1,rd N p a i,hmap i hi,by simp[h2]⟩
  ·exact Or.inr ⟨h1,rd N p a i,rd N p a k,hmap i hi,hmap k hk,by simp[h2]⟩
lemma rdel_prefix (N p a: ℕ) (gs: List Gate) (hcl: CL N gs) (hp: p < gs.length)
  (ha: a < N+p) (x: Fin N→Bool) :
  ∀ w: ℕ,w < N+p → vl (rdel N p a gs) x w=vl gs x w:=by
 have hcl' := rdel_clean N p a gs hcl hp ha;intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hw
  by_cases hwN: w < N
  ·rw[vli _ x w hwN,vli _ x w hwN]
  ·obtain ⟨j,rfl⟩ : ∃ j,w=N+j:=⟨w - N,by omega⟩
   have hj: j < p:=by omega
   obtain ⟨g,hg⟩ : ∃ g,gs[j]? = some g:=⟨gs[j],List.getElem?_eq_getElem (by omega)⟩
   have hg' : (rdel N p a gs)[j]? = some g:=by rw[rdel_get_lt N p a gs hp j hj,hg]
   rw[vlg _ hcl' x j g hg',vlg _ hcl x j g hg]
   congr 1;apply List.map_congr_left;intro i hi
   exact ih i ((hcl j g hg).lt i hi) (by have := (hcl j g hg).lt i hi;omega)
lemma rdel_all (N p a: ℕ) (gs: List Gate) (hcl: CL N gs) (hp: p < gs.length)
  (ha: a < N+p) (x: Fin N→Bool) (hx: vl gs x (N+p)=vl gs x a) :
  ∀ w: ℕ,vl (rdel N p a gs) x (rd N p a w)=vl gs x w:=by
 have hcl' := rdel_clean N p a gs hcl hp ha;have hlen:=rdel_length N p a gs hp;intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  rcases lt_trichotomy w (N+p) with hw|rfl|hw
  ·rw[rd_lt N p a w hw];exact rdel_prefix N p a gs hcl hp ha x w hw
  ·rw[rd_eq,hx];exact rdel_prefix N p a gs hcl hp ha x a ha
  ·rw[rd_gt N p a w hw];obtain ⟨j,rfl⟩ : ∃ j,w=N+(j+1):=⟨w - N - 1,by omega⟩
   have e: N+(j+1) - 1=N+j:=by omega
   rw[e]
   by_cases hjl: j+1 < gs.length
   ·obtain ⟨g,hg⟩ : ∃ g,gs[j+1]? = some g:=⟨gs[j+1],List.getElem?_eq_getElem hjl⟩
    have hg' : (rdel N p a gs)[j]? = some ⟨g.op,g.inputs.map (rd N p a)⟩:=by
     rw[rdel_get_ge N p a gs hp j (by omega),hg];rfl
    rw[vlg _ hcl' x j _ hg',vlg _ hcl x (j+1) g hg];simp only[lmp];congr 1;apply List.map_congr_left;intro i hi;exact ih i ((hcl (j+1) g hg).lt i hi)
   ·rw[vl_beyond _ x _ (by omega),vl_beyond _ x _ (by omega)]
def ng0 (g: Gate): Gate :=
 match g.op with
 | GateOp.not => ⟨GateOp.not,g.inputs.take 1⟩
 | _ => g
lemma eval_normGate539 (w: List Bool) (g: Gate) :
  (ng0 g).op.eval ((ng0 g).inputs.map fun i => w.getD i false) =
  g.op.eval (g.inputs.map fun i => w.getD i false):=by
 rcases g with ⟨op,ins⟩
 cases op <;> simp only[ng0]
 cases ins <;> rfl
lemma wng0 (gs: List Gate) (w: List Bool) :
  wF (gs.map ng0) w=wF gs w:=by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only[lmC,wF,List.foldl_cons]
  have hstep: w ++ [(ng0 g).op.eval ((ng0 g).inputs.map fun i => w.getD i false)] =
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by rw[eval_normGate539]
  rw[hstep];exact ih _
def dropStep (n: ℕ) (acc: List (Bool ⊕ ℕ) × List Gate) (g: Gate) :
  List (Bool ⊕ ℕ) × List Gate :=
 let m:=acc.1;let out:=acc.2
 let ins:=g.inputs.map fun i => m.getD i (Sum.inl false)
 let nextW:=n+out.length
 let res: Bool ⊕ (ℕ ⊕ Gate) :=
  match g.op with
  | GateOp.not =>
   match ins with
   | [Sum.inl b] => Sum.inl (!b)
   | [Sum.inr w] => Sum.inr (Sum.inr ⟨GateOp.not,[w]⟩)
   | _ => Sum.inl true
  | GateOp.and =>
   match ins with
   | [] => Sum.inl true
   | [Sum.inl b] => Sum.inl b
   | [Sum.inr w] => Sum.inr (Sum.inl w)
   | [Sum.inl false,_] => Sum.inl false
   | [_,Sum.inl false] => Sum.inl false
   | [Sum.inl true,Sum.inl b] => Sum.inl b
   | [Sum.inl true,Sum.inr w] => Sum.inr (Sum.inl w)
   | [Sum.inr w,Sum.inl true] => Sum.inr (Sum.inl w)
   | [Sum.inr w1,Sum.inr w2] => Sum.inr (Sum.inr ⟨GateOp.and,[w1,w2]⟩)
   | _ => Sum.inl false
  | GateOp.or =>
   match ins with
   | [] => Sum.inl false
   | [Sum.inl b] => Sum.inl b
   | [Sum.inr w] => Sum.inr (Sum.inl w)
   | [Sum.inl true,_] => Sum.inl true
   | [_,Sum.inl true] => Sum.inl true
   | [Sum.inl false,Sum.inl b] => Sum.inl b
   | [Sum.inl false,Sum.inr w] => Sum.inr (Sum.inl w)
   | [Sum.inr w,Sum.inl false] => Sum.inr (Sum.inl w)
   | [Sum.inr w1,Sum.inr w2] => Sum.inr (Sum.inr ⟨GateOp.or,[w1,w2]⟩)
   | _ => Sum.inl false
  | _ => Sum.inl false
 match res with
 | Sum.inl b => (m ++ [Sum.inl b],out)
 | Sum.inr (Sum.inl w) => (m ++ [Sum.inr w],out)
 | Sum.inr (Sum.inr g') => (m ++ [Sum.inr nextW],out ++ [g'])
def evalSym (w: List Bool): Bool ⊕ ℕ → Bool
 | Sum.inl b => b
 | Sum.inr k => w.getD k false
lemma dropStep_struct (n: ℕ) (acc: List (Bool ⊕ ℕ) × List Gate) (g: Gate)
  (hg: g.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧
     (g.op=GateOp.not → g.inputs.length ≤ 1)∧g.inputs.length ≤ 2)
  (hok: ∀ g' ∈ acc.2,g'.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧ g'.inputs.length ≤ 2)
  (hbound: ∀ k w,acc.1.getD k (Sum.inl false)=Sum.inr w → w < n+acc.2.length) :
  (dropStep n acc g).1.length=acc.1.length+1 ∧
  (dropStep n acc g).2.length ≤ acc.2.length+1 ∧
  (∀ g' ∈ (dropStep n acc g).2,
   g'.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
  (∀ k w,(dropStep n acc g).1.getD k (Sum.inl false)=Sum.inr w →
   w < n+(dropStep n acc g).2.length):=by
 have hb_inl: ∀ b: Bool,∀ k w,(acc.1 ++ [Sum.inl b]).getD k (Sum.inl false)=Sum.inr w →
   w < n+acc.2.length:=by
  intro b k w hk
  rcases lt_trichotomy k acc.1.length with hlt|rfl|hgt
  ·rw[List.getD_append _ _ _ _ hlt] at hk;exact hbound k w hk
  ·rw[getD_snoc_eq] at hk;cases hk
  ·rw[gdD _ _ (by simp;omega)] at hk;cases hk
 have hb_inr: ∀ w0: ℕ,w0 < n+acc.2.length→∀ k w,
   (acc.1 ++ [Sum.inr w0]).getD k (Sum.inl false)=Sum.inr w → w < n+acc.2.length:=by
  intro w0 hw0 k w hk
  rcases lt_trichotomy k acc.1.length with hlt|rfl|hgt
  ·rw[List.getD_append _ _ _ _ hlt] at hk;exact hbound k w hk
  ·rw[getD_snoc_eq] at hk;cases hk;exact hw0
  ·rw[gdD _ _ (by simp;omega)] at hk;cases hk
 have hb_gate: ∀ g' : Gate,∀ k w,
   (acc.1 ++ [Sum.inr (n+acc.2.length)]).getD k (Sum.inl false)=Sum.inr w →
   w < n+(acc.2 ++ [g']).length:=by
  intro g' k w hk
  rcases lt_trichotomy k acc.1.length with hlt|rfl|hgt
  ·rw[List.getD_append _ _ _ _ hlt] at hk;have := hbound k w hk;simp;omega
  ·rw[getD_snoc_eq] at hk;cases hk;simp
  ·rw[gdD _ _ (by simp;omega)] at hk;cases hk
 unfold dropStep;obtain ⟨hop,hnot,hlen⟩:=hg;simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at hop
 rcases g with ⟨op,ins⟩
 dsimp only at hop hnot hlen ⊢
 rcases hop with rfl|rfl|rfl
 ·rcases ins with _|⟨a,_|⟨b,_|⟨c,_⟩⟩⟩ <;> try (simp at hlen)
  ·simp only[lmN];exact ⟨by simp,by simp,hok,hb_inl true⟩
  ·simp only[lmC,lmN]
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba => exact ⟨by simp,by simp,hok,hb_inl ba⟩
   | inr wa => exact ⟨by simp,by simp,hok,hb_inr wa (hbound a wa hma)⟩
  ·simp only[lmC,lmN]
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba =>
    cases ba
    ·exact ⟨by simp,by simp,hok,hb_inl false⟩
    ·cases hmb: acc.1.getD b (Sum.inl false) with
     | inl bb => cases bb <;> exact ⟨by simp,by simp,hok,hb_inl _⟩
     | inr wb => exact ⟨by simp,by simp,hok,hb_inr wb (hbound b wb hmb)⟩
   | inr wa =>
    cases hmb: acc.1.getD b (Sum.inl false) with
    | inl bb =>
     cases bb
     ·exact ⟨by simp,by simp,hok,hb_inl false⟩
     ·exact ⟨by simp,by simp,hok,hb_inr wa (hbound a wa hma)⟩
    | inr wb =>
     refine ⟨by simp,by simp,?_,hb_gate _⟩
     intro g' hg';simp at hg';rcases hg' with h' | rfl
     ·exact hok g' h'
     ·simp
 ·rcases ins with _|⟨a,_|⟨b,_|⟨c,_⟩⟩⟩ <;> try (simp at hlen)
  ·simp only[lmN];exact ⟨by simp,by simp,hok,hb_inl false⟩
  ·simp only[lmC,lmN]
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba => exact ⟨by simp,by simp,hok,hb_inl ba⟩
   | inr wa => exact ⟨by simp,by simp,hok,hb_inr wa (hbound a wa hma)⟩
  ·simp only[lmC,lmN]
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba =>
    cases ba
    ·cases hmb: acc.1.getD b (Sum.inl false) with
     | inl bb => cases bb <;> exact ⟨by simp,by simp,hok,hb_inl _⟩
     | inr wb => exact ⟨by simp,by simp,hok,hb_inr wb (hbound b wb hmb)⟩
    ·exact ⟨by simp,by simp,hok,hb_inl true⟩
   | inr wa =>
    cases hmb: acc.1.getD b (Sum.inl false) with
    | inl bb =>
     cases bb
     ·exact ⟨by simp,by simp,hok,hb_inr wa (hbound a wa hma)⟩
     ·exact ⟨by simp,by simp,hok,hb_inl true⟩
    | inr wb =>
     refine ⟨by simp,by simp,?_,hb_gate _⟩
     intro g' hg';simp at hg';rcases hg' with h' | rfl
     ·exact hok g' h'
     ·simp
 ·have h1' := hnot rfl
  rcases ins with _|⟨a,_|⟨b,_⟩⟩ <;> try (simp at h1')
  ·simp only[lmN];exact ⟨by simp,by simp,hok,hb_inl true⟩
  ·simp only[lmC,lmN]
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba => exact ⟨by simp,by simp,hok,hb_inl (!ba)⟩
   | inr wa =>
    refine ⟨by simp,by simp,?_,hb_gate _⟩
    intro g' hg';simp at hg';rcases hg' with h' | rfl
    ·exact hok g' h'
    ·simp
lemma dropStep_val (n: ℕ) (acc: List (Bool ⊕ ℕ) × List Gate) (g: Gate)
  (hg: g.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧
     (g.op=GateOp.not → g.inputs.length ≤ 1)∧g.inputs.length ≤ 2)
  (x: Fin n→Bool) (Wold: List Bool)
  (hlenW: Wold.length=acc.1.length)
  (hmatch: ∀ i,evalSym (wF acc.2 (List.ofFn x)) (acc.1.getD i (Sum.inl false))=Wold.getD i false)
  (hbound: ∀ k w,acc.1.getD k (Sum.inl false)=Sum.inr w → w < n+acc.2.length) :
  ∀ i,evalSym (wF (dropStep n acc g).2 (List.ofFn x))
    ((dropStep n acc g).1.getD i (Sum.inl false)) =
    (Wold ++ [g.op.eval (g.inputs.map fun j => Wold.getD j false)]).getD i false:=by
 let Wnew:=wF acc.2 (List.ofFn x)
 have hWnew_len: Wnew.length=n+acc.2.length:=by simp[Wnew,length_wiresFrom]
 have hkeep: ∀ (g' : Gate) (i: ℕ),i < acc.1.length →
   evalSym (wF (acc.2 ++ [g']) (List.ofFn x)) (acc.1.getD i (Sum.inl false)) =
   Wold.getD i false:=by
  intro g' i hi;rw[←hmatch i]
  cases hm: acc.1.getD i (Sum.inl false) with
  | inl b => rfl
  | inr w =>
   have hw: w < n+acc.2.length:=hbound i w hm;simp only[evalSym,wiresFrom_append];exact List.getD_append _ _ _ _ (by rw[hWnew_len];exact hw)
 have hcheck_inl: ∀ (b: Bool),
   g.op.eval (g.inputs.map fun j => Wold.getD j false)=b →
   ∀ i,evalSym Wnew ((acc.1 ++ [Sum.inl b]).getD i (Sum.inl false)) =
    (Wold ++ [g.op.eval (g.inputs.map fun j => Wold.getD j false)]).getD i false:=by
  intro b hb i;rw[hb]
  rcases lt_trichotomy i acc.1.length with hi|rfl|hi
  ·rw[List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (by omega)];exact hmatch i
  ·rw[getD_snoc_eq,←hlenW,getD_snoc_eq];rfl
  ·rw[gdD _ _ (by simp;omega),gdD _ _ (by simp;omega)];rfl
 have hcheck_inr: ∀ (w0: ℕ),
   g.op.eval (g.inputs.map fun j => Wold.getD j false)=Wnew.getD w0 false →
   ∀ i,evalSym Wnew ((acc.1 ++ [Sum.inr w0]).getD i (Sum.inl false)) =
    (Wold ++ [g.op.eval (g.inputs.map fun j => Wold.getD j false)]).getD i false:=by
  intro w0 hb i;rw[hb]
  rcases lt_trichotomy i acc.1.length with hi|rfl|hi
  ·rw[List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (by omega)];exact hmatch i
  ·rw[getD_snoc_eq,←hlenW,getD_snoc_eq];rfl
  ·rw[gdD _ _ (by simp;omega),gdD _ _ (by simp;omega)];rfl
 have hcheck_gate: ∀ (g' : Gate),
   g.op.eval (g.inputs.map fun j => Wold.getD j false) =
    g'.op.eval (g'.inputs.map fun j => Wnew.getD j false) →
   ∀ i,evalSym (wF (acc.2 ++ [g']) (List.ofFn x))
     ((acc.1 ++ [Sum.inr (n+acc.2.length)]).getD i (Sum.inl false)) =
    (Wold ++ [g.op.eval (g.inputs.map fun j => Wold.getD j false)]).getD i false:=by
  intro g' hb i
  rcases lt_trichotomy i acc.1.length with hi|rfl|hi
  ·rw[List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (by omega)];exact hkeep g' i hi
  ·rw[getD_snoc_eq,←hlenW,getD_snoc_eq,hb];simp only[evalSym,wiresFrom_append]
   change (Wnew ++ [g'.op.eval (g'.inputs.map fun j => Wnew.getD j false)]).getD (n+acc.2.length) false=_
   rw[←hWnew_len,getD_snoc_eq]
  ·rw[gdD _ _ (by simp;omega),gdD _ _ (by simp;omega)];rfl
 unfold dropStep;obtain ⟨hop,hnot,hlen⟩:=hg;simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at hop
 rcases g with ⟨op,ins⟩
 dsimp only at hop hnot hlen ⊢
 rcases hop with rfl|rfl|rfl
 ·rcases ins with _|⟨a,_|⟨b,_|⟨c,_⟩⟩⟩ <;> try (simp at hlen)
  ·simp only[lmN];exact hcheck_inl true rfl
  ·simp only[lmC,lmN];have ha := hmatch a
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba => rw[hma] at ha;dsimp[evalSym] at ha;exact hcheck_inl ba (by simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,Bool.and_true,←ha])
   | inr wa => rw[hma] at ha;dsimp[evalSym] at ha;exact hcheck_inr wa (by simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,Bool.and_true,←ha,Wnew])
  ·simp only[lmC,lmN];have ha := hmatch a;have hb := hmatch b
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba =>
    rw[hma] at ha;dsimp[evalSym] at ha
    cases ba
    ·exact hcheck_inl false (by simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,←ha,Bool.false_and])
    ·cases hmb: acc.1.getD b (Sum.inl false) with
     | inl bb => rw[hmb] at hb;dsimp[evalSym] at hb;cases bb <;> exact hcheck_inl _ (by simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,←ha,←hb,Bool.true_and,Bool.and_true])
     | inr wb => rw[hmb] at hb;dsimp[evalSym] at hb;exact hcheck_inr wb (by simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,←ha,←hb,Bool.true_and,Bool.and_true,Wnew])
   | inr wa =>
    rw[hma] at ha;dsimp[evalSym] at ha
    cases hmb: acc.1.getD b (Sum.inl false) with
    | inl bb =>
     rw[hmb] at hb;dsimp[evalSym] at hb
     cases bb
     ·exact hcheck_inl false (by simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,←hb,Bool.false_and,Bool.and_false])
     ·exact hcheck_inr wa (by simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,←ha,←hb,Bool.and_true,Wnew])
    | inr wb =>
     rw[hmb] at hb;dsimp[evalSym] at hb;exact hcheck_gate ⟨GateOp.and,[wa,wb]⟩ (by simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,←ha,←hb,Wnew])
 ·rcases ins with _|⟨a,_|⟨b,_|⟨c,_⟩⟩⟩ <;> try (simp at hlen)
  ·simp only[lmN];exact hcheck_inl false rfl
  ·simp only[lmC,lmN];have ha := hmatch a
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba => rw[hma] at ha;dsimp[evalSym] at ha;exact hcheck_inl ba (by simp only[GateOp.eval,lmC,lmN,lyC,lyN,id_eq,Bool.or_false,←ha])
   | inr wa => rw[hma] at ha;dsimp[evalSym] at ha;exact hcheck_inr wa (by simp only[GateOp.eval,lmC,lmN,lyC,lyN,id_eq,Bool.or_false,←ha,Wnew])
  ·simp only[lmC,lmN];have ha := hmatch a;have hb := hmatch b
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba =>
    rw[hma] at ha;dsimp[evalSym] at ha
    cases ba
    ·cases hmb: acc.1.getD b (Sum.inl false) with
     | inl bb => rw[hmb] at hb;dsimp[evalSym] at hb;cases bb <;> exact hcheck_inl _ (by simp only[GateOp.eval,lmC,lmN,lyC,lyN,id_eq,←ha,←hb,Bool.false_or,Bool.or_false])
     | inr wb => rw[hmb] at hb;dsimp[evalSym] at hb;exact hcheck_inr wb (by simp only[GateOp.eval,lmC,lmN,lyC,lyN,id_eq,←ha,←hb,Bool.false_or,Bool.or_false,Wnew])
    ·exact hcheck_inl true (by simp only[GateOp.eval,lmC,lmN,lyC,lyN,id_eq,←ha,Bool.true_or])
   | inr wa =>
    rw[hma] at ha;dsimp[evalSym] at ha
    cases hmb: acc.1.getD b (Sum.inl false) with
    | inl bb =>
     rw[hmb] at hb;dsimp[evalSym] at hb
     cases bb
     ·exact hcheck_inr wa (by simp only[GateOp.eval,lmC,lmN,lyC,lyN,id_eq,←ha,←hb,Bool.or_false,Wnew])
     ·exact hcheck_inl true (by simp only[GateOp.eval,lmC,lmN,lyC,lyN,id_eq,←hb,Bool.true_or,Bool.or_true])
    | inr wb =>
     rw[hmb] at hb;dsimp[evalSym] at hb;exact hcheck_gate ⟨GateOp.or,[wa,wb]⟩ (by simp only[GateOp.eval,lmC,lmN,lyC,lyN,id_eq,←ha,←hb,Wnew])
 ·have h1' := hnot rfl
  rcases ins with _|⟨a,_|⟨b,_⟩⟩ <;> try (simp at h1')
  ·simp only[lmN];exact hcheck_inl true rfl
  ·simp only[lmC,lmN];have ha := hmatch a
   cases hma: acc.1.getD a (Sum.inl false) with
   | inl ba => rw[hma] at ha;dsimp[evalSym] at ha;exact hcheck_inl (!ba) (by simp only[GateOp.eval,lmC,lmN,←ha];rfl)
   | inr wa => rw[hma] at ha;dsimp[evalSym] at ha;exact hcheck_gate ⟨GateOp.not,[wa]⟩ (by simp only[GateOp.eval,lmC,lmN,←ha,Wnew])
lemma dropStep_strict (n: ℕ) (acc: List (Bool ⊕ ℕ) × List Gate) (g: Gate)
  (hg: g.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧
     (g.op=GateOp.not → g.inputs.length ≤ 1)∧g.inputs.length ≤ 2)
  (hbad: ¬ ((g.op=GateOp.not ∧ ∃ a < acc.1.length,g.inputs=[a]) ∨
   ((g.op=GateOp.and∨g.op=GateOp.or) ∧
    ∃ a b,a < acc.1.length∧b < acc.1.length∧g.inputs=[a,b]))) :
  (dropStep n acc g).2.length=acc.2.length:=by
 unfold dropStep;obtain ⟨hop,hnot,hlen⟩:=hg;simp only[Set.mem_insert_iff,Set.mem_singleton_iff] at hop
 rcases g with ⟨op,ins⟩
 dsimp only at hop hnot hlen hbad ⊢
 rcases hop with rfl|rfl|rfl
 ·rcases ins with _|⟨a,_|⟨b,_|⟨c,_⟩⟩⟩ <;> try (simp at hlen)
  ·rfl
  ·simp only[lmC,lmN];cases acc.1.getD a (Sum.inl false) <;> rfl
  ·simp only[lmC,lmN]
   have hor: ¬ (a < acc.1.length∧b < acc.1.length):=fun ⟨ha,hb⟩ =>
    hbad (Or.inr ⟨Or.inl rfl,a,b,ha,hb,rfl⟩)
   by_cases ha: a < acc.1.length
   ·have hb: acc.1.length ≤ b:=by omega
    rw[gdD acc.1 (Sum.inl false) hb]
    cases acc.1.getD a (Sum.inl false) with
    | inl ba => cases ba <;> rfl
    | inr wa => rfl
   ·have ha' : acc.1.length ≤ a:=by omega
    rw[gdD acc.1 (Sum.inl false) ha']
 ·rcases ins with _|⟨a,_|⟨b,_|⟨c,_⟩⟩⟩ <;> try (simp at hlen)
  ·rfl
  ·simp only[lmC,lmN];cases acc.1.getD a (Sum.inl false) <;> rfl
  ·simp only[lmC,lmN]
   have hor: ¬ (a < acc.1.length∧b < acc.1.length):=fun ⟨ha,hb⟩ =>
    hbad (Or.inr ⟨Or.inr rfl,a,b,ha,hb,rfl⟩)
   by_cases ha: a < acc.1.length
   ·have hb: acc.1.length ≤ b:=by omega
    rw[gdD acc.1 (Sum.inl false) hb]
    cases acc.1.getD a (Sum.inl false) with
    | inl ba => cases ba <;> rfl
    | inr wa => rfl
   ·have ha' : acc.1.length ≤ a:=by omega
    rw[gdD acc.1 (Sum.inl false) ha']
    cases acc.1.getD b (Sum.inl false) with
    | inl bb => cases bb <;> rfl
    | inr wb => rfl
 ·have h1' := hnot rfl
  rcases ins with _|⟨a,_|⟨b,_⟩⟩ <;> try (simp at h1')
  ·rfl
  ·simp only[lmC,lmN]
   have ha: acc.1.length ≤ a:=by
    by_contra hlt;exact hbad (Or.inl ⟨rfl,a,by omega,rfl⟩)
   rw[gdD acc.1 (Sum.inl false) ha]
lemma dropFold_props (n: ℕ) (l: List Gate) :
  ∀ (acc: List (Bool ⊕ ℕ) × List Gate),
   (∀ g∈l,g.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧
    (g.op=GateOp.not → g.inputs.length ≤ 1)∧g.inputs.length ≤ 2) →
   (∀ g' ∈ acc.2,g'.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧ g'.inputs.length ≤ 2) →
   (∀ k w,acc.1.getD k (Sum.inl false)=Sum.inr w → w < n+acc.2.length) →
   (l.foldl (dropStep n) acc).1.length=acc.1.length+l.length ∧
   (l.foldl (dropStep n) acc).2.length ≤ acc.2.length+l.length ∧
   (∀ g' ∈ (l.foldl (dropStep n) acc).2,
    g'.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
   (∀ k w,(l.foldl (dropStep n) acc).1.getD k (Sum.inl false)=Sum.inr w →
    w < n+(l.foldl (dropStep n) acc).2.length) ∧
   (∀ x: Fin n→Bool,∀ Wold: List Bool,Wold.length=acc.1.length →
    (∀ i,evalSym (wF acc.2 (List.ofFn x)) (acc.1.getD i (Sum.inl false))=Wold.getD i false) →
    ∀ i,evalSym (wF (l.foldl (dropStep n) acc).2 (List.ofFn x))
     ((l.foldl (dropStep n) acc).1.getD i (Sum.inl false))=(wF l Wold).getD i false):=by
 induction l with
 | nil =>
  intro acc _ hok hb
  exact ⟨by simp,by simp,hok,hb,fun _ _ _ hm i => hm i⟩
 | cons g l ih =>
  intro acc hgl hok hb;have hg:=hgl g (by simp);obtain ⟨hl1,hl2,hok1,hb1⟩:=dropStep_struct n acc g hg hok hb
  obtain ⟨fl1,fl2,fok,fb,fval⟩:=ih (dropStep n acc g) (fun g' hg' => hgl g' (by simp[hg'])) hok1 hb1
  refine ⟨by simp only[List.foldl_cons,fl1,hl1,List.length_cons];omega,
      by simp only[List.foldl_cons,List.length_cons];omega,
      fok,fb,?_⟩
  intro x Wold hWlen hmatch i;simp only[List.foldl_cons]
  exact fval x (Wold ++ [g.op.eval (g.inputs.map fun j => Wold.getD j false)])
   (by simp[hl1,hWlen]) (dropStep_val n acc g hg x Wold hWlen hmatch hb) i
lemma mnc {n: ℕ} (C: Circuit) (hmin: IsMinimalCircuit n C)
  (hnc: ∃ x y: Fin n→Bool,circuitFun n C x≠circuitFun n C y) :
  CL n (C.gates.map ng0):=by
 let gs:=C.gates.map ng0
 have hgs_ok: ∀ g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧
   (g.op=GateOp.not → g.inputs.length ≤ 1)∧g.inputs.length ≤ 2:=by
  intro g hg;obtain ⟨g0,hg0,rfl⟩:=lmm.mp hg;obtain ⟨hop,hlen⟩:=hmin.1 g0 hg0
  rcases g0 with ⟨op,ins⟩
  dsimp only at hop hlen
  cases op with
  | not => exact ⟨by simp[ng0],fun _ => by simp[ng0],by simp[ng0]⟩
  | and => exact ⟨hop,fun h => by simp[ng0] at h,hlen⟩
  | or => exact ⟨hop,fun h => by simp[ng0] at h,hlen⟩
  | mod _ => simp at hop
  | maj => simp at hop
 have hcf_gs: ∀ x,vl gs x C.output=circuitFun n C x:=by
  intro x;unfold vl circuitFun Circuit.eval;rw[wng0];rfl
 by_contra hnotcl
 unfold CL at hnotcl
 push Not at hnotcl
 obtain ⟨j0,g0,hj0,hbad0⟩:=hnotcl;have hj0_lt: j0 < gs.length:=(gEs.1 hj0).1
 have hsplit: gs=gs.take j0 ++ g0 :: gs.drop (j0+1):=by
  have h1:=List.take_append_drop j0 gs
  have h2: gs.drop j0=g0 :: gs.drop (j0+1):=by
   have hg0: gs[j0]=g0:=by
    have:=List.getElem?_eq_getElem hj0_lt;rw[hj0] at this;exact osi this.symm
   rw[←hg0];exact List.drop_eq_getElem_cons hj0_lt
  rw[h2] at h1;exact h1.symm
 let initM: List (Bool ⊕ ℕ):=List.ofFn fun i: Fin n => Sum.inr i.val
 have hinit_b: ∀ k w,initM.getD k (Sum.inl false)=Sum.inr w → w < n+([]: List Gate).length:=by
  intro k w hk
  by_cases hkn: k < n
  ·simp only[initM,List.getD,List.getElem?_ofFn,hkn,↓reduceDIte,Option.getD_some,Sum.inr.injEq] at hk;subst hk;simp;exact hkn
  ·rw[gdD _ _ (by simp[initM];omega)] at hk;cases hk
 have hinit_m: ∀ x: Fin n→Bool,∀ i,
   evalSym (wF [] (List.ofFn x)) (initM.getD i (Sum.inl false))=(List.ofFn x).getD i false:=by
  intro x i
  by_cases hin: i < n
  ·simp[initM,evalSym,wF,List.getD,hin]
  ·rw[gdD initM _ (by simp[initM];omega),
    gdD (List.ofFn x) _ (by simp;omega)];rfl
 have hpre_ok: ∀ g∈gs.take j0,g.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧
   (g.op=GateOp.not → g.inputs.length ≤ 1)∧g.inputs.length ≤ 2 := fun g hg =>
  hgs_ok g (List.mem_of_mem_take hg)
 have hpost_ok: ∀ g∈gs.drop (j0+1),g.op∈({GateOp.and,GateOp.or,GateOp.not}: Set GateOp) ∧
   (g.op=GateOp.not → g.inputs.length ≤ 1)∧g.inputs.length ≤ 2 := fun g hg =>
  hgs_ok g (List.mem_of_mem_drop hg)
 have hg0_ok:=hgs_ok g0 (List.mem_of_getElem? hj0);let acc1:=(gs.take j0).foldl (dropStep n) (initM,[]);obtain ⟨h1_len1,h1_len2,h1_ok,h1_b,_⟩:=dropFold_props n (gs.take j0) (initM,[]) hpre_ok (by simp) hinit_b
 have hacc1_len: acc1.1.length=n+j0:=by simp[acc1,h1_len1,initM];omega
 let acc2:=dropStep n acc1 g0;obtain ⟨_,_,h2_ok,h2_b⟩:=dropStep_struct n acc1 g0 hg0_ok h1_ok h1_b
 have h2_strict: acc2.2.length=acc1.2.length :=
  dropStep_strict n acc1 g0 hg0_ok (by rw[hacc1_len];exact hbad0)
 let acc3:=(gs.drop (j0+1)).foldl (dropStep n) acc2;obtain ⟨_,h3_len2,h3_ok,_,_⟩:=dropFold_props n (gs.drop (j0+1)) acc2 hpost_ok h2_ok h2_b
 have hrun_eq: gs.foldl (dropStep n) (initM,[])=acc3:=by
  conv_lhs => rw[hsplit]
  rw[List.foldl_append,List.foldl_cons]
 obtain ⟨_,_,_,_,hall_val⟩:=dropFold_props n gs (initM,[]) hgs_ok (by simp) hinit_b
 have hval_out: ∀ x: Fin n→Bool,evalSym (wF acc3.2 (List.ofFn x))
   (acc3.1.getD C.output (Sum.inl false))=circuitFun n C x:=by
  intro x;rw[←hcf_gs x,←hrun_eq];exact hall_val x (List.ofFn x) (by simp[initM]) (hinit_m x) C.output
 have hsz_lt: acc3.2.length < C.size:=by
  have hgs_len: gs.length=C.gates.length:=by simp[gs]
  have h1' : acc1.2.length ≤ j0:=by
   have htk: (gs.take j0).length=j0:=by simp;omega
   simpa [acc1,htk] using h1_len2
  have h3' : acc3.2.length ≤ acc2.2.length+(gs.drop (j0+1)).length:=h3_len2
  have hdp: (gs.drop (j0+1)).length=gs.length - (j0+1):=by simp
  change acc3.2.length < C.gates.length;omega
 cases hout: acc3.1.getD C.output (Sum.inl false) with
 | inl b =>
  obtain ⟨x,y,hxy⟩:=hnc;apply hxy;have hx:=hval_out x;have hy:=hval_out y;rw[hout] at hx hy;rw[←hx,←hy];rfl
 | inr o' =>
  let D: Circuit:=⟨acc3.2,o'⟩
  have hD_fan: FanInTwo D:=fun g hg => h3_ok g hg
  have hD_cf: circuitFun n D=circuitFun n C:=by
   funext x
   have hv:=hval_out x;rw[hout] at hv;exact hv
  have hle:=hmin.2 D hD_fan hD_cf;change C.gates.length ≤ acc3.2.length at hle;change acc3.2.length < C.gates.length at hsz_lt;omega
lemma read_dep_direct {n: ℕ} {f: (Fin n→Bool)→Bool} {gs: List Gate} {o: ℕ}
  (hev: ∀ x: Fin n→Bool,vl gs x o=f x) (l: Fin n)
  (hdep: ∃ x: Fin n→Bool,f (Function.update x l (!x l))≠f x)
  (ho: o≠l.val) :
  ∃ p: ℕ,Reads gs p l.val:=by
 by_contra hno
 push Not at hno
 obtain ⟨x,hx⟩:=hdep;apply hx;rw[←hev,←hev];let x' := Function.update x l (!x l)
 have hagree: ∀ (gsl: List Gate) (w1 w2: List Bool),
   w1.length=w2.length →
   (∀ i < w1.length,i≠l.val → w1.getD i false=w2.getD i false) →
   (∀ g∈gsl,l.val∉g.inputs) →
   ∀ i,i≠l.val→(wF gsl w1).getD i false=(wF gsl w2).getD i false:=by
  intro gsl
  induction gsl with
  | nil =>
   intro w1 w2 hlen hagr _ i hi;simp only[wF,List.foldl_nil]
   by_cases hilt: i < w1.length
   ·exact hagr i hilt hi
   ·rw[gdD w1 _ (by omega),gdD w2 _ (by omega)]
  | cons g gsl ih =>
   intro w1 w2 hlen hagr hnot i hi;have hgn: l.val∉g.inputs:=hnot g (by simp)
   have hev_g: g.op.eval (g.inputs.map fun a => w1.getD a false) =
     g.op.eval (g.inputs.map fun a => w2.getD a false):=by
    congr 1;apply List.map_congr_left;intro a ha
    have hal: a≠l.val:=fun e => hgn (e ▸ ha)
    by_cases halt: a < w1.length
    ·exact hagr a halt hal
    ·rw[gdD w1 _ (by omega),gdD w2 _ (by omega)]
   simp only[wF,List.foldl_cons]
   apply ih _ _ (by simp[hlen]) _ (fun g' hg' => hnot g' (by simp[hg'])) i hi
   intro k hk hkl
   by_cases hk1: k < w1.length
   ·rw[List.getD_append _ _ _ _ hk1,List.getD_append _ _ _ _ (by omega)];exact hagr k hk1 hkl
   ·have hke: k=w1.length:=by simp at hk;omega
    subst hke;rw[getD_snoc_eq,hlen,getD_snoc_eq,hev_g]
 have hno_mem: ∀ g∈gs,l.val∉g.inputs:=by
  intro g hg hm;obtain ⟨j,hj,rfl⟩:=List.getElem_of_mem hg;exact hno j ⟨gs[j],List.getElem?_eq_getElem hj,hm⟩
 apply hagree gs (List.ofFn x') (List.ofFn x) (by simp) _ hno_mem o ho;intro i hi hil;simp only[List.length_ofFn] at hi;simp only[List.getD,List.getElem?_ofFn,hi,↓reduceDIte,Option.getD_some,x']
 rw[fupn (fun e => hil (congrArg Fin.val e))]
def li1 (jl j' : ℕ): ℕ := if j' < jl then j' else j' + 1
def lw1 (n jl w: ℕ): ℕ := if w < n+jl then w else w+1
lemma li1i (jl: ℕ): Function.Injective (li1 jl):=by
 intro a b h;unfold li1 at h;split_ifs at h <;> omega
lemma lw1j (n jl: ℕ): Function.Injective (lw1 n jl):=by
 intro a b h;unfold lw1 at h;split_ifs at h <;> omega
lemma li1n (jl j' : ℕ): li1 jl j' ≠ jl:=by
 unfold li1;split_ifs <;> omega
lemma lw1n (n jl w: ℕ): lw1 n jl w≠n+jl:=by
 unfold lw1;split_ifs <;> omega
lemma lw1g (n jl j' : ℕ): lw1 n jl (n + j')=n+li1 jl j' := by
 unfold lw1 li1;split_ifs <;> omega
lemma lw1i (n jl i: ℕ) (hi: i < n): lw1 n jl i=i:=by
 unfold lw1;split_ifs <;> omega
lemma rd_liftW (n jl wl w: ℕ): rd n jl wl (lw1 n jl w)=w:=by
 unfold rd lw1;split_ifs <;> omega
lemma lw1r (n jl wl u: ℕ) (hu: u≠n+jl): lw1 n jl (rd n jl wl u)=u:=by
 unfold lw1 rd;split_ifs <;> omega
lemma list_map_id_on {α : Type*} {f: α → α} (l: List α) (h: ∀ x∈l,f x=x) :
  l.map f=l:=by
 induction l with
 | nil => rfl
 | cons a t ih => simp[h a (by simp),ih (fun x hx => h x (by simp[hx]))]
lemma r1l {n jl: ℕ} (wl: ℕ) (C: Circuit) (hrb: ReadsBack n C)
  (hj_l: jl < C.gates.length) (j' : ℕ) (hj' : j' < C.gates.length - 1) :
  let C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩
  (gateAt C' j').op=(gateAt C (li1 jl j')).op ∧
  (gateAt C' j').inputs=(gateAt C (li1 jl j')).inputs.map (rd n jl wl):=by
 dsimp only
 set C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩
 by_cases hlt: j' < jl
 ·have hget:=rdel_get_lt n jl wl C.gates hj_l j' hlt
  have hj'C: j' < C.gates.length:=by omega
  have h1: gateAt C' j' = C.gates[j']:=by
   simp only[gateAt,List.getD,C'];rw[hget,List.getElem?_eq_getElem hj'C];rfl
  have h2: gateAt C (li1 jl j')=C.gates[j']:=by
   simp[gateAt,List.getD,li1,hlt,hj'C]
  rw[h1,h2]
  refine ⟨rfl,?_⟩
  symm
  exact list_map_id_on _ fun i hi => by
   have hilt: i < n + j' := hrb j' hj'C i (by rw[show gateAt C j' = C.gates[j'] by simp[gateAt,List.getD,hj'C]];exact hi);exact rd_lt n jl wl i (by omega)
 ·have hge: jl ≤ j' := by omega
  have hget:=rdel_get_ge n jl wl C.gates hj_l j' hge
  have hj'1: j' + 1 < C.gates.length:=by omega
  have h1: gateAt C' j' = ⟨(C.gates[j' + 1]).op,(C.gates[j' + 1]).inputs.map (rd n jl wl)⟩:=by
   simp only[gateAt,List.getD,C'];rw[hget,List.getElem?_eq_getElem hj'1];rfl
  have h2: gateAt C (li1 jl j')=C.gates[j' + 1]:=by
   simp[gateAt,List.getD,li1,hlt,hj'1]
  rw[h1,h2];exact ⟨rfl,rfl⟩
lemma vluu {n: ℕ} (gs: List Gate) (o: ℕ) (l: Fin n)
  (hno: ∀ g∈gs,l.val∉g.inputs) (ho: o≠l.val) (x: Fin n→Bool) (b: Bool) :
  vl gs (Function.update x l b) o=vl gs x o:=by
 have hagree: ∀ (gsl: List Gate) (w1 w2: List Bool),
   w1.length=w2.length →
   (∀ i < w1.length,i≠l.val → w1.getD i false=w2.getD i false) →
   (∀ g∈gsl,l.val∉g.inputs) →
   ∀ i,i≠l.val→(wF gsl w1).getD i false=(wF gsl w2).getD i false:=by
  intro gsl
  induction gsl with
  | nil =>
   intro w1 w2 hlen hagr _ i hi;simp only[wF,List.foldl_nil]
   by_cases hilt: i < w1.length
   ·exact hagr i hilt hi
   ·rw[gdD w1 _ (by omega),gdD w2 _ (by omega)]
  | cons g gsl ih =>
   intro w1 w2 hlen hagr hnot i hi;have hgn: l.val∉g.inputs:=hnot g (by simp)
   have hev_g: g.op.eval (g.inputs.map fun a => w1.getD a false) =
     g.op.eval (g.inputs.map fun a => w2.getD a false):=by
    congr 1;apply List.map_congr_left;intro a ha
    have hal: a≠l.val:=fun e => hgn (e ▸ ha)
    by_cases halt: a < w1.length
    ·exact hagr a halt hal
    ·rw[gdD w1 _ (by omega),gdD w2 _ (by omega)]
   simp only[wF,List.foldl_cons]
   apply ih _ _ (by simp[hlen]) _ (fun g' hg' => hnot g' (by simp[hg'])) i hi
   intro k hk hkl
   by_cases hk1: k < w1.length
   ·rw[List.getD_append _ _ _ _ hk1,List.getD_append _ _ _ _ (by omega)];exact hagr k hk1 hkl
   ·have hke: k=w1.length:=by simp at hk;omega
    subst hke;rw[getD_snoc_eq,hlen,getD_snoc_eq,hev_g]
 apply hagree gs (List.ofFn (Function.update x l b)) (List.ofFn x) (by simp) _ hno o ho;intro i hi hil;simp only[List.length_ofFn] at hi;simp only[List.getD,List.getElem?_ofFn,hi,↓reduceDIte,Option.getD_some]
 rw[fupn (fun e => hil (congrArg Fin.val e))]
lemma r1in {n jl: ℕ} (wl: ℕ) (C: Circuit) (hrb: ReadsBack n C)
  (hj_l: jl < C.gates.length) (j' : ℕ) (hj' : j' < C.gates.length - 1)
  (hno: n+jl∉(gateAt C (li1 jl j')).inputs) :
  let C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩
  (gateAt C (li1 jl j')).inputs=(gateAt C' j').inputs.map (lw1 n jl):=by
 dsimp only
 set C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩;have h:=(r1l wl C hrb hj_l j' hj').2;rw[h,lmp]
 symm
 exact list_map_id_on _ fun i hi => lw1r n jl wl i (fun e => hno (e ▸ hi))
lemma r1cnt {n jl: ℕ} (wl: ℕ) (C: Circuit) (hrb: ReadsBack n C)
  (hj_l: jl < C.gates.length) (j' : ℕ) (hj' : j' < C.gates.length - 1)
  (hno: n+jl∉(gateAt C (li1 jl j')).inputs) (w: ℕ) :
  let C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩
  (gateAt C (li1 jl j')).inputs.count (lw1 n jl w)=(gateAt C' j').inputs.count w:=by
 dsimp only
 set C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩;rw[r1in wl C hrb hj_l j' hj' hno];exact List.count_map_of_injective _ _ (lw1j n jl) w
lemma ot1u {n jl wl: ℕ} (C: Circuit) (hrb: ReadsBack n C)
  (hj_l: jl < C.gates.length)
  {G' L' : Finset ℕ} {ρ' : ℕ}
  (ht: IsOrTree n ⟨rdel n jl wl C.gates,rd n jl wl C.output⟩ G' L' ρ')
  (hGlt: ∀ j' ∈ G',j' < C.gates.length - 1)
  (hno: ∀ j' ∈ G',n+jl∉(gateAt C (li1 jl j')).inputs) :
  IsOrTree n C (G'.image (li1 jl)) (L'.image (lw1 n jl)) (lw1 n jl ρ'):=by
 set C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩
 have hreads: ∀ w,readsIn C (G'.image (li1 jl)) (lw1 n jl w)=readsIn C' G' w:=by
  intro w;unfold readsIn
  rw[sum_image (fun a _ b _ h => li1i jl h)]
  apply sum_congr rfl;intro j' hj';exact r1cnt wl C hrb hj_l j' (hGlt j' hj') (hno j' hj') w
 refine ⟨?_,?_,?_,?_⟩
 ·intro j hj;obtain ⟨j',hj',rfl⟩:=mI.mp hj;obtain ⟨hop,hlen,hin⟩:=ht.1 j' hj';have hlif:=r1l wl C hrb hj_l j' (hGlt j' hj');have hinp:=r1in wl C hrb hj_l j' (hGlt j' hj') (hno j' hj')
  refine ⟨by rw[←hlif.1,hop],by rw[hinp,llm,hlen],?_⟩
  intro i hi;rw[hinp] at hi;obtain ⟨i',hi',rfl⟩:=lmm.mp hi
  rcases hin i' hi' with hiL|⟨hni,hiG⟩
  ·exact Or.inl (mI.mpr ⟨i',hiL,rfl⟩)
  ·right
   have hi_eq: i' = n+(i' - n):=by omega
   rw[hi_eq,lw1g];exact ⟨Nat.le_add_right _ _,by simpa using mI.mpr ⟨i' - n,hiG,rfl⟩⟩
 ·intro w hw;obtain ⟨w',hw',rfl⟩:=mI.mp hw;obtain ⟨hnotG,hr⟩:=ht.2.1 w' hw'
  refine ⟨?_,?_⟩
  ·rintro ⟨hnl,hm⟩
   obtain ⟨j',hj',hjeq⟩:=mI.mp hm
   have heq: lw1 n jl w' = lw1 n jl (n + j'):=by rw[lw1g];omega
   have hwj:=lw1j n jl heq;exact hnotG ⟨by omega,by simpa [hwj] using hj'⟩
  ·rw[hreads w',hr]
   by_cases he: w' = ρ'
   ·simp[he]
   ·have hne: lw1 n jl w' ≠ lw1 n jl ρ' := fun h => he (lw1j n jl h)
    simp[he,hne]
 ·intro j hj;obtain ⟨j',hj',rfl⟩:=mI.mp hj;rw[←lw1g,hreads (n + j'),ht.2.2.1 j' hj']
  by_cases he: n + j' = ρ'
  ·simp[he]
  ·have hne: lw1 n jl (n + j')≠lw1 n jl ρ' := fun h => he (lw1j n jl h)
   simp[he,hne]
 ·by_cases hG: G' = ∅
  ·have hGim: G'.image (li1 jl) = ∅ := by simp[hG]
   have hrt:=ht.2.2.2;simp only[hG,↓reduceIte] at hrt;simp only[hGim,↓reduceIte,hrt,Finset.image_singleton]
  ·have hGim: G'.image (li1 jl) ≠ ∅ := by
    intro he;exact hG (Finset.image_eq_empty.mp he)
   have hrt:=ht.2.2.2;simp only[hG,↓reduceIte] at hrt;obtain ⟨j',hj',rfl⟩:=hrt;simp only[hGim,↓reduceIte];exact ⟨li1 jl j',mI.mpr ⟨j',hj',rfl⟩,lw1g n jl j'⟩
lemma ot1ir {n jl wl: ℕ} (C: Circuit) (hrb: ReadsBack n C)
  (hj_l: jl < C.gates.length) (hw_l: wl < n+jl) (leaf: ℕ) (hleaf_lt: leaf < n+jl) (hwne: wl≠leaf)
  (hjlo: (gateAt C jl).op=GateOp.or)
  (hjli: (gateAt C jl).inputs=[leaf,wl]∨(gateAt C jl).inputs=[wl,leaf])
  {G' L' : Finset ℕ}
  (ht: IsOrTree n ⟨rdel n jl wl C.gates,rd n jl wl C.output⟩ G' L' wl)
  (hGlt: ∀ j' ∈ G',j' < C.gates.length - 1)
  (hno: ∀ j' ∈ G',n+jl∉(gateAt C (li1 jl j')).inputs)
  (hlnotL: leaf ∉ L') (hlnotG: ∀ j' ∈ G',n + j' ≠ leaf) :
  IsOrTree n C (insert jl (G'.image (li1 jl))) (insert leaf (L'.image (lw1 n jl))) (n+jl):=by
 set C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩;set G:=insert jl (G'.image (li1 jl));set L:=insert leaf (L'.image (lw1 n jl))
 have hjnot: jl ∉ G'.image (li1 jl):=by
  intro h;obtain ⟨j',_,he⟩ := mI.mp h;exact li1n jl j' he
 have hrsp: ∀ u,readsIn C G u=(gateAt C jl).inputs.count u+readsIn C (G'.image (li1 jl)) u:=by
  intro u;unfold readsIn;rw[sum_insert hjnot]
 have hrim: ∀ w,readsIn C (G'.image (li1 jl)) (lw1 n jl w)=readsIn C' G' w:=by
  intro w;unfold readsIn
  rw[sum_image (fun a _ b _ h => li1i jl h)]
  apply sum_congr rfl;intro j' hj';exact r1cnt wl C hrb hj_l j' (hGlt j' hj') (hno j' hj') w
 have hcnt_l: (gateAt C jl).inputs.count leaf=1:=by
  rcases hjli with h|h <;> rw[h] <;> simp[hwne,Ne.symm hwne]
 have hcnt_w: (gateAt C jl).inputs.count wl=1:=by
  rcases hjli with h|h <;> rw[h] <;> simp[hwne,Ne.symm hwne]
 have hcnt_other: ∀ u,u≠leaf → u≠wl→(gateAt C jl).inputs.count u=0:=by
  intro u h1 h2;rcases hjli with h|h <;> rw[h] <;> simp[h1,h2,Ne.symm h1,Ne.symm h2]
 have hlift_w: lw1 n jl wl=wl:=by unfold lw1;simp[hw_l]
 have hlift_l: lw1 n jl leaf=leaf:=by unfold lw1;simp[hleaf_lt]
 have hlt:=ot1u C hrb hj_l ht hGlt hno
 refine ⟨?_,?_,?_,?_⟩
 ·intro j hj
  rcases mN.mp hj with hje | hj'
  ·rw[hje]
   refine ⟨hjlo,by rcases hjli with h|h <;> simp[h],?_⟩
   intro i hi
   have hcases: i=leaf∨i=wl:=by rcases hjli with h|h <;> rw[h] at hi <;> simp at hi <;> tauto
   rcases hcases with rfl|hiw
   ·exact Or.inl (mNs _ _)
   ·rw[hiw]
    by_cases hGe: G' = ∅
    ·have hrt:=ht.2.2.2;simp only[hGe,↓reduceIte] at hrt
     left;apply mNo
     exact mI.mpr ⟨wl,by rw[hrt];simp,hlift_w⟩
    ·have hrt:=ht.2.2.2;simp only[hGe,↓reduceIte] at hrt;obtain ⟨j0',hj0',hw0⟩:=hrt;right
     have hj0_lt: j0' < jl:=by omega
     refine ⟨by omega,?_⟩
     apply mNo
     refine mI.mpr ⟨j0',hj0',?_⟩
     simp only[li1,hj0_lt,↓reduceIte];omega
  ·obtain ⟨hop,hlen,hin⟩:=hlt.1 j hj'
   refine ⟨hop,hlen,?_⟩
   intro i hi
   rcases hin i hi with hiL|⟨hni,hiG⟩
   ·exact Or.inl (mNo hiL)
   ·exact Or.inr ⟨hni,mNo hiG⟩
 ·intro u hu
  rcases mN.mp hu with huleaf | hu'
  ·rw[huleaf]
   refine ⟨fun ⟨hnl,hm⟩ => ?_,?_⟩
   ·rcases mN.mp hm with he | hm'
    ·omega
    ·obtain ⟨j',hj',hjeq⟩:=mI.mp hm'
     have: li1 jl j' < jl := by omega
     have: j' = li1 jl j' := by unfold li1 at *;split_ifs at * <;> omega
     exact hlnotG j' hj' (by omega)
   ·have hne_root: leaf≠n+jl:=by omega
    simp only[hne_root,↓reduceIte,hrsp,hcnt_l]
    have hzero: readsIn C (G'.image (li1 jl)) leaf=0:=by
     rw[←hlift_l,hrim leaf];apply sum_eq_zero;intro j' hj';apply lcz.mpr;intro hmem
     rcases (ht.1 j' hj').2.2 leaf hmem with hL|⟨hnl,hG⟩
     ·exact hlnotL hL
     ·exact hlnotG (leaf - n) hG (by omega)
    omega
  ·obtain ⟨w',hw',rfl⟩:=mI.mp hu';have hne_root: lw1 n jl w' ≠ n+jl:=lw1n n jl w'
   have hne_l: lw1 n jl w' ≠ leaf:=fun e => hlnotL (by rw[←hlift_l] at e;rw[←lw1j n jl e];exact hw')
   refine ⟨?_,?_⟩
   ·rintro ⟨hnl,hm⟩
    rcases mN.mp hm with he | hm'
    ·exact hne_root (by omega)
    ·exact (hlt.2.1 _ (mI.mpr ⟨w',hw',rfl⟩)).1 ⟨hnl,hm'⟩
   ·simp only[hne_root,↓reduceIte,hrsp,hrim];have hr:=(ht.2.1 w' hw').2
    by_cases hww: w' = wl
    ·subst hww;simp only[↓reduceIte] at hr;rw[hlift_w,hcnt_w,hr]
    ·have hne_w: lw1 n jl w' ≠ wl:=fun e => hww (lw1j n jl (by rw[e,hlift_w]))
     simp only[hww,↓reduceIte] at hr;rw[hcnt_other _ hne_l hne_w,hr]
 ·intro j hj
  rcases mN.mp hj with hje|hj_im
  ·rw[hje];simp only[↓reduceIte,hrsp]
   have h1: (gateAt C jl).inputs.count (n+jl)=0 :=
    hcnt_other (n+jl) (by omega) (by omega)
   have h2: readsIn C (G'.image (li1 jl)) (n+jl)=0:=by
    unfold readsIn;apply sum_eq_zero;intro q hq;obtain ⟨q',hq',rfl⟩:=mI.mp hq;exact lcz.mpr (hno q' hq')
   omega
  ·obtain ⟨j',hj',rfl⟩:=mI.mp hj_im
   have hne_root: n+li1 jl j' ≠ n+jl:=fun e => li1n jl j' (by omega)
   have hne_root' : lw1 n jl (n + j')≠n+jl:=lw1n n jl (n + j')
   have hne_l: n+li1 jl j' ≠ leaf:=by
    intro e
    have: li1 jl j' < jl := by omega
    have: j' = li1 jl j' := by unfold li1 at *;split_ifs at * <;> omega
    exact hlnotG j' hj' (by omega)
   simp only[hne_root,↓reduceIte,hrsp,←lw1g,hrim];have hr:=ht.2.2.1 j' hj'
   by_cases hww: n + j' = wl
   ·rw[if_pos hww] at hr;rw[hr,hww,hlift_w,hcnt_w];simp[show wl≠n+jl by omega]
   ·have hne_w: lw1 n jl (n + j')≠wl:=fun e => hww (lw1j n jl (by rw[e,hlift_w]))
    rw[if_neg hww] at hr;rw[hcnt_other _ (by rw[lw1g];exact hne_l) hne_w,hr];simp[hne_root']
 ·have hGne: G ≠ ∅ := insert_ne_empty _ _;simp only[hGne,↓reduceIte];exact ⟨jl,mNs _ _,rfl⟩
lemma ot1im {n jl wl: ℕ} (C: Circuit) (hrb: ReadsBack n C)
  (hj_l: jl < C.gates.length) (hw_l: wl < n+jl) (leaf: ℕ) (hleaf_lt: leaf < n+jl) (hwne: wl≠leaf)
  (hjlo: (gateAt C jl).op=GateOp.or)
  (hjli: (gateAt C jl).inputs=[leaf,wl]∨(gateAt C jl).inputs=[wl,leaf])
  {G' L' : Finset ℕ} {ρ' : ℕ}
  (ht: IsOrTree n ⟨rdel n jl wl C.gates,rd n jl wl C.output⟩ G' L' ρ')
  (hGlt: ∀ j' ∈ G',j' < C.gates.length - 1)
  (q0' : ℕ) (hq0' : q0' ∈ G')
  (hq0_read: n+jl∈(gateAt C (li1 jl q0')).inputs)
  (hnoo: ∀ j' ∈ G',j' ≠ q0' → n+jl∉(gateAt C (li1 jl j')).inputs)
  (hlnotL: leaf ∉ L') (hlnotG: ∀ j' ∈ G',n + j' ≠ leaf) :
  IsOrTree n C (insert jl (G'.image (li1 jl))) (insert leaf (L'.image (lw1 n jl))) (lw1 n jl ρ'):=by
 set C' : Circuit:=⟨rdel n jl wl C.gates,rd n jl wl C.output⟩;set G:=insert jl (G'.image (li1 jl));set L:=insert leaf (L'.image (lw1 n jl))
 have hjnot: jl ∉ G'.image (li1 jl):=by
  intro h;obtain ⟨j',_,he⟩ := mI.mp h;exact li1n jl j' he
 have hlif_q0:=r1l wl C hrb hj_l q0' (hGlt q0' hq0')
 have hwl_in_q0: wl∈(gateAt C' q0').inputs:=by
  rw[hlif_q0.2];exact lmm.mpr ⟨n+jl,hq0_read,rd_eq n jl wl⟩
 have hwl_valid: wl ∈ L' ∨ (n ≤ wl∧wl - n ∈ G'):=(ht.1 q0' hq0').2.2 wl hwl_in_q0
 have hwl_reads_pos: 1 ≤ readsIn C' G' wl:=by
  have hle: (gateAt C' q0').inputs.count wl ≤ readsIn C' G' wl :=
   single_le_sum (f := fun j => (gateAt C' j).inputs.count wl) (fun _ _ => Nat.zero_le _) hq0'
  have hpos: 0 < (gateAt C' q0').inputs.count wl:=lcpi.mpr hwl_in_q0;omega
 have hwl_reads1: readsIn C' G' wl=1∧wl ≠ ρ' := by
  rcases hwl_valid with hL|⟨hnw,hG⟩
  ·have h:=(ht.2.1 wl hL).2
   by_cases he: wl = ρ'
   ·rw[if_pos he] at h;omega
   ·rw[if_neg he] at h;exact ⟨h,he⟩
  ·have h:=ht.2.2.1 (wl - n) hG
   have heq: n+(wl - n)=wl:=by omega
   rw[heq] at h
   by_cases he: wl = ρ'
   ·rw[if_pos he] at h;omega
   ·rw[if_neg he] at h;exact ⟨h,he⟩
 have hq0_lenC: (gateAt C (li1 jl q0')).inputs.length=2:=by
  have hlen' := (ht.1 q0' hq0').2.1;rw[hlif_q0.2,llm] at hlen';exact hlen'
 rcases ll2.mp hq0_lenC with ⟨a,b,hab⟩
 have hab' : (gateAt C' q0').inputs=[rd n jl wl a,rd n jl wl b]:=by
  rw[hlif_q0.2,hab];rfl
 have hq0_cnt_wl: (gateAt C' q0').inputs.count wl=1:=by
  have hle: (gateAt C' q0').inputs.count wl ≤ readsIn C' G' wl :=
   single_le_sum (f := fun j => (gateAt C' j).inputs.count wl) (fun _ _ => Nat.zero_le _) hq0'
  have hpos: 0 < (gateAt C' q0').inputs.count wl:=lcpi.mpr hwl_in_q0;omega
 have hab_cases: (a=n+jl∧b≠n+jl∧rd n jl wl b≠wl) ∨
   (b=n+jl∧a≠n+jl∧rd n jl wl a≠wl):=by
  rw[hab] at hq0_read;simp only[lmc,lnn,or_false] at hq0_read
  rcases hq0_read with rfl|rfl
  ·left
   have hrb: rd n jl wl b≠wl:=by
    intro e;rw[hab',rd_eq,e] at hq0_cnt_wl;simp at hq0_cnt_wl
   exact ⟨rfl,fun e => hrb (by rw[e,rd_eq]),hrb⟩
  ·right
   have hra: rd n jl wl a≠wl:=by
    intro e;rw[hab',rd_eq,e] at hq0_cnt_wl;simp at hq0_cnt_wl
   exact ⟨rfl,fun e => hra (by rw[e,rd_eq]),hra⟩
 have hlift_w: lw1 n jl wl=wl:=by unfold lw1;simp[hw_l]
 have hlift_l: lw1 n jl leaf=leaf:=by unfold lw1;simp[hleaf_lt]
 have hq0_cnt_njl: (gateAt C (li1 jl q0')).inputs.count (n+jl)=1:=by
  rw[hab];rcases hab_cases with ⟨rfl,hne,_⟩ | ⟨rfl,hne,_⟩ <;> simp[hne,Ne.symm hne]
 have hq0_cnt_w: (gateAt C (li1 jl q0')).inputs.count wl=0:=by
  rw[hab]
  rcases hab_cases with ⟨rfl,hne,hrb'⟩ | ⟨rfl,hne,hra'⟩
  ·have hbne: b≠wl:=fun e => hrb' (by rw[e,rd_lt n jl wl wl hw_l])
   simp[List.count_cons,show n+jl≠wl by omega,hbne]
  ·have hane: a≠wl:=fun e => hra' (by rw[e,rd_lt n jl wl wl hw_l])
   simp[List.count_cons,show n+jl≠wl by omega,hane]
 have hq0_cnt_other: ∀ u',u' ≠ wl →
   (gateAt C (li1 jl q0')).inputs.count (lw1 n jl u')=(gateAt C' q0').inputs.count u' := by
  intro u' hu';rw[hab,hab']
  rcases hab_cases with ⟨rfl,hne,_⟩ | ⟨rfl,hne,_⟩
  ·have hb_eq: b=lw1 n jl (rd n jl wl b):=(lw1r n jl wl b hne).symm;have h1: n+jl≠lw1 n jl u' := (lw1n n jl u').symm;rw[rd_eq,List.count_cons,List.count_cons,List.count_nil,List.count_cons,List.count_cons,List.count_nil];have hbeq1: (n+jl == lw1 n jl u')=false:=beq_false_of_ne h1;have hbeq2: (wl == u')=false:=beq_false_of_ne (Ne.symm hu')
   have hbeq3: (b == lw1 n jl u')=(rd n jl wl b == u'):=by
    conv_lhs => rw[hb_eq]
    by_cases h: rd n jl wl b = u'
    ·rw[h];simp
    ·have: lw1 n jl (rd n jl wl b)≠lw1 n jl u' := fun e => h (lw1j n jl e)
     rw[beq_false_of_ne h,beq_false_of_ne this]
   simp[hbeq1,hbeq2,hbeq3]
  ·have ha_eq: a=lw1 n jl (rd n jl wl a):=(lw1r n jl wl a hne).symm;have h1: n+jl≠lw1 n jl u' := (lw1n n jl u').symm;rw[rd_eq,List.count_cons,List.count_cons,List.count_nil,List.count_cons,List.count_cons,List.count_nil];have hbeq1: (n+jl == lw1 n jl u')=false:=beq_false_of_ne h1;have hbeq2: (wl == u')=false:=beq_false_of_ne (Ne.symm hu')
   have hbeq3: (a == lw1 n jl u')=(rd n jl wl a == u'):=by
    conv_lhs => rw[ha_eq]
    by_cases h: rd n jl wl a = u'
    ·rw[h];simp
    ·have: lw1 n jl (rd n jl wl a)≠lw1 n jl u' := fun e => h (lw1j n jl e)
     rw[beq_false_of_ne h,beq_false_of_ne this]
   simp[hbeq1,hbeq2,hbeq3]
 have hcnt_l: (gateAt C jl).inputs.count leaf=1:=by
  rcases hjli with h|h <;> rw[h] <;> simp[hwne,Ne.symm hwne]
 have hcnt_w: (gateAt C jl).inputs.count wl=1:=by
  rcases hjli with h|h <;> rw[h] <;> simp[hwne,Ne.symm hwne]
 have hcnt_other: ∀ u,u≠leaf → u≠wl→(gateAt C jl).inputs.count u=0:=by
  intro u h1 h2;rcases hjli with h|h <;> rw[h] <;> simp[h1,h2,Ne.symm h1,Ne.symm h2]
 have hreads_im_other: ∀ u',u' ≠ wl →
   readsIn C (G'.image (li1 jl)) (lw1 n jl u')=readsIn C' G' u' := by
  intro u' hu';unfold readsIn
  rw[sum_image (fun x _ y _ h => li1i jl h)]
  apply sum_congr rfl;intro j' hj'
  by_cases hjq: j' = q0'
  ·subst hjq;exact hq0_cnt_other u' hu'
  ·exact r1cnt wl C hrb hj_l j' (hGlt j' hj') (hnoo j' hj' hjq) u'
 have hreads_im_wl: readsIn C (G'.image (li1 jl)) wl=0:=by
  unfold readsIn
  rw[sum_image (fun x _ y _ h => li1i jl h)]
  apply sum_eq_zero;intro j' hj'
  by_cases hjq: j' = q0'
  ·subst hjq;exact hq0_cnt_w
  ·rw[←hlift_w,r1cnt wl C hrb hj_l j' (hGlt j' hj') (hnoo j' hj' hjq) wl]
   have hsum:=add_sum_erase G' (fun k => (gateAt C' k).inputs.count wl) hq0'
   have hz: ∑ k ∈ G'.erase q0',(gateAt C' k).inputs.count wl=0:=by
    change _=readsIn C' G' wl at hsum;omega
   exact sum_eq_zero_iff.mp hz j' (mE.mpr ⟨hjq,hj'⟩)
 have hreads_im_njl: readsIn C (G'.image (li1 jl)) (n+jl)=1:=by
  unfold readsIn
  rw[sum_image (fun x _ y _ h => li1i jl h)]
  rw[←add_sum_erase G' _ hq0',hq0_cnt_njl]
  have hz: ∑ k ∈ G'.erase q0',(gateAt C (li1 jl k)).inputs.count (n+jl)=0:=by
   apply sum_eq_zero;intro k hk;obtain ⟨hne,hkG⟩:=mE.mp hk;exact lcz.mpr (hnoo k hkG hne)
  omega
 have hrsp: ∀ u,readsIn C G u=(gateAt C jl).inputs.count u+readsIn C (G'.image (li1 jl)) u:=by
  intro u;unfold readsIn;rw[sum_insert hjnot]
 refine ⟨?_,?_,?_,?_⟩
 ·intro j hj
  rcases mN.mp hj with hje|hj_im
  ·rw[hje]
   refine ⟨hjlo,by rcases hjli with h|h <;> simp[h],?_⟩
   intro i hi
   have hcases: i=leaf∨i=wl:=by rcases hjli with h|h <;> rw[h] at hi <;> simp at hi <;> tauto
   rcases hcases with rfl|hiw
   ·exact Or.inl (mNs _ _)
   ·rw[hiw]
    rcases hwl_valid with hL|⟨hnw,hG⟩
    ·exact Or.inl (mNo (mI.mpr ⟨wl,hL,hlift_w⟩))
    ·right
     refine ⟨hnw,mNo (mI.mpr ⟨wl - n,hG,?_⟩)⟩
     simp only[li1,show wl - n < jl by omega,↓reduceIte]
  ·obtain ⟨j',hj',rfl⟩:=mI.mp hj_im
   by_cases hjq: j' = q0'
   ·rw[hjq];have hlif_q0' := hlif_q0;dsimp only at hlif_q0'
    refine ⟨by rw[←hlif_q0'.1,(ht.1 q0' hq0').1],hq0_lenC,?_⟩
    intro i hi
    by_cases hi_njl: i=n+jl
    ·subst hi_njl;exact Or.inr ⟨Nat.le_add_right _ _,by rw[ascl];exact mNs jl _⟩
    ·have hi_rd: rd n jl wl i∈(gateAt C' q0').inputs:=by
      rw[hlif_q0.2];exact lmm.mpr ⟨i,hi,rfl⟩
     have hi_eq: i=lw1 n jl (rd n jl wl i):=(lw1r n jl wl i hi_njl).symm
     rcases (ht.1 q0' hq0').2.2 (rd n jl wl i) hi_rd with hL|⟨hnr,hG⟩
     ·exact Or.inl (mNo (mI.mpr ⟨_,hL,hi_eq.symm⟩))
     ·right
      have hrr: rd n jl wl i=n+(rd n jl wl i - n):=by omega
      rw[hi_eq,hrr,lw1g];exact ⟨Nat.le_add_right _ _,by rw[ascl];exact mNo (mI.mpr ⟨_,hG,rfl⟩)⟩
   ·obtain ⟨hop,hlen,hin⟩:=ht.1 j' hj';have hlif:=r1l wl C hrb hj_l j' (hGlt j' hj');have hinp:=r1in wl C hrb hj_l j' (hGlt j' hj') (hnoo j' hj' hjq)
    refine ⟨by rw[←hlif.1,hop],by rw[hinp,llm,hlen],?_⟩
    intro i hi;rw[hinp] at hi;obtain ⟨i',hi',rfl⟩:=lmm.mp hi
    rcases hin i' hi' with hiL|⟨hni,hiG⟩
    ·exact Or.inl (mNo (mI.mpr ⟨i',hiL,rfl⟩))
    ·right
     have hi_eq: i' = n+(i' - n):=by omega
     rw[hi_eq,lw1g];exact ⟨Nat.le_add_right _ _,by rw[ascl];exact mNo (mI.mpr ⟨i' - n,hiG,rfl⟩)⟩
 ·intro u hu
  rcases mN.mp hu with huleaf | hu'
  ·rw[huleaf]
   refine ⟨fun ⟨hnl,hm⟩ => ?_,?_⟩
   ·rcases mN.mp hm with he | hm'
    ·omega
    ·obtain ⟨j',hj',hjeq⟩:=mI.mp hm'
     have: li1 jl j' < jl := by omega
     have: j' = li1 jl j' := by unfold li1 at *;split_ifs at * <;> omega
     exact hlnotG j' hj' (by omega)
   ·have hne_root: leaf≠lw1 n jl ρ' := by
     intro e;have he' : leaf = ρ' := lw1j n jl (by rw[hlift_l,e])
     by_cases hGe: G' = ∅
     ·exact notMem_empty q0' (hGe ▸ hq0')
     ·have hrt:=ht.2.2.2;simp only[hGe,↓reduceIte] at hrt;obtain ⟨j0',hj0',rfl⟩:=hrt;exact hlnotG j0' hj0' he'.symm
    simp only[hne_root,↓reduceIte,hrsp,hcnt_l]
    have hzero: readsIn C (G'.image (li1 jl)) leaf=0:=by
     rw[←hlift_l,hreads_im_other leaf (Ne.symm hwne)];apply sum_eq_zero;intro j' hj';apply lcz.mpr;intro hmem
     rcases (ht.1 j' hj').2.2 leaf hmem with hL|⟨hnl,hG⟩
     ·exact hlnotL hL
     ·exact hlnotG (leaf - n) hG (by omega)
    omega
  ·obtain ⟨w',hw',rfl⟩:=mI.mp hu'
   have hne_l: lw1 n jl w' ≠ leaf:=fun e => hlnotL (by rw[←hlift_l] at e;rw[←lw1j n jl e];exact hw')
   refine ⟨?_,?_⟩
   ·rintro ⟨hnl,hm⟩
    rcases mN.mp hm with he | hm'
    ·exact lw1n n jl w' (by omega)
    ·obtain ⟨j',hj',hjeq⟩:=mI.mp hm'
     have heq: lw1 n jl w' = lw1 n jl (n + j'):=by rw[lw1g];omega
     have hwj:=lw1j n jl heq;exact (ht.2.1 w' hw').1 ⟨by omega,by simpa [hwj] using hj'⟩
   ·rw[hrsp]
    by_cases hww: w' = wl
    ·rw[hww]
     have hne_r: lw1 n jl wl≠lw1 n jl ρ' := fun e => hwl_reads1.2 (lw1j n jl e)
     rw[if_neg hne_r,hlift_w,hcnt_w,hreads_im_wl]
    ·have hne_w: lw1 n jl w' ≠ wl:=fun e => hww (lw1j n jl (by rw[e,hlift_w]))
     rw[hcnt_other _ hne_l hne_w,hreads_im_other w' hww,(ht.2.1 w' hw').2]
     by_cases hr: w' = ρ'
     ·simp[hr]
     ·have hnr: lw1 n jl w' ≠ lw1 n jl ρ' := fun e => hr (lw1j n jl e)
      simp[hr,hnr]
 ·intro j hj
  rcases mN.mp hj with hje|hj_im
  ·rw[hje];have hne_r: n+jl≠lw1 n jl ρ' := (lw1n n jl ρ').symm;simp only[hne_r,↓reduceIte,hrsp,hreads_im_njl]
   have h1: (gateAt C jl).inputs.count (n+jl)=0 :=
    hcnt_other (n+jl) (by omega) (by omega)
   omega
  ·obtain ⟨j',hj',rfl⟩:=mI.mp hj_im
   have hne_l: lw1 n jl (n + j')≠leaf:=by
    rw[lw1g];intro e
    have: li1 jl j' < jl := by omega
    have: j' = li1 jl j' := by unfold li1 at *;split_ifs at * <;> omega
    exact hlnotG j' hj' (by omega)
   rw[←lw1g,hrsp]
   by_cases hww: n + j' = wl
   ·have hne_r: lw1 n jl (n + j')≠lw1 n jl ρ' := fun e =>
     hwl_reads1.2 (by rw[←hww];exact lw1j n jl e)
    rw[if_neg hne_r,hww,hlift_w,hcnt_w,hreads_im_wl]
   ·have hne_w: lw1 n jl (n + j')≠wl:=fun e => hww (lw1j n jl (by rw[e,hlift_w]))
    rw[hcnt_other _ hne_l hne_w,hreads_im_other (n + j') hww,ht.2.2.1 j' hj']
    by_cases hr: n + j' = ρ'
    ·simp[hr]
    ·have hnr: lw1 n jl (n + j')≠lw1 n jl ρ' := fun e => hr (lw1j n jl e)
     simp[hr,hnr]
 ·have hGne: G ≠ ∅ := insert_ne_empty _ _
  have hG'ne: G' ≠ ∅ := fun h => notMem_empty q0' (h ▸ hq0')
  have hrt:=ht.2.2.2;simp only[hG'ne,↓reduceIte] at hrt;obtain ⟨j0',hj0',rfl⟩:=hrt;simp only[hGne,↓reduceIte];exact ⟨li1 jl j0',mNo (mI.mpr ⟨j0',hj0',rfl⟩),lw1g n jl j0'⟩
lemma coo {n: ℕ} {K' : SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C' : Circuit} {d' : NCCData n} (hv' : Valid n K' A C' d')
  (u: Fin n) (hu: u ∈ d'.cover) :
  ∃ v: Fin n,d'.owns u v=true∧v ∉ d'.cover:=by
 by_contra hno
 push Not at hno
 have hcov: K'.IsVertexCover ((d'.cover.erase u: Finset (Fin n)): Set (Fin n)):=by
  intro a b hab;have hne := hv'.2.2.1.2 a b hab
  have hown: d'.owns a b=true ∨ d'.owns b a=true:=by
   cases h1: d'.owns a b
   ·right;rw[h1] at hne;cases h2: d'.owns b a
    ·exact absurd h2.symm hne
    ·rfl
   ·exact Or.inl rfl
  rcases hown with h1|h2
  ·have ha: a ∈ d'.cover:=(hv'.2.2.1.1 a b h1).2
   by_cases hau: a=u
   ·subst hau;exact Or.inr (mC.mpr (mE.mpr ⟨hab.ne',hno b h1⟩))
   ·exact Or.inl (mC.mpr (mE.mpr ⟨hau,ha⟩))
  ·have hb: b ∈ d'.cover:=(hv'.2.2.1.1 b a h2).2
   by_cases hbu: b=u
   ·subst hbu;exact Or.inl (mC.mpr (mE.mpr ⟨hab.ne,hno a h2⟩))
   ·exact Or.inr (mC.mpr (mE.mpr ⟨hbu,hb⟩))
 have hle := hv'.2.1.2 (d'.cover.erase u) hcov;have hlt:=Finset.card_erase_lt_of_mem hu;omega
lemma zrs {n: ℕ} {K' : SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C' : Circuit} {d' : NCCData n} (hv' : Valid n K' A C' d')
  (t: Fin n) (ht: t ∈ d'.cover) :
  d'.zroot t=t.val ∨ ∃ jz < C'.gates.length,d'.zroot t=n+jz ∧ d'.role jz=(Kind.z,t.val):=by
 have hZt:=(hv'.2.2.2.2.2.1 t ht).2.1
 by_cases hG: gatesOf d' C' Kind.z t.val = ∅
 ·have hr:=hZt.2.2.2;simp only[hG,↓reduceIte] at hr;have hmem: t.val∈zLeaves d' t:=mNs _ _;rw[hr,mS] at hmem;exact Or.inl hmem.symm
 ·have hr:=hZt.2.2.2;simp only[hG,↓reduceIte] at hr;obtain ⟨jz,hjz,heq⟩:=hr;have hjz' := mF.mp hjz;exact Or.inr ⟨jz,mR.mp hjz'.1,heq,hjz'.2⟩
lemma ors {n: ℕ} {K' : SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C' : Circuit} {d' : NCCData n} (hv' : Valid n K' A C' d')
  (t: Fin n) (ht: t ∈ d'.cover) :
  (∃ r,d'.owns t r=true ∧ d'.oroot t = d'.lam t r) ∨
  ∃ jo < C'.gates.length,d'.oroot t=n+jo ∧ d'.role jo=(Kind.o,t.val):=by
 have hOt:=(hv'.2.2.2.2.2.1 t ht).2.2.1
 by_cases hG: gatesOf d' C' Kind.o t.val = ∅
 ·have hr:=hOt.2.2.2;simp only[hG,↓reduceIte] at hr
  have hmem: d'.oroot t∈oLeaves d' t:=by rw[hr];simp
  obtain ⟨r,hr1,hr2⟩:=mI.mp hmem;exact Or.inl ⟨r,(mF.mp hr1).2,hr2.symm⟩
 ·have hr:=hOt.2.2.2;simp only[hG,↓reduceIte] at hr;obtain ⟨jo,hjo,heq⟩:=hr;have hjo' := mF.mp hjo;exact Or.inr ⟨jo,mR.mp hjo'.1,heq,hjo'.2⟩
lemma zroot_ne_oroot {n: ℕ} {K' : SimpleGraph (Fin n)} {A: Finset (Fin n)}
  {C' : Circuit} {d' : NCCData n} (hv' : Valid n K' A C' d')
  (t: Fin n) (ht: t ∈ d'.cover): d'.zroot t ≠ d'.oroot t:=by
 intro heq
 rcases zrs hv' t ht with hz|⟨jz,_,hz,hrz⟩ <;>
  rcases ors hv' t ht with ⟨r,hown,ho⟩ | ⟨jo,_,ho,hro⟩
 ·have hne: r≠t:=(hv'.2.2.1.1 t r hown).1.ne';have hlam:=(hv'.2.2.2.2.2.1 t ht).2.2.2 r hown;unfold LamOK at hlam
  split_ifs at hlam
  ·rcases hlam.2.1 with h1|⟨j,_,h1,_⟩
   ·exact hne (Fin.ext (by omega))
   ·have:=t.isLt;omega
  ·exact hne (Fin.ext (by omega))
 ·have:=t.isLt;omega
 ·have hne: r≠t:=(hv'.2.2.1.1 t r hown).1.ne';have hlam:=(hv'.2.2.2.2.2.1 t ht).2.2.2 r hown;unfold LamOK at hlam
  split_ifs at hlam
  ·rcases hlam.2.1 with h1|⟨j,_,h1,hrj⟩
   ·have:=r.isLt;omega
   ·have hj: jz=j:=by omega
    subst hj;rw[hrz] at hrj;exact hne (Fin.ext (pei.mp hrj).2.symm)
  ·have:=r.isLt;omega
 ·have hj: jz=jo:=by omega
  subst hj;rw[hrz] at hro;simp at hro
lemma mcEx {n: ℕ} (K: SimpleGraph (Fin n)) [DecidableRel K.Adj] :
  ∃ T: Finset (Fin n),IsMinCover K T:=by
 classical
 let S: Finset (Finset (Fin n)):=Finset.univ.filter (fun T => K.IsVertexCover (T: Set (Fin n)))
 have hSne: S.Nonempty:=by
  refine ⟨Finset.univ,mF.mpr ⟨mV _,?_⟩⟩
  intro u v _;exact Or.inl (mC.mpr (mV u))
 obtain ⟨T,hTS,hmin⟩:=exists_min_image S Finset.card hSne
 refine ⟨T,(mF.mp hTS).2,fun T' hT' => hmin T' (mF.mpr ⟨mV _,hT'⟩)⟩
lemma ecEq {n: ℕ} {K K' : SimpleGraph (Fin n)} [DecidableRel K.Adj] [DecidableRel K'.Adj]
  {l p: Fin n} (hl: ∀ v: Fin n,K.Adj l v↔v=p)
  (hK' : ∀ u v: Fin n,K'.Adj u v↔K.Adj u v∧u≠l∧v≠l) :
  K.edgeFinset.card = K'.edgeFinset.card+1:=by
 have heq: K.edgeFinset=insert s(l,p) K'.edgeFinset:=by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
   simp only[SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,mN,Sym2.eq_iff,hK']
   constructor
   ·intro huv
    by_cases hul: u=l
    ·rw[hul] at huv ⊢;exact Or.inl (Or.inl ⟨rfl,(hl v).mp huv⟩)
    ·by_cases hvl: v=l
     ·rw[hvl] at huv ⊢;exact Or.inl (Or.inr ⟨(hl u).mp huv.symm,rfl⟩)
     ·exact Or.inr ⟨huv,hul,hvl⟩
   ·rintro ((⟨h1,h2⟩ | ⟨h1,h2⟩)|⟨huv,_,_⟩)
    ·rw[h1,h2];exact (hl p).mpr rfl
    ·rw[h1,h2];exact ((hl p).mpr rfl).symm
    ·exact huv
 have hnot: s(l,p) ∉ K'.edgeFinset:=by
  simp only[SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,hK'];tauto
 rw[heq,card_insert_of_notMem hnot]
lemma mciEx {n: ℕ} (f: (Fin n→Bool)→Bool) :
  ∃ C: Circuit,IsMinimalCircuit n C∧circuitFun n C=f:=by
 classical
 have hex: ∃ s: ℕ,HasCircuitSize n f s:=by
  obtain ⟨gs,out,hok,_,_,hev⟩:=shannon n f n (le_refl n)
  refine ⟨gs.length,⟨gs,out⟩,?_,le_refl _,?_⟩
  ·intro g hg;exact hok g hg
  ·intro x;change (wF gs (List.ofFn x)).getD out false=f x;rw[hev (List.ofFn x) (by simp)]
   congr 1;funext i;simp[List.getD,i.isLt]
 let s0:=Nat.find hex;obtain ⟨C,hfan,hsz,hcf⟩:=Nat.find_spec hex
 have hmin: ∀ C' : Circuit,FanInTwo C' → circuitFun n C' = f→C.size ≤ C'.size:=by
  intro C' hfan' hcf'
  have hle: s0 ≤ C'.size:=Nat.find_min' hex ⟨C',hfan',le_refl _,fun x => congrFun hcf' x⟩
  omega
 exact ⟨C,⟨hfan,fun C' hfan' hcf' => hmin C' hfan' (hcf'.trans (funext hcf))⟩,funext hcf⟩
lemma gfK1 {n: ℕ} {K K' : SimpleGraph (Fin n)} [DecidableRel K.Adj] [DecidableRel K'.Adj]
  {A: Finset (Fin n)} {l p: Fin n}
  (hA: ∀ a∈A,∀ v: Fin n,¬ K.Adj a v)
  (hl: ∀ v: Fin n,K.Adj l v↔v=p)
  (hK' : ∀ u v: Fin n,K'.Adj u v↔K.Adj u v∧u≠l∧v≠l)
  (x: Fin n→Bool) :
  graphFun K' A x=graphFun K A (Function.update x l false):=by
 have hlnA: l∉A:=fun h => hA l h p ((hl p).mpr rfl)
 simp only[graphFun]
 congr 1
 ·rw[decide_eq_decide]
  constructor <;> (rintro ⟨a,ha,hxa⟩;refine ⟨a,ha,?_⟩;have hal: a≠l := fun e => hlnA (e ▸ ha))
  ·rwa[fupn hal]
  ·rwa[fupn hal] at hxa
 ·rw[decide_eq_decide]
  constructor
  ·rintro ⟨u,v,huv',hxu,hxv⟩
   obtain ⟨huv,hul,hvl⟩:=(hK' u v).mp huv';exact ⟨u,v,huv,by rwa[fupn hul],by rwa[fupn hvl]⟩
  ·rintro ⟨u,v,huv,hxu,hxv⟩
   have hul: u≠l:=fun e => by subst e;simp at hxu
   have hvl: v≠l:=fun e => by subst e;simp at hxv
   rw[fupn hul] at hxu;rw[fupn hvl] at hxv;exact ⟨u,v,(hK' u v).mpr ⟨huv,hul,hvl⟩,hxu,hxv⟩
lemma gfK2 {n: ℕ} {K K2: SimpleGraph (Fin n)}
  [DecidableRel K.Adj] [DecidableRel K2.Adj]
  {A: Finset (Fin n)} {l p q: Fin n}
  (hA: ∀ a∈A,∀ v: Fin n,¬ K.Adj a v)
  (hl: ∀ v: Fin n,K.Adj l v↔v=p)
  (hp: ∀ v: Fin n,K.Adj p v↔v=l∨v=q)
  (hK2: ∀ u v: Fin n,K2.Adj u v↔K.Adj u v∧u≠l∧u≠p∧v≠l∧v≠p)
  (x: Fin n→Bool) :
  graphFun K A (Function.update x l true)=graphFun K2 (insert p A) x:=by
 have hlp: l≠p:=((hl p).mpr rfl).ne
 have hlnA: l∉A:=fun h => hA l h p ((hl p).mpr rfl)
 apply Bool.eq_iff_iff.mpr;simp only[graphFun,boT,dTe,mN]
 constructor
 ·rintro (⟨a,ha,hxa⟩ | ⟨u,v,huv,hxu,hxv⟩)
  ·have hal: a≠l:=fun e => hlnA (e ▸ ha)
   rw[fupn hal] at hxa;exact Or.inl ⟨a,Or.inr ha,hxa⟩
  ·by_cases hul: u=l
   ·rw[hul] at huv;have hvp: v=p:=(hl v).mp huv;rw[hvp,fupn hlp.symm] at hxv;exact Or.inl ⟨p,Or.inl rfl,hxv⟩
   ·by_cases hvl: v=l
    ·rw[hvl] at huv;have hup: u=p:=(hl u).mp huv.symm;rw[hup,fupn hlp.symm] at hxu;exact Or.inl ⟨p,Or.inl rfl,hxu⟩
    ·rw[fupn hul] at hxu;rw[fupn hvl] at hxv
     by_cases hup: u=p
     ·rw[hup] at hxu;exact Or.inl ⟨p,Or.inl rfl,hxu⟩
     ·by_cases hvp: v=p
      ·rw[hvp] at hxv;exact Or.inl ⟨p,Or.inl rfl,hxv⟩
      ·exact Or.inr ⟨u,v,(hK2 u v).mpr ⟨huv,hul,hup,hvl,hvp⟩,hxu,hxv⟩
 ·rintro (⟨a,hap|ha,hxa⟩ | ⟨u,v,huv,hxu,hxv⟩)
  ·rw[hap] at hxa;right
   refine ⟨l,p,(hl p).mpr rfl,by simp,?_⟩
   rw[fupn hlp.symm];exact hxa
  ·left
   have hal: a≠l:=fun e => hlnA (e ▸ ha)
   exact ⟨a,ha,by rw[fupn hal];exact hxa⟩
  ·obtain ⟨hKuv,hul,_,hvl,_⟩:=(hK2 u v).mp huv;right
   exact ⟨u,v,hKuv,by rw[fupn hul];exact hxu,
    by rw[fupn hvl];exact hxv⟩
lemma tK2 {n: ℕ} {K K2: SimpleGraph (Fin n)}
  [DecidableRel K.Adj] [DecidableRel K2.Adj]
  {l p q: Fin n}
  (hl: ∀ v: Fin n,K.Adj l v↔v=p)
  (hp: ∀ v: Fin n,K.Adj p v↔v=l∨v=q)
  (hK2: ∀ u v: Fin n,K2.Adj u v↔K.Adj u v∧u≠l∧u≠p∧v≠l∧v≠p)
  {T T2: Finset (Fin n)} (hT: IsMinCover K T) (hT2: IsMinCover K2 T2) :
  T.card=T2.card+1:=by
 have h1: T.card ≤ T2.card+1:=by
  have hcov: K.IsVertexCover ((insert p T2: Finset (Fin n)): Set (Fin n)):=by
   intro u v huv
   by_cases hup: u=p
   ·left;simp[hup]
   ·by_cases hvp: v=p
    ·right;simp[hvp]
    ·have hul: u≠l:=fun e => hvp ((hl v).mp (e ▸ huv))
     have hvl: v≠l:=fun e => hup ((hl u).mp (e ▸ huv.symm))
     rcases hT2.1 ((hK2 u v).mpr ⟨huv,hul,hup,hvl,hvp⟩) with hu|hv
     ·left;exact mC.mpr (mNo (mC.mp hu))
     ·right;exact mC.mpr (mNo (mC.mp hv))
  have hle:=hT.2 (insert p T2) hcov;have hins:=card_insert_le p T2;omega
 have h2: T2.card+1 ≤ T.card:=by
  by_cases hpT: p∈T
  ·have hcov: K2.IsVertexCover ((T.erase p: Finset (Fin n)): Set (Fin n)):=by
    intro u v huv;obtain ⟨hKuv,_,hup,_,hvp⟩:=(hK2 u v).mp huv
    rcases hT.1 hKuv with hu|hv
    ·left;exact mC.mpr (mE.mpr ⟨hup,mC.mp hu⟩)
    ·right;exact mC.mpr (mE.mpr ⟨hvp,mC.mp hv⟩)
   have hle:=hT2.2 (T.erase p) hcov;have her:=card_erase_of_mem hpT;have hpos: 1 ≤ T.card:=one_le_card.mpr ⟨p,hpT⟩;omega
  ·have hlT: l∈T:=by
    rcases hT.1 ((hl p).mpr rfl) with hl' | hp'
    ·exact mC.mp hl'
    ·exact absurd (mC.mp hp') hpT
   have hcov: K2.IsVertexCover ((T.erase l: Finset (Fin n)): Set (Fin n)):=by
    intro u v huv;obtain ⟨hKuv,hul,_,hvl,_⟩:=(hK2 u v).mp huv
    rcases hT.1 hKuv with hu|hv
    ·left;exact mC.mpr (mE.mpr ⟨hul,mC.mp hu⟩)
    ·right;exact mC.mpr (mE.mpr ⟨hvl,mC.mp hv⟩)
   have hle:=hT2.2 (T.erase l) hcov;have her:=card_erase_of_mem hlT;have hpos: 1 ≤ T.card:=one_le_card.mpr ⟨l,hlT⟩;omega
 omega
lemma urpB {n' : ℕ} (f: (Fin (n' + 1)→Bool)→Bool)
  (gs: List Gate) (o: ℕ) (L: Least (n' + 1) f gs o) (l: Fin (n' + 1))
  (hdep: ∃ x: Fin (n' + 1)→Bool,f (Function.update x l (!x l))≠f x)
  (hnc: ∀ b: Bool,∃ x y: Fin (n' + 1)→Bool,
   f (Function.update x l b)≠f (Function.update y l b))
  (hno3: ∀ b: Bool,¬ Drop f l b 3 gs.length) :
  ∃ (jl wl r u: ℕ) (g_l g_r: Gate),
   jl < r∧r < gs.length∧wl < n' + 1+jl∧wl≠l.val ∧
   u < n' + 1+r∧u ≠ n' + 1+jl∧o≠l.val∧o ≠ n' + 1+jl ∧
   gs[jl]? = some g_l∧gs[r]? = some g_r ∧
   (g_l.inputs=[l.val,wl]∨g_l.inputs=[wl,l.val]) ∧
   (g_r.inputs=[n' + 1+jl,u]∨g_r.inputs=[u,n' + 1+jl]) ∧
   (∀ q' : ℕ,Reads gs q' l.val → q' = jl) ∧
   (∀ q' : ℕ,Reads gs q' (n' + 1+jl) → q' = r) ∧
   ((g_l.op=GateOp.or∧g_r.op=GateOp.and) ∨
   (g_l.op=GateOp.and∧g_r.op=GateOp.or)):=by
 have hfnc: ∃ x y: Fin (n' + 1)→Bool,f x≠f y:=by
  obtain ⟨x,y,h⟩:=hnc false;exact ⟨_,_,h⟩
 have hon0: o≠l.val:=by
  intro e;obtain ⟨x,y,hxy⟩:=hnc false;apply hxy;rw[←L.hev,←L.hev,e,vli gs _ l.val l.isLt,vli gs _ l.val l.isLt];simp
 obtain ⟨jl,hjl_read⟩:=read_dep_direct L.hev l hdep hon0
 have hul: ∀ q' : ℕ,Reads gs q' l.val → q' = jl:=by
  intro q' hq'
  by_contra hne
  have hkill: ∀ p1 p2: ℕ,p1 < p2→Reads gs p1 l.val→Reads gs p2 l.val→False:=by
   intro p1 p2 hlt hp1 hp2;obtain ⟨g2,hg2,hm2⟩:=hp2;have hp2_len: p2 < gs.length:=(gEs.1 hg2).1
   rcases gate_cases gs L.hcl p2 g2 hg2 l.val hm2 with
    ⟨hop2,_,_⟩ | ⟨_,_,⟨hop2,_⟩ | ⟨hop2,_⟩⟩
   ·have hc:=isC_reader L.hcl l p2 g2 hg2 hm2 false (Or.inl hop2);obtain ⟨r,hr_gt,_,hr_rc⟩:=L.next l false (hnc false) p2 hp2_len hc
    exact hno3 false (L.save3 l false (hnc false) p1 p2 r (by omega) (by omega) (by omega)
     (rc_input false hp1) (rc_input false ⟨g2,hg2,hm2⟩) hr_rc)
   ·have hc:=isC_reader L.hcl l p2 g2 hg2 hm2 false (Or.inr (by simp[fixBit,hop2]));obtain ⟨r,hr_gt,_,hr_rc⟩:=L.next l false (hnc false) p2 hp2_len hc
    exact hno3 false (L.save3 l false (hnc false) p1 p2 r (by omega) (by omega) (by omega)
     (rc_input false hp1) (rc_input false ⟨g2,hg2,hm2⟩) hr_rc)
   ·have hc:=isC_reader L.hcl l p2 g2 hg2 hm2 true (Or.inr (by simp[fixBit,hop2]));obtain ⟨r,hr_gt,_,hr_rc⟩:=L.next l true (hnc true) p2 hp2_len hc
    exact hno3 true (L.save3 l true (hnc true) p1 p2 r (by omega) (by omega) (by omega)
     (rc_input true hp1) (rc_input true ⟨g2,hg2,hm2⟩) hr_rc)
  rcases Nat.lt_or_gt_of_ne hne with h1|h2
  ·exact hkill q' jl h1 hq' hjl_read
  ·exact hkill jl q' h2 hjl_read hq'
 obtain ⟨g_l,hgl,hm_l⟩:=hjl_read;have hjl_len: jl < gs.length:=(gEs.1 hgl).1
 have hparent_of_isC: ∀ b: Bool,IsC n' gs l b (n' + 1+jl) →
   ∃ (r: ℕ) (g_r: Gate),jl < r∧r < gs.length∧gs[r]? = some g_r ∧
    n' + 1+jl∈g_r.inputs∧o ≠ n' + 1+jl ∧
    (∀ q' : ℕ,Reads gs q' (n' + 1+jl) → q' = r) ∧
    ¬ IsC n' gs l b (n' + 1+r):=by
  intro b hc_jl
  have ho_njl: o ≠ n' + 1+jl:=by
   intro e;obtain ⟨c,hc_eq⟩:=hc_jl;obtain ⟨x,y,hxy⟩:=hnc b;apply hxy;rw[←L.hev,←L.hev,e];have hx:=st_val_const n' gs L.hcl l b (n' + 1+jl) c hc_eq (l.removeNth x);have hy:=st_val_const n' gs L.hcl l b (n' + 1+jl) c hc_eq (l.removeNth y);rw[upd_ins l b x,upd_ins l b y];exact hx.trans hy.symm
  obtain ⟨r,hr_gt,hr_read,hr_rc⟩:=L.next l b (hnc b) jl hjl_len hc_jl;obtain ⟨g_r,hgr,hm_r⟩:=hr_read;have hr_len: r < gs.length:=(gEs.1 hgr).1
  have hur: ∀ q' : ℕ,Reads gs q' (n' + 1+jl) → q' = r:=by
   intro q' hq'
   by_contra hne
   have hjl_lt_q' : jl < q' := by
    have:=reads_lt L.hcl hq';omega
   have hq'_rc: RC n' gs l b q' := rc_of_reads hq' hc_jl
   exact hno3 b (L.save3 l b (hnc b) jl r q' (by omega) (by omega) (by omega)
    (rc_input b ⟨g_l,hgl,hm_l⟩) hr_rc hq'_rc)
  have hnot_isC_r: ¬ IsC n' gs l b (n' + 1+r):=by
   intro hc_r;obtain ⟨r2,hr2_gt,_,hr2_rc⟩:=L.next l b (hnc b) r hr_len hc_r
   exact hno3 b (L.save3 l b (hnc b) jl r r2 (by omega) (by omega) (by omega)
    (rc_input b ⟨g_l,hgl,hm_l⟩) hr_rc hr2_rc)
  exact ⟨r,g_r,hr_gt,hr_len,hgr,hm_r,ho_njl,hur,hnot_isC_r⟩
 have hgr_shape: ∀ (b c: Bool) (r: ℕ) (g_r: Gate),
   gs[r]? = some g_r → n' + 1+jl∈g_r.inputs →
   stF n' gs l b (n' + 1+jl)=Stat.const c →
   ¬ IsC n' gs l b (n' + 1+r) →
   ∃ u: ℕ,u < n' + 1+r∧u ≠ n' + 1+jl ∧
    (g_r.inputs=[n' + 1+jl,u]∨g_r.inputs=[u,n' + 1+jl]) ∧
    g_r.op=(if c then GateOp.and else GateOp.or):=by
  intro b c r g_r hgr hmr hst hnotC;have hr_len: r < gs.length:=(gEs.1 hgr).1;have hc_jl: IsC n' gs l b (n' + 1+jl):=⟨c,hst⟩
  rcases gate_cases gs L.hcl r g_r hgr (n' + 1+jl) hmr with
   ⟨hopr,hinr,_⟩ | ⟨u,hinr,⟨hopr,_⟩ | ⟨hopr,_⟩⟩
  ·exfalso
   apply hnotC;obtain ⟨t,hst_r⟩:=st_gate n' gs L.hcl l b r g_r hgr;rw[hopr,hinr] at hst_r;simp only[lmC,lmN,hst,smp,sN0] at hst_r;exact ⟨!c,hst_r⟩
  ·have hult: u < n' + 1+r:=(L.hcl r g_r hgr).lt u (by rcases hinr with h|h <;> simp[h])
   have hune: u ≠ n' + 1+jl:=by
    intro e;subst e;apply L.no_alias hfnc r hr_len (n' + 1+jl) (by have := reads_lt L.hcl ⟨g_r,hgr,hmr⟩;omega);intro x;rw[vlg gs L.hcl x r g_r hgr,hopr]
    rcases hinr with h|h <;> rw[h] <;> simp[GateOp.eval]
   cases c with
   | true => exact ⟨u,hult,hune,hinr,by simp[hopr]⟩
   | false =>
    exfalso;apply hnotC
    obtain ⟨t,hst_r⟩:=st_gate n' gs L.hcl l b r g_r hgr;rw[hopr] at hst_r
    rcases hinr with h|h <;> rw[h] at hst_r <;>
     simp only[lmC,lmN,hst,smp,sA0] at hst_r
    ·cases hu: stF n' gs l b u with
     | const d => cases d <;> simp[hu] at hst_r <;> exact ⟨false,hst_r⟩
     | wire k => simp[hu] at hst_r;exact ⟨false,hst_r⟩
    ·cases hu: stF n' gs l b u with
     | const d => cases d <;> simp[hu] at hst_r <;> exact ⟨false,hst_r⟩
     | wire k => simp[hu] at hst_r;exact ⟨false,hst_r⟩
  ·have hult: u < n' + 1+r:=(L.hcl r g_r hgr).lt u (by rcases hinr with h|h <;> simp[h])
   have hune: u ≠ n' + 1+jl:=by
    intro e;subst e;apply L.no_alias hfnc r hr_len (n' + 1+jl) (by have := reads_lt L.hcl ⟨g_r,hgr,hmr⟩;omega);intro x;rw[vlg gs L.hcl x r g_r hgr,hopr]
    rcases hinr with h|h <;> rw[h] <;> simp[GateOp.eval]
   cases c with
   | false => exact ⟨u,hult,hune,hinr,by simp[hopr]⟩
   | true =>
    exfalso;apply hnotC
    obtain ⟨t,hst_r⟩:=st_gate n' gs L.hcl l b r g_r hgr;rw[hopr] at hst_r
    rcases hinr with h|h <;> rw[h] at hst_r <;>
     simp only[lmC,lmN,hst,smp,sO0] at hst_r
    ·cases hu: stF n' gs l b u with
     | const d => cases d <;> simp[hu] at hst_r <;> exact ⟨true,hst_r⟩
     | wire k => simp[hu] at hst_r;exact ⟨true,hst_r⟩
    ·cases hu: stF n' gs l b u with
     | const d => cases d <;> simp[hu] at hst_r <;> exact ⟨true,hst_r⟩
     | wire k => simp[hu] at hst_r;exact ⟨true,hst_r⟩
 rcases gate_cases gs L.hcl jl g_l hgl l.val hm_l with
  ⟨hop,hin,_⟩ | ⟨wl,hin,⟨hop,_⟩ | ⟨hop,_⟩⟩
 ·
  exfalso
  have hst_f: stF n' gs l false (n' + 1+jl)=Stat.const true:=by
   obtain ⟨t,h1⟩:=st_gate n' gs L.hcl l false jl g_l hgl;rw[hop,hin] at h1;simp only[lmC,lmN,stF_self,smp,sN0,Bool.not_false] at h1;exact h1
  have hst_t: stF n' gs l true (n' + 1+jl)=Stat.const false:=by
   obtain ⟨t,h1⟩:=st_gate n' gs L.hcl l true jl g_l hgl;rw[hop,hin] at h1;simp only[lmC,lmN,stF_self,smp,sN0,Bool.not_true] at h1;exact h1
  obtain ⟨r1,gr1,_,_,hgr1,hmr1,_,huniq1,hnotC1⟩:=hparent_of_isC false ⟨true,hst_f⟩;obtain ⟨r2,gr2,_,_,hgr2,hmr2,_,_,hnotC2⟩:=hparent_of_isC true ⟨false,hst_t⟩;have hr12: r2=r1:=huniq1 r2 ⟨gr2,hgr2,hmr2⟩;subst hr12;have hgeq: gr2=gr1:=osi (hgr2.symm.trans hgr1);subst hgeq;obtain ⟨_,_,_,_,hop1⟩:=hgr_shape false true r2 gr2 hgr2 hmr2 hst_f hnotC1;obtain ⟨_,_,_,_,hop2⟩:=hgr_shape true false r2 gr2 hgr2 hmr2 hst_t hnotC2;simp only[↓reduceIte,Bool.false_eq_true] at hop1 hop2;rw[hop1] at hop2;cases hop2
 ·
  have hwlt: wl < n' + 1+jl:=(L.hcl jl g_l hgl).lt wl (by rcases hin with h|h <;> simp[h])
  have hwne: wl≠l.val:=by
   intro e;subst e;apply L.no_alias hfnc jl hjl_len l.val (by have := l.isLt;omega);intro x;rw[vlg gs L.hcl x jl g_l hgl,hop]
   rcases hin with h|h <;> rw[h] <;> simp[GateOp.eval]
  have hst_f: stF n' gs l false (n' + 1+jl)=Stat.const false:=by
   obtain ⟨t,h1⟩:=st_gate n' gs L.hcl l false jl g_l hgl;rw[hop] at h1
   rcases hin with h|h <;> rw[h] at h1 <;>
    simp only[lmC,lmN,stF_self,smp,sA0] at h1
   ·cases hw: stF n' gs l false wl with
    | const d => cases d <;> simp[hw] at h1 <;> exact h1
    | wire k => simp[hw] at h1;exact h1
   ·cases hw: stF n' gs l false wl with
    | const d => cases d <;> simp[hw] at h1 <;> exact h1
    | wire k => simp[hw] at h1;exact h1
  obtain ⟨r,g_r,hlt,hr_len,hgr,hmr,ho_njl,hur,hnotC_r⟩ :=
   hparent_of_isC false ⟨false,hst_f⟩
  obtain ⟨u,hult,hune,hin_r,hop_r⟩:=hgr_shape false false r g_r hgr hmr hst_f hnotC_r;simp only[Bool.false_eq_true,↓reduceIte] at hop_r
  exact ⟨jl,wl,r,u,g_l,g_r,hlt,hr_len,hwlt,hwne,hult,hune,hon0,ho_njl,
   hgl,hgr,hin,hin_r,hul,hur,Or.inr ⟨hop,hop_r⟩⟩
 ·
  have hwlt: wl < n' + 1+jl:=(L.hcl jl g_l hgl).lt wl (by rcases hin with h|h <;> simp[h])
  have hwne: wl≠l.val:=by
   intro e;subst e;apply L.no_alias hfnc jl hjl_len l.val (by have := l.isLt;omega);intro x;rw[vlg gs L.hcl x jl g_l hgl,hop]
   rcases hin with h|h <;> rw[h] <;> simp[GateOp.eval]
  have hst_t: stF n' gs l true (n' + 1+jl)=Stat.const true:=by
   obtain ⟨t,h1⟩:=st_gate n' gs L.hcl l true jl g_l hgl;rw[hop] at h1
   rcases hin with h|h <;> rw[h] at h1 <;>
    simp only[lmC,lmN,stF_self,smp,sO0] at h1
   ·cases hw: stF n' gs l true wl with
    | const d => cases d <;> simp[hw] at h1 <;> exact h1
    | wire k => simp[hw] at h1;exact h1
   ·cases hw: stF n' gs l true wl with
    | const d => cases d <;> simp[hw] at h1 <;> exact h1
    | wire k => simp[hw] at h1;exact h1
  obtain ⟨r,g_r,hlt,hr_len,hgr,hmr,ho_njl,hur,hnotC_r⟩ :=
   hparent_of_isC true ⟨true,hst_t⟩
  obtain ⟨u,hult,hune,hin_r,hop_r⟩:=hgr_shape true true r g_r hgr hmr hst_t hnotC_r;simp only[↓reduceIte] at hop_r
  exact ⟨jl,wl,r,u,g_l,g_r,hlt,hr_len,hwlt,hwne,hult,hune,hon0,ho_njl,
   hgl,hgr,hin,hin_r,hul,hur,Or.inl ⟨hop,hop_r⟩⟩
def li2 (jl r j' : ℕ): ℕ := li1 r (li1 jl j')
def lw2 (n jl r w: ℕ): ℕ := lw1 n r (lw1 n jl w)
lemma li2i (jl r: ℕ): Function.Injective (li2 jl r) :=
 (li1i r).comp (li1i jl)
lemma lw2j (n jl r: ℕ): Function.Injective (lw2 n jl r) :=
 (lw1j n r).comp (lw1j n jl)
lemma li2nr (jl r j' : ℕ): li2 jl r j' ≠ r := li1n r _
lemma li2nj (jl r j' : ℕ) (hjr: jl < r): li2 jl r j' ≠ jl:=by
 unfold li2 li1;split_ifs <;> omega
lemma lw2nr (n jl r w: ℕ): lw2 n jl r w≠n+r := lw1n n r _
lemma lw2g (n jl r j' : ℕ): lw2 n jl r (n + j')=n+li2 jl r j' := by
 unfold lw2 li2;rw[lw1g,lw1g]
lemma lw2i (n jl r i: ℕ) (hi: i < n): lw2 n jl r i=i:=by
 unfold lw2;rw[lw1i n jl i hi,lw1i n r i hi]
lemma li2lt {jl r j' len: ℕ} (hjr: jl < r) (hr: r < len) (hj' : j' < len - 2) :
  li2 jl r j' < len:=by
 unfold li2 li1;split_ifs <;> omega
lemma li2s {jl r j len: ℕ} (hjr: jl < r) (hr: r < len) (hj: j < len) (h1: j≠jl) (h2: j≠r) :
  ∃ j' < len - 2,li2 jl r j' = j:=by
 let j1:=if j < r then j else j - 1
 have hj1_ne: j1≠jl:=by simp[j1];split_ifs <;> omega
 let j' := if j1 < jl then j1 else j1 - 1
 refine ⟨j',by simp[j',j1];split_ifs <;> omega,?_⟩
 unfold li2 li1;simp only[j',j1];split_ifs <;> omega
lemma lw2r {n jl r u w: ℕ} (hjr: jl < r) (h1: w≠n+jl) (h2: w≠n+r) :
  lw2 n jl r (rd n jl 0 (rd n r u w))=w:=by
 unfold lw2
 have hne1: rd n r u w≠n+jl:=by
  unfold rd;split_ifs <;> omega
 rw[lw1r n jl 0 (rd n r u w) hne1,lw1r n r u w h2]
lemma rd2l {n jl r u w: ℕ} :
  rd n jl 0 (rd n r u (lw2 n jl r w))=w:=by
 unfold lw2;rw[rd_liftW,rd_liftW]
lemma rmnj {n jl r u: ℕ} (C: Circuit) (hrb: ReadsBack n C)
  (hjr: jl < r) (hr: r < C.gates.length) (hu_ne: u≠n+jl) (hon0: C.output≠n+jl)
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r) :
  let Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩
  Cm0.output≠n+jl ∧
  ∀ j' < Cm0.gates.length,n+jl∉(gateAt Cm0 j').inputs:=by
 dsimp only
 have hlen: (rdel n r u C.gates).length=C.gates.length - 1:=by
  have:=rdel_length n r u C.gates hr;omega
 constructor
 ·change rd n r u C.output≠n+jl;unfold rd;split_ifs <;> omega
 ·intro j' hj' hmem
  have hj'_lt: j' < C.gates.length - 1:=by simp only[hlen] at hj';exact hj'
  have hlif:=r1l u C hrb hr j' hj'_lt;rw[hlif.2] at hmem;obtain ⟨a,ha,hrd⟩:=lmm.mp hmem
  have ha_eq: a=n+jl:=by
   unfold rd at hrd;split_ifs at hrd with h1 h2
   ·exact hrd
   ·exact absurd hrd hu_ne
   ·omega
  subst ha_eq
  have hj_lt: li1 r j' < C.gates.length:=by unfold li1;split_ifs <;> omega
  exact li1n r j' (hur (li1 r j') hj_lt ha)
lemma r2l {n jl r u: ℕ} (C: Circuit) (hcl: CL n C.gates)
  (hrb: ReadsBack n C) (hjr: jl < r) (hr: r < C.gates.length) (hu: u < n+r)
  (j' : ℕ) (hj' : j' < C.gates.length - 2) :
  let Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;let Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩
  (gateAt Cs0 j').op=(gateAt C (li2 jl r j')).op ∧
  (gateAt Cs0 j').inputs=(gateAt C (li2 jl r j')).inputs.map (fun w => rd n jl 0 (rd n r u w)):=by
 dsimp only
 set Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;set Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩;have hcl_mid: CL n Cm0.gates:=rdel_clean n r u C.gates hcl hr hu
 have hrb_mid: ReadsBack n Cm0:=fun j hj i hi =>
  (hcl_mid j _ (by simp[gateAt,List.getD,hj])).lt i hi
 have hlm: Cm0.gates.length=C.gates.length - 1:=by
  have:=rdel_length n r u C.gates hr;simp[Cm0];omega
 have hj_l_mid: jl < Cm0.gates.length:=by omega
 have h1:=r1l 0 Cm0 hrb_mid hj_l_mid j' (by omega);have h2:=r1l u C hrb hr (li1 jl j') (by unfold li1;split_ifs <;> omega)
 refine ⟨h1.1.trans h2.1,?_⟩
 rw[h1.2,h2.2,lmp];rfl
lemma r2in {n jl r u: ℕ} (C: Circuit) (hcl: CL n C.gates)
  (hrb: ReadsBack n C) (hjr: jl < r) (hr: r < C.gates.length) (hu: u < n+r)
  (hu_ne: u≠n+jl) (hon0: C.output≠n+jl)
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  (j' : ℕ) (hj' : j' < C.gates.length - 2)
  (hno_r: n+r∉(gateAt C (li2 jl r j')).inputs) :
  let Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;let Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩
  (gateAt C (li2 jl r j')).inputs=(gateAt Cs0 j').inputs.map (lw2 n jl r):=by
 dsimp only
 set Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;set Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩;have hlif:=r2l C hcl hrb hjr hr hu j' hj';rw[hlif.2,lmp]
 symm
 apply list_map_id_on;intro w hw
 have hne_r: w≠n+r:=fun e => hno_r (e ▸ hw)
 have hne_jl: w≠n+jl:=fun e =>
  li2nr jl r j' (hur (li2 jl r j') (li2lt hjr hr hj') (e ▸ hw))
 exact lw2r hjr hne_jl hne_r
lemma ot2u {n jl r u: ℕ} (C: Circuit) (hcl: CL n C.gates)
  (hrb: ReadsBack n C) (hjr: jl < r) (hr: r < C.gates.length) (hu: u < n+r)
  (hu_ne: u≠n+jl) (hon0: C.output≠n+jl)
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  {G L: Finset ℕ} {ρ : ℕ}
  (ht: IsOrTree n ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ G L ρ)
  (hGlt: ∀ j' ∈ G,j' < C.gates.length - 2)
  (hno_r: ∀ j' ∈ G,n+r∉(gateAt C (li2 jl r j')).inputs) :
  IsOrTree n C (G.image (li2 jl r)) (L.image (lw2 n jl r)) (lw2 n jl r ρ):=by
 set Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;have hcl_mid: CL n Cm0.gates:=rdel_clean n r u C.gates hcl hr hu
 have hrb_mid: ReadsBack n Cm0:=fun j hj i hi =>
  (hcl_mid j _ (by simp[gateAt,List.getD,hj])).lt i hi
 have hlm: Cm0.gates.length=C.gates.length - 1:=by
  have:=rdel_length n r u C.gates hr;simp[Cm0];omega
 have hj_l_mid: jl < Cm0.gates.length:=by omega
 obtain ⟨_,hmid_no_jl⟩:=rmnj C hrb hjr hr hu_ne hon0 hur
 have ht_mid: IsOrTree n Cm0 (G.image (li1 jl)) (L.image (lw1 n jl)) (lw1 n jl ρ) :=
  ot1u Cm0 hrb_mid hj_l_mid ht
   (fun j' hj' => by have := hGlt j' hj';omega)
   (fun j' hj' => hmid_no_jl (li1 jl j') (by
    have:=hGlt j' hj'
    change li1 jl j' < Cm0.gates.length
    rw[hlm];unfold li1;split_ifs <;> omega))
 have ht_C:=ot1u C hrb hr ht_mid
  (fun j1 hj1 => by
   rcases mI.mp hj1 with ⟨j',hj',rfl⟩
   have:=hGlt j' hj';unfold li1;split_ifs <;> omega)
  (fun j1 hj1 => by
   rcases mI.mp hj1 with ⟨j',hj',rfl⟩
   exact hno_r j' hj')
 have h1: (G.image (li1 jl)).image (li1 r)=G.image (li2 jl r):=by
  rw[Finset.image_image];rfl
 have h2: (L.image (lw1 n jl)).image (lw1 n r)=L.image (lw2 n jl r):=by
  rw[Finset.image_image];rfl
 rw[h1,h2] at ht_C;exact ht_C
lemma vlb {n jl r u: ℕ} (hn: 0 < n) (C: Circuit) (hcl: CL n C.gates)
  (hrb: ReadsBack n C) (hjr: jl < r) (hr: r < C.gates.length) (hu: u < n+r)
  (hu_ne: u≠n+jl) (hon0: C.output≠n+jl)
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  (x: Fin n→Bool) :
  let Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;let Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩
  ∀ w: ℕ,lw2 n jl r w < n+r →
   vl C.gates x (lw2 n jl r w)=vl Cs0.gates x w:=by
 dsimp only
 let Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;let Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩
 have hlm: Cm0.gates.length=C.gates.length - 1:=by
  have:=rdel_length n r u C.gates hr;simp[Cm0];omega
 have hj_l_mid: jl < Cm0.gates.length:=by omega
 have hcl_mid: CL n Cm0.gates:=rdel_clean n r u C.gates hcl hr hu;have hcl_sub: CL n Cs0.gates:=rdel_clean n jl 0 Cm0.gates hcl_mid hj_l_mid (by omega)
 have hlen_sub: Cs0.gates.length=C.gates.length - 2:=by
  have h2:=rdel_length n jl 0 Cm0.gates hj_l_mid;simp[Cs0] at h2 ⊢;omega
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hlt
  by_cases hwn: w < n
  ·rw[lw2i n jl r w hwn,vli _ _ w hwn,vli _ _ w hwn]
  ·set j' := w - n
   have hweq: w=n + j' := by omega
   rw[hweq,lw2g] at hlt ⊢
   have hj'lt: j' < C.gates.length - 2:=by
    unfold li2 li1 at hlt;split_ifs at hlt <;> omega
   have hlj_lt: li2 jl r j' < r:=by omega
   have hno_r: n+r∉(gateAt C (li2 jl r j')).inputs:=fun h => by
    have:=hrb (li2 jl r j') (by omega) (n+r) h;omega
   have hlif:=r2l C hcl hrb hjr hr hu j' hj'lt;have hinp:=r2in C hcl hrb hjr hr hu hu_ne hon0 hur j' hj'lt hno_r
   have hgC: C.gates[li2 jl r j']? = some (gateAt C (li2 jl r j')):=by
    simp[gateAt,List.getD,show li2 jl r j' < C.gates.length by omega]
   have hgS: Cs0.gates[j']? = some (gateAt Cs0 j'):=by
    simp[gateAt,List.getD,show j' < Cs0.gates.length by omega]
   rw[vlg C.gates hcl x (li2 jl r j') _ hgC,
     vlg Cs0.gates hcl_sub x j' _ hgS,←hlif.1,hinp,lmp]
   congr 1
   apply List.map_congr_left;intro a ha;have halt: a < n + j' := (hcl_sub j' _ hgS).lt a ha
   have ha_lw: lw2 n jl r a < n+r:=by
    have: lw2 n jl r a < lw2 n jl r (n + j'):=by
     unfold lw2 lw1;split_ifs <;> omega
    rw[lw2g] at this;omega
   exact ih a (by omega) ha_lw
lemma vlab {n jl r u: ℕ} (hn: 0 < n) (C: Circuit) (hcl: CL n C.gates)
  (hrb: ReadsBack n C) (hjr: jl < r) (hr: r < C.gates.length) (hu: u < n+r)
  (hu_ne: u≠n+jl) (hon0: C.output≠n+jl)
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  (x: Fin n→Bool) (hru: vl C.gates x (n+r)=vl C.gates x u) :
  let Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;let Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩
  ∀ w: ℕ,vl Cs0.gates x w=vl C.gates x (lw2 n jl r w):=by
 dsimp only
 let Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;let Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩;have hcl_mid: CL n Cm0.gates:=rdel_clean n r u C.gates hcl hr hu
 have hlm: Cm0.gates.length=C.gates.length - 1:=by
  have:=rdel_length n r u C.gates hr;simp[Cm0];omega
 have hj_l_mid: jl < Cm0.gates.length:=by omega
 obtain ⟨_,hmid_no_jl⟩:=rmnj C hrb hjr hr hu_ne hon0 hur;intro w
 have h1: vl Cm0.gates x (lw1 n jl w)=vl C.gates x (lw2 n jl r w):=by
  have:=rdel_all n r u C.gates hcl hr hu x hru (lw2 n jl r w)
  rw[show rd n r u (lw2 n jl r w)=lw1 n jl w from rd_liftW n r u (lw1 n jl w)] at this;exact this
 have h2_all: ∀ w: ℕ,vl Cs0.gates x w=vl Cm0.gates x (lw1 n jl w):=by
  have hcl_sub: CL n Cs0.gates:=rdel_clean n jl 0 Cm0.gates hcl_mid hj_l_mid (by omega)
  have hrb_mid: ReadsBack n Cm0:=fun j hj i hi =>
   (hcl_mid j _ (by simp[gateAt,List.getD,hj])).lt i hi
  have hlen_sub: Cs0.gates.length=Cm0.gates.length - 1:=by
   have:=rdel_length n jl 0 Cm0.gates hj_l_mid;simp[Cs0];omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   by_cases hwn: w < n
   ·rw[lw1i n jl w hwn,vli _ _ w hwn,vli _ _ w hwn]
   ·set j' := w - n
    have hweq: w=n + j' := by omega
    rw[hweq,lw1g]
    by_cases hj'lt: j' < Cs0.gates.length
    ·have hno:=hmid_no_jl (li1 jl j') (by
      change li1 jl j' < Cm0.gates.length
      rw[hlm];unfold li1;split_ifs <;> omega)
     have hlif:=r1l 0 Cm0 hrb_mid hj_l_mid j' (by omega);have hinp:=r1in 0 Cm0 hrb_mid hj_l_mid j' (by omega) hno
     have hgS: Cs0.gates[j']? = some (gateAt Cs0 j'):=by simp[gateAt,List.getD,hj'lt]
     have hgM: Cm0.gates[li1 jl j']? = some (gateAt Cm0 (li1 jl j')):=by
      simp[gateAt,List.getD,show li1 jl j' < Cm0.gates.length by unfold li1;split_ifs <;> omega]
     rw[vlg Cs0.gates hcl_sub x j' _ hgS,
       vlg Cm0.gates hcl_mid x (li1 jl j') _ hgM,hlif.1,hinp,lmp]
     congr 1
     apply List.map_congr_left;intro a ha;exact ih a (by have := (hcl_sub j' _ hgS).lt a ha;omega)
    ·rw[vl_beyond Cs0.gates x (n + j') (by omega),
       vl_beyond Cm0.gates x (n+li1 jl j') (by unfold li1;split_ifs <;> omega)]
 rw[h2_all w,h1]
def osG (n: ℕ) (C: Circuit) (G: Finset ℕ) (w: ℕ): Finset ℕ :=
 if h: n ≤ w∧w - n∈G then
  insert (w - n) ((gateAt C (w - n)).inputs.foldr
   (fun a acc => if ha: a < w then osG n C G a ∪ acc else acc) ∅)
 else ∅
termination_by w
def osL (n: ℕ) (C: Circuit) (G L: Finset ℕ) (w: ℕ): Finset ℕ :=
 if w∈L then {w}
 else if h: n ≤ w∧w - n∈G then
  (gateAt C (w - n)).inputs.foldr
   (fun a acc => if ha: a < w then osL n C G L a ∪ acc else acc) ∅
 else ∅
termination_by w
lemma orSubGates_leaf {n: ℕ} {C: Circuit} {G L: Finset ℕ} {ρ w: ℕ}
  (ht: IsOrTree n C G L ρ) (hw: w∈L): osG n C G w = ∅ := by
 rw[osG];simp[(ht.2.1 w hw).1]
lemma osLl {n: ℕ} {C: Circuit} {G L: Finset ℕ} {ρ w: ℕ}
  (ht: IsOrTree n C G L ρ) (hw: w∈L): osL n C G L w={w}:=by
 rw[osL];simp[hw]
lemma osGq {n: ℕ} {C: Circuit} (hrb: ReadsBack n C)
  {G L: Finset ℕ} {ρ j a b: ℕ} (ht: IsOrTree n C G L ρ)
  (hj: j∈G) (hjlt: j < C.gates.length) (hin: (gateAt C j).inputs=[a,b]) :
  osG n C G (n+j)=insert j (osG n C G a ∪ osG n C G b) ∧
  osL n C G L (n+j)=osL n C G L a ∪ osL n C G L b:=by
 have ha: a < n+j:=hrb j hjlt a (by simp[hin]);have hb: b < n+j:=hrb j hjlt b (by simp[hin])
 have hnotL: n+j∉L:=fun hL => (ht.2.1 (n+j) hL).1 ⟨by omega,by simpa using hj⟩
 constructor
 ·conv_lhs => rw[osG]
  have hcond: n ≤ n+j∧(n+j) - n∈G:=⟨by omega,by simpa using hj⟩;rw[dif_pos hcond]
  simp only[ascl,hin,List.foldr_cons,List.foldr_nil,
   ha,hb,↓reduceDIte,Finset.union_empty]
 ·conv_lhs => rw[osL]
  have hcond: n ≤ n+j∧(n+j) - n∈G:=⟨by omega,by simpa using hj⟩;rw[if_neg hnotL,dif_pos hcond]
  simp only[ascl,hin,
   List.foldr_cons,List.foldr_nil,ha,hb,↓reduceDIte,Finset.union_empty]
lemma osS {n: ℕ} {C: Circuit} (hrb: ReadsBack n C)
  {G L: Finset ℕ} {ρ : ℕ} (ht: IsOrTree n C G L ρ) (hGlt: ∀ j∈G,j < C.gates.length) :
  ∀ w: ℕ,osG n C G w⊆G∧osL n C G L w⊆L ∧
   (∀ g∈osG n C G w,n+g ≤ w):=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  by_cases hL: w∈L
  ·rw[orSubGates_leaf ht hL,osLl ht hL];exact ⟨Finset.empty_subset _,Finset.singleton_subset_iff.mpr hL,by simp⟩
  ·by_cases hG: n ≤ w∧w - n∈G
   ·set j:=w - n
    have hweq: w=n+j:=by omega
    have hj: j∈G:=hG.2;have hjlt: j < C.gates.length:=hGlt j hj;obtain ⟨a,b,hab⟩:=ll2.mp (ht.1 j hj).2.1;have ha: a < n+j:=hrb j hjlt a (by simp[hab]);have hb: b < n+j:=hrb j hjlt b (by simp[hab]);have hsub:=osGq hrb ht hj hjlt hab;rw[hweq,hsub.1,hsub.2];obtain ⟨haG,haL,hale⟩:=ih a (by omega);obtain ⟨hbG,hbL,hble⟩:=ih b (by omega)
    refine ⟨insert_subset_iff.mpr ⟨hj,Finset.union_subset haG hbG⟩,
     Finset.union_subset haL hbL,?_⟩
    intro g hg
    rcases mN.mp hg with rfl|h1
    ·exact le_rfl
    ·rcases mU.mp h1 with h2|h3
     ·have:=hale g h2;omega
     ·have:=hble g h3;omega
   ·have h1: osG n C G w = ∅ := by rw[osG];simp[hG]
    have h2: osL n C G L w = ∅ := by rw[osL];simp[hL,hG]
    rw[h1,h2];exact ⟨Finset.empty_subset _,Finset.empty_subset _,by simp⟩
lemma osV {n: ℕ} {C: Circuit} (hcl: CL n C.gates) (hrb: ReadsBack n C)
  {G L: Finset ℕ} {ρ : ℕ} (ht: IsOrTree n C G L ρ) (hGlt: ∀ j∈G,j < C.gates.length)
  (x: Fin n→Bool) :
  ∀ w: ℕ,(w∈L∨(n ≤ w∧w - n∈G)) →
   (vl C.gates x w=true ↔ ∃ v∈osL n C G L w,vl C.gates x v=true):=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw
  rcases hw with hL|hG
  ·rw[osLl ht hL];simp
  ·set j:=w - n
   have hweq: w=n+j:=by omega
   have hj: j∈G:=hG.2;have hjlt: j < C.gates.length:=hGlt j hj;obtain ⟨hop,hlen,hins⟩:=ht.1 j hj;obtain ⟨a,b,hab⟩:=ll2.mp hlen;have ha: a < n+j:=hrb j hjlt a (by simp[hab]);have hb: b < n+j:=hrb j hjlt b (by simp[hab]);have hsub:=osGq hrb ht hj hjlt hab
   have hg: C.gates[j]? = some (gateAt C j):=by simp[gateAt,List.getD,hjlt]
   rw[hweq,hsub.2,vlg C.gates hcl x j _ hg,hop,hab]
   simp only[GateOp.eval,lmC,lmN,lyC,lyN,
    id_eq,Bool.or_false,boT,mU]
   rw[ih a (by omega) (hins a (by simp[hab])),ih b (by omega) (hins b (by simp[hab]))]
   constructor
   ·rintro (⟨v,hv,hxv⟩ | ⟨v,hv,hxv⟩)
    ·exact ⟨v,Or.inl hv,hxv⟩
    ·exact ⟨v,Or.inr hv,hxv⟩
   ·rintro ⟨v,hv|hv,hxv⟩
    ·exact Or.inl ⟨v,hv,hxv⟩
    ·exact Or.inr ⟨v,hv,hxv⟩
lemma osT {n: ℕ} {C: Circuit} (hrb: ReadsBack n C)
  {G L: Finset ℕ} {ρ : ℕ} (ht: IsOrTree n C G L ρ) (hGlt: ∀ j∈G,j < C.gates.length) :
  ∀ w: ℕ,(w∈L∨(n ≤ w∧w - n∈G)) →
   IsOrTree n C (osG n C G w) (osL n C G L w) w:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw
  rcases hw with hL|hG
  ·rw[orSubGates_leaf ht hL,osLl ht hL]
   refine ⟨by simp,?_,by simp,by simp⟩
   intro u hu;rw[mS.mp hu];simp[readsIn]
  ·set j:=w - n
   have hweq: w=n+j:=by omega
   have hj: j∈G:=hG.2;have hjlt: j < C.gates.length:=hGlt j hj;obtain ⟨hop,hlen,hins⟩:=ht.1 j hj;obtain ⟨a,b,hab⟩:=ll2.mp hlen;have ha_lt: a < n+j:=hrb j hjlt a (by simp[hab]);have hb_lt: b < n+j:=hrb j hjlt b (by simp[hab]);have ha_mem:=hins a (by simp[hab]);have hb_mem:=hins b (by simp[hab])
   have hab_ne: a≠b:=by
    intro e;subst e
    have hcnt: 2 ≤ (gateAt C j).inputs.count a:=by rw[hab];simp
    have hle: (gateAt C j).inputs.count a ≤ readsIn C G a :=
     single_le_sum (f := fun k => (gateAt C k).inputs.count a) (fun _ _ => Nat.zero_le _) hj
    rcases ha_mem with haL|⟨han,haG⟩
    ·have:=(ht.2.1 a haL).2;split_ifs at this <;> omega
    ·have:=ht.2.2.1 (a - n) haG;rw[show n+(a - n)=a by omega] at this
     split_ifs at this <;> omega
   have hta:=ih a (by omega) ha_mem;have htb:=ih b (by omega) hb_mem;have hsub:=osGq hrb ht hj hjlt hab;set Ga:=osG n C G a;set La:=osL n C G L a;set Gb:=osG n C G b;set Lb:=osL n C G L b;obtain ⟨haGsub,haLsub,hale⟩:=osS hrb ht hGlt a;obtain ⟨hbGsub,hbLsub,hble⟩:=osS hrb ht hGlt b
   have hno_read_outside: ∀ (G1 L1: Finset ℕ) (r1: ℕ),
     IsOrTree n C G1 L1 r1→G1⊆G→L1⊆L →
     ∀ u: ℕ,(u∈L1∨(n ≤ u∧u - n∈G1)) → u≠r1 →
     ∀ k∈G,k∉G1 → u∉(gateAt C k).inputs:=by
    intro G1 L1 r1 ht1 hG1 hL1 u hu hne k hk hk1 hmem
    have hr1: readsIn C G1 u=1:=by
     rcases hu with huL|⟨hun,huG⟩
     ·have:=(ht1.2.1 u huL).2;simp[hne] at this;exact this
     ·have:=ht1.2.2.1 (u - n) huG;rw[show n+(u - n)=u by omega] at this
      simp[hne] at this;exact this
    have htot: readsIn C G u ≤ 1:=by
     rcases hu with huL|⟨hun,huG⟩
     ·have:=(ht.2.1 u (hL1 huL)).2;split_ifs at this <;> omega
     ·have:=ht.2.2.1 (u - n) (hG1 huG);rw[show n+(u - n)=u by omega] at this
      split_ifs at this <;> omega
    have hk_pos: 0 < (gateAt C k).inputs.count u:=lcpi.mpr hmem
    have hsum_le: readsIn C (insert k G1) u ≤ readsIn C G u :=
     sum_le_sum_of_subset (insert_subset_iff.mpr ⟨hk,hG1⟩)
    have hsum_eq: readsIn C (insert k G1) u=(gateAt C k).inputs.count u+readsIn C G1 u :=
     sum_insert hk1
    omega
   have ha_only_j: ∀ k∈G,k≠j → a∉(gateAt C k).inputs:=by
    intro k hk hkj hmem
    have htot: readsIn C G a ≤ 1:=by
     rcases ha_mem with haL|⟨han,haG⟩
     ·have:=(ht.2.1 a haL).2;split_ifs at this <;> omega
     ·have:=ht.2.2.1 (a - n) haG;rw[show n+(a - n)=a by omega] at this
      split_ifs at this <;> omega
    have h1: 1 ≤ (gateAt C j).inputs.count a:=lcpi.mpr (by simp[hab]);have h2: 1 ≤ (gateAt C k).inputs.count a:=lcpi.mpr hmem
    have hsub2: ({j,k}: Finset ℕ)⊆G:=by intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
    have hsum:=sum_le_sum_of_subset (f:=fun m => (gateAt C m).inputs.count a) hsub2
    rw[sum_pair (Ne.symm hkj)] at hsum;change _ ≤ readsIn C G a at hsum;omega
   have hb_only_j: ∀ k∈G,k≠j → b∉(gateAt C k).inputs:=by
    intro k hk hkj hmem
    have htot: readsIn C G b ≤ 1:=by
     rcases hb_mem with hbL|⟨hbn,hbG⟩
     ·have:=(ht.2.1 b hbL).2;split_ifs at this <;> omega
     ·have:=ht.2.2.1 (b - n) hbG;rw[show n+(b - n)=b by omega] at this
      split_ifs at this <;> omega
    have h1: 1 ≤ (gateAt C j).inputs.count b:=lcpi.mpr (by simp[hab]);have h2: 1 ≤ (gateAt C k).inputs.count b:=lcpi.mpr hmem
    have hsub2: ({j,k}: Finset ℕ)⊆G:=by intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
    have hsum:=sum_le_sum_of_subset (f:=fun m => (gateAt C m).inputs.count b) hsub2
    rw[sum_pair (Ne.symm hkj)] at hsum;change _ ≤ readsIn C G b at hsum;omega
   have hdisj_G: Disjoint Ga Gb:=by
    rw[disjoint_left];intro g hga hgb;have hne_inter: (Ga ∩ Gb).Nonempty:=⟨g,Finset.mem_inter.mpr ⟨hga,hgb⟩⟩;set gm:=(Ga ∩ Gb).max' hne_inter;have hgm: gm∈Ga ∩ Gb := max'_mem _ hne_inter;have hgm_a: gm∈Ga:=(Finset.mem_inter.mp hgm).1;have hgm_b: gm∈Gb:=(Finset.mem_inter.mp hgm).2
    by_cases h1: n+gm=a
    ·have hne_b: n+gm≠b:=by omega
     have hrb_gm:=htb.2.2.1 gm hgm_b;simp only[hne_b,↓reduceIte] at hrb_gm
     have hpos: 0 < ∑ k∈Gb,(gateAt C k).inputs.count (n+gm):=by
      change 0 < readsIn C Gb (n+gm);omega
     obtain ⟨k,hk,hcnt⟩:=exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos);have hmem: a∈(gateAt C k).inputs:=h1 ▸ lcpi.mp (Nat.pos_of_ne_zero hcnt)
     have hkj: k≠j:=by have:=hble k hk;omega
     exact ha_only_j k (hbGsub hk) hkj hmem
    ·by_cases h2: n+gm=b
     ·have hra_gm:=hta.2.2.1 gm hgm_a;simp only[h1,↓reduceIte] at hra_gm
      have hpos: 0 < ∑ k∈Ga,(gateAt C k).inputs.count (n+gm):=by
       change 0 < readsIn C Ga (n+gm);omega
      obtain ⟨k,hk,hcnt⟩:=exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos);have hmem: b∈(gateAt C k).inputs:=h2 ▸ lcpi.mp (Nat.pos_of_ne_zero hcnt)
      have hkj: k≠j:=by have:=hale k hk;omega
      exact hb_only_j k (haGsub hk) hkj hmem
     ·have hra_gm:=hta.2.2.1 gm hgm_a;simp only[h1,↓reduceIte] at hra_gm
      have hpos: 0 < ∑ k∈Ga,(gateAt C k).inputs.count (n+gm):=by
       change 0 < readsIn C Ga (n+gm);omega
      obtain ⟨ka,hka,hcnta⟩:=exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos);have hmema: n+gm∈(gateAt C ka).inputs:=lcpi.mp (Nat.pos_of_ne_zero hcnta)
      have hka_gt: gm < ka:=by
       have:=hrb ka (hGlt ka (haGsub hka)) (n+gm) hmema;omega
      have hka_not_b: ka∉Gb:=fun hkb => by
       have hle_m:=Finset.le_max' (Ga ∩ Gb) ka (Finset.mem_inter.mpr ⟨hka,hkb⟩);omega
      exact hno_read_outside Gb Lb b htb hbGsub hbLsub (n+gm)
       (Or.inr ⟨by omega,by simpa using hgm_b⟩) h2 ka (haGsub hka) hka_not_b hmema
   have hj_not_Ga: j∉Ga:=fun h => by have:=hale j h;omega
   have hj_not_Gb: j∉Gb:=fun h => by have:=hble j h;omega
   have hj_not_Gab: j∉Ga ∪ Gb:=by simp[hj_not_Ga,hj_not_Gb]
   have hrsp: ∀ u: ℕ,
     readsIn C (insert j (Ga ∪ Gb)) u =
      (gateAt C j).inputs.count u+readsIn C Ga u+readsIn C Gb u:=by
    intro u;unfold readsIn;rw[sum_insert hj_not_Gab,Finset.sum_union hdisj_G];omega
   have hLa_no_Gb: ∀ u∈La,readsIn C Gb u=0:=by
    intro u hu;apply sum_eq_zero;intro k hk;rw[lcz]
    by_cases hua: u=a
    ·subst hua;exact ha_only_j k (hbGsub hk) (fun e => hj_not_Gb (e ▸ hk))
    ·exact hno_read_outside Ga La a hta haGsub haLsub u (Or.inl hu) hua k (hbGsub hk)
      (Finset.disjoint_right.mp hdisj_G hk)
   have hLb_no_Ga: ∀ u∈Lb,readsIn C Ga u=0:=by
    intro u hu;apply sum_eq_zero;intro k hk;rw[lcz]
    by_cases hub: u=b
    ·subst hub;exact hb_only_j k (haGsub hk) (fun e => hj_not_Ga (e ▸ hk))
    ·exact hno_read_outside Gb Lb b htb hbGsub hbLsub u (Or.inl hu) hub k (haGsub hk)
      (disjoint_left.mp hdisj_G hk)
   have hGa_no_Gb: ∀ g∈Ga,readsIn C Gb (n+g)=0:=by
    intro g hg;apply sum_eq_zero;intro k hk;rw[lcz]
    by_cases hga: n+g=a
    ·rw[hga];exact ha_only_j k (hbGsub hk) (fun e => hj_not_Gb (e ▸ hk))
    ·exact hno_read_outside Ga La a hta haGsub haLsub (n+g)
      (Or.inr ⟨by omega,by simpa using hg⟩) hga k (hbGsub hk)
      (Finset.disjoint_right.mp hdisj_G hk)
   have hGb_no_Ga: ∀ g∈Gb,readsIn C Ga (n+g)=0:=by
    intro g hg;apply sum_eq_zero;intro k hk;rw[lcz]
    by_cases hgb: n+g=b
    ·rw[hgb];exact hb_only_j k (haGsub hk) (fun e => hj_not_Ga (e ▸ hk))
    ·exact hno_read_outside Gb Lb b htb hbGsub hbLsub (n+g)
      (Or.inr ⟨by omega,by simpa using hg⟩) hgb k (haGsub hk)
      (disjoint_left.mp hdisj_G hk)
   rw[hweq,hsub.1,hsub.2]
   refine ⟨?_,?_,?_,?_⟩
   ·intro k hk
    rcases mN.mp hk with rfl|h1
    ·refine ⟨hop,hlen,fun i hi => ?_⟩
     rw[hab] at hi;simp only[lmc,lnn,or_false] at hi
     rcases hi with rfl|rfl
     ·by_cases hGa_e: Ga = ∅
      ·have hLa_eq:=hta.2.2.2;simp[hGa_e] at hLa_eq
       left;exact Finset.mem_union_left _ (by rw[hLa_eq];simp)
      ·have hLa_eq:=hta.2.2.2;simp[hGa_e] at hLa_eq;obtain ⟨ga,hga,rfl⟩:=hLa_eq
       right;exact ⟨by omega,mNo (Finset.mem_union_left _ (by simpa using hga))⟩
     ·by_cases hGb_e: Gb = ∅
      ·have hLb_eq:=htb.2.2.2;simp[hGb_e] at hLb_eq
       left;exact Finset.mem_union_right _ (by rw[hLb_eq];simp)
      ·have hLb_eq:=htb.2.2.2;simp[hGb_e] at hLb_eq;obtain ⟨gb,hgb,rfl⟩:=hLb_eq
       right;exact ⟨by omega,mNo (Finset.mem_union_right _ (by simpa using hgb))⟩
    ·rcases mU.mp h1 with hka|hkb
     ·obtain ⟨opk,lenk,insk⟩:=hta.1 k hka
      refine ⟨opk,lenk,fun i hi => ?_⟩
      rcases insk i hi with h1|⟨h2,h3⟩
      ·exact Or.inl (Finset.mem_union_left _ h1)
      ·exact Or.inr ⟨h2,mNo (Finset.mem_union_left _ h3)⟩
     ·obtain ⟨opk,lenk,insk⟩:=htb.1 k hkb
      refine ⟨opk,lenk,fun i hi => ?_⟩
      rcases insk i hi with h1|⟨h2,h3⟩
      ·exact Or.inl (Finset.mem_union_right _ h1)
      ·exact Or.inr ⟨h2,mNo (Finset.mem_union_right _ h3)⟩
   ·intro u hu;have huL: u∈L:=(Finset.union_subset haLsub hbLsub) hu
    have hnotG: ¬ (n ≤ u∧u - n∈insert j (Ga ∪ Gb)):=fun ⟨h1,h2⟩ =>
     (ht.2.1 u huL).1 ⟨h1,insert_subset_iff.mpr ⟨hj,Finset.union_subset haGsub hbGsub⟩ h2⟩
    have hune: u≠n+j:=fun e => hnotG ⟨by omega,by simp[e]⟩
    refine ⟨hnotG,?_⟩
    rw[hrsp u,if_neg hune]
    rcases mU.mp hu with hua|hub
    ·rw[hLa_no_Gb u hua,(hta.2.1 u hua).2]
     by_cases he: u=a
     ·subst he;rw[hab];simp[List.count_cons,Ne.symm hab_ne]
     ·have hnb: u≠b:=fun eb => by
       subst eb
       have:=hno_read_outside Ga La a hta haGsub haLsub u (Or.inl hua) he j hj hj_not_Ga
       exact this (by simp[hab])
      rw[hab,lcz.mpr (by simp[he,hnb])];simp[he]
    ·rw[hLb_no_Ga u hub,(htb.2.1 u hub).2]
     by_cases he: u=b
     ·subst he;rw[hab];simp[hab_ne]
     ·have hna: u≠a:=fun ea => by
       subst ea
       have:=hno_read_outside Gb Lb b htb hbGsub hbLsub u (Or.inl hub) he j hj hj_not_Gb
       exact this (by simp[hab])
      rw[hab,lcz.mpr (by simp[hna,he])];simp[he]
   ·intro g hg;rw[hrsp (n+g)]
    rcases mN.mp hg with rfl|h1
    ·simp only[↓reduceIte]
     have h0: (gateAt C j).inputs.count (n+j)=0:=by
      rw[hab];simp[List.count_cons,Nat.ne_of_lt ha_lt,Nat.ne_of_lt hb_lt]
     have h1: readsIn C Ga (n+j)=0:=sum_eq_zero fun k hk => by
      rw[lcz];intro hm
      have:=hrb k (hGlt k (haGsub hk)) (n+j) hm
      have:=hale k hk;omega
     have h2: readsIn C Gb (n+j)=0:=sum_eq_zero fun k hk => by
      rw[lcz];intro hm
      have:=hrb k (hGlt k (hbGsub hk)) (n+j) hm
      have:=hble k hk;omega
     omega
    ·rcases mU.mp h1 with hga|hgb
     ·have hne_j: n+g≠n+j:=by have:=hale g hga;omega
      simp only[hne_j,↓reduceIte];rw[hGa_no_Gb g hga,hta.2.2.1 g hga]
      by_cases he: n+g=a
      ·rw[he,hab];simp[List.count_cons,Ne.symm hab_ne]
      ·have hnb: n+g≠b:=fun eb => by
        have:=hno_read_outside Ga La a hta haGsub haLsub (n+g)
         (Or.inr ⟨by omega,by simpa using hga⟩) he j hj hj_not_Ga
        exact this (by rw[eb,hab];simp)
       rw[hab,lcz.mpr (by simp[he,hnb])];simp[he]
     ·have hne_j: n+g≠n+j:=by have:=hble g hgb;omega
      simp only[hne_j,↓reduceIte];rw[hGb_no_Ga g hgb,htb.2.2.1 g hgb]
      by_cases he: n+g=b
      ·rw[he,hab];simp[hab_ne]
      ·have hna: n+g≠a:=fun ea => by
        have:=hno_read_outside Gb Lb b htb hbGsub hbLsub (n+g)
         (Or.inr ⟨by omega,by simpa using hgb⟩) he j hj hj_not_Gb
        exact this (by rw[ea,hab];simp)
       rw[hab,lcz.mpr (by simp[hna,he])];simp[he]
   ·simp only[insert_ne_empty,↓reduceIte];exact ⟨j,mNs _ _,rfl⟩
lemma osC2 {n: ℕ} {C: Circuit} (hrb: ReadsBack n C)
  {G L: Finset ℕ} {ρ j: ℕ} (ht: IsOrTree n C G L ρ)
  (hGlt: ∀ k∈G,k < C.gates.length) (hj: j∈G) :
  2 ≤ (osL n C G L (n+j)).card:=by
 have hsub:=osT hrb ht hGlt (n+j) (Or.inr ⟨by omega,by simpa using hj⟩);have hcard:=tree_card n C _ _ (n+j) hsub
 have hjmem: j∈osG n C G (n+j):=by
  obtain ⟨a,b,hab⟩:=ll2.mp (ht.1 j hj).2.1;rw[(osGq hrb ht hj (hGlt j hj) hab).1];exact mNs _ _
 have hpos: 1 ≤ (osG n C G (n+j)).card:=one_le_card.mpr ⟨j,hjmem⟩;omega
lemma osRL {n: ℕ} {C: Circuit} (hrb: ReadsBack n C)
  {G L: Finset ℕ} {ρ : ℕ} (ht: IsOrTree n C G L ρ) (hGlt: ∀ k∈G,k < C.gates.length) :
  osG n C G ρ = G∧osL n C G L ρ = L:=by
 have hρ_mem: ρ ∈ L∨(n ≤ ρ ∧ ρ - n∈G):=by
  by_cases hG: G = ∅
  ·have h1:=ht.2.2.2;simp[hG] at h1;left;rw[h1];simp
  ·have h1:=ht.2.2.2;simp[hG] at h1;obtain ⟨j,hj,rfl⟩:=h1
   right;exact ⟨by omega,by simpa using hj⟩
 have hsub:=osT hrb ht hGlt ρ hρ_mem;obtain ⟨hGsub,hLsub,_⟩:=osS hrb ht hGlt ρ
 have hGeq: osG n C G ρ = G:=by
  apply Finset.Subset.antisymm hGsub;intro g hg
  by_contra hnot
  have hne: (G \ osG n C G ρ).Nonempty:=⟨g,mem_sdiff.mpr ⟨hg,hnot⟩⟩;set gm:=(G \ osG n C G ρ).max' hne;have hgm := max'_mem _ hne;have hgmG: gm∈G:=(mem_sdiff.mp hgm).1;have hgmN: gm∉osG n C G ρ := (mem_sdiff.mp hgm).2
  have hne_ρ : n+gm ≠ ρ := by
   intro e
   have hmem_self: gm∈osG n C G (n+gm):=by
    obtain ⟨a,b,hab⟩:=ll2.mp (ht.1 gm hgmG).2.1;rw[(osGq hrb ht hgmG (hGlt gm hgmG) hab).1];exact mNs _ _
   exact hgmN (e ▸ hmem_self)
  have hr:=ht.2.2.1 gm hgmG;simp only[hne_ρ,↓reduceIte] at hr
  have hpos: 0 < ∑ k∈G,(gateAt C k).inputs.count (n+gm):=by
   change 0 < readsIn C G (n+gm);omega
  obtain ⟨k,hkG,hcnt⟩:=exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos);have hmem: n+gm∈(gateAt C k).inputs:=lcpi.mp (Nat.pos_of_ne_zero hcnt)
  have hlt: gm < k:=by have:=hrb k (hGlt k hkG) (n+gm) hmem;omega
  have hk_in: k∈osG n C G ρ := by
   by_contra hkn
   have hle:=Finset.le_max' (G \ osG n C G ρ) k (mem_sdiff.mpr ⟨hkG,hkn⟩);omega
  rcases (hsub.1 k hk_in).2.2 (n+gm) hmem with hL' | ⟨_,hG'⟩
  ·exact (ht.2.1 (n+gm) (hLsub hL')).1 ⟨by omega,by simpa using hgmG⟩
  ·exact hgmN (by simpa using hG')
 have hLeq: osL n C G L ρ = L:=by
  apply eq_of_subset_of_card_le hLsub;have c1:=tree_card n C _ _ ρ ht;have c2:=tree_card n C _ _ ρ hsub;rw[hGeq] at c2;omega
 exact ⟨hGeq,hLeq⟩
lemma otrc {n: ℕ} {C: Circuit} (hrb: ReadsBack n C)
  {G L: Finset ℕ} {ρ ju a b: ℕ} (ht: IsOrTree n C G L ρ)
  (hGlt: ∀ k∈G,k < C.gates.length)
  (hju: ju∈G) (hin: (gateAt C ju).inputs=[a,b])
  (haL: a∈L) (hbL: b∈L) :
  IsOrTree n C (G.erase ju) (insert (n+ju) ((L.erase a).erase b)) ρ := by
 have hab_ne: a≠b:=by
  intro e;subst e
  have hcnt: 2 ≤ (gateAt C ju).inputs.count a:=by rw[hin];simp
  have hle: (gateAt C ju).inputs.count a ≤ readsIn C G a :=
   single_le_sum (f := fun k => (gateAt C k).inputs.count a) (fun _ _ => Nat.zero_le _) hju
  have hr:=(ht.2.1 a haL).2;split_ifs at hr <;> omega
 have ha_ne_ρ : a ≠ ρ := by
  intro e;have hr := (ht.2.1 a haL).2;rw[if_pos e] at hr
  have h1: 1 ≤ (gateAt C ju).inputs.count a:=by rw[hin];simp
  have hle: (gateAt C ju).inputs.count a ≤ readsIn C G a :=
   single_le_sum (f := fun k => (gateAt C k).inputs.count a) (fun _ _ => Nat.zero_le _) hju
  omega
 have hb_ne_ρ : b ≠ ρ := by
  intro e;have hr := (ht.2.1 b hbL).2;rw[if_pos e] at hr
  have h1: 1 ≤ (gateAt C ju).inputs.count b:=by rw[hin];simp
  have hle: (gateAt C ju).inputs.count b ≤ readsIn C G b :=
   single_le_sum (f := fun k => (gateAt C k).inputs.count b) (fun _ _ => Nat.zero_le _) hju
  omega
 have hreads_erase: ∀ w: ℕ,readsIn C G w=(gateAt C ju).inputs.count w+readsIn C (G.erase ju) w :=
  fun w => (add_sum_erase G (fun k => (gateAt C k).inputs.count w) hju).symm
 have hno_a: ∀ k∈G.erase ju,a∉(gateAt C k).inputs:=by
  intro k hk hmem;have h1:=(ht.2.1 a haL).2;rw[if_neg ha_ne_ρ] at h1
  have h2: (gateAt C ju).inputs.count a=1:=by rw[hin];simp[List.count_cons,Ne.symm hab_ne]
  have h3: 1 ≤ (gateAt C k).inputs.count a:=lcpi.mpr hmem
  have h4: (gateAt C k).inputs.count a ≤ readsIn C (G.erase ju) a :=
   single_le_sum (f := fun m => (gateAt C m).inputs.count a) (fun _ _ => Nat.zero_le _) hk
  have h5:=hreads_erase a;omega
 have hno_b: ∀ k∈G.erase ju,b∉(gateAt C k).inputs:=by
  intro k hk hmem;have h1:=(ht.2.1 b hbL).2;rw[if_neg hb_ne_ρ] at h1
  have h2: (gateAt C ju).inputs.count b=1:=by rw[hin];simp[List.count_cons,hab_ne]
  have h3: 1 ≤ (gateAt C k).inputs.count b:=lcpi.mpr hmem
  have h4: (gateAt C k).inputs.count b ≤ readsIn C (G.erase ju) b :=
   single_le_sum (f := fun m => (gateAt C m).inputs.count b) (fun _ _ => Nat.zero_le _) hk
  have h5:=hreads_erase b;omega
 refine ⟨?_,?_,?_,?_⟩
 ·intro k hk;have hkG: k∈G:=mEo hk;obtain ⟨opk,lenk,insk⟩:=ht.1 k hkG
  refine ⟨opk,lenk,fun i hi => ?_⟩
  have hia: i≠a:=fun e => hno_a k hk (e ▸ hi)
  have hib: i≠b:=fun e => hno_b k hk (e ▸ hi)
  rcases insk i hi with hiL|⟨hin_ge,hiG⟩
  ·exact Or.inl (mNo (mE.mpr ⟨hib,mE.mpr ⟨hia,hiL⟩⟩))
  ·by_cases hje: i - n=ju
   ·left;exact mN.mpr (Or.inl (by omega))
   ·right;exact ⟨hin_ge,mE.mpr ⟨hje,hiG⟩⟩
 ·intro w hw
  rcases mN.mp hw with rfl | hw'
  ·refine ⟨by simp,?_⟩
   have h0: (gateAt C ju).inputs.count (n+ju)=0:=by
    rw[lcz];intro hm
    have:=hrb ju (hGlt ju hju) (n+ju) hm;omega
   have h1:=hreads_erase (n+ju);have h2:=ht.2.2.1 ju hju;omega
  ·obtain ⟨hwb,hw2⟩:=mE.mp hw';obtain ⟨hwa,hwL⟩:=mE.mp hw2
   refine ⟨fun ⟨h1,h2⟩ => (ht.2.1 w hwL).1 ⟨h1,mEo h2⟩,?_⟩
   have h0: (gateAt C ju).inputs.count w=0:=by
    rw[hin,lcz];simp[hwa,hwb]
   have h1:=hreads_erase w;have h2:=(ht.2.1 w hwL).2;omega
 ·intro g hg;have hgG: g∈G:=mEo hg
  have hga: n+g≠a:=fun e => (ht.2.1 a haL).1 ⟨by omega,by simpa [←e] using hgG⟩
  have hgb: n+g≠b:=fun e => (ht.2.1 b hbL).1 ⟨by omega,by simpa [←e] using hgG⟩
  have h0: (gateAt C ju).inputs.count (n+g)=0:=by
   rw[hin,lcz];simp[hga,hgb]
  have h1:=hreads_erase (n+g);have h2:=ht.2.2.1 g hgG;omega
 ·by_cases hGe: G.erase ju = ∅
  ·simp only[hGe,↓reduceIte]
   have hGeq: G={ju}:=by
    ext k;simp only[mS]
    constructor
    ·intro hk;by_contra hne;exact notMem_empty k (hGe ▸ mE.mpr ⟨hne,hk⟩)
    ·rintro rfl;exact hju
   have hρ_eq: ρ = n+ju:=by
    have h1:=ht.2.2.2;have hne: G ≠ ∅ := nonempty_iff_ne_empty.mp ⟨ju,hju⟩;simp only[hne,↓reduceIte] at h1;obtain ⟨g0,hg0,hρ⟩:=h1;rw[hGeq] at hg0;rw[mS.mp hg0] at hρ;exact hρ
   have hLcard: L.card=2:=by have:=tree_card n C G L ρ ht;rw[hGeq] at this;simp at this;exact this
   have hLeq: L={a,b}:=Eq.symm (eq_of_subset_of_card_le
    (fun x hx => by simp at hx;rcases hx with rfl|rfl <;> assumption)
    (by rw[card_pair hab_ne];omega))
   rw[hρ_eq,hLeq]
   ext x;simp only[mN,mE,mS]
   tauto
  ·simp only[hGe,↓reduceIte];have hGne: G ≠ ∅ := nonempty_iff_ne_empty.mp ⟨ju,hju⟩;have h1:=ht.2.2.2;simp only[hGne,↓reduceIte] at h1;obtain ⟨g0,hg0,hρ⟩:=h1
   by_cases hgj: g0=ju
   ·exfalso
    have hne' : (G.erase ju).Nonempty:=nonempty_iff_ne_empty.mpr hGe;set gm:=(G.erase ju).max' hne';have hgm := max'_mem _ hne';have hgm_ne: gm≠ju:=(mE.mp hgm).1;have hgmG: gm∈G:=mEo hgm;have hrm:=ht.2.2.1 gm hgmG;rw[hρ,hgj,if_neg (by omega)] at hrm
    have hpos: 0 < ∑ k∈G,(gateAt C k).inputs.count (n+gm):=by change 0 < readsIn C G (n+gm);omega
    obtain ⟨k,hkG,hcnt⟩:=exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos);have hmem: n+gm∈(gateAt C k).inputs:=lcpi.mp (Nat.pos_of_ne_zero hcnt)
    by_cases hkj: k=ju
    ·rw[hkj,hin] at hmem;simp only[lmc,lnn,or_false] at hmem
     rcases hmem with e|e
     ·exact (ht.2.1 a haL).1 ⟨by omega,by simpa [←e] using hgmG⟩
     ·exact (ht.2.1 b hbL).1 ⟨by omega,by simpa [←e] using hgmG⟩
    ·have hle:=Finset.le_max' (G.erase ju) k (mE.mpr ⟨hkj,hkG⟩);have hlt:=hrb k (hGlt k hkG) (n+gm) hmem;omega
   ·exact ⟨g0,mE.mpr ⟨hgj,hg0⟩,hρ⟩
lemma ot2r {n jl r u: ℕ} (C: Circuit) (hcl: CL n C.gates)
  (hrb: ReadsBack n C) (hjr: jl < r) (hr: r < C.gates.length) (hu: u < n+r)
  (hu_ne: u≠n+jl) (hon0: C.output≠n+jl)
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  {G L: Finset ℕ} {ρ w_old: ℕ}
  (ht: IsOrTree n ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ G L ρ)
  (hGlt: ∀ j' ∈ G,j' < C.gates.length - 2)
  (hw_old: w_old∈L) (hu_eq: rd n jl 0 u=w_old)
  (hr_read: ∀ j' ∈ G,n+r∈(gateAt C (li2 jl r j')).inputs →
   w_old∈(gateAt ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ j').inputs)
  (hread_at: ∀ j' ∈ G,w_old∈(gateAt ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ j').inputs →
   n+r∈(gateAt C (li2 jl r j')).inputs) :
  IsOrTree n C (G.image (li2 jl r))
   (insert (n+r) ((L.erase w_old).image (lw2 n jl r)))
   (if w_old = ρ then n+r else lw2 n jl r ρ):=by
 set Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;set Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩
 by_cases hwr: w_old = ρ
 ·
  have hGe: G = ∅ := by
   by_contra hne
   have h1:=ht.2.2.2;simp only[hne,↓reduceIte] at h1;obtain ⟨g0,hg0,hρ⟩:=h1;exact (ht.2.1 w_old hw_old).1 ⟨by omega,by rw[hwr,hρ,ascl];exact hg0⟩
  have hLe: L={w_old}:=by
   have h1:=ht.2.2.2;simp only[hGe,↓reduceIte] at h1;rw[h1,hwr]
  simp only[hGe,hLe,hwr,↓reduceIte,Finset.image_empty,Finset.erase_singleton]
  refine ⟨by simp,?_,by simp,by simp⟩
  intro w hw;rw[mS.mp hw];simp[readsIn]
 ·
  simp only[hwr,↓reduceIte];have hr_old:=(ht.2.1 w_old hw_old).2;simp only[hwr,↓reduceIte] at hr_old
  have hpos: 0 < ∑ k∈G,(gateAt Cs0 k).inputs.count w_old:=by change 0 < readsIn Cs0 G w_old;omega
  obtain ⟨k0,hk0,hcnt0⟩:=exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos);have hmem0: w_old∈(gateAt Cs0 k0).inputs:=lcpi.mp (Nat.pos_of_ne_zero hcnt0)
  have huniq_k0: ∀ k∈G,w_old∈(gateAt Cs0 k).inputs → k=k0:=by
   intro k hk hmem
   by_contra hne
   have h1: 1 ≤ (gateAt Cs0 k0).inputs.count w_old:=lcpi.mpr hmem0;have h2: 1 ≤ (gateAt Cs0 k).inputs.count w_old:=lcpi.mpr hmem
   have hsub: ({k0,k}: Finset ℕ)⊆G:=by intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
   have hsum:=sum_le_sum_of_subset (f:=fun m => (gateAt Cs0 m).inputs.count w_old) hsub
   rw[sum_pair (Ne.symm hne)] at hsum;change _ ≤ readsIn Cs0 G w_old at hsum;omega
  have hlif0:=r2l C hcl hrb hjr hr hu k0 (hGlt k0 hk0)
  have hlen0: (gateAt C (li2 jl r k0)).inputs.length=2:=by
   have:=(ht.1 k0 hk0).2.1;rw[hlif0.2,llm] at this;exact this
  obtain ⟨x1,x2,hx12⟩:=ll2.mp hlen0
  have hsub0: (gateAt Cs0 k0).inputs =
    [rd n jl 0 (rd n r u x1),rd n jl 0 (rd n r u x2)] := by rw[hlif0.2,hx12];rfl
  have hx_nr: n+r∈(gateAt C (li2 jl r k0)).inputs:=hread_at k0 hk0 hmem0
  have hcnt0_eq1: (gateAt Cs0 k0).inputs.count w_old=1:=by
   have hle: (gateAt Cs0 k0).inputs.count w_old ≤ readsIn Cs0 G w_old :=
    single_le_sum (f := fun m => (gateAt Cs0 m).inputs.count w_old) (fun _ _ => Nat.zero_le _) hk0
   have hge: 1 ≤ (gateAt Cs0 k0).inputs.count w_old:=lcpi.mpr hmem0;omega
  have hx12_shape: ∃ y: ℕ,y≠w_old ∧
    (((gateAt C (li2 jl r k0)).inputs=[n+r,lw2 n jl r y] ∧
     (gateAt Cs0 k0).inputs=[w_old,y]) ∨
    ((gateAt C (li2 jl r k0)).inputs=[lw2 n jl r y,n+r] ∧
     (gateAt Cs0 k0).inputs=[y,w_old])):=by
   rw[hx12] at hx_nr;simp only[lmc,lnn,or_false] at hx_nr
   have hne_jl1: x1≠n+jl:=fun e =>
    li2nr jl r k0 (hur (li2 jl r k0) (li2lt hjr hr (hGlt k0 hk0)) (by rw[hx12,e];simp))
   have hne_jl2: x2≠n+jl:=fun e =>
    li2nr jl r k0 (hur (li2 jl r k0) (li2lt hjr hr (hGlt k0 hk0)) (by rw[hx12,e];simp))
   rcases hx_nr with rfl|rfl
   ·have hne2: x2≠n+r:=by
     intro e;subst e;rw[rd_eq,hu_eq] at hsub0;rw[hsub0] at hcnt0_eq1;simp at hcnt0_eq1
    refine ⟨rd n jl 0 (rd n r u x2),?_,Or.inl ⟨?_,?_⟩⟩
    ·intro e;rw[rd_eq,hu_eq,e] at hsub0;rw[hsub0] at hcnt0_eq1;simp at hcnt0_eq1
    ·rw[hx12,lw2r hjr hne_jl2 hne2]
    ·rw[hsub0,rd_eq,hu_eq]
   ·have hne1: x1≠n+r:=by
     intro e;subst e;rw[rd_eq,hu_eq] at hsub0;rw[hsub0] at hcnt0_eq1;simp at hcnt0_eq1
    refine ⟨rd n jl 0 (rd n r u x1),?_,Or.inr ⟨?_,?_⟩⟩
    ·intro e;rw[rd_eq,hu_eq,e] at hsub0;rw[hsub0] at hcnt0_eq1;simp at hcnt0_eq1
    ·rw[hx12,lw2r hjr hne_jl1 hne1]
    ·rw[hsub0,rd_eq,hu_eq]
  obtain ⟨y0,hy0_ne,hy0_cases⟩:=hx12_shape
  have hother_inp: ∀ k∈G,k≠k0 →
    (gateAt C (li2 jl r k)).inputs=(gateAt Cs0 k).inputs.map (lw2 n jl r):=by
   intro k hk hne;apply r2in C hcl hrb hjr hr hu hu_ne hon0 hur k (hGlt k hk);intro hmr;exact hne (huniq_k0 k hk (hr_read k hk hmr))
  have hreads_lw: ∀ w: ℕ,w≠w_old →
    readsIn C (G.image (li2 jl r)) (lw2 n jl r w)=readsIn Cs0 G w:=by
   intro w hwne;unfold readsIn
   rw[sum_image (fun a _ b _ h => li2i jl r h)]
   apply sum_congr rfl;intro k hk
   by_cases hkk0: k=k0
   ·subst hkk0;have hnr_ne: n+r≠lw2 n jl r w:=(lw2nr n jl r w).symm
    rcases hy0_cases with ⟨hC0,hS0⟩ | ⟨hC0,hS0⟩ <;> rw[hC0,hS0]
    ·simp only[List.count_cons,List.count_nil,beq_iff_eq,hnr_ne,hwne.symm,↓reduceIte,
      (lw2j n jl r).eq_iff]
    ·simp only[List.count_cons,List.count_nil,beq_iff_eq,hnr_ne,hwne.symm,↓reduceIte,
      (lw2j n jl r).eq_iff]
   ·rw[hother_inp k hk hkk0];exact List.count_map_of_injective _ (lw2 n jl r) (lw2j n jl r) w
  have hreads_nr: readsIn C (G.image (li2 jl r)) (n+r)=1:=by
   unfold readsIn
   rw[sum_image (fun a _ b _ h => li2i jl r h)]
   rw[←add_sum_erase G _ hk0]
   have h0: (gateAt C (li2 jl r k0)).inputs.count (n+r)=1:=by
    have hne_y: lw2 n jl r y0≠n+r:=lw2nr n jl r y0
    rcases hy0_cases with ⟨hC0,_⟩ | ⟨hC0,_⟩ <;> rw[hC0] <;>
     simp[List.count_cons,hne_y,hne_y.symm]
   have hrest: ∑ k∈G.erase k0,(gateAt C (li2 jl r k)).inputs.count (n+r)=0:=by
    apply sum_eq_zero;intro k hk;rw[hother_inp k (mEo hk) (mE.mp hk).1,lcz];intro hm;rcases lmm.mp hm with ⟨z,_,hz⟩;exact lw2nr n jl r z hz
   omega
  refine ⟨?_,?_,?_,?_⟩
  ·intro j hj
   rcases mI.mp hj with ⟨k,hk,rfl⟩
   have hlif:=r2l C hcl hrb hjr hr hu k (hGlt k hk);obtain ⟨opk,lenk,insk⟩:=ht.1 k hk
   refine ⟨by rw[←hlif.1,opk],?_,?_⟩
   ·rw[hlif.2,llm] at lenk;exact lenk
   ·intro i hi
    by_cases hkk0: k=k0
    ·subst hkk0
     rcases hy0_cases with ⟨hC0,hS0⟩ | ⟨hC0,hS0⟩
     ·rw[hC0] at hi;simp only[lmc,lnn,or_false] at hi
      rcases hi with rfl|rfl
      ·exact Or.inl (mNs _ _)
      ·rcases insk y0 (by rw[hS0];simp) with hyL|⟨hyn,hyG⟩
       ·exact Or.inl (mNo (mI.mpr ⟨y0,mE.mpr ⟨hy0_ne,hyL⟩,rfl⟩))
       ·right
        have hyeq: y0=n+(y0 - n):=by omega
        rw[hyeq,lw2g];exact ⟨by omega,by rw[ascl];exact mI.mpr ⟨y0 - n,hyG,rfl⟩⟩
     ·rw[hC0] at hi;simp only[lmc,lnn,or_false] at hi
      rcases hi with rfl|rfl
      ·rcases insk y0 (by rw[hS0];simp) with hyL|⟨hyn,hyG⟩
       ·exact Or.inl (mNo (mI.mpr ⟨y0,mE.mpr ⟨hy0_ne,hyL⟩,rfl⟩))
       ·right
        have hyeq: y0=n+(y0 - n):=by omega
        rw[hyeq,lw2g];exact ⟨by omega,by rw[ascl];exact mI.mpr ⟨y0 - n,hyG,rfl⟩⟩
      ·exact Or.inl (mNs _ _)
    ·rw[hother_inp k hk hkk0] at hi
     rcases lmm.mp hi with ⟨z,hz,rfl⟩
     have hzne: z≠w_old:=fun e => hkk0 (huniq_k0 k hk (e ▸ hz))
     rcases insk z hz with hzL|⟨hzn,hzG⟩
     ·exact Or.inl (mNo (mI.mpr ⟨z,mE.mpr ⟨hzne,hzL⟩,rfl⟩))
     ·right
      have hzeq: z=n+(z - n):=by omega
      rw[hzeq,lw2g];exact ⟨by omega,by rw[ascl];exact mI.mpr ⟨z - n,hzG,rfl⟩⟩
  ·intro w hw
   rcases mN.mp hw with rfl | hw'
   ·refine ⟨fun ⟨_,h2⟩ => ?_,?_⟩
    ·rw[ascl] at h2
     rcases mI.mp h2 with ⟨k,_,hk⟩
     exact li2nr jl r k hk
    ·rw[if_neg (lw2nr n jl r ρ).symm];exact hreads_nr
   ·rcases mI.mp hw' with ⟨z,hz,rfl⟩
    obtain ⟨hzne,hzL⟩:=mE.mp hz
    refine ⟨fun ⟨h1,h2⟩ => ?_,?_⟩
    ·rcases mI.mp h2 with ⟨k,hkG,hk⟩
     have hzk: lw2 n jl r z=lw2 n jl r (n+k):=by rw[lw2g];omega
     have heq:=lw2j n jl r hzk;exact (ht.2.1 z hzL).1 ⟨by omega,by rw[heq,ascl];exact hkG⟩
    ·rw[hreads_lw z hzne,(ht.2.1 z hzL).2];simp only[(lw2j n jl r).eq_iff]
  ·intro j hj
   rcases mI.mp hj with ⟨k,hk,rfl⟩
   have hne_old: n+k≠w_old:=fun e => (ht.2.1 w_old hw_old).1 ⟨by omega,by simpa [←e] using hk⟩
   rw[←lw2g n jl r k,hreads_lw (n+k) hne_old,ht.2.2.1 k hk];simp only[(lw2j n jl r).eq_iff]
  ·have hGne: G ≠ ∅ := nonempty_iff_ne_empty.mp ⟨k0,hk0⟩;have himg_ne: G.image (li2 jl r) ≠ ∅ := Finset.Nonempty.ne_empty ⟨li2 jl r k0,mI.mpr ⟨k0,hk0,rfl⟩⟩;simp only[himg_ne,↓reduceIte];have h1:=ht.2.2.2;simp only[hGne,↓reduceIte] at h1;obtain ⟨g0,hg0,hρ⟩:=h1;exact ⟨li2 jl r g0,mI.mpr ⟨g0,hg0,rfl⟩,by rw[hρ,lw2g]⟩
lemma cf2 {n jl r u: ℕ} (C: Circuit) (hcl: CL n C.gates)
  (hrb: ReadsBack n C) (hjr: jl < r) (hr: r < C.gates.length) (hu: u < n+r)
  (hu_ne: u≠n+jl) (hon0: C.output≠n+jl)
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  {Ks0: SimpleGraph (Fin n)} {As0: Finset (Fin n)} {ds0 d: NCCData n}
  (hv: Valid n Ks0 As0 ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ ds0)
  (S: Finset (Fin n)) (hS_sub: S⊆ds0.cover) (hS_d: S⊆d.cover)
  (hZ_ok: ∀ j' < C.gates.length - 2,(ds0.role j').1=Kind.z →
   n+r∉(gateAt C (li2 jl r j')).inputs∧(d.role (li2 jl r j')).1=Kind.z)
  (v: Fin n) (hvS: v∈S) :
  ∀ w: ℕ,IsCentred n ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ ds0 w →
   (w=v.val ∨ ∃ j' < C.gates.length - 2,w=n + j' ∧ ds0.role j' = (Kind.z,v.val)) →
   IsCentred n C d (lw2 n jl r w):=by
 set Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;set Cs0: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩
 have hlen_sub: Cs0.gates.length=C.gates.length - 2:=by
  have h1:=rdel_length n r u C.gates hr;have h2:=rdel_length n jl 0 Cm0.gates (by simp[Cm0];omega);simp[Cs0,Cm0] at h2 ⊢;omega
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hcen hshape
  rcases hshape with rfl|⟨j',hj',rfl,hrj'⟩
  ·rw[lw2i n jl r v.val v.isLt,cfi C d v];exact hS_d hvS
  ·have hj'sub: j' < Cs0.gates.length:=by omega
   have hcen' := (cfg Cs0 ds0 hv.1 j' hj'sub).mp hcen;obtain ⟨_,a,ha_in,ha_cen⟩ := hcen'
   have ha_lt: a < n + j' := hv.1 j' hj'sub a ha_in
   have hj'Z: j' ∈ gatesOf ds0 Cs0 Kind.z v.val :=
    mF.mpr ⟨mR.mpr hj'sub,hrj'⟩
   have hZt:=(hv.2.2.2.2.2.1 v (hS_sub hvS)).2.1
   have ha_shape: a=v.val ∨ ∃ k < C.gates.length - 2,a=n+k∧ds0.role k=(Kind.z,v.val):=by
    rcases (hZt.1 j' hj'Z).2.2 a ha_in with haL|⟨han,haG⟩
    ·simp only[zLeaves,mN,mI,mF] at haL
     rcases haL with rfl|⟨s,⟨hs,_⟩,rfl⟩
     ·exact Or.inl rfl
     ·exfalso
      obtain ⟨jb,hjb,hbw,hrb_s,_,_⟩:=(hv.2.2.2.2.2.1 s hs).1;rw[hbw] at ha_cen;have hcg_b:=(cfg Cs0 ds0 hv.1 jb hjb).mp ha_cen;rw[hrb_s] at hcg_b
      simp at hcg_b
    ·right;have haG' := mF.mp haG;exact ⟨a - n,by have := mR.mp haG'.1;omega,by omega,haG'.2⟩
   have hih:=ih a ha_lt ha_cen ha_shape;have hZ:=hZ_ok j' hj' (by rw[hrj']);have hinp:=r2in C hcl hrb hjr hr hu hu_ne hon0 hur j' hj' hZ.1;rw[lw2g,cfg C d hrb (li2 jl r j') (li2lt hjr hr hj')];exact ⟨hZ.2,lw2 n jl r a,by rw[hinp];exact lmm.mpr ⟨a,ha_in,rfl⟩,hih⟩
lemma nbs {n: ℕ} {Ks0: SimpleGraph (Fin n)} {As0: Finset (Fin n)}
  {Cs0: Circuit} {ds0: NCCData n}
  (hv: Valid n Ks0 As0 Cs0 ds0) (hcl: CL n Cs0.gates)
  (v0: Fin n) :
  ∀ w < n+Cs0.gates.length,
   (∀ t∈ds0.cover,w=ds0.bw t → vl Cs0.gates (fun i => decide (i=v0)) w=false):=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw t ht hbw;obtain ⟨jb,hjb,hbw_eq,_,hop,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
  have hgj: Cs0.gates[jb]? = some (gateAt Cs0 jb):=by simp[gateAt,List.getD,hjb]
  rw[hbw,hbw_eq,vlg Cs0.gates hcl _ jb _ hgj,hop]
  suffices hor: vl Cs0.gates (fun i => decide (i=v0)) (ds0.zroot t)=false ∨
    vl Cs0.gates (fun i => decide (i=v0)) (ds0.oroot t)=false by
   rcases hin with h|h <;> rw[h] <;>
    simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,
     Bool.and_true,Bool.and_eq_false_iff]
   ·rcases hor with h1|h1
    ·exact Or.inl h1
    ·exact Or.inr h1
   ·rcases hor with h1|h1
    ·exact Or.inr h1
    ·exact Or.inl h1
  by_cases htv: t=v0
  ·right;have hOt:=(hv.2.2.2.2.2.1 t ht).2.2.1
   have hGlt: ∀ k∈gatesOf ds0 Cs0 Kind.o t.val,k < Cs0.gates.length:=fun k hk =>
    mR.mp (mF.mp hk).1
   have hsub:=osRL hv.1 hOt hGlt
   have hmem: ds0.oroot t∈oLeaves ds0 t ∨
     (n ≤ ds0.oroot t∧ds0.oroot t - n∈gatesOf ds0 Cs0 Kind.o t.val):=by
    by_cases hGe: gatesOf ds0 Cs0 Kind.o t.val = ∅
    ·have h1:=hOt.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
    ·have h1:=hOt.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
   rw[Bool.eq_false_iff];intro htr
   have hiff:=(osV hcl hv.1 hOt hGlt (fun i => decide (i=v0)) (ds0.oroot t) hmem).mp htr
   rw[hsub.2] at hiff;obtain ⟨wL,hwL,hxwL⟩:=hiff;simp only[oLeaves,mI,mF,mV,true_and] at hwL;obtain ⟨s,hown,rfl⟩:=hwL
   have hne_ts: s≠v0:=by
    rw[←htv];exact (hv.2.2.1.1 t s hown).1.ne'
   have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 s hown;unfold LamOK at hlam
   by_cases hsc: s∈ds0.cover
   ·simp only[hsc,↓reduceIte] at hlam;have hZs:=(hv.2.2.2.2.2.1 s hsc).2.1
    have hZlt: ∀ k∈gatesOf ds0 Cs0 Kind.z s.val,k < Cs0.gates.length:=fun k hk =>
     mR.mp (mF.mp hk).1
    have hmem_l: ds0.lam t s∈zLeaves ds0 s ∨
      (n ≤ ds0.lam t s∧ds0.lam t s - n∈gatesOf ds0 Cs0 Kind.z s.val):=by
     rcases hlam.2.1 with h1|⟨jz,hjz,h1,h2⟩
     ·left;rw[h1];exact mNs _ _
     ·right;exact ⟨by omega,by rw[h1,ascl];exact mF.mpr ⟨mR.mpr hjz,h2⟩⟩
    obtain ⟨zL,hzL,hxzL⟩:=(osV hcl hv.1 hZs hZlt _ _ hmem_l).mp hxwL;have hzL' := (osS hv.1 hZs hZlt _).2.1 hzL;simp only[zLeaves,mN,mI,mF] at hzL'
    rcases hzL' with rfl|⟨u',⟨hu',_⟩,rfl⟩
    ·rw[vli Cs0.gates _ s.val s.isLt] at hxzL;simp[hne_ts] at hxzL
    ·have hbw_lt: ds0.bw u' < n+jb:=by
      have h1: ds0.lam t s < n+jb:=by
       have hlt1:=orTree_lt_root hcl hOt hGlt _ (ds0.lam t s) rfl (Or.inl (by
        simp only[oLeaves,mI,mF,mV,true_and]
        exact ⟨s,hown,rfl⟩))
       have hlt2: ds0.oroot t < n+jb:=hv.1 jb hjb (ds0.oroot t) (by rcases hin with h|h <;> simp[h])
       omega
      have h2:=orTree_lt_root hcl (osT hv.1 hZs hZlt (ds0.lam t s) hmem_l)
       (fun k hk => hZlt k ((osS hv.1 hZs hZlt _).1 hk)) _ (ds0.bw u') rfl (Or.inl hzL)
      omega
     have hf:=ih (ds0.bw u') (by omega) (by omega) u' hu' rfl;rw[hf] at hxzL;cases hxzL
   ·simp only[hsc,↓reduceIte] at hlam;rw[hlam,vli Cs0.gates _ s.val s.isLt] at hxwL;simp[hne_ts] at hxwL
  ·left;have hZt:=(hv.2.2.2.2.2.1 t ht).2.1
   have hGlt: ∀ k∈gatesOf ds0 Cs0 Kind.z t.val,k < Cs0.gates.length:=fun k hk =>
    mR.mp (mF.mp hk).1
   have hsub:=osRL hv.1 hZt hGlt
   have hmem: ds0.zroot t∈zLeaves ds0 t ∨
     (n ≤ ds0.zroot t∧ds0.zroot t - n∈gatesOf ds0 Cs0 Kind.z t.val):=by
    by_cases hGe: gatesOf ds0 Cs0 Kind.z t.val = ∅
    ·have h1:=hZt.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
    ·have h1:=hZt.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
   rw[Bool.eq_false_iff];intro htr
   have hiff:=(osV hcl hv.1 hZt hGlt (fun i => decide (i=v0)) (ds0.zroot t) hmem).mp htr
   rw[hsub.2] at hiff;obtain ⟨zL,hzL,hxzL⟩:=hiff;simp only[zLeaves,mN,mI,mF] at hzL
   rcases hzL with rfl|⟨u',⟨hu',_⟩,rfl⟩
   ·rw[vli Cs0.gates _ t.val t.isLt] at hxzL;simp[htv] at hxzL
   ·have hbw_lt: ds0.bw u' < n+jb:=by
     have hlt1:=orTree_lt_root hcl hZt hGlt _ (ds0.bw u') rfl (Or.inl (by
      simp only[zLeaves,mN,mI,mF]
      exact Or.inr ⟨u',⟨hu',by assumption⟩,rfl⟩))
     have hlt2: ds0.zroot t < n+jb:=hv.1 jb hjb (ds0.zroot t) (by rcases hin with h|h <;> simp[h])
     omega
    have hf:=ih (ds0.bw u') (by omega) (by omega) u' hu' rfl;rw[hf] at hxzL;cases hxzL
lemma nbpo {n: ℕ} {Ks0: SimpleGraph (Fin n)} {As0: Finset (Fin n)}
  {Cs0: Circuit} {ds0: NCCData n}
  (hv: Valid n Ks0 As0 Cs0 ds0) (hcl: CL n Cs0.gates)
  {s v: Fin n} (hown: ds0.owns s v=true) (hfree: ds0.tie s=none) :
  ∀ w < n+Cs0.gates.length,
   ∀ t∈ds0.cover,t≠s → w=ds0.bw t →
    vl Cs0.gates (fun i => decide (i=s∨i=v)) w=false:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw t ht hts hbw;obtain ⟨jb,hjb,hbw_eq,_,hop,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
  have hgj: Cs0.gates[jb]? = some (gateAt Cs0 jb):=by simp[gateAt,List.getD,hjb]
  rw[hbw,hbw_eq,vlg Cs0.gates hcl _ jb _ hgj,hop]
  suffices hor: vl Cs0.gates (fun i => decide (i=s∨i=v)) (ds0.zroot t)=false ∨
    vl Cs0.gates (fun i => decide (i=s∨i=v)) (ds0.oroot t)=false by
   rcases hin with h|h <;> rw[h] <;>
    simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,
     Bool.and_true,Bool.and_eq_false_iff]
   ·rcases hor with h1|h1
    ·exact Or.inl h1
    ·exact Or.inr h1
   ·rcases hor with h1|h1
    ·exact Or.inr h1
    ·exact Or.inl h1
  by_cases htv: t=v
  ·right;have hOt:=(hv.2.2.2.2.2.1 t ht).2.2.1
   have hGlt: ∀ k∈gatesOf ds0 Cs0 Kind.o t.val,k < Cs0.gates.length:=fun k hk =>
    mR.mp (mF.mp hk).1
   have hsub:=osRL hv.1 hOt hGlt
   have hmem: ds0.oroot t∈oLeaves ds0 t ∨
     (n ≤ ds0.oroot t∧ds0.oroot t - n∈gatesOf ds0 Cs0 Kind.o t.val):=by
    by_cases hGe: gatesOf ds0 Cs0 Kind.o t.val = ∅
    ·have h1:=hOt.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
    ·have h1:=hOt.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
   rw[Bool.eq_false_iff];intro htr;have hiff:=(osV hcl hv.1 hOt hGlt _ (ds0.oroot t) hmem).mp htr;rw[hsub.2] at hiff;obtain ⟨wL,hwL,hxwL⟩:=hiff;simp only[oLeaves,mI,mF,mV,true_and] at hwL;obtain ⟨r',hown',rfl⟩:=hwL
   have hr'_ne_v: r' ≠ v:=by rw[←htv];exact (hv.2.2.1.1 t r' hown').1.ne'
   have hr'_ne_s: r' ≠ s:=by
    intro e;have h1:=hv.2.2.1.2 s v (hv.2.2.1.1 s v hown).1;rw[hown,←htv,←e,hown'] at h1;exact h1 rfl
   have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam
   by_cases hrc: r' ∈ ds0.cover
   ·simp only[hrc,↓reduceIte] at hlam;have hZr:=(hv.2.2.2.2.2.1 r' hrc).2.1
    have hZlt: ∀ k∈gatesOf ds0 Cs0 Kind.z r'.val,k < Cs0.gates.length:=fun k hk =>
     mR.mp (mF.mp hk).1
    have hmem_l: ds0.lam t r' ∈ zLeaves ds0 r' ∨
      (n ≤ ds0.lam t r' ∧ ds0.lam t r' - n∈gatesOf ds0 Cs0 Kind.z r'.val):=by
     rcases hlam.2.1 with h1|⟨jz,hjz,h1,h2⟩
     ·left;rw[h1];exact mNs _ _
     ·right;exact ⟨by omega,by rw[h1,ascl];exact mF.mpr ⟨mR.mpr hjz,h2⟩⟩
    obtain ⟨zL,hzL,hxzL⟩:=(osV hcl hv.1 hZr hZlt _ _ hmem_l).mp hxwL;have hzL' := (osS hv.1 hZr hZlt _).2.1 hzL;simp only[zLeaves,mN,mI,mF] at hzL'
    rcases hzL' with rfl|⟨u',⟨hu',htu'⟩,rfl⟩
    ·rw[vli Cs0.gates _ r'.val r'.isLt] at hxzL;simp[hr'_ne_s,hr'_ne_v] at hxzL
    ·have hu'_ne_s: u' ≠ s:=fun e => by rw[e,hfree] at htu';cases htu'
     have hbw_lt: ds0.bw u' < n+jb:=by
      have h1: ds0.lam t r' < n+jb:=by
       have hlt1:=orTree_lt_root hcl hOt hGlt _ (ds0.lam t r') rfl (Or.inl (by
        simp only[oLeaves,mI,mF,mV,true_and]
        exact ⟨r',hown',rfl⟩))
       have hlt2: ds0.oroot t < n+jb:=hv.1 jb hjb (ds0.oroot t) (by rcases hin with h|h <;> simp[h])
       omega
      have h2:=orTree_lt_root hcl (osT hv.1 hZr hZlt (ds0.lam t r') hmem_l)
       (fun k hk => hZlt k ((osS hv.1 hZr hZlt _).1 hk)) _ (ds0.bw u') rfl (Or.inl hzL)
      omega
     have hf:=ih (ds0.bw u') (by omega) (by omega) u' hu' hu'_ne_s rfl;rw[hf] at hxzL;cases hxzL
   ·simp only[hrc,↓reduceIte] at hlam;rw[hlam,vli Cs0.gates _ r'.val r'.isLt] at hxwL;simp[hr'_ne_s,hr'_ne_v] at hxwL
  ·left;have hZt:=(hv.2.2.2.2.2.1 t ht).2.1
   have hGlt: ∀ k∈gatesOf ds0 Cs0 Kind.z t.val,k < Cs0.gates.length:=fun k hk =>
    mR.mp (mF.mp hk).1
   have hsub:=osRL hv.1 hZt hGlt
   have hmem: ds0.zroot t∈zLeaves ds0 t ∨
     (n ≤ ds0.zroot t∧ds0.zroot t - n∈gatesOf ds0 Cs0 Kind.z t.val):=by
    by_cases hGe: gatesOf ds0 Cs0 Kind.z t.val = ∅
    ·have h1:=hZt.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
    ·have h1:=hZt.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
   rw[Bool.eq_false_iff];intro htr;have hiff:=(osV hcl hv.1 hZt hGlt _ (ds0.zroot t) hmem).mp htr;rw[hsub.2] at hiff;obtain ⟨zL,hzL,hxzL⟩:=hiff;simp only[zLeaves,mN,mI,mF] at hzL
   rcases hzL with rfl|⟨u',⟨hu',htu'⟩,rfl⟩
   ·rw[vli Cs0.gates _ t.val t.isLt] at hxzL;simp[hts,htv] at hxzL
   ·have hu'_ne_s: u' ≠ s:=fun e => by rw[e,hfree] at htu';cases htu'
    have hbw_lt: ds0.bw u' < n+jb:=by
     have hlt1:=orTree_lt_root hcl hZt hGlt _ (ds0.bw u') rfl (Or.inl (by
      simp only[zLeaves,mN,mI,mF]
      exact Or.inr ⟨u',⟨hu',htu'⟩,rfl⟩))
     have hlt2: ds0.zroot t < n+jb:=hv.1 jb hjb (ds0.zroot t) (by rcases hin with h|h <;> simp[h])
     omega
    have hf:=ih (ds0.bw u') (by omega) (by omega) u' hu' hu'_ne_s rfl;rw[hf] at hxzL;cases hxzL
lemma nbpt {n: ℕ} {Ks0: SimpleGraph (Fin n)} {As0: Finset (Fin n)}
  {Cs0: Circuit} {ds0: NCCData n}
  (hv: Valid n Ks0 As0 Cs0 ds0) (hcl: CL n Cs0.gates)
  {t0 q0 v0: Fin n} (ht0: t0∈ds0.cover) (hq0: q0∈ds0.cover)
  (hown0: ds0.owns t0 v0=true) (hv0_out: v0∉ds0.cover)
  (htie0: ds0.tie t0=some q0) (hq0_free: ds0.tie q0=none) :
  ∀ w < n+Cs0.gates.length,
   ∀ t∈ds0.cover,t≠t0 → t≠q0 → w=ds0.bw t →
    vl Cs0.gates (fun i => decide (i=t0∨i=v0)) w=false:=by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw t ht htt0 htq0 hbw;obtain ⟨jb,hjb,hbw_eq,_,hop,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
  have hgj: Cs0.gates[jb]? = some (gateAt Cs0 jb):=by simp[gateAt,List.getD,hjb]
  rw[hbw,hbw_eq,vlg Cs0.gates hcl _ jb _ hgj,hop]
  suffices hz: vl Cs0.gates (fun i => decide (i=t0∨i=v0)) (ds0.zroot t)=false by
   rcases hin with h|h <;> rw[h] <;>
    simp only[GateOp.eval,lmC,lmN,laC,laN,id_eq,
     Bool.and_true,Bool.and_eq_false_iff]
   ·exact Or.inl hz
   ·exact Or.inr hz
  have hZt:=(hv.2.2.2.2.2.1 t ht).2.1
  have hGlt: ∀ k∈gatesOf ds0 Cs0 Kind.z t.val,k < Cs0.gates.length:=fun k hk =>
   mR.mp (mF.mp hk).1
  have hsub:=osRL hv.1 hZt hGlt
  have hmem: ds0.zroot t∈zLeaves ds0 t ∨
    (n ≤ ds0.zroot t∧ds0.zroot t - n∈gatesOf ds0 Cs0 Kind.z t.val):=by
   by_cases hGe: gatesOf ds0 Cs0 Kind.z t.val = ∅
   ·have h1:=hZt.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
   ·have h1:=hZt.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
  rw[Bool.eq_false_iff];intro htr;have hiff:=(osV hcl hv.1 hZt hGlt _ (ds0.zroot t) hmem).mp htr;rw[hsub.2] at hiff;obtain ⟨zL,hzL,hxzL⟩:=hiff;simp only[zLeaves,mN,mI,mF] at hzL
  rcases hzL with rfl|⟨u',⟨hu',htu'⟩,rfl⟩
  ·rw[vli Cs0.gates _ t.val t.isLt] at hxzL
   have htv0: t≠v0:=fun e => hv0_out (e ▸ ht)
   simp[htt0,htv0] at hxzL
  ·have hu'_ne_t0: u' ≠ t0:=fun e => by rw[e,htie0] at htu';exact htq0 (osi htu').symm
   have hu'_ne_q0: u' ≠ q0:=fun e => by rw[e,hq0_free] at htu';cases htu'
   have hbw_lt: ds0.bw u' < n+jb:=by
    have hlt1:=orTree_lt_root hcl hZt hGlt _ (ds0.bw u') rfl (Or.inl (by
     simp only[zLeaves,mN,mI,mF]
     exact Or.inr ⟨u',⟨hu',htu'⟩,rfl⟩))
    have hlt2: ds0.zroot t < n+jb:=hv.1 jb hjb (ds0.zroot t) (by rcases hin with h|h <;> simp[h])
    omega
   have hf:=ih (ds0.bw u') (by omega) (by omega) u' hu' hu'_ne_t0 hu'_ne_q0 rfl;rw[hf] at hxzL;cases hxzL
lemma nnti {n: ℕ} {Ks0: SimpleGraph (Fin n)} {As0: Finset (Fin n)}
  {Cs0: Circuit} {ds0: NCCData n}
  (hv: Valid n Ks0 As0 Cs0 ds0) (hcl: CL n Cs0.gates)
  (p: Fin n) (hp_iso: ∀ v: Fin n,¬ Ks0.Adj p v) (x: Fin n→Bool) (b: Bool) :
  ∀ w < n+Cs0.gates.length,
   w≠p.val →
   (∀ j < Cs0.gates.length,w=n+j→(ds0.role j).1≠Kind.top) →
   vl Cs0.gates (Function.update x p b) w=vl Cs0.gates x w:=by
 have hpnc: p∉ds0.cover:=by
  intro hpc;obtain ⟨v,hown,_⟩:=coo hv p hpc;exact hp_iso v (hv.2.2.1.1 p v hown).1
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw hwne hnotTop
  by_cases hwn: w < n
  ·rw[vli _ _ w hwn,vli _ _ w hwn]
   have hne: (⟨w,hwn⟩ : Fin n)≠p:=fun e => hwne (congrArg Fin.val e)
   exact fupn hne b x
  ·set j:=w - n
   have hweq: w=n+j:=by omega
   have hj: j < Cs0.gates.length:=by omega
   have hgj: Cs0.gates[j]? = some (gateAt Cs0 j):=by simp[gateAt,List.getD,hj]
   rw[hweq,vlg Cs0.gates hcl _ j _ hgj,vlg Cs0.gates hcl _ j _ hgj]
   congr 1;apply List.map_congr_left;intro a ha
   have halt: a < n+j:=hv.1 j hj a ha;have hnt:=hnotTop j hj hweq
   rcases hv.2.2.2.2.1 j hj with htop|⟨t,ht,hrt2,hrb_t⟩
   ·exact absurd htop hnt
   ·have hne_p: a≠p.val:=by
     intro e;subst e
     cases hkr: (ds0.role j).1 with
     | top => exact hnt hkr
     | b =>
      have hbw:=hrb_t hkr;obtain ⟨jb,hjb,hbw2,_,_,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
      have hje: j=jb:=by omega
      subst hje
      rcases hin with h|h <;> rw[h] at ha <;> simp at ha <;> rcases ha with h1|h2
      ·rcases zrs hv t ht with hzr|⟨_,_,hzr,_⟩
       ·rw[hzr] at h1;exact hpnc (Fin.ext h1 ▸ ht)
       ·omega
      ·rcases ors hv t ht with ⟨r',hown',hlam'⟩ | ⟨_,_,hor,_⟩
       ·have hne_r' : r' ≠ p:=fun er => hp_iso t (er ▸ (hv.2.2.1.1 t r' hown').1).symm
        have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
        ·rcases hlam.2.1 with h3|⟨_,_,h3,_⟩
         ·rw[hlam',h3] at h2;exact hne_r' (Fin.ext h2.symm)
         ·omega
        ·rw[hlam',hlam] at h2;exact hne_r' (Fin.ext h2.symm)
       ·omega
      ·rcases ors hv t ht with ⟨r',hown',hlam'⟩ | ⟨_,_,hor,_⟩
       ·have hne_r' : r' ≠ p:=fun er => hp_iso t (er ▸ (hv.2.2.1.1 t r' hown').1).symm
        have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
        ·rcases hlam.2.1 with h3|⟨_,_,h3,_⟩
         ·rw[hlam',h3] at h1;exact hne_r' (Fin.ext h1.symm)
         ·omega
        ·rw[hlam',hlam] at h1;exact hne_r' (Fin.ext h1.symm)
       ·omega
      ·rcases zrs hv t ht with hzr|⟨_,_,hzr,_⟩
       ·rw[hzr] at h2;exact hpnc (Fin.ext h2 ▸ ht)
       ·omega
     | z =>
      have hjZ: j∈gatesOf ds0 Cs0 Kind.z t.val :=
       mF.mpr ⟨mR.mpr hj,Prod.ext hkr hrt2⟩
      rcases ((hv.2.2.2.2.2.1 t ht).2.1.1 j hjZ).2.2 p.val ha with hL|⟨hge,_⟩
      ·simp only[zLeaves,mN,mI,mF] at hL
       rcases hL with h1|⟨s,⟨hs,_⟩,h2⟩
       ·exact hpnc (Fin.ext h1 ▸ ht)
       ·obtain ⟨jb,_,hbw,_,_,_⟩:=(hv.2.2.2.2.2.1 s hs).1;omega
      ·omega
     | o =>
      have hjO: j∈gatesOf ds0 Cs0 Kind.o t.val :=
       mF.mpr ⟨mR.mpr hj,Prod.ext hkr hrt2⟩
      rcases ((hv.2.2.2.2.2.1 t ht).2.2.1.1 j hjO).2.2 p.val ha with hL|⟨hge,_⟩
      ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',hlam'⟩:=hL
       have hne_r' : r' ≠ p:=fun er => hp_iso t (er ▸ (hv.2.2.1.1 t r' hown').1).symm
       have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
       ·rcases hlam.2.1 with h3|⟨_,_,h3,_⟩
        ·rw[h3] at hlam';exact hne_r' (Fin.ext hlam')
        ·omega
       ·rw[hlam] at hlam';exact hne_r' (Fin.ext hlam')
      ·omega
    have ha_nt: ∀ k < Cs0.gates.length,a=n+k→(ds0.role k).1≠Kind.top:=by
     intro k hk hak htop_k
     cases hkr: (ds0.role j).1 with
     | top => exact hnt hkr
     | b =>
      have hbw:=hrb_t hkr;obtain ⟨jb,hjb,hbw2,_,_,hin⟩:=(hv.2.2.2.2.2.1 t ht).1
      have hje: j=jb:=by omega
      subst hje
      rcases hin with h|h <;> rw[h] at ha <;> simp at ha <;> rcases ha with h1|h2
      ·rcases zrs hv t ht with hzr|⟨jz,_,hzr,hrz⟩
       ·omega
       ·have: k=jz := by omega
        rw[this,hrz] at htop_k;cases htop_k
      ·rcases ors hv t ht with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
       ·have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
        ·rcases hlam.2.1 with h3|⟨jz,_,h3,hrz⟩
         ·omega
         ·have: k=jz := by omega
          rw[this,hrz] at htop_k;cases htop_k
        ·omega
       ·have: k=jo := by omega
        rw[this,hro] at htop_k;cases htop_k
      ·rcases ors hv t ht with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
       ·have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
        ·rcases hlam.2.1 with h3|⟨jz,_,h3,hrz⟩
         ·omega
         ·have: k=jz := by omega
          rw[this,hrz] at htop_k;cases htop_k
        ·omega
       ·have: k=jo := by omega
        rw[this,hro] at htop_k;cases htop_k
      ·rcases zrs hv t ht with hzr|⟨jz,_,hzr,hrz⟩
       ·omega
       ·have: k=jz := by omega
        rw[this,hrz] at htop_k;cases htop_k
     | z =>
      have hjZ: j∈gatesOf ds0 Cs0 Kind.z t.val :=
       mF.mpr ⟨mR.mpr hj,Prod.ext hkr hrt2⟩
      rcases ((hv.2.2.2.2.2.1 t ht).2.1.1 j hjZ).2.2 a ha with hL|⟨_,hG⟩
      ·simp only[zLeaves,mN,mI,mF] at hL
       rcases hL with h1|⟨s,⟨hs,_⟩,h2⟩
       ·omega
       ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(hv.2.2.2.2.2.1 s hs).1
        have: k=jb := by omega
        rw[this,hrb_s] at htop_k;cases htop_k
      ·have hG' := (mF.mp hG).2;rw[hak,ascl] at hG';rw[hG'] at htop_k;cases htop_k
     | o =>
      have hjO: j∈gatesOf ds0 Cs0 Kind.o t.val :=
       mF.mpr ⟨mR.mpr hj,Prod.ext hkr hrt2⟩
      rcases ((hv.2.2.2.2.2.1 t ht).2.2.1.1 j hjO).2.2 a ha with hL|⟨_,hG⟩
      ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',hlam'⟩:=hL;have hlam:=(hv.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
       ·rcases hlam.2.1 with h3|⟨jz,_,h3,hrz⟩
        ·omega
        ·have: k=jz := by omega
         rw[this,hrz] at htop_k;cases htop_k
       ·omega
      ·have hG' := (mF.mp hG).2;rw[hak,ascl] at hG';rw[hG'] at htop_k;cases htop_k
    exact ih a (by omega) (by omega) hne_p ha_nt
set_option maxHeartbeats 1600000 in
lemma nlB1 {n jl wl r u: ℕ} (hn: 0 < n)
  {K K2: SimpleGraph (Fin n)} [DecidableRel K.Adj] [DecidableRel K2.Adj]
  {A: Finset (Fin n)} {l p q: Fin n}
  (hA: ∀ a∈A,∀ v: Fin n,¬ K.Adj a v)
  (hl: ∀ v: Fin n,K.Adj l v↔v=p)
  (hql: q≠l)
  (hp: ∀ v: Fin n,K.Adj p v↔v=l∨v=q)
  (hK2: ∀ u v: Fin n,K2.Adj u v↔K.Adj u v∧u≠l∧u≠p∧v≠l∧v≠p)
  (C: Circuit) (hcl: CL n C.gates) (hrb: ReadsBack n C)
  (hcf: circuitFun n C=graphFun K A)
  (hjr: jl < r) (hr: r < C.gates.length)
  (hw_l: wl < n+jl) (hwne: wl≠l.val)
  (hu: u < n+r) (hune: u≠n+jl) (hon0: C.output≠n+jl)
  (hjlo: (gateAt C jl).op=GateOp.or)
  (hjli: (gateAt C jl).inputs=[l.val,wl]∨(gateAt C jl).inputs=[wl,l.val])
  (hro0: (gateAt C r).op=GateOp.and)
  (hri0: (gateAt C r).inputs=[n+jl,u]∨(gateAt C r).inputs=[u,n+jl])
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  {d2: NCCData n}
  (hv2: Valid n K2 (insert p A)
   ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ d2)
  (htK2: ∀ T: Finset (Fin n),K.IsVertexCover (T: Set (Fin n)) → d2.cover.card+1 ≤ T.card) :
  IsNestedCoverCircuit n K A C:=by
 set Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;set C2: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩;have hcl2: CL n C2.gates:=ncc_clean hv2
 have hlm: Cm0.gates.length=C.gates.length - 1:=by
  have:=rdel_length n r u C.gates hr;simp[Cm0];omega
 have hlen2: C2.gates.length=C.gates.length - 2:=by
  have:=rdel_length n jl 0 Cm0.gates (by omega);simp[C2] at this ⊢;omega
 have hlp: l≠p:=((hl p).mpr rfl).ne;have hpq: p≠q:=((hp q).mpr (Or.inr rfl)).ne
 have hlnA: l∉A:=fun h => hA l h p ((hl p).mpr rfl)
 have hpnA: p∉A:=fun h => hA p h l ((hl p).mpr rfl).symm
 have hqnA: q∉A:=fun h => hA q h p ((hp q).mpr (Or.inr rfl)).symm
 have hp_iso: ∀ v: Fin n,¬ K2.Adj p v:=fun v h => ((hK2 p v).mp h).2.2.1 rfl
 have hl_iso: ∀ v: Fin n,¬ K2.Adj l v:=fun v h => ((hK2 l v).mp h).2.1 rfl
 have hpnc: p∉d2.cover:=fun h => by
  obtain ⟨v,hown,_⟩:=coo hv2 p h;exact hp_iso v (hv2.2.2.1.1 p v hown).1
 have hlnc: l∉d2.cover:=fun h => by
  obtain ⟨v,hown,_⟩:=coo hv2 l h;exact hl_iso v (hv2.2.2.1.1 l v hown).1
 have hcnA: ∀ s∈d2.cover,s∉insert p A:=by
  intro s hs hsa
  rcases mN.mp hsa with rfl|ha
  ·exact hpnc hs
  ·obtain ⟨v,hown,_⟩:=coo hv2 s hs;exact hA s ha v ((hK2 s v).mp (hv2.2.2.1.1 s v hown).1).1
 have hval_C: ∀ x: Fin n→Bool,vl C.gates x C.output=graphFun K A x:=fun x => congrFun hcf x
 have hval_C2: ∀ x: Fin n→Bool,vl C2.gates x C2.output=graphFun K2 (insert p A) x:=fun x =>
  congrFun (ncc_eval hv2) x
 let u2:=rd n jl 0 u;let wl2:=rd n jl 0 wl
 have hu_lw: lw2 n jl r u2=u:=by
  have h1: lw1 n jl u2=u:=lw1r n jl 0 u hune;unfold lw2;rw[h1];unfold lw1;split_ifs <;> omega
 have hwl_lw: lw2 n jl r wl2=wl:=by
  have h1: lw1 n jl wl2=wl:=lw1r n jl 0 wl (by omega);unfold lw2;rw[h1];unfold lw1;split_ifs <;> omega
 have hu2_lt: u2 < n+C2.gates.length:=by
  change rd n jl 0 u < n+C2.gates.length;unfold rd;split_ifs <;> omega
 have hwl2_lt: wl2 < n+C2.gates.length:=by
  change rd n jl 0 wl < n+C2.gates.length;unfold rd;split_ifs <;> omega
 have hvl_u: ∀ x: Fin n→Bool,vl C.gates x u=vl C2.gates x u2:=fun x => by
  rw[←hu_lw];exact vlb hn C hcl hrb hjr hr hu hune hon0 hur x u2 (by omega)
 have hvl_wl: ∀ x: Fin n→Bool,vl C.gates x wl=vl C2.gates x wl2:=fun x => by
  rw[←hwl_lw];exact vlb hn C hcl hrb hjr hr hu hune hon0 hur x wl2 (by omega)
 have hvl_r: ∀ x: Fin n→Bool,vl C.gates x (n+r)=((x l||vl C2.gates x wl2)&&vl C2.gates x u2):=by
  intro x
  have hgj: C.gates[jl]? = some (gateAt C jl):=by simp[gateAt,List.getD,show jl < C.gates.length by omega]
  have hgr: C.gates[r]? = some (gateAt C r):=by simp[gateAt,List.getD,hr]
  have h1: vl C.gates x (n+jl)=(x l||vl C2.gates x wl2):=by
   rw[vlg C.gates hcl x jl _ hgj,hjlo]
   rcases hjli with h|h <;> rw[h] <;>
    simp[GateOp.eval,vli C.gates x l.val l.isLt,hvl_wl x,Bool.or_comm]
  rw[vlg C.gates hcl x r _ hgr,hro0]
  rcases hri0 with h|h <;> rw[h] <;>
   simp[GateOp.eval,h1,hvl_u x,Bool.and_comm]
 have hCC2: ∀ x: Fin n→Bool,vl C.gates x (n+r)=vl C.gates x u →
   vl C.gates x C.output=vl C2.gates x C2.output:=by
  intro x hru;have hall:=vlab hn C hcl hrb hjr hr hu hune hon0 hur x hru
  by_cases hor: C.output=n+r
  ·have hc2: C2.output=u2:=by
    change rd n jl 0 (rd n r u C.output)=u2;rw[hor,rd_eq]
   rw[hor,hc2,hru,hvl_u x]
  ·have hlout: lw2 n jl r C2.output=C.output:=lw2r hjr hon0 hor;rw[hall C2.output,hlout]
 let x_p: Fin n→Bool:=fun v => decide (v=p)
 have hpC: vl C.gates x_p C.output=false:=by
  rw[hval_C];simp only[graphFun,boF,dFn,x_p,dTe]
  refine ⟨fun ⟨a,ha,e⟩ => hpnA (e ▸ ha),fun ⟨v1,v2,huv,e1,e2⟩ => huv.ne (e1.trans e2.symm)⟩
 have hp2: vl C2.gates x_p C2.output=true:=by
  rw[hval_C2];simp[graphFun,x_p]
 have hx_p_ru: vl C.gates x_p (n+r)≠vl C.gates x_p u:=fun h => by
  have:=hCC2 x_p h;rw[hpC,hp2] at this;cases this
 have hpu: vl C2.gates x_p u2=true:=by
  rw[hvl_r,hvl_u] at hx_p_ru
  cases hu2v: vl C2.gates x_p u2
  ·simp[hu2v] at hx_p_ru
  ·rfl
 have hpw: vl C2.gates x_p wl2=false:=by
  rw[hvl_r,hvl_u,hpu] at hx_p_ru
  have hxl: x_p l=false:=by simp[x_p,hlp]
  rw[hxl] at hx_p_ru
  cases hwl2v: vl C2.gates x_p wl2
  ·rfl
  ·simp[hwl2v] at hx_p_ru
 have hntx: ∀ w < n+C2.gates.length,w≠p.val →
   (∀ j < C2.gates.length,w=n+j→(d2.role j).1≠Kind.top) →
   vl C2.gates x_p w=false:=by
  intro w hw hwp hnt
  have h0: vl C2.gates (Function.update x_p p false) w=vl C2.gates x_p w :=
   nnti hv2 hcl2 p hp_iso x_p false w hw hwp hnt
  have hall0: Function.update x_p p false=fun _ => false:=by
   funext v;by_cases hvp: v=p
   ·subst hvp;simp
   ·rw[fupn hvp];simp[x_p,hvp]
  rw[←h0,hall0]
  clear h0 hall0 hwp hnt
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   by_cases hwn: w < n
   ·rw[vli _ _ w hwn]
   ·set j:=w - n
    have hj: j < C2.gates.length:=by omega
    have hgj: C2.gates[j]? = some (gateAt C2 j):=by simp[gateAt,List.getD,hj]
    rw[show w=n+j by omega,vlg C2.gates hcl2 _ j _ hgj];have hnn:=ncc_no_not hv2 j hj;have hcg:=hcl2 j _ hgj
    rcases hcg with ⟨h1,_⟩ | ⟨h1|h1,a,b,_,_,hab⟩
    ·exact absurd h1 hnn
    ·rw[h1,hab];have ha: a < n+j:=hv2.1 j hj a (by rw[hab];simp);have hb: b < n+j:=hv2.1 j hj b (by rw[hab];simp);simp[GateOp.eval,ih a (by omega) (by omega),ih b (by omega) (by omega)]
    ·rw[h1,hab];have ha: a < n+j:=hv2.1 j hj a (by rw[hab];simp);have hb: b < n+j:=hv2.1 j hj b (by rw[hab];simp);simp[GateOp.eval,ih a (by omega) (by omega),ih b (by omega) (by omega)]
 have hu2_top: u2=p.val∨(n ≤ u2∧u2 - n∈topGates d2 C2):=by
  by_cases h1: u2=p.val
  ·exact Or.inl h1
  ·right
   by_contra hnot
   have hnt: ∀ j < C2.gates.length,u2=n+j→(d2.role j).1≠Kind.top:=by
    intro j hj he htop;exact hnot ⟨by omega,mF.mpr ⟨mR.mpr (by omega),by rw[he,ascl];exact htop⟩⟩
   have hf:=hntx u2 hu2_lt h1 hnt;rw[hf] at hpu;cases hpu
 have htGl: ∀ k∈topGates d2 C2,k < C2.gates.length:=fun k hk =>
  mR.mp (mF.mp hk).1
 have hnt0: ∀ j' < C2.gates.length,(d2.role j').1≠Kind.top →
   n+r∉(gateAt C (li2 jl r j')).inputs:=by
  intro j' hj' hnt hmem;have hlif:=r2l C hcl hrb hjr hr hu j' (by omega)
  have hu2_in: u2∈(gateAt C2 j').inputs:=by
   rw[hlif.2];exact lmm.mpr ⟨n+r,hmem,by rw[rd_eq]⟩
  rcases hv2.2.2.2.2.1 j' hj' with htop|⟨t,ht,hrt2,hrb_t⟩
  ·exact hnt htop
  ·
   have hu2_ne_nt: ∀ w < n+C2.gates.length,(w≠p.val ∧ ∀ k < C2.gates.length,w=n+k→(d2.role k).1≠Kind.top) → w≠u2:=by
    intro w _ ⟨h1,h2⟩ he
    rcases hu2_top with hup|⟨hge,htg⟩
    ·exact h1 (he.trans hup)
    ·exact h2 (u2 - n) (htGl _ htg) (by omega) (mF.mp htg).2
   have hne_u2: ∀ w∈(gateAt C2 j').inputs,w≠u2:=by
    intro w hw
    have hwlt: w < n+C2.gates.length:=by have:=hv2.1 j' hj' w hw;omega
    apply hu2_ne_nt w hwlt
    cases hkr: (d2.role j').1 with
    | top => exact absurd hkr hnt
    | b =>
     have hbw:=hrb_t hkr;obtain ⟨jb,hjb,hbw2,_,_,hin⟩:=(hv2.2.2.2.2.2.1 t ht).1;have hje: j' = jb:=(by omega);subst hje
     have hzr_nt: d2.zroot t≠p.val ∧ ∀ k < C2.gates.length,d2.zroot t=n+k→(d2.role k).1≠Kind.top:=by
      rcases zrs hv2 t ht with h1|⟨jz,_,h1,h2⟩
      ·exact ⟨fun e => hpnc (Fin.ext (h1.symm.trans e) ▸ ht),fun k _ ek => by omega⟩
      ·exact ⟨by omega,fun k _ ek => by have: k=jz := (by omega);rw[this,h2];intro hc;cases hc⟩
     have hor_nt: d2.oroot t≠p.val ∧ ∀ k < C2.gates.length,d2.oroot t=n+k→(d2.role k).1≠Kind.top:=by
      rcases ors hv2 t ht with ⟨r',hown',hlam'⟩ | ⟨jo,_,h1,h2⟩
      ·have hne_r' : r' ≠ p:=fun er => hp_iso t (er ▸ (hv2.2.2.1.1 t r' hown').1).symm
       have hlam:=(hv2.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
       ·rcases hlam.2.1 with h3|⟨jz,_,h3,hrz⟩
        ·exact ⟨fun e => hne_r' (Fin.ext (h3.symm.trans (hlam'.symm.trans e))),fun k _ ek => by omega⟩
        ·exact ⟨by omega,fun k _ ek => by have: k=jz := (by omega);rw[this,hrz];intro hc;cases hc⟩
       ·exact ⟨fun e => hne_r' (Fin.ext (hlam.symm.trans (hlam'.symm.trans e))),fun k _ ek => by omega⟩
      ·exact ⟨by omega,fun k _ ek => by have: k=jo := (by omega);rw[this,h2];intro hc;cases hc⟩
     rcases hin with h|h <;> rw[h] at hw <;> simp at hw <;> rcases hw with rfl|rfl
     ·exact hzr_nt
     ·exact hor_nt
     ·exact hor_nt
     ·exact hzr_nt
    | z =>
     have hjZ: j' ∈ gatesOf d2 C2 Kind.z t.val :=
      mF.mpr ⟨mR.mpr hj',Prod.ext hkr hrt2⟩
     rcases ((hv2.2.2.2.2.2.1 t ht).2.1.1 j' hjZ).2.2 w hw with hL|⟨hge,hG⟩
     ·simp only[zLeaves,mN,mI,mF] at hL
      rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
      ·exact ⟨fun e => hpnc (Fin.ext e.symm ▸ ht),fun k _ ek => by omega⟩
      ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(hv2.2.2.2.2.2.1 s hs).1
       exact ⟨by omega,fun k _ ek => by have: k=jb := (by omega);rw[this,hrb_s];intro hc;cases hc⟩
     ·have hG' := (mF.mp hG).2
      exact ⟨by omega,fun k _ ek => by have: k=w - n := (by omega);rw[this,hG'];intro hc;cases hc⟩
    | o =>
     have hjO: j' ∈ gatesOf d2 C2 Kind.o t.val :=
      mF.mpr ⟨mR.mpr hj',Prod.ext hkr hrt2⟩
     rcases ((hv2.2.2.2.2.2.1 t ht).2.2.1.1 j' hjO).2.2 w hw with hL|⟨hge,hG⟩
     ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',rfl⟩:=hL
      have hne_r' : r' ≠ p:=fun er => hp_iso t (er ▸ (hv2.2.2.1.1 t r' hown').1).symm
      have hlam:=(hv2.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
      ·rcases hlam.2.1 with h3|⟨jz,_,h3,hrz⟩
       ·exact ⟨fun e => hne_r' (Fin.ext (h3.symm.trans e)),fun k _ ek => by omega⟩
       ·exact ⟨by omega,fun k _ ek => by have: k=jz := (by omega);rw[this,hrz];intro hc;cases hc⟩
      ·exact ⟨fun e => hne_r' (Fin.ext (hlam.symm.trans e)),fun k _ ek => by omega⟩
     ·have hG' := (mF.mp hG).2
      exact ⟨by omega,fun k _ ek => by have: k=w - n := (by omega);rw[this,hG'];intro hc;cases hc⟩
   exact hne_u2 u2 hu2_in rfl
 have hvnt: ∀ x: Fin n→Bool,∀ w < n+C2.gates.length,
   (∀ j' < C2.gates.length,w=n + j' → (d2.role j').1≠Kind.top) →
   vl C.gates x (lw2 n jl r w)=vl C2.gates x w:=by
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   intro hw hnt
   by_cases hwn: w < n
   ·rw[lw2i n jl r w hwn,vli _ _ w hwn,vli _ _ w hwn]
   ·set j' := w - n
    have hweq: w=n + j' := by omega
    have hj' : j' < C2.gates.length:=by omega
    have hnt' : (d2.role j').1≠Kind.top:=hnt j' hj' hweq;have hno:=hnt0 j' hj' hnt';have hlif:=r2l C hcl hrb hjr hr hu j' (by omega);have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur j' (by omega) hno;have hlt_C: li2 jl r j' < C.gates.length:=li2lt hjr hr (by rw[←hlen2];exact hj')
    have hgC: C.gates[li2 jl r j']? = some (gateAt C (li2 jl r j')):=by
     simp[gateAt,List.getD,hlt_C]
    have hg2: C2.gates[j']? = some (gateAt C2 j'):=by simp[gateAt,List.getD,hj']
    rw[hweq,lw2g,vlg C.gates hcl x (li2 jl r j') _ hgC,
      vlg C2.gates hcl2 x j' _ hg2,←hlif.1,hinp,lmp]
    congr 1;apply List.map_congr_left;intro a ha
    have halt: a < n + j' := hv2.1 j' hj' a ha;apply ih a (by omega) (by omega);intro k hk hak htop
    have ha_ne_top: ∀ h1: a=n+k,(d2.role k).1=Kind.top→False:=by
     intro h1 h2
     rcases hv2.2.2.2.2.1 j' hj' with htop_j|⟨t,ht,hrt2,hrb_t⟩
     ·exact hnt' htop_j
     ·cases hkr: (d2.role j').1 with
      | top => exact hnt' hkr
      | b =>
       have hbw:=hrb_t hkr;obtain ⟨jb,hjb,hbw2,_,_,hin⟩:=(hv2.2.2.2.2.2.1 t ht).1;have hje: j' = jb:=(by omega);subst hje
       rcases hin with h|h <;> rw[h] at ha <;> simp at ha <;> rcases ha with h3|h3
       ·rcases zrs hv2 t ht with hzr|⟨jz,_,hzr,hrz⟩
        ·omega
        ·have: k=jz := (by omega);rw[this,hrz] at h2;cases h2
       ·rcases ors hv2 t ht with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
        ·have hlam:=(hv2.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
         ·rcases hlam.2.1 with h4|⟨jz,_,h4,hrz⟩
          ·omega
          ·have: k=jz := (by omega);rw[this,hrz] at h2;cases h2
         ·omega
        ·have: k=jo := (by omega);rw[this,hro] at h2;cases h2
       ·rcases ors hv2 t ht with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
        ·have hlam:=(hv2.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
         ·rcases hlam.2.1 with h4|⟨jz,_,h4,hrz⟩
          ·omega
          ·have: k=jz := (by omega);rw[this,hrz] at h2;cases h2
         ·omega
        ·have: k=jo := (by omega);rw[this,hro] at h2;cases h2
       ·rcases zrs hv2 t ht with hzr|⟨jz,_,hzr,hrz⟩
        ·omega
        ·have: k=jz := (by omega);rw[this,hrz] at h2;cases h2
      | z =>
       have hjZ: j' ∈ gatesOf d2 C2 Kind.z t.val :=
        mF.mpr ⟨mR.mpr hj',Prod.ext hkr hrt2⟩
       rcases ((hv2.2.2.2.2.2.1 t ht).2.1.1 j' hjZ).2.2 a ha with hL|⟨_,hG⟩
       ·simp only[zLeaves,mN,mI,mF] at hL
        rcases hL with h3|⟨s,⟨hs,_⟩,h3⟩
        ·omega
        ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(hv2.2.2.2.2.2.1 s hs).1
         have: k=jb := (by omega);rw[this,hrb_s] at h2;cases h2
       ·have hG' := (mF.mp hG).2
        have: k=a - n := (by omega);rw[this,hG'] at h2;cases h2
      | o =>
       have hjO: j' ∈ gatesOf d2 C2 Kind.o t.val :=
        mF.mpr ⟨mR.mpr hj',Prod.ext hkr hrt2⟩
       rcases ((hv2.2.2.2.2.2.1 t ht).2.2.1.1 j' hjO).2.2 a ha with hL|⟨_,hG⟩
       ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',hlam'⟩:=hL;have hlam:=(hv2.2.2.2.2.2.1 t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
        ·rcases hlam.2.1 with h4|⟨jz,_,h4,hrz⟩
         ·omega
         ·have: k=jz := (by omega);rw[this,hrz] at h2;cases h2
        ·omega
       ·have hG' := (mF.mp hG).2
        have: k=a - n := (by omega);rw[this,hG'] at h2;cases h2
    exact ha_ne_top hak htop
 have htop:=hv2.2.2.2.2.2.2
 have hu2_mem: u2∈topLeaves d2 (insert p A)∨(n ≤ u2∧u2 - n∈topGates d2 C2):=by
  rcases hu2_top with h1|h2
  ·left;rw[h1];exact Finset.mem_union_left _ (mI.mpr ⟨p,mNs _ _,rfl⟩)
  ·exact Or.inr h2
 let Gu:=osG n C2 (topGates d2 C2) u2;let Lu:=osL n C2 (topGates d2 C2) (topLeaves d2 (insert p A)) u2;have hsub_u:=osT hv2.1 htop htGl u2 hu2_mem;obtain ⟨hGu_sub,hLu_sub,hGu_le⟩:=osS hv2.1 htop htGl u2
 have hp_in_Lu: p.val∈Lu:=by
  obtain ⟨v,hvL,hxv⟩:=(osV hcl2 hv2.1 htop htGl x_p u2 hu2_mem).mp hpu
  have hv_eq: v=p.val:=by
   have hv_tl:=hLu_sub hvL;simp only[topLeaves,mU,mI,mF] at hv_tl
   rcases hv_tl with ⟨a,ha,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
   ·rw[vli C2.gates x_p a.val a.isLt] at hxv;simp only[x_p,dTe] at hxv;exact congrArg Fin.val hxv
   ·obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 s hs).1;have hf:=nbs hv2 hcl2 p (d2.bw s) (by omega) s hs rfl;dsimp only[x_p] at hxv;rw[hf] at hxv;cases hxv
  exact hv_eq ▸ hvL
 have hnrt: ∀ k' ∈ topGates d2 C2,
   n+r∈(gateAt C (li2 jl r k')).inputs → u2∈(gateAt C2 k').inputs:=by
  intro k' hk' hmem;have hlif:=r2l C hcl hrb hjr hr hu k' (by have:=htGl k' hk';omega);rw[hlif.2];exact lmm.mpr ⟨n+r,hmem,by rw[rd_eq]⟩
 have hor0: (u2=C2.output∧C.output=n+r) ∨
   (u2≠C2.output∧C.output≠n+r ∧
    ∀ k' ∈ topGates d2 C2,u2∈(gateAt C2 k').inputs → n+r∈(gateAt C (li2 jl r k')).inputs):=by
  by_cases he: u2=C2.output
  ·left;refine ⟨he,?_⟩
   by_contra hne
   have hc2_eq: lw2 n jl r C2.output=C.output:=lw2r hjr hon0 hne
   have hcout_u: C.output=u:=by rw[←hc2_eq,←he,hu_lw]
   rw[hcout_u,hvl_u x_p,he,hp2] at hpC;cases hpC
  ·right
   have hne_out: C.output≠n+r:=fun e => he (by
    change u2=rd n jl 0 (rd n r u C.output);rw[e,rd_eq])
   refine ⟨he,hne_out,?_⟩
   intro k' hk' hu2_in
   by_contra hnot_read
   have hno_any: ∀ q' < C2.gates.length,n+r∉(gateAt C (li2 jl r q')).inputs:=by
    intro q' hq' hmem
    by_cases hqt: (d2.role q').1=Kind.top
    ·have hq'_tg: q' ∈ topGates d2 C2:=mF.mpr ⟨mR.mpr hq',hqt⟩;have hu2_in' := hnrt q' hq'_tg hmem
     have hq'_eq: q' = k' := by
      by_contra hqk
      have htot: readsIn C2 (topGates d2 C2) u2 ≤ 1:=by
       rcases hu2_mem with hL|⟨hge,hG⟩
       ·have:=(htop.2.1 u2 hL).2;split_ifs at this <;> omega
       ·have:=htop.2.2.1 (u2 - n) hG;rw[show n+(u2 - n)=u2 by omega] at this
        split_ifs at this <;> omega
      have h1: 1 ≤ (gateAt C2 k').inputs.count u2:=lcpi.mpr hu2_in
      have h2: 1 ≤ (gateAt C2 q').inputs.count u2:=lcpi.mpr hu2_in'
      have hsub: ({k',q'}: Finset ℕ)⊆topGates d2 C2:=by
       intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
      have hsum:=sum_le_sum_of_subset (f:=fun m => (gateAt C2 m).inputs.count u2) hsub
      rw[sum_pair (Ne.symm hqk)] at hsum;change _ ≤ readsIn C2 (topGates d2 C2) u2 at hsum;omega
     exact hnot_read (hq'_eq ▸ hmem)
    ·exact hnt0 q' hq' hqt hmem
   have hall_xp: ∀ w < n+C2.gates.length,vl C.gates x_p (lw2 n jl r w)=vl C2.gates x_p w:=by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
     intro hw
     by_cases hwn: w < n
     ·rw[lw2i n jl r w hwn,vli _ _ w hwn,vli _ _ w hwn]
     ·set q' := w - n
      have hq' : q' < C2.gates.length:=by omega
      have hlif:=r2l C hcl hrb hjr hr hu q' (by omega);have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur q' (by omega) (hno_any q' hq');have hlt_C: li2 jl r q' < C.gates.length:=li2lt hjr hr (by rw[←hlen2];exact hq')
      have hgC: C.gates[li2 jl r q']? = some (gateAt C (li2 jl r q')):=by
       simp[gateAt,List.getD,hlt_C]
      have hg2: C2.gates[q']? = some (gateAt C2 q'):=by simp[gateAt,List.getD,hq']
      rw[show w=n + q' by omega,lw2g,
        vlg C.gates hcl x_p (li2 jl r q') _ hgC,
        vlg C2.gates hcl2 x_p q' _ hg2,←hlif.1,hinp,lmp]
      congr 1;apply List.map_congr_left;intro a ha
      exact ih a (by have := hv2.1 q' hq' a ha;omega) (by have := hv2.1 q' hq' a ha;omega)
   have hc2_lt: C2.output < n+C2.gates.length:=orTree_rt_lt htop htGl (by
    intro w hw;simp only[topLeaves,mU,mI,mF] at hw
    rcases hw with ⟨a,_,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
    ·have:=a.isLt;omega
    ·obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 s hs).1;omega)
   have hlout: lw2 n jl r C2.output=C.output:=lw2r hjr hon0 hne_out
   have:=hall_xp C2.output hc2_lt
   rw[hlout,hpC,hp2] at this;cases this
 have hCoi: ∀ x: Fin n→Bool,
   vl C.gates x C.output=true ↔
    vl C.gates x (n+r)=true ∨
    ∃ v∈topLeaves d2 (insert p A) \ Lu,vl C2.gates x v=true:=by
  intro x
  have hkey: ∀ w: ℕ,(w∈topLeaves d2 (insert p A)∨(n ≤ w∧w - n∈topGates d2 C2)) →
    (w=u2∨(w∉Lu ∧ ¬ (n ≤ w∧w - n∈Gu))) →
    (vl C.gates x (if w=u2 then n+r else lw2 n jl r w)=true ↔
     (p.val∈osL n C2 (topGates d2 C2) (topLeaves d2 (insert p A)) w∧vl C.gates x (n+r)=true) ∨
     ∃ v∈osL n C2 (topGates d2 C2) (topLeaves d2 (insert p A)) w \ Lu,vl C2.gates x v=true):=by
   intro w
   induction w using Nat.strong_induction_on with
   | ind w ih =>
    intro hw hcond
    by_cases hwu: w=u2
    ·rw[hwu];simp only[↓reduceIte];change vl C.gates x (n+r)=true↔(p.val∈Lu∧vl C.gates x (n+r)=true) ∨ ∃ v∈Lu \ Lu,vl C2.gates x v=true;simp only[Finset.sdiff_self,notMem_empty,false_and,exists_false,or_false]
     exact ⟨fun h => ⟨hp_in_Lu,h⟩,fun h => h.2⟩
    ·simp only[hwu,↓reduceIte]
     have hcond' : w∉Lu ∧ ¬ (n ≤ w∧w - n∈Gu):=by rcases hcond with h|h;exact absurd h hwu;exact h
     rcases hw with hL|hG
     ·
      have hnot_top: ∀ j' < C2.gates.length,w=n + j' → (d2.role j').1≠Kind.top:=by
       intro j' hj' he htop_j;exact (htop.2.1 w hL).1 ⟨by omega,by rw[he,ascl];exact mF.mpr ⟨mR.mpr hj',htop_j⟩⟩
      have hwlt: w < n+C2.gates.length:=by
       simp only[topLeaves,mU,mI,mF] at hL
       rcases hL with ⟨a,_,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
       ·have:=a.isLt;omega
       ·obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 s hs).1;omega
      rw[hvnt x w hwlt hnot_top,osLl htop hL]
      have hwp: p.val≠w:=fun e => hcond'.1 (e ▸ hp_in_Lu)
      simp[hwp,hcond'.1]
     ·
      set k' := w - n
      have hweq: w=n + k' := by omega
      have hk' : k' ∈ topGates d2 C2:=hG.2;have hk'lt: k' < C2.gates.length:=htGl k' hk';obtain ⟨hop,hlen,hins⟩:=htop.1 k' hk';obtain ⟨a,b,hab⟩:=ll2.mp hlen;have ha_lt: a < n + k' := hv2.1 k' hk'lt a (by simp[hab]);have hb_lt: b < n + k' := hv2.1 k' hk'lt b (by simp[hab]);have hsub_k:=osGq hv2.1 htop hk' hk'lt hab
      have ha_not_Gu: a=u2∨(a∉Lu ∧ ¬ (n ≤ a∧a - n∈Gu)):=by
       by_cases hau: a=u2
       ·exact Or.inl hau
       ·right
        have ha_in_Gu_imp: (a∈Lu∨(n ≤ a∧a - n∈Gu))→False:=by
         intro hmem_a
         have hr1: readsIn C2 Gu a=1:=by
          rcases hmem_a with haL|⟨han,haG⟩
          ·have:=(hsub_u.2.1 a haL).2;simp[hau] at this;exact this
          ·have:=hsub_u.2.2.1 (a - n) haG;rw[show n+(a - n)=a by omega] at this
           simp[hau] at this;exact this
         have htot: readsIn C2 (topGates d2 C2) a ≤ 1:=by
          rcases hins a (by simp[hab]) with haL|⟨han,haG⟩
          ·have:=(htop.2.1 a haL).2;split_ifs at this <;> omega
          ·have:=htop.2.2.1 (a - n) haG;rw[show n+(a - n)=a by omega] at this
           split_ifs at this <;> omega
         have hk'_not_Gu: k' ∉ Gu:=fun h => hcond'.2 ⟨by omega,by simpa [k'] using h⟩
         have hsum_le: readsIn C2 (insert k' Gu) a ≤ readsIn C2 (topGates d2 C2) a :=
          sum_le_sum_of_subset (insert_subset_iff.mpr ⟨hk',hGu_sub⟩)
         have hsum_eq: readsIn C2 (insert k' Gu) a=(gateAt C2 k').inputs.count a+readsIn C2 Gu a :=
          sum_insert hk'_not_Gu
         have hcnt: 1 ≤ (gateAt C2 k').inputs.count a:=by rw[hab];simp
         omega
        exact ⟨fun h => ha_in_Gu_imp (Or.inl h),fun h => ha_in_Gu_imp (Or.inr h)⟩
      have hb_not_Gu: b=u2∨(b∉Lu ∧ ¬ (n ≤ b∧b - n∈Gu)):=by
       by_cases hbu: b=u2
       ·exact Or.inl hbu
       ·right
        have hb_in_Gu_imp: (b∈Lu∨(n ≤ b∧b - n∈Gu))→False:=by
         intro hmem_b
         have hr1: readsIn C2 Gu b=1:=by
          rcases hmem_b with hbL|⟨hbn,hbG⟩
          ·have:=(hsub_u.2.1 b hbL).2;simp[hbu] at this;exact this
          ·have:=hsub_u.2.2.1 (b - n) hbG;rw[show n+(b - n)=b by omega] at this
           simp[hbu] at this;exact this
         have htot: readsIn C2 (topGates d2 C2) b ≤ 1:=by
          rcases hins b (by simp[hab]) with hbL|⟨hbn,hbG⟩
          ·have:=(htop.2.1 b hbL).2;split_ifs at this <;> omega
          ·have:=htop.2.2.1 (b - n) hbG;rw[show n+(b - n)=b by omega] at this
           split_ifs at this <;> omega
         have hk'_not_Gu: k' ∉ Gu:=fun h => hcond'.2 ⟨by omega,by simpa [k'] using h⟩
         have hsum_le: readsIn C2 (insert k' Gu) b ≤ readsIn C2 (topGates d2 C2) b :=
          sum_le_sum_of_subset (insert_subset_iff.mpr ⟨hk',hGu_sub⟩)
         have hsum_eq: readsIn C2 (insert k' Gu) b=(gateAt C2 k').inputs.count b+readsIn C2 Gu b :=
          sum_insert hk'_not_Gu
         have hcnt: 1 ≤ (gateAt C2 k').inputs.count b:=by rw[hab];simp
         omega
        exact ⟨fun h => hb_in_Gu_imp (Or.inl h),fun h => hb_in_Gu_imp (Or.inr h)⟩
      have hlif:=r2l C hcl hrb hjr hr hu k' (by omega)
      have hin_C: (gateAt C (li2 jl r k')).inputs =
        [if a=u2 then n+r else lw2 n jl r a,
        if b=u2 then n+r else lw2 n jl r b]:=by
       by_cases hnr: n+r∈(gateAt C (li2 jl r k')).inputs
       ·have hu2_in:=hnrt k' hk' hnr
        have hlenC: (gateAt C (li2 jl r k')).inputs.length=2:=by
         rw[hlif.2,llm] at hlen;exact hlen
        obtain ⟨x1,x2,hx12⟩:=ll2.mp hlenC
        have hmap: [rd n jl 0 (rd n r u x1),rd n jl 0 (rd n r u x2)]=[a,b]:=by
         rw[←hab,hlif.2,hx12];rfl
        have hm1: rd n jl 0 (rd n r u x1)=a:=(List.cons.inj hmap).1;have hm2: rd n jl 0 (rd n r u x2)=b:=(List.cons.inj (List.cons.inj hmap).2).1
        have hne_jl1: x1≠n+jl:=fun e =>
         li2nr jl r k' (hur (li2 jl r k') ((li2lt hjr hr (by omega): _ < C.gates.length)) (by rw[hx12,e];simp))
        have hne_jl2: x2≠n+jl:=fun e =>
         li2nr jl r k' (hur (li2 jl r k') ((li2lt hjr hr (by omega): _ < C.gates.length)) (by rw[hx12,e];simp))
        have hab_ne: a≠b:=by
         intro e;subst e
         have hcnt: 2 ≤ (gateAt C2 k').inputs.count a:=by rw[hab];simp
         have hle: (gateAt C2 k').inputs.count a ≤ readsIn C2 (topGates d2 C2) a :=
          single_le_sum (f := fun m => (gateAt C2 m).inputs.count a) (fun _ _ => Nat.zero_le _) hk'
         rcases hins a (by simp[hab]) with hL|⟨han,hG⟩
         ·have:=(htop.2.1 a hL).2;split_ifs at this <;> omega
         ·have:=htop.2.2.1 (a - n) hG;rw[show n+(a - n)=a by omega] at this
          split_ifs at this <;> omega
        rw[hx12] at hnr ⊢;simp only[lmc,lnn,or_false] at hnr
        rcases hnr with rfl|rfl
        ·have ha_eq: a=u2:=by change a=rd n jl 0 u;rw[←hm1,rd_eq]
         have hb_ne: b≠u2:=by rw[←ha_eq];exact hab_ne.symm
         have hx2_ne: x2≠n+r:=fun e => hb_ne (by change b=rd n jl 0 u;rw[←hm2,e,rd_eq])
         rw[if_pos ha_eq,if_neg hb_ne,←hm2,lw2r hjr hne_jl2 hx2_ne]
        ·have hb_eq: b=u2:=by change b=rd n jl 0 u;rw[←hm2,rd_eq]
         have ha_ne: a≠u2:=by rw[←hb_eq];exact hab_ne
         have hx1_ne: x1≠n+r:=fun e => ha_ne (by change a=rd n jl 0 u;rw[←hm1,e,rd_eq])
         rw[if_neg ha_ne,if_pos hb_eq,←hm1,lw2r hjr hne_jl1 hx1_ne]
       ·have ha_ne: a≠u2:=by
         intro e;rcases hor0 with ⟨he,_⟩ | ⟨_,_,hread⟩
         ·have:=htop.2.2.1 k' hk'
          have htot: readsIn C2 (topGates d2 C2) C2.output=0:=by
           rcases hu2_mem with hL|⟨hge,hG⟩
           ·have:=(htop.2.1 u2 hL).2;rw[he] at this;simp at this;exact this
           ·have:=htop.2.2.1 (u2 - n) hG;rw[show n+(u2 - n)=u2 by omega,he] at this;simp at this;exact this
          have h1: 1 ≤ (gateAt C2 k').inputs.count C2.output:=by rw[hab,e,he];simp
          have hle: (gateAt C2 k').inputs.count C2.output ≤ readsIn C2 (topGates d2 C2) C2.output :=
           single_le_sum (f := fun m => (gateAt C2 m).inputs.count C2.output) (fun _ _ => Nat.zero_le _) hk'
          omega
         ·exact hnr (hread k' hk' (by rw[hab,e];simp))
        have hb_ne: b≠u2:=by
         intro e;rcases hor0 with ⟨he,_⟩ | ⟨_,_,hread⟩
         ·have htot: readsIn C2 (topGates d2 C2) C2.output=0:=by
           rcases hu2_mem with hL|⟨hge,hG⟩
           ·have:=(htop.2.1 u2 hL).2;rw[he] at this;simp at this;exact this
           ·have:=htop.2.2.1 (u2 - n) hG;rw[show n+(u2 - n)=u2 by omega,he] at this;simp at this;exact this
          have h1: 1 ≤ (gateAt C2 k').inputs.count C2.output:=by rw[hab,e,he];simp
          have hle: (gateAt C2 k').inputs.count C2.output ≤ readsIn C2 (topGates d2 C2) C2.output :=
           single_le_sum (f := fun m => (gateAt C2 m).inputs.count C2.output) (fun _ _ => Nat.zero_le _) hk'
          omega
         ·exact hnr (hread k' hk' (by rw[hab,e];simp))
        have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur k' (by omega) hnr;rw[hinp,hab];simp[ha_ne,hb_ne]
      have hlt_C: li2 jl r k' < C.gates.length:=li2lt hjr hr (by rw[←hlen2];exact hk'lt)
      have hgC: C.gates[li2 jl r k']? = some (gateAt C (li2 jl r k')):=by
       simp[gateAt,List.getD,hlt_C]
      rw[hweq,lw2g,vlg C.gates hcl x (li2 jl r k') _ hgC,←hlif.1,hop,hin_C]
      simp only[GateOp.eval,lmC,lmN,lyC,lyN,
       id_eq,Bool.or_false,boT,hsub_k.2]
      rw[ih a (by omega) (hins a (by simp[hab])) ha_not_Gu,
        ih b (by omega) (hins b (by simp[hab])) hb_not_Gu]
      simp only[mU,mem_sdiff]
      constructor
      ·rintro ((⟨h1,h2⟩ | ⟨v,⟨hv1,hv2⟩,hv3⟩)|(⟨h1,h2⟩ | ⟨v,⟨hv1,hv2⟩,hv3⟩))
       ·exact Or.inl ⟨Or.inl h1,h2⟩
       ·exact Or.inr ⟨v,⟨Or.inl hv1,hv2⟩,hv3⟩
       ·exact Or.inl ⟨Or.inr h1,h2⟩
       ·exact Or.inr ⟨v,⟨Or.inr hv1,hv2⟩,hv3⟩
      ·rintro (⟨h1|h1,h2⟩ | ⟨v,⟨hv1|hv1,hv2⟩,hv3⟩)
       ·exact Or.inl (Or.inl ⟨h1,h2⟩)
       ·exact Or.inr (Or.inl ⟨h1,h2⟩)
       ·exact Or.inl (Or.inr ⟨v,⟨hv1,hv2⟩,hv3⟩)
       ·exact Or.inr (Or.inr ⟨v,⟨hv1,hv2⟩,hv3⟩)
  have hrm: C2.output∈topLeaves d2 (insert p A)∨(n ≤ C2.output∧C2.output - n∈topGates d2 C2):=by
   by_cases hGe: topGates d2 C2 = ∅
   ·have h1:=htop.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
   ·have h1:=htop.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
  have hroot_cond: C2.output=u2∨(C2.output∉Lu ∧ ¬ (n ≤ C2.output∧C2.output - n∈Gu)):=by
   by_cases he: C2.output=u2
   ·exact Or.inl he
   ·right
    have hlt_u: u2 < C2.output:=by
     have hle:=orTree_lt_root hcl2 htop htGl _ u2 rfl (by
      rcases hu2_mem with h1|⟨h1,h2⟩
      ·exact Or.inl h1
      ·exact Or.inr ⟨u2 - n,h2,by omega⟩)
     omega
    refine ⟨fun hL => ?_,fun ⟨_,hG⟩ => ?_⟩
    ·have hle:=orTree_lt_root hcl2 hsub_u (fun k hk => htGl k (hGu_sub hk)) _ C2.output rfl (Or.inl hL)
     omega
    ·have:=hGu_le (C2.output - n) hG;omega
  have hres:=hkey C2.output hrm hroot_cond;have hsa:=osRL hv2.1 htop htGl;rw[hsa.2] at hres
  have hp_tl: p.val∈topLeaves d2 (insert p A) :=
   Finset.mem_union_left _ (mI.mpr ⟨p,mNs _ _,rfl⟩)
  have hout_eq: (if C2.output=u2 then n+r else lw2 n jl r C2.output)=C.output:=by
   rcases hor0 with ⟨he,hr_out⟩ | ⟨hne,hne_out,_⟩
   ·simp[he.symm,hr_out]
   ·rw[if_neg (Ne.symm hne),lw2r hjr hon0 hne_out]
  rw[hout_eq] at hres
  simpa [hp_tl] using hres
 let x_pq: Fin n→Bool:=fun v => decide (v=p∨v=q)
 have hpqC: vl C.gates x_pq C.output=true:=by
  rw[hval_C];simp only[graphFun,boT,dTe]
  right;exact ⟨p,q,(hp q).mpr (Or.inr rfl),by simp[x_pq],by simp[x_pq]⟩
 have htfx: ∀ v∈topLeaves d2 (insert p A) \ Lu,vl C2.gates x_pq v=false:=by
  intro v hv;obtain ⟨hv_tl,hv_not⟩:=mem_sdiff.mp hv;simp only[topLeaves,mU,mI,mF] at hv_tl
  rcases hv_tl with ⟨a,ha,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
  ·rw[vli C2.gates x_pq a.val a.isLt]
   have hap: a≠p:=fun e => hv_not (e ▸ hp_in_Lu)
   have haq: a≠q:=by
    rcases mN.mp ha with rfl|haA
    ·exact absurd rfl hap
    ·exact fun e => hqnA (e ▸ haA)
   simp[x_pq,hap,haq]
  ·obtain ⟨jb,hjb,hbw,hrb_s,_,_⟩:=(hv2.2.2.2.2.2.1 s hs).1
   have hnt: ∀ j' < C2.gates.length,d2.bw s=n + j' → (d2.role j').1≠Kind.top:=by
    intro j' _ ej;have: j' = jb := (by omega);rw[this,hrb_s];intro hc;cases hc
   have h1:=nnti hv2 hcl2 p hp_iso x_pq false (d2.bw s) (by omega) (by omega) hnt
   have hupd: Function.update x_pq p false=fun v => decide (v=q):=by
    funext i;by_cases hip: i=p
    ·subst hip;simp[hpq]
    ·rw[fupn hip];simp[x_pq,hip]
   rw[←h1,hupd];exact nbs hv2 hcl2 q (d2.bw s) (by omega) s hs rfl
 have hpqw: vl C2.gates x_pq wl2=true:=by
  rcases (hCoi x_pq).mp hpqC with hr_t|⟨v,hv,hxv⟩
  ·rw[hvl_r] at hr_t
   have hxl: x_pq l=false:=by simp[x_pq,hlp,hql.symm]
   rw[hxl] at hr_t;simp at hr_t;exact hr_t.1
  ·rw[htfx v hv] at hxv;cases hxv
 have hw2t: ∀ j' < C2.gates.length,wl2=n + j' → (d2.role j').1≠Kind.top:=by
  intro j' hj' he htop_j;have hj'_tg: j' ∈ topGates d2 C2:=mF.mpr ⟨mR.mpr hj',htop_j⟩
  have hmem: wl2∈topLeaves d2 (insert p A)∨(n ≤ wl2∧wl2 - n∈topGates d2 C2) :=
   Or.inr ⟨by omega,by rw[he,ascl];exact hj'_tg⟩
  obtain ⟨v,hv,hxv⟩:=(osV hcl2 hv2.1 htop htGl x_pq wl2 hmem).mp hpqw;have hv_tl: v∈topLeaves d2 (insert p A):=(osS hv2.1 htop htGl wl2).2.1 hv
  by_cases hvp: v=p.val
  ·have h1: vl C2.gates x_p wl2=true :=
    (osV hcl2 hv2.1 htop htGl x_p wl2 hmem).mpr
     ⟨p.val,hvp ▸ hv,by rw[vli C2.gates x_p p.val p.isLt];simp[x_p]⟩
   rw[hpw] at h1;cases h1
  ·
   simp only[topLeaves,mU,mI,mF] at hv_tl
   rcases hv_tl with ⟨a,ha,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
   ·rw[vli C2.gates x_pq a.val a.isLt] at hxv
    have hap: a≠p:=fun e => hvp (congrArg Fin.val e)
    have haq: a≠q:=by
     rcases mN.mp ha with rfl|haA
     ·exact absurd rfl hap
     ·exact fun e => hqnA (e ▸ haA)
    simp[x_pq,hap,haq] at hxv
   ·obtain ⟨jb,hjb,hbw,hrb_s,_,_⟩:=(hv2.2.2.2.2.2.1 s hs).1
    have hnt: ∀ k' < C2.gates.length,d2.bw s=n + k' → (d2.role k').1≠Kind.top:=by
     intro k' _ ek;have: k' = jb := (by omega);rw[this,hrb_s];intro hc;cases hc
    have h1:=nnti hv2 hcl2 p hp_iso x_pq false (d2.bw s) (by omega) (by omega) hnt
    have hupd: Function.update x_pq p false=fun v => decide (v=q):=by
     funext i;by_cases hip: i=p
     ·subst hip;simp[hpq]
     ·rw[fupn hip];simp[x_pq,hip]
    rw[←h1,hupd,nbs hv2 hcl2 q (d2.bw s) (by omega) s hs rfl] at hxv;cases hxv
 have hw2p: wl2≠p.val:=fun e => by
  rw[e,vli C2.gates x_p p.val p.isLt] at hpw;simp[x_p] at hpw
 let x_q: Fin n→Bool:=fun v => decide (v=q)
 have hqw2: vl C2.gates x_q wl2=true:=by
  have h1:=nnti hv2 hcl2 p hp_iso x_pq false wl2 hwl2_lt hw2p hw2t
  have hupd: Function.update x_pq p false=x_q:=by
   funext i;by_cases hip: i=p
   ·subst hip;simp[x_q,hpq]
   ·rw[fupn hip];simp[x_pq,x_q,hip]
  rw[hupd] at h1;rw[h1,hpqw]
 have hw2c: wl2=q.val ∨
   (q∈d2.cover∧IsCentred n C2 d2 wl2 ∧
    ∃ jz < C2.gates.length,wl2=n+jz∧d2.role jz=(Kind.z,q.val)):=by
  by_cases hlt: wl2 < n
  ·left;rw[vli C2.gates x_q wl2 hlt] at hqw2;simp only[x_q,dTe] at hqw2;exact congrArg Fin.val hqw2
  ·set j:=wl2 - n
   have hjeq: wl2=n+j:=by omega
   have hj: j < C2.gates.length:=by omega
   rcases hv2.2.2.2.2.1 j hj with htop_j|⟨t,ht,hrt2,hrb_t⟩
   ·exact absurd htop_j (hw2t j hj hjeq)
   ·cases hkr: (d2.role j).1 with
    | top => exact absurd hkr (hw2t j hj hjeq)
    | b =>
     exfalso
     have hbw:=hrb_t hkr;have hf:=nbs hv2 hcl2 q (n+j) (by omega) t ht hbw.symm;rw[hjeq,hf] at hqw2;cases hqw2
    | z =>
     have hjZ: j∈gatesOf d2 C2 Kind.z t.val :=
      mF.mpr ⟨mR.mpr hj,Prod.ext hkr hrt2⟩
     have hZt:=(hv2.2.2.2.2.2.1 t ht).2.1
     have hZlt: ∀ k∈gatesOf d2 C2 Kind.z t.val,k < C2.gates.length:=fun k hk =>
      mR.mp (mF.mp hk).1
     have hmem: n+j∈zLeaves d2 t∨(n ≤ n+j∧(n+j) - n∈gatesOf d2 C2 Kind.z t.val) :=
      Or.inr ⟨by omega,by simpa using hjZ⟩
     obtain ⟨zL,hzL,hxzL⟩:=(osV hcl2 hv2.1 hZt hZlt x_q (n+j) hmem).mp (hjeq ▸ hqw2);have hzL' := (osS hv2.1 hZt hZlt (n+j)).2.1 hzL;simp only[zLeaves,mN,mI,mF] at hzL'
     rcases hzL' with rfl|⟨s,⟨hs,_⟩,rfl⟩
     ·rw[vli C2.gates x_q t.val t.isLt] at hxzL;simp only[x_q,dTe] at hxzL;have htq: t=q:=hxzL;subst htq
      have hcen_of_leaf: ∀ w: ℕ,(w∈zLeaves d2 t∨(n ≤ w∧w - n∈gatesOf d2 C2 Kind.z t.val)) →
        t.val∈osL n C2 (gatesOf d2 C2 Kind.z t.val) (zLeaves d2 t) w →
        IsCentred n C2 d2 w:=by
       intro w
       induction w using Nat.strong_induction_on with
       | ind w ih =>
        intro hw htl
        rcases hw with hL|hG
        ·rw[osLl hZt hL,mS] at htl;rw[←htl,cfi C2 d2 t];exact ht
        ·set k:=w - n;have hk: k∈gatesOf d2 C2 Kind.z t.val:=hG.2;have hklt: k < C2.gates.length:=hZlt k hk;obtain ⟨_,hlen,hins⟩:=hZt.1 k hk;obtain ⟨a,b,hab⟩:=ll2.mp hlen;have hsub:=osGq hv2.1 hZt hk hklt hab;rw[show w=n+k by omega] at htl ⊢;rw[hsub.2,mU] at htl;rw[cfg C2 d2 hv2.1 k hklt]
         refine ⟨by rw[(mF.mp hk).2],?_⟩
         rcases htl with ha|hb
         ·exact ⟨a,by rw[hab];simp,ih a (by have := hv2.1 k hklt a (by rw[hab];simp);omega) (hins a (by rw[hab];simp)) ha⟩
         ·exact ⟨b,by rw[hab];simp,ih b (by have := hv2.1 k hklt b (by rw[hab];simp);omega) (hins b (by rw[hab];simp)) hb⟩
      right;exact ⟨ht,hjeq ▸ hcen_of_leaf (n+j) hmem hzL,j,hj,hjeq,Prod.ext hkr hrt2⟩
     ·obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 s hs).1;rw[nbs hv2 hcl2 q (d2.bw s) (by omega) s hs rfl] at hxzL;cases hxzL
    | o =>
     exfalso
     have hjO: j∈gatesOf d2 C2 Kind.o t.val :=
      mF.mpr ⟨mR.mpr hj,Prod.ext hkr hrt2⟩
     have hOt:=(hv2.2.2.2.2.2.1 t ht).2.2.1
     have hOlt: ∀ k∈gatesOf d2 C2 Kind.o t.val,k < C2.gates.length:=fun k hk =>
      mR.mp (mF.mp hk).1
     have hcard:=osC2 hv2.1 hOt hOlt hjO;obtain ⟨v1,hv1,v2,hv2_m,hv12⟩:=one_lt_card.mp (by omega: 1 < (osL n C2 (gatesOf d2 C2 Kind.o t.val) (oLeaves d2 t) (n+j)).card);have hsubO:=(osS hv2.1 hOt hOlt (n+j)).2.1;have hv1_o:=hsubO hv1;have hv2_o:=hsubO hv2_m;simp only[oLeaves,mI,mF,mV,true_and] at hv1_o hv2_o;obtain ⟨s1,hs1,hv1_eq⟩:=hv1_o;obtain ⟨s2,hs2,hv2_eq⟩:=hv2_o
     have hs12: s1≠s2:=fun e => hv12 (by rw[←hv1_eq,←hv2_eq,e])
     obtain ⟨s,hs_own,hs_ne_q,hs_mem⟩ : ∃ s,d2.owns t s=true∧s≠q ∧
       d2.lam t s∈osL n C2 (gatesOf d2 C2 Kind.o t.val) (oLeaves d2 t) (n+j):=by
      by_cases h1: s1=q
      ·exact ⟨s2,hs2,fun e => hs12 (h1.trans e.symm),hv2_eq ▸ hv2_m⟩
      ·exact ⟨s1,hs1,h1,hv1_eq ▸ hv1⟩
     have hs_adj:=(hK2 t s).mp (hv2.2.2.1.1 t s hs_own).1
     have hs_notA: s∉A:=fun h => hA s h t hs_adj.1.symm
     let x_ps: Fin n→Bool:=fun v => decide (v=p∨v=s)
     have hwl_true: vl C2.gates x_ps wl2=true:=by
      rw[hjeq];apply (osV hcl2 hv2.1 hOt hOlt x_ps (n+j) (Or.inr ⟨by omega,by simpa using hjO⟩)).mpr
      refine ⟨d2.lam t s,hs_mem,?_⟩
      have hlam:=(hv2.2.2.2.2.2.1 t ht).2.2.2 s hs_own;unfold LamOK at hlam;split_ifs at hlam with hsc
      ·exact ncx hv2 s hsc x_ps (by simp[x_ps]) (d2.lam t s) hlam.1
        (by
          rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
          ·exact Or.inl h
          ·exact Or.inr ⟨jz,hjz,h1,h2⟩)
      ·rw[hlam,vli C2.gates x_ps s.val s.isLt];simp[x_ps]
     have hu2_true: vl C2.gates x_ps u2=true :=
      (osV hcl2 hv2.1 htop htGl x_ps u2 hu2_mem).mpr
       ⟨p.val,hp_in_Lu,by rw[vli C2.gates x_ps p.val p.isLt];simp[x_ps]⟩
     have hr_true: vl C.gates x_ps (n+r)=true:=by rw[hvl_r,hwl_true,hu2_true];simp
     have hC_true: vl C.gates x_ps C.output=true:=(hCoi x_ps).mpr (Or.inl hr_true);rw[hval_C] at hC_true;simp only[graphFun,boT,dTe,x_ps] at hC_true
     rcases hC_true with ⟨a,ha,hap|has⟩ | ⟨a,b,hab,hap|has,hbp|hbs⟩
     ·exact hpnA (hap ▸ ha)
     ·exact hs_notA (has ▸ ha)
     ·exact hab.ne (hap.trans hbp.symm)
     ·rcases (hp s).mp (hap ▸ hbs ▸ hab) with h1|h2
      ·exact hs_adj.2.2.2.1 h1
      ·exact hs_ne_q h2
     ·rcases (hp s).mp (has ▸ hbp ▸ hab).symm with h1|h2
      ·exact hs_adj.2.2.2.1 h1
      ·exact hs_ne_q h2
     ·exact hab.ne (has.trans hbs.symm)
 have hLmc: ∀ v∈Lu,v=p.val ∨
   (q∈d2.cover∧d2.tie q=none∧v=d2.bw q∧wl2=d2.zroot q) ∨
   (q∉d2.cover ∧ ∃ s∈d2.cover,d2.tie s=none∧v=d2.bw s ∧ ∀ r',d2.owns s r' = true → r' = q):=by
  intro v hv
  by_cases hvp: v=p.val
  ·exact Or.inl hvp
  ·have hv_tl:=hLu_sub hv;simp only[topLeaves,mU,mI,mF] at hv_tl
   rcases hv_tl with ⟨a,ha,rfl⟩ | ⟨s,⟨hs,hs_free⟩,rfl⟩
   ·exfalso
    have haA: a∈A:=by
     rcases mN.mp ha with rfl|h
     ·exact absurd rfl hvp
     ·exact h
    let x_a: Fin n→Bool:=fun i => decide (i=a)
    have hC_t: vl C.gates x_a C.output=true:=by rw[hval_C];simp[graphFun,x_a,haA]
    rcases (hCoi x_a).mp hC_t with hr_t|⟨w',hw',hxw'⟩
    ·rw[hvl_r] at hr_t
     have hla: l≠a:=fun e => hlnA (e ▸ haA)
     have hxl: x_a l=false:=by simp[x_a,hla]
     rw[hxl] at hr_t;simp only[Bool.false_or,baT] at hr_t
     rcases hw2c with hq_eq|⟨hqc,_,jz,hjz,hjeq,hrz⟩
     ·rw[hq_eq,vli C2.gates x_a q.val q.isLt] at hr_t
      have hqa: q≠a:=fun e => hqnA (e ▸ haA)
      simp[x_a,hqa] at hr_t
     ·have hZq:=(hv2.2.2.2.2.2.1 q hqc).2.1
      have hZlt: ∀ k∈gatesOf d2 C2 Kind.z q.val,k < C2.gates.length:=fun k hk =>
       mR.mp (mF.mp hk).1
      have hjZ: jz∈gatesOf d2 C2 Kind.z q.val:=mF.mpr ⟨mR.mpr hjz,hrz⟩
      obtain ⟨zL,hzL,hxzL⟩:=(osV hcl2 hv2.1 hZq hZlt x_a (n+jz)
       (Or.inr ⟨by omega,by simpa using hjZ⟩)).mp (hjeq ▸ hr_t.1)
      have hzL' := (osS hv2.1 hZq hZlt (n+jz)).2.1 hzL;simp only[zLeaves,mN,mI,mF] at hzL'
      rcases hzL' with rfl|⟨u',⟨hu',_⟩,rfl⟩
      ·rw[vli C2.gates x_a q.val q.isLt] at hxzL
       have hqa: q≠a:=fun e => hqnA (e ▸ haA)
       simp[x_a,hqa] at hxzL
      ·obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 u' hu').1;rw[nbs hv2 hcl2 a (d2.bw u') (by omega) u' hu' rfl] at hxzL;cases hxzL
    ·obtain ⟨hw'_tl,hw'_not⟩:=mem_sdiff.mp hw';simp only[topLeaves,mU,mI,mF] at hw'_tl
     rcases hw'_tl with ⟨a',_,rfl⟩ | ⟨s',⟨hs',_⟩,rfl⟩
     ·rw[vli C2.gates x_a a'.val a'.isLt] at hxw';simp only[x_a,dTe] at hxw';exact hw'_not (by rw[congrArg Fin.val hxw'];exact hv)
     ·obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 s' hs').1;rw[nbs hv2 hcl2 a (d2.bw s') (by omega) s' hs' rfl] at hxw';cases hxw'
   ·by_cases hsq: s=q
    ·subst hsq
     right;left;refine ⟨hs,hs_free,rfl,?_⟩
     by_contra hne_zr
     have hZq:=(hv2.2.2.2.2.2.1 s hs).2.1
     have hZlt: ∀ k∈gatesOf d2 C2 Kind.z s.val,k < C2.gates.length:=fun k hk =>
      mR.mp (mF.mp hk).1
     have hwl_memZ: wl2∈zLeaves d2 s∨(n ≤ wl2∧wl2 - n∈gatesOf d2 C2 Kind.z s.val):=by
      rcases hw2c with h|⟨_,_,jz,hjz,h1,h2⟩
      ·left;rw[h];exact mNs _ _
      ·right;exact ⟨by omega,by rw[h1,ascl];exact mF.mpr ⟨mR.mpr hjz,h2⟩⟩
     have hsub_lt: (osL n C2 (gatesOf d2 C2 Kind.z s.val) (zLeaves d2 s) wl2).card < (zLeaves d2 s).card:=by
      have h1:=tree_card n C2 _ _ wl2 (osT hv2.1 hZq hZlt wl2 hwl_memZ);have h2:=tree_card n C2 _ _ (d2.zroot s) hZq;have hGsub:=(osS hv2.1 hZq hZlt wl2).1
      have hGne: osG n C2 (gatesOf d2 C2 Kind.z s.val) wl2≠gatesOf d2 C2 Kind.z s.val:=by
       intro hEq
       have hGe: gatesOf d2 C2 Kind.z s.val ≠ ∅ := by
        intro hE;have hrt:=hZq.2.2.2;simp only[hE,↓reduceIte] at hrt
        have hwl_L: wl2∈zLeaves d2 s:=by rcases hwl_memZ with h|⟨_,h⟩;exact h;rw[hE] at h;cases h
        rw[hrt,mS] at hwl_L;exact hne_zr hwl_L
       have hrt:=hZq.2.2.2;simp only[hGe,↓reduceIte] at hrt;obtain ⟨g0,hg0,hρ⟩:=hrt;have hle:=(osS hv2.1 hZq hZlt wl2).2.2 g0 (hEq.symm ▸ hg0)
       have hle2:=orTree_lt_root hcl2 hZq hZlt _ wl2 rfl (by
        rcases hwl_memZ with h|⟨h1,h2⟩;exact Or.inl h;exact Or.inr ⟨wl2 - n,h2,by omega⟩)
       omega
      have hltG:=card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hGsub,hGne⟩);omega
     have hdiff_ne: (zLeaves d2 s \ osL n C2 (gatesOf d2 C2 Kind.z s.val) (zLeaves d2 s) wl2).Nonempty:=by
      by_contra he;rw[not_nonempty_iff_eq_empty,sdiff_eq_empty_iff_subset] at he
      have:=card_le_card he;omega
     obtain ⟨zL,hzL_diff⟩:=hdiff_ne;obtain ⟨hzL_in,hzL_not⟩:=mem_sdiff.mp hzL_diff
     simp only[zLeaves,mN,mI,mF] at hzL_in
     rcases hzL_in with rfl|⟨t0,⟨ht0,htie0⟩,rfl⟩
     ·
      obtain ⟨z0,hz0,hxz0⟩:=(osV hcl2 hv2.1 hZq hZlt x_q wl2 hwl_memZ).mp hqw2;have hz0' := (osS hv2.1 hZq hZlt wl2).2.1 hz0;simp only[zLeaves,mN,mI,mF] at hz0'
      rcases hz0' with rfl|⟨u',⟨hu',_⟩,rfl⟩
      ·exact hzL_not hz0
      ·obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 u' hu').1;rw[nbs hv2 hcl2 s (d2.bw u') (by omega) u' hu' rfl] at hxz0;cases hxz0
     ·
      obtain ⟨v0,hown0,hv0_out⟩:=coo hv2 t0 ht0
      let x_tv: Fin n→Bool:=fun i => decide (i=t0∨i=v0)
      have ht0_ne_s: t0≠s:=(hv2.2.2.1.1 s t0 (hv2.2.2.2.1 t0 s htie0).2).1.ne'
      have hv0_ne_s: v0≠s:=fun e => hv0_out (e ▸ hs)
      have ht0_adj:=(hK2 t0 v0).mp (hv2.2.2.1.1 t0 v0 hown0).1
      have hC_t: vl C.gates x_tv C.output=true:=by
       rw[hval_C];simp only[graphFun,boT,dTe]
       right;exact ⟨t0,v0,ht0_adj.1,by simp[x_tv],by simp[x_tv]⟩
      rcases (hCoi x_tv).mp hC_t with hr_t|⟨w',hw',hxw'⟩
      ·rw[hvl_r] at hr_t
       have hxl: x_tv l=false:=by simp[x_tv,ht0_adj.2.1.symm,ht0_adj.2.2.2.1.symm]
       rw[hxl] at hr_t;simp only[Bool.false_or,baT] at hr_t;obtain ⟨z0,hz0,hxz0⟩:=(osV hcl2 hv2.1 hZq hZlt x_tv wl2 hwl_memZ).mp hr_t.1;have hz0' := (osS hv2.1 hZq hZlt wl2).2.1 hz0;simp only[zLeaves,mN,mI,mF] at hz0'
       rcases hz0' with rfl|⟨u',⟨hu',htu'⟩,rfl⟩
       ·rw[vli C2.gates x_tv s.val s.isLt] at hxz0;simp[x_tv,ht0_ne_s.symm,hv0_ne_s.symm] at hxz0
       ·have hu'_ne_t0: u' ≠ t0:=fun e => hzL_not (e ▸ hz0)
        have hu'_ne_s: u' ≠ s:=fun e => by rw[e,hs_free] at htu';cases htu'
        obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 u' hu').1;rw[nbpt hv2 hcl2 ht0 hs hown0 hv0_out htie0 hs_free (d2.bw u') (by omega) u' hu' hu'_ne_t0 hu'_ne_s rfl] at hxz0
        cases hxz0
      ·obtain ⟨hw'_tl,hw'_not⟩:=mem_sdiff.mp hw';simp only[topLeaves,mU,mI,mF] at hw'_tl
       rcases hw'_tl with ⟨a,ha,rfl⟩ | ⟨u',⟨hu',hu'_free⟩,rfl⟩
       ·rw[vli C2.gates x_tv a.val a.isLt] at hxw';simp only[x_tv,dTe] at hxw'
        rcases hxw' with e|e
        ·have ea: a=t0:=by simpa using e
         exact hcnA t0 ht0 (ea ▸ ha)
        ·have ea: a=v0:=by simpa using e
         rcases mN.mp (ea ▸ ha) with hpv|haA
         ·exact ht0_adj.2.2.2.2 hpv
         ·exact hA v0 haA t0 ht0_adj.1.symm
       ·have hu'_ne_s: u' ≠ s:=fun e => hw'_not (e ▸ hv)
        have hu'_ne_t0: u' ≠ t0:=fun e => by rw[e,htie0] at hu'_free;cases hu'_free
        obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 u' hu').1;rw[nbpt hv2 hcl2 ht0 hs hown0 hv0_out htie0 hs_free (d2.bw u') (by omega) u' hu' hu'_ne_t0 hu'_ne_s rfl] at hxw'
        cases hxw'
    ·
     have hs_only_q: ∀ r' : Fin n,d2.owns s r' = true → r' = q:=by
      intro r' hown'
      by_contra hr'q
      let x_sr: Fin n→Bool:=fun i => decide (i=s∨i = r')
      have hsr_adj:=(hK2 s r').mp (hv2.2.2.1.1 s r' hown').1
      have hC_t: vl C.gates x_sr C.output=true:=by
       rw[hval_C];simp only[graphFun,boT,dTe]
       right;exact ⟨s,r',hsr_adj.1,by simp[x_sr],by simp[x_sr]⟩
      rcases (hCoi x_sr).mp hC_t with hr_t|⟨w',hw',hxw'⟩
      ·rw[hvl_r] at hr_t
       have hxl: x_sr l=false:=by simp[x_sr,hsr_adj.2.1.symm,hsr_adj.2.2.2.1.symm]
       rw[hxl] at hr_t;simp only[Bool.false_or,baT] at hr_t
       rcases hw2c with hq_eq|⟨hqc,_,jz,hjz,hjeq,hrz⟩
       ·rw[hq_eq,vli C2.gates x_sr q.val q.isLt] at hr_t
        simp[x_sr,show q≠s from fun e => hsq e.symm,show q ≠ r' from fun e => hr'q e.symm] at hr_t
       ·have hZq:=(hv2.2.2.2.2.2.1 q hqc).2.1
        have hZlt: ∀ k∈gatesOf d2 C2 Kind.z q.val,k < C2.gates.length:=fun k hk =>
         mR.mp (mF.mp hk).1
        have hjZ: jz∈gatesOf d2 C2 Kind.z q.val:=mF.mpr ⟨mR.mpr hjz,hrz⟩
        obtain ⟨z0,hz0,hxz0⟩:=(osV hcl2 hv2.1 hZq hZlt x_sr (n+jz)
         (Or.inr ⟨by omega,by simpa using hjZ⟩)).mp (hjeq ▸ hr_t.1)
        have hz0' := (osS hv2.1 hZq hZlt (n+jz)).2.1 hz0;simp only[zLeaves,mN,mI,mF] at hz0'
        rcases hz0' with rfl|⟨u',⟨hu',htu'⟩,rfl⟩
        ·rw[vli C2.gates x_sr q.val q.isLt] at hxz0;simp[x_sr,show q≠s from fun e => hsq e.symm,show q ≠ r' from fun e => hr'q e.symm] at hxz0
        ·have hu'_ne_s: u' ≠ s:=fun e => by rw[e,hs_free] at htu';cases htu'
         obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 u' hu').1;rw[nbpo hv2 hcl2 hown' hs_free (d2.bw u') (by omega) u' hu' hu'_ne_s rfl] at hxz0
         cases hxz0
      ·obtain ⟨hw'_tl,hw'_not⟩:=mem_sdiff.mp hw';simp only[topLeaves,mU,mI,mF] at hw'_tl
       rcases hw'_tl with ⟨a,ha,rfl⟩ | ⟨u',⟨hu',_⟩,rfl⟩
       ·rw[vli C2.gates x_sr a.val a.isLt] at hxw';simp only[x_sr,dTe] at hxw'
        rcases hxw' with e|e
        ·have ea: a=s:=by simpa using e
         exact hcnA s hs (ea ▸ ha)
        ·have ea: a = r' := by simpa using e
         rcases mN.mp (ea ▸ ha) with hpr|haA
         ·exact hsr_adj.2.2.2.2 hpr
         ·exact hA r' haA s hsr_adj.1.symm
       ·have hu'_ne_s: u' ≠ s:=fun e => hw'_not (e ▸ hv)
        obtain ⟨jb,hjb,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 u' hu').1;rw[nbpo hv2 hcl2 hown' hs_free (d2.bw u') (by omega) u' hu' hu'_ne_s rfl] at hxw'
        cases hxw'
     obtain ⟨v0,hown0,hv0_out⟩:=coo hv2 s hs;have hv0q: v0=q:=hs_only_q v0 hown0
     right;right;exact ⟨hv0q ▸ hv0_out,s,hs,hs_free,rfl,hs_only_q⟩
 by_cases hLu_one: Lu={p.val}
 ·
  have hu2_eq_p: u2=p.val:=by
   rcases hu2_top with h|⟨hge,htg⟩
   ·exact h
   ·have hcard:=osC2 hv2.1 htop htGl htg;rw[show n+(u2 - n)=u2 by omega] at hcard;change 2 ≤ Lu.card at hcard;rw[hLu_one] at hcard;simp at hcard
  let roleB: ℕ → Kind × ℕ := fun j =>
   if j=jl then (Kind.o,p.val)
   else if j=r then (Kind.b,p.val)
   else d2.role (rd 0 jl 0 (rd 0 r 0 j))
  have hrl: ∀ j' : ℕ,roleB (li2 jl r j')=d2.role j' := by
   intro j';have h1:=li2nj jl r j' hjr;have h2:=li2nr jl r j';simp only[roleB,h1,h2,↓reduceIte]
   congr 1
   have hlift_eq: li2 jl r j' = lw2 0 jl r j' := by unfold li2 lw2 li1 lw1;simp
   rw[hlift_eq];exact rd2l
  let d: NCCData n:={
   cover := insert p d2.cover
   owns := fun a b => if a=p∧(b=l∨b=q) then true else d2.owns a b
   tie := d2.tie
   role := roleB
   bw := fun t => if t=p then n+r else lw2 n jl r (d2.bw t)
   zroot := fun t => if t=p then p.val else lw2 n jl r (d2.zroot t)
   oroot := fun t => if t=p then n+jl else lw2 n jl r (d2.oroot t)
   lam := fun t v => if t=p then (if v=l then l.val else wl) else lw2 n jl r (d2.lam t v)
  }
  have hgn: ∀ (k: Kind) (v: ℕ),(k,v)≠(Kind.o,p.val)→(k,v)≠(Kind.b,p.val) →
    gatesOf d C k v=(gatesOf d2 C2 k v).image (li2 jl r):=by
   intro k v h1 h2
   ext j;simp only[gatesOf,d,mF,mR,mI]
   constructor
   ·rintro ⟨hj,hrj⟩
    have hjl_ne: j≠jl:=fun e => h1 (by rw[←hrj,e];simp[roleB])
    have hr_ne: j≠r:=fun e => h2 (by rw[←hrj,e];simp[roleB,Nat.ne_of_gt hjr])
    obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hjl_ne hr_ne;exact ⟨j',⟨by omega,by rw[←hrl j'];exact hrj⟩,rfl⟩
   ·rintro ⟨j',⟨hj',hrj'⟩,rfl⟩
    exact ⟨(li2lt hjr hr (by omega): _ < C.gates.length),by rw[hrl,hrj']⟩
  refine ⟨d,hrb,?_,?_,?_,?_,?_,?_⟩
  ·
   refine ⟨?_,fun T hT => by have := htK2 T hT;simp only[d,card_insert_of_notMem hpnc];omega⟩
   intro a b hab
   by_cases hap: a=p
   ·left;simp[d,hap]
   ·by_cases hbp: b=p
    ·right;simp[d,hbp]
    ·have hal: a≠l:=fun e => hbp ((hl b).mp (e ▸ hab))
     have hbl: b≠l:=fun e => hap ((hl a).mp (e ▸ hab.symm))
     rcases hv2.2.1.1 ((hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩) with ha|hb
     ·left;exact mC.mpr (mNo (mC.mp ha))
     ·right;exact mC.mpr (mNo (mC.mp hb))
  ·
   refine ⟨?_,?_⟩
   ·intro a b hown;dsimp[d] at hown;split_ifs at hown with h
    ·exact ⟨by rw[h.1];exact (hp b).mpr h.2,by rw[h.1];exact mNs _ _⟩
    ·have h1:=hv2.2.2.1.1 a b hown;exact ⟨((hK2 a b).mp h1.1).1,mNo h1.2⟩
   ·intro a b hab
    by_cases hap: a=p
    ·rw[hap] at hab ⊢;have hbp: b≠p:=hab.ne';have hblq: b=l∨b=q:=(hp b).mp hab
     have hb_no: d2.owns b p=false:=by
      cases h: d2.owns b p
      ·rfl
      ·exfalso;exact hp_iso b (hv2.2.2.1.1 b p h).1.symm
     dsimp[d];simp[hblq,hbp,hb_no]
    ·by_cases hbp: b=p
     ·rw[hbp] at hab ⊢;have halq: a=l∨a=q:=(hp a).mp hab.symm
      have ha_no: d2.owns a p=false:=by
       cases h: d2.owns a p
       ·rfl
       ·exfalso;exact hp_iso a (hv2.2.2.1.1 a p h).1.symm
      dsimp[d];simp[halq,hap,ha_no]
     ·have hal: a≠l:=fun e => hbp ((hl b).mp (e ▸ hab))
      have hbl: b≠l:=fun e => hap ((hl a).mp (e ▸ hab.symm))
      dsimp[d];simp[hap,hbp,hv2.2.2.1.2 a b ((hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩)]
  ·
   intro s t hst;have h1:=hv2.2.2.2.1 s t hst
   refine ⟨mNo h1.1,?_⟩
   dsimp[d];split_ifs
   ·rfl
   ·exact h1.2
  ·
   intro j hj
   by_cases hje: j=jl
   ·subst hje;right;exact ⟨p,mNs _ _,by simp[d,roleB],fun h => by simp[d,roleB] at h⟩
   ·by_cases hre: j=r
    ·subst hre;right;exact ⟨p,mNs _ _,by simp[d,roleB,Nat.ne_of_gt hjr],fun _ => by simp[d]⟩
    ·obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre;have hr_eq: d.role (li2 jl r j')=d2.role j' := hrl j'
     rcases hv2.2.2.2.2.1 j' (by omega) with htop_j|⟨t,ht,e1,e2⟩
     ·exact Or.inl (by rw[hr_eq];exact htop_j)
     ·right;refine ⟨t,mNo ht,by rw[hr_eq];exact e1,fun hk => ?_⟩
      rw[hr_eq] at hk
      have htp: t≠p:=fun e => hpnc (e ▸ ht)
      dsimp[d];simp only[htp,↓reduceIte];rw[e2 hk,lw2g]
  ·
   intro t ht
   by_cases htp: t=p
   ·rw[htp]
    refine ⟨?_,?_,?_,?_⟩
    ·have hu_eq_p: u=p.val:=by rw[←hu_lw,hu2_eq_p,lw2i n jl r p.val p.isLt]
     refine ⟨r,hr,by simp[d],by simp[d,roleB,Nat.ne_of_gt hjr],hro0,?_⟩
     dsimp[d];simp only[↓reduceIte];rw[←hu_eq_p];exact hri0.symm
    ·have hG: gatesOf d C Kind.z p.val = ∅ := by
      rw[hgn Kind.z p.val (by simp) (by simp)]
      have hE: gatesOf d2 C2 Kind.z p.val = ∅ := by
       ext j';simp only[gatesOf,mF,mR,notMem_empty,iff_false,not_and]
       intro hj' hrj'
       rcases hv2.2.2.2.2.1 j' hj' with htop_j|⟨s,hs,e1,_⟩
       ·rw[hrj'] at htop_j;cases htop_j
       ·rw[hrj'] at e1;exact hpnc (Fin.ext e1.symm ▸ hs)
      simp[hE]
     have hL: zLeaves d p={p.val}:=by
      ext w;simp only[zLeaves,d,mN,mI,mF,mS,or_iff_left_iff_imp]
      rintro ⟨s,⟨_,hts⟩,_⟩
      exact absurd (hv2.2.2.1.1 p s (hv2.2.2.2.1 s p hts).2).1 (hp_iso s)
     rw[hG,hL];dsimp[d];simp only[↓reduceIte]
     refine ⟨by simp,fun w hw => by rw[mS.mp hw];simp[readsIn],by simp,by simp⟩
    ·have hG: gatesOf d C Kind.o p.val={jl}:=by
      ext j;simp only[gatesOf,d,mF,mR,mS]
      constructor
      ·rintro ⟨hj,hrj⟩
       by_contra hje
       have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleB,Nat.ne_of_gt hjr] at hrj
       obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre;rw[hrl] at hrj
       rcases hv2.2.2.2.2.1 j' (by omega) with htop_j|⟨s,hs,e1,_⟩
       ·rw[hrj] at htop_j;cases htop_j
       ·rw[hrj] at e1;exact hpnc (Fin.ext e1.symm ▸ hs)
      ·rintro rfl;exact ⟨by omega,by simp[roleB]⟩
     have hL: oLeaves d p={l.val,wl}:=by
      ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
       mN,mS]
      constructor
      ·rintro ⟨v,hown,rfl⟩
       split_ifs at hown with hv
       ·rcases hv with rfl|rfl
        ·left;simp
        ·right;simp[hql]
       ·exact absurd (hv2.2.2.1.1 p v hown).1 (hp_iso v)
      ·rintro (rfl|rfl)
       ·exact ⟨l,by simp,by simp⟩
       ·exact ⟨q,by simp,by simp[hql]⟩
     rw[hG,hL];dsimp[d];simp only[↓reduceIte]
     have hwl_ne_jl: wl≠n+jl:=by omega
     have hl_ne_jl: l.val≠n+jl:=by have:=l.isLt;omega
     refine ⟨?_,?_,?_,?_⟩
     ·intro j hj;rw[mS.mp hj]
      refine ⟨hjlo,by rcases hjli with h|h <;> simp[h],fun i hi => ?_⟩
      rcases hjli with h|h <;> rw[h] at hi <;> simp at hi <;> rcases hi with rfl|rfl <;> exact Or.inl (by simp)
     ·intro w hw;simp only[mN,mS] at hw
      rcases hw with rfl|rfl
      ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
       simp only[readsIn,sum_singleton,hl_ne_jl,↓reduceIte]
       rcases hjli with h|h <;> rw[h] <;> simp[hwne,hwne.symm]
      ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
       simp only[readsIn,sum_singleton,hwl_ne_jl,↓reduceIte]
       rcases hjli with h|h <;> rw[h] <;> simp[hwne,hwne.symm]
     ·intro j hj;rw[mS.mp hj];simp only[readsIn,sum_singleton,↓reduceIte,lcz]
      rcases hjli with h|h <;> rw[h] <;> simp[hl_ne_jl.symm,hwl_ne_jl.symm]
     ·simp
    ·intro v hown;dsimp[d] at hown
     have hvlq: v=l∨v=q:=by
      split_ifs at hown with h;exact h.2
      exact absurd (hv2.2.2.1.1 p v hown).1 (hp_iso v)
     rcases hvlq with hvl|hvq
     ·rw[hvl];unfold LamOK;dsimp[d];simp[hlp,hlnc]
     ·rw[hvq];unfold LamOK;dsimp[d];simp only[↓reduceIte,hql]
      by_cases hqc: q∈d2.cover
      ·have hqc' : q∈insert p d2.cover:=mNo hqc;simp only[hqc',↓reduceIte]
       have htie_q: d2.tie q≠some p:=fun e => hp_iso q (hv2.2.2.1.1 p q (hv2.2.2.2.1 q p e).2).1
       refine ⟨?_,?_,fun e => absurd e htie_q⟩
       ·rw[←hwl_lw]
        apply cf2 (d := d) C hcl hrb hjr hr hu hune hon0 hur hv2 d2.cover
         (Subset.refl _) (subset_insert p d2.cover)
         (fun j' hj' hrz => ⟨hnt0 j' (by omega) (by rw[hrz];intro hc;cases hc),by dsimp[d];rw[hrl,hrz]⟩)
         q hqc wl2
        ·rcases hw2c with hq|⟨_,hcen,_⟩
         ·rw[hq,cfi C2 d2 q];exact hqc
         ·exact hcen
        ·rcases hw2c with hq|⟨_,_,jz,hjz,h1,h2⟩
         ·exact Or.inl hq
         ·exact Or.inr ⟨jz,by omega,h1,h2⟩
       ·rcases hw2c with hq|⟨_,_,jz,hjz,h1,h2⟩
        ·left;rw[←hwl_lw,hq,lw2i n jl r q.val q.isLt]
        ·right;refine ⟨li2 jl r jz,(li2lt hjr hr (by omega): _ < C.gates.length),
          by rw[←hwl_lw,h1,lw2g],by rw[hrl,h2]⟩
      ·have hqc' : q∉insert p d2.cover:=by simp[hpq.symm,hqc]
       simp only[hqc',↓reduceIte]
       rcases hw2c with hq|⟨h1,_⟩
       ·rw[←hwl_lw,hq,lw2i n jl r q.val q.isLt]
       ·exact absurd h1 hqc
   ·have ht2: t∈d2.cover:=by rcases mN.mp ht with rfl|h;exact absurd rfl htp;exact h
    refine ⟨?_,?_,?_,?_⟩
    ·obtain ⟨jb,hjb,hbw,hrb_t,hop,hin⟩:=(hv2.2.2.2.2.2.1 t ht2).1;have hno:=hnt0 jb hjb (by rw[hrb_t];intro hc;cases hc);have hlif:=r2l C hcl hrb hjr hr hu jb (by omega);have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jb (by omega) hno
     refine ⟨li2 jl r jb,(li2lt hjr hr (by omega): _ < C.gates.length),by dsimp[d];simp[htp,hbw,lw2g],
      by dsimp[d];rw[hrl,hrb_t],by rw[←hlif.1,hop],?_⟩
     rw[hinp];rcases hin with h|h <;> rw[h] <;> simp[d,htp]
    ·have hG: gatesOf d C Kind.z t.val=(gatesOf d2 C2 Kind.z t.val).image (li2 jl r) :=
      hgn Kind.z t.val (by simp) (by simp)
     have hL: zLeaves d t=(zLeaves d2 t).image (lw2 n jl r):=by
      ext w;simp only[zLeaves,d,mN,mI,mF]
      constructor
      ·rintro (rfl|⟨s,⟨hs,hst⟩,rfl⟩)
       ·exact ⟨t.val,Or.inl rfl,lw2i n jl r t.val t.isLt⟩
       ·have hs2: s∈d2.cover:=(hv2.2.2.2.1 s t hst).1
        have hsp: s≠p:=fun e => hpnc (e ▸ hs2)
        simp only[hsp,↓reduceIte];exact ⟨d2.bw s,Or.inr ⟨s,⟨hs2,hst⟩,rfl⟩,rfl⟩
      ·rintro ⟨_,rfl|⟨s,⟨hs,hst⟩,rfl⟩,rfl⟩
       ·exact Or.inl (lw2i n jl r t.val t.isLt)
       ·have hsp: s≠p:=fun e => hpnc (e ▸ hs)
        exact Or.inr ⟨s,⟨Or.inr hs,hst⟩,by simp[hsp]⟩
     rw[hG,hL];dsimp[d];simp only[htp,↓reduceIte]
     exact ot2u C hcl hrb hjr hr hu hune hon0 hur (hv2.2.2.2.2.2.1 t ht2).2.1
      (fun j' hj' => by have := mR.mp (mF.mp hj').1;omega)
      (fun j' hj' => hnt0 j' (mR.mp (mF.mp hj').1)
       (by rw[(mF.mp hj').2];intro hc;cases hc))
    ·have hG: gatesOf d C Kind.o t.val=(gatesOf d2 C2 Kind.o t.val).image (li2 jl r) :=
      hgn Kind.o t.val (fun h => htp (Fin.ext (pei.mp h).2)) (by simp)
     have hL: oLeaves d t=(oLeaves d2 t).image (lw2 n jl r):=by
      ext w;simp only[oLeaves,d,mI,mF,mV,true_and,htp,false_and,↓reduceIte]
      constructor
      ·rintro ⟨v,hown,rfl⟩;exact ⟨d2.lam t v,⟨v,hown,rfl⟩,rfl⟩
      ·rintro ⟨_,⟨v,hown,rfl⟩,rfl⟩;exact ⟨v,hown,rfl⟩
     rw[hG,hL];dsimp[d];simp only[htp,↓reduceIte]
     exact ot2u C hcl hrb hjr hr hu hune hon0 hur (hv2.2.2.2.2.2.1 t ht2).2.2.1
      (fun j' hj' => by have := mR.mp (mF.mp hj').1;omega)
      (fun j' hj' => hnt0 j' (mR.mp (mF.mp hj').1)
       (by rw[(mF.mp hj').2];intro hc;cases hc))
    ·intro v hown;dsimp[d] at hown;simp only[htp,false_and,↓reduceIte] at hown
     have hvp: v≠p:=fun e => hp_iso t (e ▸ (hv2.2.2.1.1 t v hown).1).symm
     have hlam:=(hv2.2.2.2.2.2.1 t ht2).2.2.2 v hown;unfold LamOK at hlam ⊢;dsimp[d];simp only[htp,↓reduceIte]
     by_cases hvc: v∈d2.cover
     ·have hvc' : v∈insert p d2.cover:=mNo hvc;simp only[hvc,hvc',↓reduceIte] at hlam ⊢
      refine ⟨?_,?_,?_⟩
      ·exact cf2 (d := d) C hcl hrb hjr hr hu hune hon0 hur hv2 d2.cover
        (Subset.refl _) (subset_insert p d2.cover)
        (fun j' hj' hrz => ⟨hnt0 j' (by omega) (by rw[hrz];intro hc;cases hc),by dsimp[d];rw[hrl,hrz]⟩)
        v hvc (d2.lam t v) hlam.1 (by
         rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
         ·exact Or.inl h
         ·exact Or.inr ⟨jz,by omega,h1,h2⟩)
      ·rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
       ·exact Or.inl (by rw[h,lw2i n jl r v.val v.isLt])
       ·exact Or.inr ⟨li2 jl r jz,(li2lt hjr hr (by omega): _ < C.gates.length),
         by rw[h1,lw2g],by rw[hrl,h2]⟩
      ·intro htie;simp only[hvp,↓reduceIte];rw[hlam.2.2 htie]
     ·have hvc' : v∉insert p d2.cover:=by simp[hvp,hvc]
      simp only[hvc,hvc',↓reduceIte] at hlam ⊢;rw[hlam,lw2i n jl r v.val v.isLt]
  ·have hG: topGates d C=(topGates d2 C2).image (li2 jl r):=by
    ext j;simp only[topGates,d,mF,mR,mI]
    constructor
    ·rintro ⟨hj,hrj⟩
     have hje: j≠jl:=fun e => by rw[e] at hrj;simp[roleB] at hrj
     have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleB,Nat.ne_of_gt hjr] at hrj
     obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre;exact ⟨j',⟨by omega,by rw[←hrl j'];exact hrj⟩,rfl⟩
    ·rintro ⟨j',⟨hj',hrj'⟩,rfl⟩
     exact ⟨(li2lt hjr hr (by omega): _ < C.gates.length),by rw[hrl,hrj']⟩
   have hL: topLeaves d A=insert (n+r) (((topLeaves d2 (insert p A)).erase p.val).image (lw2 n jl r)):=by
    ext w;simp only[topLeaves,d,mU,mI,mF,
     mN,mE]
    constructor
    ·rintro (⟨a,ha,rfl⟩ | ⟨s,⟨hs,hst⟩,rfl⟩)
     ·right;refine ⟨a.val,⟨fun e => hpnA (Fin.ext e ▸ ha),Or.inl ⟨a,Or.inr ha,rfl⟩⟩,lw2i n jl r a.val a.isLt⟩
     ·by_cases hsp: s=p
      ·left;simp[hsp]
      ·right;simp only[hsp,↓reduceIte]
       have hs2: s∈d2.cover:=by rcases hs with rfl|h;exact absurd rfl hsp;exact h
       obtain ⟨jb,_,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 s hs2).1;exact ⟨d2.bw s,⟨by omega,Or.inr ⟨s,⟨hs2,hst⟩,rfl⟩⟩,rfl⟩
    ·rintro (rfl|⟨w',⟨hw'ne,hw'tl⟩,rfl⟩)
     ·right;exact ⟨p,⟨Or.inl rfl,by
       cases h: d2.tie p with
       | none => rfl
       | some t => exfalso;exact hpnc (hv2.2.2.2.1 p t h).1⟩,by simp⟩
     ·rcases hw'tl with ⟨a,rfl|ha,rfl⟩ | ⟨s,⟨hs,hst⟩,rfl⟩
      ·exact absurd rfl hw'ne
      ·left;exact ⟨a,ha,(lw2i n jl r a.val a.isLt).symm⟩
      ·right;have hsp: s≠p := fun e => hpnc (e ▸ hs)
       exact ⟨s,⟨Or.inr hs,hst⟩,by simp[hsp]⟩
   have hout_eq: C.output=if p.val=C2.output then n+r else lw2 n jl r C2.output:=by
    rcases hor0 with ⟨he,hr_out⟩ | ⟨hne,hne_out,_⟩
    ·rw[hu2_eq_p] at he;simp[he,hr_out]
    ·rw[hu2_eq_p] at hne;rw[if_neg hne,lw2r hjr hon0 hne_out]
   rw[hG,hL,hout_eq]
   exact ot2r C hcl hrb hjr hr hu hune hon0 hur htop
    (fun j' hj' => by have := htGl j' hj';omega)
    (Finset.mem_union_left _ (mI.mpr ⟨p,mNs _ _,rfl⟩))
    hu2_eq_p
    (fun j' hj' hmem => hu2_eq_p ▸ hnrt j' hj' hmem)
    (fun j' hj' hmem => by
     rcases hor0 with ⟨he,_⟩ | ⟨_,_,hread⟩
     ·have hr0:=(htop.2.1 p.val (Finset.mem_union_left _ (mI.mpr ⟨p,mNs _ _,rfl⟩))).2;rw[if_pos (hu2_eq_p.symm.trans he)] at hr0;have h1: 1 ≤ (gateAt C2 j').inputs.count p.val:=lcpi.mpr hmem
      have hle: (gateAt C2 j').inputs.count p.val ≤ readsIn C2 (topGates d2 C2) p.val :=
       single_le_sum (f := fun m => (gateAt C2 m).inputs.count p.val) (fun _ _ => Nat.zero_le _) hj'
      omega
     ·exact hread j' hj' (hu2_eq_p.symm ▸ hmem))
 ·
  have hdiff_ne: (Lu.erase p.val).Nonempty:=by
   by_contra he;rw[not_nonempty_iff_eq_empty] at he
   apply hLu_one;ext x;simp only[mS]
   constructor
   ·intro hx;by_contra hne;exact notMem_empty x (he ▸ mE.mpr ⟨hne,hx⟩)
   ·rintro rfl;exact hp_in_Lu
  obtain ⟨v0,hv0_er⟩:=hdiff_ne;obtain ⟨hv0_ne_p,hv0_Lu⟩:=mE.mp hv0_er
  have hLu_pair: Lu={p.val,v0}:=by
   ext v;simp only[mN,mS]
   constructor
   ·intro hv
    rcases hLmc v hv with rfl|⟨hqc,_,rfl,_⟩ | ⟨hqnc,s,hs,_,rfl,hs_only⟩
    ·exact Or.inl rfl
    ·rcases hLmc v0 hv0_Lu with h1|⟨_,_,rfl,_⟩ | ⟨hqnc,_⟩
     ·exact absurd h1 hv0_ne_p
     ·exact Or.inr rfl
     ·exact absurd hqc hqnc
    ·rcases hLmc v0 hv0_Lu with h1|⟨hqc,_⟩ | ⟨_,s0,hs0,_,rfl,hs0_only⟩
     ·exact absurd h1 hv0_ne_p
     ·exact absurd hqc hqnc
     ·right;congr 1
      by_contra hss0
      let T_small: Finset (Fin n):=insert q ((d2.cover.erase s).erase s0)
      have hcov_s: K2.IsVertexCover (T_small: Set (Fin n)):=by
       intro a b hab;have hown_ne:=hv2.2.2.1.2 a b hab
       by_cases h1: d2.owns a b=true
       ·have ha_cov: a∈d2.cover:=(hv2.2.2.1.1 a b h1).2
        by_cases has: a=s
        ·right;rw[hs_only b (has ▸ h1)];exact mC.mpr (mNs _ _)
        ·by_cases has0: a=s0
         ·right;rw[hs0_only b (has0 ▸ h1)];exact mC.mpr (mNs _ _)
         ·left;exact mC.mpr (mNo
           (mE.mpr ⟨has0,mE.mpr ⟨has,ha_cov⟩⟩))
       ·have h2: d2.owns b a=true:=by cases h' : d2.owns a b <;> cases h'' : d2.owns b a <;> simp[h',h''] at h1 hown_ne ⊢
        have hb_cov: b∈d2.cover:=(hv2.2.2.1.1 b a h2).2
        by_cases hbs: b=s
        ·left;rw[hs_only a (hbs ▸ h2)];exact mC.mpr (mNs _ _)
        ·by_cases hbs0: b=s0
         ·left;rw[hs0_only a (hbs0 ▸ h2)];exact mC.mpr (mNs _ _)
         ·right;exact mC.mpr (mNo
           (mE.mpr ⟨hbs0,mE.mpr ⟨hbs,hb_cov⟩⟩))
      have hle:=hv2.2.1.2 T_small hcov_s;have hs0_in: s0∈d2.cover.erase s:=mE.mpr ⟨Ne.symm hss0,hs0⟩
      have hc1: ((d2.cover.erase s).erase s0).card=(d2.cover.erase s).card - 1:=card_erase_of_mem hs0_in
      have hc2: (d2.cover.erase s).card=d2.cover.card - 1:=card_erase_of_mem hs;have hc3: T_small.card ≤ ((d2.cover.erase s).erase s0).card+1:=card_insert_le _ _
      have hge2: 2 ≤ d2.cover.card:=by
       have: ({s,s0}: Finset (Fin n))⊆d2.cover := by intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
       have:=card_le_card this;rw[card_pair hss0] at this;exact this
      omega
   ·rintro (rfl|rfl);exact hp_in_Lu;exact hv0_Lu
  have hu2_gt: n ≤ u2∧u2 - n∈topGates d2 C2:=by
   rcases hu2_top with h|h
   ·exfalso;have h1: Lu={p.val} := by simp only[Lu,h];exact osLl htop (Finset.mem_union_left _ (mI.mpr ⟨p,mNs _ _,rfl⟩))
    exact hLu_one h1
   ·exact h
  set ju:=u2 - n;have hju_tg: ju∈topGates d2 C2:=hu2_gt.2;have hju_lt: ju < C2.gates.length:=htGl ju hju_tg
  have hu2_eq_ju: u2=n+ju:=by omega
  have hGu_eq: Gu={ju}:=by
   have hcard:=tree_card n C2 Gu Lu u2 hsub_u;rw[hLu_pair,card_pair (Ne.symm hv0_ne_p)] at hcard
   have hju_in: ju∈Gu:=by
    obtain ⟨a,b,hab⟩:=ll2.mp (htop.1 ju hju_tg).2.1;change ju∈osG n C2 (topGates d2 C2) u2;rw[hu2_eq_ju,(osGq hv2.1 htop hju_tg hju_lt hab).1];exact mNs _ _
   exact eq_singleton_iff_unique_mem.mpr ⟨hju_in,fun g hg => by
    by_contra hne
    have: ({ju,g}: Finset ℕ)⊆Gu := by intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
    have:=card_le_card this;rw[card_pair (Ne.symm hne)] at this;omega⟩
  have hju_op: (gateAt C2 ju).op=GateOp.or:=(htop.1 ju hju_tg).1
  have hju_in: (gateAt C2 ju).inputs=[p.val,v0]∨(gateAt C2 ju).inputs=[v0,p.val]:=by
   obtain ⟨a,b,hab⟩:=ll2.mp (htop.1 ju hju_tg).2.1;have hsub_j:=osGq hv2.1 htop hju_tg hju_lt hab
   have ha_sub: osG n C2 (topGates d2 C2) a = ∅ := by
    by_contra hne;obtain ⟨g,hg⟩ := nonempty_iff_ne_empty.mpr hne
    have hgGu: g∈Gu:=by change g∈osG n C2 (topGates d2 C2) u2;rw[hu2_eq_ju,hsub_j.1];simp[hg]
    rw[hGu_eq,mS] at hgGu;have h1:=(osS hv2.1 htop htGl a).2.2 g hg;rw[hgGu] at h1;have h2:=hv2.1 ju hju_lt a (by simp[hab]);omega
   have hb_sub: osG n C2 (topGates d2 C2) b = ∅ := by
    by_contra hne;obtain ⟨g,hg⟩ := nonempty_iff_ne_empty.mpr hne
    have hgGu: g∈Gu:=by change g∈osG n C2 (topGates d2 C2) u2;rw[hu2_eq_ju,hsub_j.1];simp[hg]
    rw[hGu_eq,mS] at hgGu;have h1:=(osS hv2.1 htop htGl b).2.2 g hg;rw[hgGu] at h1;have h2:=hv2.1 ju hju_lt b (by simp[hab]);omega
   have hta:=(osT hv2.1 htop htGl a ((htop.1 ju hju_tg).2.2 a (by simp[hab]))).2.2.2;have htb:=(osT hv2.1 htop htGl b ((htop.1 ju hju_tg).2.2 b (by simp[hab]))).2.2.2;simp only[ha_sub,hb_sub,↓reduceIte] at hta htb
   have hLu_ab: Lu={a,b}:=by
    change osL n C2 (topGates d2 C2) (topLeaves d2 (insert p A)) u2={a,b};rw[hu2_eq_ju,hsub_j.2,hta,htb];ext x;simp
   rw[hLu_pair] at hLu_ab
   have ha_m: a∈({p.val,v0}: Finset ℕ):=by rw[hLu_ab];simp
   have hb_m: b∈({p.val,v0}: Finset ℕ):=by rw[hLu_ab];simp
   have hab_ne: a≠b:=by
    intro e;rw[e] at hLu_ab;simp only[pair_eq_singleton] at hLu_ab
    have:=congrArg Finset.card hLu_ab;rw[card_pair (Ne.symm hv0_ne_p),card_singleton] at this;omega
   simp only[mN,mS] at ha_m hb_m
   rcases ha_m with rfl|rfl <;> rcases hb_m with rfl|rfl
   ·exact absurd rfl hab_ne
   ·exact Or.inl hab
   ·exact Or.inr hab
   ·exact absurd rfl hab_ne
  have hjnn: n+r∉(gateAt C (li2 jl r ju)).inputs:=by
   intro hm
   have:=hrb (li2 jl r ju) ((li2lt hjr hr (by omega): _ < C.gates.length)) (n+r) hm
   have h1: n+li2 jl r ju=u:=by rw[←lw2g,←hu2_eq_ju,hu_lw]
   omega
  have hjlf:=r2l C hcl hrb hjr hr hu ju (by omega);have hjiC:=r2in C hcl hrb hjr hr hu hune hon0 hur ju (by omega) hjnn
  have hjnC: (gateAt C (li2 jl r ju)).inputs=[p.val,lw2 n jl r v0] ∨
    (gateAt C (li2 jl r ju)).inputs=[lw2 n jl r v0,p.val]:=by
   rw[hjiC];rcases hju_in with h|h <;> rw[h] <;> simp[lw2i n jl r p.val p.isLt]
  have htrm: IsOrTree n C2 ((topGates d2 C2).erase ju)
    (insert (n+ju) (((topLeaves d2 (insert p A)).erase p.val).erase v0)) C2.output:=by
   rcases hju_in with h|h
   ·exact otrc hv2.1 htop htGl hju_tg h
     (Finset.mem_union_left _ (mI.mpr ⟨p,mNs _ _,rfl⟩))
     (hLu_sub hv0_Lu)
   ·have h1:=otrc hv2.1 htop htGl hju_tg h (hLu_sub hv0_Lu)
     (Finset.mem_union_left _ (mI.mpr ⟨p,mNs _ _,rfl⟩))
    rwa[erase_right_comm] at h1
  have htCl: IsOrTree n C (((topGates d2 C2).erase ju).image (li2 jl r))
    (insert (n+r) ((((topLeaves d2 (insert p A)).erase p.val).erase v0).image (lw2 n jl r)))
    C.output:=by
   have hout_eq: C.output=if u2=C2.output then n+r else lw2 n jl r C2.output:=by
    rcases hor0 with ⟨he,hr_out⟩ | ⟨hne,hne_out,_⟩
    ·simp[he,hr_out]
    ·rw[if_neg hne,lw2r hjr hon0 hne_out]
   have hju_not_in: n+ju∉((topLeaves d2 (insert p A)).erase p.val).erase v0:=fun h =>
    (htop.2.1 (n+ju) (mEo (mEo h))).1 ⟨by omega,by simpa using hju_tg⟩
   have her_eq: (insert (n+ju) (((topLeaves d2 (insert p A)).erase p.val).erase v0)).erase (n+ju) =
     ((topLeaves d2 (insert p A)).erase p.val).erase v0 := erase_insert hju_not_in
   rw[hout_eq,hu2_eq_ju,←her_eq]
   exact ot2r C hcl hrb hjr hr hu hune hon0 hur htrm
    (fun j' hj' => by have := htGl j' (mEo hj');omega)
    (mNs _ _) hu2_eq_ju
    (fun j' hj' hmem => hu2_eq_ju ▸ hnrt j' (mEo hj') hmem)
    (fun j' hj' hmem => by
     rcases hor0 with ⟨he,_⟩ | ⟨_,_,hread⟩
     ·have hr0:=htop.2.2.1 ju hju_tg;rw[←hu2_eq_ju,if_pos he] at hr0;have h1: 1 ≤ (gateAt C2 j').inputs.count (n+ju):=lcpi.mpr hmem
      have hle: (gateAt C2 j').inputs.count (n+ju) ≤ readsIn C2 (topGates d2 C2) (n+ju) :=
       single_le_sum (f := fun m => (gateAt C2 m).inputs.count (n+ju)) (fun _ _ => Nat.zero_le _) (mEo hj')
      rw[hu2_eq_ju] at hr0;omega
     ·exact hread j' (mEo hj') (hu2_eq_ju.symm ▸ hmem))
  rcases hLmc v0 hv0_Lu with h1|⟨hqc,hq_free,hv0_eq,hwl_zr⟩ | ⟨hqnc,s,hs,hs_free,hv0_eq,hs_only⟩
  ·exact absurd h1 hv0_ne_p
  ·
   let roleB: ℕ → Kind × ℕ := fun j =>
    if j=jl then (Kind.o,p.val)
    else if j=r then (Kind.b,p.val)
    else if j=li2 jl r ju then (Kind.z,p.val)
    else d2.role (rd 0 jl 0 (rd 0 r 0 j))
   have hrln: ∀ j' : ℕ,j' ≠ ju → roleB (li2 jl r j')=d2.role j' := by
    intro j' hne;have h1:=li2nj jl r j' hjr;have h2:=li2nr jl r j'
    have h3: li2 jl r j' ≠ li2 jl r ju:=fun e => hne (li2i jl r e)
    simp only[roleB,h1,h2,h3,↓reduceIte]
    congr 1
    have hlift_eq: li2 jl r j' = lw2 0 jl r j' := by unfold li2 lw2 li1 lw1;simp
    rw[hlift_eq];exact rd2l
   have hrole_ju: roleB (li2 jl r ju)=(Kind.z,p.val):=by
    simp[roleB,li2nj jl r ju hjr,li2nr jl r ju]
   let d: NCCData n:={
    cover := insert p d2.cover
    owns := fun a b => if a=p∧(b=l∨b=q) then true else d2.owns a b
    tie := fun t => if t=q then some p else d2.tie t
    role := roleB
    bw := fun t => if t=p then n+r else lw2 n jl r (d2.bw t)
    zroot := fun t => if t=p then lw2 n jl r u2 else lw2 n jl r (d2.zroot t)
    oroot := fun t => if t=p then n+jl else lw2 n jl r (d2.oroot t)
    lam := fun t v => if t=p then (if v=l then l.val else wl) else lw2 n jl r (d2.lam t v)
   }
   have hgn: ∀ (k: Kind) (v: ℕ),k≠Kind.top →
     (k,v)≠(Kind.o,p.val)→(k,v)≠(Kind.b,p.val)→(k,v)≠(Kind.z,p.val) →
     gatesOf d C k v=(gatesOf d2 C2 k v).image (li2 jl r):=by
    intro k v hnt h1 h2 h3
    ext j;simp only[gatesOf,d,mF,mR,mI]
    constructor
    ·rintro ⟨hj,hrj⟩
     have hjl_ne: j≠jl:=fun e => h1 (by rw[←hrj,e];simp[roleB])
     have hr_ne: j≠r:=fun e => h2 (by rw[←hrj,e];simp[roleB,Nat.ne_of_gt hjr])
     have hju_ne: j≠li2 jl r ju:=fun e => h3 (by rw[←hrj,e,hrole_ju])
     obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hjl_ne hr_ne
     have hj'_ne: j' ≠ ju:=fun e => hju_ne (by rw[e])
     exact ⟨j',⟨by omega,by rw[←hrln j' hj'_ne];exact hrj⟩,rfl⟩
    ·rintro ⟨j',⟨hj',hrj'⟩,rfl⟩
     have hj'_ne: j' ≠ ju:=fun e => hnt (by
      have:=(mF.mp hju_tg).2;rw[←e,hrj'] at this;exact this)
     exact ⟨(li2lt hjr hr (by omega): _ < C.gates.length),by rw[hrln j' hj'_ne,hrj']⟩
   refine ⟨d,hrb,?_,?_,?_,?_,?_,?_⟩
   ·refine ⟨?_,fun T hT => by have := htK2 T hT;simp only[d,card_insert_of_notMem hpnc];omega⟩
    intro a b hab
    by_cases hap: a=p
    ·left;simp[d,hap]
    ·by_cases hbp: b=p
     ·right;simp[d,hbp]
     ·have hal: a≠l:=fun e => hbp ((hl b).mp (e ▸ hab))
      have hbl: b≠l:=fun e => hap ((hl a).mp (e ▸ hab.symm))
      rcases hv2.2.1.1 ((hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩) with ha|hb
      ·left;exact mC.mpr (mNo (mC.mp ha))
      ·right;exact mC.mpr (mNo (mC.mp hb))
   ·refine ⟨?_,?_⟩
    ·intro a b hown;dsimp[d] at hown;split_ifs at hown with h
     ·exact ⟨by rw[h.1];exact (hp b).mpr h.2,by rw[h.1];exact mNs _ _⟩
     ·have h1:=hv2.2.2.1.1 a b hown;exact ⟨((hK2 a b).mp h1.1).1,mNo h1.2⟩
    ·intro a b hab
     by_cases hap: a=p
     ·rw[hap] at hab ⊢;have hbp: b≠p:=hab.ne';have hblq: b=l∨b=q:=(hp b).mp hab
      have hb_no: d2.owns b p=false:=by
       cases h: d2.owns b p;rfl;exact absurd (hv2.2.2.1.1 b p h).1.symm (hp_iso b)
      dsimp[d];simp[hblq,hbp,hb_no]
     ·by_cases hbp: b=p
      ·rw[hbp] at hab ⊢;have halq: a=l∨a=q:=(hp a).mp hab.symm
       have ha_no: d2.owns a p=false:=by
        cases h: d2.owns a p;rfl;exact absurd (hv2.2.2.1.1 a p h).1.symm (hp_iso a)
       dsimp[d];simp[halq,hap,ha_no]
      ·have hal: a≠l:=fun e => hbp ((hl b).mp (e ▸ hab))
       have hbl: b≠l:=fun e => hap ((hl a).mp (e ▸ hab.symm))
       dsimp[d];simp[hap,hbp,hv2.2.2.1.2 a b ((hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩)]
   ·intro a b hab;dsimp[d] at hab;split_ifs at hab with haq
    ·rw[haq];cases hab;exact ⟨mNo hqc,by simp[d]⟩
    ·have h1:=hv2.2.2.2.1 a b hab
     refine ⟨mNo h1.1,?_⟩
     dsimp[d];split_ifs
     ·rfl
     ·exact h1.2
   ·intro j hj
    by_cases hje: j=jl
    ·subst hje;right;exact ⟨p,mNs _ _,by simp[d,roleB],fun h => by simp[d,roleB] at h⟩
    ·by_cases hre: j=r
     ·subst hre;right;exact ⟨p,mNs _ _,by simp[d,roleB,Nat.ne_of_gt hjr],fun _ => by simp[d]⟩
     ·by_cases hjue: j=li2 jl r ju
      ·subst hjue;right;exact ⟨p,mNs _ _,by simp[d,hrole_ju],fun h => by simp[d,hrole_ju] at h⟩
      ·obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
       have hj'_ne: j' ≠ ju:=fun e => hjue (by rw[e])
       have hr_eq: d.role (li2 jl r j')=d2.role j' := hrln j' hj'_ne
       rcases hv2.2.2.2.2.1 j' (by omega) with htop_j|⟨t,ht,e1,e2⟩
       ·exact Or.inl (by rw[hr_eq];exact htop_j)
       ·right;refine ⟨t,mNo ht,by rw[hr_eq];exact e1,fun hk => ?_⟩
        rw[hr_eq] at hk
        have htp: t≠p:=fun e => hpnc (e ▸ ht)
        dsimp[d];simp only[htp,↓reduceIte];rw[e2 hk,lw2g]
   ·intro t ht
    by_cases htp: t=p
    ·rw[htp]
     refine ⟨?_,?_,?_,?_⟩
     ·refine ⟨r,hr,by simp[d],by simp[d,roleB,Nat.ne_of_gt hjr],hro0,?_⟩
      dsimp[d];simp only[↓reduceIte,hu_lw];exact hri0.symm
     ·have hG: gatesOf d C Kind.z p.val={li2 jl r ju}:=by
       ext j;simp only[gatesOf,d,mF,mR,mS]
       constructor
       ·rintro ⟨hj,hrj⟩
        by_contra hjue
        have hje: j≠jl:=fun e => by rw[e] at hrj;simp[roleB] at hrj
        have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleB,Nat.ne_of_gt hjr] at hrj
        obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
        rw[hrln j' (fun e => hjue (by rw[e]))] at hrj
        rcases hv2.2.2.2.2.1 j' (by omega) with htop_j|⟨s,hs,e1,_⟩
        ·rw[hrj] at htop_j;cases htop_j
        ·rw[hrj] at e1;exact hpnc (Fin.ext e1.symm ▸ hs)
       ·rintro rfl;exact ⟨(li2lt hjr hr (by omega): _ < C.gates.length),hrole_ju⟩
      have hL: zLeaves d p={p.val,lw2 n jl r (d2.bw q)}:=by
       ext w;simp only[zLeaves,d,mN,mI,mF,mS]
       constructor
       ·rintro (rfl|⟨s,⟨_,hst⟩,rfl⟩)
        ·exact Or.inl rfl
        ·split_ifs at hst with hsq
         ·right;rw[hsq];simp[hpq.symm]
         ·exact absurd (hv2.2.2.1.1 p s (hv2.2.2.2.1 s p hst).2).1 (hp_iso s)
       ·rintro (rfl|rfl)
        ·exact Or.inl rfl
        ·right;exact ⟨q,⟨Or.inr hqc,by simp⟩,by simp[hpq.symm]⟩
      rw[hG,hL];dsimp[d];simp only[↓reduceIte,hu2_eq_ju,lw2g]
      have hne_p_bw: p.val≠lw2 n jl r (d2.bw q):=by
       obtain ⟨jb,_,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 q hqc).1;rw[hbw,lw2g];have := p.isLt;omega
      have hne_p_ju: p.val≠n+li2 jl r ju:=by have:=p.isLt;omega
      have hne_bw_ju: lw2 n jl r (d2.bw q)≠n+li2 jl r ju:=by
       rw[←lw2g];intro e;have := lw2j n jl r e;exact (htop.2.1 (d2.bw q) (hv0_eq ▸ hLu_sub hv0_Lu)).1 ⟨by omega,by rw[this,ascl];exact hju_tg⟩
      have hjnC' : (gateAt C (li2 jl r ju)).inputs=[p.val,lw2 n jl r (d2.bw q)] ∨
        (gateAt C (li2 jl r ju)).inputs=[lw2 n jl r (d2.bw q),p.val] := hv0_eq ▸ hjnC
      refine ⟨?_,?_,?_,?_⟩
      ·intro j hj;rw[mS.mp hj]
       refine ⟨by rw[←hjlf.1,hju_op],by rcases hjnC' with h|h <;> simp[h],fun i hi => ?_⟩
       rcases hjnC' with h|h <;> rw[h] at hi <;> simp at hi <;> rcases hi with rfl|rfl <;> exact Or.inl (by simp)
      ·intro w hw;simp only[mN,mS] at hw
       rcases hw with rfl|rfl
       ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
        simp only[readsIn,sum_singleton,hne_p_ju,↓reduceIte]
        rcases hjnC' with h|h <;> rw[h] <;> simp[hne_p_bw,hne_p_bw.symm]
       ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
        simp only[readsIn,sum_singleton,hne_bw_ju,↓reduceIte]
        rcases hjnC' with h|h <;> rw[h] <;> simp[hne_p_bw,hne_p_bw.symm]
      ·intro j hj;rw[mS.mp hj];simp only[readsIn,sum_singleton,↓reduceIte,lcz]
       rcases hjnC' with h|h <;> rw[h] <;> simp[hne_p_ju.symm,hne_bw_ju.symm]
      ·simp
     ·have hG: gatesOf d C Kind.o p.val={jl}:=by
       ext j;simp only[gatesOf,d,mF,mR,mS]
       constructor
       ·rintro ⟨hj,hrj⟩
        by_contra hje
        have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleB,Nat.ne_of_gt hjr] at hrj
        have hjue: j≠li2 jl r ju:=fun e => by rw[e,hrole_ju] at hrj;simp at hrj
        obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
        rw[hrln j' (fun e => hjue (by rw[e]))] at hrj
        rcases hv2.2.2.2.2.1 j' (by omega) with htop_j|⟨s,hs,e1,_⟩
        ·rw[hrj] at htop_j;cases htop_j
        ·rw[hrj] at e1;exact hpnc (Fin.ext e1.symm ▸ hs)
       ·rintro rfl;exact ⟨by omega,by simp[roleB]⟩
      have hL: oLeaves d p={l.val,wl}:=by
       ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
        mN,mS]
       constructor
       ·rintro ⟨v,hown,rfl⟩
        split_ifs at hown with hv
        ·rcases hv with rfl|rfl
         ·left;simp
         ·right;simp[hql]
        ·exact absurd (hv2.2.2.1.1 p v hown).1 (hp_iso v)
       ·rintro (rfl|rfl)
        ·exact ⟨l,by simp,by simp⟩
        ·exact ⟨q,by simp,by simp[hql]⟩
      rw[hG,hL];dsimp[d];simp only[↓reduceIte]
      have hwl_ne_jl: wl≠n+jl:=by omega
      have hl_ne_jl: l.val≠n+jl:=by have:=l.isLt;omega
      refine ⟨?_,?_,?_,?_⟩
      ·intro j hj;rw[mS.mp hj]
       refine ⟨hjlo,by rcases hjli with h|h <;> simp[h],fun i hi => ?_⟩
       rcases hjli with h|h <;> rw[h] at hi <;> simp at hi <;> rcases hi with rfl|rfl <;> exact Or.inl (by simp)
      ·intro w hw;simp only[mN,mS] at hw
       rcases hw with rfl|rfl
       ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
        simp only[readsIn,sum_singleton,hl_ne_jl,↓reduceIte]
        rcases hjli with h|h <;> rw[h] <;> simp[hwne,hwne.symm]
       ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
        simp only[readsIn,sum_singleton,hwl_ne_jl,↓reduceIte]
        rcases hjli with h|h <;> rw[h] <;> simp[hwne,hwne.symm]
      ·intro j hj;rw[mS.mp hj];simp only[readsIn,sum_singleton,↓reduceIte,lcz]
       rcases hjli with h|h <;> rw[h] <;> simp[hl_ne_jl.symm,hwl_ne_jl.symm]
      ·simp
     ·intro v hown;dsimp[d] at hown
      have hvlq: v=l∨v=q:=by
       split_ifs at hown with h;exact h.2
       exact absurd (hv2.2.2.1.1 p v hown).1 (hp_iso v)
      rcases hvlq with hvl|hvq
      ·rw[hvl];unfold LamOK;dsimp[d];simp[hlp,hlnc]
      ·rw[hvq];unfold LamOK;dsimp[d];simp only[mNo hqc,↓reduceIte,hql]
       refine ⟨?_,?_,?_⟩
       ·rw[←hwl_lw]
        apply cf2 (d := d) C hcl hrb hjr hr hu hune hon0 hur hv2 d2.cover
         (Subset.refl _) (subset_insert p d2.cover)
         (fun j' hj' hrz => ⟨hnt0 j' (by omega) (by rw[hrz];intro hc;cases hc),by
          have hne_ju: j' ≠ ju:=fun e => by
           have:=(mF.mp hju_tg).2;rw[←e,hrz] at this;cases this
          dsimp[d];rw[hrln j' hne_ju,hrz]⟩)
         q hqc wl2
        ·rcases hw2c with hq|⟨_,hcen,_⟩
         ·rw[hq,cfi C2 d2 q];exact hqc
         ·exact hcen
        ·rcases hw2c with hq|⟨_,_,jz,hjz,h1,h2⟩
         ·exact Or.inl hq
         ·exact Or.inr ⟨jz,by omega,h1,h2⟩
       ·rcases hw2c with hq|⟨_,_,jz,hjz,h1,h2⟩
        ·left;rw[←hwl_lw,hq,lw2i n jl r q.val q.isLt]
        ·right
         have hne_ju: jz≠ju:=fun e => by
          have:=(mF.mp hju_tg).2;rw[←e,h2] at this;cases this
         refine ⟨li2 jl r jz,(li2lt hjr hr (by omega): _ < C.gates.length),
          by rw[←hwl_lw,h1,lw2g],by rw[hrln jz hne_ju,h2]⟩
       ·intro _;simp only[hpq.symm,↓reduceIte];rw[←hwl_lw,hwl_zr]
    ·have ht2: t∈d2.cover:=by rcases mN.mp ht with rfl|h;exact absurd rfl htp;exact h
     refine ⟨?_,?_,?_,?_⟩
     ·obtain ⟨jb,hjb,hbw,hrb_t,hop,hin⟩:=(hv2.2.2.2.2.2.1 t ht2).1
      have hne_ju: jb≠ju:=fun e => by
       have:=(mF.mp hju_tg).2;rw[←e,hrb_t] at this;cases this
      have hno:=hnt0 jb hjb (by rw[hrb_t];intro hc;cases hc);have hlif:=r2l C hcl hrb hjr hr hu jb (by omega);have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jb (by omega) hno
      refine ⟨li2 jl r jb,(li2lt hjr hr (by omega): _ < C.gates.length),by dsimp[d];simp[htp,hbw,lw2g],
       by dsimp[d];rw[hrln jb hne_ju,hrb_t],by rw[←hlif.1,hop],?_⟩
      rw[hinp];rcases hin with h|h <;> rw[h] <;> simp[d,htp]
     ·have hG: gatesOf d C Kind.z t.val=(gatesOf d2 C2 Kind.z t.val).image (li2 jl r) :=
       hgn Kind.z t.val (by simp) (by simp) (by simp) (fun h => htp (Fin.ext (pei.mp h).2))
      have hL: zLeaves d t=(zLeaves d2 t).image (lw2 n jl r):=by
       ext w;simp only[zLeaves,d,mN,mI,mF]
       constructor
       ·rintro (rfl|⟨s,⟨hs,hst⟩,rfl⟩)
        ·exact ⟨t.val,Or.inl rfl,lw2i n jl r t.val t.isLt⟩
        ·split_ifs at hst with hsq
         ·cases hst;exact absurd rfl htp
         ·have hs2: s∈d2.cover:=(hv2.2.2.2.1 s t hst).1
          have hsp: s≠p:=fun e => hpnc (e ▸ hs2)
          simp only[hsp,↓reduceIte];exact ⟨d2.bw s,Or.inr ⟨s,⟨hs2,hst⟩,rfl⟩,rfl⟩
       ·rintro ⟨_,rfl|⟨s,⟨hs,hst⟩,rfl⟩,rfl⟩
        ·exact Or.inl (lw2i n jl r t.val t.isLt)
        ·have hsp: s≠p:=fun e => hpnc (e ▸ hs)
         have hsq: s≠q:=fun e => by rw[e,hq_free] at hst;cases hst
         exact Or.inr ⟨s,⟨Or.inr hs,by simp[hsq,hst]⟩,by simp[hsp]⟩
      rw[hG,hL];dsimp[d];simp only[htp,↓reduceIte]
      exact ot2u C hcl hrb hjr hr hu hune hon0 hur (hv2.2.2.2.2.2.1 t ht2).2.1
       (fun j' hj' => by have := mR.mp (mF.mp hj').1;omega)
       (fun j' hj' => hnt0 j' (mR.mp (mF.mp hj').1)
        (by rw[(mF.mp hj').2];intro hc;cases hc))
     ·have hG: gatesOf d C Kind.o t.val=(gatesOf d2 C2 Kind.o t.val).image (li2 jl r) :=
       hgn Kind.o t.val (by simp) (fun h => htp (Fin.ext (pei.mp h).2)) (by simp) (by simp)
      have hL: oLeaves d t=(oLeaves d2 t).image (lw2 n jl r):=by
       ext w;simp only[oLeaves,d,mI,mF,mV,true_and,htp,false_and,↓reduceIte]
       constructor
       ·rintro ⟨v,hown,rfl⟩;exact ⟨d2.lam t v,⟨v,hown,rfl⟩,rfl⟩
       ·rintro ⟨_,⟨v,hown,rfl⟩,rfl⟩;exact ⟨v,hown,rfl⟩
      rw[hG,hL];dsimp[d];simp only[htp,↓reduceIte]
      exact ot2u C hcl hrb hjr hr hu hune hon0 hur (hv2.2.2.2.2.2.1 t ht2).2.2.1
       (fun j' hj' => by have := mR.mp (mF.mp hj').1;omega)
       (fun j' hj' => hnt0 j' (mR.mp (mF.mp hj').1)
        (by rw[(mF.mp hj').2];intro hc;cases hc))
     ·intro v hown;dsimp[d] at hown;simp only[htp,false_and,↓reduceIte] at hown
      have hvp: v≠p:=fun e => hp_iso t (e ▸ (hv2.2.2.1.1 t v hown).1).symm
      have hlam:=(hv2.2.2.2.2.2.1 t ht2).2.2.2 v hown;unfold LamOK at hlam ⊢;dsimp[d];simp only[htp,↓reduceIte]
      by_cases hvc: v∈d2.cover
      ·have hvc' : v∈insert p d2.cover:=mNo hvc;simp only[hvc,hvc',↓reduceIte] at hlam ⊢
       refine ⟨?_,?_,?_⟩
       ·exact cf2 (d := d) C hcl hrb hjr hr hu hune hon0 hur hv2 d2.cover
         (Subset.refl _) (subset_insert p d2.cover)
         (fun j' hj' hrz => ⟨hnt0 j' (by omega) (by rw[hrz];intro hc;cases hc),by
          have hne_ju: j' ≠ ju:=fun e => by
           have:=(mF.mp hju_tg).2;rw[←e,hrz] at this;cases this
          dsimp[d];rw[hrln j' hne_ju,hrz]⟩)
         v hvc (d2.lam t v) hlam.1 (by
          rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
          ·exact Or.inl h
          ·exact Or.inr ⟨jz,by omega,h1,h2⟩)
       ·rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
        ·exact Or.inl (by rw[h,lw2i n jl r v.val v.isLt])
        ·have hne_ju: jz≠ju:=fun e => by
          have:=(mF.mp hju_tg).2;rw[←e,h2] at this;cases this
         exact Or.inr ⟨li2 jl r jz,(li2lt hjr hr (by omega): _ < C.gates.length),
          by rw[h1,lw2g],by rw[hrln jz hne_ju,h2]⟩
       ·intro htie;split_ifs at htie with hvq
        ·cases htie;exact absurd rfl htp
        ·simp only[hvp,↓reduceIte];rw[hlam.2.2 htie]
      ·have hvc' : v∉insert p d2.cover:=by simp[hvp,hvc]
       simp only[hvc,hvc',↓reduceIte] at hlam ⊢;rw[hlam,lw2i n jl r v.val v.isLt]
   ·have hG: topGates d C=((topGates d2 C2).erase ju).image (li2 jl r):=by
     ext j;simp only[topGates,d,mF,mR,mI,mE]
     constructor
     ·rintro ⟨hj,hrj⟩
      have hje: j≠jl:=fun e => by rw[e] at hrj;simp[roleB] at hrj
      have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleB,Nat.ne_of_gt hjr] at hrj
      have hjue: j≠li2 jl r ju:=fun e => by rw[e,hrole_ju] at hrj;cases hrj
      obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
      have hj'_ne: j' ≠ ju:=fun e => hjue (by rw[e])
      exact ⟨j',⟨hj'_ne,⟨by omega,by rw[←hrln j' hj'_ne];exact hrj⟩⟩,rfl⟩
     ·rintro ⟨j',⟨hj'_ne,⟨hj',hrj'⟩⟩,rfl⟩
      exact ⟨(li2lt hjr hr (by omega): _ < C.gates.length),by rw[hrln j' hj'_ne,hrj']⟩
    have hL: topLeaves d A=insert (n+r) ((((topLeaves d2 (insert p A)).erase p.val).erase v0).image (lw2 n jl r)):=by
     ext w;simp only[topLeaves,d,mU,mI,mF,
      mN,mE]
     constructor
     ·rintro (⟨a,ha,rfl⟩ | ⟨s,⟨hs,hst⟩,rfl⟩)
      ·right
       have hne_v0: a.val≠v0:=by
        rw[hv0_eq];obtain ⟨jb,_,hbw,_,_,_⟩ := (hv2.2.2.2.2.2.1 q hqc).1;have := a.isLt;omega
       exact ⟨a.val,⟨hne_v0,fun e => hpnA (Fin.ext e ▸ ha),Or.inl ⟨a,Or.inr ha,rfl⟩⟩,lw2i n jl r a.val a.isLt⟩
      ·by_cases hsp: s=p
       ·left;simp[hsp]
       ·right;simp only[hsp,↓reduceIte]
        have hsq: s≠q:=fun e => by rw[e] at hst;simp at hst
        simp only[hsq,↓reduceIte] at hst
        have hs2: s∈d2.cover:=by rcases hs with rfl|h;exact absurd rfl hsp;exact h
        obtain ⟨jb,_,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 s hs2).1
        have hne_v0: d2.bw s≠v0:=by rw[hv0_eq];exact fun e => hsq (bw_injOn hv2 d2.cover (Subset.refl _) hs2 hqc e)
        exact ⟨d2.bw s,⟨hne_v0,by omega,Or.inr ⟨s,⟨hs2,hst⟩,rfl⟩⟩,rfl⟩
     ·rintro (rfl|⟨w',⟨hw'ne_v0,hw'ne_p,hw'tl⟩,rfl⟩)
      ·right;exact ⟨p,⟨Or.inl rfl,by
        simp only[hpq,↓reduceIte]
        cases h: d2.tie p with
        | none => rfl
        | some t => exfalso;exact hpnc (hv2.2.2.2.1 p t h).1⟩,by simp⟩
      ·rcases hw'tl with ⟨a,rfl|ha,rfl⟩ | ⟨s,⟨hs,hst⟩,rfl⟩
       ·exact absurd rfl hw'ne_p
       ·left;exact ⟨a,ha,(lw2i n jl r a.val a.isLt).symm⟩
       ·right
        have hsp: s≠p:=fun e => hpnc (e ▸ hs)
        have hsq: s≠q:=fun e => hw'ne_v0 (hv0_eq ▸ congrArg d2.bw e)
        exact ⟨s,⟨Or.inr hs,by simp[hsq,hst]⟩,by simp[hsp]⟩
    rw[hG,hL];exact htCl
  ·
   have hwl_eq_q: wl2=q.val:=by
    rcases hw2c with h|⟨h1,_⟩
    ·exact h
    ·exact absurd h1 hqnc
   have hwl_eq_qv: wl=q.val:=by rw[←hwl_lw,hwl_eq_q,lw2i n jl r q.val q.isLt]
   have hZse: gatesOf d2 C2 Kind.z s.val = ∅ := by
    have hL: zLeaves d2 s={s.val}:=by
     ext w;simp only[zLeaves,mN,mI,mF,mS,or_iff_left_iff_imp]
     rintro ⟨t,⟨ht,hts⟩,_⟩
     have htq: t=q:=hs_only t (hv2.2.2.2.1 t s hts).2;exact absurd (htq ▸ ht) hqnc
    have hcard:=tree_card n C2 _ _ (d2.zroot s) (hv2.2.2.2.2.2.1 s hs).2.1;rw[hL,card_singleton] at hcard;exact card_eq_zero.mp (by omega)
   have hOse: gatesOf d2 C2 Kind.o s.val = ∅ := by
    have hL: oLeaves d2 s={q.val}:=by
     ext w;simp only[oLeaves,mI,mF,mV,true_and,mS]
     constructor
     ·rintro ⟨r',hown,rfl⟩
      have hr'q: r' = q:=hs_only r' hown;have hlam:=(hv2.2.2.2.2.2.1 s hs).2.2.2 r' hown;rw[hr'q] at hlam ⊢;unfold LamOK at hlam;simp[hqnc] at hlam;exact hlam
     ·rintro rfl
      obtain ⟨r',hown,_⟩:=coo hv2 s hs;have hr'q: r' = q:=hs_only r' hown;rw[hr'q] at hown;have hlam:=(hv2.2.2.2.2.2.1 s hs).2.2.2 q hown;unfold LamOK at hlam;simp[hqnc] at hlam;exact ⟨q,hown,hlam⟩
    have hcard:=tree_card n C2 _ _ (d2.oroot s) (hv2.2.2.2.2.2.1 s hs).2.2.1;rw[hL,card_singleton] at hcard;exact card_eq_zero.mp (by omega)
   have hzrs: d2.zroot s=s.val:=by
    have h1:=(hv2.2.2.2.2.2.1 s hs).2.1.2.2.2;simp only[hZse,↓reduceIte] at h1;have hs_in: s.val∈zLeaves d2 s:=mNs _ _;rw[h1,mS] at hs_in;exact hs_in.symm
   have hors: d2.oroot s=q.val:=by
    have h1:=(hv2.2.2.2.2.2.1 s hs).2.2.1.2.2.2;simp only[hOse,↓reduceIte] at h1;obtain ⟨r',hown,_⟩:=coo hv2 s hs;have hr'q: r' = q:=hs_only r' hown;rw[hr'q] at hown;have hlam:=(hv2.2.2.2.2.2.1 s hs).2.2.2 q hown;unfold LamOK at hlam;simp[hqnc] at hlam
    have hq_in: q.val∈oLeaves d2 s:=by
     simp only[oLeaves,mI,mF,mV,true_and];exact ⟨q,hown,hlam⟩
    rw[h1,mS] at hq_in;exact hq_in.symm
   have hsq: s≠q:=fun e => hqnc (e ▸ hs)
   have hsp: s≠p:=fun e => hpnc (e ▸ hs)
   have hown_sq: d2.owns s q=true:=by
    obtain ⟨r',hown,_⟩:=coo hv2 s hs;rw[←hs_only r' hown];exact hown
   have hK2_sq: K2.Adj s q:=(hv2.2.2.1.1 s q hown_sq).1;obtain ⟨jbs,hjbs,hbws,hrbs,hop_bs,hin_bs⟩:=(hv2.2.2.2.2.2.1 s hs).1;let covC: Finset (Fin n):=insert p (insert q (d2.cover.erase s))
   have hcCc: covC.card=d2.cover.card+1:=by
    have hq_not_er: q∉d2.cover.erase s:=fun h => hqnc (mEo h)
    have hp_not_er: p∉d2.cover.erase s:=fun h => hpnc (mEo h)
    have hp_not_in: p∉insert q (d2.cover.erase s):=by
     simp[hpq,hp_not_er]
    have her:=card_erase_of_mem hs;have hpos: 1 ≤ d2.cover.card:=one_le_card.mpr ⟨s,hs⟩;simp only[covC,card_insert_of_notMem hp_not_in,card_insert_of_notMem hq_not_er];omega
   let roleC: ℕ → Kind × ℕ := fun j =>
    if j=jl then (Kind.o,p.val)
    else if j=r then (Kind.b,p.val)
    else if j=li2 jl r ju then (Kind.z,p.val)
    else if j=li2 jl r jbs then (Kind.b,q.val)
    else d2.role (rd 0 jl 0 (rd 0 r 0 j))
   have hnjb: jbs≠ju:=fun e => by
    have:=(mF.mp hju_tg).2;rw[←e,hrbs] at this;cases this
   have hrln: ∀ j' : ℕ,j' ≠ ju → j' ≠ jbs → roleC (li2 jl r j')=d2.role j' := by
    intro j' h1 h2;have e1:=li2nj jl r j' hjr;have e2:=li2nr jl r j'
    have e3: li2 jl r j' ≠ li2 jl r ju:=fun e => h1 (li2i jl r e)
    have e4: li2 jl r j' ≠ li2 jl r jbs:=fun e => h2 (li2i jl r e)
    simp only[roleC,e1,e2,e3,e4,↓reduceIte]
    congr 1
    have hlift_eq: li2 jl r j' = lw2 0 jl r j' := by unfold li2 lw2 li1 lw1;simp
    rw[hlift_eq];exact rd2l
   have hrole_ju: roleC (li2 jl r ju)=(Kind.z,p.val):=by
    simp[roleC,li2nj jl r ju hjr,li2nr jl r ju]
   have hrole_jbs: roleC (li2 jl r jbs)=(Kind.b,q.val):=by
    have h3: li2 jl r jbs≠li2 jl r ju:=fun e => hnjb (li2i jl r e)
    simp[roleC,li2nj jl r jbs hjr,li2nr jl r jbs,h3]
   let d: NCCData n:={
    cover := covC
    owns := fun a b =>
     if a=p∧(b=l∨b=q) then true
     else if a=q∧b=s then true
     else if a=s then false
     else d2.owns a b
    tie := fun t => if t=q then some p else d2.tie t
    role := roleC
    bw := fun t => if t=p then n+r else if t=q then lw2 n jl r (d2.bw s) else lw2 n jl r (d2.bw t)
    zroot := fun t => if t=p then lw2 n jl r u2 else if t=q then q.val else lw2 n jl r (d2.zroot t)
    oroot := fun t => if t=p then n+jl else if t=q then s.val else lw2 n jl r (d2.oroot t)
    lam := fun t v =>
     if t=p then (if v=l then l.val else q.val)
     else if t=q then s.val
     else lw2 n jl r (d2.lam t v)
   }
   have hgn: ∀ (k: Kind) (v: ℕ),k≠Kind.top →
     (k,v)≠(Kind.o,p.val)→(k,v)≠(Kind.b,p.val)→(k,v)≠(Kind.z,p.val) →
     (k,v)≠(Kind.b,q.val) → v≠s.val →
     gatesOf d C k v=(gatesOf d2 C2 k v).image (li2 jl r):=by
    intro k v hnt h1 h2 h3 h4 hns
    ext j;simp only[gatesOf,d,mF,mR,mI]
    constructor
    ·rintro ⟨hj,hrj⟩
     have hjl_ne: j≠jl:=fun e => h1 (by rw[←hrj,e];simp[roleC])
     have hr_ne: j≠r:=fun e => h2 (by rw[←hrj,e];simp[roleC,Nat.ne_of_gt hjr])
     have hju_ne: j≠li2 jl r ju:=fun e => h3 (by rw[←hrj,e,hrole_ju])
     have hjbs_ne: j≠li2 jl r jbs:=fun e => h4 (by rw[←hrj,e,hrole_jbs])
     obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hjl_ne hr_ne
     have h1' : j' ≠ ju:=fun e => hju_ne (by rw[e])
     have h2' : j' ≠ jbs:=fun e => hjbs_ne (by rw[e])
     exact ⟨j',⟨by omega,by rw[←hrln j' h1' h2'];exact hrj⟩,rfl⟩
    ·rintro ⟨j',⟨hj',hrj'⟩,rfl⟩
     have h1' : j' ≠ ju:=fun e => hnt (by have:=(mF.mp hju_tg).2;rw[←e,hrj'] at this;exact this)
     have h2' : j' ≠ jbs:=fun e => hns (by rw[e,hrbs] at hrj';exact (pei.mp hrj').2.symm)
     exact ⟨(li2lt hjr hr (by omega): _ < C.gates.length),by rw[hrln j' h1' h2',hrj']⟩
   refine ⟨d,hrb,?_,?_,?_,?_,?_,?_⟩
   ·
    refine ⟨?_,fun T hT => by have := htK2 T hT;dsimp[d];omega⟩
    intro a b hab
    by_cases hap: a=p
    ·left;exact mC.mpr (hap ▸ mNs p _)
    ·by_cases hbp: b=p
     ·right;exact mC.mpr (hbp ▸ mNs p _)
     ·have hal: a≠l:=fun e => hbp ((hl b).mp (e ▸ hab))
      have hbl: b≠l:=fun e => hap ((hl a).mp (e ▸ hab.symm))
      have hK2ab: K2.Adj a b:=(hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩;have hne:=hv2.2.2.1.2 a b hK2ab
      by_cases h1: d2.owns a b=true
      ·by_cases has: a=s
       ·right;rw[hs_only b (has ▸ h1)];exact mC.mpr (mNo (mNs q _))
       ·left;exact mC.mpr (mNo (mNo
         (mE.mpr ⟨has,(hv2.2.2.1.1 a b h1).2⟩)))
      ·have h2: d2.owns b a=true:=by cases h' : d2.owns a b <;> cases h'' : d2.owns b a <;> simp[h',h''] at h1 hne ⊢
       by_cases hbs: b=s
       ·left;rw[hs_only a (hbs ▸ h2)];exact mC.mpr (mNo (mNs q _))
       ·right;exact mC.mpr (mNo (mNo
         (mE.mpr ⟨hbs,(hv2.2.2.1.1 b a h2).2⟩)))
   ·
    refine ⟨?_,?_⟩
    ·intro a b hown;dsimp[d] at hown
     by_cases h1: a=p∧(b=l∨b=q)
     ·exact ⟨by rw[h1.1];exact (hp b).mpr h1.2,by rw[h1.1];exact mNs p _⟩
     ·simp only[h1,↓reduceIte] at hown
      by_cases h2: a=q∧b=s
      ·exact ⟨by rw[h2.1,h2.2];exact ((hK2 s q).mp hK2_sq).1.symm,
        by rw[h2.1];exact mNo (mNs q _)⟩
      ·simp only[h2,↓reduceIte] at hown
       by_cases h3: a=s
       ·simp only[h3,↓reduceIte] at hown;cases hown
       ·simp only[h3,↓reduceIte] at hown;have h4:=hv2.2.2.1.1 a b hown;exact ⟨((hK2 a b).mp h4.1).1,mNo (mNo (mE.mpr ⟨h3,h4.2⟩))⟩
    ·intro a b hab
     by_cases hap: a=p
     ·rw[hap] at hab ⊢;have hbp: b≠p:=hab.ne';have hblq: b=l∨b=q:=(hp b).mp hab
      have hbs: b≠s:=fun e => by rcases hblq with rfl|rfl;exact hlnc (e ▸ hs);exact hsq e.symm
      have hb_no: d2.owns b p=false:=by cases h: d2.owns b p;rfl;exact absurd (hv2.2.2.1.1 b p h).1.symm (hp_iso b)
      dsimp[d];simp[hblq,hbp,hbs,hb_no,hsp.symm]
     ·by_cases hbp: b=p
      ·rw[hbp] at hab ⊢;have halq: a=l∨a=q:=(hp a).mp hab.symm
       have has: a≠s:=fun e => by rcases halq with rfl|rfl;exact hlnc (e ▸ hs);exact hsq e.symm
       have ha_no: d2.owns a p=false:=by cases h: d2.owns a p;rfl;exact absurd (hv2.2.2.1.1 a p h).1.symm (hp_iso a)
       dsimp[d];simp[halq,hap,has,ha_no,hsp.symm]
      ·have hal: a≠l:=fun e => hbp ((hl b).mp (e ▸ hab))
       have hbl: b≠l:=fun e => hap ((hl a).mp (e ▸ hab.symm))
       have hK2ab: K2.Adj a b:=(hK2 a b).mpr ⟨hab,hal,hap,hbl,hbp⟩
       by_cases has: a=s
       ·rw[has] at hab hK2ab hap ⊢
        by_cases hbq: b=q
        ·rw[hbq] at hbp ⊢;dsimp[d];simp[hap,hbp,hsq]
        ·have ha_no: d2.owns s b=false:=by cases h: d2.owns s b;rfl;exact absurd (hs_only b h) hbq
         have hb_yes: d2.owns b s=true:=by
          have:=hv2.2.2.1.2 s b hK2ab;rw[ha_no] at this;cases h: d2.owns b s;rw[h] at this;exact absurd rfl this;rfl
         dsimp[d];simp[hap,hbp,hbq,hab.ne',hb_yes]
       ·by_cases hbs: b=s
        ·rw[hbs] at hab hK2ab hbp ⊢
         by_cases haq: a=q
         ·rw[haq] at hap ⊢;dsimp[d];simp[hap,hbp,hsq.symm]
         ·have hb_no: d2.owns s a=false:=by cases h: d2.owns s a;rfl;exact absurd (hs_only a h) haq
          have ha_yes: d2.owns a s=true:=by
           have:=hv2.2.2.1.2 a s hK2ab;rw[hb_no] at this;cases h: d2.owns a s;rw[h] at this;exact absurd rfl this;rfl
          dsimp[d];simp[hap,hbp,haq,hab.ne,ha_yes]
        ·dsimp[d];simp[hap,hbp,has,hbs,hv2.2.2.1.2 a b hK2ab]
   ·
    intro a b hab;dsimp[d] at hab;split_ifs at hab with haq
    ·have hbp: b=p:=(osi hab).symm;rw[haq,hbp];exact ⟨mNo (mNs q _),by simp[d]⟩
    ·have h1:=hv2.2.2.2.1 a b hab
     have has: a≠s:=fun e => by rw[e,hs_free] at hab;cases hab
     have hbs: b≠s:=fun e => hqnc (hs_only a (e ▸ h1.2) ▸ h1.1)
     refine ⟨mNo (mNo (mE.mpr ⟨has,h1.1⟩)),?_⟩
     dsimp[d]
     by_cases h1' : b=p∧(a=l∨a=q)
     ·simp[h1']
     ·simp only[h1',↓reduceIte]
      by_cases h2' : b=q∧a=s
      ·simp[h2']
      ·simp only[h2',↓reduceIte,hbs];exact h1.2
   ·
    intro j hj
    by_cases hje: j=jl
    ·subst hje;right;exact ⟨p,by simp[d,covC],by simp[d,roleC],fun h => by simp[d,roleC] at h⟩
    ·by_cases hre: j=r
     ·subst hre;right;exact ⟨p,by simp[d,covC],by simp[d,roleC,Nat.ne_of_gt hjr],fun _ => by simp[d]⟩
     ·by_cases hjue: j=li2 jl r ju
      ·subst hjue;right;exact ⟨p,by simp[d,covC],by simp[d,hrole_ju],fun h => by simp[d,hrole_ju] at h⟩
      ·by_cases hjbse: j=li2 jl r jbs
       ·subst hjbse;right;exact ⟨q,by simp[d,covC],by simp[d,hrole_jbs],fun _ => by dsimp[d];simp[hpq.symm,hbws,lw2g]⟩
       ·obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
        have h1' : j' ≠ ju:=fun e => hjue (by rw[e])
        have h2' : j' ≠ jbs:=fun e => hjbse (by rw[e])
        have hr_eq: d.role (li2 jl r j')=d2.role j' := hrln j' h1' h2'
        by_cases htop_j: (d2.role j').1=Kind.top
        ·exact Or.inl (by rw[hr_eq];exact htop_j)
        ·rcases hv2.2.2.2.2.1 j' (by omega) with htop_j' | ⟨t,ht,e1,e2⟩
         ·exact absurd htop_j' htop_j
         ·have hts: t≠s:=by
           intro e;rw[e] at e1 e2
           cases hkr: (d2.role j').1 with
           | top => exact htop_j hkr
           | b => have := e2 hkr;rw[hbws] at this;exact h2' (by omega)
           | z =>
            have: j' ∈ gatesOf d2 C2 Kind.z s.val := mF.mpr ⟨mR.mpr (by omega),Prod.ext hkr e1⟩
            rw[hZse] at this;cases this
           | o =>
            have: j' ∈ gatesOf d2 C2 Kind.o s.val := mF.mpr ⟨mR.mpr (by omega),Prod.ext hkr e1⟩
            rw[hOse] at this;cases this
          have htp: t≠p:=fun e => hpnc (e ▸ ht)
          have htq: t≠q:=fun e => hqnc (e ▸ ht)
          right;refine ⟨t,mNo (mNo (mE.mpr ⟨hts,ht⟩)),
           by rw[hr_eq];exact e1,fun hk => ?_⟩
          rw[hr_eq] at hk;dsimp[d];simp only[htp,htq,↓reduceIte];rw[e2 hk,lw2g]
   ·
    intro t ht
    by_cases htp: t=p
    ·rw[htp]
     refine ⟨?_,?_,?_,?_⟩
     ·refine ⟨r,hr,by simp[d],by simp[d,roleC,Nat.ne_of_gt hjr],hro0,?_⟩
      dsimp[d];simp only[↓reduceIte,hu_lw];exact hri0.symm
     ·have hG: gatesOf d C Kind.z p.val={li2 jl r ju}:=by
       ext j;simp only[gatesOf,d,mF,mR,mS]
       constructor
       ·rintro ⟨hj,hrj⟩
        by_contra hjue
        have hje: j≠jl:=fun e => by rw[e] at hrj;simp[roleC] at hrj
        have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleC,Nat.ne_of_gt hjr] at hrj
        have hjbse: j≠li2 jl r jbs:=fun e => by rw[e,hrole_jbs] at hrj;simp at hrj
        obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
        rw[hrln j' (fun e => hjue (by rw[e])) (fun e => hjbse (by rw[e]))] at hrj
        rcases hv2.2.2.2.2.1 j' (by omega) with htop_j|⟨s',hs',e1,_⟩
        ·rw[hrj] at htop_j;cases htop_j
        ·rw[hrj] at e1;exact hpnc (Fin.ext e1.symm ▸ hs')
       ·rintro rfl;exact ⟨(li2lt hjr hr (by omega): _ < C.gates.length),hrole_ju⟩
      have hL: zLeaves d p={p.val,lw2 n jl r (d2.bw s)}:=by
       ext w;simp only[zLeaves,d,mN,mI,mF,mS]
       constructor
       ·rintro (rfl|⟨t',⟨_,hst⟩,rfl⟩)
        ·exact Or.inl rfl
        ·split_ifs at hst with htq
         ·right;rw[htq];simp[hpq.symm]
         ·exact absurd (hv2.2.2.1.1 p t' (hv2.2.2.2.1 t' p hst).2).1 (hp_iso t')
       ·rintro (rfl|rfl)
        ·exact Or.inl rfl
        ·right;exact ⟨q,⟨by simp[covC],by simp⟩,by simp[hpq.symm]⟩
      rw[hG,hL];dsimp[d];simp only[↓reduceIte,hu2_eq_ju,lw2g]
      have hne_p_bw: p.val≠lw2 n jl r (d2.bw s):=by
       rw[hbws,lw2g];have := p.isLt;omega
      have hne_p_ju: p.val≠n+li2 jl r ju:=by have:=p.isLt;omega
      have hne_bw_ju: lw2 n jl r (d2.bw s)≠n+li2 jl r ju:=by
       rw[←lw2g];intro e;have := lw2j n jl r e;exact (htop.2.1 (d2.bw s) (hv0_eq ▸ hLu_sub hv0_Lu)).1 ⟨by omega,by rw[this,ascl];exact hju_tg⟩
      have hjnC' : (gateAt C (li2 jl r ju)).inputs=[p.val,lw2 n jl r (d2.bw s)] ∨
        (gateAt C (li2 jl r ju)).inputs=[lw2 n jl r (d2.bw s),p.val] := hv0_eq ▸ hjnC
      refine ⟨?_,?_,?_,?_⟩
      ·intro j hj;rw[mS.mp hj]
       refine ⟨by rw[←hjlf.1,hju_op],by rcases hjnC' with h|h <;> simp[h],fun i hi => ?_⟩
       rcases hjnC' with h|h <;> rw[h] at hi <;> simp at hi <;> rcases hi with rfl|rfl <;> exact Or.inl (by simp)
      ·intro w hw;simp only[mN,mS] at hw
       rcases hw with rfl|rfl
       ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
        simp only[readsIn,sum_singleton,hne_p_ju,↓reduceIte]
        rcases hjnC' with h|h <;> rw[h] <;> simp[hne_p_bw,hne_p_bw.symm]
       ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
        simp only[readsIn,sum_singleton,hne_bw_ju,↓reduceIte]
        rcases hjnC' with h|h <;> rw[h] <;> simp[hne_p_bw,hne_p_bw.symm]
      ·intro j hj;rw[mS.mp hj];simp only[readsIn,sum_singleton,↓reduceIte,lcz]
       rcases hjnC' with h|h <;> rw[h] <;> simp[hne_p_ju.symm,hne_bw_ju.symm]
      ·simp
     ·have hG: gatesOf d C Kind.o p.val={jl}:=by
       ext j;simp only[gatesOf,d,mF,mR,mS]
       constructor
       ·rintro ⟨hj,hrj⟩
        by_contra hje
        have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleC,Nat.ne_of_gt hjr] at hrj
        have hjue: j≠li2 jl r ju:=fun e => by rw[e,hrole_ju] at hrj;simp at hrj
        have hjbse: j≠li2 jl r jbs:=fun e => by rw[e,hrole_jbs] at hrj;simp at hrj
        obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
        rw[hrln j' (fun e => hjue (by rw[e])) (fun e => hjbse (by rw[e]))] at hrj
        rcases hv2.2.2.2.2.1 j' (by omega) with htop_j|⟨s',hs',e1,_⟩
        ·rw[hrj] at htop_j;cases htop_j
        ·rw[hrj] at e1;exact hpnc (Fin.ext e1.symm ▸ hs')
       ·rintro rfl;exact ⟨by omega,by simp[roleC]⟩
      have hL: oLeaves d p={l.val,q.val}:=by
       ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
        mN,mS]
       constructor
       ·rintro ⟨v,hown,rfl⟩
        simp only[hpq,hsp.symm,false_and,↓reduceIte,true_and] at hown
        split_ifs at hown with h1
        ·rcases h1 with rfl|rfl
         ·left;simp
         ·right;simp[hql]
        ·exact absurd (hv2.2.2.1.1 p v hown).1 (hp_iso v)
       ·rintro (rfl|rfl)
        ·exact ⟨l,by simp,by simp⟩
        ·exact ⟨q,by simp,by simp[hql]⟩
      rw[hG,hL];dsimp[d];simp only[↓reduceIte];have hjli' : (gateAt C jl).inputs=[l.val,q.val]∨(gateAt C jl).inputs=[q.val,l.val]:=hwl_eq_qv ▸ hjli
      have hq_ne_jl: q.val≠n+jl:=by have:=q.isLt;omega
      have hl_ne_jl: l.val≠n+jl:=by have:=l.isLt;omega
      refine ⟨?_,?_,?_,?_⟩
      ·intro j hj;rw[mS.mp hj]
       refine ⟨hjlo,by rcases hjli' with h|h <;> simp[h],fun i hi => ?_⟩
       rcases hjli' with h|h <;> rw[h] at hi <;> simp at hi <;> rcases hi with rfl|rfl <;> exact Or.inl (by simp)
      ·intro w hw;simp only[mN,mS] at hw
       rcases hw with rfl|rfl
       ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
        simp only[readsIn,sum_singleton,hl_ne_jl,↓reduceIte]
        rcases hjli' with h|h <;> rw[h] <;> simp[Fin.val_ne_of_ne hql,Fin.val_ne_of_ne hql.symm]
       ·refine ⟨by intro ⟨h1,h2⟩;rw[mS] at h2;omega,?_⟩
        simp only[readsIn,sum_singleton,hq_ne_jl,↓reduceIte]
        rcases hjli' with h|h <;> rw[h] <;> simp[Fin.val_ne_of_ne hql,Fin.val_ne_of_ne hql.symm]
      ·intro j hj;rw[mS.mp hj];simp only[readsIn,sum_singleton,↓reduceIte,lcz]
       rcases hjli' with h|h <;> rw[h] <;> simp[hl_ne_jl.symm,hq_ne_jl.symm]
      ·simp
     ·intro v hown;dsimp[d] at hown
      have hvlq: v=l∨v=q:=by
       simp only[hpq,hsp.symm,false_and,↓reduceIte,true_and] at hown
       split_ifs at hown with h1
       ·exact h1
       ·exact absurd (hv2.2.2.1.1 p v hown).1 (hp_iso v)
      rcases hvlq with hvl|hvq
      ·rw[hvl]
       have hl_not: l∉covC:=by simp[covC,hlp,hql.symm,hlnc]
       unfold LamOK;dsimp[d];simp[hl_not]
      ·rw[hvq];have hq_in: q∈covC:=mNo (mNs q _);unfold LamOK;dsimp[d];simp only[hq_in,↓reduceIte,hql,hpq.symm]
       exact ⟨by rw[cfi C d q];exact hq_in,Or.inl trivial,fun _ => trivial⟩
    ·by_cases htq: t=q
     ·rw[htq]
      refine ⟨?_,?_,?_,?_⟩
      ·
       have hno:=hnt0 jbs hjbs (by rw[hrbs];intro hc;cases hc);have hlif:=r2l C hcl hrb hjr hr hu jbs (by omega);have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jbs (by omega) hno
       refine ⟨li2 jl r jbs,(li2lt hjr hr (by omega): _ < C.gates.length),
        by dsimp[d];simp[hpq.symm,hbws,lw2g],
        by dsimp[d];exact hrole_jbs,by rw[←hlif.1,hop_bs],?_⟩
       rw[hinp];dsimp[d];simp only[hpq.symm,↓reduceIte];rw[hzrs,hors] at hin_bs
       rcases hin_bs with h|h <;> rw[h] <;> simp[lw2i n jl r s.val s.isLt,lw2i n jl r q.val q.isLt]
      ·
       have hG: gatesOf d C Kind.z q.val = ∅ := by
        rw[hgn Kind.z q.val (by simp) (by simp) (by simp) (fun h => hpq (Fin.ext (pei.mp h).2).symm) (by simp) (Fin.val_ne_of_ne hsq.symm)]
        have hE: gatesOf d2 C2 Kind.z q.val = ∅ := by
         ext j';simp only[gatesOf,mF,mR,notMem_empty,iff_false,not_and]
         intro hj' hrj'
         rcases hv2.2.2.2.2.1 j' hj' with htop_j|⟨s',hs',e1,_⟩
         ·rw[hrj'] at htop_j;cases htop_j
         ·rw[hrj'] at e1;exact hqnc (Fin.ext e1.symm ▸ hs')
        simp[hE]
       have hL: zLeaves d q={q.val}:=by
        ext w;simp only[zLeaves,d,mN,mI,mF,mS,or_iff_left_iff_imp]
        rintro ⟨t',⟨_,hst⟩,_⟩
        split_ifs at hst with htq'
        ·cases hst;exact absurd rfl hpq
        ·exact absurd (hv2.2.2.1.1 q t' (hv2.2.2.2.1 t' q hst).2).2 hqnc
       rw[hG,hL];dsimp[d];simp only[hpq.symm,↓reduceIte]
       refine ⟨by simp,fun w hw => by rw[mS.mp hw];simp[readsIn],by simp,by simp⟩
      ·
       have hG: gatesOf d C Kind.o q.val = ∅ := by
        rw[hgn Kind.o q.val (by simp) (fun h => hpq (Fin.ext (pei.mp h).2).symm) (by simp) (by simp) (by simp) (Fin.val_ne_of_ne hsq.symm)]
        have hE: gatesOf d2 C2 Kind.o q.val = ∅ := by
         ext j';simp only[gatesOf,mF,mR,notMem_empty,iff_false,not_and]
         intro hj' hrj'
         rcases hv2.2.2.2.2.1 j' hj' with htop_j|⟨s',hs',e1,_⟩
         ·rw[hrj'] at htop_j;cases htop_j
         ·rw[hrj'] at e1;exact hqnc (Fin.ext e1.symm ▸ hs')
        simp[hE]
       have hL: oLeaves d q={s.val}:=by
        ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
         hpq.symm,false_and,↓reduceIte,mS]
        constructor
        ·rintro ⟨v,hown,rfl⟩;rfl
        ·rintro rfl;exact ⟨s,by simp,rfl⟩
       rw[hG,hL];dsimp[d];simp only[hpq.symm,↓reduceIte]
       refine ⟨by simp,fun w hw => by rw[mS.mp hw];simp[readsIn],by simp,by simp⟩
      ·intro v hown;dsimp[d] at hown
       have hvs: v=s:=by
        simp only[hpq.symm,hsq.symm,false_and,↓reduceIte,true_and] at hown
        split_ifs at hown with h2
        ·exact h2
        ·exact absurd (hv2.2.2.1.1 q v hown).2 hqnc
       rw[hvs]
       have hs_not: s∉covC:=by simp[covC,hsp,hsq]
       unfold LamOK;dsimp[d];simp[hs_not,hpq.symm]
     ·
      have ht_er: t∈d2.cover.erase s:=by
       simp only[d,covC,mN] at ht
       rcases ht with rfl|rfl|h;exact absurd rfl htp;exact absurd rfl htq;exact h
      obtain ⟨hts,ht2⟩:=mE.mp ht_er
      refine ⟨?_,?_,?_,?_⟩
      ·obtain ⟨jb,hjb,hbw,hrb_t,hop,hin⟩:=(hv2.2.2.2.2.2.1 t ht2).1
       have hne_ju: jb≠ju:=fun e => by have:=(mF.mp hju_tg).2;rw[←e,hrb_t] at this;cases this
       have hne_jbs: jb≠jbs:=fun e => hts (by rw[e,hrbs] at hrb_t;exact Fin.ext (pei.mp hrb_t).2.symm)
       have hno:=hnt0 jb hjb (by rw[hrb_t];intro hc;cases hc);have hlif:=r2l C hcl hrb hjr hr hu jb (by omega);have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jb (by omega) hno
       refine ⟨li2 jl r jb,(li2lt hjr hr (by omega): _ < C.gates.length),
        by dsimp[d];simp[htp,htq,hbw,lw2g],
        by dsimp[d];rw[hrln jb hne_ju hne_jbs,hrb_t],
        by rw[←hlif.1,hop],?_⟩
       rw[hinp];rcases hin with h|h <;> rw[h] <;> simp[d,htp,htq]
      ·have hG: gatesOf d C Kind.z t.val=(gatesOf d2 C2 Kind.z t.val).image (li2 jl r) :=
        hgn Kind.z t.val (by simp) (by simp) (by simp) (fun h => htp (Fin.ext (pei.mp h).2)) (by simp) (Fin.val_ne_of_ne hts)
       have hL: zLeaves d t=(zLeaves d2 t).image (lw2 n jl r):=by
        ext w;simp only[zLeaves,d,mN,mI,mF]
        constructor
        ·rintro (rfl|⟨u',⟨hu',hut⟩,rfl⟩)
         ·exact ⟨t.val,Or.inl rfl,lw2i n jl r t.val t.isLt⟩
         ·split_ifs at hut with huq
          ·cases hut;exact absurd rfl htp
          ·have hu2: u' ∈ d2.cover:=(hv2.2.2.2.1 u' t hut).1
           have hup: u' ≠ p:=fun e => hpnc (e ▸ hu2)
           simp only[hup,huq,↓reduceIte];exact ⟨d2.bw u',Or.inr ⟨u',⟨hu2,hut⟩,rfl⟩,rfl⟩
        ·rintro ⟨_,rfl|⟨u',⟨hu',hut⟩,rfl⟩,rfl⟩
         ·exact Or.inl (lw2i n jl r t.val t.isLt)
         ·have hup: u' ≠ p:=fun e => hpnc (e ▸ hu')
          have huq: u' ≠ q:=fun e => hqnc (e ▸ hu')
          have hus: u' ≠ s:=fun e => by rw[e,hs_free] at hut;cases hut
          exact Or.inr ⟨u',⟨mNo (mNo (mE.mpr ⟨hus,hu'⟩)),
           by simp[huq,hut]⟩,by simp[hup,huq]⟩
       rw[hG,hL];dsimp[d];simp only[htp,htq,↓reduceIte]
       exact ot2u C hcl hrb hjr hr hu hune hon0 hur (hv2.2.2.2.2.2.1 t ht2).2.1
        (fun j' hj' => by have := mR.mp (mF.mp hj').1;omega)
        (fun j' hj' => hnt0 j' (mR.mp (mF.mp hj').1)
         (by rw[(mF.mp hj').2];intro hc;cases hc))
      ·have hG: gatesOf d C Kind.o t.val=(gatesOf d2 C2 Kind.o t.val).image (li2 jl r) :=
        hgn Kind.o t.val (by simp) (fun h => htp (Fin.ext (pei.mp h).2)) (by simp) (by simp) (by simp) (Fin.val_ne_of_ne hts)
       have hL: oLeaves d t=(oLeaves d2 t).image (lw2 n jl r):=by
        ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
         htp,htq,hts,false_and,↓reduceIte]
        constructor
        ·rintro ⟨v,hown,rfl⟩;exact ⟨d2.lam t v,⟨v,hown,rfl⟩,rfl⟩
        ·rintro ⟨_,⟨v,hown,rfl⟩,rfl⟩;exact ⟨v,hown,rfl⟩
       rw[hG,hL];dsimp[d];simp only[htp,htq,↓reduceIte]
       exact ot2u C hcl hrb hjr hr hu hune hon0 hur (hv2.2.2.2.2.2.1 t ht2).2.2.1
        (fun j' hj' => by have := mR.mp (mF.mp hj').1;omega)
        (fun j' hj' => hnt0 j' (mR.mp (mF.mp hj').1)
         (by rw[(mF.mp hj').2];intro hc;cases hc))
      ·intro v hown;dsimp[d] at hown;simp only[htp,htq,hts,false_and,↓reduceIte] at hown
       have hvp: v≠p:=fun e => hp_iso t (e ▸ (hv2.2.2.1.1 t v hown).1).symm
       have hlam:=(hv2.2.2.2.2.2.1 t ht2).2.2.2 v hown;unfold LamOK at hlam ⊢;dsimp[d];simp only[htp,htq,↓reduceIte]
       by_cases hvq: v=q
       ·rw[hvq] at hlam ⊢;simp only[hqnc,↓reduceIte] at hlam;simp only[covC,mNo (mNs q _),↓reduceIte];rw[hlam,lw2i n jl r q.val q.isLt]
        exact ⟨by rw[cfi C d q];simp[d,covC],Or.inl rfl,fun h => by simp at h;exact absurd h.symm htp⟩
       ·by_cases hvs: v=s
        ·rw[hvs] at hlam ⊢;simp only[hs,↓reduceIte] at hlam
         have hs_not: s∉covC:=by simp[covC,hsp,hsq]
         simp only[hs_not,↓reduceIte]
         rcases hlam.2.1 with h|⟨jz,hjz,_,hrz⟩
         ·rw[h,lw2i n jl r s.val s.isLt]
         ·exfalso;have: jz∈gatesOf d2 C2 Kind.z s.val := mF.mpr ⟨mR.mpr hjz,hrz⟩
          rw[hZse] at this;cases this
        ·by_cases hvc: v∈d2.cover
         ·have hvc' : v∈covC:=mNo (mNo (mE.mpr ⟨hvs,hvc⟩));simp only[hvc,hvc',↓reduceIte] at hlam ⊢
          refine ⟨?_,?_,?_⟩
          ·exact cf2 (d := d) C hcl hrb hjr hr hu hune hon0 hur hv2 (d2.cover.erase s)
            (erase_subset _ _) (fun x hx => mNo (mNo hx))
            (fun j' hj' hrz => ⟨hnt0 j' (by omega) (by rw[hrz];intro hc;cases hc),by
             have h1' : j' ≠ ju:=fun e => by have:=(mF.mp hju_tg).2;rw[←e,hrz] at this;cases this
             have h2' : j' ≠ jbs:=fun e => by rw[e,hrbs] at hrz;cases hrz
             dsimp[d];rw[hrln j' h1' h2',hrz]⟩)
            v (mE.mpr ⟨hvs,hvc⟩) (d2.lam t v) hlam.1 (by
             rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
             ·exact Or.inl h
             ·exact Or.inr ⟨jz,by omega,h1,h2⟩)
          ·rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
           ·exact Or.inl (by rw[h,lw2i n jl r v.val v.isLt])
           ·have h1' : jz≠ju:=fun e => by have:=(mF.mp hju_tg).2;rw[←e,h2] at this;cases this
            have h2' : jz≠jbs:=fun e => by rw[e,hrbs] at h2;cases h2
            exact Or.inr ⟨li2 jl r jz,(li2lt hjr hr (by omega): _ < C.gates.length),
             by rw[h1,lw2g],by rw[hrln jz h1' h2',h2]⟩
          ·intro htie;simp only[hvq,↓reduceIte] at htie;simp only[hvp,hvq,↓reduceIte];rw[hlam.2.2 htie]
         ·have hvc' : v∉covC:=by simp[covC,hvp,hvq,hvc]
          simp only[hvc,hvc',↓reduceIte] at hlam ⊢;rw[hlam,lw2i n jl r v.val v.isLt]
   ·
    have hG: topGates d C=((topGates d2 C2).erase ju).image (li2 jl r):=by
     ext j;simp only[topGates,d,mF,mR,mI,mE]
     constructor
     ·rintro ⟨hj,hrj⟩
      have hje: j≠jl:=fun e => by rw[e] at hrj;simp[roleC] at hrj
      have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleC,Nat.ne_of_gt hjr] at hrj
      have hjue: j≠li2 jl r ju:=fun e => by rw[e,hrole_ju] at hrj;cases hrj
      have hjbse: j≠li2 jl r jbs:=fun e => by rw[e,hrole_jbs] at hrj;cases hrj
      obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
      have h1' : j' ≠ ju:=fun e => hjue (by rw[e])
      have h2' : j' ≠ jbs:=fun e => hjbse (by rw[e])
      exact ⟨j',⟨h1',⟨by omega,by rw[←hrln j' h1' h2'];exact hrj⟩⟩,rfl⟩
     ·rintro ⟨j',⟨h1',⟨hj',hrj'⟩⟩,rfl⟩
      have h2' : j' ≠ jbs:=fun e => by rw[e,hrbs] at hrj';cases hrj'
      exact ⟨(li2lt hjr hr (by omega): _ < C.gates.length),by rw[hrln j' h1' h2',hrj']⟩
    have hL: topLeaves d A=insert (n+r) ((((topLeaves d2 (insert p A)).erase p.val).erase v0).image (lw2 n jl r)):=by
     ext w;simp only[topLeaves,d,mU,mI,mF,
      mN,mE]
     constructor
     ·rintro (⟨a,ha,rfl⟩ | ⟨u',⟨hu',hut⟩,rfl⟩)
      ·right
       have hne_v0: a.val≠v0:=by rw[hv0_eq,hbws];have:=a.isLt;omega
       exact ⟨a.val,⟨hne_v0,fun e => hpnA (Fin.ext e ▸ ha),Or.inl ⟨a,Or.inr ha,rfl⟩⟩,lw2i n jl r a.val a.isLt⟩
      ·by_cases hup: u' = p
       ·left;simp[hup]
       ·right
        have huq: u' ≠ q:=fun e => by rw[e] at hut;simp at hut
        simp only[huq,↓reduceIte] at hut;simp only[hup,huq,↓reduceIte]
        have hu_er: u' ∈ d2.cover.erase s:=by
         simp only[covC,mN] at hu'
         rcases hu' with rfl|rfl|h;exact absurd rfl hup;exact absurd rfl huq;exact h
        obtain ⟨hus,hu2⟩:=mE.mp hu_er;obtain ⟨jb,_,hbw,_,_,_⟩:=(hv2.2.2.2.2.2.1 u' hu2).1
        have hne_v0: d2.bw u' ≠ v0:=by rw[hv0_eq];exact fun e => hus (bw_injOn hv2 d2.cover (Subset.refl _) hu2 hs e)
        exact ⟨d2.bw u',⟨hne_v0,by omega,Or.inr ⟨u',⟨hu2,hut⟩,rfl⟩⟩,rfl⟩
     ·rintro (rfl|⟨w',⟨hw'ne_v0,hw'ne_p,hw'tl⟩,rfl⟩)
      ·right;exact ⟨p,⟨by simp[covC],by
        simp only[hpq,↓reduceIte]
        cases h: d2.tie p with
        | none => rfl
        | some t => exfalso;exact hpnc (hv2.2.2.2.1 p t h).1⟩,by simp⟩
      ·rcases hw'tl with ⟨a,rfl|ha,rfl⟩ | ⟨u',⟨hu',hut⟩,rfl⟩
       ·exact absurd rfl hw'ne_p
       ·left;exact ⟨a,ha,(lw2i n jl r a.val a.isLt).symm⟩
       ·right
        have hup: u' ≠ p:=fun e => hpnc (e ▸ hu')
        have huq: u' ≠ q:=fun e => hqnc (e ▸ hu')
        have hus: u' ≠ s:=fun e => hw'ne_v0 (hv0_eq ▸ congrArg d2.bw e)
        exact ⟨u',⟨mNo (mNo (mE.mpr ⟨hus,hu'⟩)),
         by simp[huq,hut]⟩,by simp[hup,huq]⟩
    rw[hG,hL];exact htCl
lemma ot2i {n jl r u: ℕ} (C: Circuit) (hrb: ReadsBack n C)
  (hjr: jl < r) (hr: r < C.gates.length) (hu: u < n+r)
  (hune: u≠n+jl) (hon0: C.output≠n+jl)
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  (hro0: (gateAt C r).op=GateOp.or)
  (hri0: (gateAt C r).inputs=[n+jl,u]∨(gateAt C r).inputs=[u,n+jl])
  {G1 L1: Finset ℕ} {ρ1: ℕ}
  (ht: IsOrTree n ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ G1 L1 ρ1)
  (hGlt: ∀ j' ∈ G1,j' < C.gates.length - 2)
  (hcase: (rd n jl 0 u = ρ1 ∧ ∀ j' ∈ G1,n+r∉(gateAt C (li2 jl r j')).inputs) ∨
   (rd n jl 0 u ≠ ρ1 ∧ ∃ q0' ∈ G1,n+r∈(gateAt C (li2 jl r q0')).inputs ∧
    ∀ j' ∈ G1,j' ≠ q0' → n+r∉(gateAt C (li2 jl r j')).inputs)) :
  IsOrTree n C (insert r (G1.image (li2 jl r)))
   (insert (n+jl) (L1.image (lw2 n jl r)))
   (if rd n jl 0 u = ρ1 then n+r else lw2 n jl r ρ1):=by
 set Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩
 have hlm: Cm0.gates.length=C.gates.length - 1:=by
  have:=rdel_length n r u C.gates hr;simp[Cm0];omega
 have hrb_mid: ReadsBack n Cm0:=by
  intro j hj i hi;have hlif:=r1l u C hrb hr j (by omega);rw[hlif.2] at hi;obtain ⟨a,ha,rfl⟩:=lmm.mp hi;have halt: a < n+li1 r j:=hrb (li1 r j) (by unfold li1;split_ifs <;> omega) a ha;unfold rd li1 at *;split_ifs at * <;> omega
 have hmid_no:=rmnj C hrb hjr hr hune hon0 hur
 have ht_mid: IsOrTree n Cm0 (G1.image (li1 jl)) (L1.image (lw1 n jl)) (lw1 n jl ρ1) :=
  ot1u Cm0 hrb_mid (by omega) ht (fun j' hj' => by have := hGlt j' hj';omega)
   (fun j' hj' => hmid_no.2 (li1 jl j') (by
    have:=hGlt j' hj';have: li1 jl j' < Cm0.gates.length:=(by unfold li1;split_ifs <;> omega);exact this))
 have hGim_lt: ∀ k∈G1.image (li1 jl),k < C.gates.length - 1:=by
  intro k hk;obtain ⟨j',hj',rfl⟩ := mI.mp hk
  have:=hGlt j' hj';unfold li1;split_ifs <;> omega
 have hlnotL: n+jl∉L1.image (lw1 n jl):=by
  intro h;obtain ⟨w',_,he⟩ := mI.mp h;exact lw1n n jl w' he
 have hlnotG: ∀ k∈G1.image (li1 jl),n+k≠n+jl:=by
  intro k hk he;obtain ⟨j',_,rfl⟩ := mI.mp hk;exact li1n jl j' (by omega)
 have hG_im: (G1.image (li1 jl)).image (li1 r)=G1.image (li2 jl r):=by
  ext k;simp[li2]
 have hL_im: (L1.image (lw1 n jl)).image (lw1 n r)=L1.image (lw2 n jl r):=by
  ext w;simp[lw2]
 have hu_eq: lw1 n jl (rd n jl 0 u)=u:=lw1r n jl 0 u hune
 rcases hcase with ⟨huρ,hno⟩ | ⟨hne,q0',hq0',hq0_read,hnoo⟩
 ·rw[if_pos huρ]
  have hρ_eq: lw1 n jl ρ1=u:=by rw[←huρ,hu_eq]
  rw[hρ_eq] at ht_mid
  have hres:=ot1ir C hrb hr hu (n+jl) (by omega) hune hro0 hri0 ht_mid hGim_lt
   (fun k hk => by obtain ⟨j',hj',rfl⟩ := mI.mp hk;exact hno j' hj') hlnotL hlnotG
  rwa[hG_im,hL_im] at hres
 ·rw[if_neg hne]
  have hres:=ot1im C hrb hr hu (n+jl) (by omega) hune hro0 hri0 ht_mid hGim_lt
   (li1 jl q0') (mI.mpr ⟨q0',hq0',rfl⟩) hq0_read
   (fun k hk hkne => by
    obtain ⟨j',hj',rfl⟩:=mI.mp hk
    exact hnoo j' hj' (fun e => hkne (by rw[e])))
   hlnotL hlnotG
  rwa[hG_im,hL_im] at hres
set_option maxHeartbeats 1600000 in
lemma nlB2 {n jl wl r u: ℕ} (hn: 0 < n)
  {K K1: SimpleGraph (Fin n)} [DecidableRel K.Adj] [DecidableRel K1.Adj]
  {A: Finset (Fin n)} {l p q: Fin n}
  (hA: ∀ a∈A,∀ v: Fin n,¬ K.Adj a v)
  (hl: ∀ v: Fin n,K.Adj l v↔v=p)
  (hql: q≠l)
  (hp: ∀ v: Fin n,K.Adj p v↔v=l∨v=q)
  (hK1: ∀ u v: Fin n,K1.Adj u v↔K.Adj u v∧u≠l∧v≠l)
  (C: Circuit) (hcl: CL n C.gates) (hrb: ReadsBack n C)
  (hcf: circuitFun n C=graphFun K A)
  (hjr: jl < r) (hr: r < C.gates.length)
  (hw_l: wl < n+jl) (hwne: wl≠l.val)
  (hu: u < n+r) (hune: u≠n+jl) (hu_ne_l: u≠l.val) (hon0: C.output≠n+jl)
  (hjlo: (gateAt C jl).op=GateOp.and)
  (hjli: (gateAt C jl).inputs=[l.val,wl]∨(gateAt C jl).inputs=[wl,l.val])
  (hro0: (gateAt C r).op=GateOp.or)
  (hri0: (gateAt C r).inputs=[n+jl,u]∨(gateAt C r).inputs=[u,n+jl])
  (hur: ∀ q' < C.gates.length,n+jl∈(gateAt C q').inputs → q' = r)
  {d1: NCCData n}
  (hv1: Valid n K1 A
   ⟨rdel n jl 0 (rdel n r u C.gates),rd n jl 0 (rd n r u C.output)⟩ d1)
  (htK1: ∀ T: Finset (Fin n),K.IsVertexCover (T: Set (Fin n)) → d1.cover.card+1 ≤ T.card) :
  IsNestedCoverCircuit n K A C:=by
 classical
 set Cm0: Circuit:=⟨rdel n r u C.gates,rd n r u C.output⟩;set C1: Circuit:=⟨rdel n jl 0 Cm0.gates,rd n jl 0 Cm0.output⟩;have hrb1:=hv1.1;have hmc1:=hv1.2.1;have hown1:=hv1.2.2.1;have htie1:=hv1.2.2.2.1;have hrol1:=hv1.2.2.2.2.1;have h1c:=hv1.2.2.2.2.2.1;have htop1:=hv1.2.2.2.2.2.2;have hcl1: CL n C1.gates:=ncc_clean hv1
 have hlm: Cm0.gates.length=C.gates.length - 1:=by
  have:=rdel_length n r u C.gates hr;simp[Cm0];omega
 have hlen1: C1.gates.length=C.gates.length - 2:=by
  have:=rdel_length n jl 0 Cm0.gates (by omega);simp[C1] at this ⊢;omega
 have hlp: l≠p:=((hl p).mpr rfl).ne;have hpq: p≠q:=((hp q).mpr (Or.inr rfl)).ne
 have hlnA: l∉A:=fun h => hA l h p ((hl p).mpr rfl)
 have hpnA: p∉A:=fun h => hA p h l ((hl p).mpr rfl).symm
 have hqnA: q∉A:=fun h => hA q h p ((hp q).mpr (Or.inr rfl)).symm
 have hl_iso: ∀ v: Fin n,¬ K1.Adj l v:=fun v h => ((hK1 l v).mp h).2.1 rfl
 have hlnc: l∉d1.cover:=fun h => by
  obtain ⟨v,hown,_⟩:=coo hv1 l h;exact hl_iso v (hown1.1 l v hown).1
 have hpnc: p∉d1.cover:=by
  intro hpc
  have hcovK: K.IsVertexCover (d1.cover: Set (Fin n)):=by
   intro a b hab
   by_cases hal: a=l
   ·right;rw[(hl b).mp (hal ▸ hab)];exact mC.mpr hpc
   ·by_cases hbl: b=l
    ·left;rw[(hl a).mp (hbl ▸ hab.symm)];exact mC.mpr hpc
    ·exact hmc1.1 ((hK1 a b).mpr ⟨hab,hal,hbl⟩)
  have:=htK1 d1.cover hcovK;omega
 have hK1_pq: K1.Adj p q:=(hK1 p q).mpr ⟨(hp q).mpr (Or.inr rfl),hlp.symm,hql⟩
 have hq_cov: q∈d1.cover:=by
  rcases hmc1.1 hK1_pq with h|h
  ·exact absurd (mC.mp h) hpnc
  ·exact mC.mp h
 have hown_qp: d1.owns q p=true:=by
  have hne:=hown1.2 p q hK1_pq
  have hp_no: d1.owns p q=false:=by
   cases h: d1.owns p q;rfl;exact absurd (hown1.1 p q h).2 hpnc
  rw[hp_no] at hne;cases h: d1.owns q p;rw[h] at hne;exact absurd rfl hne;rfl
 have hlam_qp: d1.lam q p=p.val:=by
  have h:=(h1c q hq_cov).2.2.2 p hown_qp;unfold LamOK at h;simp[hpnc] at h;exact h
 have honly_qp: ∀ t: Fin n,d1.owns t p=true → t=q:=by
  intro t hown;have hadj:=(hK1 t p).mp (hown1.1 t p hown).1
  rcases (hp t).mp hadj.1.symm with h|h
  ·exact absurd h hadj.2.1
  ·exact h
 have hval_C: ∀ x: Fin n→Bool,vl C.gates x C.output=graphFun K A x:=fun x => congrFun hcf x
 have hval_C1: ∀ x: Fin n→Bool,vl C1.gates x C1.output=graphFun K1 A x:=fun x =>
  congrFun (ncc_eval hv1) x
 let u1:=rd n jl 0 u;let wl1:=rd n jl 0 wl
 have hu_lw: lw2 n jl r u1=u:=by
  have h1: lw1 n jl u1=u:=lw1r n jl 0 u hune;unfold lw2;rw[h1];unfold lw1;split_ifs <;> omega
 have hwl_lw: lw2 n jl r wl1=wl:=by
  have h1: lw1 n jl wl1=wl:=lw1r n jl 0 wl (by omega);unfold lw2;rw[h1];unfold lw1;split_ifs <;> omega
 have hu1_lt: u1 < n+C1.gates.length:=by
  change rd n jl 0 u < n+C1.gates.length;unfold rd;split_ifs <;> omega
 have hwl1_lt: wl1 < n+C1.gates.length:=by
  change rd n jl 0 wl < n+C1.gates.length;unfold rd;split_ifs <;> omega
 have hwl1_ne_l: wl1≠l.val:=by
  change rd n jl 0 wl≠l.val;unfold rd;split_ifs <;> have := l.isLt <;> omega
 have hvl_u: ∀ x: Fin n→Bool,vl C.gates x u=vl C1.gates x u1:=fun x => by
  rw[←hu_lw];exact vlb hn C hcl hrb hjr hr hu hune hon0 hur x u1 (by omega)
 have hvl_wl: ∀ x: Fin n→Bool,vl C.gates x wl=vl C1.gates x wl1:=fun x => by
  rw[←hwl_lw];exact vlb hn C hcl hrb hjr hr hu hune hon0 hur x wl1 (by omega)
 have hvl_r: ∀ x: Fin n→Bool,vl C.gates x (n+r)=((x l&&vl C1.gates x wl1)||vl C1.gates x u1):=by
  intro x
  have hgj: C.gates[jl]? = some (gateAt C jl):=by simp[gateAt,List.getD,show jl < C.gates.length by omega]
  have hgr: C.gates[r]? = some (gateAt C r):=by simp[gateAt,List.getD,hr]
  have h1: vl C.gates x (n+jl)=(x l&&vl C1.gates x wl1):=by
   rw[vlg C.gates hcl x jl _ hgj,hjlo]
   rcases hjli with h|h <;> rw[h] <;>
    simp[GateOp.eval,vli C.gates x l.val l.isLt,hvl_wl x,Bool.and_comm]
  rw[vlg C.gates hcl x r _ hgr,hro0]
  rcases hri0 with h|h <;> rw[h] <;>
   simp[GateOp.eval,h1,hvl_u x,Bool.or_comm]
 have hCC1: ∀ x: Fin n→Bool,vl C.gates x (n+r)=vl C.gates x u →
   vl C.gates x C.output=vl C1.gates x C1.output:=by
  intro x hru;have hall:=vlab hn C hcl hrb hjr hr hu hune hon0 hur x hru
  by_cases hor: C.output=n+r
  ·have hc1: C1.output=u1:=by change rd n jl 0 (rd n r u C.output)=u1;rw[hor,rd_eq]
   rw[hor,hc1,hru,hvl_u x]
  ·have hlout: lw2 n jl r C1.output=C.output:=lw2r hjr hon0 hor;rw[hall C1.output,hlout]
 let x_lp: Fin n→Bool:=fun v => decide (v=l∨v=p)
 have hlpC: vl C.gates x_lp C.output=true:=by
  rw[hval_C];simp only[graphFun,boT,dTe]
  right;exact ⟨l,p,(hl p).mpr rfl,by simp[x_lp],by simp[x_lp]⟩
 have hlp1: vl C1.gates x_lp C1.output=false:=by
  rw[hval_C1];simp only[graphFun,boF,dFn,x_lp,dTe]
  refine ⟨?_,?_⟩
  ·rintro ⟨a,ha,hal|hap⟩
   ·exact hlnA (hal ▸ ha)
   ·exact hpnA (hap ▸ ha)
  ·rintro ⟨a,b,hab,hal|hap,hbl|hbp⟩
   ·exact ((hK1 a b).mp hab).2.1 hal
   ·exact ((hK1 a b).mp hab).2.1 hal
   ·exact ((hK1 a b).mp hab).2.2 hbl
   ·exact hab.ne (hap.trans hbp.symm)
 have hx_lp_ru: vl C.gates x_lp (n+r)≠vl C.gates x_lp u:=fun h => by
  have:=hCC1 x_lp h;rw[hlpC,hlp1] at this;cases this
 have hlpu: vl C1.gates x_lp u1=false:=by
  rw[hvl_r,hvl_u] at hx_lp_ru
  cases hu1v: vl C1.gates x_lp u1
  ·rfl
  ·simp[hu1v] at hx_lp_ru
 have hlpw: vl C1.gates x_lp wl1=true:=by
  rw[hvl_r,hvl_u,hlpu] at hx_lp_ru
  have hxl: x_lp l=true:=by simp[x_lp]
  rw[hxl] at hx_lp_ru
  cases hwl1v: vl C1.gates x_lp wl1
  ·simp[hwl1v] at hx_lp_ru
  ·rfl
 have h1xf: ∀ w < n+C1.gates.length,w≠l.val → w≠p.val →
   (∀ j < C1.gates.length,w=n+j → d1.role j≠(Kind.o,q.val)) →
   vl C1.gates x_lp w=false:=by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
   intro hw hwl hwp hnoOq
   by_cases hwn: w < n
   ·rw[vli C1.gates x_lp w hwn]
    have h1: (⟨w,hwn⟩ : Fin n)≠l:=fun e => hwl (congrArg Fin.val e)
    have h2: (⟨w,hwn⟩ : Fin n)≠p:=fun e => hwp (congrArg Fin.val e)
    simp[x_lp,h1,h2]
   ·set j:=w - n
    have hweq: w=n+j:=by omega
    have hj: j < C1.gates.length:=by omega
    have hgj: C1.gates[j]? = some (gateAt C1 j):=by simp[gateAt,List.getD,hj]
    rw[hweq,vlg C1.gates hcl1 x_lp j _ hgj];have hrole_ne: d1.role j≠(Kind.o,q.val):=hnoOq j hj hweq
    by_cases htop_j: (d1.role j).1=Kind.top
    ·have hjT: j∈topGates d1 C1:=mF.mpr ⟨mR.mpr hj,htop_j⟩;obtain ⟨hop,hlen,hins⟩:=htop1.1 j hjT;obtain ⟨a,b,hab⟩:=ll2.mp hlen
     have hfa: ∀ c∈(gateAt C1 j).inputs,vl C1.gates x_lp c=false:=by
      intro c hc;have hclt: c < n+j:=hrb1 j hj c hc;apply ih c (by omega) (by omega)
      ·rcases hins c hc with hL|⟨hge,_⟩
       ·simp only[topLeaves,mU,mI,mF] at hL
        rcases hL with ⟨a',ha',rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
        ·exact fun e => hlnA (Fin.ext e.symm ▸ ha')
        ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have:=l.isLt;omega
       ·have:=l.isLt;omega
      ·rcases hins c hc with hL|⟨hge,_⟩
       ·simp only[topLeaves,mU,mI,mF] at hL
        rcases hL with ⟨a',ha',rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
        ·exact fun e => hpnA (Fin.ext e.symm ▸ ha')
        ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have:=p.isLt;omega
       ·have:=p.isLt;omega
      ·intro k hk eck hro
       rcases hins c hc with hL|⟨_,hG⟩
       ·simp only[topLeaves,mU,mI,mF] at hL
        rcases hL with ⟨a',_,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
        ·have := a'.isLt;omega
        ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1
         have: k=jb := by omega
         rw[this,hrb_s] at hro;cases hro
       ·have hG' := (mF.mp hG).2;rw[eck,ascl] at hG';rw[hro] at hG';cases hG'
     rw[hop,hab];simp[GateOp.eval,hfa a (by simp[hab]),hfa b (by simp[hab])]
    ·rcases hrol1 j hj with htop' | ⟨t,ht,hrt2,hrb_t⟩
     ·exact absurd htop' htop_j
     ·cases hkr: (d1.role j).1 with
      | top => exact absurd hkr htop_j
      | b =>
       have hbw:=hrb_t hkr;obtain ⟨jb,hjb,hbw2,_,hop,hin⟩:=(h1c t ht).1
       have hje: j=jb:=by omega
       rw[hje,hop]
       have hz_false: vl C1.gates x_lp (d1.zroot t)=false:=by
        have hzlt: d1.zroot t < n+jb:=hrb1 jb hjb (d1.zroot t) (by rcases hin with h|h <;> simp[h])
        apply ih (d1.zroot t) (by omega) (by omega)
        ·rcases zrs hv1 t ht with h|⟨_,_,h,_⟩
         ·exact fun e => hlnc (Fin.ext (h.symm.trans e) ▸ ht)
         ·have:=l.isLt;omega
        ·rcases zrs hv1 t ht with h|⟨_,_,h,_⟩
         ·exact fun e => hpnc (Fin.ext (h.symm.trans e) ▸ ht)
         ·have:=p.isLt;omega
        ·intro k _ ek hro
         rcases zrs hv1 t ht with h|⟨jz,_,h,hrz⟩
         ·have:=t.isLt;omega
         ·have: k=jz := by omega
          rw[this,hrz] at hro;cases hro
       rcases hin with h|h <;> rw[h] <;> simp[GateOp.eval,hz_false]
      | z =>
       have hjZ: j∈gatesOf d1 C1 Kind.z t.val :=
        mF.mpr ⟨mR.mpr hj,Prod.ext hkr hrt2⟩
       obtain ⟨hop,hlen,hins⟩:=(h1c t ht).2.1.1 j hjZ;obtain ⟨a,b,hab⟩:=ll2.mp hlen
       have hfa: ∀ c∈(gateAt C1 j).inputs,vl C1.gates x_lp c=false:=by
        intro c hc;have hclt: c < n+j:=hrb1 j hj c hc;apply ih c (by omega) (by omega)
        ·rcases hins c hc with hL|⟨_,_⟩
         ·simp only[zLeaves,mN,mI,mF] at hL
          rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
          ·exact fun e => hlnc (Fin.ext e.symm ▸ ht)
          ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have:=l.isLt;omega
         ·have:=l.isLt;omega
        ·rcases hins c hc with hL|⟨_,_⟩
         ·simp only[zLeaves,mN,mI,mF] at hL
          rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
          ·exact fun e => hpnc (Fin.ext e.symm ▸ ht)
          ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have:=p.isLt;omega
         ·have:=p.isLt;omega
        ·intro k _ eck hro
         rcases hins c hc with hL|⟨_,hG⟩
         ·simp only[zLeaves,mN,mI,mF] at hL
          rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
          ·have:=t.isLt;omega
          ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1
           have: k=jb := by omega
           rw[this,hrb_s] at hro;cases hro
         ·have hG' := (mF.mp hG).2;rw[eck,ascl] at hG';rw[hro] at hG';cases hG'
       rw[hop,hab];simp[GateOp.eval,hfa a (by simp[hab]),hfa b (by simp[hab])]
      | o =>
       have htq: t≠q:=fun e => hrole_ne (Prod.ext hkr (hrt2.trans (congrArg Fin.val e)))
       have hjO: j∈gatesOf d1 C1 Kind.o t.val :=
        mF.mpr ⟨mR.mpr hj,Prod.ext hkr hrt2⟩
       obtain ⟨hop,hlen,hins⟩:=(h1c t ht).2.2.1.1 j hjO;obtain ⟨a,b,hab⟩:=ll2.mp hlen
       have hfa: ∀ c∈(gateAt C1 j).inputs,vl C1.gates x_lp c=false:=by
        intro c hc;have hclt: c < n+j:=hrb1 j hj c hc;apply ih c (by omega) (by omega)
        ·rcases hins c hc with hL|⟨_,_⟩
         ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',rfl⟩:=hL
          have hne_l: r' ≠ l:=fun e => hl_iso t (e ▸ (hown1.1 t r' hown').1).symm
          have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
          ·rcases hlam.2.1 with h|⟨_,_,h,_⟩
           ·exact fun e => hne_l (Fin.ext (h.symm.trans e))
           ·have:=l.isLt;omega
          ·exact fun e => hne_l (Fin.ext (hlam.symm.trans e))
         ·have:=l.isLt;omega
        ·rcases hins c hc with hL|⟨_,_⟩
         ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',rfl⟩:=hL
          have hne_p: r' ≠ p:=fun e => htq (honly_qp t (e ▸ hown'))
          have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
          ·rcases hlam.2.1 with h|⟨_,_,h,_⟩
           ·exact fun e => hne_p (Fin.ext (h.symm.trans e))
           ·have:=p.isLt;omega
          ·exact fun e => hne_p (Fin.ext (hlam.symm.trans e))
         ·have:=p.isLt;omega
        ·intro k _ eck hro
         rcases hins c hc with hL|⟨_,hG⟩
         ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',rfl⟩:=hL;have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
          ·rcases hlam.2.1 with h|⟨jz,_,h,hrz⟩
           ·have := r'.isLt;omega
           ·have: k=jz := by omega
            rw[this,hrz] at hro;cases hro
          ·have := r'.isLt;omega
         ·have hG' := (mF.mp hG).2;rw[eck,ascl] at hG';rw[hro] at hG';exact htq (Fin.ext (pei.mp hG').2.symm)
       rw[hop,hab];simp[GateOp.eval,hfa a (by simp[hab]),hfa b (by simp[hab])]
 have hw1c: wl1=p.val∨(n ≤ wl1∧wl1 - n < C1.gates.length∧d1.role (wl1 - n)=(Kind.o,q.val)):=by
  by_cases h1: wl1=p.val
  ·exact Or.inl h1
  ·right
   by_contra hnot
   have hno: ∀ j < C1.gates.length,wl1=n+j → d1.role j≠(Kind.o,q.val):=by
    intro j hj he hro;exact hnot ⟨by omega,by omega,by rw[he,ascl];exact hro⟩
   have hf:=h1xf wl1 hwl1_lt hwl1_ne_l h1 hno;rw[hf] at hlpw;cases hlpw
 have htGl: ∀ k∈topGates d1 C1,k < C1.gates.length:=fun k hk =>
  mR.mp (mF.mp hk).1
 have hZGl: ∀ t: Fin n,∀ k∈gatesOf d1 C1 Kind.z t.val,k < C1.gates.length:=fun t k hk =>
  mR.mp (mF.mp hk).1
 have hOGl: ∀ t: Fin n,∀ k∈gatesOf d1 C1 Kind.o t.val,k < C1.gates.length:=fun t k hk =>
  mR.mp (mF.mp hk).1
 have h1ol: C1.output < n+C1.gates.length:=orTree_rt_lt htop1 htGl (by
  intro w hw;simp only[topLeaves,mU,mI,mF] at hw
  rcases hw with ⟨a,_,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
  ·have:=a.isLt;omega
  ·obtain ⟨jb,hjb,hbw,_,_,_⟩:=(h1c s hs).1;omega)
 have hZd: ∀ t1 t2: Fin n,t1∈d1.cover → t2∈d1.cover → t1≠t2 →
   ∀ w,(w∈zLeaves d1 t1∨(n ≤ w∧w - n∈gatesOf d1 C1 Kind.z t1.val)) →
   ¬ (w∈zLeaves d1 t2∨(n ≤ w∧w - n∈gatesOf d1 C1 Kind.z t2.val)):=by
  intro t1 t2 ht1 ht2 h12 w hw1 hw2
  rcases hw1 with hL1|⟨hg1,hG1⟩ <;> rcases hw2 with hL2|⟨hg2,hG2⟩
  ·simp only[zLeaves,mN,mI,mF] at hL1 hL2
   rcases hL1 with rfl|⟨s1,⟨hs1,hst1⟩,rfl⟩ <;> rcases hL2 with h2|⟨s2,⟨hs2,hst2⟩,h2⟩
   ·exact h12 (Fin.ext h2)
   ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s2 hs2).1;have:=t1.isLt;omega
   ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s1 hs1).1;have:=t2.isLt;omega
   ·have hs12: s1=s2:=bw_injOn hv1 d1.cover (Subset.refl _) hs1 hs2 h2.symm;rw[hs12,hst2] at hst1;exact h12 (osi hst1).symm
  ·simp only[zLeaves,mN,mI,mF] at hL1
   rcases hL1 with rfl|⟨s1,⟨hs1,_⟩,rfl⟩
   ·have:=t1.isLt;omega
   ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s1 hs1).1;have hG' := (mF.mp hG2).2;rw[hbw,ascl,hrb_s] at hG';cases hG'
  ·simp only[zLeaves,mN,mI,mF] at hL2
   rcases hL2 with rfl|⟨s2,⟨hs2,_⟩,rfl⟩
   ·have:=t2.isLt;omega
   ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s2 hs2).1;have hG' := (mF.mp hG1).2;rw[hbw,ascl,hrb_s] at hG';cases hG'
  ·have h1:=(mF.mp hG1).2;have h2:=(mF.mp hG2).2;rw[h1] at h2;exact h12 (Fin.ext (pei.mp h2).2)
 have htZd: ∀ t∈d1.cover,∀ w,
   (w∈topLeaves d1 A∨(n ≤ w∧w - n∈topGates d1 C1)) →
   ¬ (w∈zLeaves d1 t∨(n ≤ w∧w - n∈gatesOf d1 C1 Kind.z t.val)):=by
  intro t ht w hwt hwz
  rcases hwt with hL1|⟨hg1,hG1⟩ <;> rcases hwz with hL2|⟨hg2,hG2⟩
  ·simp only[topLeaves,mU,mI,mF] at hL1;simp only[zLeaves,mN,mI,mF] at hL2
   rcases hL1 with ⟨a,ha,rfl⟩ | ⟨s1,⟨hs1,hs1f⟩,rfl⟩ <;> rcases hL2 with h2|⟨s2,⟨hs2,hst2⟩,h2⟩
   ·obtain ⟨v,hown,_⟩:=coo hv1 t ht;exact hA a ha v (Fin.ext h2 ▸ ((hK1 t v).mp (hown1.1 t v hown).1).1)
   ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s2 hs2).1;have:=a.isLt;omega
   ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s1 hs1).1;have:=t.isLt;omega
   ·have hs12: s1=s2:=bw_injOn hv1 d1.cover (Subset.refl _) hs1 hs2 h2.symm;rw[hs12,hst2] at hs1f;cases hs1f
  ·simp only[topLeaves,mU,mI,mF] at hL1
   rcases hL1 with ⟨a,_,rfl⟩ | ⟨s1,⟨hs1,_⟩,rfl⟩
   ·have:=a.isLt;omega
   ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s1 hs1).1;have hG' := (mF.mp hG2).2;rw[hbw,ascl,hrb_s] at hG';cases hG'
  ·simp only[zLeaves,mN,mI,mF] at hL2
   rcases hL2 with rfl|⟨s2,⟨hs2,_⟩,rfl⟩
   ·have:=t.isLt;omega
   ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s2 hs2).1;have hG' := (mF.mp hG1).2;rw[hbw,ascl,hrb_s] at hG';cases hG'
  ·have h1:=(mF.mp hG1).2;have h2:=(mF.mp hG2).2;rw[h2] at h1;cases h1
 have hOZd: ∀ t∈d1.cover,∀ w,
   (w∈oLeaves d1 t∨(n ≤ w∧w - n∈gatesOf d1 C1 Kind.o t.val)) →
   ¬ (w∈zLeaves d1 t∨(n ≤ w∧w - n∈gatesOf d1 C1 Kind.z t.val)):=by
  intro t ht w hwo hwz
  rcases hwo with hL1|⟨hg1,hG1⟩
  ·simp only[oLeaves,mI,mF,mV,true_and] at hL1;obtain ⟨r',hown',rfl⟩:=hL1;have hrt: r' ≠ t:=(hown1.1 t r' hown').1.ne';have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
   ·have hw_r' : d1.lam t r' ∈ zLeaves d1 r' ∨ (n ≤ d1.lam t r' ∧ d1.lam t r' - n∈gatesOf d1 C1 Kind.z r'.val):=by
     rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
     ·exact Or.inl (h ▸ mNs _ _)
     ·exact Or.inr ⟨by omega,by rw[h1,ascl];exact mF.mpr ⟨mR.mpr hjz,h2⟩⟩
    exact hZd r' t hrc ht hrt (d1.lam t r') hw_r' hwz
   ·rcases hwz with hL2|⟨hg2,_⟩
    ·simp only[zLeaves,mN,mI,mF] at hL2
     rcases hL2 with h2|⟨s2,⟨hs2,_⟩,h2⟩
     ·exact hrt (Fin.ext (hlam.symm.trans h2))
     ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s2 hs2).1;rw[hlam] at h2;have := r'.isLt;omega
    ·rw[hlam] at hg2;have := r'.isLt;omega
  ·rcases hwz with hL2|⟨hg2,hG2⟩
   ·simp only[zLeaves,mN,mI,mF] at hL2
    rcases hL2 with rfl|⟨s2,⟨hs2,_⟩,rfl⟩
    ·have:=t.isLt;omega
    ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s2 hs2).1;have hG' := (mF.mp hG1).2;rw[hbw,ascl,hrb_s] at hG';cases hG'
   ·have h1:=(mF.mp hG1).2;have h2:=(mF.mp hG2).2;rw[h1] at h2;cases h2
 have hnu1: ∀ j' < C1.gates.length,
   n+r∈(gateAt C (li2 jl r j')).inputs → u1∈(gateAt C1 j').inputs:=by
  intro j' hj' hmem;have hlif:=r2l C hcl hrb hjr hr hu j' (by omega);rw[hlif.2];exact lmm.mpr ⟨n+r,hmem,by rw[rd_eq]⟩
 have hu1_cases: (u1∈topLeaves d1 A∨(n ≤ u1∧u1 - n∈topGates d1 C1)) ∨
   (u1∈zLeaves d1 q∨(n ≤ u1∧u1 - n∈gatesOf d1 C1 Kind.z q.val)):=by
  by_contra hneither
  push_neg at hneither
  obtain ⟨⟨hu1_not_tL,hu1_not_tG⟩,⟨hu1_not_zL,hu1_not_zG⟩⟩:=hneither
  have hu1_not_top: ¬ (u1∈topLeaves d1 A∨(n ≤ u1∧u1 - n∈topGates d1 C1)):=fun h =>
   h.elim hu1_not_tL (fun ⟨h1,h2⟩ => hu1_not_tG h1 h2)
  have hu1_not_Zq: ¬ (u1∈zLeaves d1 q∨(n ≤ u1∧u1 - n∈gatesOf d1 C1 Kind.z q.val)):=fun h =>
   h.elim hu1_not_zL (fun ⟨h1,h2⟩ => hu1_not_zG h1 h2)
  have hP_false: ∀ w < n+C1.gates.length,
    (w < n → w≠l.val∧w≠p.val) →
    (∀ j' < C1.gates.length,w=n + j' →
     (d1.role j').1=Kind.top∨(d1.role j').1=Kind.b ∨
     (∃ t∈d1.cover,d1.role j' = (Kind.z,t.val) ∧ ¬ (u1∈zLeaves d1 t∨(n ≤ u1∧u1 - n∈gatesOf d1 C1 Kind.z t.val))) ∨
     (∃ t∈d1.cover,d1.role j' = (Kind.o,t.val)∧t≠q∧(u1∈zLeaves d1 t∨(n ≤ u1∧u1 - n∈gatesOf d1 C1 Kind.z t.val)))) →
    vl C.gates x_lp (lw2 n jl r w)=false:=by
   intro w
   induction w using Nat.strong_induction_on with
   | ind w ih =>
    intro hw hlt_in hP
    by_cases hwn: w < n
    ·rw[lw2i n jl r w hwn,vli C.gates x_lp w hwn];have ⟨h1,h2⟩:=hlt_in hwn
     simp[x_lp,show (⟨w,hwn⟩ : Fin n)≠l from fun e => h1 (congrArg Fin.val e),
      show (⟨w,hwn⟩ : Fin n)≠p from fun e => h2 (congrArg Fin.val e)]
    ·set j' := w - n
     have hweq: w=n + j' := by omega
     have hj' : j' < C1.gates.length:=by omega
     have hlt_C: li2 jl r j' < C.gates.length:=li2lt hjr hr (by rw[←hlen1];exact hj')
     have hgC: C.gates[li2 jl r j']? = some (gateAt C (li2 jl r j')):=by
      simp[gateAt,List.getD,hlt_C]
     have hlif:=r2l C hcl hrb hjr hr hu j' (by omega);rw[hweq,lw2g,vlg C.gates hcl x_lp (li2 jl r j') _ hgC,←hlif.1]
     have hNoAndFalse: ∀ (hop: (gateAt C1 j').op=GateOp.or)
       (hno: n+r∉(gateAt C (li2 jl r j')).inputs)
       (hfa: ∀ a∈(gateAt C1 j').inputs,vl C.gates x_lp (lw2 n jl r a)=false),
       (gateAt C1 j').op.eval ((gateAt C (li2 jl r j')).inputs.map (vl C.gates x_lp))=false:=by
      intro hop hno hfa;have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur j' (by omega) hno;rw[hop,hinp,lmp];simp only[GateOp.eval,lyF,lmm,Function.comp_apply,Bool.not_eq_true]
      rintro _ ⟨a,ha,rfl⟩;exact hfa a ha
     rcases hP j' hj' hweq with htop_j|hb_j|⟨t,ht,hrz_j,hno_u1⟩ | ⟨t,ht,hro_j,htq,hyes_u1⟩
     ·
      have hjT: j' ∈ topGates d1 C1:=mF.mpr ⟨mR.mpr hj',htop_j⟩;obtain ⟨hop,_,hins⟩:=htop1.1 j' hjT
      apply hNoAndFalse hop (fun hm => hu1_not_top (hins u1 (hnu1 j' hj' hm)))
      intro a ha;have halt: a < n + j' := hrb1 j' hj' a ha;apply ih a (by omega) (by omega)
      ·intro han;rcases hins a ha with hL|⟨hge,_⟩
       ·simp only[topLeaves,mU,mI,mF] at hL
        rcases hL with ⟨a',ha',rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
        ·exact ⟨fun e => hlnA (Fin.ext e.symm ▸ ha'),fun e => hpnA (Fin.ext e.symm ▸ ha')⟩
        ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;omega
       ·omega
      ·intro k hk eak
       rcases hins a ha with hL|⟨_,hG⟩
       ·simp only[topLeaves,mU,mI,mF] at hL
        rcases hL with ⟨a',_,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
        ·have := a'.isLt;omega
        ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1
         have: k=jb := (by omega);right;left;rw[this,hrb_s]
       ·left;have hG' := (mF.mp hG).2;rw[eak,ascl] at hG';exact hG'
     ·
      rcases hrol1 j' hj' with ht' | ⟨t,ht,_,hrb_t⟩
      ·rw[hb_j] at ht';cases ht'
      ·have hbw:=hrb_t hb_j;obtain ⟨jb,hjb,hbw2,_,hop,hin⟩:=(h1c t ht).1
       have hje: j' = jb:=by omega
       rw[hje] at hlif ⊢;rw[hop]
       have hlenC: (gateAt C (li2 jl r jb)).inputs.length=2:=by
        have h2: (gateAt C1 jb).inputs.length=2:=by rcases hin with h|h <;> simp[h]
        rw[hlif.2,llm] at h2;exact h2
       obtain ⟨x1,x2,hx12⟩:=ll2.mp hlenC
       have hmap: [rd n jl 0 (rd n r u x1),rd n jl 0 (rd n r u x2)]=(gateAt C1 jb).inputs:=by
        rw[hlif.2,hx12];rfl
       have hne_jl: ∀ c∈(gateAt C (li2 jl r jb)).inputs,c≠n+jl:=fun c hc e =>
        li2nr jl r jb (hur (li2 jl r jb) (by rw[←hje];exact hlt_C) (e ▸ hc))
       by_cases hu1_Zt: u1∈zLeaves d1 t∨(n ≤ u1∧u1 - n∈gatesOf d1 C1 Kind.z t.val)
       ·
        have htq: t≠q:=fun e => hu1_not_Zq (e ▸ hu1_Zt)
        have hor_mem: d1.oroot t∈oLeaves d1 t∨(n ≤ d1.oroot t∧d1.oroot t - n∈gatesOf d1 C1 Kind.o t.val):=by
         rcases ors hv1 t ht with ⟨r',hown',hlam'⟩ | ⟨jo,hjo,hor,hro⟩
         ·exact Or.inl (by simp only[oLeaves,mI,mF,mV,true_and];exact ⟨r',hown',hlam'.symm⟩)
         ·exact Or.inr ⟨by omega,by rw[hor,ascl];exact mF.mpr ⟨mR.mpr hjo,hro⟩⟩
        have hor_ne_u1: d1.oroot t≠u1:=fun e => hOZd t ht u1 (e ▸ hor_mem) hu1_Zt
        have hor_lt: d1.oroot t < n+jb:=hrb1 jb hjb (d1.oroot t) (by rcases hin with h|h <;> simp[h])
        have hor_false: vl C.gates x_lp (lw2 n jl r (d1.oroot t))=false:=by
         apply ih (d1.oroot t) (by omega) (by omega)
         ·intro han
          rcases ors hv1 t ht with ⟨r',hown',hlam'⟩ | ⟨_,_,hor,_⟩
          ·have hne_l: r' ≠ l:=fun e => hl_iso t (e ▸ (hown1.1 t r' hown').1).symm
           have hne_p: r' ≠ p:=fun e => htq (honly_qp t (e ▸ hown'))
           have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
           ·rcases hlam.2.1 with h|⟨_,_,h,_⟩
            ·exact ⟨fun e => hne_l (Fin.ext (h.symm.trans (hlam'.symm.trans e))),
              fun e => hne_p (Fin.ext (h.symm.trans (hlam'.symm.trans e)))⟩
            ·omega
           ·exact ⟨fun e => hne_l (Fin.ext (hlam.symm.trans (hlam'.symm.trans e))),
             fun e => hne_p (Fin.ext (hlam.symm.trans (hlam'.symm.trans e)))⟩
          ·omega
         ·intro k hk eok
          rcases ors hv1 t ht with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
          ·have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
           ·rcases hlam.2.1 with h|⟨jz,_,h,hrz⟩
            ·have := r'.isLt;omega
            ·right;right;left
             have hne_rt: r' ≠ t:=(hown1.1 t r' hown').1.ne'
             have: k=jz := (by omega)
             exact ⟨r',hrc,by rw[this,hrz],fun hu1_r' => hZd r' t hrc ht hne_rt u1 hu1_r' hu1_Zt⟩
           ·have := r'.isLt;omega
          ·right;right;right
           have: k=jo := (by omega)
           exact ⟨t,ht,by rw[this,hro],htq,hu1_Zt⟩
        have hor_inC: lw2 n jl r (d1.oroot t)∈(gateAt C (li2 jl r jb)).inputs:=by
         have hmem1: d1.oroot t∈(gateAt C1 jb).inputs:=by rcases hin with h|h <;> simp[h]
         rw[←hmap] at hmem1;simp at hmem1
         rcases hmem1 with e|e
         ·have hx1_ne_r: x1≠n+r:=fun er => hor_ne_u1 (by rw[e,er,rd_eq])
          have hx1_eq: lw2 n jl r (d1.oroot t)=x1:=by
           rw[e,lw2r hjr (hne_jl x1 (by rw[hx12];simp)) hx1_ne_r]
          rw[hx1_eq,hx12];simp
         ·have hx2_ne_r: x2≠n+r:=fun er => hor_ne_u1 (by rw[e,er,rd_eq])
          have hx2_eq: lw2 n jl r (d1.oroot t)=x2:=by
           rw[e,lw2r hjr (hne_jl x2 (by rw[hx12];simp)) hx2_ne_r]
          rw[hx2_eq,hx12];simp
        simp only[GateOp.eval,laF,lmm,id_eq];exact ⟨false,⟨lw2 n jl r (d1.oroot t),hor_inC,hor_false⟩,by simp⟩
       ·
        have hzr_mem: d1.zroot t∈zLeaves d1 t∨(n ≤ d1.zroot t∧d1.zroot t - n∈gatesOf d1 C1 Kind.z t.val):=by
         rcases zrs hv1 t ht with h|⟨jz,hjz,hzr,hrz⟩
         ·exact Or.inl (h ▸ mNs _ _)
         ·exact Or.inr ⟨by omega,by rw[hzr,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩
        have hzr_ne_u1: d1.zroot t≠u1:=fun e => hu1_Zt (e ▸ hzr_mem)
        have hzr_lt: d1.zroot t < n+jb:=hrb1 jb hjb (d1.zroot t) (by rcases hin with h|h <;> simp[h])
        have hzr_false: vl C.gates x_lp (lw2 n jl r (d1.zroot t))=false:=by
         apply ih (d1.zroot t) (by omega) (by omega)
         ·intro han
          rcases zrs hv1 t ht with h|⟨_,_,hzr,_⟩
          ·exact ⟨fun e => hlnc (Fin.ext (h.symm.trans e) ▸ ht),
            fun e => hpnc (Fin.ext (h.symm.trans e) ▸ ht)⟩
          ·omega
         ·intro k _ ezk
          rcases zrs hv1 t ht with h|⟨jz,_,hzr,hrz⟩
          ·have:=t.isLt;omega
          ·right;right;left
           have: k=jz := (by omega)
           exact ⟨t,ht,by rw[this,hrz],hu1_Zt⟩
        have hzr_inC: lw2 n jl r (d1.zroot t)∈(gateAt C (li2 jl r jb)).inputs:=by
         have hmem1: d1.zroot t∈(gateAt C1 jb).inputs:=by rcases hin with h|h <;> simp[h]
         rw[←hmap] at hmem1;simp at hmem1
         rcases hmem1 with e|e
         ·have hx1_ne_r: x1≠n+r:=fun er => hzr_ne_u1 (by rw[e,er,rd_eq])
          have hx1_eq: lw2 n jl r (d1.zroot t)=x1:=by
           rw[e,lw2r hjr (hne_jl x1 (by rw[hx12];simp)) hx1_ne_r]
          rw[hx1_eq,hx12];simp
         ·have hx2_ne_r: x2≠n+r:=fun er => hzr_ne_u1 (by rw[e,er,rd_eq])
          have hx2_eq: lw2 n jl r (d1.zroot t)=x2:=by
           rw[e,lw2r hjr (hne_jl x2 (by rw[hx12];simp)) hx2_ne_r]
          rw[hx2_eq,hx12];simp
        simp only[GateOp.eval,laF,lmm,id_eq];exact ⟨false,⟨lw2 n jl r (d1.zroot t),hzr_inC,hzr_false⟩,by simp⟩
     ·
      have hjZ: j' ∈ gatesOf d1 C1 Kind.z t.val:=mF.mpr ⟨mR.mpr hj',hrz_j⟩;obtain ⟨hop,_,hins⟩:=(h1c t ht).2.1.1 j' hjZ
      apply hNoAndFalse hop (fun hm => hno_u1 (hins u1 (hnu1 j' hj' hm)))
      intro a ha;have halt: a < n + j' := hrb1 j' hj' a ha;apply ih a (by omega) (by omega)
      ·intro han;rcases hins a ha with hL|⟨_,_⟩
       ·simp only[zLeaves,mN,mI,mF] at hL
        rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
        ·exact ⟨fun e => hlnc (Fin.ext e.symm ▸ ht),fun e => hpnc (Fin.ext e.symm ▸ ht)⟩
        ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;omega
       ·omega
      ·intro k _ eak
       rcases hins a ha with hL|⟨_,hG⟩
       ·simp only[zLeaves,mN,mI,mF] at hL
        rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
        ·have:=t.isLt;omega
        ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1
         have: k=jb := (by omega);right;left;rw[this,hrb_s]
       ·right;right;left
        have hG' := (mF.mp hG).2;rw[eak,ascl] at hG';exact ⟨t,ht,hG',hno_u1⟩
     ·
      have hjO: j' ∈ gatesOf d1 C1 Kind.o t.val:=mF.mpr ⟨mR.mpr hj',hro_j⟩;obtain ⟨hop,_,hins⟩:=(h1c t ht).2.2.1.1 j' hjO
      apply hNoAndFalse hop (fun hm => hOZd t ht u1 (hins u1 (hnu1 j' hj' hm)) hyes_u1)
      intro a ha;have halt: a < n + j' := hrb1 j' hj' a ha;apply ih a (by omega) (by omega)
      ·intro han;rcases hins a ha with hL|⟨_,_⟩
       ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',rfl⟩:=hL
        have hne_l: r' ≠ l:=fun e => hl_iso t (e ▸ (hown1.1 t r' hown').1).symm
        have hne_p: r' ≠ p:=fun e => htq (honly_qp t (e ▸ hown'))
        have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam
        ·rcases hlam.2.1 with h|⟨_,_,h,_⟩
         ·exact ⟨fun e => hne_l (Fin.ext (h.symm.trans e)),fun e => hne_p (Fin.ext (h.symm.trans e))⟩
         ·omega
        ·exact ⟨fun e => hne_l (Fin.ext (hlam.symm.trans e)),fun e => hne_p (Fin.ext (hlam.symm.trans e))⟩
       ·omega
      ·intro k _ eak
       rcases hins a ha with hL|⟨_,hG⟩
       ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',rfl⟩:=hL;have hne_rt: r' ≠ t:=(hown1.1 t r' hown').1.ne';have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
        ·rcases hlam.2.1 with h|⟨jz,_,h,hrz⟩
         ·have := r'.isLt;omega
         ·right;right;left
          have: k=jz := (by omega)
          exact ⟨r',hrc,by rw[this,hrz],fun hu1_r' => hZd r' t hrc ht hne_rt u1 hu1_r' hyes_u1⟩
        ·have := r'.isLt;omega
       ·right;right;right
        have hG' := (mF.mp hG).2;rw[eak,ascl] at hG';exact ⟨t,ht,hG',htq,hyes_u1⟩
  have hrm: C1.output∈topLeaves d1 A∨(n ≤ C1.output∧C1.output - n∈topGates d1 C1):=by
   by_cases hGe: topGates d1 C1 = ∅
   ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
   ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
  have hne_out: C.output≠n+r:=fun e => hu1_not_top (by
   have: u1=C1.output := by change rd n jl 0 u=rd n jl 0 (rd n r u C.output);rw[e,rd_eq]
   rw[this];exact hrm)
  have hlout: lw2 n jl r C1.output=C.output:=lw2r hjr hon0 hne_out
  have hcf_f: vl C.gates x_lp C.output=false:=by
   rw[←hlout];apply hP_false C1.output h1ol
   ·intro han;rcases hrm with hL|⟨_,_⟩
    ·simp only[topLeaves,mU,mI,mF] at hL
     rcases hL with ⟨a,ha,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
     ·exact ⟨fun e => hlnA (Fin.ext (hea.trans e).symm ▸ ha),fun e => hpnA (Fin.ext (hea.trans e).symm ▸ ha)⟩
     ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;omega
    ·omega
   ·intro k _ ek;rcases hrm with hL|⟨_,hG⟩
    ·simp only[topLeaves,mU,mI,mF] at hL
     rcases hL with ⟨a,_,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
     ·have:=a.isLt;omega
     ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1
      have: k=jb := (by omega);right;left;rw[this,hrb_s]
    ·left;have hG' := (mF.mp hG).2;rw[ek,ascl] at hG';exact hG'
  rw[hcf_f] at hlpC;cases hlpC
 rcases hu1_cases with hu1_top|hu1_Zq
 ·
  have hnt0: ∀ j' < C1.gates.length,(d1.role j').1≠Kind.top →
    n+r∉(gateAt C (li2 jl r j')).inputs:=by
   intro j' hj' hnt hm;have hu1_in:=hnu1 j' hj' hm
   rcases hrol1 j' hj' with ht' | ⟨t,ht,hrt2,hrb_t⟩
   ·exact hnt ht'
   ·cases hkr: (d1.role j').1 with
    | top => exact hnt hkr
    | b =>
     have hbw:=hrb_t hkr;obtain ⟨jb,hjb,hbw2,_,_,hin⟩:=(h1c t ht).1
     have hje: j' = jb:=by omega
     rw[hje] at hu1_in
     rcases hin with h|h <;> rw[h] at hu1_in <;> simp at hu1_in <;> rcases hu1_in with e|e
     ·apply htZd t ht u1 hu1_top
      rw[e];rcases zrs hv1 t ht with hz|⟨jz,hjz,hz,hrz⟩
      ·exact Or.inl (hz ▸ mNs _ _)
      ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩
     ·
      rcases ors hv1 t ht with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
      ·have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
       ·apply htZd r' hrc u1 hu1_top;rw[e,hlam']
        rcases hlam.2.1 with hz|⟨jz,hjz,hz,hrz⟩
        ·exact Or.inl (hz ▸ mNs _ _)
        ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩
       ·rw[hlam',hlam] at e
        rcases hu1_top with hL|⟨hg,_⟩
        ·simp only[topLeaves,mU,mI,mF] at hL
         rcases hL with ⟨a,ha,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
         ·exact hA a ha t (Fin.ext (hea.trans e) ▸ ((hK1 t r').mp (hown1.1 t r' hown').1).1.symm)
         ·obtain ⟨jb',_,hbw',_,_,_⟩:=(h1c s hs).1;have := r'.isLt;omega
        ·have := r'.isLt;omega
      ·rw[hor] at e
       rcases hu1_top with hL|⟨_,hG⟩
       ·simp only[topLeaves,mU,mI,mF] at hL
        rcases hL with ⟨a,_,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
        ·have:=a.isLt;omega
        ·obtain ⟨jb',_,hbw',hrb_s,_,_⟩:=(h1c s hs).1
         have: jb' = jo := (by omega);rw[this,hro] at hrb_s;cases hrb_s
       ·have hG' := (mF.mp hG).2;rw[e,ascl,hro] at hG';cases hG'
     ·rcases ors hv1 t ht with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
      ·have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
       ·apply htZd r' hrc u1 hu1_top;rw[e,hlam']
        rcases hlam.2.1 with hz|⟨jz,hjz,hz,hrz⟩
        ·exact Or.inl (hz ▸ mNs _ _)
        ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩
       ·rw[hlam',hlam] at e
        rcases hu1_top with hL|⟨hg,_⟩
        ·simp only[topLeaves,mU,mI,mF] at hL
         rcases hL with ⟨a,ha,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
         ·exact hA a ha t (Fin.ext (hea.trans e) ▸ ((hK1 t r').mp (hown1.1 t r' hown').1).1.symm)
         ·obtain ⟨jb',_,hbw',_,_,_⟩:=(h1c s hs).1;have := r'.isLt;omega
        ·have := r'.isLt;omega
      ·rw[hor] at e
       rcases hu1_top with hL|⟨_,hG⟩
       ·simp only[topLeaves,mU,mI,mF] at hL
        rcases hL with ⟨a,_,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
        ·have:=a.isLt;omega
        ·obtain ⟨jb',_,hbw',hrb_s,_,_⟩:=(h1c s hs).1
         have: jb' = jo := (by omega);rw[this,hro] at hrb_s;cases hrb_s
       ·have hG' := (mF.mp hG).2;rw[e,ascl,hro] at hG';cases hG'
     ·apply htZd t ht u1 hu1_top
      rw[e];rcases zrs hv1 t ht with hz|⟨jz,hjz,hz,hrz⟩
      ·exact Or.inl (hz ▸ mNs _ _)
      ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩
    | z =>
     have hjZ: j' ∈ gatesOf d1 C1 Kind.z t.val:=mF.mpr ⟨mR.mpr hj',Prod.ext hkr hrt2⟩;exact htZd t ht u1 hu1_top (((h1c t ht).2.1.1 j' hjZ).2.2 u1 hu1_in)
    | o =>
     have hjO: j' ∈ gatesOf d1 C1 Kind.o t.val:=mF.mpr ⟨mR.mpr hj',Prod.ext hkr hrt2⟩
     rcases ((h1c t ht).2.2.1.1 j' hjO).2.2 u1 hu1_in with hL|⟨_,hG⟩
     ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',he⟩:=hL;have hlam:=(h1c t ht).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
      ·apply htZd r' hrc u1 hu1_top;rw[←he]
       rcases hlam.2.1 with hz|⟨jz,hjz,hz,hrz⟩
       ·exact Or.inl (hz ▸ mNs _ _)
       ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩
      ·rw[hlam] at he
       rcases hu1_top with hLt|⟨_,_⟩
       ·simp only[topLeaves,mU,mI,mF] at hLt
        rcases hLt with ⟨a,ha,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
        ·exact hA a ha t (Fin.ext (hea.trans he.symm) ▸ ((hK1 t r').mp (hown1.1 t r' hown').1).1.symm)
        ·obtain ⟨jb',_,hbw',_,_,_⟩:=(h1c s hs).1;have := r'.isLt;omega
       ·have := r'.isLt;omega
     ·rcases hu1_top with hLt|⟨_,hGt⟩
      ·simp only[topLeaves,mU,mI,mF] at hLt
       rcases hLt with ⟨a,_,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
       ·have:=a.isLt;omega
       ·obtain ⟨jb',_,hbw',hrb_s,_,_⟩:=(h1c s hs).1;have hG' := (mF.mp hG).2;rw[←hes,hbw',ascl,hrb_s] at hG';cases hG'
      ·have h1:=(mF.mp hG).2;have h2:=(mF.mp hGt).2;rw[h1] at h2;cases h2
  have htpc: (u1=C1.output∧C.output=n+r ∧ ∀ j' ∈ topGates d1 C1,n+r∉(gateAt C (li2 jl r j')).inputs) ∨
    (u1≠C1.output∧C.output≠n+r ∧ ∃ q0' ∈ topGates d1 C1,
     n+r∈(gateAt C (li2 jl r q0')).inputs ∧
     ∀ j' ∈ topGates d1 C1,j' ≠ q0' → n+r∉(gateAt C (li2 jl r j')).inputs):=by
   have hrl1: readsIn C1 (topGates d1 C1) u1=if u1=C1.output then 0 else 1:=by
    rcases hu1_top with hL|⟨hg,hG⟩
    ·exact (htop1.2.1 u1 hL).2
    ·have:=htop1.2.2.1 (u1 - n) hG;rwa[show n+(u1 - n)=u1 by omega] at this
   by_cases he: u1=C1.output
   ·left
    have hno_t: ∀ j' ∈ topGates d1 C1,n+r∉(gateAt C (li2 jl r j')).inputs:=by
     intro j' hj' hm;have h1: 1 ≤ (gateAt C1 j').inputs.count u1:=lcpi.mpr (hnu1 j' (htGl j' hj') hm)
     have hle: (gateAt C1 j').inputs.count u1 ≤ readsIn C1 (topGates d1 C1) u1 :=
      single_le_sum (f := fun m => (gateAt C1 m).inputs.count u1) (fun _ _ => Nat.zero_le _) hj'
     rw[if_pos he] at hrl1;omega
    have hout_r: C.output=n+r:=by
     by_contra hne
     have hlout: lw2 n jl r C1.output=C.output:=lw2r hjr hon0 hne
     have hcout_u: C.output=u:=by rw[←hlout,←he,hu_lw]
     rw[hcout_u,hvl_u x_lp,he,hlp1] at hlpC;cases hlpC
    exact ⟨he,hout_r,hno_t⟩
   ·right
    have hne_out: C.output≠n+r:=fun e => he (by change u1=rd n jl 0 (rd n r u C.output);rw[e,rd_eq])
    rw[if_neg he] at hrl1
    have hpos: 0 < ∑ k∈topGates d1 C1,(gateAt C1 k).inputs.count u1:=by change 0 < readsIn C1 (topGates d1 C1) u1;omega
    obtain ⟨q0',hq0',hcnt⟩:=exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos)
    have huniq_q0: ∀ j' ∈ topGates d1 C1,u1∈(gateAt C1 j').inputs → j' = q0' := by
     intro j' hj' hm;by_contra hne';have h1: 1 ≤ (gateAt C1 q0').inputs.count u1:=Nat.pos_of_ne_zero hcnt;have h2: 1 ≤ (gateAt C1 j').inputs.count u1:=lcpi.mpr hm
     have hsub: ({q0',j'}: Finset ℕ)⊆topGates d1 C1:=by intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
     have hsum:=sum_le_sum_of_subset (f:=fun m => (gateAt C1 m).inputs.count u1) hsub
     rw[sum_pair (Ne.symm hne')] at hsum;change _ ≤ readsIn C1 (topGates d1 C1) u1 at hsum;omega
    have hnoo: ∀ j' ∈ topGates d1 C1,j' ≠ q0' → n+r∉(gateAt C (li2 jl r j')).inputs:=fun j' hj' hne' hm =>
     hne' (huniq_q0 j' hj' (hnu1 j' (htGl j' hj') hm))
    have hq0_read: n+r∈(gateAt C (li2 jl r q0')).inputs:=by
     by_contra hnot
     have hno_any: ∀ k' < C1.gates.length,n+r∉(gateAt C (li2 jl r k')).inputs:=by
      intro k' hk' hm
      by_cases hkt: (d1.role k').1=Kind.top
      ·have hkT: k' ∈ topGates d1 C1:=mF.mpr ⟨mR.mpr hk',hkt⟩
       by_cases hkq: k' = q0'
       ·exact hnot (hkq ▸ hm)
       ·exact hnoo k' hkT hkq hm
      ·exact hnt0 k' hk' hkt hm
     have hall_eq: ∀ w < n+C1.gates.length,vl C.gates x_lp (lw2 n jl r w)=vl C1.gates x_lp w:=by
      intro w;induction w using Nat.strong_induction_on with
      | ind w ih =>
       intro hw;by_cases hwn: w < n
       ·rw[lw2i n jl r w hwn,vli _ _ w hwn,vli _ _ w hwn]
       ·set k' := w - n;have hk' : k' < C1.gates.length:=by omega
        have hlif:=r2l C hcl hrb hjr hr hu k' (by omega);have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur k' (by omega) (hno_any k' hk');have hlt_C: li2 jl r k' < C.gates.length:=li2lt hjr hr (by rw[←hlen1];exact hk')
        have hgC: C.gates[li2 jl r k']? = some (gateAt C (li2 jl r k')):=by simp[gateAt,List.getD,hlt_C]
        have hg1: C1.gates[k']? = some (gateAt C1 k'):=by simp[gateAt,List.getD,hk']
        rw[show w=n + k' by omega,lw2g,vlg C.gates hcl x_lp _ _ hgC,
          vlg C1.gates hcl1 x_lp k' _ hg1,←hlif.1,hinp,lmp]
        congr 1;apply List.map_congr_left;intro a ha
        exact ih a (by have := hrb1 k' hk' a ha;omega) (by have := hrb1 k' hk' a ha;omega)
     have hlout: lw2 n jl r C1.output=C.output:=lw2r hjr hon0 hne_out;have h1:=hall_eq C1.output h1ol;rw[hlout,hlpC,hlp1] at h1;cases h1
    exact ⟨he,hne_out,q0',hq0',hq0_read,hnoo⟩
  have htop_C: IsOrTree n C (insert r ((topGates d1 C1).image (li2 jl r)))
    (insert (n+jl) ((topLeaves d1 A).image (lw2 n jl r))) C.output:=by
   have hout_eq: C.output=if u1=C1.output then n+r else lw2 n jl r C1.output:=by
    rcases htpc with ⟨he,hr_out,_⟩ | ⟨hne,hne_out,_⟩
    ·simp[he,hr_out]
    ·rw[if_neg hne,lw2r hjr hon0 hne_out]
   rw[hout_eq]
   exact ot2i C hrb hjr hr hu hune hon0 hur hro0 hri0 htop1
    (fun j' hj' => by have := htGl j' hj';omega)
    (by
      rcases htpc with ⟨he,_,hno⟩ | ⟨hne,_,q0',hq0',hq0_r,hno⟩
      ·exact Or.inl ⟨he,hno⟩
      ·exact Or.inr ⟨hne,q0',hq0',hq0_r,hno⟩)
  have hw1p: wl1=p.val:=by
   rcases hw1c with h|⟨hge,hj_lt,hro⟩
   ·exact h
   ·exfalso
    set jo:=wl1 - n;have hjo_O: jo∈gatesOf d1 C1 Kind.o q.val:=mF.mpr ⟨mR.mpr hj_lt,hro⟩;have hOq:=(h1c q hq_cov).2.2.1;have hcard:=osC2 hrb1 hOq (hOGl q) hjo_O;obtain ⟨v1,hv1_m,v2,hv2_m,hv12⟩:=one_lt_card.mp (by omega: 1 < (osL n C1 (gatesOf d1 C1 Kind.o q.val) (oLeaves d1 q) (n+jo)).card);have hsubO:=(osS hrb1 hOq (hOGl q) (n+jo)).2.1;have hv1_o:=hsubO hv1_m;have hv2_o:=hsubO hv2_m;simp only[oLeaves,mI,mF,mV,true_and] at hv1_o hv2_o;obtain ⟨r1,hr1,hv1_eq⟩:=hv1_o;obtain ⟨r2,hr2,hv2_eq⟩:=hv2_o
    have hr12: r1≠r2:=fun e => hv12 (by rw[←hv1_eq,←hv2_eq,e])
    obtain ⟨r',hr'_own,hr'_ne_p,hr'_mem⟩ : ∃ r',d1.owns q r' = true ∧ r' ≠ p ∧
      d1.lam q r' ∈ osL n C1 (gatesOf d1 C1 Kind.o q.val) (oLeaves d1 q) (n+jo):=by
     by_cases h1: r1=p
     ·exact ⟨r2,hr2,fun e => hr12 (h1.trans e.symm),hv2_eq ▸ hv2_m⟩
     ·exact ⟨r1,hr1,h1,hv1_eq ▸ hv1_m⟩
    have hr'_adj:=(hK1 q r').mp (hown1.1 q r' hr'_own).1
    have hr'_notA: r' ∉ A:=fun h => hA r' h q hr'_adj.1.symm
    let x_lr: Fin n→Bool:=fun v => decide (v=l∨v = r')
    have hwl_t: vl C1.gates x_lr wl1=true:=by
     rw[show wl1=n+jo by omega];apply (osV hcl1 hrb1 hOq (hOGl q) x_lr (n+jo) (Or.inr ⟨by omega,by simpa using hjo_O⟩)).mpr
     refine ⟨d1.lam q r',hr'_mem,?_⟩
     have hlam:=(h1c q hq_cov).2.2.2 r' hr'_own;unfold LamOK at hlam;split_ifs at hlam with hrc
     ·exact ncx hv1 r' hrc x_lr (by simp[x_lr]) (d1.lam q r') hlam.1
       (by rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩;exact Or.inl h;exact Or.inr ⟨jz,hjz,h1,h2⟩)
     ·rw[hlam,vli C1.gates x_lr r'.val r'.isLt];simp[x_lr]
    have hnr_t: vl C.gates x_lr (n+r)=true:=by rw[hvl_r,hwl_t];simp[x_lr]
    have hC_t: vl C.gates x_lr C.output=true:=by
     have hGltC: ∀ k∈insert r ((topGates d1 C1).image (li2 jl r)),k < C.gates.length:=by
      intro k hk;rcases mN.mp hk with rfl | hk'
      ·exact hr
      ·obtain ⟨j',hj',rfl⟩:=mI.mp hk';exact li2lt hjr hr (by have:=htGl j' hj';omega)
     have hrm: C.output∈insert (n+jl) ((topLeaves d1 A).image (lw2 n jl r)) ∨
       (n ≤ C.output∧C.output - n∈insert r ((topGates d1 C1).image (li2 jl r))):=by
      have h1:=htop_C.2.2.2;simp only[insert_ne_empty,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;exact Or.inr ⟨by omega,by rw[hρ,ascl];exact hg⟩
     have hsa:=osRL hrb htop_C hGltC;apply (osV hcl hrb htop_C hGltC x_lr C.output hrm).mpr
     refine ⟨n+jl,by rw[hsa.2];exact mNs _ _,?_⟩
     have hgj: C.gates[jl]? = some (gateAt C jl):=by simp[gateAt,List.getD,show jl < C.gates.length by omega]
     rw[vlg C.gates hcl x_lr jl _ hgj,hjlo]
     have hxl_t: x_lr l=true:=by simp[x_lr]
     rcases hjli with h|h <;> rw[h] <;>
      simp[GateOp.eval,vli C.gates x_lr l.val l.isLt,hvl_wl x_lr,hwl_t,hxl_t]
    rw[hval_C] at hC_t;simp only[graphFun,boT,dTe,x_lr] at hC_t
    rcases hC_t with ⟨a,ha,hal|har⟩ | ⟨a,b,hab,hal|har,hbl|hbr⟩
    ·exact hlnA (hal ▸ ha)
    ·exact hr'_notA (har ▸ ha)
    ·exact hab.ne (hal.trans hbl.symm)
    ·exact hr'_ne_p ((hl r').mp (hal ▸ hbr ▸ hab))
    ·exact hr'_ne_p ((hl r').mp (hbl ▸ har ▸ hab.symm))
    ·exact hab.ne (har.trans hbr.symm)
  have hwp0: wl=p.val:=by rw[←hwl_lw,hw1p,lw2i n jl r p.val p.isLt]
  let roleA: ℕ → Kind × ℕ := fun j =>
   if j=jl then (Kind.b,l.val)
   else if j=r then (Kind.top,0)
   else d1.role (rd 0 jl 0 (rd 0 r 0 j))
  have hrl: ∀ j' : ℕ,roleA (li2 jl r j')=d1.role j' := by
   intro j';simp only[roleA,li2nj jl r j' hjr,li2nr jl r j',↓reduceIte]
   congr 1
   have hlift_eq: li2 jl r j' = lw2 0 jl r j' := by unfold li2 lw2 li1 lw1;simp
   rw[hlift_eq];exact rd2l
  let d: NCCData n:={
   cover := insert l d1.cover
   owns := fun a b => if a=l∧b=p then true else d1.owns a b
   tie := d1.tie
   role := roleA
   bw := fun t => if t=l then n+jl else lw2 n jl r (d1.bw t)
   zroot := fun t => if t=l then l.val else lw2 n jl r (d1.zroot t)
   oroot := fun t => if t=l then p.val else lw2 n jl r (d1.oroot t)
   lam := fun t v => if t=l then p.val else lw2 n jl r (d1.lam t v)
  }
  have hgn: ∀ (k: Kind) (v: ℕ),k≠Kind.top→(k,v)≠(Kind.b,l.val) →
    gatesOf d C k v=(gatesOf d1 C1 k v).image (li2 jl r):=by
   intro k v hnt hnb
   ext j;simp only[gatesOf,d,mF,mR,mI]
   constructor
   ·rintro ⟨hj,hrj⟩
    have hje: j≠jl:=fun e => hnb (by rw[←hrj,e];simp[roleA])
    have hre: j≠r:=fun e => hnt (by rw[e] at hrj;simp[roleA,Nat.ne_of_gt hjr] at hrj;exact hrj.1.symm)
    obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre;exact ⟨j',⟨by omega,by rw[←hrl j'];exact hrj⟩,rfl⟩
   ·rintro ⟨j',⟨hj',hrj'⟩,rfl⟩
    exact ⟨li2lt hjr hr (by omega),by rw[hrl,hrj']⟩
  refine ⟨d,hrb,?_,?_,?_,?_,?_,?_⟩
  ·
   refine ⟨?_,fun T hT => by have := htK1 T hT;simp only[d,card_insert_of_notMem hlnc];omega⟩
   intro a b hab
   by_cases hal: a=l
   ·left;exact mC.mpr (hal ▸ mNs l _)
   ·by_cases hbl: b=l
    ·right;exact mC.mpr (hbl ▸ mNs l _)
    ·rcases hmc1.1 ((hK1 a b).mpr ⟨hab,hal,hbl⟩) with ha|hb
     ·left;exact mC.mpr (mNo (mC.mp ha))
     ·right;exact mC.mpr (mNo (mC.mp hb))
  ·
   refine ⟨?_,?_⟩
   ·intro a b hown;dsimp[d] at hown;split_ifs at hown with h
    ·exact ⟨by rw[h.1,h.2];exact (hl p).mpr rfl,by rw[h.1];exact mNs _ _⟩
    ·have h1:=hown1.1 a b hown;exact ⟨((hK1 a b).mp h1.1).1,mNo h1.2⟩
   ·intro a b hab
    by_cases hal: a=l
    ·rw[hal] at hab ⊢;have hbp: b=p:=(hl b).mp hab;rw[hbp]
     have hb_no: d1.owns p l=false:=by cases h: d1.owns p l;rfl;exact absurd (hown1.1 p l h).1.symm (hl_iso p)
     dsimp[d];simp[hlp,hlp.symm,hb_no]
    ·by_cases hbl: b=l
     ·rw[hbl] at hab ⊢;have hap: a=p:=(hl a).mp hab.symm;rw[hap]
      have ha_no: d1.owns p l=false:=by cases h: d1.owns p l;rfl;exact absurd (hown1.1 p l h).1.symm (hl_iso p)
      dsimp[d];simp[hlp,hlp.symm,ha_no]
     ·dsimp[d];simp[hal,hbl,hown1.2 a b ((hK1 a b).mpr ⟨hab,hal,hbl⟩)]
  ·
   intro s t hst;have h1:=htie1 s t hst
   refine ⟨mNo h1.1,?_⟩
   dsimp[d];split_ifs
   ·rfl
   ·exact h1.2
  ·
   intro j hj
   by_cases hje: j=jl
   ·rw[hje];right;exact ⟨l,mNs _ _,by simp[d,roleA],fun _ => by simp[d]⟩
   ·by_cases hre: j=r
    ·rw[hre];exact Or.inl (by simp[d,roleA,Nat.ne_of_gt hjr])
    ·obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
     rcases hrol1 j' (by omega) with ht' | ⟨t,ht,e1,e2⟩
     ·exact Or.inl (by dsimp[d];rw[hrl];exact ht')
     ·right;refine ⟨t,mNo ht,by dsimp[d];rw[hrl];exact e1,fun hk => ?_⟩
      dsimp[d] at hk ⊢;rw[hrl] at hk
      have htl: t≠l:=fun e => hlnc (e ▸ ht)
      simp only[htl,↓reduceIte];rw[e2 hk,lw2g]
  ·
   intro t ht
   by_cases htl: t=l
   ·rw[htl]
    refine ⟨?_,?_,?_,?_⟩
    ·refine ⟨jl,by omega,by simp[d],by simp[d,roleA],hjlo,?_⟩
     dsimp[d];simp only[↓reduceIte];rw[←hwp0];exact hjli
    ·have hG: gatesOf d C Kind.z l.val = ∅ := by
      rw[hgn Kind.z l.val (by simp) (by simp)]
      have hE: gatesOf d1 C1 Kind.z l.val = ∅ := by
       ext j';simp only[gatesOf,mF,mR,notMem_empty,iff_false,not_and]
       intro hj' hrj'
       rcases hrol1 j' hj' with ht' | ⟨s,hs,e1,_⟩
       ·rw[hrj'] at ht';cases ht'
       ·rw[hrj'] at e1;exact hlnc (Fin.ext e1.symm ▸ hs)
      simp[hE]
     have hL: zLeaves d l={l.val}:=by
      ext w;simp only[zLeaves,d,mN,mI,mF,mS,or_iff_left_iff_imp]
      rintro ⟨s,⟨_,hst⟩,_⟩;exact absurd (hown1.1 l s (htie1 s l hst).2).1 (hl_iso s)
     rw[hG,hL];dsimp[d];simp only[↓reduceIte]
     exact ⟨by simp,fun w hw => by rw[mS.mp hw];simp[readsIn],by simp,by simp⟩
    ·have hG: gatesOf d C Kind.o l.val = ∅ := by
      rw[hgn Kind.o l.val (by simp) (by simp)]
      have hE: gatesOf d1 C1 Kind.o l.val = ∅ := by
       ext j';simp only[gatesOf,mF,mR,notMem_empty,iff_false,not_and]
       intro hj' hrj'
       rcases hrol1 j' hj' with ht' | ⟨s,hs,e1,_⟩
       ·rw[hrj'] at ht';cases ht'
       ·rw[hrj'] at e1;exact hlnc (Fin.ext e1.symm ▸ hs)
      simp[hE]
     have hL: oLeaves d l={p.val}:=by
      ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
       mS,↓reduceIte]
      constructor
      ·rintro ⟨v,_,rfl⟩;rfl
      ·rintro rfl;exact ⟨p,by simp,rfl⟩
     rw[hG,hL];dsimp[d];simp only[↓reduceIte]
     exact ⟨by simp,fun w hw => by rw[mS.mp hw];simp[readsIn],by simp,by simp⟩
    ·intro v hown;dsimp[d] at hown
     have hvp: v=p:=by
      simp only[true_and] at hown;split_ifs at hown with h;exact h;exact absurd (hown1.1 l v hown).1 (hl_iso v)
     rw[hvp];unfold LamOK;dsimp[d];simp[hlp.symm,hpnc]
   ·have ht1: t∈d1.cover:=by rcases mN.mp ht with rfl|h;exact absurd rfl htl;exact h
    refine ⟨?_,?_,?_,?_⟩
    ·obtain ⟨jb,hjb,hbw,hrb_t,hop,hin⟩:=(h1c t ht1).1;have hno:=hnt0 jb hjb (by rw[hrb_t];intro hc;cases hc);have hlif:=r2l C hcl hrb hjr hr hu jb (by omega);have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jb (by omega) hno
     refine ⟨li2 jl r jb,li2lt hjr hr (by omega),by dsimp[d];simp[htl,hbw,lw2g],
      by dsimp[d];rw[hrl,hrb_t],by rw[←hlif.1,hop],?_⟩
     rw[hinp];rcases hin with h|h <;> rw[h] <;> simp[d,htl]
    ·have hG: gatesOf d C Kind.z t.val=(gatesOf d1 C1 Kind.z t.val).image (li2 jl r) :=
      hgn Kind.z t.val (by simp) (by simp)
     have hL: zLeaves d t=(zLeaves d1 t).image (lw2 n jl r):=by
      ext w;simp only[zLeaves,d,mN,mI,mF]
      constructor
      ·rintro (rfl|⟨s,⟨_,hst⟩,rfl⟩)
       ·exact ⟨t.val,Or.inl rfl,lw2i n jl r t.val t.isLt⟩
       ·have hs1:=(htie1 s t hst).1
        have hsl: s≠l:=fun e => hlnc (e ▸ hs1)
        simp only[hsl,↓reduceIte];exact ⟨d1.bw s,Or.inr ⟨s,⟨hs1,hst⟩,rfl⟩,rfl⟩
      ·rintro ⟨_,rfl|⟨s,⟨hs,hst⟩,rfl⟩,rfl⟩
       ·exact Or.inl (lw2i n jl r t.val t.isLt)
       ·have hsl: s≠l:=fun e => hlnc (e ▸ hs)
        exact Or.inr ⟨s,⟨Or.inr hs,hst⟩,by simp[hsl]⟩
     rw[hG,hL];dsimp[d];simp only[htl,↓reduceIte]
     exact ot2u C hcl hrb hjr hr hu hune hon0 hur (h1c t ht1).2.1
      (fun j' hj' => by have := hZGl t j' hj';omega)
      (fun j' hj' => hnt0 j' (hZGl t j' hj') (by rw[(mF.mp hj').2];intro hc;cases hc))
    ·have hG: gatesOf d C Kind.o t.val=(gatesOf d1 C1 Kind.o t.val).image (li2 jl r) :=
      hgn Kind.o t.val (by simp) (by simp)
     have hL: oLeaves d t=(oLeaves d1 t).image (lw2 n jl r):=by
      ext w;simp only[oLeaves,d,mI,mF,mV,true_and,htl,false_and,↓reduceIte]
      constructor
      ·rintro ⟨v,hown,rfl⟩;exact ⟨d1.lam t v,⟨v,hown,rfl⟩,rfl⟩
      ·rintro ⟨_,⟨v,hown,rfl⟩,rfl⟩;exact ⟨v,hown,rfl⟩
     rw[hG,hL];dsimp[d];simp only[htl,↓reduceIte]
     exact ot2u C hcl hrb hjr hr hu hune hon0 hur (h1c t ht1).2.2.1
      (fun j' hj' => by have := hOGl t j' hj';omega)
      (fun j' hj' => hnt0 j' (hOGl t j' hj') (by rw[(mF.mp hj').2];intro hc;cases hc))
    ·intro v hown;dsimp[d] at hown;simp only[htl,false_and,↓reduceIte] at hown
     have hvl: v≠l:=fun e => hl_iso t (e ▸ (hown1.1 t v hown).1).symm
     have hlam:=(h1c t ht1).2.2.2 v hown;unfold LamOK at hlam ⊢;dsimp[d];simp only[htl,↓reduceIte]
     by_cases hvc: v∈d1.cover
     ·have hvc' : v∈insert l d1.cover:=mNo hvc;simp only[hvc,hvc',↓reduceIte] at hlam ⊢
      refine ⟨?_,?_,?_⟩
      ·exact cf2 (d := d) C hcl hrb hjr hr hu hune hon0 hur hv1 d1.cover
        (Subset.refl _) (subset_insert l d1.cover)
        (fun j' hj' hrz => ⟨hnt0 j' (by omega) (by rw[hrz];intro hc;cases hc),by dsimp[d];rw[hrl,hrz]⟩)
        v hvc (d1.lam t v) hlam.1 (by rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩;exact Or.inl h;exact Or.inr ⟨jz,by omega,h1,h2⟩)
      ·rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
       ·exact Or.inl (by rw[h,lw2i n jl r v.val v.isLt])
       ·exact Or.inr ⟨li2 jl r jz,li2lt hjr hr (by omega),by rw[h1,lw2g],by rw[hrl,h2]⟩
      ·intro htie;simp only[hvl,↓reduceIte];rw[hlam.2.2 htie]
     ·have hvc' : v∉insert l d1.cover:=by simp[hvl,hvc]
      simp only[hvc,hvc',↓reduceIte] at hlam ⊢;rw[hlam,lw2i n jl r v.val v.isLt]
  ·
   have hG: topGates d C=insert r ((topGates d1 C1).image (li2 jl r)):=by
    ext j;simp only[topGates,d,mF,mR,mN,mI]
    constructor
    ·rintro ⟨hj,hrj⟩
     by_cases hre: j=r
     ·exact Or.inl hre
     ·right
      have hje: j≠jl:=fun e => by rw[e] at hrj;simp[roleA] at hrj
      obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre;exact ⟨j',⟨by omega,by rw[←hrl j'];exact hrj⟩,rfl⟩
    ·rintro (rfl|⟨j',⟨hj',hrj'⟩,rfl⟩)
     ·exact ⟨hr,by simp[roleA,Nat.ne_of_gt hjr]⟩
     ·exact ⟨li2lt hjr hr (by omega),by rw[hrl,hrj']⟩
   have hL: topLeaves d A=insert (n+jl) ((topLeaves d1 A).image (lw2 n jl r)):=by
    ext w;simp only[topLeaves,d,mU,mI,mF,mN]
    constructor
    ·rintro (⟨a,ha,rfl⟩ | ⟨s,⟨hs,hst⟩,rfl⟩)
     ·right;exact ⟨a.val,Or.inl ⟨a,ha,rfl⟩,lw2i n jl r a.val a.isLt⟩
     ·by_cases hsl: s=l
      ·left;simp[hsl]
      ·right;simp only[hsl,↓reduceIte]
       have hs1: s∈d1.cover:=by rcases hs with rfl|h;exact absurd rfl hsl;exact h
       exact ⟨d1.bw s,Or.inr ⟨s,⟨hs1,hst⟩,rfl⟩,rfl⟩
    ·rintro (rfl|⟨w',hw',rfl⟩)
     ·right;exact ⟨l,⟨Or.inl rfl,by
       cases h: d1.tie l with
       | none => rfl
       | some t => exfalso;exact hlnc (htie1 l t h).1⟩,by simp⟩
     ·rcases hw' with ⟨a,ha,rfl⟩ | ⟨s,⟨hs,hst⟩,rfl⟩
      ·left;exact ⟨a,ha,(lw2i n jl r a.val a.isLt).symm⟩
      ·right;have hsl: s≠l := fun e => hlnc (e ▸ hs)
       exact ⟨s,⟨Or.inr hs,hst⟩,by simp[hsl]⟩
   rw[hG,hL];exact htop_C
 ·
  have hZq:=(h1c q hq_cov).2.1
  have hnt1: ∀ j' ∈ topGates d1 C1,n+r∉(gateAt C (li2 jl r j')).inputs:=fun j' hj' hm =>
   htZd q hq_cov u1 ((htop1.1 j' hj').2.2 u1 (hnu1 j' (htGl j' hj') hm)) hu1_Zq
  have hnZn: ∀ t∈d1.cover,t≠q→∀ j' ∈ gatesOf d1 C1 Kind.z t.val,
    n+r∉(gateAt C (li2 jl r j')).inputs := fun t ht htq j' hj' hm =>
   hZd t q ht hq_cov htq u1 (((h1c t ht).2.1.1 j' hj').2.2 u1 (hnu1 j' (hZGl t j' hj') hm)) hu1_Zq
  have hnOq: ∀ j' ∈ gatesOf d1 C1 Kind.o q.val,n+r∉(gateAt C (li2 jl r j')).inputs:=fun j' hj' hm =>
   hOZd q hq_cov u1 (((h1c q hq_cov).2.2.1.1 j' hj').2.2 u1 (hnu1 j' (hOGl q j' hj') hm)) hu1_Zq
  have hne_out: C.output≠n+r:=fun e => by
   have hu_out: u1=C1.output:=by change rd n jl 0 u=rd n jl 0 (rd n r u C.output);rw[e,rd_eq]
   have hrm: C1.output∈topLeaves d1 A∨(n ≤ C1.output∧C1.output - n∈topGates d1 C1):=by
    by_cases hGe: topGates d1 C1 = ∅
    ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
    ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
   exact htZd q hq_cov u1 (hu_out ▸ hrm) hu1_Zq
  obtain ⟨jbq,hjbq,hbwq,hrbq,hop_bq,hin_bq⟩:=(h1c q hq_cov).1
  have hZqc: (u1=d1.zroot q∧n+r∈(gateAt C (li2 jl r jbq)).inputs ∧
     ∀ j' ∈ gatesOf d1 C1 Kind.z q.val,n+r∉(gateAt C (li2 jl r j')).inputs) ∨
    (u1≠d1.zroot q∧n+r∉(gateAt C (li2 jl r jbq)).inputs ∧
     ∃ q0' ∈ gatesOf d1 C1 Kind.z q.val,n+r∈(gateAt C (li2 jl r q0')).inputs ∧
      ∀ j' ∈ gatesOf d1 C1 Kind.z q.val,j' ≠ q0' → n+r∉(gateAt C (li2 jl r j')).inputs):=by
   have hrl1: readsIn C1 (gatesOf d1 C1 Kind.z q.val) u1=if u1=d1.zroot q then 0 else 1:=by
    rcases hu1_Zq with hL|⟨hg,hG⟩
    ·exact (hZq.2.1 u1 hL).2
    ·have:=hZq.2.2.1 (u1 - n) hG;rwa[show n+(u1 - n)=u1 by omega] at this
   have hnZq: n+r∉(gateAt C (li2 jl r jbq)).inputs →
     (∀ j' ∈ gatesOf d1 C1 Kind.z q.val,n+r∉(gateAt C (li2 jl r j')).inputs)→False:=by
    intro hno_bq hno_zq
    have hfalse: ∀ w < n+C1.gates.length,
      (w < n → w≠l.val∧w≠p.val) →
      (∀ j' < C1.gates.length,w=n + j' → (d1.role j').1≠Kind.o) →
      vl C.gates x_lp (lw2 n jl r w)=false:=by
     intro w;induction w using Nat.strong_induction_on with
     | ind w ih =>
      intro hw hlt_in hnoO
      by_cases hwn: w < n
      ·rw[lw2i n jl r w hwn,vli C.gates x_lp w hwn];have ⟨h1,h2⟩:=hlt_in hwn
       simp[x_lp,show (⟨w,hwn⟩ : Fin n)≠l from fun e => h1 (congrArg Fin.val e),
        show (⟨w,hwn⟩ : Fin n)≠p from fun e => h2 (congrArg Fin.val e)]
      ·set j' := w - n;have hweq: w=n + j' := by omega
       have hj' : j' < C1.gates.length:=by omega
       have hlt_C: li2 jl r j' < C.gates.length:=li2lt hjr hr (by rw[←hlen1];exact hj')
       have hgC: C.gates[li2 jl r j']? = some (gateAt C (li2 jl r j')):=by simp[gateAt,List.getD,hlt_C]
       have hlif:=r2l C hcl hrb hjr hr hu j' (by omega);rw[hweq,lw2g,vlg C.gates hcl x_lp (li2 jl r j') _ hgC,←hlif.1]
       by_cases htop_j: (d1.role j').1=Kind.top
       ·have hjT: j' ∈ topGates d1 C1:=mF.mpr ⟨mR.mpr hj',htop_j⟩;obtain ⟨hop,_,hins⟩:=htop1.1 j' hjT;have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur j' (by omega) (hnt1 j' hjT);rw[hop,hinp,lmp];simp only[GateOp.eval,lyF,lmm,Function.comp_apply,Bool.not_eq_true,id_eq]
        rintro _ ⟨a,ha,rfl⟩
        have halt: a < n + j' := hrb1 j' hj' a ha;apply ih a (by omega) (by omega)
        ·intro han;rcases hins a ha with hL|⟨_,_⟩
         ·simp only[topLeaves,mU,mI,mF] at hL
          rcases hL with ⟨a',ha',rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
          ·exact ⟨fun e => hlnA (Fin.ext e.symm ▸ ha'),fun e => hpnA (Fin.ext e.symm ▸ ha')⟩
          ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;omega
         ·omega
        ·intro k _ eak;rcases hins a ha with hL|⟨_,hG⟩
         ·simp only[topLeaves,mU,mI,mF] at hL
          rcases hL with ⟨a',_,rfl⟩ | ⟨s,⟨hs,_⟩,rfl⟩
          ·have := a'.isLt;omega
          ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1
           have: k=jb := (by omega);rw[this,hrb_s];intro hc;cases hc
         ·have hG' := (mF.mp hG).2;rw[eak,ascl] at hG';rw[hG'];intro hc;cases hc
       ·rcases hrol1 j' hj' with ht' | ⟨t,ht,hrt2,hrb_t⟩
        ·exact absurd ht' htop_j
        ·cases hkr: (d1.role j').1 with
         | top => exact absurd hkr htop_j
         | o => exact absurd hkr (hnoO j' hj' hweq)
         | z =>
          have hjZ: j' ∈ gatesOf d1 C1 Kind.z t.val:=mF.mpr ⟨mR.mpr hj',Prod.ext hkr hrt2⟩
          have hno_z: n+r∉(gateAt C (li2 jl r j')).inputs:=by
           by_cases htq: t=q
           ·exact hno_zq j' (htq ▸ hjZ)
           ·exact hnZn t ht htq j' hjZ
          obtain ⟨hop,_,hins⟩:=(h1c t ht).2.1.1 j' hjZ;have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur j' (by omega) hno_z;rw[hop,hinp,lmp];simp only[GateOp.eval,lyF,lmm,Function.comp_apply,Bool.not_eq_true,id_eq]
          rintro _ ⟨a,ha,rfl⟩
          have halt: a < n + j' := hrb1 j' hj' a ha;apply ih a (by omega) (by omega)
          ·intro han;rcases hins a ha with hL|⟨_,_⟩
           ·simp only[zLeaves,mN,mI,mF] at hL
            rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
            ·exact ⟨fun e => hlnc (Fin.ext e.symm ▸ ht),fun e => hpnc (Fin.ext e.symm ▸ ht)⟩
            ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;omega
           ·omega
          ·intro k _ eak;rcases hins a ha with hL|⟨_,hG⟩
           ·simp only[zLeaves,mN,mI,mF] at hL
            rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
            ·have:=t.isLt;omega
            ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1
             have: k=jb := (by omega);rw[this,hrb_s];intro hc;cases hc
           ·have hG' := (mF.mp hG).2;rw[eak,ascl] at hG';rw[hG'];intro hc;cases hc
         | b =>
          have hbw:=hrb_t hkr;obtain ⟨jb,hjb,hbw2,_,hop,hin⟩:=(h1c t ht).1
          have hje: j' = jb:=by omega
          rw[hje] at hlif ⊢;rw[hop]
          have hzr_lt: d1.zroot t < n+jb:=hrb1 jb hjb (d1.zroot t) (by rcases hin with h|h <;> simp[h])
          have hzr_f: vl C.gates x_lp (lw2 n jl r (d1.zroot t))=false:=by
           apply ih (d1.zroot t) (by omega) (by omega)
           ·intro han;rcases zrs hv1 t ht with h|⟨_,_,_,_⟩
            ·exact ⟨fun e => hlnc (Fin.ext (h.symm.trans e) ▸ ht),fun e => hpnc (Fin.ext (h.symm.trans e) ▸ ht)⟩
            ·omega
           ·intro k _ ezk;rcases zrs hv1 t ht with h|⟨jz,_,hzr,hrz⟩
            ·have:=t.isLt;omega
            ·have: k=jz := (by omega);rw[this,hrz];intro hc;cases hc
          have hzr_inC: lw2 n jl r (d1.zroot t)∈(gateAt C (li2 jl r jb)).inputs:=by
           by_cases htq: t=q
           ·have hjb_eq: jb=jbq:=by rw[htq,hbwq] at hbw2;omega
            have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jb (by omega) (hjb_eq ▸ hno_bq)
            rw[hinp];exact lmm.mpr ⟨d1.zroot t,by change d1.zroot t∈(gateAt C1 jb).inputs;rcases hin with h|h <;> simp[h],rfl⟩
           ·have hzr_ne_u1: d1.zroot t≠u1:=fun e => hZd t q ht hq_cov htq u1 (by
             rw[←e];rcases zrs hv1 t ht with h|⟨jz,hjz,hzr,hrz⟩
             ·exact Or.inl (h ▸ mNs _ _)
             ·exact Or.inr ⟨by omega,by rw[hzr,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩) hu1_Zq
            have hlenC: (gateAt C (li2 jl r jb)).inputs.length=2:=by
             have h2: (gateAt C1 jb).inputs.length=2:=by rcases hin with h|h <;> simp[h]
             rw[hlif.2,llm] at h2;exact h2
            obtain ⟨x1,x2,hx12⟩:=ll2.mp hlenC
            have hmap: [rd n jl 0 (rd n r u x1),rd n jl 0 (rd n r u x2)]=(gateAt C1 jb).inputs:=by
             rw[hlif.2,hx12];rfl
            have hne_jl: ∀ c∈(gateAt C (li2 jl r jb)).inputs,c≠n+jl:=fun c hc e =>
             li2nr jl r jb (hur (li2 jl r jb) (by rw[←hje];exact hlt_C) (e ▸ hc))
            have hmem1: d1.zroot t∈(gateAt C1 jb).inputs:=by rcases hin with h|h <;> simp[h]
            rw[←hmap] at hmem1;simp at hmem1
            rcases hmem1 with e|e
            ·have hx1_ne_r: x1≠n+r:=fun er => hzr_ne_u1 (by rw[e,er,rd_eq])
             rw[show lw2 n jl r (d1.zroot t)=x1 by rw[e,lw2r hjr (hne_jl x1 (by rw[hx12];simp)) hx1_ne_r],hx12];simp
            ·have hx2_ne_r: x2≠n+r:=fun er => hzr_ne_u1 (by rw[e,er,rd_eq])
             rw[show lw2 n jl r (d1.zroot t)=x2 by rw[e,lw2r hjr (hne_jl x2 (by rw[hx12];simp)) hx2_ne_r],hx12];simp
          simp only[GateOp.eval,laF,lmm,id_eq];exact ⟨false,⟨lw2 n jl r (d1.zroot t),hzr_inC,hzr_f⟩,by simp⟩
    have hrm: C1.output∈topLeaves d1 A∨(n ≤ C1.output∧C1.output - n∈topGates d1 C1):=by
     by_cases hGe: topGates d1 C1 = ∅
     ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
     ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
    have h1:=hfalse C1.output h1ol
     (fun han => by
      rcases hrm with hL|⟨_,_⟩
      ·simp only[topLeaves,mU,mI,mF] at hL
       rcases hL with ⟨a,ha,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
       ·exact ⟨fun e => hlnA (Fin.ext (hea.trans e).symm ▸ ha),fun e => hpnA (Fin.ext (hea.trans e).symm ▸ ha)⟩
       ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;omega
      ·omega)
     (fun k _ ek => by
      rcases hrm with hL|⟨_,hG⟩
      ·simp only[topLeaves,mU,mI,mF] at hL
       rcases hL with ⟨a,_,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
       ·have:=a.isLt;omega
       ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1;have: k=jb:=(by omega);rw[this,hrb_s];intro hc;cases hc
      ·have hG' := (mF.mp hG).2;rw[ek,ascl] at hG';rw[hG'];intro hc;cases hc)
    rw[lw2r hjr hon0 hne_out,hlpC] at h1;cases h1
   by_cases he: u1=d1.zroot q
   ·left
    have hno_z: ∀ j' ∈ gatesOf d1 C1 Kind.z q.val,n+r∉(gateAt C (li2 jl r j')).inputs:=by
     intro j' hj' hm;have h1: 1 ≤ (gateAt C1 j').inputs.count u1:=lcpi.mpr (hnu1 j' (hZGl q j' hj') hm)
     have hle: (gateAt C1 j').inputs.count u1 ≤ readsIn C1 (gatesOf d1 C1 Kind.z q.val) u1 :=
      single_le_sum (f := fun m => (gateAt C1 m).inputs.count u1) (fun _ _ => Nat.zero_le _) hj'
     rw[if_pos he] at hrl1;omega
    have hbq_read: n+r∈(gateAt C (li2 jl r jbq)).inputs:=by
     by_contra hnot;exact hnZq hnot hno_z
    exact ⟨he,hbq_read,hno_z⟩
   ·right
    have hno_bq: n+r∉(gateAt C (li2 jl r jbq)).inputs:=by
     intro hm;have hu1_in:=hnu1 jbq hjbq hm
     rcases hin_bq with h|h <;> rw[h] at hu1_in <;> simp at hu1_in <;> rcases hu1_in with e|e
     ·exact he e
     ·exact hOZd q hq_cov u1 (by
       rw[e];rcases ors hv1 q hq_cov with ⟨r',hown',hlam'⟩ | ⟨jo,hjo,hor,hro⟩
       ·exact Or.inl (by simp only[oLeaves,mI,mF,mV,true_and];exact ⟨r',hown',hlam'.symm⟩)
       ·exact Or.inr ⟨by omega,by rw[hor,ascl];exact mF.mpr ⟨mR.mpr hjo,hro⟩⟩) hu1_Zq
     ·exact hOZd q hq_cov u1 (by
       rw[e];rcases ors hv1 q hq_cov with ⟨r',hown',hlam'⟩ | ⟨jo,hjo,hor,hro⟩
       ·exact Or.inl (by simp only[oLeaves,mI,mF,mV,true_and];exact ⟨r',hown',hlam'.symm⟩)
       ·exact Or.inr ⟨by omega,by rw[hor,ascl];exact mF.mpr ⟨mR.mpr hjo,hro⟩⟩) hu1_Zq
     ·exact he e
    rw[if_neg he] at hrl1
    have hpos: 0 < ∑ k∈gatesOf d1 C1 Kind.z q.val,(gateAt C1 k).inputs.count u1:=by
     change 0 < readsIn C1 (gatesOf d1 C1 Kind.z q.val) u1;omega
    obtain ⟨q0',hq0',hcnt⟩:=exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos)
    have huniq_q0: ∀ j' ∈ gatesOf d1 C1 Kind.z q.val,u1∈(gateAt C1 j').inputs → j' = q0' := by
     intro j' hj' hm;by_contra hne';have h1: 1 ≤ (gateAt C1 q0').inputs.count u1:=Nat.pos_of_ne_zero hcnt;have h2: 1 ≤ (gateAt C1 j').inputs.count u1:=lcpi.mpr hm
     have hsub: ({q0',j'}: Finset ℕ)⊆gatesOf d1 C1 Kind.z q.val:=by intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
     have hsum:=sum_le_sum_of_subset (f:=fun m => (gateAt C1 m).inputs.count u1) hsub
     rw[sum_pair (Ne.symm hne')] at hsum;change _ ≤ readsIn C1 (gatesOf d1 C1 Kind.z q.val) u1 at hsum;omega
    have hnoo: ∀ j' ∈ gatesOf d1 C1 Kind.z q.val,j' ≠ q0' → n+r∉(gateAt C (li2 jl r j')).inputs :=
     fun j' hj' hne' hm => hne' (huniq_q0 j' hj' (hnu1 j' (hZGl q j' hj') hm))
    have hq0_read: n+r∈(gateAt C (li2 jl r q0')).inputs:=by
     by_contra hnot
     exact hnZq hno_bq (fun j' hj' => by by_cases e: j' = q0';exact e ▸ hnot;exact hnoo j' hj' e)
    exact ⟨he,hno_bq,q0',hq0',hq0_read,hnoo⟩
  have hw1p: wl1=p.val:=by
   rcases hw1c with h|⟨hge,hj_lt,hro⟩
   ·exact h
   ·exfalso
    set jo:=wl1 - n;have hjo_O: jo∈gatesOf d1 C1 Kind.o q.val:=mF.mpr ⟨mR.mpr hj_lt,hro⟩;have hOq:=(h1c q hq_cov).2.2.1;have hcard:=osC2 hrb1 hOq (hOGl q) hjo_O;obtain ⟨v1,hv1_m,v2,hv2_m,hv12⟩:=one_lt_card.mp (by omega: 1 < (osL n C1 (gatesOf d1 C1 Kind.o q.val) (oLeaves d1 q) (n+jo)).card);have hsubO:=(osS hrb1 hOq (hOGl q) (n+jo)).2.1;have hv1_o:=hsubO hv1_m;have hv2_o:=hsubO hv2_m;simp only[oLeaves,mI,mF,mV,true_and] at hv1_o hv2_o;obtain ⟨r1,hr1,hv1_eq⟩:=hv1_o;obtain ⟨r2,hr2,hv2_eq⟩:=hv2_o
    have hr12: r1≠r2:=fun e => hv12 (by rw[←hv1_eq,←hv2_eq,e])
    obtain ⟨r',hr'_own,hr'_ne_p,hr'_mem⟩ : ∃ r',d1.owns q r' = true ∧ r' ≠ p ∧
      d1.lam q r' ∈ osL n C1 (gatesOf d1 C1 Kind.o q.val) (oLeaves d1 q) (n+jo):=by
     by_cases h1: r1=p
     ·exact ⟨r2,hr2,fun e => hr12 (h1.trans e.symm),hv2_eq ▸ hv2_m⟩
     ·exact ⟨r1,hr1,h1,hv1_eq ▸ hv1_m⟩
    have hr'_adj:=(hK1 q r').mp (hown1.1 q r' hr'_own).1
    have hr'_notA: r' ∉ A:=fun h => hA r' h q hr'_adj.1.symm
    let x_lr: Fin n→Bool:=fun v => decide (v=l∨v = r')
    have hwl_t: vl C1.gates x_lr wl1=true:=by
     rw[show wl1=n+jo by omega];apply (osV hcl1 hrb1 hOq (hOGl q) x_lr (n+jo) (Or.inr ⟨by omega,by simpa using hjo_O⟩)).mpr
     refine ⟨d1.lam q r',hr'_mem,?_⟩
     have hlam:=(h1c q hq_cov).2.2.2 r' hr'_own;unfold LamOK at hlam;split_ifs at hlam with hrc
     ·exact ncx hv1 r' hrc x_lr (by simp[x_lr]) (d1.lam q r') hlam.1
       (by rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩;exact Or.inl h;exact Or.inr ⟨jz,hjz,h1,h2⟩)
     ·rw[hlam,vli C1.gates x_lr r'.val r'.isLt];simp[x_lr]
    have hnr_t: vl C.gates x_lr (n+r)=true:=by rw[hvl_r,hwl_t];simp[x_lr]
    have horq_t: vl C.gates x_lr (lw2 n jl r (d1.oroot q))=true:=by
     have hmono_C: ∀ w < n+C1.gates.length,vl C1.gates x_lr w=true → vl C.gates x_lr (lw2 n jl r w)=true:=by
      intro w;induction w using Nat.strong_induction_on with
      | ind w ih =>
       intro hw h1
       by_cases hwn: w < n
       ·rw[lw2i n jl r w hwn,vli _ _ w hwn];rw[vli _ _ w hwn] at h1;exact h1
       ·set k' := w - n;have hk' : k' < C1.gates.length:=by omega
        have hlt_C: li2 jl r k' < C.gates.length:=li2lt hjr hr (by rw[←hlen1];exact hk')
        have hgC: C.gates[li2 jl r k']? = some (gateAt C (li2 jl r k')):=by simp[gateAt,List.getD,hlt_C]
        have hg1: C1.gates[k']? = some (gateAt C1 k'):=by simp[gateAt,List.getD,hk']
        have hlif:=r2l C hcl hrb hjr hr hu k' (by omega);rw[show w=n + k' by omega,vlg C1.gates hcl1 x_lr k' _ hg1] at h1;rw[show w=n + k' by omega,lw2g,vlg C.gates hcl x_lr _ _ hgC,←hlif.1];have hnn:=ncc_no_not hv1 k' hk';have hcg:=hcl1 k' _ hg1
        have hne_jl: ∀ c∈(gateAt C (li2 jl r k')).inputs,c≠n+jl:=fun c hc e =>
         li2nr jl r k' (hur _ hlt_C (e ▸ hc))
        have hin_step: ∀ c∈(gateAt C (li2 jl r k')).inputs,
          vl C1.gates x_lr (rd n jl 0 (rd n r u c))=true → vl C.gates x_lr c=true:=by
         intro c hc hct
         by_cases hcr: c=n+r
         ·exact hcr ▸ hnr_t
         ·have hceq: lw2 n jl r (rd n jl 0 (rd n r u c))=c:=lw2r hjr (hne_jl c hc) hcr;rw[←hceq]
          have hrd_in: rd n jl 0 (rd n r u c)∈(gateAt C1 k').inputs:=by
           rw[hlif.2];exact lmm.mpr ⟨c,hc,rfl⟩
          exact ih _ (by have := hrb1 k' hk' _ hrd_in;omega) (by have := hrb1 k' hk' _ hrd_in;omega) hct
        rcases hcg with ⟨hop,_⟩ | ⟨hop|hop,_,_,_,_,_⟩
        ·exact absurd hop hnn
        ·rw[hop] at h1 ⊢;simp only[GateOp.eval,laT,lmm,id_eq] at h1 ⊢
         rintro _ ⟨c,hc,rfl⟩
         exact hin_step c hc (h1 (vl C1.gates x_lr (rd n jl 0 (rd n r u c)))
          ⟨rd n jl 0 (rd n r u c),by rw[hlif.2];exact lmm.mpr ⟨c,hc,rfl⟩,rfl⟩)
        ·rw[hop] at h1 ⊢;simp only[GateOp.eval,lyT,lmm,id_eq] at h1 ⊢;obtain ⟨_,⟨a,ha,rfl⟩,hat⟩:=h1;rw[hlif.2] at ha;obtain ⟨c,hc,rfl⟩ := lmm.mp ha;exact ⟨true,⟨c,hc,hin_step c hc hat⟩,rfl⟩
     have hor_lt: d1.oroot q < n+C1.gates.length:=by
      have:=hrb1 jbq hjbq (d1.oroot q) (by rcases hin_bq with h|h <;> simp[h]);omega
     exact hmono_C (d1.oroot q) hor_lt (ncc_o_of_x hv1 q r' hq_cov hr'_own x_lr (by simp[x_lr]))
    have hdom: ∀ w < n+C.gates.length,w≠p.val →
      (∀ j' ∈ gatesOf d1 C1 Kind.o q.val,w≠n+li2 jl r j') →
      vl C.gates x_lp w=true → vl C.gates x_lr w=true:=by
     intro w;induction w using Nat.strong_induction_on with
     | ind w ih =>
      intro hw hwp hnoOq htr
      by_cases hwn: w < n
      ·rw[vli _ _ w hwn] at htr ⊢;simp only[x_lp,dTe] at htr
       rcases htr with h|h
       ·simp[x_lr,h]
       ·exact absurd (congrArg Fin.val h) hwp
      ·set j:=w - n;have hweq: w=n+j:=by omega
       have hj: j < C.gates.length:=by omega
       by_cases hje: j=jl
       ·rw[hweq,hje];have hgj: C.gates[jl]? = some (gateAt C jl) := by simp[gateAt,List.getD,show jl < C.gates.length by omega]
        rw[vlg C.gates hcl x_lr jl _ hgj,hjlo]
        have hxl_t: x_lr l=true:=by simp[x_lr]
        rcases hjli with h|h <;> rw[h] <;>
         simp[GateOp.eval,vli C.gates x_lr l.val l.isLt,hvl_wl x_lr,hwl_t,hxl_t]
       ·by_cases hre: j=r
        ·rw[hweq,hre];exact hnr_t
        ·obtain ⟨j',hj',hj_eq⟩:=li2s hjr hr hj hje hre;rw[←hj_eq] at hweq hj
         have hj'1: j' < C1.gates.length:=by omega
         have hgC: C.gates[li2 jl r j']? = some (gateAt C (li2 jl r j')):=by simp[gateAt,List.getD,hj]
         have hlif:=r2l C hcl hrb hjr hr hu j' (by omega);have hnn:=ncc_no_not hv1 j' hj'1;rw[hweq,vlg C.gates hcl x_lp _ _ hgC,←hlif.1] at htr;rw[hweq,vlg C.gates hcl x_lr _ _ hgC,←hlif.1]
         have hne_jl: ∀ c∈(gateAt C (li2 jl r j')).inputs,c≠n+jl:=fun c hc e =>
          li2nr jl r j' (hur _ hj (e ▸ hc))
         by_cases hjbqe: j' = jbq
         ·
          rw[hjbqe] at hweq;rw[hjbqe,hop_bq] at htr ⊢;simp only[GateOp.eval,laT,lmm,id_eq] at htr ⊢
          rintro _ ⟨c,hc,rfl⟩
          have hct:=htr (vl C.gates x_lp c) ⟨c,hc,rfl⟩;have hclt: c < n+li2 jl r jbq:=hrb (li2 jl r jbq) (hjbqe ▸ hj) c hc
          by_cases hcr: c=n+r
          ·exact hcr ▸ hnr_t
          ·have hc_rd: rd n jl 0 (rd n r u c)∈(gateAt C1 jbq).inputs:=by
            rw[hjbqe] at hlif;rw[hlif.2];exact lmm.mpr ⟨c,hc,rfl⟩
           have hceq: lw2 n jl r (rd n jl 0 (rd n r u c))=c:=lw2r hjr (hne_jl c (hjbqe ▸ hc)) hcr
           rcases hin_bq with h|h <;> rw[h] at hc_rd <;> simp at hc_rd <;> rcases hc_rd with e|e
           ·
            apply ih c (by omega) (by omega)
            ·rw[←hceq,e];rcases zrs hv1 q hq_cov with hz|⟨jz,_,hz,_⟩
             ·rw[hz,lw2i n jl r q.val q.isLt];exact Fin.val_ne_of_ne hpq.symm
             ·rw[hz,lw2g];have := p.isLt;omega
            ·intro k hk ek;rw[←hceq,e] at ek
             rcases zrs hv1 q hq_cov with hz|⟨jz,_,hz,hrz⟩
             ·rw[hz,lw2i n jl r q.val q.isLt] at ek;have := q.isLt;omega
             ·rw[hz,lw2g] at ek;have: jz=k := li2i jl r (by omega);have hO' := (mF.mp hk).2;rw[←this,hrz] at hO';cases hO'
            ·exact hct
           ·rw[←hceq,e];exact horq_t
           ·rw[←hceq,e];exact horq_t
           ·apply ih c (by omega) (by omega)
            ·rw[←hceq,e];rcases zrs hv1 q hq_cov with hz|⟨jz,_,hz,_⟩
             ·rw[hz,lw2i n jl r q.val q.isLt];exact Fin.val_ne_of_ne hpq.symm
             ·rw[hz,lw2g];have := p.isLt;omega
            ·intro k hk ek;rw[←hceq,e] at ek
             rcases zrs hv1 q hq_cov with hz|⟨jz,_,hz,hrz⟩
             ·rw[hz,lw2i n jl r q.val q.isLt] at ek;have := q.isLt;omega
             ·rw[hz,lw2g] at ek;have: jz=k := li2i jl r (by omega);have hO' := (mF.mp hk).2;rw[←this,hrz] at hO';cases hO'
            ·exact hct
         ·
          have hj'_notOq: j' ∉ gatesOf d1 C1 Kind.o q.val:=fun h => hnoOq j' h hweq
          have hstep_c: ∀ c∈(gateAt C (li2 jl r j')).inputs,
            vl C.gates x_lp c=true → vl C.gates x_lr c=true:=by
           intro c hc hct
           by_cases hcr: c=n+r
           ·exact hcr ▸ hnr_t
           ·have hclt: c < n+li2 jl r j' := hrb _ hj c hc
            have hc_rd: rd n jl 0 (rd n r u c)∈(gateAt C1 j').inputs:=by
             rw[hlif.2];exact lmm.mpr ⟨c,hc,rfl⟩
            have hceq: lw2 n jl r (rd n jl 0 (rd n r u c))=c:=lw2r hjr (hne_jl c hc) hcr;set a:=rd n jl 0 (rd n r u c)
            have ha_ne_p: a≠p.val:=by
             intro eap
             by_cases htop_j: (d1.role j').1=Kind.top
             ·rcases (htop1.1 j' (mF.mpr ⟨mR.mpr hj'1,htop_j⟩)).2.2 a hc_rd with hL|⟨hg,_⟩
              ·simp only[topLeaves,mU,mI,mF] at hL
               rcases hL with ⟨a',ha',hea'⟩ | ⟨s,⟨hs,_⟩,hes⟩
               ·exact hpnA (Fin.ext (hea'.trans eap) ▸ ha')
               ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have:=p.isLt;omega
              ·have:=p.isLt;omega
             ·rcases hrol1 j' hj'1 with ht' | ⟨t,ht,hrt2,hrb_t⟩
              ·exact htop_j ht'
              ·cases hkr: (d1.role j').1 with
               | top => exact htop_j hkr
               | b =>
                have hbw:=hrb_t hkr;obtain ⟨jb,_,hbw2,_,_,hin⟩:=(h1c t ht).1;have hje: j' = jb:=(by omega)
                have htq: t≠q:=fun e => hjbqe (by rw[e,hbwq] at hbw2;omega)
                rw[hje] at hc_rd
                rcases hin with h|h <;> rw[h] at hc_rd <;> simp at hc_rd <;> rcases hc_rd with ea|ea
                ·rcases zrs hv1 t ht with hz|⟨_,_,hz,_⟩
                 ·exact hpnc (Fin.ext (hz.symm.trans (ea.symm.trans eap)) ▸ ht)
                 ·have:=p.isLt;omega
                ·rcases ors hv1 t ht with ⟨r'',hown'',hlam''⟩ | ⟨_,_,hor,_⟩
                 ·have hlam:=(h1c t ht).2.2.2 r'' hown'';unfold LamOK at hlam;split_ifs at hlam
                  ·rcases hlam.2.1 with hz|⟨_,_,hz,_⟩
                   ·exact htq (honly_qp t (Fin.ext (hz.symm.trans (hlam''.symm.trans (ea.symm.trans eap))) ▸ hown''))
                   ·have:=p.isLt;omega
                  ·exact htq (honly_qp t (Fin.ext (hlam.symm.trans (hlam''.symm.trans (ea.symm.trans eap))) ▸ hown''))
                 ·have:=p.isLt;omega
                ·rcases ors hv1 t ht with ⟨r'',hown'',hlam''⟩ | ⟨_,_,hor,_⟩
                 ·have hlam:=(h1c t ht).2.2.2 r'' hown'';unfold LamOK at hlam;split_ifs at hlam
                  ·rcases hlam.2.1 with hz|⟨_,_,hz,_⟩
                   ·exact htq (honly_qp t (Fin.ext (hz.symm.trans (hlam''.symm.trans (ea.symm.trans eap))) ▸ hown''))
                   ·have:=p.isLt;omega
                  ·exact htq (honly_qp t (Fin.ext (hlam.symm.trans (hlam''.symm.trans (ea.symm.trans eap))) ▸ hown''))
                 ·have:=p.isLt;omega
                ·rcases zrs hv1 t ht with hz|⟨_,_,hz,_⟩
                 ·exact hpnc (Fin.ext (hz.symm.trans (ea.symm.trans eap)) ▸ ht)
                 ·have:=p.isLt;omega
               | z =>
                have hjZ: j' ∈ gatesOf d1 C1 Kind.z t.val:=mF.mpr ⟨mR.mpr hj'1,Prod.ext hkr hrt2⟩
                rcases ((h1c t ht).2.1.1 j' hjZ).2.2 a hc_rd with hL|⟨hg,_⟩
                ·simp only[zLeaves,mN,mI,mF] at hL
                 rcases hL with ha|⟨s,⟨hs,_⟩,hes⟩
                 ·exact hpnc (Fin.ext (ha.symm.trans eap) ▸ ht)
                 ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have:=p.isLt;omega
                ·have:=p.isLt;omega
               | o =>
                have htq: t≠q:=fun e => hj'_notOq (mF.mpr ⟨mR.mpr hj'1,Prod.ext hkr (hrt2.trans (congrArg Fin.val e))⟩)
                have hjO: j' ∈ gatesOf d1 C1 Kind.o t.val:=mF.mpr ⟨mR.mpr hj'1,Prod.ext hkr hrt2⟩
                rcases ((h1c t ht).2.2.1.1 j' hjO).2.2 a hc_rd with hL|⟨hg,_⟩
                ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r'',hown'',hea⟩:=hL;have hlam:=(h1c t ht).2.2.2 r'' hown'';unfold LamOK at hlam;split_ifs at hlam
                 ·rcases hlam.2.1 with hz|⟨_,_,hz,_⟩
                  ·exact htq (honly_qp t (Fin.ext (hz.symm.trans (hea.trans eap)) ▸ hown''))
                  ·have:=p.isLt;omega
                 ·exact htq (honly_qp t (Fin.ext (hlam.symm.trans (hea.trans eap)) ▸ hown''))
                ·have:=p.isLt;omega
            have ha_notOq: ∀ k∈gatesOf d1 C1 Kind.o q.val,a≠n+k:=by
             intro k hk eak;have hOk:=(mF.mp hk).2
             by_cases htop_j: (d1.role j').1=Kind.top
             ·rcases (htop1.1 j' (mF.mpr ⟨mR.mpr hj'1,htop_j⟩)).2.2 a hc_rd with hL|⟨_,hG⟩
              ·simp only[topLeaves,mU,mI,mF] at hL
               rcases hL with ⟨a',_,hea'⟩ | ⟨s,⟨hs,_⟩,hes⟩
               ·have := a'.isLt;omega
               ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1;have: k=jb:=(by omega);rw[this,hrb_s] at hOk;cases hOk
              ·have hG' := (mF.mp hG).2;rw[eak,ascl,hOk] at hG';cases hG'
             ·rcases hrol1 j' hj'1 with ht' | ⟨t,ht,hrt2,hrb_t⟩
              ·exact htop_j ht'
              ·cases hkr: (d1.role j').1 with
               | top => exact htop_j hkr
               | b =>
                have hbw:=hrb_t hkr;obtain ⟨jb,_,hbw2,_,_,hin⟩:=(h1c t ht).1;have hje: j' = jb:=(by omega)
                have htq: t≠q:=fun e => hjbqe (by rw[e,hbwq] at hbw2;omega)
                rw[hje] at hc_rd
                rcases hin with h|h <;> rw[h] at hc_rd <;> simp at hc_rd <;> rcases hc_rd with ea|ea
                ·rcases zrs hv1 t ht with hz|⟨jz,_,hz,hrz⟩
                 ·have:=t.isLt;omega
                 ·have: k=jz := (by omega);rw[this,hrz] at hOk;cases hOk
                ·rcases ors hv1 t ht with ⟨r'',hown'',hlam''⟩ | ⟨jo',_,hor,hro'⟩
                 ·have hlam:=(h1c t ht).2.2.2 r'' hown'';unfold LamOK at hlam;split_ifs at hlam
                  ·rcases hlam.2.1 with hz|⟨jz,_,hz,hrz⟩
                   ·have := r''.isLt;omega
                   ·have: k=jz := (by omega);rw[this,hrz] at hOk;cases hOk
                  ·have := r''.isLt;omega
                 ·have: k = jo' := (by omega);rw[this,hro'] at hOk;exact htq (Fin.ext (pei.mp hOk).2)
                ·rcases ors hv1 t ht with ⟨r'',hown'',hlam''⟩ | ⟨jo',_,hor,hro'⟩
                 ·have hlam:=(h1c t ht).2.2.2 r'' hown'';unfold LamOK at hlam;split_ifs at hlam
                  ·rcases hlam.2.1 with hz|⟨jz,_,hz,hrz⟩
                   ·have := r''.isLt;omega
                   ·have: k=jz := (by omega);rw[this,hrz] at hOk;cases hOk
                  ·have := r''.isLt;omega
                 ·have: k = jo' := (by omega);rw[this,hro'] at hOk;exact htq (Fin.ext (pei.mp hOk).2)
                ·rcases zrs hv1 t ht with hz|⟨jz,_,hz,hrz⟩
                 ·have:=t.isLt;omega
                 ·have: k=jz := (by omega);rw[this,hrz] at hOk;cases hOk
               | z =>
                have hjZ: j' ∈ gatesOf d1 C1 Kind.z t.val:=mF.mpr ⟨mR.mpr hj'1,Prod.ext hkr hrt2⟩
                rcases ((h1c t ht).2.1.1 j' hjZ).2.2 a hc_rd with hL|⟨_,hG⟩
                ·simp only[zLeaves,mN,mI,mF] at hL
                 rcases hL with ha|⟨s,⟨hs,_⟩,hes⟩
                 ·have:=t.isLt;omega
                 ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1;have: k=jb:=(by omega);rw[this,hrb_s] at hOk;cases hOk
                ·have hG' := (mF.mp hG).2;rw[eak,ascl,hOk] at hG';cases hG'
               | o =>
                have htq: t≠q:=fun e => hj'_notOq (mF.mpr ⟨mR.mpr hj'1,Prod.ext hkr (hrt2.trans (congrArg Fin.val e))⟩)
                have hjO: j' ∈ gatesOf d1 C1 Kind.o t.val:=mF.mpr ⟨mR.mpr hj'1,Prod.ext hkr hrt2⟩
                rcases ((h1c t ht).2.2.1.1 j' hjO).2.2 a hc_rd with hL|⟨_,hG⟩
                ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r'',hown'',hea⟩:=hL;have hlam:=(h1c t ht).2.2.2 r'' hown'';unfold LamOK at hlam;split_ifs at hlam
                 ·rcases hlam.2.1 with hz|⟨jz,_,hz,hrz⟩
                  ·have := r''.isLt;omega
                  ·have: k=jz := (by omega);rw[this,hrz] at hOk;cases hOk
                 ·have := r''.isLt;omega
                ·have hG' := (mF.mp hG).2;rw[eak,ascl,hOk] at hG';exact htq (Fin.ext (pei.mp hG').2.symm)
            apply ih c (by omega) (by omega)
            ·rw[←hceq];intro e;exact ha_ne_p (lw2j n jl r (e.trans (lw2i n jl r p.val p.isLt).symm))
            ·intro k hk ek;rw[←hceq,←lw2g] at ek;exact ha_notOq k hk (lw2j n jl r ek)
            ·exact hct
          have hg1: C1.gates[j']? = some (gateAt C1 j'):=by simp[gateAt,List.getD,hj'1]
          rcases hcl1 j' _ hg1 with ⟨hop,_⟩ | ⟨hop|hop,_,_,_,_,_⟩
          ·exact absurd hop hnn
          ·rw[hop] at htr ⊢;simp only[GateOp.eval,laT,lmm,id_eq] at htr ⊢
           rintro _ ⟨c,hc,rfl⟩;exact hstep_c c hc (htr _ ⟨c,hc,rfl⟩)
          ·rw[hop] at htr ⊢;simp only[GateOp.eval,lyT,lmm,id_eq] at htr ⊢;obtain ⟨_,⟨c,hc,rfl⟩,hct⟩:=htr;exact ⟨true,⟨c,hc,hstep_c c hc hct⟩,rfl⟩
    have hlout: lw2 n jl r C1.output=C.output:=lw2r hjr hon0 hne_out
    have hrm: C1.output∈topLeaves d1 A∨(n ≤ C1.output∧C1.output - n∈topGates d1 C1):=by
     by_cases hGe: topGates d1 C1 = ∅
     ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
     ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
    have hC_t: vl C.gates x_lr C.output=true:=by
     apply hdom C.output (by
      rw[←hlout];by_cases hlt: C1.output < n
      ·rw[lw2i n jl r _ hlt];omega
      ·rw[show C1.output=n+(C1.output - n) by omega,lw2g]
       have:=li2lt hjr hr (show C1.output - n < C.gates.length - 2 by omega);omega)
     ·rw[←hlout];intro e;have h1: C1.output=p.val:=lw2j n jl r (e.trans (lw2i n jl r p.val p.isLt).symm)
      rcases hrm with hL|⟨hg,_⟩
      ·simp only[topLeaves,mU,mI,mF] at hL
       rcases hL with ⟨a,ha,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
       ·exact hpnA (Fin.ext (hea.trans h1) ▸ ha)
       ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have:=p.isLt;omega
      ·have:=p.isLt;omega
     ·intro k hk ek;rw[←hlout,←lw2g] at ek;have h1:=lw2j n jl r ek;have hOk:=(mF.mp hk).2
      rcases hrm with hL|⟨_,hG⟩
      ·simp only[topLeaves,mU,mI,mF] at hL
       rcases hL with ⟨a,_,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
       ·have:=a.isLt;omega
       ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1;have: k=jb:=(by omega);rw[this,hrb_s] at hOk;cases hOk
      ·have hG' := (mF.mp hG).2;rw[h1,ascl,hOk] at hG';cases hG'
     ·exact hlpC
    rw[hval_C] at hC_t;simp only[graphFun,boT,dTe,x_lr] at hC_t
    rcases hC_t with ⟨a,ha,hal|har⟩ | ⟨a,b,hab,hal|har,hbl|hbr⟩
    ·exact hlnA (hal ▸ ha)
    ·exact hr'_notA (har ▸ ha)
    ·exact hab.ne (hal.trans hbl.symm)
    ·exact hr'_ne_p ((hl r').mp (hal ▸ hbr ▸ hab))
    ·exact hr'_ne_p ((hl r').mp (hbl ▸ har ▸ hab.symm))
    ·exact hab.ne (har.trans hbr.symm)
  have hwp0: wl=p.val:=by rw[←hwl_lw,hw1p,lw2i n jl r p.val p.isLt]
  let readO: Fin n→Prop:=fun t =>
   t∈d1.cover∧d1.owns t q=true∧d1.lam t q=u1 ∧
   ((d1.oroot t=u1 ∧ ∃ jb < C1.gates.length,d1.bw t=n+jb∧n+r∈(gateAt C (li2 jl r jb)).inputs) ∨
   ∃ j' ∈ gatesOf d1 C1 Kind.o t.val,n+r∈(gateAt C (li2 jl r j')).inputs)
  let roleB: ℕ → Kind × ℕ := fun j =>
   if j=jl then (Kind.b,p.val)
   else if j=r then (Kind.z,q.val)
   else d1.role (rd 0 jl 0 (rd 0 r 0 j))
  have hrl: ∀ j' : ℕ,roleB (li2 jl r j')=d1.role j' := by
   intro j';simp only[roleB,li2nj jl r j' hjr,li2nr jl r j',↓reduceIte]
   congr 1
   have hlift_eq: li2 jl r j' = lw2 0 jl r j' := by unfold li2 lw2 li1 lw1;simp
   rw[hlift_eq];exact rd2l
  let d: NCCData n:={
   cover := insert p d1.cover
   owns := fun a b => if a=p∧b=l then true else d1.owns a b
   tie := fun t => if t=p then some q else d1.tie t
   role := roleB
   bw := fun t => if t=p then n+jl else lw2 n jl r (d1.bw t)
   zroot := fun t => if t=p then p.val else if t=q∧u1=d1.zroot q then n+r else lw2 n jl r (d1.zroot t)
   oroot := fun t => if t=p then l.val else if d1.oroot t=u1∧readO t then n+r else lw2 n jl r (d1.oroot t)
   lam := fun t v => if t=p then l.val else if v=q∧readO t then n+r else lw2 n jl r (d1.lam t v)
  }
  have hgn: ∀ (k: Kind) (v: ℕ),(k,v)≠(Kind.b,p.val)→(k,v)≠(Kind.z,q.val) →
    gatesOf d C k v=(gatesOf d1 C1 k v).image (li2 jl r):=by
   intro k v h1 h2
   ext j;simp only[gatesOf,d,mF,mR,mI]
   constructor
   ·rintro ⟨hj,hrj⟩
    have hje: j≠jl:=fun e => h1 (by rw[←hrj,e];simp[roleB])
    have hre: j≠r:=fun e => h2 (by rw[←hrj,e];simp[roleB,Nat.ne_of_gt hjr])
    obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre;exact ⟨j',⟨by omega,by rw[←hrl j'];exact hrj⟩,rfl⟩
   ·rintro ⟨j',⟨hj',hrj'⟩,rfl⟩
    exact ⟨li2lt hjr hr (by omega),by rw[hrl,hrj']⟩
  have hcZq: ∀ w: ℕ,IsCentred n C1 d1 w →
    (w=q.val ∨ ∃ jz < C1.gates.length,w=n+jz∧d1.role jz=(Kind.z,q.val)) →
    IsCentred n C d (lw2 n jl r w):=by
   intro w;induction w using Nat.strong_induction_on with
   | ind w ih =>
    intro hcen hwq
    rcases hwq with rfl|⟨jz,hjz,rfl,hrz⟩
    ·rw[lw2i n jl r q.val q.isLt,cfi C d q];exact mNo hq_cov
    ·rw[cfg C1 d1 hrb1 jz hjz] at hcen;obtain ⟨_,a,ha,ha_cen⟩:=hcen;have hjZ: jz∈gatesOf d1 C1 Kind.z q.val:=mF.mpr ⟨mR.mpr hjz,hrz⟩;have ha_lt: a < n+jz:=hrb1 jz hjz a ha
     have ha_spec: a=q.val ∨ ∃ k < C1.gates.length,a=n+k∧d1.role k=(Kind.z,q.val):=by
      rcases (hZq.1 jz hjZ).2.2 a ha with hL|⟨hg,hG⟩
      ·simp only[zLeaves,mN,mI,mF] at hL
       rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
       ·exact Or.inl rfl
       ·obtain ⟨jb,hjb,hbw,hrb_s,_,_⟩:=(h1c s hs).1;rw[hbw,cfg C1 d1 hrb1 jb hjb] at ha_cen;rw[hrb_s] at ha_cen;cases ha_cen.1
      ·exact Or.inr ⟨a - n,hZGl q _ hG,by omega,(mF.mp hG).2⟩
     have ha_lift_cen: IsCentred n C d (lw2 n jl r a):=ih a (by omega) ha_cen ha_spec;have hlt_C: li2 jl r jz < C.gates.length:=li2lt hjr hr (by omega);rw[lw2g,cfg C d hrb (li2 jl r jz) hlt_C]
     refine ⟨by dsimp[d];rw[hrl,hrz],?_⟩
     by_cases hnr: n+r∈(gateAt C (li2 jl r jz)).inputs
     ·have hlif:=r2l C hcl hrb hjr hr hu jz (by omega)
      have hlenC: (gateAt C (li2 jl r jz)).inputs.length=2:=by
       have h2:=(hZq.1 jz hjZ).2.1;rw[hlif.2,llm] at h2;exact h2
      obtain ⟨x1,x2,hx12⟩:=ll2.mp hlenC
      have hmap: [rd n jl 0 (rd n r u x1),rd n jl 0 (rd n r u x2)]=(gateAt C1 jz).inputs:=by
       rw[hlif.2,hx12];rfl
      have hne_jl: ∀ c∈(gateAt C (li2 jl r jz)).inputs,c≠n+jl:=fun c hc e =>
       li2nr jl r jz (hur _ hlt_C (e ▸ hc))
      rw[←hmap] at ha;simp at ha
      rcases ha with e|e
      ·by_cases hx1r: x1=n+r
       ·have hau: a=u1:=by rw[e,hx1r,rd_eq]
        refine ⟨n+r,hnr,?_⟩
        rw[cfg C d hrb r hr]
        refine ⟨by simp[d,roleB,Nat.ne_of_gt hjr],u,by rcases hri0 with h|h <;> simp[h],?_⟩
        rw[←hu_lw,←hau];exact ha_lift_cen
       ·refine ⟨x1,by rw[hx12];simp,?_⟩
        have hx1_eq: lw2 n jl r a=x1:=by rw[e,lw2r hjr (hne_jl x1 (by rw[hx12];simp)) hx1r]
        rw[←hx1_eq];exact ha_lift_cen
      ·by_cases hx2r: x2=n+r
       ·have hau: a=u1:=by rw[e,hx2r,rd_eq]
        refine ⟨n+r,hnr,?_⟩
        rw[cfg C d hrb r hr]
        refine ⟨by simp[d,roleB,Nat.ne_of_gt hjr],u,by rcases hri0 with h|h <;> simp[h],?_⟩
        rw[←hu_lw,←hau];exact ha_lift_cen
       ·refine ⟨x2,by rw[hx12];simp,?_⟩
        have hx2_eq: lw2 n jl r a=x2:=by rw[e,lw2r hjr (hne_jl x2 (by rw[hx12];simp)) hx2r]
        rw[←hx2_eq];exact ha_lift_cen
     ·have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jz (by omega) hnr;exact ⟨lw2 n jl r a,by rw[hinp];exact lmm.mpr ⟨a,ha,rfl⟩,ha_lift_cen⟩
  have hcnr: IsCentred n C1 d1 u1→IsCentred n C d (n+r):=by
   intro hcen
   have hu1_spec: u1=q.val ∨ ∃ jz < C1.gates.length,u1=n+jz∧d1.role jz=(Kind.z,q.val):=by
    rcases hu1_Zq with hL|⟨hg,hG⟩
    ·simp only[zLeaves,mN,mI,mF] at hL
     rcases hL with huq|⟨s,⟨hs,_⟩,hus⟩
     ·exact Or.inl huq
     ·obtain ⟨jb,hjb,hbw,hrb_s,_,_⟩:=(h1c s hs).1;rw[←hus,hbw,cfg C1 d1 hrb1 jb hjb,hrb_s] at hcen;cases hcen.1
    ·exact Or.inr ⟨u1 - n,hZGl q _ hG,by omega,(mF.mp hG).2⟩
   rw[cfg C d hrb r hr]
   exact ⟨by simp[d,roleB,Nat.ne_of_gt hjr],u,by rcases hri0 with h|h <;> simp[h],
    by rw[←hu_lw];exact hcZq u1 hcen hu1_spec⟩
  refine ⟨d,hrb,?_,?_,?_,?_,?_,?_⟩
  ·
   refine ⟨?_,fun T hT => by have := htK1 T hT;simp only[d,card_insert_of_notMem hpnc];omega⟩
   intro a b hab
   by_cases hap: a=p
   ·left;exact mC.mpr (hap ▸ mNs p _)
   ·by_cases hbp: b=p
    ·right;exact mC.mpr (hbp ▸ mNs p _)
    ·have hal: a≠l:=fun e => hbp ((hl b).mp (e ▸ hab))
     have hbl: b≠l:=fun e => hap ((hl a).mp (e ▸ hab.symm))
     rcases hmc1.1 ((hK1 a b).mpr ⟨hab,hal,hbl⟩) with ha|hb
     ·left;exact mC.mpr (mNo (mC.mp ha))
     ·right;exact mC.mpr (mNo (mC.mp hb))
  ·
   refine ⟨?_,?_⟩
   ·intro a b hown;dsimp[d] at hown;split_ifs at hown with h
    ·exact ⟨by rw[h.1,h.2];exact ((hl p).mpr rfl).symm,by rw[h.1];exact mNs _ _⟩
    ·have h1:=hown1.1 a b hown;exact ⟨((hK1 a b).mp h1.1).1,mNo h1.2⟩
   ·intro a b hab
    by_cases hal: a=l
    ·rw[hal] at hab ⊢;have hbp: b=p:=(hl b).mp hab;rw[hbp]
     have ha_no: d1.owns l p=false:=by cases h: d1.owns l p;rfl;exact absurd (hown1.1 l p h).1 (hl_iso p)
     dsimp[d];simp[hlp,hlp.symm,ha_no]
    ·by_cases hbl: b=l
     ·rw[hbl] at hab ⊢;have hap: a=p:=(hl a).mp hab.symm;rw[hap]
      have hb_no: d1.owns l p=false:=by cases h: d1.owns l p;rfl;exact absurd (hown1.1 l p h).1 (hl_iso p)
      dsimp[d];simp[hlp,hlp.symm,hb_no]
     ·dsimp[d];simp[hal,hbl,hown1.2 a b ((hK1 a b).mpr ⟨hab,hal,hbl⟩)]
  ·
   intro s t hst;dsimp[d] at hst;split_ifs at hst with hsp
   ·have htq: t=q:=(osi hst).symm;rw[hsp,htq];exact ⟨mNs _ _,by dsimp[d];simp[hpq.symm,hown_qp]⟩
   ·have h1:=htie1 s t hst
    refine ⟨mNo h1.1,?_⟩
    dsimp[d];by_cases h2: t=p∧s=l
    ·simp[h2]
    ·simp[h2,h1.2]
  ·
   intro j hj
   by_cases hje: j=jl
   ·rw[hje];right;exact ⟨p,mNs _ _,by simp[d,roleB],fun _ => by simp[d]⟩
   ·by_cases hre: j=r
    ·rw[hre];right;exact ⟨q,mNo hq_cov,by simp[d,roleB,Nat.ne_of_gt hjr],fun h => by simp[d,roleB,Nat.ne_of_gt hjr] at h⟩
    ·obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre
     rcases hrol1 j' (by omega) with ht' | ⟨t,ht,e1,e2⟩
     ·exact Or.inl (by dsimp[d];rw[hrl];exact ht')
     ·right;refine ⟨t,mNo ht,by dsimp[d];rw[hrl];exact e1,fun hk => ?_⟩
      dsimp[d] at hk ⊢;rw[hrl] at hk
      have htp: t≠p:=fun e => hpnc (e ▸ ht)
      simp only[htp,↓reduceIte];rw[e2 hk,lw2g]
  ·
   intro t ht
   by_cases htp: t=p
   ·rw[htp]
    refine ⟨?_,?_,?_,?_⟩
    ·refine ⟨jl,by omega,by simp[d],by simp[d,roleB],hjlo,?_⟩
     dsimp[d];simp only[↓reduceIte];rw[←hwp0];exact hjli.symm
    ·have hG: gatesOf d C Kind.z p.val = ∅ := by
      rw[hgn Kind.z p.val (by simp) (fun h => hpq (Fin.ext (pei.mp h).2))]
      have hE: gatesOf d1 C1 Kind.z p.val = ∅ := by
       ext j';simp only[gatesOf,mF,mR,notMem_empty,iff_false,not_and]
       intro hj' hrj'
       rcases hrol1 j' hj' with ht' | ⟨s,hs,e1,_⟩
       ·rw[hrj'] at ht';cases ht'
       ·rw[hrj'] at e1;exact hpnc (Fin.ext e1.symm ▸ hs)
      simp[hE]
     have hL: zLeaves d p={p.val}:=by
      ext w;simp only[zLeaves,d,mN,mI,mF,mS,or_iff_left_iff_imp]
      rintro ⟨s,⟨_,hst⟩,_⟩;split_ifs at hst with hsp
      ·exact absurd (osi hst) hpq.symm
      ·exact absurd (hown1.1 p s (htie1 s p hst).2).2 hpnc
     rw[hG,hL];dsimp[d];simp only[↓reduceIte]
     exact ⟨by simp,fun w hw => by rw[mS.mp hw];simp[readsIn],by simp,by simp⟩
    ·have hG: gatesOf d C Kind.o p.val = ∅ := by
      rw[hgn Kind.o p.val (by simp) (by simp)]
      have hE: gatesOf d1 C1 Kind.o p.val = ∅ := by
       ext j';simp only[gatesOf,mF,mR,notMem_empty,iff_false,not_and]
       intro hj' hrj'
       rcases hrol1 j' hj' with ht' | ⟨s,hs,e1,_⟩
       ·rw[hrj'] at ht';cases ht'
       ·rw[hrj'] at e1;exact hpnc (Fin.ext e1.symm ▸ hs)
      simp[hE]
     have hL: oLeaves d p={l.val}:=by
      ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
       mS,↓reduceIte]
      constructor
      ·rintro ⟨v,_,rfl⟩;rfl
      ·rintro rfl;exact ⟨l,by simp,rfl⟩
     rw[hG,hL];dsimp[d];simp only[↓reduceIte]
     exact ⟨by simp,fun w hw => by rw[mS.mp hw];simp[readsIn],by simp,by simp⟩
    ·intro v hown;dsimp[d] at hown
     have hvl: v=l:=by
      simp only[true_and] at hown;split_ifs at hown with h;exact h;exact absurd (hown1.1 p v hown).2 hpnc
     rw[hvl];unfold LamOK;dsimp[d];simp[hlp,hlnc]
   ·have ht1: t∈d1.cover:=by rcases mN.mp ht with rfl|h;exact absurd rfl htp;exact h
    have hOnr: ∀ j' ∈ gatesOf d1 C1 Kind.o t.val,n+r∈(gateAt C (li2 jl r j')).inputs →
      d1.owns t q=true∧d1.lam t q=u1:=by
     intro j' hj' hm;have hu1_in:=hnu1 j' (hOGl t j' hj') hm
     rcases ((h1c t ht1).2.2.1.1 j' hj').2.2 u1 hu1_in with hL|⟨_,hG⟩
     ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',hlam'⟩:=hL;have hlam:=(h1c t ht1).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
      ·have hr'_z: u1∈zLeaves d1 r' ∨ (n ≤ u1∧u1 - n∈gatesOf d1 C1 Kind.z r'.val):=by
        rw[←hlam'];rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
        ·exact Or.inl (h ▸ mNs _ _)
        ·exact Or.inr ⟨by omega,by rw[h1,ascl];exact mF.mpr ⟨mR.mpr hjz,h2⟩⟩
       have hr'q: r' = q:=by by_contra hne;exact hZd r' q hrc hq_cov hne u1 hr'_z hu1_Zq
       exact ⟨hr'q ▸ hown',hr'q ▸ hlam'⟩
      ·exfalso;rw[hlam] at hlam'
       rcases hu1_Zq with hLz|⟨hg,_⟩
       ·simp only[zLeaves,mN,mI,mF] at hLz
        rcases hLz with h2|⟨s,⟨hs,_⟩,h2⟩
        ·exact hrc (Fin.ext (hlam'.trans h2) ▸ hq_cov)
        ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have := r'.isLt;omega
       ·have := r'.isLt;omega
     ·exfalso
      rcases hu1_Zq with hLz|⟨_,hGz⟩
      ·simp only[zLeaves,mN,mI,mF] at hLz
       rcases hLz with h2|⟨s,⟨hs,_⟩,h2⟩
       ·have:=q.isLt;omega
       ·obtain ⟨jb,_,hbw,hrb_s,_,_⟩:=(h1c s hs).1;have hG' := (mF.mp hG).2;rw[←h2,hbw,ascl,hrb_s] at hG';cases hG'
      ·have h1:=(mF.mp hG).2;have h2:=(mF.mp hGz).2;rw[h1] at h2;cases h2
    refine ⟨?_,?_,?_,?_⟩
    ·
     obtain ⟨jb,hjb,hbw,hrb_t,hop,hin⟩:=(h1c t ht1).1;have hlt_C: li2 jl r jb < C.gates.length:=li2lt hjr hr (by omega);have hlif:=r2l C hcl hrb hjr hr hu jb (by omega)
     refine ⟨li2 jl r jb,hlt_C,by dsimp[d];simp[htp,hbw,lw2g],
      by dsimp[d];rw[hrl,hrb_t],by rw[←hlif.1,hop],?_⟩
     have hlenC: (gateAt C (li2 jl r jb)).inputs.length=2:=by
      have h2: (gateAt C1 jb).inputs.length=2:=by rcases hin with h|h <;> simp[h]
      rw[hlif.2,llm] at h2;exact h2
     obtain ⟨x1,x2,hx12⟩:=ll2.mp hlenC
     have hmap: [rd n jl 0 (rd n r u x1),rd n jl 0 (rd n r u x2)]=(gateAt C1 jb).inputs:=by
      rw[hlif.2,hx12];rfl
     have hne_jl: ∀ c∈(gateAt C (li2 jl r jb)).inputs,c≠n+jl:=fun c hc e =>
      li2nr jl r jb (hur _ hlt_C (e ▸ hc))
     have hne_zo: d1.zroot t≠d1.oroot t:=zroot_ne_oroot hv1 t ht1
     have hnr_iff: n+r∈(gateAt C (li2 jl r jb)).inputs →
       (t=q∧u1=d1.zroot q)∨(d1.oroot t=u1∧readO t):=by
      intro hm;have hu1_in:=hnu1 jb hjb hm
      rcases hin with h|h <;> rw[h] at hu1_in <;> simp at hu1_in <;> rcases hu1_in with e|e
      ·left
       have htq: t=q:=by
        by_contra hne
        exact hZd t q ht1 hq_cov hne u1 (by
         rw[e];rcases zrs hv1 t ht1 with hz|⟨jz,hjz,hz,hrz⟩
         ·exact Or.inl (hz ▸ mNs _ _)
         ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩) hu1_Zq
       exact ⟨htq,htq ▸ e⟩
      ·right
       rcases ors hv1 t ht1 with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
       ·have hlam:=(h1c t ht1).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
        ·have hr'q: r' = q:=by
          by_contra hne
          exact hZd r' q hrc hq_cov hne u1 (by
           rw[e,hlam'];rcases hlam.2.1 with hz|⟨jz,hjz,hz,hrz⟩
           ·exact Or.inl (hz ▸ mNs _ _)
           ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩) hu1_Zq
         exact ⟨e.symm,ht1,hr'q ▸ hown',by rw[←hr'q,←hlam',e],Or.inl ⟨e.symm,jb,hjb,hbw,hm⟩⟩
        ·exfalso;rw[hlam',hlam] at e
         rcases hu1_Zq with hLz|⟨hg,_⟩
         ·simp only[zLeaves,mN,mI,mF] at hLz
          rcases hLz with h2|⟨s,⟨hs,_⟩,h2⟩
          ·exact hrc (Fin.ext (e.symm.trans h2) ▸ hq_cov)
          ·obtain ⟨jb',_,hbw',_,_,_⟩:=(h1c s hs).1;have := r'.isLt;omega
         ·have := r'.isLt;omega
       ·exfalso;rw[hor] at e
        rcases hu1_Zq with hLz|⟨_,hGz⟩
        ·simp only[zLeaves,mN,mI,mF] at hLz
         rcases hLz with h2|⟨s,⟨hs,_⟩,h2⟩
         ·have:=q.isLt;omega
         ·obtain ⟨jb',_,hbw',hrb_s,_,_⟩:=(h1c s hs).1
          have: jb' = jo := (by omega);rw[this,hro] at hrb_s;cases hrb_s
        ·have hG' := (mF.mp hGz).2;rw[e,ascl,hro] at hG';cases hG'
      ·right
       rcases ors hv1 t ht1 with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro⟩
       ·have hlam:=(h1c t ht1).2.2.2 r' hown';unfold LamOK at hlam;split_ifs at hlam with hrc
        ·have hr'q: r' = q:=by
          by_contra hne
          exact hZd r' q hrc hq_cov hne u1 (by
           rw[e,hlam'];rcases hlam.2.1 with hz|⟨jz,hjz,hz,hrz⟩
           ·exact Or.inl (hz ▸ mNs _ _)
           ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩) hu1_Zq
         exact ⟨e.symm,ht1,hr'q ▸ hown',by rw[←hr'q,←hlam',e],Or.inl ⟨e.symm,jb,hjb,hbw,hm⟩⟩
        ·exfalso;rw[hlam',hlam] at e
         rcases hu1_Zq with hLz|⟨hg,_⟩
         ·simp only[zLeaves,mN,mI,mF] at hLz
          rcases hLz with h2|⟨s,⟨hs,_⟩,h2⟩
          ·exact hrc (Fin.ext (e.symm.trans h2) ▸ hq_cov)
          ·obtain ⟨jb',_,hbw',_,_,_⟩:=(h1c s hs).1;have := r'.isLt;omega
         ·have := r'.isLt;omega
       ·exfalso;rw[hor] at e
        rcases hu1_Zq with hLz|⟨_,hGz⟩
        ·simp only[zLeaves,mN,mI,mF] at hLz
         rcases hLz with h2|⟨s,⟨hs,_⟩,h2⟩
         ·have:=q.isLt;omega
         ·obtain ⟨jb',_,hbw',hrb_s,_,_⟩:=(h1c s hs).1
          have: jb' = jo := (by omega);rw[this,hro] at hrb_s;cases hrb_s
        ·have hG' := (mF.mp hGz).2;rw[e,ascl,hro] at hG';cases hG'
      ·left
       have htq: t=q:=by
        by_contra hne
        exact hZd t q ht1 hq_cov hne u1 (by
         rw[e];rcases zrs hv1 t ht1 with hz|⟨jz,hjz,hz,hrz⟩
         ·exact Or.inl (hz ▸ mNs _ _)
         ·exact Or.inr ⟨by omega,by rw[hz,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz⟩⟩) hu1_Zq
       exact ⟨htq,htq ▸ e⟩
     by_cases hnr: n+r∈(gateAt C (li2 jl r jb)).inputs
     ·have hor_disj:=hnr_iff hnr;rw[hx12] at hnr ⊢;simp at hnr
      rcases hnr with rfl|rfl
      ·have hx1_u: rd n jl 0 (rd n r u (n+r))=u1:=by rw[rd_eq]
       rw[hx1_u] at hmap
       rcases hin with h|h <;> rw[h] at hmap
       ·have hm1: u1=d1.zroot t:=(List.cons.inj hmap).1;have hm2: rd n jl 0 (rd n r u x2)=d1.oroot t:=(List.cons.inj (List.cons.inj hmap).2).1
        have hx2_ne_r: x2≠n+r:=fun e => hne_zo (by rw[←hm1,←hm2,e,rd_eq])
        have hx2_eq: x2=lw2 n jl r (d1.oroot t):=by rw[←hm2,lw2r hjr (hne_jl x2 (by rw[hx12];simp)) hx2_ne_r]
        rcases hor_disj with ⟨htq,hu_zq⟩ | ⟨ho_u,_⟩
        ·left;dsimp[d];have hno_o: ¬ (d1.oroot t=u1∧readO t) := fun h => hne_zo (by rw[←hm1,←h.1])
         rw[if_neg htp,if_neg htp,if_pos ⟨htq,hu_zq⟩,if_neg hno_o,hx2_eq]
        ·exact absurd (hm1.symm.trans ho_u.symm) hne_zo
       ·have hm1: u1=d1.oroot t:=(List.cons.inj hmap).1;have hm2: rd n jl 0 (rd n r u x2)=d1.zroot t:=(List.cons.inj (List.cons.inj hmap).2).1
        have hx2_ne_r: x2≠n+r:=fun e => hne_zo (by symm;rw[←hm1,←hm2,e,rd_eq])
        have hx2_eq: x2=lw2 n jl r (d1.zroot t):=by rw[←hm2,lw2r hjr (hne_jl x2 (by rw[hx12];simp)) hx2_ne_r]
        rcases hor_disj with ⟨htq,hu_zq⟩ | ⟨ho_u,hro⟩
        ·exact absurd (by rw[←hm1,hu_zq,←htq]: d1.zroot t=d1.oroot t) hne_zo
        ·right;dsimp[d];have hno_z: ¬ (t=q∧u1=d1.zroot q) := fun h => hne_zo (by rw[ho_u,h.2,←h.1])
         simp only[htp,↓reduceIte,ho_u,hro,and_self,hno_z,hx2_eq]
      ·have hx2_u: rd n jl 0 (rd n r u (n+r))=u1:=by rw[rd_eq]
       rw[hx2_u] at hmap
       rcases hin with h|h <;> rw[h] at hmap
       ·have hm1: rd n jl 0 (rd n r u x1)=d1.zroot t:=(List.cons.inj hmap).1;have hm2: u1=d1.oroot t:=(List.cons.inj (List.cons.inj hmap).2).1
        have hx1_ne_r: x1≠n+r:=fun e => hne_zo (by rw[←hm1,←hm2,e,rd_eq])
        have hx1_eq: x1=lw2 n jl r (d1.zroot t):=by rw[←hm1,lw2r hjr (hne_jl x1 (by rw[hx12];simp)) hx1_ne_r]
        rcases hor_disj with ⟨htq,hu_zq⟩ | ⟨ho_u,hro⟩
        ·exact absurd (by rw[←hm2,hu_zq,←htq]: d1.zroot t=d1.oroot t) hne_zo
        ·left;dsimp[d];have hno_z: ¬ (t=q∧u1=d1.zroot q) := fun h => hne_zo (by rw[ho_u,h.2,←h.1])
         simp only[htp,↓reduceIte,ho_u,hro,and_self,hno_z,hx1_eq]
       ·have hm1: rd n jl 0 (rd n r u x1)=d1.oroot t:=(List.cons.inj hmap).1;have hm2: u1=d1.zroot t:=(List.cons.inj (List.cons.inj hmap).2).1
        have hx1_ne_r: x1≠n+r:=fun e => hne_zo (by symm;rw[←hm1,←hm2,e,rd_eq])
        have hx1_eq: x1=lw2 n jl r (d1.oroot t):=by rw[←hm1,lw2r hjr (hne_jl x1 (by rw[hx12];simp)) hx1_ne_r]
        rcases hor_disj with ⟨htq,hu_zq⟩ | ⟨ho_u,_⟩
        ·right;dsimp[d];have hno_o: ¬ (d1.oroot t=u1∧readO t) := fun h => hne_zo (by rw[←hm2,←h.1])
         rw[if_neg htp,if_neg htp,if_neg hno_o,if_pos ⟨htq,hu_zq⟩,hx1_eq]
        ·exact absurd (hm2.symm.trans ho_u.symm) hne_zo
     ·
      have hnot_z: ¬ (t=q∧u1=d1.zroot q):=by
       rintro ⟨htq,hu_zq⟩
       rcases hZqc with ⟨_,hbq_r,_⟩ | ⟨hne,_⟩
       ·have hje: jb=jbq:=by rw[htq,hbwq] at hbw;omega
        exact hnr (hje ▸ hbq_r)
       ·exact hne hu_zq
      have hnot_o: ¬ (d1.oroot t=u1∧readO t):=by
       rintro ⟨ho_u,_,_,_,⟨_,jb',_,hbw',hnr'⟩ | ⟨jo',hjo',hnr'⟩⟩
       ·have hje: jb = jb' := by rw[hbw'] at hbw;omega
        exact hnr (hje ▸ hnr')
       ·have hOt:=(h1c t ht1).2.2.1
        have hr0:=(hOt.2.1 u1 (by
         rcases ors hv1 t ht1 with ⟨r',hown',hlam'⟩ | ⟨jo'',_,hor,hro⟩
         ·rw[←ho_u,hlam'];simp only[oLeaves,mI,mF,mV,true_and];exact ⟨r',hown',rfl⟩
         ·exfalso;have h2 := hOnr jo' hjo' hnr'
          have hlam_q:=(h1c t ht1).2.2.2 q h2.1
          have:=(hOt.2.1 (d1.lam t q) (by simp only[oLeaves,mI,mF,mV,true_and];exact ⟨q,h2.1,rfl⟩)).1
          rw[h2.2,←ho_u,hor] at this;exact this ⟨by omega,by rw[ascl];exact mF.mpr ⟨mR.mpr (by have := hrb1 jb hjb (d1.oroot t) (by rcases hin with h|h <;> simp[h]);omega),hro⟩⟩)).2
        rw[if_pos ho_u.symm] at hr0;have h1: 1 ≤ (gateAt C1 jo').inputs.count u1:=lcpi.mpr (hnu1 jo' (hOGl t jo' hjo') hnr')
        have hle: (gateAt C1 jo').inputs.count u1 ≤ readsIn C1 (gatesOf d1 C1 Kind.o t.val) u1 :=
         single_le_sum (f := fun m => (gateAt C1 m).inputs.count u1) (fun _ _ => Nat.zero_le _) hjo'
        omega
      have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jb (by omega) hnr;rw[hinp];dsimp[d];simp only[htp,hnot_z,hnot_o,↓reduceIte]
      rcases hin with h|h <;> rw[h] <;> simp
    ·
     by_cases htq: t=q
     ·rw[htq]
      have hG: gatesOf d C Kind.z q.val=insert r ((gatesOf d1 C1 Kind.z q.val).image (li2 jl r)):=by
       ext j;simp only[gatesOf,d,mF,mR,mN,mI]
       constructor
       ·rintro ⟨hj,hrj⟩
        by_cases hre: j=r
        ·exact Or.inl hre
        ·right
         have hje: j≠jl:=fun e => by rw[e] at hrj;simp[roleB] at hrj
         obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre;exact ⟨j',⟨by omega,by rw[←hrl j'];exact hrj⟩,rfl⟩
       ·rintro (rfl|⟨j',⟨hj',hrj'⟩,rfl⟩)
        ·exact ⟨hr,by simp[roleB,Nat.ne_of_gt hjr]⟩
        ·exact ⟨li2lt hjr hr (by omega),by rw[hrl,hrj']⟩
      have hL: zLeaves d q=insert (n+jl) ((zLeaves d1 q).image (lw2 n jl r)):=by
       ext w;simp only[zLeaves,d,mN,mI,mF]
       constructor
       ·rintro (rfl|⟨s,⟨hs,hst⟩,rfl⟩)
        ·right;exact ⟨q.val,Or.inl rfl,lw2i n jl r q.val q.isLt⟩
        ·by_cases hsp: s=p
         ·left;simp[hsp]
         ·right;simp only[hsp,↓reduceIte] at hst ⊢
          have hs1:=(htie1 s q hst).1;exact ⟨d1.bw s,Or.inr ⟨s,⟨hs1,hst⟩,rfl⟩,rfl⟩
       ·rintro (rfl|⟨_,rfl|⟨s,⟨hs,hst⟩,rfl⟩,rfl⟩)
        ·right;exact ⟨p,⟨Or.inl rfl,by simp⟩,by simp⟩
        ·exact Or.inl (lw2i n jl r q.val q.isLt)
        ·right;have hsp: s≠p := fun e => hpnc (e ▸ hs)
         exact ⟨s,⟨Or.inr hs,by simp[hsp,hst]⟩,by simp[hsp]⟩
      rw[hG,hL];dsimp[d];simp only[hpq.symm,true_and,↓reduceIte]
      exact ot2i C hrb hjr hr hu hune hon0 hur hro0 hri0 hZq
       (fun j' hj' => by have := hZGl q j' hj';omega)
       (by
         rcases hZqc with ⟨he,_,hno⟩ | ⟨hne,_,q0',hq0',hq0_r,hno⟩
         ·exact Or.inl ⟨he,hno⟩
         ·exact Or.inr ⟨hne,q0',hq0',hq0_r,hno⟩)
     ·have hG: gatesOf d C Kind.z t.val=(gatesOf d1 C1 Kind.z t.val).image (li2 jl r) :=
       hgn Kind.z t.val (by simp) (fun h => htq (Fin.ext (pei.mp h).2))
      have hL: zLeaves d t=(zLeaves d1 t).image (lw2 n jl r):=by
       ext w;simp only[zLeaves,d,mN,mI,mF]
       constructor
       ·rintro (rfl|⟨s,⟨hs,hst⟩,rfl⟩)
        ·exact ⟨t.val,Or.inl rfl,lw2i n jl r t.val t.isLt⟩
        ·split_ifs at hst with hsp
         ·exact absurd (osi hst) (fun e => htq e.symm)
         ·have hs1:=(htie1 s t hst).1;simp only[hsp,↓reduceIte];exact ⟨d1.bw s,Or.inr ⟨s,⟨hs1,hst⟩,rfl⟩,rfl⟩
       ·rintro ⟨_,rfl|⟨s,⟨hs,hst⟩,rfl⟩,rfl⟩
        ·exact Or.inl (lw2i n jl r t.val t.isLt)
        ·have hsp: s≠p:=fun e => hpnc (e ▸ hs)
         exact Or.inr ⟨s,⟨Or.inr hs,by simp[hsp,hst]⟩,by simp[hsp]⟩
      rw[hG,hL];dsimp[d];simp only[htp,htq,false_and,↓reduceIte]
      exact ot2u C hcl hrb hjr hr hu hune hon0 hur (h1c t ht1).2.1
       (fun j' hj' => by have := hZGl t j' hj';omega)
       (fun j' hj' => hnZn t ht1 htq j' hj')
    ·
     have hG: gatesOf d C Kind.o t.val=(gatesOf d1 C1 Kind.o t.val).image (li2 jl r) :=
      hgn Kind.o t.val (by simp) (by simp)
     have hOt:=(h1c t ht1).2.2.1
     by_cases hro: readO t
     ·have ⟨_,hown_tq,hlam_tq,hread_disj⟩:=hro
      have hu1_oL: u1∈oLeaves d1 t:=by
       simp only[oLeaves,mI,mF,mV,true_and];exact ⟨q,hown_tq,hlam_tq⟩
      have hL: oLeaves d t=insert (n+r) (((oLeaves d1 t).erase u1).image (lw2 n jl r)):=by
       ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
        htp,false_and,↓reduceIte,mN,mE]
       constructor
       ·rintro ⟨v,hown,rfl⟩
        by_cases hvq: v=q
        ·left;simp[hvq,hro]
        ·right;simp only[hvq,false_and,↓reduceIte]
         have hne_u1: d1.lam t v≠u1:=by
          intro e;rw[←hlam_tq] at e;have hv_lam:=(h1c t ht1).2.2.2 v hown;have hq_lam:=(h1c t ht1).2.2.2 q hown_tq;unfold LamOK at hv_lam hq_lam;simp only[hq_cov,↓reduceIte] at hq_lam
          split_ifs at hv_lam with hvc
          ·exact hZd v q hvc hq_cov hvq u1 (by
            rw[←hlam_tq,←e];rcases hv_lam.2.1 with h|⟨jz,hjz,h1,h2⟩
            ·exact Or.inl (h ▸ mNs _ _)
            ·exact Or.inr ⟨by omega,by rw[h1,ascl];exact mF.mpr ⟨mR.mpr hjz,h2⟩⟩) hu1_Zq
          ·rw[hv_lam] at e;rw[hlam_tq] at e
           rcases hu1_Zq with hLz|⟨hg,_⟩
           ·simp only[zLeaves,mN,mI,mF] at hLz
            rcases hLz with h2|⟨s,⟨hs,_⟩,h2⟩
            ·exact hvq (Fin.ext (e.trans h2))
            ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;have:=v.isLt;omega
           ·have:=v.isLt;omega
         exact ⟨d1.lam t v,⟨hne_u1,v,hown,rfl⟩,rfl⟩
       ·rintro (rfl|⟨_,⟨hne_u1,v,hown,rfl⟩,rfl⟩)
        ·exact ⟨q,hown_tq,by simp[hro]⟩
        ·have hvq: v≠q:=fun e => hne_u1 (e ▸ hlam_tq)
         exact ⟨v,hown,by simp[hvq]⟩
      have hrt_eq: d.oroot t=if u1=d1.oroot t then n+r else lw2 n jl r (d1.oroot t):=by
       dsimp[d];simp only[htp,↓reduceIte,hro,and_true]
       by_cases h: d1.oroot t=u1
       ·simp[h]
       ·simp[h,Ne.symm h]
      rw[hG,hL,hrt_eq]
      exact ot2r C hcl hrb hjr hr hu hune hon0 hur hOt
       (fun j' hj' => by have := hOGl t j' hj';omega)
       hu1_oL rfl
       (fun j' hj' hm => hnu1 j' (hOGl t j' hj') hm)
       (fun j' hj' hm => by
        rcases hread_disj with ⟨ho_u,_⟩ | ⟨jo',hjo',hnr'⟩
        ·have hr0:=(hOt.2.1 u1 hu1_oL).2;rw[if_pos ho_u.symm] at hr0;have h1: 1 ≤ (gateAt C1 j').inputs.count u1:=lcpi.mpr hm
         have hle: (gateAt C1 j').inputs.count u1 ≤ readsIn C1 (gatesOf d1 C1 Kind.o t.val) u1 :=
          single_le_sum (f := fun m => (gateAt C1 m).inputs.count u1) (fun _ _ => Nat.zero_le _) hj'
         omega
        ·have hj'_eq: j' = jo' := by
          by_contra hne
          have hr1:=(hOt.2.1 u1 hu1_oL).2;have h1: 1 ≤ (gateAt C1 j').inputs.count u1:=lcpi.mpr hm;have h2: 1 ≤ (gateAt C1 jo').inputs.count u1:=lcpi.mpr (hnu1 jo' (hOGl t jo' hjo') hnr')
          have hsub: ({j',jo'}: Finset ℕ)⊆gatesOf d1 C1 Kind.o t.val:=by
           intro x hx;simp at hx;rcases hx with rfl|rfl <;> assumption
          have hsum:=sum_le_sum_of_subset (f:=fun m => (gateAt C1 m).inputs.count u1) hsub
          rw[sum_pair hne] at hsum;change _ ≤ readsIn C1 (gatesOf d1 C1 Kind.o t.val) u1 at hsum
          split_ifs at hr1 <;> omega
         exact hj'_eq ▸ hnr')
     ·have hL: oLeaves d t=(oLeaves d1 t).image (lw2 n jl r):=by
       ext w;simp only[oLeaves,d,mI,mF,mV,true_and,
        htp,false_and,↓reduceIte,hro,and_false]
       constructor
       ·rintro ⟨v,hown,rfl⟩;exact ⟨d1.lam t v,⟨v,hown,rfl⟩,rfl⟩
       ·rintro ⟨_,⟨v,hown,rfl⟩,rfl⟩;exact ⟨v,hown,rfl⟩
      have hno_Ot: ∀ j' ∈ gatesOf d1 C1 Kind.o t.val,n+r∉(gateAt C (li2 jl r j')).inputs:=by
       intro j' hj' hm;have ⟨h1,h2⟩:=hOnr j' hj' hm;exact hro ⟨ht1,h1,h2,Or.inr ⟨j',hj',hm⟩⟩
      rw[hG,hL];dsimp[d];simp only[htp,hro,and_false,↓reduceIte]
      exact ot2u C hcl hrb hjr hr hu hune hon0 hur hOt
       (fun j' hj' => by have := hOGl t j' hj';omega) hno_Ot
    ·
     intro v hown;dsimp[d] at hown;simp only[htp,false_and,↓reduceIte] at hown;have hlam:=(h1c t ht1).2.2.2 v hown;unfold LamOK at hlam ⊢;dsimp[d];simp only[htp,↓reduceIte]
     by_cases hvp: v=p
     ·rw[hvp] at hown hlam ⊢;have htq: t=q:=honly_qp t hown;simp only[hpnc,↓reduceIte] at hlam;simp only[mNs p,↓reduceIte,hpq,false_and];rw[hlam,lw2i n jl r p.val p.isLt]
      refine ⟨by rw[cfi C d p];exact mNs p _,Or.inl rfl,fun _ => rfl⟩
     ·by_cases hvq: v=q
      ·rw[hvq] at hown hlam ⊢;simp only[hq_cov,mNo hq_cov,↓reduceIte,true_and] at hlam ⊢
       by_cases hro: readO t
       ·simp only[hro,↓reduceIte];have hlam_eq: d1.lam t q=u1:=hro.2.2.1
        refine ⟨hcnr (hlam_eq ▸ hlam.1),
         Or.inr ⟨r,hr,rfl,by simp[roleB,Nat.ne_of_gt hjr]⟩,?_⟩
        intro htie;simp only[hpq.symm,↓reduceIte] at htie ⊢;have hzr_eq:=hlam.2.2 htie;rw[hlam_eq] at hzr_eq;simp[hzr_eq]
       ·simp only[hro,↓reduceIte]
        refine ⟨hcZq (d1.lam t q) hlam.1 (by rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩;exact Or.inl h;exact Or.inr ⟨jz,hjz,h1,h2⟩),
         ?_,?_⟩
        ·rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
         ·exact Or.inl (by rw[h,lw2i n jl r q.val q.isLt])
         ·exact Or.inr ⟨li2 jl r jz,li2lt hjr hr (by omega),by rw[h1,lw2g],by rw[hrl,h2]⟩
        ·intro htie;simp only[hpq.symm,↓reduceIte] at htie ⊢;have hzr_eq:=hlam.2.2 htie
         by_cases hu_zq: u1=d1.zroot q
         ·exfalso
          have hlam_eq_u1: d1.lam t q=u1:=hzr_eq.trans hu_zq.symm
          have hno_Ot: ∀ j' ∈ gatesOf d1 C1 Kind.o t.val,n+r∉(gateAt C (li2 jl r j')).inputs:=fun j' hj' hm =>
           hro ⟨ht1,hown,hlam_eq_u1,Or.inr ⟨j',hj',hm⟩⟩
          obtain ⟨jbt,hjbt,hbwt,hrbt,hopt,hint⟩:=(h1c t ht1).1
          have hno_Bt_or: d1.oroot t=u1 → n+r∉(gateAt C (li2 jl r jbt)).inputs:=fun ho hm =>
           hro ⟨ht1,hown,hlam_eq_u1,Or.inl ⟨ho,jbt,hjbt,hbwt,hm⟩⟩
          have hkill: ∀ w < n+C1.gates.length,
            (w < n → w≠l.val∧w≠p.val) →
            (∀ j' < C1.gates.length,w=n + j' →
             (d1.role j').1=Kind.top ∨
             (∃ s∈d1.cover,s≠q∧d1.role j' = (Kind.b,s.val)) ∨
             (∃ s∈d1.cover,s≠q∧s≠t∧d1.role j' = (Kind.z,s.val)) ∨
             d1.role j' = (Kind.o,t.val)) →
            vl C.gates x_lp (lw2 n jl r w)=false:=by
           intro w;induction w using Nat.strong_induction_on with
           | ind w ih =>
            intro hw hlt_in hP
            by_cases hwn: w < n
            ·rw[lw2i n jl r w hwn,vli C.gates x_lp w hwn];have ⟨h1,h2⟩:=hlt_in hwn
             simp[x_lp,show (⟨w,hwn⟩ : Fin n)≠l from fun e => h1 (congrArg Fin.val e),
              show (⟨w,hwn⟩ : Fin n)≠p from fun e => h2 (congrArg Fin.val e)]
            ·set j' := w - n;have hweq: w=n + j' := by omega
             have hj' : j' < C1.gates.length:=by omega
             have hlt_C: li2 jl r j' < C.gates.length:=li2lt hjr hr (by rw[←hlen1];exact hj')
             have hgC: C.gates[li2 jl r j']? = some (gateAt C (li2 jl r j')):=by simp[gateAt,List.getD,hlt_C]
             have hlif:=r2l C hcl hrb hjr hr hu j' (by omega);rw[hweq,lw2g,vlg C.gates hcl x_lp _ _ hgC,←hlif.1]
             rcases hP j' hj' hweq with htop_j|⟨s,hs,hsq,hrb_s⟩ | ⟨s,hs,hsq,hst,hrz_s⟩ | hro_t
             ·have hjT: j' ∈ topGates d1 C1:=mF.mpr ⟨mR.mpr hj',htop_j⟩;obtain ⟨hop,_,hins⟩:=htop1.1 j' hjT;have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur j' (by omega) (hnt1 j' hjT);rw[hop,hinp,lmp];simp only[GateOp.eval,lyF,lmm,Function.comp_apply,Bool.not_eq_true,id_eq]
              rintro _ ⟨a,ha,rfl⟩;have halt: a < n + j' := hrb1 j' hj' a ha
              apply ih a (by omega) (by omega)
              ·intro han;rcases hins a ha with hL|⟨_,_⟩
               ·simp only[topLeaves,mU,mI,mF] at hL
                rcases hL with ⟨a',ha',rfl⟩ | ⟨s',⟨hs',_⟩,rfl⟩
                ·exact ⟨fun e => hlnA (Fin.ext e.symm ▸ ha'),fun e => hpnA (Fin.ext e.symm ▸ ha')⟩
                ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s' hs').1;omega
               ·omega
              ·intro k _ eak;rcases hins a ha with hL|⟨_,hG⟩
               ·simp only[topLeaves,mU,mI,mF] at hL
                rcases hL with ⟨a',_,rfl⟩ | ⟨s',⟨hs',hs'f⟩,rfl⟩
                ·have := a'.isLt;omega
                ·have hs'q: s' ≠ q:=fun e => by rw[e,htie] at hs'f;cases hs'f
                 obtain ⟨jb,_,hbw,hrb',_,_⟩:=(h1c s' hs').1
                 have: k=jb := (by omega);right;left;exact ⟨s',hs',hs'q,by rw[this,hrb']⟩
               ·left;have hG' := (mF.mp hG).2;rw[eak,ascl] at hG';exact hG'
             ·obtain ⟨jbs,hjbs,hbws,_,hops,hins⟩:=(h1c s hs).1
              have hje: j' = jbs:=by
               rcases hrol1 j' hj' with ht' | ⟨s',_,e1,e2⟩
               ·rw[hrb_s] at ht';cases ht'
               ·rw[hrb_s] at e1;have hss' : s' = s := Fin.ext e1.symm;rw[hss'] at e2
                have:=e2 (by rw[hrb_s]);omega
              rw[hje] at hlif ⊢;rw[hops]
              have hlenC: (gateAt C (li2 jl r jbs)).inputs.length=2:=by
               have h2: (gateAt C1 jbs).inputs.length=2:=by rcases hins with h|h <;> simp[h]
               rw[hlif.2,llm] at h2;exact h2
              obtain ⟨x1,x2,hx12⟩:=ll2.mp hlenC
              have hmap: [rd n jl 0 (rd n r u x1),rd n jl 0 (rd n r u x2)]=(gateAt C1 jbs).inputs:=by
               rw[hlif.2,hx12];rfl
              have hne_jl: ∀ c∈(gateAt C (li2 jl r jbs)).inputs,c≠n+jl:=fun c hc e =>
               li2nr jl r jbs (hur _ (by rw[←hje];exact hlt_C) (e ▸ hc))
              by_cases hst: s=t
              ·
               rw[hst] at hins hbws
               have hor_lt: d1.oroot t < n+jbs:=hrb1 jbs hjbs (d1.oroot t) (by rcases hins with h|h <;> simp[h])
               have hor_f: vl C.gates x_lp (lw2 n jl r (d1.oroot t))=false:=by
                by_cases ho_u: d1.oroot t=u1
                ·rw[ho_u,hu_lw,hvl_u x_lp,hlpu]
                ·apply ih (d1.oroot t) (by omega) (by omega)
                 ·intro han;rcases ors hv1 t ht1 with ⟨r',hown',hlam'⟩ | ⟨_,_,_,_⟩
                  ·have hr'q: r' ≠ q:=fun e => ho_u (by rw[hlam',e,hlam_eq_u1])
                   have hr'p: r' ≠ p:=fun e => hsq (hst.trans (honly_qp t (e ▸ hown')))
                   have hr'l: r' ≠ l:=fun e => hl_iso t (e ▸ (hown1.1 t r' hown').1).symm
                   have hl' := (h1c t ht1).2.2.2 r' hown';unfold LamOK at hl';split_ifs at hl'
                   ·rcases hl'.2.1 with h|⟨_,_,h,_⟩
                    ·exact ⟨fun e => hr'l (Fin.ext (h.symm.trans (hlam'.symm.trans e))),
                      fun e => hr'p (Fin.ext (h.symm.trans (hlam'.symm.trans e)))⟩
                    ·omega
                   ·exact ⟨fun e => hr'l (Fin.ext (hl'.symm.trans (hlam'.symm.trans e))),
                     fun e => hr'p (Fin.ext (hl'.symm.trans (hlam'.symm.trans e)))⟩
                  ·omega
                 ·intro k _ ek;rcases ors hv1 t ht1 with ⟨r',hown',hlam'⟩ | ⟨jo,_,hor,hro'⟩
                  ·have hr'q: r' ≠ q:=fun e => ho_u (by rw[hlam',e,hlam_eq_u1])
                   have hr't: r' ≠ t:=(hown1.1 t r' hown').1.ne';have hl' := (h1c t ht1).2.2.2 r' hown';unfold LamOK at hl';split_ifs at hl' with hrc
                   ·rcases hl'.2.1 with h|⟨jz,_,h,hrz'⟩
                    ·have := r'.isLt;omega
                    ·right;right;left;have: k=jz := (by omega)
                     exact ⟨r',hrc,hr'q,hr't,by rw[this,hrz']⟩
                   ·have := r'.isLt;omega
                  ·right;right;right;have: k=jo := (by omega);rw[this,hro']
               have hor_inC: lw2 n jl r (d1.oroot t)∈(gateAt C (li2 jl r jbs)).inputs:=by
                have hmem1: d1.oroot t∈(gateAt C1 jbs).inputs:=by rcases hins with h|h <;> simp[h]
                rw[←hmap] at hmem1;simp at hmem1
                rcases hmem1 with e|e
                ·have hx1_ne: x1≠n+r:=fun er => by
                  have ho_u: d1.oroot t=u1:=by rw[e,er,rd_eq]
                  have hjbt_eq: jbs=jbt:=by rw[hbwt] at hbws;omega
                  exact hno_Bt_or ho_u (by rw[←hjbt_eq,hx12,er];simp)
                 rw[show lw2 n jl r (d1.oroot t)=x1 by rw[e,lw2r hjr (hne_jl x1 (by rw[hx12];simp)) hx1_ne],hx12];simp
                ·have hx2_ne: x2≠n+r:=fun er => by
                  have ho_u: d1.oroot t=u1:=by rw[e,er,rd_eq]
                  have hjbt_eq: jbs=jbt:=by rw[hbwt] at hbws;omega
                  exact hno_Bt_or ho_u (by rw[←hjbt_eq,hx12,er];simp)
                 rw[show lw2 n jl r (d1.oroot t)=x2 by rw[e,lw2r hjr (hne_jl x2 (by rw[hx12];simp)) hx2_ne],hx12];simp
               simp only[GateOp.eval,laF,lmm,id_eq];exact ⟨false,⟨lw2 n jl r (d1.oroot t),hor_inC,hor_f⟩,by simp⟩
              ·
               have hzr_lt: d1.zroot s < n+jbs:=hrb1 jbs hjbs (d1.zroot s) (by rcases hins with h|h <;> simp[h])
               have hzr_f: vl C.gates x_lp (lw2 n jl r (d1.zroot s))=false:=by
                apply ih (d1.zroot s) (by omega) (by omega)
                ·intro han;rcases zrs hv1 s hs with h|⟨_,_,_,_⟩
                 ·exact ⟨fun e => hlnc (Fin.ext (h.symm.trans e) ▸ hs),fun e => hpnc (Fin.ext (h.symm.trans e) ▸ hs)⟩
                 ·omega
                ·intro k _ ek;rcases zrs hv1 s hs with h|⟨jz,_,_,hrz'⟩
                 ·have:=s.isLt;omega
                 ·right;right;left;have: k=jz := (by omega)
                  exact ⟨s,hs,hsq,hst,by rw[this,hrz']⟩
               have hzr_ne_u1: d1.zroot s≠u1:=fun e => hZd s q hs hq_cov hsq u1 (by
                rw[←e];rcases zrs hv1 s hs with h|⟨jz,hjz,hzr,hrz'⟩
                ·exact Or.inl (h ▸ mNs _ _)
                ·exact Or.inr ⟨by omega,by rw[hzr,ascl];exact mF.mpr ⟨mR.mpr hjz,hrz'⟩⟩) hu1_Zq
               have hzr_inC: lw2 n jl r (d1.zroot s)∈(gateAt C (li2 jl r jbs)).inputs:=by
                have hmem1: d1.zroot s∈(gateAt C1 jbs).inputs:=by rcases hins with h|h <;> simp[h]
                rw[←hmap] at hmem1;simp at hmem1
                rcases hmem1 with e|e
                ·have hx1_ne: x1≠n+r:=fun er => hzr_ne_u1 (by rw[e,er,rd_eq])
                 rw[show lw2 n jl r (d1.zroot s)=x1 by rw[e,lw2r hjr (hne_jl x1 (by rw[hx12];simp)) hx1_ne],hx12];simp
                ·have hx2_ne: x2≠n+r:=fun er => hzr_ne_u1 (by rw[e,er,rd_eq])
                 rw[show lw2 n jl r (d1.zroot s)=x2 by rw[e,lw2r hjr (hne_jl x2 (by rw[hx12];simp)) hx2_ne],hx12];simp
               simp only[GateOp.eval,laF,lmm,id_eq];exact ⟨false,⟨lw2 n jl r (d1.zroot s),hzr_inC,hzr_f⟩,by simp⟩
             ·
              have hjZ: j' ∈ gatesOf d1 C1 Kind.z s.val:=mF.mpr ⟨mR.mpr hj',hrz_s⟩;obtain ⟨hop,_,hins⟩:=(h1c s hs).2.1.1 j' hjZ;have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur j' (by omega) (hnZn s hs hsq j' hjZ);rw[hop,hinp,lmp];simp only[GateOp.eval,lyF,lmm,Function.comp_apply,Bool.not_eq_true,id_eq]
              rintro _ ⟨a,ha,rfl⟩;have halt: a < n + j' := hrb1 j' hj' a ha
              apply ih a (by omega) (by omega)
              ·intro han;rcases hins a ha with hL|⟨_,_⟩
               ·simp only[zLeaves,mN,mI,mF] at hL
                rcases hL with rfl|⟨s',⟨hs',_⟩,rfl⟩
                ·exact ⟨fun e => hlnc (Fin.ext e.symm ▸ hs),fun e => hpnc (Fin.ext e.symm ▸ hs)⟩
                ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s' hs').1;omega
               ·omega
              ·intro k _ eak;rcases hins a ha with hL|⟨_,hG⟩
               ·simp only[zLeaves,mN,mI,mF] at hL
                rcases hL with rfl|⟨s',⟨hs',hs't⟩,rfl⟩
                ·have:=s.isLt;omega
                ·have hs'q: s' ≠ q:=fun e => by rw[e,htie] at hs't;exact hst (osi hs't).symm
                 obtain ⟨jb,_,hbw,hrb',_,_⟩:=(h1c s' hs').1
                 have: k=jb := (by omega);right;left;exact ⟨s',hs',hs'q,by rw[this,hrb']⟩
               ·right;right;left;have hG' := (mF.mp hG).2
                rw[eak,ascl] at hG';exact ⟨s,hs,hsq,hst,hG'⟩
             ·
              have hjO: j' ∈ gatesOf d1 C1 Kind.o t.val:=mF.mpr ⟨mR.mpr hj',hro_t⟩;obtain ⟨hop,_,hins⟩:=(h1c t ht1).2.2.1.1 j' hjO;have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur j' (by omega) (hno_Ot j' hjO);rw[hop,hinp,lmp];simp only[GateOp.eval,lyF,lmm,Function.comp_apply,Bool.not_eq_true,id_eq]
              rintro _ ⟨a,ha,rfl⟩;have halt: a < n + j' := hrb1 j' hj' a ha
              by_cases hau: a=u1
              ·rw[hau,hu_lw,hvl_u x_lp,hlpu]
              ·apply ih a (by omega) (by omega)
               ·intro han;rcases hins a ha with hL|⟨_,_⟩
                ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',rfl⟩:=hL
                 have hr'p: r' ≠ p:=fun e => by
                  have htq: t=q:=honly_qp t (e ▸ hown');exact (hown1.1 t q hown).1.ne htq
                 have hr'l: r' ≠ l:=fun e => hl_iso t (e ▸ (hown1.1 t r' hown').1).symm
                 have hl' := (h1c t ht1).2.2.2 r' hown';unfold LamOK at hl';split_ifs at hl'
                 ·rcases hl'.2.1 with h|⟨_,_,h,_⟩
                  ·exact ⟨fun e => hr'l (Fin.ext (h.symm.trans e)),fun e => hr'p (Fin.ext (h.symm.trans e))⟩
                  ·omega
                 ·exact ⟨fun e => hr'l (Fin.ext (hl'.symm.trans e)),fun e => hr'p (Fin.ext (hl'.symm.trans e))⟩
                ·omega
               ·intro k _ eak;rcases hins a ha with hL|⟨_,hG⟩
                ·simp only[oLeaves,mI,mF,mV,true_and] at hL;obtain ⟨r',hown',rfl⟩:=hL
                 have hr'q: r' ≠ q:=fun e => hau (e ▸ hlam_eq_u1)
                 have hr't: r' ≠ t:=(hown1.1 t r' hown').1.ne';have hl' := (h1c t ht1).2.2.2 r' hown';unfold LamOK at hl';split_ifs at hl' with hrc
                 ·rcases hl'.2.1 with h|⟨jz,_,h,hrz'⟩
                  ·have := r'.isLt;omega
                  ·right;right;left;have: k=jz := (by omega)
                   exact ⟨r',hrc,hr'q,hr't,by rw[this,hrz']⟩
                 ·have := r'.isLt;omega
                ·right;right;right;have hG' := (mF.mp hG).2
                 rw[eak,ascl] at hG';exact hG'
          have hrm: C1.output∈topLeaves d1 A∨(n ≤ C1.output∧C1.output - n∈topGates d1 C1):=by
           by_cases hGe: topGates d1 C1 = ∅
           ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;left;rw[h1];simp
           ·have h1:=htop1.2.2.2;simp only[hGe,↓reduceIte] at h1;obtain ⟨g,hg,hρ⟩:=h1;right;exact ⟨by omega,by rw[hρ,ascl];exact hg⟩
          have h1:=hkill C1.output h1ol
           (fun han => by
            rcases hrm with hL|⟨_,_⟩
            ·simp only[topLeaves,mU,mI,mF] at hL
             rcases hL with ⟨a,ha,hea⟩ | ⟨s,⟨hs,_⟩,hes⟩
             ·exact ⟨fun e => hlnA (Fin.ext (hea.trans e).symm ▸ ha),fun e => hpnA (Fin.ext (hea.trans e).symm ▸ ha)⟩
             ·obtain ⟨jb,_,hbw,_,_,_⟩:=(h1c s hs).1;omega
            ·omega)
           (fun k _ ek => by
            rcases hrm with hL|⟨_,hG⟩
            ·simp only[topLeaves,mU,mI,mF] at hL
             rcases hL with ⟨a,_,hea⟩ | ⟨s,⟨hs,hsf⟩,hes⟩
             ·have:=a.isLt;omega
             ·have hsq: s≠q:=fun e => by rw[e,htie] at hsf;cases hsf
              obtain ⟨jb,_,hbw,hrb',_,_⟩:=(h1c s hs).1
              have: k=jb := (by omega);right;left;exact ⟨s,hs,hsq,by rw[this,hrb']⟩
            ·left;have hG' := (mF.mp hG).2;rw[ek,ascl] at hG';exact hG')
          rw[lw2r hjr hon0 hne_out,hlpC] at h1;cases h1
         ·simp[hu_zq,hzr_eq]
      ·simp only[hvq,false_and,↓reduceIte]
       by_cases hvc: v∈d1.cover
       ·have hvc' : v∈insert p d1.cover:=mNo hvc;simp only[hvc,hvc',↓reduceIte] at hlam ⊢
        refine ⟨?_,?_,?_⟩
        ·have hcen_v: ∀ w: ℕ,IsCentred n C1 d1 w →
           (w=v.val ∨ ∃ jz < C1.gates.length,w=n+jz∧d1.role jz=(Kind.z,v.val)) →
           IsCentred n C d (lw2 n jl r w):=by
          intro w;induction w using Nat.strong_induction_on with
          | ind w ih =>
           intro hc hwv
           rcases hwv with rfl|⟨jz,hjz,rfl,hrz⟩
           ·rw[lw2i n jl r v.val v.isLt,cfi C d v];exact hvc'
           ·rw[cfg C1 d1 hrb1 jz hjz] at hc;obtain ⟨_,a,ha,ha_cen⟩:=hc;have hjZ: jz∈gatesOf d1 C1 Kind.z v.val:=mF.mpr ⟨mR.mpr hjz,hrz⟩;have ha_lt: a < n+jz:=hrb1 jz hjz a ha
            have ha_spec: a=v.val ∨ ∃ k < C1.gates.length,a=n+k∧d1.role k=(Kind.z,v.val):=by
             rcases ((h1c v hvc).2.1.1 jz hjZ).2.2 a ha with hL|⟨hg,hG⟩
             ·simp only[zLeaves,mN,mI,mF] at hL
              rcases hL with rfl|⟨s,⟨hs,_⟩,rfl⟩
              ·exact Or.inl rfl
              ·obtain ⟨jb,hjb,hbw,hrb_s,_,_⟩:=(h1c s hs).1;rw[hbw,cfg C1 d1 hrb1 jb hjb,hrb_s] at ha_cen;cases ha_cen.1
             ·exact Or.inr ⟨a - n,hZGl v _ hG,by omega,(mF.mp hG).2⟩
            have hno_v:=hnZn v hvc hvq jz hjZ;have hinp:=r2in C hcl hrb hjr hr hu hune hon0 hur jz (by omega) hno_v;rw[lw2g,cfg C d hrb (li2 jl r jz) (li2lt hjr hr (by omega))]
            exact ⟨by dsimp[d];rw[hrl,hrz],lw2 n jl r a,
             by rw[hinp];exact lmm.mpr ⟨a,ha,rfl⟩,ih a (by omega) ha_cen ha_spec⟩
         exact hcen_v (d1.lam t v) hlam.1 (by rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩;exact Or.inl h;exact Or.inr ⟨jz,hjz,h1,h2⟩)
        ·rcases hlam.2.1 with h|⟨jz,hjz,h1,h2⟩
         ·exact Or.inl (by rw[h,lw2i n jl r v.val v.isLt])
         ·exact Or.inr ⟨li2 jl r jz,li2lt hjr hr (by omega),by rw[h1,lw2g],by rw[hrl,h2]⟩
        ·intro htie;simp only[hvp,hvq,false_and,↓reduceIte] at htie ⊢;rw[hlam.2.2 htie]
       ·have hvc' : v∉insert p d1.cover:=by simp[hvp,hvc]
        simp only[hvc,hvc',↓reduceIte] at hlam ⊢;rw[hlam,lw2i n jl r v.val v.isLt]
  ·
   have hG: topGates d C=(topGates d1 C1).image (li2 jl r):=by
    ext j;simp only[topGates,d,mF,mR,mI]
    constructor
    ·rintro ⟨hj,hrj⟩
     have hje: j≠jl:=fun e => by rw[e] at hrj;simp[roleB] at hrj
     have hre: j≠r:=fun e => by rw[e] at hrj;simp[roleB,Nat.ne_of_gt hjr] at hrj
     obtain ⟨j',hj',rfl⟩:=li2s hjr hr hj hje hre;exact ⟨j',⟨by omega,by rw[←hrl j'];exact hrj⟩,rfl⟩
    ·rintro ⟨j',⟨hj',hrj'⟩,rfl⟩
     exact ⟨li2lt hjr hr (by omega),by rw[hrl,hrj']⟩
   have hL: topLeaves d A=(topLeaves d1 A).image (lw2 n jl r):=by
    ext w;simp only[topLeaves,d,mU,mI,mF]
    constructor
    ·rintro (⟨a,ha,rfl⟩ | ⟨s,⟨hs,hst⟩,rfl⟩)
     ·exact ⟨a.val,Or.inl ⟨a,ha,rfl⟩,lw2i n jl r a.val a.isLt⟩
     ·by_cases hsp: s=p
      ·simp[hsp] at hst
      ·simp only[hsp,↓reduceIte] at hst ⊢
       have hs1: s∈d1.cover:=by rcases mN.mp hs with rfl|h;exact absurd rfl hsp;exact h
       exact ⟨d1.bw s,Or.inr ⟨s,⟨hs1,hst⟩,rfl⟩,rfl⟩
    ·rintro ⟨_,⟨a,ha,rfl⟩ | ⟨s,⟨hs,hst⟩,rfl⟩,rfl⟩
     ·left;exact ⟨a,ha,(lw2i n jl r a.val a.isLt).symm⟩
     ·right;have hsp: s≠p := fun e => hpnc (e ▸ hs)
      exact ⟨s,⟨mNo hs,by simp[hsp,hst]⟩,by simp[hsp]⟩
   rw[hG,hL,←lw2r hjr hon0 hne_out]
   exact ot2u C hcl hrb hjr hr hu hune hon0 hur htop1
    (fun j' hj' => by have := htGl j' hj';omega) hnt1
lemma L_meta_540_main
  (n: ℕ) (K K1 K2: SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj]
  (A: Finset (Fin n)) (l p q: Fin n)
  (k m: ℕ) (H: SimpleGraph (Fin m)) (hk: 3 ≤ k)
  (hemb: Nonempty (K.Adj ↪r (PEqualNP.Library.Subdivision.subdiv k H).Adj))
  (hA: ∀ a∈A,∀ v: Fin n,¬ K.Adj a v)
  (hl: ∀ v: Fin n,K.Adj l v↔v=p)
  (hql: q≠l)
  (hp: ∀ v: Fin n,K.Adj p v↔v=l∨v=q)
  (hK1: ∀ u v: Fin n,K1.Adj u v↔K.Adj u v∧u≠l∧v≠l)
  (hK2: ∀ u v: Fin n,K2.Adj u v↔K.Adj u v∧u≠l∧u≠p∧v≠l∧v≠p)
  (hIH1: ∀ C: PEqualNP.CircuitLowerBounds.Circuit,
   (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧
    PEqualNP.MetaComplexity.circuitFun n C=PEqualNP.MetaComplexity.NestedCover.graphFun K1 A) ↔
   PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K1 A C)
  (hIH2: ∀ C: PEqualNP.CircuitLowerBounds.Circuit,
   (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧
    PEqualNP.MetaComplexity.circuitFun n C=PEqualNP.MetaComplexity.NestedCover.graphFun K2 (insert p A)) ↔
   PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K2 (insert p A) C) :
  ∀ C: PEqualNP.CircuitLowerBounds.Circuit,
   (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧
    PEqualNP.MetaComplexity.circuitFun n C=PEqualNP.MetaComplexity.NestedCover.graphFun K A) ↔
   PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K A C:=by
 cases n with
 | zero => exact l.elim0
 | succ n' =>
  have hn: 0 < n' + 1:=Nat.succ_pos n';have hlp: l≠p:=((hl p).mpr rfl).ne;have hpl: p≠l:=hlp.symm;have hpq: p≠q:=((hp q).mpr (Or.inr rfl)).ne;have hKpq: K.Adj p q:=(hp q).mpr (Or.inr rfl);have hK1pq: K1.Adj p q:=(hK1 p q).mpr ⟨hKpq,hpl,hql⟩
  have hlnA: l∉A:=fun h => hA l h p ((hl p).mpr rfl)
  have hpnA: p∉A:=fun h => hA p h l ((hl p).mpr rfl).symm
  have hqnA: q∉A:=fun h => hA q h p hKpq.symm
  have hE1: K.edgeFinset.card=K1.edgeFinset.card+1:=ecEq hl hK1
  have hE2: K1.edgeFinset.card=K2.edgeFinset.card+1:=by
   have hp1: ∀ v: Fin (n' + 1),K1.Adj p v↔v=q:=by
    intro v;rw[hK1,hp];constructor
    ·rintro ⟨rfl|rfl,_,hvl⟩;exact absurd rfl hvl;rfl
    ·rintro rfl;exact ⟨Or.inr rfl,hpl,hql⟩
   have hK2' : ∀ u v: Fin (n' + 1),K2.Adj u v↔K1.Adj u v∧u≠p∧v≠p:=by
    intro u v;rw[hK2,hK1];tauto
   exact ecEq hp1 hK2'
  obtain ⟨T0,hT0⟩:=mcEx K;obtain ⟨T1,hT1⟩:=mcEx K1;obtain ⟨T2,hT2⟩:=mcEx K2;have htau2: T0.card=T2.card+1:=tK2 hl hp hK2 hT0 hT2
  have htau1_le: T1.card ≤ T0.card:=hT1.2 T0 (fun u v huv => hT0.1 ((hK1 u v).mp huv).1)
  have htau1_ge: T0.card ≤ T1.card+1:=by
   have hcovK: K.IsVertexCover ((insert p T1: Finset (Fin (n' + 1))): Set (Fin (n' + 1))):=by
    intro u v huv
    by_cases hul: u=l
    ·right;rw[(hl v).mp (hul ▸ huv)];exact mC.mpr (mNs _ _)
    ·by_cases hvl: v=l
     ·left;rw[(hl u).mp (hvl ▸ huv.symm)];exact mC.mpr (mNs _ _)
     ·rcases hT1.1 ((hK1 u v).mpr ⟨huv,hul,hvl⟩) with hu|hv
      ·left;exact mC.mpr (mNo (mC.mp hu))
      ·right;exact mC.mpr (mNo (mC.mp hv))
   have h1:=hT0.2 (insert p T1) hcovK;have h2:=card_insert_le p T1;omega
  obtain ⟨C1_0,hC1_min,hC1_cf⟩:=mciEx (graphFun K1 A);obtain ⟨d1_0,hv1_0⟩:=(hIH1 C1_0).mp ⟨hC1_min,hC1_cf⟩
  have hM1_eq: C1_0.size+1=A.card+K1.edgeFinset.card+T1.card:=by
   have hs:=ncc_size hv1_0;have hc: d1_0.cover.card=T1.card:=le_antisymm (hv1_0.2.1.2 T1 hT1.1) (hT1.2 d1_0.cover hv1_0.2.1.1);omega
  have hM1_lb: ∀ s: ℕ,HasCircuitSize (n' + 1) (graphFun K1 A) s→C1_0.size ≤ s:=fun s ⟨D,hf,hsz,hcf⟩ =>
   le_trans (hC1_min.2 D hf ((funext hcf).trans hC1_cf.symm)) hsz
  obtain ⟨C2_0,hC2_min,hC2_cf⟩:=mciEx (graphFun K2 (insert p A));obtain ⟨d2_0,hv2_0⟩:=(hIH2 C2_0).mp ⟨hC2_min,hC2_cf⟩
  have hM2_eq: C2_0.size+1=(A.card+1)+K2.edgeFinset.card+T2.card:=by
   have hs:=ncc_size hv2_0;have hc: d2_0.cover.card=T2.card:=le_antisymm (hv2_0.2.1.2 T2 hT2.1) (hT2.2 d2_0.cover hv2_0.2.1.1);rw[card_insert_of_notMem hpnA] at hs;omega
  have hM2_lb: ∀ s: ℕ,HasCircuitSize (n' + 1) (graphFun K2 (insert p A)) s→C2_0.size ≤ s:=fun s ⟨D,hf,hsz,hcf⟩ =>
   le_trans (hC2_min.2 D hf ((funext hcf).trans hC2_cf.symm)) hsz
  let NK: ℕ := A.card+K.edgeFinset.card+T0.card - 1
  have hNK_eq_M2: NK=C2_0.size+2:=by
   have hpos1: 1 ≤ K1.edgeFinset.card:=card_pos.mpr ⟨s(p,q),by simpa using hK1pq⟩;omega
  have hNK_le_M1: NK ≤ C1_0.size+2:=by
   have hpos1: 1 ≤ K1.edgeFinset.card:=card_pos.mpr ⟨s(p,q),by simpa using hK1pq⟩;omega
  have hK_ub: HasCircuitSize (n' + 1) (graphFun K A) NK :=
   nfc_graph_upper K A T0 ⟨l,p,(hl p).mpr rfl⟩ hT0.1
  have hdep_l: ∃ x: Fin (n' + 1)→Bool,
    graphFun K A (Function.update x l (!x l))≠graphFun K A x:=by
   let x: Fin (n' + 1)→Bool:=fun v => decide (v=p)
   refine ⟨x,?_⟩
   have h1: graphFun K A x=false:=by
    simp only[graphFun,boF,dFn,x,dTe]
    exact ⟨fun ⟨a,ha,e⟩ => hpnA (e ▸ ha),fun ⟨u,v,huv,e1,e2⟩ => huv.ne (e1.trans e2.symm)⟩
   have h2: graphFun K A (Function.update x l (!x l))=true:=by
    simp only[graphFun,boT,dTe]
    right;exact ⟨l,p,(hl p).mpr rfl,by simp[x,hlp],by rw[fupn hpl];simp[x]⟩
   rw[h1,h2];decide
  have hnc_l: ∀ b: Bool,∃ x y: Fin (n' + 1)→Bool,
    graphFun K A (Function.update x l b)≠graphFun K A (Function.update y l b):=by
   intro b
   refine ⟨fun _ => false,fun v => decide (v=p∨v=q),?_⟩
   have h1: graphFun K A (Function.update (fun _ => false) l b)=false:=by
    simp only[graphFun,boF,dFn]
    refine ⟨?_,?_⟩
    ·rintro ⟨a,ha,hxa⟩
     by_cases hal: a=l
     ·exact hlnA (hal ▸ ha)
     ·rw[fupn hal] at hxa;cases hxa
    ·rintro ⟨u,v,huv,hxu,hxv⟩
     by_cases hul: u=l
     ·by_cases hvl: v=l
      ·exact huv.ne (hul.trans hvl.symm)
      ·rw[fupn hvl] at hxv;cases hxv
     ·rw[fupn hul] at hxu;cases hxu
   have h2: graphFun K A (Function.update (fun v => decide (v=p∨v=q)) l b)=true:=by
    simp only[graphFun,boT,dTe]
    right;exact ⟨p,q,hKpq,by rw[fupn hpl];simp,by rw[fupn hql];simp⟩
   rw[h1,h2];decide
  have hfwd: ∀ C: Circuit,IsMinimalCircuit (n' + 1) C → circuitFun (n' + 1) C=graphFun K A →
    IsNestedCoverCircuit (n' + 1) K A C:=by
   intro C hmin hcf
   have hC_le_NK: C.size ≤ NK:=by
    obtain ⟨D,hfD,hszD,hcfD⟩:=hK_ub;exact le_trans (hmin.2 D hfD ((funext hcfD).trans hcf.symm)) hszD
   have hnc_K: ∃ x y: Fin (n' + 1)→Bool,circuitFun (n' + 1) C x≠circuitFun (n' + 1) C y:=by
    obtain ⟨x,y,hxy⟩:=hnc_l false;exact ⟨_,_,by rw[hcf];exact hxy⟩
   have hcl_norm: CL (n' + 1) (C.gates.map ng0):=mnc C hmin hnc_K;let gs:=C.gates.map ng0
   have hgs_len: gs.length=C.size:=by simp[gs,Circuit.size]
   have hL: Least (n' + 1) (graphFun K A) gs C.output:={
    hcl := hcl_norm
    hev := fun x => by
     have h1: vl gs x C.output=circuitFun (n' + 1) C x:=by
      unfold vl circuitFun Circuit.eval;rw[wng0];rfl
     rw[h1,hcf]
    hmin := fun gs' o' hcl' hev' => by
     obtain ⟨D,hfD,hsD,hcD⟩:=has_of_clean (n' + 1) gs' o' hcl'
     have hle:=hmin.2 D hfD ((funext fun x => (hcD x).trans (hev' x)).trans hcf.symm)
     omega
   }
   have hno3: ∀ b: Bool,¬ Drop (graphFun K A) l b 3 gs.length:=by
    intro b ⟨t,ht,hc⟩
    cases b with
    | false =>
     have hc1: HasCircuitSize (n' + 1) (graphFun K1 A) t:=by
      obtain ⟨E,hfE,hsE,hcE⟩:=hc
      exact ⟨E,hfE,hsE,fun x => (hcE x).trans (gfK1 hA hl hK1 x).symm⟩
     have hle:=hM1_lb t hc1;omega
    | true =>
     have hc2: HasCircuitSize (n' + 1) (graphFun K2 (insert p A)) t:=by
      obtain ⟨E,hfE,hsE,hcE⟩:=hc
      exact ⟨E,hfE,hsE,fun x => (hcE x).trans (gfK2 hA hl hp hK2 x)⟩
     have hle:=hM2_lb t hc2;omega
   obtain ⟨jl,wl,r,u,g_l,g_r,hjr,hr_len,hw_l,hwne,hu,hune,ho_ne_l,ho_ne_jl,
    hgl,hgr,hgl_in,hgr_in,hul,hur,hop_cases⟩ :=
    urpB (graphFun K A) gs C.output hL l hdep_l hnc_l hno3
   set Cn0: Circuit:=⟨gs,C.output⟩
   have hrb_norm: ReadsBack (n' + 1) Cn0:=by
    intro j hj i hi
    have hgj: gs[j]? = some (gateAt Cn0 j):=by simp[Cn0,gateAt,List.getD,hj]
    exact (hcl_norm j _ hgj).lt i hi
   have hgat_jl: gateAt Cn0 jl=g_l:=by simp[Cn0,gateAt,List.getD,hgl]
   have hgat_r: gateAt Cn0 r=g_r:=by simp[Cn0,gateAt,List.getD,hgr]
   have hur' : ∀ q' < Cn0.gates.length,n' + 1+jl∈(gateAt Cn0 q').inputs → q' = r:=fun q' hq' hm =>
    hur q' ⟨gateAt Cn0 q',by simp[Cn0,gateAt,List.getD,hq'],hm⟩
   have hu_ne_l: u≠l.val:=fun e => by
    have hread: Reads gs r l.val:=⟨g_r,hgr,by rcases hgr_in with h|h <;> rw[h] <;> simp[e]⟩
    have:=hul r hread;omega
   set Cm0: Circuit:=⟨rdel (n' + 1) r u gs,rd (n' + 1) r u C.output⟩;set Cs0: Circuit:=⟨rdel (n' + 1) jl 0 Cm0.gates,rd (n' + 1) jl 0 Cm0.output⟩
   have hlm: Cm0.gates.length=gs.length - 1:=by
    have:=rdel_length (n' + 1) r u gs hr_len;simp[Cm0];omega
   have hlen_sub: Cs0.gates.length=gs.length - 2:=by
    have:=rdel_length (n' + 1) jl 0 Cm0.gates (by omega);simp[Cs0] at this ⊢;omega
   have hcl_mid: CL (n' + 1) Cm0.gates:=rdel_clean (n' + 1) r u gs hcl_norm hr_len hu;have hcl_sub: CL (n' + 1) Cs0.gates:=rdel_clean (n' + 1) jl 0 Cm0.gates hcl_mid (by omega) (by omega)
   have hsub_fan: FanInTwo Cs0:=by
    intro g hg;obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    rcases hcl_sub j _ (List.getElem?_eq_getElem hj) with ⟨hop,_,_,hin⟩ | ⟨hop|hop,_,_,_,_,hin⟩
    ·exact ⟨by simp[hop],by simp[hin]⟩
    ·exact ⟨by simp[hop],by simp[hin]⟩
    ·exact ⟨by simp[hop],by simp[hin]⟩
   have hsub_no_l: ∀ g∈Cs0.gates,l.val∉g.inputs:=by
    intro g hg hm;obtain ⟨j',hj',rfl⟩:=List.getElem_of_mem hg
    have hgat_eq: Cs0.gates[j']=gateAt Cs0 j' := by simp[gateAt,List.getD,hj']
    rw[hgat_eq] at hm
    have hj'_lt: j' < Cn0.gates.length - 2:=by simp[Cn0];omega
    have hlif:=r2l Cn0 hcl_norm hrb_norm hjr hr_len hu j' hj'_lt;rw[hlif.2] at hm;obtain ⟨a,ha,hea⟩:=lmm.mp hm;have hlt_C: li2 jl r j' < gs.length:=li2lt hjr hr_len (by omega)
    have ha_ne_jl: a ≠ n' + 1+jl:=fun e =>
     li2nr jl r j' (hur' _ hlt_C (e ▸ ha))
    have ha_eq: a=l.val:=by
     unfold rd at hea;split_ifs at hea <;> have := l.isLt <;> omega
    have heq:=hul (li2 jl r j') ⟨gateAt Cn0 (li2 jl r j'),
     by simp[Cn0,gateAt,List.getD,hlt_C],ha_eq ▸ ha⟩
    exact li2nj jl r j' hjr heq
   have hsub_out_ne_l: Cs0.output≠l.val:=by
    change rd (n' + 1) jl 0 (rd (n' + 1) r u C.output)≠l.val;unfold rd;split_ifs with h1 h2 h3 h4 <;> have := l.isLt <;> omega
   have hC_eq_of_noNot: (∀ j' < Cs0.gates.length,(gateAt Cs0 j').op≠GateOp.not) →
     g_l.op≠GateOp.not → g_r.op≠GateOp.not→Cn0=C:=by
    intro hnn_sub hnn_l hnn_r
    have hnoNot_norm: ∀ j < gs.length,(gateAt Cn0 j).op≠GateOp.not:=by
     intro j hj
     by_cases hje: j=jl
     ·rw[hje,hgat_jl];exact hnn_l
     ·by_cases hre: j=r
      ·rw[hre,hgat_r];exact hnn_r
      ·obtain ⟨j',hj',rfl⟩:=li2s hjr hr_len hj hje hre;have hlif:=r2l Cn0 hcl_norm hrb_norm hjr hr_len hu j' (by omega);rw[←hlif.1];exact hnn_sub j' (by omega)
    have hgates_eq: gs=C.gates:=by
     apply List.ext_getElem (by simp[gs]);intro j h1 h2;have hnn:=hnoNot_norm j h1
     have hgat: gateAt Cn0 j=gs[j]:=by simp[Cn0,gateAt,List.getD,h1]
     rw[hgat] at hnn;simp only[gs,List.getElem_map] at hnn ⊢
     rcases hcg: C.gates[j] with ⟨op,ins⟩;rw[hcg] at hnn
     cases op <;> simp[ng0] at hnn ⊢
    cases C;simp[Cn0,hgates_eq]
   rcases hop_cases with ⟨hgl_op,hgr_op⟩ | ⟨hgl_op,hgr_op⟩
   ·
    have hsub_cf: circuitFun (n' + 1) Cs0=graphFun K2 (insert p A):=by
     funext x;change vl Cs0.gates x Cs0.output=graphFun K2 (insert p A) x
     rw[←gfK2 hA hl hp hK2 x];rw[←vluu Cs0.gates Cs0.output l hsub_no_l hsub_out_ne_l x true]
     have hru: vl gs (Function.update x l true) (n' + 1+r)=vl gs (Function.update x l true) u:=by
      have h1: vl gs (Function.update x l true) (n' + 1+jl)=true:=by
       rw[vlg gs hcl_norm _ jl g_l hgl,hgl_op]
       rcases hgl_in with h|h <;> rw[h] <;> simp[GateOp.eval,vli gs _ l.val l.isLt]
      rw[vlg gs hcl_norm _ r g_r hgr,hgr_op]
      rcases hgr_in with h|h <;> rw[h] <;> simp[GateOp.eval,h1]
     have hmid_eq:=vlab hn Cn0 hcl_norm hrb_norm hjr hr_len hu hune ho_ne_jl hur'
      (Function.update x l true) hru
     have hout_eq: vl Cs0.gates (Function.update x l true) Cs0.output =
       vl gs (Function.update x l true) C.output:=by
      by_cases hor: C.output = n' + 1+r
      ·have hc: Cs0.output=rd (n' + 1) jl 0 u:=by change rd (n' + 1) jl 0 (rd (n' + 1) r u C.output)=_;rw[hor,rd_eq]
       have hu_lw: lw2 (n' + 1) jl r (rd (n' + 1) jl 0 u)=u:=by
        have h1:=lw1r (n' + 1) jl 0 u hune;unfold lw2;rw[h1];unfold lw1;split_ifs <;> omega
       conv_rhs => rw[hor,hru,←hu_lw]
       rw[hc];exact hmid_eq (rd (n' + 1) jl 0 u)
      ·exact (hmid_eq Cs0.output).trans (by dsimp[Cn0];rw[lw2r hjr ho_ne_jl hor])
     rw[hout_eq];exact hL.hev (Function.update x l true)
    have hsub_sz_eq: Cs0.size=C2_0.size:=by
     have hlb: C2_0.size ≤ Cs0.gates.length:=hM2_lb Cs0.size ⟨Cs0,hsub_fan,le_refl _,fun x => congrFun hsub_cf x⟩
     change Cs0.gates.length=C2_0.size;omega
    have hsub_min: IsMinimalCircuit (n' + 1) Cs0 :=
     ⟨hsub_fan,fun D hfD hcD => by rw[hsub_sz_eq];exact hM2_lb D.size ⟨D,hfD,le_refl _,fun x => congrFun (hcD.trans hsub_cf) x⟩⟩
    obtain ⟨d2,hv2⟩:=(hIH2 Cs0).mp ⟨hsub_min,hsub_cf⟩;have hC_eq: Cn0=C:=hC_eq_of_noNot (ncc_no_not hv2) (by rw[hgl_op];intro h;cases h) (by rw[hgr_op];intro h;cases h)
    have htK2: ∀ T: Finset (Fin (n' + 1)),K.IsVertexCover (T: Set (Fin (n' + 1))) → d2.cover.card+1 ≤ T.card:=by
     intro T hT;have hc: d2.cover.card=T2.card:=le_antisymm (hv2.2.1.2 T2 hT2.1) (hT2.2 d2.cover hv2.2.1.1);have hle:=hT0.2 T hT;omega
    rw[←hC_eq]
    exact nlB1 hn hA hl hql hp hK2 Cn0 hcl_norm hrb_norm
     (by rw[hC_eq];exact hcf) hjr hr_len hw_l hwne hu hune ho_ne_jl
     (by rw[hgat_jl,hgl_op]) (by rw[hgat_jl];exact hgl_in)
     (by rw[hgat_r,hgr_op]) (by rw[hgat_r];exact hgr_in)
     hur' hv2 htK2
   ·
    have hsub_cf: circuitFun (n' + 1) Cs0=graphFun K1 A:=by
     funext x;change vl Cs0.gates x Cs0.output=graphFun K1 A x
     rw[gfK1 hA hl hK1 x];rw[←vluu Cs0.gates Cs0.output l hsub_no_l hsub_out_ne_l x false]
     have hru: vl gs (Function.update x l false) (n' + 1+r)=vl gs (Function.update x l false) u:=by
      have h1: vl gs (Function.update x l false) (n' + 1+jl)=false:=by
       rw[vlg gs hcl_norm _ jl g_l hgl,hgl_op]
       rcases hgl_in with h|h <;> rw[h] <;> simp[GateOp.eval,vli gs _ l.val l.isLt]
      rw[vlg gs hcl_norm _ r g_r hgr,hgr_op]
      rcases hgr_in with h|h <;> rw[h] <;> simp[GateOp.eval,h1]
     have hmid_eq:=vlab hn Cn0 hcl_norm hrb_norm hjr hr_len hu hune ho_ne_jl hur'
      (Function.update x l false) hru
     have hout_eq: vl Cs0.gates (Function.update x l false) Cs0.output =
       vl gs (Function.update x l false) C.output:=by
      by_cases hor: C.output = n' + 1+r
      ·have hc: Cs0.output=rd (n' + 1) jl 0 u:=by change rd (n' + 1) jl 0 (rd (n' + 1) r u C.output)=_;rw[hor,rd_eq]
       have hu_lw: lw2 (n' + 1) jl r (rd (n' + 1) jl 0 u)=u:=by
        have h1:=lw1r (n' + 1) jl 0 u hune;unfold lw2;rw[h1];unfold lw1;split_ifs <;> omega
       conv_rhs => rw[hor,hru,←hu_lw]
       rw[hc];exact hmid_eq (rd (n' + 1) jl 0 u)
      ·exact (hmid_eq Cs0.output).trans (by dsimp[Cn0];rw[lw2r hjr ho_ne_jl hor])
     rw[hout_eq];exact hL.hev (Function.update x l false)
    have hsub_lb: C1_0.size ≤ Cs0.gates.length:=hM1_lb Cs0.size ⟨Cs0,hsub_fan,le_refl _,fun x => congrFun hsub_cf x⟩
    have hsub_sz_eq: Cs0.size=C1_0.size:=by change Cs0.gates.length=C1_0.size;omega
    have htau_K1_eq: T0.card=T1.card+1:=by dsimp only[NK] at hNK_eq_M2 hNK_le_M1 hC_le_NK;omega
    have hsub_min: IsMinimalCircuit (n' + 1) Cs0 :=
     ⟨hsub_fan,fun D hfD hcD => by rw[hsub_sz_eq];exact hM1_lb D.size ⟨D,hfD,le_refl _,fun x => congrFun (hcD.trans hsub_cf) x⟩⟩
    obtain ⟨d1,hv1⟩:=(hIH1 Cs0).mp ⟨hsub_min,hsub_cf⟩;have hC_eq: Cn0=C:=hC_eq_of_noNot (ncc_no_not hv1) (by rw[hgl_op];intro h;cases h) (by rw[hgr_op];intro h;cases h)
    have htK1: ∀ T: Finset (Fin (n' + 1)),K.IsVertexCover (T: Set (Fin (n' + 1))) → d1.cover.card+1 ≤ T.card:=by
     intro T hT;have hc: d1.cover.card=T1.card:=le_antisymm (hv1.2.1.2 T1 hT1.1) (hT1.2 d1.cover hv1.2.1.1);have hle:=hT0.2 T hT;omega
    rw[←hC_eq]
    exact nlB2 hn hA hl hql hp hK1 Cn0 hcl_norm hrb_norm
     (by rw[hC_eq];exact hcf) hjr hr_len hw_l hwne hu hune hu_ne_l ho_ne_jl
     (by rw[hgat_jl,hgl_op]) (by rw[hgat_jl];exact hgl_in)
     (by rw[hgat_r,hgr_op]) (by rw[hgat_r];exact hgr_in)
     hur' hv1 htK1
  intro C
  constructor
  ·rintro ⟨hmin,hcf⟩;exact hfwd C hmin hcf
  ·rintro ⟨d,hv⟩
   have hcf: circuitFun (n' + 1) C=graphFun K A:=ncc_eval hv
   refine ⟨⟨ncc_fanInTwo hv,fun D hfD hcD => ?_⟩,hcf⟩
   obtain ⟨C_min,hCmin_min,hCmin_cf⟩:=mciEx (graphFun K A);obtain ⟨d_min,hv_min⟩:=hfwd C_min hCmin_min hCmin_cf;have hsz1:=ncc_size hv
   have hsz2:=ncc_size hv_min
   have hc1: d.cover.card=T0.card:=le_antisymm (hv.2.1.2 T0 hT0.1) (hT0.2 d.cover hv.2.1.1);have hc2: d_min.cover.card=T0.card:=le_antisymm (hv_min.2.1.2 T0 hT0.1) (hT0.2 d_min.cover hv_min.2.1.1);have hle:=hCmin_min.2 D hfD ((hcD.trans hcf).trans hCmin_cf.symm);omega
end L540.Main
end PEqualNP.Outside.L_meta_540_aux

theorem PEqualNP.Outside.L_meta_540 :
    ∀ (n : ℕ) (K K1 K2 : SimpleGraph (Fin n)) [DecidableRel K.Adj] [DecidableRel K1.Adj] [DecidableRel K2.Adj] (A : Finset (Fin n)) (l p q : Fin n), ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 3 ≤ k → Nonempty (K.Adj ↪r (PEqualNP.Library.Subdivision.subdiv k H).Adj) → (∀ a ∈ A, ∀ v : Fin n, ¬ K.Adj a v) → (∀ v : Fin n, K.Adj l v ↔ v = p) → q ≠ l → (∀ v : Fin n, K.Adj p v ↔ v = l ∨ v = q) → (∀ u v : Fin n, K1.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ v ≠ l) → (∀ u v : Fin n, K2.Adj u v ↔ K.Adj u v ∧ u ≠ l ∧ u ≠ p ∧ v ≠ l ∧ v ≠ p) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K1 A) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K1 A C) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K2 (insert p A)) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K2 (insert p A) C) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun K A) ↔ PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K A C) :=
  fun n K K1 K2 _ _ _ A l p q k m H hk hemb hA hl hql hp hK1 hK2 hIH1 hIH2 =>
    PEqualNP.Outside.L_meta_540_aux.L540.Main.L_meta_540_main n K K1 K2 A l p q k m H hk hemb hA hl hql hp hK1 hK2 hIH1 hIH2
