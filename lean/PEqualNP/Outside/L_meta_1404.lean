import Mathlib.Data.Set.Defs
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
namespace PEqualNP.Outside.L_meta_1404_aux
open Nat (land lor shiftRight shiftLeft)
abbrev nB:=Nat.ble
abbrev nE:=Nat.beq
abbrev bF:=Bool.false_eq_true
abbrev bA:=Bool.and_eq_true
abbrev bO:=Bool.or_eq_true
abbrev bT:=@Bool.cond_true
abbrev bC:=@Bool.cond_false
abbrev bTA:=Bool.true_and
abbrev bFA:=Bool.false_and
abbrev bFO:=Bool.false_or
abbrev bOF:=Bool.or_false
abbrev nA {a b c d:Nat}:=@Nat.add_le_add a b c d
abbrev nS {a b:Nat}:=@Nat.sub_le_sub_right a b
abbrev nP {a:Nat} (ha:0<a) {m n:Nat}:=@Nat.pow_le_pow_right a ha m n
abbrev nT {a n:Nat}:=@Nat.testBit_lt_two_pow a n
abbrev n2:=Nat.two_pow_pos
abbrev nM:=Nat.mod_lt
abbrev nE2 {a b:Nat}:=@Nat.eq_of_testBit_eq a b
abbrev lT {a b c:Nat}:=@le_trans Nat _ a b c
abbrev lR (a:Nat):=@le_refl Nat _ a
abbrev mL (a b:Nat):=@min_le_left Nat _ a b
abbrev mR (a b:Nat):=@min_le_right Nat _ a b
abbrev xL {a b c:Nat}:=@max_le Nat _ a b c
abbrev lM {a b c:Nat}:=@le_min Nat _ a b c
abbrev nQ {a b:Nat}:=@Nat.mod_eq_of_lt a b
abbrev bL {n m:Nat}:=@Nat.ble_eq n m
abbrev bQ {n m:Nat}:=@Nat.eq_of_beq_eq_true n m
abbrev nO {a b n:Nat}:=@Nat.or_lt_two_pow a b n
abbrev nW:=Nat.and_two_pow_sub_one_eq_mod
abbrev nL:=Nat.shiftLeft_eq
abbrev nI:=Nat.testBit_or
abbrev nK:=Nat.testBit_two_pow_sub_one
abbrev nC:=Nat.mul_comm
abbrev nD:=Nat.shiftRight_eq_div_pow
abbrev bX:=Bool.and_false
abbrev bY:=Bool.and_comm
abbrev bZ:=Bool.not_false
abbrev bP:=Bool.or_comm
abbrev bN:=Bool.not_true
abbrev lO {a b c:Nat}:=@lt_of_le_of_lt Nat _ a b c
abbrev lQ {a b c:Nat}:=@lt_of_lt_of_le Nat _ a b c
abbrev lZ (a b:Nat):=@le_total Nat _ a b
abbrev oR {a b:Prop}:=@Or.inr a b
abbrev oL {a b:Prop}:=@Or.inl a b
abbrev nG {n m:Nat}:=@Nat.blt_eq n m
abbrev fE {n:Nat} {a b:Fin n}:=@Fin.ext n a b
abbrev nR {a b:Nat}:=@Nat.and_le_right a b
abbrev nU {i j:Nat}:=@Nat.testBit_shiftRight i j
abbrev nV:=Nat.testBit_and
abbrev nX {i j:Nat}:=@Nat.testBit_shiftLeft i j
abbrev nY {m n:Nat}:=@Nat.testBit_two_pow m n
abbrev nJ {x i:Nat}:=@Nat.testBit_eq_decide_div_mod_eq x i
abbrev nF {a b c:Nat}:=@Nat.sub_le_of_le_add a b c
abbrev nZ:=Nat.add_zero
abbrev bU:=Bool.and_true
abbrev nH {a b:Nat}:=@Nat.div_eq_of_lt a b
abbrev n1:=Nat.one_mul
abbrev n0:=Nat.pow_add
abbrev n3:=Nat.div_le_self
abbrev n4:=Nat.zero_testBit
abbrev n5 {a b:Nat}:=@Nat.and_le_left a b
abbrev dT:=@decide_true
abbrev dE {p:Prop} [Decidable p]:=@decide_eq_true_eq p _
def av (a b:Nat):Nat:=a - (a - b)
def aa (a b:Nat):Nat:=b+(a - b)
lemma aG (a b:Nat):av a b=min a b:=by unfold av;omega
lemma aP (a b:Nat):aa a b=max a b:=by unfold aa;omega
def o (w i a:Nat):Nat:=(a >>> (w*i))&&&((1 <<< w) - 1)
lemma U (w i a k:Nat) :
  (o w i a).testBit k=(decide (k<w)&&a.testBit (w*i+k)):=by
 unfold o;rw[nV,nU]
 have b:((1 <<< w) - 1).testBit k=decide (k<w):=by
  rw[nL,n1,nK]
 rw[b,bY]
lemma aY (w c e a:Nat) (hc:c<3) :
   o w c (o (3*w) e a)=o w (3*e+c) a:=by
 apply nE2;intro k;rw[U,U,U]
 by_cases hk:k<w
 . have d:w*c+k<3*w:=by nlinarith
   have b:3*w*e+(w*c+k)=w*(3*e+c)+k:=by ring
   simp[hk,d,b]
 . simp[hk]
lemma eL (w d c k:Nat) (j:d<2^w) :
   (d+c*2^w).testBit k=if k<w then d.testBit k else c.testBit (k - w):=by
 by_cases hk:k<w
 . simp only[hk,↓reduceIte,nJ]
   have a:2^w=2^k*2^(w - k):=by rw[<- n0,Nat.add_sub_cancel' (Nat.le_of_lt hk)]
   have b:(d+c*2^w)/2^k=d/2^k+c*2^(w - k):=by
     have:d+c*2^w=d+2^k*(c*2^(w - k)):=by rw[a];ring
     rw[this,Nat.add_mul_div_left _ _ (n2 k)]
   have h:(d/2^k+c*2^(w - k)) % 2=(d/2^k) % 2:=by
     have h2:2 ∣ 2^(w - k):=by
       cases hm:w - k with
       | zero=>omega
       | succ m=>rw[Nat.pow_succ];exact dvd_mul_left 2 _
     rcases dvd_mul_of_dvd_right h2 c with ⟨t,ht⟩;rw[ht];omega
   rw[b,h]
 . simp only[hk,↓reduceIte,nJ];have i:w<=k:=Nat.le_of_not_lt hk
   have a:2^k=2^w*2^(k - w):=by rw[<- n0,Nat.add_sub_cancel' i]
   rw[a,<-Nat.div_div_eq_div_mul]
   have b:(d+c*2^w)/2^w=c:=by
     rw[Nat.add_mul_div_right _ _ (n2 w),nH j,Nat.zero_add]
   rw[b]
lemma dD (w a:Nat):o w 0 a=a % 2^w:=by
 unfold o;simp[nL]
lemma aS (w i a:Nat):o w i a=(a/2^(w*i)) % 2^w:=by
 unfold o;rw[nD,nL,n1,nW]
lemma bB (w n a:Nat) (b:a<2^(w*(n+1))):o w n a=a/2^(w*n):=by
 rw[aS,nQ]
 rw[Nat.div_lt_iff_lt_mul (n2 _),<-n0,show w+w*n=w*(n+1) by ring]
 exact b
lemma gW (W n x y:Nat) (l:0<W) (c:x<2^(W*n)) (b:y<2^(W*n))
   (h:∀ i<n,o W i x=o W i y):x=y:=by
 apply nE2;intro k
 by_cases hk:k<W*n
 . have j:k/W<n:=Nat.div_lt_of_lt_mul hk;have d:k % W<W:=nM k l;have a:=congrArg (fun z=>z.testBit (k % W)) (h (k/W) j);rw[U,U] at a;simp only[d,dT,bTA,Nat.div_add_mod k W] at a;exact a
 . rw[nT (lQ c (nP (by decide:0<2) (by omega:W*n<=k))),
       nT (lQ b (nP (by decide:0<2) (by omega:W*n<=k)))]
lemma ce (w a b:Nat) (c:a<2^w):a+b*2^w=a|||(b <<< w):=by
 apply nE2;intro k;rw[eL w a b k c,nI,nX]
 by_cases hk:k<w
 . simp[hk,show ¬ w<=k by omega]
 . simp[hk,show w<=k by omega,nT (lQ c (nP (by decide:0<2) (by omega:w<=k)))]
def ke (W r w:Nat):Nat:=
 if nE r 0 then w else ((w <<< (W*r))|||(w >>> (W*(5 - r))))&&&((1 <<< (5*W)) - 1)
def hP (W w:Nat):Nat:=
 let m:=(1 <<< W) - 1
 ((w&&&m) <<< (4*W))|||(((w >>> W)&&&m) <<< (3*W))|||(((w >>> (2*W))&&&m) <<< (2*W))|||
 (((w >>> (3*W))&&&m) <<< W)|||((w >>> (4*W))&&&m)
def jU (W w:Nat):Nat:=
 let m:=(1 <<< W) - 1
 ((w&&&m) <<< (3*W))|||(((w >>> W)&&&m) <<< (2*W))|||(((w >>> (2*W))&&&m) <<< W)|||
 ((w >>> (3*W))&&&m)|||(((w >>> (4*W))&&&m) <<< (4*W))
lemma lF (w s W d k:Nat) :
   (((w >>> s)&&&((1 <<< W) - 1)) <<< d).testBit k =
   (decide (d<=k)&&decide (k<d+W)&&w.testBit (s+(k - d))):=by
 rw[nX,nV,nU]
 have a:((1 <<< W) - 1).testBit (k - d)=decide (k - d<W):=by
   rw[nL,n1,nK]
 rw[a]
 by_cases h1:d<=k
 . have h2:(k - d<W) ↔ (k<d+W):=by omega
   simp[h1,h2,bY]
 . simp[h1]
lemma l6 (w W d k:Nat) :
  ((w&&&((1 <<< W) - 1)) <<< d).testBit k =
  (decide (d<=k)&&decide (k<d+W)&&w.testBit (k - d)):=by
 have:=lF w 0 W d k
 simpa using this
lemma cl (w s W d N:Nat) (h:d+W<=N) :
  (((w >>> s)&&&((1 <<< W) - 1)) <<< d)<2^N:=by
 rw[nL]
 have c:(w >>> s)&&&((1 <<< W) - 1)<2^W:=by
  rw[nL,n1,nW];exact nM _ (n2 W)
 have b:((w >>> s)&&&((1 <<< W) - 1))*2^d<2^W*2^d:=
  Nat.mul_lt_mul_of_pos_right c (n2 d)
 have a:2^W*2^d<=2^N:=by
  rw[<- n0];exact nP (by omega) (by omega)
 exact lQ b a
lemma dt (W r w:Nat) (a:w<2^(5*W)):ke W r w<2^(5*W):=by
 unfold ke;split_ifs
 . exact a
 . have h1:(1 <<< (5*W))=2^(5*W):=by rw[nL,n1]
   rw[h1,nW];exact nM _ (n2 _)
lemma cP (W w:Nat):hP W w<2^(5*W):=by
 unfold hP
 have h0:((w&&&((1 <<< W) - 1)) <<< (4*W))<2^(5*W):=by
  simpa using cl w 0 W (4*W) (5*W) (by omega)
 have h1:=cl w W W (3*W) (5*W) (by omega);have h2:=cl w (2*W) W (2*W) (5*W) (by omega);have h3:=cl w (3*W) W W (5*W) (by omega)
 have h4:((w >>> (4*W))&&&((1 <<< W) - 1))<2^(5*W):=by
  simpa using cl w (4*W) W 0 (5*W) (by omega)
 exact nO (nO (nO (nO h0 h1) h2) h3) h4
lemma gE (W w:Nat):jU W w<2^(5*W):=by
 unfold jU
 have h0:((w&&&((1 <<< W) - 1)) <<< (3*W))<2^(5*W):=by
  simpa using cl w 0 W (3*W) (5*W) (by omega)
 have h1:=cl w W W (2*W) (5*W) (by omega);have h2:=cl w (2*W) W W (5*W) (by omega)
 have h3:((w >>> (3*W))&&&((1 <<< W) - 1))<2^(5*W):=by
  simpa using cl w (3*W) W 0 (5*W) (by omega)
 have h4:=cl w (4*W) W (4*W) (5*W) (by omega);exact nO (nO (nO (nO h0 h1) h2) h3) h4
lemma tv (W r w k:Nat) (hr:r<5) (c:w<2^(5*W)) (h:k<5*W) :
   (ke W r w).testBit k=w.testBit (if k<W*r then k+W*(5 - r) else k - W*r):=by
 unfold ke
 cases r with
 | zero=>simp
 | succ r'=>
   have a:nE (r'+1) 0=false:=rfl
   simp only[a,bF,↓reduceIte,nV,nI,
     nX,nU,ge_iff_le]
   have d:((1 <<< (5*W)) - 1).testBit k=true:=by
     rw[nL,n1,nK];simp[h]
   rw[d,bU]
   by_cases hlt:k<W*(r'+1)
   . have h1:decide (W*(r'+1)<=k)=false:=by simp;omega
     simp only[hlt,↓reduceIte,h1,bFA,bFO];congr 1;omega
   . have h1:decide (W*(r'+1)<=k)=true:=by simp;omega
     have b:5*W<=W*(5 - (r'+1))+k:=by
       have:W*(5 - (r'+1))+W*(r'+1)=5*W:=by
         rw[<- Nat.mul_add];rw[show 5 - (r'+1)+(r'+1)=5 by omega,nC]
       omega
     have h2:w.testBit (W*(5 - (r'+1))+k)=false:=
       nT (lQ c (nP (by omega) b))
     simp only[hlt,↓reduceIte,h1,bTA,h2,bOF]
lemma ee (W r w i:Nat) (h:r<5) (hi:i<5) (d:w<2^(5*W)) :
   o W ((i+r) % 5) (ke W r w)=o W i w:=by
 apply nE2;intro k;rw[U,U]
 by_cases hk:k<W
 . simp only[hk,dT,bTA]
   have b:W*((i+r) % 5)+k<5*W:=by
     have:(i+r) % 5<=4:=by omega
     nlinarith
   rw[tv W r w _ h d b];congr 1
   by_cases hsum:i+r<5
   . rw[nQ hsum];have h1:W*(i+r)=W*i+W*r:=Nat.mul_add W i r
     have a:¬ W*(i+r)+k<W*r:=by omega
     simp only[a,↓reduceIte];omega
   . rw[show (i+r) % 5=i+r - 5 by omega]
     have c:W*(i+r - 5)+k<W*r:=by
       have:i+r - 5+1<=r:=by omega
       nlinarith
     simp only[c,↓reduceIte]
     have h1:W*(i+r - 5)+k+W*(5 - r)=W*((i+r - 5)+(5 - r))+k:=by ring
     rw[h1,show i+r - 5+(5 - r)=i by omega]
 . simp[hk]
lemma lL (W w i:Nat) (hi:i<5) :
   o W (4 - i) (hP W w)=o W i w:=by
 apply nE2;intro k;rw[U,U]
 by_cases hk:k<W
 . simp only[hk,dT,bTA];unfold hP;simp only[nI,l6,nV,nU]
   have b:((1 <<< W) - 1).testBit (W*(4 - i)+k)=decide (W*(4 - i)+k<W):=by
     rw[nL,n1,nK]
   rw[b]
   have a:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
   rcases a with rfl|rfl|rfl|rfl|rfl
   . simp only[show decide (4*W<=W*(4 - 0)+k)=true by simp;omega,
       show decide (W*(4 - 0)+k<4*W+W)=true by simp;omega,
       show decide (W*(4 - 0)+k<3*W+W)=false by simp;omega,
       show decide (W*(4 - 0)+k<2*W+W)=false by simp;omega,
       show decide (W*(4 - 0)+k<W+W)=false by simp;omega,
       show decide (W*(4 - 0)+k<W)=false by simp;omega,
       bTA,bX,bFA,bOF]
     congr 1;omega
   . simp only[show decide (4*W<=W*(4 - 1)+k)=false by simp;omega,
       show decide (3*W<=W*(4 - 1)+k)=true by simp;omega,
       show decide (W*(4 - 1)+k<3*W+W)=true by simp;omega,
       show decide (W*(4 - 1)+k<2*W+W)=false by simp;omega,
       show decide (W*(4 - 1)+k<W+W)=false by simp;omega,
       show decide (W*(4 - 1)+k<W)=false by simp;omega,
       bTA,bFA,bX,bFO,bOF]
     congr 1;omega
   . simp only[show decide (4*W<=W*(4 - 2)+k)=false by simp;omega,
       show decide (3*W<=W*(4 - 2)+k)=false by simp;omega,
       show decide (2*W<=W*(4 - 2)+k)=true by simp;omega,
       show decide (W*(4 - 2)+k<2*W+W)=true by simp;omega,
       show decide (W*(4 - 2)+k<W+W)=false by simp;omega,
       show decide (W*(4 - 2)+k<W)=false by simp;omega,
       bTA,bFA,bX,bFO,bOF]
     congr 1;omega
   . simp only[show decide (4*W<=W*(4 - 3)+k)=false by simp;omega,
       show decide (3*W<=W*(4 - 3)+k)=false by simp;omega,
       show decide (2*W<=W*(4 - 3)+k)=false by simp;omega,
       show decide (W<=W*(4 - 3)+k)=true by simp,
       show decide (W*(4 - 3)+k<W+W)=true by simp;omega,
       show decide (W*(4 - 3)+k<W)=false by simp,
       bTA,bFA,bX,bFO,bOF]
     congr 1;omega
   . simp only[show decide (4*W<=W*(4 - 4)+k)=false by simp;omega,
       show decide (3*W<=W*(4 - 4)+k)=false by simp;omega,
       show decide (2*W<=W*(4 - 4)+k)=false by simp;omega,
       show decide (W<=W*(4 - 4)+k)=false by simp;omega,
       show decide (W*(4 - 4)+k<W)=true by simp;omega,
       bFA,bU,bFO]
     congr 1;omega
 . simp[hk]
lemma qD (W w i:Nat) (hi:i<5) :
   o W ((8 - i) % 5) (jU W w)=o W i w:=by
 apply nE2;intro k;rw[U,U]
 by_cases hk:k<W
 . simp only[hk,dT,bTA];unfold jU;simp only[nI,l6,nV,nU]
   have b:((1 <<< W) - 1).testBit (W*((8 - i) % 5)+k)=decide (W*((8 - i) % 5)+k<W):=by
     rw[nL,n1,nK]
   rw[b]
   have a:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
   rcases a with rfl|rfl|rfl|rfl|rfl
   . simp only[show (8 - 0) % 5=3 by decide,
       show decide (3*W<=W*3+k)=true by simp;omega,
       show decide (W*3+k<3*W+W)=true by simp;omega,
       show decide (W*3+k<2*W+W)=false by simp;omega,
       show decide (W*3+k<W+W)=false by simp;omega,
       show decide (W*3+k<W)=false by simp;omega,
       show decide (4*W<=W*3+k)=false by simp;omega,
       bTA,bFA,bX,bOF]
     congr 1;omega
   . simp only[show (8 - 1) % 5=2 by decide,
       show decide (3*W<=W*2+k)=false by simp;omega,
       show decide (2*W<=W*2+k)=true by simp;omega,
       show decide (W*2+k<2*W+W)=true by simp;omega,
       show decide (W*2+k<W+W)=false by simp;omega,
       show decide (W*2+k<W)=false by simp;omega,
       show decide (4*W<=W*2+k)=false by simp;omega,
       bTA,bFA,bX,bFO,bOF]
     congr 1;omega
   . simp only[show (8 - 2) % 5=1 by decide,
       show decide (3*W<=W*1+k)=false by simp;omega,
       show decide (2*W<=W*1+k)=false by simp;omega,
       show decide (W<=W*1+k)=true by simp,
       show decide (W*1+k<W+W)=true by simp;omega,
       show decide (W*1+k<W)=false by simp,
       show decide (4*W<=W*1+k)=false by simp;omega,
       bTA,bFA,bX,bFO,bOF]
     congr 1;omega
   . simp only[show (8 - 3) % 5=0 by decide,
       show decide (3*W<=W*0+k)=false by simp;omega,
       show decide (2*W<=W*0+k)=false by simp;omega,
       show decide (W<=W*0+k)=false by simp;omega,
       show decide (W*0+k<W)=true by simp;omega,
       show decide (4*W<=W*0+k)=false by simp;omega,
       bFA,bU,bFO,bOF]
     congr 1;omega
   . simp only[show (8 - 4) % 5=4 by decide,
       show decide (W*4+k<3*W+W)=false by simp;omega,
       show decide (W*4+k<2*W+W)=false by simp;omega,
       show decide (W*4+k<W+W)=false by simp;omega,
       show decide (W*4+k<W)=false by simp;omega,
       show decide (4*W<=W*4+k)=true by simp;omega,
       show decide (W*4+k<4*W+W)=true by simp;omega,
       bTA,bFA,bX,bFO]
     congr 1;omega
 . simp[hk]
lemma bj (w i a:Nat):o w i (a/2^w)=o w (i+1) a:=by
 unfold o
 have b:a >>> (w*(i+1))=(a/2^w) >>> (w*i):=by
  simp only[nD,Nat.mul_add,Nat.mul_one,n0,
   Nat.div_div_eq_div_mul,nC (2^(w*i)) (2^w)]
 rw[b]
lemma cN (w n a:Nat) (b:a<2^(w*(n+1))):a/2^w<2^(w*n):=by
 rw[Nat.div_lt_iff_lt_mul (n2 w)]
 have h:2^(w*n)*2^w=2^(w*(n+1)):=by
  rw[<- n0,show w*n+w=w*(n+1) by ring]
 exact lt_of_lt_of_eq b h.symm
lemma dQ (w i a b:Nat):o w i (lor a b)=lor (o w i a) (o w i b):=by
 apply nE2;intro k;change (o w i (a|||b)).testBit k=(o w i a|||o w i b).testBit k;simp only[U,nI];cases decide (k<w) <;> simp
lemma bm (w i a b:Nat):o w i (land a b)=land (o w i a) (o w i b):=by
 apply nE2;intro k;change (o w i (a&&&b)).testBit k=(o w i a&&&o w i b).testBit k;simp only[U,nV];cases decide (k<w) <;> simp
lemma ap (w:Nat):∀ (n a b:Nat),
   (∀ i<n,o w i a+o w i b<2^w)->a<2^(w*n)->b<2^(w*n)->
   (a+b<2^(w*n))/\(∀ i<n,o w i (a+b)=o w i a+o w i b):=by
 intro n;induction n with
 | zero=>intro a b _ ha hb;simp only[Nat.mul_zero,Nat.pow_zero] at ha hb ⊢;exact ⟨by omega,fun _ hi=>by omega⟩
 | succ n ih=>
   intro a b hsum ha hb
   have h0:a % 2^w+b % 2^w<2^w:=by simpa [dD] using hsum 0 (Nat.zero_lt_succ n)
   have h1:=ih (a/2^w) (b/2^w)
     (fun i hi=>by rw[bj,bj];exact hsum (i+1) (Nat.succ_lt_succ hi))
     (cN w n a ha) (cN w n b hb)
   have c:a+b=(a % 2^w+b % 2^w)+2^w*(a/2^w+b/2^w):=by
     have hae:=Nat.mod_add_div a (2^w);have hbe:=Nat.mod_add_div b (2^w);linarith
   have k:(a+b)/2^w=a/2^w+b/2^w:=by
     rw[c,Nat.add_mul_div_left _ _ (n2 w),nH h0,Nat.zero_add]
   have h:(a+b) % 2^w=a % 2^w+b % 2^w:=by
     rw[c,Nat.add_mul_mod_self_left,nQ h0]
   refine ⟨?_,fun i hi=>?_⟩
   . have d:2^(w*(n+1))=2^w*2^(w*n):=by rw[<- n0,show w+w*n=w*(n+1) by ring]
     have hle:2^w*(a/2^w+b/2^w+1)<=2^w*2^(w*n):=Nat.mul_le_mul_left _ h1.1;rw[d,c];linarith
   . cases i with
     | zero=>rw[dD,dD,dD,h]
     | succ j=>rw[<- bj,<-bj,<-bj,k];exact h1.2 j (Nat.lt_of_succ_lt_succ hi)
lemma ct (w:Nat):∀ (n a b:Nat),
  (∀ i<n,o w i b<=o w i a)->a<2^(w*n)->b<2^(w*n)->
  (a - b<2^(w*n))/\(∀ i<n,o w i (a - b)=o w i a - o w i b):=by
 intro n;induction n with
 | zero=>intro a b _ ha hb;simp only[Nat.mul_zero,Nat.pow_zero] at ha hb ⊢;exact ⟨by omega,fun _ hi=>by omega⟩
 | succ n ih=>
  intro a b hle ha hb
  have h0:b % 2^w<=a % 2^w:=by simpa [dD] using hle 0 (Nat.zero_lt_succ n)
  have h1:=ih (a/2^w) (b/2^w)
   (fun i hi=>by rw[bj,bj];exact hle (i+1) (Nat.succ_lt_succ hi))
   (cN w n a ha) (cN w n b hb)
  have m:b/2^w<=a/2^w:=by
   have r:∀ k a' b',(∀ i<k,o w i b'<=o w i a')->a'<2^(w*k)->b'<2^(w*k)->b'<=a':=by
    intro k;induction k with
    | zero=>intro a' b' _ ha' hb';simp only[Nat.mul_zero,Nat.pow_zero] at ha' hb';omega
    | succ k ihk=>
     intro a' b' hl' ha' hb'
     have l0:b' % 2^w<=a' % 2^w:=by simpa [dD] using hl' 0 (Nat.zero_lt_succ k)
     have t:=ihk (a'/2^w) (b'/2^w) (fun i hi=>by rw[bj,bj];exact hl' (i+1) (Nat.succ_lt_succ hi))
      (cN w k a' ha') (cN w k b' hb')
     have:=Nat.mod_add_div a' (2^w);have:=Nat.mod_add_div b' (2^w)
     have:=Nat.mul_le_mul_left (2^w) t;omega
   exact r n (a/2^w) (b/2^w)
    (fun i hi=>by rw[bj,bj];exact hle (i+1) (Nat.succ_lt_succ hi))
    (cN w n a ha) (cN w n b hb)
  have c:a - b=(a % 2^w - b % 2^w)+2^w*(a/2^w - b/2^w):=by
   have hae:=Nat.mod_add_div a (2^w);have hbe:=Nat.mod_add_div b (2^w);have hm:2^w*(b/2^w)<=2^w*(a/2^w):=Nat.mul_le_mul_left _ m;have hdm:2^w*(a/2^w - b/2^w)=2^w*(a/2^w) - 2^w*(b/2^w):=Nat.mul_sub_left_distrib _ _ _;omega
  have d:a % 2^w - b % 2^w<2^w:=lO (Nat.sub_le _ _) (nM _ (n2 w))
  have l:(a - b)/2^w=a/2^w - b/2^w:=by
   rw[c,Nat.add_mul_div_left _ _ (n2 w),nH d,Nat.zero_add]
  have h:(a - b) % 2^w=a % 2^w - b % 2^w:=by
   rw[c,Nat.add_mul_mod_self_left,nQ d]
  refine ⟨lO (Nat.sub_le a b) ha,fun i hi=>?_⟩
  cases i with
  | zero=>rw[dD,dD,dD,h]
  | succ j=>rw[<- bj,<-bj,<-bj,l];exact h1.2 j (Nat.lt_of_succ_lt_succ hi)
lemma iG (w s i a:Nat) (hs:s<=w) (h0:∀ k<s,(o w (i+1) a).testBit k=false) :
   o w i (shiftRight a s)=shiftRight (o w i a) s:=by
 apply nE2;intro k;change (o w i (a >>> s)).testBit k=((o w i a) >>> s).testBit k;rw[U,nU,nU,U]
 by_cases hk:k<w
 . simp only[hk,dT,bTA]
   by_cases b:s+k<w
   . simp only[b,dT,bTA];congr 1;omega
   . simp only[b,decide_false,bFA];have h1:=h0 (s+k - w) (by omega);rw[U] at h1
     have d:s+k - w<w:=by omega
     simp only[d,dT,bTA] at h1
     have c:s+(w*i+k)=w*(i+1)+(s+k - w):=by ring_nf;omega
     rw[c];exact h1
 . have b:¬ s+k<w:=by omega
   simp[hk,b]
lemma kg (w s i a:Nat) (hs:s<=w) (l:∀ j<i+1,o w j a<2^(w - s)) :
   o w i (shiftLeft a s)=shiftLeft (o w i a) s:=by
 apply nE2;intro k;change (o w i (a <<< s)).testBit k=((o w i a) <<< s).testBit k;rw[U,nX,nX,U]
 by_cases hk:k<w
 . simp only[hk,dT,bTA]
   by_cases hsk:s<=k
   . have c:k - s<w:=by omega
     have d:w*i+k - s=w*i+(k - s):=by omega
     simp[hsk,c,d,show s<=w*i+k by omega]
   . simp only[hsk,decide_false,bFA]
     cases i with
     | zero=>simp[show ¬ s<=k by omega]
     | succ j=>
       by_cases hle:s<=w*(j+1)+k
       . simp only[hle,dT,bTA]
         have d:w*(j+1)+k - s=w*j+(w+k - s):=by ring_nf;omega
         rw[d];have h:=l j (by omega)
         have b:(o w j a).testBit (w+k - s)=false:=
           nT (lQ h (nP (by omega) (by omega)))
         rw[U] at b
         simp only[show w+k - s<w by omega,dT,bTA] at b
         exact b
       . simp[hle]
 . simp only[hk,decide_false,bFA]
   by_cases hsk:s<=k
   . by_cases c:k - s<w
     . have h:=l i (by omega)
       have b:(o w i a).testBit (k - s)=false:=
         nT (lQ h (nP (by omega) (by omega)))
       rw[U] at b;simp only[c,dT,bTA] at b;simp[hsk,c,b]
     . simp[hsk,c]
   . simp[hsk]
lemma fS (s x:Nat) (i:x<2^s):lor x (2^s)=x+2^s:=by
 apply nE2;intro k;change (x|||2^s).testBit k=(x+2^s).testBit k;rw[nI,nY]
 by_cases hk:k<s
 . have b:s ≠ k:=by omega
   simp only[b,decide_false,bOF];rw[nJ,nJ]
   have c:2^s=2^k*2^(s - k):=by rw[<- n0,Nat.add_sub_cancel' (Nat.le_of_lt hk)]
   have h:(x+2^s)/2^k=x/2^k+2^(s - k):=by
     rw[c,Nat.add_mul_div_left _ _ (n2 k)]
   have h2:2 ∣ 2^(s - k):=by cases hm:s - k with|zero=>omega|succ m=>rw[Nat.pow_succ];exact dvd_mul_left 2 _
   rcases h2 with ⟨t,ht⟩;rw[h,ht,Nat.add_mul_mod_self_left]
 . by_cases hke:k=s
   . subst hke;have a:x.testBit k=false:=nT i;simp only[a,dT,bFO];rw[nJ,Nat.add_div_right _ (n2 k),nH i]
     decide
   . have b:s ≠ k:=by omega
     have a:x.testBit k=false:=nT (lQ i (nP (by omega) (by omega)))
     have d:x+2^s<2^k:=by
       have:2*2^s<=2^k:=by rw[<- Nat.pow_succ'];exact nP (by omega) (by omega)
       omega
     rw[a,nT d];simp[b]
lemma hR (s a b:Nat) (d:a<2^s) (hb:b<2^s) :
   land ((lor a (2^s)) - b) (2^s)=if b<=a then 2^s else 0:=by
 rw[fS s a d];apply nE2;intro k;change ((a+2^s - b)&&&2^s).testBit k=_;rw[nV,nY]
 split_ifs with hle
 . rw[nY]
   by_cases hk:s=k
   . subst hk;simp only[dT,bU];rw[nJ]
     have c:(a+2^s - b)/2^s=1:=by
       have h1:2^s<=a+2^s - b:=by omega
       have h2:a+2^s - b<2*2^s:=by omega
       rw[Nat.div_eq_of_lt_le (by omega) h2]
     rw[c];decide
   . simp[hk]
 . simp only[n4]
   by_cases hk:s=k
   . subst hk;simp only[dT,bU];exact nT (by omega)
   . simp[hk]
lemma mT (s a b:Nat) (l:a<2^s) (k:b<2^s) :
   let d:=land ((lor a (2^s)) - b) (2^s)
   let m:=d - shiftRight d s
   lor (land a m) (land b ((2^s - 1) - m))=max a b/\
   lor (land b m) (land a ((2^s - 1) - m))=min a b:=by
 dsimp only;rw[hR s a b l k]
 split_ifs with hle
 . have j:shiftRight (2^s) s=1:=by
     change (2^s) >>> s=1;rw[nD,Nat.div_self (n2 s)]
   rw[j,Nat.sub_self]
   have h:land a (2^s - 1)=a:=by
     change a&&&(2^s - 1)=a;rw[nW,nQ l]
   have c:land b (2^s - 1)=b:=by
     change b&&&(2^s - 1)=b;rw[nW,nQ k]
   have h0:∀ x,land x 0=0:=fun x=>Nat.and_zero x;have i:∀ x,lor x 0=x:=fun x=>Nat.or_zero x;rw[h,c,h0,h0,i,i];exact ⟨(max_eq_left hle).symm,(min_eq_right hle).symm⟩
 . have j:shiftRight 0 s=0:=by change 0 >>> s=0;rw[nD];simp
   rw[j,Nat.sub_zero,Nat.sub_zero]
   have h:land a (2^s - 1)=a:=by
     change a&&&(2^s - 1)=a;rw[nW,nQ l]
   have c:land b (2^s - 1)=b:=by
     change b&&&(2^s - 1)=b;rw[nW,nQ k]
   have h0:∀ x,land x 0=0:=fun x=>Nat.and_zero x;have i:∀ x,lor 0 x=x:=fun x=>Nat.zero_or x;rw[h0,h0,h,c,i,i];exact ⟨(max_eq_right (by omega)).symm,(min_eq_left (by omega)).symm⟩
lemma de (w s n a b M F:Nat) (W:s<w)
   (ha:a<2^(w*n)) (hb:b<2^(w*n))
   (L:M<2^(w*n)) (T:F<2^(w*n))
   (hM:∀ i<n,o w i M=2^s) (hF:∀ i<n,o w i F=2^s - 1)
   (v:∀ i<n,o w i a<2^s) (u:∀ i<n,o w i b<2^s) :
   let d:=land ((lor a M) - b) M
   let m:=d - shiftRight d s
   (∀ i<n,o w i (lor (land a m) (land b (F - m)))=max (o w i a) (o w i b))/\
   (∀ i<n,o w i (lor (land b m) (land a (F - m)))=min (o w i a) (o w i b))/\
   lor (land a m) (land b (F - m))<2^(w*n)/\
   lor (land b m) (land a (F - m))<2^(w*n):=by
 have h1s:2^s<2^w:=Nat.pow_lt_pow_right (by omega) W;have P:lor a M<2^(w*n):=nO ha L
 have C:∀ i<n,o w i b<=o w i (lor a M):=fun i hi=>by
   rw[dQ,hM i hi,fS s _ (v i hi)];have:=u i hi;omega
 have z:=ct w n (lor a M) b C P hb;set d:=land ((lor a M) - b) M;have r:d<2^(w*n):=lO nR L
 have K:∀ i<n,o w i d=if o w i b<=o w i a then 2^s else 0:=fun i hi=>by
   dsimp only[d];rw[bm,z.2 i hi,dQ,hM i hi];exact hR s (o w i a) (o w i b) (v i hi) (u i hi)
 have j:∀ i k,k<s->(o w (i+1) d).testBit k=false:=fun i k hk=>by
   by_cases hi:i+1<n
   . rw[K (i+1) hi];split_ifs
     . rw[nY];simp[show s ≠ k by omega]
     . simp
   . have a3:o w (i+1) d=0:=by
       rw[aS,nH (lQ r (nP (by omega) (by nlinarith)))];rfl
     rw[a3];simp
 have l:shiftRight d s<2^(w*n):=by
   change d >>> s<2^(w*n);rw[nD];exact lO (n3 _ _) r
 have c:∀ i<n,o w i (shiftRight d s)=shiftRight (o w i d) s:=fun i _=>
   iG w s i d (le_of_lt W) (j i)
 have Q:∀ i<n,o w i (shiftRight d s)<=o w i d:=fun i hi=>by
   rw[c i hi,K i hi];split_ifs
   . change (2^s) >>> s<=2^s;rw[nD];exact n3 _ _
   . simp[nD]
 have h:=ct w n d (shiftRight d s) Q r l;set m:=d - shiftRight d s
 have a0:∀ i<n,o w i m=if o w i b<=o w i a then 2^s - 1 else 0:=fun i hi=>by
   dsimp only[m];rw[h.2 i hi,c i hi,K i hi];split_ifs
   . change 2^s - (2^s) >>> s=2^s - 1;rw[nD,Nat.div_self (n2 s)]
   . change 0 - 0 >>> s=0;simp[nD]
 have N:∀ i<n,o w i m<=o w i F:=fun i hi=>by
   rw[a0 i hi,hF i hi];split_ifs <;> omega
 have a1:=ct w n F m N T h.1
 have y:lor (land a m) (land b (F - m))<2^(w*n):=
   nO (lO n5 ha) (lO n5 hb)
 have x:lor (land b m) (land a (F - m))<2^(w*n):=
   nO (lO n5 hb) (lO n5 ha)
 refine ⟨fun i hi=>?_,fun i hi=>?_,y,x⟩
 . rw[dQ,bm,bm,a1.2 i hi,hF i hi,h.2 i hi,c i hi]
   have t:o w i d=land ((lor (o w i a) (2^s)) - o w i b) (2^s):=by
     dsimp only[d];rw[bm,z.2 i hi,dQ,hM i hi]
   rw[t];exact (mT s (o w i a) (o w i b) (v i hi) (u i hi)).1
 . rw[dQ,bm,bm,a1.2 i hi,hF i hi,h.2 i hi,c i hi]
   have t:o w i d=land ((lor (o w i a) (2^s)) - o w i b) (2^s):=by
     dsimp only[d];rw[bm,z.2 i hi,dQ,hM i hi]
   rw[t];exact (mT s (o w i a) (o w i b) (v i hi) (u i hi)).2
lemma sH (s T v:Nat) (hT:T<=2^s) (b:v+(2^s - T)<2*2^s) :
   let x:=v+(2^s - T)
   let d:=land x (2^s)
   let m:=d - shiftRight d s
   land x m=v - T:=by
 dsimp only
 have c:land (v+(2^s - T)) (2^s)=if T<=v then 2^s else 0:=by
   apply nE2;intro k;change ((v+(2^s - T))&&&2^s).testBit k=_;rw[nV,nY]
   split_ifs with hle
   . rw[nY];by_cases hk:s=k
     . subst hk;simp only[dT,bU];rw[nJ,Nat.div_eq_of_lt_le (by omega) b];decide
     . simp[hk]
   . simp only[n4];by_cases hk:s=k
     . subst hk;simp only[dT,bU];exact nT (by omega)
     . simp[hk]
 rw[c];split_ifs with hle
 . have a:shiftRight (2^s) s=1:=by
     change (2^s) >>> s=1;rw[nD,Nat.div_self (n2 s)]
   rw[a];change (v+(2^s - T))&&&(2^s - 1)=v - T;rw[nW]
   have:v+(2^s - T)=(v - T)+2^s:=by omega
   rw[this,Nat.add_mod_right,nQ (by omega)]
 . have a:shiftRight 0 s=0:=by change 0 >>> s=0;rw[nD];simp
   rw[a,Nat.sub_zero];change _&&&0=_;rw[Nat.and_zero];omega
lemma jB (w s T n v K M:Nat) (z:s<w) (W:T<=2^s)
   (r:v<2^(w*n)) (y:K<2^(w*n)) (u:M<2^(w*n))
   (N:∀ i<n,o w i K=2^s - T) (P:∀ i<n,o w i M=2^s)
   (j:∀ i<n,o w i v+(2^s - T)<2*2^s) :
   let x:=v+K
   let d:=land x M
   let m:=d - shiftRight d s
   (∀ i<n,o w i (land x m)=o w i v - T)/\land x m<2^(w*n):=by
 have h2s:2*2^s<=2^w:=by rw[<- Nat.pow_succ'];exact nP (by omega) z
 have C:=ap w n v K (fun i hi=>by rw[N i hi];have:=j i hi;omega) r y;set x:=v+K;set d:=land x M;have h:d<2^(w*n):=lO nR u
 have l:∀ i<n,o w i d=if T<=o w i v then 2^s else 0:=fun i hi=>by
   dsimp only[d];rw[bm,C.2 i hi,N i hi,P i hi];apply nE2;intro k;change ((o w i v+(2^s - T))&&&2^s).testBit k=_;rw[nV,nY];split_ifs with hle
   . rw[nY];by_cases hk:s=k
     . subst hk;simp only[dT,bU];rw[nJ,Nat.div_eq_of_lt_le (by omega) (j i hi)];decide
     . simp[hk]
   . simp only[n4];by_cases hk:s=k
     . subst hk;simp only[dT,bU];exact nT (by omega)
     . simp[hk]
 have b:∀ i k,k<s->(o w (i+1) d).testBit k=false:=fun i k hk=>by
   by_cases hi:i+1<n
   . rw[l (i+1) hi];split_ifs
     . rw[nY];simp[show s ≠ k by omega]
     . simp
   . have F:o w (i+1) d=0:=by
       rw[aS,nH (lQ h (nP (by omega) (by nlinarith)))];rfl
     rw[F];simp
 have c:shiftRight d s<2^(w*n):=by
   change d >>> s<2^(w*n);rw[nD];exact lO (n3 _ _) h
 have a:∀ i<n,o w i (shiftRight d s)=shiftRight (o w i d) s:=fun i _=>
   iG w s i d (le_of_lt z) (b i)
 have t:∀ i<n,o w i (shiftRight d s)<=o w i d:=fun i hi=>by
   rw[a i hi,l i hi];split_ifs
   . change (2^s) >>> s<=2^s;rw[nD];exact n3 _ _
   . simp[nD]
 have Q:=ct w n d (shiftRight d s) t h c;refine ⟨fun i hi=>?_,lO n5 C.1⟩;rw[bm,Q.2 i hi,a i hi]
 have L:o w i d=land (o w i x) (2^s):=by dsimp only[d];rw[bm,P i hi]
 rw[L,C.2 i hi,N i hi];exact sH s T (o w i v) W (j i hi)
lemma jf (w s C n v K M F VC:Nat) (P:s<w) (hC:C<2^s)
   (j:v<2^(w*n)) (L:K<2^(w*n)) (z:M<2^(w*n))
   (N:F<2^(w*n)) (t:VC<2^(w*n))
   (hK:∀ i<n,o w i K=2^s - (C+1)) (hM:∀ i<n,o w i M=2^s)
   (hF:∀ i<n,o w i F=2^s - 1) (T:∀ i<n,o w i VC=C)
   (u:∀ i<n,o w i v+(2^s - (C+1))<2*2^s) :
   let d:=land (v+K) M
   let m:=d - shiftRight d s
   (∀ i<n,o w i (lor (land v (F - m)) (land VC m))=min C (o w i v))/\
   lor (land v (F - m)) (land VC m)<2^(w*n):=by
 have h2s:2*2^s<=2^w:=by rw[<- Nat.pow_succ'];exact nP (by omega) P
 have hx:=ap w n v K (fun i hi=>by rw[hK i hi];have:=u i hi;omega) j L;set d:=land (v+K) M;have h:d<2^(w*n):=lO nR z
 have l:∀ i<n,o w i d=if C+1<=o w i v then 2^s else 0:=fun i hi=>by
   dsimp only[d];rw[bm,hx.2 i hi,hK i hi,hM i hi];apply nE2;intro k;change ((o w i v+(2^s - (C+1)))&&&2^s).testBit k=_;rw[nV,nY];split_ifs with hle
   . rw[nY];by_cases hk:s=k
     . subst hk;simp only[dT,bU];rw[nJ,Nat.div_eq_of_lt_le (by omega) (u i hi)];decide
     . simp[hk]
   . simp only[n4];by_cases hk:s=k
     . subst hk;simp only[dT,bU];exact nT (by omega)
     . simp[hk]
 have b:∀ i k,k<s->(o w (i+1) d).testBit k=false:=fun i k hk=>by
   by_cases hi:i+1<n
   . rw[l (i+1) hi];split_ifs
     . rw[nY];simp[show s ≠ k by omega]
     . simp
   . have Q:o w (i+1) d=0:=by
       rw[aS,nH (lQ h (nP (by omega) (by nlinarith)))];rfl
     rw[Q];simp
 have c:shiftRight d s<2^(w*n):=by
   change d >>> s<2^(w*n);rw[nD];exact lO (n3 _ _) h
 have a:∀ i<n,o w i (shiftRight d s)=shiftRight (o w i d) s:=fun i _=>
   iG w s i d (le_of_lt P) (b i)
 have y:∀ i<n,o w i (shiftRight d s)<=o w i d:=fun i hi=>by
   rw[a i hi,l i hi];split_ifs
   . change (2^s) >>> s<=2^s;rw[nD];exact n3 _ _
   . simp[nD]
 have hm:=ct w n d (shiftRight d s) y h c;set m:=d - shiftRight d s
 have x:∀ i<n,o w i m=if C+1<=o w i v then 2^s - 1 else 0:=fun i hi=>by
   dsimp only[m];rw[hm.2 i hi,a i hi,l i hi];split_ifs
   . change 2^s - (2^s) >>> s=2^s - 1;rw[nD,Nat.div_self (n2 s)]
   . change 0 - 0 >>> s=0;simp[nD]
 have r:∀ i<n,o w i m<=o w i F:=fun i hi=>by rw[x i hi,hF i hi];split_ifs <;> omega
 have W:=ct w n F m r N hm.1;refine ⟨fun i hi=>?_,nO (lO n5 j) (lO n5 t)⟩;rw[dQ,bm,bm,W.2 i hi,hF i hi,T i hi,x i hi]
 split_ifs with hle
 . rw[Nat.sub_self];change (o w i v&&&0)|||(C&&&(2^s - 1))=_;rw[Nat.and_zero,Nat.zero_or,nW,nQ hC];exact (min_eq_left (by omega)).symm
 . rw[Nat.sub_zero];change (o w i v&&&(2^s - 1))|||(C&&&0)=_;rw[Nat.and_zero,Nat.or_zero,nW,nQ (by omega)];exact (min_eq_right (by omega)).symm
lemma gb (w s n a b M:Nat) (_hsw:s<w)
   (x:a<2^(w*n)) (v:b<2^(w*n)) (k:M<2^(w*n))
   (u:∀ i<n,o w i M=2^s)
   (j:∀ i<n,o w i a<2^s) (h:∀ i<n,o w i b<2^s)
   (m:nE (land ((lor a M) - b) M) M=true) :
   ∀ i<n,o w i b<=o w i a:=by
 have r:=bQ m;have d:lor a M<2^(w*n):=nO x k
 have c:∀ i<n,o w i b<=o w i (lor a M):=fun i hi=>by
   rw[dQ,u i hi,fS s _ (j i hi)];have:=h i hi;omega
 have l:=ct w n (lor a M) b c d v;intro i hi;have t:=congrArg (o w i) r;rw[bm,l.2 i hi,dQ,u i hi,hR s _ _ (j i hi) (h i hi)] at t
 split_ifs at t with hle
 . exact hle
 . exfalso;have:=n2 s;omega
lemma br (W r w:Nat) (hr1:1<=r) (hr5:r<5) (c:w<2^(5*W)) :
   lor (shiftLeft (land w ((1 <<< (W*(5 - r))) - 1)) (W*r)) (shiftRight w (W*(5 - r))) =
   ke W r w:=by
 unfold ke
 have b:nE r 0=false:=by cases r;omega;rfl
 simp only[b,bF,↓reduceIte];apply nE2;intro k;change (((w&&&((1 <<< (W*(5 - r))) - 1)) <<< (W*r))|||(w >>> (W*(5 - r)))).testBit k=_;simp only[nI,nV,nX,nU];simp only[nL,n1,nK,ge_iff_le]
 have hsum:W*r+W*(5 - r)=5*W:=by rw[<- Nat.mul_add,show r+(5 - r)=5 by omega,nC]
 by_cases hk5:k<5*W
 . simp only[hk5,dT,bU]
   by_cases hkd:W*r<=k
   . have a:k - W*r<W*(5 - r):=by omega
     simp[hkd,a]
   . simp[hkd]
 . simp only[hk5,decide_false,bX]
   have h1:w.testBit (W*(5 - r)+k)=false:=
     nT (lQ c (nP (by omega) (by omega)))
   by_cases hkd:W*r<=k
   . have a:¬ (k - W*r<W*(5 - r)):=by omega
     simp[hkd,a,h1]
   . simp[hkd,h1]
lemma fZ (W w:Nat) (a:w<2^(5*W)) :
  shiftRight w (4*W)=land (shiftRight w (4*W)) ((1 <<< W) - 1):=by
 change w >>> (4*W)=(w >>> (4*W))&&&((1 <<< W) - 1);rw[nL,n1,nW,nD,nQ]
 rw[Nat.div_lt_iff_lt_mul (n2 _),<-n0,show W+4*W=5*W by omega];exact a
lemma jV (w n l b d:Nat)
   (h0:l<2^(3*w*n)) (h1:b<2^(3*w*n)) (h2:d<2^(3*w*n))
   (gK:∀ i<n,o (3*w) i l<2^w)
   (eW:∀ i<n,o (3*w) i b<2^w)
   (fj:∀ i<n,o (3*w) i d<2^w) :
   let t:=lor l (lor (shiftLeft b w) (shiftLeft d (2*w)))
   t<2^(3*w*n)/\
   (∀ i<n,o w (3*i) t=o (3*w) i l/\
             o w (3*i+1) t=o (3*w) i b/\
             o w (3*i+2) t=o (3*w) i d):=by
 have T:shiftLeft b w<2^(3*w*n):=by
   have v:∀ k,3*w*n<=k->(shiftLeft b w).testBit k=false:=fun k hk=>by
     change (b <<< w).testBit k=false;rw[nX]
     by_cases hwk:w<=k
     . simp only[hwk,dT,bTA]
       by_cases hkn:k - w<3*w*n
       . have z:(k - w)/(3*w)<n:=Nat.div_lt_of_lt_mul hkn;have K:(k - w) % (3*w)<3*w:=nM _ (by omega)
         have a:w<=(k - w) % (3*w):=by
           have N:=Nat.div_add_mod (k - w) (3*w);have M:k - w+w=k:=Nat.sub_add_cancel hwk;have L:(k - w)/(3*w)+1<=n:=z
           nlinarith
         have x:=nT (lQ (eW _ z) (nP (by omega) a));rw[U] at x;simp only[K,dT,bTA,Nat.div_add_mod] at x;exact x
       . exact nT (lQ h1 (nP (by omega) (by omega)))
     . simp[hwk]
   by_contra a;push Not at a
   have h:=Nat.testBit_log2 (show shiftLeft b w ≠ 0 by intro hz;rw[hz] at a;have:=n2 (3*w*n);omega);have r:3*w*n<=Nat.log2 (shiftLeft b w):=Nat.le_log2 (by intro hz;rw[hz] at a;have:=n2 (3*w*n);omega) |>.mpr a;rw[v _ r] at h;cases h
 have P:shiftLeft d (2*w)<2^(3*w*n):=by
   have v:∀ k,3*w*n<=k->(shiftLeft d (2*w)).testBit k=false:=fun k hk=>by
     change (d <<< (2*w)).testBit k=false;rw[nX]
     by_cases hwk:2*w<=k
     . simp only[hwk,dT,bTA]
       by_cases hkn:k - 2*w<3*w*n
       . have z:(k - 2*w)/(3*w)<n:=Nat.div_lt_of_lt_mul hkn;have K:(k - 2*w) % (3*w)<3*w:=nM _ (by omega)
         have a:w<=(k - 2*w) % (3*w):=by
           have N:=Nat.div_add_mod (k - 2*w) (3*w);have M:k - 2*w+2*w=k:=Nat.sub_add_cancel hwk;have L:(k - 2*w)/(3*w)+1<=n:=z
           nlinarith
         have x:=nT (lQ (fj _ z) (nP (by omega) a));rw[U] at x;simp only[K,dT,bTA,Nat.div_add_mod] at x;exact x
       . exact nT (lQ h2 (nP (by omega) (by omega)))
     . simp[hwk]
   by_contra a;push Not at a
   have h:=Nat.testBit_log2 (show shiftLeft d (2*w) ≠ 0 by intro hz;rw[hz] at a;have:=n2 (3*w*n);omega);have r:3*w*n<=Nat.log2 (shiftLeft d (2*w)):=Nat.le_log2 (by intro hz;rw[hz] at a;have:=n2 (3*w*n);omega) |>.mpr a;rw[v _ r] at h;cases h
 refine ⟨nO h0 (nO T P),fun i hi=>?_⟩
 have F:o (3*w) i (shiftLeft b w)=shiftLeft (o (3*w) i b) w:=
   kg (3*w) w i b (by omega) (fun j hj=>lQ (eW j (by omega)) (nP (by omega) (by omega)))
 have C:o (3*w) i (shiftLeft d (2*w))=shiftLeft (o (3*w) i d) (2*w):=
   kg (3*w) (2*w) i d (by omega) (fun j hj=>by simpa [show 3*w - 2*w=w by omega] using fj j (by omega))
 have u:o (3*w) i (lor l (lor (shiftLeft b w) (shiftLeft d (2*w)))) =
     lor (o (3*w) i l) (lor (shiftLeft (o (3*w) i b) w) (shiftLeft (o (3*w) i d) (2*w))):=by
   rw[dQ,dQ,F,C]
 have m:∀ c<3,o w (3*i+c) (lor l (lor (shiftLeft b w) (shiftLeft d (2*w)))) =
     match c with|0=>o (3*w) i l|1=>o (3*w) i b|_=>o (3*w) i d:=fun c hc=>by
   rw[<- aY w c i _ hc,u];apply nE2;intro k;change (o w c (o (3*w) i l|||((o (3*w) i b <<< w)|||(o (3*w) i d <<< (2*w))))).testBit k=_;rw[U,nI,nI,nX,nX]
   by_cases hk:k<w
   . simp only[hk,dT,bTA]
     have:c=0\/c=1\/c=2:=by omega
     rcases this with rfl|rfl|rfl
     . simp[show ¬ w<=k by omega,show ¬ 2*w<=k by omega]
     . have y:(o (3*w) i l).testBit (w+k)=false:=
         nT (lQ (gK i hi) (nP (by omega) (by omega)))
       simp[y,show ¬ 2*w<=w+k by omega]
     . have y:(o (3*w) i l).testBit (w*2+k)=false:=
         nT (lQ (gK i hi) (nP (by omega) (by omega)))
       have Q:(o (3*w) i b).testBit (w*2+k - w)=false:=
         nT (lQ (eW i hi) (nP (by omega) (by omega)))
       simp[y,Q,show 2*w<=w*2+k by omega,show w*2+k - 2*w=k by omega]
   . simp only[hk,decide_false,bFA]
     have:c=0\/c=1\/c=2:=by omega
     rcases this with rfl|rfl|rfl
     . exact (nT (lQ (gK i hi) (nP (by omega) (by omega)))).symm
     . exact (nT (lQ (eW i hi) (nP (by omega) (by omega)))).symm
     . exact (nT (lQ (fj i hi) (nP (by omega) (by omega)))).symm
 exact ⟨by simpa using m 0 (by omega),m 1 (by omega),m 2 (by omega)⟩
lemma cb (w n c p C:Nat) (d:∀ i<n,o (3*w) i C=2^w - 1) :
   ∀ i<n,o (3*w) i (land (shiftRight p (c*w)) C)=o w (3*i+c) p:=fun i hi=>by
 apply nE2;intro k
 rw[bm,d i hi]
 change (o (3*w) i (p >>> (c*w))&&&(2^w - 1)).testBit k=(o w (3*i+c) p).testBit k
 rw[nV,nK,U,nU,U]
 by_cases hk:k<w
 . have b:k<3*w:=by omega
   have a:c*w+(3*w*i+k)=w*(3*i+c)+k:=by ring
   simp[hk,b,a]
 . simp[hk]
lemma Rz (a:Nat) (b:a<2^45) (n:∀ i<5,o 9 i a<4) :
  let l:=land (shiftRight (a+0x30180c0603) 2) 0x1008040201
  l<2^45/\∀ i<5,o 9 i l=if o 9 i a=0 then 0 else 1:=by
 have d:(0x30180c0603:Nat)<2^45:=by decide
 have j:(0x1008040201:Nat)<2^45:=by decide
 have c:∀ i<5,o 9 i 0x30180c0603=3:=by
  intro i hi;have:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
  rcases this with rfl|rfl|rfl|rfl|rfl <;> decide
 have u:∀ i<5,o 9 i 0x1008040201=1:=by
  intro i hi;have:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
  rcases this with rfl|rfl|rfl|rfl|rfl <;> decide
 have t:=ap 9 5 a 0x30180c0603 (fun i hi=>by rw[c i hi];have:=n i hi;omega) b d;refine ⟨lO nR j,fun i hi=>?_⟩;rw[bm,u i hi];apply nE2;intro k;change (o 9 i ((a+0x30180c0603) >>> 2)&&&1).testBit k=_;rw[nV,U,nU]
 cases k with
 | zero=>
  simp only[show 0<9 by omega,dT,bTA,nZ]
  have r:(a+0x30180c0603).testBit (2+9*i)=(o 9 i (a+0x30180c0603)).testBit 2:=by
   rw[U];simp[show 2<9 by omega,Nat.add_comm]
  rw[r,t.2 i hi,c i hi];have hlt:=n i hi
  have:o 9 i a=0\/o 9 i a=1\/o 9 i a=2\/o 9 i a=3:=by omega
  rcases this with h|h|h|h <;> simp[h] <;> decide
 | succ m=>
  have v:(1:Nat).testBit (m+1)=false:=by simp[Nat.testBit_succ]
  rw[v,bX]
  split_ifs <;> simp[Nat.testBit_succ]
def lI (m:Nat):Nat:=
 land m 73+land (shiftRight m 1) 73+land (shiftRight m 2) 73
lemma vB (mA:Nat) (e:Fin 5) :
   let v:=land mA 0x49249249249+land (shiftRight mA 1) 0x49249249249+land (shiftRight mA 2) 0x49249249249
   o 9 e.val v=lI (o 9 e.val mA):=by
 dsimp only
 have b:(0x49249249249:Nat)<2^45:=by decide
 have d:∀ i<5,o 9 i 0x49249249249=73:=fun i hi=>by
   have:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
   rcases this with rfl|rfl|rfl|rfl|rfl <;> decide
 have m:land mA 0x49249249249<2^45:=lO nR b;have l:land (shiftRight mA 1) 0x49249249249<2^45:=lO nR b;have j:land (shiftRight mA 2) 0x49249249249<2^45:=lO nR b
 have a:∀ x i,i<5->o 9 i (land x 0x49249249249)<=73:=fun x i hi=>by
   rw[bm,d i hi];exact nR
 have h:=ap 9 5 _ _ (fun i hi=>by have:=a mA i hi;have:=a (shiftRight mA 1) i hi;omega) m l;have u:=ap 9 5 _ _ (fun i hi=>by rw[h.2 i hi];have:=a mA i hi;have:=a (shiftRight mA 1) i hi;have:=a (shiftRight mA 2) i hi;omega) h.1 j;rw[u.2 e.val e.isLt,h.2 e.val e.isLt]
 have c:∀ s<3,o 9 e.val (land (shiftRight mA s) 0x49249249249)=land (shiftRight (o 9 e.val mA) s) 73:=fun s hs=>by
   rw[bm,d e.val e.isLt];apply nE2;intro k;change (o 9 e.val (mA >>> s)&&&73).testBit k=((o 9 e.val mA >>> s)&&&73).testBit k;rw[nV,nV,U,nU,nU,U]
   by_cases hk:k=0\/k=3\/k=6
   . have t:k<9:=by omega
     have r:s+k<9:=by omega
     have n:s+(9*e.val+k)=9*e.val+(s+k):=by omega
     simp[t,r,n]
   . have tG:(73:Nat).testBit k=false:=by
       by_cases h9:k<9
       . have:k=1\/k=2\/k=4\/k=5\/k=7\/k=8:=by omega
         rcases this with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
       . exact nT (lQ (by decide:73<2^9) (nP (by omega) (by omega)))
     simp[tG]
 have w:o 9 e.val (land mA 0x49249249249)=land (o 9 e.val mA) 73:=by simpa using c 0 (by omega)
 rw[w,c 1 (by omega),c 2 (by omega)];rfl
lemma tu (mB:Nat) (k:Fin 15) :
   let y:=land mB 0x1249249249249249249249249249249249+land (shiftRight mB 1) 0x1249249249249249249249249249249249+land (shiftRight mB 2) 0x1249249249249249249249249249249249
   o 9 k.val y=lI (o 9 k.val mB):=by
 dsimp only
 have c:(0x1249249249249249249249249249249249:Nat)<2^135:=by decide
 have h:∀ i<15,o 9 i 0x1249249249249249249249249249249249=73:=fun i hi=>
   (by decide +kernel:∀ j:Fin 15,o 9 j.val 0x1249249249249249249249249249249249=73) ⟨i,hi⟩
 have r:land mB 0x1249249249249249249249249249249249<2^135:=lO nR c;have n:land (shiftRight mB 1) 0x1249249249249249249249249249249249<2^135:=lO nR c;have m:land (shiftRight mB 2) 0x1249249249249249249249249249249249<2^135:=lO nR c
 have a:∀ x i,i<15->o 9 i (land x 0x1249249249249249249249249249249249)<=73:=fun x i hi=>by
   rw[bm,h i hi];exact nR
 have l:=ap 9 15 _ _ (fun i hi=>by have:=a mB i hi;have:=a (shiftRight mB 1) i hi;omega) r n;have w:=ap 9 15 _ _ (fun i hi=>by rw[l.2 i hi];have:=a mB i hi;have:=a (shiftRight mB 1) i hi;have:=a (shiftRight mB 2) i hi;omega) l.1 m;rw[w.2 k.val k.isLt,l.2 k.val k.isLt]
 have d:∀ s<3,o 9 k.val (land (shiftRight mB s) 0x1249249249249249249249249249249249)=land (shiftRight (o 9 k.val mB) s) 73:=fun s hs=>by
   rw[bm,h k.val k.isLt];apply nE2;intro b;change (o 9 k.val (mB >>> s)&&&73).testBit b=((o 9 k.val mB >>> s)&&&73).testBit b;rw[nV,nV,U,nU,nU,U]
   by_cases hb:b=0\/b=3\/b=6
   . have v:b<9:=by omega
     have u:s+b<9:=by omega
     have t:s+(9*k.val+b)=9*k.val+(s+b):=by omega
     simp[v,u,t]
   . have tG:(73:Nat).testBit b=false:=by
       by_cases h9:b<9
       . have:b=1\/b=2\/b=4\/b=5\/b=7\/b=8:=by omega
         rcases this with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
       . exact nT (lQ (by decide:73<2^9) (nP (by omega) (by omega)))
     simp[tG]
 have z:o 9 k.val (land mB 0x1249249249249249249249249249249249)=land (o 9 k.val mB) 73:=by simpa using d 0 (by omega)
 rw[z,d 1 (by omega),d 2 (by omega)];rfl
def vG (e:Fin 5) (k1 k2:Fin 3):Fin 15->Bool:=
 fun i=>decide ((i.val % 5=e.val/\i.val/5 ≠ k1.val)\/(i.val % 5=(e.val+1) % 5/\i.val/5 ≠ k2.val))
def vH (s:Fin 5) (a b c:Fin 3):Fin 15->Bool:=
 fun i=>decide (i.val % 5=s.val\/i.val % 5=(s.val+2) % 5\/
  (i.val % 5=(s.val+1) % 5/\i.val/5=a.val)\/
  (i.val % 5=(s.val+3) % 5/\i.val/5=b.val)\/
  (i.val % 5=(s.val+4) % 5/\i.val/5=c.val))
def targetFn (z:Fin 15->Bool):Bool:=
 (((z 0&&z 5)||(z 0&&z 10)||(z 5&&z 10))&&((z 1&&z 6)||(z 1&&z 11)||(z 6&&z 11)))||
 (((z 1&&z 6)||(z 1&&z 11)||(z 6&&z 11))&&((z 2&&z 7)||(z 2&&z 12)||(z 7&&z 12)))||
 (((z 2&&z 7)||(z 2&&z 12)||(z 7&&z 12))&&((z 3&&z 8)||(z 3&&z 13)||(z 8&&z 13)))||
 (((z 3&&z 8)||(z 3&&z 13)||(z 8&&z 13))&&((z 4&&z 9)||(z 4&&z 14)||(z 9&&z 14)))||
 (((z 4&&z 9)||(z 4&&z 14)||(z 9&&z 14))&&((z 0&&z 5)||(z 0&&z 10)||(z 5&&z 10)))
def cF (p:Nat->Bool):Nat->Nat
 | 0=>0
 | n+1=>if p n then cF p n|||(1 <<< n) else cF p n
lemma el (p:Nat->Bool) (n k:Nat) :
   (cF p n).testBit k=(decide (k<n)&&p k):=by
 induction n with
 | zero=>simp[cF]
 | succ n ih=>
   unfold cF;cases hp:p n
   . simp only[bF,↓reduceIte,ih]
     by_cases hk:k=n
     . subst hk;simp[hp]
     . simp[show (k<n+1) ↔ (k<n) by omega]
   . simp only[↓reduceIte,nI,ih,nX,ge_iff_le]
     by_cases hk:k=n
     . subst hk;simp[hp]
     . have a:(decide (n<=k)&&Nat.testBit 1 (k - n))=false:=by
         cases h1:decide (n<=k) <;> cases h2:Nat.testBit 1 (k - n) <;> try rfl
         exfalso
         have hle:n<=k:=of_decide_eq_true h1
         cases hm:k - n with
         | zero=>omega
         | succ m=>rw[hm] at h2;simp[Nat.testBit_succ] at h2
       simp[a,show (k<n+1) ↔ (k<n) by omega]
lemma lS (p q:Nat->Bool) (n:Nat) :
  cF (fun k=>p k&&q k) n=cF p n&&&cF q n:=by
 apply nE2;intro k;simp[nV,el];cases decide (k<n) <;> simp
lemma mV (p q:Nat->Bool) (n:Nat) :
  cF (fun k=>p k||q k) n=cF p n|||cF q n:=by
 apply nE2;intro k;simp[el];cases decide (k<n) <;> simp
def R (f:(Fin 15->Bool)->Bool):Nat:=
 cF (fun idx=>f (vG ⟨idx/9 % 5,by omega⟩ ⟨idx/3 % 3,by omega⟩ ⟨idx % 3,by omega⟩)) 45
def O (f:(Fin 15->Bool)->Bool):Nat:=
 cF (fun idx=>f (vH ⟨idx/27 % 5,by omega⟩ ⟨idx/9 % 3,by omega⟩ ⟨idx/3 % 3,by omega⟩ ⟨idx % 3,by omega⟩)) 135
lemma lW (f:(Fin 15->Bool)->Bool) (e:Fin 5) (b a:Fin 3) :
   (R f).testBit (9*e.val+3*b.val+a.val)=f (vG e b a):=by
 unfold R;rw[el]
 have c:9*e.val+3*b.val+a.val<45:=by omega
 simp only[c,dT,bTA];congr 1;congr 1
 . ext;dsimp only;omega
 . ext;dsimp only;omega
 . ext;dsimp only;omega
lemma lV (f:(Fin 15->Bool)->Bool) (s:Fin 5) (a b c:Fin 3) :
   (O f).testBit (27*s.val+9*a.val+3*b.val+c.val)=f (vH s a b c):=by
 unfold O;rw[el]
 have d:27*s.val+9*a.val+3*b.val+c.val<135:=by omega
 simp only[d,dT,bTA];congr 1;congr 1
 . ext;dsimp only;omega
 . ext;dsimp only;omega
 . ext;dsimp only;omega
 . ext;dsimp only;omega
lemma aF (f g:(Fin 15->Bool)->Bool) :
 R (fun x=>f x&&g x)=R f&&&R g:=lS _ _ 45
lemma aX (f g:(Fin 15->Bool)->Bool) :
 R (fun x=>f x||g x)=R f|||R g:=mV _ _ 45
lemma aZ (f g:(Fin 15->Bool)->Bool) :
 O (fun x=>f x&&g x)=O f&&&O g:=lS _ _ 135
lemma aJ (f g:(Fin 15->Bool)->Bool) :
 O (fun x=>f x||g x)=O f|||O g:=mV _ _ 135
lemma tB:R targetFn=(1 <<< 45) - 1:=by decide +kernel
lemma tA:O targetFn=0:=by decide +kernel
def DV (g:Fin 10) (v:Fin 5):Fin 5:=
 ⟨if g.val<5 then (v.val+g.val) % 5 else (10 - v.val+g.val) % 5,by split_ifs <;> omega⟩
def ek (g:Fin 10) (i:Fin 15):Fin 15:=
 ⟨5*(i.val/5)+(DV g ⟨i.val % 5,by omega⟩).val,by have:=(DV g ⟨i.val % 5,by omega⟩).isLt;omega⟩
def E (g:Fin 10) (f:(Fin 15->Bool)->Bool):(Fin 15->Bool)->Bool:=
 fun x=>f (fun i=>x (ek g i))
def au (g:Fin 10) (e:Fin 5):Fin 5:=
 ⟨if g.val<5 then (e.val+g.val) % 5 else (9 - e.val+(g.val - 5)) % 5,by split_ifs <;> omega⟩
def ad (g:Fin 10) (s:Fin 5):Fin 5:=
 ⟨if g.val<5 then (s.val+g.val) % 5 else (8 - s.val+(g.val - 5)) % 5,by split_ifs <;> omega⟩
def bx (g h:Fin 10):Fin 10:=
 let b:=g.val % 5;let a:=h.val % 5
 if g.val<5 then
  if h.val<5 then ⟨(a+b) % 5,by omega⟩
  else ⟨5+(a+b) % 5,by omega⟩
 else
  if h.val<5 then ⟨5+(5 - a+b) % 5,by omega⟩
  else ⟨(5 - a+b) % 5,by omega⟩
def I (g:Fin 10):Fin 10:=
 if g.val<5 then ⟨(5 - g.val) % 5,by omega⟩ else g
lemma xm:∀ (g h:Fin 10) (i:Fin 15),ek g (ek h i)=ek (bx g h) i:=by decide +kernel
lemma vE:∀ (g:Fin 10) (i:Fin 15),ek (I g) (ek g i)=i:=by decide +kernel
lemma cE:∀ (g:Fin 10) (e:Fin 5),au g (au (I g) e)=e:=by decide +kernel
lemma cd:∀ (g:Fin 10) (s:Fin 5),ad g (ad (I g) s)=s:=by decide +kernel
def Ch (g e:Nat):Nat:=cond (nB g 4) ((e+5 - g) % 5) ((4 - e+g) % 5)
def zp (g s:Nat):Nat:=cond (nB g 4) ((s+5 - g) % 5) ((3+g - s) % 5)
lemma H2:∀ (g:Fin 10) (e:Fin 5),Ch g.val e.val=(au (I g) e).val:=by decide +kernel
lemma Gh:∀ (g:Fin 10) (s:Fin 5),zp g.val s.val=(ad (I g) s).val:=by decide +kernel
def eJ (sp sq:Nat):List Nat:=
 cond (nE sp 0&&nE sq 0) [0,1,2,3,4,5,6,7,8,9]
  (cond (nE sp 0||nE sq 0) [0,1,2,3,4]
   (let a:=(3*(sp+5 - sq)) % 5;[a,(a+1) % 5,(a+2) % 5]))
lemma fQ:∀ (gp gq sp sq:Fin 10),
 (sq.val=0\/5<=sq.val)->
 bx (bx sp gp) (I (bx sq gq))=bx sp (bx (bx gp (I gq)) sq):=by decide +kernel
lemma dO:∀ g:Fin 10,bx ⟨0,by decide⟩ g=g:=by decide +kernel
lemma p7:∀ g:Fin 10,bx g ⟨0,by decide⟩=g:=by decide +kernel
set_option maxHeartbeats 0 in
lemma ty:∀ (g:Fin 10) (e:Fin 5) (k1 k2:Fin 3) (i:Fin 15),
 vG (au g e) (if g.val<5 then k1 else k2) (if g.val<5 then k2 else k1) (ek g i) =
 vG e k1 k2 i:=by decide +kernel
set_option maxHeartbeats 0 in
lemma tz:∀ (g:Fin 10) (s:Fin 5) (a b c:Fin 3) (i:Fin 15),
 vH (ad g s) a (if g.val<5 then b else c) (if g.val<5 then c else b) (ek g i) =
 vH s a b c i:=by decide +kernel
lemma cK (g h:Fin 10) (f:(Fin 15->Bool)->Bool) :
  E g (E h f)=E (bx g h) f:=by
 funext x;unfold E;dsimp only;congr 1;funext i;rw[xm]
lemma mi (g:Fin 10) (f:(Fin 15->Bool)->Bool) :
  E (I g) (E g f)=f:=by
 funext x;unfold E;dsimp only;congr 1;funext i;rw[vE]
def bE (W a0 a1 a2:Nat):Nat:=
 a0+a1*2^W+a2*2^(2*W)
def bM (W a0 a1 a2 a3 a4:Nat):Nat:=
 a0+a1*2^W+a2*2^(2*W)+a3*2^(3*W)+a4*2^(4*W)
lemma eH (W a d N:Nat) (b:a<2^W) (h:d+W<=N):a <<< d<2^N:=by
 rw[nL];have h1:a*2^d<2^W*2^d:=Nat.mul_lt_mul_of_pos_right b (n2 d)
 have h2:2^W*2^d<=2^N:=by rw[<- n0];exact nP (by omega) (by omega)
 exact lQ h1 h2
lemma iX (W a0 a1 a2:Nat) (h0:a0<2^W) (h1:a1<2^W) :
  bE W a0 a1 a2=a0|||(a1 <<< W)|||(a2 <<< (2*W)):=by
 unfold bE
 have a:a0+a1*2^W<2^(2*W):=by
  rw[show 2*W=W+W by omega,n0]
  have hmul:a1*2^W+2^W<=2^W*2^W:=by
   have:a1+1<=2^W:=h1
   calc a1*2^W+2^W=(a1+1)*2^W:=by ring
    _<=2^W*2^W:=Nat.mul_le_mul_right _ this
  omega
 rw[ce (2*W) (a0+a1*2^W) a2 a,ce W a0 a1 h0]
lemma dv (W a0 a1 a2 a3 a4:Nat)
  (h0:a0<2^W) (h1:a1<2^W) (h2:a2<2^W) (h3:a3<2^W) :
  bM W a0 a1 a2 a3 a4=a0|||(a1 <<< W)|||(a2 <<< (2*W))|||(a3 <<< (3*W))|||(a4 <<< (4*W)):=by
 unfold bM
 have a:∀ k x y:Nat,x<2^(k*W)->y<2^W->x+y*2^(k*W)<2^((k+1)*W):=by
  intro k x y hx hy
  rw[show (k+1)*W=W+k*W by ring,n0]
  have hmul:y*2^(k*W)+2^(k*W)<=2^W*2^(k*W):=by
   calc y*2^(k*W)+2^(k*W)=(y+1)*2^(k*W):=by ring
    _<=2^W*2^(k*W):=Nat.mul_le_mul_right _ hy
  omega
 have c:a0+a1*2^W<2^(2*W):=by simpa using a 1 a0 a1 (by simpa using h0) h1
 have b:a0+a1*2^W+a2*2^(2*W)<2^(3*W):=a 2 _ a2 c h2;have d:a0+a1*2^W+a2*2^(2*W)+a3*2^(3*W)<2^(4*W):=a 3 _ a3 b h3
 rw[ce (4*W) _ a4 d,ce (3*W) _ a3 b,
   ce (2*W) _ a2 c,ce W a0 a1 h0]
lemma gG (W a0 a1 a2:Nat) (h0:a0<2^W) (h1:a1<2^W) (h2:a2<2^W) :
  bE W a0 a1 a2<2^(3*W):=by
 rw[iX W a0 a1 a2 h0 h1]
 exact nO
  (nO (lQ h0 (nP (by omega) (by omega)))
   (eH W a1 W (3*W) h1 (by omega)))
  (eH W a2 (2*W) (3*W) h2 (by omega))
lemma dl (W a0 a1 a2 a3 a4:Nat)
  (h0:a0<2^W) (h1:a1<2^W) (h2:a2<2^W) (h3:a3<2^W) (h4:a4<2^W) :
  bM W a0 a1 a2 a3 a4<2^(5*W):=by
 rw[dv W a0 a1 a2 a3 a4 h0 h1 h2 h3]
 exact nO
  (nO
   (nO
    (nO (lQ h0 (nP (by omega) (by omega)))
     (eH W a1 W (5*W) h1 (by omega)))
    (eH W a2 (2*W) (5*W) h2 (by omega)))
   (eH W a3 (3*W) (5*W) h3 (by omega)))
  (eH W a4 (4*W) (5*W) h4 (by omega))
lemma bI (W a d k:Nat) (c:a<2^W) :
   (a <<< d).testBit k=(decide (d<=k)&&decide (k<d+W)&&a.testBit (k - d)):=by
 rw[nX]
 by_cases h1:d<=k
 . by_cases h2:k<d+W
   . simp[h1,h2]
   . have b:a.testBit (k - d)=false:=
       nT (lQ c (nP (by omega) (by omega)))
     simp[h1,h2,b]
 . simp[h1]
lemma fd (W a0 a1 a2:Nat) (h0:a0<2^W) (h1:a1<2^W) (h2:a2<2^W) :
   o W 0 (bE W a0 a1 a2)=a0/\
   o W 1 (bE W a0 a1 a2)=a1/\
   o W 2 (bE W a0 a1 a2)=a2:=by
 rw[iX W a0 a1 a2 h0 h1];refine ⟨?_,?_,?_⟩
 . apply nE2;intro k;rw[U];simp only[nI,bI W a1 W _ h1,bI W a2 (2*W) _ h2]
   by_cases hk:k<W
   . simp only[hk,dT,bTA,Nat.mul_zero,Nat.zero_add,
       show decide (W<=k)=false by simp;omega,
       show decide (2*W<=k)=false by simp;omega,
       bFA,bOF]
   . simp[hk,nT (lQ h0 (nP (by decide:0<2) (by omega:W<=k)))]
 . apply nE2;intro k;rw[U];simp only[nI,bI W a1 W _ h1,bI W a2 (2*W) _ h2]
   by_cases hk:k<W
   . simp only[hk,dT,bTA,Nat.mul_one,
       show a0.testBit (W+k)=false from nT (lQ h0 (nP (by decide:0<2) (by omega:W<=W+k))),
       show decide (W<=W+k)=true by simp,
       show decide (W+k<W+W)=true by simp;omega,
       show decide (2*W<=W+k)=false by simp;omega,
       Nat.add_sub_cancel_left,bTA,bFA,bFO,bOF]
   . simp[hk,nT (lQ h1 (nP (by decide:0<2) (by omega:W<=k)))]
 . apply nE2;intro k;rw[U];simp only[nI,bI W a1 W _ h1,bI W a2 (2*W) _ h2]
   by_cases hk:k<W
   . simp only[hk,dT,bTA,
       show a0.testBit (W*2+k)=false from nT (lQ h0 (nP (by decide:0<2) (by omega:W<=W*2+k))),
       show decide (W*2+k<W+W)=false by simp;omega,
       show decide (2*W<=W*2+k)=true by simp;omega,
       show decide (W*2+k<2*W+W)=true by simp;omega,
       show W*2+k - 2*W=k by omega,
       bTA,bX,bFA,bFO]
   . simp[hk,nT (lQ h2 (nP (by decide:0<2) (by omega:W<=k)))]
lemma cv (W a0 a1 a2 a3 a4:Nat)
   (h0:a0<2^W) (h1:a1<2^W) (h2:a2<2^W) (h3:a3<2^W) (h4:a4<2^W) :
   o W 0 (bM W a0 a1 a2 a3 a4)=a0/\
   o W 1 (bM W a0 a1 a2 a3 a4)=a1/\
   o W 2 (bM W a0 a1 a2 a3 a4)=a2/\
   o W 3 (bM W a0 a1 a2 a3 a4)=a3/\
   o W 4 (bM W a0 a1 a2 a3 a4)=a4:=by
 rw[dv W a0 a1 a2 a3 a4 h0 h1 h2 h3]
 have c:∀ i<5,o W i (a0|||(a1 <<< W)|||(a2 <<< (2*W))|||(a3 <<< (3*W))|||(a4 <<< (4*W))) =
     match i with|0=>a0|1=>a1|2=>a2|3=>a3|_=>a4:=by
   intro i c;apply nE2;intro k;rw[U]
   simp only[nI,bI W a1 W _ h1,bI W a2 (2*W) _ h2,
     bI W a3 (3*W) _ h3,bI W a4 (4*W) _ h4]
   by_cases hk:k<W
   . simp only[hk,dT,bTA]
     have a:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
     rcases a with rfl|rfl|rfl|rfl|rfl
     . simp[show decide (W<=k)=false by simp;omega,show decide (2*W<=k)=false by simp;omega,
         show decide (3*W<=k)=false by simp;omega,show decide (4*W<=k)=false by simp;omega]
     . simp[show a0.testBit (W+k)=false from nT (lQ h0 (nP (by omega) (by omega))),
         show decide (2*W<=W+k)=false by simp;omega,
         show decide (3*W<=W+k)=false by simp;omega,
         show decide (4*W<=W+k)=false by simp;omega,hk]
     . simp[show a0.testBit (W*2+k)=false from nT (lQ h0 (nP (by omega) (by omega))),
         show decide (W*2+k<W+W)=false by simp;omega,
         show decide (2*W<=W*2+k)=true by simp;omega,
         show decide (W*2+k<2*W+W)=true by simp;omega,
         show decide (3*W<=W*2+k)=false by simp;omega,
         show decide (4*W<=W*2+k)=false by simp;omega,
         show W*2+k - 2*W=k by omega]
     . simp[show a0.testBit (W*3+k)=false from nT (lQ h0 (nP (by omega) (by omega))),
         show decide (W*3+k<W+W)=false by simp;omega,
         show decide (W*3+k<2*W+W)=false by simp;omega,
         show decide (3*W<=W*3+k)=true by simp;omega,
         show decide (W*3+k<3*W+W)=true by simp;omega,
         show decide (4*W<=W*3+k)=false by simp;omega,
         show W*3+k - 3*W=k by omega]
     . simp[show a0.testBit (W*4+k)=false from nT (lQ h0 (nP (by omega) (by omega))),
         show decide (W*4+k<W+W)=false by simp;omega,
         show decide (W*4+k<2*W+W)=false by simp;omega,
         show decide (W*4+k<3*W+W)=false by simp;omega,
         show decide (4*W<=W*4+k)=true by simp;omega,
         show decide (W*4+k<4*W+W)=true by simp;omega,
         show W*4+k - 4*W=k by omega]
   . have b:∀ x<2^W,x.testBit k=false:=fun x hx=>
       nT (lQ hx (nP (by omega) (by omega)))
     have a:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
     rcases a with rfl|rfl|rfl|rfl|rfl <;> simp[hk,b a0 h0,b a1 h1,b a2 h2,b a3 h3,b a4 h4]
 exact ⟨c 0 (by omega),c 1 (by omega),c 2 (by omega),c 3 (by omega),c 4 (by omega)⟩
def D (a b c:Nat):Nat × Nat × Nat:=
 let x:=av a b;let y:=aa a b;let y':=av y c;let z:=aa y c
 (av x y',aa x y',z)
lemma X (a b c:Nat):D a b c=D b a c:=by
 simp only[D,aG,aP,min_comm a b,max_comm a b]
lemma aj (a b c:Nat):D a b c=D a c b:=by
 have d:∀ x y z:Nat,min (max x y) z=max (min x z) (min y z):=fun x y z=>by omega
 unfold D;simp only[aG,aP,Prod.mk.injEq];refine ⟨?_,?_,?_⟩
 . have h:∀ x y z:Nat,min (min x y) (min (max x y) z)=min x (min y z):=fun x y z=>by
     rw[<- min_assoc,min_eq_left (min_le_max:min x y<=max x y),min_assoc]
   rw[h,h,min_comm b c]
 . rw[d,d,min_comm b c,max_left_comm]
 . rw[max_assoc,max_comm b c,<-max_assoc]
lemma af (a b c:Nat) (h1:a<=b) (h2:b<=c):D a b c=(a,b,c):=by
 have EI:a<=c:=lT h1 h2;unfold D;simp only[aG,aP,min_eq_left h1,max_eq_right h1,min_eq_left h2,max_eq_right h2]
lemma jS (a b c:Nat) :
  (D a b c).1<=(D a b c).2.1/\(D a b c).2.1<=(D a b c).2.2:=by
 unfold D;simp only[aG,aP];exact ⟨min_le_max,xL (lT (mR a b) (lT (le_max_right a b) (le_max_left _ c))) (lT (mL _ c) (le_max_left _ c))⟩
lemma cr (a b c:Nat) :
   (D a b c).1+(D a b c).2.1+(D a b c).2.2=a+b+c:=by
 rcases lZ a b with hab|hba
 . rcases lZ b c with hbc|hcb
   . rw[af a b c hab hbc]
   . rcases lZ a c with hac|hca
     . rw[aj a b c,af a c b hac hcb];dsimp only;omega
     . rw[aj a b c,X a c b,af c a b hca hab];dsimp only;omega
 . rcases lZ a c with hac|hca
   . rw[X a b c,af b a c hba hac];dsimp only;omega
   . rcases lZ b c with hbc|hcb
     . rw[X a b c,aj b a c,af b c a hbc hca];dsimp only;omega
     . rw[X a b c,aj b a c,X b c a,af c b a hcb hba];dsimp only;omega
lemma lH {a b c k:Nat} (h:a<=k\/b<=k\/c<=k):(D a b c).1<=k:=by
 unfold D;simp only[aG,aP];rcases h with ha|hb|hc
 . exact lT (mL _ _) (lT (mL _ _) ha)
 . exact lT (mL _ _) (lT (mR _ _) hb)
 . exact lT (mR _ _) (lT (mR _ _) hc)
lemma kz {a b c k:Nat} (h:(a<=k/\b<=k)\/(a<=k/\c<=k)\/(b<=k/\c<=k)):(D a b c).2.1<=k:=by
 unfold D;simp only[aG,aP];rcases h with ⟨ha,hb⟩|⟨ha,hc⟩|⟨hb,hc⟩
 . exact xL (lT (mL _ _) ha) (lT (mL _ _) (xL ha hb))
 . exact xL (lT (mL _ _) ha) (lT (mR _ _) hc)
 . exact xL (lT (mR _ _) hb) (lT (mR _ _) hc)
lemma gQ {a b c k:Nat} (i:a<=k) (h:b<=k) (d:c<=k):(D a b c).2.2<=k:=by
 unfold D;simp only[aP];exact xL (xL i h) d
lemma xt {a b c k:Nat} (d:k<=a) (i:k<=b) (h:k<=c):k<=(D a b c).1:=by
 unfold D;simp only[aG,aP];exact lM (lM d i) (lM (lT d (le_max_left _ _)) h)
lemma vJ {a b c k:Nat} (h:(k<=a/\k<=b)\/(k<=a/\k<=c)\/(k<=b/\k<=c)):k<=(D a b c).2.1:=by
 unfold D;simp only[aG,aP];rcases h with ⟨ha,hb⟩|⟨ha,hc⟩|⟨hb,hc⟩
 . exact lT (lM ha hb) (le_max_left _ _)
 . exact lT (lM (lT ha (le_max_left _ _)) hc) (le_max_right _ _)
 . exact lT (lM (lT hb (le_max_right _ _)) hc) (le_max_right _ _)
lemma vI {a b c k:Nat} (h:k<=a\/k<=b\/k<=c):k<=(D a b c).2.2:=by
 unfold D;simp only[aP];rcases h with ha|hb|hc
 . exact lT ha (lT (le_max_left _ _) (le_max_left _ _))
 . exact lT hb (lT (le_max_right _ _) (le_max_left _ _))
 . exact lT hc (le_max_right _ _)
lemma cM {a b c a' b' c':Nat} (i:a<=a') (h:b<=b') (d:c<=c') :
  (D a b c).1<=(D a' b' c').1/\
  (D a b c).2.1<=(D a' b' c').2.1/\
  (D a b c).2.2<=(D a' b' c').2.2:=by
 unfold D;simp only[aG,aP];have h1:=min_le_min i h;have h2:=max_le_max i h;have h3:=min_le_min h2 d;have h4:=max_le_max h2 d;exact ⟨min_le_min h1 h3,max_le_max h1 h3,h4⟩
lemma jw (P:Nat->Nat->Nat->Nat->Nat->Nat->Prop)
   (i:∀ a b c d e f,P a b c d e f->P b a c e d f)
   (j:∀ a b c d e f,P a b c d e f->P a c b d f e)
   (h:∀ a b c d e f,a<=b->b<=c->P a b c d e f) :
   ∀ a b c d e f,P a b c d e f:=by
 intro a b c d e f;rcases lZ a b with hab|hba
 . rcases lZ b c with hbc|hcb
   . exact h a b c d e f hab hbc
   . rcases lZ a c with hac|hca
     . exact j a c b d f e (h a c b d f e hac hcb)
     . exact j a c b d f e (i c a b f d e (h c a b f d e hca hab))
 . rcases lZ a c with hac|hca
   . exact i b a c e d f (h b a c e d f hba hac)
   . rcases lZ b c with hbc|hcb
     . exact i b a c e d f (j b c a e f d (h b c a e f d hbc hca))
     . exact i b a c e d f (j b c a e f d (i c b a f e d (h c b a f e d hcb hba)))
lemma pT (u0 u1 u2 v0 v1 v2:Nat) :
   let x:=D u0 u1 u2;let y:=D v0 v1 v2
   let w:=D (min 3 (u0+v0)) (min 3 (u1+v1)) (min 3 (u2+v2))
   w.1<=min 3 (min (x.1+y.2.2) (min (x.2.1+y.2.1) (x.2.2+y.1)))/\
   w.2.1<=min 3 (min (x.2.1+y.2.2) (x.2.2+y.2.1))/\
   w.2.2<=min 3 (x.2.2+y.2.2):=by
 refine jw (fun u0 u1 u2 v0 v1 v2=>
   let x:=D u0 u1 u2;let y:=D v0 v1 v2;let w:=D (min 3 (u0+v0)) (min 3 (u1+v1)) (min 3 (u2+v2))
   w.1<=min 3 (min (x.1+y.2.2) (min (x.2.1+y.2.1) (x.2.2+y.1)))/\
   w.2.1<=min 3 (min (x.2.1+y.2.2) (x.2.2+y.2.1))/\
   w.2.2<=min 3 (x.2.2+y.2.2)) ?_ ?_ ?_ u0 u1 u2 v0 v1 v2
 . intro a b c d e f h;simpa only [X a b c,X d e f,X (min 3 (a+d))] using h
 . intro a b c d e f h;simpa only [aj a b c,aj d e f,aj (min 3 (a+d))] using h
 . intro a b c d e f hab hbc;dsimp only;rw[af a b c hab hbc]
   have i:∀ y0 y1 y2,D d e f=(y0,y1,y2)->
       (d<=y2/\e<=y2/\f<=y2)->
       (a+d<=b+y1\/b+e<=b+y1\/c+f<=b+y1)->
       (a+d<=c+y0\/b+e<=c+y0\/c+f<=c+y0)->
       ((a+d<=b+y2/\b+e<=b+y2)\/(a+d<=b+y2/\c+f<=b+y2)\/(b+e<=b+y2/\c+f<=b+y2))->
       ((a+d<=c+y1/\b+e<=c+y1)\/(a+d<=c+y1/\c+f<=c+y1)\/(b+e<=c+y1/\c+f<=c+y1))->
       (D (min 3 (a+d)) (min 3 (b+e)) (min 3 (c+f))).1<=min 3 (min (a+y2) (min (b+y1) (c+y0)))/\
       (D (min 3 (a+d)) (min 3 (b+e)) (min 3 (c+f))).2.1<=min 3 (min (b+y2) (c+y1))/\
       (D (min 3 (a+d)) (min 3 (b+e)) (min 3 (c+f))).2.2<=min 3 (c+y2):=by
     intro y0 y1 y2 _ h3 h1b h1c h2b h2c;have l:∀ t k,t<=k->min 3 t<=k:=fun t k h=>lT (mR 3 t) h
     have m:∀ k,(a+d<=k\/b+e<=k\/c+f<=k)->(D (min 3 (a+d)) (min 3 (b+e)) (min 3 (c+f))).1<=k:=
       fun k h=>lH (h.imp (l _ _) (fun h=>h.imp (l _ _) (l _ _)))
     have n:∀ k,((a+d<=k/\b+e<=k)\/(a+d<=k/\c+f<=k)\/(b+e<=k/\c+f<=k))->(D (min 3 (a+d)) (min 3 (b+e)) (min 3 (c+f))).2.1<=k:=
       fun k h=>kz (h.imp (fun h=>⟨l _ _ h.1,l _ _ h.2⟩) (fun h=>h.imp (fun h=>⟨l _ _ h.1,l _ _ h.2⟩) (fun h=>⟨l _ _ h.1,l _ _ h.2⟩)))
     exact ⟨lM (lH (oL (mL _ _))) (lM (m _ (oL (by omega))) (lM (m _ h1b) (m _ h1c))),
            lM (kz (oL ⟨mL _ _,mL _ _⟩)) (lM (n _ h2b) (n _ h2c)),
            lM (gQ (mL _ _) (mL _ _) (mL _ _))
              (gQ (l _ _ (by omega)) (l _ _ (by omega)) (l _ _ (by omega)))⟩
   rcases lZ d e with hde|hed
   . rcases lZ e f with hef|hfe
     . have j:=af d e f hde hef;rw[j]
       exact i d e f j ⟨by omega,by omega,by omega⟩ (oL (by omega)) (oL (by omega)) (oL ⟨by omega,by omega⟩) (oL ⟨by omega,by omega⟩)
     . rcases lZ d f with hdf|hfd
       . have j:D d e f=(d,f,e):=by rw[aj,af d f e hdf hfe]
         rw[j];exact i d f e j ⟨by omega,by omega,by omega⟩ (oL (by omega)) (oL (by omega)) (oL ⟨by omega,by omega⟩) (oR (oL ⟨by omega,by omega⟩))
       . have j:D d e f=(f,d,e):=by rw[aj,X,af f d e hfd hde]
         rw[j];exact i f d e j ⟨by omega,by omega,by omega⟩ (oL (by omega)) (oR (oR (by omega))) (oL ⟨by omega,by omega⟩) (oR (oL ⟨by omega,by omega⟩))
   . rcases lZ d f with hdf|hfd
     . have j:D d e f=(e,d,f):=by rw[X,af e d f hed hdf]
       rw[j];exact i e d f j ⟨by omega,by omega,by omega⟩ (oR (oL (by omega))) (oR (oL (by omega))) (oL ⟨by omega,by omega⟩) (oL ⟨by omega,by omega⟩)
     . rcases lZ e f with hef|hfe
       . have j:D d e f=(e,f,d):=by rw[X,aj,af e f d hef hfd]
         rw[j];exact i e f d j ⟨by omega,by omega,by omega⟩ (oR (oL (by omega))) (oR (oL (by omega))) (oL ⟨by omega,by omega⟩) (oR (oR ⟨by omega,by omega⟩))
       . have j:D d e f=(f,e,d):=by rw[X,aj,X,af f e d hfe hed]
         rw[j];exact i f e d j ⟨by omega,by omega,by omega⟩ (oR (oL (by omega))) (oR (oR (by omega))) (oL ⟨by omega,by omega⟩) (oR (oR ⟨by omega,by omega⟩))
lemma hS (a b d e:Nat) (hab:a<=b) (hed:e<=d):min a d+min b e<=min a e+min b d:=by
 omega
lemma nu (u0 u1 u2 v0 v1 v2:Nat) :
   let x:=D u0 u1 u2;let y:=D v0 v1 v2
   min u0 v0+min u1 v1+min u2 v2<=min x.1 y.1+min x.2.1 y.2.1+min x.2.2 y.2.2:=by
 refine jw (fun u0 u1 u2 v0 v1 v2=>
   let x:=D u0 u1 u2;let y:=D v0 v1 v2
   min u0 v0+min u1 v1+min u2 v2<=min x.1 y.1+min x.2.1 y.2.1+min x.2.2 y.2.2) ?_ ?_ ?_ u0 u1 u2 v0 v1 v2
 . intro a b c d e f h;simp only[X a b c,X d e f] at h ⊢;omega
 . intro a b c d e f h;simp only[aj a b c,aj d e f] at h ⊢;omega
 . intro a b c d e f hab hbc;dsimp only;rw[af a b c hab hbc];have i:a<=c:=lT hab hbc;rcases lZ d e with hde|hed
   . rcases lZ e f with hef|hfe
     . rw[af d e f hde hef]
     . rcases lZ d f with hdf|hfd
       . rw[aj d e f,af d f e hdf hfe];dsimp only;have:=hS b c e f hbc hfe;omega
       . rw[aj d e f,X d f e,af f d e hfd hde];dsimp only
         have:=hS b c e f hbc hfe;have:=hS a b d f hab hfd;omega
   . rcases lZ d f with hdf|hfd
     . rw[X d e f,af e d f hed hdf];dsimp only;have:=hS a b d e hab hed;omega
     . rcases lZ e f with hef|hfe
       . rw[X d e f,aj e d f,af e f d hef hfd];dsimp only
         have:=hS a b d e hab hed;have:=hS b c d f hbc hfd;omega
       . rw[X d e f,aj e d f,X e f d,af f e d hfe hed];dsimp only
         have:=hS a c d f i (lT hfe hed);omega
lemma zm (u0 u1 u2 v0 v1 v2:Nat) :
  let x:=D u0 u1 u2;let y:=D v0 v1 v2
  max x.1 y.1+max x.2.1 y.2.1+max x.2.2 y.2.2<=max u0 v0+max u1 v1+max u2 v2:=by
 have a:=nu u0 u1 u2 v0 v1 v2;have hs1:=cr u0 u1 u2;have hs2:=cr v0 v1 v2
 have h1:∀ p q:Nat,min p q+max p q=p+q:=fun p q=>by omega
 have e0:=h1 u0 v0;have e1:=h1 u1 v1;have e2:=h1 u2 v2;have f0:=h1 (D u0 u1 u2).1 (D v0 v1 v2).1;have f1:=h1 (D u0 u1 u2).2.1 (D v0 v1 v2).2.1;have f2:=h1 (D u0 u1 u2).2.2 (D v0 v1 v2).2.2;dsimp only at a ⊢;omega
lemma gX (u0 u1 u2 v0 v1 v2:Nat) :
   let x:=D u0 u1 u2;let y:=D v0 v1 v2
   let w:=D (u0+v0 - 9) (u1+v1 - 9) (u2+v2 - 9)
   x.1+y.1 - 9<=w.1/\
   max (x.1+y.2.1) (x.2.1+y.1) - 9<=w.2.1/\
   max (x.1+y.2.2) (max (x.2.1+y.2.1) (x.2.2+y.1)) - 9<=w.2.2:=by
 refine jw (fun u0 u1 u2 v0 v1 v2=>
   let x:=D u0 u1 u2;let y:=D v0 v1 v2;let w:=D (u0+v0 - 9) (u1+v1 - 9) (u2+v2 - 9)
   x.1+y.1 - 9<=w.1/\
   max (x.1+y.2.1) (x.2.1+y.1) - 9<=w.2.1/\
   max (x.1+y.2.2) (max (x.2.1+y.2.1) (x.2.2+y.1)) - 9<=w.2.2) ?_ ?_ ?_ u0 u1 u2 v0 v1 v2
 . intro a b c d e f h;simpa only [X a b c,X d e f,X (a+d - 9)] using h
 . intro a b c d e f h;simpa only [aj a b c,aj d e f,aj (a+d - 9)] using h
 . intro a b c d e f hab hbc;dsimp only;rw[af a b c hab hbc]
   have j:∀ y0 y1 y2,D d e f=(y0,y1,y2)->
       (a+y0<=a+d/\a+y0<=b+e/\a+y0<=c+f)->
       ((a+y1<=a+d/\a+y1<=b+e)\/(a+y1<=a+d/\a+y1<=c+f)\/(a+y1<=b+e/\a+y1<=c+f))->
       ((b+y0<=a+d/\b+y0<=b+e)\/(b+y0<=a+d/\b+y0<=c+f)\/(b+y0<=b+e/\b+y0<=c+f))->
       (a+y2<=a+d\/a+y2<=b+e\/a+y2<=c+f)->
       (b+y1<=a+d\/b+y1<=b+e\/b+y1<=c+f)->
       (c+y0<=a+d\/c+y0<=b+e\/c+y0<=c+f)->
       a+y0 - 9<=(D (a+d - 9) (b+e - 9) (c+f - 9)).1/\
       max (a+y1) (b+y0) - 9<=(D (a+d - 9) (b+e - 9) (c+f - 9)).2.1/\
       max (a+y2) (max (b+y1) (c+y0)) - 9<=(D (a+d - 9) (b+e - 9) (c+f - 9)).2.2:=by
     intro y0 y1 y2 _ h1 h2a h2b h3a h3b h3c;have i:∀ p q,p<=q->p - 9<=q - 9:=fun p q h=>nS h 9
     have m:∀ p q k,p - 9<=k->q - 9<=k->max p q - 9<=k:=fun p q k hp hq=>by
       rcases lZ p q with h|h <;> simp only[max_eq_right,max_eq_left,h] <;> assumption
     have n:∀ k,((k<=a+d/\k<=b+e)\/(k<=a+d/\k<=c+f)\/(k<=b+e/\k<=c+f))->k - 9<=(D (a+d-9) (b+e-9) (c+f-9)).2.1:=
       fun k h=>vJ (h.imp (fun h=>⟨i _ _ h.1,i _ _ h.2⟩) (fun h=>h.imp (fun h=>⟨i _ _ h.1,i _ _ h.2⟩) (fun h=>⟨i _ _ h.1,i _ _ h.2⟩)))
     have l:∀ k,(k<=a+d\/k<=b+e\/k<=c+f)->k - 9<=(D (a+d-9) (b+e-9) (c+f-9)).2.2:=
       fun k h=>vI (h.imp (i _ _) (fun h=>h.imp (i _ _) (i _ _)))
     exact ⟨xt (i _ _ h1.1) (i _ _ h1.2.1) (i _ _ h1.2.2),
            m _ _ _ (n _ h2a) (n _ h2b),
            m _ _ _ (l _ h3a) (m _ _ _ (l _ h3b) (l _ h3c))⟩
   rcases lZ d e with hde|hed
   . rcases lZ e f with hef|hfe
     . have i:=af d e f hde hef;rw[i]
       exact j d e f i ⟨by omega,by omega,by omega⟩ (oR (oR ⟨by omega,by omega⟩)) (oR (oR ⟨by omega,by omega⟩)) (oR (oR (by omega))) (oR (oR (by omega))) (oR (oR (by omega)))
     . rcases lZ d f with hdf|hfd
       . have i:D d e f=(d,f,e):=by rw[aj,af d f e hdf hfe]
         rw[i];exact j d f e i ⟨by omega,by omega,by omega⟩ (oR (oR ⟨by omega,by omega⟩)) (oR (oR ⟨by omega,by omega⟩)) (oR (oL (by omega))) (oR (oL (by omega))) (oR (oR (by omega)))
       . have i:D d e f=(f,d,e):=by rw[aj,X,af f d e hfd hde]
         rw[i];exact j f d e i ⟨by omega,by omega,by omega⟩ (oL ⟨by omega,by omega⟩) (oR (oR ⟨by omega,by omega⟩)) (oR (oL (by omega))) (oR (oL (by omega))) (oR (oR (by omega)))
   . rcases lZ d f with hdf|hfd
     . have i:D d e f=(e,d,f):=by rw[X,af e d f hed hdf]
       rw[i];exact j e d f i ⟨by omega,by omega,by omega⟩ (oR (oL ⟨by omega,by omega⟩)) (oR (oR ⟨by omega,by omega⟩)) (oR (oR (by omega))) (oR (oR (by omega))) (oR (oR (by omega)))
     . rcases lZ e f with hef|hfe
       . have i:D d e f=(e,f,d):=by rw[X,aj,af e f d hef hfd]
         rw[i];exact j e f d i ⟨by omega,by omega,by omega⟩ (oR (oL ⟨by omega,by omega⟩)) (oR (oR ⟨by omega,by omega⟩)) (oL (by omega)) (oR (oR (by omega))) (oR (oR (by omega)))
       . have i:D d e f=(f,e,d):=by rw[X,aj,X,af f e d hfe hed]
         rw[i];exact j f e d i ⟨by omega,by omega,by omega⟩ (oL ⟨by omega,by omega⟩) (oR (oR ⟨by omega,by omega⟩)) (oL (by omega)) (oR (oL (by omega))) (oR (oR (by omega)))
lemma gn (a b d e:Nat) (hab:a<=b) (hde:d<=e) :
 (a+e - 9)+(b+d - 9)<=(a+d - 9)+(b+e - 9):=by omega
lemma rn (u0 u1 u2 v0 v1 v2:Nat) :
   let x:=D u0 u1 u2;let y:=D v0 v1 v2
   (x.1+y.2.2 - 9)+(x.2.1+y.2.1 - 9)+(x.2.2+y.1 - 9)<=
     (u0+v0 - 9)+(u1+v1 - 9)+(u2+v2 - 9):=by
 refine jw (fun u0 u1 u2 v0 v1 v2=>
   let x:=D u0 u1 u2;let y:=D v0 v1 v2
   (x.1+y.2.2 - 9)+(x.2.1+y.2.1 - 9)+(x.2.2+y.1 - 9)<=
     (u0+v0 - 9)+(u1+v1 - 9)+(u2+v2 - 9)) ?_ ?_ ?_ u0 u1 u2 v0 v1 v2
 . intro a b c d e f h;simp only[X a b c,X d e f] at h ⊢;omega
 . intro a b c d e f h;simp only[aj a b c,aj d e f] at h ⊢;omega
 . intro a b c d e f hab hbc;dsimp only;rw[af a b c hab hbc];have i:a<=c:=lT hab hbc;rcases lZ d e with hde|hed
   . rcases lZ e f with hef|hfe
     . rw[af d e f hde hef];dsimp only
       have:=gn a c d f i (lT hde hef);omega
     . rcases lZ d f with hdf|hfd
       . rw[aj d e f,af d f e hdf hfe];dsimp only
         have:=gn a b d e hab hde;have:=gn b c d f hbc hdf;omega
       . rw[aj d e f,X d f e,af f d e hfd hde];dsimp only
         have:=gn a b d e hab hde;omega
   . rcases lZ d f with hdf|hfd
     . rw[X d e f,af e d f hed hdf];dsimp only
       have:=gn a c d f i hdf;have:=gn b c e d hbc hed;omega
     . rcases lZ e f with hef|hfe
       . rw[X d e f,aj e d f,af e f d hef hfd];dsimp only
         have:=gn b c e f hbc hef;omega
       . rw[X d e f,aj e d f,X e f d,af f e d hfe hed]
lemma fc (f:Nat->Nat) (d:∀ a b,a<=b->f a<=f b) (u0 u1 u2:Nat) :
   D (f u0) (f u1) (f u2)=(f (D u0 u1 u2).1,f (D u0 u1 u2).2.1,f (D u0 u1 u2).2.2):=by
 have h1:∀ a b c,a<=b->b<=c->D (f a) (f b) (f c)=(f a,f b,f c):=by
   intro a b c hab hbc;exact af (f a) (f b) (f c) (d a b hab) (d b c hbc)
 rcases lZ u0 u1 with h01|fT
 . rcases lZ u1 u2 with hH|gV
   . rw[af u0 u1 u2 h01 hH,h1 u0 u1 u2 h01 hH]
   . rcases lZ u0 u2 with h02|gL
     . rw[aj u0 u1 u2,aj (f u0) (f u1) (f u2),af u0 u2 u1 h02 gV,h1 u0 u2 u1 h02 gV]
     . rw[aj u0 u1 u2,X u0 u2 u1,aj (f u0) (f u1) (f u2),X (f u0) (f u2) (f u1),
         af u2 u0 u1 gL h01,h1 u2 u0 u1 gL h01]
 . rcases lZ u0 u2 with h02|gL
   . rw[X u0 u1 u2,X (f u0) (f u1) (f u2),af u1 u0 u2 fT h02,h1 u1 u0 u2 fT h02]
   . rcases lZ u1 u2 with hH|gV
     . rw[X u0 u1 u2,aj u1 u0 u2,X (f u0) (f u1) (f u2),aj (f u1) (f u0) (f u2),
         af u1 u2 u0 hH gL,h1 u1 u2 u0 hH gL]
     . rw[X u0 u1 u2,aj u1 u0 u2,X u1 u2 u0,
         X (f u0) (f u1) (f u2),aj (f u1) (f u0) (f u2),X (f u1) (f u2) (f u0),
         af u2 u1 u0 gV fT,h1 u2 u1 u0 gV fT]
lemma gO (c d b a:Nat) :
  (d - c)+(b - c)+(a - c) =
  ((D d b a).1 - c)+((D d b a).2.1 - c)+((D d b a).2.2 - c):=by
 have h:=fc (fun t=>t - c) (fun x y hxy=>by omega) d b a;have i:=cr (d - c) (b - c) (a - c);rw[h] at i;exact i.symm
def al (b:Bool):Nat:=if b then 1 else 0
def Y (M:Fin 3->Fin 3->Bool) (r:Fin 3):Nat:=al (M r 0)+al (M r 1)+al (M r 2)
def aQ (M:Fin 3->Fin 3->Bool) (c:Fin 3):Nat:=al (M 0 c)+al (M 1 c)+al (M 2 c)
def gz (M:Fin 3->Fin 3->Bool):Nat:=Y M 0+Y M 1+Y M 2
lemma gM (M:Fin 3->Fin 3->Bool):gz M=aQ M 0+aQ M 1+aQ M 2:=by
 unfold gz Y aQ;omega
lemma gC (M:Fin 3->Fin 3->Bool) (r:Fin 3):Y M r<=3:=by
 unfold Y;cases M r 0 <;> cases M r 1 <;> cases M r 2 <;> simp[al]
lemma fN (M:Fin 3->Fin 3->Bool) (r c:Fin 3) (h:M r c=true):1<=Y M r:=by
 unfold Y
 have a:c=0\/c=1\/c=2:=by fin_cases c <;> simp
 rcases a with rfl|rfl|rfl <;> (simp only[al,h,↓reduceIte];omega)
lemma iU (M:Fin 3->Fin 3->Bool) (r c:Fin 3) (h:M r c=true):1<=aQ M c:=by
 unfold aQ
 have a:r=0\/r=1\/r=2:=by fin_cases r <;> simp
 rcases a with rfl|rfl|rfl <;> (simp only[al,h,↓reduceIte];omega)
lemma iu (M N:Fin 3->Fin 3->Bool) (r:Fin 3) :
   Y (fun x y=>M x y&&N x y) r<=
     (if aQ M 0=0 then 0 else 1)+(if aQ M 1=0 then 0 else 1)+(if aQ M 2=0 then 0 else 1):=by
 have a:∀ c:Fin 3,al (M r c&&N r c)<=if aQ M c=0 then 0 else 1:=by
   intro c;cases h1:M r c <;> cases N r c
   . simp[al]
   . simp[al]
   . simp[al]
   . have:=iU M r c h1;simp[al];split_ifs <;> omega
 have h0:=a 0;have h1:=a 1;have h2:=a 2;unfold Y;dsimp only;omega
lemma jT (f:Nat->Nat) (a b c:Nat) :
   f (D a b c).1+f (D a b c).2.1+f (D a b c).2.2=f a+f b+f c:=by
 rcases lZ a b with hab|hba
 . rcases lZ b c with hbc|hcb
   . rw[af a b c hab hbc]
   . rcases lZ a c with hac|hca
     . rw[aj a b c,af a c b hac hcb];dsimp only;omega
     . rw[aj a b c,X a c b,af c a b hca hab];dsimp only;omega
 . rcases lZ a c with hac|hca
   . rw[X a b c,af b a c hba hac];dsimp only;omega
   . rcases lZ b c with hbc|hcb
     . rw[X a b c,aj b a c,af b c a hbc hca];dsimp only;omega
     . rw[X a b c,aj b a c,X b c a,af c b a hcb hba];dsimp only;omega
lemma ds (a b c:Nat) :
  (if a=0 then 1 else 0)+(if b=0 then 1 else 0)+(if c=0 then 1 else 0) =
  (if (D a b c).1=0 then 1 else 0)+(if (D a b c).2.1=0 then 1 else 0)+(if (D a b c).2.2=0 then 1 else 0):=
 (jT (fun t=>if t=0 then 1 else 0) a b c).symm
lemma la (a b c:Nat) :
  (if a=0 then 0 else 1)+(if b=0 then 0 else 1)+(if c=0 then 0 else 1) =
  (if (D a b c).1=0 then 0 else 1)+(if (D a b c).2.1=0 then 0 else 1)+(if (D a b c).2.2=0 then 0 else 1):=
 (jT (fun t=>if t=0 then 0 else 1) a b c).symm
lemma lP (M N:Fin 3->Fin 3->Bool) :
   gz (fun r c=>M r c||N r c) +
     ((if Y M 0=0 then 1 else 0)+(if Y M 1=0 then 1 else 0)+(if Y M 2=0 then 1 else 0)) *
     ((if aQ N 0=0 then 1 else 0)+(if aQ N 1=0 then 1 else 0)+(if aQ N 2=0 then 1 else 0))<=9:=by
 have a:∀ r c:Fin 3,
     al (M r c||N r c)+(if Y M r=0 then 1 else 0)*(if aQ N c=0 then 1 else 0)<=1:=by
   intro r c;cases h1:M r c <;> cases h2:N r c
   . simp only[Bool.or_self,al,bF,↓reduceIte,Nat.zero_add];split_ifs <;> omega
   . have:=iU N r c h2;simp only[bFO,al,↓reduceIte];split_ifs <;> omega
   . have:=fN M r c h1;simp only[Bool.true_or,al,↓reduceIte];split_ifs <;> omega
   . have:=fN M r c h1;simp only[Bool.true_or,al,↓reduceIte];split_ifs <;> omega
 have h00:=a 0 0;have h01:=a 0 1;have h02:=a 0 2;have fT:=a 1 0;have kG:=a 1 1;have hH:=a 1 2;have gL:=a 2 0;have gV:=a 2 1;have jW:=a 2 2;set r0:=if Y M 0=0 then 1 else 0;set r1:=if Y M 1=0 then 1 else 0;set r2:=if Y M 2=0 then 1 else 0;set h:=if aQ N 0=0 then 1 else 0;set d:=if aQ N 1=0 then 1 else 0;set b:=if aQ N 2=0 then 1 else 0
 have hmul:(r0+r1+r2)*(h+d+b) =
     r0*h+r0*d+r0*b+r1*h+r1*d+r1*b+r2*h+r2*d+r2*b:=by ring
 unfold gz;simp only[Y];linarith
lemma eK (M N:Fin 3->Fin 3->Bool) (b d:Fin 3->Bool) :
  gz (fun r c=>M r c&&N r c)<=
   (al (b 0)+al (b 1)+al (b 2))*(al (d 0)+al (d 1)+al (d 2)) +
   (if b 0 then 0 else Y M 0)+(if b 1 then 0 else Y M 1)+(if b 2 then 0 else Y M 2) +
   (if d 0 then 0 else aQ N 0)+(if d 1 then 0 else aQ N 1)+(if d 2 then 0 else aQ N 2):=by
 have a:∀ r c:Fin 3,
   al (M r c&&N r c)<=al (b r)*al (d c)+(if b r then 0 else al (M r c))+(if d c then 0 else al (N r c)):=by
  intro r c;cases b r <;> cases d c <;> cases M r c <;> cases N r c <;> simp[al]
 have h:∀ r:Fin 3,(if b r then 0 else Y M r) =
   (if b r then 0 else al (M r 0))+(if b r then 0 else al (M r 1))+(if b r then 0 else al (M r 2)):=by
  intro r;cases b r <;> simp[Y]
 have i:∀ c:Fin 3,(if d c then 0 else aQ N c) =
   (if d c then 0 else al (N 0 c))+(if d c then 0 else al (N 1 c))+(if d c then 0 else al (N 2 c)):=by
  intro c;cases d c <;> simp[aQ]
 have h00:=a 0 0;have h01:=a 0 1;have h02:=a 0 2;have fT:=a 1 0;have kG:=a 1 1;have hH:=a 1 2;have gL:=a 2 0;have gV:=a 2 1;have jW:=a 2 2
 have hmul:(al (b 0)+al (b 1)+al (b 2))*(al (d 0)+al (d 1)+al (d 2)) =
   al (b 0)*al (d 0)+al (b 0)*al (d 1)+al (b 0)*al (d 2) +
   al (b 1)*al (d 0)+al (b 1)*al (d 1)+al (b 1)*al (d 2) +
   al (b 2)*al (d 0)+al (b 2)*al (d 1)+al (b 2)*al (d 2):=by ring
 rw[h 0,h 1,h 2,i 0,i 1,i 2];unfold gz;simp only[Y];linarith
lemma j2 (u:Fin 3->Nat) :
   ∃ ind:Fin 3->Bool,al (ind 0)+al (ind 1)+al (ind 2)=1/\
     (if ind 0 then 0 else u 0)+(if ind 1 then 0 else u 1)+(if ind 2 then 0 else u 2) =
     (D (u 0) (u 1) (u 2)).1+(D (u 0) (u 1) (u 2)).2.1/\
     (if ind 0 then u 0 else 0)+(if ind 1 then u 1 else 0)+(if ind 2 then u 2 else 0) =
     (D (u 0) (u 1) (u 2)).2.2:=by
 have hsum:=cr (u 0) (u 1) (u 2);rcases lZ (u 0) (u 1) with h01|fT
 . rcases lZ (u 1) (u 2) with hH|gV
   . refine ⟨fun i=>decide (i=2),by decide,?_,?_⟩ <;> (simp[af (u 0) (u 1) (u 2) h01 hH])
   . refine ⟨fun i=>decide (i=1),by decide,?_,?_⟩
     . simp only[dE,Fin.isValue,Fin.reduceEq,↓reduceIte]
       have:(D (u 0) (u 1) (u 2)).2.2=u 1:=by simp[D,aG,aP];omega
       omega
     . simp only[dE,Fin.isValue,Fin.reduceEq,↓reduceIte];simp[D,aG,aP];omega
 . rcases lZ (u 0) (u 2) with h02|gL
   . refine ⟨fun i=>decide (i=2),by decide,?_,?_⟩
     . simp only[dE,Fin.isValue,Fin.reduceEq,↓reduceIte]
       have:(D (u 0) (u 1) (u 2)).2.2=u 2:=by simp[D,aG,aP];omega
       omega
     . simp only[dE,Fin.isValue,Fin.reduceEq,↓reduceIte];simp[D,aG,aP];omega
   . refine ⟨fun i=>decide (i=0),by decide,?_,?_⟩
     . simp only[dE,Fin.isValue,Fin.reduceEq,↓reduceIte]
       have:(D (u 0) (u 1) (u 2)).2.2=u 0:=by simp[D,aG,aP];omega
       omega
     . simp only[dE,Fin.isValue,Fin.reduceEq,↓reduceIte];simp[D,aG,aP];omega
lemma j1 (u:Fin 3->Nat) :
   ∃ ind:Fin 3->Bool,al (ind 0)+al (ind 1)+al (ind 2)=2/\
     (if ind 0 then 0 else u 0)+(if ind 1 then 0 else u 1)+(if ind 2 then 0 else u 2) =
     (D (u 0) (u 1) (u 2)).1/\
     (if ind 0 then u 0 else 0)+(if ind 1 then u 1 else 0)+(if ind 2 then u 2 else 0) =
     (D (u 0) (u 1) (u 2)).2.1+(D (u 0) (u 1) (u 2)).2.2:=by
 have hsum:=cr (u 0) (u 1) (u 2);rcases lZ (u 0) (u 1) with h01|fT
 . rcases lZ (u 0) (u 2) with h02|gL
   . refine ⟨fun i=>decide (i ≠ 0),by decide,?_,?_⟩
     . simp only[ne_eq,dE,not_true_eq_false,↓reduceIte,Fin.isValue,Fin.reduceEq,not_false_eq_true];simp[D,aG,aP];omega
     . simp only[ne_eq,dE,not_true_eq_false,↓reduceIte,Fin.isValue,Fin.reduceEq,not_false_eq_true]
       have:(D (u 0) (u 1) (u 2)).1=u 0:=by simp[D,aG,aP];omega
       omega
   . refine ⟨fun i=>decide (i ≠ 2),by decide,?_,?_⟩
     . simp only[ne_eq,dE,Fin.isValue,Fin.reduceEq,not_false_eq_true,↓reduceIte,not_true_eq_false];simp[D,aG,aP];omega
     . simp only[ne_eq,dE,Fin.isValue,Fin.reduceEq,not_false_eq_true,↓reduceIte,not_true_eq_false]
       have:(D (u 0) (u 1) (u 2)).1=u 2:=by simp[D,aG,aP];omega
       omega
 . rcases lZ (u 1) (u 2) with hH|gV
   . refine ⟨fun i=>decide (i ≠ 1),by decide,?_,?_⟩
     . simp only[ne_eq,dE,Fin.isValue,Fin.reduceEq,not_false_eq_true,↓reduceIte,not_true_eq_false];simp[D,aG,aP];omega
     . simp only[ne_eq,dE,Fin.isValue,Fin.reduceEq,not_false_eq_true,↓reduceIte,not_true_eq_false]
       have:(D (u 0) (u 1) (u 2)).1=u 1:=by simp[D,aG,aP];omega
       omega
   . refine ⟨fun i=>decide (i ≠ 2),by decide,?_,?_⟩
     . simp only[ne_eq,dE,Fin.isValue,Fin.reduceEq,not_false_eq_true,↓reduceIte,not_true_eq_false];simp[D,aG,aP];omega
     . simp only[ne_eq,dE,Fin.isValue,Fin.reduceEq,not_false_eq_true,↓reduceIte,not_true_eq_false]
       have:(D (u 0) (u 1) (u 2)).1=u 2:=by simp[D,aG,aP];omega
       omega
def g7 (r0 r1 r2 c0 c1 c2:Nat):Nat:=
 av (r0+r1+r2) (av (c0+c1+c2) (av (r0+r1+c0+c1+1) (av (r0+r1+c0+2) (av (r0+c0+c1+2) (r0+c0+4)))))
lemma io (M N:Fin 3->Fin 3->Bool) :
  let a:=D (Y M 0) (Y M 1) (Y M 2)
  let b:=D (aQ N 0) (aQ N 1) (aQ N 2)
  gz (fun r c=>M r c&&N r c)<=g7 a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2:=by
 dsimp only;unfold g7;simp only[aG];rcases j2 (Y M) with ⟨ir1,hir1_c,hir1_o,_⟩;rcases j1 (Y M) with ⟨ir2,hir2_c,hir2_o,_⟩;rcases j2 (aQ N) with ⟨ic1,hic1_c,hic1_o,_⟩;rcases j1 (aQ N) with ⟨ic2,hic2_c,hic2_o,_⟩;have kG:=eK M N ir1 ic1;have hH:=eK M N ir1 ic2;have gV:=eK M N ir2 ic1;have jW:=eK M N ir2 ic2;have d:=eK M N (fun _=>false) (fun _=>true);have xG:=eK M N (fun _=>true) (fun _=>false);have hsr:=cr (Y M 0) (Y M 1) (Y M 2);have hsc:=cr (aQ N 0) (aQ N 1) (aQ N 2);simp[al] at d xG;rw[hir1_c,hic1_c] at kG;rw[hir1_c,hic2_c] at hH;rw[hir2_c,hic1_c] at gV;rw[hir2_c,hic2_c] at jW;refine lM (by linarith) (lM (by linarith) (lM (by linarith) (lM (by linarith) (lM (by linarith) (by linarith)))))
def aq (P:Fin 3->Fin 3->Fin 3->Bool) (a b:Fin 3):Nat:=
 al (P a b 0)+al (P a b 1)+al (P a b 2)
def A (P:Fin 3->Fin 3->Fin 3->Bool) (a:Fin 3):Nat:=
 aq P a 0+aq P a 1+aq P a 2
def Z (P:Fin 3->Fin 3->Fin 3->Bool) (b:Fin 3):Nat:=
 aq P 0 b+aq P 1 b+aq P 2 b
def aK (P:Fin 3->Fin 3->Fin 3->Bool) (c:Fin 3):Nat:=
 A (fun z x y=>P x y z) c
def cU (P:Fin 3->Fin 3->Fin 3->Bool):Nat:=
 A P 0+A P 1+A P 2
lemma dw (P:Fin 3->Fin 3->Fin 3->Bool) (a b:Fin 3):aq P a b<=3:=by
 unfold aq;cases P a b 0 <;> cases P a b 1 <;> cases P a b 2 <;> simp[al]
lemma bS (P:Fin 3->Fin 3->Fin 3->Bool) (a:Fin 3):A P a<=9:=by
 unfold A;have:=dw P a 0;have:=dw P a 1;have:=dw P a 2;omega
lemma zi (P:Fin 3->Fin 3->Fin 3->Bool):cU P<=27:=by
 unfold cU;have:=bS P 0;have:=bS P 1;have:=bS P 2;omega
lemma fD (P:Fin 3->Fin 3->Fin 3->Bool) (a b:Fin 3) :
  Z P b - 6<=aq P a b:=by
 unfold Z;have h0:=dw P 0 b;have h1:=dw P 1 b;have h2:=dw P 2 b
 have c:a=0\/a=1\/a=2:=by fin_cases a <;> simp
 rcases c with rfl|rfl|rfl <;> omega
lemma gc (P:Fin 3->Fin 3->Fin 3->Bool) (a:Fin 3) :
  (Z P 0 - 6)+(Z P 1 - 6)+(Z P 2 - 6)<=A P a:=by
 unfold A;have h0:=fD P a 0;have h1:=fD P a 1;have h2:=fD P a 2;omega
lemma dP (P Q:Fin 3->Fin 3->Fin 3->Bool) (a b:Fin 3) :
  A P a+Z Q b - 15<=aq (fun x y z=>P x y z&&Q x y z) a b:=by
 have hL:aq P a b+aq Q a b - 3<=aq (fun x y z=>P x y z&&Q x y z) a b:=by
  unfold aq
  have c:∀ k:Fin 3,al (P a b k)+al (Q a b k)<=al (P a b k&&Q a b k)+1:=by
   intro k;cases P a b k <;> cases Q a b k <;> simp[al]
  have c0:=c 0;have c1:=c 1;have c2:=c 2;dsimp only;omega
 have hp:A P a - 6<=aq P a b:=by
  unfold A;have h0:=dw P a 0;have h1:=dw P a 1;have h2:=dw P a 2
  have d:b=0\/b=1\/b=2:=by fin_cases b <;> simp
  rcases d with rfl|rfl|rfl <;> omega
 have hq:=fD Q a b;omega
lemma df (P Q:Fin 3->Fin 3->Fin 3->Bool) (h d:Fin 3->Bool) :
  (if h 0 then A P 0 else 0)+(if h 1 then A P 1 else 0)+(if h 2 then A P 2 else 0) +
  (if d 0 then Z Q 0 else 0)+(if d 1 then Z Q 1 else 0)+(if d 2 then Z Q 2 else 0) -
  3*(al (h 0)+al (h 1)+al (h 2))*(al (d 0)+al (d 1)+al (d 2))<=
  cU (fun x y z=>P x y z||Q x y z):=by
 have c:∀ a b:Fin 3,
   (if h a then aq P a b else 0)+(if d b then aq Q a b else 0)<=
   aq (fun x y z=>P x y z||Q x y z) a b+3*al (h a)*al (d b):=by
  intro a b
  have i:∀ k:Fin 3,al (P a b k)+al (Q a b k)<=al (P a b k||Q a b k)+1:=by
   intro k;cases P a b k <;> cases Q a b k <;> simp[al]
  have l:∀ k:Fin 3,al (P a b k)<=al (P a b k||Q a b k):=by
   intro k;cases P a b k <;> cases Q a b k <;> simp[al]
  have j:∀ k:Fin 3,al (Q a b k)<=al (P a b k||Q a b k):=by
   intro k;cases P a b k <;> cases Q a b k <;> simp[al]
  have h0:=i 0;have h1:=i 1;have h2:=i 2;have p0:=l 0;have p1:=l 1;have p2:=l 2;have q0:=j 0;have q1:=j 1;have q2:=j 2;cases h a <;> cases d b <;> unfold aq <;> simp only[↓reduceIte,bF,al] at*<;> omega
 have n:∀ a:Fin 3,(if h a then A P a else 0) =
   (if h a then aq P a 0 else 0)+(if h a then aq P a 1 else 0)+(if h a then aq P a 2 else 0):=by
  intro a;cases h a <;> simp[A]
 have m:∀ b:Fin 3,(if d b then Z Q b else 0) =
   (if d b then aq Q 0 b else 0)+(if d b then aq Q 1 b else 0)+(if d b then aq Q 2 b else 0):=by
  intro b;cases d b <;> simp[Z]
 have h00:=c 0 0;have h01:=c 0 1;have h02:=c 0 2;have fT:=c 1 0;have kG:=c 1 1;have hH:=c 1 2;have gL:=c 2 0;have gV:=c 2 1;have jW:=c 2 2
 have hmul:3*(al (h 0)+al (h 1)+al (h 2))*(al (d 0)+al (d 1)+al (d 2)) =
   3*al (h 0)*al (d 0)+3*al (h 0)*al (d 1)+3*al (h 0)*al (d 2) +
   3*al (h 1)*al (d 0)+3*al (h 1)*al (d 1)+3*al (h 1)*al (d 2) +
   3*al (h 2)*al (d 0)+3*al (h 2)*al (d 1)+3*al (h 2)*al (d 2):=by ring
 apply nF;rw[n 0,n 1,n 2,m 0,m 1,m 2];unfold cU A;linarith
def dm (x0 x1 x2 y0 y1 y2:Nat):Nat:=
 aa (x0+x1+x2) (aa (y0+y1+y2) (aa (x2+y2-3) (aa (x2+y1+y2-6) (aa (x1+x2+y2-6) (x1+x2+y1+y2-12)))))
lemma p5 (P Q:Fin 3->Fin 3->Fin 3->Bool) :
  let b:=D (A P 0) (A P 1) (A P 2)
  let a:=D (Z Q 0) (Z Q 1) (Z Q 2)
  dm b.1 b.2.1 b.2.2 a.1 a.2.1 a.2.2<=cU (fun x y z=>P x y z||Q x y z):=by
 dsimp only;unfold dm;simp only[aP];rcases j2 (A P) with ⟨ia1,hia1_c,_,hia1_i⟩;rcases j1 (A P) with ⟨ia2,hia2_c,_,hia2_i⟩;rcases j2 (Z Q) with ⟨ib1,hib1_c,_,hib1_i⟩;rcases j1 (Z Q) with ⟨ib2,hib2_c,_,hib2_i⟩;have kG:=df P Q ia1 ib1;have hH:=df P Q ia1 ib2;have gV:=df P Q ia2 ib1;have jW:=df P Q ia2 ib2;have xG:=df P Q (fun _=>true) (fun _=>false);have c:=df P Q (fun _=>false) (fun _=>true);have hsx:=cr (A P 0) (A P 1) (A P 2);have hsy:=cr (Z Q 0) (Z Q 1) (Z Q 2);simp[al] at xG c;rw[hia1_c,hib1_c] at kG;rw[hia1_c,hib2_c] at hH;rw[hia2_c,hib1_c] at gV;rw[hia2_c,hib2_c] at jW
 refine xL (by linarith) (xL (by linarith)
  (xL (lT (nS (by linarith) 3) kG)
  (xL (lT (nS (by linarith) 6) hH)
  (xL (lT (nS (by linarith) 6) gV)
   (lT (nS (by linarith) 12) jW)))))
def d5 (x0 x1 x2 y0 y1 y2:Nat):Nat:=
 cond (nB (x2+y2) 15) 0
 ((x0+y0-15)+(x0+y1-15)+(x0+y2-15)+(x1+y0-15)+(x1+y1-15)+(x1+y2-15)+(x2+y0-15)+(x2+y1-15)+(x2+y2-15))
lemma o7 (P Q:Fin 3->Fin 3->Fin 3->Bool) :
  let i:=D (A P 0) (A P 1) (A P 2)
  let c:=D (Z Q 0) (Z Q 1) (Z Q 2)
  d5 i.1 i.2.1 i.2.2 c.1 c.2.1 c.2.2<=cU (fun x y z=>P x y z&&Q x y z):=by
 dsimp only;unfold d5;cases nB _ 15
 swap;· simp only[bT];exact Nat.zero_le _
 simp only[bC]
 have h:∀ a:Fin 3,(A P a+(D (Z Q 0) (Z Q 1) (Z Q 2)).1 - 15) +
   (A P a+(D (Z Q 0) (Z Q 1) (Z Q 2)).2.1 - 15) +
   (A P a+(D (Z Q 0) (Z Q 1) (Z Q 2)).2.2 - 15)<=
   A (fun x y z=>P x y z&&Q x y z) a:=by
  intro a;have h0:=dP P Q a 0;have h1:=dP P Q a 1;have h2:=dP P Q a 2;have n:=fc (fun t=>A P a+t - 15) (fun x y hxy=>by omega) (Z Q 0) (Z Q 1) (Z Q 2);have b:=cr (A P a+Z Q 0 - 15) (A P a+Z Q 1 - 15) (A P a+Z Q 2 - 15);rw[n] at b;dsimp only at b
  have j:A (fun x y z=>P x y z&&Q x y z) a =
    aq (fun x y z=>P x y z&&Q x y z) a 0+aq (fun x y z=>P x y z&&Q x y z) a 1 +
    aq (fun x y z=>P x y z&&Q x y z) a 2:=rfl
  rw[j,b];exact nA (nA h0 h1) h2
 set c:=D (Z Q 0) (Z Q 1) (Z Q 2)
 have r:=fc (fun t=>(t+c.1 - 15)+(t+c.2.1 - 15)+(t+c.2.2 - 15))
  (fun x y hxy=>nA (nA (nS (Nat.add_le_add_right hxy _) _)
   (nS (Nat.add_le_add_right hxy _) _)) (nS (Nat.add_le_add_right hxy _) _))
  (A P 0) (A P 1) (A P 2)
 have b:=cr
  ((A P 0+c.1 - 15)+(A P 0+c.2.1 - 15)+(A P 0+c.2.2 - 15))
  ((A P 1+c.1 - 15)+(A P 1+c.2.1 - 15)+(A P 1+c.2.2 - 15))
  ((A P 2+c.1 - 15)+(A P 2+c.2.1 - 15)+(A P 2+c.2.2 - 15))
 rw[r] at b;dsimp only at b;have m:=h 0;have l:=h 1;have k:=h 2;unfold cU;have d:=nA (nA m l) k;rw[<- b] at d;exact lT (by linarith) d
lemma cZ (P Q:Fin 3->Fin 3->Fin 3->Bool) :
  let d:=D (A P 0) (A P 1) (A P 2)
  let b:=D (Z Q 0) (Z Q 1) (Z Q 2)
  let i:=D (A (fun x y z=>P x y z&&Q x y z) 0)
     (A (fun x y z=>P x y z&&Q x y z) 1)
     (A (fun x y z=>P x y z&&Q x y z) 2)
  (d.1+b.1 - 15)+(d.1+b.2.1 - 15)+(d.1+b.2.2 - 15)<=i.1/\
  (d.2.1+b.1 - 15)+(d.2.1+b.2.1 - 15)+(d.2.1+b.2.2 - 15)<=i.2.1/\
  (d.2.2+b.1 - 15)+(d.2.2+b.2.1 - 15)+(d.2.2+b.2.2 - 15)<=i.2.2:=by
 dsimp only;set b:=D (Z Q 0) (Z Q 1) (Z Q 2);let fn:=fun t=>(t+b.1 - 15)+(t+b.2.1 - 15)+(t+b.2.2 - 15)
 have h:∀ a:Fin 3,fn (A P a)<=A (fun x y z=>P x y z&&Q x y z) a:=by
  intro a;dsimp[fn];have h0:=dP P Q a 0;have h1:=dP P Q a 1;have h2:=dP P Q a 2;have l:=fc (fun t=>A P a+t - 15) (fun x y hxy=>by omega) (Z Q 0) (Z Q 1) (Z Q 2);have c:=cr (A P a+Z Q 0 - 15) (A P a+Z Q 1 - 15) (A P a+Z Q 2 - 15);rw[l] at c;dsimp only[b] at c ⊢
  have j:A (fun x y z=>P x y z&&Q x y z) a =
    aq (fun x y z=>P x y z&&Q x y z) a 0+aq (fun x y z=>P x y z&&Q x y z) a 1 +
    aq (fun x y z=>P x y z&&Q x y z) a 2:=rfl
  rw[j,c];exact nA (nA h0 h1) h2
 have k:=cM (h 0) (h 1) (h 2)
 have m:=fc fn (fun x y hxy=>nA (nA (nS (Nat.add_le_add_right hxy _) _)
   (nS (Nat.add_le_add_right hxy _) _)) (nS (Nat.add_le_add_right hxy _) _))
  (A P 0) (A P 1) (A P 2)
 rw[m] at k;exact k
lemma pX (M1 M2:Fin 3->Fin 3->Bool) (P1 P2:Fin 3->Fin 3->Fin 3->Bool)
   (eW:∀ k:Fin 3,A P1 k=9->Y M1 k=0)
   (fj:∀ k:Fin 3,A P2 k=9->Y M2 k=0)
   (j i:Nat)
   (hnp:j<=(if A P1 0=9 then 1 else 0)+(if A P1 1=9 then 1 else 0)+(if A P1 2=9 then 1 else 0))
   (hnq:i<=(if A P2 0=9 then 1 else 0)+(if A P2 1=9 then 1 else 0)+(if A P2 2=9 then 1 else 0)) :
   (9<=(D (A (fun x y z=>P1 x y z&&P2 x y z) 0)
                (A (fun x y z=>P1 x y z&&P2 x y z) 1)
                (A (fun x y z=>P1 x y z&&P2 x y z) 2)).2.2/\
    9<=cU (fun x y z=>P1 x y z&&P2 x y z))\/
   (let a:=D (Y (fun r c=>M1 r c&&M2 r c) 0)
                    (Y (fun r c=>M1 r c&&M2 r c) 1)
                    (Y (fun r c=>M1 r c&&M2 r c) 2)
    let w:=D (aQ (fun r c=>M1 r c&&M2 r c) 0)
                    (aQ (fun r c=>M1 r c&&M2 r c) 1)
                    (aQ (fun r c=>M1 r c&&M2 r c) 2)
    (if 1<=j+i then a.1=0 else True)/\
    (if 2<=j+i then a.2.1=0 else True)/\
    (if 3<=j+i then a.2.2=0 else True)/\
    w.1<=3 - (j+i)/\w.2.1<=3 - (j+i)/\w.2.2<=3 - (j+i)):=by
 by_cases hsh:∃ k:Fin 3,A P1 k=9/\A P2 k=9
 . left;rcases hsh with ⟨k,hk1,hk2⟩
   have hfull:A (fun x y z=>P1 x y z&&P2 x y z) k=9:=by
     have hge:A P1 k+A P2 k - 9<=A (fun x y z=>P1 x y z&&P2 x y z) k:=by
       have K:∀ b:Fin 3,aq P1 k b+aq P2 k b - 3<=aq (fun x y z=>P1 x y z&&P2 x y z) k b:=by
         intro b;unfold aq
         have c:∀ z:Fin 3,al (P1 k b z)+al (P2 k b z)<=al (P1 k b z&&P2 k b z)+1:=by
           intro z;cases P1 k b z <;> cases P2 k b z <;> simp[al]
         have:=c 0;have:=c 1;have:=c 2;dsimp only;omega
       have l0:=K 0;have l1:=K 1;have l2:=K 2;unfold A;omega
     have hle:=bS (fun x y z=>P1 x y z&&P2 x y z) k;omega
   have hmax:A (fun x y z=>P1 x y z&&P2 x y z) k<=
       (D (A (fun x y z=>P1 x y z&&P2 x y z) 0)
              (A (fun x y z=>P1 x y z&&P2 x y z) 1)
              (A (fun x y z=>P1 x y z&&P2 x y z) 2)).2.2:=by
     have m:k=0\/k=1\/k=2:=by fin_cases k <;> simp
     rcases m with rfl|rfl|rfl <;> (simp only[D,aG,aP];omega)
   have htot:A (fun x y z=>P1 x y z&&P2 x y z) k<=cU (fun x y z=>P1 x y z&&P2 x y z):=by
     have m:k=0\/k=1\/k=2:=by fin_cases k <;> simp
     rcases m with rfl|rfl|rfl <;> (unfold cU;omega)
   omega
 . right;have hsh':∀ k:Fin 3,A P1 k=9->A P2 k ≠ 9:=fun k h1 h2=>hsh ⟨k,h1,h2⟩
   have M:∀ k:Fin 3,(A P1 k=9\/A P2 k=9)->Y (fun r c=>M1 r c&&M2 r c) k=0:=by
     intro k m
     have hle1:Y (fun r c=>M1 r c&&M2 r c) k<=Y M1 k:=by
       unfold Y
       have t:∀ c,al (M1 k c&&M2 k c)<=al (M1 k c):=fun c=>by cases M1 k c <;> cases M2 k c <;> simp[al]
       have:=t 0;have:=t 1;have:=t 2;dsimp only;omega
     have hle2:Y (fun r c=>M1 r c&&M2 r c) k<=Y M2 k:=by
       unfold Y
       have t:∀ c,al (M1 k c&&M2 k c)<=al (M2 k c):=fun c=>by cases M1 k c <;> cases M2 k c <;> simp[al]
       have:=t 0;have:=t 1;have:=t 2;dsimp only;omega
     rcases m with h1|h2
     . have:=eW k h1;omega
     . have:=fj k h2;omega
   let r0:=Y (fun r c=>M1 r c&&M2 r c) 0;let r1:=Y (fun r c=>M1 r c&&M2 r c) 1;let r2:=Y (fun r c=>M1 r c&&M2 r c) 2
   have u:(if r0=0 then 1 else 0)+(if r1=0 then 1 else 0)+(if r2=0 then 1 else 0) ≥ j+i:=by
     have m:∀ k:Fin 3,(if A P1 k=9 then 1 else 0)+(if A P2 k=9 then 1 else 0)<=
         if Y (fun r c=>M1 r c&&M2 r c) k=0 then 1 else 0:=by
       intro k
       by_cases h1:A P1 k=9
       . have h2:A P2 k ≠ 9:=hsh' k h1;have F:=M k (oL h1);simp[h1,h2,F]
       . by_cases h2:A P2 k=9
         . have F:=M k (oR h2);simp[h1,h2,F]
         . simp[h1,h2]
     have k0:=m 0;have k1:=m 1;have k2:=m 2;dsimp only[r0,r1,r2];omega
   have C:=ds r0 r1 r2
   have l:∀ c:Fin 3,aQ (fun r c=>M1 r c&&M2 r c) c<=3 - (j+i):=by
     intro c
     have h:∀ r:Fin 3,al (M1 r c&&M2 r c)+(if Y (fun x y=>M1 x y&&M2 x y) r=0 then 1 else 0)<=1:=by
       intro r;cases h1:M1 r c&&M2 r c
       . simp only[al,bF,↓reduceIte,Nat.zero_add];split_ifs <;> omega
       . have:=fN (fun x y=>M1 x y&&M2 x y) r c h1
         simp only[al,↓reduceIte];split_ifs <;> omega
     have c0:=h 0;have c1:=h 1;have c2:=h 2;unfold aQ;dsimp only;dsimp only[r0,r1,r2] at u;omega
   have n:=l 0;have v:=l 1;have L:=l 2;have hcs:=jS r0 r1 r2;set a:=D r0 r1 r2
   have d:(if a.1=0 then 1 else 0)+(if a.2.1=0 then 1 else 0)+(if a.2.2=0 then 1 else 0) ≥ j+i:=by
     rw[<- C];exact u
   dsimp only
   change (if 1<=j+i then a.1=0 else True)/\
     (if 2<=j+i then a.2.1=0 else True)/\
     (if 3<=j+i then a.2.2=0 else True)/\_
   refine ⟨?_,?_,?_,?_,?_,?_⟩
   . split_ifs
     by_cases h0:a.1=0
     . exact h0
     . exfalso;have h1:a.2.1 ≠ 0:=by omega
       have h2:a.2.2 ≠ 0:=by omega
       simp[h0,h1,h2] at d;omega
   . split_ifs
     by_cases h1:a.2.1=0
     . exact h1
     . exfalso;have h2:a.2.2 ≠ 0:=by omega
       by_cases h0:a.1=0 <;> simp[h0,h1,h2] at d <;> omega
   . split_ifs
     by_cases h2:a.2.2=0
     . exact h2
     . exfalso
       by_cases h0:a.1=0 <;> by_cases h1:a.2.1=0 <;> simp[h0,h1,h2] at d <;> omega
   . exact lH (oL n)
   . exact kz (oL ⟨n,v⟩)
   . exact gQ n v L
abbrev iN:=Nat × Nat
abbrev AS:=Nat × Nat × Nat × Nat
abbrev RS:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
abbrev RL:=RS × Nat
def ao (mA:Nat) (e:Fin 5) (k1 k2:Fin 3):Bool:=
 mA.testBit (9*e.val+3*k1.val+k2.val)
def B (mB:Nat) (s:Fin 5) (a b c:Fin 3):Bool:=
 mB.testBit (27*s.val+9*a.val+3*b.val+c.val)
def am (mA:Nat) (e:Fin 5) (k:Fin 3):Nat:=Y (ao mA e) k
def aR (mA:Nat) (e:Fin 5) (k:Fin 3):Nat:=aQ (ao mA e) k
def bk (mA:Nat) (e:Fin 5):Nat:=gz (ao mA e)
def S (mB:Nat) (s:Fin 5) (ax k:Fin 3):Nat:=
 match ax.val with
 | 0=>A (B mB s) k
 | 1=>Z (B mB s) k
 | _=>aK (B mB s) k
def cw (mB:Nat) (s:Fin 5):Nat:=cU (B mB s)
def cf (mA:Nat) (e:Fin 5):Nat × Nat × Nat:=D (am mA e 0) (am mA e 1) (am mA e 2)
def cg (mA:Nat) (e:Fin 5):Nat × Nat × Nat:=D (aR mA e 0) (aR mA e 1) (aR mA e 2)
def ak (mB:Nat) (s:Fin 5) (ax:Fin 3):Nat × Nat × Nat:=
 D (S mB s ax 0) (S mB s ax 1) (S mB s ax 2)
def cH (ax:Fin 3):Nat:=match ax.val with|0=>4|1=>2|_=>1
def lY (mA mB:Nat) (e:Fin 5) (ax:Fin 3):Bool:=
 decide (∀ k:Fin 3,S mB ⟨(e.val+cH ax) % 5,by omega⟩ ax k=9->am mA e k=0)
def m4 (mA mB:Nat) (e:Fin 5) (ax:Fin 3):Bool:=
 decide (∀ k:Fin 3,S mB ⟨((e.val+1) % 5+cH ax) % 5,by omega⟩ ax k=9->aR mA e k=0)
def bo (mA:Nat):Nat:=bk mA 0+bk mA 1+bk mA 2+bk mA 3+bk mA 4
def bv (mB:Nat):Nat:=cw mB 0+cw mB 1+cw mB 2+cw mB 3+cw mB 4
lemma vA:bo ((1 <<< 45) - 1)=45:=by decide +kernel
lemma vz:bv 0=0:=by decide +kernel
lemma fk (d c:Nat) (e:Fin 5) (b a:Fin 3) :
 ao (d&&&c) e b a=(ao d e b a&&ao c e b a):=nV _ _ _
lemma hX (d c:Nat) (e:Fin 5) (b a:Fin 3) :
 ao (d|||c) e b a=(ao d e b a||ao c e b a):=nI _ _ _
lemma dG (h d:Nat) (s:Fin 5) (a b c:Fin 3) :
 B (h&&&d) s a b c=(B h s a b c&&B d s a b c):=nV _ _ _
lemma gH (h d:Nat) (s:Fin 5) (a b c:Fin 3) :
 B (h|||d) s a b c=(B h s a b c||B d s a b c):=nI _ _ _
lemma et (d b:Nat) (e:Fin 5):bk (d&&&b) e<=bk d e/\bk (d&&&b) e<=bk b e:=by
 have a:∀ r c:Fin 3,al (ao (d&&&b) e r c)<=al (ao d e r c)/\al (ao (d&&&b) e r c)<=al (ao b e r c):=by
  intro r c;rw[fk];cases ao d e r c <;> cases ao b e r c <;> simp[al]
 have h00:=a 0 0;have h01:=a 0 1;have h02:=a 0 2;have fT:=a 1 0;have kG:=a 1 1;have hH:=a 1 2;have gL:=a 2 0;have gV:=a 2 1;have jW:=a 2 2;unfold bk gz Y;omega
lemma fm (d b:Nat) (e:Fin 5):bk (d|||b) e<=bk d e+bk b e:=by
 have a:∀ r c:Fin 3,al (ao (d|||b) e r c)<=al (ao d e r c)+al (ao b e r c):=by
  intro r c;rw[hX];cases ao d e r c <;> cases ao b e r c <;> simp[al]
 have h00:=a 0 0;have h01:=a 0 1;have h02:=a 0 2;have fT:=a 1 0;have kG:=a 1 1;have hH:=a 1 2;have gL:=a 2 0;have gV:=a 2 1;have jW:=a 2 2;unfold bk gz Y;omega
lemma fl (h d:Nat) (s:Fin 5):cw h s<=cw (h|||d) s/\cw d s<=cw (h|||d) s:=by
 have i:∀ a b:Fin 3,aq (B h s) a b<=aq (B (h|||d) s) a b/\
   aq (B d s) a b<=aq (B (h|||d) s) a b:=by
  intro a b
  have j:∀ c:Fin 3,al (B h s a b c)<=al (B (h|||d) s a b c)/\
    al (B d s a b c)<=al (B (h|||d) s a b c):=by
   intro c;rw[gH];cases B h s a b c <;> cases B d s a b c <;> simp[al]
  have c0:=j 0;have c1:=j 1;have c2:=j 2;unfold aq;omega
 have h00:=i 0 0;have h01:=i 0 1;have h02:=i 0 2;have fT:=i 1 0;have kG:=i 1 1;have hH:=i 1 2;have gL:=i 2 0;have gV:=i 2 1;have jW:=i 2 2
 unfold cw cU A;exact ⟨by linarith,by linarith⟩
lemma kM (i h:Nat) (s:Fin 5):cw i s+cw h s - 27<=cw (i&&&h) s:=by
 have d:∀ a b:Fin 3,aq (B i s) a b+aq (B h s) a b<=aq (B (i&&&h) s) a b+3:=by
  intro a b
  have j:∀ c:Fin 3,al (B i s a b c)+al (B h s a b c)<=al (B (i&&&h) s a b c)+1:=by
   intro c;rw[dG];cases B i s a b c <;> cases B h s a b c <;> simp[al]
  have c0:=j 0;have c1:=j 1;have c2:=j 2;unfold aq;omega
 have h00:=d 0 0;have h01:=d 0 1;have h02:=d 0 2;have fT:=d 1 0;have kG:=d 1 1;have hH:=d 1 2;have gL:=d 2 0;have gV:=d 2 1;have jW:=d 2 2;apply nF;unfold cw cU A;linarith
lemma fb (b a:Nat):bo (b&&&a)<=bo b/\bo (b&&&a)<=bo a:=by
 have h0:=et b a 0;have h1:=et b a 1;have h2:=et b a 2;have h3:=et b a 3;have h4:=et b a 4;unfold bo;omega
lemma fY (b a:Nat):bo (b|||a)<=bo b+bo a:=by
 have h0:=fm b a 0;have h1:=fm b a 1;have h2:=fm b a 2;have h3:=fm b a 3;have h4:=fm b a 4;unfold bo;omega
lemma dC (b a:Nat):bv b<=bv (b|||a)/\bv a<=bv (b|||a):=by
 have h0:=fl b a 0;have h1:=fl b a 1;have h2:=fl b a 2;have h3:=fl b a 3;have h4:=fl b a 4;unfold bv;omega
lemma dN (b a:Nat):bv b+bv a - 135<=bv (b&&&a):=by
 have c:∀ s:Fin 5,cw b s+cw a s<=cw (b&&&a) s+27:=fun s=>by
  have:=kM b a s;omega
 have h0:=c 0;have h1:=c 1;have h2:=c 2;have h3:=c 3;have h4:=c 4;apply nF;unfold bv;omega
def oe (w n lim a:Nat):Prop:=(∀ i<n,o w i a<=lim)/\a<2^(w*n)
def eV (a:Nat):Prop:=oe 5 5 9 a
def fv (b:Nat):Prop:=oe 6 5 27 b
def cq (t:Nat):Prop:=oe 3 15 3 t
def az (b:Nat):Prop:=oe 5 15 9 b
def bD (w:Nat):Nat:=
 land w 31+land (shiftRight w 5) 31+land (shiftRight w 10) 31 +
 land (shiftRight w 15) 31+shiftRight w 20
def bG (w:Nat):Nat:=
 land w 63+land (shiftRight w 6) 63+land (shiftRight w 12) 63 +
 land (shiftRight w 18) 63+shiftRight w 24
def kv (p:iN):Prop:=eV p.1/\fv p.2
def iP (p:AS):Prop:=eV p.2.1/\cq p.2.2.1/\cq p.2.2.2/\p.1=bD p.2.1
def cu (p:RS):Prop:=
 eV p.2.2.1/\fv p.2.2.2.1/\cq p.2.2.2.2.1/\cq p.2.2.2.2.2.1/\
 az p.2.2.2.2.2.2.1/\az p.2.2.2.2.2.2.2.1/\az p.2.2.2.2.2.2.2.2/\
 p.1=bD p.2.2.1/\p.2.1=bG p.2.2.2.1
def gw (p:RL):Prop:=cu p.1/\p.2<2^30
lemma fz (w:Nat) (a:eV w) :
  bD w=o 5 0 w+o 5 1 w+o 5 2 w+o 5 3 w+o 5 4 w:=by
 have h0:o 5 0 w=land w 31:=by unfold o;simp
 have h4:o 5 4 w=shiftRight w 20:=by
  rw[bB 5 4 w a.2];exact (nD w 20).symm
 unfold bD;rw[h0,h4];rfl
lemma fy (w:Nat) (a:fv w) :
  bG w=o 6 0 w+o 6 1 w+o 6 2 w+o 6 3 w+o 6 4 w:=by
 have h0:o 6 0 w=land w 63:=by unfold o;simp
 have h4:o 6 4 w=shiftRight w 24:=by
  rw[bB 6 4 w a.2];exact (nD w 24).symm
 unfold bG;rw[h0,h4];rfl
def dI (pa mA:Nat):Prop:=∀ e:Fin 5,bk mA e<=o 5 e.val pa
def e7 (pb mB:Nat):Prop:=∀ s:Fin 5,o 6 s.val pb<=cw mB s
def bg (pt:Nat) (f:Fin 5->Nat × Nat × Nat):Prop:=
 ∀ e:Fin 5,(f e).1<=o 3 (3*e.val) pt/\(f e).2.1<=o 3 (3*e.val+1) pt/\(f e).2.2<=o 3 (3*e.val+2) pt
def ag (pbs:Nat) (f:Fin 5->Nat × Nat × Nat):Prop:=
 ∀ s:Fin 5,o 5 (3*s.val) pbs<=(f s).1/\o 5 (3*s.val+1) pbs<=(f s).2.1/\o 5 (3*s.val+2) pbs<=(f s).2.2
def ju (p:iN) (mA mB:Nat):Prop:=dI p.1 mA/\e7 p.2 mB
def dk (p:AS) (mA:Nat):Prop:=dI p.2.1 mA/\bg p.2.2.1 (cf mA)/\bg p.2.2.2 (cg mA)
def aW (p:RS) (mA mB:Nat):Prop:=
 dI p.2.2.1 mA/\e7 p.2.2.2.1 mB/\
 bg p.2.2.2.2.1 (cf mA)/\bg p.2.2.2.2.2.1 (cg mA)/\
 ag p.2.2.2.2.2.2.1 (fun s=>ak mB s 0)/\
 ag p.2.2.2.2.2.2.2.1 (fun s=>ak mB s 1)/\
 ag p.2.2.2.2.2.2.2.2 (fun s=>ak mB s 2)
def dj (p:RL) (mA mB:Nat):Prop:=
 aW p.1 mA mB/\
 (∀ e:Fin 5,∀ ax:Fin 3,p.2.testBit (3*e.val+ax.val)=true->lY mA mB e ax=true)/\
 (∀ e:Fin 5,∀ ax:Fin 3,p.2.testBit (15+3*e.val+ax.val)=true->m4 mA mB e ax=true)
lemma cS {a mA:Nat} (c:eV a) (b:dI a mA):bo mA<=bD a:=by
 rw[fz a c];have h0:bk mA 0<=o 5 0 a:=b 0;have h1:bk mA 1<=o 5 1 a:=b 1;have h2:bk mA 2<=o 5 2 a:=b 2;have h3:bk mA 3<=o 5 3 a:=b 3;have h4:bk mA 4<=o 5 4 a:=b 4;unfold bo;omega
lemma cR {a mB:Nat} (c:fv a) (b:e7 a mB):bG a<=bv mB:=by
 rw[fy a c];have h0:o 6 0 a<=cw mB 0:=b 0;have h1:o 6 1 a<=cw mB 1:=b 1;have h2:o 6 2 a<=cw mB 2:=b 2;have h3:o 6 3 a<=cw mB 3:=b 3;have h4:o 6 4 a<=cw mB 4:=b 4;unfold bv;omega
def q3 (a b:Nat):Bool:=
 nE (land ((lor a 0x1084210) - b) 0x1084210) 0x1084210
def vS (a b:Nat):Bool:=
 nE (land ((lor a 0x20820820) - b) 0x20820820) 0x20820820
def eP (a b:Nat):Bool:=
 nE a 0xdb6db6db6db||
 nE (land ((lor a 0x124924924924) - b) 0x124924924924) 0x124924924924
def iZ (a b:Nat):Bool:=
 nE b 0||
 nE (land ((lor a 0x4210842108421084210) - b) 0x4210842108421084210) 0x4210842108421084210
def kd (u q:Nat):Bool:=
 nE (land u q) u
def me (pa pb qa qb:Nat):Bool:=q3 pa qa&&vS qb pb
def md (pa par pac qa qar qac:Nat):Bool:=
 q3 pa qa&&eP par qar&&eP pac qac
def jI (u:RS) (qar qac qb0 qb1 qb2:Nat):Bool:=
 eP u.2.2.2.2.1 qar&&eP u.2.2.2.2.2.1 qac&&
 iZ qb0 u.2.2.2.2.2.2.1&&iZ qb1 u.2.2.2.2.2.2.2.1&&iZ qb2 u.2.2.2.2.2.2.2.2
def mc (u q:RS):Bool:=
 me u.2.2.1 u.2.2.2.1 q.2.2.1 q.2.2.2.1&&
 jI u q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2
def vX (u q:RL):Bool:=
 mc u.1 q.1&&kd u.2 q.2
lemma hU:∀ i:Fin 15,o 3 i.val 0xdb6db6db6db=3:=by decide +kernel
lemma nx:∀ i:Fin 5,o 5 i.val 0x1084210=16:=by decide +kernel
lemma nw:∀ i:Fin 5,o 6 i.val 0x20820820=32:=by decide +kernel
lemma qK:∀ i:Fin 15,o 3 i.val 0x124924924924=4:=by decide +kernel
lemma qJ:∀ i:Fin 15,o 5 i.val 0x4210842108421084210=16:=by decide +kernel
lemma kH {d c mA:Nat} (b:eV d) (a:eV c)
  (h:q3 d c=true) (k:dI c mA):dI d mA:=by
 have j:=gb 5 4 5 d c 0x1084210 (by omega) b.2 a.2 (by decide)
  (fun i hi=>nx ⟨i,hi⟩) (fun i hi=>lO (b.1 i hi) (by decide))
  (fun i hi=>lO (a.1 i hi) (by decide)) h
 exact fun e=>lT (k e) (j e.val e.isLt)
lemma ph {d c mB:Nat} (b:fv d) (a:fv c)
  (h:vS c d=true) (k:e7 c mB):e7 d mB:=by
 have j:=gb 6 5 5 c d 0x20820820 (by omega) a.2 b.2 (by decide)
  (fun i hi=>nw ⟨i,hi⟩) (fun i hi=>lO (a.1 i hi) (by decide))
  (fun i hi=>lO (b.1 i hi) (by decide)) h
 exact fun s=>lT (j s.val s.isLt) (k s)
lemma ig {j d:Nat} {f:Fin 5->Nat × Nat × Nat} (c:cq j) (a:cq d)
   (h:eP j d=true) (k:bg d f):bg j f:=by
 unfold eP at h;simp only[bO] at h;rcases h with h3|hsw
 . rw[bQ h3];intro e;rcases k e with ⟨d0,d1,d2⟩
   have n:=hU ⟨3*e.val,by omega⟩;have q0:=a.1 (3*e.val) (by omega)
   have m:=hU ⟨3*e.val+1,by omega⟩;have q1:=a.1 (3*e.val+1) (by omega)
   have l:=hU ⟨3*e.val+2,by omega⟩;have q2:=a.1 (3*e.val+2) (by omega)
   dsimp only at n m l;omega
 . have b:=gb 3 2 15 j d 0x124924924924 (by omega) c.2 a.2 (by decide)
     (fun i hi=>qK ⟨i,hi⟩) (fun i hi=>lO (c.1 i hi) (by decide))
     (fun i hi=>lO (a.1 i hi) (by decide)) hsw
   intro e;rcases k e with ⟨d0,d1,d2⟩
   exact ⟨lT d0 (b (3*e.val) (by omega)),
          lT d1 (b (3*e.val+1) (by omega)),
          lT d2 (b (3*e.val+2) (by omega))⟩
lemma jX {j d:Nat} {f:Fin 5->Nat × Nat × Nat} (c:az j) (b:az d)
   (h:iZ d j=true) (k:ag d f):ag j f:=by
 unfold iZ at h;simp only[bO] at h;rcases h with hb0|hsw
 . rw[bQ hb0];intro s;simp[o]
 . have a:=gb 5 4 15 d j 0x4210842108421084210 (by omega) b.2 c.2 (by decide)
     (fun i hi=>qJ ⟨i,hi⟩) (fun i hi=>lO (b.1 i hi) (by decide))
     (fun i hi=>lO (c.1 i hi) (by decide)) hsw
   intro s;rcases k s with ⟨d0,d1,d2⟩
   exact ⟨lT (a (3*s.val) (by omega)) d0,
          lT (a (3*s.val+1) (by omega)) d1,
          lT (a (3*s.val+2) (by omega)) d2⟩
lemma l7 {u q:Nat} (_hu:u<2^30) (_hq:q<2^30) (h:kd u q=true) :
  ∀ k<30,u.testBit k=true->q.testBit k=true:=by
 have b:=bQ h;intro k _ hu;have a:=congrArg (fun z=>z.testBit k) b;change (u&&&q).testBit k=u.testBit k at a;rw[nV,hu,bTA] at a;exact a
lemma kL {p q:iN} {mA mB:Nat} (b:kv p) (a:kv q)
  (h:me p.1 p.2 q.1 q.2=true) (c:ju q mA mB):ju p mA mB:=by
 unfold me at h;simp only[bA] at h;exact ⟨kH b.1 a.1 h.1 c.1,ph b.2 a.2 h.2 c.2⟩
lemma j3 {p q:AS} {mA:Nat} (b:iP p) (a:iP q)
  (h:md p.2.1 p.2.2.1 p.2.2.2 q.2.1 q.2.2.1 q.2.2.2=true) (c:dk q mA):dk p mA:=by
 unfold md at h;simp only[bA] at h;exact ⟨kH b.1 a.1 h.1.1 c.1,ig b.2.1 a.2.1 h.1.2 c.2.1,ig b.2.2.1 a.2.2.1 h.2 c.2.2⟩
lemma ep {u q:RS} {mA mB:Nat} (a:cu u) (b:cu q)
  (h:mc u q=true) (c:aW q mA mB):aW u mA mB:=by
 unfold mc me jI at h;simp only[bA] at h
 exact ⟨kH a.1 b.1 h.1.1 c.1,
  ph a.2.1 b.2.1 h.1.2 c.2.1,
  ig a.2.2.1 b.2.2.1 h.2.1.1.1.1 c.2.2.1,
  ig a.2.2.2.1 b.2.2.2.1 h.2.1.1.1.2 c.2.2.2.1,
  jX a.2.2.2.2.1 b.2.2.2.2.1 h.2.1.1.2 c.2.2.2.2.1,
  jX a.2.2.2.2.2.1 b.2.2.2.2.2.1 h.2.1.2 c.2.2.2.2.2.1,
  jX a.2.2.2.2.2.2.1 b.2.2.2.2.2.2.1 h.2.2 c.2.2.2.2.2.2⟩
lemma vW {u q:RL} {mA mB:Nat} (a:gw u) (b:gw q)
   (h:vX u q=true) (c:dj q mA mB):dj u mA mB:=by
 unfold vX at h;simp only[bA] at h;refine ⟨ep a.1 b.1 h.1 c.1,?_,?_⟩
 . intro e ax hu;exact c.2.1 e ax (l7 a.2 b.2 h.2 _ (by omega) hu)
 . intro e ax hu;exact c.2.2 e ax (l7 a.2 b.2 h.2 _ (by omega) hu)
def oY (r w:Nat):Nat:=match r with
 | 0=>w
 | 1=>lor (shiftLeft (land w 1048575) 5) (shiftRight w 20)
 | 2=>lor (shiftLeft (land w 32767) 10) (shiftRight w 15)
 | 3=>lor (shiftLeft (land w 1023) 15) (shiftRight w 10)
 | _=>lor (shiftLeft (land w 31) 20) (shiftRight w 5)
def sn (r w:Nat):Nat:=match r with
 | 0=>w
 | 1=>lor (shiftLeft (land w 16777215) 6) (shiftRight w 24)
 | 2=>lor (shiftLeft (land w 262143) 12) (shiftRight w 18)
 | 3=>lor (shiftLeft (land w 4095) 18) (shiftRight w 12)
 | _=>lor (shiftLeft (land w 63) 24) (shiftRight w 6)
def gD (r w:Nat):Nat:=match r with
 | 0=>w
 | 1=>lor (shiftLeft (land w 68719476735) 9) (shiftRight w 36)
 | 2=>lor (shiftLeft (land w 134217727) 18) (shiftRight w 27)
 | 3=>lor (shiftLeft (land w 262143) 27) (shiftRight w 18)
 | _=>lor (shiftLeft (land w 511) 36) (shiftRight w 9)
def gR (r w:Nat):Nat:=match r with
 | 0=>w
 | 1=>lor (shiftLeft (land w 0xfffffffffffffff) 15) (shiftRight w 60)
 | 2=>lor (shiftLeft (land w 35184372088831) 30) (shiftRight w 45)
 | 3=>lor (shiftLeft (land w 1073741823) 45) (shiftRight w 30)
 | _=>lor (shiftLeft (land w 32767) 60) (shiftRight w 15)
def ux (w:Nat):Nat:=
 lor (lor (lor (lor
  (shiftLeft (land w 31) 20)
  (shiftLeft (land (shiftRight w 5) 31) 15))
  (shiftLeft (land (shiftRight w 10) 31) 10))
  (shiftLeft (land (shiftRight w 15) 31) 5))
  (shiftRight w 20)
def xb (w:Nat):Nat:=
 lor (lor (lor (lor
  (shiftLeft (land w 63) 18)
  (shiftLeft (land (shiftRight w 6) 63) 12))
  (shiftLeft (land (shiftRight w 12) 63) 6))
  (land (shiftRight w 18) 63))
  (shiftLeft (shiftRight w 24) 24)
def l8 (w:Nat):Nat:=
 lor (lor (lor (lor
  (shiftLeft (land w 511) 36)
  (shiftLeft (land (shiftRight w 9) 511) 27))
  (shiftLeft (land (shiftRight w 18) 511) 18))
  (shiftLeft (land (shiftRight w 27) 511) 9))
  (shiftRight w 36)
def kA (w:Nat):Nat:=
 lor (lor (lor (lor
  (shiftLeft (land w 32767) 45)
  (shiftLeft (land (shiftRight w 15) 32767) 30))
  (shiftLeft (land (shiftRight w 30) 32767) 15))
  (land (shiftRight w 45) 32767))
  (shiftLeft (shiftRight w 60) 60)
lemma oX (r w:Nat) (hr:r<5) (a:w<2^25):oY r w=ke 5 r w:=by
 have:r=0\/r=1\/r=2\/r=3\/r=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . rfl
 . exact br 5 1 w (by omega) (by omega) a
 . exact br 5 2 w (by omega) (by omega) a
 . exact br 5 3 w (by omega) (by omega) a
 . exact br 5 4 w (by omega) (by omega) a
lemma oW (r w:Nat) (hr:r<5) (a:w<2^30):sn r w=ke 6 r w:=by
 have:r=0\/r=1\/r=2\/r=3\/r=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . rfl
 . exact br 6 1 w (by omega) (by omega) a
 . exact br 6 2 w (by omega) (by omega) a
 . exact br 6 3 w (by omega) (by omega) a
 . exact br 6 4 w (by omega) (by omega) a
lemma oV (r w:Nat) (hr:r<5) (a:w<2^45):gD r w=ke 9 r w:=by
 have:r=0\/r=1\/r=2\/r=3\/r=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . rfl
 . exact br 9 1 w (by omega) (by omega) a
 . exact br 9 2 w (by omega) (by omega) a
 . exact br 9 3 w (by omega) (by omega) a
 . exact br 9 4 w (by omega) (by omega) a
lemma mx (r w:Nat) (hr:r<5) (a:w<2^75):gR r w=ke 15 r w:=by
 have:r=0\/r=1\/r=2\/r=3\/r=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . rfl
 . exact br 15 1 w (by omega) (by omega) a
 . exact br 15 2 w (by omega) (by omega) a
 . exact br 15 3 w (by omega) (by omega) a
 . exact br 15 4 w (by omega) (by omega) a
lemma xc (w:Nat) (a:w<2^25):ux w=hP 5 w:=by
 have b:shiftRight w 20=land (shiftRight w 20) 31:=fZ 5 w a;unfold ux hP;dsimp only;rw[b];rfl
lemma x9 (w:Nat) (a:w<2^30):xb w=jU 6 w:=by
 have b:shiftRight w 24=land (shiftRight w 24) 63:=fZ 6 w a;unfold xb jU;dsimp only;rw[b];rfl
lemma x8 (w:Nat) (a:w<2^45):l8 w=hP 9 w:=by
 have b:shiftRight w 36=land (shiftRight w 36) 511:=fZ 9 w a;unfold l8 hP;dsimp only;rw[b];rfl
lemma uw (w:Nat) (a:w<2^75):kA w=jU 15 w:=by
 have b:shiftRight w 60=land (shiftRight w 60) 32767:=fZ 15 w a;unfold kA jU;dsimp only;rw[b];rfl
def bH (g w:Nat):Nat:=cond (nB g 4) (oY g w) (oY (g - 5) (ux w))
def cx (g w:Nat):Nat:=cond (nB g 4) (sn g w) (sn (g - 5) (xb w))
def cY (g w:Nat):Nat:=cond (nB g 4) (gD g w) (gD (g - 5) (l8 w))
def cA (g w:Nat):Nat:=cond (nB g 4) (gR g w) (gR (g - 5) (kA w))
def dV (g:Nat) (x:iN):iN:=(bH g x.1,cx g x.2)
def cB (g:Nat) (x:AS):AS:=
 let (sa,pa,par,pac):=x
 cond (nB g 4) (sa,oY g pa,gD g par,gD g pac)
  (let r:=g - 5;(sa,oY r (ux pa),gD r (l8 pac),gD r (l8 par)))
def ay (g:Nat) (x:RS):RS:=
 let (sa,sb,pa,pb,par,pac,bf,be,bd):=x
 cond (nB g 4)
  (sa,sb,oY g pa,sn g pb,gD g par,gD g pac,gR g bf,gR g be,gR g bd)
  (let r:=g - 5
   (sa,sb,oY r (ux pa),sn r (xb pb),gD r (l8 pac),gD r (l8 par),
    gR r (kA bf),gR r (kA bd),gR r (kA be)))
def pQ (r m:Nat):Nat:=match r with
 | 0=>m
 | 1=>lor (shiftLeft (land m 4095) 3) (shiftRight m 12)
 | 2=>lor (shiftLeft (land m 511) 6) (shiftRight m 9)
 | 3=>lor (shiftLeft (land m 63) 9) (shiftRight m 6)
 | _=>lor (shiftLeft (land m 7) 12) (shiftRight m 3)
def ss (m:Nat):Nat:=
 lor (lor (lor (lor
  (shiftLeft (land m 7) 12)
  (shiftLeft (land (shiftRight m 3) 7) 9))
  (shiftLeft (land (shiftRight m 6) 7) 6))
  (shiftLeft (land (shiftRight m 9) 7) 3))
  (shiftRight m 12)
def bq (c:Nat):Nat:=(c % 2)+((c/2) % 2)*4+(c/4)*2
def dB (m:Nat):Nat:=
 bq (m % 8)+bq ((m/8) % 8)*8+bq ((m/64) % 8)*64 +
 bq ((m/512) % 8)*512+bq (m/4096)*4096
def bR (g m:Nat):Nat:=
 let a:=land m 32767;let b:=shiftRight m 15
 cond (nB g 4) (lor (pQ g a) (shiftLeft (pQ g b) 15))
  (let r:=g - 5;lor (pQ r (ss (dB b))) (shiftLeft (pQ r (ss (dB a))) 15))
def d7 (g:Nat) (x:RL):RL:=(ay g x.1,bR g x.2)
def sW (g:Nat) (r z:AS):Bool:=
 q3 (bH g r.2.1) z.2.1&&
 cond (nB g 4)
  (eP (gD g r.2.2.1) z.2.2.1&&eP (gD g r.2.2.2) z.2.2.2)
  (let k:=g - 5;eP (gD k (l8 r.2.2.2)) z.2.2.1&&eP (gD k (l8 r.2.2.1)) z.2.2.2)
lemma ym (g:Nat) (r z:AS) :
  sW g r z=md (cB g r).2.1 (cB g r).2.2.1 (cB g r).2.2.2 z.2.1 z.2.2.1 z.2.2.2:=by
 unfold sW md cB bH;cases nB g 4 <;> simp[Bool.and_assoc]
lemma nn (r:Nat):gD r 0xdb6db6db6db=0xdb6db6db6db:=by
 match r with|0=>rfl|1=>rfl|2=>rfl|3=>rfl|_+4=>rfl
lemma so:l8 0xdb6db6db6db=0xdb6db6db6db:=by decide +kernel
lemma lK (r:Nat):gR r 0=0:=by
 match r with|0=>rfl|1=>rfl|2=>rfl|3=>rfl|_+4=>rfl
lemma qC:kA 0=0:=by decide +kernel
lemma Ho (g:Nat):cY g 0xdb6db6db6db=0xdb6db6db6db:=by
 unfold cY;cases nB g 4 <;> simp[nn,so]
lemma Gi (g:Nat):cA g 0=0:=by
 unfold cA;cases nB g 4 <;> simp[lK,qC]
lemma db (g:Fin 10) (e:Fin 5) (w:Nat) (c:w<2^25) :
   o 5 (au g e).val (bH g.val w)=o 5 e.val w:=by
 unfold bH au
 by_cases hg:g.val<5
 . have a:nB g.val 4=true:=bL.mpr (by omega);simp only[hg,↓reduceIte,a,bT,oX g.val w hg c];exact ee 5 g.val w e.val hg e.isLt c
 . have a:nB g.val 4=false:=by
     cases hb:nB g.val 4
     . rfl
     . exfalso;have:=bL.mp hb;omega
   simp only[hg,↓reduceIte,a,bC,xc w c,oX (g.val - 5) _ (by omega) (cP 5 w)]
   have b:(9 - e.val+(g.val - 5)) % 5=((4 - e.val)+(g.val - 5)) % 5:=by omega
   rw[b,ee 5 (g.val - 5) (hP 5 w) (4 - e.val) (by omega) (by omega) (cP 5 w),
     lL 5 w e.val e.isLt]
lemma d9 (g:Fin 10) (s:Fin 5) (w:Nat) (c:w<2^30) :
   o 6 (ad g s).val (cx g.val w)=o 6 s.val w:=by
 unfold cx ad
 by_cases hg:g.val<5
 . have a:nB g.val 4=true:=bL.mpr (by omega);simp only[hg,↓reduceIte,a,bT,oW g.val w hg c];exact ee 6 g.val w s.val hg s.isLt c
 . have a:nB g.val 4=false:=by
     cases hb:nB g.val 4
     . rfl
     . exfalso;have:=bL.mp hb;omega
   simp only[hg,↓reduceIte,a,bC,x9 w c,oW (g.val - 5) _ (by omega) (gE 6 w)]
   have b:(8 - s.val+(g.val - 5)) % 5=(((8 - s.val) % 5)+(g.val - 5)) % 5:=by omega
   rw[b,ee 6 (g.val - 5) (jU 6 w) ((8 - s.val) % 5) (by omega) (by omega) (gE 6 w),
     qD 6 w s.val s.isLt]
lemma d8 (g:Fin 10) (e:Fin 5) (c:Fin 3) (w:Nat) (d:w<2^45) :
   o 3 (3*(au g e).val+c.val) (cY g.val w)=o 3 (3*e.val+c.val) w:=by
 rw[<- aY 3 c.val (au g e).val _ c.isLt,<-aY 3 c.val e.val w c.isLt];congr 1;unfold cY au
 by_cases hg:g.val<5
 . have a:nB g.val 4=true:=bL.mpr (by omega);simp only[hg,↓reduceIte,a,bT,oV g.val w hg d];exact ee 9 g.val w e.val hg e.isLt d
 . have a:nB g.val 4=false:=by
     cases hb:nB g.val 4
     . rfl
     . exfalso;have:=bL.mp hb;omega
   simp only[hg,↓reduceIte,a,bC,x8 w d,oV (g.val - 5) _ (by omega) (cP 9 w)]
   have b:(9 - e.val+(g.val - 5)) % 5=((4 - e.val)+(g.val - 5)) % 5:=by omega
   rw[b,ee 9 (g.val - 5) (hP 9 w) (4 - e.val) (by omega) (by omega) (cP 9 w),
     lL 9 w e.val e.isLt]
lemma cn (g:Fin 10) (s:Fin 5) (c:Fin 3) (w:Nat) (d:w<2^75) :
   o 5 (3*(ad g s).val+c.val) (cA g.val w)=o 5 (3*s.val+c.val) w:=by
 rw[<- aY 5 c.val (ad g s).val _ c.isLt,<-aY 5 c.val s.val w c.isLt];congr 1;unfold cA ad
 by_cases hg:g.val<5
 . have a:nB g.val 4=true:=bL.mpr (by omega);simp only[hg,↓reduceIte,a,bT,mx g.val w hg d];exact ee 15 g.val w s.val hg s.isLt d
 . have a:nB g.val 4=false:=by
     cases hb:nB g.val 4
     . rfl
     . exfalso;have:=bL.mp hb;omega
   simp only[hg,↓reduceIte,a,bC,uw w d,mx (g.val - 5) _ (by omega) (gE 15 w)]
   have b:(8 - s.val+(g.val - 5)) % 5=(((8 - s.val) % 5)+(g.val - 5)) % 5:=by omega
   rw[b,ee 15 (g.val - 5) (jU 15 w) ((8 - s.val) % 5) (by omega) (by omega) (gE 15 w),
     qD 15 w s.val s.isLt]
lemma fa (g:Fin 10) (w:Nat) (a:eV w):eV (bH g.val w):=by
 refine ⟨?_,?_⟩
 . intro i hi;have h:=db g (au (I g) ⟨i,hi⟩) w a.2;rw[cE] at h;rw[h];exact a.1 _ (au (I g) ⟨i,hi⟩).isLt
 . unfold bH;by_cases hg:g.val<5
   . simp only[show nB g.val 4=true from bL.mpr (by omega),bT,oX g.val w hg a.2];exact dt 5 g.val w a.2
   . simp only[show nB g.val 4=false by cases hb:nB g.val 4;rfl;exfalso;have:=bL.mp hb;omega,
       bC,xc w a.2,oX (g.val - 5) _ (by omega) (cP 5 w)]
     exact dt 5 (g.val - 5) _ (cP 5 w)
lemma gx (g:Fin 10) (w:Nat) (a:fv w):fv (cx g.val w):=by
 refine ⟨?_,?_⟩
 . intro i hi;have h:=d9 g (ad (I g) ⟨i,hi⟩) w a.2;rw[cd] at h;rw[h];exact a.1 _ (ad (I g) ⟨i,hi⟩).isLt
 . unfold cx;by_cases hg:g.val<5
   . simp only[show nB g.val 4=true from bL.mpr (by omega),bT,oW g.val w hg a.2];exact dt 6 g.val w a.2
   . simp only[show nB g.val 4=false by cases hb:nB g.val 4;rfl;exfalso;have:=bL.mp hb;omega,
       bC,x9 w a.2,oW (g.val - 5) _ (by omega) (gE 6 w)]
     exact dt 6 (g.val - 5) _ (gE 6 w)
lemma eZ (g:Fin 10) (w:Nat) (b:cq w):cq (cY g.val w):=by
 refine ⟨?_,?_⟩
 . intro i hi
   set e:Fin 5:=⟨i/3,by omega⟩;set c:Fin 3:=⟨i % 3,by omega⟩
   have h:=d8 g (au (I g) e) c w b.2;rw[cE] at h
   have a:3*e.val+c.val=i:=by dsimp[e,c];omega
   rw[a] at h;rw[h];exact b.1 _ (by omega)
 . unfold cY;by_cases hg:g.val<5
   . simp only[show nB g.val 4=true from bL.mpr (by omega),bT,oV g.val w hg b.2];exact dt 9 g.val w b.2
   . simp only[show nB g.val 4=false by cases hb:nB g.val 4;rfl;exfalso;have:=bL.mp hb;omega,
       bC,x8 w b.2,oV (g.val - 5) _ (by omega) (cP 9 w)]
     exact dt 9 (g.val - 5) _ (cP 9 w)
lemma eB (g:Fin 10) (w:Nat) (b:az w):az (cA g.val w):=by
 refine ⟨?_,?_⟩
 . intro i hi
   set s:Fin 5:=⟨i/3,by omega⟩;set c:Fin 3:=⟨i % 3,by omega⟩
   have h:=cn g (ad (I g) s) c w b.2;rw[cd] at h
   have a:3*s.val+c.val=i:=by dsimp[s,c];omega
   rw[a] at h;rw[h];exact b.1 _ (by omega)
 . unfold cA;by_cases hg:g.val<5
   . simp only[show nB g.val 4=true from bL.mpr (by omega),bT,mx g.val w hg b.2];exact dt 15 g.val w b.2
   . simp only[show nB g.val 4=false by cases hb:nB g.val 4;rfl;exfalso;have:=bL.mp hb;omega,
       bC,uw w b.2,mx (g.val - 5) _ (by omega) (gE 15 w)]
     exact dt 15 (g.val - 5) _ (gE 15 w)
def gA (w e:Nat):Nat:=match e with
 | 0=>land w 31|1=>land (shiftRight w 5) 31|2=>land (shiftRight w 10) 31
 | 3=>land (shiftRight w 15) 31|_=>shiftRight w 20
def gB (w s:Nat):Nat:=match s with
 | 0=>land w 63|1=>land (shiftRight w 6) 63|2=>land (shiftRight w 12) 63
 | 3=>land (shiftRight w 18) 63|_=>shiftRight w 24
def aL (w e:Nat):Nat:=match e with
 | 0=>land w 511|1=>land (shiftRight w 9) 511|2=>land (shiftRight w 18) 511
 | 3=>land (shiftRight w 27) 511|_=>shiftRight w 36
def V (w s:Nat):Nat:=match s with
 | 0=>land w 32767|1=>land (shiftRight w 15) 32767|2=>land (shiftRight w 30) 32767
 | 3=>land (shiftRight w 45) 32767|_=>shiftRight w 60
lemma m8 (w e:Nat) (a:eV w) (he:e<5):gA w e=o 5 e w:=by
 have:e=0\/e=1\/e=2\/e=3\/e=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . unfold gA o;simp
 . rfl
 . rfl
 . rfl
 . rw[bB 5 4 w a.2];exact nD w 20
lemma o1 (w s:Nat) (a:fv w) (hs:s<5):gB w s=o 6 s w:=by
 have:s=0\/s=1\/s=2\/s=3\/s=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . unfold gB o;simp
 . rfl
 . rfl
 . rfl
 . rw[bB 6 4 w a.2];exact nD w 24
lemma m7 (w e:Nat) (a:w<2^45) (he:e<5):aL w e=o 9 e w:=by
 have:e=0\/e=1\/e=2\/e=3\/e=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . unfold aL o;simp
 . rfl
 . rfl
 . rfl
 . rw[bB 9 4 w a];exact nD w 36
lemma kI (w s:Nat) (a:w<2^75) (hs:s<5):V w s=o 15 s w:=by
 have:s=0\/s=1\/s=2\/s=3\/s=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . unfold V o;simp
 . rfl
 . rfl
 . rfl
 . rw[bB 15 4 w a];exact nD w 60
lemma lG (g:Fin 10) (w:Nat) (a:eV w):bD (bH g.val w)=bD w:=by
 rw[fz _ (fa g w a),fz _ a];have h0:=db g 0 w a.2;have h1:=db g 1 w a.2;have h2:=db g 2 w a.2;have h3:=db g 3 w a.2;have h4:=db g 4 w a.2
 have b:g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9:=by
  fin_cases g <;> simp
 rcases b with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  (simp only[au] at h0 h1 h2 h3 h4;norm_num at h0 h1 h2 h3 h4 ⊢;omega)
lemma sm (g:Fin 10) (w:Nat) (a:fv w):bG (cx g.val w)=bG w:=by
 rw[fy _ (gx g w a),fy _ a];have h0:=d9 g 0 w a.2;have h1:=d9 g 1 w a.2;have h2:=d9 g 2 w a.2;have h3:=d9 g 3 w a.2;have h4:=d9 g 4 w a.2
 have b:g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9:=by
  fin_cases g <;> simp
 rcases b with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  (simp only[ad] at h0 h1 h2 h3 h4;norm_num at h0 h1 h2 h3 h4 ⊢;omega)
lemma cy (g:Fin 10) (x:RS) (n:cu x):cu (ay g.val x):=by
 rcases x with ⟨sa,sb,pa,pb,par,pac,bf,be,bd⟩;rcases n with ⟨hpa,hpb,hpar,hpac,hpb0,hpb1,hpb2,hsa,hsb⟩;have m:=fa g pa hpa;have l:=gx g pb hpb;have j:=eZ g par hpar;have k:=eZ g pac hpac;have i:=eB g bf hpb0;have h:=eB g be hpb1;have d:=eB g bd hpb2;have b:=lG g pa hpa;have a:=sm g pb hpb
 unfold ay;unfold bH cx cY cA at *
 by_cases hg:g.val<5
 . have c:nB g.val 4=true:=bL.mpr (by omega);simp only[c,bT] at m l j k i h d b a ⊢
   exact ⟨m,l,j,k,i,h,d,by rw[hsa,<-b],by rw[hsb,<-a]⟩
 . have c:nB g.val 4=false:=by cases hb':nB g.val 4;rfl;exfalso;have:=bL.mp hb';omega
   simp only[c,bC] at m l j k i h d b a ⊢
   exact ⟨m,l,k,j,i,d,h,by rw[hsa,<-b],by rw[hsb,<-a]⟩
lemma cD (g:Fin 10) (f:(Fin 15->Bool)->Bool) (e:Fin 5) (b a:Fin 3) :
  ao (R (E g f)) (au g e) (if g.val<5 then b else a) (if g.val<5 then a else b) =
  ao (R f) e b a:=by
 unfold ao;rw[lW,lW];unfold E;congr 1;funext i;exact ty g e b a i
lemma pn (g:Fin 10) (f:(Fin 15->Bool)->Bool) (s:Fin 5) (a b c:Fin 3) :
  B (O (E g f)) (ad g s) a (if g.val<5 then b else c) (if g.val<5 then c else b) =
  B (O f) s a b c:=by
 unfold B;rw[lV,lV];unfold E;congr 1;funext i;exact tz g s a b c i
lemma cJ (g:Fin 10) (f:(Fin 15->Bool)->Bool) (e:Fin 5) (k:Fin 3) :
   am (R (E g f)) (au g e) k=if g.val<5 then am (R f) e k else aR (R f) e k:=by
 unfold am aR Y aQ
 by_cases hg:g.val<5
 . simp only[hg,↓reduceIte];have h0:=cD g f e k 0;have h1:=cD g f e k 1;have h2:=cD g f e k 2;simp only[hg,↓reduceIte] at h0 h1 h2;rw[h0,h1,h2]
 . simp only[hg,↓reduceIte];have h0:=cD g f e 0 k;have h1:=cD g f e 1 k;have h2:=cD g f e 2 k;simp only[hg,↓reduceIte] at h0 h1 h2;rw[h0,h1,h2]
lemma du (g:Fin 10) (f:(Fin 15->Bool)->Bool) (e:Fin 5) (k:Fin 3) :
   aR (R (E g f)) (au g e) k=if g.val<5 then aR (R f) e k else am (R f) e k:=by
 unfold am aR Y aQ
 by_cases hg:g.val<5
 . simp only[hg,↓reduceIte];have h0:=cD g f e 0 k;have h1:=cD g f e 1 k;have h2:=cD g f e 2 k;simp only[hg,↓reduceIte] at h0 h1 h2;rw[h0,h1,h2]
 . simp only[hg,↓reduceIte];have h0:=cD g f e k 0;have h1:=cD g f e k 1;have h2:=cD g f e k 2;simp only[hg,↓reduceIte] at h0 h1 h2;rw[h0,h1,h2]
lemma gJ (g:Fin 10) (f:(Fin 15->Bool)->Bool) (e:Fin 5) :
   bk (R (E g f)) (au g e)=bk (R f) e:=by
 have h0:=cJ g f e 0;have h1:=cJ g f e 1;have h2:=cJ g f e 2;unfold bk gz;change am _ _ 0+am _ _ 1+am _ _ 2=_;rw[h0,h1,h2];by_cases hg:g.val<5
 . simp[hg,am]
 . simp only[hg,↓reduceIte,aR];exact (gM (ao (R f) e)).symm
lemma bJ (g:Fin 10) (f:(Fin 15->Bool)->Bool) :
  bo (R (E g f))=bo (R f):=by
 have h0:=gJ g f 0;have h1:=gJ g f 1;have h2:=gJ g f 2;have h3:=gJ g f 3;have h4:=gJ g f 4
 have a:g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9:=by
  fin_cases g <;> simp
 unfold bo
 rcases a with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  (simp only[au] at h0 h1 h2 h3 h4;norm_num at h0 h1 h2 h3 h4 ⊢;omega)
lemma aO (g:Fin 10) (f:(Fin 15->Bool)->Bool) (s:Fin 5) (k:Fin 3) :
   S (O (E g f)) (ad g s) 0 k=S (O f) s 0 k/\
   S (O (E g f)) (ad g s) 1 k=(if g.val<5 then S (O f) s 1 k else S (O f) s 2 k)/\
   S (O (E g f)) (ad g s) 2 k=(if g.val<5 then S (O f) s 2 k else S (O f) s 1 k):=by
 have h:∀ a b c:Fin 3,B (O (E g f)) (ad g s) a b c =
     if g.val<5 then B (O f) s a b c else B (O f) s a c b:=by
   intro a b c
   by_cases hg:g.val<5
   . simpa [hg] using pn g f s a b c
   . simpa [hg] using pn g f s a c b
 refine ⟨?_,?_,?_⟩
 . change A (B (O (E g f)) (ad g s)) k=A (B (O f) s) k;unfold A aq
   by_cases hg:g.val<5
   . simp only[h,hg,↓reduceIte]
   . simp only[h,hg,↓reduceIte];omega
 . change Z (B (O (E g f)) (ad g s)) k =
     if g.val<5 then Z (B (O f) s) k else aK (B (O f) s) k
   unfold Z aK A aq;dsimp only
   by_cases hg:g.val<5
   . simp only[h,hg,↓reduceIte]
   . simp only[h,hg,↓reduceIte]
 . change aK (B (O (E g f)) (ad g s)) k =
     if g.val<5 then aK (B (O f) s) k else Z (B (O f) s) k
   unfold Z aK A aq;dsimp only
   by_cases hg:g.val<5
   . simp only[h,hg,↓reduceIte]
   . simp only[h,hg,↓reduceIte]
lemma gI (g:Fin 10) (f:(Fin 15->Bool)->Bool) (s:Fin 5) :
  cw (O (E g f)) (ad g s)=cw (O f) s:=by
 have h0:=(aO g f s 0).1;have h1:=(aO g f s 1).1;have h2:=(aO g f s 2).1;unfold cw cU;change S _ _ 0 0+S _ _ 0 1+S _ _ 0 2=S _ _ 0 0+S _ _ 0 1+S _ _ 0 2;rw[h0,h1,h2]
lemma bt (g:Fin 10) (f:(Fin 15->Bool)->Bool) :
  bv (O (E g f))=bv (O f):=by
 have h0:=gI g f 0;have h1:=gI g f 1;have h2:=gI g f 2;have h3:=gI g f 3;have h4:=gI g f 4
 have a:g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9:=by
  fin_cases g <;> simp
 unfold bv
 rcases a with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  (simp only[ad] at h0 h1 h2 h3 h4;norm_num at h0 h1 h2 h3 h4 ⊢;omega)
lemma iO (g:Fin 10) {p:iN} {f:(Fin 15->Bool)->Bool} (a:kv p)
   (c:ju p (R f) (O f)):ju (dV g.val p) (R (E g f)) (O (E g f)):=by
 refine ⟨?_,?_⟩
 . intro e;have h:=db g (au (I g) e) p.1 a.1.2;rw[cE] at h;rw[show (dV g.val p).1=bH g.val p.1 from rfl,h];have b:=gJ g f (au (I g) e);rw[cE] at b;rw[b];exact c.1 _
 . intro s;have h:=d9 g (ad (I g) s) p.2 a.2.2;rw[cd] at h;rw[show (dV g.val p).2=cx g.val p.2 from rfl,h];have b:=gI g f (ad (I g) s);rw[cd] at b;rw[b];exact c.2 _
lemma cX (g:Fin 10) {p:RS} {f:(Fin 15->Bool)->Bool} (l:cu p)
   (m:aW p (R f) (O f)):aW (ay g.val p) (R (E g f)) (O (E g f)):=by
 rcases p with ⟨sa,sb,pa,pb,par,pac,bf,be,bd⟩;rcases l with ⟨hpa,hpb,hpar,hpac,hpb0,hpb1,hpb2,_,_⟩;rcases m with ⟨hda,hdb,hdar,hdac,hdb0,hdb1,hdb2⟩;have fT:=iO g (p:=(pa,pb)) ⟨hpa,hpb⟩ ⟨hda,hdb⟩;have k:∀ e:Fin 5,bk (R (E g f)) e<=o 5 e.val (bH g.val pa):=fT.1;have j:∀ s:Fin 5,o 6 s.val (cx g.val pb)<=cw (O (E g f)) s:=fT.2
 have d:∀ e:Fin 5,
     o 3 (3*e.val) (cY g.val par)=o 3 (3*(au (I g) e).val) par/\
     o 3 (3*e.val+1) (cY g.val par)=o 3 (3*(au (I g) e).val+1) par/\
     o 3 (3*e.val+2) (cY g.val par)=o 3 (3*(au (I g) e).val+2) par:=fun e=>by
   have h0:=d8 g (au (I g) e) 0 par hpar.2;have h1:=d8 g (au (I g) e) 1 par hpar.2;have h2:=d8 g (au (I g) e) 2 par hpar.2
   rw[cE] at h0 h1 h2;exact ⟨by simpa using h0,h1,h2⟩
 have h:∀ e:Fin 5,
     o 3 (3*e.val) (cY g.val pac)=o 3 (3*(au (I g) e).val) pac/\
     o 3 (3*e.val+1) (cY g.val pac)=o 3 (3*(au (I g) e).val+1) pac/\
     o 3 (3*e.val+2) (cY g.val pac)=o 3 (3*(au (I g) e).val+2) pac:=fun e=>by
   have h0:=d8 g (au (I g) e) 0 pac hpac.2;have h1:=d8 g (au (I g) e) 1 pac hpac.2;have h2:=d8 g (au (I g) e) 2 pac hpac.2
   rw[cE] at h0 h1 h2;exact ⟨by simpa using h0,h1,h2⟩
 have c:∀ s:Fin 5,
     o 5 (3*s.val) (cA g.val bf)=o 5 (3*(ad (I g) s).val) bf/\
     o 5 (3*s.val+1) (cA g.val bf)=o 5 (3*(ad (I g) s).val+1) bf/\
     o 5 (3*s.val+2) (cA g.val bf)=o 5 (3*(ad (I g) s).val+2) bf:=fun s=>by
   have h0:=cn g (ad (I g) s) 0 bf hpb0.2;have h1:=cn g (ad (I g) s) 1 bf hpb0.2;have h2:=cn g (ad (I g) s) 2 bf hpb0.2
   rw[cd] at h0 h1 h2;exact ⟨by simpa using h0,h1,h2⟩
 have b:∀ s:Fin 5,
     o 5 (3*s.val) (cA g.val be)=o 5 (3*(ad (I g) s).val) be/\
     o 5 (3*s.val+1) (cA g.val be)=o 5 (3*(ad (I g) s).val+1) be/\
     o 5 (3*s.val+2) (cA g.val be)=o 5 (3*(ad (I g) s).val+2) be:=fun s=>by
   have h0:=cn g (ad (I g) s) 0 be hpb1.2;have h1:=cn g (ad (I g) s) 1 be hpb1.2;have h2:=cn g (ad (I g) s) 2 be hpb1.2
   rw[cd] at h0 h1 h2;exact ⟨by simpa using h0,h1,h2⟩
 have a:∀ s:Fin 5,
     o 5 (3*s.val) (cA g.val bd)=o 5 (3*(ad (I g) s).val) bd/\
     o 5 (3*s.val+1) (cA g.val bd)=o 5 (3*(ad (I g) s).val+1) bd/\
     o 5 (3*s.val+2) (cA g.val bd)=o 5 (3*(ad (I g) s).val+2) bd:=fun s=>by
   have h0:=cn g (ad (I g) s) 0 bd hpb2.2;have h1:=cn g (ad (I g) s) 1 bd hpb2.2;have h2:=cn g (ad (I g) s) 2 bd hpb2.2
   rw[cd] at h0 h1 h2;exact ⟨by simpa using h0,h1,h2⟩
 unfold ay;unfold bH cx cY cA at *
 by_cases hg:g.val<5
 . have i:nB g.val 4=true:=bL.mpr (by omega);simp only[i,bT] at k j d h c b a ⊢;refine ⟨k,j,?_,?_,?_,?_,?_⟩
   . intro e;rw[(d e).1,(d e).2.1,(d e).2.2];have r0:=cJ g f (au (I g) e) 0;have r1:=cJ g f (au (I g) e) 1;have r2:=cJ g f (au (I g) e) 2;simp only[cE,hg,↓reduceIte] at r0 r1 r2;unfold cf;rw[r0,r1,r2];exact hdar _
   . intro e;rw[(h e).1,(h e).2.1,(h e).2.2];have r0:=du g f (au (I g) e) 0;have r1:=du g f (au (I g) e) 1;have r2:=du g f (au (I g) e) 2;simp only[cE,hg,↓reduceIte] at r0 r1 r2;unfold cg;rw[r0,r1,r2];exact hdac _
   . intro s;rw[(c s).1,(c s).2.1,(c s).2.2];have r0:=(aO g f (ad (I g) s) 0).1;have r1:=(aO g f (ad (I g) s) 1).1;have r2:=(aO g f (ad (I g) s) 2).1;simp only[cd] at r0 r1 r2;dsimp only;unfold ak;rw[r0,r1,r2];exact hdb0 _
   . intro s;rw[(b s).1,(b s).2.1,(b s).2.2];have r0:=(aO g f (ad (I g) s) 0).2.1;have r1:=(aO g f (ad (I g) s) 1).2.1;have r2:=(aO g f (ad (I g) s) 2).2.1;simp only[cd,hg,↓reduceIte] at r0 r1 r2;dsimp only;unfold ak;rw[r0,r1,r2];exact hdb1 _
   . intro s;rw[(a s).1,(a s).2.1,(a s).2.2];have r0:=(aO g f (ad (I g) s) 0).2.2;have r1:=(aO g f (ad (I g) s) 1).2.2;have r2:=(aO g f (ad (I g) s) 2).2.2;simp only[cd,hg,↓reduceIte] at r0 r1 r2;dsimp only;unfold ak;rw[r0,r1,r2];exact hdb2 _
 . have i:nB g.val 4=false:=by cases hb':nB g.val 4;rfl;exfalso;have:=bL.mp hb';omega
   simp only[i,bC] at k j d h c b a ⊢;refine ⟨k,j,?_,?_,?_,?_,?_⟩
   . intro e;rw[(h e).1,(h e).2.1,(h e).2.2];have r0:=cJ g f (au (I g) e) 0;have r1:=cJ g f (au (I g) e) 1;have r2:=cJ g f (au (I g) e) 2;simp only[cE,hg,↓reduceIte] at r0 r1 r2;unfold cf;rw[r0,r1,r2];exact hdac _
   . intro e;rw[(d e).1,(d e).2.1,(d e).2.2];have r0:=du g f (au (I g) e) 0;have r1:=du g f (au (I g) e) 1;have r2:=du g f (au (I g) e) 2;simp only[cE,hg,↓reduceIte] at r0 r1 r2;unfold cg;rw[r0,r1,r2];exact hdar _
   . intro s;rw[(c s).1,(c s).2.1,(c s).2.2];have r0:=(aO g f (ad (I g) s) 0).1;have r1:=(aO g f (ad (I g) s) 1).1;have r2:=(aO g f (ad (I g) s) 2).1;simp only[cd] at r0 r1 r2;dsimp only;unfold ak;rw[r0,r1,r2];exact hdb0 _
   . intro s;rw[(a s).1,(a s).2.1,(a s).2.2];have r0:=(aO g f (ad (I g) s) 0).2.1;have r1:=(aO g f (ad (I g) s) 1).2.1;have r2:=(aO g f (ad (I g) s) 2).2.1;simp only[cd,hg,↓reduceIte] at r0 r1 r2;dsimp only;unfold ak;rw[r0,r1,r2];exact hdb2 _
   . intro s;rw[(b s).1,(b s).2.1,(b s).2.2];have r0:=(aO g f (ad (I g) s) 0).2.2;have r1:=(aO g f (ad (I g) s) 1).2.2;have r2:=(aO g f (ad (I g) s) 2).2.2;simp only[cd,hg,↓reduceIte] at r0 r1 r2;dsimp only;unfold ak;rw[r0,r1,r2];exact hdb1 _
lemma jt (g:Fin 10) {p:AS} {f:(Fin 15->Bool)->Bool} (b:iP p)
   (d:dk p (R f)):dk (cB g.val p) (R (E g f)):=by
 have c:fv 0:=⟨fun _ _=>by simp[o],by norm_num⟩
 have a:az 0:=⟨fun _ _=>by simp[o],by norm_num⟩
 have h:=cX g (p:=(p.1,0,p.2.1,0,p.2.2.1,p.2.2.2,0,0,0)) (f:=f)
   ⟨b.1,c,b.2.1,b.2.2.1,a,a,a,b.2.2.2,by simp[bG]⟩
   ⟨d.1,fun _=>by simp[o],d.2.1,d.2.2,fun _=>by simp[o],fun _=>by simp[o],fun _=>by simp[o]⟩
 unfold ay at h;unfold cB;cases hb:nB g.val 4 <;> simp only[hb,bT,bC] at h ⊢
 . exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
 . exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
def bu (ax:Fin 3):Fin 3:=
 match ax.val with|0=>⟨0,by omega⟩|1=>⟨2,by omega⟩|_=>⟨1,by omega⟩
lemma cW (c:Nat) (hc:c<8):bq c<8:=by unfold bq;omega
lemma oS (c:Nat) (b:c<8) (ax:Fin 3) :
  (bq c).testBit ax.val=c.testBit (bu ax).val:=
 (by decide +kernel:∀ (x:Fin 8) (a:Fin 3),(bq x.val).testBit a.val=x.val.testBit (bu a).val) ⟨c,b⟩ ax
lemma i7 (m:Nat) (hm:m<2^15):dB m<2^15:=by
 have h4:m/4096<8:=by omega
 exact dl 3 _ _ _ _ _ (cW _ (nM _ (by decide)))
  (cW _ (nM _ (by decide))) (cW _ (nM _ (by decide)))
  (cW _ (nM _ (by decide))) (cW _ h4)
lemma jg (m:Nat) (i:m<2^15) (e:Fin 5) (ax:Fin 3) :
   (dB m).testBit (3*e.val+ax.val)=m.testBit (3*e.val+(bu ax).val):=by
 have h4:m/4096<8:=by omega
 have a:=cv 3 (bq (m % 8)) (bq ((m/8) % 8)) (bq ((m/64) % 8))
   (bq ((m/512) % 8)) (bq (m/4096))
   (cW _ (nM _ (by decide))) (cW _ (nM _ (by decide)))
   (cW _ (nM _ (by decide))) (cW _ (nM _ (by decide))) (cW _ h4)
 have h:o 3 e.val (dB m)=bq (o 3 e.val m):=by
   have d:dB m=bM 3 (bq (m % 8)) (bq ((m/8) % 8)) (bq ((m/64) % 8))
       (bq ((m/512) % 8)) (bq (m/4096)):=rfl
   rw[d]
   have j:e=0\/e=1\/e=2\/e=3\/e=4:=by fin_cases e <;> simp
   rcases j with rfl|rfl|rfl|rfl|rfl
   . change o 3 0 _=bq (o 3 0 m);rw[a.1,dD];rfl
   . change o 3 1 _=bq (o 3 1 m);rw[a.2.1,aS];rfl
   . change o 3 2 _=bq (o 3 2 m);rw[a.2.2.1,aS];rfl
   . change o 3 3 _=bq (o 3 3 m);rw[a.2.2.2.1,aS];rfl
   . change o 3 4 _=bq (o 3 4 m);rw[a.2.2.2.2,bB 3 4 m i];rfl
 have c:o 3 e.val m<8:=by rw[aS];exact nM _ (by decide)
 have h1:=congrArg (fun z=>z.testBit ax.val) h;rw[U,oS _ c ax,U] at h1;have b:(bu ax).val<3:=(bu ax).isLt;simpa [ax.isLt,b] using h1
lemma jb (r m:Nat) (hr:r<5) (a:m<2^15):pQ r m=ke 3 r m:=by
 have:r=0\/r=1\/r=2\/r=3\/r=4:=by omega
 rcases this with rfl|rfl|rfl|rfl|rfl
 . rfl
 . exact br 3 1 m (by omega) (by omega) a
 . exact br 3 2 m (by omega) (by omega) a
 . exact br 3 3 m (by omega) (by omega) a
 . exact br 3 4 m (by omega) (by omega) a
lemma my (m:Nat) (b:m<2^15):ss m=hP 3 m:=by
 have a:shiftRight m 12=land (shiftRight m 12) 7:=fZ 3 m b;unfold ss hP;dsimp only;rw[a];rfl
lemma fo (g m:Nat) (hg:g<10) (hm:m<2^30):bR g m<2^30:=by
 unfold bR;dsimp only
 have b:land m 32767=m % 32768:=by change m&&&(2^15 - 1)=_;exact nW m 15
 have c:shiftRight m 15=m/32768:=nD m 15;rw[b,c];have d:m % 32768<2^15:=nM _ (by decide)
 have h:m/32768<2^15:=by omega
 by_cases hg5:g<5
 . have a:nB g 4=true:=bL.mpr (by omega);simp only[a,bT,jb g _ hg5 d,jb g _ hg5 h];have h1:=dt 3 g (m % 32768) d;have h2:=dt 3 g (m/32768) h;change _|||(_ <<< 15)<_;rw[<- ce 15 _ _ h1];omega
 . have a:nB g 4=false:=by cases hb:nB g 4;rfl;exfalso;have:=bL.mp hb;omega
   have j:=i7 _ h;have i:=i7 _ d
   simp only[a,bC,my _ j,my _ i,
     jb (g - 5) _ (by omega) (cP 3 _)]
   have h1:=dt 3 (g - 5) _ (cP 3 (dB (m/32768)));have h2:=dt 3 (g - 5) _ (cP 3 (dB (m % 32768)));change _|||(_ <<< 15)<_;rw[<- ce 15 _ _ h1];omega
lemma cL (g:Fin 10) (e:Fin 5) (ax:Fin 3) (m:Nat) (hm:m<2^30) :
   (bR g.val m).testBit (3*(au g e).val+(if g.val<5 then ax.val else (bu ax).val)) =
     (if g.val<5 then m.testBit (3*e.val+ax.val) else m.testBit (15+3*e.val+ax.val))/\
   (bR g.val m).testBit (15+3*(au g e).val+(if g.val<5 then ax.val else (bu ax).val)) =
     (if g.val<5 then m.testBit (15+3*e.val+ax.val) else m.testBit (3*e.val+ax.val)):=by
 have v:land m 32767=m % 32768:=by change m&&&(2^15 - 1)=_;exact nW m 15
 have w:shiftRight m 15=m/32768:=nD m 15;have n:m % 32768<2^15:=nM _ (by decide)
 have y:m/32768<2^15:=by omega
 have F:∀ (a b:Nat) (k:Nat),a<2^15->k<15->(lor a (shiftLeft b 15)).testBit k=a.testBit k:=by
   intro a b k _ hk;change (a|||(b <<< 15)).testBit k=_
   rw[nI,nX];simp[show ¬ 15<=k by omega]
 have L:∀ (a b:Nat) (k:Nat),a<2^15->k<15->(lor a (shiftLeft b 15)).testBit (15+k)=b.testBit k:=by
   intro a b k ha _;change (a|||(b <<< 15)).testBit _=_
   rw[nI,nX,
     nT (lQ ha (nP (by omega) (by omega)))]
   simp
 have j:∀ (r x:Nat) (hr:r<5) (hx:x<2^15) (ei:Fin 5) (c:Fin 3),
     (ke 3 r x).testBit (3*((ei.val+r) % 5)+c.val)=x.testBit (3*ei.val+c.val):=by
   intro r x hr hx ei c;have K:=congrArg (fun z=>z.testBit c.val) (ee 3 r x ei.val hr ei.isLt hx);rw[U,U] at K;simpa [c.isLt] using K
 have C:∀ (x:Nat) (ei:Fin 5) (c:Fin 3),
     (hP 3 x).testBit (3*(4 - ei.val)+c.val)=x.testBit (3*ei.val+c.val):=by
   intro x ei c;have K:=congrArg (fun z=>z.testBit c.val) (lL 3 x ei.val ei.isLt);rw[U,U] at K;simpa [c.isLt] using K
 have h:∀ k<15,(m % 32768).testBit k=m.testBit k:=fun k hk=>by
   have:(m % 2^15).testBit k=(decide (k<15)&&m.testBit k):=Nat.testBit_mod_two_pow m 15 k
   simpa [hk] using this
 have i:∀ k<15,(m/32768).testBit k=m.testBit (15+k):=fun k _=>by
   have:(m/2^15).testBit k=m.testBit (15+k):=by rw[<- nD,nU]
   exact this
 unfold bR;dsimp only;rw[v,w]
 by_cases hg:g.val<5
 . have t:nB g.val 4=true:=bL.mpr (by omega);simp only[hg,↓reduceIte,t,bT,jb g.val _ hg n,jb g.val _ hg y]
   have u:(au g e).val=(e.val+g.val) % 5:=by unfold au;simp[hg]
   have d:3*(au g e).val+ax.val<15:=by omega
   have l:=dt 3 g.val (m % 32768) n
   rw[F _ _ _ l d,show 15+3*(au g e).val+ax.val=15+(3*(au g e).val+ax.val) by omega,
     L _ _ _ l d,u,j g.val _ hg n e ax,j g.val _ hg y e ax,
     h _ (by omega),i _ (by omega),Nat.add_assoc]
   exact ⟨rfl,rfl⟩
 . have t:nB g.val 4=false:=by cases hb:nB g.val 4;rfl;exfalso;have:=bL.mp hb;omega
   have P:=i7 _ y;have N:=i7 _ n
   simp only[hg,↓reduceIte,t,bC,my _ P,my _ N,
     jb (g.val - 5) _ (by omega) (cP 3 _)]
   have u:(au g e).val=((4 - e.val)+(g.val - 5)) % 5:=by unfold au;simp only[hg,↓reduceIte];omega
   have d:3*(au g e).val+(bu ax).val<15:=by have:=(bu ax).isLt;omega
   have l:=dt 3 (g.val - 5) _ (cP 3 (dB (m/32768)))
   rw[F _ _ _ l d,
     show 15+3*(au g e).val+(bu ax).val=15+(3*(au g e).val+(bu ax).val) by omega,
     L _ _ _ l d,u,
     j (g.val - 5) _ (by omega) (cP 3 _) ⟨4 - e.val,by omega⟩ (bu ax),
     j (g.val - 5) _ (by omega) (cP 3 _) ⟨4 - e.val,by omega⟩ (bu ax)]
   dsimp only;rw[C _ e (bu ax),C _ e (bu ax),jg _ y,jg _ n]
   have M:bu (bu ax)=ax:=by fin_cases ax <;> rfl
   rw[M,i _ (by omega),h _ (by omega),Nat.add_assoc];exact ⟨rfl,rfl⟩
lemma mX:∀ (g:Fin 10) (e:Fin 5) (ax:Fin 3),g.val<5->
 ((au g e).val+cH ax) % 5=(ad g ⟨(e.val+cH ax) % 5,by omega⟩).val/\
 (((au g e).val+1) % 5+cH ax) % 5=(ad g ⟨((e.val+1) % 5+cH ax) % 5,by omega⟩).val:=by decide +kernel
lemma lX:∀ (g:Fin 10) (e:Fin 5) (ax:Fin 3),¬ g.val<5->
 ((au g e).val+cH (bu ax)) % 5=(ad g ⟨((e.val+1) % 5+cH ax) % 5,by omega⟩).val/\
 (((au g e).val+1) % 5+cH (bu ax)) % 5=(ad g ⟨(e.val+cH ax) % 5,by omega⟩).val:=by decide +kernel
lemma hE (g:Fin 10) {p:RL} {f:(Fin 15->Bool)->Bool} (u:gw p)
   (x:dj p (R f) (O f)):dj (d7 g.val p) (R (E g f)) (O (E g f)):=by
 refine ⟨cX g u.1 x.1,?_,?_⟩
 . intro e ax hb;set b:=au (I g) e;set a:=if g.val<5 then ax else bu ax
   have v:(if g.val<5 then a.val else (bu a).val)=ax.val:=by
     dsimp only[a];split_ifs;rfl;fin_cases ax <;> rfl
   have d:au g b=e:=cE g e;have w:=(cL g b a p.2 u.2).1;unfold d7 at hb;dsimp only at hb;rw[d,v] at w;rw[w] at hb;unfold lY;rw[decide_eq_true_iff];intro k hbs
   by_cases hg:g.val<5
   . dsimp only[a] at hb;simp only[hg,↓reduceIte] at hb;have i:=x.2.1 b ax hb;unfold lY at i;rw[decide_eq_true_iff] at i;have t:=(mX g b ax hg).1;rw[d] at t
     have c:(⟨(e.val+cH ax) % 5,by omega⟩:Fin 5)=ad g ⟨(b.val+cH ax) % 5,by omega⟩:=fE t
     rw[c] at hbs
     have hbs':S (O f) ⟨(b.val+cH ax) % 5,by omega⟩ ax k=9:=by
       have h:=aO g f ⟨(b.val+cH ax) % 5,by omega⟩ k
       have l:ax=0\/ax=1\/ax=2:=by fin_cases ax <;> simp
       rcases l with rfl|rfl|rfl
       . rw[h.1] at hbs;exact hbs
       . rw[h.2.1] at hbs;simpa [hg] using hbs
       . rw[h.2.2] at hbs;simpa [hg] using hbs
     have m:=cJ g f b k;rw[d] at m;simp only[hg,↓reduceIte] at m;rw[m];exact i k hbs'
   . simp only[hg,↓reduceIte] at hb;have j:=x.2.2 b a hb;unfold m4 at j;rw[decide_eq_true_iff] at j;have t:=(lX g b a hg).1
     have r:bu a=ax:=by dsimp only[a];simp only[hg,↓reduceIte];fin_cases ax <;> rfl
     rw[d,r] at t
     have c:(⟨(e.val+cH ax) % 5,by omega⟩:Fin 5)=ad g ⟨((b.val+1) % 5+cH a) % 5,by omega⟩:=fE t
     rw[c] at hbs
     have hbs':S (O f) ⟨((b.val+1) % 5+cH a) % 5,by omega⟩ a k=9:=by
       dsimp only[a] at hbs ⊢;simp only[hg,↓reduceIte] at hbs ⊢
       have h:=aO g f ⟨((b.val+1) % 5+cH (bu ax)) % 5,by omega⟩ k
       have l:ax=0\/ax=1\/ax=2:=by fin_cases ax <;> simp
       rcases l with rfl|rfl|rfl
       . rw[h.1] at hbs;exact hbs
       . rw[h.2.1] at hbs;simpa [hg,bu] using hbs
       . rw[h.2.2] at hbs;simpa [hg,bu] using hbs
     have m:=cJ g f b k;rw[d] at m;simp only[hg,↓reduceIte] at m;rw[m];exact j k hbs'
 . intro e ax hb;set b:=au (I g) e;set a:=if g.val<5 then ax else bu ax
   have v:(if g.val<5 then a.val else (bu a).val)=ax.val:=by
     dsimp only[a];split_ifs;rfl;fin_cases ax <;> rfl
   have d:au g b=e:=cE g e;have w:=(cL g b a p.2 u.2).2;unfold d7 at hb;dsimp only at hb;rw[d,v] at w;rw[w] at hb;unfold m4;rw[decide_eq_true_iff];intro k hbs
   by_cases hg:g.val<5
   . dsimp only[a] at hb;simp only[hg,↓reduceIte] at hb;have j:=x.2.2 b ax hb;unfold m4 at j;rw[decide_eq_true_iff] at j;have t:=(mX g b ax hg).2;rw[d] at t
     have c:(⟨((e.val+1) % 5+cH ax) % 5,by omega⟩:Fin 5)=ad g ⟨((b.val+1) % 5+cH ax) % 5,by omega⟩:=fE t
     rw[c] at hbs
     have hbs':S (O f) ⟨((b.val+1) % 5+cH ax) % 5,by omega⟩ ax k=9:=by
       have h:=aO g f ⟨((b.val+1) % 5+cH ax) % 5,by omega⟩ k
       have l:ax=0\/ax=1\/ax=2:=by fin_cases ax <;> simp
       rcases l with rfl|rfl|rfl
       . rw[h.1] at hbs;exact hbs
       . rw[h.2.1] at hbs;simpa [hg] using hbs
       . rw[h.2.2] at hbs;simpa [hg] using hbs
     have n:=du g f b k;rw[d] at n;simp only[hg,↓reduceIte] at n;rw[n];exact j k hbs'
   . simp only[hg,↓reduceIte] at hb;have i:=x.2.1 b a hb;unfold lY at i;rw[decide_eq_true_iff] at i;have t:=(lX g b a hg).2
     have r:bu a=ax:=by dsimp only[a];simp only[hg,↓reduceIte];fin_cases ax <;> rfl
     rw[d,r] at t
     have c:(⟨((e.val+1) % 5+cH ax) % 5,by omega⟩:Fin 5)=ad g ⟨(b.val+cH a) % 5,by omega⟩:=fE t
     rw[c] at hbs
     have hbs':S (O f) ⟨(b.val+cH a) % 5,by omega⟩ a k=9:=by
       dsimp only[a] at hbs ⊢;simp only[hg,↓reduceIte] at hbs ⊢
       have h:=aO g f ⟨(b.val+cH (bu ax)) % 5,by omega⟩ k
       have l:ax=0\/ax=1\/ax=2:=by fin_cases ax <;> simp
       rcases l with rfl|rfl|rfl
       . rw[h.1] at hbs;exact hbs
       . rw[h.2.1] at hbs;simpa [hg,bu] using hbs
       . rw[h.2.2] at hbs;simpa [hg,bu] using hbs
     have n:=du g f b k;rw[d] at n;simp only[hg,↓reduceIte] at n;rw[n];exact i k hbs'
lemma jQ (g:Fin 10) (x:RL) (a:gw x):gw (d7 g.val x):=
 ⟨cy g x.1 a.1,fo g.val x.2 g.isLt a.2⟩
def hI (w e c:Nat):Nat:=
 let a:=aL w e
 match c with|0=>land a 7|1=>land (shiftRight a 3) 7|_=>shiftRight a 6
def en (w s c:Nat):Nat:=
 let a:=V w s
 match c with|0=>land a 31|1=>land (shiftRight a 5) 31|_=>shiftRight a 10
lemma cc (w e c:Nat) (b:cq w) (d:e<5) (h:c<3) :
   hI w e c=o 3 (3*e+c) w:=by
 rw[<- aY 3 c e w h,<-m7 w e b.2 d]
 have a:aL w e<2^9:=by rw[m7 w e b.2 d,aS];exact nM _ (by decide)
 unfold hI
 have:c=0\/c=1\/c=2:=by omega
 rcases this with rfl|rfl|rfl
 . unfold o;simp
 . rfl
 . rw[bB 3 2 _ a];exact nD _ 6
lemma j0 (w s c:Nat) (b:az w) (d:s<5) (h:c<3) :
   en w s c=o 5 (3*s+c) w:=by
 rw[<- aY 5 c s w h,<-kI w s b.2 d]
 have a:V w s<2^15:=by rw[kI w s b.2 d,aS];exact nM _ (by decide)
 unfold en
 have:c=0\/c=1\/c=2:=by omega
 rcases this with rfl|rfl|rfl
 . unfold o;simp
 . rfl
 . rw[bB 5 2 _ a];exact nD _ 10
def sI (a b:Nat):Nat:=
 let d:=land ((lor a 0x8040201008) - b) 0x8040201008;let m:=d - shiftRight d 3
 lor (land b m) (land a (0x70381c0e07 - m))
def p8 (v:Nat):Nat:=
 let d:=land (v+0x4020100804) 0x8040201008;let m:=d - shiftRight d 3
 lor (land v (0x70381c0e07 - m)) (land 0x30180c0603 m)
def ez (pr qr:Nat):Nat:=
 let gt:=land pr 0x70381c0e07;let fP:=land (shiftRight pr 3) 0x70381c0e07;let ey:=land (shiftRight pr 6) 0x70381c0e07;let c:=land qr 0x70381c0e07;let b:=land (shiftRight qr 3) 0x70381c0e07;let a:=land (shiftRight qr 6) 0x70381c0e07;let i:=p8 (sI (gt+a) (sI (fP+b) (ey+c)));let h:=p8 (sI (fP+a) (ey+b));let d:=p8 (ey+a)
 lor i (lor (shiftLeft h 3) (shiftLeft d 6))
def kC (a b:Nat):Nat:=
 let d:=land ((lor a 0x124924924924) - b) 0x124924924924;let m:=d - shiftRight d 2
 lor (land b m) (land a (0xdb6db6db6db - m))
def fg (pc:Nat):Nat:=
 let f:=land (shiftRight (pc+0xdb6db6db6db) 2) 0x49249249249
 land (f+shiftRight f 3+shiftRight f 6) 0x70381c0e07
def dH (pr pc qr qc:Nat):Nat:=
 let b:=kC (fg pc) (fg qc);let a:=lor b (lor (shiftLeft b 3) (shiftLeft b 6))
 kC (kC pr qr) a
def eA (pr pc qr qc:Nat) (e:Nat):Nat:=
 let k:=aL pr e;let d:=aL qr e;let l:=aL pc e;let i:=aL qc e;let gt:=land k 7;let fP:=land (shiftRight k 3) 7;let ey:=shiftRight k 6;let n:=land d 7;let h:=land (shiftRight d 3) 7;let a:=shiftRight d 6;let C:=av 3 (av (gt+a) (av (fP+h) (ey+n)));let z:=av 3 (av (fP+a) (ey+h));let y:=av 3 (ey+a);let t:=land l 7;let m:=land (shiftRight l 3) 7;let c:=shiftRight l 6;let r:=land i 7;let j:=land (shiftRight i 3) 7;let b:=shiftRight i 6;let L:=av 3 (av (t+b) (av (m+j) (c+r)));let K:=av 3 (av (m+b) (c+j));let F:=av 3 (c+b);let w:=(1 - gt)+(1 - fP)+(1 - ey);let x:=(1 - t)+(1 - m)+(1 - c);let u:=(1 - n)+(1 - h)+(1 - a);let v:=(1 - r)+(1 - j)+(1 - b)
 av (C+z+y) (av (L+K+F) (9 - aa (w*v) (x*u)))
def d6 (pr pc qr qc:Nat) (e:Nat):Nat:=
 let c:=aL pr e;let a:=aL qr e;let d:=aL pc e;let b:=aL qc e;let gt:=land c 7;let fP:=land (shiftRight c 3) 7;let ey:=shiftRight c 6;let j:=land a 7;let i:=land (shiftRight a 3) 7;let h:=shiftRight a 6;let t:=land d 7;let r:=land (shiftRight d 3) 7;let n:=shiftRight d 6;let m:=land b 7;let l:=land (shiftRight b 3) 7;let k:=shiftRight b 6
 av (av gt j+av fP i+av ey h)
  (av (av t m+av r l+av n k)
   (av (g7 gt fP ey m l k) (g7 t r n j i h)))
def ff (p0 p1 p2 q0 q1 q2:Nat) (s:Nat):Nat:=
 let M:=V p0 s;let L:=V p1 s;let K:=V p2 s;let F:=V q0 s;let C:=V q1 s;let z:=V q2 s
 cond (nE (M+L+K+F+C+z) 0) 0
 (let y:=land M 31;let x:=land (shiftRight M 5) 31;let w:=shiftRight M 10
  let v:=land L 31;let u:=land (shiftRight L 5) 31;let t:=shiftRight L 10;let r:=land K 31;let n:=land (shiftRight K 5) 31;let m:=shiftRight K 10;let l:=land F 31;let k:=land (shiftRight F 5) 31;let j:=shiftRight F 10;let i:=land C 31;let h:=land (shiftRight C 5) 31;let d:=shiftRight C 10;let c:=land z 31;let b:=land (shiftRight z 5) 31;let a:=shiftRight z 10;let s0:=aa y l+aa x k+aa w j;let s1:=aa v i+aa u h+aa t d;let s2:=aa r c+aa n b+aa m a;let a0:=dm y x w i h d;let W:=dm y x w c b a;let T:=dm v u t l k j;let Q:=dm v u t c b a;let P:=dm r n m l k j;let N:=dm r n m i h d
  aa s0 (aa s1 (aa s2 (aa a0 (aa W (aa T (aa Q (aa P N))))))))
def dh (p0 p1 p2 q0 q1 q2:Nat) (s:Nat):Nat:=
 let M:=V p0 s;let L:=V p1 s;let K:=V p2 s;let F:=V q0 s;let C:=V q1 s;let z:=V q2 s
 cond (nE (M+L+K) 0||nE (F+C+z) 0) 0
 (let y:=land M 31;let x:=land (shiftRight M 5) 31;let w:=shiftRight M 10
  let v:=land L 31;let u:=land (shiftRight L 5) 31;let t:=shiftRight L 10;let r:=land K 31;let n:=land (shiftRight K 5) 31;let m:=shiftRight K 10;let l:=land F 31;let k:=land (shiftRight F 5) 31;let j:=shiftRight F 10;let i:=land C 31;let h:=land (shiftRight C 5) 31;let d:=shiftRight C 10;let c:=land z 31;let b:=land (shiftRight z 5) 31;let a:=shiftRight z 10;let s0:=(y+j-9)+(x+k-9)+(w+l-9);let s1:=(v+d-9)+(u+h-9)+(t+i-9);let s2:=(r+a-9)+(n+b-9)+(m+c-9);let a0:=d5 y x w i h d;let W:=d5 y x w c b a;let T:=d5 v u t l k j;let Q:=d5 v u t c b a;let P:=d5 r n m l k j;let N:=d5 r n m i h d
  aa s0 (aa s1 (aa s2 (aa a0 (aa W (aa T (aa Q (aa P N))))))))
def em (p q:Nat):Nat:=
 let d:=land ((lor p 0x4210842108421084210) - q) 0x4210842108421084210;let m:=d - shiftRight d 4
 lor (land p m) (land q (0x3def7bdef7bdef7bdef - m))
def ge (a b:Nat):Nat:=
 let d:=land ((lor a 0x20004000800100020) - b) 0x20004000800100020;let m:=d - shiftRight d 5
 lor (land a m) (land b (0x1f003e007c00f801f - m))
def it (v:Nat):Nat:=
 let x:=v+0x7000e001c0038007;let d:=land x 0x10002000400080010
 land x (d - shiftRight d 4)
def cp (p q:Nat):Nat:=
 cond (nE p 0||nE q 0) 0
 (let b:=land p 0x1f003e007c00f801f
  let d:=land (shiftRight p 5) 0x1f003e007c00f801f;let l:=land (shiftRight p 10) 0x1f003e007c00f801f;let a:=land q 0x1f003e007c00f801f;let c:=land (shiftRight q 5) 0x1f003e007c00f801f;let k:=land (shiftRight q 10) 0x1f003e007c00f801f;let j:=it (b+a);let i:=it (ge (b+c) (d+a));let h:=it (ge (b+k) (ge (d+c) (l+a)))
  lor j (lor (shiftLeft i 5) (shiftLeft h 10)))
def cO (c:Nat):Nat:=
 let a:=shiftRight c 10
 cond (nB a 6) 0 ((land c 31 - 6)+(land (shiftRight c 5) 31 - 6)+(a - 6))
def aE (pa pb pc qa qb qc:Nat) (s:Nat):Nat:=
 let b:=V pa s;let a:=V qa s
 let c:=aa (aa (cO (V pb s)) (cO (V qb s)))
    (aa (cO (V pc s)) (cO (V qc s)))
 cond (nE c 0)
  (lor (lor (aa (land b 31) (land a 31))
   (shiftLeft (aa (land (shiftRight b 5) 31) (land (shiftRight a 5) 31)) 5))
   (shiftLeft (aa (shiftRight b 10) (shiftRight a 10)) 10))
  (lor (lor (aa c (aa (land b 31) (land a 31)))
   (shiftLeft (aa c (aa (land (shiftRight b 5) 31) (land (shiftRight a 5) 31))) 5))
   (shiftLeft (aa c (aa (shiftRight b 10) (shiftRight a 10))) 10))
def ci (pa pb pc qa qb qc:Nat):Nat:=
 cond (nE (lor (lor pb pc) (lor qb qc)) 0) (em pa qa)
 (lor (lor (lor (lor
  (aE pa pb pc qa qb qc 0)
  (shiftLeft (aE pa pb pc qa qb qc 1) 15))
  (shiftLeft (aE pa pb pc qa qb qc 2) 30))
  (shiftLeft (aE pa pb pc qa qb qc 3) 45))
  (shiftLeft (aE pa pb pc qa qb qc 4) 60))
def es (u v:Nat):Nat:=
 let v2:=shiftRight v 10
 cond (nB (u+v2) 15) 0
 ((u+land v 31 - 15)+(u+land (shiftRight v 5) 31 - 15)+(u+v2 - 15))
def bp (pa pb pc qa qb qc:Nat) (s:Nat):Nat:=
 let m:=V pa s;let j:=V qa s;let b:=land m 31;let d:=land (shiftRight m 5) 31;let i:=shiftRight m 10;let a:=land j 31;let c:=land (shiftRight j 5) 31;let h:=shiftRight j 10;let r:=V pb s;let n:=V pc s;let l:=V qb s;let k:=V qc s;let v:=aa (b+a - 9) (aa (aa (es b l) (es a r)) (aa (es b k) (es a n)));let u:=aa (aa (b+c) (d+a) - 9) (aa (aa (es d l) (es c r)) (aa (es d k) (es c n)));let t:=aa (aa (b+h) (aa (d+c) (i+a)) - 9) (aa (aa (es i l) (es h r)) (aa (es i k) (es h n)))
 lor (lor v (shiftLeft u 5)) (shiftLeft t 10)
def eN (pa pb pc qa qb qc:Nat):Nat:=
 cond (nE (lor (lor pa pb) pc) 0||nE (lor (lor qa qb) qc) 0) 0
 (cond (nE (lor (lor pb pc) (lor qb qc)) 0) (cp pa qa)
 (lor (lor (lor (lor
  (bp pa pb pc qa qb qc 0)
  (shiftLeft (bp pa pb pc qa qb qc 1) 15))
  (shiftLeft (bp pa pb pc qa qb qc 2) 30))
  (shiftLeft (bp pa pb pc qa qb qc 3) 45))
  (shiftLeft (bp pa pb pc qa qb qc 4) 60)))
def bi {α:Type} (f:α->Bool):List α->Bool
 | []=>true
 | x :: xs=>f x&&bi f xs
lemma aC {α:Type} {f:α->Bool} {L:List α} (h:bi f L=true) :
   ∀ x ∈ L,f x=true:=by
 induction L with
 | nil=>intro x hx;cases hx
 | cons a t ih=>
   unfold bi at h;simp only[bA] at h;intro x hx;rcases List.mem_cons.mp hx with rfl|ht
   . exact h.1
   . exact ih h.2 x ht
def J {α:Type} (ok:α->α->Bool):List α->Bool
 | []=>true
 | q :: rest=>ok q q&&bi (fun p=>ok q p) rest&&J ok rest
def gg {α:Type} (ok:α->α->Bool) (q:α):List (List α)->Bool
 | []=>true
 | g :: gs=>bi (fun p=>ok p q) g&&gg ok q gs
def H {α:Type} (ok:α->α->Bool) (prev:List (List α)):List α->Bool
 | []=>true
 | q :: rest=>gg ok q prev&&H ok prev rest
lemma dU {α:Type} {ok:α->α->Bool} {L:List α} (h:J ok L=true) :
   ∀ p ∈ L,∀ q ∈ L,ok p q=true\/ok q p=true:=by
 induction L with
 | nil=>intro p hp;cases hp
 | cons a t ih=>
   unfold J at h;simp only[bA] at h;have b:=aC h.1.2;intro p hp q hq;rcases List.mem_cons.mp hp with rfl|hpt
   . rcases List.mem_cons.mp hq with rfl|hqt
     . exact oL h.1.1
     . exact oL (b q hqt)
   . rcases List.mem_cons.mp hq with rfl|hqt
     . exact oR (b p hpt)
     . exact ih h.2 p hpt q hqt
lemma li {α:Type} {ok:α->α->Bool} {q:α} {b:List (List α)}
   (h:gg ok q b=true):∀ g ∈ b,∀ p ∈ g,ok p q=true:=by
 induction b with
 | nil=>intro g hg;cases hg
 | cons a t ih=>
   unfold gg at h;simp only[bA] at h;intro g hg;rcases List.mem_cons.mp hg with rfl|hgt
   . exact aC h.1
   . exact ih h.2 g hgt
lemma jL {α:Type} {ok:α->α->Bool} {b:List (List α)} {c:List α}
   (h:H ok b c=true):∀ g ∈ b,∀ p ∈ g,∀ q ∈ c,ok p q=true:=by
 induction c with
 | nil=>intro g _ p _ q hq;cases hq
 | cons a t ih=>
   unfold H at h;simp only[bA] at h;intro g hg p hp q hq;rcases List.mem_cons.mp hq with rfl|hqt
   . exact li h.1 g hg p hp
   . exact ih h.2 g hg p hp q hqt
lemma jK {α:Type} {ok:α->α->Bool} {chunks:List (List α)}
   (h:∀ k:Fin chunks.length,J ok chunks[k]=true/\H ok (chunks.take k.val) chunks[k]=true) :
   ∀ p ∈ chunks.flatten,∀ q ∈ chunks.flatten,ok p q=true\/ok q p=true:=by
 intro p hp q hq;rcases List.mem_flatten.mp hp with ⟨gp,hgp,hpg⟩;rcases List.mem_flatten.mp hq with ⟨gq,hgq,hqg⟩;rcases List.getElem_of_mem hgp with ⟨ip,hip,rfl⟩;rcases List.getElem_of_mem hgq with ⟨iq,hiq,rfl⟩
 by_cases hlt:ip<iq
 . left
   have a:chunks[ip] ∈ chunks.take iq:=by
     have:(chunks.take iq)[ip]'(by simp;omega)=chunks[ip]:=by simp
     rw[<- this];exact List.getElem_mem _
   exact jL (h ⟨iq,hiq⟩).2 chunks[ip] a p hpg q hqg
 . by_cases hgt:iq<ip
   . right
     have a:chunks[iq] ∈ chunks.take ip:=by
       have:(chunks.take ip)[iq]'(by simp;omega)=chunks[iq]:=by simp
       rw[<- this];exact List.getElem_mem _
     exact jL (h ⟨ip,hip⟩).2 chunks[iq] a q hqg p hpg
   . have b:ip=iq:=by omega
     subst b;exact dU (h ⟨ip,hip⟩).1 p hpg q hqg
lemma lJ (M:Fin 3->Fin 3->Bool) (c:Fin 3):Y (fun r c'=>M c' r) c=aQ M c:=rfl
lemma sX (M:Fin 3->Fin 3->Bool) (r:Fin 3):aQ (fun r' c=>M c r') r=Y M r:=rfl
lemma kw (M:Fin 3->Fin 3->Bool):gz (fun r c=>M c r)=gz M:=(gM M).symm
lemma zl {a b c d:Nat} (h1:a<=c) (h2:b<=d):av a b<=av c d:=by
 simp only[aG];omega
lemma zn {a b c d:Nat} (h1:a<=c) (h2:b<=d):aa a b<=aa c d:=by
 simp only[aP];omega
lemma aV {a b c:Nat} (h1:a<=c) (h2:b<=c):aa a b<=c:=by
 simp only[aP];omega
lemma gT {a b c:Nat}:a<=av b c ↔ a<=b/\a<=c:=by
 simp only[aG];omega
lemma cz (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 A (fun a c b=>P a b c) k=A P k:=by unfold A aq;dsimp only;ring
lemma bK (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 Z (fun a c b=>P a b c) k=aK P k:=rfl
lemma oP (P:Fin 3->Fin 3->Fin 3->Bool) :
 cU (fun a c b=>P a b c)=cU P:=by unfold cU A aq;dsimp only;ring
lemma aT (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 A (fun b a c=>P a b c) k=Z P k:=rfl
lemma eE (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 Z (fun b a c=>P a b c) k=A P k:=rfl
lemma fx (P:Fin 3->Fin 3->Fin 3->Bool) :
 cU (fun b a c=>P a b c)=cU P:=by unfold cU A aq;dsimp only;ring
lemma eG (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 A (fun b c a=>P a b c) k=Z P k:=by unfold A Z aq;dsimp only;ring
lemma eD (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 Z (fun b c a=>P a b c) k=aK P k:=by unfold Z aK A aq;dsimp only;ring
lemma oO (P:Fin 3->Fin 3->Fin 3->Bool) :
 cU (fun b c a=>P a b c)=cU P:=by unfold cU A aq;dsimp only;ring
lemma dd (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 Z (fun c a b=>P a b c) k=A P k:=by unfold Z A aq;dsimp only;ring
lemma e8 (P:Fin 3->Fin 3->Fin 3->Bool) :
 cU (fun c a b=>P a b c)=cU P:=by unfold cU A aq;dsimp only;ring
lemma eF (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 A (fun c b a=>P a b c) k=aK P k:=by unfold aK A aq;dsimp only;ring
lemma eC (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3) :
 Z (fun c b a=>P a b c) k=Z P k:=by unfold Z aq;dsimp only;ring
lemma oN (P:Fin 3->Fin 3->Fin 3->Bool) :
 cU (fun c b a=>P a b c)=cU P:=by unfold cU A aq;dsimp only;ring
lemma aH (w s:Nat) (a:az w) (b:s<5):land (V w s) 31=o 5 (3*s) w:=by
 simpa [en] using j0 w s 0 a b (by omega)
lemma ai (w s:Nat) (a:az w) (b:s<5):land (shiftRight (V w s) 5) 31=o 5 (3*s+1) w:=
 j0 w s 1 a b (by omega)
lemma aA (w s:Nat) (a:az w) (b:s<5):shiftRight (V w s) 10=o 5 (3*s+2) w:=
 j0 w s 2 a b (by omega)
lemma ky (c:Nat):cO c<=(land c 31 - 6)+(land (shiftRight c 5) 31 - 6)+(shiftRight c 10 - 6):=by
 unfold cO;dsimp only;cases nB (shiftRight c 10) 6
 . exact lR _
 . exact Nat.zero_le _
lemma zw (u v:Nat):es u v<=(u+land v 31 - 15)+(u+land (shiftRight v 5) 31 - 15)+(u+shiftRight v 10 - 15):=by
 unfold es;dsimp only;cases nB (u+shiftRight v 10) 15
 . exact lR _
 . exact Nat.zero_le _
lemma sF (m i d l c b s:Nat) :
   aE m i d l c b s =
   let k:=V m s;let j:=V l s
   let a:=aa (aa (cO (V i s)) (cO (V c s)))
                  (aa (cO (V d s)) (cO (V b s)))
   lor (lor (aa a (aa (land k 31) (land j 31)))
     (shiftLeft (aa a (aa (land (shiftRight k 5) 31) (land (shiftRight j 5) 31))) 5))
     (shiftLeft (aa a (aa (shiftRight k 10) (shiftRight j 10))) 10):=by
 unfold aE;dsimp only
 set a:=aa (aa (cO (V i s)) (cO (V c s)))
                (aa (cO (V d s)) (cO (V b s)))
 cases h:nE a 0
 . rfl
 . have h0:=bQ h;rw[h0];simp only[bT,aP,Nat.zero_max]
lemma sO:∀ i:Fin 5,o 9 i.val 0x70381c0e07=7:=by decide +kernel
lemma sM:∀ i:Fin 5,o 9 i.val 0x8040201008=8:=by decide +kernel
lemma xz:∀ i:Fin 5,o 9 i.val 0x4020100804=4:=by decide +kernel
lemma vK:∀ i:Fin 5,o 9 i.val 0x30180c0603=3:=by decide +kernel
lemma xw:∀ i:Fin 15,o 3 i.val 0x49249249249=1:=by decide +kernel
lemma Cg:∀ i:Fin 15,o 3 i.val 0x70381c0e07=if i.val % 3=0 then 7 else 0:=by decide +kernel
lemma xC:∀ i:Fin 15,o 5 i.val 0x3def7bdef7bdef7bdef=15:=by decide +kernel
lemma uN:∀ i:Fin 5,o 15 i.val 0x1f003e007c00f801f=31:=by decide +kernel
lemma xx:∀ i:Fin 5,o 15 i.val 0x20004000800100020=32:=by decide +kernel
lemma xy:∀ i:Fin 5,o 15 i.val 0x10002000400080010=16:=by decide +kernel
lemma tC:∀ i:Fin 5,o 15 i.val 0x7000e001c0038007=7:=by decide +kernel
lemma lU {a b:Nat} (k:a<2^45) (j:b<2^45)
  (d:∀ i<5,o 9 i a<8) (c:∀ i<5,o 9 i b<8) :
  sI a b<2^45/\∀ i<5,o 9 i (sI a b)=min (o 9 i a) (o 9 i b):=by
 have h:=de 9 3 5 a b 0x8040201008 0x70381c0e07 (by omega) k j (by decide) (by decide)
  (fun i hi=>sM ⟨i,hi⟩) (fun i hi=>sO ⟨i,hi⟩) d c
 exact ⟨h.2.2.2,h.2.1⟩
lemma kD {v:Nat} (b:v<2^45) (a:∀ i<5,o 9 i v<12) :
  p8 v<2^45/\∀ i<5,o 9 i (p8 v)=min 3 (o 9 i v):=by
 have h:=jf 9 3 3 5 v 0x4020100804 0x8040201008 0x70381c0e07 0x30180c0603
  (by omega) (by decide) b (by decide) (by decide) (by decide) (by decide)
  (fun i hi=>xz ⟨i,hi⟩) (fun i hi=>sM ⟨i,hi⟩)
  (fun i hi=>sO ⟨i,hi⟩) (fun i hi=>vK ⟨i,hi⟩)
  (fun i hi=>by have:=a i hi;omega)
 exact ⟨h.2,h.1⟩
lemma no {k j:Nat} (c:cq k) (b:cq j) :
   cq (ez k j)/\∀ e:Fin 5,
     o 3 (3*e.val) (ez k j)=min 3 (min (o 3 (3*e.val) k+o 3 (3*e.val+2) j)
       (min (o 3 (3*e.val+1) k+o 3 (3*e.val+1) j) (o 3 (3*e.val+2) k+o 3 (3*e.val) j)))/\
     o 3 (3*e.val+1) (ez k j)=min 3 (min (o 3 (3*e.val+1) k+o 3 (3*e.val+2) j)
       (o 3 (3*e.val+2) k+o 3 (3*e.val+1) j))/\
     o 3 (3*e.val+2) (ez k j)=min 3 (o 3 (3*e.val+2) k+o 3 (3*e.val+2) j):=by
 unfold ez;dsimp only
 have a:(0x70381c0e07:Nat)<2^45:=by decide
 have d:∀ i<5,o 9 i 0x70381c0e07=7:=fun i hi=>sO ⟨i,hi⟩;set gt:=land k 0x70381c0e07;set fP:=land (shiftRight k 3) 0x70381c0e07;set ey:=land (shiftRight k 6) 0x70381c0e07;set W:=land j 0x70381c0e07;set M:=land (shiftRight j 3) 0x70381c0e07;set x:=land (shiftRight j 6) 0x70381c0e07
 have T:∀ i<5,o 9 i gt=o 3 (3*i) k:=fun i hi=>by
   have h:=cb 3 5 0 k 0x70381c0e07 d i hi;simp only[Nat.zero_mul,nZ] at h;exact h
 have r:∀ i<5,o 9 i fP=o 3 (3*i+1) k:=cb 3 5 1 k 0x70381c0e07 d;have n:∀ i<5,o 9 i ey=o 3 (3*i+2) k:=cb 3 5 2 k 0x70381c0e07 d
 have a4:∀ i<5,o 9 i W=o 3 (3*i) j:=fun i hi=>by
   have h:=cb 3 5 0 j 0x70381c0e07 d i hi;simp only[Nat.zero_mul,nZ] at h;exact h
 have w:∀ i<5,o 9 i M=o 3 (3*i+1) j:=cb 3 5 1 j 0x70381c0e07 d;have l:∀ i<5,o 9 i x=o 3 (3*i+2) j:=cb 3 5 2 j 0x70381c0e07 d;have a9:gt<2^45:=lO nR a;have a6:fP<2^45:=lO nR a;have a1:ey<2^45:=lO nR a;have a8:W<2^45:=lO nR a;have a5:M<2^45:=lO nR a;have a0:x<2^45:=lO nR a;have v:=ap 9 5 gt x (fun i hi=>by rw[T i hi,l i hi];have:=c.1 (3*i) (by omega);have:=b.1 (3*i+2) (by omega);omega) a9 a0;have u:=ap 9 5 fP M (fun i hi=>by rw[r i hi,w i hi];have:=c.1 (3*i+1) (by omega);have:=b.1 (3*i+1) (by omega);omega) a6 a5;have L:=ap 9 5 ey W (fun i hi=>by rw[n i hi,a4 i hi];have:=c.1 (3*i+2) (by omega);have:=b.1 (3*i) (by omega);omega) a1 a8;have t:=ap 9 5 fP x (fun i hi=>by rw[r i hi,l i hi];have:=c.1 (3*i+1) (by omega);have:=b.1 (3*i+2) (by omega);omega) a6 a0;have K:=ap 9 5 ey M (fun i hi=>by rw[n i hi,w i hi];have:=c.1 (3*i+2) (by omega);have:=b.1 (3*i+1) (by omega);omega) a1 a5;have F:=ap 9 5 ey x (fun i hi=>by rw[n i hi,l i hi];have:=c.1 (3*i+2) (by omega);have:=b.1 (3*i+2) (by omega);omega) a1 a0
 have C:=lU u.1 L.1
   (fun i hi=>by rw[u.2 i hi,r i hi,w i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide))
   (fun i hi=>by rw[L.2 i hi,n i hi,a4 i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide))
 have z:=lU v.1 C.1
   (fun i hi=>by rw[v.2 i hi,T i hi,l i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide))
   (fun i hi=>by rw[C.2 i hi];exact lO (mL _ _) (by rw[u.2 i hi,r i hi,w i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide)))
 have a3:=lU t.1 K.1
   (fun i hi=>by rw[t.2 i hi,r i hi,l i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide))
   (fun i hi=>by rw[K.2 i hi,n i hi,w i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide))
 have Q:=kD z.1 (fun i hi=>by rw[z.2 i hi];exact lO (mL _ _) (by rw[v.2 i hi,T i hi,l i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide)));have P:=kD a3.1 (fun i hi=>by rw[a3.2 i hi];exact lO (mL _ _) (by rw[t.2 i hi,r i hi,l i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide)));have N:=kD F.1 (fun i hi=>by rw[F.2 i hi,n i hi,l i hi];exact lO (nA (c.1 _ (by omega)) (b.1 _ (by omega))) (by decide))
 have y:=jV 3 5 _ _ _ Q.1 P.1 N.1
   (fun i hi=>by rw[Q.2 i hi];exact lO (mL _ _) (by decide))
   (fun i hi=>by rw[P.2 i hi];exact lO (mL _ _) (by decide))
   (fun i hi=>by rw[N.2 i hi];exact lO (mL _ _) (by decide))
 refine ⟨⟨fun i hi=>?_,y.1⟩,fun e=>?_⟩
 . have m:3*(i/3)+i % 3=i:=by omega
   have hr:=y.2 (i/3) (by omega)
   have a7:i % 3=0\/i % 3=1\/i % 3=2:=by omega
   rcases a7 with hm|hm|hm
   . rw[<- m,hm,nZ,hr.1,Q.2 _ (by omega)];exact mL _ _
   . rw[<- m,hm,hr.2.1,P.2 _ (by omega)];exact mL _ _
   . rw[<- m,hm,hr.2.2,N.2 _ (by omega)];exact mL _ _
 . have hr:=y.2 e.val e.isLt
   rw[hr.1,hr.2.1,hr.2.2,Q.2 e.val e.isLt,P.2 e.val e.isLt,N.2 e.val e.isLt,
     z.2 e.val e.isLt,C.2 e.val e.isLt,a3.2 e.val e.isLt,
     v.2 e.val e.isLt,u.2 e.val e.isLt,L.2 e.val e.isLt,
     t.2 e.val e.isLt,K.2 e.val e.isLt,F.2 e.val e.isLt,
     T e.val e.isLt,r e.val e.isLt,n e.val e.isLt,
     a4 e.val e.isLt,w e.val e.isLt,l e.val e.isLt]
   exact ⟨rfl,rfl,rfl⟩
lemma kB {a b:Nat} (c:cq a) (d:cq b) :
  cq (kC a b)/\∀ i<15,o 3 i (kC a b)=min (o 3 i a) (o 3 i b):=by
 have h:=de 3 2 15 a b 0x124924924924 0xdb6db6db6db (by omega) c.2 d.2 (by decide) (by decide)
  (fun i hi=>qK ⟨i,hi⟩) (fun i hi=>hU ⟨i,hi⟩)
  (fun i hi=>lO (c.1 i hi) (by decide)) (fun i hi=>lO (d.1 i hi) (by decide))
 unfold kC
 exact ⟨⟨fun i hi=>by rw[h.2.1 i hi];exact lT (mL _ _) (c.1 i hi),h.2.2.2⟩,h.2.1⟩
lemma mU {c:Nat} (u:cq c) :
   cq (fg c)/\∀ e:Fin 5,
     o 3 (3*e.val) (fg c) =
       (if o 3 (3*e.val) c=0 then 0 else 1) +
       (if o 3 (3*e.val+1) c=0 then 0 else 1) +
       (if o 3 (3*e.val+2) c=0 then 0 else 1)/\
     o 3 (3*e.val+1) (fg c)=0/\
     o 3 (3*e.val+2) (fg c)=0:=by
 unfold fg;dsimp only
 have x:=ap 3 15 c 0xdb6db6db6db
   (fun i hi=>by rw[hU ⟨i,hi⟩];have:=u.1 i hi;omega) u.2 (by decide)
 set f:=land (shiftRight (c+0xdb6db6db6db) 2) 0x49249249249;have b:f<2^45:=lO nR (by decide)
 have j:∀ i<15,o 3 i f=if o 3 i c=0 then 0 else 1:=fun i hi=>by
   dsimp only[f];rw[bm,xw ⟨i,hi⟩];apply nE2;intro k;change (o 3 i ((c+0xdb6db6db6db) >>> 2)&&&1).testBit k=_;rw[nV,U,nU]
   cases k with
   | zero=>
     simp only[show 0<3 by omega,dT,bTA,nZ]
     have w:(c+0xdb6db6db6db).testBit (2+3*i)=(o 3 i (c+0xdb6db6db6db)).testBit 2:=by
       rw[U];simp[show 2<3 by omega,Nat.add_comm]
     rw[w,x.2 i hi,hU ⟨i,hi⟩];have hlt:=u.1 i hi
     have:o 3 i c=0\/o 3 i c=1\/o 3 i c=2\/o 3 i c=3:=by omega
     rcases this with h|h|h|h <;> simp[h] <;> decide
   | succ m=>
     have C:(1:Nat).testBit (m+1)=false:=by simp[Nat.testBit_succ]
     rw[C,bX];split_ifs <;> simp[Nat.testBit_succ]
 have v:∀ i,15<=i->o 3 i f=0:=fun i hi=>by
   rw[aS,nH (lQ b (nP (by omega) (by omega)))];rfl
 have a:∀ i,o 3 i f<=1:=fun i=>by
   by_cases hi:i<15
   . rw[j i hi];split_ifs <;> omega
   . rw[v i (by omega)];omega
 have d:∀ i,o 3 i (shiftRight f 3)=o 3 (i+1) f:=fun i=>by
   change o 3 i (f >>> 3)=_;rw[nD];exact bj 3 i f
 have l:∀ i,o 3 i (shiftRight f 6)=o 3 (i+2) f:=fun i=>by
   change o 3 i (f >>> 6)=_
   rw[nD,show (2^6:Nat)=2^3*2^3 by decide,
     <- Nat.div_div_eq_div_mul,bj,bj]
 have r:shiftRight f 3<2^45:=by change f >>> 3<_;rw[nD];exact lO (n3 _ _) b
 have n:shiftRight f 6<2^45:=by change f >>> 6<_;rw[nD];exact lO (n3 _ _) b
 have t:=ap 3 15 f (shiftRight f 3)
   (fun i _=>by rw[d i];have:=a i;have:=a (i+1);omega) b r
 have z:=ap 3 15 (f+shiftRight f 3) (shiftRight f 6)
   (fun i hi=>by rw[t.2 i hi,d i,l i];have:=a i;have:=a (i+1);have:=a (i+2);omega) t.1 n
 have y:∀ i<15,o 3 i (land (f+shiftRight f 3+shiftRight f 6) 0x70381c0e07) =
     if i % 3=0 then o 3 i f+o 3 (i+1) f+o 3 (i+2) f else 0:=fun i hi=>by
   rw[bm,z.2 i hi,t.2 i hi,d i,l i,Cg ⟨i,hi⟩]
   split_ifs
   . change _&&&(2^3 - 1)=_;rw[nW,nQ]
     have:=a i;have:=a (i+1);have:=a (i+2);omega
   . exact Nat.and_zero _
 refine ⟨⟨fun i hi=>?_,lO nR (by decide)⟩,fun e=>?_⟩
 . rw[y i hi];split_ifs
   . have:=a i;have:=a (i+1);have:=a (i+2);omega
   . omega
 . have h0:=y (3*e.val) (by omega);have h1:=y (3*e.val+1) (by omega);have h2:=y (3*e.val+2) (by omega)
   simp only[show (3*e.val) % 3=0 by omega,show (3*e.val+1) % 3 ≠ 0 by omega,
     show (3*e.val+2) % 3 ≠ 0 by omega,↓reduceIte] at h0 h1 h2
   rw[h0,h1,h2,j (3*e.val) (by omega),j (3*e.val+1) (by omega),j (3*e.val+2) (by omega)];exact ⟨rfl,rfl,rfl⟩
lemma kh {w e:Nat} (h1:o 3 (3*e+1) w=0) (h2:o 3 (3*e+2) w=0) :
   o 9 e w=o 3 (3*e) w:=by
 apply nE2;intro k;rw[U,U]
 by_cases hk3:k<3
 . have c:k<9:=by omega
   have a:9*e+k=3*(3*e)+k:=by omega
   simp[hk3,c,a]
 . simp only[hk3,decide_false,bFA]
   by_cases hk6:k<6
   . have c:k<9:=by omega
     have b:=congrArg (fun z=>z.testBit (k - 3)) h1;rw[U,n4] at b
     simp only[show k - 3<3 by omega,dT,bTA] at b
     have a:9*e+k=3*(3*e+1)+(k - 3):=by omega
     simp[c,a,b]
   . by_cases c:k<9
     . have b:=congrArg (fun z=>z.testBit (k - 6)) h2;rw[U,n4] at b
       simp only[show k - 6<3 by omega,dT,bTA] at b
       have a:9*e+k=3*(3*e+2)+(k - 6):=by omega
       simp[c,a,b]
     . simp[c]
lemma gd (M1 M2:Fin 5->Fin 3->Fin 3->Bool) (h d:Nat)
  (l:cq h) (k:cq d)
  (t:bg h (fun e=>D (Y (M1 e) 0) (Y (M1 e) 1) (Y (M1 e) 2)))
  (n:bg d (fun e=>D (Y (M2 e) 0) (Y (M2 e) 1) (Y (M2 e) 2))) :
  cq (ez h d)/\
  bg (ez h d) (fun e=>D (Y (fun r c=>M1 e r c||M2 e r c) 0)
     (Y (fun r c=>M1 e r c||M2 e r c) 1)
     (Y (fun r c=>M1 e r c||M2 e r c) 2)):=by
 have b:=no l k;refine ⟨b.1,fun e=>?_⟩
 have a:∀ r:Fin 3,Y (fun x y=>M1 e x y||M2 e x y) r<=min 3 (Y (M1 e) r+Y (M2 e) r):=by
  intro r;have h3:=gC (fun x y=>M1 e x y||M2 e x y) r
  have m:∀ c:Fin 3,al (M1 e r c||M2 e r c)<=al (M1 e r c)+al (M2 e r c):=by
   intro c;cases M1 e r c <;> cases M2 e r c <;> simp[al]
  have hc0:=m 0;have hc1:=m 1;have hc2:=m 2
  have hsum:Y (fun x y=>M1 e x y||M2 e x y) r<=Y (M1 e) r+Y (M2 e) r:=by
   unfold Y;dsimp only;omega
  omega
 have i:=cM (a 0) (a 1) (a 2)
 have j:=pT (Y (M1 e) 0) (Y (M1 e) 1) (Y (M1 e) 2)
    (Y (M2 e) 0) (Y (M2 e) 1) (Y (M2 e) 2)
 rcases t e with ⟨hp0,hp1,hp2⟩;rcases n e with ⟨hq0,hq1,hq2⟩;rcases b.2 e with ⟨gK,eW,fj⟩;dsimp only at i j hp0 hp1 hp2 hq0 hq1 hq2;rw[gK,eW,fj]
 exact ⟨lT i.1 (lT j.1 (min_le_min (lR 3)
   (min_le_min (nA hp0 hq2) (min_le_min (nA hp1 hq1) (nA hp2 hq0))))),
  lT i.2.1 (lT j.2.1 (min_le_min (lR 3)
   (min_le_min (nA hp1 hq2) (nA hp2 hq1)))),
  lT i.2.2 (lT j.2.2 (min_le_min (lR 3) (nA hp2 hq2)))⟩
lemma kq (M1 M2:Fin 5->Fin 3->Fin 3->Bool) (pr pc qr W:Nat)
   (a3:cq pr) (a4:cq pc) (a1:cq qr) (a2:cq W)
   (ac:bg pr (fun e=>D (Y (M1 e) 0) (Y (M1 e) 1) (Y (M1 e) 2)))
   (ae:bg pc (fun e=>D (aQ (M1 e) 0) (aQ (M1 e) 1) (aQ (M1 e) 2)))
   (a9:bg qr (fun e=>D (Y (M2 e) 0) (Y (M2 e) 1) (Y (M2 e) 2)))
   (ab:bg W (fun e=>D (aQ (M2 e) 0) (aQ (M2 e) 1) (aQ (M2 e) 2))) :
   cq (dH pr pc qr W)/\
   bg (dH pr pc qr W) (fun e=>D (Y (fun r c=>M1 e r c&&M2 e r c) 0)
                                            (Y (fun r c=>M1 e r c&&M2 e r c) 1)
                                            (Y (fun r c=>M1 e r c&&M2 e r c) 2)):=by
 unfold dH;dsimp only;have t:=mU a4;have L:=mU a2;have k:=kB t.1 L.1;set v:=kC (fg pc) (fg W)
 have d:∀ i<5,o 9 i v=o 3 (3*i) v:=fun i hi=>by
   have h1:o 3 (3*i+1) v=0:=by rw[k.2 _ (by omega),(t.2 ⟨i,hi⟩).2.1];simp
   have h2:o 3 (3*i+2) v=0:=by rw[k.2 _ (by omega),(t.2 ⟨i,hi⟩).2.2];simp
   exact kh h1 h2
 have w:=jV 3 5 v v v k.1.2 k.1.2 k.1.2
   (fun i hi=>by rw[d i hi];have:=k.1.1 (3*i) (by omega);omega)
   (fun i hi=>by rw[d i hi];have:=k.1.1 (3*i) (by omega);omega)
   (fun i hi=>by rw[d i hi];have:=k.1.1 (3*i) (by omega);omega)
 have z:cq (lor v (lor (shiftLeft v 3) (shiftLeft v 6))):=by
   refine ⟨fun i hi=>?_,w.1⟩
   have m:3*(i/3)+i % 3=i:=by omega
   have M:=w.2 (i/3) (by omega)
   have hm:i % 3=0\/i % 3=1\/i % 3=2:=by omega
   rcases hm with h|h|h
   . rw[<- m,h,nZ,M.1,d _ (by omega)];exact k.1.1 _ (by omega)
   . rw[<- m,h,M.2.1,d _ (by omega)];exact k.1.1 _ (by omega)
   . rw[<- m,h,M.2.2,d _ (by omega)];exact k.1.1 _ (by omega)
 have K:=kB a3 a1;have n:=kB K.1 z;refine ⟨n.1,fun e=>?_⟩
 have F:∀ r:Fin 3,Y (fun x y=>M1 e x y&&M2 e x y) r<=Y (M1 e) r:=fun r=>by
   have T:∀ c:Fin 3,al (M1 e r c&&M2 e r c)<=al (M1 e r c):=fun c=>by cases M1 e r c <;> cases M2 e r c <;> simp[al]
   have:=T 0;have:=T 1;have:=T 2;unfold Y;dsimp only;omega
 have C:∀ r:Fin 3,Y (fun x y=>M1 e x y&&M2 e x y) r<=Y (M2 e) r:=fun r=>by
   have T:∀ c:Fin 3,al (M1 e r c&&M2 e r c)<=al (M2 e r c):=fun c=>by cases M1 e r c <;> cases M2 e r c <;> simp[al]
   have:=T 0;have:=T 1;have:=T 2;unfold Y;dsimp only;omega
 have P:=cM (F 0) (F 1) (F 2);have N:=cM (C 0) (C 1) (C 2)
 have a6:∀ r:Fin 3,Y (fun x y=>M1 e x y&&M2 e x y) r<=o 3 (3*e.val) (fg pc):=fun r=>by
   have h1:=iu (M1 e) (M2 e) r;rw[la] at h1;rcases ae e with ⟨c0,c1,c2⟩;dsimp only at c0 c1 c2;rw[(t.2 e).1]
   have j:∀ a b:Nat,a<=b->(if a=0 then 0 else 1)<=(if b=0 then 0 else 1):=fun a b hab=>by split_ifs <;> omega
   have b0:=j _ _ c0;have b1:=j _ _ c1;have b2:=j _ _ c2;omega
 have a5:∀ r:Fin 3,Y (fun x y=>M1 e x y&&M2 e x y) r<=o 3 (3*e.val) (fg W):=fun r=>by
   have h1:=iu (M2 e) (M1 e) r
   have Q:Y (fun x y=>M1 e x y&&M2 e x y) r=Y (fun x y=>M2 e x y&&M1 e x y) r:=by
     unfold Y;simp only[bY]
   rw[<- Q,la] at h1;rcases ab e with ⟨c0,c1,c2⟩;dsimp only at c0 c1 c2;rw[(L.2 e).1]
   have j:∀ a b:Nat,a<=b->(if a=0 then 0 else 1)<=(if b=0 then 0 else 1):=fun a b hab=>by split_ifs <;> omega
   have b0:=j _ _ c0;have b1:=j _ _ c1;have b2:=j _ _ c2;omega
 have l:∀ r:Fin 3,Y (fun x y=>M1 e x y&&M2 e x y) r<=o 3 (3*e.val) v:=fun r=>by
   rw[k.2 (3*e.val) (by omega)];exact lM (a6 r) (a5 r)
 have u:=cM (l 0) (l 1) (l 2);rw[af _ _ _ (lR _) (lR _)] at u;rcases ac e with ⟨p0,p1,p2⟩;rcases a9 e with ⟨q0,q1,q2⟩;have M:=w.2 e.val e.isLt
 rw[n.2 (3*e.val) (by omega),n.2 (3*e.val+1) (by omega),n.2 (3*e.val+2) (by omega),
   K.2 (3*e.val) (by omega),K.2 (3*e.val+1) (by omega),K.2 (3*e.val+2) (by omega),
   M.1,M.2.1,M.2.2,d e.val e.isLt]
 exact ⟨lM (lM (lT P.1 p0) (lT N.1 q0)) u.1,
        lM (lM (lT P.2.1 p1) (lT N.2.1 q1)) u.2.1,
        lM (lM (lT P.2.2 p2) (lT N.2.2 q2)) u.2.2⟩
lemma xp {b a w x u v:Nat} {e:Fin 5}
  (k:cq w) (l:cq x) (i:cq u) (j:cq v)
  (aw:bg w (cf b)) (b3:bg x (cg b))
  (an:bg u (cf a)) (ar:bg v (cg a)) :
  bk (b|||a) e<=eA w x u v e.val/\eA w x u v e.val<=9:=by
 unfold eA;dsimp only;set gt:=land (aL w e.val) 7;set fP:=land (shiftRight (aL w e.val) 3) 7;set ey:=shiftRight (aL w e.val) 6;set z:=land (aL u e.val) 7;set y:=land (shiftRight (aL u e.val) 3) 7;set m:=shiftRight (aL u e.val) 6;set L:=land (aL x e.val) 7;set K:=land (shiftRight (aL x e.val) 3) 7;set t:=shiftRight (aL x e.val) 6;set F:=land (aL v e.val) 7;set C:=land (shiftRight (aL v e.val) 3) 7;set n:=shiftRight (aL v e.val) 6
 have a7:gt=o 3 (3*e.val) w:=by simpa [gt,hI] using cc w e.val 0 k e.isLt (by omega)
 have a6:fP=o 3 (3*e.val+1) w:=cc w e.val 1 k e.isLt (by omega);have a5:ey=o 3 (3*e.val+2) w:=cc w e.val 2 k e.isLt (by omega)
 have T:z=o 3 (3*e.val) u:=by simpa [z,hI] using cc u e.val 0 i e.isLt (by omega)
 have Q:y=o 3 (3*e.val+1) u:=cc u e.val 1 i e.isLt (by omega);have P:m=o 3 (3*e.val+2) u:=cc u e.val 2 i e.isLt (by omega)
 have ab:L=o 3 (3*e.val) x:=by simpa [L,hI] using cc x e.val 0 l e.isLt (by omega)
 have a9:K=o 3 (3*e.val+1) x:=cc x e.val 1 l e.isLt (by omega);have a8:t=o 3 (3*e.val+2) x:=cc x e.val 2 l e.isLt (by omega)
 have a4:F=o 3 (3*e.val) v:=by simpa [F,hI] using cc v e.val 0 j e.isLt (by omega)
 have a3:C=o 3 (3*e.val+1) v:=cc v e.val 1 j e.isLt (by omega);have W:n=o 3 (3*e.val+2) v:=cc v e.val 2 j e.isLt (by omega);set ah:=av 3 (av (gt+m) (av (fP+y) (ey+z)));set ae:=av 3 (av (fP+m) (ey+y));set ac:=av 3 (ey+m);set b6:=av 3 (av (L+n) (av (K+C) (t+F)));set b5:=av 3 (av (K+n) (t+C));set b4:=av 3 (t+n)
 refine ⟨?_,by rw[aG,aG];exact lT (mR _ _) (lT (mR _ _) (Nat.sub_le 9 _))⟩
 simp only[aG,aP]
 have h1:bk (b|||a) e<=ah+ae+ac:=by
  have h:=(gd (ao b) (ao a) w u k i aw an).2 e;rcases (no k i).2 e with ⟨gK,eW,fj⟩;rw[gK,eW,fj] at h;rcases h with ⟨h_0,h_1,h_2⟩
  have M:=cr (Y (fun r c=>ao b e r c||ao a e r c) 0)
     (Y (fun r c=>ao b e r c||ao a e r c) 1)
     (Y (fun r c=>ao b e r c||ao a e r c) 2)
  have d:ao (b|||a) e=fun r c=>ao b e r c||ao a e r c:=by
   funext r c;exact hX b a e r c
  unfold bk;rw[d];unfold gz;dsimp only[ah,ae,ac];simp only[aG,a7,a6,a5,T,Q,P];exact lT M.symm.le (nA (nA h_0 h_1) h_2)
 have h2:bk (b|||a) e<=b6+b5+b4:=by
  have h:=(gd (fun e' r c=>ao b e' c r) (fun e' r c=>ao a e' c r) x v l j b3 ar).2 e;rcases (no l j).2 e with ⟨gK,eW,fj⟩;rw[gK,eW,fj] at h;rcases h with ⟨h_0,h_1,h_2⟩
  have M:=cr (Y (fun r c=>ao b e c r||ao a e c r) 0)
     (Y (fun r c=>ao b e c r||ao a e c r) 1)
     (Y (fun r c=>ao b e c r||ao a e c r) 2)
  have d:ao (b|||a) e=fun r c=>ao b e r c||ao a e r c:=by
   funext r c;exact hX b a e r c
  unfold bk;rw[d,<-kw];unfold gz;dsimp only[b6,b5,b4];simp only[aG,ab,a9,a8,a4,a3,W];exact lT M.symm.le (nA (nA h_0 h_1) h_2)
 have N:∀ (u0 u1 u2 v0 v1 v2:Nat),u0<=v0->u1<=v1->u2<=v2->
   (1 - v0)+(1 - v1)+(1 - v2)<=
   (if u0=0 then 1 else 0)+(if u1=0 then 1 else 0)+(if u2=0 then 1 else 0):=by
  intro u0 u1 u2 v0 v1 v2 h0 h1 h2;split_ifs <;> omega
 have h3a:bk (b|||a) e +
   ((1 - gt)+(1 - fP)+(1 - ey))*((1 - F)+(1 - C)+(1 - n))<=9:=by
  have h0:=lP (ao b e) (ao a e);rw[ds (Y (ao b e) 0),ds (aQ (ao a e) 0)] at h0;rcases aw e with ⟨a0,a1,a2⟩;rcases ar e with ⟨b0,b1,b2⟩;unfold cf am at a0 a1 a2;unfold cg aR at b0 b1 b2;have z1:=N _ _ _ gt fP ey (a7 ▸ a0) (a6 ▸ a1) (a5 ▸ a2);have z2:=N _ _ _ F C n (a4 ▸ b0) (a3 ▸ b1) (W ▸ b2);have hm:=Nat.mul_le_mul z1 z2
  have d:ao (b|||a) e=fun r c=>ao b e r c||ao a e r c:=by
   funext r c;exact hX b a e r c
  unfold bk;rw[d];exact lT (Nat.add_le_add_left hm _) h0
 have h3b:bk (b|||a) e +
   ((1 - L)+(1 - K)+(1 - t))*((1 - z)+(1 - y)+(1 - m))<=9:=by
  have h0:=lP (fun r c=>ao b e c r) (fun r c=>ao a e c r);rw[ds (Y (fun r c=>ao b e c r) 0),ds (aQ (fun r c=>ao a e c r) 0)] at h0;rcases b3 e with ⟨a0,a1,a2⟩;rcases an e with ⟨b0,b1,b2⟩;unfold cg aR at a0 a1 a2;unfold cf am at b0 b1 b2;have z1:=N _ _ _ L K t (ab ▸ a0) (a9 ▸ a1) (a8 ▸ a2);have z2:=N _ _ _ z y m (T ▸ b0) (Q ▸ b1) (P ▸ b2);have hm:=Nat.mul_le_mul z1 z2
  have d:ao (b|||a) e=fun r c=>ao b e r c||ao a e r c:=by
   funext r c;exact hX b a e r c
  unfold bk;rw[d,<-kw];exact lT (Nat.add_le_add_left hm _) h0
 exact lM h1 (lM h2 (by
  have h3:bk (b|||a) e<=9 - max
    (((1 - gt)+(1 - fP)+(1 - ey))*((1 - F)+(1 - C)+(1 - n)))
    (((1 - L)+(1 - K)+(1 - t))*((1 - z)+(1 - y)+(1 - m))):=by omega
  exact h3))
set_option maxHeartbeats 800000 in
lemma w2 {b a F K z C:Nat} {e:Fin 5}
   (i:cq F) (N:cq K) (L:cq z) (M:cq C)
   (b9:bg F (cf b)) (bb:bg K (cg b))
   (b7:bg z (cf a)) (b8:bg C (cg a)) :
   bk (b&&&a) e<=d6 F K z C e.val/\d6 F K z C e.val<=9:=by
 unfold d6;dsimp only;set gt:=land (aL F e.val) 7;set fP:=land (shiftRight (aL F e.val) 3) 7;set ey:=shiftRight (aL F e.val) 6;set v:=land (aL z e.val) 7;set y:=land (shiftRight (aL z e.val) 3) 7;set x:=shiftRight (aL z e.val) 6;set k:=land (aL K e.val) 7;set t:=land (shiftRight (aL K e.val) 3) 7;set n:=shiftRight (aL K e.val) 6;set j:=land (aL C e.val) 7;set m:=land (shiftRight (aL C e.val) 3) 7;set l:=shiftRight (aL C e.val) 6
 have W:gt=o 3 (3*e.val) F:=by simpa [gt,hI] using cc F e.val 0 i e.isLt (by omega)
 have T:fP=o 3 (3*e.val+1) F:=cc F e.val 1 i e.isLt (by omega);have Q:ey=o 3 (3*e.val+2) F:=cc F e.val 2 i e.isLt (by omega)
 have a5:v=o 3 (3*e.val) z:=by simpa [v,hI] using cc z e.val 0 L e.isLt (by omega)
 have a4:y=o 3 (3*e.val+1) z:=cc z e.val 1 L e.isLt (by omega);have a3:x=o 3 (3*e.val+2) z:=cc z e.val 2 L e.isLt (by omega)
 have ac:k=o 3 (3*e.val) K:=by simpa [k,hI] using cc K e.val 0 N e.isLt (by omega)
 have ab:t=o 3 (3*e.val+1) K:=cc K e.val 1 N e.isLt (by omega);have a9:n=o 3 (3*e.val+2) K:=cc K e.val 2 N e.isLt (by omega)
 have a8:j=o 3 (3*e.val) C:=by simpa [j,hI] using cc C e.val 0 M e.isLt (by omega)
 have a7:m=o 3 (3*e.val+1) C:=cc C e.val 1 M e.isLt (by omega);have a6:l=o 3 (3*e.val+2) C:=cc C e.val 2 M e.isLt (by omega);have b0:=i.1 (3*e.val) (by omega);have b1:=i.1 (3*e.val+1) (by omega);have b2:=i.1 (3*e.val+2) (by omega);refine ⟨?_,?_⟩
 swap
 . rw[aG];apply lT (mL _ _);rw[aG,aG,aG];have m0:min gt v<=3:=lT (mL _ _) (by rw[W];omega);have b:min fP y<=3:=lT (mL _ _) (by rw[T];omega);have a:min ey x<=3:=lT (mL _ _) (by rw[Q];omega);omega
 have P:ao (b&&&a) e=fun r c=>ao b e r c&&ao a e r c:=by
   funext r c;exact fk b a e r c
 have hr:∀ r:Fin 3,Y (ao (b&&&a) e) r<=min (am b e r) (am a e r):=fun r=>by
   have hc:∀ c:Fin 3,al (ao (b&&&a) e r c)<=al (ao b e r c)/\al (ao (b&&&a) e r c)<=al (ao a e r c):=fun c=>by
     rw[fk];cases ao b e r c <;> cases ao a e r c <;> simp[al]
   have:=hc 0;have:=hc 1;have:=hc 2;unfold am Y;omega
 have hc:∀ c:Fin 3,aQ (ao (b&&&a) e) c<=min (aR b e c) (aR a e c):=fun c=>by
   have h':∀ r:Fin 3,al (ao (b&&&a) e r c)<=al (ao b e r c)/\al (ao (b&&&a) e r c)<=al (ao a e r c):=fun r=>by
     rw[fk];cases ao b e r c <;> cases ao a e r c <;> simp[al]
   have:=h' 0;have:=h' 1;have:=h' 2;unfold aR aQ;omega
 have bs:=nu (am b e 0) (am b e 1) (am b e 2) (am a e 0) (am a e 1) (am a e 2);have bw:=nu (aR b e 0) (aR b e 1) (aR b e 2) (aR a e 0) (aR a e 1) (aR a e 2);rcases b9 e with ⟨p0,p1,p2⟩;rcases b7 e with ⟨q0,q1,q2⟩;rcases bb e with ⟨pc0',pc1',pc2'⟩;rcases b8 e with ⟨qc0',qc1',qc2'⟩
 have c0:bk (b&&&a) e<=av gt v+av fP y+av ey x:=by
   rw[aG,aG,aG]
   have h1:bk (b&&&a) e<=min (am b e 0) (am a e 0)+min (am b e 1) (am a e 1)+min (am b e 2) (am a e 2):=
     nA (nA (hr 0) (hr 1)) (hr 2)
   have h2:min (cf b e).1 (cf a e).1+min (cf b e).2.1 (cf a e).2.1+min (cf b e).2.2 (cf a e).2.2<=
       min gt v+min fP y+min ey x:=
     nA (nA (min_le_min (W ▸ p0) (a5 ▸ q0)) (min_le_min (T ▸ p1) (a4 ▸ q1))) (min_le_min (Q ▸ p2) (a3 ▸ q2))
   exact lT h1 (lT bs h2)
 have bz:bk (b&&&a) e<=av k j+av t m+av n l:=by
   rw[aG,aG,aG]
   have h1:bk (b&&&a) e<=min (aR b e 0) (aR a e 0)+min (aR b e 1) (aR a e 1)+min (aR b e 2) (aR a e 2):=by
     unfold bk;rw[gM];exact nA (nA (hc 0) (hc 1)) (hc 2)
   have h2:min (cg b e).1 (cg a e).1+min (cg b e).2.1 (cg a e).2.1+min (cg b e).2.2 (cg a e).2.2<=
       min k j+min t m+min n l:=
     nA (nA (min_le_min (ac ▸ pc0') (a8 ▸ qc0')) (min_le_min (ab ▸ pc1') (a7 ▸ qc1'))) (min_le_min (a9 ▸ pc2') (a6 ▸ qc2'))
   exact lT h1 (lT bw h2)
 have w:=io (ao b e) (ao a e);have u:=io (fun r c=>ao b e c r) (fun r c=>ao a e c r)
 have d:∀ a0 a1 a2 b0 b1 b2 a0' a1' a2' b0' b1' b2',
     a0<=a0'->a1<=a1'->a2<=a2'->b0<=b0'->b1<=b1'->b2<=b2'->
     g7 a0 a1 a2 b0 b1 b2<=g7 a0' a1' a2' b0' b1' b2':=by
   intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _;unfold g7
   repeat (first|apply zl|omega)
 have b4:=d _ _ _ _ _ _ gt fP ey j m l (W ▸ p0) (T ▸ p1) (Q ▸ p2) (a8 ▸ qc0') (a7 ▸ qc1') (a6 ▸ qc2');have b3:=d _ _ _ _ _ _ k t n v y x (ac ▸ pc0') (ab ▸ pc1') (a9 ▸ pc2') (a5 ▸ q0) (a4 ▸ q1) (a3 ▸ q2)
 have b5:gz (fun r c=>ao b e c r&&ao a e c r)=bk (b&&&a) e:=by
   unfold bk;rw[P,<-kw]
 have aw:gz (fun r c=>ao b e r c&&ao a e r c)=bk (b&&&a) e:=by
   unfold bk;rw[P]
 have hcr1':bk (b&&&a) e<=g7 gt fP ey j m l:=by
   rw[aw] at w;exact lT w b4
 have hcr2':bk (b&&&a) e<=g7 k t n v y x:=by
   rw[b5] at u;change bk (b&&&a) e<=g7 (cg b e).1 (cg b e).2.1 (cg b e).2.2 (cf a e).1 (cf a e).2.1 (cf a e).2.2 at u;exact lT u b3
 exact gT.mpr ⟨c0,gT.mpr ⟨bz,gT.mpr ⟨hcr1',hcr2'⟩⟩⟩
set_option maxHeartbeats 800000 in
lemma xo {h d L K F C w v:Nat} {s:Fin 5}
  (W:az L) (T:az K) (Q:az F) (P:az C) (N:az w) (M:az v)
  (an:ag L (fun s'=>ak h s' 0)) (ah:ag K (fun s'=>ak h s' 1)) (ae:ag F (fun s'=>ak h s' 2))
  (ac:ag C (fun s'=>ak d s' 0)) (ab:ag w (fun s'=>ak d s' 1)) (a9:ag v (fun s'=>ak d s' 2)) :
  ff L K F C w v s.val<=cw (h|||d) s:=by
 have a4:B (h|||d) s=fun a b c=>B h s a b c||B d s a b c:=by
  funext a b c;exact gH h d s a b c
 have j:∀ (P1 P2:Fin 3->Fin 3->Fin 3->Bool) (x0 x1 x2 y0 y1 y2:Nat),
   x0<=(D (A P1 0) (A P1 1) (A P1 2)).1->
   x1<=(D (A P1 0) (A P1 1) (A P1 2)).2.1->
   x2<=(D (A P1 0) (A P1 1) (A P1 2)).2.2->
   y0<=(D (A P2 0) (A P2 1) (A P2 2)).1->
   y1<=(D (A P2 0) (A P2 1) (A P2 2)).2.1->
   y2<=(D (A P2 0) (A P2 1) (A P2 2)).2.2->
   aa x0 y0+aa x1 y1+aa x2 y2<=cU (fun a b c=>P1 a b c||P2 a b c):=by
  intro P1 P2 x0 x1 x2 y0 y1 y2 hx0 hx1 hx2 hy0 hy1 hy2;have a5:=zm (A P1 0) (A P1 1) (A P1 2) (A P2 0) (A P2 1) (A P2 2)
  have a3:∀ a:Fin 3,max (A P1 a) (A P2 a)<=A (fun x y z=>P1 x y z||P2 x y z) a:=fun a=>by
   have l:∀ b c:Fin 3,al (P1 a b c)<=al (P1 a b c||P2 a b c)/\al (P2 a b c)<=al (P1 a b c||P2 a b c):=fun b c=>by
    cases P1 a b c <;> cases P2 a b c <;> simp[al]
   have h00:=l 0 0;have h01:=l 0 1;have h02:=l 0 2;have fT:=l 1 0;have kG:=l 1 1;have hH:=l 1 2;have gL:=l 2 0;have gV:=l 2 1;have jW:=l 2 2;unfold A aq;dsimp only;exact xL (by linarith) (by linarith)
  have a0:=a3 0;have a1:=a3 1;have a2:=a3 2;dsimp only at a5;unfold cU;simp only[aP]
  exact lT (nA (nA (max_le_max hx0 hy0) (max_le_max hx1 hy1)) (max_le_max hx2 hy2))
   (lT a5 (nA (nA a0 a1) a2))
 have i:∀ x0 x1 x2 y0 y1 y2 x0' x1' x2' y0' y1' y2',
   x0<=x0'->x1<=x1'->x2<=x2'->y0<=y0'->y1<=y1'->y2<=y2'->
   dm x0 x1 x2 y0 y1 y2<=dm x0' x1' x2' y0' y1' y2':=by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _;unfold dm
  repeat (first|apply zn|omega)
 have k:∀ (P1 P2:Fin 3->Fin 3->Fin 3->Bool) (x0 x1 x2 y0 y1 y2:Nat),
   x0<=(D (A P1 0) (A P1 1) (A P1 2)).1->
   x1<=(D (A P1 0) (A P1 1) (A P1 2)).2.1->
   x2<=(D (A P1 0) (A P1 1) (A P1 2)).2.2->
   y0<=(D (Z P2 0) (Z P2 1) (Z P2 2)).1->
   y1<=(D (Z P2 0) (Z P2 1) (Z P2 2)).2.1->
   y2<=(D (Z P2 0) (Z P2 1) (Z P2 2)).2.2->
   dm x0 x1 x2 y0 y1 y2<=cU (fun a b c=>P1 a b c||P2 a b c):=fun P1 P2 x0 x1 x2 y0 y1 y2 hx0 hx1 hx2 hy0 hy1 hy2=>
  lT (i _ _ _ _ _ _ _ _ _ _ _ _ hx0 hx1 hx2 hy0 hy1 hy2) (p5 P1 P2)
 rcases an s with ⟨p00,p01,p02⟩;rcases ah s with ⟨p10,p11,p12⟩;rcases ae s with ⟨p20,p21,p22⟩;rcases ac s with ⟨q00,q01,q02⟩;rcases ab s with ⟨q10,q11,q12⟩;rcases a9 s with ⟨q20,q21,q22⟩;unfold ff cw;rw[a4];dsimp only;cases nE (V L s.val+V K s.val+V F s.val+V C s.val+V w s.val+V v s.val) 0
 swap;· exact Nat.zero_le _
 simp only[bC]
 simp only[aH L s.val W s.isLt,ai L s.val W s.isLt,aA L s.val W s.isLt,
  aH K s.val T s.isLt,ai K s.val T s.isLt,aA K s.val T s.isLt,
  aH F s.val Q s.isLt,ai F s.val Q s.isLt,aA F s.val Q s.isLt,
  aH C s.val P s.isLt,ai C s.val P s.isLt,aA C s.val P s.isLt,
  aH w s.val N s.isLt,ai w s.val N s.isLt,aA w s.val N s.isLt,
  aH v s.val M s.isLt,ai v s.val M s.isLt,aA v s.val M s.isLt]
 unfold ak S at p00 p01 p02 p10 p11 p12 p20 p21 p22 q00 q01 q02 q10 q11 q12 q20 q21 q22;dsimp only at p00 p01 p02 p10 p11 p12 p20 p21 p22 q00 q01 q02 q10 q11 q12 q20 q21 q22;have ar:=j (B h s) (B d s) _ _ _ _ _ _ p00 p01 p02 q00 q01 q02
 have a7:=j (fun b a c=>B h s a b c) (fun b a c=>B d s a b c) _ _ _ _ _ _
  (by simpa [aT] using p10) (by simpa [aT] using p11) (by simpa [aT] using p12)
  (by simpa [aT] using q10) (by simpa [aT] using q11) (by simpa [aT] using q12)
 rw[fx (fun a b c=>B h s a b c||B d s a b c)] at a7;have a6:=j (fun c a b=>B h s a b c) (fun c a b=>B d s a b c) _ _ _ _ _ _ p20 p21 p22 q20 q21 q22;rw[e8 (fun a b c=>B h s a b c||B d s a b c)] at a6;have a8:=k (B h s) (B d s) _ _ _ _ _ _ p00 p01 p02 q10 q11 q12
 have u:=k (fun a c b=>B h s a b c) (fun a c b=>B d s a b c) _ _ _ _ _ _
  (by simpa [cz] using p00) (by simpa [cz] using p01) (by simpa [cz] using p02)
  (by simpa [bK] using q20) (by simpa [bK] using q21) (by simpa [bK] using q22)
 rw[oP (fun a b c=>B h s a b c||B d s a b c)] at u
 have t:=k (fun b a c=>B h s a b c) (fun b a c=>B d s a b c) _ _ _ _ _ _
  (by simpa [aT] using p10) (by simpa [aT] using p11) (by simpa [aT] using p12)
  (by simpa [eE] using q00) (by simpa [eE] using q01) (by simpa [eE] using q02)
 rw[fx (fun a b c=>B h s a b c||B d s a b c)] at t
 have r:=k (fun b c a=>B h s a b c) (fun b c a=>B d s a b c) _ _ _ _ _ _
  (by simpa [eG] using p10) (by simpa [eG] using p11) (by simpa [eG] using p12)
  (by simpa [eD] using q20) (by simpa [eD] using q21) (by simpa [eD] using q22)
 rw[oO (fun a b c=>B h s a b c||B d s a b c)] at r
 have n:=k (fun c a b=>B h s a b c) (fun c a b=>B d s a b c) _ _ _ _ _ _ p20 p21 p22
  (by simpa [dd] using q00) (by simpa [dd] using q01) (by simpa [dd] using q02)
 rw[e8 (fun a b c=>B h s a b c||B d s a b c)] at n
 have m:=k (fun c b a=>B h s a b c) (fun c b a=>B d s a b c) _ _ _ _ _ _
  (by simpa [eF] using p20) (by simpa [eF] using p21) (by simpa [eF] using p22)
  (by simpa [eC] using q10) (by simpa [eC] using q11) (by simpa [eC] using q12)
 rw[oN (fun a b c=>B h s a b c||B d s a b c)] at m;exact aV ar (aV a7 (aV a6 (aV a8 (aV u (aV t (aV r (aV n m)))))))
set_option maxHeartbeats 800000 in
lemma w1 {i d L K F C w v:Nat} {s:Fin 5}
   (W:az L) (T:az K) (Q:az F) (P:az C) (N:az w) (M:az v)
   (an:ag L (fun s'=>ak i s' 0)) (ah:ag K (fun s'=>ak i s' 1)) (ae:ag F (fun s'=>ak i s' 2))
   (ac:ag C (fun s'=>ak d s' 0)) (ab:ag w (fun s'=>ak d s' 1)) (a9:ag v (fun s'=>ak d s' 2)) :
   dh L K F C w v s.val<=cw (i&&&d) s:=by
 have a4:B (i&&&d) s=fun a b c=>B i s a b c&&B d s a b c:=by
   funext a b c;exact dG i d s a b c
 have j:∀ (P1 P2:Fin 3->Fin 3->Fin 3->Bool) (x0 x1 x2 y0 y1 y2:Nat),
     x0<=(D (A P1 0) (A P1 1) (A P1 2)).1->
     x1<=(D (A P1 0) (A P1 1) (A P1 2)).2.1->
     x2<=(D (A P1 0) (A P1 1) (A P1 2)).2.2->
     y0<=(D (A P2 0) (A P2 1) (A P2 2)).1->
     y1<=(D (A P2 0) (A P2 1) (A P2 2)).2.1->
     y2<=(D (A P2 0) (A P2 1) (A P2 2)).2.2->
     (x0+y2 - 9)+(x1+y1 - 9)+(x2+y0 - 9)<=cU (fun a b c=>P1 a b c&&P2 a b c):=by
   intro P1 P2 x0 x1 x2 y0 y1 y2 hx0 hx1 hx2 hy0 hy1 hy2;have a5:=rn (A P1 0) (A P1 1) (A P1 2) (A P2 0) (A P2 1) (A P2 2)
   have a3:∀ a:Fin 3,A P1 a+A P2 a - 9<=A (fun x y z=>P1 x y z&&P2 x y z) a:=fun a=>by
     have l:∀ b c:Fin 3,al (P1 a b c)+al (P2 a b c)<=al (P1 a b c&&P2 a b c)+1:=fun b c=>by
       cases P1 a b c <;> cases P2 a b c <;> simp[al]
     have h00:=l 0 0;have h01:=l 0 1;have h02:=l 0 2;have fT:=l 1 0;have kG:=l 1 1;have hH:=l 1 2;have gL:=l 2 0;have gV:=l 2 1;have jW:=l 2 2;apply nF;unfold A aq;dsimp only;linarith
   have a0:=a3 0;have a1:=a3 1;have a2:=a3 2;dsimp only at a5;unfold cU
   exact lT (nA (nA (nS (nA hx0 hy2) 9)
     (nS (nA hx1 hy1) 9)) (nS (nA hx2 hy0) 9))
     (lT a5 (nA (nA a0 a1) a2))
 have k:∀ (P1 P2:Fin 3->Fin 3->Fin 3->Bool) (x0 x1 x2 y0 y1 y2:Nat),
     x0<=(D (A P1 0) (A P1 1) (A P1 2)).1->
     x1<=(D (A P1 0) (A P1 1) (A P1 2)).2.1->
     x2<=(D (A P1 0) (A P1 1) (A P1 2)).2.2->
     y0<=(D (Z P2 0) (Z P2 1) (Z P2 2)).1->
     y1<=(D (Z P2 0) (Z P2 1) (Z P2 2)).2.1->
     y2<=(D (Z P2 0) (Z P2 1) (Z P2 2)).2.2->
     d5 x0 x1 x2 y0 y1 y2<=cU (fun a b c=>P1 a b c&&P2 a b c):=fun P1 P2 x0 x1 x2 y0 y1 y2 hx0 hx1 hx2 hy0 hy1 hy2=>by
   have hm:d5 x0 x1 x2 y0 y1 y2<=d5
       (D (A P1 0) (A P1 1) (A P1 2)).1 (D (A P1 0) (A P1 1) (A P1 2)).2.1 (D (A P1 0) (A P1 1) (A P1 2)).2.2
       (D (Z P2 0) (Z P2 1) (Z P2 2)).1 (D (Z P2 0) (Z P2 1) (Z P2 2)).2.1 (D (Z P2 0) (Z P2 1) (Z P2 2)).2.2:=by
     unfold d5;cases h1:nB (x2+y2) 15
     . have h1':¬ (x2+y2<=15):=fun h=>by have:=bL.mpr h;exact Bool.false_ne_true (h1.symm.trans this)
       have h2:nB ((D (A P1 0) (A P1 1) (A P1 2)).2.2+(D (Z P2 0) (Z P2 1) (Z P2 2)).2.2) 15=false:=by
         cases hb:nB _ 15
         . rfl
         . exfalso;have:=bL.mp hb;omega
       rw[h2];simp only[bC]
       repeat (first|apply nA|apply nS|assumption)
     . exact Nat.zero_le _
   exact lT hm (o7 P1 P2)
 rcases an s with ⟨p00,p01,p02⟩;rcases ah s with ⟨p10,p11,p12⟩;rcases ae s with ⟨p20,p21,p22⟩;rcases ac s with ⟨q00,q01,q02⟩;rcases ab s with ⟨q10,q11,q12⟩;rcases a9 s with ⟨q20,q21,q22⟩;unfold dh cw;rw[a4];dsimp only;cases (nE (V L s.val+V K s.val+V F s.val) 0||nE (V C s.val+V w s.val+V v s.val) 0)
 swap;· exact Nat.zero_le _
 simp only[bC]
 simp only[aH L s.val W s.isLt,ai L s.val W s.isLt,aA L s.val W s.isLt,
   aH K s.val T s.isLt,ai K s.val T s.isLt,aA K s.val T s.isLt,
   aH F s.val Q s.isLt,ai F s.val Q s.isLt,aA F s.val Q s.isLt,
   aH C s.val P s.isLt,ai C s.val P s.isLt,aA C s.val P s.isLt,
   aH w s.val N s.isLt,ai w s.val N s.isLt,aA w s.val N s.isLt,
   aH v s.val M s.isLt,ai v s.val M s.isLt,aA v s.val M s.isLt]
 unfold ak S at p00 p01 p02 p10 p11 p12 p20 p21 p22 q00 q01 q02 q10 q11 q12 q20 q21 q22;dsimp only at p00 p01 p02 p10 p11 p12 p20 p21 p22 q00 q01 q02 q10 q11 q12 q20 q21 q22;have ar:=j (B i s) (B d s) _ _ _ _ _ _ p00 p01 p02 q00 q01 q02
 have a7:=j (fun b a c=>B i s a b c) (fun b a c=>B d s a b c) _ _ _ _ _ _
   (by simpa [aT] using p10) (by simpa [aT] using p11) (by simpa [aT] using p12)
   (by simpa [aT] using q10) (by simpa [aT] using q11) (by simpa [aT] using q12)
 rw[fx (fun a b c=>B i s a b c&&B d s a b c)] at a7;have a6:=j (fun c a b=>B i s a b c) (fun c a b=>B d s a b c) _ _ _ _ _ _ p20 p21 p22 q20 q21 q22;rw[e8 (fun a b c=>B i s a b c&&B d s a b c)] at a6;have a8:=k (B i s) (B d s) _ _ _ _ _ _ p00 p01 p02 q10 q11 q12
 have u:=k (fun a c b=>B i s a b c) (fun a c b=>B d s a b c) _ _ _ _ _ _
   (by simpa [cz] using p00) (by simpa [cz] using p01) (by simpa [cz] using p02)
   (by simpa [bK] using q20) (by simpa [bK] using q21) (by simpa [bK] using q22)
 rw[oP (fun a b c=>B i s a b c&&B d s a b c)] at u
 have t:=k (fun b a c=>B i s a b c) (fun b a c=>B d s a b c) _ _ _ _ _ _
   (by simpa [aT] using p10) (by simpa [aT] using p11) (by simpa [aT] using p12)
   (by simpa [eE] using q00) (by simpa [eE] using q01) (by simpa [eE] using q02)
 rw[fx (fun a b c=>B i s a b c&&B d s a b c)] at t
 have r:=k (fun b c a=>B i s a b c) (fun b c a=>B d s a b c) _ _ _ _ _ _
   (by simpa [eG] using p10) (by simpa [eG] using p11) (by simpa [eG] using p12)
   (by simpa [eD] using q20) (by simpa [eD] using q21) (by simpa [eD] using q22)
 rw[oO (fun a b c=>B i s a b c&&B d s a b c)] at r
 have n:=k (fun c a b=>B i s a b c) (fun c a b=>B d s a b c) _ _ _ _ _ _ p20 p21 p22
   (by simpa [dd] using q00) (by simpa [dd] using q01) (by simpa [dd] using q02)
 rw[e8 (fun a b c=>B i s a b c&&B d s a b c)] at n
 have m:=k (fun c b a=>B i s a b c) (fun c b a=>B d s a b c) _ _ _ _ _ _
   (by simpa [eF] using p20) (by simpa [eF] using p21) (by simpa [eF] using p22)
   (by simpa [eC] using q10) (by simpa [eC] using q11) (by simpa [eC] using q12)
 rw[oN (fun a b c=>B i s a b c&&B d s a b c)] at m;exact aV ar (aV a7 (aV a6 (aV a8 (aV u (aV t (aV r (aV n m)))))))
lemma fB (P1 P2:Fin 5->Fin 3->Fin 3->Fin 3->Bool) (v u:Nat)
  (n:az v) (m:az u)
  (x:ag v (fun s=>D (A (P1 s) 0) (A (P1 s) 1) (A (P1 s) 2)))
  (w:ag u (fun s=>D (A (P2 s) 0) (A (P2 s) 1) (A (P2 s) 2))) :
  az (em v u)/\
  ag (em v u) (fun s=>D (A (fun a b c=>P1 s a b c||P2 s a b c) 0)
    (A (fun a b c=>P1 s a b c||P2 s a b c) 1)
    (A (fun a b c=>P1 s a b c||P2 s a b c) 2)):=by
 have h:=de 5 4 15 v u 0x4210842108421084210 0x3def7bdef7bdef7bdef (by omega)
  n.2 m.2 (by decide) (by decide)
  (fun i hi=>qJ ⟨i,hi⟩) (fun i hi=>xC ⟨i,hi⟩)
  (fun i hi=>lO (n.1 i hi) (by decide))
  (fun i hi=>lO (m.1 i hi) (by decide))
 unfold em
 refine ⟨⟨fun i hi=>by rw[h.1 i hi];exact xL (n.1 i hi) (m.1 i hi),h.2.2.1⟩,fun s=>?_⟩
 have l:∀ k:Fin 3,A (P1 s) k<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>by
  have d:∀ b c:Fin 3,al (P1 s k b c)<=al (P1 s k b c||P2 s k b c):=fun b c=>by cases P1 s k b c <;> cases P2 s k b c <;> simp[al]
  have:=d 0 0;have:=d 0 1;have:=d 0 2;have:=d 1 0;have:=d 1 1;have:=d 1 2
  have:=d 2 0;have:=d 2 1;have:=d 2 2;unfold A aq;dsimp only;linarith
 have j:∀ k:Fin 3,A (P2 s) k<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>by
  have d:∀ b c:Fin 3,al (P2 s k b c)<=al (P1 s k b c||P2 s k b c):=fun b c=>by cases P1 s k b c <;> cases P2 s k b c <;> simp[al]
  have:=d 0 0;have:=d 0 1;have:=d 0 2;have:=d 1 0;have:=d 1 1;have:=d 1 2
  have:=d 2 0;have:=d 2 1;have:=d 2 2;unfold A aq;dsimp only;linarith
 have t:=cM (l 0) (l 1) (l 2);have r:=cM (j 0) (j 1) (j 2);rcases x s with ⟨a0,a1,a2⟩;rcases w s with ⟨b0,b1,b2⟩;rw[h.1 (3*s.val) (by omega),h.1 (3*s.val+1) (by omega),h.1 (3*s.val+2) (by omega)]
 exact ⟨xL (lT a0 t.1) (lT b0 r.1),
   xL (lT a1 t.2.1) (lT b1 r.2.1),
   xL (lT a2 t.2.2) (lT b2 r.2.2)⟩
lemma fe (P1 P2:Fin 5->Fin 3->Fin 3->Fin 3->Bool)
   (r n m l j d:Nat)
   (a4:az r) (ac:az n) (ab:az m) (a3:az l) (a9:az j) (a8:az d)
   (c4:ag r (fun s=>D (A (P1 s) 0) (A (P1 s) 1) (A (P1 s) 2)))
   (d0:ag n (fun s=>D (Z (P1 s) 0) (Z (P1 s) 1) (Z (P1 s) 2)))
   (cs:ag m (fun s=>D (aK (P1 s) 0) (aK (P1 s) 1) (aK (P1 s) 2)))
   (c3:ag l (fun s=>D (A (P2 s) 0) (A (P2 s) 1) (A (P2 s) 2)))
   (ch:ag j (fun s=>D (Z (P2 s) 0) (Z (P2 s) 1) (Z (P2 s) 2)))
   (ca:ag d (fun s=>D (aK (P2 s) 0) (aK (P2 s) 1) (aK (P2 s) 2))) :
   az (ci r n m l j d)/\
   ag (ci r n m l j d) (fun s=>D (A (fun a b c=>P1 s a b c||P2 s a b c) 0)
                                                       (A (fun a b c=>P1 s a b c||P2 s a b c) 1)
                                                       (A (fun a b c=>P1 s a b c||P2 s a b c) 2)):=by
 unfold ci;cases nE (lor (lor n m) (lor j d)) 0
 swap
 . simp only[bT];exact fB P1 P2 r l a4 a3 c4 c3
 simp only[bC]
 have L:∀ s:Fin 5,aE r n m l j d s.val<2^15/\
     (∀ c<3,o 5 c (aE r n m l j d s.val)<=9)/\
     (let sw:=D (A (fun a b c=>P1 s a b c||P2 s a b c) 0)
                      (A (fun a b c=>P1 s a b c||P2 s a b c) 1)
                      (A (fun a b c=>P1 s a b c||P2 s a b c) 2)
      o 5 0 (aE r n m l j d s.val)<=sw.1/\
      o 5 1 (aE r n m l j d s.val)<=sw.2.1/\
      o 5 2 (aE r n m l j d s.val)<=sw.2.2):=by
   intro s
   have K:∀ k:Fin 3,A (P1 s) k<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>by
     have u:∀ b c:Fin 3,al (P1 s k b c)<=al (P1 s k b c||P2 s k b c):=fun b c=>by cases P1 s k b c <;> cases P2 s k b c <;> simp[al]
     have:=u 0 0;have:=u 0 1;have:=u 0 2;have:=u 1 0;have:=u 1 1;have:=u 1 2
     have:=u 2 0;have:=u 2 1;have:=u 2 2;unfold A aq;dsimp only;linarith
   have F:∀ k:Fin 3,A (P2 s) k<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>by
     have u:∀ b c:Fin 3,al (P2 s k b c)<=al (P1 s k b c||P2 s k b c):=fun b c=>by cases P1 s k b c <;> cases P2 s k b c <;> simp[al]
     have:=u 0 0;have:=u 0 1;have:=u 0 2;have:=u 1 0;have:=u 1 1;have:=u 1 2
     have:=u 2 0;have:=u 2 1;have:=u 2 2;unfold A aq;dsimp only;linarith
   have ah:=cM (K 0) (K 1) (K 2);have ae:=cM (F 0) (F 1) (F 2)
   have bb:∀ k:Fin 3,cO (V n s.val)<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>by
     have t:=ky (V n s.val);have u:=gc (P1 s) k;rw[gO] at u;rcases d0 s with ⟨b0,b1,b2⟩;dsimp only at b0 b1 b2;rw[aH n s.val ac s.isLt,ai n s.val ac s.isLt,aA n s.val ac s.isLt] at t;exact lT t (lT (nA (nA (nS b0 6) (nS b1 6)) (nS b2 6)) (lT u (K k)))
   have b9:∀ k:Fin 3,cO (V j s.val)<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>by
     have t:=ky (V j s.val);have u:=gc (P2 s) k;rw[gO] at u;rcases ch s with ⟨b0,b1,b2⟩;dsimp only at b0 b1 b2;rw[aH j s.val a9 s.isLt,ai j s.val a9 s.isLt,aA j s.val a9 s.isLt] at t;exact lT t (lT (nA (nA (nS b0 6) (nS b1 6)) (nS b2 6)) (lT u (F k)))
   have b8:∀ k:Fin 3,cO (V m s.val)<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>by
     have t:=ky (V m s.val);have u:=gc (fun a c b=>P1 s a b c) k;rw[cz,bK,bK,bK,gO] at u;rcases cs s with ⟨b0,b1,b2⟩;dsimp only at b0 b1 b2;rw[aH m s.val ab s.isLt,ai m s.val ab s.isLt,aA m s.val ab s.isLt] at t;exact lT t (lT (nA (nA (nS b0 6) (nS b1 6)) (nS b2 6)) (lT u (K k)))
   have b7:∀ k:Fin 3,cO (V d s.val)<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>by
     have t:=ky (V d s.val);have u:=gc (fun a c b=>P2 s a b c) k;rw[cz,bK,bK,bK,gO] at u;rcases ca s with ⟨b0,b1,b2⟩;dsimp only at b0 b1 b2;rw[aH d s.val a8 s.isLt,ai d s.val a8 s.isLt,aA d s.val a8 s.isLt] at t;exact lT t (lT (nA (nA (nS b0 6) (nS b1 6)) (nS b2 6)) (lT u (F k)))
   rw[sF];dsimp only
   set cm:=aa (aa (cO (V n s.val)) (cO (V j s.val)))
                  (aa (cO (V m s.val)) (cO (V d s.val)))
   set z0:=aa cm (aa (land (V r s.val) 31) (land (V l s.val) 31));set z1:=aa cm (aa (land (shiftRight (V r s.val) 5) 31) (land (shiftRight (V l s.val) 5) 31));set z2:=aa cm (aa (shiftRight (V r s.val) 10) (shiftRight (V l s.val) 10))
   have C:∀ k:Fin 3,cm<=A (fun a b c=>P1 s a b c||P2 s a b c) k:=fun k=>
     aV (aV (bb k) (b9 k)) (aV (b8 k) (b7 k))
   have z:=cM (C 0) (C 1) (C 2);rw[af cm cm cm (lR _) (lR _)] at z;rcases c4 s with ⟨a0,a1,a2⟩;rcases c3 s with ⟨b0,b1,b2⟩;dsimp only at a0 a1 a2 b0 b1 b2;have c2:=aH r s.val a4 s.isLt;have c1:=ai r s.val a4 s.isLt;have c0:=aA r s.val a4 s.isLt;have bz:=aH l s.val a3 s.isLt;have bw:=ai l s.val a3 s.isLt;have bs:=aA l s.val a3 s.isLt
   have W:(D (A (fun a b c=>P1 s a b c||P2 s a b c) 0)
                      (A (fun a b c=>P1 s a b c||P2 s a b c) 1)
                      (A (fun a b c=>P1 s a b c||P2 s a b c) 2)).2.2<=9:=
     gQ (bS _ 0) (bS _ 1) (bS _ 2)
   have v:=jS (A (fun a b c=>P1 s a b c||P2 s a b c) 0)
                                (A (fun a b c=>P1 s a b c||P2 s a b c) 1)
                                (A (fun a b c=>P1 s a b c||P2 s a b c) 2)
   have Q:z0<=(D (A (fun a b c=>P1 s a b c||P2 s a b c) 0)
                             (A (fun a b c=>P1 s a b c||P2 s a b c) 1)
                             (A (fun a b c=>P1 s a b c||P2 s a b c) 2)).1:=
     aV z.1 (aV (lT (c2 ▸ a0) ah.1) (lT (bz ▸ b0) ae.1))
   have P:z1<=(D (A (fun a b c=>P1 s a b c||P2 s a b c) 0)
                             (A (fun a b c=>P1 s a b c||P2 s a b c) 1)
                             (A (fun a b c=>P1 s a b c||P2 s a b c) 2)).2.1:=
     aV z.2.1 (aV (lT (c1 ▸ a1) ah.2.1) (lT (bw ▸ b1) ae.2.1))
   have M:z2<=(D (A (fun a b c=>P1 s a b c||P2 s a b c) 0)
                             (A (fun a b c=>P1 s a b c||P2 s a b c) 1)
                             (A (fun a b c=>P1 s a b c||P2 s a b c) 2)).2.2:=
     aV z.2.2 (aV (lT (c0 ▸ a2) ah.2.2) (lT (bs ▸ b2) ae.2.2))
   have b4:z0<=9:=lT Q (lT v.1 (lT v.2 W));have b3:z1<=9:=lT P (lT v.2 W);have aw:z2<=9:=lT M W;have x:z0<2^5:=lO b4 (by decide);have w:z1<2^5:=lO b3 (by decide);have N:z2<2^5:=lO aw (by decide);have T:=fd 5 z0 z1 z2 x w N;have c8:=gG 5 z0 z1 z2 x w N
   have c9:lor (lor z0 (shiftLeft z1 5)) (shiftLeft z2 10)=bE 5 z0 z1 z2:=
     (iX 5 z0 z1 z2 x w).symm
   rw[c9]
   refine ⟨c8,fun c u=>by
     have:c=0\/c=1\/c=2:=by omega
     rcases this with rfl|rfl|rfl
     . rw[T.1];exact b4
     . rw[T.2.1];exact b3
     . rw[T.2.2];exact aw,?_⟩
   rw[T.1,T.2.1,T.2.2];exact ⟨Q,P,M⟩
 have h5:=cv 15 (aE r n m l j d 0) (aE r n m l j d 1) (aE r n m l j d 2)
   (aE r n m l j d 3) (aE r n m l j d 4) (L 0).1 (L 1).1 (L 2).1 (L 3).1 (L 4).1
 have b6:=dl 15 (aE r n m l j d 0) (aE r n m l j d 1) (aE r n m l j d 2)
   (aE r n m l j d 3) (aE r n m l j d 4) (L 0).1 (L 1).1 (L 2).1 (L 3).1 (L 4).1
 have b5:lor (lor (lor (lor (aE r n m l j d 0)
     (shiftLeft (aE r n m l j d 1) 15))
     (shiftLeft (aE r n m l j d 2) 30))
     (shiftLeft (aE r n m l j d 3) 45))
     (shiftLeft (aE r n m l j d 4) 60) =
     bM 15 (aE r n m l j d 0) (aE r n m l j d 1) (aE r n m l j d 2)
       (aE r n m l j d 3) (aE r n m l j d 4):=
   (dv 15 _ _ _ _ _ (L 0).1 (L 1).1 (L 2).1 (L 3).1).symm
 rw[b5]
 have y:∀ (s:Fin 5) (c:Fin 3),o 5 (3*s.val+c.val)
     (bM 15 (aE r n m l j d 0) (aE r n m l j d 1) (aE r n m l j d 2)
       (aE r n m l j d 3) (aE r n m l j d 4))=o 5 c.val (aE r n m l j d s.val):=by
   intro s c;rw[<- aY 5 c.val s.val _ c.isLt];congr 1
   fin_cases s
   . exact h5.1
   . exact h5.2.1
   . exact h5.2.2.1
   . exact h5.2.2.2.1
   . exact h5.2.2.2.2
 refine ⟨⟨fun i hi=>?_,b6⟩,fun s=>?_⟩
 . have h:=y ⟨i/3,by omega⟩ ⟨i % 3,by omega⟩
   have an:3*(i/3)+i % 3=i:=by omega
   rw[an] at h;rw[h];exact (L ⟨i/3,by omega⟩).2.1 (i % 3) (by omega)
 . have gK:=y s 0;simp only[Fin.val_zero,nZ] at gK;have eW:=y s 1;have c7:(1:Fin 3).val=1:=rfl;rw[c7] at eW;have fj:=y s 2;have c6:(2:Fin 3).val=2:=rfl;rw[c6] at fj;rw[gK,eW,fj];exact (L s).2.2
lemma kE {a b:Nat} (k:a<2^75) (j:b<2^75)
  (d:∀ i<5,o 15 i a<32) (c:∀ i<5,o 15 i b<32) :
  ge a b<2^75/\∀ i<5,o 15 i (ge a b)=max (o 15 i a) (o 15 i b):=by
 have h:=de 15 5 5 a b 0x20004000800100020 0x1f003e007c00f801f (by omega) k j (by decide) (by decide)
  (fun i hi=>xx ⟨i,hi⟩) (fun i hi=>uN ⟨i,hi⟩) d c
 exact ⟨h.2.2.1,h.1⟩
lemma jR {v:Nat} (b:v<2^75) (a:∀ i<5,o 15 i v<=18) :
  it v<2^75/\∀ i<5,o 15 i (it v)=o 15 i v - 9:=by
 have h:=jB 15 4 9 5 v 0x7000e001c0038007 0x10002000400080010 (by omega) (by decide)
  b (by decide) (by decide) (fun i hi=>tC ⟨i,hi⟩) (fun i hi=>xy ⟨i,hi⟩)
  (fun i hi=>by have:=a i hi;omega)
 exact ⟨h.2,h.1⟩
lemma dK (P1 P2:Fin 5->Fin 3->Fin 3->Fin 3->Bool) (M L:Nat)
   (l:az M) (j:az L)
   (c1:ag M (fun s=>D (A (P1 s) 0) (A (P1 s) 1) (A (P1 s) 2)))
   (c0:ag L (fun s=>D (A (P2 s) 0) (A (P2 s) 1) (A (P2 s) 2))) :
   az (cp M L)/\
   ag (cp M L) (fun s=>D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
                                          (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
                                          (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)):=by
 unfold cp;cases (nE M 0||nE L 0)
 swap
 . rw[bT];exact ⟨⟨fun _ _=>by simp[o],by decide⟩,fun _=>by simp[o]⟩
 rw[bC];dsimp only
 have d:(0x1f003e007c00f801f:Nat)<2^75:=by decide
 have m:∀ i<5,o 15 i 0x1f003e007c00f801f=31:=fun i hi=>uN ⟨i,hi⟩;set x0:=land M 0x1f003e007c00f801f;set x1:=land (shiftRight M 5) 0x1f003e007c00f801f;set x2:=land (shiftRight M 10) 0x1f003e007c00f801f;set y0:=land L 0x1f003e007c00f801f;set y1:=land (shiftRight L 5) 0x1f003e007c00f801f;set y2:=land (shiftRight L 10) 0x1f003e007c00f801f
 have r:∀ i<5,o 15 i x0=o 5 (3*i) M:=fun i hi=>by
   have h:=cb 5 5 0 M 0x1f003e007c00f801f m i hi;simp only[Nat.zero_mul,nZ] at h;exact h
 have K:∀ i<5,o 15 i x1=o 5 (3*i+1) M:=cb 5 5 1 M 0x1f003e007c00f801f m;have aw:∀ i<5,o 15 i x2=o 5 (3*i+2) M:=cb 5 5 2 M 0x1f003e007c00f801f m
 have n:∀ i<5,o 15 i y0=o 5 (3*i) L:=fun i hi=>by
   have h:=cb 5 5 0 L 0x1f003e007c00f801f m i hi;simp only[Nat.zero_mul,nZ] at h;exact h
 have F:∀ i<5,o 15 i y1=o 5 (3*i+1) L:=cb 5 5 1 L 0x1f003e007c00f801f m;have ar:∀ i<5,o 15 i y2=o 5 (3*i+2) L:=cb 5 5 2 L 0x1f003e007c00f801f m;have b1:x0<2^75:=lO nR d;have bb:x1<2^75:=lO nR d;have bz:x2<2^75:=lO nR d;have b0:y0<2^75:=lO nR d;have b9:y1<2^75:=lO nR d;have bw:y2<2^75:=lO nR d;have a9:=ap 15 5 x0 y0 (fun i hi=>by rw[r i hi,n i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide)) b1 b0;have a3:=ap 15 5 x0 y1 (fun i hi=>by rw[r i hi,F i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide)) b1 b9;have T:=ap 15 5 x1 y0 (fun i hi=>by rw[K i hi,n i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide)) bb b0;have W:=ap 15 5 x0 y2 (fun i hi=>by rw[r i hi,ar i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide)) b1 bw;have Q:=ap 15 5 x1 y1 (fun i hi=>by rw[K i hi,F i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide)) bb b9;have P:=ap 15 5 x2 y0 (fun i hi=>by rw[aw i hi,n i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide)) bz b0
 have b6:=kE a3.1 T.1
   (fun i hi=>by rw[a3.2 i hi,r i hi,F i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide))
   (fun i hi=>by rw[T.2 i hi,K i hi,n i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide))
 have a8:=kE Q.1 P.1
   (fun i hi=>by rw[Q.2 i hi,K i hi,F i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide))
   (fun i hi=>by rw[P.2 i hi,aw i hi,n i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide))
 have x:∀ i<5,o 15 i (ge (x1+y1) (x2+y0))<=18:=fun i hi=>by
   rw[a8.2 i hi,Q.2 i hi,P.2 i hi,K i hi,F i hi,aw i hi,n i hi];exact xL (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (nA (l.1 _ (by omega)) (j.1 _ (by omega)))
 have a7:=kE W.1 a8.1
   (fun i hi=>by rw[W.2 i hi,r i hi,ar i hi];exact lO (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (by decide))
   (fun i hi=>lO (x i hi) (by decide))
 have y:∀ i<5,o 15 i (x0+y0)<=18:=fun i hi=>by
   rw[a9.2 i hi,r i hi,n i hi];exact nA (l.1 _ (by omega)) (j.1 _ (by omega))
 have N:∀ i<5,o 15 i (ge (x0+y1) (x1+y0))<=18:=fun i hi=>by
   rw[b6.2 i hi,a3.2 i hi,T.2 i hi,r i hi,F i hi,K i hi,n i hi];exact xL (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (nA (l.1 _ (by omega)) (j.1 _ (by omega)))
 have w:∀ i<5,o 15 i (ge (x0+y2) (ge (x1+y1) (x2+y0)))<=18:=fun i hi=>by
   rw[a7.2 i hi,W.2 i hi,r i hi,ar i hi];exact xL (nA (l.1 _ (by omega)) (j.1 _ (by omega))) (x i hi)
 have b4:=jR a9.1 y;have b3:=jR b6.1 N;have b2:=jR a7.1 w
 have v:∀ i<5,o 15 i (it (x0+y0))<=9:=fun i hi=>by
   rw[b4.2 i hi];exact nF (y i hi)
 have u:∀ i<5,o 15 i (it (ge (x0+y1) (x1+y0)))<=9:=fun i hi=>by
   rw[b3.2 i hi];exact nF (N i hi)
 have t:∀ i<5,o 15 i (it (ge (x0+y2) (ge (x1+y1) (x2+y0))))<=9:=fun i hi=>by
   rw[b2.2 i hi];exact nF (w i hi)
 have a6:=jV 5 5 _ _ _ b4.1 b3.1 b2.1
   (fun i hi=>lO (v i hi) (by decide))
   (fun i hi=>lO (u i hi) (by decide))
   (fun i hi=>lO (t i hi) (by decide))
 refine ⟨⟨fun i hi=>?_,a6.1⟩,fun s=>?_⟩
 . have z:3*(i/3)+i % 3=i:=by omega
   have hr:=a6.2 (i/3) (by omega)
   have bs:i % 3=0\/i % 3=1\/i % 3=2:=by omega
   rcases bs with hm|hm|hm
   . rw[<- z,hm,nZ,hr.1];exact v _ (by omega)
   . rw[<- z,hm,hr.2.1];exact u _ (by omega)
   . rw[<- z,hm,hr.2.2];exact t _ (by omega)
 . have C:∀ k:Fin 3,A (P1 s) k+A (P2 s) k - 9<=A (fun a b c=>P1 s a b c&&P2 s a b c) k:=fun k=>by
     have hc:∀ b c:Fin 3,al (P1 s k b c)+al (P2 s k b c)<=al (P1 s k b c&&P2 s k b c)+1:=fun b c=>by
       cases P1 s k b c <;> cases P2 s k b c <;> simp[al]
     have:=hc 0 0;have:=hc 0 1;have:=hc 0 2;have:=hc 1 0;have:=hc 1 1;have:=hc 1 2
     have:=hc 2 0;have:=hc 2 1;have:=hc 2 2;apply nF;unfold A aq;dsimp only;linarith
   have ae:=cM (C 0) (C 1) (C 2);have an:=gX (A (P1 s) 0) (A (P1 s) 1) (A (P1 s) 2) (A (P2 s) 0) (A (P2 s) 1) (A (P2 s) 2);rcases c1 s with ⟨a0,a1,a2⟩;rcases c0 s with ⟨qa0,qa1,qa2⟩;dsimp only at an ae a0 a1 a2 qa0 qa1 qa2;have hr:=a6.2 s.val s.isLt
   rw[hr.1,hr.2.1,hr.2.2,b4.2 s.val s.isLt,b3.2 s.val s.isLt,b2.2 s.val s.isLt,
     a9.2 s.val s.isLt,b6.2 s.val s.isLt,a3.2 s.val s.isLt,T.2 s.val s.isLt,
     a7.2 s.val s.isLt,W.2 s.val s.isLt,a8.2 s.val s.isLt,Q.2 s.val s.isLt,P.2 s.val s.isLt,
     r s.val s.isLt,K s.val s.isLt,aw s.val s.isLt,n s.val s.isLt,F s.val s.isLt,ar s.val s.isLt]
   exact ⟨lT (nS (nA a0 qa0) 9) (lT an.1 ae.1),
     lT (nS (max_le_max (nA a0 qa1) (nA a1 qa0)) 9) (lT an.2.1 ae.2.1),
     lT (nS (max_le_max (nA a0 qa2) (max_le_max (nA a1 qa1) (nA a2 qa0))) 9) (lT an.2.2 ae.2.2)⟩
set_option maxHeartbeats 800000 in
lemma i4 (P1 P2:Fin 5->Fin 3->Fin 3->Fin 3->Bool)
   (l w t j r n:Nat)
   (c5:az l) (cs:az w) (cm:az t) (c4:az j) (ch:az r) (ca:az n)
   (g1:ag l (fun s=>D (A (P1 s) 0) (A (P1 s) 1) (A (P1 s) 2)))
   (hd:ag w (fun s=>D (Z (P1 s) 0) (Z (P1 s) 1) (Z (P1 s) 2)))
   (hb:ag t (fun s=>D (aK (P1 s) 0) (aK (P1 s) 1) (aK (P1 s) 2)))
   (g0:ag j (fun s=>D (A (P2 s) 0) (A (P2 s) 1) (A (P2 s) 2)))
   (ha:ag r (fun s=>D (Z (P2 s) 0) (Z (P2 s) 1) (Z (P2 s) 2)))
   (gs:ag n (fun s=>D (aK (P2 s) 0) (aK (P2 s) 1) (aK (P2 s) 2))) :
   az (eN l w t j r n)/\
   ag (eN l w t j r n) (fun s=>D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
                                                   (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
                                                   (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)):=by
 unfold eN;cases (nE (lor (lor l w) t) 0||nE (lor (lor j r) n) 0)
 swap
 . rw[bT];exact ⟨⟨fun _ _=>by simp[o],by decide⟩,fun _=>by simp[o]⟩
 rw[bC];cases nE (lor (lor w t) (lor r n)) 0
 swap
 . rw[bT];exact dK P1 P2 l j c5 c4 g1 g0
 rw[bC]
 have hs:∀ s:Fin 5,bp l w t j r n s.val<2^15/\
     (∀ c<3,o 5 c (bp l w t j r n s.val)<=9)/\
     (let sw:=D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
                      (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
                      (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)
      o 5 0 (bp l w t j r n s.val)<=sw.1/\
      o 5 1 (bp l w t j r n s.val)<=sw.2.1/\
      o 5 2 (bp l w t j r n s.val)<=sw.2.2):=by
   intro s
   have a7:∀ k:Fin 3,A (P1 s) k+A (P2 s) k - 9<=A (fun a b c=>P1 s a b c&&P2 s a b c) k:=fun k=>by
     have hc:∀ b c:Fin 3,al (P1 s k b c)+al (P2 s k b c)<=al (P1 s k b c&&P2 s k b c)+1:=fun b c=>by
       cases P1 s k b c <;> cases P2 s k b c <;> simp[al]
     have:=hc 0 0;have:=hc 0 1;have:=hc 0 2;have:=hc 1 0;have:=hc 1 1;have:=hc 1 2
     have:=hc 2 0;have:=hc 2 1;have:=hc 2 2;apply nF;unfold A aq;dsimp only;linarith
   have d0:=cM (a7 0) (a7 1) (a7 2);have c6:=gX (A (P1 s) 0) (A (P1 s) 1) (A (P1 s) 2) (A (P2 s) 0) (A (P2 s) 1) (A (P2 s) 2);have ah:=cZ (P1 s) (P2 s);have a4:=cZ (P2 s) (P1 s)
   have a8:(fun a b c=>P2 s a b c&&P1 s a b c)=(fun a b c=>P1 s a b c&&P2 s a b c):=by
     funext a b c;exact bY _ _
   rw[a8] at a4;have a3:=cZ (fun a c b=>P1 s a b c) (fun a c b=>P2 s a b c);have F:=cZ (fun a c b=>P2 s a b c) (fun a c b=>P1 s a b c)
   have a5:(fun x y z=>P2 s x z y&&P1 s x z y)=(fun x y z=>P1 s x z y&&P2 s x z y):=by
     funext a b c;exact bY _ _
   rw[a5] at F;have T:∀ k,A (fun a c b=>P1 s a b c) k=A (P1 s) k:=cz (P1 s);have Q:∀ k,A (fun a c b=>P2 s a b c) k=A (P2 s) k:=cz (P2 s)
   have m:∀ k,A (fun x y z=>P1 s x z y&&P2 s x z y) k=A (fun a b c=>P1 s a b c&&P2 s a b c) k:=
     cz (fun a b c=>P1 s a b c&&P2 s a b c)
   have P:∀ k,Z (fun a c b=>P1 s a b c) k=aK (P1 s) k:=bK (P1 s);have N:∀ k,Z (fun a c b=>P2 s a b c) k=aK (P2 s) k:=bK (P2 s);dsimp only at c6 ah a4 a3 F;rw[T 0,T 1,T 2,N 0,N 1,N 2,m 0,m 1,m 2] at a3;rw[Q 0,Q 1,Q 2,P 0,P 1,P 2,m 0,m 1,m 2] at F
   have aw:(D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
                      (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
                      (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)).2.2<=9:=
     gQ (bS _ 0) (bS _ 1) (bS _ 2)
   have C:=jS (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
                                (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
                                (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)
   rcases g1 s with ⟨a0,a1,a2⟩;rcases hd s with ⟨b0,b1,b2⟩;rcases hb s with ⟨c0,c1,c2⟩;rcases g0 s with ⟨qa0,qa1,qa2⟩;rcases ha s with ⟨qb0,qb1,qb2⟩;rcases gs s with ⟨qc0,qc1,qc2⟩;dsimp only at a0 a1 a2 b0 b1 b2 c0 c1 c2 qa0 qa1 qa2 qb0 qb1 qb2 qc0 qc1 qc2
   have e0:o 5 (3*s.val) l+o 5 (3*s.val) j - 9<=
       (D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
              (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
              (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)).1:=
     lT (nS (nA a0 qa0) 9) (lT c6.1 d0.1)
   have dr:aa (o 5 (3*s.val) l+o 5 (3*s.val+1) j) (o 5 (3*s.val+1) l+o 5 (3*s.val) j) - 9<=
       (D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
              (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
              (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)).2.1:=by
     rw[aP];exact lT (nS (max_le_max (nA a0 qa1) (nA a1 qa0)) 9) (lT c6.2.1 d0.2.1)
   have dq:aa (o 5 (3*s.val) l+o 5 (3*s.val+2) j)
       (aa (o 5 (3*s.val+1) l+o 5 (3*s.val+1) j) (o 5 (3*s.val+2) l+o 5 (3*s.val) j)) - 9<=
       (D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
              (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
              (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)).2.2:=by
     rw[aP,aP];exact lT (nS (max_le_max (nA a0 qa2) (max_le_max (nA a1 qa1) (nA a2 qa0))) 9) (lT c6.2.2 d0.2.2)
   have d:∀ u v x' y0' y1' y2' K,u<=x'->land v 31<=y0'->land (shiftRight v 5) 31<=y1'->shiftRight v 10<=y2'->
       (x'+y0' - 15)+(x'+y1' - 15)+(x'+y2' - 15)<=K->
       es u v<=K:=fun u v x' y0' y1' y2' K hx h0 h1 h2 hK=>by
     have hc:=zw u v;have s0:u+land v 31 - 15<=x'+y0' - 15:=nS (nA hx h0) 15;have s1:u+land (shiftRight v 5) 31 - 15<=x'+y1' - 15:=nS (nA hx h1) 15;have s2:u+shiftRight v 10 - 15<=x'+y2' - 15:=nS (nA hx h2) 15;exact lT hc (lT (nA (nA s0 s1) s2) hK)
   unfold bp;dsimp only;have fu:=aH l s.val c5 s.isLt;have ew:=ai l s.val c5 s.isLt;have ei:=aA l s.val c5 s.isLt;have ef:=aH j s.val c4 s.isLt;have e5:=ai j s.val c4 s.isLt;have e3:=aA j s.val c4 s.isLt;have c3:=aH w s.val cs s.isLt;have bz:=ai w s.val cs s.isLt;have bw:=aA w s.val cs s.isLt;have bs:=aH t s.val cm s.isLt;have bb:=ai t s.val cm s.isLt;have b9:=aA t s.val cm s.isLt;have b8:=aH r s.val ch s.isLt;have b7:=ai r s.val ch s.isLt;have b6:=aA r s.val ch s.isLt;have b5:=aH n s.val ca s.isLt;have b4:=ai n s.val ca s.isLt;have b3:=aA n s.val ca s.isLt;rw[fu,ew,ei,ef,e5,e3];set z0:=aa (o 5 (3*s.val) l+o 5 (3*s.val) j - 9) _;set z1:=aa (aa (o 5 (3*s.val) l+o 5 (3*s.val+1) j) (o 5 (3*s.val+1) l+o 5 (3*s.val) j) - 9) _;set z2:=aa (aa (o 5 (3*s.val) l+o 5 (3*s.val+2) j) (aa (o 5 (3*s.val+1) l+o 5 (3*s.val+1) j) (o 5 (3*s.val+2) l+o 5 (3*s.val) j)) - 9) _
   have ae:z0<=(D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
                             (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
                             (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)).1:=
     aV e0 (aV
       (aV (d _ _ _ _ _ _ _ a0 (by rwa[b8]) (by rwa[b7]) (by rwa[b6]) ah.1)
                (d _ _ _ _ _ _ _ qa0 (by rwa[c3]) (by rwa[bz]) (by rwa[bw]) a4.1))
       (aV (d _ _ _ _ _ _ _ a0 (by rwa[b5]) (by rwa[b4]) (by rwa[b3]) a3.1)
                (d _ _ _ _ _ _ _ qa0 (by rwa[bs]) (by rwa[bb]) (by rwa[b9]) F.1)))
   have ac:z1<=(D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
                             (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
                             (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)).2.1:=
     aV dr (aV
       (aV (d _ _ _ _ _ _ _ a1 (by rwa[b8]) (by rwa[b7]) (by rwa[b6]) ah.2.1)
                (d _ _ _ _ _ _ _ qa1 (by rwa[c3]) (by rwa[bz]) (by rwa[bw]) a4.2.1))
       (aV (d _ _ _ _ _ _ _ a1 (by rwa[b5]) (by rwa[b4]) (by rwa[b3]) a3.2.1)
                (d _ _ _ _ _ _ _ qa1 (by rwa[bs]) (by rwa[bb]) (by rwa[b9]) F.2.1)))
   have a9:z2<=(D (A (fun a b c=>P1 s a b c&&P2 s a b c) 0)
                             (A (fun a b c=>P1 s a b c&&P2 s a b c) 1)
                             (A (fun a b c=>P1 s a b c&&P2 s a b c) 2)).2.2:=
     aV dq (aV
       (aV (d _ _ _ _ _ _ _ a2 (by rwa[b8]) (by rwa[b7]) (by rwa[b6]) ah.2.2)
                (d _ _ _ _ _ _ _ qa2 (by rwa[c3]) (by rwa[bz]) (by rwa[bw]) a4.2.2))
       (aV (d _ _ _ _ _ _ _ a2 (by rwa[b5]) (by rwa[b4]) (by rwa[b3]) a3.2.2)
                (d _ _ _ _ _ _ _ qa2 (by rwa[bs]) (by rwa[bb]) (by rwa[b9]) F.2.2)))
   have dp:z0<=9:=lT ae (lT C.1 (lT C.2 aw));have da:z1<=9:=lT ac (lT C.2 aw);have d2:z2<=9:=lT a9 aw;have M:z0<2^5:=lO dp (by decide);have L:z1<2^5:=lO da (by decide);have ab:z2<2^5:=lO d2 (by decide);have an:=fd 5 z0 z1 z2 M L ab;have gp:=gG 5 z0 z1 z2 M L ab
   have gq:lor (lor z0 (shiftLeft z1 5)) (shiftLeft z2 10)=bE 5 z0 z1 z2:=
     (iX 5 z0 z1 z2 M L).symm
   rw[gq]
   refine ⟨gp,fun c hc=>by
     have:c=0\/c=1\/c=2:=by omega
     rcases this with rfl|rfl|rfl
     . rw[an.1];exact dp
     . rw[an.2.1];exact da
     . rw[an.2.2];exact d2,?_⟩
   rw[an.1,an.2.1,an.2.2];exact ⟨ae,ac,a9⟩
 have h5:=cv 15 (bp l w t j r n 0) (bp l w t j r n 1) (bp l w t j r n 2)
   (bp l w t j r n 3) (bp l w t j r n 4) (hs 0).1 (hs 1).1 (hs 2).1 (hs 3).1 (hs 4).1
 have e2:=dl 15 (bp l w t j r n 0) (bp l w t j r n 1) (bp l w t j r n 2)
   (bp l w t j r n 3) (bp l w t j r n 4) (hs 0).1 (hs 1).1 (hs 2).1 (hs 3).1 (hs 4).1
 have e1:lor (lor (lor (lor (bp l w t j r n 0)
     (shiftLeft (bp l w t j r n 1) 15))
     (shiftLeft (bp l w t j r n 2) 30))
     (shiftLeft (bp l w t j r n 3) 45))
     (shiftLeft (bp l w t j r n 4) 60) =
     bM 15 (bp l w t j r n 0) (bp l w t j r n 1) (bp l w t j r n 2)
       (bp l w t j r n 3) (bp l w t j r n 4):=
   (dv 15 _ _ _ _ _ (hs 0).1 (hs 1).1 (hs 2).1 (hs 3).1).symm
 rw[e1]
 have W:∀ (s:Fin 5) (c:Fin 3),o 5 (3*s.val+c.val)
     (bM 15 (bp l w t j r n 0) (bp l w t j r n 1) (bp l w t j r n 2)
       (bp l w t j r n 3) (bp l w t j r n 4))=o 5 c.val (bp l w t j r n s.val):=by
   intro s c;rw[<- aY 5 c.val s.val _ c.isLt];congr 1
   fin_cases s
   . exact h5.1
   . exact h5.2.1
   . exact h5.2.2.1
   . exact h5.2.2.2.1
   . exact h5.2.2.2.2
 refine ⟨⟨fun i hi=>?_,e2⟩,fun s=>?_⟩
 . have h:=W ⟨i/3,by omega⟩ ⟨i % 3,by omega⟩
   have d1:3*(i/3)+i % 3=i:=by omega
   rw[d1] at h;rw[h];exact (hs ⟨i/3,by omega⟩).2.1 (i % 3) (by omega)
 . have gK:=W s 0;simp only[Fin.val_zero,nZ] at gK;have eW:=W s 1;have g4:(1:Fin 3).val=1:=rfl;rw[g4] at eW;have fj:=W s 2;have g3:(2:Fin 3).val=2:=rfl;rw[g3] at fj;rw[gK,eW,fj];exact (hs s).2.2
lemma vb (m:Nat) (e:Fin 5):bk m e<=9:=by
 unfold bk gz;have h0:=gC (ao m e) 0;have h1:=gC (ao m e) 1;have h2:=gC (ao m e) 2;omega
lemma bV (m:Nat) (s:Fin 5):cw m s<=27:=zi (B m s)
lemma iE (m:Nat) (h d c b a:Nat)
   (h0:bk m 0<=h/\h<=9) (h1:bk m 1<=d/\d<=9)
   (h2:bk m 2<=c/\c<=9) (h3:bk m 3<=b/\b<=9)
   (h4:bk m 4<=a/\a<=9) :
   eV (bM 5 h d c b a)/\dI (bM 5 h d c b a) m:=by
 have hl:=cv 5 h d c b a (by omega) (by omega) (by omega) (by omega) (by omega);have j:=dl 5 h d c b a (by omega) (by omega) (by omega) (by omega) (by omega);refine ⟨⟨fun i hi=>?_,j⟩,fun e=>?_⟩
 . have:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
   rcases this with rfl|rfl|rfl|rfl|rfl <;> omega
 . have:e=0\/e=1\/e=2\/e=3\/e=4:=by fin_cases e <;> simp
   rcases this with rfl|rfl|rfl|rfl|rfl <;> norm_num <;> omega
lemma iD (m:Nat) (h d c b a:Nat)
   (h0:h<=cw m 0) (h1:d<=cw m 1) (h2:c<=cw m 2)
   (h3:b<=cw m 3) (h4:a<=cw m 4) :
   fv (bM 6 h d c b a)/\e7 (bM 6 h d c b a) m:=by
 have c0:=bV m 0;have c1:=bV m 1;have c2:=bV m 2;have c3:=bV m 3;have c4:=bV m 4;have hl:=cv 6 h d c b a (by omega) (by omega) (by omega) (by omega) (by omega);have j:=dl 6 h d c b a (by omega) (by omega) (by omega) (by omega) (by omega);refine ⟨⟨fun i hi=>?_,j⟩,fun s=>?_⟩
 . have:i=0\/i=1\/i=2\/i=3\/i=4:=by omega
   rcases this with rfl|rfl|rfl|rfl|rfl <;> omega
 . have:s=0\/s=1\/s=2\/s=3\/s=4:=by fin_cases s <;> simp
   rcases this with rfl|rfl|rfl|rfl|rfl <;> norm_num <;> omega
lemma sN:∀ i:Fin 5,o 5 i.val 0xf7bdef=15:=by decide +kernel
lemma vL:∀ i:Fin 5,o 5 i.val 0x6318c6=6:=by decide +kernel
lemma tD:∀ i:Fin 5,o 5 i.val 0x94a529=9:=by decide +kernel
lemma zo:∀ i:Fin 5,o 6 i.val 0x1f7df7df=31:=by decide +kernel
lemma tE:∀ i:Fin 5,o 6 i.val 0x5145145=5:=by decide +kernel
def fF (pa qa:Nat):Nat:=
 let s:=pa+qa;let d:=land (s+0x6318c6) 0x1084210;let m:=d - shiftRight d 4
 lor (land s (0xf7bdef - m)) (land 0x94a529 m)
def eI (pb qb:Nat):Nat:=
 let d:=land ((lor pb 0x20820820) - qb) 0x20820820;let m:=d - shiftRight d 5
 lor (land pb m) (land qb (0x1f7df7df - m))
def eo (pa qa:Nat):Nat:=
 let d:=land ((lor pa 0x1084210) - qa) 0x1084210;let m:=d - shiftRight d 4
 lor (land qa m) (land pa (0xf7bdef - m))
def dF (pb qb:Nat):Nat:=
 let x:=pb+qb+0x5145145;let d:=land x 0x20820820
 land x (d - shiftRight d 5)
def e9 (pa qa par pac qar qac:Nat):Nat:=
 let h:=av (land pa 31+land qa 31) (eA par pac qar qac 0);let d:=av (land (shiftRight pa 5) 31+land (shiftRight qa 5) 31) (eA par pac qar qac 1);let c:=av (land (shiftRight pa 10) 31+land (shiftRight qa 10) 31) (eA par pac qar qac 2);let b:=av (land (shiftRight pa 15) 31+land (shiftRight qa 15) 31) (eA par pac qar qac 3);let a:=av (shiftRight pa 20+shiftRight qa 20) (eA par pac qar qac 4)
 lor (lor (lor (lor h (shiftLeft d 5)) (shiftLeft c 10)) (shiftLeft b 15)) (shiftLeft a 20)
def gl (pb qb bf be bd qb0 qb1 qb2:Nat):Nat:=
 cond (nE (lor (lor bf be) (lor bd (lor qb0 (lor qb1 qb2)))) 0) (eI pb qb)
 (let h:=aa (aa (land pb 63) (land qb 63)) (ff bf be bd qb0 qb1 qb2 0)
  let d:=aa (aa (land (shiftRight pb 6) 63) (land (shiftRight qb 6) 63)) (ff bf be bd qb0 qb1 qb2 1);let c:=aa (aa (land (shiftRight pb 12) 63) (land (shiftRight qb 12) 63)) (ff bf be bd qb0 qb1 qb2 2);let b:=aa (aa (land (shiftRight pb 18) 63) (land (shiftRight qb 18) 63)) (ff bf be bd qb0 qb1 qb2 3);let a:=aa (aa (shiftRight pb 24) (shiftRight qb 24)) (ff bf be bd qb0 qb1 qb2 4)
  lor (lor (lor (lor h (shiftLeft d 6)) (shiftLeft c 12)) (shiftLeft b 18)) (shiftLeft a 24))
def e4 (pa qa par pac qar qac:Nat):Nat:=
 let h:=av (av (land pa 31) (land qa 31)) (d6 par pac qar qac 0);let d:=av (av (land (shiftRight pa 5) 31) (land (shiftRight qa 5) 31)) (d6 par pac qar qac 1);let c:=av (av (land (shiftRight pa 10) 31) (land (shiftRight qa 10) 31)) (d6 par pac qar qac 2);let b:=av (av (land (shiftRight pa 15) 31) (land (shiftRight qa 15) 31)) (d6 par pac qar qac 3);let a:=av (av (shiftRight pa 20) (shiftRight qa 20)) (d6 par pac qar qac 4)
 lor (lor (lor (lor h (shiftLeft d 5)) (shiftLeft c 10)) (shiftLeft b 15)) (shiftLeft a 20)
def dZ (pb qb bf be bd qb0 qb1 qb2:Nat):Nat:=
 cond (nE (lor (lor bf be) bd) 0||nE (lor (lor qb0 qb1) qb2) 0) (dF pb qb)
 (let h:=aa (land pb 63+land qb 63 - 27) (dh bf be bd qb0 qb1 qb2 0)
  let d:=aa (land (shiftRight pb 6) 63+land (shiftRight qb 6) 63 - 27) (dh bf be bd qb0 qb1 qb2 1);let c:=aa (land (shiftRight pb 12) 63+land (shiftRight qb 12) 63 - 27) (dh bf be bd qb0 qb1 qb2 2);let b:=aa (land (shiftRight pb 18) 63+land (shiftRight qb 18) 63 - 27) (dh bf be bd qb0 qb1 qb2 3);let a:=aa (shiftRight pb 24+shiftRight qb 24 - 27) (dh bf be bd qb0 qb1 qb2 4)
  lor (lor (lor (lor h (shiftLeft d 6)) (shiftLeft c 12)) (shiftLeft b 18)) (shiftLeft a 24))
lemma iI {k j h d:Nat} (c:eV h) (b:eV d)
  (n:dI h k) (m:dI d j) :
  eV (fF h d)/\dI (fF h d) (k|||j):=by
 have a:=ap 5 5 h d
  (fun i hi=>by have:=c.1 i hi;have:=b.1 i hi;omega) c.2 b.2
 have l:=jf 5 4 9 5 (h+d) 0x6318c6 0x1084210 0xf7bdef 0x94a529 (by omega) (by decide)
  a.1 (by decide) (by decide) (by decide) (by decide)
  (fun i hi=>vL ⟨i,hi⟩) (fun i hi=>nx ⟨i,hi⟩)
  (fun i hi=>sN ⟨i,hi⟩) (fun i hi=>tD ⟨i,hi⟩)
  (fun i hi=>by rw[a.2 i hi];have:=c.1 i hi;have:=b.1 i hi;omega)
 unfold fF
 refine ⟨⟨fun i hi=>by rw[l.1 i hi];exact mL _ _,l.2⟩,fun e=>?_⟩
 rw[l.1 e.val e.isLt,a.2 e.val e.isLt];have h1:=n e;have h2:=m e;have ho:=fm k j e;have h9:=vb (k|||j) e;omega
lemma gf {j h d c:Nat} (b:fv d) (a:fv c)
  (m:e7 d j) (l:e7 c h) :
  fv (eI d c)/\e7 (eI d c) (j|||h):=by
 have k:=de 6 5 5 d c 0x20820820 0x1f7df7df (by omega) b.2 a.2 (by decide) (by decide)
  (fun i hi=>nw ⟨i,hi⟩) (fun i hi=>zo ⟨i,hi⟩)
  (fun i hi=>lO (b.1 i hi) (by decide)) (fun i hi=>lO (a.1 i hi) (by decide))
 unfold eI
 refine ⟨⟨fun i hi=>by rw[k.1 i hi];exact xL (b.1 i hi) (a.1 i hi),k.2.2.1⟩,fun s=>?_⟩
 rw[k.1 s.val s.isLt];have h1:=m s;have h2:=l s;have ho:=fl j h s;omega
lemma hY {j h c b:Nat} (a:eV c) (d:eV b)
  (m:dI c j) (l:dI b h) :
  eV (eo c b)/\dI (eo c b) (j&&&h):=by
 have k:=de 5 4 5 c b 0x1084210 0xf7bdef (by omega) a.2 d.2 (by decide) (by decide)
  (fun i hi=>nx ⟨i,hi⟩) (fun i hi=>sN ⟨i,hi⟩)
  (fun i hi=>lO (a.1 i hi) (by decide)) (fun i hi=>lO (d.1 i hi) (by decide))
 unfold eo
 refine ⟨⟨fun i hi=>by rw[k.2.1 i hi];exact lT (mL _ _) (a.1 i hi),k.2.2.2⟩,fun e=>?_⟩
 rw[k.2.1 e.val e.isLt];have h1:=m e;have h2:=l e;have ha:=et j h e;omega
lemma fG {k j h d:Nat} (c:fv h) (b:fv d)
  (n:e7 h k) (m:e7 d j) :
  fv (dF h d)/\e7 (dF h d) (k&&&j):=by
 have a:=ap 6 5 h d
  (fun i hi=>by have:=c.1 i hi;have:=b.1 i hi;omega) c.2 b.2
 have l:=jB 6 5 27 5 (h+d) 0x5145145 0x20820820 (by omega) (by decide)
  a.1 (by decide) (by decide) (fun i hi=>tE ⟨i,hi⟩) (fun i hi=>nw ⟨i,hi⟩)
  (fun i hi=>by rw[a.2 i hi];have:=c.1 i hi;have:=b.1 i hi;omega)
 unfold dF
 refine ⟨⟨fun i hi=>by rw[l.1 i hi,a.2 i hi];have:=c.1 i hi;have:=b.1 i hi;omega,l.2⟩,fun s=>?_⟩
 rw[l.1 s.val s.isLt,a.2 s.val s.isLt];have h1:=n s;have h2:=m s;have ha:=kM k j s;omega
def gP (pa qa:Nat):Nat:=bD (fF pa qa)
def iW (pb qb:Nat):Nat:=bG (eI pb qb)
def i9 (pa qa:Nat):Nat:=bD (eo pa qa)
def i8 (pb qb:Nat):Nat:=bG (dF pb qb)
lemma eb {j i b a:Nat} (d:eV b) (c:eV a)
  (l:dI b j) (k:dI a i):bo (j|||i)<=gP b a:=
 let h:=iI d c l k;cS h.1 h.2
lemma gm {j i b a:Nat} (d:fv b) (c:fv a)
  (l:e7 b j) (k:e7 a i):iW b a<=bv (j|||i):=
 let h:=gf d c l k;cR h.1 h.2
lemma fM {j i b a:Nat} (d:eV b) (c:eV a)
  (l:dI b j) (k:dI a i):bo (j&&&i)<=i9 b a:=
 let h:=hY d c l k;cS h.1 h.2
lemma fL {j i b a:Nat} (d:fv b) (c:fv a)
  (l:e7 b j) (k:e7 a i):i8 b a<=bv (j&&&i):=
 let h:=fG d c l k;cR h.1 h.2
lemma kc {k j i h c d a b:Nat}
  (C:eV i) (y:eV h) (n:cq c) (r:cq d) (l:cq a) (m:cq b)
  (K:dI i k) (F:dI h j)
  (w:bg c (cf k)) (x:bg d (cg k))
  (u:bg a (cf j)) (v:bg b (cg j)) :
  eV (e9 i h c d a b)/\dI (e9 i h c d a b) (k|||j):=by
 have t:∀ e:Fin 5,bk (k|||j) e<=av (gA i e.val+gA h e.val) (eA c d a b e.val)/\
   av (gA i e.val+gA h e.val) (eA c d a b e.val)<=9:=fun e=>by
  rw[m8 i e.val C e.isLt,m8 h e.val y e.isLt];have h1:=K e;have h2:=F e;have ho:=fm k j e;have h3:=xp (e:=e) n r l m w x u v;simp only[aG];omega
 unfold e9;dsimp only;have h0:=t 0;have h1:=t 1;have h2:=t 2;have h3:=t 3;have h4:=t 4
 have z:lor (lor (lor (lor
   (av (gA i 0+gA h 0) (eA c d a b 0))
   (shiftLeft (av (gA i 1+gA h 1) (eA c d a b 1)) 5))
   (shiftLeft (av (gA i 2+gA h 2) (eA c d a b 2)) 10))
   (shiftLeft (av (gA i 3+gA h 3) (eA c d a b 3)) 15))
   (shiftLeft (av (gA i 4+gA h 4) (eA c d a b 4)) 20) =
   bM 5 _ _ _ _ _:=
  (dv 5 _ _ _ _ _ (lO h0.2 (by decide)) (lO h1.2 (by decide))
   (lO h2.2 (by decide)) (lO h3.2 (by decide))).symm
 change eV (lor (lor (lor (lor
   (av (gA i 0+gA h 0) (eA c d a b 0))
   (shiftLeft (av (gA i 1+gA h 1) (eA c d a b 1)) 5))
   (shiftLeft (av (gA i 2+gA h 2) (eA c d a b 2)) 10))
   (shiftLeft (av (gA i 3+gA h 3) (eA c d a b 3)) 15))
   (shiftLeft (av (gA i 4+gA h 4) (eA c d a b 4)) 20))/\
  dI (lor (lor (lor (lor
   (av (gA i 0+gA h 0) (eA c d a b 0))
   (shiftLeft (av (gA i 1+gA h 1) (eA c d a b 1)) 5))
   (shiftLeft (av (gA i 2+gA h 2) (eA c d a b 2)) 10))
   (shiftLeft (av (gA i 3+gA h 3) (eA c d a b 3)) 15))
   (shiftLeft (av (gA i 4+gA h 4) (eA c d a b 4)) 20)) _
 rw[z];exact iE (k|||j) _ _ _ _ _ h0 h1 h2 h3 h4
lemma pO {j i h d bf be bd c b a:Nat}
   (w:fv h) (r:fv d)
   (v:az bf) (u:az be) (t:az bd)
   (n:az c) (m:az b) (l:az a)
   (M:e7 h j) (C:e7 d i)
   (L:ag bf (fun s=>ak j s 0)) (K:ag be (fun s=>ak j s 1)) (F:ag bd (fun s=>ak j s 2))
   (z:ag c (fun s=>ak i s 0)) (y:ag b (fun s=>ak i s 1)) (x:ag a (fun s=>ak i s 2)) :
   fv (gl h d bf be bd c b a)/\e7 (gl h d bf be bd c b a) (j|||i):=by
 unfold gl;cases nE (lor (lor bf be) (lor bd (lor c (lor b a)))) 0
 swap
 . rw[bT];exact gf w r M C
 rw[bC]
 have k:∀ s:Fin 5,aa (aa (gB h s.val) (gB d s.val)) (ff bf be bd c b a s.val)<=cw (j|||i) s:=fun s=>by
   rw[o1 h s.val w s.isLt,o1 d s.val r s.isLt];have h1:=M s;have h2:=C s;have ho:=fl j i s;have h3:=xo (s:=s) v u t n m l L K F z y x;simp only[aP];omega
 have h0:=k 0;have h1:=k 1;have h2:=k 2;have h3:=k 3;have h4:=k 4;have W:=bV (j|||i) 0;have T:=bV (j|||i) 1;have Q:=bV (j|||i) 2;have P:=bV (j|||i) 3
 have N:lor (lor (lor (lor
     (aa (aa (gB h 0) (gB d 0)) (ff bf be bd c b a 0))
     (shiftLeft (aa (aa (gB h 1) (gB d 1)) (ff bf be bd c b a 1)) 6))
     (shiftLeft (aa (aa (gB h 2) (gB d 2)) (ff bf be bd c b a 2)) 12))
     (shiftLeft (aa (aa (gB h 3) (gB d 3)) (ff bf be bd c b a 3)) 18))
     (shiftLeft (aa (aa (gB h 4) (gB d 4)) (ff bf be bd c b a 4)) 24) =
     bM 6 _ _ _ _ _:=
   (dv 6 _ _ _ _ _ (lO (lT h0 W) (by decide)) (lO (lT h1 T) (by decide))
     (lO (lT h2 Q) (by decide)) (lO (lT h3 P) (by decide))).symm
 change fv (lor (lor (lor (lor
     (aa (aa (gB h 0) (gB d 0)) (ff bf be bd c b a 0))
     (shiftLeft (aa (aa (gB h 1) (gB d 1)) (ff bf be bd c b a 1)) 6))
     (shiftLeft (aa (aa (gB h 2) (gB d 2)) (ff bf be bd c b a 2)) 12))
     (shiftLeft (aa (aa (gB h 3) (gB d 3)) (ff bf be bd c b a 3)) 18))
     (shiftLeft (aa (aa (gB h 4) (gB d 4)) (ff bf be bd c b a 4)) 24))/\
   e7 (lor (lor (lor (lor
     (aa (aa (gB h 0) (gB d 0)) (ff bf be bd c b a 0))
     (shiftLeft (aa (aa (gB h 1) (gB d 1)) (ff bf be bd c b a 1)) 6))
     (shiftLeft (aa (aa (gB h 2) (gB d 2)) (ff bf be bd c b a 2)) 12))
     (shiftLeft (aa (aa (gB h 3) (gB d 3)) (ff bf be bd c b a 3)) 18))
     (shiftLeft (aa (aa (gB h 4) (gB d 4)) (ff bf be bd c b a 4)) 24)) _
 rw[N];exact iD (j|||i) _ _ _ _ _ h0 h1 h2 h3 h4
lemma jA {k j i h c d a b:Nat}
  (C:eV i) (y:eV h) (n:cq c) (r:cq d) (l:cq a) (m:cq b)
  (K:dI i k) (F:dI h j)
  (w:bg c (cf k)) (x:bg d (cg k))
  (u:bg a (cf j)) (v:bg b (cg j)) :
  eV (e4 i h c d a b)/\dI (e4 i h c d a b) (k&&&j):=by
 have t:∀ e:Fin 5,bk (k&&&j) e<=av (av (gA i e.val) (gA h e.val)) (d6 c d a b e.val)/\
   av (av (gA i e.val) (gA h e.val)) (d6 c d a b e.val)<=9:=fun e=>by
  rw[m8 i e.val C e.isLt,m8 h e.val y e.isLt];have h1:=K e;have h2:=F e;have ha:=et k j e;have h3:=w2 (e:=e) n r l m w x u v;simp only[aG];omega
 unfold e4;dsimp only;have h0:=t 0;have h1:=t 1;have h2:=t 2;have h3:=t 3;have h4:=t 4
 have z:lor (lor (lor (lor
   (av (av (gA i 0) (gA h 0)) (d6 c d a b 0))
   (shiftLeft (av (av (gA i 1) (gA h 1)) (d6 c d a b 1)) 5))
   (shiftLeft (av (av (gA i 2) (gA h 2)) (d6 c d a b 2)) 10))
   (shiftLeft (av (av (gA i 3) (gA h 3)) (d6 c d a b 3)) 15))
   (shiftLeft (av (av (gA i 4) (gA h 4)) (d6 c d a b 4)) 20) =
   bM 5 _ _ _ _ _:=
  (dv 5 _ _ _ _ _ (lO h0.2 (by decide)) (lO h1.2 (by decide))
   (lO h2.2 (by decide)) (lO h3.2 (by decide))).symm
 change eV (lor (lor (lor (lor
   (av (av (gA i 0) (gA h 0)) (d6 c d a b 0))
   (shiftLeft (av (av (gA i 1) (gA h 1)) (d6 c d a b 1)) 5))
   (shiftLeft (av (av (gA i 2) (gA h 2)) (d6 c d a b 2)) 10))
   (shiftLeft (av (av (gA i 3) (gA h 3)) (d6 c d a b 3)) 15))
   (shiftLeft (av (av (gA i 4) (gA h 4)) (d6 c d a b 4)) 20))/\
  dI (lor (lor (lor (lor
   (av (av (gA i 0) (gA h 0)) (d6 c d a b 0))
   (shiftLeft (av (av (gA i 1) (gA h 1)) (d6 c d a b 1)) 5))
   (shiftLeft (av (av (gA i 2) (gA h 2)) (d6 c d a b 2)) 10))
   (shiftLeft (av (av (gA i 3) (gA h 3)) (d6 c d a b 3)) 15))
   (shiftLeft (av (av (gA i 4) (gA h 4)) (d6 c d a b 4)) 20)) _
 rw[z];exact iE (k&&&j) _ _ _ _ _ h0 h1 h2 h3 h4
lemma oQ {j i h d bf be bd c b a:Nat}
   (w:fv h) (r:fv d)
   (v:az bf) (u:az be) (t:az bd)
   (n:az c) (m:az b) (l:az a)
   (M:e7 h j) (C:e7 d i)
   (L:ag bf (fun s=>ak j s 0)) (K:ag be (fun s=>ak j s 1)) (F:ag bd (fun s=>ak j s 2))
   (z:ag c (fun s=>ak i s 0)) (y:ag b (fun s=>ak i s 1)) (x:ag a (fun s=>ak i s 2)) :
   fv (dZ h d bf be bd c b a)/\e7 (dZ h d bf be bd c b a) (j&&&i):=by
 unfold dZ;cases (nE (lor (lor bf be) bd) 0||nE (lor (lor c b) a) 0)
 swap
 . rw[bT];exact fG w r M C
 rw[bC]
 have k:∀ s:Fin 5,aa (gB h s.val+gB d s.val - 27) (dh bf be bd c b a s.val)<=cw (j&&&i) s:=fun s=>by
   rw[o1 h s.val w s.isLt,o1 d s.val r s.isLt];have h1:=M s;have h2:=C s;have ha:=kM j i s;have h3:=w1 (s:=s) v u t n m l L K F z y x;simp only[aP];omega
 have h0:=k 0;have h1:=k 1;have h2:=k 2;have h3:=k 3;have h4:=k 4;have W:=bV (j&&&i) 0;have T:=bV (j&&&i) 1;have Q:=bV (j&&&i) 2;have P:=bV (j&&&i) 3
 have N:lor (lor (lor (lor
     (aa (gB h 0+gB d 0 - 27) (dh bf be bd c b a 0))
     (shiftLeft (aa (gB h 1+gB d 1 - 27) (dh bf be bd c b a 1)) 6))
     (shiftLeft (aa (gB h 2+gB d 2 - 27) (dh bf be bd c b a 2)) 12))
     (shiftLeft (aa (gB h 3+gB d 3 - 27) (dh bf be bd c b a 3)) 18))
     (shiftLeft (aa (gB h 4+gB d 4 - 27) (dh bf be bd c b a 4)) 24) =
     bM 6 _ _ _ _ _:=
   (dv 6 _ _ _ _ _ (lO (lT h0 W) (by decide)) (lO (lT h1 T) (by decide))
     (lO (lT h2 Q) (by decide)) (lO (lT h3 P) (by decide))).symm
 change fv (lor (lor (lor (lor
     (aa (gB h 0+gB d 0 - 27) (dh bf be bd c b a 0))
     (shiftLeft (aa (gB h 1+gB d 1 - 27) (dh bf be bd c b a 1)) 6))
     (shiftLeft (aa (gB h 2+gB d 2 - 27) (dh bf be bd c b a 2)) 12))
     (shiftLeft (aa (gB h 3+gB d 3 - 27) (dh bf be bd c b a 3)) 18))
     (shiftLeft (aa (gB h 4+gB d 4 - 27) (dh bf be bd c b a 4)) 24))/\
   e7 (lor (lor (lor (lor
     (aa (gB h 0+gB d 0 - 27) (dh bf be bd c b a 0))
     (shiftLeft (aa (gB h 1+gB d 1 - 27) (dh bf be bd c b a 1)) 6))
     (shiftLeft (aa (gB h 2+gB d 2 - 27) (dh bf be bd c b a 2)) 12))
     (shiftLeft (aa (gB h 3+gB d 3 - 27) (dh bf be bd c b a 3)) 18))
     (shiftLeft (aa (gB h 4+gB d 4 - 27) (dh bf be bd c b a 4)) 24)) _
 rw[N];exact iD (j&&&i) _ _ _ _ _ h0 h1 h2 h3 h4
lemma jj {b a i d:Nat} (k:cq i) (j:cq d)
  (n:bg i (cf b)) (m:bg d (cf a)) :
  cq (ez i d)/\bg (ez i d) (cf (b|||a)):=by
 have h:=gd (ao b) (ao a) i d k j n m;refine ⟨h.1,fun e=>?_⟩
 have l:ao (b|||a) e=fun r c=>ao b e r c||ao a e r c:=by
  funext r c;exact hX b a e r c
 have h':=h.2 e;unfold cf am;rw[l];exact h'
lemma jk {b a i d:Nat} (k:cq i) (j:cq d)
  (n:bg i (cg b)) (m:bg d (cg a)) :
  cq (ez i d)/\bg (ez i d) (cg (b|||a)):=by
 have h:=gd (fun e r c=>ao b e c r) (fun e r c=>ao a e c r) i d k j n m;refine ⟨h.1,fun e=>?_⟩
 have l:ao (b|||a) e=fun r c=>ao b e r c||ao a e r c:=by
  funext r c;exact hX b a e r c
 have h':=h.2 e;unfold cg aR;rw[l];exact h'
lemma iK {b a j k d i:Nat} (n:cq j) (t:cq k) (l:cq d) (m:cq i)
  (w:bg j (cf b)) (x:bg k (cg b)) (u:bg d (cf a)) (v:bg i (cg a)) :
  cq (dH j k d i)/\bg (dH j k d i) (cf (b&&&a)):=by
 have h:=kq (ao b) (ao a) j k d i n t l m w x u v;refine ⟨h.1,fun e=>?_⟩
 have y:ao (b&&&a) e=fun r c=>ao b e r c&&ao a e r c:=by
  funext r c;exact fk b a e r c
 have h':=h.2 e;unfold cf am;rw[y];exact h'
lemma iL {b a j k d i:Nat} (n:cq j) (t:cq k) (l:cq d) (m:cq i)
  (w:bg j (cf b)) (x:bg k (cg b)) (u:bg d (cf a)) (v:bg i (cg a)) :
  cq (dH k j i d)/\bg (dH k j i d) (cg (b&&&a)):=by
 have h:=kq (fun e r c=>ao b e c r) (fun e r c=>ao a e c r) k j i d t n m l x w v u;refine ⟨h.1,fun e=>?_⟩
 have y:ao (b&&&a) e=fun r c=>ao b e r c&&ao a e r c:=by
  funext r c;exact fk b a e r c
 have h':=h.2 e;unfold cg aR;rw[y];exact h'
lemma sL {i d k j:Nat} (m:az k) (l:az j)
  (t:ag k (fun s=>ak i s 0)) (r:ag j (fun s=>ak d s 0)) :
  az (em k j)/\ag (em k j) (fun s=>ak (i|||d) s 0):=by
 have h:=fB (B i) (B d) k j m l t r;refine ⟨h.1,fun s=>?_⟩
 have n:B (i|||d) s=fun a b c=>B i s a b c||B d s a b c:=by
  funext a b c;exact gH i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[n];exact h'
lemma sK {i d k j:Nat} (m:az k) (l:az j)
  (t:ag k (fun s=>ak i s 1)) (r:ag j (fun s=>ak d s 1)) :
  az (em k j)/\ag (em k j) (fun s=>ak (i|||d) s 1):=by
 have h:=fB (fun s b a c=>B i s a b c) (fun s b a c=>B d s a b c) k j m l t r;refine ⟨h.1,fun s=>?_⟩
 have n:B (i|||d) s=fun a b c=>B i s a b c||B d s a b c:=by
  funext a b c;exact gH i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[n];exact h'
lemma sJ {i d k j:Nat} (m:az k) (l:az j)
  (t:ag k (fun s=>ak i s 2)) (r:ag j (fun s=>ak d s 2)) :
  az (em k j)/\ag (em k j) (fun s=>ak (i|||d) s 2):=by
 have h:=fB (fun s c a b=>B i s a b c) (fun s c a b=>B d s a b c) k j m l t r;refine ⟨h.1,fun s=>?_⟩
 have n:B (i|||d) s=fun a b c=>B i s a b c||B d s a b c:=by
  funext a b c;exact gH i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[n];exact h'
lemma nt {i d r n m l k j:Nat}
  (y:az r) (x:az n) (w:az m) (v:az l) (u:az k) (t:az j)
  (N:ag r (fun s=>ak i s 0)) (M:ag n (fun s=>ak i s 1)) (L:ag m (fun s=>ak i s 2))
  (K:ag l (fun s=>ak d s 0)) (F:ag k (fun s=>ak d s 1)) (C:ag j (fun s=>ak d s 2)) :
  az (ci r n m l k j)/\ag (ci r n m l k j) (fun s=>ak (i|||d) s 0):=by
 have h:=fe (B i) (B d) r n m l k j y x w v u t N M L K F C;refine ⟨h.1,fun s=>?_⟩
 have z:B (i|||d) s=fun a b c=>B i s a b c||B d s a b c:=by
  funext a b c;exact gH i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[z];exact h'
lemma ns {i d v u n t r m:Nat}
  (F:az v) (C:az u) (z:az n) (y:az t) (x:az r) (w:az m)
  (Q:ag v (fun s=>ak i s 0)) (N:ag u (fun s=>ak i s 1)) (l:ag n (fun s=>ak i s 2))
  (M:ag t (fun s=>ak d s 0)) (L:ag r (fun s=>ak d s 1)) (j:ag m (fun s=>ak d s 2)) :
  az (ci u v n r t m)/\ag (ci u v n r t m) (fun s=>ak (i|||d) s 1):=by
 have h2:∀ (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3),aK (fun b a c=>P a b c) k=aK P k:=fun P k=>by
  unfold aK A aq;dsimp only;omega
 have dp2':ag n (fun s=>D (aK (fun b a c=>B i s a b c) 0)
   (aK (fun b a c=>B i s a b c) 1)
   (aK (fun b a c=>B i s a b c) 2)):=fun s=>by
  dsimp only;rw[h2 (B i s) 0,h2 (B i s) 1,h2 (B i s) 2];exact l s
 have dq2':ag m (fun s=>D (aK (fun b a c=>B d s a b c) 0)
   (aK (fun b a c=>B d s a b c) 1)
   (aK (fun b a c=>B d s a b c) 2)):=fun s=>by
  dsimp only;rw[h2 (B d s) 0,h2 (B d s) 1,h2 (B d s) 2];exact j s
 have h:=fe (fun s b a c=>B i s a b c) (fun s b a c=>B d s a b c)
  u v n r t m C F z x y w N Q dp2' L M dq2'
 refine ⟨h.1,fun s=>?_⟩
 have K:B (i|||d) s=fun a b c=>B i s a b c||B d s a b c:=by
  funext a b c;exact gH i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[K];exact h'
lemma nr {i d v u x t r w:Nat}
  (L:az v) (K:az u) (F:az x) (C:az t) (z:az r) (y:az w)
  (n:ag v (fun s=>ak i s 0)) (m:ag u (fun s=>ak i s 1)) (Q:ag x (fun s=>ak i s 2))
  (l:ag t (fun s=>ak d s 0)) (j:ag r (fun s=>ak d s 1)) (N:ag w (fun s=>ak d s 2)) :
  az (ci x v u w t r)/\ag (ci x v u w t r) (fun s=>ak (i|||d) s 2):=by
 have h1:∀ (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3),Z (fun c a b=>P a b c) k=A P k:=dd
 have h2:∀ (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3),aK (fun c a b=>P a b c) k=Z P k:=fun P k=>by
  unfold aK Z A aq;dsimp only;omega
 have dp0':ag v (fun s=>D (Z (fun c a b=>B i s a b c) 0)
   (Z (fun c a b=>B i s a b c) 1)
   (Z (fun c a b=>B i s a b c) 2)):=fun s=>by
  dsimp only;rw[h1,h1,h1];exact n s
 have dp1':ag u (fun s=>D (aK (fun c a b=>B i s a b c) 0)
   (aK (fun c a b=>B i s a b c) 1)
   (aK (fun c a b=>B i s a b c) 2)):=fun s=>by
  dsimp only;rw[h2,h2,h2];exact m s
 have dq0':ag t (fun s=>D (Z (fun c a b=>B d s a b c) 0)
   (Z (fun c a b=>B d s a b c) 1)
   (Z (fun c a b=>B d s a b c) 2)):=fun s=>by
  dsimp only;rw[h1,h1,h1];exact l s
 have dq1':ag r (fun s=>D (aK (fun c a b=>B d s a b c) 0)
   (aK (fun c a b=>B d s a b c) 1)
   (aK (fun c a b=>B d s a b c) 2)):=fun s=>by
  dsimp only;rw[h2,h2,h2];exact j s
 have h:=fe (fun s c a b=>B i s a b c) (fun s c a b=>B d s a b c)
  x v u w t r F L K y C z Q dp0' dp1' N dq0' dq1'
 refine ⟨h.1,fun s=>?_⟩
 have M:B (i|||d) s=fun a b c=>B i s a b c||B d s a b c:=by
  funext a b c;exact gH i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[M];exact h'
lemma t2 {i d r n m l k j:Nat}
  (y:az r) (x:az n) (w:az m) (v:az l) (u:az k) (t:az j)
  (N:ag r (fun s=>ak i s 0)) (M:ag n (fun s=>ak i s 1)) (L:ag m (fun s=>ak i s 2))
  (K:ag l (fun s=>ak d s 0)) (F:ag k (fun s=>ak d s 1)) (C:ag j (fun s=>ak d s 2)) :
  az (eN r n m l k j)/\ag (eN r n m l k j) (fun s=>ak (i&&&d) s 0):=by
 have h:=i4 (B i) (B d) r n m l k j y x w v u t N M L K F C;refine ⟨h.1,fun s=>?_⟩
 have z:B (i&&&d) s=fun a b c=>B i s a b c&&B d s a b c:=by
  funext a b c;exact dG i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[z];exact h'
lemma sZ {i d v u n t r m:Nat}
  (F:az v) (C:az u) (z:az n) (y:az t) (x:az r) (w:az m)
  (Q:ag v (fun s=>ak i s 0)) (N:ag u (fun s=>ak i s 1)) (l:ag n (fun s=>ak i s 2))
  (M:ag t (fun s=>ak d s 0)) (L:ag r (fun s=>ak d s 1)) (j:ag m (fun s=>ak d s 2)) :
  az (eN u v n r t m)/\ag (eN u v n r t m) (fun s=>ak (i&&&d) s 1):=by
 have h2:∀ (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3),aK (fun b a c=>P a b c) k=aK P k:=fun P k=>by
  unfold aK A aq;dsimp only;omega
 have dp2':ag n (fun s=>D (aK (fun b a c=>B i s a b c) 0)
   (aK (fun b a c=>B i s a b c) 1)
   (aK (fun b a c=>B i s a b c) 2)):=fun s=>by
  dsimp only;rw[h2 (B i s) 0,h2 (B i s) 1,h2 (B i s) 2];exact l s
 have dq2':ag m (fun s=>D (aK (fun b a c=>B d s a b c) 0)
   (aK (fun b a c=>B d s a b c) 1)
   (aK (fun b a c=>B d s a b c) 2)):=fun s=>by
  dsimp only;rw[h2 (B d s) 0,h2 (B d s) 1,h2 (B d s) 2];exact j s
 have h:=i4 (fun s b a c=>B i s a b c) (fun s b a c=>B d s a b c)
  u v n r t m C F z x y w N Q dp2' L M dq2'
 refine ⟨h.1,fun s=>?_⟩
 have K:B (i&&&d) s=fun a b c=>B i s a b c&&B d s a b c:=by
  funext a b c;exact dG i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[K];exact h'
lemma sY {i d v u x t r w:Nat}
  (L:az v) (K:az u) (F:az x) (C:az t) (z:az r) (y:az w)
  (n:ag v (fun s=>ak i s 0)) (m:ag u (fun s=>ak i s 1)) (Q:ag x (fun s=>ak i s 2))
  (l:ag t (fun s=>ak d s 0)) (j:ag r (fun s=>ak d s 1)) (N:ag w (fun s=>ak d s 2)) :
  az (eN x v u w t r)/\ag (eN x v u w t r) (fun s=>ak (i&&&d) s 2):=by
 have h1:∀ (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3),Z (fun c a b=>P a b c) k=A P k:=dd
 have h2:∀ (P:Fin 3->Fin 3->Fin 3->Bool) (k:Fin 3),aK (fun c a b=>P a b c) k=Z P k:=fun P k=>by
  unfold aK Z A aq;dsimp only;omega
 have dp0':ag v (fun s=>D (Z (fun c a b=>B i s a b c) 0)
   (Z (fun c a b=>B i s a b c) 1)
   (Z (fun c a b=>B i s a b c) 2)):=fun s=>by
  dsimp only;rw[h1,h1,h1];exact n s
 have dp1':ag u (fun s=>D (aK (fun c a b=>B i s a b c) 0)
   (aK (fun c a b=>B i s a b c) 1)
   (aK (fun c a b=>B i s a b c) 2)):=fun s=>by
  dsimp only;rw[h2,h2,h2];exact m s
 have dq0':ag t (fun s=>D (Z (fun c a b=>B d s a b c) 0)
   (Z (fun c a b=>B d s a b c) 1)
   (Z (fun c a b=>B d s a b c) 2)):=fun s=>by
  dsimp only;rw[h1,h1,h1];exact l s
 have dq1':ag r (fun s=>D (aK (fun c a b=>B d s a b c) 0)
   (aK (fun c a b=>B d s a b c) 1)
   (aK (fun c a b=>B d s a b c) 2)):=fun s=>by
  dsimp only;rw[h2,h2,h2];exact j s
 have h:=i4 (fun s c a b=>B i s a b c) (fun s c a b=>B d s a b c)
  x v u w t r F L K y C z Q dp0' dp1' N dq0' dq1'
 refine ⟨h.1,fun s=>?_⟩
 have M:B (i&&&d) s=fun a b c=>B i s a b c&&B d s a b c:=by
  funext a b c;exact dG i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[M];exact h'
lemma pw {i d k j:Nat} (m:az k) (l:az j)
  (t:ag k (fun s=>ak i s 0)) (r:ag j (fun s=>ak d s 0)) :
  az (cp k j)/\ag (cp k j) (fun s=>ak (i&&&d) s 0):=by
 have h:=dK (B i) (B d) k j m l t r;refine ⟨h.1,fun s=>?_⟩
 have n:B (i&&&d) s=fun a b c=>B i s a b c&&B d s a b c:=by
  funext a b c;exact dG i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[n];exact h'
lemma pv {i d k j:Nat} (m:az k) (l:az j)
  (t:ag k (fun s=>ak i s 1)) (r:ag j (fun s=>ak d s 1)) :
  az (cp k j)/\ag (cp k j) (fun s=>ak (i&&&d) s 1):=by
 have h:=dK (fun s b a c=>B i s a b c) (fun s b a c=>B d s a b c) k j m l t r;refine ⟨h.1,fun s=>?_⟩
 have n:B (i&&&d) s=fun a b c=>B i s a b c&&B d s a b c:=by
  funext a b c;exact dG i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[n];exact h'
lemma pu {i d k j:Nat} (m:az k) (l:az j)
  (t:ag k (fun s=>ak i s 2)) (r:ag j (fun s=>ak d s 2)) :
  az (cp k j)/\ag (cp k j) (fun s=>ak (i&&&d) s 2):=by
 have h:=dK (fun s c a b=>B i s a b c) (fun s c a b=>B d s a b c) k j m l t r;refine ⟨h.1,fun s=>?_⟩
 have n:B (i&&&d) s=fun a b c=>B i s a b c&&B d s a b c:=by
  funext a b c;exact dG i d s a b c
 have h':=h.2 s;unfold ak S;dsimp only;rw[n];exact h'
def o2 (p q:RS):RS:=
 let (_,_,pa,pb,par,pac,bf,be,bd):=p;let (_,_,qa,qb,qar,qac,qb0,qb1,qb2):=q;let b:=fF pa qa;let a:=eI pb qb
 (bD b,bG a,b,a,ez par qar,ez pac qac,em bf qb0,em be qb1,em bd qb2)
def m9 (p q:RS):RS:=
 let (_,_,pa,pb,par,pac,bf,be,bd):=p;let (_,_,qa,qb,qar,qac,qb0,qb1,qb2):=q;let b:=eo pa qa;let a:=dF pb qb
 (bD b,bG a,b,a,dH par pac qar qac,dH pac par qac qar,
  cp bf qb0,cp be qb1,cp bd qb2)
def lE (p q:RS):RS:=
 let (_,_,pa,pb,par,pac,bf,be,bd):=p;let (_,_,qa,qb,qar,qac,qb0,qb1,qb2):=q;let b:=e9 pa qa par pac qar qac;let a:=gl pb qb bf be bd qb0 qb1 qb2
 (bD b,bG a,b,a,ez par qar,ez pac qac,
  ci bf be bd qb0 qb1 qb2,ci be bf bd qb1 qb0 qb2,ci bd bf be qb2 qb0 qb1)
def kx (p q:RS):RS:=
 let (_,_,pa,pb,par,pac,bf,be,bd):=p;let (_,_,qa,qb,qar,qac,qb0,qb1,qb2):=q;let b:=e4 pa qa par pac qar qac;let a:=dZ pb qb bf be bd qb0 qb1 qb2
 (bD b,bG a,b,a,dH par pac qar qac,dH pac par qac qar,
  eN bf be bd qb0 qb1 qb2,eN be bf bd qb1 qb0 qb2,eN bd bf be qb2 qb0 qb1)
def sG (p q:AS):AS:=
 let (_,pa,par,pac):=p;let (_,qa,qar,qac):=q;let a:=e9 pa qa par pac qar qac
 (bD a,a,ez par qar,ez pac qac)
def pU (p q:AS):AS:=
 let (_,pa,par,pac):=p;let (_,qa,qar,qac):=q;let a:=e4 pa qa par pac qar qac
 (bD a,a,dH par pac qar qac,dH pac par qac qar)
lemma km {p q:RS} {k i j h:Nat}
  (b:cu p) (a:cu q) (d:aW p k i) (c:aW q j h) :
  cu (o2 p q)/\aW (o2 p q) (k|||j) (i|||h):=by
 have v:=iI b.1 a.1 d.1 c.1;have u:=gf b.2.1 a.2.1 d.2.1 c.2.1;have r:=jj b.2.2.1 a.2.2.1 d.2.2.1 c.2.2.1;have t:=jk b.2.2.2.1 a.2.2.2.1 d.2.2.2.1 c.2.2.2.1;have n:=sL b.2.2.2.2.1 a.2.2.2.2.1 d.2.2.2.2.1 c.2.2.2.2.1;have m:=sK b.2.2.2.2.2.1 a.2.2.2.2.2.1 d.2.2.2.2.2.1 c.2.2.2.2.2.1;have l:=sJ b.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.2.2
 exact ⟨⟨v.1,u.1,r.1,t.1,n.1,m.1,l.1,rfl,rfl⟩,
   ⟨v.2,u.2,r.2,t.2,n.2,m.2,l.2⟩⟩
lemma jH {p q:RS} {k i j h:Nat}
  (b:cu p) (a:cu q) (d:aW p k i) (c:aW q j h) :
  cu (m9 p q)/\aW (m9 p q) (k&&&j) (i&&&h):=by
 have v:=hY b.1 a.1 d.1 c.1;have u:=fG b.2.1 a.2.1 d.2.1 c.2.1;have r:=iK b.2.2.1 b.2.2.2.1 a.2.2.1 a.2.2.2.1 d.2.2.1 d.2.2.2.1 c.2.2.1 c.2.2.2.1;have t:=iL b.2.2.1 b.2.2.2.1 a.2.2.1 a.2.2.2.1 d.2.2.1 d.2.2.2.1 c.2.2.1 c.2.2.2.1;have n:=pw b.2.2.2.2.1 a.2.2.2.2.1 d.2.2.2.2.1 c.2.2.2.2.1;have m:=pv b.2.2.2.2.2.1 a.2.2.2.2.2.1 d.2.2.2.2.2.1 c.2.2.2.2.2.1;have l:=pu b.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.2.2
 exact ⟨⟨v.1,u.1,r.1,t.1,n.1,m.1,l.1,rfl,rfl⟩,
   ⟨v.2,u.2,r.2,t.2,n.2,m.2,l.2⟩⟩
lemma gN {p q:RS} {k i j h:Nat}
  (b:cu p) (a:cu q) (d:aW p k i) (c:aW q j h) :
  cu (lE p q)/\aW (lE p q) (k|||j) (i|||h):=by
 have v:=kc b.1 a.1 b.2.2.1 b.2.2.2.1 a.2.2.1 a.2.2.2.1 d.1 c.1 d.2.2.1 d.2.2.2.1 c.2.2.1 c.2.2.2.1
 have u:=pO b.2.1 a.2.1 b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1
  d.2.1 c.2.1 d.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2
 have r:=jj b.2.2.1 a.2.2.1 d.2.2.1 c.2.2.1;have t:=jk b.2.2.2.1 a.2.2.2.1 d.2.2.2.1 c.2.2.2.1
 have n:=nt b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1
  d.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2
 have m:=ns b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1
  d.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2
 have l:=nr b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1
  d.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2
 exact ⟨⟨v.1,u.1,r.1,t.1,n.1,m.1,l.1,rfl,rfl⟩,
   ⟨v.2,u.2,r.2,t.2,n.2,m.2,l.2⟩⟩
lemma ea {p q:RS} {k i j h:Nat}
  (b:cu p) (a:cu q) (d:aW p k i) (c:aW q j h) :
  cu (kx p q)/\aW (kx p q) (k&&&j) (i&&&h):=by
 have v:=jA b.1 a.1 b.2.2.1 b.2.2.2.1 a.2.2.1 a.2.2.2.1 d.1 c.1 d.2.2.1 d.2.2.2.1 c.2.2.1 c.2.2.2.1
 have u:=oQ b.2.1 a.2.1 b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1
  d.2.1 c.2.1 d.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2
 have r:=iK b.2.2.1 b.2.2.2.1 a.2.2.1 a.2.2.2.1 d.2.2.1 d.2.2.2.1 c.2.2.1 c.2.2.2.1;have t:=iL b.2.2.1 b.2.2.2.1 a.2.2.1 a.2.2.2.1 d.2.2.1 d.2.2.2.1 c.2.2.1 c.2.2.2.1
 have n:=t2 b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1
  d.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2
 have m:=sZ b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1
  d.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2
 have l:=sY b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1
  d.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.2.2 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2
 exact ⟨⟨v.1,u.1,r.1,t.1,n.1,m.1,l.1,rfl,rfl⟩,
   ⟨v.2,u.2,r.2,t.2,n.2,m.2,l.2⟩⟩
lemma gS {p q:AS} {d c:Nat}
  (b:iP p) (a:iP q) (k:dk p d) (j:dk q c) :
  iP (sG p q)/\dk (sG p q) (d|||c):=by
 have l:=kc b.1 a.1 b.2.1 b.2.2.1 a.2.1 a.2.2.1 k.1 j.1 k.2.1 k.2.2 j.2.1 j.2.2;have h:=jj b.2.1 a.2.1 k.2.1 j.2.1;have i:=jk b.2.2.1 a.2.2.1 k.2.2 j.2.2;exact ⟨⟨l.1,h.1,i.1,rfl⟩,⟨l.2,h.2,i.2⟩⟩
lemma iF {p q:AS} {i h:Nat}
  (b:iP p) (a:iP q) (d:dk p i) (c:dk q h) :
  iP (pU p q)/\dk (pU p q) (i&&&h):=by
 have l:=jA b.1 a.1 b.2.1 b.2.2.1 a.2.1 a.2.2.1 d.1 c.1 d.2.1 d.2.2 c.2.1 c.2.2;have j:=iK b.2.1 b.2.2.1 a.2.1 a.2.2.1 d.2.1 d.2.2 c.2.1 c.2.2;have k:=iL b.2.1 b.2.2.1 a.2.1 a.2.2.1 d.2.1 d.2.2 c.2.1 c.2.2;exact ⟨⟨l.1,j.1,k.1,rfl⟩,⟨l.2,j.2,k.2⟩⟩
def x6 (e val w:Nat):Nat:=
 bM 5
  (cond (nE e 0) val (gA w 0))
  (cond (nE e 1) val (gA w 1))
  (cond (nE e 2) val (gA w 2))
  (cond (nE e 3) val (gA w 3))
  (cond (nE e 4) val (gA w 4))
def uv (s val w:Nat):Nat:=
 bM 6
  (cond (nE s 0) val (gB w 0))
  (cond (nE s 1) val (gB w 1))
  (cond (nE s 2) val (gB w 2))
  (cond (nE s 3) val (gB w 3))
  (cond (nE s 4) val (gB w 4))
def go (e z0 z1 z2 w:Nat):Nat:=
 let a:=bE 3 z0 z1 z2
 bM 9
  (cond (nE e 0) a (aL w 0))
  (cond (nE e 1) a (aL w 1))
  (cond (nE e 2) a (aL w 2))
  (cond (nE e 3) a (aL w 3))
  (cond (nE e 4) a (aL w 4))
def ec (s z0 z1 z2 w:Nat):Nat:=
 let a:=bE 5 z0 z1 z2
 bM 15
  (cond (nE s 0) a (V w 0))
  (cond (nE s 1) a (V w 1))
  (cond (nE s 2) a (V w 2))
  (cond (nE s 3) a (V w 3))
  (cond (nE s 4) a (V w 4))
lemma x5 {w:Nat} (d:eV w) (e:Fin 5) {val:Nat} (hv:val<=9) :
   eV (x6 e.val val w)/\∀ i:Fin 5,o 5 i.val (x6 e.val val w)=if i=e then val else o 5 i.val w:=by
 have j:∀ k<5,gA w k=o 5 k w/\gA w k<=9:=fun k hk=>⟨m8 w k d hk,by rw[m8 w k d hk];exact d.1 k hk⟩
 have a:∀ k<5,cond (nE e.val k) val (gA w k)<32:=fun k hk=>by
   have:=(j k hk).2;cases nE e.val k <;> simp only[bT,bC] <;> omega
 have o0:∀ k<5,cond (nE e.val k) val (gA w k)<=9:=fun k hk=>by
   have:=(j k hk).2;cases nE e.val k <;> simp only[bT,bC] <;> omega
 have c:=cv 5 _ _ _ _ _ (a 0 (by omega)) (a 1 (by omega)) (a 2 (by omega)) (a 3 (by omega)) (a 4 (by omega));have l:=dl 5 _ _ _ _ _ (a 0 (by omega)) (a 1 (by omega)) (a 2 (by omega)) (a 3 (by omega)) (a 4 (by omega))
 have b:∀ k<5,o 5 k (x6 e.val val w)=cond (nE e.val k) val (gA w k):=fun k hk=>by
   unfold x6
   have:k=0\/k=1\/k=2\/k=3\/k=4:=by omega
   rcases this with rfl|rfl|rfl|rfl|rfl
   . exact c.1
   . exact c.2.1
   . exact c.2.2.1
   . exact c.2.2.2.1
   . exact c.2.2.2.2
 refine ⟨⟨fun k hk=>by rw[b k hk];exact o0 k hk,l⟩,fun i=>?_⟩
 rw[b i.val i.isLt,(j i.val i.isLt).1]
 by_cases hie:i=e
 . subst hie;simp
 . have h:nE e.val i.val=false:=by
     cases hb:nE e.val i.val;rfl;exfalso;exact hie (fE (bQ hb).symm)
   simp[hie,h]
lemma x4 {w:Nat} (d:fv w) (s:Fin 5) {val:Nat} (hv:val<=27) :
   fv (uv s.val val w)/\∀ i:Fin 5,o 6 i.val (uv s.val val w)=if i=s then val else o 6 i.val w:=by
 have j:∀ k<5,gB w k=o 6 k w/\gB w k<=27:=fun k hk=>⟨o1 w k d hk,by rw[o1 w k d hk];exact d.1 k hk⟩
 have a:∀ k<5,cond (nE s.val k) val (gB w k)<64:=fun k hk=>by
   have:=(j k hk).2;cases nE s.val k <;> simp only[bT,bC] <;> omega
 have Hg:∀ k<5,cond (nE s.val k) val (gB w k)<=27:=fun k hk=>by
   have:=(j k hk).2;cases nE s.val k <;> simp only[bT,bC] <;> omega
 have c:=cv 6 _ _ _ _ _ (a 0 (by omega)) (a 1 (by omega)) (a 2 (by omega)) (a 3 (by omega)) (a 4 (by omega));have l:=dl 6 _ _ _ _ _ (a 0 (by omega)) (a 1 (by omega)) (a 2 (by omega)) (a 3 (by omega)) (a 4 (by omega))
 have b:∀ k<5,o 6 k (uv s.val val w)=cond (nE s.val k) val (gB w k):=fun k hk=>by
   unfold uv
   have:k=0\/k=1\/k=2\/k=3\/k=4:=by omega
   rcases this with rfl|rfl|rfl|rfl|rfl
   . exact c.1
   . exact c.2.1
   . exact c.2.2.1
   . exact c.2.2.2.1
   . exact c.2.2.2.2
 refine ⟨⟨fun k hk=>by rw[b k hk];exact Hg k hk,l⟩,fun i=>?_⟩
 rw[b i.val i.isLt,(j i.val i.isLt).1]
 by_cases his:i=s
 . subst his;simp
 . have h:nE s.val i.val=false:=by
     cases hb:nE s.val i.val;rfl;exfalso;exact his (fE (bQ hb).symm)
   simp[his,h]
lemma oU {w:Nat} (C:cq w) (e:Fin 5) {m l d:Nat} (h0:m<=3) (h1:l<=3) (h2:d<=3) :
   cq (go e.val m l d w)/\
   ∀ (i:Fin 5) (c:Fin 3),o 3 (3*i.val+c.val) (go e.val m l d w) =
     if i=e then (match c.val with|0=>m|1=>l|_=>d) else o 3 (3*i.val+c.val) w:=by
 have r:bE 3 m l d<2^9:=gG 3 m l d (by omega) (by omega) (by omega);have b:=fd 3 m l d (by omega) (by omega) (by omega);have F:∀ k<5,aL w k=o 9 k w:=fun k hk=>m7 w k C.2 hk
 have u:∀ k<5,aL w k<2^9:=fun k hk=>by rw[F k hk,aS];exact nM _ (by decide)
 have a:∀ k<5,cond (nE e.val k) (bE 3 m l d) (aL w k)<2^9:=fun k hk=>by
   cases nE e.val k;simp only[bC];exact u k hk;simp only[bT];exact r
 have h5:=cv 9 _ _ _ _ _ (a 0 (by omega)) (a 1 (by omega)) (a 2 (by omega)) (a 3 (by omega)) (a 4 (by omega));have x:=dl 9 _ _ _ _ _ (a 0 (by omega)) (a 1 (by omega)) (a 2 (by omega)) (a 3 (by omega)) (a 4 (by omega))
 have t:∀ i:Fin 5,o 9 i.val (go e.val m l d w)=if i=e then bE 3 m l d else o 9 i.val w:=fun i=>by
   have z:o 9 i.val (go e.val m l d w)=cond (nE e.val i.val) (bE 3 m l d) (aL w i.val):=by
     unfold go
     have:i=0\/i=1\/i=2\/i=3\/i=4:=by fin_cases i <;> simp
     rcases this with rfl|rfl|rfl|rfl|rfl
     . simpa using h5.1
     . exact h5.2.1
     . exact h5.2.2.1
     . exact h5.2.2.2.1
     . exact h5.2.2.2.2
   rw[z,F i.val i.isLt]
   by_cases hie:i=e
   . subst hie;simp
   . have y:nE e.val i.val=false:=by
       cases hb:nE e.val i.val;rfl;exfalso;exact hie (fE (bQ hb).symm)
     simp[hie,y]
 have n:∀ (i:Fin 5) (c:Fin 3),o 3 (3*i.val+c.val) (go e.val m l d w) =
     if i=e then (match c.val with|0=>m|1=>l|_=>d) else o 3 (3*i.val+c.val) w:=fun i c=>by
   rw[<- aY 3 c.val i.val (go e.val m l d w) c.isLt,t i]
   by_cases hie:i=e
   . simp only[hie,↓reduceIte]
     have:c=0\/c=1\/c=2:=by fin_cases c <;> simp
     rcases this with rfl|rfl|rfl
     . exact b.1
     . exact b.2.1
     . exact b.2.2
   . simp only[hie,↓reduceIte];exact aY 3 c.val i.val w c.isLt
 refine ⟨⟨fun j hj=>?_,x⟩,n⟩
 have h:=n ⟨j/3,by omega⟩ ⟨j % 3,by omega⟩
 have v:3*(j/3)+j % 3=j:=by omega
 rw[v] at h;rw[h];split_ifs
 . have:j % 3=0\/j % 3=1\/j % 3=2:=by omega
   rcases this with h'|h'|h' <;> simp[h'] <;> omega
 . exact C.1 j hj
lemma tt {w:Nat} (C:az w) (s:Fin 5) {m l d:Nat} (h0:m<=9) (h1:l<=9) (h2:d<=9) :
   az (ec s.val m l d w)/\
   ∀ (i:Fin 5) (c:Fin 3),o 5 (3*i.val+c.val) (ec s.val m l d w) =
     if i=s then (match c.val with|0=>m|1=>l|_=>d) else o 5 (3*i.val+c.val) w:=by
 have r:bE 5 m l d<2^15:=gG 5 m l d (by omega) (by omega) (by omega);have b:=fd 5 m l d (by omega) (by omega) (by omega);have F:∀ k<5,V w k=o 15 k w:=fun k hk=>kI w k C.2 hk
 have u:∀ k<5,V w k<2^15:=fun k hk=>by rw[F k hk,aS];exact nM _ (by decide)
 have a:∀ k<5,cond (nE s.val k) (bE 5 m l d) (V w k)<2^15:=fun k hk=>by
   cases nE s.val k;simp only[bC];exact u k hk;simp only[bT];exact r
 have h5:=cv 15 _ _ _ _ _ (a 0 (by omega)) (a 1 (by omega)) (a 2 (by omega)) (a 3 (by omega)) (a 4 (by omega));have x:=dl 15 _ _ _ _ _ (a 0 (by omega)) (a 1 (by omega)) (a 2 (by omega)) (a 3 (by omega)) (a 4 (by omega))
 have t:∀ i:Fin 5,o 15 i.val (ec s.val m l d w)=if i=s then bE 5 m l d else o 15 i.val w:=fun i=>by
   have z:o 15 i.val (ec s.val m l d w)=cond (nE s.val i.val) (bE 5 m l d) (V w i.val):=by
     unfold ec
     have:i=0\/i=1\/i=2\/i=3\/i=4:=by fin_cases i <;> simp
     rcases this with rfl|rfl|rfl|rfl|rfl
     . simpa using h5.1
     . exact h5.2.1
     . exact h5.2.2.1
     . exact h5.2.2.2.1
     . exact h5.2.2.2.2
   rw[z,F i.val i.isLt]
   by_cases his:i=s
   . subst his;simp
   . have y:nE s.val i.val=false:=by
       cases hb:nE s.val i.val;rfl;exfalso;exact his (fE (bQ hb).symm)
     simp[his,y]
 have n:∀ (i:Fin 5) (c:Fin 3),o 5 (3*i.val+c.val) (ec s.val m l d w) =
     if i=s then (match c.val with|0=>m|1=>l|_=>d) else o 5 (3*i.val+c.val) w:=fun i c=>by
   rw[<- aY 5 c.val i.val (ec s.val m l d w) c.isLt,t i]
   by_cases his:i=s
   . simp only[his,↓reduceIte]
     have:c=0\/c=1\/c=2:=by fin_cases c <;> simp
     rcases this with rfl|rfl|rfl
     . exact b.1
     . exact b.2.1
     . exact b.2.2
   . simp only[his,↓reduceIte];exact aY 5 c.val i.val w c.isLt
 refine ⟨⟨fun j hj=>?_,x⟩,n⟩
 have h:=n ⟨j/3,by omega⟩ ⟨j % 3,by omega⟩
 have v:3*(j/3)+j % 3=j:=by omega
 rw[v] at h;rw[h];split_ifs
 . have:j % 3=0\/j % 3=1\/j % 3=2:=by omega
   rcases this with h'|h'|h' <;> simp[h'] <;> omega
 . exact C.1 j hj
def gr (ax:Nat):Nat:=match ax with|0=>4|1=>2|_=>1
def cQ (x:RS) (ax:Nat):Nat:=
 match ax with|0=>x.2.2.2.2.2.2.1|1=>x.2.2.2.2.2.2.2.1|_=>x.2.2.2.2.2.2.2.2
def fH (w s:Nat):Nat:=
 cond (nE (en w s 0) 9) 1 0 +
 cond (nE (en w s 1) 9) 1 0 +
 cond (nE (en w s 2) 9) 1 0
def fI (e npq pa rwW cwW:Nat):Nat × Nat × Nat:=
 let r0:=cond (nB 1 npq) 0 (hI rwW e 0);let r1:=cond (nB 2 npq) 0 (hI rwW e 1);let r2:=cond (nB 3 npq) 0 (hI rwW e 2);let a:=3 - npq;let d:=av (hI cwW e 0) a;let c:=av (hI cwW e 1) a;let b:=av (hI cwW e 2) a;let rwW':=go e r0 r1 r2 rwW;let cwW':=go e d c b cwW;let ae':=av (gA pa e) (av (r0+r1+r2) (d+c+b));let pa':=x6 e ae' pa
 (pa',rwW',cwW')
def iy (isCol:Bool) (e npq:Nat) (x:RS):RS:=
 let (_,sb,pa,pb,par,pac,bf,be,bd):=x
 cond isCol
  (let a:=fI e npq pa pac par
   (bD a.1,sb,a.1,pb,a.2.2,a.2.1,bf,be,bd))
  (let a:=fI e npq pa par pac
   (bD a.1,sb,a.1,pb,a.2.1,a.2.2,bf,be,bd))
def ix (s ax:Nat) (x:RS):RS:=
 let (sa,_,pa,pb,par,pac,bf,be,bd):=x;let pb':=uv s (aa (gB pb s) 9) pb
 match ax with
 | 0=>(sa,bG pb',pa,pb',par,pac,ec s (en bf s 0) (en bf s 1) (aa (en bf s 2) 9) bf,be,bd)
 | 1=>(sa,bG pb',pa,pb',par,pac,bf,ec s (en be s 0) (en be s 1) (aa (en be s 2) 9) be,bd)
 | _=>(sa,bG pb',pa,pb',par,pac,bf,be,ec s (en bd s 0) (en bd s 1) (aa (en bd s 2) 9) bd)
def i5 (mA1 mB1 mA2 mB2:Nat) (t:Bool × Nat × Nat × Nat):Prop:=
 let (isCol,e,ax,npq):=t
 ∃ (he:e<5) (hax:ax<3),
  let s:Fin 5:=⟨((if isCol then (e+1) % 5 else e)+cH ⟨ax,hax⟩) % 5,by omega⟩
  (if isCol then m4 mA1 mB1 ⟨e,he⟩ ⟨ax,hax⟩=true/\m4 mA2 mB2 ⟨e,he⟩ ⟨ax,hax⟩=true
   else lY mA1 mB1 ⟨e,he⟩ ⟨ax,hax⟩=true/\lY mA2 mB2 ⟨e,he⟩ ⟨ax,hax⟩=true)/\
  ∃ np nq,np+nq=npq/\
    np<=(if S mB1 s ⟨ax,hax⟩ 0=9 then 1 else 0)+(if S mB1 s ⟨ax,hax⟩ 1=9 then 1 else 0)+(if S mB1 s ⟨ax,hax⟩ 2=9 then 1 else 0)/\
    nq<=(if S mB2 s ⟨ax,hax⟩ 0=9 then 1 else 0)+(if S mB2 s ⟨ax,hax⟩ 1=9 then 1 else 0)+(if S mB2 s ⟨ax,hax⟩ 2=9 then 1 else 0)
lemma p6 (a b c:Nat) :
  (if (D a b c).1=9 then 1 else 0) +
  (if (D a b c).2.1=9 then 1 else 0) +
  (if (D a b c).2.2=9 then 1 else 0) =
  (if a=9 then 1 else 0)+(if b=9 then 1 else 0)+(if c=9 then 1 else 0):=
 jT (fun t=>if t=9 then 1 else 0) a b c
lemma kQ {mA mB:Nat} {x:RS} (a:Fin 5) {ax:Nat} (y:ax<3)
   (u:cu x) (v:aW x mA mB)
   (j:9<=(ak mB a ⟨ax,y⟩).2.2) (m:9<=cw mB a) :
   cu (ix a.val ax x)/\aW (ix a.val ax x) mA mB:=by
 rcases x with ⟨sa,sb,pa,pb,par,pac,bf,be,bd⟩;dsimp only[cu,aW] at u v;rcases u with ⟨hpa,hpb,hpar,hpac,hpb0,hpb1,hpb2,hsa,hsb⟩;rcases v with ⟨dpa,dpb,dpar,dpac,dpb0,dpb1,dpb2⟩
 have l:aa (gB pb a.val) 9<=cw mB a:=
   aV (by rw[o1 pb a.val hpb a.isLt];exact dpb a) m
 have k:aa (gB pb a.val) 9<=27:=by have:=bV mB a;omega
 have b:=x4 hpb a k
 have dpb':e7 (uv a.val (aa (gB pb a.val) 9) pb) mB:=fun s'=>by
   rw[b.2 s'];split_ifs with h
   . subst h;exact l
   . exact dpb s'
 have c:∀ (w:Nat) (axf:Fin 3),az w->ag w (fun s'=>ak mB s' axf)->
     9<=(ak mB a axf).2.2->
     az (ec a.val (en w a.val 0) (en w a.val 1) (aa (en w a.val 2) 9) w)/\
     ag (ec a.val (en w a.val 0) (en w a.val 1) (aa (en w a.val 2) 9) w) (fun s'=>ak mB s' axf):=by
   intro w axf hw hd h9
   have h0:en w a.val 0=o 5 (3*a.val) w:=by simpa using j0 w a.val 0 hw a.isLt (by omega)
   have h1:=j0 w a.val 1 hw a.isLt (by omega);have h2:=j0 w a.val 2 hw a.isLt (by omega);have t:=hw.1 (3*a.val) (by omega);have r:=hw.1 (3*a.val+1) (by omega);have n:=hw.1 (3*a.val+2) (by omega)
   have i:=tt hw a
     (by rw[h0];exact t:en w a.val 0<=9)
     (by rw[h1];exact r:en w a.val 1<=9)
     (by rw[aP,h2];exact xL n (lR 9):aa (en w a.val 2) 9<=9)
   refine ⟨i.1,fun s'=>?_⟩
   have gK:o 5 (3*s'.val) (ec a.val (en w a.val 0) (en w a.val 1) (aa (en w a.val 2) 9) w) =
       if s'=a then en w a.val 0 else o 5 (3*s'.val) w:=by simpa using i.2 s' 0
   have eW:o 5 (3*s'.val+1) (ec a.val (en w a.val 0) (en w a.val 1) (aa (en w a.val 2) 9) w) =
       if s'=a then en w a.val 1 else o 5 (3*s'.val+1) w:=i.2 s' 1
   have fj:o 5 (3*s'.val+2) (ec a.val (en w a.val 0) (en w a.val 1) (aa (en w a.val 2) 9) w) =
       if s'=a then aa (en w a.val 2) 9 else o 5 (3*s'.val+2) w:=i.2 s' 2
   rw[gK,eW,fj];split_ifs with hs'
   . subst hs';rcases hd s' with ⟨d0,d1,d2⟩
     rw[h0,h1,h2];exact ⟨d0,d1,by rw[aP];exact xL d2 h9⟩
   . exact hd s'
 have d:ax=0\/ax=1\/ax=2:=by omega
 rcases d with rfl|rfl|rfl
 . have h:=c bf 0 hpb0 dpb0 j;exact ⟨⟨hpa,b.1,hpar,hpac,h.1,hpb1,hpb2,hsa,rfl⟩,⟨dpa,dpb',dpar,dpac,h.2,dpb1,dpb2⟩⟩
 . have h:=c be 1 hpb1 dpb1 j;exact ⟨⟨hpa,b.1,hpar,hpac,hpb0,h.1,hpb2,hsa,rfl⟩,⟨dpa,dpb',dpar,dpac,dpb0,h.2,dpb2⟩⟩
 . have h:=c bd 2 hpb2 dpb2 j;exact ⟨⟨hpa,b.1,hpar,hpac,hpb0,hpb1,h.1,hsa,rfl⟩,⟨dpa,dpb',dpar,dpac,dpb0,dpb1,h.2⟩⟩
lemma kp {mA:Nat} (a:Fin 5) (d:Nat) {pa b c:Nat}
   {y z:Fin 5->Nat × Nat × Nat}
   (P:eV pa) (k:cq b) (l:cq c)
   (b1:dI pa mA) (b0:bg b y) (b2:bg c z)
   (a5:(y a).1+(y a).2.1+(y a).2.2=bk mA a)
   (a6:(z a).1+(z a).2.1+(z a).2.2=bk mA a)
   (a3:if 1<=d then (y a).1=0 else True)
   (a2:if 2<=d then (y a).2.1=0 else True)
   (a1:if 3<=d then (y a).2.2=0 else True)
   (a9:(z a).1<=3 - d) (a8:(z a).2.1<=3 - d) (a7:(z a).2.2<=3 - d) :
   let m:=fI a.val d pa b c
   eV m.1/\cq m.2.1/\cq m.2.2/\dI m.1 mA/\bg m.2.1 y/\bg m.2.2 z:=by
 unfold fI;dsimp only;set r0:=cond (nB 1 d) 0 (hI b a.val 0);set r1:=cond (nB 2 d) 0 (hI b a.val 1);set r2:=cond (nB 3 d) 0 (hI b a.val 2);set K:=av (hI c a.val 0) (3 - d);set F:=av (hI c a.val 1) (3 - d);set C:=av (hI c a.val 2) (3 - d)
 have ah:hI b a.val 0=o 3 (3*a.val) b:=by simpa using cc b a.val 0 k a.isLt (by omega)
 have ae:hI b a.val 1=o 3 (3*a.val+1) b:=cc b a.val 1 k a.isLt (by omega);have ac:hI b a.val 2=o 3 (3*a.val+2) b:=cc b a.val 2 k a.isLt (by omega)
 have aw:hI c a.val 0=o 3 (3*a.val) c:=by simpa using cc c a.val 0 l a.isLt (by omega)
 have ar:hI c a.val 1=o 3 (3*a.val+1) c:=cc c a.val 1 l a.isLt (by omega);have an:hI c a.val 2=o 3 (3*a.val+2) c:=cc c a.val 2 l a.isLt (by omega)
 have N:r0<=3:=by dsimp[r0];cases nB 1 d;(simp only[bC];rw[ah];exact k.1 (3*a.val) (by omega));(simp only[bT];decide)
 have M:r1<=3:=by dsimp[r1];cases nB 2 d;(simp only[bC];rw[ae];exact k.1 (3*a.val+1) (by omega));(simp only[bT];decide)
 have L:r2<=3:=by dsimp[r2];cases nB 3 d;(simp only[bC];rw[ac];exact k.1 (3*a.val+2) (by omega));(simp only[bT];decide)
 have W:K<=3:=by dsimp[K];rw[aG,aw];exact lT (mL _ _) (l.1 (3*a.val) (by omega))
 have T:F<=3:=by dsimp[F];rw[aG,ar];exact lT (mL _ _) (l.1 (3*a.val+1) (by omega))
 have Q:C<=3:=by dsimp[C];rw[aG,an];exact lT (mL _ _) (l.1 (3*a.val+2) (by omega))
 have h:=oU k a N M L;have j:=oU l a W T Q
 have a0:av (gA pa a.val) (av (r0+r1+r2) (K+F+C))<=9:=by
   rw[aG,m8 pa a.val P a.isLt];exact lT (mL _ _) (P.1 a.val a.isLt)
 have n:=x5 P a a0;rcases b0 a with ⟨dr0,dr1,dr2⟩;rcases b2 a with ⟨dc0,dc1,dc2⟩
 have u:(y a).1<=r0:=by
   dsimp[r0];cases hb:nB 1 d
   . simp only[bC,ah];exact dr0
   . have h1:=bL.mp hb;simp only[h1,↓reduceIte] at a3;simp[a3]
 have t:(y a).2.1<=r1:=by
   dsimp[r1];cases hb:nB 2 d
   . simp only[bC,ae];exact dr1
   . have h2:=bL.mp hb;simp only[h2,↓reduceIte] at a2;simp[a2]
 have r:(y a).2.2<=r2:=by
   dsimp[r2];cases hb:nB 3 d
   . simp only[bC,ac];exact dr2
   . have h3:=bL.mp hb;simp only[h3,↓reduceIte] at a1;simp[a1]
 have x:(z a).1<=K:=by dsimp[K];rw[aw,aG];exact lM dc0 a9
 have w:(z a).2.1<=F:=by dsimp[F];rw[ar,aG];exact lM dc1 a8
 have v:(z a).2.2<=C:=by dsimp[C];rw[an,aG];exact lM dc2 a7
 have ab:bk mA a<=av (gA pa a.val) (av (r0+r1+r2) (K+F+C)):=by
   have hd:=b1 a;rw[<- m8 pa a.val P a.isLt] at hd
   exact gT.mpr ⟨hd,gT.mpr ⟨by linarith [a5,u,t,r],by linarith [a6,x,w,v]⟩⟩
 refine ⟨n.1,h.1,j.1,fun i=>?_,fun i=>?_,fun i=>?_⟩
 . rw[n.2 i];split_ifs with hi
   . subst hi;exact ab
   . exact b1 i
 . have gK:o 3 (3*i.val) (go a.val r0 r1 r2 b)=if i=a then r0 else o 3 (3*i.val) b:=by simpa using h.2 i 0
   have eW:o 3 (3*i.val+1) (go a.val r0 r1 r2 b)=if i=a then r1 else o 3 (3*i.val+1) b:=h.2 i 1;have fj:o 3 (3*i.val+2) (go a.val r0 r1 r2 b)=if i=a then r2 else o 3 (3*i.val+2) b:=h.2 i 2;rw[gK,eW,fj];split_ifs with hi
   . subst hi;exact ⟨u,t,r⟩
   . exact b0 i
 . have gK:o 3 (3*i.val) (go a.val K F C c)=if i=a then K else o 3 (3*i.val) c:=by simpa using j.2 i 0
   have eW:o 3 (3*i.val+1) (go a.val K F C c)=if i=a then F else o 3 (3*i.val+1) c:=j.2 i 1;have fj:o 3 (3*i.val+2) (go a.val K F C c)=if i=a then C else o 3 (3*i.val+2) c:=j.2 i 2;rw[gK,eW,fj];split_ifs with hi
   . subst hi;exact ⟨x,w,v⟩
   . exact b2 i
def er (mB:Nat) (s:Fin 5) (ax:Fin 3):Fin 3->Fin 3->Fin 3->Bool:=
 match ax.val with
 | 0=>B mB s
 | 1=>fun b a c=>B mB s a b c
 | _=>fun c a b=>B mB s a b c
def jG (mA:Nat) (e:Fin 5) (isCol:Bool):Fin 3->Fin 3->Bool:=
 if isCol then fun r c=>ao mA e c r else ao mA e
lemma ie (mB:Nat) (s:Fin 5) (ax k:Fin 3) :
  A (er mB s ax) k=S mB s ax k:=by
 fin_cases ax <;> rfl
lemma oT (h d:Nat) (s:Fin 5) (ax k:Fin 3) :
   A (fun a b c=>er h s ax a b c&&er d s ax a b c) k=S (h&&&d) s ax k:=by
 have i:B (h&&&d) s=fun a b c=>B h s a b c&&B d s a b c:=by
   funext a b c;exact dG h d s a b c
 fin_cases ax
 . change A _ k=A (B (h&&&d) s) k;rw[i];rfl
 . change A _ k=Z (B (h&&&d) s) k;rw[i];rfl
 . change A _ k=aK (B (h&&&d) s) k;rw[i];rfl
lemma pN (h d:Nat) (s:Fin 5) (ax:Fin 3) :
   cU (fun a b c=>er h s ax a b c&&er d s ax a b c)=cw (h&&&d) s:=by
 have i:B (h&&&d) s=fun a b c=>B h s a b c&&B d s a b c:=by
   funext a b c;exact dG h d s a b c
 unfold cw;rw[i]
 fin_cases ax
 . rfl
 . exact fx (fun a b c=>B h s a b c&&B d s a b c)
 . exact e8 (fun a b c=>B h s a b c&&B d s a b c)
lemma pP (ax:Nat) (a:ax<3):gr ax=cH ⟨ax,a⟩:=by
 have:ax=0\/ax=1\/ax=2:=by omega
 rcases this with rfl|rfl|rfl <;> rfl
lemma pW {b l a j:Nat} {x:RS} {t:Bool × Nat × Nat × Nat}
   (w:cu x) (z:aW x (b&&&a) (l&&&j))
   (F:i5 b l a j t) :
   let (isCol,e,ax,npq):=t
   let s:=((if isCol then (e+1) % 5 else e)+gr ax) % 5
   (cu (iy isCol e npq x)/\aW (iy isCol e npq x) (b&&&a) (l&&&j))\/
   (cu (ix s ax x)/\aW (ix s ax x) (b&&&a) (l&&&j)):=by
 rcases t with ⟨isCol,e,ax,npq⟩;rcases F with ⟨he,hax,hlnk,np,nq,hnpq,hnp,hnq⟩;let h:Fin 5:=⟨e,he⟩;let d:Fin 3:=⟨ax,hax⟩
 let i:Fin 5:=⟨((if isCol then (e+1) % 5 else e)+cH d) % 5,by omega⟩
 have y:((if isCol then (e+1) % 5 else e)+gr ax) % 5=i.val:=by
   dsimp only[i,d];rw[pP ax hax]
 have eW:∀ k:Fin 3,A (er l i d) k=9->Y (jG b h isCol) k=0:=by
   intro k hk;rw[ie] at hk;cases isCol
   . simp only[bF,↓reduceIte] at hlnk
     have m:i=⟨(e+cH d) % 5,by omega⟩:=by ext;simp[i]
     rw[m] at hk;exact of_decide_eq_true hlnk.1 k hk
   . simp only[↓reduceIte] at hlnk
     have m:i=⟨((e+1) % 5+cH d) % 5,by omega⟩:=by ext;simp[i]
     rw[m] at hk;exact of_decide_eq_true hlnk.1 k hk
 have fj:∀ k:Fin 3,A (er j i d) k=9->Y (jG a h isCol) k=0:=by
   intro k hk;rw[ie] at hk;cases isCol
   . simp only[bF,↓reduceIte] at hlnk
     have m:i=⟨(e+cH d) % 5,by omega⟩:=by ext;simp[i]
     rw[m] at hk;exact of_decide_eq_true hlnk.2 k hk
   . simp only[↓reduceIte] at hlnk
     have m:i=⟨((e+1) % 5+cH d) % 5,by omega⟩:=by ext;simp[i]
     rw[m] at hk;exact of_decide_eq_true hlnk.2 k hk
 have hnp':np<=(if A (er l i d) 0=9 then 1 else 0)+(if A (er l i d) 1=9 then 1 else 0)+(if A (er l i d) 2=9 then 1 else 0):=by
   simp only[ie];exact hnp
 have hnq':nq<=(if A (er j i d) 0=9 then 1 else 0)+(if A (er j i d) 1=9 then 1 else 0)+(if A (er j i d) 2=9 then 1 else 0):=by
   simp only[ie];exact hnq
 have C:=pX (jG b h isCol) (jG a h isCol) (er l i d) (er j i d) eW fj np nq hnp' hnq';dsimp only;rw[y];rcases C with ⟨hbs9,hbtot9⟩|⟨hsr0,hsr1,hsr2,hsc0,hsc1,hsc2⟩
 . right;simp only[oT] at hbs9;rw[pN] at hbtot9;exact kQ i hax w z hbs9 hbtot9
 . left;rw[hnpq] at hsr0 hsr1 hsr2 hsc0 hsc1 hsc2
   have u:(cf (b&&&a) h).1+(cf (b&&&a) h).2.1+(cf (b&&&a) h).2.2=bk (b&&&a) h:=by
     unfold cf bk gz am;exact cr _ _ _
   have v:(cg (b&&&a) h).1+(cg (b&&&a) h).2.1+(cg (b&&&a) h).2.2=bk (b&&&a) h:=by
     unfold cg bk aR;rw[gM];exact cr _ _ _
   rcases x with ⟨sa,sb,pa,pb,par,pac,bf,be,bd⟩;dsimp only[cu,aW] at w z;rcases w with ⟨hpa,hpb,hpar,hpac,hpb0,hpb1,hpb2,hsa,hsb⟩;rcases z with ⟨dpa,dpb,dpar,dpac,dpb0,dpb1,dpb2⟩
   clear eW fj hnp' hnq' hnp hnq hlnk
   cases isCol
   . have K:(fun r c=>jG b h false r c&&jG a h false r c)=ao (b&&&a) h:=by
       funext r c;exact (fk b a h r c).symm
     rw[K] at hsr0 hsr1 hsr2 hsc0 hsc1 hsc2;have n:=kp h npq hpa hpar hpac dpa dpar dpac u v hsr0 hsr1 hsr2 hsc0 hsc1 hsc2;unfold iy;simp only[bC]
     exact ⟨⟨n.1,hpb,n.2.1,n.2.2.1,hpb0,hpb1,hpb2,rfl,hsb⟩,
            ⟨n.2.2.2.1,dpb,n.2.2.2.2.1,n.2.2.2.2.2,dpb0,dpb1,dpb2⟩⟩
   . have K:(fun r c=>jG b h true r c&&jG a h true r c)=fun r c=>ao (b&&&a) h c r:=by
       funext r c;exact (fk b a h c r).symm
     rw[K] at hsr0 hsr1 hsr2 hsc0 hsc1 hsc2;simp only[lJ] at hsr0 hsr1 hsr2;simp only[sX] at hsc0 hsc1 hsc2;have n:=kp h npq hpa hpac hpar dpa dpac dpar v u hsr0 hsr1 hsr2 hsc0 hsc1 hsc2;unfold iy;simp only[bT]
     exact ⟨⟨n.1,hpb,n.2.2.1,n.2.1,hpb0,hpb1,hpb2,rfl,hsb⟩,
            ⟨n.2.2.2.1,dpb,n.2.2.2.2.2,n.2.2.2.2.1,dpb0,dpb1,dpb2⟩⟩
def ry (m k:Nat):Bool:=nE (land (shiftRight m k) 1) 1
lemma zt (m k:Nat):ry m k=m.testBit k:=by
 unfold ry;rw[nJ]
 have b:land (shiftRight m k) 1=(m/2^k) % 2:=by
   change (m >>> k)&&&(2^1 - 1)=_;rw[nW,nD]
 rw[b];cases h:nE ((m/2^k) % 2) 1
 . have a:(m/2^k) % 2 ≠ 1:=fun c=>by rw[c] at h;cases h
   simp[a]
 . have c:=bQ h;simp[c]
def lD (p q:RL) (isCol:Bool) (e ax:Nat):List (Bool × Nat × Nat × Nat):=
 let a:=cond isCol 15 0+3*e+ax
 cond (ry p.2 a&&ry q.2 a)
  (let s:=(cond isCol ((e+1) % 5) e+gr ax) % 5
   let c:=fH (cQ p.1 ax) s;let b:=fH (cQ q.1 ax) s
   cond (nB 1 c&&nB 1 b) [(isCol,e,ax,c+b)] [])
  []
def kJ (p q:RL):List (Bool × Nat × Nat × Nat):=
 let f:=fun isCol e=>lD p q isCol e 0 ++ lD p q isCol e 1 ++ lD p q isCol e 2
 f false 0 ++ f false 1 ++ f false 2 ++ f false 3 ++ f false 4 ++
 f true 0 ++ f true 1 ++ f true 2 ++ f true 3 ++ f true 4
lemma o3 {w mB:Nat} {s:Fin 5} {ax:Fin 3} (c:az w) (d:ag w (fun s'=>ak mB s' ax)) :
   fH w s.val<=(if S mB s ax 0=9 then 1 else 0)+(if S mB s ax 1=9 then 1 else 0)+(if S mB s ax 2=9 then 1 else 0):=by
 rw[<- p6];unfold fH;rw[j0 w s.val 0 c s.isLt (by omega),j0 w s.val 1 c s.isLt (by omega),j0 w s.val 2 c s.isLt (by omega)];rcases d s with ⟨d0,d1,d2⟩;dsimp only at d0 d1 d2;simp only[nZ]
 have b:∀ k:Fin 3,S mB s ax k<=9:=fun k=>by
   have:ax=0\/ax=1\/ax=2:=by fin_cases ax <;> simp
   rcases this with rfl|rfl|rfl
   . exact bS (B mB s) k
   . change Z (B mB s) k<=9;rw[<- aT];exact bS _ k
   . change aK (B mB s) k<=9;exact bS _ k
 have H5:=b 0;have QJ:=b 1;have H4:=b 2
 have a:(ak mB s ax).1<=9/\(ak mB s ax).2.1<=9/\(ak mB s ax).2.2<=9:=by
   unfold ak D;simp only[aG,aP];omega
 have f:∀ u v,u<=v->v<=9->cond (nE u 9) 1 0<=if v=9 then 1 else 0:=fun u v huv hv=>by
   cases h:nE u 9
   . simp
   . have:u=9:=bQ h;simp[show v=9 by omega]
 have l:=f _ _ d0 a.1;have j:=f _ _ d1 a.2.1;have i:=f _ _ d2 a.2.2;unfold ak at l j i;omega
lemma sj {p q:RL} {l j k i:Nat} (d:Bool) {e ax:Nat} (m:e<5) (a:ax<3)
   (u:gw p) (n:gw q) (w:dj p l j) (v:dj q k i) :
   ∀ t ∈ lD p q d e ax,i5 l j k i t:=by
 intro t ht;unfold lD at ht;simp only[zt] at ht
 have b:∀ (r:RL) (mA mB:Nat),gw r->dj r mA mB->
     ∀ s:Fin 5,fH (cQ r.1 ax) s.val<=
       (if S mB s ⟨ax,a⟩ 0=9 then 1 else 0)+(if S mB s ⟨ax,a⟩ 1=9 then 1 else 0)+(if S mB s ⟨ax,a⟩ 2=9 then 1 else 0):=by
   intro r mA mB hwr dr s
   have:ax=0\/ax=1\/ax=2:=by omega
   rcases this with rfl|rfl|rfl
   . exact o3 (ax:=0) hwr.1.2.2.2.2.1 dr.1.2.2.2.2.1
   . exact o3 (ax:=1) hwr.1.2.2.2.2.2.1 dr.1.2.2.2.2.2.1
   . exact o3 (ax:=2) hwr.1.2.2.2.2.2.2.1 dr.1.2.2.2.2.2.2
 have h:gr ax=cH ⟨ax,a⟩:=by
   have:ax=0\/ax=1\/ax=2:=by omega
   rcases this with rfl|rfl|rfl <;> rfl
 cases d
 . simp only[bC] at ht;cases h1:(p.2.testBit (0+3*e+ax)&&q.2.testBit (0+3*e+ax))
   . simp only[h1,bC] at ht;cases ht
   . simp only[h1,bT] at ht
     cases h2:(nB 1 (fH (cQ p.1 ax) ((e+gr ax) % 5))&&
                 nB 1 (fH (cQ q.1 ax) ((e+gr ax) % 5)))
     . simp only[h2,bC] at ht;cases ht
     . simp only[h2,bT,List.mem_singleton] at ht;rw[ht];simp only[bA,Nat.zero_add] at h1
       set c:Fin 5:=⟨(e+cH ⟨ax,a⟩) % 5,by omega⟩
       refine ⟨m,a,⟨w.2.1 ⟨e,m⟩ ⟨ax,a⟩ h1.1,v.2.1 ⟨e,m⟩ ⟨ax,a⟩ h1.2⟩,
         fH (cQ p.1 ax) c.val,fH (cQ q.1 ax) c.val,by dsimp only[c];rw[h],
         b p l j u w c,b q k i n v c⟩
 . simp only[bT] at ht;cases h1:(p.2.testBit (15+3*e+ax)&&q.2.testBit (15+3*e+ax))
   . simp only[h1,bC] at ht;cases ht
   . simp only[h1,bT] at ht
     cases h2:(nB 1 (fH (cQ p.1 ax) (((e+1) % 5+gr ax) % 5))&&
                 nB 1 (fH (cQ q.1 ax) (((e+1) % 5+gr ax) % 5)))
     . simp only[h2,bC] at ht;cases ht
     . simp only[h2,bT,List.mem_singleton] at ht;rw[ht];simp only[bA] at h1
       set c:Fin 5:=⟨((e+1) % 5+cH ⟨ax,a⟩) % 5,by omega⟩
       refine ⟨m,a,⟨w.2.2 ⟨e,m⟩ ⟨ax,a⟩ h1.1,v.2.2 ⟨e,m⟩ ⟨ax,a⟩ h1.2⟩,
         fH (cQ p.1 ax) c.val,fH (cQ q.1 ax) c.val,by dsimp only[c];rw[h],
         b p l j u w c,b q k i n v c⟩
lemma q4 {p q:RL} {d b c a:Nat}
  (i:gw p) (h:gw q) (k:dj p d b) (j:dj q c a) :
  ∀ t ∈ kJ p q,i5 d b c a t:=by
 intro t ht;unfold kJ at ht;simp only[List.mem_append] at ht
 rcases ht with (((((((((ht|ht)|ht)|ht)|ht)|ht)|ht)|ht)|ht)|ht) <;>
  (rcases ht with (ht|ht)|ht <;> exact sj _ (by omega) (by omega) i h k j t ht)
def dg (check:RS->Bool):List (Bool × Nat × Nat × Nat)->RS->Bool
 | [],_=>false
 | (isCol,e,ax,npq) :: rest,x=>
  let s:=(cond isCol ((e+1) % 5) e+gr ax) % 5
  cond (nB 9 (en (cQ x ax) s 2)) (dg check rest x)
   (let b:=iy isCol e npq x
    let a:=ix s ax x
    (check b||dg check rest b)&&
    (check a||dg check rest a))
lemma iw {c:RS->Bool} {j h i d:Nat}
   (a:List (Bool × Nat × Nat × Nat))
   (k:∀ t ∈ a,i5 j h i d t) :
   ∀ x:RS,cu x->aW x (j&&&i) (h&&&d)->
     dg c a x=true->
     ∃ x':RS,cu x'/\aW x' (j&&&i) (h&&&d)/\c x'=true:=by
 induction a with
 | nil=>intro x _ _ hc;cases hc
 | cons t rest ih=>
   intro x hwx hdx hc;rcases t with ⟨isCol,e,ax,npq⟩;unfold dg at hc;have b:∀ u ∈ rest,i5 j h i d u:=fun u hu=>k u (List.mem_cons_of_mem _ hu)
   have m:cond isCol ((e+1) % 5) e=if isCol then (e+1) % 5 else e:=by cases isCol <;> rfl
   rw[m] at hc;set s:=((if isCol then (e+1) % 5 else e)+gr ax) % 5;cases hskip:nB 9 (en (cQ x ax) s 2)
   . simp only[hskip,bC,bA,bO] at hc;have l:=pW hwx hdx (k _ (List.mem_cons_self ..));rcases l with ⟨hwA,hdA⟩|⟨hwB,hdB⟩
     . rcases hc.1 with hca|hba
       . exact ⟨_,hwA,hdA,hca⟩
       . exact ih b _ hwA hdA hba
     . rcases hc.2 with hcb|hbb
       . exact ⟨_,hwB,hdB,hcb⟩
       . exact ih b _ hwB hdB hbb
   . simp only[hskip,bT] at hc;exact ih b x hwx hdx hc
abbrev cT:=Nat × Nat × Bool
def og (p:cT):Prop:=p.1<15/\p.2.1<15
def H1 (g v:Nat):Nat:=cond (nB g 4) ((v+g) % 5) ((10 - v+g) % 5)
def ji (g i:Nat):Nat:=5*(i/5)+H1 g (i % 5)
def gY (g:Nat) (p:cT):cT:=(ji g p.1,ji g p.2.1,p.2.2)
def aN (p:cT) (x:Fin 15->Bool):Bool:=
 let v1:=x ⟨p.1 % 15,nM _ (by decide)⟩;let v2:=x ⟨p.2.1 % 15,nM _ (by decide)⟩
 if p.2.2 then v1||v2 else v1&&v2
def TH (p q:cT) (outerOr:Bool) (x:Fin 15->Bool):Bool:=
 if outerOr then aN p x||aN q x else aN p x&&aN q x
lemma jF:∀ (g:Fin 10) (i:Fin 15),ji g.val i.val=(ek g i).val:=by decide +kernel
lemma we (g:Fin 10) {p:cT} (a:og p):og (gY g.val p):=by
 refine ⟨?_,?_⟩
 . change ji g.val p.1<15;rw[jF g ⟨p.1,a.1⟩];exact (ek g ⟨p.1,a.1⟩).isLt
 . change ji g.val p.2.1<15;rw[jF g ⟨p.2.1,a.2⟩];exact (ek g ⟨p.2.1,a.2⟩).isLt
lemma g6 (g:Fin 10) {p:cT} (a:og p) :
  aN (gY g.val p)=E g (aN p):=by
 funext x;unfold aN gY E;dsimp only;have c:(⟨p.1 % 15,nM _ (by decide)⟩:Fin 15)=⟨p.1,a.1⟩:=fE (nQ a.1);have b:(⟨p.2.1 % 15,nM _ (by decide)⟩:Fin 15)=⟨p.2.1,a.2⟩:=fE (nQ a.2)
 have h1:(⟨ji g.val p.1 % 15,nM _ (by decide)⟩:Fin 15)=ek g ⟨p.1 % 15,nM _ (by decide)⟩:=by
  rw[c];ext;dsimp only;rw[jF g ⟨p.1,a.1⟩,nQ (ek g ⟨p.1,a.1⟩).isLt]
 have h2:(⟨ji g.val p.2.1 % 15,nM _ (by decide)⟩:Fin 15)=ek g ⟨p.2.1 % 15,nM _ (by decide)⟩:=by
  rw[b];ext;dsimp only;rw[jF g ⟨p.2.1,a.2⟩,nQ (ek g ⟨p.2.1,a.2⟩).isLt]
 rw[h1,h2]
lemma vU (i j:Nat) (b:Bool):aN (i,j,b)=aN (j,i,b):=by
 funext x;unfold aN;dsimp only;cases b
 . exact bY _ _
 . exact bP _ _
lemma pk (i:Nat) (b:Bool):aN (i,i,b)=fun x=>x ⟨i % 15,nM _ (by decide)⟩:=by
 funext x;unfold aN;dsimp only;cases b <;> simp
def nj (i:Nat):Nat:=match i with
 | 0=>0x1b60000001f8|1=>0x3f1b6|2=>0x7e36c00|3=>0xfc6d80000|4=>0x1f8db0000000
 | 5=>0x16d0000001c7|6=>0x38f6d|7=>0x71eda00|8=>0xe3db40000|9=>0x1c7b68000000
 | 10=>0xdb00000003f|11=>0x7edb|12=>0xfdb600|13=>0x1fb6c0000|_=>0x3f6d8000000
def ni (i:Nat):Nat:=match i with
 | 0=>0x1ffffffffe070381c924924fffffff
 | 1=>0x7ffffff0381c0e4924927ffffff80001ff
 | 2=>0x1c0e072492493ffffffc0000fffffffff
 | 3=>0x1249249ffffffe00007ffffffff81c0e07
 | 4=>0x7ffffff00003ffffffffc0e07039249249
 | 5=>0x3fe00ffffffe381c0e12492497ffffff
 | 6=>0x7ffffff1c0e070924924bffffff803fe00
 | 7=>0xe070384924925ffffffc01ff007ffffff
 | 8=>0x2492492ffffffe00ff803ffffff8e07038
 | 9=>0x7ffffff007fc01ffffffc70381c2492492
 | 10=>0x7fc0000fffffffc0e07024924927ffffff
 | 11=>0x7ffffffe0703812492493ffffffffc0000
 | 12=>0x70381c09249249ffffffffe00007ffffff
 | 13=>0x4924924fffffffff00003fffffff0381c0
 | _=>0x7ffffffff80001fffffff81c0e04924924
def Bj (p:cT):Nat:=
 cond p.2.2 (lor (nj p.1) (nj p.2.1)) (land (nj p.1) (nj p.2.1))
def Bi (p:cT):Nat:=
 cond p.2.2 (lor (ni p.1) (ni p.2.1)) (land (ni p.1) (ni p.2.1))
lemma tX:∀ i:Fin 15,nj i.val=R (fun x=>x i):=by decide +kernel
lemma tW:∀ i:Fin 15,ni i.val=O (fun x=>x i):=by decide +kernel
lemma mW (p:Nat->Bool) (n:Nat):cF p n<2^n:=by
 induction n with
 | zero=>exact Nat.zero_lt_one
 | succ n ih=>
   unfold cF;split_ifs
   . exact nO (lt_trans ih (Nat.pow_lt_pow_right (by omega) (by omega)))
       (by rw[nL,n1];exact Nat.pow_lt_pow_right (by omega) (by omega))
   . exact lt_trans ih (Nat.pow_lt_pow_right (by omega) (by omega))
lemma uL (f:(Fin 15->Bool)->Bool):R f<2^45:=mW _ 45
lemma uK (f:(Fin 15->Bool)->Bool):O f<2^135:=mW _ 135
lemma yo {p:cT} (a:og p):Bj p=R (aN p):=by
 unfold Bj aN;have h1:(⟨p.1 % 15,nM _ (by decide)⟩:Fin 15)=⟨p.1,a.1⟩:=fE (nQ a.1);have h2:(⟨p.2.1 % 15,nM _ (by decide)⟩:Fin 15)=⟨p.2.1,a.2⟩:=fE (nQ a.2);have c:nj p.1=R (fun x=>x ⟨p.1,a.1⟩):=tX ⟨p.1,a.1⟩;have b:nj p.2.1=R (fun x=>x ⟨p.2.1,a.2⟩):=tX ⟨p.2.1,a.2⟩;cases hb:p.2.2
 . simp only[bC,bF,↓reduceIte,h1,h2,c,b];exact (aF _ _).symm
 . simp only[bT,↓reduceIte,h1,h2,c,b];exact (aX _ _).symm
lemma yn {p:cT} (a:og p):Bi p=O (aN p):=by
 unfold Bi aN;have h1:(⟨p.1 % 15,nM _ (by decide)⟩:Fin 15)=⟨p.1,a.1⟩:=fE (nQ a.1);have h2:(⟨p.2.1 % 15,nM _ (by decide)⟩:Fin 15)=⟨p.2.1,a.2⟩:=fE (nQ a.2);have c:ni p.1=O (fun x=>x ⟨p.1,a.1⟩):=tW ⟨p.1,a.1⟩;have b:ni p.2.1=O (fun x=>x ⟨p.2.1,a.2⟩):=tW ⟨p.2.1,a.2⟩;cases hb:p.2.2
 . simp only[bC,bF,↓reduceIte,h1,h2,c,b];exact (aZ _ _).symm
 . simp only[bT,↓reduceIte,h1,h2,c,b];exact (aJ _ _).symm
def eM (g s:Nat):Nat × Nat × Nat × Nat × Nat × Nat:=
 cond (nE g 0) (0,0,0,0,0,0)
 (let r0:=land s 7;let r1:=land (shiftRight s 3) 7;let r2:=shiftRight s 6
  let b:=land g 1+land (shiftRight g 3) 1+land (shiftRight g 6) 1;let a:=land (shiftRight g 1) 1+land (shiftRight g 4) 1+land (shiftRight g 7) 1
  (r0,r1,r2,b,a,r0+r1+r2 - b - a))
def dx (c s:Nat):(Nat × Nat × Nat) × (Nat × Nat × Nat) × (Nat × Nat × Nat):=
 cond (nE c 134217727) ((9,9,9),(9,9,9),(9,9,9))
 (cond (nE c 0) ((0,0,0),(0,0,0),(0,0,0))
  (let m:=land s 7;let l:=land (shiftRight s 3) 7;let k:=land (shiftRight s 6) 7
   let j:=land (shiftRight s 9) 7;let i:=land (shiftRight s 12) 7;let h:=land (shiftRight s 15) 7;let d:=land (shiftRight s 18) 7;let b:=land (shiftRight s 21) 7;let a:=shiftRight s 24;let x:=m+l+k;let w:=j+i+h;let v:=d+b+a;let C:=m+j+d;let z:=l+i+b;let y:=k+h+a;let r:=land c 73+land (shiftRight c 9) 73+land (shiftRight c 18) 73;let n:=land (shiftRight c 1) 73+land (shiftRight c 10) 73+land (shiftRight c 19) 73;let u:=land r 7+land (shiftRight r 3) 7+shiftRight r 6;let t:=land n 7+land (shiftRight n 3) 7+shiftRight n 6
   ((x,w,v),(C,z,y),(u,t,x+w+v - u - t))))
lemma tM:∀ g:Fin 512,eM g.val (lI g.val) =
 (al (g.val.testBit 0)+al (g.val.testBit 1)+al (g.val.testBit 2),
  al (g.val.testBit 3)+al (g.val.testBit 4)+al (g.val.testBit 5),
  al (g.val.testBit 6)+al (g.val.testBit 7)+al (g.val.testBit 8),
  al (g.val.testBit 0)+al (g.val.testBit 3)+al (g.val.testBit 6),
  al (g.val.testBit 1)+al (g.val.testBit 4)+al (g.val.testBit 7),
  al (g.val.testBit 2)+al (g.val.testBit 5)+al (g.val.testBit 8)):=by decide +kernel
lemma ed:∀ g:Fin 512,
 o 3 0 (lI g.val)=al (g.val.testBit 0)+al (g.val.testBit 1)+al (g.val.testBit 2)/\
 o 3 1 (lI g.val)=al (g.val.testBit 3)+al (g.val.testBit 4)+al (g.val.testBit 5)/\
 o 3 2 (lI g.val)=al (g.val.testBit 6)+al (g.val.testBit 7)+al (g.val.testBit 8)/\
 o 3 0 (land g.val 73)=al (g.val.testBit 0)/\
 o 3 1 (land g.val 73)=al (g.val.testBit 3)/\
 o 3 2 (land g.val 73)=al (g.val.testBit 6)/\
 o 3 0 (land (shiftRight g.val 1) 73)=al (g.val.testBit 1)/\
 o 3 1 (land (shiftRight g.val 1) 73)=al (g.val.testBit 4)/\
 o 3 2 (land (shiftRight g.val 1) 73)=al (g.val.testBit 7):=by decide +kernel
lemma sk:∀ k:Fin 27,(134217727:Nat).testBit k.val=true:=by decide +kernel
lemma Co (mA:Nat) (e:Fin 5) :
  eM (o 9 e.val mA) (lI (o 9 e.val mA)) =
  (am mA e 0,am mA e 1,am mA e 2,aR mA e 0,aR mA e 1,aR mA e 2):=by
 have b:o 9 e.val mA<512:=by rw[aS];exact nM _ (by decide)
 rw[tM ⟨o 9 e.val mA,b⟩]
 have a:∀ k<9,(o 9 e.val mA).testBit k=mA.testBit (9*e.val+k):=fun k hk=>by
  rw[U];simp[hk]
 dsimp only;rw[a 0 (by omega),a 1 (by omega),a 2 (by omega),a 3 (by omega),a 4 (by omega),
  a 5 (by omega),a 6 (by omega),a 7 (by omega),a 8 (by omega)]
 rfl
lemma jo (mB:Nat) (k:Fin 5) :
   let sB:=land mB 0x1249249249249249249249249249249249 +
             land (shiftRight mB 1) 0x1249249249249249249249249249249249 +
             land (shiftRight mB 2) 0x1249249249249249249249249249249249
   dx (o 27 k.val mB) (o 27 k.val sB) =
   ((S mB k 0 0,S mB k 0 1,S mB k 0 2),
    (S mB k 1 0,S mB k 1 1,S mB k 1 2),
    (S mB k 2 0,S mB k 2 1,S mB k 2 2)):=by
 intro sB;set c:=o 27 k.val mB;set s:=o 27 k.val sB
 have hc_lt:c<2^27:=by dsimp only[c];rw[aS];exact nM _ (by decide)
 have P:s<2^27:=by dsimp only[s];rw[aS];exact nM _ (by decide)
 have T:∀ (a b d:Fin 3),B mB k a b d=c.testBit (9*a.val+3*b.val+d.val):=fun a b d=>by
   unfold B;dsimp only[c];rw[U]
   have Q:9*a.val+3*b.val+d.val<27:=by omega
   have y:27*k.val+(9*a.val+3*b.val+d.val)=27*k.val+9*a.val+3*b.val+d.val:=by omega
   simp[Q,y]
 unfold dx;cases xK:nE c 134217727
 . rw[bC];cases h0:nE c 0
   . rw[bC]
     have b9:∀ a:Fin 3,o 9 a.val s=lI (o 9 a.val c):=fun a=>by
       dsimp only[s,c];rw[aY 9 a.val k.val sB a.isLt,aY 9 a.val k.val mB a.isLt]
       exact tu mB ⟨3*k.val+a.val,by omega⟩
     have u:∀ a:Fin 3,o 9 a.val c<512:=fun a=>by rw[aS];exact nM _ (by decide)
     have h:∀ (a:Fin 3) (b d:Fin 3),(o 9 a.val c).testBit (3*b.val+d.val)=B mB k a b d:=fun a b d=>by
       rw[T a b d,U]
       have Q:3*b.val+d.val<9:=by omega
       have y:9*a.val+(3*b.val+d.val)=9*a.val+3*b.val+d.val:=by omega
       simp[Q,y]
     have m:∀ (a b:Fin 3),o 3 (3*a.val+b.val) s=aq (B mB k) a b:=fun a b=>by
       rw[<- aY 3 b.val a.val s b.isLt,b9 a];have hf:=ed ⟨o 9 a.val c,u a⟩;dsimp only at hf;unfold aq
       have:b=0\/b=1\/b=2:=by fin_cases b <;> simp
       rcases this with rfl|rfl|rfl
       . change o 3 0 (lI (o 9 a.val c))=_;rw[hf.1];simp only[<- h a 0 0,<-h a 0 1,<-h a 0 2];rfl
       . change o 3 1 (lI (o 9 a.val c))=_;rw[hf.2.1];simp only[<- h a 1 0,<-h a 1 1,<-h a 1 2];rfl
       . change o 3 2 (lI (o 9 a.val c))=_;rw[hf.2.2.1];simp only[<- h a 2 0,<-h a 2 1,<-h a 2 2];rfl
     have bs:land s 7=o 3 0 s:=by unfold o;simp
     have bb:shiftRight s 24=o 3 8 s:=by rw[bB 3 8 s P];exact nD s 24
     have r:∀ (a:Fin 3),land (shiftRight c (9*a.val)) 73=land (o 9 a.val c) 73:=fun a=>by
       apply nE2;intro b;change ((c >>> (9*a.val))&&&73).testBit b=((o 9 a.val c)&&&73).testBit b;rw[nV,nV,nU,U 9]
       by_cases hb:b<9
       . simp only[hb,dT,bTA]
       . have tG:(73:Nat).testBit b=false:=nT (lQ (by decide:73<2^9) (nP (by omega) (by omega)));simp[tG]
     have n:∀ (a:Fin 3),land (shiftRight c (9*a.val+1)) 73=land (shiftRight (o 9 a.val c) 1) 73:=fun a=>by
       apply nE2;intro b;change ((c >>> (9*a.val+1))&&&73).testBit b=(((o 9 a.val c) >>> 1)&&&73).testBit b;rw[nV,nV,nU,nU,U 9]
       by_cases hb:b=0\/b=3\/b=6
       . rcases hb with rfl|rfl|rfl
         . simp only[show (1:Nat)+0<9 by decide,dT,bTA,nZ]
         . simp only[show (1:Nat)+3<9 by decide,dT,bTA,show 9*a.val+1+3=9*a.val+(1+3) by omega]
         . simp only[show (1:Nat)+6<9 by decide,dT,bTA,show 9*a.val+1+6=9*a.val+(1+6) by omega]
       . have tG:(73:Nat).testBit b=false:=by
           by_cases h9:b<9
           . have:b=1\/b=2\/b=4\/b=5\/b=7\/b=8:=by omega
             rcases this with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
           . exact nT (lQ (by decide:73<2^9) (nP (by omega) (by omega)))
         simp[tG]
     have w:∀ (f0 f1 f2:Nat),f0<2^9->f1<2^9->f2<2^9->
         (∀ j<3,o 3 j f0<=1)->(∀ j<3,o 3 j f1<=1)->(∀ j<3,o 3 j f2<=1)->
         let t:=f0+f1+f2
         land t 7+land (shiftRight t 3) 7+shiftRight t 6 =
         o 3 0 f0+o 3 0 f1+o 3 0 f2+(o 3 1 f0+o 3 1 f1+o 3 1 f2)+(o 3 2 f0+o 3 2 f1+o 3 2 f2):=by
       intro f0 f1 f2 hf0 hf1 hf2 l0 l1 l2;have C:=ap 3 3 f0 f1 (fun j hj=>by have:=l0 j hj;have:=l1 j hj;omega) hf0 hf1;have N:=ap 3 3 (f0+f1) f2 (fun j hj=>by rw[C.2 j hj];have:=l0 j hj;have:=l1 j hj;have:=l2 j hj;omega) C.1 hf2
       have ab:land (f0+f1+f2) 7=o 3 0 (f0+f1+f2):=by unfold o;simp
       have a9:land (shiftRight (f0+f1+f2) 3) 7=o 3 1 (f0+f1+f2):=rfl
       have a8:shiftRight (f0+f1+f2) 6=o 3 2 (f0+f1+f2):=by rw[bB 3 2 _ N.1];exact nD _ 6
       dsimp only;rw[ab,a9,a8,N.2 0 (by omega),N.2 1 (by omega),N.2 2 (by omega),
         C.2 0 (by omega),C.2 1 (by omega),C.2 2 (by omega)]
     have l:∀ x,land x 73<2^9:=fun x=>lO nR (by decide)
     have i:∀ x j,j<3->o 3 j (land x 73)<=1:=fun x j hj=>by
       rw[bm]
       have ae:o 3 j 73=1:=by
         have:j=0\/j=1\/j=2:=by omega
         rcases this with rfl|rfl|rfl <;> decide
       rw[ae];exact nR
     have K:land c 73+land (shiftRight c 9) 73+land (shiftRight c 18) 73 =
         land (o 9 0 c) 73+land (o 9 1 c) 73+land (o 9 2 c) 73:=by
       have h0:land c 73=land (o 9 0 c) 73:=by
         have:=r 0;change land (c >>> 0) 73=_ at this;rwa[Nat.shiftRight_zero] at this
       have h1:land (shiftRight c 9) 73=land (o 9 1 c) 73:=r 1;have h2:land (shiftRight c 18) 73=land (o 9 2 c) 73:=r 2;rw[h0,h1,h2]
     have F:land (shiftRight c 1) 73+land (shiftRight c 10) 73+land (shiftRight c 19) 73 =
         land (shiftRight (o 9 0 c) 1) 73+land (shiftRight (o 9 1 c) 1) 73+land (shiftRight (o 9 2 c) 1) 73:=by
       have h0:land (shiftRight c 1) 73=land (shiftRight (o 9 0 c) 1) 73:=n 0;have h1:land (shiftRight c 10) 73=land (shiftRight (o 9 1 c) 1) 73:=n 1;have h2:land (shiftRight c 19) 73=land (shiftRight (o 9 2 c) 1) 73:=n 2;rw[h0,h1,h2]
     have M:let t0:=land c 73+land (shiftRight c 9) 73+land (shiftRight c 18) 73
         land t0 7+land (shiftRight t0 3) 7+shiftRight t0 6=S mB k 2 0:=by
       have v:=w (land (o 9 0 c) 73) (land (o 9 1 c) 73) (land (o 9 2 c) 73)
         (l (o 9 0 c)) (l (o 9 1 c)) (l (o 9 2 c))
         (i (o 9 0 c)) (i (o 9 1 c)) (i (o 9 2 c))
       dsimp only at v ⊢;rw[K,v];have f0:=ed ⟨o 9 0 c,u 0⟩;have f1:=ed ⟨o 9 1 c,u 1⟩;have f2:=ed ⟨o 9 2 c,u 2⟩;dsimp only at f0 f1 f2;rw[f0.2.2.2.1,f0.2.2.2.2.1,f0.2.2.2.2.2.1,f1.2.2.2.1,f1.2.2.2.2.1,f1.2.2.2.2.2.1,f2.2.2.2.1,f2.2.2.2.2.1,f2.2.2.2.2.2.1];have a7:(o 9 0 c).testBit 0=B mB k 0 0 0:=h 0 0 0;have a6:(o 9 0 c).testBit 3=B mB k 0 1 0:=h 0 1 0;have a5:(o 9 0 c).testBit 6=B mB k 0 2 0:=h 0 2 0;have a4:(o 9 1 c).testBit 0=B mB k 1 0 0:=h 1 0 0;have a3:(o 9 1 c).testBit 3=B mB k 1 1 0:=h 1 1 0;have a2:(o 9 1 c).testBit 6=B mB k 1 2 0:=h 1 2 0;have a1:(o 9 2 c).testBit 0=B mB k 2 0 0:=h 2 0 0;have a0:(o 9 2 c).testBit 3=B mB k 2 1 0:=h 2 1 0;have W:(o 9 2 c).testBit 6=B mB k 2 2 0:=h 2 2 0;rw[a7,a6,a5,a4,a3,a2,a1,a0,W];change _=aK (B mB k) 0;unfold aK A aq;dsimp only;ring
     have L:let t1:=land (shiftRight c 1) 73+land (shiftRight c 10) 73+land (shiftRight c 19) 73
         land t1 7+land (shiftRight t1 3) 7+shiftRight t1 6=S mB k 2 1:=by
       have v:=w (land (shiftRight (o 9 0 c) 1) 73) (land (shiftRight (o 9 1 c) 1) 73) (land (shiftRight (o 9 2 c) 1) 73)
         (l _) (l _) (l _) (i _) (i _) (i _)
       dsimp only at v ⊢;rw[F,v];have f0:=ed ⟨o 9 0 c,u 0⟩;have f1:=ed ⟨o 9 1 c,u 1⟩;have f2:=ed ⟨o 9 2 c,u 2⟩;dsimp only at f0 f1 f2
       rw[f0.2.2.2.2.2.2.1,f0.2.2.2.2.2.2.2.1,f0.2.2.2.2.2.2.2.2,
           f1.2.2.2.2.2.2.1,f1.2.2.2.2.2.2.2.1,f1.2.2.2.2.2.2.2.2,
           f2.2.2.2.2.2.2.1,f2.2.2.2.2.2.2.2.1,f2.2.2.2.2.2.2.2.2]
       have a7:(o 9 0 c).testBit 1=B mB k 0 0 1:=h 0 0 1;have a6:(o 9 0 c).testBit 4=B mB k 0 1 1:=h 0 1 1;have a5:(o 9 0 c).testBit 7=B mB k 0 2 1:=h 0 2 1;have a4:(o 9 1 c).testBit 1=B mB k 1 0 1:=h 1 0 1;have a3:(o 9 1 c).testBit 4=B mB k 1 1 1:=h 1 1 1;have a2:(o 9 1 c).testBit 7=B mB k 1 2 1:=h 1 2 1;have a1:(o 9 2 c).testBit 1=B mB k 2 0 1:=h 2 0 1;have a0:(o 9 2 c).testBit 4=B mB k 2 1 1:=h 2 1 1;have W:(o 9 2 c).testBit 7=B mB k 2 2 1:=h 2 2 1;rw[a7,a6,a5,a4,a3,a2,a1,a0,W];change _=aK (B mB k) 1;unfold aK A aq;dsimp only;ring
     have htot:S mB k 0 0+S mB k 0 1+S mB k 0 2=S mB k 2 0+S mB k 2 1+S mB k 2 2:=
       (e8 (B mB k)).symm
     have b8:o 3 0 s=aq (B mB k) 0 0:=m 0 0;have b7:o 3 1 s=aq (B mB k) 0 1:=m 0 1;have b6:o 3 2 s=aq (B mB k) 0 2:=m 0 2;have b5:o 3 3 s=aq (B mB k) 1 0:=m 1 0;have b4:o 3 4 s=aq (B mB k) 1 1:=m 1 1;have b3:o 3 5 s=aq (B mB k) 1 2:=m 1 2;have b2:o 3 6 s=aq (B mB k) 2 0:=m 2 0;have b1:o 3 7 s=aq (B mB k) 2 1:=m 2 1;have b0:o 3 8 s=aq (B mB k) 2 2:=m 2 2;rw[bs,bb]
     change ((o 3 0 s+o 3 1 s+o 3 2 s,o 3 3 s+o 3 4 s+o 3 5 s,o 3 6 s+o 3 7 s+o 3 8 s),
             (o 3 0 s+o 3 3 s+o 3 6 s,o 3 1 s+o 3 4 s+o 3 7 s,o 3 2 s+o 3 5 s+o 3 8 s),
             (_,_,(o 3 0 s+o 3 1 s+o 3 2 s)+(o 3 3 s+o 3 4 s+o 3 5 s)+(o 3 6 s+o 3 7 s+o 3 8 s) - _ - _))=_
     rw[b8,b7,b6,b5,b4,b3,b2,b1,b0,M,L];simp only[Prod.mk.injEq];refine ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩,⟨trivial,trivial,?_⟩⟩;change S mB k 0 0+S mB k 0 1+S mB k 0 2 - S mB k 2 0 - S mB k 2 1=S mB k 2 2;omega
   . rw[bT];have bw:=bQ h0
     have z:∀ a b d:Fin 3,B mB k a b d=false:=fun a b d=>by rw[T a b d,bw];exact n4 _
     unfold S aK Z A aq;dsimp only;simp only[z,al];rfl
 . rw[bT];have ac:=bQ xK
   have z:∀ a b d:Fin 3,B mB k a b d=true:=fun a b d=>by
     rw[T a b d,ac];exact sk ⟨9*a.val+3*b.val+d.val,by omega⟩
   unfold S aK Z A aq;dsimp only;simp only[z,al];rfl
def eg (t:Nat × Nat × Nat):Nat:=let s:=D t.1 t.2.1 t.2.2;s.1+s.2.1*8+s.2.2*64
def eh (t:Nat × Nat × Nat):Nat:=let s:=D t.1 t.2.1 t.2.2;s.1+s.2.1*32+s.2.2*1024
def l9 (a:Nat) (t:Nat × Nat × Nat):Nat:=cond (nE a 0) 0 (eg t)
def iv (b:Nat) (t:Nat × Nat × Nat):Nat:=cond (nE b 27) 9513 (cond (nE b 0) 0 (eh t))
def gU (bs ar:Nat × Nat × Nat):Nat:=
 cond (!(nE bs.1 9&&!nE ar.1 0)&&
  !(nE bs.2.1 9&&!nE ar.2.1 0)&&
  !(nE bs.2.2 9&&!nE ar.2.2 0)) 1 0
def lb (a:Nat) (b0 b1 b2 ar:Nat × Nat × Nat):Nat:=
 cond (nE a 0) 7 (gU b0 ar+gU b1 ar*2+gU b2 ar*4)
def iY (getR getC:Nat->Nat × Nat × Nat) (getB:Nat->Nat->Nat × Nat × Nat):Nat:=
 let a:=fun e=>gU (getB ((e+4) % 5) 0) (getR e)+gU (getB ((e+2) % 5) 1) (getR e)*2+gU (getB ((e+1) % 5) 2) (getR e)*4;let b:=fun e=>let c:=(e+1) % 5;gU (getB ((c+4) % 5) 0) (getC e)+gU (getB ((c+2) % 5) 1) (getC e)*2+gU (getB ((c+1) % 5) 2) (getC e)*4;let d:=a 0+a 1*8+a 2*64+a 3*512+a 4*4096;let h:=b 0+b 1*8+b 2*64+b 3*512+b 4*4096
 d+h*32768
def fX (g0 g1 g2 g3 g4:Nat × Nat × Nat × Nat × Nat × Nat)
  (c0 c1 c2 c3 c4:(Nat × Nat × Nat) × (Nat × Nat × Nat) × (Nat × Nat × Nat)):RL:=
 let h:=g0.1+g0.2.1+g0.2.2.1;let d:=g1.1+g1.2.1+g1.2.2.1;let c:=g2.1+g2.2.1+g2.2.2.1;let b:=g3.1+g3.2.1+g3.2.2.1;let a:=g4.1+g4.2.1+g4.2.2.1;let m:=c0.1.1+c0.1.2.1+c0.1.2.2;let l:=c1.1.1+c1.1.2.1+c1.1.2.2;let k:=c2.1.1+c2.1.2.1+c2.1.2.2;let j:=c3.1.1+c3.1.2.1+c3.1.2.2;let i:=c4.1.1+c4.1.2.1+c4.1.2.2;let z:=h+d*32+c*1024+b*32768+a*1048576;let y:=m+l*64+k*4096+j*262144+i*16777216;let r0:=(g0.1,g0.2.1,g0.2.2.1);let r1:=(g1.1,g1.2.1,g1.2.2.1);let r2:=(g2.1,g2.2.1,g2.2.2.1);let r3:=(g3.1,g3.2.1,g3.2.2.1);let r4:=(g4.1,g4.2.1,g4.2.2.1);let x:=(g0.2.2.2.1,g0.2.2.2.2.1,g0.2.2.2.2.2);let w:=(g1.2.2.2.1,g1.2.2.2.2.1,g1.2.2.2.2.2);let v:=(g2.2.2.2.1,g2.2.2.2.2.1,g2.2.2.2.2.2);let u:=(g3.2.2.2.1,g3.2.2.2.2.1,g3.2.2.2.2.2);let t:=(g4.2.2.2.1,g4.2.2.2.2.1,g4.2.2.2.2.2);let n:=l9 h r0+l9 d r1*512+l9 c r2*262144+l9 b r3*134217728+l9 a r4*68719476736;let r:=l9 h x+l9 d w*512+l9 c v*262144+l9 b u*134217728+l9 a t*68719476736;let bf:=iv m c0.1+iv l c1.1*32768+iv k c2.1*1073741824+iv j c3.1*35184372088832+iv i c4.1*0x1000000000000000
 let be:=iv m c0.2.1+iv l c1.2.1*32768+iv k c2.2.1*1073741824+iv j c3.2.1*35184372088832+iv i c4.2.1*0x1000000000000000;let bd:=iv m c0.2.2+iv l c1.2.2*32768+iv k c2.2.2*1073741824+iv j c3.2.2*35184372088832+iv i c4.2.2*0x1000000000000000
 let C:=lb h c4.1 c2.2.1 c1.2.2 r0+lb d c0.1 c3.2.1 c2.2.2 r1*8 +
   lb c c1.1 c4.2.1 c3.2.2 r2*64+lb b c2.1 c0.2.1 c4.2.2 r3*512+lb a c3.1 c1.2.1 c0.2.2 r4*4096
 let F:=lb h c0.1 c3.2.1 c2.2.2 x+lb d c1.1 c4.2.1 c3.2.2 w*8 +
   lb c c2.1 c0.2.1 c4.2.2 v*64+lb b c3.1 c1.2.1 c0.2.2 u*512+lb a c4.1 c2.2.1 c1.2.2 t*4096
 ((h+d+c+b+a,m+l+k+j+i,z,y,n,r,bf,be,bd),C+F*32768)
def mw (mA mB:Nat):RL:=
 let b:=land mA 0x49249249249+land (shiftRight mA 1) 0x49249249249+land (shiftRight mA 2) 0x49249249249
 let a:=land mB 0x1249249249249249249249249249249249 +
   land (shiftRight mB 1) 0x1249249249249249249249249249249249 +
   land (shiftRight mB 2) 0x1249249249249249249249249249249249
 fX
  (eM (land mA 511) (land b 511))
  (eM (land (shiftRight mA 9) 511) (land (shiftRight b 9) 511))
  (eM (land (shiftRight mA 18) 511) (land (shiftRight b 18) 511))
  (eM (land (shiftRight mA 27) 511) (land (shiftRight b 27) 511))
  (eM (shiftRight mA 36) (shiftRight b 36))
  (dx (land mB 134217727) (land a 134217727))
  (dx (land (shiftRight mB 27) 134217727) (land (shiftRight a 27) 134217727))
  (dx (land (shiftRight mB 54) 134217727) (land (shiftRight a 54) 134217727))
  (dx (land (shiftRight mB 81) 134217727) (land (shiftRight a 81) 134217727))
  (dx (shiftRight mB 108) (shiftRight a 108))
lemma xl (a d c b:Nat) (h:a=d+c+b):l9 a (d,c,b)=eg (d,c,b):=by
 unfold l9;cases hb:nE a 0
 . rfl
 . have h0:=bQ hb
   have i:d=0/\c=0/\b=0:=by omega
   rw[i.1,i.2.1,i.2.2];rfl
lemma sE (b i d c:Nat) (h:b=i+d+c) (h0:i<=9) (h1:d<=9) (h2:c<=9) :
   iv b (i,d,c)=eh (i,d,c):=by
 unfold iv;cases xK:nE b 27
 . simp only[bC];cases hz:nE b 0
   . rfl
   . have hb0:=bQ hz
     have a:i=0/\d=0/\c=0:=by omega
     rw[a.1,a.2.1,a.2.2];rfl
 . have hb27:=bQ xK
   have a:i=9/\d=9/\c=9:=by omega
   rw[a.1,a.2.1,a.2.2];simp only[bT];decide
lemma xr (a:Nat) (m l k:Nat × Nat × Nat) (d c b:Nat) (h:a=d+c+b) :
   lb a m l k (d,c,b)=gU m (d,c,b)+gU l (d,c,b)*2+gU k (d,c,b)*4:=by
 unfold lb;cases hb:nE a 0
 . rfl
 . have h0:=bQ hb
   have i:d=0/\c=0/\b=0:=by omega
   rw[i.1,i.2.1,i.2.2];have j:(!nE 0 0)=false:=rfl;simp only[gU,j,bX,bZ,bU,bT]
lemma kf (f:Fin 5->Fin 3->Nat) (u:∀ e k,f e k<=3) :
   let w:=eg (f 0 0,f 0 1,f 0 2)+eg (f 1 0,f 1 1,f 1 2)*512+eg (f 2 0,f 2 1,f 2 2)*262144 +
            eg (f 3 0,f 3 1,f 3 2)*134217728+eg (f 4 0,f 4 1,f 4 2)*68719476736
   cq w/\bg w (fun e=>D (f e 0) (f e 1) (f e 2)):=by
 have b:∀ e:Fin 5,eg (f e 0,f e 1,f e 2)<2^9/\
     (∀ c<3,o 3 c (eg (f e 0,f e 1,f e 2))<=3)/\
     o 3 0 (eg (f e 0,f e 1,f e 2))=(D (f e 0) (f e 1) (f e 2)).1/\
     o 3 1 (eg (f e 0,f e 1,f e 2))=(D (f e 0) (f e 1) (f e 2)).2.1/\
     o 3 2 (eg (f e 0,f e 1,f e 2))=(D (f e 0) (f e 1) (f e 2)).2.2:=by
   intro e;have h0:=u e 0;have h1:=u e 1;have h2:=u e 2
   have v:(D (f e 0) (f e 1) (f e 2)).1<=3/\(D (f e 0) (f e 1) (f e 2)).2.1<=3/\(D (f e 0) (f e 1) (f e 2)).2.2<=3:=by
     simp only[D,aG,aP];omega
   rcases v with ⟨hs0,hs1,hs2⟩;have d:=fd 3 (D (f e 0) (f e 1) (f e 2)).1 (D (f e 0) (f e 1) (f e 2)).2.1 (D (f e 0) (f e 1) (f e 2)).2.2 (by omega) (by omega) (by omega);have t:=gG 3 (D (f e 0) (f e 1) (f e 2)).1 (D (f e 0) (f e 1) (f e 2)).2.1 (D (f e 0) (f e 1) (f e 2)).2.2 (by omega) (by omega) (by omega);have j:eg (f e 0,f e 1,f e 2)=bE 3 (D (f e 0) (f e 1) (f e 2)).1 (D (f e 0) (f e 1) (f e 2)).2.1 (D (f e 0) (f e 1) (f e 2)).2.2:=rfl;rw[j];refine ⟨t,fun c hc=>?_,d.1,d.2.1,d.2.2⟩
   have:c=0\/c=1\/c=2:=by omega
   rcases this with rfl|rfl|rfl
   . rw[d.1];omega
   . rw[d.2.1];omega
   . rw[d.2.2];omega
 have h5:=cv 9 (eg (f 0 0,f 0 1,f 0 2)) (eg (f 1 0,f 1 1,f 1 2)) (eg (f 2 0,f 2 1,f 2 2))
   (eg (f 3 0,f 3 1,f 3 2)) (eg (f 4 0,f 4 1,f 4 2)) (b 0).1 (b 1).1 (b 2).1 (b 3).1 (b 4).1
 have r:=dl 9 (eg (f 0 0,f 0 1,f 0 2)) (eg (f 1 0,f 1 1,f 1 2)) (eg (f 2 0,f 2 1,f 2 2))
   (eg (f 3 0,f 3 1,f 3 2)) (eg (f 4 0,f 4 1,f 4 2)) (b 0).1 (b 1).1 (b 2).1 (b 3).1 (b 4).1
 have a:∀ (e:Fin 5) (c:Fin 3),o 3 (3*e.val+c.val)
     (bM 9 (eg (f 0 0,f 0 1,f 0 2)) (eg (f 1 0,f 1 1,f 1 2)) (eg (f 2 0,f 2 1,f 2 2))
       (eg (f 3 0,f 3 1,f 3 2)) (eg (f 4 0,f 4 1,f 4 2)))=o 3 c.val (eg (f e 0,f e 1,f e 2)):=fun e c=>by
   rw[<- aY 3 c.val e.val _ c.isLt];congr 1
   have:e=0\/e=1\/e=2\/e=3\/e=4:=by fin_cases e <;> simp
   rcases this with rfl|rfl|rfl|rfl|rfl
   . exact h5.1
   . exact h5.2.1
   . exact h5.2.2.1
   . exact h5.2.2.2.1
   . exact h5.2.2.2.2
 change cq (bM 9 (eg (f 0 0,f 0 1,f 0 2)) (eg (f 1 0,f 1 1,f 1 2)) (eg (f 2 0,f 2 1,f 2 2))
     (eg (f 3 0,f 3 1,f 3 2)) (eg (f 4 0,f 4 1,f 4 2)))/\
   bg (bM 9 (eg (f 0 0,f 0 1,f 0 2)) (eg (f 1 0,f 1 1,f 1 2)) (eg (f 2 0,f 2 1,f 2 2))
     (eg (f 3 0,f 3 1,f 3 2)) (eg (f 4 0,f 4 1,f 4 2))) _
 refine ⟨⟨fun i hi=>?_,r⟩,fun e=>?_⟩
 . have h:=a ⟨i/3,by omega⟩ ⟨i % 3,by omega⟩
   have l:3*(i/3)+i % 3=i:=by omega
   rw[l] at h;rw[h];exact (b ⟨i/3,by omega⟩).2.1 (i % 3) (by omega)
 . have gK:=a e 0;simp only[Fin.val_zero,nZ] at gK;have eW:=a e 1;have n:(1:Fin 3).val=1:=rfl;rw[n] at eW;have fj:=a e 2;have m:(2:Fin 3).val=2:=rfl;rw[m] at fj;rw[gK,eW,fj,(b e).2.2.1,(b e).2.2.2.1,(b e).2.2.2.2];exact ⟨lR _,lR _,lR _⟩
lemma hQ (f:Fin 5->Fin 3->Nat) (v:∀ s k,f s k<=9) :
   let w:=eh (f 0 0,f 0 1,f 0 2)+eh (f 1 0,f 1 1,f 1 2)*32768+eh (f 2 0,f 2 1,f 2 2)*1073741824 +
            eh (f 3 0,f 3 1,f 3 2)*35184372088832+eh (f 4 0,f 4 1,f 4 2)*0x1000000000000000
   az w/\ag w (fun s=>D (f s 0) (f s 1) (f s 2)):=by
 have b:∀ s:Fin 5,eh (f s 0,f s 1,f s 2)<2^15/\
     (∀ c<3,o 5 c (eh (f s 0,f s 1,f s 2))<=9)/\
     o 5 0 (eh (f s 0,f s 1,f s 2))=(D (f s 0) (f s 1) (f s 2)).1/\
     o 5 1 (eh (f s 0,f s 1,f s 2))=(D (f s 0) (f s 1) (f s 2)).2.1/\
     o 5 2 (eh (f s 0,f s 1,f s 2))=(D (f s 0) (f s 1) (f s 2)).2.2:=by
   intro s;have h0:=v s 0;have h1:=v s 1;have h2:=v s 2
   have r:(D (f s 0) (f s 1) (f s 2)).1<=9/\(D (f s 0) (f s 1) (f s 2)).2.1<=9/\(D (f s 0) (f s 1) (f s 2)).2.2<=9:=by
     simp only[D,aG,aP];omega
   rcases r with ⟨hs0,hs1,hs2⟩;have d:=fd 5 (D (f s 0) (f s 1) (f s 2)).1 (D (f s 0) (f s 1) (f s 2)).2.1 (D (f s 0) (f s 1) (f s 2)).2.2 (by omega) (by omega) (by omega);have u:=gG 5 (D (f s 0) (f s 1) (f s 2)).1 (D (f s 0) (f s 1) (f s 2)).2.1 (D (f s 0) (f s 1) (f s 2)).2.2 (by omega) (by omega) (by omega);have j:eh (f s 0,f s 1,f s 2)=bE 5 (D (f s 0) (f s 1) (f s 2)).1 (D (f s 0) (f s 1) (f s 2)).2.1 (D (f s 0) (f s 1) (f s 2)).2.2:=rfl;rw[j];refine ⟨u,fun c hc=>?_,d.1,d.2.1,d.2.2⟩
   have:c=0\/c=1\/c=2:=by omega
   rcases this with rfl|rfl|rfl
   . rw[d.1];omega
   . rw[d.2.1];omega
   . rw[d.2.2];omega
 have h5:=cv 15 (eh (f 0 0,f 0 1,f 0 2)) (eh (f 1 0,f 1 1,f 1 2)) (eh (f 2 0,f 2 1,f 2 2))
   (eh (f 3 0,f 3 1,f 3 2)) (eh (f 4 0,f 4 1,f 4 2)) (b 0).1 (b 1).1 (b 2).1 (b 3).1 (b 4).1
 have t:=dl 15 (eh (f 0 0,f 0 1,f 0 2)) (eh (f 1 0,f 1 1,f 1 2)) (eh (f 2 0,f 2 1,f 2 2))
   (eh (f 3 0,f 3 1,f 3 2)) (eh (f 4 0,f 4 1,f 4 2)) (b 0).1 (b 1).1 (b 2).1 (b 3).1 (b 4).1
 have a:∀ (s:Fin 5) (c:Fin 3),o 5 (3*s.val+c.val)
     (bM 15 (eh (f 0 0,f 0 1,f 0 2)) (eh (f 1 0,f 1 1,f 1 2)) (eh (f 2 0,f 2 1,f 2 2))
       (eh (f 3 0,f 3 1,f 3 2)) (eh (f 4 0,f 4 1,f 4 2)))=o 5 c.val (eh (f s 0,f s 1,f s 2)):=fun s c=>by
   rw[<- aY 5 c.val s.val _ c.isLt];congr 1
   have:s=0\/s=1\/s=2\/s=3\/s=4:=by fin_cases s <;> simp
   rcases this with rfl|rfl|rfl|rfl|rfl
   . exact h5.1
   . exact h5.2.1
   . exact h5.2.2.1
   . exact h5.2.2.2.1
   . exact h5.2.2.2.2
 change az (bM 15 (eh (f 0 0,f 0 1,f 0 2)) (eh (f 1 0,f 1 1,f 1 2)) (eh (f 2 0,f 2 1,f 2 2))
     (eh (f 3 0,f 3 1,f 3 2)) (eh (f 4 0,f 4 1,f 4 2)))/\
   ag (bM 15 (eh (f 0 0,f 0 1,f 0 2)) (eh (f 1 0,f 1 1,f 1 2)) (eh (f 2 0,f 2 1,f 2 2))
     (eh (f 3 0,f 3 1,f 3 2)) (eh (f 4 0,f 4 1,f 4 2))) _
 refine ⟨⟨fun i hi=>?_,t⟩,fun s=>?_⟩
 . have h:=a ⟨i/3,by omega⟩ ⟨i % 3,by omega⟩
   have l:3*(i/3)+i % 3=i:=by omega
   rw[l] at h;rw[h];exact (b ⟨i/3,by omega⟩).2.1 (i % 3) (by omega)
 . have gK:=a s 0;simp only[Fin.val_zero,nZ] at gK;have eW:=a s 1;have n:(1:Fin 3).val=1:=rfl;rw[n] at eW;have fj:=a s 2;have m:(2:Fin 3).val=2:=rfl;rw[m] at fj;rw[gK,eW,fj,(b s).2.2.1,(b s).2.2.2.1,(b s).2.2.2.2];exact ⟨lR _,lR _,lR _⟩
lemma iS (f:Nat->Nat->Nat) (b:∀ e ax,f e ax<2) :
  let g:=fun e=>bE 1 (f e 0) (f e 1) (f e 2)
  bM 3 (g 0) (g 1) (g 2) (g 3) (g 4)<2^15:=by
 intro g;have a:∀ e,g e<2^3:=fun e=>gG 1 _ _ _ (b e 0) (b e 1) (b e 2);exact dl 3 _ _ _ _ _ (a 0) (a 1) (a 2) (a 3) (a 4)
lemma g5 (f:Nat->Nat->Nat) (c:∀ e ax,f e ax<2) (e:Fin 5) (ax:Fin 3) :
   let g:=fun e=>bE 1 (f e 0) (f e 1) (f e 2)
   (bM 3 (g 0) (g 1) (g 2) (g 3) (g 4)).testBit (3*e.val+ax.val)=decide (f e.val ax.val=1):=by
 intro g;have d:∀ i,g i<2^3:=fun i=>gG 1 _ _ _ (c i 0) (c i 1) (c i 2);have h5:=cv 3 (g 0) (g 1) (g 2) (g 3) (g 4) (d 0) (d 1) (d 2) (d 3) (d 4)
 have j:o 3 e.val (bM 3 (g 0) (g 1) (g 2) (g 3) (g 4))=g e.val:=by
   have:e=0\/e=1\/e=2\/e=3\/e=4:=by fin_cases e <;> simp
   rcases this with rfl|rfl|rfl|rfl|rfl
   . exact h5.1
   . exact h5.2.1
   . exact h5.2.2.1
   . exact h5.2.2.2.1
   . exact h5.2.2.2.2
 have b:=congrArg (fun z=>z.testBit ax.val) j;rw[U] at b;simp only[ax.isLt,dT,bTA] at b;rw[b];have h3:=fd 1 (f e.val 0) (f e.val 1) (f e.val 2) (c e.val 0) (c e.val 1) (c e.val 2)
 have k:o 1 ax.val (g e.val)=f e.val ax.val:=by
   have:ax=0\/ax=1\/ax=2:=by fin_cases ax <;> simp
   rcases this with rfl|rfl|rfl
   . exact h3.1
   . exact h3.2.1
   . exact h3.2.2
 have a:=congrArg (fun z=>z.testBit 0) k;rw[U] at a
 simp only[show 0<1 by omega,dT,bTA,n1,nZ] at a
 rw[a];have hlt:=c e.val ax.val
 have:f e.val ax.val=0\/f e.val ax.val=1:=by omega
 rcases this with h|h <;> simp[h]
lemma uM (a b:Nat × Nat × Nat):gU a b<2:=by
 unfold gU;cases (!(nE a.1 9&&!nE b.1 0)&&
  !(nE a.2.1 9&&!nE b.2.1 0)&&
  !(nE a.2.2 9&&!nE b.2.2 0)) <;> decide
lemma ld {a b:Nat × Nat × Nat} (h:gU a b=1) :
   (a.1=9->b.1=0)/\(a.2.1=9->b.2.1=0)/\(a.2.2=9->b.2.2=0):=by
 unfold gU at h
 cases hc:(!(nE a.1 9&&!nE b.1 0)&&
             !(nE a.2.1 9&&!nE b.2.1 0)&&
             !(nE a.2.2 9&&!nE b.2.2 0))
 . rw[hc] at h;cases h
 . simp only[bA,Bool.not_eq_true',Bool.and_eq_false_iff,Bool.not_eq_false'] at hc;refine ⟨fun h1=>?_,fun h2=>?_,fun h3=>?_⟩
   . rcases hc.1.1 with hb|ha
     . rw[h1] at hb;cases hb
     . exact bQ ha
   . rcases hc.1.2 with hb|ha
     . rw[h2] at hb;cases hb
     . exact bQ ha
   . rcases hc.2 with hb|ha
     . rw[h3] at hb;cases hb
     . exact bQ ha
lemma nv (mA mB:Nat)
   (d h:Nat->Nat × Nat × Nat) (c:Nat->Nat->Nat × Nat × Nat)
   (n:∀ e:Fin 5,d e.val=(am mA e 0,am mA e 1,am mA e 2))
   (r:∀ e:Fin 5,h e.val=(aR mA e 0,aR mA e 1,aR mA e 2))
   (l:∀ (s:Fin 5) (ax:Fin 3),c s.val ax.val=(S mB s ax 0,S mB s ax 1,S mB s ax 2)) :
   iY d h c<2^30/\
   (∀ (e:Fin 5) (ax:Fin 3),(iY d h c).testBit (3*e.val+ax.val)=true->lY mA mB e ax=true)/\
   (∀ (e:Fin 5) (ax:Fin 3),(iY d h c).testBit (15+3*e.val+ax.val)=true->m4 mA mB e ax=true):=by
 let a:Nat->Nat->Nat:=fun e ax=>gU (c ((e+gr ax) % 5) ax) (d e);let b:Nat->Nat->Nat:=fun e ax=>gU (c (((e+1) % 5+gr ax) % 5) ax) (h e);have t:∀ e ax,a e ax<2:=fun e ax=>uM _ _;have u:∀ e ax,b e ax<2:=fun e ax=>uM _ _
 have j:bM 3 (bE 1 (a 0 0) (a 0 1) (a 0 2)) (bE 1 (a 1 0) (a 1 1) (a 1 2))
     (bE 1 (a 2 0) (a 2 1) (a 2 2)) (bE 1 (a 3 0) (a 3 1) (a 3 2))
     (bE 1 (a 4 0) (a 4 1) (a 4 2))<2^15:=iS a t
 have hlc_lt:bM 3 (bE 1 (b 0 0) (b 0 1) (b 0 2)) (bE 1 (b 1 0) (b 1 1) (b 1 2))
     (bE 1 (b 2 0) (b 2 1) (b 2 2)) (bE 1 (b 3 0) (b 3 1) (b 3 2))
     (bE 1 (b 4 0) (b 4 1) (b 4 2))<2^15:=iS b u
 have m:iY d h c =
     bM 3 (bE 1 (a 0 0) (a 0 1) (a 0 2)) (bE 1 (a 1 0) (a 1 1) (a 1 2))
       (bE 1 (a 2 0) (a 2 1) (a 2 2)) (bE 1 (a 3 0) (a 3 1) (a 3 2))
       (bE 1 (a 4 0) (a 4 1) (a 4 2)) +
     bM 3 (bE 1 (b 0 0) (b 0 1) (b 0 2)) (bE 1 (b 1 0) (b 1 1) (b 1 2))
       (bE 1 (b 2 0) (b 2 1) (b 2 2)) (bE 1 (b 3 0) (b 3 1) (b 3 2))
       (bE 1 (b 4 0) (b 4 1) (b 4 2))*2^15:=rfl
 rw[m]
 refine ⟨by omega,?_,?_⟩
 . intro e ax hb;rw[eL 15 _ _ (3*e.val+ax.val) j] at hb
   simp only[show 3*e.val+ax.val<15 by omega,↓reduceIte] at hb
   rw[g5 a t e ax] at hb;have h1:a e.val ax.val=1:=of_decide_eq_true hb;dsimp only[a] at h1
   have v:(e.val+gr ax.val) % 5=(⟨(e.val+cH ax) % 5,by omega⟩:Fin 5).val:=by
     dsimp only;rw[pP ax.val ax.isLt]
   rw[v,l ⟨(e.val+cH ax) % 5,by omega⟩ ax,n e] at h1
   have i:=ld h1;unfold lY;rw[decide_eq_true_iff];intro k hk
   have:k=0\/k=1\/k=2:=by fin_cases k <;> simp
   rcases this with rfl|rfl|rfl
   . exact i.1 hk
   . exact i.2.1 hk
   . exact i.2.2 hk
 . intro e ax hb;rw[eL 15 _ _ (15+3*e.val+ax.val) j] at hb
   simp only[show ¬ (15+3*e.val+ax.val<15) by omega,↓reduceIte,
     show 15+3*e.val+ax.val - 15=3*e.val+ax.val by omega] at hb
   rw[g5 b u e ax] at hb;have h1:b e.val ax.val=1:=of_decide_eq_true hb;dsimp only[b] at h1
   have v:((e.val+1) % 5+gr ax.val) % 5=(⟨((e.val+1) % 5+cH ax) % 5,by omega⟩:Fin 5).val:=by
     dsimp only;rw[pP ax.val ax.isLt]
   rw[v,l ⟨((e.val+1) % 5+cH ax) % 5,by omega⟩ ax,r e] at h1
   have i:=ld h1;unfold m4;rw[decide_eq_true_iff];intro k hk
   have:k=0\/k=1\/k=2:=by fin_cases k <;> simp
   rcases this with rfl|rfl|rfl
   . exact i.1 hk
   . exact i.2.1 hk
   . exact i.2.2 hk
lemma mG (mA mB:Nat) :
  let g:=fun e:Fin 5=>(am mA e 0,am mA e 1,am mA e 2,aR mA e 0,aR mA e 1,aR mA e 2)
  let c:=fun s:Fin 5=>((S mB s 0 0,S mB s 0 1,S mB s 0 2),
      (S mB s 1 0,S mB s 1 1,S mB s 1 2),
      (S mB s 2 0,S mB s 2 1,S mB s 2 2))
  gw (fX (g 0) (g 1) (g 2) (g 3) (g 4) (c 0) (c 1) (c 2) (c 3) (c 4))/\
  dj (fX (g 0) (g 1) (g 2) (g 3) (g 4) (c 0) (c 1) (c 2) (c 3) (c 4)) mA mB:=by
 intro g c
 have b:∀ e:Fin 5,bk mA e<=am mA e 0+am mA e 1+am mA e 2/\
   am mA e 0+am mA e 1+am mA e 2<=9:=fun e=>by
  have h9:=vb mA e;unfold bk gz at h9 ⊢;unfold am;omega
 have y:=iE mA _ _ _ _ _ (b 0) (b 1) (b 2) (b 3) (b 4);have a:∀ s:Fin 5,S mB s 0 0+S mB s 0 1+S mB s 0 2<=cw mB s:=fun s=>lR _;have x:=iD mB _ _ _ _ _ (a 0) (a 1) (a 2) (a 3) (a 4)
 have t:am mA 0 0+am mA 0 1+am mA 0 2 +
   (am mA 1 0+am mA 1 1+am mA 1 2) +
   (am mA 2 0+am mA 2 1+am mA 2 2) +
   (am mA 3 0+am mA 3 1+am mA 3 2) +
   (am mA 4 0+am mA 4 1+am mA 4 2) =
   bD (bM 5 (am mA 0 0+am mA 0 1+am mA 0 2) (am mA 1 0+am mA 1 1+am mA 1 2)
    (am mA 2 0+am mA 2 1+am mA 2 2) (am mA 3 0+am mA 3 1+am mA 3 2)
    (am mA 4 0+am mA 4 1+am mA 4 2)):=by
  rw[fz _ y.1]
  have d:=cv 5 (am mA 0 0+am mA 0 1+am mA 0 2) (am mA 1 0+am mA 1 1+am mA 1 2)
   (am mA 2 0+am mA 2 1+am mA 2 2) (am mA 3 0+am mA 3 1+am mA 3 2)
   (am mA 4 0+am mA 4 1+am mA 4 2)
   (by have:=(b 0).2;omega) (by have:=(b 1).2;omega) (by have:=(b 2).2;omega)
   (by have:=(b 3).2;omega) (by have:=(b 4).2;omega)
  rw[d.1,d.2.1,d.2.2.1,d.2.2.2.1,d.2.2.2.2]
 have r:S mB 0 0 0+S mB 0 0 1+S mB 0 0 2 +
   (S mB 1 0 0+S mB 1 0 1+S mB 1 0 2) +
   (S mB 2 0 0+S mB 2 0 1+S mB 2 0 2) +
   (S mB 3 0 0+S mB 3 0 1+S mB 3 0 2) +
   (S mB 4 0 0+S mB 4 0 1+S mB 4 0 2) =
   bG (bM 6 (S mB 0 0 0+S mB 0 0 1+S mB 0 0 2) (S mB 1 0 0+S mB 1 0 1+S mB 1 0 2)
    (S mB 2 0 0+S mB 2 0 1+S mB 2 0 2) (S mB 3 0 0+S mB 3 0 1+S mB 3 0 2)
    (S mB 4 0 0+S mB 4 0 1+S mB 4 0 2)):=by
  rw[fy _ x.1]
  have d:=cv 6 (S mB 0 0 0+S mB 0 0 1+S mB 0 0 2) (S mB 1 0 0+S mB 1 0 1+S mB 1 0 2)
   (S mB 2 0 0+S mB 2 0 1+S mB 2 0 2) (S mB 3 0 0+S mB 3 0 1+S mB 3 0 2)
   (S mB 4 0 0+S mB 4 0 1+S mB 4 0 2)
   (by have:=bV mB 0;have:=a 0;omega) (by have:=bV mB 1;have:=a 1;omega)
   (by have:=bV mB 2;have:=a 2;omega) (by have:=bV mB 3;have:=a 3;omega)
   (by have:=bV mB 4;have:=a 4;omega)
  rw[d.1,d.2.1,d.2.2.1,d.2.2.2.1,d.2.2.2.2]
 have l:=kf (am mA) (fun e k=>gC (ao mA e) k);have m:=kf (aR mA) (fun e k=>by unfold aR;rw[<- lJ];exact gC _ k);have j:=hQ (fun s k=>S mB s 0 k) (fun s k=>bS _ k);have i:=hQ (fun s k=>S mB s 1 k) (fun s k=>by change Z (B mB s) k<=9;rw[<- aT];exact bS _ k);have h:=hQ (fun s k=>S mB s 2 k) (fun s k=>by change aK (B mB s) k<=9;exact bS _ k)
 have z:=nv mA mB
  (fun e=>match e with|0=>((g 0).1,(g 0).2.1,(g 0).2.2.1)|1=>((g 1).1,(g 1).2.1,(g 1).2.2.1)|2=>((g 2).1,(g 2).2.1,(g 2).2.2.1)|3=>((g 3).1,(g 3).2.1,(g 3).2.2.1)|_=>((g 4).1,(g 4).2.1,(g 4).2.2.1))
  (fun e=>match e with|0=>((g 0).2.2.2.1,(g 0).2.2.2.2.1,(g 0).2.2.2.2.2)|1=>((g 1).2.2.2.1,(g 1).2.2.2.2.1,(g 1).2.2.2.2.2)|2=>((g 2).2.2.2.1,(g 2).2.2.2.2.1,(g 2).2.2.2.2.2)|3=>((g 3).2.2.2.1,(g 3).2.2.2.2.1,(g 3).2.2.2.2.2)|_=>((g 4).2.2.2.1,(g 4).2.2.2.2.1,(g 4).2.2.2.2.2))
  (fun s ax=>let K:=match s with|0=>c 0|1=>c 1|2=>c 2|3=>c 3|_=>c 4;match ax with|0=>K.1|1=>K.2.1|_=>K.2.2)
  (fun e=>by fin_cases e <;> rfl)
  (fun e=>by fin_cases e <;> rfl)
  (fun s ax=>by fin_cases s <;> fin_cases ax <;> rfl)
 have n:∀ e:Fin 5,am mA e 0+am mA e 1+am mA e 2=aR mA e 0+aR mA e 1+aR mA e 2:=
  fun e=>gM (ao mA e)
 have F:∀ s:Fin 5,S mB s 0 0+S mB s 0 1+S mB s 0 2=S mB s 1 0+S mB s 1 1+S mB s 1 2:=
  fun s=>(fx (B mB s)).symm
 have C:∀ s:Fin 5,S mB s 0 0+S mB s 0 1+S mB s 0 2=S mB s 2 0+S mB s 2 1+S mB s 2 2:=
  fun s=>(e8 (B mB s)).symm
 have w:∀ s k,S mB s 0 k<=9:=fun s k=>bS _ k
 have v:∀ s k,S mB s 1 k<=9:=fun s k=>by change Z (B mB s) k<=9;rw[<- aT];exact bS _ k
 have u:∀ s k,S mB s 2 k<=9:=fun s k=>by change aK (B mB s) k<=9;exact bS _ k
 unfold fX;dsimp only[g,c]
 simp only[xl _ _ _ _ rfl,xl _ _ _ _ (n _),
  sE _ _ _ _ rfl (w _ 0) (w _ 1) (w _ 2),
  sE _ _ _ _ (F _) (v _ 0) (v _ 1) (v _ 2),
  sE _ _ _ _ (C _) (u _ 0) (u _ 1) (u _ 2),
  xr _ _ _ _ _ _ _ rfl,xr _ _ _ _ _ _ _ (n _)]
 exact ⟨⟨⟨y.1,x.1,l.1,m.1,j.1,i.1,h.1,t,r⟩,z.1⟩,
     ⟨⟨y.2,x.2,l.2,m.2,j.2,i.2,h.2⟩,z.2.1,z.2.2⟩⟩
lemma mS {mA mB:Nat} (P:mA<2^45) (N:mB<2^135) :
  gw (mw mA mB)/\dj (mw mA mB) mA mB:=by
 set a:=land mA 0x49249249249+land (shiftRight mA 1) 0x49249249249+land (shiftRight mA 2) 0x49249249249
 set b:=land mB 0x1249249249249249249249249249249249 +
    land (shiftRight mB 1) 0x1249249249249249249249249249249249 +
    land (shiftRight mB 2) 0x1249249249249249249249249249249249
 have d:a<2^45:=
  lO (nA (nA nR nR) nR) (by decide)
 have c:b<2^135:=
  lO (nA (nA nR nR) nR) (by decide)
 have t:land mA 511=o 9 0 mA:=by unfold o;simp
 have l:land a 511=o 9 0 a:=by unfold o;simp
 have r:shiftRight mA 36=o 9 4 mA:=by rw[bB 9 4 mA P];exact nD mA 36
 have k:shiftRight a 36=o 9 4 a:=by rw[bB 9 4 a d];exact nD a 36
 have n:land mB 134217727=o 27 0 mB:=by unfold o;simp
 have j:land b 134217727=o 27 0 b:=by unfold o;simp
 have m:shiftRight mB 108=o 27 4 mB:=by rw[bB 27 4 mB N];exact nD mB 108
 have i:shiftRight b 108=o 27 4 b:=by rw[bB 27 4 b c];exact nD b 108
 have u:∀ e:Fin 5,eM (o 9 e.val mA) (o 9 e.val a) =
   (am mA e 0,am mA e 1,am mA e 2,aR mA e 0,aR mA e 1,aR mA e 2):=fun e=>by
  rw[vB mA e];exact Co mA e
 have h:mw mA mB=fX
   (eM (o 9 0 mA) (o 9 0 a)) (eM (o 9 1 mA) (o 9 1 a))
   (eM (o 9 2 mA) (o 9 2 a)) (eM (o 9 3 mA) (o 9 3 a)) (eM (o 9 4 mA) (o 9 4 a))
   (dx (o 27 0 mB) (o 27 0 b)) (dx (o 27 1 mB) (o 27 1 b))
   (dx (o 27 2 mB) (o 27 2 b)) (dx (o 27 3 mB) (o 27 3 b)) (dx (o 27 4 mB) (o 27 4 b)):=by
  unfold mw;dsimp only;rw[t,l,r,k,n,j,m,i];rfl
 rw[h];have z:eM (o 9 0 mA) (o 9 0 a)=(am mA 0 0,am mA 0 1,am mA 0 2,aR mA 0 0,aR mA 0 1,aR mA 0 2):=u 0;have y:eM (o 9 1 mA) (o 9 1 a)=(am mA 1 0,am mA 1 1,am mA 1 2,aR mA 1 0,aR mA 1 1,aR mA 1 2):=u 1;have x:eM (o 9 2 mA) (o 9 2 a)=(am mA 2 0,am mA 2 1,am mA 2 2,aR mA 2 0,aR mA 2 1,aR mA 2 2):=u 2;have w:eM (o 9 3 mA) (o 9 3 a)=(am mA 3 0,am mA 3 1,am mA 3 2,aR mA 3 0,aR mA 3 1,aR mA 3 2):=u 3;have v:eM (o 9 4 mA) (o 9 4 a)=(am mA 4 0,am mA 4 1,am mA 4 2,aR mA 4 0,aR mA 4 1,aR mA 4 2):=u 4;have M:dx (o 27 0 mB) (o 27 0 b)=_:=jo mB 0;have L:dx (o 27 1 mB) (o 27 1 b)=_:=jo mB 1;have K:dx (o 27 2 mB) (o 27 2 b)=_:=jo mB 2;have F:dx (o 27 3 mB) (o 27 3 b)=_:=jo mB 3;have C:dx (o 27 4 mB) (o 27 4 b)=_:=jo mB 4;rw[z,y,x,w,v,M,L,K,F,C];exact mG mA mB
def q7 (f:Nat->Bool):Bool:=
 f 0&&f 1&&f 2&&f 3&&f 4&&f 5&&f 6&&f 7&&f 8&&f 9
lemma j5 {f:Nat->Bool} (h:q7 f=true) (g:Fin 10):f g.val=true:=by
 unfold q7 at h;simp only[bA] at h
 have:g=0\/g=1\/g=2\/g=3\/g=4\/g=5\/g=6\/g=7\/g=8\/g=9:=by fin_cases g <;> simp
 rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 . exact h.1.1.1.1.1.1.1.1.1
 . exact h.1.1.1.1.1.1.1.1.2
 . exact h.1.1.1.1.1.1.1.2
 . exact h.1.1.1.1.1.1.2
 . exact h.1.1.1.1.1.2
 . exact h.1.1.1.1.2
 . exact h.1.1.1.2
 . exact h.1.1.2
 . exact h.1.2
 . exact h.2
def w0 (f:Nat->Bool):Bool:=
 f 0||f 1||f 2||f 3||f 4||f 5||f 6||f 7||f 8||f 9
lemma ps {f:Nat->Bool} (h:w0 f=true):∃ g:Fin 10,f g.val=true:=by
 unfold w0 at h;simp only[bO] at h;rcases h with ((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h
 . exact ⟨0,h⟩
 . exact ⟨1,h⟩
 . exact ⟨2,h⟩
 . exact ⟨3,h⟩
 . exact ⟨4,h⟩
 . exact ⟨5,h⟩
 . exact ⟨6,h⟩
 . exact ⟨7,h⟩
 . exact ⟨8,h⟩
 . exact ⟨9,h⟩
def mz (qa qb:Nat):List iN->Bool
 | []=>false
 | (pa,pb) :: us=>me pa pb qa qb||mz qa qb us
lemma jY {c b:Nat} {L:List iN} (h:mz c b L=true) :
   ∃ u ∈ L,me u.1 u.2 c b=true:=by
 induction L with
 | nil=>cases h
 | cons a t ih=>
   unfold mz at h;simp only[bO] at h;rcases h with hd|ht
   . exact ⟨a,List.mem_cons_self ..,hd⟩
   . rcases ih ht with ⟨u,hu,hdu⟩;exact ⟨u,List.mem_cons_of_mem _ hu,hdu⟩
def i3 (z:AS):List AS->Bool
 | []=>false
 | r :: rs=>(nB z.1 r.1&&w0 (fun g=>sW g r z))||i3 z rs
lemma gi {z:AS} {L:List AS} (h:i3 z L=true) :
   ∃ r ∈ L,∃ g:Fin 10,md (cB g.val r).2.1 (cB g.val r).2.2.1 (cB g.val r).2.2.2 z.2.1 z.2.2.1 z.2.2.2=true:=by
 induction L with
 | nil=>cases h
 | cons a t ih=>
   unfold i3 at h;simp only[bO,bA] at h;rcases h with ⟨_,fT⟩|ht
   . rcases ps fT with ⟨g,hg⟩;rw[ym] at hg;exact ⟨a,List.mem_cons_self ..,g,hg⟩
   . rcases ih ht with ⟨r,hr,g,hg⟩;exact ⟨r,List.mem_cons_of_mem _ hr,g,hg⟩
def pf (g rt qt:Nat):Bool:=nE rt 0xdb6db6db6db||eP (gD g rt) qt
def pg (k rt qt:Nat):Bool:=nE rt 0xdb6db6db6db||eP (gD k (l8 rt)) qt
def kk (g rb qb:Nat):Bool:=nE rb 0||iZ qb (gR g rb)
def kl (k rb qb:Nat):Bool:=nE rb 0||iZ qb (gR k (kA rb))
lemma y5 (g a b:Nat):pf g a b=eP (gD g a) b:=by
 unfold pf;cases h:nE a 0xdb6db6db6db
 . rfl
 . rw[bQ h,nn];rfl
lemma y6 (k a b:Nat):pg k a b=eP (gD k (l8 a)) b:=by
 unfold pg;cases h:nE a 0xdb6db6db6db
 . rfl
 . rw[bQ h,so,nn];rfl
lemma vQ (g a b:Nat):kk g a b=iZ b (gR g a):=by
 unfold kk;cases h:nE a 0
 . rfl
 . rw[bQ h,lK];rfl
lemma vR (k a b:Nat):kl k a b=iZ b (gR k (kA a)):=by
 unfold kl;cases h:nE a 0
 . rfl
 . rw[bQ h,qC,lK];rfl
def jJ (g:Nat) (r:RS) (aw bw ar ac b0 b1 b2:Nat):Bool:=
 cond (nB g 4)
  (q3 (oY g r.2.2.1) aw&&vS bw (sn g r.2.2.2.1)&&
   pf g r.2.2.2.2.1 ar&&pf g r.2.2.2.2.2.1 ac&&
   kk g r.2.2.2.2.2.2.1 b0&&kk g r.2.2.2.2.2.2.2.1 b1&&kk g r.2.2.2.2.2.2.2.2 b2)
  (let k:=g - 5
   q3 (oY k (ux r.2.2.1)) aw&&vS bw (sn k (xb r.2.2.2.1))&&
   pg k r.2.2.2.2.2.1 ar&&pg k r.2.2.2.2.1 ac&&
   kl k r.2.2.2.2.2.2.1 b0&&kl k r.2.2.2.2.2.2.2.2 b1&&kl k r.2.2.2.2.2.2.2.1 b2)
lemma mb (g:Nat) (r:RS) (l k h a i j d c b:Nat) :
  jJ g r h a i j d c b=mc (ay g r) (l,k,h,a,i,j,d,c,b):=by
 unfold jJ mc me jI ay;cases nB g 4 <;> simp[y5,y6,vQ,vR,Bool.and_assoc]
def i2 (sa sb aw bw ar ac b0 b1 b2:Nat):List RS->Bool
 | []=>false
 | u :: us=>
  (nB sa u.1&&nB u.2.1 sb&&me u.2.2.1 u.2.2.2.1 aw bw&&
   jI u ar ac b0 b1 b2)||i2 sa sb aw bw ar ac b0 b1 b2 us
lemma gh {c b l d m n k j i:Nat} {L:List RS}
   (h:i2 c b l d m n k j i L=true) :
   ∃ u ∈ L,mc u (c,b,l,d,m,n,k,j,i)=true:=by
 induction L with
 | nil=>cases h
 | cons a t ih=>
   unfold i2 at h;simp only[bO,bA] at h;rcases h with ⟨⟨⟨_,_⟩,hd10⟩,htail⟩|ht
   . exact ⟨a,List.mem_cons_self ..,by unfold mc;simp[hd10,htail]⟩
   . rcases ih ht with ⟨u,hu,hdu⟩;exact ⟨u,List.mem_cons_of_mem _ hu,hdu⟩
def g8 (sa sb aw bw ar ac b0 b1 b2:Nat):List (RS × Nat)->Bool
 | []=>false
 | (r,g) :: rs=>
  (nB sa r.1&&nB r.2.1 sb&&jJ g r aw bw ar ac b0 b1 b2)||
  g8 sa sb aw bw ar ac b0 b1 b2 rs
lemma iV {c b l d m n k j i:Nat} {L:List (RS × Nat)}
   (h:g8 c b l d m n k j i L=true) :
   ∃ p ∈ L,mc (ay p.2 p.1) (c,b,l,d,m,n,k,j,i)=true:=by
 induction L with
 | nil=>cases h
 | cons a t ih=>
   unfold g8 at h;simp only[bO,bA] at h;rcases h with ⟨_,hd⟩|ht
   . rw[mb a.2 a.1 c b] at hd;exact ⟨a,List.mem_cons_self ..,hd⟩
   . rcases ih ht with ⟨p,hp,hdp⟩;exact ⟨p,List.mem_cons_of_mem _ hp,hdp⟩
lemma x7 (r:Nat):pQ r 0=0:=by
 match r with|0=>rfl|1=>rfl|2=>rfl|3=>rfl|_+4=>rfl
lemma q6 (g:Nat):bR g 0=0:=by
 unfold bR;cases nB g 4 <;> simp[x7,ss,dB,bq]
def ii (q:RL):List (RL × Nat)->Bool
 | []=>false
 | (r,g) :: rs=>
  (nB q.1.1 r.1.1&&nB r.1.2.1 q.1.2.1&&
   jJ g r.1 q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2.1 q.1.2.2.2.2.2.1
    q.1.2.2.2.2.2.2.1 q.1.2.2.2.2.2.2.2.1 q.1.2.2.2.2.2.2.2.2&&
   (nE r.2 0||kd (bR g r.2) q.2))||
  ii q rs
lemma mI {q:RL} {L:List (RL × Nat)}
   (h:ii q L=true) :
   ∃ p ∈ L,vX (d7 p.2 p.1) q=true:=by
 induction L with
 | nil=>cases h
 | cons a t ih=>
   unfold ii at h;simp only[bO,bA] at h;rcases h with ⟨⟨_,hd⟩,hsub⟩|ht
   . rw[mb a.2 a.1.1 q.1.1 q.1.2.1] at hd
     have hsub':kd (bR a.2 a.1.2) q.2=true:=by
       rcases hsub with hz|hs
       . rw[bQ hz,q6];unfold kd;change nE (0&&&q.2) 0=true;rw[Nat.zero_and];rfl
       . exact hs
     exact ⟨a,List.mem_cons_self ..,by unfold vX d7;simp[hd,hsub']⟩
   . rcases ih ht with ⟨p,hp,hdp⟩;exact ⟨p,List.mem_cons_of_mem _ hp,hdp⟩
def dW {α:Type} (f:α->Bool):List α->Bool
 | []=>false
 | x :: xs=>f x||dW f xs
lemma cC {α:Type} {f:α->Bool} {L:List α} (h:dW f L=true) :
   ∃ x ∈ L,f x=true:=by
 induction L with
 | nil=>cases h
 | cons a t ih=>
   unfold dW at h;simp only[bO] at h;rcases h with hf|ht
   . exact ⟨a,List.mem_cons_self ..,hf⟩
   . rcases ih ht with ⟨x,hx,hfx⟩;exact ⟨x,List.mem_cons_of_mem _ hx,hfx⟩
def cj (w n lim a:Nat):Bool:=
 Nat.blt a (shiftLeft 1 (w*n))&&
 (List.range n).all (fun i=>nB (land (shiftRight a (w*i)) (shiftLeft 1 w - 1)) lim)
lemma bh (w n b a:Nat) (h:cj w n b a=true):oe w n b a:=by
 unfold cj at h;simp only[bA,List.all_eq_true,List.mem_range,nG,bL] at h
 exact ⟨fun i hi=>h.2 i hi,by simpa [nL] using h.1⟩
def mf (p:iN):Bool:=cj 5 5 9 p.1&&cj 6 5 27 p.2
def kN (p:AS):Bool:=
 cj 5 5 9 p.2.1&&cj 3 15 3 p.2.2.1&&cj 3 15 3 p.2.2.2&&nE p.1 (bD p.2.1)
def jm (p:RS):Bool:=
 cj 5 5 9 p.2.2.1&&cj 6 5 27 p.2.2.2.1&&
 cj 3 15 3 p.2.2.2.2.1&&cj 3 15 3 p.2.2.2.2.2.1&&
 cj 5 15 9 p.2.2.2.2.2.2.1&&cj 5 15 9 p.2.2.2.2.2.2.2.1&&cj 5 15 9 p.2.2.2.2.2.2.2.2&&
 nE p.1 (bD p.2.2.1)&&nE p.2.1 (bG p.2.2.2.1)
def o4 (p:RL):Bool:=jm p.1&&Nat.blt p.2 1073741824
lemma po {p:iN} (h:mf p=true):kv p:=by
 unfold mf at h;simp only[bA] at h;exact ⟨bh 5 5 9 _ h.1,bh 6 5 27 _ h.2⟩
lemma ko {p:AS} (h:kN p=true):iP p:=by
 unfold kN at h;simp only[bA] at h;exact ⟨bh 5 5 9 _ h.1.1.1,bh 3 15 3 _ h.1.1.2,bh 3 15 3 _ h.1.2,bQ h.2⟩
lemma i1 {p:RS} (h:jm p=true):cu p:=by
 unfold jm at h;simp only[bA] at h
 exact ⟨bh 5 5 9 _ h.1.1.1.1.1.1.1.1,bh 6 5 27 _ h.1.1.1.1.1.1.1.2,
  bh 3 15 3 _ h.1.1.1.1.1.1.2,bh 3 15 3 _ h.1.1.1.1.1.2,
  bh 5 15 9 _ h.1.1.1.1.2,bh 5 15 9 _ h.1.1.1.2,bh 5 15 9 _ h.1.1.2,
  bQ h.1.2,bQ h.2⟩
lemma q5 {p:RL} (h:o4 p=true):gw p:=by
 unfold o4 at h;simp only[bA,nG] at h;exact ⟨i1 h.1,h.2⟩
lemma eQ:∀ (g:Fin 10) (e:Fin 5),au (I g) (au g e)=e:=by decide +kernel
lemma jp:∀ (g:Fin 10) (s:Fin 5),ad (I g) (ad g s)=s:=by decide +kernel
lemma ny:∀ g:Fin 10,decide ((I g).val<5)=decide (g.val<5):=by decide +kernel
lemma mh (g:Fin 10) (w:Nat) (a:eV w):bH (I g).val (bH g.val w)=w:=by
 apply gW 5 5 _ _ (by omega) (fa (I g) _ (fa g w a)).2 a.2;intro i hi;have h1:=db (I g) (au g ⟨i,hi⟩) (bH g.val w) (fa g w a).2;rw[eQ] at h1;rw[h1];exact db g ⟨i,hi⟩ w a.2
lemma qQ (g:Fin 10) (w:Nat) (a:fv w):cx (I g).val (cx g.val w)=w:=by
 apply gW 6 5 _ _ (by omega) (gx (I g) _ (gx g w a)).2 a.2;intro i hi;have h1:=d9 (I g) (ad g ⟨i,hi⟩) (cx g.val w) (gx g w a).2;rw[jp] at h1;rw[h1];exact d9 g ⟨i,hi⟩ w a.2
lemma jM (g:Fin 10) (w:Nat) (b:cq w):cY (I g).val (cY g.val w)=w:=by
 apply gW 3 15 _ _ (by omega) (eZ (I g) _ (eZ g w b)).2 b.2;intro i hi
 set e:Fin 5:=⟨i/3,by omega⟩;set c:Fin 3:=⟨i % 3,by omega⟩
 have a:3*e.val+c.val=i:=by dsimp[e,c];omega
 have h1:=d8 (I g) (au g e) c (cY g.val w) (eZ g w b).2;rw[eQ,a] at h1;rw[h1];have h2:=d8 g e c w b.2;rwa[a] at h2
lemma kR (g:Fin 10) (w:Nat) (b:az w):cA (I g).val (cA g.val w)=w:=by
 apply gW 5 15 _ _ (by omega) (eB (I g) _ (eB g w b)).2 b.2;intro i hi
 set s:Fin 5:=⟨i/3,by omega⟩;set c:Fin 3:=⟨i % 3,by omega⟩
 have a:3*s.val+c.val=i:=by dsimp[s,c];omega
 have h1:=cn (I g) (ad g s) c (cA g.val w) (eB g w b).2;rw[jp,a] at h1;rw[h1];have h2:=cn g s c w b.2;rwa[a] at h2
lemma rm (g:Fin 10) (m:Nat) (d:m<2^30):bR (I g).val (bR g.val m)=m:=by
 have c:(I g).val<5 ↔ g.val<5:=by
   have:=ny g;simpa using this
 have i:∀ ax:Fin 3,bu (bu ax)=ax:=fun ax=>by fin_cases ax <;> rfl
 apply nE2;intro k
 by_cases hk:k<30
 . by_cases hk15:k<15
   . set e:Fin 5:=⟨k/3,by omega⟩;set ax:Fin 3:=⟨k % 3,by omega⟩
     have a:3*e.val+ax.val=k:=by dsimp[e,ax];omega
     set b:Fin 3:=if g.val<5 then ax else bu ax;have h1:=(cL (I g) (au g e) b (bR g.val m) (fo g.val m g.isLt d)).1;have h2:=cL g e ax m d;rw[eQ] at h1
     by_cases hg:g.val<5
     . have hg':(I g).val<5:=c.mpr hg;dsimp only[b] at h1;simp only[hg,hg',↓reduceIte] at h1 h2;rw[a] at h1 h2;rw[h1,h2.1]
     . have hg':¬ (I g).val<5:=fun h=>hg (c.mp h);dsimp only[b] at h1;simp only[hg,hg',↓reduceIte,i] at h1 h2;rw[a] at h1 h2;rw[h1,h2.2]
   . set e:Fin 5:=⟨(k - 15)/3,by omega⟩;set ax:Fin 3:=⟨(k - 15) % 3,by omega⟩
     have a:15+3*e.val+ax.val=k:=by dsimp[e,ax];omega
     set b:Fin 3:=if g.val<5 then ax else bu ax;have h1:=(cL (I g) (au g e) b (bR g.val m) (fo g.val m g.isLt d)).2;have h2:=cL g e ax m d;rw[eQ] at h1
     by_cases hg:g.val<5
     . have hg':(I g).val<5:=c.mpr hg;dsimp only[b] at h1;simp only[hg,hg',↓reduceIte] at h1 h2;rw[a] at h1 h2;rw[h1,h2.2]
     . have hg':¬ (I g).val<5:=fun h=>hg (c.mp h);dsimp only[b] at h1;simp only[hg,hg',↓reduceIte,i] at h1 h2;rw[a] at h1 h2;rw[h1,h2.1]
 . rw[nT (lQ (fo _ _ (I g).isLt (fo g.val m g.isLt d)) (nP (by decide:0<2) (by omega:30<=k))),
       nT (lQ d (nP (by decide:0<2) (by omega:30<=k)))]
lemma ex (g:Fin 10) (p:iN) (a:kv p):kv (dV g.val p):=
 ⟨fa g p.1 a.1,gx g p.2 a.2⟩
lemma dA (g:Fin 10) (p:AS) (i:iP p):iP (cB g.val p):=by
 rcases p with ⟨sa,pa,par,pac⟩;rcases i with ⟨hpa,hpar,hpac,hsa⟩;have h:=fa g pa hpa;have c:=eZ g par hpar;have d:=eZ g pac hpac;have a:=lG g pa hpa
 unfold cB;unfold bH cY at *
 by_cases hg:g.val<5
 . have b:nB g.val 4=true:=bL.mpr (by omega);simp only[b,bT] at h c d a ⊢
   exact ⟨h,c,d,by rw[hsa,<-a]⟩
 . have b:nB g.val 4=false:=by cases hb':nB g.val 4;rfl;exfalso;have:=bL.mp hb';omega
   simp only[b,bC] at h c d a ⊢
   exact ⟨h,d,c,by rw[hsa,<-a]⟩
lemma tP (g:Fin 10) (p:iN) (a:kv p):dV (I g).val (dV g.val p)=p:=
 Prod.ext (mh g p.1 a.1) (qQ g p.2 a.2)
lemma vZ (g:Fin 10) (p:AS) (k:iP p):cB (I g).val (cB g.val p)=p:=by
 rcases p with ⟨sa,pa,par,pac⟩;rcases k with ⟨hpa,hpar,hpac,_⟩;have d:=mh g pa hpa;have a:=jM g par hpar;have b:=jM g pac hpac
 have c:(I g).val<5 ↔ g.val<5:=by have:=ny g;simpa using this
 unfold cB;unfold bH at d;unfold cY at a b
 by_cases hg:g.val<5
 . have hg':(I g).val<5:=c.mpr hg;have j:nB g.val 4=true:=bL.mpr (by omega);have i:nB (I g).val 4=true:=bL.mpr (by omega);simp only[j,i,bT] at d a b ⊢;rw[d,a,b]
 . have hg':¬ (I g).val<5:=fun h=>hg (c.mp h)
   have j:nB g.val 4=false:=by cases hb:nB g.val 4;rfl;exfalso;have:=bL.mp hb;omega
   have i:nB (I g).val 4=false:=by cases hb:nB (I g).val 4;rfl;exfalso;have:=bL.mp hb;omega
   simp only[j,i,bC] at d a b ⊢;rw[d,a,b]
lemma pq (g:Fin 10) (p:RS) (r:cu p):ay (I g).val (ay g.val p)=p:=by
 rcases p with ⟨sa,sb,pa,pb,par,pac,bf,be,bd⟩;rcases r with ⟨hpa,hpb,hpar,hpac,hpb0,hpb1,hpb2,_,_⟩;have l:=mh g pa hpa;have j:=qQ g pb hpb;have d:=jM g par hpar;have i:=jM g pac hpac;have c:=kR g bf hpb0;have b:=kR g be hpb1;have a:=kR g bd hpb2
 have k:(I g).val<5 ↔ g.val<5:=by have:=ny g;simpa using this
 unfold ay;unfold bH at l;unfold cx at j;unfold cY at d i;unfold cA at c b a
 by_cases hg:g.val<5
 . have hg':(I g).val<5:=k.mpr hg;have n:nB g.val 4=true:=bL.mpr (by omega);have m:nB (I g).val 4=true:=bL.mpr (by omega);simp only[n,m,bT] at l j d i c b a ⊢;rw[l,j,d,i,c,b,a]
 . have hg':¬ (I g).val<5:=fun h=>hg (k.mp h)
   have n:nB g.val 4=false:=by cases hb':nB g.val 4;rfl;exfalso;have:=bL.mp hb';omega
   have m:nB (I g).val 4=false:=by cases hb':nB (I g).val 4;rfl;exfalso;have:=bL.mp hb';omega
   simp only[n,m,bC] at l j d i c b a ⊢;rw[l,j,d,i,c,b,a]
lemma vY (g:Fin 10) (p:RL) (a:gw p):d7 (I g).val (d7 g.val p)=p:=
 Prod.ext (pq g p.1 a.1) (rm g p.2 a.2)
lemma gv (g:Fin 10) {p:iN} {f:(Fin 15->Bool)->Bool} (a:kv p)
  (b:ju (dV g.val p) (R f) (O f)) :
  ju p (R (E (I g) f)) (O (E (I g) f)):=by
 have h:=iO (I g) (ex g p a) b;rwa[tP g p a] at h
lemma eU (g:Fin 10) {p:AS} {f:(Fin 15->Bool)->Bool} (a:iP p)
  (b:dk (cB g.val p) (R f)) :
  dk p (R (E (I g) f)):=by
 have h:=jt (I g) (dA g p a) b;rwa[vZ g p a] at h
lemma d4 (g:Fin 10) {p:RS} {f:(Fin 15->Bool)->Bool} (a:cu p)
  (b:aW (ay g.val p) (R f) (O f)) :
  aW p (R (E (I g) f)) (O (E (I g) f)):=by
 have h:=cX (I g) (cy g p a) b;rwa[pq g p a] at h
lemma pD (g:Fin 10) {p:RL} {f:(Fin 15->Bool)->Bool} (a:gw p)
  (b:dj (d7 g.val p) (R f) (O f)) :
  dj p (R (E (I g) f)) (O (E (I g) f)):=by
 have h:=hE (I g) (jQ g p a) b;rwa[vY g p a] at h
lemma aM (g:Fin 10) (f h:(Fin 15->Bool)->Bool) :
 E g (fun y=>f y&&h y)=(fun y=>E g f y&&E g h y):=rfl
lemma aU (g:Fin 10) (f h:(Fin 15->Bool)->Bool) :
 E g (fun y=>f y||h y)=(fun y=>E g f y||E g h y):=rfl
inductive BTree (α:Type)|lf (a:α)|nd (l r:BTree α)
abbrev bl {α:Type}:=@BTree.lf α
abbrev bn {α:Type}:=@BTree.nd α
def d3 {α:Type} (f:α->Bool):BTree α->Bool|.lf a=>f a|.nd l r=>d3 f l&&d3 f r
def dn {α:Type} (x:α):BTree α->Prop|.lf a=>x=a|.nd l r=>dn x l\/dn x r
lemma co {α:Type} {f:α->Bool} {t:BTree α} (h:d3 f t=true):∀ x,dn x t->f x=true:=by
 induction t with
 | lf a=>intro x hx;rw[hx];exact h
 | nd l r ihl ihr=>unfold d3 at h;simp only[bA] at h;intro x hx;rcases hx with hl|hr;exact ihl h.1 x hl;exact ihr h.2 x hr
lemma i0 {α:Type} {c:Bool} {a b:α} {l r:BTree α} (h:dn a l) (d:dn b r):dn (cond c a b) (.nd l r):=by
 cases c;exact oR d;exact oL h
def lN {α:Type}:BTree (List α)->Nat->List α
 | .lf a,_=>a
 | .nd l r,k=>cond (nE (land k 1) 0) (lN l (shiftRight k 1)) (lN r (shiftRight k 1))
lemma jh {α:Type} (t:BTree (List α)) (k:Nat):dn (lN t k) t:=by
 induction t generalizing k with
 | lf a=>rfl
 | nd l r ihl ihr=>exact i0 (ihl _) (ihr _)
abbrev LP:=List (RL × Nat)
abbrev LR:=List (RS × Nat)
abbrev LS:=List RS
abbrev L1:=List iN
def G:=0xdb6db6db6db
def Z1:=9741609
def Z2:=0x18c600000000000
def Z3:=9895604649984
def Z4:=0xdb6db6db600
def Z5:=0x421000000000000000
def Z6:=0x480000000000000
def Z7:=0xc63000000000000000
def Z8:=0x84200000000000
def Z9:=0x2400000000000000000
def jv:=0xdb6db61b6db
def rx:=0x2529000094a40000000
def ks:=9925055854299
def t8:=0x1c00000000000000000
def tV:=0x24630000918c0000000
def tU:=0x2463000052940000000
def tT:=0x14a50000918c0000000
def mJ:=1134945107968
def w9:=0x25294a5294a5294a529
def w8:=0x2529000094a40002529
def w7:=0x2529000000000002529
def yM:=0x246348c600000000000
def tS:=0x380000000000000
def qd:=0xdb6da400000
def q9:=0xd86db6db6db
def q8:=3404835323904
def rv:=0xdb6db6db0db
def ru:=0xdb6da49b6db
def rr:=0xdb6d8000000
def t6:=0xdb6c36db6db
def kr:=34635776
def CH:=0x2529494a94a5252a529
def CG:=0x2463000000000000000
def CF:=0x24000000318c0000000
def tR:=9914932002816
def tQ:=9895642398720
def CE:=0xc63000090000000000
def CD:=0xc630000318c0000000
def o9:=301989888
def o8:=103907328
def CC:=0x48c600000000000
def yz:=0xdb6db6d80db
def yy:=0xdb6db6d20db
def yx:=0xdb6db01b6db
def yw:=0xdb000000000
def yv:=0xd8490000000
def yu:=0x926db6db6db
def yt:=0x926c0000000
def ys:=9925036193499
def zD:=0xdb6db6db6d8
def zC:=0xdb6d8012000
def zB:=0x918c0000000
def zA:=7696581394432
def t5:=234881024
def Fr:=0x48c600012318000
def Fq:=0x48c60000a528000
def Fp:=0x294a00012318000
def Fo:=0x280000000000000
def Hx:=0x25294a5294a5294a463
def Hw:=0x25294a5294a5231a463
def Hv:=0x2529284294a4a10a529
def Hu:=0x2463000094a40000000
def Ht:=0x2400000030000000000
def Hs:=0x1400000000000000000
def Hr:=0xc00000010840000000
def CB:=0xdb6db6d24db
def CA:=0xdb6db6c92db
def Cz:=0xdb6db6c0000
def Cy:=0xdb6da41b6db
def w5:=453095424
def w4:=436314112
def ro:=6488064
def Hq:=0x318c00000000000
def Hp:=0x18c694a52948000
def yr:=454583104
def yq:=251719680
def yp:=167772160
def Fn:=0xdb6db6db6d9
def Fm:=0xdb6db69b6db
def Fl:=0xdb6db65b6db
def Fk:=0xdb6db612400
def Fj:=0xdb6da49b000
def Fi:=0xdb6da412000
def Fh:=0xdb4936db6db
def Fg:=0xd96db6db6db
def Ff:=0xc06db6db6db
def t4:=9736480
def t3:=9736192
def Rs:=0x25294a5294a52948000
def Rr:=0x25294a5294a5252a529
def Rq:=0x25294a5294a40002529
def Rp:=0x2529494a000000024a5
def Ro:=0x252948c694a5231a529
def Rn:=0x2529294a0001231a463
def Rm:=0x2529284294a5252a4a5
def Rl:=0x2529000000000000000
def Rk:=0x2520000063180000000
def Rj:=0x246348c6918d231a529
def Ri:=0x246348c65294a52a529
def Rh:=0x24634800918c6318c63
def Gg:=0x246318c65294631a400
def Gf:=0x246300000000c630000
def Ge:=0x24004800318c0000c63
def Gd:=0x18c618c663180000000
def Gc:=0x18c6000094800000000
def Gb:=0x18c6000063180000000
def Ga:=0x14a5294a918d231a529
def G9:=0x14a5294a00000000000
def G8:=0x14a518c6918d2000c63
def G7:=0x14a5000000000002463
def G6:=0x1463294a00000000000
def tc:=457028559
def tb:=453038470
def ta:=254079561
def t9:=218214790
def G5:=0xc6348c600000000000
def G4:=0xc6318c690000000c63
def G3:=0xc6318c6318c0002400
def G2:=0xc0018c61084631a400
def G1:=0xc00000000000000000
def G0:=0x421000030000000000
def py:=9738432
def px:=4325376
def BJ:=0xdb6db6db6d2
def BI:=0xdb6db6db6c0
def BH:=0xdb6db6db2db
def BG:=0xdb6db41b6db
def BF:=0xdb6da45b6db
def BE:=0xdb6da412090
def BD:=0xdb6d925b6db
def BC:=0xdb6d801b400
def BB:=0xdb6d8000090
def BA:=0xdb6cb6db6db
def Bz:=0xd26db6db6db
def By:=3298534883328
def vk:=436298112
def vj:=369205254
def vi:=305233920
def vh:=251736079
def vf:=251720200
def ve:=151031808
def FZ:=0x4a5294a40000000
def FY:=0x318c00000002520
def FX:=0x180000006000000
def yR:=1073741823
def qU:=8691712
def qT:=8655108
def qS:=4198400
def qR:=4194304
def yQ:=460175049
def yP:=457028571
def yO:=453095451
def yN:=100663296
def t7:=4197376
def FW:=0xdb6db6da4db
def FV:=0xdb6db61b690
def FU:=0xdb6db61b600
def FT:=0xdb6db6124db
def FR:=0xdb6db000000
def FQ:=0xdb6da49b690
def FP:=0xdb6da49b0db
def FO:=0xdb6d9240000
def FN:=0xdb6c361b600
def FM:=0xdb6c249b092
def FL:=0xdb6936db6db
def FK:=0xdb6036db000
def FJ:=0xdb4936124d8
def FI:=0xda6db6db6db
def FH:=0xd86da41b6db
def FG:=0xd8480000000
def FF:=0xd8000000000
def FE:=0xd06db6db6db
def FD:=0xd0488000000
def FC:=0x94a52948000
def FB:=0x926da41b6db
def FA:=0x92480000000
def Fz:=0x92000000000
def Fy:=9993775331035
def Fx:=9992241414144
def Fw:=9925055741952
def Fv:=9895604653155
def Fu:=5497558138880
def Ft:=3404835333120
def Fs:=3404835327075
def vd:=9735168
def vc:=9707520
def Q0:=0x25294a5294a5294a526
def PZ:=0x25294a5294a5294a4e7
def PY:=0x25294a5294a529498c6
def PX:=0x25294a5294a529494a5
def PW:=0x25294a5294a52948c63
def PV:=0x25294a5294a52948c60
def PU:=0x25294a5294a5231a529
def PT:=0x25294a5294a4a5294a5
def PS:=0x25294a5294992949463
def PR:=0x25294a52918d294a463
def PQ:=0x25294a52918d2948c63
def PP:=0x25294a52918c00024a5
def PO:=0x25294a5263192948000
def PN:=0x25294a5200012318000
def PM:=0x252949ce94a5294a529
def PL:=0x2529498c94a5231a529
def PK:=0x2529498c94a4e73a523
def PJ:=0x2529494a94a5231a529
def PI:=0x252948c694a523194a5
def PH:=0x252948c694a4a52a463
def PG:=0x252948c694a4a10a529
def PF:=0x252948c694a40002529
def PE:=0x252948c60001231a529
def PD:=0x252948c60001231a463
def PC:=0x252948c60000a52a463
def PB:=0x2529480094a4631a529
def PA:=0x2529318c94a4c632463
def Pz:=0x2529314a94a4a10a529
def Py:=0x2529294a94a5231a463
def Px:=0x2529280094a4e31a529
def Pw:=0x252918c694a52002529
def Pv:=0x252918c694a4631a529
def Pu:=0x252918c694a40000000
def Pt:=0x2529084294a46002529
def Ps:=0x25290000918c0000000
def Pr:=0x252900000001231a529
def Pq:=0x25204a40631842118c6
def Pp:=0x2520480063186318c63
def Po:=0x2520480063180000000
def Pn:=0x24e5000000000002529
def Pm:=0x24a5294a00012318000
def Pl:=0x24634a5294a46108000
def Pk:=0x246348c600012318000
def Pj:=0x2463000052940002463
def Pi:=0x2463000000000002463
def Ph:=0x24630000000000014a5
def Pg:=0x242148c600000000000
def Pf:=0x2400480030006318c63
def Pe:=0x2400480000000000000
def Pd:=0x240000009000a528000
def Pc:=0x24000000900000014a5
def Pb:=0x2400000052940000000
def Pa:=0x18c6318c948063018c6
def P9:=0x18c6318c63186302520
def P8:=0x18c618c694812000c63
def P7:=0x18c618c694800000000
def P6:=0x18c618c66318631a400
def P5:=0x1860000061800000000
def P4:=0x14a5000094a40000000
def P3:=0x14a5000090000002400
def P0:=0x14a5000090000000000
def OZ:=0x14630000918c0000000
def OY:=0x1463000052940000000
def Bx:=458601813
def Bw:=458601807
def Bv:=458077403
def Bu:=455455323
def Bt:=453095433
def Bs:=453042176
def Br:=318829504
def Bq:=304423305
def Bp:=302063616
def Bo:=255652827
def Bn:=136376335
def Bm:=104072902
def Bl:=103809024
def Bk:=100769814
def OX:=0xc634a5294a4631a529
def OW:=0xc63480000006318000
def OV:=0xc6318c694a46002529
def OU:=0xc6318c600000002463
def OT:=0xc6318c600000000000
def OS:=0x42118c690012000c63
def yL:=9741600
def yK:=9738240
def yJ:=9735264
def yI:=9732096
def yH:=9708672
def yG:=9577760
def yF:=9437184
def yE:=8528132
def yD:=6494400
def yC:=6422528
def yB:=4329472
def yA:=3670016
def hG:List (cT × Nat):=[((0,0,false),5),((0,1,false),6),((0,1,true),6),((0,2,false),7),((0,2,true),7),((0,5,false),5),((0,5,true),5),((0,6,false),0),((0,6,true),0),((0,7,false),0),((0,7,true),0),((0,10,false),5)]
def ik:List (cT × Nat):=[((0,10,true),5),((0,11,false),0),((0,11,true),0),((0,12,false),0)]
def j9:List (cT × Nat):=[((0,12,true),0),((5,5,false),5),((5,6,false),6),((5,6,true),6)]
def jP:List (cT × Nat):=[((5,7,false),7),((5,7,true),7),((5,10,false),5),((5,10,true),5)]
def kY:List (cT × Nat):=[((5,11,false),0),((5,11,true),0)]
def mD:List (cT × Nat):=[((5,12,false),0),((5,12,true),0)]
def pE:List (cT × Nat):=[((10,10,false),5),((10,11,false),6),((10,11,true),6)]
def rA:List (cT × Nat):=[((10,12,false),7),((10,12,true),7)]
def iA:List (cT × Nat):=hG++ik++j9++jP++kY++mD++pE++rA
def gt:=((4,111,qR,460125903,Z3,Z3,0x25294a52529529494a5,PR,PR),402640895)
def fP:=((6,99,3244032,460173897,0xc0248000000,5042291605504,0x25294a5294a46318c63,0x25294a5294a4631a400,0x25294a5294a52000c63),117432831)
def ey:=((16,95,6488192,455979983,0xd8490012000,0x926c0012000,0x2529484294a5231a463,0x252928c694a523194a5,0x252928c694a4a52a463),670561759)
def Cf:=((2,42,2097152,453046272,8796093022208,4947802324992,0x2529000052940000000,Ps,Ps),939524095)
def DU:=((10,75,7438336,455454921,0xd2248000000,0xd9600000000,0x2529480094a42108c63,0x252918c694a46000c63,0x252918c694a46002400),587179519)
def H0:=((8,67,qS,188543695,tQ,tQ,0x242148c6918d21094a5,0x1463294a918ca31a463,0x146348c65294a31a463),yR)
def zk:=((24,117,yJ,457815195,0xdb6db009200,0xdb6d9258000,0x25294a4094a4c632529,0x2529318c94a52902529,0x2529318c94a4c632529),538411351)
def Ce:=((8,103,5341184,457028059,0xd0248000000,9990093930496,PG,0x2529294a94a4630a529,PG),603959807)
def Cd:=((10,81,4295680,158111433,9921393590272,9905452875776,0x24004a52318d2948c63,0xc634a5290012948c63,0xc634a52318d294a400),419417791)
def vD:=((24,123,yK,460175055,0xdb6da480000,0xdb6db600000,PX,Hx,Hx),6258751)
def AP:=((28,119,6494404,Bv,0xd8493612490,0x926c249b090,CH,CH,CH),51720516)
def uI:=((1,0,1048576,0,4398046511104,4398046511104,0,0,0),yR)
def uH:=((3,36,3145728,Bp,0xc0000000000,5016521801728,Rk,Gc,Gb),671088639)
def p4:=((30,111,py,yP,Fk,Fj,Ro,0x2529294a94a5231a529,0x252948c694a4a52a529),538411351)
def p3:=((4,18,qR,ve,Z3,Z3,CF,CE,CD),yR)
def xk:=((4,78,qR,456192780,Z3,Z3,0x252948c052948421863,0x252930c6918d2301084,0x25292108918cc31a460),939515903)
def AO:=((4,30,2162688,yq,8805756698624,4964982194176,tV,tT,tU),yR)
def oZ:=((32,127,8591558,460174555,0xda4936124d8,0xda6c249b092,Rr,Rr,Rr),33816644)
def xj:=((38,131,9738502,459126491,0xdb6db61b492,0xdb6da49b4d8,0x25294a4a94a5294a529,PM,PM),65792)
def AN:=((12,84,ro,256439442,yt,yv,0x24634a40918cc6318c6,0x14a5318c918d29018c6,0x2463318c5294c632520),956272639)
def qI:=((12,81,3247200,yO,0xc024b009200,5042310840320,w8,w8,w8),588755287)
def qH:=((18,99,6491232,Bu,0xd8493009200,0x926c1258000,PB,Pw,Pv),588755287)
def sD:=((4,69,qR,455406153,Z3,Z3,0x2529480052946318c63,0x252918c6918d2000c63,0x252918c6918c631a400),939524095)
def AM:=((10,111,5406720,460174287,FD,Fx,PT,Hw,Hw),50315775)
def AL:=((36,129,yL,459388443,Z4,Z4,0x25294a4c94a52932529,0x2529421094a52932529,0x25294a4c94a50842529),537100311)
def uG:=((6,60,6291456,Bq,FF,Fz,0x2520480063184210c63,0x18c618c69480c000c63,0x18c618c663186302400),671088639)
def uF:=((28,123,7542979,460174299,0xd94936124c0,0xd26c249b049,PU,PU,0x25294a5294a4a52a529),570687556)
def qG:=((32,135,9740480,460175067,0xdb6db692400,0xdb6db69b000,w9,w9,w9),229383)
def sC:=((36,135,8659142,460175067,0xda6d36924d8,0xda6d369b092,w9,w9,w9),0)
def qF:=((36,131,9738438,460175063,0xdb6da49b092,0xdb6db6124d8,PZ,PZ,0x25294a5294a5294a525),4227080)
def sz:=((18,81,yI,455455305,rr,rr,0x2529480094a46318c63,0x252918c694a52000c63,0x252918c694a4631a400),553616895)
def AK:=((4,79,qR,255637195,Z3,Z3,0x246348c6518d2949463,0x14a548c690852949463,0x2463294a518d294a421),536862719)
def sv:=((12,54,ro,w5,yv,yt,rx,rx,rx),671086079)
def AJ:=((8,57,px,ta,tR,tR,Rh,G8,Gg),yR)
def xi:=((12,84,ro,454669446,yv,yt,0x252918c094a4c631800,0x2529300094a52900842,0x2529108494a4c630c60),637523455)
def xh:=((10,75,4197472,153465051,9895655019008,9895623884800,0x2400480094a4210a529,OV,OV),798998487)
def uE:=((2,42,2097152,251768832,8796093022208,4947802324992,Hu,Hu,P4),805306367)
def uD:=((4,78,qR,254914962,Z3,Z3,0x246348c094a481098c6,0x2463210894a463018c6,0x14a530c694a4810a520),805289983)
def AI:=((26,123,6559843,460175055,0xd86d2498049,0x926d36092c0,PX,Hx,Hx),4243464)
def AH:=((22,115,9732224,458077525,zC,zC,0x25294a4294a526324c6,0x2529398c94a52919ce7,0x2529398c94a4e73a523),553092575)
def uC:=((22,117,t3,Bx,qd,qd,0x25294a4694a52631ce7,0x252939ce94a5291a4c6,PK),543129983)
def xg:=((14,96,8585216,457814418,0xda490000000,0xda6c0000000,0x25294a4094a442118c6,0x2529318c94a463018c6,0x2529318c94a4c002520),587179519)
def DT:=((13,114,3378176,460175046,0xc0691240000,5044757856256,0x25294a5294a52948842,PV,PV),73385023)
def xf:=((6,69,3244032,453882435,0xc0248000000,5042291605504,0x2529180094a46318c00,0x2529180094a52000421,0x2529084294a46318c00),637523455)
def su:=((16,99,6492160,tc,0xd8492400000,0x926c2400000,PI,Py,PH),660599167)
def AG:=((8,72,px,256439052,tR,tR,0x24634a40918c8421084,0x14a5318c918d2301863,0x2463318c5294c31a460),989843455)
def AF:=((27,132,9741312,460175064,Cz,Cz,0x25294a5294a5294a108,Q0,Q0),2064447)
def AE:=((12,87,yB,Bo,9914969751552,9914969751552,Rj,Ga,Ri),1002421247)
def qE:=((4,65,qR,254128457,Z3,Z3,0x2463480094a46108c63,0x246318c694a4a000c63,0x14a518c694a4610a400),805306367)
def DS:=((7,78,7340032,306782610,0xd2000000000,0xd2000000000,Pq,Pa,P9),671068159)
def AD:=((9,84,yF,306782994,yw,yw,0x25204a40631884218c6,0x18c6318c9480c6018c6,0x18c6318c6318c602520),671068159)
def uB:=((21,126,vd,460175058,FO,FR,PY,PY,0x25294a5294a5294a520),6259775)
def AC:=((8,99,qS,258847695,tQ,tQ,0x24634a5294a523194a5,0x24634a5294a4a52a463,0x14a54a5294a5231a463),803204863)
def AB:=((30,135,6595776,460175067,0xd86db6d2400,0x926db6db000,w9,w9,w9),229383)
def xe:=((12,99,4361216,258799311,9923541073920,9915116552192,0x24634a52918d29494a5,0x14a54a52918d294a463,0x24634a525295294a463),419416767)
def uA:=((16,117,6523904,yQ,0xd8691240000,0x926cb000000,PW,PW,0x25294a5294a5294a400),6276159)
def AA:=((18,123,yI,460174677,rr,rr,0x25294a5294a4e739ce7,0x25294a5294a5291a4c6,0x25294a5294a52632523),16744959)
def uz:=((6,88,6291456,256488082,Fz,FF,0x24634a4094a4c2118c6,0x2463318c94a4a5018c6,0x14a5318c94a4c212520),805285887)
def Az:=((11,108,3312640,460175040,0xc0649240000,5043549896704,Rs,Rs,Rs),73385023)
def Ay:=((12,111,ro,460174287,yv,yt,PT,Hw,Hw),117432831)
def uy:=((6,96,6291456,309142671,FF,Fz,0x25204a526318c6314a5,0x18c64a529480c632463,0x18c64a5263192902463),134213631)
def dc:LP:=[(gt,9),(fP,8),(ey,8),(Cf,0),(DU,0),(H0,7),(zk,0),(Ce,0),(Cd,0),(vD,0),(AP,6),(uI,9),(uH,0),(p4,0)]
def di:LP:=[(p3,0),(xk,0),(AO,8),(oZ,9),(xj,8),(AN,8),(qI,6),(qH,0)]
def dz:LP:=[(sD,0),(AM,8),(AL,6),(uG,0)]
def dL:LP:=[(uF,0),(qG,0),(sC,7),(qF,0)]
def ev:LP:=[(sz,8),(AK,9),(sv,8),(AJ,8)]
def eT:LP:=[(xi,0),(xh,9),(uE,0)]
def fJ:LP:=[(uD,0),(AI,7),(AH,8),(uC,0)]
def gj:LP:=[(xg,0),(DT,7)]
def hn:LP:=[(xf,0),(su,0)]
def ij:LP:=[(AG,8),(AF,7),(AE,7)]
def hD:LP:=[(qE,0),(DS,9),(AD,9)]
def iz:LP:=[(uB,0),(AC,7)]
def js:LP:=[(AB,6),(xe,0),(uA,0)]
def kt:LP:=[(AA,8),(uz,0)]
def mu:LP:=[(Az,7),(Ay,8)]
def pC:LP:=[(uy,0)]
def wd:LP:=dc++di++dz++dL++ev++eT++fJ++gj++hn++ij++hD++iz++js++kt++mu++pC
def zI:BTree (List RL):=(bn (bn (bn (bn (bn (bl [Cf,uI,uH,p3,AO,sv,uE,Az]) (bl [])) (bn (bl []) (bl [AF]))) (bn (bn (bl []) (bl [])) (bn (bl [xk,AG]) (bl [])))) (bn (bn (bn (bl []) (bl [AN,uD,AI,xg,DS,AD,uB,uz])) (bn (bl []) (bl []))) (bn (bn (bl [xi,DT]) (bl [])) (bn (bl []) (bl [uF]))))) (bn (bn (bn (bn (bl [oZ,xj,sC]) (bl [])) (bn (bl [fP,DU,Cd,sD,uG,sz,AJ,qE,uA]) (bl []))) (bn (bn (bl []) (bl [AH,uC,AA])) (bn (bl []) (bl [qF])))) (bn (bn (bn (bl [xf]) (bl [])) (bn (bl [AK]) (bl [zk,Ce,p4,qI,qH,AL,qG,xh,AE,AB]))) (bn (bn (bl []) (bl [])) (bn (bl [gt,ey,H0,vD,AM,su,AC,xe,Ay,uy]) (bl [AP]))))))
def bf:LP:=[(xj,1),(sC,0),(AL,3),(AL,1)]
def be:LP:=[(sC,2),(sC,1)]
def bd:LP:=[(qG,9),(qG,1)]
def S7:LP:=[(AB,2),(AF,2),(qG,2),(qG,8),(AF,1)]
def S6:LP:=[(sC,3),(qG,3),(qF,6)]
def S5:LP:=[(AB,3),(vD,5),(vD,3)]
def S4:LP:=[(sC,1),(oZ,4),(p4,2),(oZ,2),(qG,3)]
def S3:LP:=[(oZ,3),(AI,4),(qF,4),(uF,3)]
def S2:LP:=[(oZ,1),(qF,9),(qF,2),(AI,2),(xj,4)]
def S1:LP:=[(vD,9),(vD,2),(oZ,1)]
def Ka:LP:=[(p4,1),(p4,7)]
def K9:LP:=[(qH,1),(zk,1),(uA,9),(vD,9),(uB,9)]
def K8:LP:=[(oZ,1),(p4,5),(uF,5)]
def K7:LP:=[(qH,7),(zk,7),(ey,4),(AH,4),(qI,1)]
def K6:LP:=[(xe,9),(su,2),(DT,2),(uA,2),(uB,2)]
def K5:LP:=[(Ay,2),(sz,2),(qH,5),(AA,2),(xg,5)]
def K4:LP:=[(qF,1),(xj,3),(qF,8)]
def K3:LP:=[(oZ,0),(uF,9)]
def K2:LP:=[(p4,9),(p4,3),(AP,3)]
def K1:LP:=[(su,9),(uC,9),(AN,2)]
def K0:LP:=[(xe,2),(AE,2),(AP,0)]
def JZ:LP:=[(AE,3),(su,3),(xe,5),(uC,3)]
def JY:LP:=[(p4,6),(uF,0),(ey,3)]
def JX:LP:=[(sz,3),(qH,3),(zk,3),(xi,6)]
def JW:LP:=[(vD,1),(vD,8)]
def JV:LP:=[(su,8),(qH,0),(zk,0),(uC,8),(uB,8),(uA,8)]
def JU:LP:=[(zk,9),(AA,1),(AH,1),(uC,1),(uB,1)]
def JT:LP:=[(qH,9),(qI,3),(uA,1)]
def JS:LP:=[(sz,1),(xg,1)]
def JR:LP:=[(Ay,1),(sz,1),(AN,1),(su,1),(xg,9)]
def JQ:LP:=[(sz,1),(ey,1)]
def JP:LP:=[(xi,1),(sv,1),(xi,9)]
def JO:LP:=[(AC,2),(Ce,1),(AM,1),(Az,2)]
def JN:LP:=[(gt,0),(AC,0),(uy,0),(uy,9)]
def JM:LP:=[(Ce,9),(fP,1),(xh,0),(uz,9),(qI,0),(Az,1)]
def JL:LP:=[(AG,1),(sD,0),(qE,0),(uz,0),(Cd,1),(AD,0),(uG,0)]
def JK:LP:=[(uy,5),(AM,2),(Ce,5),(fP,2)]
def JJ:LP:=[(uI,0),(gt,2),(uy,2)]
def JI:LP:=[(AK,1),(uz,1),(xk,5),(uD,5),(DS,1),(DU,5),(AD,1)]
def JH:LP:=[(H0,1),(AG,2),(qE,5),(sD,5),(uG,5)]
def JG:LP:=[(DU,1),(xk,1),(sD,1),(Cd,5)]
def JF:LP:=[(H0,3),(qE,1),(uD,1),(uG,1),(xh,1)]
def JE:LP:=[(DU,9),(qI,3),(Cd,8),(Cd,2),(qI,1)]
def JD:LP:=[(sv,1),(xh,3),(xf,1),(xf,9)]
def JC:LP:=[(Ce,3),(qE,7),(qI,1),(uz,7)]
def JB:LP:=[(uD,3),(xf,6),(qE,3)]
def JA:LP:=[(qE,9),(uD,9),(sD,9),(uG,9)]
def Jz:LP:=[(uI,0),(AK,4),(sD,6),(xk,6)]
def Jy:LP:=[(sv,1),(AJ,1)]
def Jx:LP:=[(Cf,1),(uE,1),(AO,1),(uH,1)]
def Jw:LP:=[(AJ,2)]
def Jv:LP:=[(AO,2),(sv,2),(uH,5)]
def Ju:LP:=[(p3,1),(p3,5)]
def Jt:LP:=[(uE,9),(Cf,9),(uH,9)]
def Js:LP:=[(p3,9)]
def Jr:LP:=[(Cf,0),(uE,0),(p3,0),(uH,0)]
def Jq:LP:=[(p3,2)]
def Jp:LP:=[(p3,6),(Cf,6),(sv,3)]
def Jo:LP:=[(p3,3),(uE,7)]
def Jn:LP:=[(uI,1),(uI,0)]
def kV:BTree LP:=(bn (bn (bn (bn (bn (bn (bl bf) (bl be)) (bn (bl bd) (bl S7))) (bn (bn (bl S6) (bl S5)) (bn (bl S4) (bl S3)))) (bn (bn (bn (bl S2) (bl S1)) (bn (bl Ka) (bl K9))) (bn (bn (bl K8) (bl K7)) (bn (bl K6) (bl K5))))) (bn (bn (bn (bn (bl K4) (bl K3)) (bn (bl K2) (bl K1))) (bn (bn (bl K0) (bl JZ)) (bn (bl JY) (bl JX)))) (bn (bn (bn (bl JW) (bl JV)) (bn (bl JU) (bl JT))) (bn (bn (bl JS) (bl JR)) (bn (bl JQ) (bl JP)))))) (bn (bn (bn (bn (bn (bl JO) (bl JN)) (bn (bl JM) (bl JL))) (bn (bn (bl JK) (bl JJ)) (bn (bl JI) (bl JH)))) (bn (bn (bn (bl JG) (bl JF)) (bn (bl JE) (bl JD))) (bn (bn (bl JC) (bl JB)) (bn (bl JA) (bl Jz))))) (bn (bn (bn (bl Jy) (bl Jx)) (bn (bn (bl Jw) (bl Jv)) (bl Ju))) (bn (bn (bn (bl Jt) (bl Js)) (bl Jr)) (bn (bn (bl Jq) (bl Jp)) (bn (bl Jo) (bl Jn)))))))
def jE (sa sb qa qb:Nat):LP:=(cond (nB 12 sa) (cond (nB 24 (land (shiftRight qb 6) 63)) (cond (nB 24 (land (shiftRight qb 12) 63)) (cond (nB 8 (shiftRight qa 20)) (cond (nB 36 sa) (cond (nB 8 (land (shiftRight qa 10) 31)) bf be) (cond (nB 2 (land (shiftRight qa 10) 31)) bd S7)) (cond (nB 8 (land (shiftRight qa 5) 31)) (cond (nB 8 (land (shiftRight qa 10) 31)) S6 S5) (cond (nB 24 (shiftRight qb 24)) S4 S3))) (cond (nB 6 (shiftRight qa 20)) (cond (nB 4 (land (shiftRight qa 5) 31)) (cond (nB 2 (land (shiftRight qa 10) 31)) S2 S1) (cond (nB 4 (land (shiftRight qa 10) 31)) Ka K9)) (cond (nB 2 (land (shiftRight qa 10) 31)) (cond (nB 6 (land qa 31)) K8 K7) (cond (nB 2 (shiftRight qa 20)) K6 K5)))) (cond (nB 4 (land (shiftRight qa 5) 31)) (cond (nB 6 (land qa 31)) (cond (nB 24 (shiftRight qb 24)) (cond (nB 36 sa) K4 K3) (cond (nB 24 sa) K2 K1)) (cond (nB 4 (land qa 31)) (cond (nB 2 (shiftRight qa 20)) K0 JZ) (cond (nB 4 (shiftRight qa 20)) JY JX))) (cond (nB 19 (land (shiftRight qb 12) 63)) (cond (nB 6 (land (shiftRight qa 15) 31)) (cond (nB 6 (land qa 31)) JW JV) (cond (nB 8 (land qa 31)) JU JT)) (cond (nB 14 (shiftRight qb 24)) (cond (nB 8 (land qa 31)) JS JR) (cond (nB 9 (shiftRight qb 24)) JQ JP))))) (cond (nB 60 sb) (cond (nB 14 (shiftRight qb 24)) (cond (nB 2 (shiftRight qa 20)) (cond (nB 14 (land (shiftRight qb 6) 63)) (cond (nB 19 (land qb 63)) JO JN) (cond (nB 19 (land qb 63)) JM JL)) (cond (nB 90 sb) (cond (nB 2 (land qa 31)) JK JJ) (cond (nB 75 sb) JI JH))) (cond (nB 2 (land qa 31)) (cond (nB 4 (land qa 31)) (cond (nB 19 (land qb 63)) JG JF) (cond (nB 9 (shiftRight qb 24)) JE JD)) (cond (nB 2 (land (shiftRight qa 10) 31)) (cond (nB 14 (land (shiftRight qb 6) 63)) JC JB) (cond (nB 2 (shiftRight qa 20)) JA Jz)))) (cond (nB 2 (land qa 31)) (cond (nB 14 (land qb 63)) (cond (nB 45 sb) Jy Jx) (cond (nB 14 (land (shiftRight qb 6) 63)) (cond (nB 8 sa) Jw Jv) Ju)) (cond (nB 2 (shiftRight qa 20)) (cond (nB 4 (land qb 63)) (cond (nB 14 (land qb 63)) Jt Js) Jr) (cond (nB 2 (land (shiftRight qa 5) 31)) (cond (nB 4 (land (shiftRight qb 6) 63)) Jq Jp) (cond (nB 2 (land (shiftRight qa 10) 31)) Jo Jn))))))
lemma rk (b a d c:Nat):dn (jE b a d c) kV:=by unfold jE kV;repeat (first|apply i0|rfl)
def u0:=(25,70,7542976,255652495,0xdb6cb6db0db,0xdb6936d24db,5603858584741,9998683871331,5603858588768)
def u1:=(18,97,9541632,408269455,G,G,0x4a4600000000000,0x39ce00000000000,0x498c00000000000)
def u2:=(11,84,9439232,258847680,G,G,0,0,0)
def u3:=(23,102,9509056,407458965,ru,jv,6809670647808,0x948c0000000,0x93180000000)
def u4:=(24,106,9446592,357663832,CB,rv,0,0,0)
def u5:=(21,89,6592512,340350092,G,G,3171,6240,6240)
def u6:=(28,92,8526020,255701531,0xdb6db612491,0xdb6da49b0d0,0,0,0)
def u7:=(24,75,4496512,255665100,G,G,0x146300009180c318000,0x1863000062952300000,0x2460000062946318000)
def u8:=(29,116,9705664,359487188,G,G,0,0,0)
def u9:=(20,78,8587392,455406162,0xdb6db6da0db,0xdb6db6d22db,Z6,Z2,Z2)
def Qo:=(20,101,9575424,225268949,G,G,0,0,0)
def nm:=(23,72,4463744,57448134,ks,ks,0,0,0)
def gk:=(29,71,8626368,255652559,CB,rv,0x246248c0318cc101463,0xc6318c6918ca301463,0xc6330c6518c6212463)
def ts:=(26,101,9736320,407467154,G,G,0x25264a400000c4218c5,0x2108318c000126018c6,0x2526318c0000c62a4e0)
def GR:=(17,72,7347296,138228120,G,G,0x140048c000000000000,0xc00294a00000000000,0xc2130c600000000000)
def C7:=(30,103,9703712,457012372,Cy,Cy,0,0,0)
def GQ:=(29,114,9705571,409806546,0xdb6da498049,0xdb6db6092c0,6809670654150,0x948000018c6,6809670657312)
def Qn:=(18,89,5377123,7189019,Fy,FE,0,0,0)
def wW:=(12,68,8456192,189329810,G,G,6703370213574,9998683871430,5674725549344)
def GP:=(10,66,3279872,305996736,G,G,0x252030c663192300000,0x18c6294a9480c318000,0x18c648c06318a528000)
def Qm:=(17,89,9441408,306016919,BG,BF,0,0,0)
def wV:=(13,51,9441280,4018191,G,G,5285,9315,9315)
def Ql:=(29,119,9642176,325940951,G,G,0,0,0)
def mF:=(22,70,6494336,304427599,0x926db6122db,0xd86da49a0db,0,0,0)
def zh:=(22,84,7641088,406684614,G,G,0x48c600000000421,0x294a00000000c00,0x48c600000000c00)
def GO:=(22,84,t3,305996754,G,G,0x48c6630c00014a5,0x294a930000024c3,0x48c6631800024c3)
def Qk:=(13,69,6393856,154964571,FB,FH,CF,CE,CD)
def Dp:=(13,69,3247201,453046299,G,G,0,0,0)
def tq:=(32,112,8591558,460173847,FJ,FM,0,0,0)
def Do:=(13,70,6295648,188543383,FB,FH,Pg,G6,0x146348c600000000000)
def Qj:=(24,113,yJ,390706331,G,G,207814656,311427072,207814656)
def C6:=(30,104,8591556,457028123,0xdb4936124d0,0xdb6c249b091,33554432,yp,yN)
def vy:=(30,107,8591556,458077139,FT,FP,238134371,171025507,170959971)
def s7:=(33,108,9640134,460173339,FJ,FM,0,0,0)
def GM:=(20,81,3351616,455418450,G,G,0x18c6948000018c6,0x18c663180002520,0x4800631800018c6)
def pM:=(34,116,9738436,458601749,0xdb6da49b0d0,0xdb6db612491,0,0,0)
def C5:=(27,117,9741312,yQ,G,G,0,0,0)
def Dn:=(16,73,6488192,353981386,G,G,9216,5280,7201)
def C4:=(10,57,3279872,251719707,G,G,0,0,0)
def Qi:=(7,63,t7,57447369,G,G,3171,3171,9216)
def zg:=(9,57,4262912,154964937,ks,ks,Fs,Fv,Ft)
def GL:=(18,84,7441506,455454741,0xdb24b0092db,0xdb6012580db,0,0,0)
def Qh:=(26,107,6494371,455439707,0xd849361b649,0x926c249b6c0,0x48000000c630000,0x18c600012630000,0x18c600012918000)
def GK:=(25,109,6497408,308360728,yu,q9,311623680,311623680,207814656)
def tn:=(26,72,8591552,453882249,rv,CB,0,0,0)
def s6:=(32,111,9738372,458077395,0xdb6db612091,0xdb6da4920d0,305241187,305243235,305240163)
def s5:=(26,91,9736320,455455315,BG,BF,0,0,0)
def zf:=(12,51,yB,52728027,9993772447451,0xd06da45b6db,0x480090000000000,0x18c630000000000,Z2)
def wU:=(25,108,6497408,457815186,q9,yu,Hq,Hq,0x4a4000000000000)
def oG:=(22,69,t3,453882435,G,G,0,0,0)
def GJ:=(21,90,vd,457815168,G,G,0,0,0)
def C3:=(28,111,6494404,Bw,0xd86da49b690,0x926db61b690,9315,5219,5219)
def ze:=(31,117,9741440,409831119,G,G,5285,9315,9315)
def Qg:=(26,111,8654947,456980187,Cy,Cy,zB,zB,5674725539840)
def GI:=(11,70,6391808,155751442,yu,q9,0x24004a4030000000000,0x318c90000000000,0xc00318c00000000000)
def GH:=(20,71,8587392,304427411,t6,Fh,0,0,0)
def wT:=(18,69,8490112,255652809,BD,yx,0x2460000052940000c63,0x1863000091800000c63,0x14a50000618c0002400)
def GG:=(20,71,6492288,404849222,G,G,FX,0x184200006000000,0x180000006318000)
def nl:=(33,111,9643203,258847707,CB,rv,0,0,0)
def fw:=(28,72,8659072,455455296,G,G,0,0,0)
def C2:=(29,106,9642176,324367387,G,G,vi,vi,206733312)
def vx:=(12,51,4325504,252506697,yy,yy,tV,tT,tU)
def lw:=(27,69,8528096,251768859,G,G,0,0,0)
def vw:=(10,60,6295552,Bq,q9,yu,0x480000000000c63,0x18c600000000c63,0x18c600000002400)
def GF:=(30,111,6559940,460142031,0xd86da49b0db,0x926db6124db,0x92940002463,0x92940002463,0x929400014a5)
def vv:=(20,71,4329604,321205193,G,G,0,0,0)
def Qf:=(31,111,6592708,359487183,0x926da49b090,0xd86db612490,0x948c0002463,0x931800014a5,6809670657123)
def zd:=(8,60,2230272,255652800,G,G,yM,G9,yM)
def wS:=(7,36,t7,73746,yx,BD,6342,9504,6342)
def Qe:=(26,99,6562912,306021339,q9,yu,vi,vi,173178880)
def mE:=(36,111,9738500,yP,jv,ru,0,0,0)
def vu:=(12,48,8519680,304422915,G,G,Po,P7,Gd)
def wR:=(36,123,yL,459376152,G,G,0,0,0)
def s3:=(10,51,4197472,2469903,Fy,FE,0,0,0)
def tm:=(26,72,6559936,102347163,G,G,FX,0x84200006000000,0x180000002108000)
def Qd:=(17,78,9635840,206095506,G,G,0,0,0)
def pL:=(39,119,9741510,460175051,0xdb6db6db092,0xdb6db6d24d8,0,0,0)
def GE:=(30,110,9735456,458077016,G,G,0,0,0)
def Dm:=(25,99,6492355,455456457,0xd849241b049,0x926c24124c0,0,0,0)
def wQ:=(35,116,9736484,457815509,0xdb6da41b691,0xdb6da41b6d0,0x4a4000000000000,Hq,Hq)
def GD:=(11,60,4200480,104657487,9925055067867,9925036717787,0x82148c6918000014a5,0x140018c6618c0002463,0xc6048c652940002463)
def C1:=(12,61,yB,188543689,ys,ys,0x48c600000000421,0x294a00000000c00,0x48c600000002400)
def Qc:=(24,105,6557795,457029321,0xd86da418049,0x926da4092c0,0,0,0)
def wP:=(30,109,py,458077519,ru,jv,3171,9315,9315)
def vt:=(14,60,6422656,Bq,0xd86db6d20db,0x926db6d20db,0x480062944108c63,0x18c69180a000c63,0x18c6618c6302400)
def GC:=(20,99,8490083,460101321,0xdb601258049,0xdb24b0092c0,Fs,Fv,Ft)
def C0:=(17,54,7536768,w5,G,G,0,0,0)
def GB:=(9,57,4294656,154964937,ks,ks,0x240048c00000c318000,0xc63294a00012300000,0xc6330c60000a528000)
def Qb:=(24,111,6492292,325924311,0x926c241b690,0xd849241b690,0,0,0)
def zc:=(26,75,6559936,321729483,G,G,0x48420001231a421,0x28c600012319463,0x28c60000a529463)
def rZ:=(14,57,6426624,251719707,0xd848241b6db,0x9248241b6db,0,0,0)
def GA:=(8,63,3246080,5506389,G,G,0x4a4600000001ce7,0x39ce000000024c6,0x498c00000002523)
def Gz:=(29,107,9640192,457012187,jv,ru,0,0,0)
def qZ:=(31,117,9741440,Bx,G,G,0,0,0)
def tl:=(39,118,9741510,460142290,rv,CB,0,0,0)
def Dl:=(26,99,6530176,tc,q9,yu,0x48c600000001463,0x294a00000002463,0x48c600000001463)
def qY:=(25,69,4497536,255652809,ks,ks,0x1c630000918d2318c63,0x14a50000718d2318c63,0x246300005294a529c00)
def qX:=(14,72,8585216,256438674,Fh,t6,0x918c00018c6,0x918c00018c6,5674725549344)
def vs:=(14,57,4395008,ta,9915255076571,9924633802459,0x24634800918c6000c63,0xc630842918d2000c00,0x24631800318c2108c00)
def zb:=(42,121,9740552,458601943,G,G,0,0,0)
def DH:=(9,63,4294656,156538179,G,G,Z9,Z7,Z7)
def oM:=(27,117,9735267,yQ,0xdb6d9258049,0xdb6db0092c0,0,0,0)
def DG:=(7,56,3147840,302084111,G,G,0x2520000000000002463,0x18c6000000000002463,0x18c60000000000014a5)
def uu:=(31,119,6592708,323860187,G,G,0,0,0)
def Ax:=(36,121,9738438,409831123,ru,jv,0,0,0)
def DF:=(38,121,9738502,407733979,G,G,0,0,0)
def si:=(27,84,9732384,454669257,G,G,0,0,0)
def Aw:=(31,107,8657091,258847451,0xdb6db6124c0,0xdb6da49b049,0x14a5000000000000000,CG,CG)
def Av:=(10,48,7438336,254078985,Bz,Fg,P5,0x14a5000061800000000,0x1860000052940000000)
def sh:=(7,54,t7,155751552,BD,yx,0x318c00012900000,0x318c0000c630000,0x4a400000c630000)
def sg:=(8,39,4261888,3933129,Fy,FE,0x48c600012318c63,0x294a00012318c63,0x48c60000a52a400)
def DE:=(24,105,yK,406684635,jv,ru,Fr,Fp,Fq)
def l5:=(26,99,9740288,tc,G,G,0x48c6000123194a5,0x18c60001231a463,0x48c60000631a463)
def Au:=(25,107,6592640,457028567,G,G,Fr,Fp,Fq)
def DD:=(25,107,6592640,457012187,jv,ru,Fr,Fp,Fq)
def qB:=(14,54,6490112,w5,q9,yu,0,0,0)
def lC:=(22,78,t3,255652818,G,G,0x246348c0918c00018c6,0x14a5294a918c00018c6,0x246330c652940002520)
def se:=(33,117,9735459,455456475,G,G,0,0,0)
def lB:=(10,54,yC,105406866,0x924836db6db,0xd84836db6db,0x4a40000000018c6,0x318c000000018c6,FY)
def sd:=(5,27,2163712,27,G,G,0,0,0)
def lA:=(6,0,4196352,0,ks,ks,0,0,0)
def At:=(36,123,9643206,460158171,G,G,0,0,0)
def DC:=(28,103,6494404,455979739,0xd8493612490,0x926c249b090,0,0,0)
def qA:=(6,18,4259840,2359305,G,G,3171,3171,9216)
def oK:=(12,57,yB,253292943,9914969863899,9914969863899,0x24631800918c60014a5,0x14a50842918c6002463,0x246318005294210a463)
def ut:=(7,48,t7,5506185,ks,ks,0,0,0)
def As:=(13,66,9568256,354767241,G,G,0x480000000000c63,0x18c600000000c63,0x18c600000002400)
def ur:=(26,81,8591552,yO,G,G,0,0,0)
def DB:=(12,63,9535488,304423497,G,G,Pp,P8,P6)
def oJ:=(29,99,9736416,455979987,BG,BF,0,0,0)
def DA:=(30,107,py,389919707,jv,ru,Fr,Fp,Fq)
def uq:=(8,49,2164800,vh,G,G,Pi,G7,Ph)
def Ar:=(22,78,9732224,454668873,G,G,0,0,0)
def Dz:=(8,48,4261888,154964928,ks,ks,Fr,Fp,Fq)
def Aq:=(4,36,3146752,Bp,Ff,5045973006043,0,0,0)
def Dy:=(5,39,2131968,153391683,G,G,0x240018c6318d2000000,0xc6318c690006318000,0xc634800318c6318000)
def Dx:=(25,87,qU,Bo,G,G,0x48c6918c0000000,0x294a918c0000000,0x48c652940000000)
def mQ:=(8,27,px,2359881,9992298936027,0xd048b6db6db,o8,o9,103916544)
def x3:=(12,51,yB,102261147,ys,ys,0xc00180030006000000,0x421084230006000000,0xc00180010842108000)
def Dw:=(7,45,4260864,153391689,ks,ks,0x4800318c6318000,0x18c690012000000,0x18c6318c6318000)
def Dv:=(18,75,yI,405111369,G,G,0,0,0)
def lz:=(44,119,9741608,Bv,G,G,0,0,0)
def Ap:=(32,115,9738496,456504667,G,G,0,0,0)
def Ao:=(16,67,8396800,188543695,G,G,5285,9315,9315)
def s9:=(8,43,4196416,151072783,9925055779035,9925055807707,9315,9315,5285)
def up:=(7,36,4292608,153391680,ks,ks,Ht,Z3,G1)
def oI:=(4,0,2162688,0,G,G,0,0,0)
def An:=(7,39,6324224,153391305,G,G,Ge,G4,G3)
def Am:=(26,75,9732352,453882441,G,G,301999104,103910499,103910499)
def Al:=(5,30,2163712,yq,G,G,tV,tT,tU)
def Du:=(4,27,2130944,151031817,G,G,Fs,Fv,Ft)
def qz:=(30,99,py,Bu,FT,FP,FX,0x84200006000000,0x180000002108000)
def Dt:=(5,30,2162720,yq,8805814220507,4965039716059,tV,tT,tU)
def uo:=(16,63,6492160,Bt,G,G,0,0,0)
def wZ:=(9,39,yF,153391305,G,G,Ge,G4,G3)
def ly:=(8,18,qS,2396160,ys,ys,0,0,0)
def je:=(10,30,yC,yq,G,G,0x24600000618c0000000,0x14a5000091800000000,0x1863000052940000000)
def s8:=(9,39,6389760,103047753,0x926036db6db,0xd824b6db6db,0xc00480030006318c63,0x42118c630012000c63,G2)
def Ds:=(12,48,ro,402751488,G,G,0,0,0)
def Jm:=(27,93,9738336,454668699,0xdb6db6092db,0xdb6da4980db,yN,yN,kr)
def qy:=(15,57,9633792,ta,t6,Fh,Rh,G8,Gg)
def lx:=(8,14,qS,33579014,ys,ys,0,0,0)
def oH:=(12,45,ro,153391689,0x926c36db6db,0xd84936db6db,Pf,OS,G2)
def wY:=(9,36,yF,Bp,G,G,Rk,Gc,Gb)
def un:=(24,81,yJ,yO,G,G,0,0,0)
def l4:=(36,111,yL,yP,G,G,0,0,0)
def hO:=(42,123,9741606,460174299,G,G,0,0,0)
def Dr:=(16,57,8650752,ta,G,G,0x24630000918c6318c63,0x14a50000918d2000c63,0x246300005294631a400)
def jz:=(8,15,px,151019520,9914989524699,9914989524699,Ht,G0,Hr)
def qx:=(18,54,yI,w5,G,G,0,0,0)
def Dq:=(45,133,Z1,460170970,G,G,0,0,0)
def qw:=(12,30,ro,yq,0x926c36db6db,0xd84936db6db,tV,tT,tU)
def Ak:=(6,12,4259840,100687872,ks,ks,By,By,mJ)
def iR:=(8,18,8388608,ve,G,G,CF,CE,CD)
def l3:=(45,127,Z1,460175059,G,G,0,0,0)
def wX:=(3,0,3145728,0,G,G,0,0,0)
def jr:LR:=[(u0,0),(u1,0),(u2,0),(u3,0),(u4,0),(u5,0),(u6,0),(u7,0),(u8,0),(u9,0),(Qo,0),(nm,0),(gk,0),(ts,0),(GR,0),(C7,0),(GQ,0),(Qn,0),(wW,0),(GP,0),(Qm,0),(wV,0),(Ql,0),(mF,0),(zh,0),(GO,0),(Qk,0),(Dp,6),(tq,0),(Do,0),(Qj,0),(C6,0),(vy,0),(s7,9),(GM,0),(pM,0),(C5,7),(Dn,0),(C4,0),(Qi,0),(zg,0),(GL,0),(Qh,0),(GK,0),(tn,0),(s6,0),(s5,0),(zf,0),(wU,0),(oG,0),(GJ,0),(C3,0),(ze,0),(Qg,0),(GI,0),(GH,0),(wT,0),(GG,0)]
def k6:LR:=[(nl,0),(fw,0),(C2,0),(vx,8),(lw,0),(vw,0),(GF,0),(vv,0),(Qf,0),(zd,0),(wS,0),(Qe,0),(mE,0),(vu,0),(wR,0),(s3,0),(tm,0),(Qd,0),(pL,7),(GE,0),(Dm,0),(wQ,0),(GD,0),(C1,0),(Qc,0)]
def kX:LR:=[(wP,0),(vt,0),(GC,9),(C0,0),(GB,0),(Qb,8),(zc,0),(rZ,0),(GA,0),(Gz,0),(qZ,0),(tl,0),(Dl,0),(qY,0),(qX,0),(vs,0),(zb,8),(DH,0),(oM,0)]
def ml:LR:=[(DG,0),(uu,0),(Ax,0),(DF,8),(si,0),(Aw,0),(Av,0),(sh,0),(sg,0),(DE,0),(l5,0),(Au,0),(DD,0),(qB,0),(lC,0),(se,8),(lB,0)]
def oa:LR:=[(sd,0),(lA,0),(At,0),(DC,6),(qA,0),(oK,0),(ut,0),(As,0),(ur,0),(DB,0),(oJ,0),(DA,0),(uq,6),(Ar,8)]
def qe:LR:=[(Dz,0),(Aq,0),(Dy,7),(Dx,7),(mQ,0),(x3,7),(Dw,0),(Dv,8),(lz,6),(Ap,0),(Ao,7),(s9,0),(up,0),(oI,8),(An,0),(Am,8),(Al,0)]
def td:LR:=[(Du,0),(qz,0),(Dt,8),(uo,0),(wZ,9),(ly,7),(je,0),(s8,0),(Ds,8),(Jm,0),(qy,0),(lx,0),(oH,0)]
def wa:LR:=[(wY,0),(un,0),(l4,6),(hO,0),(Dr,8),(jz,0),(qx,8),(Dq,9),(qw,8),(Ak,0),(iR,0),(l3,7),(wX,9)]
def j8:LR:=jr++k6++kX++ml++oa++qe++td++wa
def zF:BTree LS:=(bn (bn (bn (bn (bn (bl [u2,GP,GJ,fw,zd,C0,sh,qB,lA,Dz,Aq,up,oI,Al,Dt,ly,je,Ds,wY,jz,qx,qw,Ak,iR,wX]) (bl [])) (bn (bl []) (bl [u4,GR,GK,wR,GE,tl]))) (bn (bn (bl []) (bl [u8,C7])) (bn (bl [u5,u7,Dm,Qc,GC,oM]) (bl [Dp,l3])))) (bn (bn (bn (bl []) (bl [u9,ts,wW,GO,GM,wU,GI,wS,Qd,qX,lC,lB])) (bn (bl [Dn]) (bl []))) (bn (bn (bl [nm,zh,GG,lx]) (bl [])) (bn (bl []) (bl [Qn,Qh,Qg,nl,Aw,se]))))) (bn (bn (bn (bn (bl [s7,DF,At,hO]) (bl [pL])) (bn (bl [C5,Qi,zg,tn,wT,vx,vw,C1,vt,GB,qY,vs,si,Av,sg,qA,ut,As,DB,Ar,mQ,Dw,Dv,An,Am,Du,uo,wZ,s8,qy,oH,Dr]) (bl [pM,wQ,Ax]))) (bn (bn (bl []) (bl [u3,Qo,GQ,GA,qZ])) (bn (bl [vv]) (bl [tq])))) (bn (bn (bn (bl [oG,vu,DH,Dy,lz,Dq]) (bl [s5,C3,GH,GF,Qf,oJ])) (bn (bl [zc]) (bl [Qk,Qj,C4,zf,C2,lw,Qe,tm,Qb,rZ,Gz,DE,DD,sd,ur,DA,Dx,x3,Ap,qz,Jm,un,l4]))) (bn (bn (bl []) (bl [Qm,Ql,Do,vy,GL,s6,Au])) (bn (bl [u0,u1,gk,wV,mF,ze,s3,GD,wP,Dl,DG,l5,oK,uq,Ao,s9]) (bl [u6,C6,mE,zb,uu,DC]))))))
def RY:LR:=[(l3,1),(l3,3),(lz,4),(wR,2),(pL,2),(lz,3),(lz,2),(l3,2),(hO,9),(zb,2),(l3,0),(Dq,1)]
def RX:LR:=[(lz,0),(hO,0),(l3,4),(hO,9),(pL,4),(hO,3),(zb,3),(l4,3),(wR,0),(se,3)]
def RW:LR:=[(lz,1),(hO,1),(hO,7),(wR,0),(tl,1),(pL,0),(wR,8),(Ax,4)]
def RV:LR:=[(pL,1),(hO,0),(lz,3),(s7,0),(tq,9),(l3,1),(l4,3),(tl,1),(nl,0),(hO,9),(s6,1)]
def RU:LR:=[(hO,1),(l3,2),(C5,2),(tq,3),(fw,9),(mE,1),(oM,9),(se,1),(mE,3),(ze,2)]
def RT:LR:=[(pL,1),(s7,0),(fw,9),(lw,9),(oG,9),(nl,0),(u6,3),(mE,3),(nm,2),(oM,8),(un,9),(s6,1),(u0,4),(nl,7),(gk,2),(se,3),(pM,1),(oM,1),(GL,9),(vy,1),(u6,9),(oJ,3),(l4,3),(oJ,9),(nl,2),(qY,8),(tq,9),(C6,9)]
def RR:LR:=[(l4,0),(fw,6),(pL,4),(nl,0),(ur,0),(s7,3),(wR,0),(si,6),(tl,4),(gk,0),(s5,0),(s5,6),(se,1),(ze,4),(ts,4),(u4,0),(ts,6)]
def RQ:LR:=[(fw,9),(u0,0),(pL,2),(GP,2),(u3,9),(u6,7),(zh,2),(u0,6),(C2,0),(C2,6),(u1,9),(u1,2),(mE,7)]
def RP:LR:=[(l3,3),(qZ,2),(fw,2),(pM,2),(tl,1),(tq,5),(tq,3),(At,2),(At,6),(uu,8),(mE,8),(C2,9),(C2,4),(uu,4),(uu,0),(ts,3),(u7,8)]
def RO:LR:=[(hO,6),(s7,2),(hO,2),(tn,2),(se,0),(tn,3),(u0,9),(pL,3),(u6,0),(oM,5),(wU,2),(u6,4),(oM,3)]
def Jl:LR:=[(lz,0),(mE,0),(tl,1),(mE,6),(vy,6),(DC,0),(wQ,0),(tl,5),(pM,3),(nl,9),(pM,6),(C3,6)]
def Jk:LR:=[(u6,0),(fw,3),(mE,0),(u0,2),(lw,9),(u6,6),(nl,2),(pM,3),(vv,2),(GQ,1),(Dm,8),(je,2),(zd,2),(u7,8),(tm,9),(C6,0),(GF,1),(C6,6),(GC,1),(oK,9),(u7,9),(nl,9),(u0,4),(s5,3),(GF,5),(C7,3),(vy,3),(C3,6)]
def Jj:LR:=[(l4,0),(lw,0),(qz,6),(oJ,6),(tm,0),(qz,0),(u0,6),(un,6),(ur,6),(oJ,0),(DA,0),(qZ,6),(tn,6),(wP,6),(ur,0),(ts,6),(GE,0),(s5,6),(u3,2),(Qe,6),(wQ,3),(wQ,0),(Ap,0),(GE,6),(Gz,0),(gk,0)]
def Ji:LR:=[(un,0),(l4,0),(tm,0),(lw,0),(gk,0),(fw,6),(u7,0),(u9,0),(qz,6),(Dp,0),(lw,6),(Qj,0),(mF,0),(ts,0),(uo,6),(qY,0),(s5,0),(DD,0),(C4,6),(mE,0),(u7,6),(vx,0),(u0,6),(C7,6)]
def Jh:LR:=[(C0,6),(si,3),(Am,3),(fw,3),(qx,3),(gk,9),(qB,6),(Ar,3),(s3,9),(lw,9),(tn,3)]
def Jg:LR:=[(wV,9),(iR,6),(ly,2),(u0,2),(s3,9),(sh,2),(u2,9),(u4,9),(lx,9),(u7,8),(wT,9),(Gz,0),(u1,2),(wT,2),(ut,2),(u9,0),(u0,0),(u3,0)]
def Jf:LR:=[(pL,0),(hO,8),(l3,0),(s6,0),(zb,0),(tq,0),(Qg,9),(oM,0)]
def Je:LR:=[(hO,4),(u6,2),(pL,0),(gk,6),(fw,4),(s7,4),(fw,0),(u0,3),(tq,0),(oM,0),(zb,4),(hO,8),(nm,0),(u6,1),(vy,0),(tq,7),(uu,6),(pM,4),(u7,6),(u7,0),(Ax,7),(vy,8)]
def Jd:LR:=[(fw,0),(lz,2),(oJ,0),(mE,8),(u6,2),(gk,6),(vy,0),(pM,0),(wQ,8),(qZ,0),(Au,0),(nl,6),(nl,4),(wU,0),(tn,0),(gk,9),(C7,0),(wP,0),(Aw,6),(mE,2)]
def Jc:LR:=[(lw,6),(u0,9),(fw,5),(qw,3),(u0,0),(qY,3),(s3,0),(nl,4),(mF,3),(qX,6),(jz,3),(lB,3)]
def Jb:LR:=[(mE,4),(lz,4),(s6,5),(Aw,8),(mE,5),(u6,4),(u7,3),(C6,4),(nl,1),(pM,2),(C3,2),(vy,7),(zb,2),(Qb,0),(C3,4),(u7,9),(u0,9),(Qc,2),(tl,0),(Qh,5),(s6,2),(u8,9),(nl,8)]
def Ja:LR:=[(gk,3),(vv,7),(u6,8),(u0,3),(Qn,1),(Dm,2),(lw,4),(Dp,4),(Dm,7),(rZ,5),(vv,5),(mF,4),(rZ,3),(tm,4),(gk,9),(GL,4),(vv,0),(uq,4),(zd,3),(oK,3),(GC,0),(mF,5),(u0,4),(u7,3)]
def J9:LR:=[(gk,6),(nm,0),(gk,0),(vx,3),(pM,7),(gk,3),(vv,8),(uq,0),(s6,7),(qY,3),(qY,6),(zc,6),(DG,0),(u8,6),(zc,0),(u0,0),(s9,0),(s6,4),(u8,0),(vt,6),(qY,0),(wT,6)]
def J8:LR:=[(qw,3),(u0,6),(rZ,6),(rZ,4),(lC,4),(mQ,3),(nm,6),(vx,3),(sg,4),(je,3),(u7,0),(Dt,3),(GA,4),(x3,4),(pM,4),(GO,4),(up,3),(oK,6),(nm,0),(u5,3),(mF,0)]
def J7:LR:=[(l4,2),(un,8),(ur,2),(qz,8),(qz,2),(oJ,8),(fw,2),(qZ,2),(gk,2),(Ap,8)]
def J6:LR:=[(tn,2),(fw,2),(qB,2),(s5,2),(oG,2),(qZ,2),(lw,8),(vs,2),(Dl,2),(s3,4),(wP,2),(uo,2),(fw,5),(gk,8),(tm,8),(wQ,5),(l5,2),(u7,8)]
def J5:LR:=[(gk,2),(lw,2),(s5,8),(zf,2),(u7,8),(mF,8),(rZ,2),(Qf,1),(zc,8),(wU,8),(Au,8),(wQ,0),(mF,2),(s6,8),(wP,8)]
def J4:LR:=[(qw,2),(u0,2),(vs,2),(jz,5),(sg,9),(gk,8),(mQ,2),(s8,2),(s3,8),(lB,2),(uq,2),(oK,2),(Al,2),(gk,2),(oH,5),(s9,8),(lB,5)]
def J3:LR:=[(si,0),(C0,0),(u0,6),(Ar,0),(gk,8),(vx,0),(Am,0),(Qm,2),(gk,2),(u7,0),(u0,8),(u6,2),(u7,8),(u3,2),(lw,2)]
def J2:LR:=[(C0,0),(lx,6),(vx,0),(u0,6),(ly,4),(rZ,6),(sh,6),(GR,6),(GH,2),(s3,8),(Do,6),(vw,4),(wW,4),(zf,4),(GR,2),(mF,0),(Do,4),(Dn,0),(zg,6),(s9,6),(s9,2),(GH,6)]
def J1:LR:=[(ly,2),(u0,2),(wV,2),(lx,2),(wS,2),(Ao,2),(u7,3),(vt,0),(vw,2),(wV,9),(lx,9),(sh,2),(u4,6),(wW,2),(wW,9),(Dn,8),(wS,9),(u7,8),(u3,0),(vt,6),(ut,9),(wT,9),(Do,9)]
def J0:LR:=[(lA,2),(iR,6),(iR,2),(wZ,2),(vt,6),(u7,3),(vw,2),(wW,2),(Aq,2),(wS,9),(sd,6)]
def IZ:LR:=[(l3,0),(ts,7),(l4,1),(qZ,0),(qZ,7),(l5,0),(tl,7),(u7,0),(wP,7),(DF,0),(wR,1),(DE,0),(u5,0),(l5,7)]
def IY:LR:=[(C5,0),(oG,7),(hO,8),(zh,7),(l5,0),(s7,4),(l5,7),(lC,7),(fw,7),(qX,4),(wP,7),(ze,7),(ze,0),(s5,4)]
def IX:LR:=[(gk,7),(fw,0),(C5,0),(fw,7),(wU,0),(l4,1),(Dl,7),(u4,0),(si,1),(l5,0),(u3,9),(Dl,0),(u3,3),(Ql,7),(u1,0),(Qo,7),(GK,0),(u0,0),(l5,7),(u5,0),(qz,1),(oJ,1)]
def IW:LR:=[(u7,6),(fw,7),(u0,7),(oG,7),(fw,0),(gk,7),(nm,6),(wU,0),(iR,7),(iR,3),(qX,7),(mF,7),(gk,3),(vw,7),(GO,7)]
def IV:LR:=[(gk,1),(pL,1),(si,1),(s6,8),(u7,1),(fw,1),(ts,1),(qY,1),(ze,1),(mE,8),(s7,0),(zc,1),(pM,8),(ly,3),(u7,7),(ts,9),(u8,1),(qZ,1),(nm,1)]
def IU:LR:=[(l4,1),(fw,7),(hO,8),(tm,1),(s5,1),(s7,4),(u6,1),(C7,7),(u7,7),(mF,1)]
def IT:LR:=[(oG,0),(u7,1),(lC,0),(fw,7),(wV,0),(l5,7),(GM,7),(GJ,0)]
def IS:LR:=[(fw,0),(u0,0),(oG,7),(oG,0),(lx,0),(u7,0),(je,4),(fw,7),(lw,6),(vu,7),(lC,0),(zh,7),(zg,7),(GG,0)]
def IR:LR:=[(qY,7),(uo,0),(gk,0),(rZ,0),(fw,0),(C1,0),(u7,6),(fw,7),(zd,0),(gk,7),(C1,7),(oK,0),(sg,7),(Dx,0),(vs,0),(lC,0),(tm,6),(vs,7),(GP,0),(C4,0),(u7,0),(GA,7),(u9,0),(mF,6),(oG,0),(nm,7),(lw,6),(wT,7)]
def IQ:LR:=[(fw,7),(uo,7),(Dz,0),(oG,7),(qB,7),(vs,7),(sg,0),(zg,0),(GB,0),(C4,7),(lw,7),(x3,0),(Qk,0),(Dp,1),(GG,7),(uq,1),(nm,0),(mF,7),(tm,1),(DH,0),(oK,7),(GM,1)]
def IP:LR:=[(qw,4),(qx,4),(mQ,4),(s8,4),(je,4),(jz,7),(vx,4),(oH,7),(qy,4),(Ds,4),(vs,7),(qB,7),(oG,7),(vu,4),(Dv,4),(DB,4),(s3,1),(tn,7),(u0,7),(qX,7),(qX,4),(lB,4)]
def IN:LR:=[(je,4),(mQ,4),(Ak,4),(oI,4),(jz,4),(Al,7),(qB,7),(sd,4),(x3,4),(sd,7),(qA,4),(lB,7),(qA,7)]
def IM:LR:=[(lx,0),(Ao,0),(ly,0),(gk,3),(C0,9),(zc,1),(vw,0),(u7,6),(vw,7),(vt,3),(vx,1),(gk,9),(lx,7),(GD,7),(GD,0),(C1,0),(rZ,0),(s9,3),(wV,7),(u7,1),(u7,9),(wV,0),(mF,6),(vt,1)]
def IL:LR:=[(ly,0),(lx,0),(lx,7),(sh,7),(wS,0),(zf,0),(ut,0),(Dy,0),(s3,7),(lA,0),(lA,7),(wS,7),(ut,7),(zg,0),(Qi,0),(sh,0)]
def IK:LR:=[(iR,3),(iR,7),(u7,6),(wW,7),(vw,7),(vt,3)]
def IJ:LR:=[(lA,7),(wX,3),(ly,3),(wS,0),(Aq,7)]
def II:LR:=[(oG,8),(C5,1),(fw,8),(lC,1),(s7,0),(l5,8),(wU,8),(u7,1),(lw,2),(GQ,1),(GJ,8),(zh,1),(qZ,8)]
def IH:LR:=[(qY,8),(gk,8),(l5,1),(lC,8),(oG,1),(u7,2),(vs,8),(oK,8),(zh,1),(qY,1),(u5,1),(fw,1),(GK,8),(u7,8),(qZ,1),(vv,1)]
def IG:LR:=[(qx,0),(qy,0),(qy,8),(Dn,0)]
def IF:LR:=[(qy,0),(u7,7),(qw,0),(Dr,0),(lC,0),(oH,8),(oH,0),(As,0),(qy,8),(Qd,0),(As,8)]
def IE:LR:=[(je,8),(qx,0),(jz,8),(u7,7),(je,0),(jz,0),(wY,8),(qX,8),(C1,8),(s8,8),(ly,1),(vu,8),(lB,8),(vu,0),(GI,8),(lB,0),(zf,1),(mQ,0),(wZ,4),(qw,0),(vv,1)]
def ID:LR:=[(qx,0),(je,0),(fw,8),(s8,0),(vu,0),(wT,1),(GI,0),(zg,1),(zd,1),(nm,7),(u7,1),(rZ,0),(nm,2),(wW,0),(nm,1),(Av,0),(mF,2),(GB,0)]
def IC:LR:=[(je,0),(Ak,0),(up,0),(oI,0),(mQ,0),(jz,0),(up,8),(qA,8),(qB,0),(Dw,0),(jz,8),(tn,8),(zf,8),(vu,8),(zd,8),(sg,7),(C4,8)]
def IB:LR:=[(lA,4),(iR,8),(iR,4),(An,8),(ly,1),(qA,8),(jz,8),(je,8)]
def IA:LR:=[(qx,1),(qy,9),(lC,9),(qX,9),(oH,1),(qX,1)]
def Iz:LR:=[(je,9),(fw,1),(oH,9),(qX,9),(lB,9),(s8,9),(qX,1)]
def Iy:LR:=[(u7,2),(jz,1),(vu,1),(oH,1),(je,9),(mQ,1),(nm,2)]
def Ix:LR:=[(jz,1),(iR,5),(je,1),(mQ,1),(lA,1),(lB,1),(qA,1),(iR,1),(s3,7),(Av,9),(up,1),(jz,9)]
def Iw:LR:=[(wZ,0),(wY,0),(iR,0),(wY,9)]
def Iv:LR:=[(lA,9),(iR,0),(iR,9),(An,0),(u0,1)]
def Iu:LR:=[(wX,0),(sd,0),(oI,4),(qA,0),(Du,0),(oI,0)]
def It:LR:=[(wX,0),(oI,4),(lA,2),(oI,1),(lA,0),(oI,0),(sd,4)]
def kU:BTree LR:=(bn (bn (bn (bn (bn (bn (bl RY) (bl RX)) (bn (bl RW) (bl RV))) (bn (bn (bl RU) (bl RT)) (bn (bl RR) (bl RQ)))) (bn (bn (bn (bl RP) (bl RO)) (bn (bl Jl) (bl Jk))) (bn (bn (bl Jj) (bl Ji)) (bn (bl Jh) (bl Jg))))) (bn (bn (bn (bn (bl Jf) (bl Je)) (bn (bl Jd) (bl Jc))) (bn (bn (bl Jb) (bl Ja)) (bn (bl J9) (bl J8)))) (bn (bn (bn (bl J7) (bl J6)) (bn (bl J5) (bl J4))) (bn (bn (bl J3) (bl J2)) (bn (bl J1) (bl J0)))))) (bn (bn (bn (bn (bn (bl IZ) (bl IY)) (bn (bl IX) (bl IW))) (bn (bn (bl IV) (bl IU)) (bn (bl IT) (bl IS)))) (bn (bn (bn (bl IR) (bl IQ)) (bn (bl IP) (bl IN))) (bn (bn (bl IM) (bl IL)) (bn (bl IK) (bl IJ))))) (bn (bn (bn (bn (bl II) (bl IH)) (bn (bl IG) (bl IF))) (bn (bn (bl IE) (bl ID)) (bn (bl IC) (bl IB)))) (bn (bn (bn (bl IA) (bl Iz)) (bn (bl Iy) (bl Ix))) (bn (bn (bl Iw) (bl Iv)) (bn (bl Iu) (bl It)))))))
def jD (sa sb qa qb:Nat):LR:=(cond (nB 2 (land (shiftRight qa 5) 31)) (cond (nB 24 (land qb 63)) (cond (nB 24 (land (shiftRight qb 18) 63)) (cond (nB 28 sa) (cond (nB 8 (land (shiftRight qa 5) 31)) (cond (nB 8 (land qa 31)) RY RX) (cond (nB 24 (land (shiftRight qb 6) 63)) RW RV)) (cond (nB 2 (land qa 31)) (cond (nB 24 (land (shiftRight qb 6) 63)) RU RT) (cond (nB 24 (land (shiftRight qb 12) 63)) RR RQ))) (cond (nB 2 (land qa 31)) (cond (nB 24 (land (shiftRight qb 6) 63)) (cond (nB 19 (land (shiftRight qb 18) 63)) RP RO) (cond (nB 28 sa) Jl Jk)) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 6 (land (shiftRight qa 5) 31)) Jj Ji) (cond (nB 2 (land (shiftRight qa 10) 31)) Jh Jg)))) (cond (nB 2 (land (shiftRight qa 10) 31)) (cond (nB 24 (land (shiftRight qb 12) 63)) (cond (nB 24 (land (shiftRight qb 18) 63)) (cond (nB 8 (shiftRight qa 20)) Jf Je) (cond (nB 20 sa) Jd Jc)) (cond (nB 2 (land qa 31)) (cond (nB 105 sb) Jb Ja) (cond (nB 2 (shiftRight qa 20)) J9 J8))) (cond (nB 2 (land qa 31)) (cond (nB 24 (land (shiftRight qb 6) 63)) (cond (nB 24 (land (shiftRight qb 12) 63)) J7 J6) (cond (nB 19 (land (shiftRight qb 12) 63)) J5 J4)) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 12 sa) J3 J2) (cond (nB 2 (shiftRight qa 20)) J1 J0))))) (cond (nB 2 (land (shiftRight qa 10) 31)) (cond (nB 90 sb) (cond (nB 6 (land (shiftRight qa 10) 31)) (cond (nB 8 (land (shiftRight qa 15) 31)) (cond (nB 19 (land qb 63)) IZ IY) (cond (nB 6 (shiftRight qa 20)) IX IW)) (cond (nB 2 (land qa 31)) (cond (nB 4 (land (shiftRight qa 10) 31)) IV IU) (cond (nB 8 (shiftRight qa 20)) IT IS))) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 2 (shiftRight qa 20)) (cond (nB 14 (land (shiftRight qb 12) 63)) IR IQ) (cond (nB 8 sa) IP IN)) (cond (nB 2 (shiftRight qa 20)) (cond (nB 8 sa) IM IL) (cond (nB 6 (land (shiftRight qa 10) 31)) IK IJ)))) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 12 sa) (cond (nB 2 (land qa 31)) (cond (nB 24 (land (shiftRight qb 12) 63)) II IH) (cond (nB 24 (shiftRight qb 24)) IG IF)) (cond (nB 8 sa) (cond (nB 4 (land (shiftRight qa 15) 31)) IE ID) (cond (nB 2 (shiftRight qa 20)) IC IB))) (cond (nB 2 (land qa 31)) (cond (nB 6 (shiftRight qa 20)) (cond (nB 12 sa) IA Iz) (cond (nB 8 sa) Iy Ix)) (cond (nB 4 (shiftRight qa 20)) (cond (nB 8 sa) Iw Iv) (cond (nB 4 (land qb 63)) Iu It))))))
lemma ri (b a d c:Nat):dn (jD b a d c) kU:=by unfold jD kU;repeat (first|apply i0|rfl)
def v0:=(19,81,9542656,256451535,G,G,0x24600000000000014a5,0x1863000000000002463,G7)
def v1:=(20,84,6394979,6403215,G,G,0,0,0)
def v2:=(19,72,9538688,155800143,G,G,0x24004a4000000001463,0xc63318c00000000c63,0xc63318c00000002463)
def v3:=(19,67,7444576,155038153,G,G,0x240048c600000000000,0xc63294a00000000000,G5)
def v4:=(19,81,6590464,406696707,Z4,Z4,0x48c00000c300000,0x294a00010200000,0x30c60000a510000)
def v5:=(21,96,6425794,255653403,0x926836db2db,0xd848b6da4db,0x48c652952932529,0x40c6918d2932529,0x294a918d0842529)
def v6:=(18,72,8395872,54362520,Z4,Z4,0,0,0)
def v7:=(20,87,9635936,256471701,G,G,0,0,0)
def v8:=(18,66,9446400,188543631,G,G,Pg,G6,G5)
def v9:=(20,73,6491234,256438927,G,G,0x24634a400000a210000,0x2463318c0000a300000,0x14a5318c0000c210000)
def BZ:=(19,78,4301920,256439247,G,G,zB,zB,5674725539840)
def rX:=(20,63,4395138,321688521,Cy,Cy,0x24a5484090000000c00,0x24a528c6318c0001400,0x24a528c6318c0000c00)
def BY:=(20,98,8591360,324383570,G,G,0,0,0)
def oF:=(20,66,4397184,255652806,G,G,yM,G6,G5)
def Dd:=(19,76,7346368,354755785,G,G,Z6,Z2,0x18c000000000000)
def Gy:=(20,70,4396130,254112271,G,G,0x2463480000000002463,0xc6318c6000000014a5,0x246318c600000002463)
def Gx:=(20,88,6396002,339575317,G,G,0,0,0)
def BX:=(20,88,9670656,307569490,G,G,0,0,0)
def D8:=(24,120,yK,409831122,ru,jv,311728326,311728326,311731488)
def za:=(20,66,6556768,153440850,G,G,OW,0xc6318c600012000000,0x240018c600006318000)
def D4:=(23,96,9445568,306819483,0xdb0036d2400,0xdb0036db000,0x2520498000004212529,0x18c6318c00006302529,0x18c6318600006302529)
def Gw:=(21,99,9538659,460138176,0xdb6d92580db,0xdb6db0092db,PO,0x25294a5294812948000,PO)
def BW:=(11,78,9470976,306782610,G,G,Pq,Pa,P9)
def D1:=(18,69,5377123,322810368,G,G,CC,0x294a00000000000,CC)
def Qa:=(6,45,3148800,254091456,0xc0002240000,5016574230528,0x18c663180000000,0x18c694800000000,0x480063180000000)
def Q9:=(19,84,9506944,357126546,G,G,69271552,Bl,Bl)
def tk:=(20,61,4329604,321188425,G,G,6703672200192,5672681966592,0x918c6318c63)
def BV:=(25,107,6494339,322778843,0xdb6db61b649,0xdb6da49b6c0,0x24a548c69295294a529,0x20a5294a9295294a529,0x24a548c68295294a529)
def vr:=(19,84,9633920,256471698,G,G,0x24634a4000008000000,0x1863318c0000a500000,0x14a5318c0000c108000)
def CX:=(20,87,4492416,306783375,G,G,0,0,0)
def Q8:=(20,78,6524993,256439247,G,G,CG,Z7,CG)
def z9:=(27,116,9642112,342718163,0xdb6c36d20db,0xdb4936d20db,0x25224a5200012949863,0x18c64a520001294a463,0x18c64a520001294a4a5)
def BU:=(20,66,6589504,354767430,G,G,103909442,301993056,103910496)
def wj:=(24,107,7475395,325923803,0xd94824124c0,0xd248241b049,0x24634a52918d2318000,0x24a54a52918d2318000,0x24634a5292946318000)
def CW:=(25,109,9574592,408253591,Fj,Fk,0x25264a46931924224c6,0x2526318c9494c61a4c6,0x18c6498c9318c62a525)
def Gv:=(24,105,6557795,460142025,0xd86da4580db,0x926db4092db,0x4a5200000001421,0x4a5200000001400,0x4a5200000002400)
def jc:=(20,67,8523904,254603983,G,G,303076451,171021411,103916643)
def tj:=(20,84,8587392,457027977,Z4,Z4,69271552,Bl,yp)
def vq:=(20,72,9572448,254103957,G,G,Z6,Z2,Z2)
def z8:=(10,60,6390784,155751558,0xdb601000000,0xdb249000000,0x24004a40318cc630842,0xc63318c90012901800,0xc63318c318cc630c60)
def CV:=(24,108,6524098,459387855,0xd86d925b6db,0x926db01b6db,305243235,305239205,173188195)
def oj:=(20,57,7639040,254079183,BG,BF,0x24630000918c0000c63,0xc630000918c0002463,0x24630000318c0002463)
def CU:=(9,69,3213376,453046299,0xdb24201b6db,0xdb40121b6db,0,0,0)
def vp:=(20,68,8585408,320418383,G,G,301999200,103912547,103913571)
def BT:=(26,110,6592610,460174790,0xd86da498048,0x926db609280,0x4a5200012928421,0x4a5200012738c00,0x4a5200012738c00)
def z7:=(19,75,7542784,405111369,Z4,Z4,o9,Bl,o8)
def CT:=(20,72,6589504,405111177,0xdb6db01b600,0xdb6d925b600,0,0,0)
def Q6:=(13,84,9568256,306782994,rr,rr,0x25204a40631863198c6,0x18c6318c948123018c6,0x18c6318c6318631a520)
def Gu:=(19,75,4398144,255668943,G,G,yM,G9,yM)
def Gt:=(11,60,6391808,154964373,G,G,0x240048c6318c6001ce7,0xc63294a9000a0024c6,0xc6348c6318ca002523)
def Gs:=(24,113,yJ,390706331,CA,yz,Pn,0x24e7000000000002529,Pn)
def z6:=(26,111,6494340,458061015,0xd86db612090,0x926da492090,0x25290000939d2528000,0x2529000094952318000,0x25290000939d2318000)
def Q5:=(18,76,6494208,270869080,jv,ru,0x1863480094800000000,0x18a518c663180000000,0x246018c663180000000)
def z5:=(26,111,8589444,459125715,G,G,0x4a4a0001231a463,0x498c0000a52a463,0x498c0001231a4a5)
def BS:=(24,111,9636963,460173531,0xdb4936c92db,0xdb6c36d80db,w7,w7,w7)
def Q4:=(21,96,6425794,322810395,0xdb6db012480,0xdb6d925b048,0x24a548c60000a002529,0x24a5294a0000a002529,0x24a548c60000a10a529)
def Gr:=(11,60,8486912,155750802,0xdb600000000,0xdb248000000,0x4a40300000018c6,0x318c900000018c6,FY)
def vo:=(28,111,9738337,Bw,yz,CA,0x25294a46000126314a5,0x252939ce0001291a463,0x2529498c0000e73a463)
def Q3:=(21,111,vd,407471259,G,G,9513,9513,9513)
def z4:=(27,117,9741312,yQ,Cz,Cz,FZ,FZ,FZ)
def z3:=(31,110,9736387,457291091,0xdb6da41b0c0,0xdb6da412449,0x2529314494a526324a5,0x2529410894a52919ca5,0x2529314494a4e73a4a5)
def nk:=(20,57,6492288,253293510,G,G,0x24630000918cc318842,0x14a50000918d2300c00,0x246300005294a528c00)
def wi:=(20,54,7477344,253292751,0xdb48b6db6db,0xdb6836db6db,0x24630000918c00014a3,0x14a50000918c0001863,Pj)
def oi:=(20,66,6559744,255652806,G,G,0x918c0000842,0x918c0001800,5674725543008)
def yZ:=(20,63,4493408,153440847,G,G,OW,0xc63180000012000000,0x2400000000006318000)
def Gq:=(23,96,6491299,453097167,0xd8493019249,0x926c12592c0,0x2529000094a52949863,0x2529000094a5294a463,0x2529000094a529494a5)
def wh:=(20,84,6559744,407471232,Z4,Z4,0,0,0)
def CS:=(21,111,9639936,408257688,Fh,t6,0x4a4600012420000,0x318c00012618000,0x498c0000c628000)
def qW:=(20,62,7539840,402747407,0xdb49301b600,0xdb6c125b600,6243,9312,5285)
def CR:=(25,115,6494339,460157911,0xdb49361b6db,0xdb6c249b6db,PN,PN,0x25294a520000a528000)
def BR:=(20,84,8589376,457027977,G,G,68193379,103812195,100672512)
def BQ:=(26,107,6559936,458569043,0x926da49b0db,0xd86db6124db,0x25294a46918c00024a5,0x2529318c929400024a5,0x2529498c929400024a5)
def CQ:=(28,109,6592643,325908181,0x926da49b649,0xd86db61b6c0,0x24634a52918d29498c6,0x24a54a52918d29498c6,0x24634a52318d294a523)
def wg:=(30,109,py,458601679,0xdb6da49b600,FU,0x2529498c94a5290a463,PA,0x25294a4694a4c6314a5)
def Gp:=(24,109,6492323,455456467,FH,FB,0x2529280094a400024a5,0x2529284294a400024a5,0x2529480094a400024a5)
def pJ:=(18,51,4332640,102261147,9914989449947,9914989510875,0xc00000000006000000,0x421000000006000000,0xc00000000002108000)
def vn:=(27,105,6592611,460125897,0xdb6da4980db,0xdb6db6092db,PQ,PQ,0x25294a5252952949c00)
def Go:=(23,95,9733248,455979983,0xdb6d9012000,0xdb6d9012000,305243235,305239205,173188195)
def CP:=(7,36,3213312,153391680,0xc0401200000,5026219032576,Z2,Z2,Z6)
def Gn:=(22,105,8653920,256488603,G,G,Gf,0x14a5000000012900000,Gf)
def Gm:=(22,99,t3,408257865,qd,qd,3171,9216,3168)
def BP:=(25,108,6497408,457815186,0xd84936d20db,0x926c36d20db,0x2529318c94a529018c6,0x2529318c94a4c632520,0x25294a4094a4c6318c6)
def BO:=(20,69,9734144,453882435,Z4,Z4,o9,yN,0)
def BN:=(21,108,vd,460175040,BD,yx,0,0,0)
def Q2:=(22,99,6492259,456980175,0x926db6d8049,0xd86db6c92c0,0x48c6918d29494a5,0x294a918d294a463,0x48c65295294a463)
def BM:=(28,111,6595712,Bw,0xd86db6d20db,0x926db6d20db,0x25294a4600012631463,0x2529318c0001291a463,0x2529498c0000c631463)
def Q1:=(24,99,8589411,456979419,0xda6da418049,0xda6da4092c0,0x252948c6918d231a529,0x2529294a918d231a529,0x252948c65294a52a529)
def Gl:=(23,105,7477347,258847323,CA,yz,Pl,0xc634a5294a4a000000,Pl)
def pI:=(30,117,9738339,yQ,0xdb6da498049,0xdb6db6092c0,0x4a5200012948c63,0x4a5200012948c61,0x4a5200012949c00)
def Gk:=(19,67,7475328,153465043,G,G,Z6,G1,0x2400180000000000000)
def BL:=(28,111,8526020,255702747,G,G,0x246348c694a40000000,0x14a548c694a40000000,0x2463294a94a40000000)
def CO:=(29,105,8591555,455455707,0xdb49361b6c9,0xdb6c249b6c9,0x2529480094a4a50a529,Px,Px)
def wf:=(27,111,8589507,458601303,0xdb4936d24c0,0xdb6c36db049,0x25294a4694a52210000,0x2529318c94a46318000,0x2529498c94a4a318000)
def oh:=(20,57,8523904,ta,G,G,0x24634800518c6318421,0x146318c6918d2000c00,0x146318c6518c631a400)
def BK:=(18,65,4332640,52785371,G,G,0x480000002108000,0x18c600006000000,0x18c600006000000)
def CN:=(29,109,7542980,458076763,0xdb4936124d0,0xdb6c249b091,0x2529494a0000a102529,0x2529494a0000e002529,0x2529494a0000a002529)
def vm:=(24,99,yD,tc,0xd849249b000,0x926c3612400,0x252948c6000123194a5,Rn,PC)
def th:=(28,103,7479491,191738587,0xd96db6db6c0,0xd26db6db649,0x24214a5294a5210a529,OX,OX)
def yY:=(20,64,6492226,154965007,G,G,0x48c6318d2318000,0x294a90012318000,0x48c6318cc528000)
def tg:=(34,121,6595780,393049813,q9,yu,0x4a52948c00024c6,0x4a5293180002523,0x4a5273180001cc6)
def Dk:=(29,111,6494405,460125651,0x926db6db091,0xd86db6d24d0,PP,PP,0x25294a52529400024a5)
def Dj:=(31,110,6592708,393017042,0x926da49b091,0xd86db6124d0,0x24e74a52918d29498c6,0x25254a52918d29498c6,0x24e74a525295294a520)
def Aj:=(11,69,3376128,405111363,0xc06d901b6db,5045932373723,Z6,Z2,Z2)
def Ai:=(6,48,3148800,3969048,5016572133376,0xc0001240000,0,0,0)
def Ah:=(18,66,4364384,156538182,0xdb6836d80db,0xdb48b6c92db,0xc00000000000000421,0x421000000000000c00,0x2400000000000000c00)
def wO:=(25,104,9574592,389919515,0xdb4836d2400,0xdb4836db000,0x252548c694a4c302529,0x24c6294a94a50212529,0x20c648c694a4a512529)
def um:=(27,104,6592704,457016279,0xd86db61b600,0x926da49b600,0x252948c69499231a4c6,0x252928c68421231a525,0x252948c69498a52a0c6)
def wN:=(33,117,9741411,460150479,yz,CA,0x25294a5293180000c63,0x25294a52948c0002463,0x25294a5263180002463)
def rY:=(30,108,9735363,457815753,0xdb6d925b049,0xdb6db0124c0,0x2529494094a52949400,0x2529314a94a52949421,0x2529314a94a5294a400)
def ul:=(12,66,8519680,256438290,0xdb480000000,0xdb480000000,0x24630000918c00018c6,0x14a50000918c00018c6,0x2463000052940002520)
def rW:=(10,57,3245152,302088207,0xdb249009200,0xdb601018000,0x18c6000094980002460,0x18c60000631800014a5,0x2520000094980001863)
def wM:=(21,105,vd,458601801,FO,FR,3171,3171,9216)
def Ag:=(27,123,9741312,409044507,G,G,0x2526000000012930000,0x2108000000012930000,0x2526000000010840000)
def rV:=(10,60,4197472,153464847,9925048776411,9925017581275,0x2400480000000002463,5285,9315)
def wL:=(33,120,9735459,457815576,G,G,0x2529498094a529318c6,0x2529318a94a52932106,0x2529318a94a50842526)
def Di:=(12,63,8487936,354767049,0xdb24b6db600,0xdb6036db600,34638947,100666467,100672512)
def Dh:=(12,78,ro,206095506,yt,yv,0x4a400000c6318c6,0x318c000129018c6,0x318c0000c632520)
def rU:=(22,96,7539811,457027611,0xdb4930092c0,0xdb6c1258049,PF,PF,0x2529294a94a40002529)
def Dg:=(10,72,4295680,107767494,9925017468928,9925048664064,By,By,mJ)
def qv:=(20,73,7571584,455193280,G,G,0x280000012108000,0x184200006318000,0x180000006318000)
def wK:=(16,72,4295779,158111424,G,G,Z9,Z3,0)
def uk:=(10,60,3247136,453058575,0xdb24b01b600,0xdb60125b600,0x948000014a5,6809670657120,6809670654051)
def rT:=(20,66,8686592,255652806,G,G,yM,G9,yM)
def ka:=(19,63,6491233,153465039,G,G,0x24004800000000014a5,OU,OU)
def hN:=(20,67,9637920,188543695,G,G,0x918cc108000,0x918ca300000,5674896556032)
def Df:=(16,69,6392929,251768859,0xdb24b01b640,0xdb60125b640,Hu,P4,Hu)
def rS:=(12,57,7438400,453095616,0xd2248010000,0xd9600009000,Rl,Rl,Rl)
def wJ:=(22,107,6492290,458077139,yy,yy,Rp,Rp,Rp)
def Af:=(24,113,yD,392246807,0x926c249b0db,0xd84936124db,zB,0x92940000000,0x92940000000)
def wI:=(28,117,4498562,359487189,G,G,0x1cc64a5200000001cc6,0x24c64a5200000002523,0x25234a52000000024c6)
def Ae:=(19,63,8526848,154964943,G,G,0xc2148c690012318000,0xc63294a318d2318000,0x140048c6318ca528000)
def wH:=(29,117,9734432,458077527,Z4,Z4,0x4a42000126324c6,0x398c00012919ce7,0x398c0000e73a525)
def qu:=(10,60,6295552,155750802,0x920036c00db,0xd80036c00db,0x24004a40318c00018c6,0xc63318c900000018c6,0xc63318c318c0002520)
def Ad:=(26,103,8525956,323859163,0xdb483612290,0xdb48249a090,0x246348c694a4a10a529,0x24a5494a94a4a10a529,0x24a5494a94a5210a529)
def lv:=(22,81,t3,455455305,qd,qd,0x2529000000006000c63,0x2529000000006002400,0x2529000000006318c60)
def oE:=(10,60,6295552,Bq,0xd8002400000,0x92002400000,Po,P7,Gd)
def lu:=(28,111,9738368,Bw,yy,yy,0x2529000094a52618c63,0x2529000094a5261a463,0x2529000094a4c632463)
def De:=(10,63,4327424,252506331,0xdb48201b6db,0xdb48121b6db,tV,tT,tU)
def ls:=(28,105,9574595,258847323,0xdb6db61b6c0,0xdb6da49b649,0xc634a5294a52002529,0x24634a5294a46002529,0x14634a5294a46002529)
def lq:=(33,117,9736451,Bx,0xdb6da41b449,0xdb6da41b4c0,0x25294a4694a526324c6,0x2529398c94a52919cc6,PK)
def Ac:=(24,111,8591488,325924563,t6,Fh,0x24634a5292952948000,0x24a54a52918d2948000,0x24a54a5292952948000)
def Ab:=(28,117,9738368,458077527,G,G,0x4a42000126324c6,0x398c0001291a4e7,0x398c0000e73a523)
def mP:=(30,111,9736324,458077395,BE,BE,0x48c60001231a463,0x48c60001252a463,0x48c60001231a463)
def oD:=(25,102,6592640,457028562,FU,0xdb6da49b600,0x252948c694a523198c6,0x2529294a94a5231a520,0x252948c694a4a5298c6)
def Aa:=(20,57,8490083,254055369,G,G,0x24634800318c0000c63,0x246318c690000000c63,0x14a518c6318c0002400)
def A9:=(20,75,6490304,321729483,G,G,0x4842918c0000000,0x28c692940000000,0x28c6918c0000000)
def oC:=(23,99,6590592,tc,Fi,Fi,0x252948c600012319463,Rn,0x252948c60000a529463)
def qs:=(8,36,4293632,153391680,0xdb601000000,0xdb249000000,Pe,Z2,0xc0018c600000000000)
def Dc:=(24,111,6492292,325924311,BE,BE,0x24634a52918d2630000,0x24a54a5292952928000,0x24a54a5292952630000)
def lp:=(32,114,8591558,460173723,FJ,FM,Rq,Rq,Rq)
def Db:=(7,54,4292608,304422921,9993717809152,0xd06d8000000,0x18c6480094800000000,Gd,0x252018c663180000000)
def A8:=(29,117,9642176,258061851,G,G,0x2463000000012930000,0x14a5000000012930000,Gf)
def qq:=(9,51,3247104,251719701,0xc024b000000,5042310742016,0x24630000918c0001ce7,0x14a50000918c0002523,0x24630000529400024c6)
def uj:=(22,99,6492259,455456457,0xd86da418049,0x926da4092c0,Hp,Hp,0x480094a52948000)
def ui:=(30,107,9643200,457012187,Z4,Z4,PE,0x2529294a0001231a529,0x252948c60000a52a529)
def A7:=(32,114,9736388,457815507,0xdb6db6db690,0xdb6db6db690,0x2529494094a5262a4a5,0x2529314a94a5272a4a5,0x2529314a94a526324a5)
def uh:=(30,115,6595776,458601811,0xd86db6db0db,0x926db6d24db,0x498c0001291a4a5,0x318c00012632463,0x4a460000c6324a5)
def A6:=(24,103,6492292,455980243,0xd849241b690,0x926c241b690,Rm,Rm,Rm)
def qp:=(41,125,9741574,459650519,G,G,0x2529000094a526324c5,0x2529000094a5292a4e7,0x2529000094a526324e5)
def A5:=(32,111,8591620,458076891,0xdb49361b6db,0xdb6c249b6db,0x2529494494a5210a529,Pz,Pz)
def wG:=(26,103,8591552,322810843,0xdb6c36124db,0xdb49249b0db,0x246348c694a52318000,0x24a5294a94a52318000,0x24a548c694a4a528000)
def rR:=(8,38,2230272,185397824,8823089659904,4974813642752,0x24210000918d2000000,OZ,OY)
def rQ:=(28,117,9736291,457815762,0xdb6da4180db,0xdb6da4092db,FC,FC,FC)
def mO:=(31,117,9741440,Bx,Z4,Z4,0x25290000000129198c6,0x2529000000012632523,0x252900000000c6324c6)
def ug:=(21,99,9639936,258799311,0xdb6c2480000,0xdb493600000,0x24630000918c00014a5,0x14a50000918c0002463,Pj)
def oB:=(36,119,9738438,458061527,0xdb6db61b092,0xdb6da4924d8,0x252948c6949529498c6,0x2529314a9319294a525,0x2529494a9319294a4c6)
def Da:=(21,99,6491328,tc,0xd849125b000,0x926c3012400,PD,0x2529294a000123194a5,PC)
def A4:=(9,48,4294656,154964928,9921393328128,9905436098560,0x240048c6318d2318000,0xc63294a90012318000,0xc6348c6318ca528000)
def wF:=(7,39,3147840,151056399,0xc000201b600,5016540788224,0x24000000918c0001463,0x918c0002463,5674725545059)
def rP:=(31,119,6592708,323860187,FV,FQ,0x24a548c600000000000,0x24a5494a00000000000,0x2463494a00000000000)
def wE:=(37,125,9741601,459372059,G,G,0,0,0)
def rO:=(20,60,9732160,253293513,0xdb6d801b600,0xdb6d801b600,tV,tT,tU)
def uf:=(26,95,9732352,455979983,BC,BC,0x2529304094a5231a463,0x2529188494a52300c63,0x252918c494a4a52a460)
def ue:=(26,111,4498560,325924563,yy,yy,0x24630000918c00024a5,0x24a50000918c0002463,0x2463000092940002463)
def D9:=(20,75,9734144,454668681,0xdb6da01b600,0xdb6d921b600,1057,9216,3072)
def jd:=(32,111,8591558,460125903,0xdb6c36db092,0xdb4936d24d8,0x25294a52318c0002463,0x25294a52918c0000c63,0x25294a52918c0002463)
def im:=(20,57,4460672,153416271,G,G,0xc634800918c6318000,0xc6318c6318d2000000,0x240018c6918c6318000)
def A3:=(10,51,7438336,254079177,0xd2248000000,0xd9600000000,0x24604800618c0000c63,0x14a518c691800000c63,0x186318c652940002400)
def rN:=(10,54,yC,105406866,FA,FG,0x4a40300042118c6,0x318c300063018c6,0x318c1084c002520)
def ud:=(7,28,t7,153391168,9895640563712,9895657078784,q8,Z3,q8)
def qo:=(8,33,2165792,251695113,8805807063040,4965001363456,0x2463000090000000c63,0x14a50000318c0002400,0x24630000318c0000c63)
def D7:=(11,57,6423552,ta,0xd848101b600,0x9248101b600,0x24604800618c6318c63,0x14a518c691812000c63,0x186318c65294631a400)
def A2:=(24,105,yD,457815183,0xdb49249b0db,0xdb6c36124db,0x2529318c94a52902463,PA,0x25294a4094a4c6314a5)
def D6:=(9,60,7405568,354766857,0xdb24001b600,0xdb40001b600,0x2523000000000000c63,0x1ce7000000000000c63,0x24c6000000000002400)
def oA:=(26,99,8658016,255701979,CA,yz,0x246348c60001231a529,0x14a5294a0001231a529,0x246348c60000a52a529)
def D5:=(24,105,yK,406684635,jv,ru,0x252648c60001231a529,0x2108294a0001231a529,0x252648c60000a52a529)
def wD:=(24,105,yK,457028565,jv,ru,0x252948c6000123198c6,0x252918c60001231a523,0x252948c60000631a4c6)
def rM:=(39,122,9740580,458864087,G,G,0x25294a4894a526324e7,0x252939ce94a5292a4c6,0x2529498c94a4e73a525)
def A1:=(27,113,9732384,457553237,G,G,0x49080001291a523,0x3186000126318c6,0x31860000c6324c6)
def A0:=(24,103,8526016,322810843,0xdb4836d24db,0xdb4836db0db,Pk,Pm,0x24a548c60000a318000)
def il:=(39,121,9738534,456505051,0xdb6db61b692,0xdb6da49b6d8,0x2529488294a40000000,Pu,Pu)
def zZ:=(24,103,4464768,456995803,G,G,0x252948c600012318000,0x2529294a00012318000,0x252948c60000a528000)
def wC:=(36,121,9738531,458602195,0xdb6da49b649,0xdb6db61b6c0,0x498694a40002463,0x318c94a40002463,0x498694a400024a5)
def zY:=(22,97,6492352,455455699,0xdb49241b000,0xdb6c2412400,0x2529480094a5231a4a5,0x2529284294a5231a4a5,0x2529280094a4a52a4a5)
def uc:=(8,54,3246080,w5,0xc024a000000,5042310479872,0,0,0)
def zX:=(21,93,vd,455455317,FR,FO,Z6,Z2,Z2)
def zW:=(21,93,9443520,255701595,0xdb003612400,0xdb00249b000,yM,0x2463294a00000000000,0x14a548c600000000000)
def oz:=(32,113,9736419,455456471,0xdb6db6db649,BI,0x480094a52948000,Hp,Hp)
def zV:=(21,93,9732192,455456073,0xdb6d8018000,0xdb6d8009200,0x2529480000012918c63,0x252918c600012630c63,0x252918c60000c632400)
def ub:=(34,119,9740544,458601815,G,G,0x25294a46000126324c6,0x2529398c0001291a4c6,0x2529498c0000e73a525)
def zU:=(6,29,4196352,20746307,9895640301568,9895640301568,0,0,0)
def rL:=(26,102,8591552,457027995,0xda4936d2400,0xda6c36db000,0x2529000000004202529,0x2529000000006102529,0x252900000000a002529)
def oy:=(7,35,t7,3932873,9895623786496,9895654981632,CC,0x294a00000000000,CC)
def zT:=(26,103,6494402,455979739,0xd8493612480,0x926c249b048,Hv,Hv,Hv)
def rK:=(5,36,3211264,4718610,0xdb400000000,0xdb240000000,0x4a40000000018c6,0x318c000000018c6,FY)
def ox:=(28,111,9736291,457029327,yz,CA,0x48c694a40000c63,0x18c694a40002463,0x48c694a40002463)
def mN:=(7,36,t7,73746,9895654981632,9895623786496,0,0,0)
def k9:=(33,123,9738435,460174299,0xdb6db6d24c0,0xdb6db6db049,0x2529000094a4c31a529,0x2529000094a52302529,0x2529000094a4631a529)
def wB:=(38,123,9740486,458602197,rv,CB,0x4a4694a40001ce7,0x39ce94a400024c6,0x498c94a40002523)
def wA:=(19,66,9732128,354767430,G,G,103908385,301993056,103913472)
def wz:=(22,93,7444672,455454939,0xdb24b6d2400,FK,w7,w7,w7)
def wy:=(22,93,t3,457028553,qd,qd,305237091,305237091,103916544)
def zS:=(12,63,9535488,304423497,rr,rr,Pp,P8,P6)
def D3:=(15,72,6488160,453096576,0xdb6d8018000,0xdb6d8009200,0x94a52900000,0x94a4c630000,0x94a4c630000)
def ow:=(28,107,9735392,455979995,0xdb6db01b600,0xdb6d925b600,Pr,Pr,0x252900000000631a529)
def fW:=(20,65,6492288,453620288,Z4,Z4,o9,yN,kr)
def zR:=(30,107,py,389919707,FT,FP,0x24e548c60001231a529,0x24e7294a0001231a529,0x24e548c60000a52a529)
def zQ:=(26,103,8528064,322810843,0xdb6db6d2400,0xdb6db6db000,Pk,Pm,0x24a548c60000a528000)
def lo:=(26,103,9736320,457028563,Fi,Fi,PD,0x252918c60001231a463,0x252948c60000631a463)
def rJ:=(26,103,6561920,457028563,0xd86db6db600,0x926db6db600,0x252948c60001231a4a5,Rn,0x252948c60000a52a4a5)
def ua:=(8,49,2164800,vh,0xdb24201b6db,0xdb40121b6db,Pi,G7,Ph)
def rI:=(22,75,9732224,453882441,zC,zC,0x2529000094a52002400,0x2529000094a46318c63,0x2529000094a46318c60)
def wx:=(22,91,9734208,455455315,0xdb6da009000,0xdb6d9210000,0x48000000631a463,0x18c600012002463,0x18c60000631a4a5)
def qn:=(7,18,4260864,ve,0xd0401000000,9974004580352,CF,CE,CD)
def ov:=(42,126,9741606,460174491,G,G,0x94a52502529,0x94a4c50a529,0x94a4c52a529)
def D2:=(21,87,6592512,Bo,0x926db61b6db,0xd86da49b6db,Rj,Ga,Ri)
def ln:=(8,27,px,2359881,Fx,FD,0x480000006318000,0x18c600012000000,0x18c60000631a400)
def qm:=(19,57,9733120,ta,G,G,Rh,G8,Gg)
def ww:=(22,87,9732224,455455689,zC,zC,0x2529480000012318c63,0x252918c600012318c63,0x252918c60000631a400)
def wv:=(6,26,2164736,184610816,8805790253056,4965001068544,0x24210000918c0000000,OZ,OY)
def lm:=(26,99,9740288,tc,0xdb6db680000,0xdb6db680000,PI,Py,PH)
def zP:=(20,81,8591360,158111433,G,G,CF,CE,CD)
def rH:=(36,115,9738438,457029331,0xdb6db69b092,0xdb6db6924d8,0x252948c694a52949863,0x252930c694a5294a4a5,0x2529294a94a5294a463)
def wu:=(36,115,9738500,456504667,FV,FQ,0x252948840001291a529,0x252930c600012632529,0x252918c60000c632529)
def zO:=(28,103,6494404,455979739,0xdb49361b690,0xdb6c249b690,Hv,0x2529484294a4a10a529,0x2529284294a5210a529)
def ql:=(8,43,4196416,151072783,9895638316544,9895623636480,0x24000000918c0002463,0xc63000092940002463,0xc630000918c00014a5)
def gy:=(8,18,6356992,ve,0xdb440000000,0xdb440000000,Ht,Z3,G1)
def zN:=(3,27,1082368,27,4406653222912,4406653222912,0,0,0)
def D0:=(4,30,2162688,153367104,8813272891392,4957466001408,Z6,Z2,Z2)
def iQ:=(34,111,9738436,yP,FV,FQ,PE,0x252928c60001231a529,0x252948c60000a31a529)
def ou:=(39,115,9741603,458077147,BI,0xdb6db6db649,Ro,PJ,0x2529494a94a4a52a529)
def wt:=(13,54,6489088,w5,0xd8491000000,0x926c1000000,rx,rx,rx)
def ws:=(13,54,6488096,w5,0xdb490008000,0xdb6c0008000,rx,rx,rx)
def wr:=(20,75,8394944,153465051,G,G,Pe,OT,OT)
def wq:=(30,105,py,456241947,Fk,Fj,0x252930c094a4c302529,0x2529210894a4c302529,0x252930c094a48422529)
def zM:=(24,87,8658944,Bo,G,G,Rj,Ga,Ri)
def zL:=(5,24,2162720,201375744,8805756731392,4964982226944,P5,0x1084000061800000000,0x1860000042100000000)
def ot:=(16,63,6488192,453096000,0xd8490012000,0x926c0012000,0x94a52000000,0x94a46318000,0x94a46318000)
def wp:=(8,39,4261888,3933129,9912803393536,9905301880832,0x48c600012318c63,0x294a00012318c63,0x48c60000a52a400)
def rG:=(16,63,6492160,Bt,0xdb49241b600,0xdb6c241b600,3171,9216,3171)
def qk:=(9,39,yF,153391305,yw,yw,Ge,G4,G3)
def wo:=(8,18,qS,2396160,tQ,tQ,0x180030000000000,0x18c630000000000,0x1800318c0000000)
def tZ:=(9,39,6389760,103047753,0x92600000000,0xd8248000000,0x480000006318c63,0x18c600012000c63,0x18c60000631a400)
def zK:=(12,48,ro,402751488,rr,rr,0x2526000094980000000,0x2108000094980000000,0x2526000084200000000)
def zJ:=(27,93,9738336,454668699,0xdb6db609200,0xdb6da498000,0x2529180094a46002529,Pt,0x2529180094a4210a529)
def CZ:=(8,22,qS,35152006,tQ,tQ,0x180030000000000,0x84230000000000,0x180010840000000)
def qj:=(42,125,9741606,459126359,G,G,0x2529498c94a400024c6,0x2529418c94a40002525,0x25294a4a94a400024c6)
def qi:=(12,45,ro,153391689,yt,yv,Pf,OS,G2)
def os:=(30,99,py,Bu,Fk,Fj,0x2529180094a52002529,Pt,0x2529480094a4210a529)
def k8:=(8,18,qS,2359305,tQ,tQ,Z6,Z2,Z2)
def wn:=(9,36,yF,Bp,yw,yw,Rk,Gc,Gb)
def wm:=(24,81,yD,yO,0xd8493612400,0x926c249b000,w8,w8,w8)
def rF:=(24,81,yJ,yO,0xdb6db009200,0xdb6d9258000,w8,w8,w8)
def qh:=(36,117,yL,457815195,Z4,Z4,w7,w7,w7)
def cI:=(45,122,Z1,460170959,G,G,PS,0x25294a5294a1294a463,PS)
def CY:=(4,21,3178496,2359497,5045915484160,0xc06d8000000,Z6,Z2,Z2)
def oq:=(30,99,py,Bu,Fk,Fj,PB,Pw,Pv)
def k7:=(8,30,px,yq,FD,Fx,tV,tT,tU)
def wl:=(42,123,9741606,459125979,G,G,PL,0x25294a4a94a5252a529,PL)
def wk:=(5,18,4227072,2359305,9904194584576,9904194584576,Z6,Z2,Z2)
def kZ:=(36,111,yL,yP,Z4,Z4,0x48c694a52318000,0x18c694a52318000,0x48c694a46318000)
def tY:=(8,24,px,100700736,tR,tR,Z3,3298836873216,mJ)
def qf:=(10,30,yC,yq,FG,FA,tV,tT,tU)
def op:=(18,54,yI,w5,rr,rr,rx,rx,rx)
def oo:=(8,24,px,153378816,tR,tR,Z6,0,0)
def mM:=(40,119,9741604,Bv,G,G,Ro,PJ,0x252948c694a5252a529)
def rE:=(6,15,4259840,100700160,9905268326400,9912784519168,0xc00000090000000000,G0,Hr)
def ll:=(8,18,px,ve,tR,tR,Ht,0x421000090000000000,Hr)
def lk:=(4,0,3146752,0,0xc0001000000,5016538578944,0,0,0)
def om:=(12,30,ro,yq,yt,yv,tV,tT,tU)
def lj:=(6,12,4259840,100687872,9912784519168,9905268326400,0xc00000030000000000,G0,Hr)
def rD:=(8,18,8388608,ve,yw,yw,CF,CE,CD)
def mK:=(4,0,qR,0,Z3,Z3,0,0,0)
def ol:=(4,0,2162688,0,4964982194176,8805756698624,0,0,0)
def jy:=(44,119,9741608,Bv,G,G,CH,CH,CH)
def eu:LR:=[(v0,0),(v1,0),(v2,0),(v3,0),(v4,0),(v5,0),(v6,0),(v7,0),(v8,0),(v9,0),(BZ,0),(rX,0),(BY,0),(oF,0),(Dd,0),(Gy,0),(Gx,0),(BX,0),(D8,0),(za,0),(D4,0),(Gw,0),(BW,0),(D1,0),(Qa,0),(Q9,0),(tk,0),(BV,0),(vr,0),(CX,0),(Q8,0),(z9,0),(BU,0),(wj,0),(CW,0),(Gv,0),(jc,0),(tj,0),(vq,0),(z8,0),(CV,0),(oj,0),(CU,0),(vp,0),(BT,0),(z7,0),(CT,0),(Q6,0),(Gu,0),(Gt,0),(Gs,0),(z6,0),(Q5,0),(z5,0),(BS,0),(Q4,0),(Gr,0),(vo,0),(Q3,0),(z4,7),(z3,0),(nk,0),(wi,0),(oi,0),(yZ,0),(Gq,0),(wh,0),(CS,0)]
def eO:LR:=[(qW,0),(CR,0),(BR,0),(BQ,0),(CQ,0),(wg,0),(Gp,0),(pJ,0),(vn,0),(Go,0),(CP,0),(Gn,0),(Gm,0),(BP,0),(BO,0),(BN,0),(Q2,0),(BM,0),(Q1,0),(Gl,0),(pI,0),(Gk,0),(BL,0),(CO,0),(wf,0),(oh,0),(BK,0),(CN,0)]
def fq:LR:=[(vm,0),(th,0),(yY,0),(tg,0),(Dk,0),(Dj,0),(Aj,0),(Ai,0),(Ah,0),(wO,0),(um,0),(wN,0),(rY,0),(ul,0),(rW,0),(wM,0),(Ag,7),(rV,0),(wL,0),(Di,0),(Dh,8),(rU,0)]
def fU:LR:=[(Dg,0),(qv,0),(wK,0),(uk,0),(rT,0),(ka,0),(hN,0),(Df,0),(rS,0),(wJ,0),(Af,6),(wI,0),(Ae,0),(wH,0),(qu,0),(Ad,0),(lv,0),(oE,0),(lu,0)]
def gu:LR:=[(De,0),(ls,0),(lq,0),(Ac,0),(Ab,0),(mP,0),(oD,0),(Aa,0),(A9,0),(oC,0),(qs,0),(Dc,0),(lp,9),(Db,0),(A8,0),(qq,0)]
def gZ:LR:=[(uj,0),(ui,0),(A7,0),(uh,0),(A6,8),(qp,0),(A5,0),(wG,0),(rR,0),(rQ,0),(mO,0),(ug,0),(oB,0),(Da,0),(A4,0)]
def i6:LR:=[(wF,0),(rP,0),(wE,6),(rO,0),(uf,0),(ue,0),(D9,0),(jd,0),(im,0),(A3,0),(rN,0),(ud,0),(qo,0),(D7,0)]
def iM:LR:=[(A2,0),(D6,0),(oA,0),(D5,0),(wD,0),(rM,0),(A1,8),(A0,0),(il,8),(zZ,0),(wC,0),(zY,0),(uc,0)]
def jq:LR:=[(zX,0),(zW,9),(oz,0),(zV,0),(ub,0),(zU,0),(rL,0),(oy,0),(zT,0),(rK,0),(ox,0),(mN,0),(k9,0)]
def k5:LR:=[(wB,0),(wA,0),(wz,0),(wy,0),(zS,0),(D3,0),(ow,0),(fW,0),(zR,0),(zQ,0),(lo,0)]
def j6:LR:=[(rJ,0),(ua,6),(rI,0),(wx,0),(qn,0),(ov,0),(D2,7),(ln,0),(qm,0),(ww,0),(wv,0)]
def jN:LR:=[(lm,0),(zP,0),(rH,0),(wu,0),(zO,6),(ql,0),(gy,0),(zN,7),(D0,0),(iQ,0),(ou,0)]
def kW:LR:=[(wt,0),(ws,0),(wr,9),(wq,0),(zM,7),(zL,8),(ot,0),(wp,0),(rG,0),(qk,9),(wo,7),(tZ,0)]
def mC:LR:=[(zK,8),(zJ,0),(CZ,7),(qj,0),(qi,0),(os,0),(k8,0),(wn,0),(wm,6),(rF,0),(qh,6)]
def pz:LR:=[(cI,0),(CY,0),(oq,0),(k7,8),(wl,0),(wk,0),(kZ,6),(tY,0),(qf,0),(op,8)]
def rz:LR:=[(oo,0),(mM,6),(rE,0),(ll,0),(lk,0),(om,8),(lj,0),(rD,0),(mK,9),(ol,8),(jy,6)]
def j7:LR:=eu++eO++fq++fU++gu++gZ++i6++iM++jq++k5++j6++jN++kW++mC++pz++rz
def zE:BTree LS:=(bn (bn (bn (bn (bn (bl [Qa,wh,CP,BN,qv,rS,qs,rR,A4,ud,uc,D3,fW,qn,wv,gy,D0,wt,ws,zL,ot,wo,zK,wn,k7,tY,qf,op,oo,rE,ll,lk,om,lj,rD,mK,ol]) (bl [Q8,vo,ka])) (bn (bl [BT]) (bl [v6,Q5,CS,CQ,Dk,Ai,lq,cI]))) (bn (bn (bl []) (bl [])) (bn (bl [Gv,vn,pI,rY,Aa,uj]) (bl [Df,wE])))) (bn (bn (bn (bl []) (bl [v1,BY,BX,D8,za,BW,Q9,vr,Q6,Gr,Gq,BP,Q2,wN,ul,Dh,qu,oD,rN,rK,ox,mN])) (bn (bl []) (bl [CR,wf,oz]))) (bn (bn (bl [oF,BU,z8,nk,oi,Ah,Dg,rT,wA,CZ]) (bl [z3,Gp,Dj,wC])) (bn (bl []) (bl [BV,wj,BS,Q1,Gl,CO,th,rU,ls,k9,ou]))))) (bn (bn (bn (bn (bl [lp,il,ov,wl]) (bl [v9,Gy,CV,yY])) (bn (bl [v3,Dd,tj,z7,CT,z4,BR,Gm,oh,wM,Di,lv,oE,Db,rO,D9,A3,qo,D7,D6,zV,oy,wy,zS,rI,ln,qm,ww,zP,wp,rG,qk,tZ,qi,k8,CY,wk]) (bl [tg,rH]))) (bn (bn (bl []) (bl [v7,vq,Gt,wJ,qq,rQ,mO,jd,wD,A1,zX])) (bn (bl [tk]) (bl [v5,Q4,qp,oB,zT,qj])))) (bn (bn (bn (bl [v4,Gw,D1,BO,Aj,wK,zU,jy]) (bl [z9,BQ,Gk,Ac,uh,ue,zY,lo,rJ,wx])) (bn (bl [rX,A9]) (bl [D4,CU,Gs,z6,Q3,pJ,Gn,BK,wO,Ag,wL,De,Dc,A8,ui,wG,oA,D5,rM,A0,zZ,zW,rL,wB,wz,ow,zR,zQ,D2,zN,wr,wq,zM,zJ,os,wm,rF,qh,oq,kZ]))) (bn (bn (bl []) (bl [Gx,CW,z5,um,Af,wI,wH,Ab,mP,A7,A6,ub])) (bn (bl [v0,v2,v8,BZ,CX,jc,oj,vp,Gu,wi,yZ,qW,wg,Go,BM,vm,rW,rV,uk,hN,Ae,lu,oC,ug,Da,wF,uf,im,A2,ua,lm,ql]) (bl [BL,CN,Ad,A5,rP,wu,zO,iQ,mM]))))))
def RN:LR:=[(cI,8),(cI,5),(jy,1),(cI,0),(kZ,1),(mM,4),(wE,3),(ou,4),(jy,0),(ou,3),(qj,5),(wl,5),(cI,2),(wl,3),(ou,9),(wE,4),(jy,2)]
def RM:LR:=[(jy,2),(cI,1),(cI,3),(cI,2),(cI,7),(jy,0),(mM,2),(qj,8),(il,2)]
def RK:LR:=[(cI,1),(cI,7),(jy,0),(cI,4),(ov,6),(il,3),(cI,2),(mM,1),(jy,4),(wC,8),(ov,8),(qp,0),(ou,7)]
def RJ:LR:=[(cI,5),(mM,0),(il,0),(rH,8),(jy,2),(ov,2),(qj,8),(wl,0),(wu,8)]
def RI:LR:=[(cI,7),(cI,1),(cI,6),(kZ,1),(qp,8),(cI,0),(wN,1),(iQ,4),(cI,2),(pI,8),(lu,7),(ox,7),(pI,0),(il,2),(rM,0),(mP,0),(k9,0),(tg,1),(ov,8),(ou,4),(tg,6),(wC,2)]
def RH:LR:=[(cI,1),(cI,2),(cI,3),(il,1),(cI,8),(cI,7),(lp,0),(jy,4),(jy,3),(kZ,3),(cI,0),(qh,1),(cI,4),(qh,3),(iQ,5),(pI,1),(ox,2),(oB,3),(oB,6),(lq,2),(kZ,1),(il,3),(lu,1),(BL,2),(rP,6),(mM,1),(rQ,9),(mM,4),(oz,3),(qj,2),(wC,6),(CN,5),(qp,6),(qp,2),(wB,2),(jd,0),(rQ,1),(tg,7),(rH,2),(Dj,0)]
def RG:LR:=[(cI,3),(ov,6),(il,0),(jy,2),(lp,2),(iQ,8),(oz,0),(oB,8),(mP,5),(jd,7),(k9,2),(k9,6),(wB,5),(oB,7),(rQ,0),(A8,9),(A8,4),(iQ,2),(wE,1),(tg,3),(rM,2),(mM,2),(qp,5),(rM,5),(rP,0),(qp,3),(ou,6),(pI,5),(rP,8)]
def RF:LR:=[(jy,0),(iQ,0),(ox,8),(oz,8),(iQ,6),(zO,0),(CN,6),(qj,3),(mP,0),(wB,3),(CN,0),(lq,3),(ou,6),(th,2),(rQ,8),(A5,0),(ox,3),(rH,8),(oB,1),(A5,6),(mP,3)]
def RE:LR:=[(cI,7),(lp,4),(cI,3),(lp,3),(il,2),(k9,8),(oi,5),(pI,0),(k9,4),(lq,7),(mM,2),(Q1,9),(vn,7),(oz,1),(Gv,4),(ls,4),(il,1),(BT,6),(wI,3),(z3,3),(wf,3),(CR,7),(rX,9)]
def RD:LR:=[(lp,2),(cI,5),(rU,2),(oz,8),(oF,3),(k9,2),(k9,6),(iQ,8),(il,0),(vn,3),(Gq,0),(ls,6),(ox,0),(Aa,3),(pI,5),(rU,6),(BL,0),(BS,2),(BS,6),(wK,3),(jc,3),(jd,7),(jd,3),(pI,3)]
def Ir:LR:=[(oF,3),(cI,2),(wK,0),(wI,3),(pI,9),(ls,8),(uj,7),(fW,5),(mP,5),(jd,0),(ox,7),(rU,4),(tk,4),(iQ,4),(uj,2),(Df,4),(ox,9),(Aa,0),(tk,5),(Ac,9),(vn,0),(BL,4),(Q2,2),(z6,2),(Ac,3),(wj,3),(rQ,2),(ka,4),(ka,5),(BT,2),(Gl,8),(v4,5),(z5,5),(rY,7),(rP,8),(v9,3),(jc,9),(iQ,1),(vn,9),(yY,5),(CR,1),(rP,4),(oB,7),(wf,5),(z5,2),(jc,3),(vo,5),(z9,9)]
def Iq:LR:=[(im,1),(oq,1),(jc,7),(BK,1),(kZ,1),(lo,7),(za,1),(iQ,4),(ow,1),(Go,7),(lq,7),(vq,1),(vr,4),(qW,1),(oF,3),(oA,1),(oF,1),(z3,4),(oD,7),(vr,9),(tj,4),(fW,7),(zZ,1),(zJ,7),(za,7),(jc,1),(vm,7)]
def Ip:LR:=[(zO,0),(zT,6),(jd,8),(mP,0),(tk,9),(ls,2),(mP,3),(BL,2),(CO,6),(zT,0),(z5,9),(BQ,5),(CO,0),(z6,0),(Dk,5),(wJ,8),(Gx,6),(yY,6),(A7,3),(A7,8),(il,3),(Dc,0),(A6,0),(z5,0),(A6,3),(Ad,0),(Ad,3),(Gp,8),(wj,4),(BV,4),(nk,4),(rX,5),(CV,0),(wf,0),(mP,9),(rX,0),(wj,0),(th,2),(oB,1),(z6,6),(z6,9),(CR,0),(jd,5),(iQ,0),(wj,5)]
def Io:LR:=[(nk,3),(ls,9),(fW,3),(oF,3),(lo,3),(vn,5),(tk,4),(os,9),(vo,3),(uj,3),(jc,9),(oA,9),(Gq,6),(v1,2),(lo,9),(il,3),(qW,3),(jc,5),(Gx,6),(vm,3),(th,2),(ow,3),(jc,3),(z5,0),(rL,9),(yY,9),(z3,3),(pJ,9),(lp,0),(wJ,3),(v4,3),(ui,9),(yY,3),(oC,3),(im,5),(lu,3),(th,0),(wi,9),(zY,3),(wI,4),(wO,9),(v9,5),(CO,9),(Gp,3)]
def In:LR:=[(pI,8),(vn,1),(rF,9),(BS,0),(uj,8),(pI,1),(Gw,1),(jc,3),(th,7),(rU,9),(rU,0),(yZ,9),(vn,8),(yY,0),(ua,4),(qW,3),(jd,5),(rY,8),(wN,1),(nk,5),(BS,9),(rX,0),(Gv,8),(ka,9),(lp,0),(vq,9),(oz,3),(Gw,5),(il,3),(jd,4),(BV,7),(Gl,9),(wj,7),(wJ,1),(rX,1)]
def Im:LR:=[(rI,1),(cI,1),(oh,1),(jc,9),(ue,7),(ls,0),(rY,1),(BK,7),(vr,9),(im,1),(nk,7),(BQ,1),(z9,1),(lo,1),(oC,1),(ql,1),(fW,1),(im,7),(ka,7),(qW,1),(jc,3),(CW,1),(oD,1),(v9,0),(wg,1),(v6,7),(rV,1),(lq,1),(oF,3),(lp,0),(vp,9),(k9,0),(ql,3),(ua,1),(CX,9),(uf,1),(z6,8),(rJ,1),(ue,1),(jd,1),(oF,1),(iQ,0)]
def Il:LR:=[(qh,0),(cI,7),(cI,1),(cI,6),(BM,0),(lu,0),(mO,0),(tg,6),(CQ,0),(vo,0),(wg,0),(uh,0),(uh,6),(pI,8),(rM,6)]
def Ik:LR:=[(kZ,0),(oq,0),(qh,0),(lo,0),(oC,0),(rF,0),(ow,0),(lq,0),(os,0),(rM,0),(za,0),(zQ,6),(BU,0),(BQ,0),(ub,0),(oD,0),(rY,8),(uh,6),(wq,0),(rJ,0),(ui,6),(zR,0),(um,0),(rH,0),(Gs,0),(wx,0),(wu,0)]
def Ij:LR:=[(kZ,0),(os,6),(uf,3),(qh,0),(wm,0),(os,0),(ov,3),(wz,0),(A0,6),(wr,0),(wg,6),(A2,6),(zW,0),(ui,0),(ub,6),(th,9),(v5,0),(CV,0),(wG,0),(rL,0),(rL,6),(ow,6),(wg,0),(wz,6),(wL,3),(ow,0),(Af,0),(wG,6),(A9,0),(wH,6),(oq,0),(zR,0),(A1,3),(wO,6),(lq,6),(oq,6),(vm,0),(D4,0),(th,6),(wq,0),(ui,6),(Da,6),(wq,6),(vp,6),(CV,6)]
def Ii:LR:=[(rF,0),(nk,0),(kZ,0),(vq,0),(jc,0),(ka,0),(oz,1),(oA,0),(os,6),(wr,0),(lo,0),(ow,6),(oh,0),(BP,0),(qW,0),(v6,0),(z9,0),(fW,0),(k9,8),(qv,0),(Gn,0),(Gs,0),(il,1),(lu,0),(rJ,0),(Gk,0),(Q8,0),(vm,6),(wf,0),(v7,0),(jd,3),(oD,0),(vm,0),(wz,0),(wO,0),(um,0),(BV,7)]
def Ih:LR:=[(kZ,0),(rF,6),(im,0),(mO,6),(wm,0),(pJ,6),(BZ,6),(BM,0),(iQ,4),(ls,8),(qW,0),(ug,4),(oq,6),(oC,0),(wL,2),(oj,4),(nk,6),(zJ,0),(BY,4),(v0,4),(CS,4),(Ag,4),(zZ,0),(tk,2),(th,4),(wp,4),(fW,0),(qq,4),(um,0),(qq,6),(oA,6),(im,6),(hN,4),(oi,4),(BV,4),(CU,0),(wi,4)]
def Ig:LR:=[(oF,6),(cI,6),(fW,6),(lp,3),(im,0),(rG,6),(im,6),(lu,6),(k9,3),(qW,6),(ue,6),(jc,6),(rT,4),(oC,6),(tk,7),(hN,6),(BX,4),(k9,7),(ls,3),(wh,4),(wx,6),(rJ,6),(vo,4),(yZ,0),(il,1),(pJ,0),(oj,4),(oA,0),(v9,3),(CW,6),(vo,6),(CQ,6),(v9,4),(vm,6),(hN,4),(uk,6),(z3,4),(tg,0),(ov,3),(v2,6),(ua,0),(v1,0),(z9,6),(D8,4),(wj,8),(ub,6),(lo,6),(BU,6),(iQ,7),(wM,6),(Gm,4),(Gu,6),(tj,6),(lv,6),(oh,6),(qo,6),(wf,6),(lq,6),(BR,4),(rY,6),(jd,2),(qq,6)]
def If:LR:=[(rI,3),(ot,3),(oh,6),(nk,3),(ww,3),(jc,3),(D3,3),(rS,3),(ka,0),(rW,3),(tj,6),(fW,6),(ql,0),(rV,0),(zV,3),(wF,0),(ka,9),(vp,3),(fW,3),(uf,3),(rS,6),(tj,3),(CX,3),(oh,0),(ot,6),(v6,9),(rW,6)]
def Ie:LR:=[(op,3),(om,3),(ws,3),(oh,3),(rO,3),(uc,6),(ln,3),(k7,3),(ll,3),(zL,3),(wA,3),(tj,3),(z8,3),(Gr,3),(qo,6),(tj,6)]
def Id:LR:=[(z4,0),(lm,0),(lv,0),(lm,7),(mO,0),(BN,0),(wy,0),(hN,0),(BO,0),(z9,7),(wN,0),(Q3,0),(wD,0),(zX,0),(D5,0),(BM,7),(Ag,0),(wM,0),(rL,0),(BY,0)]
def Ic:LR:=[(z4,0),(wh,0),(oi,7),(lv,0),(fW,0),(CT,0),(rT,7),(BP,0),(rG,0),(lv,7),(lm,0),(BT,0),(oo,7),(BO,7),(D9,0),(BN,0),(fW,7),(z7,0),(Ah,7),(pJ,6),(vo,7),(ug,7),(oj,0),(lj,4),(BU,0),(D8,7),(rX,1)]
def Ib:LR:=[(oi,7),(lv,7),(hN,0),(lm,7),(oj,0),(hN,7),(fW,7),(rT,0),(zM,0),(wi,0),(oh,7),(ug,0),(wy,7),(oj,7),(oD,7),(oF,0),(v4,7),(pJ,0),(qv,7),(z7,7),(Ah,0),(De,0),(CS,7),(lu,7),(wM,7),(rR,0),(mO,7),(Q5,7),(D2,0),(Gm,7),(wi,7),(CX,0),(yZ,0),(zP,0),(BR,7),(BY,7)]
def Ia:LR:=[(qm,7),(op,4),(om,4),(ln,4),(tZ,4),(qf,4),(zS,4),(lj,4),(qi,7),(oo,7),(oi,7),(wt,7),(gy,4),(zK,4),(BX,4),(oi,4),(Gr,4),(tY,4),(z8,4),(hN,4),(ul,4),(tj,7)]
def I9:LR:=[(uc,7),(fW,7),(yZ,1),(rG,7),(lv,7),(wK,0),(z7,0),(zK,4),(pJ,1),(BO,7),(Dg,0),(Ae,0),(Gk,1),(A4,0),(v2,7),(oi,0),(k7,4),(uk,7)]
def I8:LR:=[(z7,0),(k7,4),(im,1),(im,6),(uk,0),(ln,4),(v0,0),(oj,0),(A4,0),(qq,0),(BZ,0),(ll,4),(v0,7),(ol,4),(rE,4),(wp,0),(qo,0),(rG,0),(hN,0),(rR,0),(CP,0),(qq,7),(wv,7),(jc,7),(lj,4),(Ae,7),(qs,4),(rK,4),(pJ,7),(rK,7),(qo,6)]
def I7:LR:=[(v8,0),(wo,0),(im,6),(k8,7),(k8,0),(CZ,0),(oE,0),(BZ,0),(mN,7),(oy,0),(mN,0),(oy,7),(v2,9),(jc,3),(Qa,7),(ka,7),(Ai,0),(rV,3),(CP,0),(BX,7),(oi,0),(wv,0),(qu,7),(hN,0),(oE,7),(rR,7),(zU,0),(CU,9),(zU,7),(Dd,3),(rW,6),(ud,7),(v2,0)]
def I6:LR:=[(mK,3),(rD,3),(gy,7),(qn,7),(BW,7),(qk,3),(qu,7),(oE,7),(k8,7),(mN,0)]
def I5:LR:=[(kZ,2),(rF,8),(oq,2),(mO,2),(wm,2),(qh,2),(oq,8),(os,2),(mO,8),(ow,8),(Ab,2),(jc,9),(os,8),(rL,2),(qj,2),(wu,8),(lm,2),(BY,2)]
def I4:LR:=[(lv,2),(z4,2),(fW,2),(zP,9),(cI,2),(op,2),(qW,2),(lo,2),(lm,2),(rG,2),(A2,2),(hN,9),(im,8),(BR,2),(ub,2),(wg,2),(wh,2),(oA,8),(zX,2),(wt,2),(ot,5),(Ab,2),(wx,2),(ug,9),(rJ,2),(wi,8),(vq,8),(wD,2),(wH,2),(Gn,8),(Go,2),(vr,2),(mO,2),(qm,2),(vo,9),(oj,2),(wf,2),(BU,2),(uh,2),(oC,2),(tg,2),(lu,2)]
def I3:LR:=[(cI,1),(lo,8),(oC,8),(fW,8),(BM,8),(lm,9),(A0,2),(ue,2),(BP,8),(oA,2),(im,8),(nk,8),(lq,8),(lu,8),(oD,8),(wg,8),(BQ,8),(zQ,2),(wG,2),(A9,8),(z3,8),(CQ,8),(Af,2),(vm,8),(tg,8),(zY,8),(jd,1),(rH,8),(um,8)]
def I2:LR:=[(wi,2),(hN,9),(om,2),(oh,2),(nk,2),(pJ,2),(fW,8),(oj,9),(oo,5),(oF,2),(qW,8),(D1,9),(rV,8),(rN,2),(ls,0),(rX,5),(wp,9),(qv,8),(v0,2),(tZ,2),(qi,5),(ua,2),(v1,8),(ql,8),(Gu,2),(Q4,2),(za,2),(z8,2)]
def I1:LR:=[(uf,8),(rI,8),(D4,2),(rO,8),(A1,0),(ww,8),(zW,2),(ww,0),(wL,0),(CW,2),(wH,0),(zV,8)]
def I0:LR:=[(rI,0),(vp,0),(fW,8),(fW,0),(nk,0),(im,0),(ot,8),(wr,2),(v8,4),(ot,0),(vr,0),(CT,0),(Dd,2),(CT,8),(qu,4),(tj,8),(vp,8),(qv,8),(rX,0),(oE,4),(Gt,4)]
def HZ:LR:=[(ot,8),(jc,0),(v6,2),(k8,4),(rI,0),(jc,2),(D4,2),(ot,0),(vp,8),(Q9,2),(tk,3),(tk,5),(rV,2),(rW,0),(vq,2),(qv,0),(v9,6),(oh,2),(vr,0),(ql,6),(Gy,0),(Gy,8),(rS,0),(rS,8),(vp,0),(ql,2),(v2,2),(oh,6),(pJ,2)]
def HY:LR:=[(v8,9),(k8,9),(v3,2),(v2,6),(qu,9),(qu,2),(vq,2),(qk,2),(yZ,8),(oE,2),(BW,2),(ka,9),(v3,9),(v8,2),(rX,8),(vq,9),(v2,2),(Gt,9),(Dd,0),(v0,2),(oE,9)]
def HX:LR:=[(z4,1),(lv,8),(lm,1),(BN,8),(lm,8),(zM,1),(wh,8),(oD,1),(D8,1),(oj,8),(wy,8),(BT,1),(mO,8),(wD,8),(oi,1)]
def HW:LR:=[(rT,1),(lv,1),(qm,1),(z4,1),(op,1),(oi,1),(v4,8),(BN,1),(oj,1),(BO,1)]
def HV:LR:=[(oi,8),(oj,8),(wh,8),(BP,8),(oF,8),(hN,8),(im,2),(fW,8),(rT,8),(hN,1),(BX,1),(pJ,2),(z7,1),(qW,8),(v4,1),(CS,1),(BK,2),(rR,1),(nk,8),(v1,7),(BZ,8),(qv,1),(BR,8),(za,8)]
def HU:LR:=[(oj,9),(qi,1),(qm,1),(op,1),(zS,1),(oo,1),(qf,9),(oi,1),(Q6,1),(BW,1),(D7,1),(om,1),(gy,9),(nk,9),(hN,9),(rN,9),(ln,1),(z8,9)]
def HT:LR:=[(op,0),(qm,0),(wt,0),(ws,0),(qi,8),(qk,4),(rO,0),(Aj,0),(ul,8)]
def HS:LR:=[(op,0),(qk,0),(A3,0),(ka,0),(om,0),(Aj,8),(rS,0),(Di,0),(vr,0)]
def HR:LR:=[(qk,0),(qm,0),(om,0),(tZ,0),(wn,0),(rO,8),(A3,0),(qi,8),(qf,0),(qi,0),(gy,0),(ul,0),(hN,0),(wA,8),(hN,8),(wn,9),(rD,0),(rN,0),(Dh,0),(jc,0),(z8,0),(D6,0)]
def HQ:LR:=[(om,0),(rO,0),(ll,8),(wn,8),(oo,8),(tY,0),(oh,8),(tY,8),(ll,0),(gy,8),(ul,8),(oo,0),(oF,1),(oh,0),(tZ,8),(rN,8),(BW,8),(qf,8),(wA,0),(qk,4),(k7,0),(qf,0),(qs,0),(pJ,7),(rN,0),(jc,8),(nk,0),(ln,0)]
def HP:LR:=[(k7,0),(ln,0),(oo,0),(lj,0),(qs,8),(D1,0),(rR,8),(qs,0),(uk,1)]
def HO:LR:=[(k7,0),(qs,0),(lj,0),(ll,0),(D0,0),(rK,8),(gy,8),(Db,8)]
def HN:LR:=[(k7,0),(uc,0),(ws,0),(ll,0),(qq,8),(wF,6),(qo,0),(wF,2)]
def HM:LR:=[(ll,0),(lj,0),(rE,0),(rE,8),(qf,0),(gy,8),(zL,0),(ol,0),(k7,0)]
def HL:LR:=[(ud,2),(k8,9),(mN,2),(wh,2),(qo,2),(oy,9),(mN,9),(rW,8),(v1,2)]
def HK:LR:=[(wo,2),(mN,9),(k8,2),(Ai,2),(mN,2),(oy,2),(CU,0)]
def HJ:LR:=[(mK,0),(rD,0),(gy,9),(v5,3),(k7,1),(gy,0),(ln,1),(tY,1)]
def HI:LR:=[(mK,0),(gy,0),(gy,9),(lj,0),(qs,1),(k7,1),(ln,1),(lk,0),(CY,0),(qn,0),(ll,9),(lk,9),(wk,9),(rE,9),(k8,9)]
def HH:LR:=[(rD,6),(gy,2),(qu,2),(oE,2)]
def HG:LR:=[(mK,2),(qn,2),(oy,6),(ln,2),(ka,2),(k8,2)]
def HF:LR:=[(wo,4),(lk,2),(k7,2),(lk,6),(D1,6),(BK,4),(ll,2),(wv,2),(uc,2),(ud,4),(oy,6),(CP,4)]
def HE:LR:=[(lk,6),(lk,2),(oy,4),(k8,4),(rE,2),(k8,2),(mN,9),(qn,6)]
def HD:LR:=[(rD,8),(mK,4),(gy,4),(gy,8),(ud,8)]
def HC:LR:=[(mK,4),(gy,4),(gy,8),(wk,8),(lj,4),(lj,8),(qn,4),(rK,8)]
def HB:LR:=[(mK,1),(gy,1),(gy,5),(ol,0)]
def HA:LR:=[(ol,0),(lk,5),(ol,2),(ol,4),(ol,1),(qn,1),(mK,1),(lk,2),(lk,0),(zN,4),(zN,0),(rK,1),(wk,1)]
def kS:BTree LR:=(bn (bn (bn (bn (bn (bn (bl RN) (bl RM)) (bn (bl RK) (bl RJ))) (bn (bn (bl RI) (bl RH)) (bn (bl RG) (bl RF)))) (bn (bn (bn (bl RE) (bl RD)) (bn (bl Ir) (bl Iq))) (bn (bn (bl Ip) (bl Io)) (bn (bl In) (bl Im))))) (bn (bn (bn (bn (bl Il) (bl Ik)) (bn (bl Ij) (bl Ii))) (bn (bn (bl Ih) (bl Ig)) (bn (bl If) (bl Ie)))) (bn (bn (bn (bl Id) (bl Ic)) (bn (bl Ib) (bl Ia))) (bn (bn (bl I9) (bl I8)) (bn (bl I7) (bl I6)))))) (bn (bn (bn (bn (bn (bl I5) (bl I4)) (bn (bl I3) (bl I2))) (bn (bn (bl I1) (bl I0)) (bn (bl HZ) (bl HY)))) (bn (bn (bn (bl HX) (bl HW)) (bn (bl HV) (bl HU))) (bn (bn (bl HT) (bl HS)) (bn (bl HR) (bl HQ))))) (bn (bn (bn (bn (bl HP) (bl HO)) (bn (bl HN) (bl HM))) (bn (bn (bl HL) (bl HK)) (bn (bl HJ) (bl HI)))) (bn (bn (bn (bl HH) (bl HG)) (bn (bl HF) (bl HE))) (bn (bn (bl HD) (bl HC)) (bn (bl HB) (bl HA)))))))
def jC (sa sb qa qb:Nat):LR:=(cond (nB 2 (land (shiftRight qa 10) 31)) (cond (nB 2 (land qa 31)) (cond (nB 28 sa) (cond (nB 36 sa) (cond (nB 8 (land qa 31)) (cond (nB 8 (land (shiftRight qa 10) 31)) RN RM) (cond (nB 24 (land (shiftRight qb 18) 63)) RK RJ)) (cond (nB 24 (land (shiftRight qb 18) 63)) (cond (nB 8 (land (shiftRight qa 15) 31)) RI RH) (cond (nB 24 (land (shiftRight qb 6) 63)) RG RF))) (cond (nB 24 (land (shiftRight qb 6) 63)) (cond (nB 24 (land (shiftRight qb 12) 63)) (cond (nB 19 (land (shiftRight qb 18) 63)) RE RD) (cond (nB 2 (land (shiftRight qa 5) 31)) Ir Iq)) (cond (nB 4 (land (shiftRight qa 5) 31)) (cond (nB 4 (land (shiftRight qa 15) 31)) Ip Io) (cond (nB 2 (land (shiftRight qa 5) 31)) In Im)))) (cond (nB 2 (land (shiftRight qa 5) 31)) (cond (nB 6 (shiftRight qa 20)) (cond (nB 8 (land (shiftRight qa 15) 31)) (cond (nB 24 (land (shiftRight qb 18) 63)) Il Ik) (cond (nB 6 (land (shiftRight qa 5) 31)) Ij Ii)) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 24 (shiftRight qb 24)) Ih Ig) (cond (nB 2 (shiftRight qa 20)) If Ie))) (cond (nB 4 (land (shiftRight qa 15) 31)) (cond (nB 24 (shiftRight qb 24)) (cond (nB 8 (shiftRight qa 20)) Id Ic) (cond (nB 2 (shiftRight qa 20)) Ib Ia)) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 24 (land (shiftRight qb 6) 63)) I9 I8) (cond (nB 2 (shiftRight qa 20)) I7 I6))))) (cond (nB 8 sa) (cond (nB 2 (land (shiftRight qa 5) 31)) (cond (nB 2 (land qa 31)) (cond (nB 24 (land (shiftRight qb 6) 63)) (cond (nB 24 (land (shiftRight qb 12) 63)) I5 I4) (cond (nB 20 sa) I3 I2)) (cond (nB 6 (land (shiftRight qa 15) 31)) (cond (nB 20 sa) I1 I0) (cond (nB 2 (land (shiftRight qa 15) 31)) HZ HY))) (cond (nB 2 (land qa 31)) (cond (nB 8 (shiftRight qa 20)) (cond (nB 6 (land (shiftRight qa 15) 31)) HX HW) (cond (nB 2 (land (shiftRight qa 15) 31)) HV HU)) (cond (nB 24 (land (shiftRight qb 12) 63)) (cond (nB 4 (land (shiftRight qa 15) 31)) HT HS) (cond (nB 6 (shiftRight qa 20)) HR HQ)))) (cond (nB 2 (shiftRight qa 20)) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 4 (land (shiftRight qb 18) 63)) (cond (nB 9 (land qb 63)) HP HO) (cond (nB 45 sb) HN HM)) (cond (nB 2 (land (shiftRight qa 5) 31)) (cond (nB 9 (land (shiftRight qb 6) 63)) HL HK) (cond (nB 4 (shiftRight qa 20)) HJ HI))) (cond (nB 2 (land (shiftRight qa 5) 31)) (cond (nB 4 (land (shiftRight qa 5) 31)) (cond (nB 6 (land (shiftRight qa 5) 31)) HH HG) (cond (nB 14 (land (shiftRight qb 6) 63)) HF HE)) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 14 (land (shiftRight qb 12) 63)) HD HC) (cond (nB 4 (land (shiftRight qb 12) 63)) HB HA))))))
lemma rd (b a d c:Nat):dn (jC b a d c) kS:=by unfold jC kS;repeat (first|apply i0|rfl)
def fr:L1:=[(8659136,0),(4497536,0),(t3,20480),(t4,117551104),(9740288,Bt),(qU,2121728),(qU,1597442),(yH,86029),(4498560,7079616),(t4,319631360),(9707712,45079),(t4,318844940),(9577728,Bn),(qU,yA),(yH,154964942),(9705728,252506124),(vc,154963976),(9701664,251719880),(t4,255652360),(9703680,251719691),(9504896,0),(9736448,302063621),(8657156,50442758),(9699584,4493333),(9511170,77839),(6559940,253571084),(qT,vf),(t4,201424896),(yH,318877703),(4329604,0),(9736320,251719705),(9732384,vf),(t3,yA),(8462530,2158607),(9703680,251703311),(9572480,134262799),(vc,154996736),(qT,Bs),(9445376,287645696),(vc,154988546),(9506946,352391168),(9443520,255627270),(qT,285274502),(8654978,255627714),(9511042,7094283),(9504834,1609728),(8687808,55854400),(t4,Bs),(8654978,254054856),(9703712,167817819),(9703680,156524883),(8659140,2994880),(9572640,352355465),(8654914,154988674),(8654914,154952073),(8529088,4494473),(6559876,152134025),(t4,419467283),(8657092,390596032)]
def f0:=(8659136,0)
def f1:=(8656904,0)
def f2:=(8585480,0)
def f3:=(6299912,0)
def f4:=(270598,0)
def f5:=(6562048,0)
def f6:=(8658950,0)
def f7:=(8650952,0)
def f8:=(8395016,0)
def f9:=(4497536,0)
def pj:=(9703428,0)
def Fa:=(8519817,0)
def yg:=(4198696,0)
def Cu:=(140548,0)
def Hn:=(139556,0)
def vT:=(4465792,0)
def Ct:=(8687620,0)
def mH:=(9568392,0)
def Cs:=(4198665,0)
def TD:=(t3,20480)
def TC:=(9568265,1310720)
def TB:=(9508,5)
def TA:=(304256,320)
def Rg:=(140576,20480)
def Tz:=(4498432,1310720)
def Rf:=(9732100,83886080)
def EO:=(t4,117551104)
def Re:=(9577481,7077895)
def Rd:=(4489513,452985280)
def Ty:=(9446692,28699)
def Tx:=(299305,117442240)
def Hm:=(yG,110599)
def Tw:=(4498441,7078336)
def Rc:=(9732388,453013504)
def Tv:=(9446537,1835035)
def Rb:=(9740288,Bt)
def Tu:=(8692736,7079625)
def Tt:=(9732104,453096000)
def Ts:=(qU,2121728)
def Tr:=(9699336,135790592)
def Tp:=(qU,1597442)
def Ra:=(yH,86029)
def R9:=(9568552,352374784)
def To:=(4497696,218189824)
def Hl:=(9708548,5505037)
def Tn:=(8683657,352322368)
def R8:=(9441576,53269)
def R7:=(9736196,w5)
def Tm:=(4198697,452986560)
def R6:=(t4,319631360)
def Tl:=(9577481,55312403)
def Tk:=(9707712,45079)
def Tj:=(8656905,2885056)
def Ti:=(8585512,184643584)
def Th:=(6300936,6029323)
def R5:=(303366,385876672)
def Tg:=(8659974,2883607)
def Tf:=(9443592,94219)
def Te:=(9446692,3223571)
def Td:=(304265,206308544)
def Tc:=(299305,321914048)
def Tb:=(yG,201404435)
def R3:=(9577728,Bn)
def R2:=(4497417,138150856)
def y8:=(9699620,vf)
def R1:=(8397961,3965455)
def Ta:=(299304,253789120)
def R0:=(8687904,vf)
def Cq:=(9577480,3965455)
def QZ:=(4489481,253789120)
def T9:=(qU,yA)
def T8:=(271616,57344)
def T7:=(qU,57344)
def SZ:=(9699336,yA)
def SY:=(4497696,238851017)
def SX:=(9708548,254079566)
def SW:=(9705728,252506124)
def SV:=(6553896,251708355)
def SU:=(8593696,201388239)
def QX:=(6562824,3945420)
def QW:=(9445576,54312975)
def EN:=(vc,154963976)
def ST:=(8650761,254018057)
def Hj:=(8659968,2421320)
def Hi:=(9437448,254050313)
def EM:=(9701664,251719880)
def SS:=(8463369,3944975)
def QV:=(2392360,252478400)
def QU:=(9446658,52490255)
def QT:=(9511200,135065615)
def SR:=(8683810,251720195)
def EL:=(9446472,3965135)
def SQ:=(4489513,253789135)
def SP:=(yG,136377295)
def Hh:=(9703680,251719691)
def SO:=(8398084,2945039)
def SN:=(8528160,184610831)
def Cp:=(9445512,3977231)
def SM:=(9504896,0)
def SL:=(2166793,0)
def OR:=(2228514,0)
def yk:=(4262176,0)
def Fe:=(9441346,0)
def yj:=(9736448,302063621)
def yi:=(9576457,4718930)
def Fd:=(4456745,302011520)
def OQ:=(8398116,1384466)
def Fc:=(304264,88605824)
def Fb:=(8529184,83959826)
def OP:=(4498440,4719749)
def yh:=(9732356,302063936)
def F9:=(9445513,4739090)
def OO:=(8657156,50442758)
def ON:=(8593544,7111043)
def OM:=(6557960,455106752)
def va:=(8528134,135802907)
def OL:=(4464840,101451464)
def OK:=(8528072,811547)
def OJ:=(9699584,4493333)
def OI:=(9445384,285298697)
def sV:=(9511170,77839)
def yf:=(8653090,318828544)
def OH:=(8653090,251736064)
def OG:=(9511170,61459)
def F8:=(6559940,253571084)
def OF:=(8591494,122422031)
def OE:=(6428934,3207635)
def OD:=(4399302,205288640)
def OC:=(4397318,254805191)
def OB:=(6496452,201404879)
def OA:=(6559878,5010380)
def Oz:=(8589510,320664320)
def lg:=(qT,vf)
def sU:=(8528008,3965455)
def Bg:=(4460808,253789120)
def Bf:=(yE,Bn)
def uZ:=(4464776,138150856)
def F7:=(t4,201424896)
def Oy:=(9577481,6291468)
def Ox:=(4489513,402653952)
def Ow:=(yG,98316)
def Ov:=(9732388,402702336)
def Ou:=(9446537,3145752)
def Ot:=(yH,318877703)
def iT:=(4329604,0)
def Os:=(4498436,3933145)
def F6:=(9732384,vf)
def Oq:=(9446409,3965455)
def F5:=(9446688,Bn)
def Op:=(t3,yA)
def Oo:=(9568265,t5)
def On:=(2365512,138150848)
def ye:=(8587522,251719688)
def Om:=(6365256,3932687)
def Ol:=(2361606,251691968)
def Ok:=(6555906,251720192)
def Oj:=(8462406,3964943)
def Oi:=(8460546,134279183)
def Oh:=(8528160,251703311)
def Og:=(9572480,134262799)
def Of:=(4329760,251703304)
def F4:=(9441412,2158603)
def Oe:=(vc,154996736)
def Od:=(8659968,4518464)
def yd:=(qT,Bs)
def Be:=(8528008,3670043)
def F3:=(yE,110606)
def Oc:=(4464776,7078784)
def Ob:=(4460808,452985728)
def yc:=(yE,57371)
def Oa:=(qT,234991616)
def F2:=(8528008,7077902)
def F1:=(9445376,287645696)
def O9:=(vc,154988546)
def O8:=(8659968,3994178)
def O7:=(4327714,285214016)
def O6:=(4327714,69653)
def Bd:=(9443520,255627270)
def O5:=(6488352,151020495)
def O4:=(qT,285274502)
def O3:=(8528008,3957137)
def F0:=(yE,102305807)
def O2:=(4464776,105120710)
def O1:=(yE,102297617)
def EZ:=(qT,251728262)
def EY:=(8654978,255627714)
def O0:=(8523848,254046351)
def pi:=(9504834,1609728)
def Bc:=(2164809,103022592)
def NZ:=(2165026,150994950)
def NY:=(2171970,393)
def NX:=(2164809,582)
def NW:=(2394178,152567808)
def yb:=(9504834,100663305)
def NV:=(9574408,353456131)
def NU:=(6432000,5522755)
def NT:=(t4,Bs)
def EX:=(9577481,3670043)
def NS:=(9446692,110606)
def NR:=(304265,7078784)
def NQ:=(299305,452985728)
def NP:=(yG,57371)
def NO:=(9732388,234991616)
def NN:=(9446537,7077902)
def NM:=(8654978,254054856)
def uY:=(4327688,152863689)
def EW:=(4268292,119599689)
def EV:=(2232584,253784649)
def NL:=(4464708,119837640)
def ya:=(8458376,154960329)
def NK:=(9703712,167817819)
def NJ:=(4465673,153879195)
def NI:=(8528160,320103753)
def EU:=(8657032,191672320)
def NH:=(6430984,184550107)
def NG:=(9572640,352355465)
def NF:=(9572640,155746325)
def NE:=(4334601,304088393)
def ND:=(9446532,5543048)
def NC:=(8654914,154988674)
def ET:=(8521800,255598729)
def NB:=(4262152,252191311)
def NA:=(4464706,37548610)
def y9:=(8654914,154952073)
def Nz:=(8521800,253256265)
def ES:=(4262152,102273615)
def ER:=(2167048,153379215)
def sT:=(4464706,102298185)
def Ny:=(8456328,254054790)
def EQ:=(8529088,4494473)
def Bb:=(9576454,304418825)
def EP:=(4331782,103059734)
def Nx:=(6426824,69505430)
def Nw:=(9446537,6631433)
def Nv:=(6496516,6030487)
def s4:BTree (List (iN × Nat × Nat)):=(bn (bn (bn (bn (bn (bl [(f0,0,0),(f5,0,6),(f9,1,0),(vT,1,6),(TD,2,0),(TA,2,4),(Rg,2,6),(Tz,2,7),(EO,3,0),(Ts,5,0),(To,7,6),(R6,9,0),(T9,13,0),(T8,13,4),(T7,13,7),(SM,20,0),(yk,20,6),(F7,27,0),(Op,32,0),(Oe,36,0),(Od,36,7),(F1,38,0),(NT,47,0)]) (bl [(Re,3,1),(OL,22,4),(F8,25,0),(uZ,26,4)])) (bn (bl [(f1,0,1),(f2,0,2),(f3,0,3),(f7,0,8),(f8,0,9),(yg,1,3),(mH,1,8),(Tt,4,8),(Tr,5,1),(R9,7,2),(Ti,10,2),(Ta,12,4),(R0,12,6),(SZ,13,8),(EN,16,0),(Hj,16,7),(EM,17,0),(QV,17,2),(Fc,21,4),(OM,22,2),(Bg,26,2),(F6,31,0),(On,33,1),(Of,35,6),(Oc,37,4),(Ob,37,5),(NZ,45,2),(EU,51,1)]) (bl [(R1,12,3),(SS,17,1),(SQ,18,2),(Oq,31,1)]))) (bn (bn (bl [(pj,1,1),(Cu,1,4),(Hn,1,5),(Ct,1,7),(Rf,2,8),(Rc,3,8),(Tv,3,9),(R7,8,1),(yh,21,8),(Ov,27,8),(iT,29,0),(yd,37,0),(Oa,37,8),(EY,43,0),(EX,47,1),(NO,47,8),(NJ,49,7),(NC,53,0),(NA,53,7)]) (bl [(QX,15,7)])) (bn (bl [(y8,12,2),(SW,15,0),(lg,26,0),(Ow,27,6),(NL,48,7),(ND,52,9)]) (bl [(Tl,9,1),(EP,56,3)])))) (bn (bn (bn (bl [(Tp,6,0),(OR,20,2),(Fe,20,9),(yf,24,2),(OH,24,6),(Ok,33,6),(O9,39,0),(O8,39,7),(O7,40,2),(pi,45,0),(NW,45,8)]) (bl [(SX,14,7),(ST,16,1),(Fb,21,6),(OA,25,7),(F3,37,3),(NS,47,3),(NE,52,7),(Nw,57,9)])) (bn (bl [(OO,22,0),(ye,33,2),(O4,42,0),(EZ,42,8),(NM,48,0)]) (bl []))) (bn (bn (bl [(f4,0,4),(f6,0,7),(R5,10,4),(OD,25,4),(Oz,25,8),(Ol,33,4),(Bd,41,0)]) (bl [(OQ,21,3),(F2,37,9)])) (bn (bl [(O2,42,4),(Ny,54,9)]) (bl [(Nx,56,9)]))))) (bn (bn (bn (bn (bl [(va,22,3),(Ou,27,9)]) (bl [(Hl,7,7),(R2,12,1),(Hi,16,9),(QU,17,3),(OI,23,9),(sV,24,0),(Oi,33,9),(uY,48,2),(EV,48,5),(ya,48,9),(ET,53,1),(Nz,54,1)])) (bn (bl [(Fa,1,2),(Cs,1,9),(TC,2,1),(TB,2,3),(Rd,3,2),(Tx,3,5),(Tw,3,7),(Rb,4,0),(Tu,4,7),(Tn,7,8),(Tm,8,3),(Tj,10,1),(Td,11,4),(Tc,11,5),(QZ,12,8),(SY,14,6),(SL,20,1),(Fd,21,2),(Ox,27,2),(Oo,32,1),(Bc,45,1),(NR,47,4),(NQ,47,5),(NI,50,6),(NG,52,0),(EQ,55,0)]) (bl [(OE,25,3),(O3,42,1)]))) (bn (bn (bl [(SR,17,8),(yj,21,0)]) (bl [(OJ,23,0),(OG,24,9),(OF,25,1),(Oy,27,1),(Oj,33,7),(O1,42,6),(NF,52,6)])) (bn (bl [(Ra,7,0),(OP,21,7),(OC,25,5),(EW,48,3)]) (bl [(R8,7,9),(Tg,10,7),(Os,30,7)])))) (bn (bn (bn (bl [(OK,22,9),(Be,37,1),(NU,46,6),(NH,51,3)]) (bl [(Th,10,3),(Tf,10,9),(Tb,11,6),(SO,19,3),(OB,25,6),(Bf,26,3),(F0,42,3)])) (bn (bl [(SV,15,2),(Hh,19,0),(ON,22,1),(NY,45,3),(yb,45,9),(NV,46,1),(y9,54,0),(sT,54,7)]) (bl [(yi,21,1),(F9,21,9),(NP,47,6),(NK,49,0),(Nv,58,6)]))) (bn (bn (bl [(Hm,3,6),(Ot,28,0)]) (bl [(Tk,10,0),(Te,11,3),(Cq,12,7),(QW,15,9),(EL,17,9),(Cp,19,9),(sU,26,1),(Om,33,3),(O6,40,6),(O0,43,1),(NN,47,9),(NB,53,2),(ES,54,2),(ER,54,5)])) (bn (bl [(R3,12,0),(SU,15,6),(QT,17,6),(SP,18,6),(SN,19,6),(F5,31,3),(Oh,34,6),(Og,35,0),(F4,35,9),(O5,41,2),(NX,45,5),(Bb,55,7)]) (bl [(Ty,3,3),(yc,37,6)]))))))
def SK:L1:=[iT,Bg,uZ,ya,lg,sU,uY,sT,O2,EY,OC,Ok,Oz,OD,yb,pi,OF,ES,ET]
def SJ:L1:=[f3,iT,f8,yg,Cs,Tm]
def SI:L1:=[f2,SV,uY,Hi,Fd,QZ,SQ,R9,f7,lg]
def SH:L1:=[f7,mH,NM,iT,Fa,y8,yh,yf,Bg,NO,yb]
def SG:L1:=[Bg,iT,QV,OL,QZ,Ob,OA,uY,On,Oc]
def SF:L1:=[f2,Ol,iT,f3,NH,Rd,sV,yd]
def SE:L1:=[f4,Td,Cu,iT,Tc,NR,R5]
def SD:L1:=[f4,Ox,yg,Tx]
def SC:L1:=[F3,iT,F0,f2,OB,yc,OE,NB,EZ,Oj,F8,Bc,Nz,sV,F2,ER,NX,yd]
def SB:L1:=[iT,f2,Bf,f4,Be,OK,sU,yc,mH,F2,EP,pi,O1,yd,lg,OG,f7,Cu,y8]
def Nt:L1:=[f8,Cp,NS,QW,SO,mH,Cs,ES,NN,f3]
def Ns:L1:=[f8,F3,Bf,pi,mH,ER]
def Nr:L1:=[iT,f8,yd,lg,OO,Oa,ON,O4,NW,Th,ET,yf,Bc,OM,Nw,ya,F8,EV,yg,EW]
def Nq:L1:=[f4,iT,Hn,Cu,f3]
def Np:L1:=[f7,yh,mH,f2,Rc,y8,lg,Fa,f8,EV,EW,ya,EU]
def No:L1:=[f2,iT,mH,yg,ya,EZ,ye,Ny]
def Nn:L1:=[TC,Cq,f1,Tr,QW,SS,mH,Bb,Oq,R8,Tt,Oo]
def Nm:L1:=[Oy,f1,yi,SZ,Cp,EX,Re,F9]
def Nl:L1:=[f1,Cq,Fc,f3,R1,Cs,f6,va,NJ,EX,O0]
def Nk:L1:=[f1,R2,Fa,Cs,yi,uZ,NE,Tn,ST,Tj]
def Nj:L1:=[f6,Fc,Tw,OP,R2,sT,Os]
def Ni:L1:=[f6,EL,sU,Cp,Hl,sT,Cq,Tl,va,Ty]
def Nh:L1:=[pj,Ct,Rf,f1,f7,R7]
def Ng:L1:=[pj,f1,Ct,y9,Rf,mH,Cp,va,lg,sT,Be,R7,yf,Fe,EY]
def Nf:L1:=[mH,f1]
def Ne:L1:=[pj,f2]
def Nd:L1:=[pj,mH,y9,Om,pi,ye,yb]
def Nc:L1:=[pj,f8,pi,f3]
def Nb:L1:=[f1,f2]
def Na:L1:=[f1,Ct,iT]
def N9:L1:=[f1,Bc,Cs,Fa,f3,SL,uZ]
def N8:L1:=[f6,iT,f3,sU,uZ,Nv]
def N7:L1:=[f0,f5,SW]
def N6:L1:=[f0]
def N5:L1:=[T7,f0,Hj,Ra,Rb,EN,SX,Tk,Oe,Ot,O8]
def N4:L1:=[f0,Tp,T9,QX,EN,Ts,Tu]
def N3:L1:=[Tz,f9,vT,TA,f0]
def N2:L1:=[vT,f0,T8,sT]
def N1:L1:=[f9,f5,R5]
def N0:L1:=[f5,sT]
def MZ:L1:=[f0,F6,R0,f9,lg,Hh,f5,yj,EM,y8]
def MY:L1:=[f0,yj,f9,F7,f5,f7,Hh,To]
def MX:L1:=[f0,NT,Rd,Ov,f9,NQ,f5,yf]
def MW:L1:=[f0,f9,yh,f5,QV,Ta,R6]
def MV:L1:=[TD,f0,pj,F6,Op,EO,Ct]
def MU:L1:=[pj,f0,R6,Rb,EM]
def MT:L1:=[Ct,f9,f0]
def MS:L1:=[f0,f1,lg]
def MR:L1:=[Ow,Tf,f0]
def MQ:L1:=[f0,sV,Ra,Fb,OQ,R3,Hh,QT,Rg,Te,F5,Tb,SU,F0,F4]
def MP:L1:=[f0,R3,SN,vT,QU,NP,QT,pj,f5,Bf,Fb,yc,F5,EM,lg,yg,sU,R8,Cu,O6,Bd,yk,Cq,mH,f6,SP]
def MO:L1:=[f0,pj,Hl,f5,vT,va,mH,Oh,Cq,Cp,Ou,f2,EL,NF,O5,NK,yi,Og,QX,EP,sU,f8,Be,Hi,Nx]
def MN:L1:=[f0,Rg,f5,vT,Hm,EQ]
def MM:L1:=[f0,vT,Bb,Hj,EN,Re,Hm,NV,uZ,NA,EQ,f3,ND,NU,Bd,F1,O9,OI,Od]
def ML:L1:=[f5,f2,EM,f0,Of,R9,yk,yg,EO,Hn,y8,yj,R0,NG,lg,Rc,SY,O7,Fd,NI,SR,Bd,uY,yh,Hi]
def MK:L1:=[f0,yj,pj,mH,ye,NC,y8,lg,Bb,F4,EU]
def MJ:L1:=[pj,f0,mH,y9,yb,y8,pi]
def MI:L1:=[f0,pj,mH,sV,O3,ye]
def MH:L1:=[Fe,f0,SM,sV,Hm,Tv,pj,Hl,f2,F7,EL,F9,EN,F1,yi,OJ]
def MG:L1:=[f0,f8,Tg,f2,QU,Hj,EO,pi,EL,Ti]
def MF:L1:=[f5,yk,Hn,Cu,f3,NZ,f2,uY,EO]
def ME:L1:=[vT,f6,f0,iT,f3,NL,Oi,y9,NY,f2,pi,R1]
def MD:L1:=[f5,vT,TB,f3,sV,yc]
def MC:L1:=[iT,f5,yg,OR,yk,OH,va]
def kT:BTree L1:=(bn (bn (bn (bn (bn (bn (bl SK) (bl SJ)) (bn (bl SI) (bl SH))) (bn (bn (bl SG) (bl SF)) (bn (bl SE) (bl SD)))) (bn (bn (bn (bl SC) (bl SB)) (bn (bl Nt) (bl Ns))) (bn (bn (bl Nr) (bl Nq)) (bn (bl Np) (bl No))))) (bn (bn (bn (bn (bl Nn) (bl Nm)) (bn (bl Nl) (bl Nk))) (bn (bn (bl Nj) (bl Ni)) (bn (bl Nh) (bl Ng)))) (bn (bn (bn (bl Nf) (bl Ne)) (bn (bl Nd) (bl Nc))) (bn (bn (bl Nb) (bl Na)) (bn (bl N9) (bl N8)))))) (bn (bn (bn (bn (bn (bl N7) (bl N6)) (bn (bl N5) (bl N4))) (bn (bn (bl N3) (bl N2)) (bn (bl N1) (bl N0)))) (bn (bn (bn (bl MZ) (bl MY)) (bn (bl MX) (bl MW))) (bn (bn (bl MV) (bl MU)) (bn (bl MT) (bl MS))))) (bn (bn (bn (bn (bl MR) (bl MQ)) (bn (bl MP) (bl MO))) (bn (bn (bl MN) (bl MM)) (bn (bl ML) (bl MK)))) (bn (bn (bn (bl MJ) (bl MI)) (bn (bl MH) (bl MG))) (bn (bn (bl MF) (bl ME)) (bn (bl MD) (bl MC)))))))
def gF (sa _sb qa qb:Nat):L1:=(cond (nB 2 (land qa 31)) (cond (nB 2 (land (shiftRight qa 5) 31)) (cond (nB 14 (land (shiftRight qb 6) 63)) (cond (nB 4 (shiftRight qa 20)) (cond (nB 2 (land (shiftRight qa 10) 31)) (cond (nB 2 (land (shiftRight qa 15) 31)) SK SJ) (cond (nB 6 (land (shiftRight qa 5) 31)) SI SH)) (cond (nB 2 (shiftRight qa 20)) (cond (nB 9 (land (shiftRight qb 18) 63)) SG SF) (cond (nB 14 (land (shiftRight qb 18) 63)) SE SD))) (cond (nB 14 (land qb 63)) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 19 (land (shiftRight qb 12) 63)) SC SB) (cond (nB 16 sa) Nt Ns)) (cond (nB 2 (land (shiftRight qa 10) 31)) (cond (nB 2 (shiftRight qa 20)) Nr Nq) (cond (nB 16 sa) Np No)))) (cond (nB 16 sa) (cond (nB 6 (land qa 31)) (cond (nB 8 (shiftRight qa 20)) (cond (nB 9 (shiftRight qb 24)) Nn Nm) (cond (nB 4 (land (shiftRight qa 10) 31)) Nl Nk)) (cond (nB 6 (land (shiftRight qa 10) 31)) (cond (nB 6 (land (shiftRight qa 15) 31)) Nj Ni) (cond (nB 4 (land qa 31)) Nh Ng))) (cond (nB 6 (shiftRight qa 20)) (cond (nB 4 (land qa 31)) (cond (nB 6 (land qa 31)) Nf Ne) (cond (nB 2 (land (shiftRight qa 15) 31)) Nd Nc)) (cond (nB 4 (land (shiftRight qa 15) 31)) (cond (nB 4 (land qa 31)) Nb Na) (cond (nB 6 (land qa 31)) N9 N8))))) (cond (nB 6 (land (shiftRight qa 15) 31)) (cond (nB 6 (land (shiftRight qa 10) 31)) (cond (nB 6 (shiftRight qa 20)) (cond (nB 4 (land (shiftRight qa 5) 31)) (cond (nB 9 (land (shiftRight qb 6) 63)) N7 N6) (cond (nB 14 (land (shiftRight qb 12) 63)) N5 N4)) (cond (nB 8 (land (shiftRight qa 10) 31)) (cond (nB 8 (land (shiftRight qa 15) 31)) N3 N2) (cond (nB 8 (land (shiftRight qa 15) 31)) N1 N0))) (cond (nB 2 (land (shiftRight qa 5) 31)) (cond (nB 9 (land qb 63)) (cond (nB 9 (land (shiftRight qb 6) 63)) MZ MY) (cond (nB 24 (shiftRight qb 24)) MX MW)) (cond (nB 8 (shiftRight qa 20)) (cond (nB 8 (land (shiftRight qa 15) 31)) MV MU) (cond (nB 8 (land (shiftRight qa 15) 31)) MT MS)))) (cond (nB 16 sa) (cond (nB 14 (land qb 63)) (cond (nB 19 (land (shiftRight qb 12) 63)) (cond (nB 24 (land (shiftRight qb 12) 63)) MR MQ) (cond (nB 14 (land (shiftRight qb 12) 63)) MP MO)) (cond (nB 6 (land (shiftRight qa 10) 31)) (cond (nB 4 (land (shiftRight qa 5) 31)) MN MM) (cond (nB 6 (land (shiftRight qa 5) 31)) ML MK))) (cond (nB 6 (shiftRight qa 20)) (cond (nB 2 (land (shiftRight qa 15) 31)) (cond (nB 9 (land (shiftRight qb 6) 63)) MJ MI) (cond (nB 8 (shiftRight qa 20)) MH MG)) (cond (nB 9 (land (shiftRight qb 6) 63)) (cond (nB 6 (land (shiftRight qa 5) 31)) MF ME) (cond (nB 4 (land (shiftRight qa 10) 31)) MD MC))))))
lemma re (b a d c:Nat):dn (gF b a d c) kT:=by unfold gF kT;repeat (first|apply i0|rfl)
def dY:List AS:=[(8,3181600,0xc9203008000,0xc9201248000),(8,5309440,0xd1401000000,0xd1241000000),(8,3246080,0xc0449200000,5043398901760),(8,3148864,0xc0001250000,5016572170240),(8,3149856,5016559583232,0xc0002408000),(8,qS,0xd0002400000,9964361875456),(9,4326400,9914948780032,9914948780032),(9,2294784,4967414890496,8825100828672),(8,2230272,4974813642752,8823089659904),(9,6358016,0xd8401000000,0x92241000000),(8,6356992,0xd2240000000,0xd9400000000),(12,ro,yt,yv),(10,yC,FG,FA),(8,2164800,4966091653120,8814382321664),(8,3213344,0xc9442008000,0xc9441208000),(8,4196416,9895623589888,9895638241280),(8,4261888,9905301880832,9912803393536),(12,9535488,0xdb600000000,0xdb248000000)]
def r0:=(45,50,Z1,374866304,Ff,Ff,0,0,0)
def r1:=(45,49,Z1,Br,0x926db69b6d8,G,Z3,Pd,t5)
def r2:=(45,49,Z1,421028230,G,G,0,Z8,1057)
def r3:=(45,49,Z1,Br,0x926db6db692,G,0,Pd,t5)
def r4:=(45,53,Z1,456417665,G,G,0,0,0)
def r5:=(45,50,Z1,369189248,BJ,G,0,0,o9)
def r6:=(45,56,Z1,436822400,G,G,0,o8,0)
def r7:=(45,51,Z1,238576515,G,G,Z6,0,tS)
def r8:=(45,54,Z1,vk,G,0xdb6d801b6d8,0,o8,0)
def r9:=(45,54,Z1,vk,0xdb6da012048,G,0,kr,0)
def QG:=(45,52,Z1,w4,0xdb6d8009080,0xdb6db6d80d8,0,0,0)
def DR:=(45,52,Z1,w4,zC,G,0,0,0)
def st:=(45,49,Z1,254079553,jv,qd,0,0,0)
def GZ:=(45,49,Z1,453074944,jv,qd,0,0,0)
def QF:=(45,54,Z1,vk,0xdb6da012080,G,0,kr,0)
def QE:=(45,54,Z1,vk,0xdb6d9011090,G,0,kr,0)
def ra:=(45,54,Z1,321184323,G,G,0,o8,3171)
def TU:=(45,52,Z1,yr,29259577051,G,0,0,0)
def DQ:=(45,59,Z1,321229184,G,G,0,Fo,0)
def DP:=(45,50,Z1,369189248,Fg,G,0,0,o9)
def xd:=(39,49,9741603,369209344,0xdb6db0000c9,0xdb6db6db6c9,0,0,0)
def TT:=(45,52,Z1,w4,0xdb6d8008048,zD,0,0,0)
def TS:=(45,52,Z1,373031872,G,0xdb6db69b4db,0,0,0x48000000a528000)
def QD:=(45,49,Z1,Br,0xdb6d90124d8,G,268435456,0x2400000090000000000,o9)
def GY:=(45,52,Z1,w4,0xdb6d8011200,G,0,0,0)
def GX:=(45,50,Z1,369189248,0xdb6d801b6db,G,0,0,o9)
def QC:=(45,59,Z1,421029248,G,G,0,0,q8)
def TR:=(45,49,Z1,385950208,29444126424,rv,0,0,0)
def tw:=(45,52,Z1,237298246,G,G,0,0x918ce000000,0x84200000001c00)
def DO:=(45,59,Z1,321164483,G,G,0,Z2,q8)
def QA:=(45,49,Z1,237040195,G,G,0,0x918c6319c00,tS)
def GW:=(45,52,Z1,373031872,G,FW,0,0,0x48000000a528000)
def TQ:=(45,52,Z1,yr,57521883,Fm,0,0,1057)
def GV:=(45,49,Z1,322700224,0xdb6db6d92db,0xc06db6c9200,0,0,0)
def Qz:=(45,49,Z1,321188224,0xdb6c36db4db,0xd86db61a200,0,0,0)
def Qy:=(45,49,Z1,321188224,t6,0xd86db01b600,0,0,0)
def DN:=(45,60,Z1,255365961,G,G,0,1057,CG)
def DM:=(45,56,Z1,318858176,Fn,G,0,0,o9)
def DL:=(45,49,Z1,403529728,jv,qd,0,0,0)
def Qx:=(45,52,Z1,yr,19365213915,G,0,0,0)
def Cc:=(45,50,Z1,420274562,G,G,0,7696685301760,0)
def GU:=(45,54,Z1,vk,0xd86db21b0d1,t6,0,o8,0)
def GT:=(45,54,Z1,vk,0xd86d901b6da,t6,0,o8,0)
def Qw:=(45,56,Z1,370762112,G,G,0,kr,1057)
def TP:=(45,59,Z1,387470723,G,G,tS,0,mJ)
def Qv:=(45,49,Z1,305987584,Fm,0xdb6c24800c0,0,0,0)
def TO:=(45,52,Z1,yr,9895621539547,G,0,0,0)
def Qu:=(45,62,Z1,436298624,yx,0xdb6d92124c8,0,kr,0)
def TN:=(45,52,Z1,yr,8796131407579,Fm,74379762595790848,0,0)
def Qt:=(45,52,Z1,yr,29393793755,Fn,0,0,0)
def DK:=(45,49,Z1,354758656,jv,qd,0,0,0)
def Cb:=(45,60,Z1,337981830,G,G,1057,t5,0)
def Ca:=(45,60,Z1,437806464,G,G,0,Z8,Fo)
def TM:=(45,59,Z1,437794178,17198855899,G,0,0,0)
def GS:=(45,61,Z1,436298560,G,0xdb6da01b6c0,0,kr,0)
def Qs:=(45,63,Z1,436298688,Ff,0xdb60349b6db,0,kr,0)
def Qr:=(45,60,Z1,369193920,0xdb6db6db688,G,0,0,t5)
def DJ:=(45,52,Z1,w4,0xdb6d8010040,G,0,0,0)
def TL:=(45,49,Z1,421028230,0xdb20001b2db,zD,mJ,1057,0)
def Qq:=(45,52,Z1,yr,29450416347,0xdb6c36db6da,0,0,1057)
def DI:=(45,49,Z1,206881024,jv,qd,0,0,0)
def C9:=(45,65,Z1,371548550,G,G,0,0,0)
def TK:=(45,52,Z1,yr,29450416347,0xdb6c36db6da,0,0,Fo)
def vC:=(45,62,Z1,337195907,G,G,0,0,0)
def pR:=(45,50,Z1,240705536,G,G,0,0,0)
def dX:LS:=[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,QG,DR,st,GZ,QF,QE,ra,TU,DQ,DP,xd,TT,TS,QD,GY,GX,QC,TR,tw,DO,QA,GW,TQ,GV,Qz,Qy,DN,DM,DL,Qx,Cc,GU,GT,Qw,TP,Qv,TO,Qu,TN,Qt,DK,Cb,Ca,TM,GS,Qs,Qr,DJ,TL,Qq,DI,C9,TK,vC,pR]
def h0:=(45,50,Z1,369123350,BI,BI,0,0,0)
def h1:=(45,50,Z1,1574294,yz,yz,0,0,0)
def h2:=(45,50,Z1,100754816,yx,yx,0,0,0)
def h3:=(45,50,Z1,5857286,0xdb6036db6db,0xdb6036db6db,0,0,0)
def h4:=(45,49,Z1,255591616,0xda6db6124db,G,Z9,0x2400294a00012000000,tS)
def h5:=(45,49,Z1,vh,0xdb6c249b6da,G,9216,P3,t8)
def h6:=(45,49,Z1,vh,G,0xdb49361b6da,Z9,7168,Pc)
def h7:=(45,49,Z1,102261145,G,G,0,Z5,kr)
def h8:=(45,49,Z1,102262342,G,G,0,1057,mJ)
def h9:=(45,49,Z1,102338950,G,G,0,kr,Z8)
def fT:=(45,49,Z1,107241862,G,G,0,mJ,Z5)
def kG:=(45,49,Z1,vh,0xdb49249b6db,G,0,P3,t8)
def hH:=(45,49,Z1,Br,G,0x926db6db692,0,zA,0x2400000052952000000)
def EI:=(45,49,Z1,3993619,G,0xdb6db6d2492,0,tS,0x294a90000002400)
def EF:=(45,49,Z1,255591616,G,0xdb6da4924db,0,t8,0x14a5480000012000000)
def Cn:=(45,49,Z1,vh,G,0xdb49249b6db,0,7168,Pc)
def o0:=(45,53,Z1,219701339,G,G,0,0,0)
def zs:=(45,53,Z1,102241997,G,G,0,0,0)
def pZ:=(45,53,Z1,101036870,G,G,0,0,0)
def tL:=(45,53,Z1,23908742,G,G,0,0,0)
def gL:=(45,53,Z1,453271949,G,G,0,0,0)
def gV:=(45,53,Z1,18375515,G,G,0,0,0)
def jW:=(45,53,Z1,102291137,G,G,0,0,0)
def tK:=(45,53,Z1,104181830,G,G,0,0,0)
def rl:=(45,53,Z1,225186182,G,G,0,0,0)
def QS:=(45,50,Z1,5791766,FW,G,0,0,Z3)
def E6:=(45,50,Z1,100753430,FL,G,0,0,Z9)
def xK:=(45,50,Z1,5768582,Bz,G,0,0,9216)
def QR:=(45,50,Z1,369124736,G,Bz,0,Z3,0)
def E0:=(45,50,Z1,1662998,G,BJ,0,Z6,0)
def xG:=(45,50,Z1,106431872,G,FW,0,Z9,0)
def vP:=(45,50,Z1,369188870,G,0xdb6db49b6db,0,9216,0)
def Hg:=(45,50,Z1,5767574,G,FL,0,o9,0)
def QQ:=(45,56,Z1,39346202,G,G,0,q8,0)
def Cm:=(45,56,Z1,370673282,G,G,0,Z2,0)
def Cl:=(45,56,Z1,100769942,G,G,0,Z7,0)
def DZ:=(45,56,Z1,6825350,G,G,0,3171,0)
def QP:=(45,56,Z1,436233602,G,G,0,0,q8)
def zr:=(45,56,Z1,1663130,G,G,0,0,Z2)
def DY:=(45,56,Z1,106440320,G,G,0,0,Z7)
def vO:=(45,56,Z1,369729542,G,G,0,0,3171)
def SA:=(45,56,Z1,40370582,G,G,0,0,o8)
def kF:=(45,51,Z1,236511438,G,G,Z9,0,t8)
def tJ:=(45,51,Z1,104346510,G,G,9216,0,7168)
def vN:=(45,51,Z1,235725702,G,G,o9,0,t5)
def tI:=(45,51,Z1,54059406,G,G,Z3,0,zA)
def nN:=(45,51,Z1,235725198,G,G,9216,7168,0)
def tH:=(45,51,Z1,54027150,G,G,o9,t5,0)
def pY:=(45,51,Z1,236512131,G,G,Z3,zA,0)
def vM:=(45,51,Z1,104390862,G,G,Z6,tS,0)
def xF:=(45,51,Z1,238564230,G,G,Z9,t8,0)
def QO:=(45,54,Z1,5791770,G,0xdb0036db0db,0,q8,0)
def Sz:=(45,54,Z1,370673280,G,29450417883,0,Z2,0)
def Hf:=(45,54,Z1,Bk,G,0xdb6c36db600,0,Z7,0)
def QN:=(45,54,Z1,6817158,G,0xd86db6c00db,0,3171,0)
def Sy:=(45,54,Z1,436233600,0xd86d801b6db,G,0,0,q8)
def QM:=(45,54,Z1,1663002,0xdb0036db6d8,G,0,0,Z2)
def DX:=(45,54,Z1,vj,FU,G,0,0,3171)
def He:=(45,54,Z1,6816150,0xdb6c36c00db,G,0,0,o8)
def Sx:=(45,54,Z1,5791770,0xdb4024090db,G,0,mJ,0)
def Sw:=(45,54,Z1,370673280,8815439361755,G,0,Z8,0)
def Sv:=(45,54,Z1,Bk,9905325848192,G,0,Z5,0)
def Su:=(45,54,Z1,1663002,G,9912842040904,0,0,Z8)
def St:=(45,54,Z1,vj,G,0xdb6d9212080,0,0,1057)
def Hd:=(45,52,Z1,w4,0xdb6db6180db,0xdb6da009000,0,0,0)
def Ss:=(45,52,Z1,6815770,0xdb0024000db,G,0,0,0)
def Sr:=(45,52,Z1,106522,9895662171648,G,0,0,0)
def Sq:=(45,52,Z1,6817408,29451092112,G,0,0,0)
def Sp:=(45,49,Z1,254079049,BB,zD,0,0,0)
def So:=(45,49,Z1,7079296,rv,29451165696,0,0,0)
def Sn:=(45,49,Z1,5768896,Fw,q9,0,0,0)
def Sm:=(45,49,Z1,369209344,BB,zD,0,0,0)
def Sl:=(45,54,Z1,vj,G,0xdb6da012080,0,0,1057)
def tG:=(45,54,Z1,vj,G,0xdb6da411040,0,0,1057)
def DW:=(45,54,Z1,154702035,G,G,0,q8,o8)
def Hc:=(45,54,Z1,237253833,G,G,0,Z2,q8)
def tF:=(45,54,Z1,151859790,G,G,0,Z7,Z2)
def Hb:=(45,54,Z1,55350153,G,G,0,3171,Z7)
def Ck:=(45,54,Z1,319591305,G,G,0,Z2,q8)
def Ha:=(45,54,Z1,52748883,G,G,0,Z7,Z2)
def H9:=(45,54,Z1,154703043,G,G,0,3171,Z7)
def H8:=(45,54,Z1,237318345,G,G,0,o8,3171)
def Sk:=(45,54,Z1,155988558,G,G,0,q8,o8)
def QL:=(45,52,Z1,Bm,29451092186,G,0,0,0)
def H7:=(45,52,Z1,t9,BC,G,0,0,0)
def H6:=(45,52,Z1,tb,G,BC,0,0,0)
def QK:=(45,52,Z1,102346765,G,0xda0036db600,0,0,0)
def Sj:=(45,52,Z1,107742022,G,29451092186,0,0,0)
def Si:=(45,59,Z1,157573139,G,G,0,Hs,0)
def Sh:=(45,59,Z1,421004489,G,G,0,5120,0)
def H5:=(45,59,Z1,100741721,G,G,0,yp,0)
def QJ:=(45,59,Z1,5019206,G,G,0,Fu,0)
def H4:=(45,59,Z1,318793289,G,G,0,0,5120)
def Sg:=(45,59,Z1,1675859,G,G,0,0,yp)
def QI:=(45,59,Z1,107254976,G,G,0,0,Fu)
def Cj:=(45,59,Z1,421867526,G,G,0,0,Fo)
def Sf:=(45,59,Z1,155976089,G,G,0,0,Hs)
def H3:=(45,50,Z1,5791766,Fn,G,0,0,Z3)
def QH:=(45,50,Z1,370673024,BH,G,0,0,Z6)
def Ci:=(45,50,Z1,100753430,Fl,G,0,0,Z9)
def y4:=(45,50,Z1,369124736,G,Fn,0,Z3,0)
def MB:=(45,50,Z1,1662998,G,BH,0,Z6,0)
def MA:=(45,50,Z1,106431872,G,Fl,0,Z9,0)
def y3:=(45,50,Z1,369188870,G,BA,0,9216,0)
def Mz:=(45,50,Z1,5767574,G,Fg,0,o9,0)
def xZ:=(39,49,3450153,5768896,0xc96db6d8000,0xc96db6db6db,0,0,0)
def xY:=(39,49,9735465,453074944,0xdb6db25b6db,0xdb6db2400c0,0,0,0)
def My:=(39,49,9545001,5767195,0xdb64b6db6db,0xdb6480180db,0,0,0)
def Ba:=(45,52,Z1,w4,jv,0xdb6d9208000,0,0,0)
def Mx:=(45,52,Z1,6815770,t6,0xdb2410000db,0,0,0)
def xX:=(45,52,Z1,251719702,G,0xdb6d369b6db,0,0,Pb)
def Mw:=(45,52,Z1,3933583,G,0xda6d36db6db,0,0,0x294a00000002400)
def Mv:=(45,52,Z1,251749312,G,0xda6db6db6da,0,0,0x14a5000000012000000)
def xW:=(45,52,Z1,369160207,0xdb6d369b6db,G,0,5674725549056,0)
def Mu:=(45,52,Z1,3933142,0xda6d36db6db,G,0,0x294a00012000000,0)
def Mt:=(45,52,Z1,251721088,0xda6db6db6da,G,0,P0,0)
def Ms:=(45,52,Z1,4022287,0xdb6db6db4da,G,0,0x4800000000014a5,0)
def Mr:=(45,52,Z1,6815770,0xdb0022400db,G,0,0,0)
def Mq:=(45,52,Z1,106522,9414625834496,G,0,0,0)
def Mp:=(45,52,Z1,6817408,29451092105,G,0,0,0)
def Mo:=(45,52,Z1,106522,G,9414625834496,0,0,0)
def Mn:=(45,52,Z1,6817408,G,29451092105,0,0,0)
def uX:=(45,52,Z1,w4,G,0xdb6d8011200,0,0,0)
def EK:=(45,52,Z1,6815770,G,0xdb0022400db,0,0,0)
def B9:=(45,50,Z1,100753430,Z4,G,0,0,Z9)
def EJ:=(45,50,Z1,5768582,0xdb6db6c00db,G,0,0,9216)
def Mm:=(45,50,Z1,369124736,G,0xdb6d801b6db,0,Z3,0)
def B8:=(45,50,Z1,369188870,G,Z4,0,9216,0)
def Ml:=(45,50,Z1,5767574,G,0xdb6db6c00db,0,o9,0)
def sS:=(45,59,Z1,102326297,G,G,0,0,Z2)
def sR:=(45,59,Z1,369201542,G,G,0,0,3171)
def Mk:=(45,59,Z1,6578582,G,G,0,0,o8)
def uW:=(45,59,Z1,419520902,G,G,0,o8,0)
def Mj:=(45,59,Z1,5792153,G,G,0,q8,0)
def EH:=(45,59,Z1,370697792,G,G,0,Z2,0)
def B7:=(45,59,Z1,102338582,G,G,0,Z7,0)
def Mi:=(45,59,Z1,107218310,G,G,0,3171,0)
def EG:=(45,49,Z1,4751383,FK,jv,0,0,0)
def Mh:=(45,49,Z1,302084104,rv,0xdb00361b6c0,0,0,0)
def xV:=(45,52,Z1,154702222,G,G,0,0x48c670000000000,0x42100000000e000000)
def Mg:=(45,52,Z1,237265801,G,G,0,0x2463380000000000000,7696581395489)
def B6:=(45,52,Z1,152625742,G,G,0,0x1c00000000000002463,0x380000002108000)
def EE:=(45,52,Z1,104371081,G,G,0,305241088,0x1c00000010840000000)
def Mf:=(45,52,Z1,236491657,G,G,0,0x380000000000421,7696886628352)
def B5:=(45,52,Z1,103080526,G,G,0,0x1c00000000002108000,0x3800918c0000000)
def Me:=(45,52,Z1,154702726,G,G,0,1134945115136,0x1c0048c600000000000)
def uV:=(45,52,Z1,237298057,G,G,0,0x8420000e000000,0x2463000000000001c00)
def B4:=(45,52,Z1,154690126,G,G,0,0x421000070000000000,234890339)
def qO:=(45,59,Z1,153432275,G,G,0,Z7,Z2)
def ED:=(45,59,Z1,155989193,G,G,0,3171,Z7)
def uU:=(45,59,Z1,319631945,G,G,0,o8,3171)
def EC:=(45,49,Z1,138186958,G,G,0,0x48c6318ce000000,t8)
def Md:=(45,49,Z1,254030728,G,G,0,0x246318c670000000000,7168)
def Mc:=(45,49,Z1,151839247,G,G,0,0xc63380000000002463,t5)
def EB:=(45,49,Z1,54035401,G,G,0,0x1c00000000012318c63,zA)
def Mb:=(45,49,Z1,235705288,G,G,0,7168,0x3800318d2318000)
def xU:=(45,49,Z1,52752910,G,G,0,t5,0x1c0018c6918c0000000)
def B3:=(45,49,Z1,154960771,G,G,0,zA,0xc6348c600000001c00)
def EA:=(45,49,Z1,253812937,G,G,0,tS,0x246300000000e000c63)
def B2:=(45,49,Z1,137900623,G,G,0,t8,7696685311075)
def uT:=(45,52,Z1,251719702,G,0xdb6db49b6db,0,0,Pb)
def Ma:=(45,52,Z1,3933583,G,FL,0,0,0x294a00000002400)
def M9:=(45,52,Z1,5828623,G,BJ,0,0,9895604655269)
def Ez:=(45,52,Z1,3933142,Bz,G,0,0x294a00012000000,0)
def Ey:=(45,52,Z1,251721088,BJ,G,0,P0,0)
def M8:=(45,52,Z1,Bm,Cz,FI,0,0,mJ)
def M7:=(45,52,Z1,t9,0xdb6d80000db,0xdb6db6db6da,0,0,Z8)
def Ex:=(45,52,Z1,tb,Fm,Cz,0,Z8,0)
def B1:=(45,49,Z1,251719699,0xdb6db25b6db,0xdb6d92400c0,0,0,0)
def M6:=(45,49,Z1,3933139,5045972992000,0xc96db6db6db,0,0,0)
def M5:=(45,49,Z1,251720896,0xdb6db000049,0xdb6db6db6c9,0,0,0)
def M4:=(45,49,Z1,253232329,0xdb6d36db6d8,0xd868801b0db,0,0,0)
def M3:=(45,49,Z1,1634899,0xd16c36db000,0xda6db61b6db,0,0,0)
def M0:=(45,49,Z1,1634899,FK,jv,0,0,0)
def qN:=(45,60,Z1,237294159,G,G,0,kr,9315)
def Ew:=(45,60,Z1,154440654,G,G,0,mJ,vi)
def Ev:=(45,60,Z1,220525449,G,G,0,Z8,zB)
def qM:=(45,60,Z1,154985037,G,G,0,Z5,CC)
def xT:=(45,60,Z1,254071374,G,G,0,CG,Z8)
def xS:=(45,60,Z1,154440591,G,G,0,9315,Z5)
def B0:=(45,60,Z1,220521417,G,G,0,vi,1057)
def mZ:=(45,60,Z1,154726989,G,G,0,zB,kr)
def AZ:=(45,60,Z1,238850889,G,G,0,CC,mJ)
def Eu:=(45,56,Z1,373032128,Fl,G,0,0,Z6)
def xR:=(45,56,Z1,251736086,BA,G,0,0,Z9)
def LZ:=(45,56,Z1,4982159,Fg,G,0,0,9216)
def LY:=(45,56,Z1,318829952,G,Fg,0,Z3,0)
def LX:=(45,56,Z1,4022291,G,Fn,0,Z6,0)
def LW:=(45,56,Z1,257426624,G,BH,0,Z9,0)
def xQ:=(45,56,Z1,369176591,G,Fl,0,9216,0)
def LV:=(45,56,Z1,4981718,G,BA,0,o9,0)
def LU:=(45,49,Z1,5780992,Fw,q9,0,0,0)
def LT:=(45,49,Z1,369983488,BB,zD,0,0,0)
def Et:=(45,52,Z1,102289435,9914989524480,G,0,0,0)
def LQ:=(45,52,Z1,Bm,9925055742096,G,0,0,0)
def AY:=(45,52,Z1,t9,0xdb6d8012090,G,0,0,0)
def pe:=(45,52,Z1,tb,G,Fi,0,0,0)
def LO:=(45,52,Z1,3432859,G,0xdb4824000db,0,0,0)
def LN:=(45,52,Z1,107742022,G,29451165840,0,0,0)
def AX:=(45,50,Z1,54026393,G,G,0,0x3800318c0000000,0)
def LM:=(45,50,Z1,236463683,G,G,0,0x1c0018c600000000000,0)
def sQ:=(45,50,Z1,101290190,G,G,0,0xc63000000000001c00,0)
def Es:=(45,50,Z1,40121222,G,G,0,234884195,0)
def Er:=(45,50,Z1,419980163,G,G,0,0,3405070204928)
def LL:=(45,50,Z1,35184857,G,G,0,0,0x18c670000000000)
def LK:=(45,50,Z1,104347202,G,G,0,0,0xc63380000000000000)
def qL:=(45,50,Z1,235769990,G,G,0,0,0x1c00000000000000c63)
def Eq:=(45,50,Z1,56893838,G,G,0,0,103914496)
def LJ:=(45,54,Z1,Bk,0xd868b61b6c8,rv,0,Z7,0)
def Ep:=(45,54,Z1,vj,q9,0xdb6c345b0c8,0,0,3171)
def Eo:=(45,54,Z1,370673280,4427497451739,zD,0,Z2,0)
def LI:=(45,54,Z1,Bk,0xdb6d361b640,rv,0,Z7,0)
def LH:=(45,54,Z1,1663002,jv,0xdb2036db0da,0,0,Z2)
def En:=(45,54,Z1,vj,q9,0xdb6c369b640,0,0,3171)
def LG:=(45,56,Z1,370673030,G,G,0,Z8,mJ)
def LF:=(45,56,Z1,100753814,G,G,0,Z5,Z8)
def LE:=(45,59,Z1,102064343,G,G,t8,0,Z8)
def LD:=(45,59,Z1,89667014,G,G,7168,0,Z5)
def Em:=(45,59,Z1,369979781,G,G,t5,0,1057)
def LC:=(45,59,Z1,85553366,G,G,tS,Z5,0)
def El:=(45,59,Z1,106706309,G,G,t8,1057,0)
def LB:=(45,49,Z1,255852562,0xdb6d36db6db,0xd84900180db,0,0,0)
def LA:=(45,49,Z1,4256896,0x926c36d8000,FI,0,0,0)
def Ek:=(45,52,Z1,t9,0xdb6da400040,G,0,0,0)
def Lz:=(45,52,Z1,tb,G,0xdb6d9000090,0,0,0)
def Ly:=(45,52,Z1,107742022,G,9925055774720,0,0,0)
def Lx:=(45,52,Z1,Bm,0x926db6d0000,FI,2114,0,0)
def Lw:=(45,52,Z1,tb,Fm,0xdb6da480080,2114,0,0)
def Ej:=(45,52,Z1,102289435,0xdb00365b600,BH,0,0,0)
def Ei:=(45,52,Z1,t9,0xd96d801b600,BA,0,0,0)
def Lv:=(45,52,Z1,102346765,Fl,0xdb0036db200,0,0,0)
def Lu:=(45,49,Z1,5543104,rv,29451165696,0,0,0)
def Eh:=(45,49,Z1,5018944,Fw,q9,0,0,0)
def Lt:=(45,49,Z1,321212416,BB,zD,0,0,0)
def Eg:=(45,60,Z1,156000660,G,G,kr,zA,0)
def Ls:=(45,60,Z1,320365833,G,G,mJ,tS,0)
def Ef:=(45,60,Z1,102318675,G,G,Z8,t8,0)
def Lr:=(45,60,Z1,105944262,G,G,Z5,7168,0)
def Ee:=(45,60,Z1,337142985,G,G,Z8,0,zA)
def Ed:=(45,60,Z1,102314580,G,G,Z5,0,tS)
def Lq:=(45,60,Z1,105682182,G,G,1057,0,t8)
def Ec:=(45,60,Z1,321208710,G,G,kr,0,7168)
def Lp:=(45,60,Z1,156262803,G,G,mJ,0,t5)
def xP:=(45,60,Z1,102326298,G,G,0,Z5,Hs)
def AW:=(45,60,Z1,106432134,G,G,0,1057,5120)
def uS:=(45,60,Z1,369205638,G,G,0,kr,yp)
def Eb:=(45,60,Z1,6840726,G,G,0,mJ,Fu)
def xO:=(45,60,Z1,436298118,G,G,0,5120,1057)
def Ea:=(45,60,Z1,5792154,G,G,0,yp,kr)
def E9:=(45,60,Z1,102342678,G,G,0,Fo,Z8)
def xN:=(45,60,Z1,107480454,G,G,0,Hs,Z5)
def Lo:=(45,59,Z1,56108678,4977253417088,G,0,0,0)
def xM:=(45,59,Z1,369729923,0xdb6d8010048,G,0,0,0)
def E8:=(45,59,Z1,436822214,G,0xdb6d9210000,0,0,0)
def E7:=(45,59,Z1,107488643,G,29451128960,0,0,0)
def Ln:=(45,61,Z1,218210326,G,0xdb6036db680,0,Z5,0)
def Lm:=(45,61,Z1,3498010,0xdb4036db6c0,G,0,0,Z8)
def Ll:=(45,61,Z1,369205261,0xdb6db01b680,G,0,0,1057)
def Lk:=(45,63,Z1,251764758,yx,0xdb6db6d80d2,0,Z5,0)
def Lj:=(45,63,Z1,6816726,0xdb6db6da4c0,Ff,0,0,kr)
def Li:=(45,60,Z1,385966095,G,0xdb6da21b6db,0,7168,0)
def AV:=(45,52,Z1,w4,G,0xdb6d9010000,0,0,0)
def Lh:=(45,49,Z1,102338950,0xd96db6c8000,t6,1057,Z8,0)
def Lg:=(45,49,Z1,102338950,jv,4427497714176,Z5,0,kr)
def Lf:=(45,49,Z1,107241862,t6,0xdb6db640040,1057,0,mJ)
def Le:=(45,52,Z1,102289435,FN,0xd86db6db4db,0,0,kr)
def Ld:=(45,52,Z1,t9,0xd86d801b6d8,0xdb6d36db0db,0,0,Z8)
def AU:=(45,52,Z1,tb,0xda6db6db0db,FN,0,Z8,0)
def Lc:=(45,52,Z1,3432859,0xdb6db61b6da,0xd86c36c00db,0,Z5,0)
def Lb:=(45,65,Z1,156787094,G,G,0,0,0)
def La:=(45,65,Z1,370697609,G,G,0,0,0)
def E5:=(45,65,Z1,102326870,G,G,0,0,0)
def L9:=(45,65,Z1,106468742,G,G,0,0,0)
def L8:=(45,52,Z1,t9,0xd86d801b6d8,0xdb6d36db0db,0,0,yp)
def E4:=(45,52,Z1,tb,0xda6db6db0db,FN,0,5120,0)
def L7:=(45,52,Z1,3432859,0xdb6db61b6da,0xd86c36c00db,0,yp,0)
def E3:=(45,62,Z1,105701588,G,G,0,0,0)
def uR:=(45,62,Z1,322450694,G,G,0,0,0)
def uQ:=(45,62,Z1,235749779,G,G,0,0,0)
def E2:=(45,62,Z1,55600334,G,G,0,0,0)
def xJ:=(45,62,Z1,336389318,G,G,0,0,0)
def xI:=(45,62,Z1,54079892,G,G,0,0,0)
def xH:=(45,62,Z1,239887619,G,G,0,0,0)
def sP:=(45,62,Z1,320422094,G,G,0,0,0)
def E1:=(45,62,Z1,105919379,G,G,0,0,0)
def uP:=(45,50,Z1,372768782,G,G,0,0,0)
def mY:=(45,50,Z1,234881942,G,G,0,0,0)
def AT:=(45,50,Z1,58766,G,G,0,0,0)
def uO:=(45,50,Z1,3761024,G,G,0,0,0)
def pK:BTree (List (RS × Nat × Nat)):=(bn (bn (bn (bn (bn (bl [(EG,27,1),(LE,44,1)]) (bl [])) (bn (bl []) (bl [(h5,1,3),(h6,1,8),(kG,3,3),(Cn,3,8),(Mw,22,2),(xW,22,5),(Ms,22,8),(Mc,30,3),(B2,30,9),(Ma,31,2),(M9,31,4),(qN,36,1),(xS,36,6),(LZ,37,4),(xQ,37,8),(Li,56,8)]))) (bn (bn (bl [(o0,4,1),(gV,4,6),(My,20,9),(Et,39,1),(LO,39,6),(Ej,49,1),(Le,59,1),(Lc,59,6),(L7,62,6)]) (bl [])) (bn (bl [(r7,7,0),(pY,7,7),(ra,16,0),(H9,16,7),(DO,29,0),(QA,30,0),(B3,30,7),(LM,40,2),(Er,40,5),(xM,53,3),(E7,53,9),(vC,63,0),(xH,63,7)]) (bl [(EI,3,6),(DW,16,1),(Ha,16,6),(Si,18,1),(Sg,18,6),(qO,29,1),(B1,33,1),(M6,33,6),(M3,34,6),(M0,35,6),(LX,37,6),(Ef,51,3),(Lp,51,9),(uQ,63,3),(E1,63,9)])))) (bn (bn (bn (bl [(h7,2,1),(H5,18,3),(Sf,18,9),(sS,26,1),(Mj,26,6),(AX,40,1),(LL,40,6)]) (bl [(Sp,12,8),(Hc,16,2),(Hb,16,4),(Ck,16,5),(H8,16,8),(Sh,18,2),(H4,18,5),(Mg,28,2),(EE,28,4),(Mf,28,5),(uV,28,8),(ED,29,2),(uU,29,3),(EB,30,4),(EA,30,8),(M4,34,2),(DN,36,0),(Ev,36,3),(B0,36,7),(AZ,36,9),(Ls,51,2),(Ee,51,5),(La,61,2)])) (bn (bl [(r4,4,0),(jW,4,7),(st,12,0)]) (bl []))) (bn (bn (bl []) (bl [(zs,4,2),(gL,4,5),(QK,17,8),(qM,36,4),(mZ,36,8),(Lv,49,8),(Ll,54,8)])) (bn (bl [(Em,44,3),(El,44,9)]) (bl []))))) (bn (bn (bn (bn (bl []) (bl [(Mh,27,8),(Md,30,2),(Mb,30,5)])) (bn (bl [(r0,0,0),(h2,0,3),(h4,1,2),(r3,3,0),(hH,3,5),(EF,3,7),(r5,5,0),(QR,5,5),(xG,5,7),(r6,6,0),(DY,6,7),(r8,8,0),(Sz,8,2),(Sy,8,5),(r9,9,0),(Sw,9,2),(QG,10,0),(Hd,10,8),(DR,11,0),(Sq,11,4),(GZ,13,0),(So,13,4),(Sn,13,7),(Sm,13,8),(QF,14,0),(QE,15,0),(DQ,18,0),(QI,18,7),(DP,19,0),(QH,19,2),(y4,19,5),(MA,19,7),(xZ,20,4),(xY,20,8),(Ba,21,8),(Mv,22,3),(Mt,22,7),(QD,23,0),(GY,24,0),(Mp,24,4),(Mn,24,7),(uX,24,8),(GX,25,0),(Mm,25,5),(QC,26,0),(EH,26,7),(GW,31,0),(Ey,31,7),(GV,33,0),(M5,33,7),(Qz,34,0),(Qy,35,0),(DM,37,0),(Eu,37,2),(LY,37,5),(LW,37,7),(DL,38,0),(LU,38,7),(LT,38,8),(Qx,39,0),(GU,41,0),(GT,42,0),(Eo,42,2),(Qw,43,0),(Qv,45,0),(LA,45,7),(Qu,47,0),(Qt,49,0),(DK,50,0),(Lu,50,4),(Eh,50,7),(Lt,50,8),(Ca,52,0),(GS,54,0),(Qs,55,0),(Qr,56,0),(DJ,57,0),(AV,57,8),(Qq,59,0),(DI,60,0),(pR,64,0),(uO,64,4)]) (bl []))) (bn (bn (bl []) (bl [])) (bn (bl []) (bl [(Eg,51,1),(Ed,51,6),(E3,63,1),(xI,63,6)])))) (bn (bn (bn (bl [(QQ,6,1),(zr,6,6),(QO,8,1),(QM,8,6),(Sx,9,1),(Su,9,6),(Ss,11,1),(Sr,11,3),(xd,20,0),(Mx,21,9),(Mr,24,1),(Mq,24,3),(Mo,24,6),(EK,24,9),(LH,42,6),(xP,52,1),(Ea,52,6),(Lm,54,6)]) (bl [])) (bn (bl [(Cm,6,2),(QP,6,5),(Cc,40,0),(LK,40,7)]) (bl [(LB,45,1)]))) (bn (bn (bl []) (bl [(kF,7,1),(tJ,7,2),(tI,7,4),(nN,7,5),(tH,7,6),(vM,7,8),(tF,16,3),(Sk,16,9),(xV,28,1),(B6,28,3),(B5,28,6),(B4,28,9),(EC,30,1),(xU,30,6),(Ew,36,2),(xT,36,5),(sQ,40,3),(Eq,40,9),(E2,63,4),(sP,63,8),(uP,64,1),(AT,64,3)])) (bn (bl [(h3,0,4),(r2,2,0),(h8,2,2),(h9,2,3),(fT,2,4),(pZ,4,3),(tL,4,4),(tK,4,8),(rl,4,9),(xK,5,4),(vP,5,8),(DZ,6,4),(vO,6,8),(vN,7,3),(xF,7,9),(QN,8,4),(DX,8,8),(St,9,8),(Sl,14,8),(tG,15,8),(QL,17,2),(H7,17,3),(H6,17,5),(Sj,17,9),(QJ,18,4),(Cj,18,8),(y3,19,8),(EJ,25,4),(B8,25,8),(sR,26,3),(uW,26,5),(Mi,26,9),(tw,28,0),(Me,28,7),(M8,32,2),(M7,32,3),(Ex,32,5),(LQ,39,2),(AY,39,3),(pe,39,5),(LN,39,9),(Es,40,4),(qL,40,8),(Ep,41,8),(En,42,8),(LG,43,2),(LD,44,2),(Ek,46,3),(Lz,46,5),(Ly,46,9),(Lx,48,2),(Lw,48,5),(Ei,49,3),(Cb,51,0),(Lr,51,4),(Lq,51,7),(Ec,51,8),(AW,52,2),(uS,52,3),(xO,52,5),(xN,52,9),(Lo,53,2),(E8,53,5),(Lh,58,3),(Lg,58,8),(Lf,58,9),(Ld,59,3),(AU,59,5),(C9,61,0),(L9,61,4),(L8,62,3),(E4,62,5),(uR,63,2),(xJ,63,5)]) (bl [(h0,0,1),(h1,0,2),(QS,5,1),(E6,5,3),(E0,5,6),(Hg,5,9),(Cl,6,3),(SA,6,9),(Hf,8,3),(He,8,9),(Sv,9,3),(H3,19,1),(Ci,19,3),(MB,19,6),(Mz,19,9),(xX,22,1),(Mu,22,6),(B9,25,3),(Ml,25,9),(Mk,26,4),(B7,26,8),(uT,31,1),(Ez,31,6),(xR,37,3),(LV,37,9),(LJ,41,3),(LI,42,3),(LF,43,3),(LC,44,8),(Eb,52,4),(E9,52,8),(Ln,54,3),(Lk,55,3),(Lj,55,9),(Lb,61,1),(E5,61,3),(mY,64,2)]))))))
def gK:LS:=[r7,pY,vC,ra,xF,st]
def eW:LS:=[r7,xF,ra,pY,xJ,r4,kF,pR,vN,st,uR,Ck]
def fj:LS:=[uO]
def Se:LS:=[r4,GW,pR,Ca,LY,Eu,r7,jW,DI,EH,vC,DK,y4]
def Sd:LS:=[xF,r7,uR,tH,rl,tJ,uP,Ck,r4,DN]
def Sc:LS:=[xF,uR,mY,Cm,xN,rl,uP,zs,Sh,r7,AW,EF]
def Sb:LS:=[r4,QH,GW,r0,Ca,uR,Eu,Eo,GV,Cm,xG]
def Sa:LS:=[xG,uR,xH,QH,DY,r7,Cm,GV,LW,DO,EF,MA]
def S9:LS:=[vC,r6,DL,Ca,xY,y4,uX,M5,r4,h2,DQ]
def S8:LS:=[QC,xJ,gL,Cm,Ck,r2,EH,Er,ra,Ca,pY,Sz,Qx,Qq,hH,vN,H6,Sw,La,uV,AU,r4,DO,Eo]
def L5:LS:=[Ck,xJ,ra,vC,pY,uV,y4,kF,jW,r5]
def L4:LS:=[Ck,mY,H4,Ls,Ee,zs,DO,qN,Cm,jW]
def L3:LS:=[xJ,QP,DM,H4,uW,AT,mY,pZ,r8,vN,kG,xO,Er,Ey,gL,uX,LG,h2,xY,vP,Qt,jW,GU,xM,r3,nN,AY,QR,Ee,DL]
def L2:LS:=[y4,r8,r6,h2,DP,QR,QP,Qr,vC,uX,Sy,Mm,xd,Mt,xM,GU]
def L0:LS:=[r6,pZ,uW,gL,vP,pY,mY,uU,xO,Cc,DM,xW,GS,kF,vC,GZ,Qu,hH,E4,nN,r3,y3]
def KZ:LS:=[r8,pZ,uU,GS,DM,H6,uS,uX,pY,GX,DR,xd,sR,QD,vC,gL,Ei,pe,DP,uW,Hd,DJ,Cc,Qs]
def KY:LS:=[kF,sP,ra,o0,gL,nN,B1,h0,rl,Ha,vM,uP,Qz,M3,qO,xT,Eg]
def KX:LS:=[sP,ra,gL,kF,xT,vM,mZ,rl,qM]
def KW:LS:=[vO,xQ,uP,sP,Cj,kF,E6,o0,y3,xd,uT,sS]
def KV:LS:=[xR,sP,o0,B7,xX,uP,pR,tK,kF,h6,h0,qL,E0,sS,kG,vP]
def KU:LS:=[C9,DQ,r6,ra,vO,r4,Cb,tK,Cj]
def KT:LS:=[ra,Cb,r2,r4,Ec,tw,Cj,pe,r0,r6,C9]
def KS:LS:=[C9,DQ,DK,r6,vO,Cj,tK,xY,r4,LT,Cb,DR,qL,pR,st,ra,H7,vP,xd,Ba]
def KR:LS:=[Cb,r4,r2,pR,st,Cj,Ec,C9,Cc,DK,tw,ra,rl,AU,pe,Lt,Ex,EA,qM,Qy]
def KQ:LS:=[h0,Ci,gL,y3,xX,o0,Cl,xQ,xR,uT,xW,vO]
def KP:LS:=[Ci,Hf,o0,uT,uQ,h0,B9,Cl,nN,vP]
def KO:LS:=[B8,gL,vP,sP,h0,uU,DX,E6,xQ,kF,sQ,sR,uQ,xW,pe,Ci,h5,y3,En,Ep,vO]
def KN:LS:=[xQ,uU,vO,gL,DX,xd,sP,sR,H7,Ll,Ci,h0,GY,pe,qL,uS,En,E8,B1,nN,Li,xO,xW,uW,Ba,AV,Cn]
def KM:LS:=[r6,xO,vP,pe,sR,E4,uW,B8,AU,uS,r2,Em,DX,pZ,r5,qL,Ep,r9,vO,gL,St,Sl]
def KL:LS:=[vP,GZ,r6,B8,pe,xY,sR,r5,Qw,Ex,tG,DL,E8,Ba,gL,uS,Em,Lw,AV,Hd,Ek,pZ,Lh]
def KK:LS:=[r8,uS,AY,Sm,r5,L8,pZ,GT,sR,QE,xd,GX,Ld,QG,r6,M7,vO,QF,Lz,DJ,DP,r9,xM]
def KJ:LS:=[DR,H6,r6,pe,r8,DX,Ei,AY,uX,uU,GY,Cc,qL,pZ,GT,Hd,DJ,r9,AV,gL,xM]
def KI:LS:=[kF,AT,vN,H9,Hc,nN,r7,pZ,mY,tI,xF,tF,Cn,Mv,pY,qN]
def KH:LS:=[xH,pY,r7,pR,vN,Hc,Ey,pZ,jW,DI,uV,Eh,uO]
def KG:LS:=[DY,rl,AW,xH,xN,ED,QI,xZ,Mp,E7,El,xK]
def KF:LS:=[xH,r7,mY,tJ,zs,Hc,tH,h8,AZ,Mw,ED,LM,M4,h4,LK]
def KE:LS:=[kF,pY,r7,xS,xF,tJ,qN,mY,tH,tF,AZ,vN,rl,tI,DN,tw,nN,LB,Hb]
def KD:LS:=[r7,pY,xF,pR,st,DN,tw,rl,AZ,uO,B0,Hb,Qv]
def KC:LS:=[tF,pZ,kF,mY,H8,uQ,Ev,pY,uV,vN,Cn,nN]
def KB:LS:=[pY,Md,mY,vN,Ev,qN,tw,Mg,nN,Mb,B0,Mf]
def KA:LS:=[E2,tH,zs,gV,AT,H9,DZ,tJ,h1,pZ,tL,tF,qM,Hg,LV,E3,B0]
def Kz:LS:=[L9,Lq,DY,Eh,h8,uO,Lr,Lu,H9,QI,jW,xZ,DI,DZ,QJ,QL,tL]
def Ky:LS:=[xK,zs,h1,tH,EJ,E1,Ez,gV,Ma,DZ,QN,xN,tJ,LZ,xZ,M6,Es,E2,Mn]
def Kx:LS:=[Mi,LQ,xK,AW,Sn,zs,xZ,Sq,xN,So,EJ,QN,M8,QL,DY,DZ,h8,Lo,LN,El,LD,Lx,xG,E7,LU,Lf,rl,Es,Ly]
def Kw:LS:=[uO,tF,gV,tH,pZ,tJ,xI,H5,E5,mZ,tI,tL,xS]
def Kv:LS:=[tH,qM,mZ,vM,tI,gV,tL,xU,tJ,EE,LA,EB,Ew,B3]
def Ku:LS:=[tH,gV,E1,Ez,xS,tJ,He,Mu,Eb,DW,B3,Mz,Lj]
def Kt:LS:=[tH,tJ,Me,B3,EB,xS,xV,Hb,Eq,EC,Ew,EE,fT,B4,Sj]
def Ks:LS:=[xI,tK,zr,h3,qO,H3]
def Kr:LS:=[Cl,uQ,E5,qO,h7,zr,Sg,Ef,xP,sQ,QK,o0,Ed,h9,Ej,H5,E0,xU,E6,Le,Et]
def Kq:LS:=[B7,qO,E6,E9,LX,tK,Ci,zr,xP,kF,Hf,QS,sQ,sS,Cl,xR,Lm,o0,pR,xX,H3,LI,Lk,B9,qL]
def Kp:LS:=[B7,QM,E9,h3,tK,Hf,Ej,QK,E0,Cl,Sr,o0,LE,xP,Mo,EI,Su,zr,Mq,Sv,LJ,LH,Ln,sS]
def Ko:LS:=[E3,QQ,vM,tL,Mj,tI,zr,H3,E0,nN,DW,uT,o0,AX,h3,He,qO,QO,pR,Ea,EG,EK,xI,sS,MB]
def Kn:LS:=[Lb,h7,QQ,Mk,Eg,Si,Lp,Eb,LO,Sf,DW,Ml,Ss,Ea,QO,Mr,L7,fT,Eq,AX,He,rl,QS,SA,Mx,tL,EK,My,xV,Lc,EG,o0,Sx]
def Km:LS:=[Ha,uQ,o0,kF,nN,uT,B1,qN,qO,xP,xX,mZ,vM,B9,xR,LC,QM]
def Kl:LS:=[h7,zr,Ha,xI,DW,LL,B4,sS,Ed,Ef,tI,vM,Et,qO,M0,mZ,gV,LF,B2,AX,o0]
def Kk:LS:=[tF,tK,kF,tI,tL,mZ,B2]
def Kj:LS:=[tF,tK,tL,pR,Ms,st,tI,sQ,B6,H8,kF]
def Ki:LS:=[kF,tF,H8,sQ,nN,tw,h5,h9,st,H7,qL,tK,Lv,Mh,Ek,Lg]
def Kh:LS:=[tF,sQ,h9,B6,B5]
def Kg:LS:=[xT,kF,qN,mZ,vM,nN,qM,tw,pR,Sp,st,rl,xV]
def Kf:LS:=[kF,tw,qN,nN,xU,QA,EA,xT,st,uV,B5]
def Ke:LS:=[xU,mZ,qM,EC,Sk]
def Kd:LS:=[qM,mZ,vM,tI,xV,B6,fT,B2,tL,Mc,B4,M9,B5]
def jZ:BTree LS:=(bn (bn (bn (bn (bn (bn (bl gK) (bl eW)) (bn (bl fj) (bl Se))) (bn (bn (bl Sd) (bl Sc)) (bn (bl Sb) (bl Sa)))) (bn (bn (bn (bl S9) (bl S8)) (bn (bl L5) (bl L4))) (bn (bn (bl L3) (bl L2)) (bn (bl L0) (bl KZ))))) (bn (bn (bn (bn (bl KY) (bl KX)) (bn (bl KW) (bl KV))) (bn (bn (bl KU) (bl KT)) (bn (bl KS) (bl KR)))) (bn (bn (bn (bl KQ) (bl KP)) (bn (bl KO) (bl KN))) (bn (bn (bl KM) (bl KL)) (bn (bl KK) (bl KJ)))))) (bn (bn (bn (bn (bn (bl KI) (bl KH)) (bn (bl KG) (bl KF))) (bn (bn (bl KE) (bl KD)) (bn (bl KC) (bl KB)))) (bn (bn (bn (bl KA) (bl Kz)) (bn (bl Ky) (bl Kx))) (bn (bn (bl Kw) (bl Kv)) (bn (bl Ku) (bl Kt))))) (bn (bn (bn (bn (bl Ks) (bl Kr)) (bn (bl Kq) (bl Kp))) (bn (bn (bl Ko) (bl Kn)) (bn (bl Km) (bl Kl)))) (bn (bn (bn (bl Kk) (bl Kj)) (bn (bl Ki) (bl Kh))) (bn (bn (bl Kg) (bl Kf)) (bn (bl Ke) (bl Kd)))))))
def ej (sa _sb qa qb:Nat):LS:=(cond (nB 19 (shiftRight qb 24)) (cond (nB 14 (land (shiftRight qb 6) 63)) (cond (nB 14 (land (shiftRight qb 18) 63)) (cond (nB 14 (land (shiftRight qb 12) 63)) (cond (nB 4 (land qb 63)) (cond (nB 19 (land (shiftRight qb 12) 63)) gK eW) (cond (nB 24 (land (shiftRight qb 12) 63)) fj Se)) (cond (nB 9 (land qb 63)) (cond (nB 9 (land (shiftRight qb 12) 63)) Sd Sc) (cond (nB 24 (shiftRight qb 24)) Sb Sa))) (cond (nB 9 (land (shiftRight qb 18) 63)) (cond (nB 24 (shiftRight qb 24)) (cond (nB 19 (land (shiftRight qb 12) 63)) S9 S8) (cond (nB 14 (land (shiftRight qb 12) 63)) L5 L4)) (cond (nB 19 (land (shiftRight qb 6) 63)) (cond (nB 4 (land qb 63)) L3 L2) (cond (nB 2 (land (shiftRight qa 10) 31)) L0 KZ)))) (cond (nB 9 (land (shiftRight qb 18) 63)) (cond (nB 14 (land qb 63)) (cond (nB 4 (land (shiftRight qb 6) 63)) (cond (nB 19 (land qb 63)) KY KX) (cond (nB 24 (shiftRight qb 24)) KW KV)) (cond (nB 24 sa) (cond (nB 24 (land (shiftRight qb 12) 63)) KU KT) (cond (nB 24 (land (shiftRight qb 12) 63)) KS KR))) (cond (nB 14 (land qb 63)) (cond (nB 24 (land qb 63)) (cond (nB 24 (shiftRight qb 24)) KQ KP) (cond (nB 4 (land (shiftRight qa 10) 31)) KO KN)) (cond (nB 2 (land (shiftRight qa 10) 31)) (cond (nB 4 (land (shiftRight qa 5) 31)) KM KL) (cond (nB 2 (land qa 31)) KK KJ))))) (cond (nB 14 (land (shiftRight qb 6) 63)) (cond (nB 14 (shiftRight qb 24)) (cond (nB 19 (land (shiftRight qb 6) 63)) (cond (nB 14 (land (shiftRight qb 12) 63)) (cond (nB 14 (land qb 63)) KI KH) (cond (nB 24 (land (shiftRight qb 18) 63)) KG KF)) (cond (nB 14 (land (shiftRight qb 18) 63)) (cond (nB 14 (land qb 63)) KE KD) (cond (nB 19 (land (shiftRight qb 12) 63)) KC KB))) (cond (nB 19 (land (shiftRight qb 6) 63)) (cond (nB 9 (land (shiftRight qb 12) 63)) (cond (nB 14 (land qb 63)) KA Kz) (cond (nB 14 (land qb 63)) Ky Kx)) (cond (nB 14 (land (shiftRight qb 12) 63)) (cond (nB 19 (land (shiftRight qb 12) 63)) Kw Kv) (cond (nB 19 (land qb 63)) Ku Kt)))) (cond (nB 19 (land qb 63)) (cond (nB 24 (land (shiftRight qb 12) 63)) (cond (nB 4 (land (shiftRight qb 6) 63)) (cond (nB 14 (land (shiftRight qb 18) 63)) Ks Kr) (cond (nB 2 (land (shiftRight qa 15) 31)) Kq Kp)) (cond (nB 19 (land (shiftRight qb 18) 63)) (cond (nB 14 (land (shiftRight qb 12) 63)) Ko Kn) (cond (nB 14 (shiftRight qb 24)) Km Kl))) (cond (nB 19 (land (shiftRight qb 12) 63)) (cond (nB 14 (land (shiftRight qb 18) 63)) (cond (nB 24 sa) Kk Kj) (cond (nB 14 (shiftRight qb 24)) Ki Kh)) (cond (nB 14 (shiftRight qb 24)) (cond (nB 14 (land (shiftRight qb 18) 63)) Kg Kf) (cond (nB 8 (land (shiftRight qa 15) 31)) Ke Kd))))))
lemma pS (b a d c:Nat):dn (ej b a d c) jZ:=by unfold ej jZ;repeat (first|apply i0|rfl)
def fp:List AS:=[(24,9670784,0xdb6d2412000,0xdb6d2412000),(23,9736224,0xdb6da408000,0xdb6da408000),(23,9541761,0xdb603612040,0xdb24a492040),(24,6497376,0xda6c36d8000,0xda4936c9200),(24,3449952,0xc96db6d8000,0xc96db6c9200),(24,yD,0xda6d249b000,0xda6d3612400),(24,9538848,0xdb60125b600,0xdb24b01b600),(24,9544800,0xdb6036d8000,0xdb24b6c9200),(24,6592577,0x926db610040,0xd86da489040),(24,9610272,0xdb64b6c8000,0xdb64b6c8000),(22,9672704,0xdb693680000,0xdb6cb680000),(23,4400225,9915257946176,9924653126208),(23,6492353,0x926c2412440,0xd849241b040),(24,9541824,0xdb60249b400,0xdb24b61b400),(24,6588609,0x926d9212440,0xd86da01b040),(24,6431842,0x9244b6d8048,0xd86436c9280),(21,9570496,0xdb641212400,0xdb44a01b000)]
def Bh (a b:cT):Bool:=
 (nE a.1 a.2.1&&nE b.1 b.2.1&&nE a.1 b.1)||
 ((a.2.2 == b.2.2)&&((nE a.1 b.1&&nE a.2.1 b.2.1)||(nE a.1 b.2.1&&nE a.2.1 b.1)))
def zq (q:RL):Bool:=
 ii q (jE q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1)
def ck (p q:cT × Nat):Bool:=
 let d:=Bj p.1;let b:=Bi p.1
 bi (fun g=>
  let h:=gY g q.1;let c:=Bj h;let a:=Bi h
  zq (mw (land d c) (land b a))&&
  zq (mw (lor d c) (lor b a))) (eJ p.2 q.2)
def kj (sa sb aw bw ar ac b0 b1 b2:Nat):Bool:=
 g8 sa sb aw bw ar ac b0 b1 b2 (jD sa sb aw bw)
def ki (sa sb aw bw ar ac b0 b1 b2:Nat):Bool:=
 g8 sa sb aw bw ar ac b0 b1 b2 (jC sa sb aw bw)
def Kc (x:RS):Bool:=
 kj x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
  x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2
def Kb (x:RS):Bool:=
 ki x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
  x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2
def bc (p q:RL × Nat):Bool:=
 let b:=p.1.1;let qr:=q.1.1;let pa:=b.2.2.1;let pb:=b.2.2.2.1
 bi (fun g=>
  let a:=ay g qr;let T:=fF pa a.2.2.1;let P:=eI pb a.2.2.2.1;let a2:=bD T;let a0:=bG P;let j:=ez b.2.2.2.2.1 a.2.2.2.2.1;let k:=ez b.2.2.2.2.2.1 a.2.2.2.2.2.1;let M:=em b.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1;let K:=em b.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1;let C:=em b.2.2.2.2.2.2.2.2 a.2.2.2.2.2.2.2.2;let x:=kj a2 a0 T P j k M K C;let w:=ki a2 a0 T P j k M K C
  let a6:=(x&&w)||
    (let i:=e9 pa a.2.2.1 b.2.2.2.2.1 b.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1
     let h:=gl pb a.2.2.2.1 b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2
      a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2
     let t:=bD i;let r:=bG h;let n:=ci b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2 a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2;let m:=ci b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2;let l:=ci b.2.2.2.2.2.2.2.2 b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2 a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1
     (x||kj t r i h j k n m l)&&
     (w||ki t r i h j k n m l))
  a6&&
  (let W:=eo pa a.2.2.1;let Q:=dF pb a.2.2.2.1
   let a3:=bD W;let a1:=bG Q;let c:=dH b.2.2.2.2.1 b.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1;let d:=dH b.2.2.2.2.2.1 b.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.1;let N:=cp b.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1;let L:=cp b.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1;let F:=cp b.2.2.2.2.2.2.2.2 a.2.2.2.2.2.2.2.2;let z:=kj a3 a1 W Q c d N L F;let y:=ki a3 a1 W Q c d N L F
   (z&&y)||
   (let i:=e4 pa a.2.2.1 b.2.2.2.2.1 b.2.2.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1
    let h:=dZ pb a.2.2.2.1 b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2
      a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2
    let t:=bD i;let r:=bG h;let n:=eN b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2 a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2;let m:=eN b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2;let l:=eN b.2.2.2.2.2.2.2.2 b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2 a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1;let v:=z||kj t r i h c d n m l;let u:=y||ki t r i h c d n m l
    (v&&u)||
    (let xa:=(t,r,i,h,c,d,n,m,l)
     let tr:=kJ p.1 (a,bR g q.1.2)
     (v||dg Kc tr xa)&&(u||dg Kb tr xa))))) (eJ p.2 q.2)
def p9 (qa qb:Nat):Bool:=
 let a:=bG qb
 nB 102 a||
 (let b:=bD qa
  nB b 10||(nB b 44&&nB 68 a)||mz qa qb (gF b a qa qb))
def cG (p q:RS × Nat):Bool:=
 let a:=p.1;let j:=q.1;let i:=a.1;let d:=a.2.1;let h:=j.1;let c:=j.2.1
 let w:=
   nB 102 d||nB 102 c||
   nB (i+h) 10||
   (nB (i+h) 44&&(nB 68 d||nB 68 c))||
   (let v:=a.2.2.1;let u:=a.2.2.2.1
    bi (fun g=>
      let r:=cx g j.2.2.2.1;let m:=eI u r;let k:=bG m
      nB 102 k||
      (let t:=bH g j.2.2.1
       let n:=fF v t;let l:=bD n
       nB l 10||(nB l 44&&nB 68 k)||
       mz n m (gF l k n m)||
       (let b:=ay g j
        p9 (e9 v t a.2.2.2.2.1 a.2.2.2.2.2.1 b.2.2.2.2.1 b.2.2.2.2.2.1)
          (gl u r a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2
           b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2)))) (eJ p.2 q.2))
 w&&
 (nB 237 (d+c)||
  nB i 10||nB h 10||
  ((nB i 44||nB h 44)&&nB 203 (d+c))||
  (let v:=a.2.2.1;let u:=a.2.2.2.1
   bi (fun g=>
     let t:=bH g j.2.2.1;let n:=eo v t;let l:=bD n
     nB l 10||
     (let r:=cx g j.2.2.2.1
      let m:=dF u r;let k:=bG m
      nB 102 k||(nB l 44&&nB 68 k)||
      mz n m (gF l k n m)||
      (let b:=ay g j
       p9 (e4 v t a.2.2.2.2.1 a.2.2.2.2.2.1 b.2.2.2.2.1 b.2.2.2.2.2.1)
         (dZ u r a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2
           b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2)))) (eJ p.2 q.2)))
def jl (p q:RS) (sa0:Nat):Bool:=
 let d:=gl p.2.2.2.1 q.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2
     q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2
 let a:=bG d
 nB 87 a||(nB sa0 20&&nB 1 a)||
 (let c:=e9 p.2.2.1 q.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
  let b:=bD c
  nB b 8||(nB b 20&&nB 1 a)||
  (nE a 0&&i3 (b,c,ez p.2.2.2.2.1 q.2.2.2.2.1,ez p.2.2.2.2.2.1 q.2.2.2.2.2.1) dY)||
  (nB 49 a&&
   i2 b a c d (ez p.2.2.2.2.1 q.2.2.2.2.1) (ez p.2.2.2.2.2.1 q.2.2.2.2.2.1)
    (ci p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2)
    (ci p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2 q.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2)
    (ci p.2.2.2.2.2.2.2.2 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1)
    (ej b a c d)))
def iH (p q:RS) (sa0:Nat):Bool:=
 let d:=dZ p.2.2.2.1 q.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2
      q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2
 let a:=bG d
 nB 87 a||(nB sa0 20&&nB 1 a)||
 (let c:=e4 p.2.2.1 q.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
  let b:=bD c
  nB b 8||(nB b 20&&nB 1 a)||
  (nE a 0&&
    i3 (b,c,dH p.2.2.2.2.1 p.2.2.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1,
      dH p.2.2.2.2.2.1 p.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.1) dY)||
  (nB 49 a&&
   i2 b a c d
     (dH p.2.2.2.2.1 p.2.2.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1)
     (dH p.2.2.2.2.2.1 p.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.1)
     (eN p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2)
     (eN p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2 q.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2)
     (eN p.2.2.2.2.2.2.2.2 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.2 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2.1)
     (ej b a c d)))
def ba (p q:RS × Nat):Bool:=
 let c:=p.1;let n:=q.1;let m:=c.1;let k:=c.2.1;let l:=n.1;let j:=n.2.1
 let r:=
   nB 87 k||nB 87 j||
   nB (m+l) 8||
   (nB (m+l) 20&&(nB 1 k||nB 1 j))||
   (let w:=c.2.2.1;let v:=c.2.2.2.1
    bi (fun g=>
      let t:=cx g n.2.2.2.1;let h:=eI v t;let a:=bG h
      nB 87 a||
      (let u:=bH g n.2.2.1
       let i:=fF w u;let b:=bD i
       nB b 8||(nB b 20&&nB 1 a)||
       (let d:=ay g n
        (nB 49 a&&
         i2 b a i h
           (ez c.2.2.2.2.1 d.2.2.2.2.1) (ez c.2.2.2.2.2.1 d.2.2.2.2.2.1)
           (em c.2.2.2.2.2.2.1 d.2.2.2.2.2.2.1)
           (em c.2.2.2.2.2.2.2.1 d.2.2.2.2.2.2.2.1)
           (em c.2.2.2.2.2.2.2.2 d.2.2.2.2.2.2.2.2)
           (ej b a i h))||
        jl c d b))) (eJ p.2 q.2))
 r&&
 (nB 222 (k+j)||
  nB m 8||nB l 8||
  ((nB m 20||nB l 20)&&nB 136 (k+j))||
  (let w:=c.2.2.1;let v:=c.2.2.2.1
   bi (fun g=>
     let u:=bH g n.2.2.1;let i:=eo w u;let b:=bD i
     nB b 8||
     (let t:=cx g n.2.2.2.1
      let h:=dF v t;let a:=bG h
      nB 87 a||(nB b 20&&nB 1 a)||
      (let d:=ay g n
       (nB 49 a&&
        i2 b a i h
          (dH c.2.2.2.2.1 c.2.2.2.2.2.1 d.2.2.2.2.1 d.2.2.2.2.2.1)
          (dH c.2.2.2.2.2.1 c.2.2.2.2.1 d.2.2.2.2.2.1 d.2.2.2.2.1)
          (cp c.2.2.2.2.2.2.1 d.2.2.2.2.2.2.1)
          (cp c.2.2.2.2.2.2.2.1 d.2.2.2.2.2.2.2.1)
          (cp c.2.2.2.2.2.2.2.2 d.2.2.2.2.2.2.2.2)
          (ej b a i h))||
       iH c d b))) (eJ p.2 q.2)))
def vF (u v:iN):Bool:=
 nB 68 (bG u.2)||nB 68 (bG v.2)||
 q7 (fun g=>
  nB (gP u.1 (bH g v.1)) 44||
  nB 68 (iW u.2 (cx g v.2)))
def xq (u v:AS):Bool:=
 q7 (fun g=>
  nB (gP u.2.1 (bH g v.2.1)) 20||
  (let z:=sG u (cB g v)
   nB z.1 20||i3 z fp))
def pV (u v:RS):Bool:=
 nB 136 (u.2.1+v.2.1)||
 q7 (fun g=>
  nB 1 (i8 u.2.2.2.1 (cx g v.2.2.2.1))||
  nB (i9 u.2.2.1 (bH g v.2.2.1)) 20||
  (let a:=ay g v
   let b:=dZ u.2.2.2.1 a.2.2.2.1 u.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.2
     a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2
   nB 1 (bG b)||
   (let z:=pU (u.1,u.2.2.1,u.2.2.2.2.1,u.2.2.2.2.2.1) (a.1,a.2.2.1,a.2.2.2.2.1,a.2.2.2.2.2.1)
    nB z.1 20||i3 z fp)))
def AQ (u v:AS):Bool:=
 q7 (fun g=>
  let a:=cB g v
  nB (bD (e9 u.2.1 a.2.1 u.2.2.1 u.2.2.2 a.2.2.1 a.2.2.2)) 44)
def n6 (a b:RS):Bool:=
 nE a.2.2.1 b.2.2.1&&nE a.2.2.2.1 b.2.2.2.1&&
 nE a.1 b.1&&nE a.2.1 b.2.1&&
 nE a.2.2.2.2.1 b.2.2.2.2.1&&nE a.2.2.2.2.2.1 b.2.2.2.2.2.1&&
 nE a.2.2.2.2.2.2.1 b.2.2.2.2.2.2.1&&nE a.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1&&
 nE a.2.2.2.2.2.2.2.2 b.2.2.2.2.2.2.2.2
def yl (a b:RL):Bool:=n6 a.1 b.1&&nE a.2 b.2
def vV (a b:iN):Bool:=nE a.1 b.1&&nE a.2 b.2
def kO (x:RL × Nat):Bool:=
 o4 x.1&&(nE x.2 0||(nB 5 x.2&&Nat.blt x.2 10&&yl (d7 x.2 x.1) x.1))
def j4 (x:RS × Nat):Bool:=
 jm x.1&&(nE x.2 0||(nB 5 x.2&&Nat.blt x.2 10&&n6 (ay x.2 x.1) x.1))
def kP (reps:List iN) (w:iN × Nat × Nat):Bool:=
 match reps[w.2.1]? with
 | none=>false
 | some r=>Nat.blt w.2.2 10&&vV (dV w.2.2 r) w.1
def mg (reps:List RS) (w:RS × Nat × Nat):Bool:=
 match reps[w.2.1]? with
 | none=>false
 | some r=>Nat.blt w.2.2 10&&n6 (ay w.2.2 r) w.1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_cover :
 bi (fun r=>Nat.blt r.1.1 15&&Nat.blt r.1.2.1 15&&
  (nE r.2 0||(nB 5 r.2&&Nat.blt r.2 10&&Bh (gY r.2 r.1) r.1))) iA=true/\
 (∀ (i j:Fin 15) (b:Bool),dW (fun r=>w0 (fun g=>Bh (gY g r.1) (i.val,j.val,b))) iA=true):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_wf_all :
 bi kO wd=true/\
 bi j4 j8=true/\
 bi j4 j7=true/\
 bi mf fr=true/\
 bi kN dY=true/\
 bi jm dX=true/\
 bi kN fp=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_bounds_l1 :
 bi (fun r=>nB (bD r.1) 34) fr=true/\
 bi (fun r=>nB r.1 12) dY=true/\
 bi (fun r=>nB 49 r.2.1) dX=true/\
 bi (fun r=>nB r.1 24) fp=true/\
 d3 (bi (fun y=>dW (fun r=>yl y r.1) wd)) zI=true/\
 d3 (bi (fun x=>Nat.blt x.2 10&&dW (fun y=>yl x.1 y) (lN zI (x.1.1.2.2.1+x.1.1.2.2.2.1)))) kV=true/\
 d3 (bi (fun y=>dW (fun r=>n6 y r.1) j8)) zF=true/\
 d3 (bi (fun x=>Nat.blt x.2 10&&dW (fun y=>n6 x.1 y) (lN zF (x.1.2.2.1+x.1.2.2.2.1)))) kU=true/\
 d3 (bi (kP fr)) s4=true/\
 d3 (bi (fun x=>dW (fun w=>vV x w.1) (lN s4 (x.1+x.2)))) kT=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_bounds_l2a :
 d3 (bi (fun y=>dW (fun r=>n6 y r.1) j7)) zE=true/\
 d3 (bi (fun x=>Nat.blt x.2 10&&dW (fun y=>n6 x.1 y) (lN zE (x.1.2.2.1+x.1.2.2.2.1)))) kS=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_bounds_l2b :
 d3 (bi (mg dX)) pK=true/\
 d3 (bi (fun x=>dW (fun w=>n6 x w.1) (lN pK (x.2.2.1+x.2.2.2.1)))) jZ=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_c0:J ck hG&&H ck [] hG=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_c1:J ck ik&&H ck [hG] ik=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_c2:J ck j9&&H ck [hG,ik] j9=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_c3:J ck jP&&H ck [hG,ik,j9] jP=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_c4:J ck kY&&H ck [hG,ik,j9,jP] kY=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_c5:J ck mD&&H ck [hG,ik,j9,jP,kY] mD=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_c6:J ck pE&&H ck [hG,ik,j9,jP,kY,mD] pE=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_d1_c7:J ck rA&&H ck [hG,ik,j9,jP,kY,mD,pE] rA=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c0:J bc dc&&H bc [] dc=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c1:J bc di&&H bc [dc] di=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c2:J bc dz&&H bc [dc,di] dz=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c3:J bc dL&&H bc [dc,di,dz] dL=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c4:J bc ev&&H bc [dc,di,dz,dL] ev=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c5:J bc eT&&H bc [dc,di,dz,dL,ev] eT=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c6:J bc fJ&&H bc [dc,di,dz,dL,ev,eT] fJ=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c7:J bc gj&&H bc [dc,di,dz,dL,ev,eT,fJ] gj=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c8:J bc hn&&H bc [dc,di,dz,dL,ev,eT,fJ,gj] hn=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c9:J bc ij&&H bc [dc,di,dz,dL,ev,eT,fJ,gj,hn] ij=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c10:J bc hD&&H bc [dc,di,dz,dL,ev,eT,fJ,gj,hn,ij] hD=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c11:J bc iz&&H bc [dc,di,dz,dL,ev,eT,fJ,gj,hn,ij,hD] iz=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c12:J bc js&&H bc [dc,di,dz,dL,ev,eT,fJ,gj,hn,ij,hD,iz] js=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c13:J bc kt&&H bc [dc,di,dz,dL,ev,eT,fJ,gj,hn,ij,hD,iz,js] kt=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c14:J bc mu&&H bc [dc,di,dz,dL,ev,eT,fJ,gj,hn,ij,hD,iz,js,kt] mu=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_p2_c15:J bc pC&&H bc [dc,di,dz,dL,ev,eT,fJ,gj,hn,ij,hD,iz,js,kt,mu] pC=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u3_c0:J cG jr&&H cG [] jr=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u3_c1:J cG k6&&H cG [jr] k6=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u3_c2:J cG kX&&H cG [jr,k6] kX=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u3_c3:J cG ml&&H cG [jr,k6,kX] ml=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u3_c4:J cG oa&&H cG [jr,k6,kX,ml] oa=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u3_c5:J cG qe&&H cG [jr,k6,kX,ml,oa] qe=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u3_c6:J cG td&&H cG [jr,k6,kX,ml,oa,qe] td=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u3_c7:J cG wa&&H cG [jr,k6,kX,ml,oa,qe,td] wa=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c0:J ba eu&&H ba [] eu=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c1:J ba eO&&H ba [eu] eO=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c2:J ba fq&&H ba [eu,eO] fq=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c3:J ba fU&&H ba [eu,eO,fq] fU=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c4:J ba gu&&H ba [eu,eO,fq,fU] gu=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c5:J ba gZ&&H ba [eu,eO,fq,fU,gu] gZ=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c6:J ba i6&&H ba [eu,eO,fq,fU,gu,gZ] i6=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c7:J ba iM&&H ba [eu,eO,fq,fU,gu,gZ,i6] iM=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c8:J ba jq&&H ba [eu,eO,fq,fU,gu,gZ,i6,iM] jq=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c9:J ba k5&&H ba [eu,eO,fq,fU,gu,gZ,i6,iM,jq] k5=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c10:J ba j6&&H ba [eu,eO,fq,fU,gu,gZ,i6,iM,jq,k5] j6=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c11:J ba jN&&H ba [eu,eO,fq,fU,gu,gZ,i6,iM,jq,k5,j6] jN=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c12:J ba kW&&H ba [eu,eO,fq,fU,gu,gZ,i6,iM,jq,k5,j6,jN] kW=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c13:J ba mC&&H ba [eu,eO,fq,fU,gu,gZ,i6,iM,jq,k5,j6,jN,kW] mC=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c14:J ba pz&&H ba [eu,eO,fq,fU,gu,gZ,i6,iM,jq,k5,j6,jN,kW,mC] pz=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v3_c15:J ba rz&&H ba [eu,eO,fq,fU,gu,gZ,i6,iM,jq,k5,j6,jN,kW,mC,pz] rz=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_u4:J vF fr=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v4c:J xq dY=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v4h:J pV dX=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_v5:J AQ fp=true:=by decide +kernel
lemma dy (b a:Fin 10) (h:(Fin 15->Bool)->Bool) :
  E (bx b (I a)) (E a h)=E b h:=by
 rw[<- cK,mi]
lemma e6 {a b:RS} (h:n6 a b=true):a=b:=by
 rcases a with ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9⟩;rcases b with ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9⟩;unfold n6 at h;simp only[bA] at h
 simp[bQ h.1.1.1.1.1.1.1.1,bQ h.1.1.1.1.1.1.1.2,
  bQ h.1.1.1.1.1.1.2,bQ h.1.1.1.1.1.2,
  bQ h.1.1.1.1.2,bQ h.1.1.1.2,
  bQ h.1.1.2,bQ h.1.2,bQ h.2]
lemma ma {a b:RL} (h:yl a b=true):a=b:=by
 rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩;unfold yl at h;simp only[bA] at h;exact Prod.ext (e6 h.1) (bQ h.2)
lemma pl {a b:iN} (h:vV a b=true):a=b:=by
 rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩;unfold vV at h;simp only[bA] at h;exact Prod.ext (bQ h.1) (bQ h.2)
lemma qP {a b:cT} (h:Bh a b=true):aN a=aN b:=by
 rcases a with ⟨a1,a2,ab⟩;rcases b with ⟨b1,b2,bb⟩;unfold Bh at h;simp only[bO,bA,beq_iff_eq] at h;rcases h with ⟨⟨h1,h2⟩,h3⟩|⟨hb,⟨h1,h2⟩|⟨h1,h2⟩⟩
 . have d:=bQ h1;have c:=bQ h2;have i:=bQ h3;subst d;subst c;subst i;rw[pk,pk]
 . have d:=bQ h1;have c:=bQ h2;subst hb;subst d;subst c;rfl
 . have d:=bQ h1;have c:=bQ h2;subst hb;subst d;subst c;exact vU _ _ _
lemma o5 {x:RL × Nat} (h:kO x=true) :
   gw x.1/\(x.2=0\/(5<=x.2/\x.2<10/\d7 x.2 x.1=x.1)):=by
 unfold kO at h;simp only[bA,bO,bL,nG] at h;refine ⟨q5 h.1,?_⟩;rcases h.2 with h0|⟨⟨h5,fT⟩,heq⟩
 . exact oL (bQ h0)
 . exact oR ⟨h5,fT,ma heq⟩
lemma jn {x:RS × Nat} (h:j4 x=true) :
   cu x.1/\(x.2=0\/(5<=x.2/\x.2<10/\ay x.2 x.1=x.1)):=by
 unfold j4 at h;simp only[bA,bO,bL,nG] at h;refine ⟨i1 h.1,?_⟩;rcases h.2 with h0|⟨⟨h5,fT⟩,heq⟩
 . exact oL (bQ h0)
 . exact oR ⟨h5,fT,e6 heq⟩
lemma od:∀ r ∈ wd,gw r.1/\(r.2=0\/(5<=r.2/\r.2<10/\d7 r.2 r.1=r.1)):=
 fun r hr=>o5 (aC cert_wf_all.1 r hr)
lemma rC:∀ r ∈ j8,cu r.1/\(r.2=0\/(5<=r.2/\r.2<10/\ay r.2 r.1=r.1)):=
 fun r hr=>jn (aC cert_wf_all.2.1 r hr)
lemma rB:∀ r ∈ j7,cu r.1/\(r.2=0\/(5<=r.2/\r.2<10/\ay r.2 r.1=r.1)):=
 fun r hr=>jn (aC cert_wf_all.2.2.1 r hr)
lemma pH:∀ r ∈ fr,kv r:=fun r hr=>po (aC cert_wf_all.2.2.2.1 r hr)
lemma mv:∀ r ∈ dY,iP r:=fun r hr=>ko (aC cert_wf_all.2.2.2.2.1 r hr)
lemma jx:∀ r ∈ dX,cu r:=fun r hr=>i1 (aC cert_wf_all.2.2.2.2.2.1 r hr)
lemma pG:∀ r ∈ fp,iP r:=fun r hr=>ko (aC cert_wf_all.2.2.2.2.2.2 r hr)
lemma Cw:∀ r ∈ fr,bD r.1<=34:=fun r hr=>
 bL.mp (aC cert_bounds_l1.1 r hr)
lemma zy:∀ r ∈ dY,r.1<=12:=fun r hr=>
 bL.mp (aC cert_bounds_l1.2.1 r hr)
lemma zx:∀ r ∈ dX,49<=r.2.1:=fun r hr=>
 bL.mp (aC cert_bounds_l1.2.2.1 r hr)
lemma Cv:∀ r ∈ fp,r.1<=24:=fun r hr=>
 bL.mp (aC cert_bounds_l1.2.2.2.1 r hr)
lemma o6 {a:List iN} {w:iN × Nat × Nat} (h:kP a w=true) :
  ∃ r ∈ a,∃ g:Fin 10,dV g.val r=w.1:=by
 unfold kP at h
 cases hget:a[w.2.1]? with
 | none=>rw[hget] at h;cases h
 | some r=>
  rw[hget] at h;simp only[bA,nG] at h;exact ⟨r,List.mem_of_getElem? hget,⟨w.2.2,h.1⟩,pl h.2⟩
lemma pp {a:List RS} {w:RS × Nat × Nat} (h:mg a w=true) :
  ∃ r ∈ a,∃ g:Fin 10,ay g.val r=w.1:=by
 unfold mg at h
 cases hget:a[w.2.1]? with
 | none=>rw[hget] at h;cases h
 | some r=>
  rw[hget] at h;simp only[bA,nG] at h;exact ⟨r,List.mem_of_getElem? hget,⟨w.2.2,h.1⟩,e6 h.2⟩
lemma rj (b a d c:Nat) {x:RL × Nat} (h:x ∈ jE b a d c) :
  (∃ r ∈ wd,r.1=x.1)/\x.2<10:=by
 have h1:=bA _ _ |>.mp (aC (co cert_bounds_l1.2.2.2.2.2.1 _ (rk b a d c)) x h);rcases cC h1.2 with ⟨y,hy,hxy⟩;have h2:=aC (co cert_bounds_l1.2.2.2.2.1 _ (jh zI (x.1.1.2.2.1+x.1.1.2.2.2.1))) y hy;rcases cC h2 with ⟨r,hr,hyr⟩;exact ⟨⟨r,hr,(ma hyr).symm.trans (ma hxy).symm⟩,nG.mp h1.1⟩
lemma rf (b a d c:Nat) {x:RS × Nat} (h:x ∈ jD b a d c) :
  (∃ r ∈ j8,r.1=x.1)/\x.2<10:=by
 have h1:=bA _ _ |>.mp (aC (co cert_bounds_l1.2.2.2.2.2.2.2.1 _ (ri b a d c)) x h);rcases cC h1.2 with ⟨y,hy,hxy⟩;have h2:=aC (co cert_bounds_l1.2.2.2.2.2.2.1 _ (jh zF (x.1.2.2.1+x.1.2.2.2.1))) y hy;rcases cC h2 with ⟨r,hr,hyr⟩;exact ⟨⟨r,hr,(e6 hyr).symm.trans (e6 hxy).symm⟩,nG.mp h1.1⟩
lemma rc (b a d c:Nat) {x:RS × Nat} (h:x ∈ jC b a d c) :
  (∃ r ∈ j7,r.1=x.1)/\x.2<10:=by
 have h1:=bA _ _ |>.mp (aC (co cert_bounds_l2a.2 _ (rd b a d c)) x h);rcases cC h1.2 with ⟨y,hy,hxy⟩;have h2:=aC (co cert_bounds_l2a.1 _ (jh zE (x.1.2.2.1+x.1.2.2.2.1))) y hy;rcases cC h2 with ⟨r,hr,hyr⟩;exact ⟨⟨r,hr,(e6 hyr).symm.trans (e6 hxy).symm⟩,nG.mp h1.1⟩
lemma iC (b a d c:Nat) {x:iN} (h:x ∈ gF b a d c) :
  ∃ r ∈ fr,∃ g:Fin 10,dV g.val r=x:=by
 have h1:=aC (co cert_bounds_l1.2.2.2.2.2.2.2.2.2 _ (re b a d c)) x h;rcases cC h1 with ⟨w,hw,hxw⟩;rw[pl hxw];exact o6 (aC (co cert_bounds_l1.2.2.2.2.2.2.2.2.1 _ (jh s4 (x.1+x.2))) w hw)
lemma fA (b a d c:Nat) {x:RS} (h:x ∈ ej b a d c) :
  ∃ r ∈ dX,∃ g:Fin 10,ay g.val r=x:=by
 have h1:=aC (co cert_bounds_l2b.2 _ (pS b a d c)) x h;rcases cC h1 with ⟨w,hw,hxw⟩;rw[e6 hxw];exact pp (aC (co cert_bounds_l2b.1 _ (jh pK (x.2.2.1+x.2.2.2.1))) w hw)
def T0 (f:(Fin 15->Bool)->Bool):Prop:=∃ i:Fin 15,f=fun x=>x i
def T1 (f:(Fin 15->Bool)->Bool):Prop:=∃ p:cT,og p/\f=aN p
def T2 (f:(Fin 15->Bool)->Bool):Prop:=
 ∃ r ∈ wd,∃ g:Fin 10,dj r.1 (R (E g f)) (O (E g f))
def yT (f:(Fin 15->Bool)->Bool):Prop:=
 ∃ r ∈ j8,∃ g:Fin 10,aW r.1 (R (E g f)) (O (E g f))
def yS (f:(Fin 15->Bool)->Bool):Prop:=
 ∃ r ∈ j7,∃ g:Fin 10,aW r.1 (R (E g f)) (O (E g f))
def T3 (f:(Fin 15->Bool)->Bool):Prop:=yT f/\yS f
def nc (f:(Fin 15->Bool)->Bool):Prop:=
 102<=bv (O f)\/bo (R f)<=10\/
 (bo (R f)<=44/\68<=bv (O f))\/
 ∃ r ∈ fr,∃ g:Fin 10,ju r (R (E g f)) (O (E g f))
def ms (f:(Fin 15->Bool)->Bool):Prop:=
 87<=bv (O f)\/bo (R f)<=8\/
 (bo (R f)<=20/\1<=bv (O f))\/
 (∃ r ∈ dY,∃ g:Fin 10,dk r (R (E g f)))\/
 (∃ r ∈ dX,∃ g:Fin 10,aW r (R (E g f)) (O (E g f)))
def T4 (f:(Fin 15->Bool)->Bool):Prop:=nc f/\ms f
def vl (f:(Fin 15->Bool)->Bool):Prop:=
 bo (R f)<=44\/68<=bv (O f)
def tf (f:(Fin 15->Bool)->Bool):Prop:=
 bo (R f)<=20\/1<=bv (O f)\/
 ∃ r ∈ fp,∃ g:Fin 10,dk r (R (E g f))
def T5 (f:(Fin 15->Bool)->Bool):Prop:=vl f/\tf f
def T6 (f:(Fin 15->Bool)->Bool):Prop:=
 bo (R f)<=44\/1<=bv (O f)
lemma pA {g:Fin 10} {f:(Fin 15->Bool)->Bool} (h:T2 (E g f)):T2 f:=by
 rcases h with ⟨r,hr,g',hd⟩;rw[cK] at hd;exact ⟨r,hr,bx g' g,hd⟩
lemma ga {g:Fin 10} {f:(Fin 15->Bool)->Bool} (h:yT (E g f)):yT f:=by
 rcases h with ⟨r,hr,g',hd⟩;rw[cK] at hd;exact ⟨r,hr,bx g' g,hd⟩
lemma g9 {g:Fin 10} {f:(Fin 15->Bool)->Bool} (h:yS (E g f)):yS f:=by
 rcases h with ⟨r,hr,g',hd⟩;rw[cK] at hd;exact ⟨r,hr,bx g' g,hd⟩
lemma mo {g:Fin 10} {f:(Fin 15->Bool)->Bool} (h:nc (E g f)):nc f:=by
 rcases h with h|h|⟨h1,h2⟩|⟨r,hr,g',hd⟩
 . left;rwa[bt] at h
 . right;left;rwa[bJ] at h
 . right;right;left;rw[bJ] at h1;rw[bt] at h2;exact ⟨h1,h2⟩
 . right;right;right;rw[cK] at hd;exact ⟨r,hr,bx g' g,hd⟩
lemma mr {g:Fin 10} {f:(Fin 15->Bool)->Bool} (h:ms (E g f)):ms f:=by
 rcases h with h|h|⟨h1,h2⟩|⟨r,hr,g',hd⟩|⟨r,hr,g',hd⟩
 . left;rwa[bt] at h
 . right;left;rwa[bJ] at h
 . right;right;left;rw[bJ] at h1;rw[bt] at h2;exact ⟨h1,h2⟩
 . right;right;right;left;rw[cK] at hd;exact ⟨r,hr,bx g' g,hd⟩
 . right;right;right;right;rw[cK] at hd;exact ⟨r,hr,bx g' g,hd⟩
lemma te {g:Fin 10} {f:(Fin 15->Bool)->Bool} (h:vl (E g f)):vl f:=by
 rcases h with h|h
 . left;rwa[bJ] at h
 . right;rwa[bt] at h
lemma mq {g:Fin 10} {f:(Fin 15->Bool)->Bool} (h:tf (E g f)):tf f:=by
 rcases h with h|h|⟨r,hr,g',hd⟩
 . left;rwa[bJ] at h
 . right;left;rwa[bt] at h
 . right;right;rw[cK] at hd;exact ⟨r,hr,bx g' g,hd⟩
lemma wc {g:Fin 10} {f:(Fin 15->Bool)->Bool} (h:T6 (E g f)):T6 f:=by
 rcases h with h|h
 . left;rwa[bJ] at h
 . right;rwa[bt] at h
lemma pd {q:RL} {f:(Fin 15->Bool)->Bool} (b:gw q)
  (c:dj q (R f) (O f)) (h:zq q=true):T2 f:=by
 rcases mI h with ⟨p,hpL,hdp⟩;rcases rj _ _ _ _ hpL with ⟨⟨r,hr,heq⟩,hglt⟩;set g:Fin 10:=⟨p.2,hglt⟩;have a:=(od r hr).1;rw[<- heq] at hdp;have d:=vW (jQ g r.1 a) b hdp c;exact ⟨r,hr,I g,pD g a d⟩
lemma fi {c b t k u v n m l:Nat} {f:(Fin 15->Bool)->Bool}
  (d:cu (c,b,t,k,u,v,n,m,l))
  (i:aW (c,b,t,k,u,v,n,m,l) (R f) (O f))
  (h:kj c b t k u v n m l=true):yT f:=by
 rcases iV h with ⟨p,hpL,hdp⟩;rcases rf _ _ _ _ hpL with ⟨⟨r,hr,heq⟩,hglt⟩;set g:Fin 10:=⟨p.2,hglt⟩;have a:=(rC r hr).1;rw[<- heq] at hdp;have j:=ep (cy g r.1 a) d hdp i;exact ⟨r,hr,I g,d4 g a j⟩
lemma fh {c b t k u v n m l:Nat} {f:(Fin 15->Bool)->Bool}
  (d:cu (c,b,t,k,u,v,n,m,l))
  (i:aW (c,b,t,k,u,v,n,m,l) (R f) (O f))
  (h:ki c b t k u v n m l=true):yS f:=by
 rcases iV h with ⟨p,hpL,hdp⟩;rcases rc _ _ _ _ hpL with ⟨⟨r,hr,heq⟩,hglt⟩;set g:Fin 10:=⟨p.2,hglt⟩;have a:=(rB r hr).1;rw[<- heq] at hdp;have j:=ep (cy g r.1 a) d hdp i;exact ⟨r,hr,I g,d4 g a j⟩
lemma xE {x:RS} {f:(Fin 15->Bool)->Bool} (a:cu x)
  (b:aW x (R f) (O f)) (h:Kc x=true):yT f:=
 fi a b h
lemma xD {x:RS} {f:(Fin 15->Bool)->Bool} (a:cu x)
  (b:aW x (R f) (O f)) (h:Kb x=true):yS f:=
 fh a b h
lemma m5 {k j:Nat} {f:(Fin 15->Bool)->Bool}
   (c:eV k) (b:fv j) (i:dI k (R f)) (d:e7 j (O f))
   (h:p9 k j=true):nc f:=by
 unfold p9 at h;simp only[bO,bA,bL] at h;have hsa:=cS c i;have hsb:=cR b d;rcases h with h1|((h2|⟨h3a,h3b⟩)|h4)
 . left;omega
 . right;left;omega
 . right;right;left;exact ⟨by omega,by omega⟩
 . rcases jY h4 with ⟨u,huL,hdu⟩;rcases iC _ _ _ _ huL with ⟨r,hr,g,rfl⟩;have a:=pH r hr;have l:=kL (q:=(k,j)) (ex g r a) ⟨c,b⟩ hdu ⟨i,d⟩;exact oR (oR (oR ⟨r,hr,I g,gv g a l⟩))
lemma m6 {p q:RS} {f h:(Fin 15->Bool)->Bool} {l:Nat}
   (c:cu p) (b:cu q)
   (w:aW p (R f) (O f)) (v:aW q (R h) (O h))
   (m:bo (R (fun y=>f y||h y))<=l)
   (d:jl p q l=true):ms (fun y=>f y||h y):=by
 unfold jl at d;dsimp only at d;simp only[bO,bA,bL] at d;have k:=gN c b w v;have i:=cR (mB:=O (fun y=>f y||h y)) k.1.2.1 (by rw[aJ];exact k.2.2.1);have n:=cS (mA:=R (fun y=>f y||h y)) k.1.1 (by rw[aX];exact k.2.1);rcases d with (h1|⟨h1a,h1b⟩)|(((h2|⟨h2a,h2b⟩)|⟨_,has⟩)|⟨_,hrs⟩)
 . left;exact lT h1 i
 . right;right;left;exact ⟨lT m h1a,lT h1b i⟩
 . right;left;exact lT n h2
 . right;right;left;exact ⟨lT n h2a,lT h2b i⟩
 . rcases gi has with ⟨r,hr,g,hdu⟩;have a:=mv r hr
   have t:=gS (p:=(p.1,p.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1))
     (q:=(q.1,q.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1))
     ⟨c.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.2.2.2.1⟩
     ⟨b.1,b.2.2.1,b.2.2.2.1,b.2.2.2.2.2.2.2.1⟩
     ⟨w.1,w.2.2.1,w.2.2.2.1⟩ ⟨v.1,v.2.2.1,v.2.2.2.1⟩
   have j:=j3 (mA:=R (fun y=>f y||h y)) (dA g r a) t.1 hdu (by rw[aX];exact t.2);exact oR (oR (oR (oL ⟨r,hr,I g,eU g a j⟩)))
 . rcases gh hrs with ⟨u,huL,hdu⟩;rcases fA _ _ _ _ huL with ⟨r,hr,g,rfl⟩;have a:=jx r hr
   have j:=ep (mA:=R (fun y=>f y||h y)) (mB:=O (fun y=>f y||h y))
     (cy g r a) k.1 hdu (by rw[aX,aJ];exact k.2)
   exact oR (oR (oR (oR ⟨r,hr,I g,d4 g a j⟩)))
lemma lh {p q:RS} {f h:(Fin 15->Bool)->Bool} {l:Nat}
   (c:cu p) (b:cu q)
   (w:aW p (R f) (O f)) (v:aW q (R h) (O h))
   (m:bo (R (fun y=>f y&&h y))<=l)
   (d:iH p q l=true):ms (fun y=>f y&&h y):=by
 unfold iH at d;dsimp only at d;simp only[bO,bA,bL] at d;have k:=ea c b w v;have i:=cR (mB:=O (fun y=>f y&&h y)) k.1.2.1 (by rw[aZ];exact k.2.2.1);have n:=cS (mA:=R (fun y=>f y&&h y)) k.1.1 (by rw[aF];exact k.2.1);rcases d with (h1|⟨h1a,h1b⟩)|(((h2|⟨h2a,h2b⟩)|⟨_,has⟩)|⟨_,hrs⟩)
 . left;exact lT h1 i
 . right;right;left;exact ⟨lT m h1a,lT h1b i⟩
 . right;left;exact lT n h2
 . right;right;left;exact ⟨lT n h2a,lT h2b i⟩
 . rcases gi has with ⟨r,hr,g,hdu⟩;have a:=mv r hr
   have t:=iF (p:=(p.1,p.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1))
     (q:=(q.1,q.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1))
     ⟨c.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.2.2.2.1⟩
     ⟨b.1,b.2.2.1,b.2.2.2.1,b.2.2.2.2.2.2.2.1⟩
     ⟨w.1,w.2.2.1,w.2.2.2.1⟩ ⟨v.1,v.2.2.1,v.2.2.2.1⟩
   have j:=j3 (mA:=R (fun y=>f y&&h y)) (dA g r a) t.1 hdu (by rw[aF];exact t.2);exact oR (oR (oR (oL ⟨r,hr,I g,eU g a j⟩)))
 . rcases gh hrs with ⟨u,huL,hdu⟩;rcases fA _ _ _ _ huL with ⟨r,hr,g,rfl⟩;have a:=jx r hr
   have j:=ep (mA:=R (fun y=>f y&&h y)) (mB:=O (fun y=>f y&&h y))
     (cy g r a) k.1 hdu (by rw[aF,aZ];exact k.2)
   exact oR (oR (oR (oR ⟨r,hr,I g,d4 g a j⟩)))
lemma zu {α:Type} (a b c d e f g h:List α):[a,b,c,d,e,f,g,h].flatten=a ++ b ++ c ++ d ++ e ++ f ++ g ++ h:=by simp[List.append_assoc]
lemma y7 {α:Type} (w v u t r n m l k j i h d c b a:List α) :
 [w,v,u,t,r,n,m,l,k,j,i,h,d,c,b,a].flatten =
 w ++ v ++ u ++ t ++ r ++ n ++ m ++ l ++ k ++ j ++ i ++ h ++ d ++ c ++ b ++ a:=by simp[List.append_assoc]
lemma xn {α:Type} {ok:α->α->Bool} (a b c d h i j l:List α)
   (h0:J ok a&&H ok [] a=true)
   (h1:J ok b&&H ok [a] b=true)
   (h2:J ok c&&H ok [a,b] c=true)
   (h3:J ok d&&H ok [a,b,c] d=true)
   (h4:J ok h&&H ok [a,b,c,d] h=true)
   (h5:J ok i&&H ok [a,b,c,d,h] i=true)
   (h6:J ok j&&H ok [a,b,c,d,h,i] j=true)
   (h7:J ok l&&H ok [a,b,c,d,h,i,j] l=true) :
   ∀ p ∈ a ++ b ++ c ++ d ++ h ++ i ++ j ++ l,
     ∀ q ∈ a ++ b ++ c ++ d ++ h ++ i ++ j ++ l,ok p q=true\/ok q p=true:=by
 have m:=jK (chunks:=[a,b,c,d,h,i,j,l]) (ok:=ok) (fun k=>by
   fin_cases k
   . exact bA _ _ |>.mp h0
   . exact bA _ _ |>.mp h1
   . exact bA _ _ |>.mp h2
   . exact bA _ _ |>.mp h3
   . exact bA _ _ |>.mp h4
   . exact bA _ _ |>.mp h5
   . exact bA _ _ |>.mp h6
   . exact bA _ _ |>.mp h7)
 rwa[zu] at m
lemma uJ {α:Type} {ok:α->α->Bool}
   (b d h i l m r t v w a c j n u x:List α)
   (h0:J ok b&&H ok [] b=true)
   (h1:J ok d&&H ok [b] d=true)
   (h2:J ok h&&H ok [b,d] h=true)
   (h3:J ok i&&H ok [b,d,h] i=true)
   (h4:J ok l&&H ok [b,d,h,i] l=true)
   (h5:J ok m&&H ok [b,d,h,i,l] m=true)
   (h6:J ok r&&H ok [b,d,h,i,l,m] r=true)
   (h7:J ok t&&H ok [b,d,h,i,l,m,r] t=true)
   (h8:J ok v&&H ok [b,d,h,i,l,m,r,t] v=true)
   (h9:J ok w&&H ok [b,d,h,i,l,m,r,t,v] w=true)
   (fT:J ok a&&H ok [b,d,h,i,l,m,r,t,v,w] a=true)
   (kG:J ok c&&H ok [b,d,h,i,l,m,r,t,v,w,a] c=true)
   (hH:J ok j&&H ok [b,d,h,i,l,m,r,t,v,w,a,c] j=true)
   (EI:J ok n&&H ok [b,d,h,i,l,m,r,t,v,w,a,c,j] n=true)
   (EF:J ok u&&H ok [b,d,h,i,l,m,r,t,v,w,a,c,j,n] u=true)
   (Cn:J ok x&&H ok [b,d,h,i,l,m,r,t,v,w,a,c,j,n,u] x=true) :
   ∀ p ∈ b ++ d ++ h ++ i ++ l ++ m ++ r ++ t ++ v ++ w ++ a ++ c ++ j ++ n ++ u ++ x,
     ∀ q ∈ b ++ d ++ h ++ i ++ l ++ m ++ r ++ t ++ v ++ w ++ a ++ c ++ j ++ n ++ u ++ x,
       ok p q=true\/ok q p=true:=by
 have y:=jK (chunks:=[b,d,h,i,l,m,r,t,v,w,a,c,j,n,u,x]) (ok:=ok) (fun k=>by
   fin_cases k
   . exact bA _ _ |>.mp h0
   . exact bA _ _ |>.mp h1
   . exact bA _ _ |>.mp h2
   . exact bA _ _ |>.mp h3
   . exact bA _ _ |>.mp h4
   . exact bA _ _ |>.mp h5
   . exact bA _ _ |>.mp h6
   . exact bA _ _ |>.mp h7
   . exact bA _ _ |>.mp h8
   . exact bA _ _ |>.mp h9
   . exact bA _ _ |>.mp fT
   . exact bA _ _ |>.mp kG
   . exact bA _ _ |>.mp hH
   . exact bA _ _ |>.mp EI
   . exact bA _ _ |>.mp EF
   . exact bA _ _ |>.mp Cn)
 rwa[y7] at y
lemma tO:∀ p ∈ iA,∀ q ∈ iA,ck p q=true\/ck q p=true:=
 xn hG ik j9 jP kY mD pE rA
  cert_d1_c0 cert_d1_c1 cert_d1_c2 cert_d1_c3 cert_d1_c4 cert_d1_c5 cert_d1_c6 cert_d1_c7
lemma tx:∀ p ∈ wd,∀ q ∈ wd,bc p q=true\/bc q p=true:=
 uJ dc di dz dL ev eT fJ gj
  hn ij hD iz js kt mu pC
  cert_p2_c0 cert_p2_c1 cert_p2_c2 cert_p2_c3 cert_p2_c4 cert_p2_c5 cert_p2_c6 cert_p2_c7
  cert_p2_c8 cert_p2_c9 cert_p2_c10 cert_p2_c11 cert_p2_c12 cert_p2_c13 cert_p2_c14 cert_p2_c15
lemma tp:∀ p ∈ j8,∀ q ∈ j8,cG p q=true\/cG q p=true:=
 xn jr k6 kX ml oa qe td wa
  cert_u3_c0 cert_u3_c1 cert_u3_c2 cert_u3_c3 cert_u3_c4 cert_u3_c5 cert_u3_c6 cert_u3_c7
lemma ti:∀ p ∈ j7,∀ q ∈ j7,ba p q=true\/ba q p=true:=
 uJ eu eO fq fU gu gZ i6 iM
  jq k5 j6 jN kW mC pz rz
  cert_v3_c0 cert_v3_c1 cert_v3_c2 cert_v3_c3 cert_v3_c4 cert_v3_c5 cert_v3_c6 cert_v3_c7
  cert_v3_c8 cert_v3_c9 cert_v3_c10 cert_v3_c11 cert_v3_c12 cert_v3_c13 cert_v3_c14 cert_v3_c15
lemma Hz (i:Fin 15):T0 (fun x=>x i):=⟨i,rfl⟩
lemma CL {f h:(Fin 15->Bool)->Bool} (d:T0 f) (c:T0 h) :
   T1 (fun y=>f y&&h y)/\T1 (fun y=>f y||h y):=by
 rcases d with ⟨i,rfl⟩;rcases c with ⟨j,rfl⟩;have b:(⟨i.val % 15,nM _ (by decide)⟩:Fin 15)=i:=fE (nQ i.isLt);have a:(⟨j.val % 15,nM _ (by decide)⟩:Fin 15)=j:=fE (nQ j.isLt);refine ⟨⟨(i.val,j.val,false),⟨i.isLt,j.isLt⟩,?_⟩,⟨(i.val,j.val,true),⟨i.isLt,j.isLt⟩,?_⟩⟩
 . funext x;unfold aN;simp[b,a]
 . funext x;unfold aN;simp[b,a]
lemma pm:∀ (sp sq g:Fin 10),
 (nE sp.val 0||nB 5 sp.val)=true->
 (nE sq.val 0||nB 5 sq.val)=true->
 dW (fun r=>Nat.blt r 10&&
  (nE r g.val||nE r (bx sp g).val||
   nE r (bx g sq).val||nE r (bx sp (bx g sq)).val))
  (eJ sp.val sq.val)=true:=by decide +kernel
lemma iJ {P Q:Fin 10->Prop} {h c:Nat} (k j:Fin 10)
   (v:h=0\/∃ hlt:h<10,5<=h/\∀ g,P g->P (bx ⟨h,hlt⟩ g))
   (m:c=0\/∃ hlt:c<10,5<=c/\∀ g,Q g->Q (bx ⟨c,hlt⟩ g))
   (x:P k) (w:Q j) :
   ∃ gp' gq':Fin 10,P gp'/\Q gq'/\(bx gp' (I gq')).val ∈ eJ h c:=by
 have b:h<10:=by rcases v with rfl|⟨hlt,_⟩;decide;exact hlt
 have a:c<10:=by rcases m with rfl|⟨hlt,_⟩;decide;exact hlt
 have n:(nE h 0||nB 5 h)=true:=by
   rcases v with rfl|⟨_,h5,_⟩
   . rfl
   . simp only[bO,bL];exact oR h5
 have l:(nE c 0||nB 5 c)=true:=by
   rcases m with rfl|⟨_,h5,_⟩
   . rfl
   . simp only[bO,bL];exact oR h5
 have i:c=0\/5<=c:=by rcases m with rfl|⟨_,h5,_⟩;exact oL rfl;exact oR h5
 have u:P (bx ⟨h,b⟩ k):=by
   rcases v with rfl|⟨_,_,hf⟩
   . rw[dO];exact x
   . exact hf k x
 have t:Q (bx ⟨c,a⟩ j):=by
   rcases m with rfl|⟨_,_,hf⟩
   . rw[dO];exact w
   . exact hf j w
 set g:=bx k (I j);rcases cC (pm ⟨h,b⟩ ⟨c,a⟩ g n l) with ⟨r,hr,hchk⟩;simp only[bA,bO,nG] at hchk;rcases hchk.2 with ((heq|heq)|heq)|heq
 . exact ⟨k,j,x,w,by rw[<- bQ heq];exact hr⟩
 . have d:=fQ k j ⟨h,b⟩ ⟨0,by decide⟩ (oL rfl)
   rw[dO,p7] at d
   exact ⟨bx ⟨h,b⟩ k,j,u,w,by rw[d,<-bQ heq];exact hr⟩
 . have d:=fQ k j ⟨0,by decide⟩ ⟨c,a⟩ i
   rw[dO,dO] at d
   exact ⟨k,bx ⟨c,a⟩ j,x,t,by rw[d,<-bQ heq];exact hr⟩
 . have d:=fQ k j ⟨h,b⟩ ⟨c,a⟩ i
   exact ⟨bx ⟨h,b⟩ k,bx ⟨c,a⟩ j,u,t,by rw[d,<-bQ heq];exact hr⟩
lemma ku {r:cT × Nat} (a:r ∈ iA) :
   og r.1/\(r.2=0\/(5<=r.2/\r.2<10/\aN (gY r.2 r.1)=aN r.1)):=by
 have h:=aC cert_d1_cover.1 r a;simp only[bA,bO,nG,bL] at h;refine ⟨⟨h.1.1,h.1.2⟩,?_⟩;rcases h.2 with h0|⟨⟨h5,fT⟩,heq⟩
 . exact oL (bQ h0)
 . exact oR ⟨h5,fT,qP heq⟩
lemma n8 {p:cT} (a:og p) :
  ∃ r ∈ iA,∃ g:Fin 10,aN (gY g.val r.1)=aN p:=by
 have h:=cert_d1_cover.2 ⟨p.1,a.1⟩ ⟨p.2.1,a.2⟩ p.2.2;rcases cC h with ⟨r,hr,hg1⟩;rcases ps hg1 with ⟨g,heq⟩;exact ⟨r,hr,g,qP heq⟩
lemma nf {p q:cT × Nat} {f h:(Fin 15->Bool)->Bool}
   (v:p ∈ iA) (u:q ∈ iA) (c m:Fin 10)
   (k:E c f=aN p.1) (t:E m h=aN q.1)
   (j:ck p q=true) :
   T2 (fun y=>f y&&h y)/\T2 (fun y=>f y||h y):=by
 rcases ku v with ⟨hwp,hsp⟩;rcases ku u with ⟨hwq,hsq⟩
 have hsp':p.2=0\/∃ hlt:p.2<10,5<=p.2/\∀ g:Fin 10,E g f=aN p.1->E (bx ⟨p.2,hlt⟩ g) f=aN p.1:=by
   rcases hsp with h0|⟨h5,hlt,heq⟩
   . exact oL h0
   . exact oR ⟨hlt,h5,fun g hg=>by rw[<- cK,hg,<-g6 ⟨p.2,hlt⟩ hwp,heq]⟩
 have hsq':q.2=0\/∃ hlt:q.2<10,5<=q.2/\∀ g:Fin 10,E g h=aN q.1->E (bx ⟨q.2,hlt⟩ g) h=aN q.1:=by
   rcases hsq with h0|⟨h5,hlt,heq⟩
   . exact oL h0
   . exact oR ⟨hlt,h5,fun g hg=>by rw[<- cK,hg,<-g6 ⟨q.2,hlt⟩ hwq,heq]⟩
 rcases iJ c m hsp' hsq' k t with ⟨gp',gq',dp',dq',hg0_mem⟩;set d:=bx gp' (I gq')
 have a:E gp' h=aN (gY d.val q.1):=by
   rw[g6 d hwq,<-dq',dy]
 have i:og (gY d.val q.1):=we d hwq;unfold ck at j;dsimp only at j;have b:=bA _ _ |>.mp (aC j d.val hg0_mem);rw[yo hwp,yn hwp,yo i,yn i] at b;refine ⟨pA (g:=gp') ?_,pA (g:=gp') ?_⟩
 . have r:land (R (aN p.1)) (R (aN (gY d.val q.1)))=R (E gp' (fun y=>f y&&h y)):=by
     rw[aM,dp',a,aF];rfl
   have n:land (O (aN p.1)) (O (aN (gY d.val q.1)))=O (E gp' (fun y=>f y&&h y)):=by
     rw[aM,dp',a,aZ];rfl
   rw[r,n] at b;have l:=mS (uL (E gp' (fun y=>f y&&h y))) (uK (E gp' (fun y=>f y&&h y)));exact pd l.1 l.2 b.1
 . have r:lor (R (aN p.1)) (R (aN (gY d.val q.1)))=R (E gp' (fun y=>f y||h y)):=by
     rw[aU,dp',a,aX];rfl
   have n:lor (O (aN p.1)) (O (aN (gY d.val q.1)))=O (E gp' (fun y=>f y||h y)):=by
     rw[aU,dp',a,aJ];rfl
   rw[r,n] at b;have l:=mS (uL (E gp' (fun y=>f y||h y))) (uK (E gp' (fun y=>f y||h y)));exact pd l.1 l.2 b.2
lemma CK {f h:(Fin 15->Bool)->Bool} (j:T1 f) (i:T1 h) :
   T2 (fun y=>f y&&h y)/\T2 (fun y=>f y||h y):=by
 rcases j with ⟨p,hwp,rfl⟩;rcases i with ⟨q,hwq,rfl⟩;rcases n8 hwp with ⟨rp,hrp,gp,heqp⟩;rcases n8 hwq with ⟨rq,hrq,gq,heqq⟩
 have c:E (I gp) (aN p)=aN rp.1:=by
   rw[<- heqp,g6 gp (ku hrp).1,mi]
 have b:E (I gq) (aN q)=aN rq.1:=by
   rw[<- heqq,g6 gq (ku hrq).1,mi]
 rcases tO rp hrp rq hrq with hok|hok
 . exact nf hrp hrq (I gp) (I gq) c b hok
 . have a:=nf hrq hrp (I gq) (I gp) b c hok
   have k:(fun y=>aN q y&&aN p y)=(fun y=>aN p y&&aN q y):=by funext y;exact bY _ _
   have d:(fun y=>aN q y||aN p y)=(fun y=>aN p y||aN q y):=by funext y;exact bP _ _
   rw[k,d] at a;exact a
lemma tN {p q:RL × Nat} {f h:(Fin 15->Bool)->Bool}
  (d:gw p.1/\(p.2=0\/(5<=p.2/\p.2<10/\d7 p.2 p.1=p.1)))
  (c:gw q.1/\(q.2=0\/(5<=q.2/\q.2<10/\d7 q.2 q.1=q.1)))
  (b a:Fin 10)
  (j:dj p.1 (R (E b f)) (O (E b f)))
  (i:dj q.1 (R (E a h)) (O (E a h))) :
  ∃ gp' gq':Fin 10,dj p.1 (R (E gp' f)) (O (E gp' f))/\
   dj q.1 (R (E gq' h)) (O (E gq' h))/\(bx gp' (I gq')).val ∈ eJ p.2 q.2:=
 iJ b a
  (d.2.elim oL fun ⟨h5,hlt,heq⟩=>oR ⟨hlt,h5,fun g hg=>by have h1:=hE ⟨p.2,hlt⟩ d.1 hg;rwa[heq,cK] at h1⟩)
  (c.2.elim oL fun ⟨h5,hlt,heq⟩=>oR ⟨hlt,h5,fun g hg=>by have h1:=hE ⟨q.2,hlt⟩ c.1 hg;rwa[heq,cK] at h1⟩)
  j i
lemma n7 {p q:RS × Nat} {f h:(Fin 15->Bool)->Bool}
  (d:cu p.1/\(p.2=0\/(5<=p.2/\p.2<10/\ay p.2 p.1=p.1)))
  (c:cu q.1/\(q.2=0\/(5<=q.2/\q.2<10/\ay q.2 q.1=q.1)))
  (b a:Fin 10)
  (j:aW p.1 (R (E b f)) (O (E b f)))
  (i:aW q.1 (R (E a h)) (O (E a h))) :
  ∃ gp' gq':Fin 10,aW p.1 (R (E gp' f)) (O (E gp' f))/\
   aW q.1 (R (E gq' h)) (O (E gq' h))/\(bx gp' (I gq')).val ∈ eJ p.2 q.2:=
 iJ b a
  (d.2.elim oL fun ⟨h5,hlt,heq⟩=>oR ⟨hlt,h5,fun g hg=>by have h1:=cX ⟨p.2,hlt⟩ d.1 hg;rwa[heq,cK] at h1⟩)
  (c.2.elim oL fun ⟨h5,hlt,heq⟩=>oR ⟨hlt,h5,fun g hg=>by have h1:=cX ⟨q.2,hlt⟩ c.1 hg;rwa[heq,cK] at h1⟩)
  j i
lemma na {p q:RL × Nat} {f h:(Fin 15->Bool)->Bool}
   (hp:p ∈ wd) (hq:q ∈ wd) (a W:Fin 10)
   (M:dj p.1 (R (E a f)) (O (E a f)))
   (dq:dj q.1 (R (E W h)) (O (E W h)))
   (T:bc p q=true) :
   T3 (fun y=>f y&&h y)/\T3 (fun y=>f y||h y):=by
 have j:=(od p hp).1;have P:=(od q hq).1;rcases tN (od p hp) (od q hq) a W M dq with ⟨gp',gq',dp',dq',hg0_mem⟩;set L:=bx gp' (I gq')
 have n:dj (d7 L.val q.1) (R (E gp' h)) (O (E gp' h)):=by
   have:=hE L P dq';rwa[dy] at this
 have b:=jQ L q.1 P;set N:=ay L.val q.1.1;have w:(N,bR L.val q.1.2)=d7 L.val q.1:=rfl;unfold bc at T;have hg:=aC T L.val hg0_mem;dsimp only at hg;simp only[bA,bO] at hg
 have x:T3 (fun y=>f y||h y):=by
   have r:=km j.1 b.1 dp'.1 n.1
   have C:aW (o2 p.1.1 N) (R (E gp' (fun y=>f y||h y))) (O (E gp' (fun y=>f y||h y))):=by
     rw[aU,aX,aJ];exact r.2
   have k:=gN j.1 b.1 dp'.1 n.1
   have z:aW (lE p.1.1 N) (R (E gp' (fun y=>f y||h y))) (O (E gp' (fun y=>f y||h y))):=by
     rw[aU,aX,aJ];exact k.2
   have i:=fun hu=>ga (fi r.1 C hu);have d:=fun hv=>g9 (fh r.1 C hv);have m:=fun hu=>ga (fi k.1 z hu);have l:=fun hv=>g9 (fh k.1 z hv);rcases hg.1 with ⟨hu,hv⟩|⟨hu|hu,hv|hv⟩
   . exact ⟨i hu,d hv⟩
   . exact ⟨i hu,d hv⟩
   . exact ⟨i hu,l hv⟩
   . exact ⟨m hu,d hv⟩
   . exact ⟨m hu,l hv⟩
 have v:T3 (fun y=>f y&&h y):=by
   have u:=jH j.1 b.1 dp'.1 n.1
   have K:aW (m9 p.1.1 N) (R (E gp' (fun y=>f y&&h y))) (O (E gp' (fun y=>f y&&h y))):=by
     rw[aM,aF,aZ];exact u.2
   have c:=ea j.1 b.1 dp'.1 n.1
   have F:aW (kx p.1.1 N) (R (E gp' (fun y=>f y&&h y))) (O (E gp' (fun y=>f y&&h y))):=by
     rw[aM,aF,aZ];exact c.2
   have i:=fun hu=>ga (fi u.1 K hu);have d:=fun hv=>g9 (fh u.1 K hv);have m:=fun hu=>ga (fi c.1 F hu);have l:=fun hv=>g9 (fh c.1 F hv)
   have Q:∀ t ∈ kJ p.1 (N,bR L.val q.1.2),i5 (R (E gp' f)) (O (E gp' f)) (R (E gp' h)) (O (E gp' h)) t:=by
     rw[w];exact q4 j b dp' n
   have a2:∀ hu,yT (fun y=>f y&&h y):=fun hu=>by
     rcases iw _ Q _ c.1 c.2 hu with ⟨xu,hwxu,hdxu,hinu⟩;exact ga (xE hwxu (by rw[aM,aF,aZ];exact hdxu) hinu)
   have a1:∀ hv,yS (fun y=>f y&&h y):=fun hv=>by
     rcases iw _ Q _ c.1 c.2 hv with ⟨xv,hwxv,hdxv,hinv⟩;exact g9 (xD hwxv (by rw[aM,aF,aZ];exact hdxv) hinv)
   rcases hg.2 with ⟨hu,hv⟩|(⟨hu,hv⟩|⟨hu,hv⟩)
   . exact ⟨i hu,d hv⟩
   . exact ⟨hu.elim i m,hv.elim d l⟩
   . exact ⟨hu.elim (fun h'=>h'.elim i m) a2,hv.elim (fun h'=>h'.elim d l) a1⟩
 exact ⟨v,x⟩
lemma CJ {f h:(Fin 15->Bool)->Bool} (d:T2 f) (c:T2 h) :
   T3 (fun y=>f y&&h y)/\T3 (fun y=>f y||h y):=by
 rcases d with ⟨p,hp,gp,dp⟩;rcases c with ⟨q,hq,gq,dq⟩;rcases tx p hp q hq with hok|hok
 . exact na hp hq gp gq dp dq hok
 . have a:=na hq hp gq gp dq dp hok
   have i:(fun y=>h y&&f y)=(fun y=>f y&&h y):=by funext y;exact bY _ _
   have b:(fun y=>h y||f y)=(fun y=>f y||h y):=by funext y;exact bP _ _
   rw[i,b] at a;exact a
lemma mn {p q:RS × Nat} {f h:(Fin 15->Bool)->Bool}
   (T:p ∈ j8) (Q:q ∈ j8) (c N:Fin 10)
   (l:aW p.1 (R (E c f)) (O (E c f)))
   (P:aW q.1 (R (E N h)) (O (E N h)))
   (t:cG p q=true) :
   nc (fun y=>f y&&h y)/\nc (fun y=>f y||h y):=by
 have b:=(rC p T).1;have m:=(rC q Q).1;rcases n7 (rC p T) (rC q Q) c N l P with ⟨gp',gq',dp',dq',hg0_mem⟩;set i:=bx gp' (I gq')
 have d:aW (ay i.val q.1) (R (E gp' h)) (O (E gp' h)):=by
   have:=cX i m dq';rwa[dy] at this
 have a:=cy i q.1 m
 have hsap:bo (R (E gp' f))<=p.1.1:=by rw[b.2.2.2.2.2.2.2.1];exact cS b.1 dp'.1
 have hsbp:p.1.2.1<=bv (O (E gp' f)):=by rw[b.2.2.2.2.2.2.2.2];exact cR b.2.1 dp'.2.1
 have hsaq:bo (R (E gp' h))<=q.1.1:=by
   have:=cS m.1 dq'.1;rw[bJ] at this
   rw[bJ,m.2.2.2.2.2.2.2.1];exact this
 have hsbq:q.1.2.1<=bv (O (E gp' h)):=by
   have:=cR m.2.1 dq'.2.1;rw[bt] at this
   rw[bt,m.2.2.2.2.2.2.2.2];exact this
 have z:bH i.val q.1.2.2.1=(ay i.val q.1).2.2.1:=by unfold ay bH;cases nB i.val 4 <;> rfl
 have x:cx i.val q.1.2.2.2.1=(ay i.val q.1).2.2.2.1:=by unfold ay cx;cases nB i.val 4 <;> rfl
 unfold cG at t;dsimp only at t;simp only[bA,bO,bL] at t;refine ⟨mo (g:=gp') ?_,mo (g:=gp') ?_⟩
 . have M:=fb (R (E gp' f)) (R (E gp' h));have L:=dN (O (E gp' f)) (O (E gp' h));rcases t.2 with (((h1|h2)|h3)|⟨h4a|h4a,h4b⟩)|hall
   . left;rw[aM,aZ];omega
   . right;left;rw[aM,aF];omega
   . right;left;rw[aM,aF];omega
   . right;right;left;rw[aM,aF,aZ];exact ⟨by omega,by omega⟩
   . right;right;left;rw[aM,aF,aZ];exact ⟨by omega,by omega⟩
   . have F:=aC hall i.val hg0_mem;rw[z,x] at F;simp only[bO,bA,bL] at F
     have k:bo (R (E gp' (fun y=>f y&&h y)))<=i9 p.1.2.2.1 (ay i.val q.1).2.2.1:=by
       rw[aM,aF];exact fM b.1 a.1 dp'.1 d.1
     have j:i8 p.1.2.2.2.1 (ay i.val q.1).2.2.2.1<=bv (O (E gp' (fun y=>f y&&h y))):=by
       rw[aM,aZ];exact fL b.2.1 a.2.1 dp'.2.1 d.2.1
     rcases F with ha1|(((hb1|⟨ha2,hb2⟩)|hp1)|ht1)
     . right;left;exact lT k ha1
     . left;exact lT hb1 j
     . right;right;left;exact ⟨lT k ha2,lT hb2 j⟩
     . have w:=hY b.1 a.1 dp'.1 d.1;have v:=fG b.2.1 a.2.1 dp'.2.1 d.2.1;rcases jY hp1 with ⟨u,huL,hdu⟩;rcases iC _ _ _ _ huL with ⟨r,hr,g,rfl⟩;have n:=pH r hr
       have K:=kL (q:=(eo p.1.2.2.1 (ay i.val q.1).2.2.1,dF p.1.2.2.2.1 (ay i.val q.1).2.2.2.1))
         (mA:=R (E gp' (fun y=>f y&&h y))) (mB:=O (E gp' (fun y=>f y&&h y)))
         (ex g r n) ⟨w.1,v.1⟩ hdu ⟨by rw[aM,aF];exact w.2,by rw[aM,aZ];exact v.2⟩
       exact oR (oR (oR ⟨r,hr,I g,gv g n K⟩))
     . have C:=ea b a dp' d;exact m5 C.1.1 C.1.2.1 (by rw[aM,aF];exact C.2.1) (by rw[aM,aZ];exact C.2.2.1) ht1
 . have M:=fY (R (E gp' f)) (R (E gp' h));have L:=dC (O (E gp' f)) (O (E gp' h));rcases t.1 with (((h1|h2)|h3)|⟨h4a,h4b|h4b⟩)|hall
   . left;rw[aU,aJ];omega
   . left;rw[aU,aJ];omega
   . right;left;rw[aU,aX];omega
   . right;right;left;rw[aU,aX,aJ];exact ⟨by omega,by omega⟩
   . right;right;left;rw[aU,aX,aJ];exact ⟨by omega,by omega⟩
   . have F:=aC hall i.val hg0_mem;rw[z,x] at F;simp only[bO,bA,bL] at F
     have k:bo (R (E gp' (fun y=>f y||h y)))<=gP p.1.2.2.1 (ay i.val q.1).2.2.1:=by
       rw[aU,aX];exact eb b.1 a.1 dp'.1 d.1
     have j:iW p.1.2.2.2.1 (ay i.val q.1).2.2.2.1<=bv (O (E gp' (fun y=>f y||h y))):=by
       rw[aU,aJ];exact gm b.2.1 a.2.1 dp'.2.1 d.2.1
     rcases F with hb1|(((ha1|⟨ha2,hb2⟩)|hp1)|ht1)
     . left;exact lT hb1 j
     . right;left;exact lT k ha1
     . right;right;left;exact ⟨lT k ha2,lT hb2 j⟩
     . have w:=iI b.1 a.1 dp'.1 d.1;have v:=gf b.2.1 a.2.1 dp'.2.1 d.2.1;rcases jY hp1 with ⟨u,huL,hdu⟩;rcases iC _ _ _ _ huL with ⟨r,hr,g,rfl⟩;have n:=pH r hr
       have K:=kL (q:=(fF p.1.2.2.1 (ay i.val q.1).2.2.1,eI p.1.2.2.2.1 (ay i.val q.1).2.2.2.1))
         (mA:=R (E gp' (fun y=>f y||h y))) (mB:=O (E gp' (fun y=>f y||h y)))
         (ex g r n) ⟨w.1,v.1⟩ hdu ⟨by rw[aU,aX];exact w.2,by rw[aU,aJ];exact v.2⟩
       exact oR (oR (oR ⟨r,hr,I g,gv g n K⟩))
     . have C:=gN b a dp' d;exact m5 C.1.1 C.1.2.1 (by rw[aU,aX];exact C.2.1) (by rw[aU,aJ];exact C.2.2.1) ht1
lemma zH {f h:(Fin 15->Bool)->Bool} (d:yT f) (c:yT h) :
   nc (fun y=>f y&&h y)/\nc (fun y=>f y||h y):=by
 rcases d with ⟨p,hp,gp,dp⟩;rcases c with ⟨q,hq,gq,dq⟩;rcases tp p hp q hq with hok|hok
 . exact mn hp hq gp gq dp dq hok
 . have a:=mn hq hp gq gp dq dp hok
   have i:(fun y=>h y&&f y)=(fun y=>f y&&h y):=by funext y;exact bY _ _
   have b:(fun y=>h y||f y)=(fun y=>f y||h y):=by funext y;exact bP _ _
   rw[i,b] at a;exact a
lemma mm {p q:RS × Nat} {f h:(Fin 15->Bool)->Bool}
   (Q:p ∈ j7) (P:q ∈ j7) (a M:Fin 10)
   (m:aW p.1 (R (E a f)) (O (E a f)))
   (N:aW q.1 (R (E M h)) (O (E M h)))
   (t:ba p q=true) :
   ms (fun y=>f y&&h y)/\ms (fun y=>f y||h y):=by
 have c:=(rB p Q).1;have l:=(rB q P).1;rcases n7 (rB p Q) (rB q P) a M m N with ⟨gp',gq',dp',dq',hg0_mem⟩;set k:=bx gp' (I gq')
 have j:aW (ay k.val q.1) (R (E gp' h)) (O (E gp' h)):=by
   have:=cX k l dq';rwa[dy] at this
 have b:=cy k q.1 l
 have hsap:bo (R (E gp' f))<=p.1.1:=by rw[c.2.2.2.2.2.2.2.1];exact cS c.1 dp'.1
 have hsbp:p.1.2.1<=bv (O (E gp' f)):=by rw[c.2.2.2.2.2.2.2.2];exact cR c.2.1 dp'.2.1
 have hsaq:bo (R (E gp' h))<=q.1.1:=by
   have:=cS l.1 dq'.1;rw[bJ] at this
   rw[bJ,l.2.2.2.2.2.2.2.1];exact this
 have hsbq:q.1.2.1<=bv (O (E gp' h)):=by
   have:=cR l.2.1 dq'.2.1;rw[bt] at this
   rw[bt,l.2.2.2.2.2.2.2.2];exact this
 have w:bH k.val q.1.2.2.1=(ay k.val q.1).2.2.1:=by unfold ay bH;cases nB k.val 4 <;> rfl
 have v:cx k.val q.1.2.2.2.1=(ay k.val q.1).2.2.2.1:=by unfold ay cx;cases nB k.val 4 <;> rfl
 unfold ba at t;dsimp only at t;simp only[bA,bO,bL] at t;refine ⟨mr (g:=gp') ?_,mr (g:=gp') ?_⟩
 . have F:=fb (R (E gp' f)) (R (E gp' h));have C:=dN (O (E gp' f)) (O (E gp' h));rcases t.2 with (((h1|h2)|h3)|⟨h4a|h4a,h4b⟩)|hall
   . left;rw[aM,aZ];omega
   . right;left;rw[aM,aF];omega
   . right;left;rw[aM,aF];omega
   . right;right;left;rw[aM,aF,aZ];exact ⟨by omega,by omega⟩
   . right;right;left;rw[aM,aF,aZ];exact ⟨by omega,by omega⟩
   . have x:=aC hall k.val hg0_mem;rw[w,v] at x;simp only[bO,bA,bL] at x
     have d:bo (R (E gp' (fun y=>f y&&h y)))<=i9 p.1.2.2.1 (ay k.val q.1).2.2.1:=by
       rw[aM,aF];exact fM c.1 b.1 dp'.1 j.1
     have i:i8 p.1.2.2.2.1 (ay k.val q.1).2.2.2.1<=bv (O (E gp' (fun y=>f y&&h y))):=by
       rw[aM,aZ];exact fL c.2.1 b.2.1 dp'.2.1 j.2.1
     rcases x with ha1|((hb1|⟨ha2,hb2⟩)|(⟨_,hhf⟩|ht))
     . right;left;exact lT d ha1
     . left;exact lT hb1 i
     . right;right;left;exact ⟨lT d ha2,lT hb2 i⟩
     . have L:=jH c b dp' j;rcases gh hhf with ⟨u,huL,hdu⟩;rcases fA _ _ _ _ huL with ⟨r,hr,g,rfl⟩;have n:=jx r hr
       have z:=ep (mA:=R (E gp' (fun y=>f y&&h y))) (mB:=O (E gp' (fun y=>f y&&h y)))
         (cy g r n) L.1 hdu (by rw[aM,aF,aZ];exact L.2)
       exact oR (oR (oR (oR ⟨r,hr,I g,d4 g n z⟩)))
     . rw[aM];exact lh c b dp' j (by rwa[aM] at d) ht
 . have F:=fY (R (E gp' f)) (R (E gp' h));have C:=dC (O (E gp' f)) (O (E gp' h));rcases t.1 with (((h1|h2)|h3)|⟨h4a,h4b|h4b⟩)|hall
   . left;rw[aU,aJ];omega
   . left;rw[aU,aJ];omega
   . right;left;rw[aU,aX];omega
   . right;right;left;rw[aU,aX,aJ];exact ⟨by omega,by omega⟩
   . right;right;left;rw[aU,aX,aJ];exact ⟨by omega,by omega⟩
   . have x:=aC hall k.val hg0_mem;rw[w,v] at x;simp only[bO,bA,bL] at x
     have d:bo (R (E gp' (fun y=>f y||h y)))<=gP p.1.2.2.1 (ay k.val q.1).2.2.1:=by
       rw[aU,aX];exact eb c.1 b.1 dp'.1 j.1
     have i:iW p.1.2.2.2.1 (ay k.val q.1).2.2.2.1<=bv (O (E gp' (fun y=>f y||h y))):=by
       rw[aU,aJ];exact gm c.2.1 b.2.1 dp'.2.1 j.2.1
     rcases x with hb1|((hb2|⟨hb2a,hb2b⟩)|(⟨_,hhf⟩|ht))
     . left;exact lT hb1 i
     . right;left;exact lT d hb2
     . right;right;left;exact ⟨lT d hb2a,lT hb2b i⟩
     . have K:=km c b dp' j;rcases gh hhf with ⟨u,huL,hdu⟩;rcases fA _ _ _ _ huL with ⟨r,hr,g,rfl⟩;have n:=jx r hr
       have z:=ep (mA:=R (E gp' (fun y=>f y||h y))) (mB:=O (E gp' (fun y=>f y||h y)))
         (cy g r n) K.1 hdu (by rw[aU,aX,aJ];exact K.2)
       exact oR (oR (oR (oR ⟨r,hr,I g,d4 g n z⟩)))
     . rw[aU];exact m6 c b dp' j (by rwa[aU] at d) ht
lemma zG {f h:(Fin 15->Bool)->Bool} (d:yS f) (c:yS h) :
   ms (fun y=>f y&&h y)/\ms (fun y=>f y||h y):=by
 rcases d with ⟨p,hp,gp,dp⟩;rcases c with ⟨q,hq,gq,dq⟩;rcases ti p hp q hq with hok|hok
 . exact mm hp hq gp gq dp dq hok
 . have a:=mm hq hp gq gp dq dp hok
   have i:(fun y=>h y&&f y)=(fun y=>f y&&h y):=by funext y;exact bY _ _
   have b:(fun y=>h y||f y)=(fun y=>f y||h y):=by funext y;exact bP _ _
   rw[i,b] at a;exact a
lemma eR {f:(Fin 15->Bool)->Bool} {r:iN} (a:r ∈ fr) {g:Fin 10}
  (b:ju r (R (E g f)) (O (E g f))):bo (R f)<=34:=by
 have h1:=cS (pH r a).1 b.1;rw[bJ] at h1;have h2:=Cw r a;omega
lemma nb {p q:iN} {f h:(Fin 15->Bool)->Bool}
   (w:p ∈ fr) (v:q ∈ fr) (a n:Fin 10)
   (r:ju p (R (E a f)) (O (E a f)))
   (u:ju q (R (E n h)) (O (E n h)))
   (i:vF p q=true):vl (fun y=>f y||h y):=by
 have d:=pH p w;have c:=pH q v;set l:=bx a (I n)
 have k:ju (dV l.val q) (R (E a h)) (O (E a h)):=by
   have:=iO l c u;rwa[dy] at this
 have b:=ex l q c;apply te (g:=a);unfold vF at i;simp only[bO,bL] at i;rcases i with (h1|h1)|hall
 . right;rw[aU,aJ];have hbp:=cR d.2 r.2;have m:=dC (O (E a f)) (O (E a h));omega
 . right;rw[aU,aJ];have j:=cR c.2 u.2;rw[bt] at j
   have hbq':bG q.2<=bv (O (E a h)):=by rw[bt];exact j
   have m:=dC (O (E a f)) (O (E a h));omega
 . have t:=j5 hall l;simp only[bO,bL] at t;rcases t with ha|hb
   . left;rw[aU,aX];exact lT (eb d.1 b.1 r.1 k.1) ha
   . right;rw[aU,aJ];exact lT hb (gm d.2 b.2 r.2 k.2)
lemma yU {f h:(Fin 15->Bool)->Bool} (b:nc f) (a:nc h) :
   vl (fun y=>f y&&h y)/\vl (fun y=>f y||h y):=by
 have ha_and:=fb (R f) (R h);have hb_and:=dN (O f) (O h);have ha_or:=fY (R f) (R h);have hb_or:=dC (O f) (O h);refine ⟨?_,?_⟩
 . rcases b with b|b|⟨hfa,_⟩|⟨p,hp,gp,dp⟩
   . rcases a with a|a|⟨hha,_⟩|⟨q,hq,gq,dq⟩
     . right;rw[aZ];omega
     . left;rw[aF];omega
     . left;rw[aF];omega
     . left;rw[aF];have:=eR hq dq;omega
   . left;rw[aF];omega
   . left;rw[aF];omega
   . left;rw[aF];have:=eR hp dp;omega
 . rcases b with b|b|⟨_,hfb⟩|⟨p,hp,gp,dp⟩
   . right;rw[aJ];omega
   . rcases a with a|a|⟨_,hhb⟩|⟨q,hq,gq,dq⟩
     . right;rw[aJ];omega
     . left;rw[aX];omega
     . right;rw[aJ];omega
     . left;rw[aX];have:=eR hq dq;omega
   . right;rw[aJ];omega
   . rcases a with a|a|⟨_,hhb⟩|⟨q,hq,gq,dq⟩
     . right;rw[aJ];omega
     . left;rw[aX];have:=eR hp dp;omega
     . right;rw[aJ];omega
     . rcases dU cert_u4 p hp q hq with hok|hok
       . exact nb hp hq gp gq dp dq hok
       . have c:=nb hq hp gq gp dq dp hok
         have d:(fun y=>h y||f y)=(fun y=>f y||h y):=by funext y;exact bP _ _
         rwa[d] at c
lemma ft {f:(Fin 15->Bool)->Bool} {r:AS} (a:r ∈ dY) {g:Fin 10}
  (b:dk r (R (E g f))):bo (R f)<=12:=by
 have h1:=cS (mv r a).1 b.1;rw[bJ] at h1;have h2:=(mv r a).2.2.2;have h3:=zy r a;omega
lemma fs {f:(Fin 15->Bool)->Bool} {r:RS} (a:r ∈ dX) {g:Fin 10}
  (b:aW r (R (E g f)) (O (E g f))):49<=bv (O f):=by
 have h1:=cR (jx r a).2.1 b.2.1;rw[bt] at h1;have h2:=(jx r a).2.2.2.2.2.2.2.2;have h3:=zx r a;omega
lemma pB {p q:AS} {f h:(Fin 15->Bool)->Bool}
   (z:p ∈ dY) (x:q ∈ dY) (m w:Fin 10)
   (v:dk p (R (E m f))) (C:dk q (R (E w h)))
   (t:xq p q=true):tf (fun y=>f y||h y):=by
 have c:=mv p z;have l:=mv q x;set j:=bx m (I w)
 have d:dk (cB j.val q) (R (E m h)):=by
   have:=jt j l C;rwa[dy] at this
 have b:=dA j q l;apply mq (g:=m)
 have i:bH j.val q.2.1=(cB j.val q).2.1:=by unfold cB bH;cases nB j.val 4 <;> rfl
 have n:=j5 t j;dsimp only at n;rw[i] at n;simp only[bO,bL] at n;rcases n with hf0|(hle|has)
 . left;rw[aU,aX];exact lT (eb c.1 b.1 v.1 d.1) hf0
 . have a:=gS c b v d;left;rw[aU,aX]
   have:=cS a.1.1 a.2.1;rw[<- a.1.2.2.2] at this;omega
 . have a:=gS c b v d;rcases gi has with ⟨r,hr,g,hdu⟩;have k:=pG r hr;have u:=j3 (mA:=R (E m (fun y=>f y||h y))) (dA g r k) a.1 hdu (by rw[aU,aX];exact a.2);exact oR (oR ⟨r,hr,I g,eU g k u⟩)
lemma nh {p q:RS} {f h:(Fin 15->Bool)->Bool}
   (M:p ∈ dX) (L:q ∈ dX) (j C:Fin 10)
   (k:aW p (R (E j f)) (O (E j f)))
   (K:aW q (R (E C h)) (O (E C h)))
   (m:pV p q=true):tf (fun y=>f y&&h y):=by
 have b:=jx p M;have l:=jx q L;set d:=bx j (I C)
 have c:aW (ay d.val q) (R (E j h)) (O (E j h)):=by
   have:=cX d l K;rwa[dy] at this
 have a:=cy d q l;apply mq (g:=j)
 have u:bH d.val q.2.2.1=(ay d.val q).2.2.1:=by unfold ay bH;cases nB d.val 4 <;> rfl
 have t:cx d.val q.2.2.2.1=(ay d.val q).2.2.2.1:=by unfold ay cx;cases nB d.val 4 <;> rfl
 unfold pV at m;simp only[bO,bL] at m;rcases m with h1|hall
 . right;left;rw[aM,aZ];have z:=cR b.2.1 k.2.1;rw[<- b.2.2.2.2.2.2.2.2] at z;have n:=cR l.2.1 K.2.1;rw[bt,<-l.2.2.2.2.2.2.2.2] at n
   have hbq':q.2.1<=bv (O (E j h)):=by rw[bt];exact n
   have hb_ge:=dN (O (E j f)) (O (E j h));omega
 . have w:=j5 hall d;rw[u,t] at w;simp only[bO,bL] at w;rcases w with (hfb|hfa)|(h2|(hle|has))
   . right;left;rw[aM,aZ];exact lT hfb (fL b.2.1 a.2.1 k.2.1 c.2.1)
   . left;rw[aM,aF];exact lT (fM b.1 a.1 k.1 c.1) hfa
   . have F:=ea b a k c;right;left;rw[aM,aZ];exact lT h2 (cR F.1.2.1 F.2.2.1)
   . have i:=iF (p:=(p.1,p.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1))
       (q:=((ay d.val q).1,(ay d.val q).2.2.1,(ay d.val q).2.2.2.2.1,(ay d.val q).2.2.2.2.2.1))
       ⟨b.1,b.2.2.1,b.2.2.2.1,b.2.2.2.2.2.2.2.1⟩
       ⟨a.1,a.2.2.1,a.2.2.2.1,a.2.2.2.2.2.2.2.1⟩
       ⟨k.1,k.2.2.1,k.2.2.2.1⟩ ⟨c.1,c.2.2.1,c.2.2.2.1⟩
     left;rw[aM,aF]
     have:=cS i.1.1 i.2.1;rw[<- i.1.2.2.2] at this;omega
   . have i:=iF (p:=(p.1,p.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1))
       (q:=((ay d.val q).1,(ay d.val q).2.2.1,(ay d.val q).2.2.2.2.1,(ay d.val q).2.2.2.2.2.1))
       ⟨b.1,b.2.2.1,b.2.2.2.1,b.2.2.2.2.2.2.2.1⟩
       ⟨a.1,a.2.2.1,a.2.2.2.1,a.2.2.2.2.2.2.2.1⟩
       ⟨k.1,k.2.2.1,k.2.2.2.1⟩ ⟨c.1,c.2.2.1,c.2.2.2.1⟩
     rcases gi has with ⟨r,hr,g,hdu⟩;have v:=pG r hr;have x:=j3 (mA:=R (E j (fun y=>f y&&h y))) (dA g r v) i.1 hdu (by rw[aM,aF];exact i.2);exact oR (oR ⟨r,hr,I g,eU g v x⟩)
lemma yV {f h:(Fin 15->Bool)->Bool} (c:ms f) (a:ms h) :
   tf (fun y=>f y&&h y)/\tf (fun y=>f y||h y):=by
 have ha_and:=fb (R f) (R h);have hb_and:=dN (O f) (O h);have ha_or:=fY (R f) (R h);have hb_or:=dC (O f) (O h);refine ⟨?_,?_⟩
 . rcases c with c|c|⟨hfa,_⟩|⟨p,hp,gp,dp⟩|⟨p,hp,gp,dp⟩
   . rcases a with a|a|⟨hha,_⟩|⟨q,hq,gq,dq⟩|⟨q,hq,gq,dq⟩
     . right;left;rw[aZ];omega
     . left;rw[aF];omega
     . left;rw[aF];omega
     . left;rw[aF];have:=ft hq dq;omega
     . right;left;rw[aZ];have:=fs hq dq;omega
   . left;rw[aF];omega
   . left;rw[aF];omega
   . left;rw[aF];have:=ft hp dp;omega
   . rcases a with a|a|⟨hha,_⟩|⟨q,hq,gq,dq⟩|⟨q,hq,gq,dq⟩
     . right;left;rw[aZ];have:=fs hp dp;omega
     . left;rw[aF];omega
     . left;rw[aF];omega
     . left;rw[aF];have:=ft hq dq;omega
     . rcases dU cert_v4h p hp q hq with hok|hok
       . exact nh hp hq gp gq dp dq hok
       . have b:=nh hq hp gq gp dq dp hok
         have i:(fun y=>h y&&f y)=(fun y=>f y&&h y):=by funext y;exact bY _ _
         rwa[i] at b
 . rcases c with c|c|⟨_,hfb⟩|⟨p,hp,gp,dp⟩|⟨p,hp,gp,dp⟩
   . right;left;rw[aJ];omega
   . rcases a with a|a|⟨_,hhb⟩|⟨q,hq,gq,dq⟩|⟨q,hq,gq,dq⟩
     . right;left;rw[aJ];omega
     . left;rw[aX];omega
     . right;left;rw[aJ];omega
     . left;rw[aX];have:=ft hq dq;omega
     . right;left;rw[aJ];have:=fs hq dq;omega
   . right;left;rw[aJ];omega
   . rcases a with a|a|⟨_,hhb⟩|⟨q,hq,gq,dq⟩|⟨q,hq,gq,dq⟩
     . right;left;rw[aJ];omega
     . left;rw[aX];have:=ft hp dp;omega
     . right;left;rw[aJ];omega
     . rcases dU cert_v4c p hp q hq with hok|hok
       . exact pB hp hq gp gq dp dq hok
       . have b:=pB hq hp gq gp dq dp hok
         have d:(fun y=>h y||f y)=(fun y=>f y||h y):=by funext y;exact bP _ _
         rwa[d] at b
     . right;left;rw[aJ];have:=fs hq dq;omega
   . right;left;rw[aJ];have:=fs hp dp;omega
lemma ng {f:(Fin 15->Bool)->Bool} {r:AS} (a:r ∈ fp) {g:Fin 10}
  (b:dk r (R (E g f))):bo (R f)<=24:=by
 have h1:=cS (pG r a).1 b.1;rw[bJ] at h1;have h2:=(pG r a).2.2.2;have h3:=Cv r a;omega
lemma qV {p q:AS} {f h:(Fin 15->Bool)->Bool}
  (r:p ∈ fp) (n:q ∈ fp) (d m:Fin 10)
  (v:dk p (R (E d f))) (u:dk q (R (E m h)))
  (l:AQ p q=true):T6 (fun y=>f y||h y):=by
 have j:=pG p r;have b:=pG q n;set i:=bx d (I m)
 have k:dk (cB i.val q) (R (E d h)):=by
  have:=jt i b u;rwa[dy] at this
 have a:=dA i q b;apply wc (g:=d);have t:=bL.mp (j5 l i);have c:=gS j a v k;left;rw[aU,aX];exact lT (cS c.1.1 c.2.1) t
lemma CI {f h:(Fin 15->Bool)->Bool} (c:T5 f) (b:T5 h) :
   T6 (fun y=>f y&&h y)/\T6 (fun y=>f y||h y):=by
 have ha_and:=fb (R f) (R h);have hb_and:=dN (O f) (O h);have ha_or:=fY (R f) (R h);have hb_or:=dC (O f) (O h);refine ⟨?_,?_⟩
 . rcases c.1 with hf1|hf1
   . left;rw[aF];omega
   . rcases b.1 with hh1|hh1
     . left;rw[aF];omega
     . right;rw[aZ];omega
 . rcases c.2 with hf2|hf2|⟨p,hp,gp,dp⟩
   . rcases b.2 with hh2|hh2|⟨q,hq,gq,dq⟩
     . left;rw[aX];omega
     . right;rw[aJ];omega
     . left;rw[aX];have:=ng hq dq;omega
   . right;rw[aJ];omega
   . rcases b.2 with hh2|hh2|⟨q,hq,gq,dq⟩
     . left;rw[aX];have:=ng hp dp;omega
     . right;rw[aJ];omega
     . rcases dU cert_v5 p hp q hq with hok|hok
       . exact qV hp hq gp gq dp dq hok
       . have a:=qV hq hp gq gp dq dp hok
         have d:(fun y=>h y||f y)=(fun y=>f y||h y):=by funext y;exact bP _ _
         rwa[d] at a
def jO:ℕ->Set ((Fin 15->Bool)->Bool)
 | 0=>{ f|T0 f }
 | 1=>{ f|T1 f }
 | 2=>{ f|T2 f }
 | 3=>{ f|T3 f }
 | 4=>{ f|T4 f }
 | 5=>{ f|T5 f }
 | 6=>{ f|T6 f }
 | _=>Set.univ
lemma n9 (k:ℕ) (f h:(Fin 15->Bool)->Bool) (b:f ∈ jO k) (a:h ∈ jO k) :
  (fun y=>f y&&h y) ∈ jO (k+1)/\(fun y=>f y||h y) ∈ jO (k+1):=by
 match k with
 | 0=>exact CL b a
 | 1=>exact CK b a
 | 2=>exact CJ b a
 | 3=>
  have hf':T3 f:=b;have hh':T3 h:=a;have d:=zH hf'.1 hh'.1;have c:=zG hf'.2 hh'.2;exact ⟨⟨d.1,c.1⟩,⟨d.2,c.2⟩⟩
 | 4=>
  have hf':T4 f:=b;have hh':T4 h:=a;have d:=yU hf'.1 hh'.1;have c:=yV hf'.2 hh'.2;exact ⟨⟨d.1,c.1⟩,⟨d.2,c.2⟩⟩
 | 5=>exact CI b a
 | k+6=>exact ⟨trivial,trivial⟩
lemma wb (k:ℕ) (f:(Fin 15->Bool)->Bool) (b:f ∈ jO k):f ∈ jO (k+1):=by
 have h:=(n9 k f f b b).1
 have a:(fun y=>f y&&f y)=f:=by funext y;exact Bool.and_self (f y)
 rwa[a] at h
lemma sl:targetFn ∉ jO 6:=by
 intro h;rcases (h:T6 targetFn) with hA|hB
 . rw[tB,vA] at hA;omega
 . rw[tA,vz] at hB;omega
theorem main_proof:¬ (∀ T:ℕ->Set ((Fin 15->Bool)->Bool),
  (∀ i:Fin 15,(fun x:Fin 15->Bool=>x i) ∈ T 0)->
  (∀ (k:ℕ) (f:(Fin 15->Bool)->Bool),f ∈ T k->f ∈ T (k+1))->
  (∀ (k:ℕ) (f g:(Fin 15->Bool)->Bool),f ∈ T k->g ∈ T k->
   (fun y:Fin 15->Bool=>f y&&g y) ∈ T (k+1)/\(fun y:Fin 15->Bool=>f y||g y) ∈ T (k+1))->
  targetFn ∈ T 6):=by
 intro h;exact sl (h jO Hz wb n9)
end PEqualNP.Outside.L_meta_1404_aux
theorem PEqualNP.Outside.L_meta_1404 : ¬ (∀ T : ℕ → Set ((Fin 15 → Bool) → Bool), (∀ i : Fin 15, (fun x : Fin 15 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 15 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 15 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 15 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 15 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 15 → Bool => (((z 0 && z 5) || (z 0 && z 10) || (z 5 && z 10)) && ((z 1 && z 6) || (z 1 && z 11) || (z 6 && z 11))) || (((z 1 && z 6) || (z 1 && z 11) || (z 6 && z 11)) && ((z 2 && z 7) || (z 2 && z 12) || (z 7 && z 12))) || (((z 2 && z 7) || (z 2 && z 12) || (z 7 && z 12)) && ((z 3 && z 8) || (z 3 && z 13) || (z 8 && z 13))) || (((z 3 && z 8) || (z 3 && z 13) || (z 8 && z 13)) && ((z 4 && z 9) || (z 4 && z 14) || (z 9 && z 14))) || (((z 4 && z 9) || (z 4 && z 14) || (z 9 && z 14)) && ((z 0 && z 5) || (z 0 && z 10) || (z 5 && z 10)))) ∈ T 6) := PEqualNP.Outside.L_meta_1404_aux.main_proof
