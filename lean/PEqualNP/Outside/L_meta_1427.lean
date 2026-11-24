import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1427_aux

abbrev B := BitVec 256
abbrev Sig := B × B
def top : B := BitVec.allOnes 256
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩

lemma Live.unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U) := Or.inl ⟨_,_,_,rfl,rfl,ha,hfresh,tail⟩

lemma Live.binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U)) := Or.inr ⟨_,_,_,_,rfl,ha,hb,hab,hfresh,tail⟩

lemma liveInd {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma liveCases {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail
    · exact binary ha hb hab hf tail

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using liveInd with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 256
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 256
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 256)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 256) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 256 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 256)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def isNot (op : GateOp) : Bool := match op with | .not => true | _ => false

lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = .not := by cases op <;> simp [isNot]

def witness (allow : Bool) (w : List Sig) (z : Sig) : Prop :=
  (allow = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness false w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness (isNot g.op) w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness true w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl,a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

private lemma pull_gate {flag : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness flag w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t+flag.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hu,hT⟩
    cases hf : isNot g.op <;> simp [List.countP_cons,hf] at hcnt ⊢ <;> omega

def bit (side : Bool) (i : Fin 256) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 256).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]


def evalT (T : ℕ) (x : Fin 5 → Bool) := Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 256) (j : Fin 5) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : (∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2))
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample raw s i)
    rw [sample_list raw raw_id,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma necessary (raw : List Sig) (every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true) {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

def special : List Sig := []
def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

private lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Live m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Live l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Live l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  induction h using liveCases with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf (by simp [special]) tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf (by simp [special]) (by simp [special]) tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    obtain ⟨rfl,rfl⟩ := h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl


def Impossible (k t : Nat) (v : List Sig) : Prop :=
  ∀ m ≤ k, ¬ Live m t v.toFinset

lemma exclude_search {k t : Nat} {v : List Sig} (hv : v.Nodup) (hc : search k t v = false) :
    Impossible k t v := by
  intro m hm h
  exact Bool.false_ne_true (hc.symm.trans (search_complete h k hm v hv rfl))

lemma exclude_step {k t : Nat} {v : List Sig} {u b : List Sig → Bool} (hv : v.Nodup)
    (hu : ∀ w, u w = false → Impossible k (t-1) w)
    (hb : ∀ w, b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k+1) t v := by
  intro m hm h
  have hu' : ∀ w, w.Nodup → ∀ j ≤ k, Live j (t-1) w.toFinset → u w = true := by
    intro w _ j hj r
    cases e : u w
    · exact (hu _ e j hj r).elim
    · rfl
  have hb' : ∀ w, w.Nodup → ∀ j ≤ k, Live j t w.toFinset → b w = true := by
    intro w _ j hj r
    cases e : b w
    · exact (hb _ e j hj r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hv rfl hu' hb'))

def index (key : Nat) (j : Fin 256) : Fin 256 := Fin.ofNat 256 ((key >>> (8 * j.val)) &&& 255)

def reindex (f : Fin 256 → Fin 256) (x : B) : B :=
  (BitVec.ofBoolListLE (List.ofFn fun j => x.getLsbD (f j).val)).cast List.length_ofFn

lemma reindex_bit (f : Fin 256 → Fin 256) (a : B) (j : Nat) (hj : j < 256) :
    (reindex f a).getLsbD j = a.getLsbD (f ⟨j,hj⟩).val := by
  rw [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have h : j < (List.ofFn fun x => a.getLsbD (f x).val).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

lemma reindex_and (f : Fin 256 → Fin 256) (a b : B) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, reindex_bit _ _ _ hj]

lemma reindex_or (f : Fin 256 → Fin 256) (a b : B) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, reindex_bit _ _ _ hj]

lemma reindex_not (f : Fin 256 → Fin 256) (a : B) :
    reindex f (~~~a) = ~~~reindex f a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_not, reindex_bit _ _ _ hj, hj, (f ⟨j,hj⟩).isLt, decide_true, Bool.true_and]

lemma reindex_zero (f : Fin 256 → Fin 256) : reindex f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [reindex_bit _ _ _ hj]
  simp

lemma reindex_top (f : Fin 256 → Fin 256) : reindex f top = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [top, reindex_bit _ _ _ hj, BitVec.getLsbD_allOnes, hj, (f ⟨j,hj⟩).isLt, decide_true]

lemma reindex_injective {s inv : Fin 256 → Fin 256} (h : Function.LeftInverse inv s) :
    Function.Injective (reindex s) := by
  have hs := Finite.surjective_of_injective h.injective
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨x,hx⟩ := hs ⟨j,hj⟩
  have c := congrArg (fun a : B => a.getLsbD x.val) eq
  simpa only [reindex_bit _ _ _ x.isLt, Fin.eta, hx] using c

def action (g : Fin 256 ≃ Fin 256) (a : Sig) : Sig :=
  (reindex g a.1, reindex g a.2)

lemma action_neg (g : Fin 256 ≃ Fin 256) (a : Sig) : action g (neg a) = neg (action g a) := by
  simp [action, neg, reindex_not]

lemma action_bin (g : Fin 256 ≃ Fin 256) (d : Bool) (a b : Sig) :
    action g (bin d a b) = bin d (action g a) (action g b) := by
  cases d <;> simp [action, bin, reindex_and, reindex_or]

lemma action_zero (g : Fin 256 ≃ Fin 256) : action g zero = zero :=
  Prod.ext (reindex_zero _) (reindex_zero _)

lemma action_one (g : Fin 256 ≃ Fin 256) : action g one = one :=
  Prod.ext (reindex_top _) (reindex_top _)

lemma action_target (g : Fin 256 ≃ Fin 256) : action g target = target :=
  Prod.ext (reindex_top _) (reindex_zero _)

set_option maxRecDepth 10000 in
lemma action_injective (g : Fin 256 ≃ Fin 256) : Function.Injective (action g) := by
  intro a b eq
  have hi := reindex_injective (inv := g.symm) g.left_inv
  have hf : reindex g a.1 = reindex g b.1 :=
    congrArg (fun x : Sig => x.1) eq
  have hs : reindex g a.2 = reindex g b.2 :=
    congrArg (fun x : Sig => x.2) eq
  exact Prod.ext (hi hf) (hi hs)

lemma action_proper (g : Fin 256 ≃ Fin 256) (a : Sig) (h : proper a) : proper (action g a) := by
  constructor
  · intro h0
    exact h.1 ((action_injective g) (h0.trans (action_zero g).symm))
  · intro h1
    exact h.2 ((action_injective g) (h1.trans (action_one g).symm))

lemma restricted_action {k t : Nat} {S : Finset Sig} (h : Live k t S) (g : Fin 256 ≃ Fin 256) :
    Live k t (S.image (action g)) := by
  induction h using liveInd with
  | stop => simpa [action_target] using Live.stop
  | @unary k t U a ha hf tail ih =>
    simp only [Finset.image_insert, action_neg] at ih ⊢
    have hne : neg (action g a) ∉ insert (action g a) (U.image (action g)) := by
      rw [← Finset.image_insert, ← action_neg]
      intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hf ((action_injective g) he ▸ hy)
    exact Live.unary (action_proper _ _ ha) hne ih
  | @binary k t U a b d ha hb hab hf tail ih =>
    simp only [Finset.image_insert, action_bin] at ih ⊢
    have hne : bin d (action g a) (action g b) ∉ insert (action g a) (insert (action g b) (U.image (action g))) := by
      rw [← Finset.image_insert, ← Finset.image_insert, ← action_bin]
      intro hx
      obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hf ((action_injective g) he ▸ hy)
    exact Live.binary (action_proper _ _ ha) (action_proper _ _ hb) (fun e => hab ((action_injective g) e)) hne ih

lemma rotate_impossible {k t : Nat} {w z : List Sig} (g : Fin 256 ≃ Fin 256)
    (hp : (w.map (action g)).Perm z) (hn : Impossible k t z) : Impossible k t w := by
  intro m hm h
  apply hn m hm
  suffices hi : z.toFinset = w.toFinset.image (action g) by rw [hi]; exact restricted_action h g
  ext a
  simp only [List.mem_toFinset, hp.mem_iff.symm, List.mem_map, Finset.mem_image]

lemma impPerm {k t : Nat} {w z : List Sig} (p : w.Perm z) (h : Impossible k t z) : Impossible k t w := by
  have e : w.toFinset = z.toFinset := by ext x; simpa using (p.mem_iff (a := x))
  simpa only [Impossible,e] using h

lemma notCount (gs : List Gate)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP (fun g => isNot g.op) ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have rest : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j := by
      intro i j hi hj
      exact Fin.succ_inj.mp (single i.succ j.succ hi hj)
    by_cases hg : g.op = .not
    · have z : gs.countP (fun h => isNot h.op) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
        intro h
        have hiNot : (gs.get i).op = .not := by rw [hi]; exact (isNot_iff _).mp h
        have eqn := single (0 : Fin (g::gs).length) i.succ hg hiNot
        exact Fin.succ_ne_zero i eqn.symm
      have hf : isNot g.op = true := (isNot_iff _).mpr hg
      simp [List.countP_cons,hf,z]
    · have flag : isNot g.op = false := Bool.eq_false_iff.mpr (fun h => hg ((isNot_iff _).mp h))
      simpa [List.countP_cons,flag] using ih rest

def Clean (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

private lemma findWire {v : Sig} {w : List Sig} (h : v ∈ w) : ∃ i : Nat, w.getD i zero = v := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  exact ⟨i,by simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using eq⟩

private lemma replay {k t S} (h : Live k t S) : t = 0 → ∀ (w : List Sig),
    (∀ v ∈ S, v ∈ w) → ∃ gs : List Gate, Clean gs ∧ gs.length ≤ k ∧ target ∈ execute gs w := by
  induction h using liveInd with
  | stop =>
    intro _ w hw
    exact ⟨[],by simp [Clean],by simp,hw target (by simp)⟩
  | unary _ _ _ _ => intro ht; omega
  | @binary k t U a b d _ _ _ _ _ ih =>
    intro ht w hw
    obtain ⟨i,hi⟩ := findWire (hw a (by simp))
    obtain ⟨j,hj⟩ := findWire (hw b (by simp))
    let g : Gate := ⟨if d then .or else .and,[i,j]⟩
    have he : gv w g = bin d a b := by
      cases d
      · change bin false (w.getD i zero) (bin false (w.getD j zero) one) = _
        rw [hi,hj,(bin_laws b).1]
      · change bin true (w.getD i zero) (bin true (w.getD j zero) zero) = _
        rw [hi,hj,(bin_laws b).2.1]
    have hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by cases d <;> simp [g]
    obtain ⟨gs,hgs,len,out⟩ := ih ht (w++[gv w g]) (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp [he]
      · exact List.mem_append_left _ (hw _ (by simp [hv])))
    refine ⟨g::gs,?_,by simp; omega,out⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hh
    · exact hg
    · exact hgs _ hh

private lemma bit_target (b i) : bit b i target = b := by
  cases b
  · simp [bit,target]
  · exact bit_one true i

theorem from_target (T : Nat) (raw : List Sig)
    (rid : List.ofFn (fun i : Fin 5 => raw.getD i.val zero) = raw)
    (rows : ∀ b i, evalT T (sample raw b i) = b)
    (allRows : ∀ x : Fin 5 → Bool, ∃ b i, sample raw b i = x)
    (gs : List Gate) (clean : Clean gs) (hit : target ∈ execute gs raw) :
    ∃ o : Nat, ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT T x := by
  obtain ⟨o,ho⟩ := findWire hit
  refine ⟨o,?_⟩
  intro x
  obtain ⟨b,i,rfl⟩ := allRows x
  rw [rows,sample_list raw rid]
  have legal (g : Gate) (hg : g ∈ gs) : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    rcases (clean g hg).1 with a | a <;> simp [a]
  change (gs.foldl _ (raw.map (bit b i))).getD o false = b
  rw [←execute_bits gs b i raw legal,b_read,ho,bit_target]

theorem solve (T : Nat) (raw : List Sig) (cap : Nat)
    (rid : List.ofFn (fun i : Fin 5 => raw.getD i.val zero) = raw)
    (rows : ∀ b i, evalT T (sample raw b i) = b)
    (allRows : ∀ x : Fin 5 → Bool, ∃ b i, sample raw b i = x)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (noOne : Impossible cap 1 raw)
    (gs : List Gate) (o : Nat) (legal : (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2))
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT T x)
    (upper : ∃ ds : List Gate, ∃ p : Nat, Clean ds ∧ ds.length = cap+1 ∧
      ∀ x, Circuit.eval ⟨ds,p⟩ (List.ofFn x) = evalT T x) :
    ∃ ds : List Gate, ∃ p : Nat, Clean ds ∧ ds.length ≤ gs.length ∧
      ∀ x, Circuit.eval ⟨ds,p⟩ (List.ofFn x) = evalT T x := by
  by_cases small : gs.length ≤ cap
  · obtain ⟨k,t,S,hk,ht,live,sub⟩ := extract gs raw legal (circuit_target T raw rid rows ⟨gs,o⟩ legal he)
    have h1 := notCount gs single
    by_cases z : t = 0
    · obtain ⟨ds,hds,n,hit⟩ := replay live z raw sub
      obtain ⟨p,hp⟩ := from_target T raw rid rows allRows ds hds hit
      exact ⟨ds,p,hds,by omega,hp⟩
    · have one : t = 1 := by omega
      subst t
      have eq := necessary raw essential live sub
      exact (noOne k (by omega) (eq ▸ live)).elim
  · obtain ⟨ds,p,hds,n,hp⟩ := upper
    exact ⟨ds,p,hds,by omega,hp⟩

open PEqualNP.CircuitLowerBounds

def r0 : List Sig := [(0xfffffff00001ffffffffffffffffffe00003fffffffffffffe00003fffffffff,0x22aa0455408aa81155022aa0455408aa81155022aa0455408aa81155022aa),(0xfffffffffffe00003ffff80000fffffffffc00007fffffffffffffc00007ffff,0x244cc48998913312266244cc48998913312266244cc48998913312266244cc),(0xffffffffffffffffc000000000ffffffffffffff80000ffffffffffffff80000,0x488f0911e1223c24478488f0911e1223c24478488f0911e1223c24478488f0),(0xffffffffffffffffffffffffff0000000000000000000fffffffffffffffffff,0x70f00e1e01c3c03878070f00e1e01c3c03878070f00e1e01c3c03878070f00),(0xfffffffffffffffffffffffffffffffffffffffffffff0000000000000000000,0x7f000fe001fc003f8007f000fe001fc003f8007f000fe001fc003f8007f000)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative0_1 : Impossible 7 1 r0 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn0 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941132288 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941132288 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941132288 r0 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative0_1 gs o legal hn he
    ⟨[⟨.or,[3,4]⟩,⟨.and,[1,2]⟩,⟨.or,[0,6]⟩,⟨.and,[3,4]⟩,⟨.or,[1,8]⟩,⟨.or,[2,9]⟩,⟨.and,[5,10]⟩,⟨.and,[7,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r1 : List Sig := [(0xfffffc0000fffffffffffffc0000fffffffffffffc0000ffffffffffffffffff,0x222488892222488892222488892222488892222488892222488892222488892),(0xffffffffff00003fffffffffffff00003fffffffffffff00003fffffffffffff,0x444911124444911124444911124444911124444911124444911124444911124),(0xffffffffffffffc0000fffffffffffffc0000fffffffffffffc0000ffffc0000,0x888e22238888e22238888e22238888e22238888e22238888e22238888e22238),(0xfffffffffffffffffff000000000000000000ffffffffffffffffff000000000,0xf0f03c3c0f0f03c3c0f0f03c3c0f0f03c3c0f0f03c3c0f0f03c3c0f0f03c3c0),(0xfffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative1_1 : Impossible 5 1 r1 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn1 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3907577992 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3907577992 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3907577992 r1 5 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative1_1 gs o legal hn he
    ⟨[⟨.and,[0,1]⟩,⟨.or,[3,4]⟩,⟨.and,[2,6]⟩,⟨.or,[0,1]⟩,⟨.or,[5,7]⟩,⟨.and,[8,9]⟩],10,by simp [Clean],rfl,by decide +kernel⟩

def r2 : List Sig := [(0xfffffc0000ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x21080842021080842021080842021080842021080842021080842021080842),(0xffffffffff00003ffff00003ffff00003ffffffffc0000fffffffff00003ffff,0x54a51529454a51529454a51529454a51529454a51529454a51529454a515294),(0xffffffffffffffc000000003ffffffffc0000fffffffff00003ffffffffc0000,0x98c62631898c62631898c62631898c62631898c62631898c62631898c626318),(0xfffffffffffffffffffffffc0000000000000fffffffffffffc0000000000000,0xe0f8383e0e0f8383e0e0f8383e0e0f8383e0e0f8383e0e0f8383e0e0f8383e0),(0xfffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative2_1 : Impossible 6 1 r2 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn2 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3936921768 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3936921768 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3936921768 r2 6 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative2_1 gs o legal hn he
    ⟨[⟨.and,[3,4]⟩,⟨.and,[1,2]⟩,⟨.or,[0,6]⟩,⟨.or,[1,2]⟩,⟨.and,[0,8]⟩,⟨.and,[5,7]⟩,⟨.or,[9,10]⟩],11,by simp [Clean],rfl,by decide +kernel⟩

def r3 : List Sig := [(0xfffffc0000fffffffffffffffffffffffffffffffc0000ffffffffffffffffff,0x22480892022480892022480892022480892022480892022480892022480892),(0xffffffffff00003ffff00003ffff00003fffffffffffff00003fffffffffffff,0x544915124544915124544915124544915124544915124544915124544915124),(0xffffffffffffffc000000003ffffffffc0000fffffffffffffc0000ffffc0000,0x988e26238988e26238988e26238988e26238988e26238988e26238988e26238),(0xfffffffffffffffffffffffc0000000000000ffffffffffffffffff000000000,0xe0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0),(0xfffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative3_1 : Impossible 7 1 r3 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn3 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3936938120 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3936938120 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3936938120 r3 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative3_1 gs o legal hn he
    ⟨[⟨.or,[2,3]⟩,⟨.and,[2,3]⟩,⟨.and,[0,5]⟩,⟨.or,[4,6]⟩,⟨.or,[0,6]⟩,⟨.and,[7,8]⟩,⟨.or,[1,10]⟩,⟨.and,[9,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r4 : List Sig := [(0xfffffc0000ffffffffffffffffffffffffffffffffffff00003fffffffffffff,0x12480492012480492012480492012480492012480492012480492012480492),(0xffffffffff00003ffff00003ffff00003ffff00003ffffffffffffffffffffff,0x544915124544915124544915124544915124544915124544915124544915124),(0xffffffffffffffc000000003ffffffffc000000003ffffffffc0000ffffc0000,0x998e26638998e26638998e26638998e26638998e26638998e26638998e26638),(0xfffffffffffffffffffffffc000000000000000003fffffffffffff000000000,0xe1f0387c0e1f0387c0e1f0387c0e1f0387c0e1f0387c0e1f0387c0e1f0387c0),(0xfffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfe003f800fe003f800fe003f800fe003f800fe003f800fe003f800fe003f800)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative4_1 : Impossible 4 1 r4 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn4 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3937061000 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3937061000 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3937061000 r4 4 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative4_1 gs o legal hn he
    ⟨[⟨.or,[1,4]⟩,⟨.and,[0,5]⟩,⟨.and,[2,3]⟩,⟨.and,[1,7]⟩,⟨.or,[6,8]⟩],9,by simp [Clean],rfl,by decide +kernel⟩

def r5 : List Sig := [(0xfffffc0000ffffffffffffffffffffffffffffffffffff00003fffffffffffff,0x4a8012a004a8012a004a8012a004a8012a004a8012a004a8012a004a8012a),(0xffffffffff00003ffff00003ffff00003ffff00003ffffffffc0000fffffffff,0x54931524c54931524c54931524c54931524c54931524c54931524c54931524c),(0xffffffffffffffc000000003ffffffffc000000003fffffffffffff00003ffff,0x991c26470991c26470991c26470991c26470991c26470991c26470991c26470),(0xfffffffffffffffffffffffc000000000000000003fffffffffffffffffc0000,0xe1e038780e1e038780e1e038780e1e038780e1e038780e1e038780e1e038780),(0xfffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfe003f800fe003f800fe003f800fe003f800fe003f800fe003f800fe003f800)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative5_1 : Impossible 7 1 r5 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn5 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3937069184 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3937069184 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3937069184 r5 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative5_1 gs o legal hn he
    ⟨[⟨.or,[1,2]⟩,⟨.and,[1,2]⟩,⟨.or,[4,6]⟩,⟨.and,[3,6]⟩,⟨.and,[3,5]⟩,⟨.or,[7,9]⟩,⟨.or,[0,8]⟩,⟨.and,[10,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r6 : List Sig := [(0xfffffc0000ffffffffffffffffff00003ffffffffc0000ffffffffffffffffff,0x122484892122484892122484892122484892122484892122484892122484892),(0xffffffffff00003ffff00003ffffffffffffffffffffff00003fffffffffffff,0x444911124444911124444911124444911124444911124444911124444911124),(0xffffffffffffffc000000003ffffffffc0000fffffffffffffc0000ffffc0000,0x988e26238988e26238988e26238988e26238988e26238988e26238988e26238),(0xfffffffffffffffffffffffc0000000000000ffffffffffffffffff000000000,0xe0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0),(0xfffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative6_1 : Impossible 7 1 r6 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn6 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3939035272 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3939035272 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3939035272 r6 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative6_1 gs o legal hn he
    ⟨[⟨.and,[0,3]⟩,⟨.and,[1,2]⟩,⟨.or,[5,6]⟩,⟨.and,[2,3]⟩,⟨.or,[4,8]⟩,⟨.and,[0,1]⟩,⟨.and,[7,9]⟩,⟨.or,[10,11]⟩],12,by simp [Clean],rfl,by decide +kernel⟩

def r7 : List Sig := [(0xfffffc0000ffffffffffffffffff00003ffffffffc0000fffffffffffffc0000,0x122a848aa122a848aa122a848aa122a848aa122a848aa122a848aa122a848aa),(0xffffffffff00003ffff00003ffffffffffffffffffffff00003fffffffffffff,0x44431110c44431110c44431110c44431110c44431110c44431110c44431110c),(0xffffffffffffffc000000003ffffffffc0000fffffffffffffc0000fffffffff,0x988c26230988c26230988c26230988c26230988c26230988c26230988c26230),(0xfffffffffffffffffffffffc0000000000000ffffffffffffffffff000000000,0xe0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0e0f0383c0),(0xfffffffffffffffffffffffffffffffffffff000000000000000000000000000,0xff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00ff003fc00)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative7_1 : Impossible 6 1 r7 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn7 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3939035328 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3939035328 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3939035328 r7 6 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative7_1 gs o legal hn he
    ⟨[⟨.and,[0,4]⟩,⟨.and,[0,3]⟩,⟨.or,[2,5]⟩,⟨.and,[1,6]⟩,⟨.or,[7,8]⟩,⟨.or,[1,6]⟩,⟨.and,[9,10]⟩],11,by simp [Clean],rfl,by decide +kernel⟩

def r8 : List Sig := [(0xfffffc0000ffffffffffffffffff00003fffffffffffff00003fffffffffffff,0x44a8112a044a8112a044a8112a044a8112a044a8112a044a8112a044a8112a),(0xffffffffff00003ffff00003ffffffffc0000fffffffffffffc0000fffffffff,0x48931224c48931224c48931224c48931224c48931224c48931224c48931224c),(0xffffffffffffffc000000003fffffffffffff00003fffffffffffff00003ffff,0x911c24470911c24470911c24470911c24470911c24470911c24470911c24470),(0xfffffffffffffffffffffffc000000000000000003fffffffffffffffffc0000,0xe1e038780e1e038780e1e038780e1e038780e1e038780e1e038780e1e038780),(0xfffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfe003f800fe003f800fe003f800fe003f800fe003f800fe003f800fe003f800)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym8_0 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdfcfbfaf9f4f3f2f1f8f7f6f5f0efeeedecebeae9e8e7e2e1e0dfe6e5e4e3dedddcdbdad9d8d7d6d5d0cfcecdd4d3d2d1cccbcac9c8c7c6c5c4c3bebdbcbbc2c1c0bfbab9b8b7b6b5b4b3b2b1acabaaa9b0afaeada8a7a6a5a4a3a25958575251504f565554534e4d4c4b4a4948474645403f3e3d444342413c3b3a393837363534332e2d2c2b3231302f2a2928272625242322211c1b1a19201f1e1d18171615141312a1a09f9a9998979e9d9c9b969594939291908f8e8d888786858c8b8a8984838281807f7e7d7c7b767574737a7978777271706f6e6d6c6b6a696463626168676665605f5e5d5c5b5a11100f0a0908070e0d0c0b06050403020100,index 0xfffefdfcfbfaf9f4f3f2f1f8f7f6f5f0efeeedecebeae9e8e7e2e1e0dfe6e5e4e3dedddcdbdad9d8d7d6d5d0cfcecdd4d3d2d1cccbcac9c8c7c6c5c4c3bebdbcbbc2c1c0bfbab9b8b7b6b5b4b3b2b1acabaaa9b0afaeada8a7a6a5a4a3a25958575251504f565554534e4d4c4b4a4948474645403f3e3d444342413c3b3a393837363534332e2d2c2b3231302f2a2928272625242322211c1b1a19201f1e1d18171615141312a1a09f9a9998979e9d9c9b969594939291908f8e8d888786858c8b8a8984838281807f7e7d7c7b767574737a7978777271706f6e6d6c6b6a696463626168676665605f5e5d5c5b5a11100f0a0908070e0d0c0b06050403020100,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_0_0 : action sym8_0 (r8.getD 0 zero) = r8.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_0_1 : action sym8_0 (r8.getD 1 zero) = r8.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_0_2 : action sym8_0 (r8.getD 2 zero) = r8.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_0_3 : action sym8_0 (r8.getD 3 zero) = r8.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_0_4 : action sym8_0 (r8.getD 4 zero) = r8.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym8_1 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdfcfafbf9f7f8f6f5f3f4f2f1f0edecefeeebeae8e9e7e5e6e4e3e1e2e0dfdedbdadddcd9d8c4c5c3c1c2c0bfbdbebcbbbab7b6b9b8b5b4d6d7d5d3d4d2d1cfd0cecdccc9c8cbcac7c6b2b3b1afb0aeadabacaaa9a8a5a4a7a6a3a2a0a19f9d9e9c9b999a9897969392959491908e8f8d8b8c8a898788868584818083827f7e6a6b696768666563646261605d5c5f5e5b5a7c7d7b797a787775767473726f6e71706d6c585957555654535152504f4e4b4a4d4c4948464745434442413f403e3d3c39383b3a37362223211f201e1d1b1c1a19181514171613123435333132302f2d2e2c2b2a27262928252410110f0d0e0c0b090a080706030205040100,index 0xfffefdfcfafbf9f7f8f6f5f3f4f2f1f0edecefeeebeae8e9e7e5e6e4e3e1e2e0dfdedbdadddcd9d8c4c5c3c1c2c0bfbdbebcbbbab7b6b9b8b5b4d6d7d5d3d4d2d1cfd0cecdccc9c8cbcac7c6b2b3b1afb0aeadabacaaa9a8a5a4a7a6a3a2a0a19f9d9e9c9b999a9897969392959491908e8f8d8b8c8a898788868584818083827f7e6a6b696768666563646261605d5c5f5e5b5a7c7d7b797a787775767473726f6e71706d6c585957555654535152504f4e4b4a4d4c4948464745434442413f403e3d3c39383b3a37362223211f201e1d1b1c1a19181514171613123435333132302f2d2e2c2b2a27262928252410110f0d0e0c0b090a080706030205040100,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_1_0 : action sym8_1 (r8.getD 0 zero) = r8.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_1_1 : action sym8_1 (r8.getD 1 zero) = r8.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_1_2 : action sym8_1 (r8.getD 2 zero) = r8.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_1_3 : action sym8_1 (r8.getD 3 zero) = r8.getD 3 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_1_4 : action sym8_1 (r8.getD 4 zero) = r8.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
def sym8_2 : Fin 256 ≃ Fin 256 :=
  ⟨index 0xfffefdfcfafbf9f3f4f2f1f7f8f6f5f0edecefeeebeae8e9e7e1e2e0dfe5e6e4e3dedbdadddcd9d8c4c5c3bdbebcbbc1c2c0bfbab7b6b9b8b5b4d6d7d5cfd0cecdd3d4d2d1ccc9c8cbcac7c6b2b3b1abacaaa9afb0aeada8a5a4a7a6a3a25859575152504f555654534e4b4a4d4c49484647453f403e3d434442413c39383b3a37362223211b1c1a191f201e1d181514171613123435332d2e2c2b3132302f2a272629282524a0a19f999a98979d9e9c9b969392959491908e8f8d878886858b8c8a8984818083827f7e6a6b696364626167686665605d5c5f5e5b5a7c7d7b75767473797a7877726f6e71706d6c10110f090a08070d0e0c0b06030205040100,index 0xfffefdfcfafbf9f3f4f2f1f7f8f6f5f0edecefeeebeae8e9e7e1e2e0dfe5e6e4e3dedbdadddcd9d8c4c5c3bdbebcbbc1c2c0bfbab7b6b9b8b5b4d6d7d5cfd0cecdd3d4d2d1ccc9c8cbcac7c6b2b3b1abacaaa9afb0aeada8a5a4a7a6a3a25859575152504f555654534e4b4a4d4c49484647453f403e3d434442413c39383b3a37362223211b1c1a191f201e1d181514171613123435332d2e2c2b3132302f2a272629282524a0a19f999a98979d9e9c9b969392959491908e8f8d878886858b8c8a8984818083827f7e6a6b696364626167686665605d5c5f5e5b5a7c7d7b75767473797a7877726f6e71706d6c10110f090a08070d0e0c0b06030205040100,by decide +kernel,by decide +kernel⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_2_0 : action sym8_2 (r8.getD 0 zero) = r8.getD 0 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_2_1 : action sym8_2 (r8.getD 1 zero) = r8.getD 2 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_2_2 : action sym8_2 (r8.getD 2 zero) = r8.getD 1 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_2_3 : action sym8_2 (r8.getD 3 zero) = r8.getD 4 zero := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma rot8_2_4 : action sym8_2 (r8.getD 4 zero) = r8.getD 3 zero := by decide +kernel

def x8_0 : Sig := r8.getD 0 zero
def x8_1 : Sig := r8.getD 1 zero
def x8_2 : Sig := r8.getD 2 zero
def x8_3 : Sig := r8.getD 3 zero
def x8_4 : Sig := r8.getD 4 zero
def y8_5 : Sig := neg x8_0
def y8_6 : Sig := neg x8_1
def y8_7 : Sig := neg x8_2
def y8_8 : Sig := neg x8_3
def y8_9 : Sig := neg x8_4
def y8_10 : Sig := bin false x8_0 x8_1
def y8_11 : Sig := bin true x8_0 x8_1
def y8_12 : Sig := bin false x8_0 x8_2
def y8_13 : Sig := bin true x8_0 x8_2
def y8_14 : Sig := bin false x8_0 x8_3
def y8_15 : Sig := bin true x8_0 x8_3
def y8_16 : Sig := bin false x8_0 x8_4
def y8_17 : Sig := bin true x8_0 x8_4
def y8_18 : Sig := bin false x8_1 x8_2
def y8_19 : Sig := bin true x8_1 x8_2
def y8_20 : Sig := bin false x8_1 x8_3
def y8_21 : Sig := bin true x8_1 x8_3
def y8_22 : Sig := bin false x8_1 x8_4
def y8_23 : Sig := bin true x8_1 x8_4
def y8_24 : Sig := bin false x8_2 x8_3
def y8_25 : Sig := bin true x8_2 x8_3
def y8_26 : Sig := bin false x8_2 x8_4
def y8_27 : Sig := bin true x8_2 x8_4
def y8_28 : Sig := bin false x8_3 x8_4
def y8_29 : Sig := bin true x8_3 x8_4
def y8_30 : Sig := neg y8_10
def y8_31 : Sig := neg y8_11
def y8_34 : Sig := neg y8_14
def y8_35 : Sig := neg y8_15
def y8_38 : Sig := neg y8_18
def y8_39 : Sig := neg y8_19
def y8_40 : Sig := neg y8_20
def y8_41 : Sig := neg y8_21
def y8_48 : Sig := neg y8_28
def y8_49 : Sig := neg y8_29
def y8_50 : Sig := bin false x8_0 y8_6
def y8_51 : Sig := bin true x8_0 y8_6
def y8_52 : Sig := bin false x8_0 y8_8
def y8_53 : Sig := bin true x8_0 y8_8
def y8_54 : Sig := bin false x8_0 y8_18
def y8_55 : Sig := bin true x8_0 y8_18
def y8_56 : Sig := bin false x8_0 y8_19
def y8_57 : Sig := bin true x8_0 y8_19
def y8_58 : Sig := bin false x8_0 y8_20
def y8_59 : Sig := bin true x8_0 y8_20
def y8_60 : Sig := bin false x8_0 y8_21
def y8_61 : Sig := bin true x8_0 y8_21
def y8_62 : Sig := bin false x8_0 y8_22
def y8_63 : Sig := bin true x8_0 y8_23
def y8_64 : Sig := bin false x8_0 y8_24
def y8_65 : Sig := bin true x8_0 y8_25
def y8_66 : Sig := bin false x8_0 y8_28
def y8_67 : Sig := bin true x8_0 y8_28
def y8_68 : Sig := bin false x8_0 y8_29
def y8_69 : Sig := bin true x8_0 y8_29
def y8_70 : Sig := bin false x8_1 y8_5
def y8_71 : Sig := bin true x8_1 y8_5
def y8_72 : Sig := bin false x8_1 y8_8
def y8_73 : Sig := bin true x8_1 y8_8
def y8_74 : Sig := bin true x8_1 y8_14
def y8_75 : Sig := bin false x8_1 y8_15
def y8_76 : Sig := bin false x8_1 y8_24
def y8_77 : Sig := bin true x8_1 y8_25
def y8_78 : Sig := bin false x8_1 y8_26
def y8_79 : Sig := bin true x8_1 y8_27
def y8_80 : Sig := bin false x8_1 y8_28
def y8_81 : Sig := bin true x8_1 y8_28
def y8_82 : Sig := bin false x8_1 y8_29
def y8_83 : Sig := bin true x8_1 y8_29
def y8_84 : Sig := bin false x8_2 y8_5
def y8_85 : Sig := bin true x8_2 y8_5
def y8_86 : Sig := bin false x8_2 y8_6
def y8_87 : Sig := bin true x8_2 y8_6
def y8_88 : Sig := bin false x8_2 y8_8
def y8_89 : Sig := bin true x8_2 y8_8
def y8_90 : Sig := bin true x8_2 y8_10
def y8_91 : Sig := bin false x8_2 y8_11
def y8_92 : Sig := bin true x8_2 y8_14
def y8_93 : Sig := bin false x8_2 y8_15
def y8_94 : Sig := bin true x8_2 y8_20
def y8_95 : Sig := bin false x8_2 y8_21
def y8_96 : Sig := bin false x8_2 y8_28
def y8_97 : Sig := bin true x8_2 y8_28
def y8_98 : Sig := bin false x8_2 y8_29
def y8_99 : Sig := bin true x8_2 y8_29
def y8_100 : Sig := bin false x8_3 y8_5
def y8_101 : Sig := bin true x8_3 y8_5
def y8_102 : Sig := bin false x8_3 y8_6
def y8_103 : Sig := bin true x8_3 y8_6
def y8_104 : Sig := bin true x8_3 y8_10
def y8_105 : Sig := bin false x8_3 y8_11
def y8_106 : Sig := bin true x8_3 y8_18
def y8_107 : Sig := bin false x8_3 y8_19
def y8_108 : Sig := bin false x8_4 y8_5
def y8_109 : Sig := bin true x8_4 y8_5
def y8_110 : Sig := bin false x8_4 y8_6
def y8_111 : Sig := bin true x8_4 y8_6
def y8_112 : Sig := bin false x8_4 y8_8
def y8_113 : Sig := bin true x8_4 y8_8
def y8_114 : Sig := bin true x8_4 y8_10
def y8_115 : Sig := bin false x8_4 y8_11
def y8_116 : Sig := bin true x8_4 y8_14
def y8_117 : Sig := bin false x8_4 y8_15
def y8_118 : Sig := bin true x8_4 y8_18
def y8_119 : Sig := bin false x8_4 y8_19
def y8_120 : Sig := bin true x8_4 y8_20
def y8_121 : Sig := bin false x8_4 y8_21

def s8_0 : List Sig := [y8_70,x8_1,x8_0,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_0x : Impossible 7 0 s8_0 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_1 : List Sig := [y8_70,y8_5,x8_1,x8_0,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_1x : Impossible 7 0 s8_1 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_2 : List Sig := [y8_71,x8_1,x8_0,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_2x : Impossible 7 0 s8_2 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_3 : List Sig := [y8_71,y8_5,x8_1,x8_0,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_3x : Impossible 7 0 s8_3 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_4 : List Sig := [y8_84,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_4x : Impossible 7 0 s8_4 := rotate_impossible sym8_1 (z := s8_0) (by simp only [s8_4,x8_0,x8_1,x8_2,x8_3,x8_4,y8_5,y8_84,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_0x

def s8_5 : List Sig := [y8_84,y8_5,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_5x : Impossible 7 0 s8_5 := rotate_impossible sym8_1 (z := s8_1) (by simp only [s8_5,x8_0,x8_1,x8_2,x8_3,x8_4,y8_5,y8_84,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_1x

def s8_6 : List Sig := [y8_85,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_6x : Impossible 7 0 s8_6 := rotate_impossible sym8_1 (z := s8_2) (by simp only [s8_6,x8_0,x8_1,x8_2,x8_3,x8_4,y8_5,y8_85,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_2x

def s8_7 : List Sig := [y8_85,y8_5,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_7x : Impossible 7 0 s8_7 := rotate_impossible sym8_1 (z := s8_3) (by simp only [s8_7,x8_0,x8_1,x8_2,x8_3,x8_4,y8_5,y8_85,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_3x

def s8_8 : List Sig := [y8_100,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_8x : Impossible 7 0 s8_8 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_9 : List Sig := [y8_100,y8_5,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_9x : Impossible 7 0 s8_9 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_10 : List Sig := [y8_101,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_10x : Impossible 7 0 s8_10 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_11 : List Sig := [y8_101,y8_5,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_11x : Impossible 7 0 s8_11 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_12 : List Sig := [y8_108,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_12x : Impossible 7 0 s8_12 := rotate_impossible sym8_0 (z := s8_8) (by simp only [s8_12,x8_0,x8_1,x8_2,x8_3,x8_4,y8_108,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_8x

def s8_13 : List Sig := [y8_108,y8_5,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_13x : Impossible 7 0 s8_13 := rotate_impossible sym8_0 (z := s8_9) (by simp only [s8_13,x8_0,x8_1,x8_2,x8_3,x8_4,y8_108,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_9x

def s8_14 : List Sig := [y8_109,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_14x : Impossible 7 0 s8_14 := rotate_impossible sym8_0 (z := s8_10) (by simp only [s8_14,x8_0,x8_1,x8_2,x8_3,x8_4,y8_109,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_10x

def s8_15 : List Sig := [y8_109,y8_5,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_15x : Impossible 7 0 s8_15 := rotate_impossible sym8_0 (z := s8_11) (by simp only [s8_15,x8_0,x8_1,x8_2,x8_3,x8_4,y8_109,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_11x

def s8_16 : List Sig := [y8_10,x8_0,x8_1,y8_5,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_16x : Impossible 7 0 s8_16 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_17 : List Sig := [y8_11,x8_0,x8_1,y8_5,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_17x : Impossible 7 0 s8_17 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_18 : List Sig := [y8_12,x8_0,x8_2,y8_5,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_18x : Impossible 7 0 s8_18 := rotate_impossible sym8_1 (z := s8_16) (by simp only [s8_18,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_16x

def s8_19 : List Sig := [y8_13,x8_0,x8_2,y8_5,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_19x : Impossible 7 0 s8_19 := rotate_impossible sym8_1 (z := s8_17) (by simp only [s8_19,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_17x

def s8_20 : List Sig := [y8_14,x8_0,x8_3,y8_5,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_20x : Impossible 7 0 s8_20 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_21 : List Sig := [y8_15,x8_0,x8_3,y8_5,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_21x : Impossible 7 0 s8_21 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_22 : List Sig := [y8_16,x8_0,x8_4,y8_5,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_22x : Impossible 7 0 s8_22 := rotate_impossible sym8_0 (z := s8_20) (by simp only [s8_22,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_20x

def s8_23 : List Sig := [y8_17,x8_0,x8_4,y8_5,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_23x : Impossible 7 0 s8_23 := rotate_impossible sym8_0 (z := s8_21) (by simp only [s8_23,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_21x

def s8_24 : List Sig := [y8_18,x8_1,x8_2,y8_5,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_24x : Impossible 7 0 s8_24 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_25 : List Sig := [y8_19,x8_1,x8_2,y8_5,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_25x : Impossible 7 0 s8_25 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_26 : List Sig := [y8_20,x8_1,x8_3,y8_5,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_26x : Impossible 7 0 s8_26 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_27 : List Sig := [y8_21,x8_1,x8_3,y8_5,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_27x : Impossible 7 0 s8_27 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_28 : List Sig := [y8_22,x8_1,x8_4,y8_5,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_28x : Impossible 7 0 s8_28 := rotate_impossible sym8_0 (z := s8_26) (by simp only [s8_28,x8_0,x8_1,x8_2,x8_3,x8_4,y8_22,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_26x

def s8_29 : List Sig := [y8_23,x8_1,x8_4,y8_5,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_29x : Impossible 7 0 s8_29 := rotate_impossible sym8_0 (z := s8_27) (by simp only [s8_29,x8_0,x8_1,x8_2,x8_3,x8_4,y8_23,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_27x

def s8_30 : List Sig := [y8_24,x8_2,x8_3,y8_5,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_30x : Impossible 7 0 s8_30 := rotate_impossible sym8_1 (z := s8_26) (by simp only [s8_30,x8_0,x8_1,x8_2,x8_3,x8_4,y8_24,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_26x

def s8_31 : List Sig := [y8_25,x8_2,x8_3,y8_5,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_31x : Impossible 7 0 s8_31 := rotate_impossible sym8_1 (z := s8_27) (by simp only [s8_31,x8_0,x8_1,x8_2,x8_3,x8_4,y8_25,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_27x

def s8_32 : List Sig := [y8_26,x8_2,x8_4,y8_5,x8_0,x8_1,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_32x : Impossible 7 0 s8_32 := rotate_impossible sym8_0 (z := s8_30) (by simp only [s8_32,x8_0,x8_1,x8_2,x8_3,x8_4,y8_26,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_30x

def s8_33 : List Sig := [y8_27,x8_2,x8_4,y8_5,x8_0,x8_1,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_33x : Impossible 7 0 s8_33 := rotate_impossible sym8_0 (z := s8_31) (by simp only [s8_33,x8_0,x8_1,x8_2,x8_3,x8_4,y8_27,y8_5,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_31x

def s8_34 : List Sig := [y8_28,x8_3,x8_4,y8_5,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_34x : Impossible 7 0 s8_34 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_35 : List Sig := [y8_29,x8_3,x8_4,y8_5,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_35x : Impossible 7 0 s8_35 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_36 : List Sig := [y8_5,x8_0,x8_1,x8_2,x8_3,x8_4]
lemma s8_36ux (v : List Sig) (h : true = false) : Impossible 7 0 v := Bool.noConfusion h
def s8_36b : List (List Sig) := [s8_0,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6,s8_7,s8_8,s8_9,s8_10,s8_11,s8_12,s8_13,s8_14,s8_15,s8_16,s8_17,s8_18,s8_19,s8_20,s8_21,s8_22,s8_23,s8_24,s8_25,s8_26,s8_27,s8_28,s8_29,s8_30,s8_31,s8_32,s8_33,s8_34,s8_35]
lemma s8_36bx (v : List Sig) (h : (!s8_36b.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_36b := by simpa using h
  simp only [s8_36b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_0x
  · exact s8_1x
  · exact s8_2x
  · exact s8_3x
  · exact s8_4x
  · exact s8_5x
  · exact s8_6x
  · exact s8_7x
  · exact s8_8x
  · exact s8_9x
  · exact s8_10x
  · exact s8_11x
  · exact s8_12x
  · exact s8_13x
  · exact s8_14x
  · exact s8_15x
  · exact s8_16x
  · exact s8_17x
  · exact s8_18x
  · exact s8_19x
  · exact s8_20x
  · exact s8_21x
  · exact s8_22x
  · exact s8_23x
  · exact s8_24x
  · exact s8_25x
  · exact s8_26x
  · exact s8_27x
  · exact s8_28x
  · exact s8_29x
  · exact s8_30x
  · exact s8_31x
  · exact s8_32x
  · exact s8_33x
  · exact s8_34x
  · exact s8_35x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_36x : Impossible 8 0 s8_36 :=
  exclude_step (u := fun _ => true) (b := fun v => !s8_36b.contains v) (by decide +kernel) s8_36ux s8_36bx (by decide +kernel)

def s8_37 : List Sig := [y8_50,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_37x : Impossible 7 0 s8_37 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_38 : List Sig := [y8_50,y8_6,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_38x : Impossible 7 0 s8_38 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_39 : List Sig := [y8_51,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_39x : Impossible 7 0 s8_39 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_40 : List Sig := [y8_51,y8_6,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_40x : Impossible 7 0 s8_40 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_41 : List Sig := [y8_86,x8_2,x8_1,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_41x : Impossible 7 0 s8_41 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_42 : List Sig := [y8_86,y8_6,x8_2,x8_1,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_42x : Impossible 7 0 s8_42 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_43 : List Sig := [y8_87,x8_2,x8_1,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_43x : Impossible 7 0 s8_43 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_44 : List Sig := [y8_87,y8_6,x8_2,x8_1,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_44x : Impossible 7 0 s8_44 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_45 : List Sig := [y8_102,x8_3,x8_1,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_45x : Impossible 7 0 s8_45 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_46 : List Sig := [y8_102,y8_6,x8_3,x8_1,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_46x : Impossible 7 0 s8_46 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_47 : List Sig := [y8_103,x8_3,x8_1,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_47x : Impossible 7 0 s8_47 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_48 : List Sig := [y8_103,y8_6,x8_3,x8_1,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_48x : Impossible 7 0 s8_48 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_49 : List Sig := [y8_110,x8_4,x8_1,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_49x : Impossible 7 0 s8_49 := rotate_impossible sym8_0 (z := s8_45) (by simp only [s8_49,x8_0,x8_1,x8_2,x8_3,x8_4,y8_110,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_45x

def s8_50 : List Sig := [y8_110,y8_6,x8_4,x8_1,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_50x : Impossible 7 0 s8_50 := rotate_impossible sym8_0 (z := s8_46) (by simp only [s8_50,x8_0,x8_1,x8_2,x8_3,x8_4,y8_110,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_46x

def s8_51 : List Sig := [y8_111,x8_4,x8_1,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_51x : Impossible 7 0 s8_51 := rotate_impossible sym8_0 (z := s8_47) (by simp only [s8_51,x8_0,x8_1,x8_2,x8_3,x8_4,y8_111,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_47x

def s8_52 : List Sig := [y8_111,y8_6,x8_4,x8_1,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_52x : Impossible 7 0 s8_52 := rotate_impossible sym8_0 (z := s8_48) (by simp only [s8_52,x8_0,x8_1,x8_2,x8_3,x8_4,y8_111,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_48x

def s8_53 : List Sig := [y8_10,x8_1,x8_0,y8_6,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_53x : Impossible 7 0 s8_53 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_54 : List Sig := [y8_11,x8_1,x8_0,y8_6,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_54x : Impossible 7 0 s8_54 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_55 : List Sig := [y8_18,x8_1,x8_2,y8_6,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_55x : Impossible 7 0 s8_55 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_56 : List Sig := [y8_19,x8_1,x8_2,y8_6,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_56x : Impossible 7 0 s8_56 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_57 : List Sig := [y8_20,x8_1,x8_3,y8_6,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_57x : Impossible 7 0 s8_57 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_58 : List Sig := [y8_21,x8_1,x8_3,y8_6,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_58x : Impossible 7 0 s8_58 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_59 : List Sig := [y8_22,x8_1,x8_4,y8_6,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_59x : Impossible 7 0 s8_59 := rotate_impossible sym8_0 (z := s8_57) (by simp only [s8_59,x8_0,x8_1,x8_2,x8_3,x8_4,y8_22,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_57x

def s8_60 : List Sig := [y8_23,x8_1,x8_4,y8_6,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_60x : Impossible 7 0 s8_60 := rotate_impossible sym8_0 (z := s8_58) (by simp only [s8_60,x8_0,x8_1,x8_2,x8_3,x8_4,y8_23,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_58x

def s8_61 : List Sig := [y8_12,x8_0,x8_2,y8_6,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_61x : Impossible 7 0 s8_61 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_62 : List Sig := [y8_13,x8_0,x8_2,y8_6,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_62x : Impossible 7 0 s8_62 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_63 : List Sig := [y8_14,x8_0,x8_3,y8_6,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_63x : Impossible 7 0 s8_63 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_64 : List Sig := [y8_15,x8_0,x8_3,y8_6,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_64x : Impossible 7 0 s8_64 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_65 : List Sig := [y8_16,x8_0,x8_4,y8_6,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_65x : Impossible 7 0 s8_65 := rotate_impossible sym8_0 (z := s8_63) (by simp only [s8_65,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_63x

def s8_66 : List Sig := [y8_17,x8_0,x8_4,y8_6,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_66x : Impossible 7 0 s8_66 := rotate_impossible sym8_0 (z := s8_64) (by simp only [s8_66,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_64x

def s8_67 : List Sig := [y8_24,x8_2,x8_3,y8_6,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_67x : Impossible 7 0 s8_67 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_68 : List Sig := [y8_25,x8_2,x8_3,y8_6,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_68x : Impossible 7 0 s8_68 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_69 : List Sig := [y8_26,x8_2,x8_4,y8_6,x8_1,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_69x : Impossible 7 0 s8_69 := rotate_impossible sym8_0 (z := s8_67) (by simp only [s8_69,x8_0,x8_1,x8_2,x8_3,x8_4,y8_26,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_67x

def s8_70 : List Sig := [y8_27,x8_2,x8_4,y8_6,x8_1,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_70x : Impossible 7 0 s8_70 := rotate_impossible sym8_0 (z := s8_68) (by simp only [s8_70,x8_0,x8_1,x8_2,x8_3,x8_4,y8_27,y8_6,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_68x

def s8_71 : List Sig := [y8_28,x8_3,x8_4,y8_6,x8_1,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_71x : Impossible 7 0 s8_71 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_72 : List Sig := [y8_29,x8_3,x8_4,y8_6,x8_1,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_72x : Impossible 7 0 s8_72 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_73 : List Sig := [y8_6,x8_1,x8_0,x8_2,x8_3,x8_4]
lemma s8_73ux (v : List Sig) (h : true = false) : Impossible 7 0 v := Bool.noConfusion h
def s8_73b : List (List Sig) := [s8_37,s8_38,s8_39,s8_40,s8_41,s8_42,s8_43,s8_44,s8_45,s8_46,s8_47,s8_48,s8_49,s8_50,s8_51,s8_52,s8_53,s8_54,s8_55,s8_56,s8_57,s8_58,s8_59,s8_60,s8_61,s8_62,s8_63,s8_64,s8_65,s8_66,s8_67,s8_68,s8_69,s8_70,s8_71,s8_72]
lemma s8_73bx (v : List Sig) (h : (!s8_73b.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_73b := by simpa using h
  simp only [s8_73b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_37x
  · exact s8_38x
  · exact s8_39x
  · exact s8_40x
  · exact s8_41x
  · exact s8_42x
  · exact s8_43x
  · exact s8_44x
  · exact s8_45x
  · exact s8_46x
  · exact s8_47x
  · exact s8_48x
  · exact s8_49x
  · exact s8_50x
  · exact s8_51x
  · exact s8_52x
  · exact s8_53x
  · exact s8_54x
  · exact s8_55x
  · exact s8_56x
  · exact s8_57x
  · exact s8_58x
  · exact s8_59x
  · exact s8_60x
  · exact s8_61x
  · exact s8_62x
  · exact s8_63x
  · exact s8_64x
  · exact s8_65x
  · exact s8_66x
  · exact s8_67x
  · exact s8_68x
  · exact s8_69x
  · exact s8_70x
  · exact s8_71x
  · exact s8_72x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_73x : Impossible 8 0 s8_73 :=
  exclude_step (u := fun _ => true) (b := fun v => !s8_73b.contains v) (by decide +kernel) s8_73ux s8_73bx (by decide +kernel)

def s8_74 : List Sig := [y8_7,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_74x : Impossible 8 0 s8_74 := rotate_impossible sym8_1 (z := s8_73) (by simp only [s8_74,x8_0,x8_1,x8_2,x8_3,x8_4,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_73x

def s8_75 : List Sig := [y8_52,x8_0,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_75x : Impossible 7 0 s8_75 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_76 : List Sig := [y8_52,y8_8,x8_0,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_76x : Impossible 7 0 s8_76 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_77 : List Sig := [y8_53,x8_0,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_77x : Impossible 7 0 s8_77 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_78 : List Sig := [y8_53,y8_8,x8_0,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_78x : Impossible 7 0 s8_78 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_79 : List Sig := [y8_72,x8_1,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_79x : Impossible 7 0 s8_79 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_80 : List Sig := [y8_72,y8_8,x8_1,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_80x : Impossible 7 0 s8_80 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_81 : List Sig := [y8_73,x8_1,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_81x : Impossible 7 0 s8_81 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_82 : List Sig := [y8_73,y8_8,x8_1,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_82x : Impossible 7 0 s8_82 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_83 : List Sig := [y8_88,x8_2,x8_3,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_83x : Impossible 7 0 s8_83 := rotate_impossible sym8_1 (z := s8_79) (by simp only [s8_83,x8_0,x8_1,x8_2,x8_3,x8_4,y8_8,y8_88,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_79x

def s8_84 : List Sig := [y8_88,y8_8,x8_2,x8_3,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_84x : Impossible 7 0 s8_84 := rotate_impossible sym8_1 (z := s8_80) (by simp only [s8_84,x8_0,x8_1,x8_2,x8_3,x8_4,y8_8,y8_88,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_80x

def s8_85 : List Sig := [y8_89,x8_2,x8_3,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_85x : Impossible 7 0 s8_85 := rotate_impossible sym8_1 (z := s8_81) (by simp only [s8_85,x8_0,x8_1,x8_2,x8_3,x8_4,y8_8,y8_89,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_81x

def s8_86 : List Sig := [y8_89,y8_8,x8_2,x8_3,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_86x : Impossible 7 0 s8_86 := rotate_impossible sym8_1 (z := s8_82) (by simp only [s8_86,x8_0,x8_1,x8_2,x8_3,x8_4,y8_8,y8_89,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_82x

def s8_87 : List Sig := [y8_112,x8_4,x8_3,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_87x : Impossible 7 0 s8_87 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_88 : List Sig := [y8_112,y8_8,x8_4,x8_3,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_88x : Impossible 7 0 s8_88 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_89 : List Sig := [y8_113,x8_4,x8_3,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_89x : Impossible 7 0 s8_89 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_90 : List Sig := [y8_113,y8_8,x8_4,x8_3,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_90x : Impossible 7 0 s8_90 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_91 : List Sig := [y8_14,x8_3,x8_0,y8_8,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_91x : Impossible 7 0 s8_91 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_92 : List Sig := [y8_15,x8_3,x8_0,y8_8,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_92x : Impossible 7 0 s8_92 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_93 : List Sig := [y8_20,x8_3,x8_1,y8_8,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_93x : Impossible 7 0 s8_93 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_94 : List Sig := [y8_21,x8_3,x8_1,y8_8,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_94x : Impossible 7 0 s8_94 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_95 : List Sig := [y8_24,x8_3,x8_2,y8_8,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_95x : Impossible 7 0 s8_95 := rotate_impossible sym8_1 (z := s8_93) (by simp only [s8_95,x8_0,x8_1,x8_2,x8_3,x8_4,y8_24,y8_8,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_93x

def s8_96 : List Sig := [y8_25,x8_3,x8_2,y8_8,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_96x : Impossible 7 0 s8_96 := rotate_impossible sym8_1 (z := s8_94) (by simp only [s8_96,x8_0,x8_1,x8_2,x8_3,x8_4,y8_25,y8_8,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_94x

def s8_97 : List Sig := [y8_28,x8_3,x8_4,y8_8,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_97x : Impossible 7 0 s8_97 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_98 : List Sig := [y8_29,x8_3,x8_4,y8_8,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_98x : Impossible 7 0 s8_98 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_99 : List Sig := [y8_10,x8_0,x8_1,y8_8,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_99x : Impossible 7 0 s8_99 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_100 : List Sig := [y8_11,x8_0,x8_1,y8_8,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_100x : Impossible 7 0 s8_100 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_101 : List Sig := [y8_12,x8_0,x8_2,y8_8,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_101x : Impossible 7 0 s8_101 := rotate_impossible sym8_1 (z := s8_99) (by simp only [s8_101,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_8,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_99x

def s8_102 : List Sig := [y8_13,x8_0,x8_2,y8_8,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_102x : Impossible 7 0 s8_102 := rotate_impossible sym8_1 (z := s8_100) (by simp only [s8_102,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_8,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_100x

def s8_103 : List Sig := [y8_16,x8_0,x8_4,y8_8,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_103x : Impossible 7 0 s8_103 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_104 : List Sig := [y8_17,x8_0,x8_4,y8_8,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_104x : Impossible 7 0 s8_104 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_105 : List Sig := [y8_18,x8_1,x8_2,y8_8,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_105x : Impossible 7 0 s8_105 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_106 : List Sig := [y8_19,x8_1,x8_2,y8_8,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_106x : Impossible 7 0 s8_106 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_107 : List Sig := [y8_22,x8_1,x8_4,y8_8,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_107x : Impossible 7 0 s8_107 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_108 : List Sig := [y8_23,x8_1,x8_4,y8_8,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_108x : Impossible 7 0 s8_108 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_109 : List Sig := [y8_26,x8_2,x8_4,y8_8,x8_3,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_109x : Impossible 7 0 s8_109 := rotate_impossible sym8_1 (z := s8_107) (by simp only [s8_109,x8_0,x8_1,x8_2,x8_3,x8_4,y8_26,y8_8,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_107x

def s8_110 : List Sig := [y8_27,x8_2,x8_4,y8_8,x8_3,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_110x : Impossible 7 0 s8_110 := rotate_impossible sym8_1 (z := s8_108) (by simp only [s8_110,x8_0,x8_1,x8_2,x8_3,x8_4,y8_27,y8_8,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_108x

def s8_111 : List Sig := [y8_8,x8_3,x8_0,x8_1,x8_2,x8_4]
lemma s8_111ux (v : List Sig) (h : true = false) : Impossible 7 0 v := Bool.noConfusion h
def s8_111b : List (List Sig) := [s8_75,s8_76,s8_77,s8_78,s8_79,s8_80,s8_81,s8_82,s8_83,s8_84,s8_85,s8_86,s8_87,s8_88,s8_89,s8_90,s8_91,s8_92,s8_93,s8_94,s8_95,s8_96,s8_97,s8_98,s8_99,s8_100,s8_101,s8_102,s8_103,s8_104,s8_105,s8_106,s8_107,s8_108,s8_109,s8_110]
lemma s8_111bx (v : List Sig) (h : (!s8_111b.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_111b := by simpa using h
  simp only [s8_111b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_75x
  · exact s8_76x
  · exact s8_77x
  · exact s8_78x
  · exact s8_79x
  · exact s8_80x
  · exact s8_81x
  · exact s8_82x
  · exact s8_83x
  · exact s8_84x
  · exact s8_85x
  · exact s8_86x
  · exact s8_87x
  · exact s8_88x
  · exact s8_89x
  · exact s8_90x
  · exact s8_91x
  · exact s8_92x
  · exact s8_93x
  · exact s8_94x
  · exact s8_95x
  · exact s8_96x
  · exact s8_97x
  · exact s8_98x
  · exact s8_99x
  · exact s8_100x
  · exact s8_101x
  · exact s8_102x
  · exact s8_103x
  · exact s8_104x
  · exact s8_105x
  · exact s8_106x
  · exact s8_107x
  · exact s8_108x
  · exact s8_109x
  · exact s8_110x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_111x : Impossible 8 0 s8_111 :=
  exclude_step (u := fun _ => true) (b := fun v => !s8_111b.contains v) (by decide +kernel) s8_111ux s8_111bx (by decide +kernel)

def s8_112 : List Sig := [y8_9,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_112x : Impossible 8 0 s8_112 := rotate_impossible sym8_0 (z := s8_111) (by simp only [s8_112,x8_0,x8_1,x8_2,x8_3,x8_4,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_111x

def s8_113 : List Sig := [y8_30,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_113x : Impossible 7 0 s8_113 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_114 : List Sig := [y8_30,y8_10,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_114x : Impossible 7 0 s8_114 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_115 : List Sig := [y8_5,x8_0,y8_10,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_115x : Impossible 7 0 s8_115 := impPerm (z := s8_16) (by decide +kernel) s8_16x

def s8_116 : List Sig := [y8_6,x8_1,y8_10,x8_0,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_116x : Impossible 7 0 s8_116 := impPerm (z := s8_53) (by decide +kernel) s8_53x

def s8_117 : List Sig := [y8_7,x8_2,y8_10,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_117x : Impossible 7 0 s8_117 := rotate_impossible sym8_1 (z := s8_61) (by simp only [s8_117,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_61x

def s8_118 : List Sig := [y8_8,x8_3,y8_10,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_118x : Impossible 7 0 s8_118 := impPerm (z := s8_99) (by decide +kernel) s8_99x

def s8_119 : List Sig := [y8_9,x8_4,y8_10,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_119x : Impossible 7 0 s8_119 := rotate_impossible sym8_0 (z := s8_99) (by simp only [s8_119,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_99x

def s8_120 : List Sig := [y8_54,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_120x : Impossible 7 1 s8_120 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_121 : List Sig := [y8_54,y8_10,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_121x : Impossible 7 1 s8_121 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_122 : List Sig := [y8_90,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_122x : Impossible 7 1 s8_122 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_123 : List Sig := [y8_90,y8_10,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_123x : Impossible 7 1 s8_123 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_124 : List Sig := [y8_58,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_124x : Impossible 7 1 s8_124 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_125 : List Sig := [y8_58,y8_10,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_125x : Impossible 7 1 s8_125 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_126 : List Sig := [y8_104,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_126x : Impossible 7 1 s8_126 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_127 : List Sig := [y8_104,y8_10,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_127x : Impossible 7 1 s8_127 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_128 : List Sig := [y8_62,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_128x : Impossible 7 1 s8_128 := rotate_impossible sym8_0 (z := s8_124) (by simp only [s8_128,x8_0,x8_1,x8_2,x8_3,x8_4,y8_22,y8_62,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_124x

def s8_129 : List Sig := [y8_62,y8_10,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_129x : Impossible 7 1 s8_129 := rotate_impossible sym8_0 (z := s8_125) (by simp only [s8_129,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_22,y8_62,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_125x

def s8_130 : List Sig := [y8_114,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_130x : Impossible 7 1 s8_130 := rotate_impossible sym8_0 (z := s8_126) (by simp only [s8_130,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_114,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_126x

def s8_131 : List Sig := [y8_114,y8_10,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_131x : Impossible 7 1 s8_131 := rotate_impossible sym8_0 (z := s8_127) (by simp only [s8_131,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_114,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_127x

def s8_132 : List Sig := [y8_11,x8_0,y8_10,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_132x : Impossible 7 1 s8_132 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_133 : List Sig := [y8_11,x8_1,y8_10,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_133x : Impossible 7 1 s8_133 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_134 : List Sig := [y8_11,x8_0,x8_1,y8_10,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_134x : Impossible 7 1 s8_134 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_135 : List Sig := [y8_12,x8_0,x8_2,y8_10,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_135x : Impossible 7 1 s8_135 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_136 : List Sig := [y8_13,x8_0,x8_2,y8_10,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_136x : Impossible 7 1 s8_136 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_137 : List Sig := [y8_14,x8_0,x8_3,y8_10,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_137x : Impossible 7 1 s8_137 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_138 : List Sig := [y8_15,x8_0,x8_3,y8_10,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_138x : Impossible 7 1 s8_138 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_139 : List Sig := [y8_16,x8_0,x8_4,y8_10,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_139x : Impossible 7 1 s8_139 := rotate_impossible sym8_0 (z := s8_137) (by simp only [s8_139,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_16,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_137x

def s8_140 : List Sig := [y8_17,x8_0,x8_4,y8_10,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_140x : Impossible 7 1 s8_140 := rotate_impossible sym8_0 (z := s8_138) (by simp only [s8_140,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_17,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_138x

def s8_141 : List Sig := [y8_18,x8_2,y8_10,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_141x : Impossible 7 1 s8_141 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_142 : List Sig := [y8_18,x8_1,x8_2,y8_10,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_142x : Impossible 7 1 s8_142 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_143 : List Sig := [y8_19,x8_1,x8_2,y8_10,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_143x : Impossible 7 1 s8_143 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_144 : List Sig := [y8_20,x8_1,x8_3,y8_10,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_144x : Impossible 7 1 s8_144 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_145 : List Sig := [y8_21,x8_1,x8_3,y8_10,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_145x : Impossible 7 1 s8_145 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_146 : List Sig := [y8_22,x8_1,x8_4,y8_10,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_146x : Impossible 7 1 s8_146 := rotate_impossible sym8_0 (z := s8_144) (by simp only [s8_146,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_22,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_144x

def s8_147 : List Sig := [y8_23,x8_1,x8_4,y8_10,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_147x : Impossible 7 1 s8_147 := rotate_impossible sym8_0 (z := s8_145) (by simp only [s8_147,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_23,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_145x

def s8_148 : List Sig := [y8_24,x8_2,x8_3,y8_10,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_148x : Impossible 7 1 s8_148 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_149 : List Sig := [y8_25,x8_2,x8_3,y8_10,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_149x : Impossible 7 1 s8_149 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_150 : List Sig := [y8_26,x8_2,x8_4,y8_10,x8_0,x8_1,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_150x : Impossible 7 1 s8_150 := rotate_impossible sym8_0 (z := s8_148) (by simp only [s8_150,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_26,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_148x

def s8_151 : List Sig := [y8_27,x8_2,x8_4,y8_10,x8_0,x8_1,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_151x : Impossible 7 1 s8_151 := rotate_impossible sym8_0 (z := s8_149) (by simp only [s8_151,x8_0,x8_1,x8_2,x8_3,x8_4,y8_10,y8_27,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_149x

def s8_152 : List Sig := [y8_28,x8_3,x8_4,y8_10,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_152x : Impossible 7 1 s8_152 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_153 : List Sig := [y8_29,x8_3,x8_4,y8_10,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_153x : Impossible 7 1 s8_153 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_154 : List Sig := [y8_10,x8_0,x8_1,x8_2,x8_3,x8_4]
def s8_154u : List (List Sig) := [s8_113,s8_114,s8_115,s8_116,s8_117,s8_118,s8_119]
lemma s8_154ux (v : List Sig) (h : (!s8_154u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_154u := by simpa using h
  simp only [s8_154u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_113x
  · exact s8_114x
  · exact s8_115x
  · exact s8_116x
  · exact s8_117x
  · exact s8_118x
  · exact s8_119x
def s8_154b : List (List Sig) := [s8_120,s8_121,s8_122,s8_123,s8_124,s8_125,s8_126,s8_127,s8_128,s8_129,s8_130,s8_131,s8_132,s8_133,s8_134,s8_135,s8_136,s8_137,s8_138,s8_139,s8_140,s8_141,s8_142,s8_143,s8_144,s8_145,s8_146,s8_147,s8_148,s8_149,s8_150,s8_151,s8_152,s8_153]
lemma s8_154bx (v : List Sig) (h : (!s8_154b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_154b := by simpa using h
  simp only [s8_154b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_120x
  · exact s8_121x
  · exact s8_122x
  · exact s8_123x
  · exact s8_124x
  · exact s8_125x
  · exact s8_126x
  · exact s8_127x
  · exact s8_128x
  · exact s8_129x
  · exact s8_130x
  · exact s8_131x
  · exact s8_132x
  · exact s8_133x
  · exact s8_134x
  · exact s8_135x
  · exact s8_136x
  · exact s8_137x
  · exact s8_138x
  · exact s8_139x
  · exact s8_140x
  · exact s8_141x
  · exact s8_142x
  · exact s8_143x
  · exact s8_144x
  · exact s8_145x
  · exact s8_146x
  · exact s8_147x
  · exact s8_148x
  · exact s8_149x
  · exact s8_150x
  · exact s8_151x
  · exact s8_152x
  · exact s8_153x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_154x : Impossible 8 1 s8_154 :=
  exclude_step (u := fun v => !s8_154u.contains v) (b := fun v => !s8_154b.contains v) (by decide +kernel) s8_154ux s8_154bx (by decide +kernel)

def s8_155 : List Sig := [y8_31,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_155x : Impossible 7 0 s8_155 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_156 : List Sig := [y8_31,y8_11,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_156x : Impossible 7 0 s8_156 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_157 : List Sig := [y8_5,x8_0,y8_11,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_157x : Impossible 7 0 s8_157 := impPerm (z := s8_17) (by decide +kernel) s8_17x

def s8_158 : List Sig := [y8_6,x8_1,y8_11,x8_0,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_158x : Impossible 7 0 s8_158 := impPerm (z := s8_54) (by decide +kernel) s8_54x

def s8_159 : List Sig := [y8_7,x8_2,y8_11,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_159x : Impossible 7 0 s8_159 := rotate_impossible sym8_1 (z := s8_62) (by simp only [s8_159,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_62x

def s8_160 : List Sig := [y8_8,x8_3,y8_11,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_160x : Impossible 7 0 s8_160 := impPerm (z := s8_100) (by decide +kernel) s8_100x

def s8_161 : List Sig := [y8_9,x8_4,y8_11,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_161x : Impossible 7 0 s8_161 := rotate_impossible sym8_0 (z := s8_100) (by simp only [s8_161,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_100x

def s8_162 : List Sig := [y8_91,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_162x : Impossible 7 1 s8_162 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_163 : List Sig := [y8_91,y8_11,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_163x : Impossible 7 1 s8_163 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_164 : List Sig := [y8_91,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_164x : Impossible 7 1 s8_164 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_165 : List Sig := [y8_91,y8_11,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_165x : Impossible 7 1 s8_165 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_166 : List Sig := [y8_57,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_166x : Impossible 7 1 s8_166 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_167 : List Sig := [y8_57,y8_11,x8_2,x8_0,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_167x : Impossible 7 1 s8_167 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_168 : List Sig := [y8_105,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_168x : Impossible 7 1 s8_168 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_169 : List Sig := [y8_105,y8_11,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_169x : Impossible 7 1 s8_169 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_170 : List Sig := [y8_105,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_170x : Impossible 7 1 s8_170 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_171 : List Sig := [y8_105,y8_11,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_171x : Impossible 7 1 s8_171 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_172 : List Sig := [y8_61,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_172x : Impossible 7 1 s8_172 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_173 : List Sig := [y8_61,y8_11,x8_3,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_173x : Impossible 7 1 s8_173 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_174 : List Sig := [y8_115,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_174x : Impossible 7 1 s8_174 := rotate_impossible sym8_0 (z := s8_168) (by simp only [s8_174,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_115,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_168x

def s8_175 : List Sig := [y8_115,y8_11,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_175x : Impossible 7 1 s8_175 := rotate_impossible sym8_0 (z := s8_169) (by simp only [s8_175,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_115,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_169x

def s8_176 : List Sig := [y8_115,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_176x : Impossible 7 1 s8_176 := rotate_impossible sym8_0 (z := s8_170) (by simp only [s8_176,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_115,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_170x

def s8_177 : List Sig := [y8_115,y8_11,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_177x : Impossible 7 1 s8_177 := rotate_impossible sym8_0 (z := s8_171) (by simp only [s8_177,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_115,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_171x

def s8_178 : List Sig := [y8_63,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_178x : Impossible 7 1 s8_178 := rotate_impossible sym8_0 (z := s8_172) (by simp only [s8_178,x8_0,x8_1,x8_2,x8_3,x8_4,y8_23,y8_63,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_172x

def s8_179 : List Sig := [y8_63,y8_11,x8_4,x8_0,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_179x : Impossible 7 1 s8_179 := rotate_impossible sym8_0 (z := s8_173) (by simp only [s8_179,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_23,y8_63,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_173x

def s8_180 : List Sig := [y8_10,x8_0,y8_11,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_180x : Impossible 7 1 s8_180 := impPerm (z := s8_132) (by decide +kernel) s8_132x

def s8_181 : List Sig := [y8_10,x8_1,y8_11,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_181x : Impossible 7 1 s8_181 := impPerm (z := s8_133) (by decide +kernel) s8_133x

def s8_182 : List Sig := [y8_10,x8_0,x8_1,y8_11,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_182x : Impossible 7 1 s8_182 := impPerm (z := s8_134) (by decide +kernel) s8_134x

def s8_183 : List Sig := [y8_12,x8_0,x8_2,y8_11,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_183x : Impossible 7 1 s8_183 := rotate_impossible sym8_1 (z := s8_136) (by simp only [s8_183,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_12,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_136x

def s8_184 : List Sig := [y8_13,x8_0,x8_2,y8_11,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_184x : Impossible 7 1 s8_184 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_185 : List Sig := [y8_14,x8_0,x8_3,y8_11,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_185x : Impossible 7 1 s8_185 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_186 : List Sig := [y8_15,x8_0,x8_3,y8_11,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_186x : Impossible 7 1 s8_186 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_187 : List Sig := [y8_16,x8_0,x8_4,y8_11,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_187x : Impossible 7 1 s8_187 := rotate_impossible sym8_0 (z := s8_185) (by simp only [s8_187,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_16,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_185x

def s8_188 : List Sig := [y8_17,x8_0,x8_4,y8_11,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_188x : Impossible 7 1 s8_188 := rotate_impossible sym8_0 (z := s8_186) (by simp only [s8_188,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_17,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_186x

def s8_189 : List Sig := [y8_18,x8_1,x8_2,y8_11,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_189x : Impossible 7 1 s8_189 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_190 : List Sig := [y8_19,x8_1,x8_2,y8_11,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_190x : Impossible 7 1 s8_190 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_191 : List Sig := [y8_20,x8_1,x8_3,y8_11,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_191x : Impossible 7 1 s8_191 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_192 : List Sig := [y8_21,x8_1,x8_3,y8_11,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_192x : Impossible 7 1 s8_192 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_193 : List Sig := [y8_22,x8_1,x8_4,y8_11,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_193x : Impossible 7 1 s8_193 := rotate_impossible sym8_0 (z := s8_191) (by simp only [s8_193,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_22,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_191x

def s8_194 : List Sig := [y8_23,x8_1,x8_4,y8_11,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_194x : Impossible 7 1 s8_194 := rotate_impossible sym8_0 (z := s8_192) (by simp only [s8_194,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_23,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_192x

def s8_195 : List Sig := [y8_24,x8_2,x8_3,y8_11,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_195x : Impossible 7 1 s8_195 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_196 : List Sig := [y8_25,x8_2,x8_3,y8_11,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_196x : Impossible 7 1 s8_196 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_197 : List Sig := [y8_26,x8_2,x8_4,y8_11,x8_0,x8_1,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_197x : Impossible 7 1 s8_197 := rotate_impossible sym8_0 (z := s8_195) (by simp only [s8_197,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_26,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_195x

def s8_198 : List Sig := [y8_27,x8_2,x8_4,y8_11,x8_0,x8_1,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_198x : Impossible 7 1 s8_198 := rotate_impossible sym8_0 (z := s8_196) (by simp only [s8_198,x8_0,x8_1,x8_2,x8_3,x8_4,y8_11,y8_27,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_196x

def s8_199 : List Sig := [y8_28,x8_3,x8_4,y8_11,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_199x : Impossible 7 1 s8_199 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_200 : List Sig := [y8_29,x8_3,x8_4,y8_11,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_200x : Impossible 7 1 s8_200 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_201 : List Sig := [y8_11,x8_0,x8_1,x8_2,x8_3,x8_4]
def s8_201u : List (List Sig) := [s8_155,s8_156,s8_157,s8_158,s8_159,s8_160,s8_161]
lemma s8_201ux (v : List Sig) (h : (!s8_201u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_201u := by simpa using h
  simp only [s8_201u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_155x
  · exact s8_156x
  · exact s8_157x
  · exact s8_158x
  · exact s8_159x
  · exact s8_160x
  · exact s8_161x
def s8_201b : List (List Sig) := [s8_162,s8_163,s8_164,s8_165,s8_166,s8_167,s8_168,s8_169,s8_170,s8_171,s8_172,s8_173,s8_174,s8_175,s8_176,s8_177,s8_178,s8_179,s8_180,s8_181,s8_182,s8_183,s8_184,s8_185,s8_186,s8_187,s8_188,s8_189,s8_190,s8_191,s8_192,s8_193,s8_194,s8_195,s8_196,s8_197,s8_198,s8_199,s8_200]
lemma s8_201bx (v : List Sig) (h : (!s8_201b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_201b := by simpa using h
  simp only [s8_201b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_162x
  · exact s8_163x
  · exact s8_164x
  · exact s8_165x
  · exact s8_166x
  · exact s8_167x
  · exact s8_168x
  · exact s8_169x
  · exact s8_170x
  · exact s8_171x
  · exact s8_172x
  · exact s8_173x
  · exact s8_174x
  · exact s8_175x
  · exact s8_176x
  · exact s8_177x
  · exact s8_178x
  · exact s8_179x
  · exact s8_180x
  · exact s8_181x
  · exact s8_182x
  · exact s8_183x
  · exact s8_184x
  · exact s8_185x
  · exact s8_186x
  · exact s8_187x
  · exact s8_188x
  · exact s8_189x
  · exact s8_190x
  · exact s8_191x
  · exact s8_192x
  · exact s8_193x
  · exact s8_194x
  · exact s8_195x
  · exact s8_196x
  · exact s8_197x
  · exact s8_198x
  · exact s8_199x
  · exact s8_200x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_201x : Impossible 8 1 s8_201 :=
  exclude_step (u := fun v => !s8_201u.contains v) (b := fun v => !s8_201b.contains v) (by decide +kernel) s8_201ux s8_201bx (by decide +kernel)

def s8_202 : List Sig := [y8_12,x8_0,x8_2,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_202x : Impossible 8 1 s8_202 := rotate_impossible sym8_1 (z := s8_154) (by simp only [s8_202,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_154x

def s8_203 : List Sig := [y8_13,x8_0,x8_2,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_203x : Impossible 8 1 s8_203 := rotate_impossible sym8_1 (z := s8_201) (by simp only [s8_203,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_201x

def s8_204 : List Sig := [y8_34,x8_0,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_204x : Impossible 7 0 s8_204 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_205 : List Sig := [y8_34,y8_14,x8_0,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_205x : Impossible 7 0 s8_205 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_206 : List Sig := [y8_5,x8_0,y8_14,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_206x : Impossible 7 0 s8_206 := impPerm (z := s8_20) (by decide +kernel) s8_20x

def s8_207 : List Sig := [y8_8,x8_3,y8_14,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_207x : Impossible 7 0 s8_207 := impPerm (z := s8_91) (by decide +kernel) s8_91x

def s8_208 : List Sig := [y8_6,x8_1,y8_14,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_208x : Impossible 7 0 s8_208 := impPerm (z := s8_63) (by decide +kernel) s8_63x

def s8_209 : List Sig := [y8_7,x8_2,y8_14,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_209x : Impossible 7 0 s8_209 := rotate_impossible sym8_1 (z := s8_63) (by simp only [s8_209,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_63x

def s8_210 : List Sig := [y8_9,x8_4,y8_14,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_210x : Impossible 7 0 s8_210 := rotate_impossible sym8_0 (z := s8_103) (by simp only [s8_210,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_103x

def s8_211 : List Sig := [y8_58,x8_1,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_211x : Impossible 7 1 s8_211 := impPerm (z := s8_124) (by decide +kernel) s8_124x

def s8_212 : List Sig := [y8_58,y8_14,x8_1,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_212x : Impossible 7 1 s8_212 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_213 : List Sig := [y8_74,x8_1,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_213x : Impossible 7 1 s8_213 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_214 : List Sig := [y8_74,y8_14,x8_1,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_214x : Impossible 7 1 s8_214 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_215 : List Sig := [y8_64,x8_2,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_215x : Impossible 7 1 s8_215 := rotate_impossible sym8_1 (z := s8_124) (by simp only [s8_215,x8_0,x8_1,x8_2,x8_3,x8_4,y8_24,y8_64,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_124x

def s8_216 : List Sig := [y8_64,y8_14,x8_2,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_216x : Impossible 7 1 s8_216 := rotate_impossible sym8_1 (z := s8_212) (by simp only [s8_216,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_24,y8_64,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_212x

def s8_217 : List Sig := [y8_92,x8_2,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_217x : Impossible 7 1 s8_217 := rotate_impossible sym8_1 (z := s8_213) (by simp only [s8_217,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_92,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_213x

def s8_218 : List Sig := [y8_92,y8_14,x8_2,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_218x : Impossible 7 1 s8_218 := rotate_impossible sym8_1 (z := s8_214) (by simp only [s8_218,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_92,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_214x

def s8_219 : List Sig := [y8_66,x8_4,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_219x : Impossible 7 1 s8_219 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_220 : List Sig := [y8_66,y8_14,x8_4,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_220x : Impossible 7 1 s8_220 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_221 : List Sig := [y8_116,x8_4,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_221x : Impossible 7 1 s8_221 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_222 : List Sig := [y8_116,y8_14,x8_4,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_222x : Impossible 7 1 s8_222 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_223 : List Sig := [y8_15,x8_0,y8_14,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_223x : Impossible 7 1 s8_223 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_224 : List Sig := [y8_15,x8_3,y8_14,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_224x : Impossible 7 1 s8_224 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_225 : List Sig := [y8_15,x8_0,x8_3,y8_14,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_225x : Impossible 7 1 s8_225 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_226 : List Sig := [y8_10,x8_0,x8_1,y8_14,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_226x : Impossible 7 1 s8_226 := impPerm (z := s8_137) (by decide +kernel) s8_137x

def s8_227 : List Sig := [y8_11,x8_0,x8_1,y8_14,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_227x : Impossible 7 1 s8_227 := impPerm (z := s8_185) (by decide +kernel) s8_185x

def s8_228 : List Sig := [y8_12,x8_0,x8_2,y8_14,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_228x : Impossible 7 1 s8_228 := rotate_impossible sym8_1 (z := s8_137) (by simp only [s8_228,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_14,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_137x

def s8_229 : List Sig := [y8_13,x8_0,x8_2,y8_14,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_229x : Impossible 7 1 s8_229 := rotate_impossible sym8_1 (z := s8_185) (by simp only [s8_229,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_14,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_185x

def s8_230 : List Sig := [y8_16,x8_0,x8_4,y8_14,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_230x : Impossible 7 1 s8_230 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_231 : List Sig := [y8_17,x8_0,x8_4,y8_14,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_231x : Impossible 7 1 s8_231 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_232 : List Sig := [y8_20,x8_1,y8_14,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_232x : Impossible 7 1 s8_232 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_233 : List Sig := [y8_20,x8_3,x8_1,y8_14,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_233x : Impossible 7 1 s8_233 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_234 : List Sig := [y8_21,x8_3,x8_1,y8_14,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_234x : Impossible 7 1 s8_234 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_235 : List Sig := [y8_24,x8_2,y8_14,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_235x : Impossible 7 1 s8_235 := rotate_impossible sym8_1 (z := s8_232) (by simp only [s8_235,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_24,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_232x

def s8_236 : List Sig := [y8_24,x8_3,x8_2,y8_14,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_236x : Impossible 7 1 s8_236 := rotate_impossible sym8_1 (z := s8_233) (by simp only [s8_236,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_24,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_233x

def s8_237 : List Sig := [y8_25,x8_3,x8_2,y8_14,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_237x : Impossible 7 1 s8_237 := rotate_impossible sym8_1 (z := s8_234) (by simp only [s8_237,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_25,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_234x

def s8_238 : List Sig := [y8_28,x8_3,x8_4,y8_14,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_238x : Impossible 7 1 s8_238 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_239 : List Sig := [y8_29,x8_4,y8_14,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_239x : Impossible 7 1 s8_239 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_240 : List Sig := [y8_29,x8_3,x8_4,y8_14,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_240x : Impossible 7 1 s8_240 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_241 : List Sig := [y8_18,x8_1,x8_2,y8_14,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_241x : Impossible 7 1 s8_241 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_242 : List Sig := [y8_19,x8_1,x8_2,y8_14,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_242x : Impossible 7 1 s8_242 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_243 : List Sig := [y8_22,x8_1,x8_4,y8_14,x8_0,x8_3,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_243x : Impossible 7 1 s8_243 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_244 : List Sig := [y8_23,x8_1,x8_4,y8_14,x8_0,x8_3,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_244x : Impossible 7 1 s8_244 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_245 : List Sig := [y8_26,x8_2,x8_4,y8_14,x8_0,x8_3,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_245x : Impossible 7 1 s8_245 := rotate_impossible sym8_1 (z := s8_243) (by simp only [s8_245,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_26,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_243x

def s8_246 : List Sig := [y8_27,x8_2,x8_4,y8_14,x8_0,x8_3,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_246x : Impossible 7 1 s8_246 := rotate_impossible sym8_1 (z := s8_244) (by simp only [s8_246,x8_0,x8_1,x8_2,x8_3,x8_4,y8_14,y8_27,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_244x

def s8_247 : List Sig := [y8_14,x8_0,x8_3,x8_1,x8_2,x8_4]
def s8_247u : List (List Sig) := [s8_204,s8_205,s8_206,s8_207,s8_208,s8_209,s8_210]
lemma s8_247ux (v : List Sig) (h : (!s8_247u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_247u := by simpa using h
  simp only [s8_247u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_204x
  · exact s8_205x
  · exact s8_206x
  · exact s8_207x
  · exact s8_208x
  · exact s8_209x
  · exact s8_210x
def s8_247b : List (List Sig) := [s8_211,s8_212,s8_213,s8_214,s8_215,s8_216,s8_217,s8_218,s8_219,s8_220,s8_221,s8_222,s8_223,s8_224,s8_225,s8_226,s8_227,s8_228,s8_229,s8_230,s8_231,s8_232,s8_233,s8_234,s8_235,s8_236,s8_237,s8_238,s8_239,s8_240,s8_241,s8_242,s8_243,s8_244,s8_245,s8_246]
lemma s8_247bx (v : List Sig) (h : (!s8_247b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_247b := by simpa using h
  simp only [s8_247b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_211x
  · exact s8_212x
  · exact s8_213x
  · exact s8_214x
  · exact s8_215x
  · exact s8_216x
  · exact s8_217x
  · exact s8_218x
  · exact s8_219x
  · exact s8_220x
  · exact s8_221x
  · exact s8_222x
  · exact s8_223x
  · exact s8_224x
  · exact s8_225x
  · exact s8_226x
  · exact s8_227x
  · exact s8_228x
  · exact s8_229x
  · exact s8_230x
  · exact s8_231x
  · exact s8_232x
  · exact s8_233x
  · exact s8_234x
  · exact s8_235x
  · exact s8_236x
  · exact s8_237x
  · exact s8_238x
  · exact s8_239x
  · exact s8_240x
  · exact s8_241x
  · exact s8_242x
  · exact s8_243x
  · exact s8_244x
  · exact s8_245x
  · exact s8_246x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_247x : Impossible 8 1 s8_247 :=
  exclude_step (u := fun v => !s8_247u.contains v) (b := fun v => !s8_247b.contains v) (by decide +kernel) s8_247ux s8_247bx (by decide +kernel)

def s8_248 : List Sig := [y8_35,x8_0,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_248x : Impossible 7 0 s8_248 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_249 : List Sig := [y8_35,y8_15,x8_0,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_249x : Impossible 7 0 s8_249 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_250 : List Sig := [y8_5,x8_0,y8_15,x8_3,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_250x : Impossible 7 0 s8_250 := impPerm (z := s8_21) (by decide +kernel) s8_21x

def s8_251 : List Sig := [y8_8,x8_3,y8_15,x8_0,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_251x : Impossible 7 0 s8_251 := impPerm (z := s8_92) (by decide +kernel) s8_92x

def s8_252 : List Sig := [y8_6,x8_1,y8_15,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_252x : Impossible 7 0 s8_252 := impPerm (z := s8_64) (by decide +kernel) s8_64x

def s8_253 : List Sig := [y8_7,x8_2,y8_15,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_253x : Impossible 7 0 s8_253 := rotate_impossible sym8_1 (z := s8_64) (by simp only [s8_253,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_64x

def s8_254 : List Sig := [y8_9,x8_4,y8_15,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_254x : Impossible 7 0 s8_254 := rotate_impossible sym8_0 (z := s8_104) (by simp only [s8_254,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_104x

def s8_255 : List Sig := [y8_75,x8_1,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_255x : Impossible 7 1 s8_255 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_256 : List Sig := [y8_75,y8_15,x8_1,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_256x : Impossible 7 1 s8_256 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_257 : List Sig := [y8_61,x8_1,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_257x : Impossible 7 1 s8_257 := impPerm (z := s8_172) (by decide +kernel) s8_172x

def s8_258 : List Sig := [y8_61,y8_15,x8_1,x8_0,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_258x : Impossible 7 1 s8_258 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_259 : List Sig := [y8_93,x8_2,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_259x : Impossible 7 1 s8_259 := rotate_impossible sym8_1 (z := s8_255) (by simp only [s8_259,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_93,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_255x

def s8_260 : List Sig := [y8_93,y8_15,x8_2,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_260x : Impossible 7 1 s8_260 := rotate_impossible sym8_1 (z := s8_256) (by simp only [s8_260,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_93,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_256x

def s8_261 : List Sig := [y8_65,x8_2,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_261x : Impossible 7 1 s8_261 := rotate_impossible sym8_1 (z := s8_172) (by simp only [s8_261,x8_0,x8_1,x8_2,x8_3,x8_4,y8_25,y8_65,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_172x

def s8_262 : List Sig := [y8_65,y8_15,x8_2,x8_0,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_262x : Impossible 7 1 s8_262 := rotate_impossible sym8_1 (z := s8_258) (by simp only [s8_262,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_25,y8_65,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_258x

def s8_263 : List Sig := [y8_117,x8_4,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_263x : Impossible 7 1 s8_263 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_264 : List Sig := [y8_117,y8_15,x8_4,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_264x : Impossible 7 1 s8_264 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_265 : List Sig := [y8_69,x8_4,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_265x : Impossible 7 1 s8_265 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_266 : List Sig := [y8_69,y8_15,x8_4,x8_0,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_266x : Impossible 7 1 s8_266 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_267 : List Sig := [y8_14,x8_0,y8_15,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_267x : Impossible 7 1 s8_267 := impPerm (z := s8_223) (by decide +kernel) s8_223x

def s8_268 : List Sig := [y8_14,x8_3,y8_15,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_268x : Impossible 7 1 s8_268 := impPerm (z := s8_224) (by decide +kernel) s8_224x

def s8_269 : List Sig := [y8_14,x8_0,x8_3,y8_15,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_269x : Impossible 7 1 s8_269 := impPerm (z := s8_225) (by decide +kernel) s8_225x

def s8_270 : List Sig := [y8_10,x8_0,x8_1,y8_15,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_270x : Impossible 7 1 s8_270 := impPerm (z := s8_138) (by decide +kernel) s8_138x

def s8_271 : List Sig := [y8_11,x8_0,x8_1,y8_15,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_271x : Impossible 7 1 s8_271 := impPerm (z := s8_186) (by decide +kernel) s8_186x

def s8_272 : List Sig := [y8_12,x8_0,x8_2,y8_15,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_272x : Impossible 7 1 s8_272 := rotate_impossible sym8_1 (z := s8_138) (by simp only [s8_272,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_15,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_138x

def s8_273 : List Sig := [y8_13,x8_0,x8_2,y8_15,x8_3,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_273x : Impossible 7 1 s8_273 := rotate_impossible sym8_1 (z := s8_186) (by simp only [s8_273,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_15,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_186x

def s8_274 : List Sig := [y8_16,x8_0,x8_4,y8_15,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_274x : Impossible 7 1 s8_274 := rotate_impossible sym8_0 (z := s8_231) (by simp only [s8_274,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_16,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_231x

def s8_275 : List Sig := [y8_17,x8_0,x8_4,y8_15,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_275x : Impossible 7 1 s8_275 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_276 : List Sig := [y8_20,x8_3,x8_1,y8_15,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_276x : Impossible 7 1 s8_276 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_277 : List Sig := [y8_21,x8_3,x8_1,y8_15,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_277x : Impossible 7 1 s8_277 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_278 : List Sig := [y8_24,x8_3,x8_2,y8_15,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_278x : Impossible 7 1 s8_278 := rotate_impossible sym8_1 (z := s8_276) (by simp only [s8_278,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_24,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_276x

def s8_279 : List Sig := [y8_25,x8_3,x8_2,y8_15,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_279x : Impossible 7 1 s8_279 := rotate_impossible sym8_1 (z := s8_277) (by simp only [s8_279,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_25,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_277x

def s8_280 : List Sig := [y8_28,x8_3,x8_4,y8_15,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_280x : Impossible 7 1 s8_280 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_281 : List Sig := [y8_29,x8_3,x8_4,y8_15,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_281x : Impossible 7 1 s8_281 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_282 : List Sig := [y8_18,x8_1,x8_2,y8_15,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_282x : Impossible 7 1 s8_282 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_283 : List Sig := [y8_19,x8_1,x8_2,y8_15,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_283x : Impossible 7 1 s8_283 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_284 : List Sig := [y8_22,x8_1,x8_4,y8_15,x8_0,x8_3,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_284x : Impossible 7 1 s8_284 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_285 : List Sig := [y8_23,x8_1,x8_4,y8_15,x8_0,x8_3,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_285x : Impossible 7 1 s8_285 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_286 : List Sig := [y8_26,x8_2,x8_4,y8_15,x8_0,x8_3,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_286x : Impossible 7 1 s8_286 := rotate_impossible sym8_1 (z := s8_284) (by simp only [s8_286,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_26,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_284x

def s8_287 : List Sig := [y8_27,x8_2,x8_4,y8_15,x8_0,x8_3,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_287x : Impossible 7 1 s8_287 := rotate_impossible sym8_1 (z := s8_285) (by simp only [s8_287,x8_0,x8_1,x8_2,x8_3,x8_4,y8_15,y8_27,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_285x

def s8_288 : List Sig := [y8_15,x8_0,x8_3,x8_1,x8_2,x8_4]
def s8_288u : List (List Sig) := [s8_248,s8_249,s8_250,s8_251,s8_252,s8_253,s8_254]
lemma s8_288ux (v : List Sig) (h : (!s8_288u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_288u := by simpa using h
  simp only [s8_288u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_248x
  · exact s8_249x
  · exact s8_250x
  · exact s8_251x
  · exact s8_252x
  · exact s8_253x
  · exact s8_254x
def s8_288b : List (List Sig) := [s8_255,s8_256,s8_257,s8_258,s8_259,s8_260,s8_261,s8_262,s8_263,s8_264,s8_265,s8_266,s8_267,s8_268,s8_269,s8_270,s8_271,s8_272,s8_273,s8_274,s8_275,s8_276,s8_277,s8_278,s8_279,s8_280,s8_281,s8_282,s8_283,s8_284,s8_285,s8_286,s8_287]
lemma s8_288bx (v : List Sig) (h : (!s8_288b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_288b := by simpa using h
  simp only [s8_288b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_255x
  · exact s8_256x
  · exact s8_257x
  · exact s8_258x
  · exact s8_259x
  · exact s8_260x
  · exact s8_261x
  · exact s8_262x
  · exact s8_263x
  · exact s8_264x
  · exact s8_265x
  · exact s8_266x
  · exact s8_267x
  · exact s8_268x
  · exact s8_269x
  · exact s8_270x
  · exact s8_271x
  · exact s8_272x
  · exact s8_273x
  · exact s8_274x
  · exact s8_275x
  · exact s8_276x
  · exact s8_277x
  · exact s8_278x
  · exact s8_279x
  · exact s8_280x
  · exact s8_281x
  · exact s8_282x
  · exact s8_283x
  · exact s8_284x
  · exact s8_285x
  · exact s8_286x
  · exact s8_287x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_288x : Impossible 8 1 s8_288 :=
  exclude_step (u := fun v => !s8_288u.contains v) (b := fun v => !s8_288b.contains v) (by decide +kernel) s8_288ux s8_288bx (by decide +kernel)

def s8_289 : List Sig := [y8_16,x8_0,x8_4,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_289x : Impossible 8 1 s8_289 := rotate_impossible sym8_0 (z := s8_247) (by simp only [s8_289,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_247x

def s8_290 : List Sig := [y8_17,x8_0,x8_4,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_290x : Impossible 8 1 s8_290 := rotate_impossible sym8_0 (z := s8_288) (by simp only [s8_290,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_288x

def s8_291 : List Sig := [y8_38,x8_1,x8_2,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_291x : Impossible 7 0 s8_291 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_292 : List Sig := [y8_38,y8_18,x8_1,x8_2,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_292x : Impossible 7 0 s8_292 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_293 : List Sig := [y8_6,x8_1,y8_18,x8_2,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_293x : Impossible 7 0 s8_293 := impPerm (z := s8_55) (by decide +kernel) s8_55x

def s8_294 : List Sig := [y8_7,x8_2,y8_18,x8_1,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_294x : Impossible 7 0 s8_294 := rotate_impossible sym8_1 (z := s8_55) (by simp only [s8_294,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_55x

def s8_295 : List Sig := [y8_5,x8_0,y8_18,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_295x : Impossible 7 0 s8_295 := impPerm (z := s8_24) (by decide +kernel) s8_24x

def s8_296 : List Sig := [y8_8,x8_3,y8_18,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_296x : Impossible 7 0 s8_296 := impPerm (z := s8_105) (by decide +kernel) s8_105x

def s8_297 : List Sig := [y8_9,x8_4,y8_18,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_297x : Impossible 7 0 s8_297 := rotate_impossible sym8_0 (z := s8_105) (by simp only [s8_297,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_105x

def s8_298 : List Sig := [y8_54,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_298x : Impossible 7 1 s8_298 := impPerm (z := s8_120) (by decide +kernel) s8_120x

def s8_299 : List Sig := [y8_54,y8_18,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_299x : Impossible 7 1 s8_299 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_300 : List Sig := [y8_55,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_300x : Impossible 7 1 s8_300 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_301 : List Sig := [y8_55,y8_18,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_301x : Impossible 7 1 s8_301 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_302 : List Sig := [y8_76,x8_3,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_302x : Impossible 7 1 s8_302 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_303 : List Sig := [y8_76,y8_18,x8_3,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_303x : Impossible 7 1 s8_303 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_304 : List Sig := [y8_106,x8_3,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_304x : Impossible 7 1 s8_304 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_305 : List Sig := [y8_106,y8_18,x8_3,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_305x : Impossible 7 1 s8_305 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_306 : List Sig := [y8_78,x8_4,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_306x : Impossible 7 1 s8_306 := rotate_impossible sym8_0 (z := s8_302) (by simp only [s8_306,x8_0,x8_1,x8_2,x8_3,x8_4,y8_26,y8_78,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_302x

def s8_307 : List Sig := [y8_78,y8_18,x8_4,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_307x : Impossible 7 1 s8_307 := rotate_impossible sym8_0 (z := s8_303) (by simp only [s8_307,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_26,y8_78,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_303x

def s8_308 : List Sig := [y8_118,x8_4,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_308x : Impossible 7 1 s8_308 := rotate_impossible sym8_0 (z := s8_304) (by simp only [s8_308,x8_0,x8_1,x8_2,x8_3,x8_4,y8_118,y8_18,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_304x

def s8_309 : List Sig := [y8_118,y8_18,x8_4,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_309x : Impossible 7 1 s8_309 := rotate_impossible sym8_0 (z := s8_305) (by simp only [s8_309,x8_0,x8_1,x8_2,x8_3,x8_4,y8_118,y8_18,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_305x

def s8_310 : List Sig := [y8_19,y8_18,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_310x : Impossible 7 1 s8_310 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_311 : List Sig := [y8_19,x8_1,y8_18,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_311x : Impossible 7 1 s8_311 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_312 : List Sig := [y8_19,x8_2,y8_18,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_312x : Impossible 7 1 s8_312 := rotate_impossible sym8_1 (z := s8_311) (by simp only [s8_312,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_19,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_311x

def s8_313 : List Sig := [y8_19,x8_1,x8_2,y8_18,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_313x : Impossible 7 1 s8_313 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_314 : List Sig := [y8_10,x8_0,y8_18,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_314x : Impossible 7 1 s8_314 := impPerm (z := s8_141) (by decide +kernel) s8_141x

def s8_315 : List Sig := [y8_10,x8_1,x8_0,y8_18,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_315x : Impossible 7 1 s8_315 := impPerm (z := s8_142) (by decide +kernel) s8_142x

def s8_316 : List Sig := [y8_11,x8_1,x8_0,y8_18,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_316x : Impossible 7 1 s8_316 := impPerm (z := s8_189) (by decide +kernel) s8_189x

def s8_317 : List Sig := [y8_20,x8_1,x8_3,y8_18,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_317x : Impossible 7 1 s8_317 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_318 : List Sig := [y8_21,x8_1,x8_3,y8_18,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_318x : Impossible 7 1 s8_318 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_319 : List Sig := [y8_22,x8_1,x8_4,y8_18,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_319x : Impossible 7 1 s8_319 := rotate_impossible sym8_0 (z := s8_317) (by simp only [s8_319,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_22,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_317x

def s8_320 : List Sig := [y8_23,x8_1,x8_4,y8_18,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_320x : Impossible 7 1 s8_320 := rotate_impossible sym8_0 (z := s8_318) (by simp only [s8_320,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_23,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_318x

def s8_321 : List Sig := [y8_12,x8_0,y8_18,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_321x : Impossible 7 1 s8_321 := rotate_impossible sym8_1 (z := s8_141) (by simp only [s8_321,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_18,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_141x

def s8_322 : List Sig := [y8_12,x8_2,x8_0,y8_18,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_322x : Impossible 7 1 s8_322 := rotate_impossible sym8_1 (z := s8_142) (by simp only [s8_322,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_18,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_142x

def s8_323 : List Sig := [y8_13,x8_2,x8_0,y8_18,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_323x : Impossible 7 1 s8_323 := rotate_impossible sym8_1 (z := s8_189) (by simp only [s8_323,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_18,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_189x

def s8_324 : List Sig := [y8_24,x8_2,x8_3,y8_18,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_324x : Impossible 7 1 s8_324 := rotate_impossible sym8_1 (z := s8_317) (by simp only [s8_324,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_24,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_317x

def s8_325 : List Sig := [y8_25,x8_2,x8_3,y8_18,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_325x : Impossible 7 1 s8_325 := rotate_impossible sym8_1 (z := s8_318) (by simp only [s8_325,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_25,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_318x

def s8_326 : List Sig := [y8_26,x8_2,x8_4,y8_18,x8_1,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_326x : Impossible 7 1 s8_326 := rotate_impossible sym8_0 (z := s8_324) (by simp only [s8_326,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_26,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_324x

def s8_327 : List Sig := [y8_27,x8_2,x8_4,y8_18,x8_1,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_327x : Impossible 7 1 s8_327 := rotate_impossible sym8_0 (z := s8_325) (by simp only [s8_327,x8_0,x8_1,x8_2,x8_3,x8_4,y8_18,y8_27,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_325x

def s8_328 : List Sig := [y8_14,x8_0,x8_3,y8_18,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_328x : Impossible 7 1 s8_328 := impPerm (z := s8_241) (by decide +kernel) s8_241x

def s8_329 : List Sig := [y8_15,x8_0,x8_3,y8_18,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_329x : Impossible 7 1 s8_329 := impPerm (z := s8_282) (by decide +kernel) s8_282x

def s8_330 : List Sig := [y8_16,x8_0,x8_4,y8_18,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_330x : Impossible 7 1 s8_330 := rotate_impossible sym8_0 (z := s8_241) (by simp only [s8_330,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_18,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_241x

def s8_331 : List Sig := [y8_17,x8_0,x8_4,y8_18,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_331x : Impossible 7 1 s8_331 := rotate_impossible sym8_0 (z := s8_282) (by simp only [s8_331,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,y8_18,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_282x

def s8_332 : List Sig := [y8_28,x8_3,x8_4,y8_18,x8_1,x8_2,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_332x : Impossible 7 1 s8_332 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_333 : List Sig := [y8_29,x8_3,x8_4,y8_18,x8_1,x8_2,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_333x : Impossible 7 1 s8_333 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_334 : List Sig := [y8_18,x8_1,x8_2,x8_0,x8_3,x8_4]
def s8_334u : List (List Sig) := [s8_291,s8_292,s8_293,s8_294,s8_295,s8_296,s8_297]
lemma s8_334ux (v : List Sig) (h : (!s8_334u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_334u := by simpa using h
  simp only [s8_334u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_291x
  · exact s8_292x
  · exact s8_293x
  · exact s8_294x
  · exact s8_295x
  · exact s8_296x
  · exact s8_297x
def s8_334b : List (List Sig) := [s8_298,s8_299,s8_300,s8_301,s8_302,s8_303,s8_304,s8_305,s8_306,s8_307,s8_308,s8_309,s8_310,s8_311,s8_312,s8_313,s8_314,s8_315,s8_316,s8_317,s8_318,s8_319,s8_320,s8_321,s8_322,s8_323,s8_324,s8_325,s8_326,s8_327,s8_328,s8_329,s8_330,s8_331,s8_332,s8_333]
lemma s8_334bx (v : List Sig) (h : (!s8_334b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_334b := by simpa using h
  simp only [s8_334b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_298x
  · exact s8_299x
  · exact s8_300x
  · exact s8_301x
  · exact s8_302x
  · exact s8_303x
  · exact s8_304x
  · exact s8_305x
  · exact s8_306x
  · exact s8_307x
  · exact s8_308x
  · exact s8_309x
  · exact s8_310x
  · exact s8_311x
  · exact s8_312x
  · exact s8_313x
  · exact s8_314x
  · exact s8_315x
  · exact s8_316x
  · exact s8_317x
  · exact s8_318x
  · exact s8_319x
  · exact s8_320x
  · exact s8_321x
  · exact s8_322x
  · exact s8_323x
  · exact s8_324x
  · exact s8_325x
  · exact s8_326x
  · exact s8_327x
  · exact s8_328x
  · exact s8_329x
  · exact s8_330x
  · exact s8_331x
  · exact s8_332x
  · exact s8_333x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_334x : Impossible 8 1 s8_334 :=
  exclude_step (u := fun v => !s8_334u.contains v) (b := fun v => !s8_334b.contains v) (by decide +kernel) s8_334ux s8_334bx (by decide +kernel)

def s8_335 : List Sig := [y8_39,x8_1,x8_2,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_335x : Impossible 7 0 s8_335 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_336 : List Sig := [y8_39,y8_19,x8_1,x8_2,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_336x : Impossible 7 0 s8_336 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_337 : List Sig := [y8_6,x8_1,y8_19,x8_2,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_337x : Impossible 7 0 s8_337 := impPerm (z := s8_56) (by decide +kernel) s8_56x

def s8_338 : List Sig := [y8_7,x8_2,y8_19,x8_1,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_338x : Impossible 7 0 s8_338 := rotate_impossible sym8_1 (z := s8_56) (by simp only [s8_338,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_56x

def s8_339 : List Sig := [y8_5,x8_0,y8_19,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_339x : Impossible 7 0 s8_339 := impPerm (z := s8_25) (by decide +kernel) s8_25x

def s8_340 : List Sig := [y8_8,x8_3,y8_19,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_340x : Impossible 7 0 s8_340 := impPerm (z := s8_106) (by decide +kernel) s8_106x

def s8_341 : List Sig := [y8_9,x8_4,y8_19,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_341x : Impossible 7 0 s8_341 := rotate_impossible sym8_0 (z := s8_106) (by simp only [s8_341,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_106x

def s8_342 : List Sig := [y8_56,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_342x : Impossible 7 1 s8_342 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_343 : List Sig := [y8_56,y8_19,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_343x : Impossible 7 1 s8_343 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_344 : List Sig := [y8_57,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_344x : Impossible 7 1 s8_344 := impPerm (z := s8_166) (by decide +kernel) s8_166x

def s8_345 : List Sig := [y8_57,y8_19,x8_0,x8_1,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_345x : Impossible 7 1 s8_345 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_346 : List Sig := [y8_107,x8_3,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_346x : Impossible 7 1 s8_346 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_347 : List Sig := [y8_107,y8_19,x8_3,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_347x : Impossible 7 1 s8_347 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_348 : List Sig := [y8_77,x8_3,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_348x : Impossible 7 1 s8_348 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_349 : List Sig := [y8_77,y8_19,x8_3,x8_1,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_349x : Impossible 7 1 s8_349 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_350 : List Sig := [y8_119,x8_4,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_350x : Impossible 7 1 s8_350 := rotate_impossible sym8_0 (z := s8_346) (by simp only [s8_350,x8_0,x8_1,x8_2,x8_3,x8_4,y8_119,y8_19,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_346x

def s8_351 : List Sig := [y8_119,y8_19,x8_4,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_351x : Impossible 7 1 s8_351 := rotate_impossible sym8_0 (z := s8_347) (by simp only [s8_351,x8_0,x8_1,x8_2,x8_3,x8_4,y8_119,y8_19,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_347x

def s8_352 : List Sig := [y8_79,x8_4,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_352x : Impossible 7 1 s8_352 := rotate_impossible sym8_0 (z := s8_348) (by simp only [s8_352,x8_0,x8_1,x8_2,x8_3,x8_4,y8_27,y8_79,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_348x

def s8_353 : List Sig := [y8_79,y8_19,x8_4,x8_1,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_353x : Impossible 7 1 s8_353 := rotate_impossible sym8_0 (z := s8_349) (by simp only [s8_353,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_27,y8_79,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_349x

def s8_354 : List Sig := [y8_18,y8_19,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_354x : Impossible 7 1 s8_354 := impPerm (z := s8_310) (by decide +kernel) s8_310x

def s8_355 : List Sig := [y8_18,x8_1,y8_19,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_355x : Impossible 7 1 s8_355 := impPerm (z := s8_311) (by decide +kernel) s8_311x

def s8_356 : List Sig := [y8_18,x8_2,y8_19,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_356x : Impossible 7 1 s8_356 := impPerm (z := s8_312) (by decide +kernel) s8_312x

def s8_357 : List Sig := [y8_18,x8_1,x8_2,y8_19,x8_0,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_357x : Impossible 7 1 s8_357 := impPerm (z := s8_313) (by decide +kernel) s8_313x

def s8_358 : List Sig := [y8_10,x8_1,x8_0,y8_19,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_358x : Impossible 7 1 s8_358 := impPerm (z := s8_143) (by decide +kernel) s8_143x

def s8_359 : List Sig := [y8_11,x8_1,x8_0,y8_19,x8_2,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_359x : Impossible 7 1 s8_359 := impPerm (z := s8_190) (by decide +kernel) s8_190x

def s8_360 : List Sig := [y8_20,x8_1,x8_3,y8_19,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_360x : Impossible 7 1 s8_360 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_361 : List Sig := [y8_21,x8_1,x8_3,y8_19,x8_2,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_361x : Impossible 7 1 s8_361 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_362 : List Sig := [y8_22,x8_1,x8_4,y8_19,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_362x : Impossible 7 1 s8_362 := rotate_impossible sym8_0 (z := s8_360) (by simp only [s8_362,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_22,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_360x

def s8_363 : List Sig := [y8_23,x8_1,x8_4,y8_19,x8_2,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_363x : Impossible 7 1 s8_363 := rotate_impossible sym8_0 (z := s8_361) (by simp only [s8_363,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_23,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_361x

def s8_364 : List Sig := [y8_12,x8_2,x8_0,y8_19,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_364x : Impossible 7 1 s8_364 := rotate_impossible sym8_1 (z := s8_143) (by simp only [s8_364,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_19,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_143x

def s8_365 : List Sig := [y8_13,x8_2,x8_0,y8_19,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_365x : Impossible 7 1 s8_365 := rotate_impossible sym8_1 (z := s8_190) (by simp only [s8_365,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_19,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_190x

def s8_366 : List Sig := [y8_24,x8_2,x8_3,y8_19,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_366x : Impossible 7 1 s8_366 := rotate_impossible sym8_1 (z := s8_360) (by simp only [s8_366,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_24,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_360x

def s8_367 : List Sig := [y8_25,x8_2,x8_3,y8_19,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_367x : Impossible 7 1 s8_367 := rotate_impossible sym8_1 (z := s8_361) (by simp only [s8_367,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_25,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_361x

def s8_368 : List Sig := [y8_26,x8_2,x8_4,y8_19,x8_1,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_368x : Impossible 7 1 s8_368 := rotate_impossible sym8_0 (z := s8_366) (by simp only [s8_368,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_26,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_366x

def s8_369 : List Sig := [y8_27,x8_2,x8_4,y8_19,x8_1,x8_0,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_369x : Impossible 7 1 s8_369 := rotate_impossible sym8_0 (z := s8_367) (by simp only [s8_369,x8_0,x8_1,x8_2,x8_3,x8_4,y8_19,y8_27,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_367x

def s8_370 : List Sig := [y8_14,x8_0,x8_3,y8_19,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_370x : Impossible 7 1 s8_370 := impPerm (z := s8_242) (by decide +kernel) s8_242x

def s8_371 : List Sig := [y8_15,x8_0,x8_3,y8_19,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_371x : Impossible 7 1 s8_371 := impPerm (z := s8_283) (by decide +kernel) s8_283x

def s8_372 : List Sig := [y8_16,x8_0,x8_4,y8_19,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_372x : Impossible 7 1 s8_372 := rotate_impossible sym8_0 (z := s8_242) (by simp only [s8_372,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_19,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_242x

def s8_373 : List Sig := [y8_17,x8_0,x8_4,y8_19,x8_1,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_373x : Impossible 7 1 s8_373 := rotate_impossible sym8_0 (z := s8_283) (by simp only [s8_373,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,y8_19,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_283x

def s8_374 : List Sig := [y8_28,x8_3,x8_4,y8_19,x8_1,x8_2,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_374x : Impossible 7 1 s8_374 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_375 : List Sig := [y8_29,x8_3,x8_4,y8_19,x8_1,x8_2,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_375x : Impossible 7 1 s8_375 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_376 : List Sig := [y8_19,x8_1,x8_2,x8_0,x8_3,x8_4]
def s8_376u : List (List Sig) := [s8_335,s8_336,s8_337,s8_338,s8_339,s8_340,s8_341]
lemma s8_376ux (v : List Sig) (h : (!s8_376u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_376u := by simpa using h
  simp only [s8_376u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_335x
  · exact s8_336x
  · exact s8_337x
  · exact s8_338x
  · exact s8_339x
  · exact s8_340x
  · exact s8_341x
def s8_376b : List (List Sig) := [s8_342,s8_343,s8_344,s8_345,s8_346,s8_347,s8_348,s8_349,s8_350,s8_351,s8_352,s8_353,s8_354,s8_355,s8_356,s8_357,s8_358,s8_359,s8_360,s8_361,s8_362,s8_363,s8_364,s8_365,s8_366,s8_367,s8_368,s8_369,s8_370,s8_371,s8_372,s8_373,s8_374,s8_375]
lemma s8_376bx (v : List Sig) (h : (!s8_376b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_376b := by simpa using h
  simp only [s8_376b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_342x
  · exact s8_343x
  · exact s8_344x
  · exact s8_345x
  · exact s8_346x
  · exact s8_347x
  · exact s8_348x
  · exact s8_349x
  · exact s8_350x
  · exact s8_351x
  · exact s8_352x
  · exact s8_353x
  · exact s8_354x
  · exact s8_355x
  · exact s8_356x
  · exact s8_357x
  · exact s8_358x
  · exact s8_359x
  · exact s8_360x
  · exact s8_361x
  · exact s8_362x
  · exact s8_363x
  · exact s8_364x
  · exact s8_365x
  · exact s8_366x
  · exact s8_367x
  · exact s8_368x
  · exact s8_369x
  · exact s8_370x
  · exact s8_371x
  · exact s8_372x
  · exact s8_373x
  · exact s8_374x
  · exact s8_375x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_376x : Impossible 8 1 s8_376 :=
  exclude_step (u := fun v => !s8_376u.contains v) (b := fun v => !s8_376b.contains v) (by decide +kernel) s8_376ux s8_376bx (by decide +kernel)

def s8_377 : List Sig := [y8_40,x8_1,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_377x : Impossible 7 0 s8_377 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_378 : List Sig := [y8_40,y8_20,x8_1,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_378x : Impossible 7 0 s8_378 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_379 : List Sig := [y8_6,x8_1,y8_20,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_379x : Impossible 7 0 s8_379 := impPerm (z := s8_57) (by decide +kernel) s8_57x

def s8_380 : List Sig := [y8_8,x8_3,y8_20,x8_1,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_380x : Impossible 7 0 s8_380 := impPerm (z := s8_93) (by decide +kernel) s8_93x

def s8_381 : List Sig := [y8_5,x8_0,y8_20,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_381x : Impossible 7 0 s8_381 := impPerm (z := s8_26) (by decide +kernel) s8_26x

def s8_382 : List Sig := [y8_7,x8_2,y8_20,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_382x : Impossible 7 0 s8_382 := rotate_impossible sym8_1 (z := s8_67) (by simp only [s8_382,x8_0,x8_1,x8_2,x8_3,x8_4,y8_20,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_67x

def s8_383 : List Sig := [y8_9,x8_4,y8_20,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_383x : Impossible 7 0 s8_383 := rotate_impossible sym8_0 (z := s8_107) (by simp only [s8_383,x8_0,x8_1,x8_2,x8_3,x8_4,y8_20,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_107x

def s8_384 : List Sig := [y8_58,x8_0,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_384x : Impossible 7 1 s8_384 := impPerm (z := s8_124) (by decide +kernel) s8_124x

def s8_385 : List Sig := [y8_58,y8_20,x8_0,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_385x : Impossible 7 1 s8_385 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_386 : List Sig := [y8_59,x8_0,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_386x : Impossible 7 1 s8_386 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_387 : List Sig := [y8_59,y8_20,x8_0,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_387x : Impossible 7 1 s8_387 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_388 : List Sig := [y8_76,x8_2,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_388x : Impossible 7 1 s8_388 := impPerm (z := s8_302) (by decide +kernel) s8_302x

def s8_389 : List Sig := [y8_76,y8_20,x8_2,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_389x : Impossible 7 1 s8_389 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_390 : List Sig := [y8_94,x8_2,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_390x : Impossible 7 1 s8_390 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_391 : List Sig := [y8_94,y8_20,x8_2,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_391x : Impossible 7 1 s8_391 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_392 : List Sig := [y8_80,x8_4,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_392x : Impossible 7 1 s8_392 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_393 : List Sig := [y8_80,y8_20,x8_4,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_393x : Impossible 7 1 s8_393 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_394 : List Sig := [y8_120,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_394x : Impossible 7 1 s8_394 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_395 : List Sig := [y8_120,y8_20,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_395x : Impossible 7 1 s8_395 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_396 : List Sig := [y8_120,x8_4,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_396x : Impossible 7 1 s8_396 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_397 : List Sig := [y8_120,y8_20,x8_4,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_397x : Impossible 7 1 s8_397 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_398 : List Sig := [y8_21,x8_1,y8_20,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_398x : Impossible 7 1 s8_398 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_399 : List Sig := [y8_21,x8_3,y8_20,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_399x : Impossible 7 1 s8_399 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_400 : List Sig := [y8_21,x8_1,x8_3,y8_20,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_400x : Impossible 7 1 s8_400 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_401 : List Sig := [y8_10,x8_1,x8_0,y8_20,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_401x : Impossible 7 1 s8_401 := impPerm (z := s8_144) (by decide +kernel) s8_144x

def s8_402 : List Sig := [y8_11,x8_1,x8_0,y8_20,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_402x : Impossible 7 1 s8_402 := impPerm (z := s8_191) (by decide +kernel) s8_191x

def s8_403 : List Sig := [y8_18,x8_1,x8_2,y8_20,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_403x : Impossible 7 1 s8_403 := impPerm (z := s8_317) (by decide +kernel) s8_317x

def s8_404 : List Sig := [y8_19,x8_1,x8_2,y8_20,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_404x : Impossible 7 1 s8_404 := impPerm (z := s8_360) (by decide +kernel) s8_360x

def s8_405 : List Sig := [y8_22,x8_1,x8_4,y8_20,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_405x : Impossible 7 1 s8_405 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_406 : List Sig := [y8_23,x8_1,x8_4,y8_20,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_406x : Impossible 7 1 s8_406 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_407 : List Sig := [y8_14,x8_0,y8_20,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_407x : Impossible 7 1 s8_407 := impPerm (z := s8_232) (by decide +kernel) s8_232x

def s8_408 : List Sig := [y8_14,x8_3,x8_0,y8_20,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_408x : Impossible 7 1 s8_408 := impPerm (z := s8_233) (by decide +kernel) s8_233x

def s8_409 : List Sig := [y8_15,x8_3,x8_0,y8_20,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_409x : Impossible 7 1 s8_409 := impPerm (z := s8_276) (by decide +kernel) s8_276x

def s8_410 : List Sig := [y8_24,x8_3,x8_2,y8_20,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_410x : Impossible 7 1 s8_410 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_411 : List Sig := [y8_25,x8_3,x8_2,y8_20,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_411x : Impossible 7 1 s8_411 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_412 : List Sig := [y8_28,x8_3,x8_4,y8_20,x8_1,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_412x : Impossible 7 1 s8_412 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_413 : List Sig := [y8_29,x8_3,x8_4,y8_20,x8_1,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_413x : Impossible 7 1 s8_413 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_414 : List Sig := [y8_12,x8_0,x8_2,y8_20,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_414x : Impossible 7 1 s8_414 := rotate_impossible sym8_1 (z := s8_148) (by simp only [s8_414,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_20,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_148x

def s8_415 : List Sig := [y8_13,x8_0,x8_2,y8_20,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_415x : Impossible 7 1 s8_415 := rotate_impossible sym8_1 (z := s8_195) (by simp only [s8_415,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_20,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_195x

def s8_416 : List Sig := [y8_16,x8_0,x8_4,y8_20,x8_1,x8_3,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_416x : Impossible 7 1 s8_416 := rotate_impossible sym8_0 (z := s8_243) (by simp only [s8_416,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_20,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_243x

def s8_417 : List Sig := [y8_17,x8_0,x8_4,y8_20,x8_1,x8_3,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_417x : Impossible 7 1 s8_417 := rotate_impossible sym8_0 (z := s8_284) (by simp only [s8_417,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,y8_20,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_284x

def s8_418 : List Sig := [y8_26,x8_2,x8_4,y8_20,x8_1,x8_3,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_418x : Impossible 7 1 s8_418 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_419 : List Sig := [y8_27,x8_2,x8_4,y8_20,x8_1,x8_3,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_419x : Impossible 7 1 s8_419 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_420 : List Sig := [y8_20,x8_1,x8_3,x8_0,x8_2,x8_4]
def s8_420u : List (List Sig) := [s8_377,s8_378,s8_379,s8_380,s8_381,s8_382,s8_383]
lemma s8_420ux (v : List Sig) (h : (!s8_420u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_420u := by simpa using h
  simp only [s8_420u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_377x
  · exact s8_378x
  · exact s8_379x
  · exact s8_380x
  · exact s8_381x
  · exact s8_382x
  · exact s8_383x
def s8_420b : List (List Sig) := [s8_384,s8_385,s8_386,s8_387,s8_388,s8_389,s8_390,s8_391,s8_392,s8_393,s8_394,s8_395,s8_396,s8_397,s8_398,s8_399,s8_400,s8_401,s8_402,s8_403,s8_404,s8_405,s8_406,s8_407,s8_408,s8_409,s8_410,s8_411,s8_412,s8_413,s8_414,s8_415,s8_416,s8_417,s8_418,s8_419]
lemma s8_420bx (v : List Sig) (h : (!s8_420b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_420b := by simpa using h
  simp only [s8_420b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_384x
  · exact s8_385x
  · exact s8_386x
  · exact s8_387x
  · exact s8_388x
  · exact s8_389x
  · exact s8_390x
  · exact s8_391x
  · exact s8_392x
  · exact s8_393x
  · exact s8_394x
  · exact s8_395x
  · exact s8_396x
  · exact s8_397x
  · exact s8_398x
  · exact s8_399x
  · exact s8_400x
  · exact s8_401x
  · exact s8_402x
  · exact s8_403x
  · exact s8_404x
  · exact s8_405x
  · exact s8_406x
  · exact s8_407x
  · exact s8_408x
  · exact s8_409x
  · exact s8_410x
  · exact s8_411x
  · exact s8_412x
  · exact s8_413x
  · exact s8_414x
  · exact s8_415x
  · exact s8_416x
  · exact s8_417x
  · exact s8_418x
  · exact s8_419x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_420x : Impossible 8 1 s8_420 :=
  exclude_step (u := fun v => !s8_420u.contains v) (b := fun v => !s8_420b.contains v) (by decide +kernel) s8_420ux s8_420bx (by decide +kernel)

def s8_421 : List Sig := [y8_41,x8_1,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_421x : Impossible 7 0 s8_421 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_422 : List Sig := [y8_41,y8_21,x8_1,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_422x : Impossible 7 0 s8_422 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_423 : List Sig := [y8_6,x8_1,y8_21,x8_3,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_423x : Impossible 7 0 s8_423 := impPerm (z := s8_58) (by decide +kernel) s8_58x

def s8_424 : List Sig := [y8_8,x8_3,y8_21,x8_1,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_424x : Impossible 7 0 s8_424 := impPerm (z := s8_94) (by decide +kernel) s8_94x

def s8_425 : List Sig := [y8_5,x8_0,y8_21,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_425x : Impossible 7 0 s8_425 := impPerm (z := s8_27) (by decide +kernel) s8_27x

def s8_426 : List Sig := [y8_7,x8_2,y8_21,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_426x : Impossible 7 0 s8_426 := rotate_impossible sym8_1 (z := s8_68) (by simp only [s8_426,x8_0,x8_1,x8_2,x8_3,x8_4,y8_21,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_68x

def s8_427 : List Sig := [y8_9,x8_4,y8_21,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_427x : Impossible 7 0 s8_427 := rotate_impossible sym8_0 (z := s8_108) (by simp only [s8_427,x8_0,x8_1,x8_2,x8_3,x8_4,y8_21,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_108x

def s8_428 : List Sig := [y8_60,x8_0,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_428x : Impossible 7 1 s8_428 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_429 : List Sig := [y8_60,y8_21,x8_0,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_429x : Impossible 7 1 s8_429 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_430 : List Sig := [y8_61,x8_0,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_430x : Impossible 7 1 s8_430 := impPerm (z := s8_172) (by decide +kernel) s8_172x

def s8_431 : List Sig := [y8_61,y8_21,x8_0,x8_1,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_431x : Impossible 7 1 s8_431 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_432 : List Sig := [y8_95,x8_2,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_432x : Impossible 7 1 s8_432 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_433 : List Sig := [y8_95,y8_21,x8_2,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_433x : Impossible 7 1 s8_433 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_434 : List Sig := [y8_77,x8_2,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_434x : Impossible 7 1 s8_434 := impPerm (z := s8_348) (by decide +kernel) s8_348x

def s8_435 : List Sig := [y8_77,y8_21,x8_2,x8_1,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_435x : Impossible 7 1 s8_435 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_436 : List Sig := [y8_121,x8_4,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_436x : Impossible 7 1 s8_436 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_437 : List Sig := [y8_121,y8_21,x8_4,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_437x : Impossible 7 1 s8_437 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_438 : List Sig := [y8_83,x8_4,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_438x : Impossible 7 1 s8_438 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_439 : List Sig := [y8_83,y8_21,x8_4,x8_1,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_439x : Impossible 7 1 s8_439 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_440 : List Sig := [y8_20,x8_1,y8_21,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_440x : Impossible 7 1 s8_440 := impPerm (z := s8_398) (by decide +kernel) s8_398x

def s8_441 : List Sig := [y8_20,x8_3,y8_21,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_441x : Impossible 7 1 s8_441 := impPerm (z := s8_399) (by decide +kernel) s8_399x

def s8_442 : List Sig := [y8_20,x8_1,x8_3,y8_21,x8_0,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_442x : Impossible 7 1 s8_442 := impPerm (z := s8_400) (by decide +kernel) s8_400x

def s8_443 : List Sig := [y8_10,x8_1,x8_0,y8_21,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_443x : Impossible 7 1 s8_443 := impPerm (z := s8_145) (by decide +kernel) s8_145x

def s8_444 : List Sig := [y8_11,x8_1,x8_0,y8_21,x8_3,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_444x : Impossible 7 1 s8_444 := impPerm (z := s8_192) (by decide +kernel) s8_192x

def s8_445 : List Sig := [y8_18,x8_1,x8_2,y8_21,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_445x : Impossible 7 1 s8_445 := impPerm (z := s8_318) (by decide +kernel) s8_318x

def s8_446 : List Sig := [y8_19,x8_1,x8_2,y8_21,x8_3,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_446x : Impossible 7 1 s8_446 := impPerm (z := s8_361) (by decide +kernel) s8_361x

def s8_447 : List Sig := [y8_22,x8_1,x8_4,y8_21,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_447x : Impossible 7 1 s8_447 := rotate_impossible sym8_0 (z := s8_406) (by simp only [s8_447,x8_0,x8_1,x8_2,x8_3,x8_4,y8_21,y8_22,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_406x

def s8_448 : List Sig := [y8_23,x8_1,x8_4,y8_21,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_448x : Impossible 7 1 s8_448 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_449 : List Sig := [y8_14,x8_3,x8_0,y8_21,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_449x : Impossible 7 1 s8_449 := impPerm (z := s8_234) (by decide +kernel) s8_234x

def s8_450 : List Sig := [y8_15,x8_3,x8_0,y8_21,x8_1,x8_2,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_450x : Impossible 7 1 s8_450 := impPerm (z := s8_277) (by decide +kernel) s8_277x

def s8_451 : List Sig := [y8_24,x8_3,x8_2,y8_21,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_451x : Impossible 7 1 s8_451 := rotate_impossible sym8_1 (z := s8_411) (by simp only [s8_451,x8_0,x8_1,x8_2,x8_3,x8_4,y8_21,y8_24,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_411x

def s8_452 : List Sig := [y8_25,x8_3,x8_2,y8_21,x8_1,x8_0,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_452x : Impossible 7 1 s8_452 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_453 : List Sig := [y8_28,x8_3,x8_4,y8_21,x8_1,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_453x : Impossible 7 1 s8_453 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_454 : List Sig := [y8_29,x8_4,y8_21,x8_1,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_454x : Impossible 7 1 s8_454 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_455 : List Sig := [y8_29,x8_3,x8_4,y8_21,x8_1,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_455x : Impossible 7 1 s8_455 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_456 : List Sig := [y8_12,x8_0,x8_2,y8_21,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_456x : Impossible 7 1 s8_456 := rotate_impossible sym8_1 (z := s8_149) (by simp only [s8_456,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_21,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_149x

def s8_457 : List Sig := [y8_13,x8_0,x8_2,y8_21,x8_1,x8_3,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_457x : Impossible 7 1 s8_457 := rotate_impossible sym8_1 (z := s8_196) (by simp only [s8_457,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_21,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_196x

def s8_458 : List Sig := [y8_16,x8_0,x8_4,y8_21,x8_1,x8_3,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_458x : Impossible 7 1 s8_458 := rotate_impossible sym8_0 (z := s8_244) (by simp only [s8_458,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_21,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_244x

def s8_459 : List Sig := [y8_17,x8_0,x8_4,y8_21,x8_1,x8_3,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_459x : Impossible 7 1 s8_459 := rotate_impossible sym8_0 (z := s8_285) (by simp only [s8_459,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,y8_21,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_285x

def s8_460 : List Sig := [y8_26,x8_2,x8_4,y8_21,x8_1,x8_3,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_460x : Impossible 7 1 s8_460 := rotate_impossible sym8_2 (z := s8_419) (by simp only [s8_460,x8_0,x8_1,x8_2,x8_3,x8_4,y8_21,y8_26,List.map_cons,List.map_nil,action_bin,action_neg,rot8_2_0,rot8_2_1,rot8_2_2,rot8_2_3,rot8_2_4]; decide +kernel) s8_419x

def s8_461 : List Sig := [y8_27,x8_2,x8_4,y8_21,x8_1,x8_3,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_461x : Impossible 7 1 s8_461 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_462 : List Sig := [y8_21,x8_1,x8_3,x8_0,x8_2,x8_4]
def s8_462u : List (List Sig) := [s8_421,s8_422,s8_423,s8_424,s8_425,s8_426,s8_427]
lemma s8_462ux (v : List Sig) (h : (!s8_462u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_462u := by simpa using h
  simp only [s8_462u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_421x
  · exact s8_422x
  · exact s8_423x
  · exact s8_424x
  · exact s8_425x
  · exact s8_426x
  · exact s8_427x
def s8_462b : List (List Sig) := [s8_428,s8_429,s8_430,s8_431,s8_432,s8_433,s8_434,s8_435,s8_436,s8_437,s8_438,s8_439,s8_440,s8_441,s8_442,s8_443,s8_444,s8_445,s8_446,s8_447,s8_448,s8_449,s8_450,s8_451,s8_452,s8_453,s8_454,s8_455,s8_456,s8_457,s8_458,s8_459,s8_460,s8_461]
lemma s8_462bx (v : List Sig) (h : (!s8_462b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_462b := by simpa using h
  simp only [s8_462b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_428x
  · exact s8_429x
  · exact s8_430x
  · exact s8_431x
  · exact s8_432x
  · exact s8_433x
  · exact s8_434x
  · exact s8_435x
  · exact s8_436x
  · exact s8_437x
  · exact s8_438x
  · exact s8_439x
  · exact s8_440x
  · exact s8_441x
  · exact s8_442x
  · exact s8_443x
  · exact s8_444x
  · exact s8_445x
  · exact s8_446x
  · exact s8_447x
  · exact s8_448x
  · exact s8_449x
  · exact s8_450x
  · exact s8_451x
  · exact s8_452x
  · exact s8_453x
  · exact s8_454x
  · exact s8_455x
  · exact s8_456x
  · exact s8_457x
  · exact s8_458x
  · exact s8_459x
  · exact s8_460x
  · exact s8_461x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_462x : Impossible 8 1 s8_462 :=
  exclude_step (u := fun v => !s8_462u.contains v) (b := fun v => !s8_462b.contains v) (by decide +kernel) s8_462ux s8_462bx (by decide +kernel)

def s8_463 : List Sig := [y8_22,x8_1,x8_4,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_463x : Impossible 8 1 s8_463 := rotate_impossible sym8_0 (z := s8_420) (by simp only [s8_463,x8_0,x8_1,x8_2,x8_3,x8_4,y8_22,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_420x

def s8_464 : List Sig := [y8_23,x8_1,x8_4,x8_0,x8_2,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_464x : Impossible 8 1 s8_464 := rotate_impossible sym8_0 (z := s8_462) (by simp only [s8_464,x8_0,x8_1,x8_2,x8_3,x8_4,y8_23,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_462x

def s8_465 : List Sig := [y8_24,x8_2,x8_3,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_465x : Impossible 8 1 s8_465 := rotate_impossible sym8_1 (z := s8_420) (by simp only [s8_465,x8_0,x8_1,x8_2,x8_3,x8_4,y8_24,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_420x

def s8_466 : List Sig := [y8_25,x8_2,x8_3,x8_0,x8_1,x8_4]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_466x : Impossible 8 1 s8_466 := rotate_impossible sym8_1 (z := s8_462) (by simp only [s8_466,x8_0,x8_1,x8_2,x8_3,x8_4,y8_25,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_462x

def s8_467 : List Sig := [y8_26,x8_2,x8_4,x8_0,x8_1,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_467x : Impossible 8 1 s8_467 := rotate_impossible sym8_0 (z := s8_465) (by simp only [s8_467,x8_0,x8_1,x8_2,x8_3,x8_4,y8_26,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_465x

def s8_468 : List Sig := [y8_27,x8_2,x8_4,x8_0,x8_1,x8_3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_468x : Impossible 8 1 s8_468 := rotate_impossible sym8_0 (z := s8_466) (by simp only [s8_468,x8_0,x8_1,x8_2,x8_3,x8_4,y8_27,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_466x

def s8_469 : List Sig := [y8_48,x8_3,x8_4,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_469x : Impossible 7 0 s8_469 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_470 : List Sig := [y8_48,y8_28,x8_3,x8_4,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_470x : Impossible 7 0 s8_470 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_471 : List Sig := [y8_8,x8_3,y8_28,x8_4,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_471x : Impossible 7 0 s8_471 := impPerm (z := s8_97) (by decide +kernel) s8_97x

def s8_472 : List Sig := [y8_9,x8_4,y8_28,x8_3,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_472x : Impossible 7 0 s8_472 := rotate_impossible sym8_0 (z := s8_97) (by simp only [s8_472,x8_0,x8_1,x8_2,x8_3,x8_4,y8_28,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_97x

def s8_473 : List Sig := [y8_5,x8_0,y8_28,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_473x : Impossible 7 0 s8_473 := impPerm (z := s8_34) (by decide +kernel) s8_34x

def s8_474 : List Sig := [y8_6,x8_1,y8_28,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_474x : Impossible 7 0 s8_474 := impPerm (z := s8_71) (by decide +kernel) s8_71x

def s8_475 : List Sig := [y8_7,x8_2,y8_28,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_475x : Impossible 7 0 s8_475 := rotate_impossible sym8_1 (z := s8_71) (by simp only [s8_475,x8_0,x8_1,x8_2,x8_3,x8_4,y8_28,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_71x

def s8_476 : List Sig := [y8_66,x8_0,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_476x : Impossible 7 1 s8_476 := impPerm (z := s8_219) (by decide +kernel) s8_219x

def s8_477 : List Sig := [y8_66,y8_28,x8_0,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_477x : Impossible 7 1 s8_477 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_478 : List Sig := [y8_67,x8_0,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_478x : Impossible 7 1 s8_478 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_479 : List Sig := [y8_67,y8_28,x8_0,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_479x : Impossible 7 1 s8_479 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_480 : List Sig := [y8_80,x8_1,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_480x : Impossible 7 1 s8_480 := impPerm (z := s8_392) (by decide +kernel) s8_392x

def s8_481 : List Sig := [y8_80,y8_28,x8_1,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_481x : Impossible 7 1 s8_481 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_482 : List Sig := [y8_81,x8_1,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_482x : Impossible 7 1 s8_482 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_483 : List Sig := [y8_81,y8_28,x8_1,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_483x : Impossible 7 1 s8_483 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_484 : List Sig := [y8_96,x8_2,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_484x : Impossible 7 1 s8_484 := rotate_impossible sym8_1 (z := s8_392) (by simp only [s8_484,x8_0,x8_1,x8_2,x8_3,x8_4,y8_28,y8_96,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_392x

def s8_485 : List Sig := [y8_96,y8_28,x8_2,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_485x : Impossible 7 1 s8_485 := rotate_impossible sym8_1 (z := s8_481) (by simp only [s8_485,x8_0,x8_1,x8_2,x8_3,x8_4,y8_28,y8_96,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_481x

def s8_486 : List Sig := [y8_97,x8_2,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_486x : Impossible 7 1 s8_486 := rotate_impossible sym8_1 (z := s8_482) (by simp only [s8_486,x8_0,x8_1,x8_2,x8_3,x8_4,y8_28,y8_97,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_482x

def s8_487 : List Sig := [y8_97,y8_28,x8_2,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_487x : Impossible 7 1 s8_487 := rotate_impossible sym8_1 (z := s8_483) (by simp only [s8_487,x8_0,x8_1,x8_2,x8_3,x8_4,y8_28,y8_97,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_483x

def s8_488 : List Sig := [y8_29,y8_28,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_488x : Impossible 7 1 s8_488 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_489 : List Sig := [y8_29,x8_3,y8_28,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_489x : Impossible 7 1 s8_489 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_490 : List Sig := [y8_29,x8_4,y8_28,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_490x : Impossible 7 1 s8_490 := rotate_impossible sym8_0 (z := s8_489) (by simp only [s8_490,x8_0,x8_1,x8_2,x8_3,x8_4,y8_28,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_489x

def s8_491 : List Sig := [y8_29,x8_3,x8_4,y8_28,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_491x : Impossible 7 1 s8_491 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_492 : List Sig := [y8_14,x8_3,x8_0,y8_28,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_492x : Impossible 7 1 s8_492 := impPerm (z := s8_238) (by decide +kernel) s8_238x

def s8_493 : List Sig := [y8_15,x8_3,x8_0,y8_28,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_493x : Impossible 7 1 s8_493 := impPerm (z := s8_280) (by decide +kernel) s8_280x

def s8_494 : List Sig := [y8_20,x8_3,x8_1,y8_28,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_494x : Impossible 7 1 s8_494 := impPerm (z := s8_412) (by decide +kernel) s8_412x

def s8_495 : List Sig := [y8_21,x8_3,x8_1,y8_28,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_495x : Impossible 7 1 s8_495 := impPerm (z := s8_453) (by decide +kernel) s8_453x

def s8_496 : List Sig := [y8_24,x8_3,x8_2,y8_28,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_496x : Impossible 7 1 s8_496 := rotate_impossible sym8_1 (z := s8_412) (by simp only [s8_496,x8_0,x8_1,x8_2,x8_3,x8_4,y8_24,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_412x

def s8_497 : List Sig := [y8_25,x8_3,x8_2,y8_28,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_497x : Impossible 7 1 s8_497 := rotate_impossible sym8_1 (z := s8_453) (by simp only [s8_497,x8_0,x8_1,x8_2,x8_3,x8_4,y8_25,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_453x

def s8_498 : List Sig := [y8_16,x8_4,x8_0,y8_28,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_498x : Impossible 7 1 s8_498 := rotate_impossible sym8_0 (z := s8_238) (by simp only [s8_498,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_238x

def s8_499 : List Sig := [y8_17,x8_4,x8_0,y8_28,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_499x : Impossible 7 1 s8_499 := rotate_impossible sym8_0 (z := s8_280) (by simp only [s8_499,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_280x

def s8_500 : List Sig := [y8_22,x8_4,x8_1,y8_28,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_500x : Impossible 7 1 s8_500 := rotate_impossible sym8_0 (z := s8_412) (by simp only [s8_500,x8_0,x8_1,x8_2,x8_3,x8_4,y8_22,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_412x

def s8_501 : List Sig := [y8_23,x8_4,x8_1,y8_28,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_501x : Impossible 7 1 s8_501 := rotate_impossible sym8_0 (z := s8_453) (by simp only [s8_501,x8_0,x8_1,x8_2,x8_3,x8_4,y8_23,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_453x

def s8_502 : List Sig := [y8_26,x8_4,x8_2,y8_28,x8_3,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_502x : Impossible 7 1 s8_502 := rotate_impossible sym8_0 (z := s8_496) (by simp only [s8_502,x8_0,x8_1,x8_2,x8_3,x8_4,y8_26,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_496x

def s8_503 : List Sig := [y8_27,x8_4,x8_2,y8_28,x8_3,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_503x : Impossible 7 1 s8_503 := rotate_impossible sym8_0 (z := s8_497) (by simp only [s8_503,x8_0,x8_1,x8_2,x8_3,x8_4,y8_27,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_497x

def s8_504 : List Sig := [y8_10,x8_0,x8_1,y8_28,x8_3,x8_4,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_504x : Impossible 7 1 s8_504 := impPerm (z := s8_152) (by decide +kernel) s8_152x

def s8_505 : List Sig := [y8_11,x8_0,x8_1,y8_28,x8_3,x8_4,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_505x : Impossible 7 1 s8_505 := impPerm (z := s8_199) (by decide +kernel) s8_199x

def s8_506 : List Sig := [y8_12,x8_0,x8_2,y8_28,x8_3,x8_4,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_506x : Impossible 7 1 s8_506 := rotate_impossible sym8_1 (z := s8_152) (by simp only [s8_506,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_152x

def s8_507 : List Sig := [y8_13,x8_0,x8_2,y8_28,x8_3,x8_4,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_507x : Impossible 7 1 s8_507 := rotate_impossible sym8_1 (z := s8_199) (by simp only [s8_507,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_28,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_199x

def s8_508 : List Sig := [y8_18,x8_1,x8_2,y8_28,x8_3,x8_4,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_508x : Impossible 7 1 s8_508 := impPerm (z := s8_332) (by decide +kernel) s8_332x

def s8_509 : List Sig := [y8_19,x8_1,x8_2,y8_28,x8_3,x8_4,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_509x : Impossible 7 1 s8_509 := impPerm (z := s8_374) (by decide +kernel) s8_374x

def s8_510 : List Sig := [y8_28,x8_3,x8_4,x8_0,x8_1,x8_2]
def s8_510u : List (List Sig) := [s8_469,s8_470,s8_471,s8_472,s8_473,s8_474,s8_475]
lemma s8_510ux (v : List Sig) (h : (!s8_510u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_510u := by simpa using h
  simp only [s8_510u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_469x
  · exact s8_470x
  · exact s8_471x
  · exact s8_472x
  · exact s8_473x
  · exact s8_474x
  · exact s8_475x
def s8_510b : List (List Sig) := [s8_476,s8_477,s8_478,s8_479,s8_480,s8_481,s8_482,s8_483,s8_484,s8_485,s8_486,s8_487,s8_488,s8_489,s8_490,s8_491,s8_492,s8_493,s8_494,s8_495,s8_496,s8_497,s8_498,s8_499,s8_500,s8_501,s8_502,s8_503,s8_504,s8_505,s8_506,s8_507,s8_508,s8_509]
lemma s8_510bx (v : List Sig) (h : (!s8_510b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_510b := by simpa using h
  simp only [s8_510b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_476x
  · exact s8_477x
  · exact s8_478x
  · exact s8_479x
  · exact s8_480x
  · exact s8_481x
  · exact s8_482x
  · exact s8_483x
  · exact s8_484x
  · exact s8_485x
  · exact s8_486x
  · exact s8_487x
  · exact s8_488x
  · exact s8_489x
  · exact s8_490x
  · exact s8_491x
  · exact s8_492x
  · exact s8_493x
  · exact s8_494x
  · exact s8_495x
  · exact s8_496x
  · exact s8_497x
  · exact s8_498x
  · exact s8_499x
  · exact s8_500x
  · exact s8_501x
  · exact s8_502x
  · exact s8_503x
  · exact s8_504x
  · exact s8_505x
  · exact s8_506x
  · exact s8_507x
  · exact s8_508x
  · exact s8_509x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_510x : Impossible 8 1 s8_510 :=
  exclude_step (u := fun v => !s8_510u.contains v) (b := fun v => !s8_510b.contains v) (by decide +kernel) s8_510ux s8_510bx (by decide +kernel)

def s8_511 : List Sig := [y8_49,x8_3,x8_4,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_511x : Impossible 7 0 s8_511 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_512 : List Sig := [y8_49,y8_29,x8_3,x8_4,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_512x : Impossible 7 0 s8_512 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_513 : List Sig := [y8_8,x8_3,y8_29,x8_4,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_513x : Impossible 7 0 s8_513 := impPerm (z := s8_98) (by decide +kernel) s8_98x

def s8_514 : List Sig := [y8_9,x8_4,y8_29,x8_3,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_514x : Impossible 7 0 s8_514 := rotate_impossible sym8_0 (z := s8_98) (by simp only [s8_514,x8_0,x8_1,x8_2,x8_3,x8_4,y8_29,y8_9,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_98x

def s8_515 : List Sig := [y8_5,x8_0,y8_29,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_515x : Impossible 7 0 s8_515 := impPerm (z := s8_35) (by decide +kernel) s8_35x

def s8_516 : List Sig := [y8_6,x8_1,y8_29,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_516x : Impossible 7 0 s8_516 := impPerm (z := s8_72) (by decide +kernel) s8_72x

def s8_517 : List Sig := [y8_7,x8_2,y8_29,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_517x : Impossible 7 0 s8_517 := rotate_impossible sym8_1 (z := s8_72) (by simp only [s8_517,x8_0,x8_1,x8_2,x8_3,x8_4,y8_29,y8_7,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_72x

def s8_518 : List Sig := [y8_68,x8_0,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_518x : Impossible 7 1 s8_518 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_519 : List Sig := [y8_68,y8_29,x8_0,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_519x : Impossible 7 1 s8_519 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_520 : List Sig := [y8_69,x8_0,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_520x : Impossible 7 1 s8_520 := impPerm (z := s8_265) (by decide +kernel) s8_265x

def s8_521 : List Sig := [y8_69,y8_29,x8_0,x8_3,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_521x : Impossible 7 1 s8_521 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_522 : List Sig := [y8_82,x8_1,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_522x : Impossible 7 1 s8_522 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_523 : List Sig := [y8_82,y8_29,x8_1,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_523x : Impossible 7 1 s8_523 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_524 : List Sig := [y8_83,x8_1,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_524x : Impossible 7 1 s8_524 := impPerm (z := s8_438) (by decide +kernel) s8_438x

def s8_525 : List Sig := [y8_83,y8_29,x8_1,x8_3,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_525x : Impossible 7 1 s8_525 := exclude_search (by decide +kernel) (by decide +kernel)

def s8_526 : List Sig := [y8_98,x8_2,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_526x : Impossible 7 1 s8_526 := rotate_impossible sym8_1 (z := s8_522) (by simp only [s8_526,x8_0,x8_1,x8_2,x8_3,x8_4,y8_29,y8_98,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_522x

def s8_527 : List Sig := [y8_98,y8_29,x8_2,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_527x : Impossible 7 1 s8_527 := rotate_impossible sym8_1 (z := s8_523) (by simp only [s8_527,x8_0,x8_1,x8_2,x8_3,x8_4,y8_29,y8_98,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_523x

def s8_528 : List Sig := [y8_99,x8_2,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_528x : Impossible 7 1 s8_528 := rotate_impossible sym8_1 (z := s8_438) (by simp only [s8_528,x8_0,x8_1,x8_2,x8_3,x8_4,y8_29,y8_99,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_438x

def s8_529 : List Sig := [y8_99,y8_29,x8_2,x8_3,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_529x : Impossible 7 1 s8_529 := rotate_impossible sym8_1 (z := s8_525) (by simp only [s8_529,x8_0,x8_1,x8_2,x8_3,x8_4,y8_29,y8_99,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_525x

def s8_530 : List Sig := [y8_28,y8_29,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_530x : Impossible 7 1 s8_530 := impPerm (z := s8_488) (by decide +kernel) s8_488x

def s8_531 : List Sig := [y8_28,x8_3,y8_29,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_531x : Impossible 7 1 s8_531 := impPerm (z := s8_489) (by decide +kernel) s8_489x

def s8_532 : List Sig := [y8_28,x8_4,y8_29,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_532x : Impossible 7 1 s8_532 := impPerm (z := s8_490) (by decide +kernel) s8_490x

def s8_533 : List Sig := [y8_28,x8_3,x8_4,y8_29,x8_0,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_533x : Impossible 7 1 s8_533 := impPerm (z := s8_491) (by decide +kernel) s8_491x

def s8_534 : List Sig := [y8_14,x8_0,y8_29,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_534x : Impossible 7 1 s8_534 := impPerm (z := s8_239) (by decide +kernel) s8_239x

def s8_535 : List Sig := [y8_14,x8_3,x8_0,y8_29,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_535x : Impossible 7 1 s8_535 := impPerm (z := s8_240) (by decide +kernel) s8_240x

def s8_536 : List Sig := [y8_15,x8_3,x8_0,y8_29,x8_4,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_536x : Impossible 7 1 s8_536 := impPerm (z := s8_281) (by decide +kernel) s8_281x

def s8_537 : List Sig := [y8_20,x8_3,x8_1,y8_29,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_537x : Impossible 7 1 s8_537 := impPerm (z := s8_413) (by decide +kernel) s8_413x

def s8_538 : List Sig := [y8_21,x8_1,y8_29,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_538x : Impossible 7 1 s8_538 := impPerm (z := s8_454) (by decide +kernel) s8_454x

def s8_539 : List Sig := [y8_21,x8_3,x8_1,y8_29,x8_4,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_539x : Impossible 7 1 s8_539 := impPerm (z := s8_455) (by decide +kernel) s8_455x

def s8_540 : List Sig := [y8_24,x8_3,x8_2,y8_29,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_540x : Impossible 7 1 s8_540 := rotate_impossible sym8_1 (z := s8_413) (by simp only [s8_540,x8_0,x8_1,x8_2,x8_3,x8_4,y8_24,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_413x

def s8_541 : List Sig := [y8_25,x8_2,y8_29,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_541x : Impossible 7 1 s8_541 := rotate_impossible sym8_1 (z := s8_454) (by simp only [s8_541,x8_0,x8_1,x8_2,x8_3,x8_4,y8_25,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_454x

def s8_542 : List Sig := [y8_25,x8_3,x8_2,y8_29,x8_4,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_542x : Impossible 7 1 s8_542 := rotate_impossible sym8_1 (z := s8_455) (by simp only [s8_542,x8_0,x8_1,x8_2,x8_3,x8_4,y8_25,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_455x

def s8_543 : List Sig := [y8_16,x8_0,y8_29,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_543x : Impossible 7 1 s8_543 := rotate_impossible sym8_0 (z := s8_239) (by simp only [s8_543,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_239x

def s8_544 : List Sig := [y8_16,x8_4,x8_0,y8_29,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_544x : Impossible 7 1 s8_544 := rotate_impossible sym8_0 (z := s8_240) (by simp only [s8_544,x8_0,x8_1,x8_2,x8_3,x8_4,y8_16,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_240x

def s8_545 : List Sig := [y8_17,x8_4,x8_0,y8_29,x8_3,x8_1,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_545x : Impossible 7 1 s8_545 := rotate_impossible sym8_0 (z := s8_281) (by simp only [s8_545,x8_0,x8_1,x8_2,x8_3,x8_4,y8_17,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_281x

def s8_546 : List Sig := [y8_22,x8_4,x8_1,y8_29,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_546x : Impossible 7 1 s8_546 := rotate_impossible sym8_0 (z := s8_413) (by simp only [s8_546,x8_0,x8_1,x8_2,x8_3,x8_4,y8_22,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_413x

def s8_547 : List Sig := [y8_23,x8_1,y8_29,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_547x : Impossible 7 1 s8_547 := rotate_impossible sym8_0 (z := s8_454) (by simp only [s8_547,x8_0,x8_1,x8_2,x8_3,x8_4,y8_23,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_454x

def s8_548 : List Sig := [y8_23,x8_4,x8_1,y8_29,x8_3,x8_0,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_548x : Impossible 7 1 s8_548 := rotate_impossible sym8_0 (z := s8_455) (by simp only [s8_548,x8_0,x8_1,x8_2,x8_3,x8_4,y8_23,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_455x

def s8_549 : List Sig := [y8_26,x8_4,x8_2,y8_29,x8_3,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_549x : Impossible 7 1 s8_549 := rotate_impossible sym8_0 (z := s8_540) (by simp only [s8_549,x8_0,x8_1,x8_2,x8_3,x8_4,y8_26,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_540x

def s8_550 : List Sig := [y8_27,x8_2,y8_29,x8_3,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_550x : Impossible 7 1 s8_550 := rotate_impossible sym8_0 (z := s8_541) (by simp only [s8_550,x8_0,x8_1,x8_2,x8_3,x8_4,y8_27,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_541x

def s8_551 : List Sig := [y8_27,x8_4,x8_2,y8_29,x8_3,x8_0,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_551x : Impossible 7 1 s8_551 := rotate_impossible sym8_0 (z := s8_542) (by simp only [s8_551,x8_0,x8_1,x8_2,x8_3,x8_4,y8_27,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_0_0,rot8_0_1,rot8_0_2,rot8_0_3,rot8_0_4]; decide +kernel) s8_542x

def s8_552 : List Sig := [y8_10,x8_0,x8_1,y8_29,x8_3,x8_4,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_552x : Impossible 7 1 s8_552 := impPerm (z := s8_153) (by decide +kernel) s8_153x

def s8_553 : List Sig := [y8_11,x8_0,x8_1,y8_29,x8_3,x8_4,x8_2]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_553x : Impossible 7 1 s8_553 := impPerm (z := s8_200) (by decide +kernel) s8_200x

def s8_554 : List Sig := [y8_12,x8_0,x8_2,y8_29,x8_3,x8_4,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_554x : Impossible 7 1 s8_554 := rotate_impossible sym8_1 (z := s8_153) (by simp only [s8_554,x8_0,x8_1,x8_2,x8_3,x8_4,y8_12,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_153x

def s8_555 : List Sig := [y8_13,x8_0,x8_2,y8_29,x8_3,x8_4,x8_1]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_555x : Impossible 7 1 s8_555 := rotate_impossible sym8_1 (z := s8_200) (by simp only [s8_555,x8_0,x8_1,x8_2,x8_3,x8_4,y8_13,y8_29,List.map_cons,List.map_nil,action_bin,action_neg,rot8_1_0,rot8_1_1,rot8_1_2,rot8_1_3,rot8_1_4]; decide +kernel) s8_200x

def s8_556 : List Sig := [y8_18,x8_1,x8_2,y8_29,x8_3,x8_4,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_556x : Impossible 7 1 s8_556 := impPerm (z := s8_333) (by decide +kernel) s8_333x

def s8_557 : List Sig := [y8_19,x8_1,x8_2,y8_29,x8_3,x8_4,x8_0]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_557x : Impossible 7 1 s8_557 := impPerm (z := s8_375) (by decide +kernel) s8_375x

def s8_558 : List Sig := [y8_29,x8_3,x8_4,x8_0,x8_1,x8_2]
def s8_558u : List (List Sig) := [s8_511,s8_512,s8_513,s8_514,s8_515,s8_516,s8_517]
lemma s8_558ux (v : List Sig) (h : (!s8_558u.contains v) = false) : Impossible 7 0 v := by
  have hm : v ∈ s8_558u := by simpa using h
  simp only [s8_558u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_511x
  · exact s8_512x
  · exact s8_513x
  · exact s8_514x
  · exact s8_515x
  · exact s8_516x
  · exact s8_517x
def s8_558b : List (List Sig) := [s8_518,s8_519,s8_520,s8_521,s8_522,s8_523,s8_524,s8_525,s8_526,s8_527,s8_528,s8_529,s8_530,s8_531,s8_532,s8_533,s8_534,s8_535,s8_536,s8_537,s8_538,s8_539,s8_540,s8_541,s8_542,s8_543,s8_544,s8_545,s8_546,s8_547,s8_548,s8_549,s8_550,s8_551,s8_552,s8_553,s8_554,s8_555,s8_556,s8_557]
lemma s8_558bx (v : List Sig) (h : (!s8_558b.contains v) = false) : Impossible 7 1 v := by
  have hm : v ∈ s8_558b := by simpa using h
  simp only [s8_558b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_518x
  · exact s8_519x
  · exact s8_520x
  · exact s8_521x
  · exact s8_522x
  · exact s8_523x
  · exact s8_524x
  · exact s8_525x
  · exact s8_526x
  · exact s8_527x
  · exact s8_528x
  · exact s8_529x
  · exact s8_530x
  · exact s8_531x
  · exact s8_532x
  · exact s8_533x
  · exact s8_534x
  · exact s8_535x
  · exact s8_536x
  · exact s8_537x
  · exact s8_538x
  · exact s8_539x
  · exact s8_540x
  · exact s8_541x
  · exact s8_542x
  · exact s8_543x
  · exact s8_544x
  · exact s8_545x
  · exact s8_546x
  · exact s8_547x
  · exact s8_548x
  · exact s8_549x
  · exact s8_550x
  · exact s8_551x
  · exact s8_552x
  · exact s8_553x
  · exact s8_554x
  · exact s8_555x
  · exact s8_556x
  · exact s8_557x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma s8_558x : Impossible 8 1 s8_558 :=
  exclude_step (u := fun v => !s8_558u.contains v) (b := fun v => !s8_558b.contains v) (by decide +kernel) s8_558ux s8_558bx (by decide +kernel)

def s8_559u : List (List Sig) := [s8_36,s8_73,s8_74,s8_111,s8_112]
lemma s8_559ux (v : List Sig) (h : (!s8_559u.contains v) = false) : Impossible 8 0 v := by
  have hm : v ∈ s8_559u := by simpa using h
  simp only [s8_559u,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact s8_36x
  · exact s8_73x
  · exact s8_74x
  · exact s8_111x
  · exact s8_112x
def s8_559b : List (List Sig) := [s8_154,s8_201,s8_202,s8_203,s8_247,s8_288,s8_289,s8_290,s8_334,s8_376,s8_420,s8_462,s8_463,s8_464,s8_465,s8_466,s8_467,s8_468,s8_510,s8_558]
lemma s8_559bx (v : List Sig) (h : (!s8_559b.contains v) = false) : Impossible 8 1 v := by
  have hm : v ∈ s8_559b := by simpa using h
  simp only [s8_559b,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s8_154x
  · exact s8_201x
  · exact s8_202x
  · exact s8_203x
  · exact s8_247x
  · exact s8_288x
  · exact s8_289x
  · exact s8_290x
  · exact s8_334x
  · exact s8_376x
  · exact s8_420x
  · exact s8_462x
  · exact s8_463x
  · exact s8_464x
  · exact s8_465x
  · exact s8_466x
  · exact s8_467x
  · exact s8_468x
  · exact s8_510x
  · exact s8_558x
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative8_1 : Impossible 9 1 r8 :=
  exclude_step (u := fun v => !s8_559u.contains v) (b := fun v => !s8_559b.contains v) (by decide +kernel) s8_559ux s8_559bx (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn8 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941132416 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941132416 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941132416 r8 9 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative8_1 gs o legal hn he
    ⟨[⟨.or,[1,2]⟩,⟨.or,[3,4]⟩,⟨.and,[1,2]⟩,⟨.and,[0,7]⟩,⟨.and,[3,4]⟩,⟨.and,[5,6]⟩,⟨.or,[8,10]⟩,⟨.or,[0,7]⟩,⟨.or,[9,11]⟩,⟨.and,[12,13]⟩],14,by simp [Clean],rfl,by decide +kernel⟩

def r9 : List Sig := [(0xfffffc0000ffffffffffffffffff00003fffffffffffff00003fffffffffffff,0x42a810aa042a810aa042a810aa042a810aa042a810aa042a810aa042a810aa),(0xffffffffff00003ffff00003ffffffffc0000fffffffffffffc0000ffffc0000,0x48b3122cc48b3122cc48b3122cc48b3122cc48b3122cc48b3122cc48b3122cc),(0xffffffffffffffc000000003fffffffffffff00003fffffffffffff000000000,0x913c244f0913c244f0913c244f0913c244f0913c244f0913c244f0913c244f0),(0xfffffffffffffffffffffffc000000000000000003ffffffffffffffffffffff,0xe1c038700e1c038700e1c038700e1c038700e1c038700e1c038700e1c038700),(0xfffffffffffffffffffffffffffffffffffffffffc0000000000000000000000,0xfe003f800fe003f800fe003f800fe003f800fe003f800fe003f800fe003f800)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative9_1 : Impossible 5 1 r9 := exclude_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn9 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3941132800 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 3941132800 x := by
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  exact solve 3941132800 r9 5 (by rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) negative9_1 gs o legal hn he
    ⟨[⟨.or,[1,2]⟩,⟨.and,[1,2]⟩,⟨.or,[0,6]⟩,⟨.and,[4,5]⟩,⟨.or,[3,8]⟩,⟨.and,[7,9]⟩],10,by simp [Clean],rfl,by decide +kernel⟩

end PEqualNP.Outside.L_meta_1427_aux

theorem PEqualNP.Outside.L_meta_1427 : ∀ T ∈ ({0xeae8e800, 0xe8e8e888, 0xeaa8a8a8, 0xeaa8e888, 0xeaaac888, 0xeaaae880, 0xeac8e888, 0xeac8e8c0, 0xeae8e880, 0xeae8ea00} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T h
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1427_aux.fn0
  · exact PEqualNP.Outside.L_meta_1427_aux.fn1
  · exact PEqualNP.Outside.L_meta_1427_aux.fn2
  · exact PEqualNP.Outside.L_meta_1427_aux.fn3
  · exact PEqualNP.Outside.L_meta_1427_aux.fn4
  · exact PEqualNP.Outside.L_meta_1427_aux.fn5
  · exact PEqualNP.Outside.L_meta_1427_aux.fn6
  · exact PEqualNP.Outside.L_meta_1427_aux.fn7
  · exact PEqualNP.Outside.L_meta_1427_aux.fn8
  · exact PEqualNP.Outside.L_meta_1427_aux.fn9
