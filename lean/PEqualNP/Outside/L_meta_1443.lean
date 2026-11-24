import Mathlib
import PEqualNP.Defs
-- The live-wire semantics and search are adapted from L-meta-1007 and L-meta-1445, Apache-2.0.
namespace PEqualNP.Outside.L_meta_1443_aux

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



-- Each bit position pairs a positive and a negative input row.
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
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

theorem cost (T : ℕ) (raw : List Sig) (s : ℕ)
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (samples : ∀ b i, evalT T (sample raw b i) = b)
    (nd : raw.Nodup) (len : raw.length = 5)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (test : ∀ t : Fin 2, search s t.val raw = false)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (single : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (correct : ∀ x, C.eval (List.ofFn x) = evalT T x) : s < C.gates.length := by
  by_contra! small
  obtain ⟨k,t,S,hk,count,live,sub⟩ := extract C.gates raw legal (circuit_target T raw raw_id samples C legal correct)
  have oneNot := notCount C.gates single
  have eq := necessary raw essential live sub
  have size := live_size live
  rw [←eq,List.toFinset_card_of_nodup nd,len] at size
  have good := search_complete live s (by omega) raw nd eq
  exact Bool.false_ne_true ((test ⟨t,by omega⟩).symm.trans good)


open PEqualNP.CircuitLowerBounds

def orc (tbl : List (List Sig)) (f : List Sig → Bool) (v : List Sig) : Bool :=
  if tbl.contains v then false else f v

lemma orc_eq (tbl : List (List Sig)) (f : List Sig → Bool) (h : ∀ v ∈ tbl, f v = false) :
    orc tbl f = f := by
  funext v
  unfold orc
  split
  · rename_i hc
    exact (h v (List.contains_iff_mem.mp hc)).symm
  · rfl

lemma consAll {p : List Sig → Prop} {a : List Sig} {l : List (List Sig)} (ha : p a)
    (hl : ∀ v ∈ l, p v) : ∀ v ∈ a :: l, p v := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | h
  · exact ha
  · exact hl v h

lemma nilAll {p : List Sig → Prop} : ∀ v ∈ ([] : List (List Sig)), p v := by
  intro v hv
  cases hv

def r0 : List Sig := [(0xf000fff000fff000fff000ffffff000ffffffffffff000fff000fff000fff000,0xa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa),(0xffffffffff000000ffffff000ffffff000fff000ffffff000000ffffffffffff,0xc20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c),(0xffffffffffffffff000000000fffffffff000000ffffffffffff000000ffffff,0x430430430430430430430430430430430430430430430430430430430430430),(0xfffffffffffffffffffff000000000000000ffffffffffffffffff000000,0x8c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c0),(0xffffffffffffffffffffffffffffffffffff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative0_0 : search 5 0 r0 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative0_1 : search 5 1 r0 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn0 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276812992 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276812992 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4276812992 r0 5 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative0_0
      · exact negative0_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.and,[0,4]⟩,⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.and,[3,7]⟩,⟨.or,[5,8]⟩,⟨.or,[6,9]⟩],10,by simp,?_,by decide +kernel⟩
  change 5 < gs.length at bound
  change 6 ≤ gs.length
  omega

def r1 : List Sig := [(0xfffffffff001fffff800fffffc007ffffffffff800fffffffffff001ffffffff,0x0),(0x1ffc007ffffe003fffff001fffff800ffe003fffff001ffc007ffffe003ff800,0x4248490921242484909212424849092124248490921242484909212424849092),(0xe000007fffffffc00000001ffffffff000003fffffffe000007fffffffc00000,0x949292524a4949292524a4949292524a4949292524a4949292524a4949292524),(0x7fffffffffffffffe00000000000003fffffffffffff80000000000000,0x18e31c638c718e31c638c718e31c638c718e31c638c718e31c638c718e31c638),(0x7fffffffffffffffffffffffffffffc000000000000000000000000000,0x1f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative1_0 : search 3 0 r1 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative1_1 : search 3 1 r1 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn1 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008372970 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008372970 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4008372970 r1 3 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative1_0
      · exact negative1_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.and,[3,4]⟩,⟨.or,[2,5]⟩,⟨.and,[1,6]⟩,⟨.or,[0,7]⟩],8,by simp,?_,by decide +kernel⟩
  change 3 < gs.length at bound
  change 4 ≤ gs.length
  omega

def r2 : List Sig := [(0x1ffffffff001fffff800fffffc007ffffffffff800fffffc007ffffe003fffff,0x4008010020040080100200400801002004008010020040080100200400801002),(0xe003fffffffe003fffff001fffff800ffe003fffff001fffff800fffffc007ff,0x8210420841082104208410821042084108210420841082104208410821042084),(0xfffc007fffffffc00000001ffffffff000003fffffffe00000000ffffffff800,0x14a294528a514a294528a514a294528a514a294528a514a294528a514a294528),(0x7fffffffffffffffe00000000000003ffffffffffffffff00000000000,0x18c318630c618c318630c618c318630c618c318630c618c318630c618c318630),(0x7fffffffffffffffffffffffffffffc000000000000000000000000000,0x1f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative2_0 : search 5 0 r2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative2_1 : search 5 1 r2 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn2 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008373992 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008373992 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4008373992 r2 5 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative2_0
      · exact negative2_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.or,[0,1]⟩,⟨.or,[1,4]⟩,⟨.and,[0,6]⟩,⟨.or,[2,3]⟩,⟨.and,[5,8]⟩,⟨.or,[7,9]⟩],10,by simp,?_,by decide +kernel⟩
  change 5 < gs.length at bound
  change 6 ≤ gs.length
  omega

def r3 : List Sig := [(0xe003fffff001fffff800fffffc007ffffe003fffff001fffff800fffffc007ff,0x40280500a0140280500a0140280500a0140280500a0140280500a0140280500a),(0xfffc007ffffe003fffff001fffff800fffffc007ffffe003fffff001fffff800,0x80300600c0180300600c0180300600c0180300600c0180300600c0180300600c),(0xffffffffffffffc00000001ffffffff000000007fffffffc00000001ffffffff,0x1542a8550aa1542a8550aa1542a8550aa1542a8550aa1542a8550aa1542a8550),(0x7fffffffffffffffe00000000000000007fffffffffffffffe00000000,0x198330660cc198330660cc198330660cc198330660cc198330660cc198330660),(0x7ffffffffffffffffffffffffffffffff8000000000000000000000000,0x1e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative3_0 : search 3 0 r3 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative3_1 : search 3 1 r3 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn3 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4008636128 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4008636128 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4008636128 r3 3 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative3_0
      · exact negative3_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.or,[4,6]⟩,⟨.and,[5,7]⟩],8,by simp,?_,by decide +kernel⟩
  change 3 < gs.length at bound
  change 4 ≤ gs.length
  omega

def r4 : List Sig := [(0x1ffffffff001ffc007ff001fffff800ffffffff800fffffc007ffffe003fffff,0x4208410821042084108210420841082104208410821042084108210420841082),(0xe003fffffffe000007ffffe003fffff001ffffffff001fffff800fffffc007ff,0x8410821042084108210420841082104208410821042084108210420841082104),(0xfffc007ffffffffff800000003fffffffe003fffffffe00000000ffffffff800,0x8a1142284508a1142284508a1142284508a1142284508a1142284508a114228),(0x7ffffffffffffffffffc00000000003ffffffffffffffff00000000000,0x10c2184308610c2184308610c2184308610c2184308610c2184308610c218430),(0x7fffffffffffffffffffffffffffffc000000000000000000000000000,0x1f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative4_0 : search 7 0 r4 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative4_1 : search 7 1 r4 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn4 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276678376 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276678376 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4276678376 r4 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative4_0
      · exact negative4_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.and,[0,1]⟩,⟨.and,[2,3]⟩,⟨.and,[4,6]⟩,⟨.or,[0,7]⟩,⟨.or,[1,8]⟩,⟨.or,[2,3]⟩,⟨.and,[9,10]⟩,⟨.or,[5,11]⟩],12,by simp,?_,by decide +kernel⟩
  change 7 < gs.length at bound
  change 8 ≤ gs.length
  omega

def r5 : List Sig := [(0xfffffffff001ffc007ff001fffff800fffffffffff001fffffffffffffffffff,0x0),(0x1ffc007ffffe000007ffffe003fffff001ffc007ffffe003ff800ffe003ff800,0x44a89512a2544a89512a2544a89512a2544a89512a2544a89512a2544a89512a),(0xe000007ffffffffff800000003fffffffe000007fffffffc00000fffffc00000,0x89312624c4989312624c4989312624c4989312624c4989312624c4989312624c),(0x7ffffffffffffffffffc00000000000007fffffffffffff00000000000,0x11c2384708e11c2384708e11c2384708e11c2384708e11c2384708e11c238470),(0x7ffffffffffffffffffffffffffffffff8000000000000000000000000,0x1e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative5_0 : search 7 0 r5 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative5_1 : search 7 1 r5 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn5 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276808362 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276808362 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4276808362 r5 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative5_0
      · exact negative5_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.and,[1,2]⟩,⟨.and,[1,3]⟩,⟨.and,[2,4]⟩,⟨.or,[6,7]⟩,⟨.and,[3,4]⟩,⟨.or,[5,9]⟩,⟨.and,[8,10]⟩,⟨.or,[0,11]⟩],12,by simp,?_,by decide +kernel⟩
  change 7 < gs.length at bound
  change 8 ≤ gs.length
  omega

def q6_0 : Sig := (0x1ffffffff001ffc007ff001fffff800fffffffffff001ffffffffffe003fffff,0x4008010020040080100200400801002004008010020040080100200400801002)
def q6_1 : Sig := (0xe003fffffffe000007ffffe003fffff001ffc007ffffe003ff800fffffc007ff,0x8490921242484909212424849092124248490921242484909212424849092124)
def q6_2 : Sig := (0xfffc007ffffffffff800000003fffffffe000007fffffffc00000ffffffff800,0x921242484909212424849092124248490921242484909212424849092124248)
def q6_3 : Sig := (0x7ffffffffffffffffffc00000000000007fffffffffffff00000000000,0x11c2384708e11c2384708e11c2384708e11c2384708e11c2384708e11c238470)
def q6_4 : Sig := (0x7ffffffffffffffffffffffffffffffff8000000000000000000000000,0x1e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780)
def r6 : List Sig := [q6_0, q6_1, q6_2, q6_3, q6_4]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b0_ : search 6 0 [(bin false (bin false q6_0 q6_1) q6_2), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b1_ : search 6 0 [(bin false (bin false q6_0 q6_1) q6_2), (bin false q6_0 q6_1), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b2_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_2), q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b3_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_2), (bin false q6_0 q6_1), q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b4_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_2), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b5_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_2), (bin false q6_0 q6_1), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b6_ : search 6 0 [(bin false (bin false q6_0 q6_1) q6_3), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b7_ : search 6 0 [(bin false (bin false q6_0 q6_1) q6_3), (bin false q6_0 q6_1), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b8_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_3), q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b9_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_3), (bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b10_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_3), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b11_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_3), (bin false q6_0 q6_1), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b12_ : search 6 0 [(bin false (bin false q6_0 q6_1) q6_4), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b13_ : search 6 0 [(bin false (bin false q6_0 q6_1) q6_4), (bin false q6_0 q6_1), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b14_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_4), q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b15_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_4), (bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b16_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_4), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b17_ : search 6 0 [(bin true (bin false q6_0 q6_1) q6_4), (bin false q6_0 q6_1), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b18_ : search 6 0 [(bin true q6_0 q6_1), q6_0, (bin false q6_0 q6_1), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b19_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_1), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b20_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_1), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b21_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_1), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b22_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_1), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b23_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_1), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b24_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_1), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b25_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_1), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b26_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_1), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b27_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_1), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b28_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_1), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b29_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_1), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b30_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_1), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b31_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_1), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b32_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_1), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b33_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_1), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b34_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_1), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b35_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_1), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b36_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_1), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_b37_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_1), q6_0, q6_1, q6_2] = false := by decide +kernel

def tbf6t0_b0_b : List (List Sig) := [[(bin false (bin false q6_0 q6_1) q6_2), q6_2, q6_0, q6_1, q6_3, q6_4], [(bin false (bin false q6_0 q6_1) q6_2), (bin false q6_0 q6_1), q6_2, q6_0, q6_1, q6_3, q6_4], [(bin true (bin false q6_0 q6_1) q6_2), q6_0, q6_1, q6_3, q6_4], [(bin true (bin false q6_0 q6_1) q6_2), (bin false q6_0 q6_1), q6_0, q6_1, q6_3, q6_4], [(bin true (bin false q6_0 q6_1) q6_2), q6_2, q6_0, q6_1, q6_3, q6_4], [(bin true (bin false q6_0 q6_1) q6_2), (bin false q6_0 q6_1), q6_2, q6_0, q6_1, q6_3, q6_4], [(bin false (bin false q6_0 q6_1) q6_3), q6_3, q6_0, q6_1, q6_2, q6_4], [(bin false (bin false q6_0 q6_1) q6_3), (bin false q6_0 q6_1), q6_3, q6_0, q6_1, q6_2, q6_4], [(bin true (bin false q6_0 q6_1) q6_3), q6_0, q6_1, q6_2, q6_4], [(bin true (bin false q6_0 q6_1) q6_3), (bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_4], [(bin true (bin false q6_0 q6_1) q6_3), q6_3, q6_0, q6_1, q6_2, q6_4], [(bin true (bin false q6_0 q6_1) q6_3), (bin false q6_0 q6_1), q6_3, q6_0, q6_1, q6_2, q6_4], [(bin false (bin false q6_0 q6_1) q6_4), q6_4, q6_0, q6_1, q6_2, q6_3], [(bin false (bin false q6_0 q6_1) q6_4), (bin false q6_0 q6_1), q6_4, q6_0, q6_1, q6_2, q6_3], [(bin true (bin false q6_0 q6_1) q6_4), q6_0, q6_1, q6_2, q6_3], [(bin true (bin false q6_0 q6_1) q6_4), (bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_3], [(bin true (bin false q6_0 q6_1) q6_4), q6_4, q6_0, q6_1, q6_2, q6_3], [(bin true (bin false q6_0 q6_1) q6_4), (bin false q6_0 q6_1), q6_4, q6_0, q6_1, q6_2, q6_3], [(bin true q6_0 q6_1), q6_0, (bin false q6_0 q6_1), q6_2, q6_3, q6_4], [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_1), q6_2, q6_3, q6_4], [(bin false q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_1), q6_1, q6_3, q6_4], [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_1), q6_1, q6_3, q6_4], [(bin false q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_1), q6_1, q6_2, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_1), q6_1, q6_2, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_1), q6_1, q6_2, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_1), q6_1, q6_2, q6_3], [(bin false q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_1), q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_1), q6_0, q6_3, q6_4], [(bin false q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_1), q6_0, q6_2, q6_4], [(bin true q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_1), q6_0, q6_2, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_1), q6_0, q6_2, q6_3], [(bin true q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_1), q6_0, q6_2, q6_3], [(bin false q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_1), q6_0, q6_1, q6_4], [(bin true q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_1), q6_0, q6_1, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_1), q6_0, q6_1, q6_3], [(bin true q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_1), q6_0, q6_1, q6_3], [(bin false q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_1), q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_1), q6_0, q6_1, q6_2]]

lemma allf6t0_b0_b : ∀ v ∈ tbf6t0_b0_b, search 6 0 v = false :=
  consAll nf6t0_b0_b0_ (consAll nf6t0_b0_b1_ (consAll nf6t0_b0_b2_ (consAll nf6t0_b0_b3_ (consAll nf6t0_b0_b4_ (consAll nf6t0_b0_b5_ (consAll nf6t0_b0_b6_ (consAll nf6t0_b0_b7_ (consAll nf6t0_b0_b8_ (consAll nf6t0_b0_b9_ (consAll nf6t0_b0_b10_ (consAll nf6t0_b0_b11_ (consAll nf6t0_b0_b12_ (consAll nf6t0_b0_b13_ (consAll nf6t0_b0_b14_ (consAll nf6t0_b0_b15_ (consAll nf6t0_b0_b16_ (consAll nf6t0_b0_b17_ (consAll nf6t0_b0_b18_ (consAll nf6t0_b0_b19_ (consAll nf6t0_b0_b20_ (consAll nf6t0_b0_b21_ (consAll nf6t0_b0_b22_ (consAll nf6t0_b0_b23_ (consAll nf6t0_b0_b24_ (consAll nf6t0_b0_b25_ (consAll nf6t0_b0_b26_ (consAll nf6t0_b0_b27_ (consAll nf6t0_b0_b28_ (consAll nf6t0_b0_b29_ (consAll nf6t0_b0_b30_ (consAll nf6t0_b0_b31_ (consAll nf6t0_b0_b32_ (consAll nf6t0_b0_b33_ (consAll nf6t0_b0_b34_ (consAll nf6t0_b0_b35_ (consAll nf6t0_b0_b36_ (consAll nf6t0_b0_b37_ (nilAll))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b0_ : search 7 0 [(bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by
  have e := search.eq_2 0 [(bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4] 6
  rw [← orc_eq tbf6t0_b0_b (search 6 0) allf6t0_b0_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b0_ : search 6 0 [(bin false (bin true q6_0 q6_1) q6_2), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b1_ : search 6 0 [(bin false (bin true q6_0 q6_1) q6_2), (bin true q6_0 q6_1), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b2_ : search 6 0 [(bin true (bin true q6_0 q6_1) q6_2), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b3_ : search 6 0 [(bin true (bin true q6_0 q6_1) q6_2), (bin true q6_0 q6_1), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b4_ : search 6 0 [(bin false (bin true q6_0 q6_1) q6_3), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b5_ : search 6 0 [(bin false (bin true q6_0 q6_1) q6_3), (bin true q6_0 q6_1), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b6_ : search 6 0 [(bin true (bin true q6_0 q6_1) q6_3), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b7_ : search 6 0 [(bin true (bin true q6_0 q6_1) q6_3), (bin true q6_0 q6_1), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b8_ : search 6 0 [(bin false (bin true q6_0 q6_1) q6_4), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b9_ : search 6 0 [(bin false (bin true q6_0 q6_1) q6_4), (bin true q6_0 q6_1), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b10_ : search 6 0 [(bin true (bin true q6_0 q6_1) q6_4), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b11_ : search 6 0 [(bin true (bin true q6_0 q6_1) q6_4), (bin true q6_0 q6_1), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b12_ : search 6 0 [(bin false q6_0 q6_1), q6_0, (bin true q6_0 q6_1), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b13_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_1), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b14_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_1), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b15_ : search 6 0 [(bin true q6_0 q6_2), q6_2, (bin true q6_0 q6_1), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b16_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_1), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b17_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_1), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b18_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_1), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b19_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_1), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b20_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_1), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b21_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_1), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b22_ : search 6 0 [(bin true q6_1 q6_2), q6_2, (bin true q6_0 q6_1), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b23_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_1), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b24_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_1), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b25_ : search 6 0 [(bin true q6_1 q6_3), q6_3, (bin true q6_0 q6_1), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b26_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_1), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b27_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_1), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b28_ : search 6 0 [(bin true q6_1 q6_4), q6_4, (bin true q6_0 q6_1), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b29_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_1), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b30_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_1), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b31_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_1), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b32_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_1), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b33_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_1), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b34_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_1), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_b35_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_1), q6_0, q6_1, q6_2] = false := by decide +kernel

def tbf6t0_b1_b : List (List Sig) := [[(bin false (bin true q6_0 q6_1) q6_2), q6_2, q6_0, q6_1, q6_3, q6_4], [(bin false (bin true q6_0 q6_1) q6_2), (bin true q6_0 q6_1), q6_2, q6_0, q6_1, q6_3, q6_4], [(bin true (bin true q6_0 q6_1) q6_2), q6_2, q6_0, q6_1, q6_3, q6_4], [(bin true (bin true q6_0 q6_1) q6_2), (bin true q6_0 q6_1), q6_2, q6_0, q6_1, q6_3, q6_4], [(bin false (bin true q6_0 q6_1) q6_3), q6_3, q6_0, q6_1, q6_2, q6_4], [(bin false (bin true q6_0 q6_1) q6_3), (bin true q6_0 q6_1), q6_3, q6_0, q6_1, q6_2, q6_4], [(bin true (bin true q6_0 q6_1) q6_3), q6_3, q6_0, q6_1, q6_2, q6_4], [(bin true (bin true q6_0 q6_1) q6_3), (bin true q6_0 q6_1), q6_3, q6_0, q6_1, q6_2, q6_4], [(bin false (bin true q6_0 q6_1) q6_4), q6_4, q6_0, q6_1, q6_2, q6_3], [(bin false (bin true q6_0 q6_1) q6_4), (bin true q6_0 q6_1), q6_4, q6_0, q6_1, q6_2, q6_3], [(bin true (bin true q6_0 q6_1) q6_4), q6_4, q6_0, q6_1, q6_2, q6_3], [(bin true (bin true q6_0 q6_1) q6_4), (bin true q6_0 q6_1), q6_4, q6_0, q6_1, q6_2, q6_3], [(bin false q6_0 q6_1), q6_0, (bin true q6_0 q6_1), q6_2, q6_3, q6_4], [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_1), q6_2, q6_3, q6_4], [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_1), q6_1, q6_3, q6_4], [(bin true q6_0 q6_2), q6_2, (bin true q6_0 q6_1), q6_1, q6_3, q6_4], [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_1), q6_1, q6_3, q6_4], [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_1), q6_1, q6_2, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_1), q6_1, q6_2, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_1), q6_1, q6_2, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_1), q6_1, q6_2, q6_3], [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_1), q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_2, (bin true q6_0 q6_1), q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_1), q6_0, q6_3, q6_4], [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_1), q6_0, q6_2, q6_4], [(bin true q6_1 q6_3), q6_3, (bin true q6_0 q6_1), q6_0, q6_2, q6_4], [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_1), q6_0, q6_2, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_1), q6_0, q6_2, q6_3], [(bin true q6_1 q6_4), q6_4, (bin true q6_0 q6_1), q6_0, q6_2, q6_3], [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_1), q6_0, q6_2, q6_3], [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_1), q6_0, q6_1, q6_4], [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_1), q6_0, q6_1, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_1), q6_0, q6_1, q6_3], [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_1), q6_0, q6_1, q6_3], [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_1), q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_1), q6_0, q6_1, q6_2]]

lemma allf6t0_b1_b : ∀ v ∈ tbf6t0_b1_b, search 6 0 v = false :=
  consAll nf6t0_b1_b0_ (consAll nf6t0_b1_b1_ (consAll nf6t0_b1_b2_ (consAll nf6t0_b1_b3_ (consAll nf6t0_b1_b4_ (consAll nf6t0_b1_b5_ (consAll nf6t0_b1_b6_ (consAll nf6t0_b1_b7_ (consAll nf6t0_b1_b8_ (consAll nf6t0_b1_b9_ (consAll nf6t0_b1_b10_ (consAll nf6t0_b1_b11_ (consAll nf6t0_b1_b12_ (consAll nf6t0_b1_b13_ (consAll nf6t0_b1_b14_ (consAll nf6t0_b1_b15_ (consAll nf6t0_b1_b16_ (consAll nf6t0_b1_b17_ (consAll nf6t0_b1_b18_ (consAll nf6t0_b1_b19_ (consAll nf6t0_b1_b20_ (consAll nf6t0_b1_b21_ (consAll nf6t0_b1_b22_ (consAll nf6t0_b1_b23_ (consAll nf6t0_b1_b24_ (consAll nf6t0_b1_b25_ (consAll nf6t0_b1_b26_ (consAll nf6t0_b1_b27_ (consAll nf6t0_b1_b28_ (consAll nf6t0_b1_b29_ (consAll nf6t0_b1_b30_ (consAll nf6t0_b1_b31_ (consAll nf6t0_b1_b32_ (consAll nf6t0_b1_b33_ (consAll nf6t0_b1_b34_ (consAll nf6t0_b1_b35_ (nilAll))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b1_ : search 7 0 [(bin true q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by
  have e := search.eq_2 0 [(bin true q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4] 6
  rw [← orc_eq tbf6t0_b1_b (search 6 0) allf6t0_b1_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b0_ : search 6 0 [(bin false (bin false q6_0 q6_2) q6_1), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b1_ : search 6 0 [(bin false (bin false q6_0 q6_2) q6_1), (bin false q6_0 q6_2), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b2_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_1), q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b3_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_1), (bin false q6_0 q6_2), q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b4_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_1), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b5_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_1), (bin false q6_0 q6_2), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b6_ : search 6 0 [(bin false (bin false q6_0 q6_2) q6_3), q6_3, q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b7_ : search 6 0 [(bin false (bin false q6_0 q6_2) q6_3), (bin false q6_0 q6_2), q6_3, q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b8_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_3), q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b9_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_3), (bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b10_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_3), q6_3, q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b11_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_3), (bin false q6_0 q6_2), q6_3, q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b12_ : search 6 0 [(bin false (bin false q6_0 q6_2) q6_4), q6_4, q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b13_ : search 6 0 [(bin false (bin false q6_0 q6_2) q6_4), (bin false q6_0 q6_2), q6_4, q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b14_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_4), q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b15_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_4), (bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b16_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_4), q6_4, q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b17_ : search 6 0 [(bin true (bin false q6_0 q6_2) q6_4), (bin false q6_0 q6_2), q6_4, q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b18_ : search 6 0 [(bin true q6_0 q6_2), q6_0, (bin false q6_0 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b19_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b20_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b21_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b22_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_2), q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b23_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_2), q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b24_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_2), q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b25_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_2), q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b26_ : search 6 0 [(bin false q6_2 q6_1), q6_2, q6_1, (bin false q6_0 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b27_ : search 6 0 [(bin true q6_2 q6_1), q6_2, q6_1, (bin false q6_0 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b28_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_2), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b29_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_2), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b30_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_2), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b31_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_2), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b32_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_2), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b33_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_2), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b34_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_2), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b35_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_2), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b36_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_2), q6_0, q6_2, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_b37_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_2), q6_0, q6_2, q6_1] = false := by decide +kernel

def tbf6t0_b2_b : List (List Sig) := [[(bin false (bin false q6_0 q6_2) q6_1), q6_1, q6_0, q6_2, q6_3, q6_4], [(bin false (bin false q6_0 q6_2) q6_1), (bin false q6_0 q6_2), q6_1, q6_0, q6_2, q6_3, q6_4], [(bin true (bin false q6_0 q6_2) q6_1), q6_0, q6_2, q6_3, q6_4], [(bin true (bin false q6_0 q6_2) q6_1), (bin false q6_0 q6_2), q6_0, q6_2, q6_3, q6_4], [(bin true (bin false q6_0 q6_2) q6_1), q6_1, q6_0, q6_2, q6_3, q6_4], [(bin true (bin false q6_0 q6_2) q6_1), (bin false q6_0 q6_2), q6_1, q6_0, q6_2, q6_3, q6_4], [(bin false (bin false q6_0 q6_2) q6_3), q6_3, q6_0, q6_2, q6_1, q6_4], [(bin false (bin false q6_0 q6_2) q6_3), (bin false q6_0 q6_2), q6_3, q6_0, q6_2, q6_1, q6_4], [(bin true (bin false q6_0 q6_2) q6_3), q6_0, q6_2, q6_1, q6_4], [(bin true (bin false q6_0 q6_2) q6_3), (bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_4], [(bin true (bin false q6_0 q6_2) q6_3), q6_3, q6_0, q6_2, q6_1, q6_4], [(bin true (bin false q6_0 q6_2) q6_3), (bin false q6_0 q6_2), q6_3, q6_0, q6_2, q6_1, q6_4], [(bin false (bin false q6_0 q6_2) q6_4), q6_4, q6_0, q6_2, q6_1, q6_3], [(bin false (bin false q6_0 q6_2) q6_4), (bin false q6_0 q6_2), q6_4, q6_0, q6_2, q6_1, q6_3], [(bin true (bin false q6_0 q6_2) q6_4), q6_0, q6_2, q6_1, q6_3], [(bin true (bin false q6_0 q6_2) q6_4), (bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_3], [(bin true (bin false q6_0 q6_2) q6_4), q6_4, q6_0, q6_2, q6_1, q6_3], [(bin true (bin false q6_0 q6_2) q6_4), (bin false q6_0 q6_2), q6_4, q6_0, q6_2, q6_1, q6_3], [(bin true q6_0 q6_2), q6_0, (bin false q6_0 q6_2), q6_1, q6_3, q6_4], [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_2), q6_1, q6_3, q6_4], [(bin false q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_2), q6_2, q6_3, q6_4], [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_2), q6_2, q6_3, q6_4], [(bin false q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_2), q6_2, q6_1, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_2), q6_2, q6_1, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_2), q6_2, q6_1, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_2), q6_2, q6_1, q6_3], [(bin false q6_2 q6_1), q6_2, q6_1, (bin false q6_0 q6_2), q6_0, q6_3, q6_4], [(bin true q6_2 q6_1), q6_2, q6_1, (bin false q6_0 q6_2), q6_0, q6_3, q6_4], [(bin false q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_2), q6_0, q6_1, q6_4], [(bin true q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_2), q6_0, q6_1, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_2), q6_0, q6_1, q6_3], [(bin true q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_2), q6_0, q6_1, q6_3], [(bin false q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_2), q6_0, q6_2, q6_4], [(bin true q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_2), q6_0, q6_2, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_2), q6_0, q6_2, q6_3], [(bin true q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_2), q6_0, q6_2, q6_3], [(bin false q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_2), q6_0, q6_2, q6_1], [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_2), q6_0, q6_2, q6_1]]

lemma allf6t0_b2_b : ∀ v ∈ tbf6t0_b2_b, search 6 0 v = false :=
  consAll nf6t0_b2_b0_ (consAll nf6t0_b2_b1_ (consAll nf6t0_b2_b2_ (consAll nf6t0_b2_b3_ (consAll nf6t0_b2_b4_ (consAll nf6t0_b2_b5_ (consAll nf6t0_b2_b6_ (consAll nf6t0_b2_b7_ (consAll nf6t0_b2_b8_ (consAll nf6t0_b2_b9_ (consAll nf6t0_b2_b10_ (consAll nf6t0_b2_b11_ (consAll nf6t0_b2_b12_ (consAll nf6t0_b2_b13_ (consAll nf6t0_b2_b14_ (consAll nf6t0_b2_b15_ (consAll nf6t0_b2_b16_ (consAll nf6t0_b2_b17_ (consAll nf6t0_b2_b18_ (consAll nf6t0_b2_b19_ (consAll nf6t0_b2_b20_ (consAll nf6t0_b2_b21_ (consAll nf6t0_b2_b22_ (consAll nf6t0_b2_b23_ (consAll nf6t0_b2_b24_ (consAll nf6t0_b2_b25_ (consAll nf6t0_b2_b26_ (consAll nf6t0_b2_b27_ (consAll nf6t0_b2_b28_ (consAll nf6t0_b2_b29_ (consAll nf6t0_b2_b30_ (consAll nf6t0_b2_b31_ (consAll nf6t0_b2_b32_ (consAll nf6t0_b2_b33_ (consAll nf6t0_b2_b34_ (consAll nf6t0_b2_b35_ (consAll nf6t0_b2_b36_ (consAll nf6t0_b2_b37_ (nilAll))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b2_ : search 7 0 [(bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4] = false := by
  have e := search.eq_2 0 [(bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4] 6
  rw [← orc_eq tbf6t0_b2_b (search 6 0) allf6t0_b2_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b0_ : search 6 0 [(bin false (bin true q6_0 q6_2) q6_1), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b1_ : search 6 0 [(bin false (bin true q6_0 q6_2) q6_1), (bin true q6_0 q6_2), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b2_ : search 6 0 [(bin true (bin true q6_0 q6_2) q6_1), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b3_ : search 6 0 [(bin true (bin true q6_0 q6_2) q6_1), (bin true q6_0 q6_2), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b4_ : search 6 0 [(bin false (bin true q6_0 q6_2) q6_3), q6_3, q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b5_ : search 6 0 [(bin false (bin true q6_0 q6_2) q6_3), (bin true q6_0 q6_2), q6_3, q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b6_ : search 6 0 [(bin true (bin true q6_0 q6_2) q6_3), q6_3, q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b7_ : search 6 0 [(bin true (bin true q6_0 q6_2) q6_3), (bin true q6_0 q6_2), q6_3, q6_0, q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b8_ : search 6 0 [(bin false (bin true q6_0 q6_2) q6_4), q6_4, q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b9_ : search 6 0 [(bin false (bin true q6_0 q6_2) q6_4), (bin true q6_0 q6_2), q6_4, q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b10_ : search 6 0 [(bin true (bin true q6_0 q6_2) q6_4), q6_4, q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b11_ : search 6 0 [(bin true (bin true q6_0 q6_2) q6_4), (bin true q6_0 q6_2), q6_4, q6_0, q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b12_ : search 6 0 [(bin false q6_0 q6_2), q6_0, (bin true q6_0 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b13_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b14_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b15_ : search 6 0 [(bin true q6_0 q6_1), q6_1, (bin true q6_0 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b16_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b17_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_2), q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b18_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_2), q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b19_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_2), q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b20_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_2), q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b21_ : search 6 0 [(bin false q6_2 q6_1), q6_2, q6_1, (bin true q6_0 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b22_ : search 6 0 [(bin true q6_2 q6_1), q6_1, (bin true q6_0 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b23_ : search 6 0 [(bin true q6_2 q6_1), q6_2, q6_1, (bin true q6_0 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b24_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_2), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b25_ : search 6 0 [(bin true q6_2 q6_3), q6_3, (bin true q6_0 q6_2), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b26_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_2), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b27_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_2), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b28_ : search 6 0 [(bin true q6_2 q6_4), q6_4, (bin true q6_0 q6_2), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b29_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_2), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b30_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_2), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b31_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_2), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b32_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_2), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b33_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_2), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b34_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_2), q6_0, q6_2, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_b35_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_2), q6_0, q6_2, q6_1] = false := by decide +kernel

def tbf6t0_b3_b : List (List Sig) := [[(bin false (bin true q6_0 q6_2) q6_1), q6_1, q6_0, q6_2, q6_3, q6_4], [(bin false (bin true q6_0 q6_2) q6_1), (bin true q6_0 q6_2), q6_1, q6_0, q6_2, q6_3, q6_4], [(bin true (bin true q6_0 q6_2) q6_1), q6_1, q6_0, q6_2, q6_3, q6_4], [(bin true (bin true q6_0 q6_2) q6_1), (bin true q6_0 q6_2), q6_1, q6_0, q6_2, q6_3, q6_4], [(bin false (bin true q6_0 q6_2) q6_3), q6_3, q6_0, q6_2, q6_1, q6_4], [(bin false (bin true q6_0 q6_2) q6_3), (bin true q6_0 q6_2), q6_3, q6_0, q6_2, q6_1, q6_4], [(bin true (bin true q6_0 q6_2) q6_3), q6_3, q6_0, q6_2, q6_1, q6_4], [(bin true (bin true q6_0 q6_2) q6_3), (bin true q6_0 q6_2), q6_3, q6_0, q6_2, q6_1, q6_4], [(bin false (bin true q6_0 q6_2) q6_4), q6_4, q6_0, q6_2, q6_1, q6_3], [(bin false (bin true q6_0 q6_2) q6_4), (bin true q6_0 q6_2), q6_4, q6_0, q6_2, q6_1, q6_3], [(bin true (bin true q6_0 q6_2) q6_4), q6_4, q6_0, q6_2, q6_1, q6_3], [(bin true (bin true q6_0 q6_2) q6_4), (bin true q6_0 q6_2), q6_4, q6_0, q6_2, q6_1, q6_3], [(bin false q6_0 q6_2), q6_0, (bin true q6_0 q6_2), q6_1, q6_3, q6_4], [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_2), q6_1, q6_3, q6_4], [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_2), q6_2, q6_3, q6_4], [(bin true q6_0 q6_1), q6_1, (bin true q6_0 q6_2), q6_2, q6_3, q6_4], [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_2), q6_2, q6_3, q6_4], [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_2), q6_2, q6_1, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_2), q6_2, q6_1, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_2), q6_2, q6_1, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_2), q6_2, q6_1, q6_3], [(bin false q6_2 q6_1), q6_2, q6_1, (bin true q6_0 q6_2), q6_0, q6_3, q6_4], [(bin true q6_2 q6_1), q6_1, (bin true q6_0 q6_2), q6_0, q6_3, q6_4], [(bin true q6_2 q6_1), q6_2, q6_1, (bin true q6_0 q6_2), q6_0, q6_3, q6_4], [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_2), q6_0, q6_1, q6_4], [(bin true q6_2 q6_3), q6_3, (bin true q6_0 q6_2), q6_0, q6_1, q6_4], [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_2), q6_0, q6_1, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_2), q6_0, q6_1, q6_3], [(bin true q6_2 q6_4), q6_4, (bin true q6_0 q6_2), q6_0, q6_1, q6_3], [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_2), q6_0, q6_1, q6_3], [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_2), q6_0, q6_2, q6_4], [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_2), q6_0, q6_2, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_2), q6_0, q6_2, q6_3], [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_2), q6_0, q6_2, q6_3], [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_2), q6_0, q6_2, q6_1], [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_2), q6_0, q6_2, q6_1]]

lemma allf6t0_b3_b : ∀ v ∈ tbf6t0_b3_b, search 6 0 v = false :=
  consAll nf6t0_b3_b0_ (consAll nf6t0_b3_b1_ (consAll nf6t0_b3_b2_ (consAll nf6t0_b3_b3_ (consAll nf6t0_b3_b4_ (consAll nf6t0_b3_b5_ (consAll nf6t0_b3_b6_ (consAll nf6t0_b3_b7_ (consAll nf6t0_b3_b8_ (consAll nf6t0_b3_b9_ (consAll nf6t0_b3_b10_ (consAll nf6t0_b3_b11_ (consAll nf6t0_b3_b12_ (consAll nf6t0_b3_b13_ (consAll nf6t0_b3_b14_ (consAll nf6t0_b3_b15_ (consAll nf6t0_b3_b16_ (consAll nf6t0_b3_b17_ (consAll nf6t0_b3_b18_ (consAll nf6t0_b3_b19_ (consAll nf6t0_b3_b20_ (consAll nf6t0_b3_b21_ (consAll nf6t0_b3_b22_ (consAll nf6t0_b3_b23_ (consAll nf6t0_b3_b24_ (consAll nf6t0_b3_b25_ (consAll nf6t0_b3_b26_ (consAll nf6t0_b3_b27_ (consAll nf6t0_b3_b28_ (consAll nf6t0_b3_b29_ (consAll nf6t0_b3_b30_ (consAll nf6t0_b3_b31_ (consAll nf6t0_b3_b32_ (consAll nf6t0_b3_b33_ (consAll nf6t0_b3_b34_ (consAll nf6t0_b3_b35_ (nilAll))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b3_ : search 7 0 [(bin true q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4] = false := by
  have e := search.eq_2 0 [(bin true q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4] 6
  rw [← orc_eq tbf6t0_b3_b (search 6 0) allf6t0_b3_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b0_ : search 6 0 [(bin false (bin false q6_0 q6_3) q6_1), q6_1, q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b1_ : search 6 0 [(bin false (bin false q6_0 q6_3) q6_1), (bin false q6_0 q6_3), q6_1, q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b2_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_1), q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b3_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_1), (bin false q6_0 q6_3), q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b4_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_1), q6_1, q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b5_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_1), (bin false q6_0 q6_3), q6_1, q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b6_ : search 6 0 [(bin false (bin false q6_0 q6_3) q6_2), q6_2, q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b7_ : search 6 0 [(bin false (bin false q6_0 q6_3) q6_2), (bin false q6_0 q6_3), q6_2, q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b8_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_2), q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b9_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_2), (bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b10_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_2), q6_2, q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b11_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_2), (bin false q6_0 q6_3), q6_2, q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b12_ : search 6 0 [(bin false (bin false q6_0 q6_3) q6_4), q6_4, q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b13_ : search 6 0 [(bin false (bin false q6_0 q6_3) q6_4), (bin false q6_0 q6_3), q6_4, q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b14_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_4), q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b15_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_4), (bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b16_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_4), q6_4, q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b17_ : search 6 0 [(bin true (bin false q6_0 q6_3) q6_4), (bin false q6_0 q6_3), q6_4, q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b18_ : search 6 0 [(bin true q6_0 q6_3), q6_0, (bin false q6_0 q6_3), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b19_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_3), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b20_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_3), q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b21_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_3), q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b22_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_3), q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b23_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_3), q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b24_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_3), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b25_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_3), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b26_ : search 6 0 [(bin false q6_3 q6_1), q6_3, q6_1, (bin false q6_0 q6_3), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b27_ : search 6 0 [(bin true q6_3 q6_1), q6_3, q6_1, (bin false q6_0 q6_3), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b28_ : search 6 0 [(bin false q6_3 q6_2), q6_3, q6_2, (bin false q6_0 q6_3), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b29_ : search 6 0 [(bin true q6_3 q6_2), q6_3, q6_2, (bin false q6_0 q6_3), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b30_ : search 6 0 [(bin false q6_3 q6_4), q6_4, (bin false q6_0 q6_3), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b31_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_3), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b32_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_3), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b33_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_3), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b34_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_3), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b35_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_3), q6_0, q6_3, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b36_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_3), q6_0, q6_3, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b37_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_3), q6_0, q6_3, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_b38_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_3), q6_0, q6_3, q6_1] = false := by decide +kernel

def tbf6t0_b4_b : List (List Sig) := [[(bin false (bin false q6_0 q6_3) q6_1), q6_1, q6_0, q6_3, q6_2, q6_4], [(bin false (bin false q6_0 q6_3) q6_1), (bin false q6_0 q6_3), q6_1, q6_0, q6_3, q6_2, q6_4], [(bin true (bin false q6_0 q6_3) q6_1), q6_0, q6_3, q6_2, q6_4], [(bin true (bin false q6_0 q6_3) q6_1), (bin false q6_0 q6_3), q6_0, q6_3, q6_2, q6_4], [(bin true (bin false q6_0 q6_3) q6_1), q6_1, q6_0, q6_3, q6_2, q6_4], [(bin true (bin false q6_0 q6_3) q6_1), (bin false q6_0 q6_3), q6_1, q6_0, q6_3, q6_2, q6_4], [(bin false (bin false q6_0 q6_3) q6_2), q6_2, q6_0, q6_3, q6_1, q6_4], [(bin false (bin false q6_0 q6_3) q6_2), (bin false q6_0 q6_3), q6_2, q6_0, q6_3, q6_1, q6_4], [(bin true (bin false q6_0 q6_3) q6_2), q6_0, q6_3, q6_1, q6_4], [(bin true (bin false q6_0 q6_3) q6_2), (bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_4], [(bin true (bin false q6_0 q6_3) q6_2), q6_2, q6_0, q6_3, q6_1, q6_4], [(bin true (bin false q6_0 q6_3) q6_2), (bin false q6_0 q6_3), q6_2, q6_0, q6_3, q6_1, q6_4], [(bin false (bin false q6_0 q6_3) q6_4), q6_4, q6_0, q6_3, q6_1, q6_2], [(bin false (bin false q6_0 q6_3) q6_4), (bin false q6_0 q6_3), q6_4, q6_0, q6_3, q6_1, q6_2], [(bin true (bin false q6_0 q6_3) q6_4), q6_0, q6_3, q6_1, q6_2], [(bin true (bin false q6_0 q6_3) q6_4), (bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_2], [(bin true (bin false q6_0 q6_3) q6_4), q6_4, q6_0, q6_3, q6_1, q6_2], [(bin true (bin false q6_0 q6_3) q6_4), (bin false q6_0 q6_3), q6_4, q6_0, q6_3, q6_1, q6_2], [(bin true q6_0 q6_3), q6_0, (bin false q6_0 q6_3), q6_1, q6_2, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_3), q6_1, q6_2, q6_4], [(bin false q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_3), q6_3, q6_2, q6_4], [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_3), q6_3, q6_2, q6_4], [(bin false q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_3), q6_3, q6_1, q6_4], [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_3), q6_3, q6_1, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_3), q6_3, q6_1, q6_2], [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_3), q6_3, q6_1, q6_2], [(bin false q6_3 q6_1), q6_3, q6_1, (bin false q6_0 q6_3), q6_0, q6_2, q6_4], [(bin true q6_3 q6_1), q6_3, q6_1, (bin false q6_0 q6_3), q6_0, q6_2, q6_4], [(bin false q6_3 q6_2), q6_3, q6_2, (bin false q6_0 q6_3), q6_0, q6_1, q6_4], [(bin true q6_3 q6_2), q6_3, q6_2, (bin false q6_0 q6_3), q6_0, q6_1, q6_4], [(bin false q6_3 q6_4), q6_4, (bin false q6_0 q6_3), q6_0, q6_1, q6_2], [(bin false q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_3), q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_0 q6_3), q6_0, q6_1, q6_2], [(bin false q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_3), q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_3), q6_0, q6_3, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_3), q6_0, q6_3, q6_2], [(bin true q6_1 q6_4), q6_1, q6_4, (bin false q6_0 q6_3), q6_0, q6_3, q6_2], [(bin false q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_3), q6_0, q6_3, q6_1], [(bin true q6_2 q6_4), q6_2, q6_4, (bin false q6_0 q6_3), q6_0, q6_3, q6_1]]

lemma allf6t0_b4_b : ∀ v ∈ tbf6t0_b4_b, search 6 0 v = false :=
  consAll nf6t0_b4_b0_ (consAll nf6t0_b4_b1_ (consAll nf6t0_b4_b2_ (consAll nf6t0_b4_b3_ (consAll nf6t0_b4_b4_ (consAll nf6t0_b4_b5_ (consAll nf6t0_b4_b6_ (consAll nf6t0_b4_b7_ (consAll nf6t0_b4_b8_ (consAll nf6t0_b4_b9_ (consAll nf6t0_b4_b10_ (consAll nf6t0_b4_b11_ (consAll nf6t0_b4_b12_ (consAll nf6t0_b4_b13_ (consAll nf6t0_b4_b14_ (consAll nf6t0_b4_b15_ (consAll nf6t0_b4_b16_ (consAll nf6t0_b4_b17_ (consAll nf6t0_b4_b18_ (consAll nf6t0_b4_b19_ (consAll nf6t0_b4_b20_ (consAll nf6t0_b4_b21_ (consAll nf6t0_b4_b22_ (consAll nf6t0_b4_b23_ (consAll nf6t0_b4_b24_ (consAll nf6t0_b4_b25_ (consAll nf6t0_b4_b26_ (consAll nf6t0_b4_b27_ (consAll nf6t0_b4_b28_ (consAll nf6t0_b4_b29_ (consAll nf6t0_b4_b30_ (consAll nf6t0_b4_b31_ (consAll nf6t0_b4_b32_ (consAll nf6t0_b4_b33_ (consAll nf6t0_b4_b34_ (consAll nf6t0_b4_b35_ (consAll nf6t0_b4_b36_ (consAll nf6t0_b4_b37_ (consAll nf6t0_b4_b38_ (nilAll)))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b4_ : search 7 0 [(bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4] = false := by
  have e := search.eq_2 0 [(bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4] 6
  rw [← orc_eq tbf6t0_b4_b (search 6 0) allf6t0_b4_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b0_ : search 6 0 [(bin false (bin true q6_0 q6_3) q6_1), q6_1, q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b1_ : search 6 0 [(bin false (bin true q6_0 q6_3) q6_1), (bin true q6_0 q6_3), q6_1, q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b2_ : search 6 0 [(bin true (bin true q6_0 q6_3) q6_1), q6_1, q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b3_ : search 6 0 [(bin true (bin true q6_0 q6_3) q6_1), (bin true q6_0 q6_3), q6_1, q6_0, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b4_ : search 6 0 [(bin false (bin true q6_0 q6_3) q6_2), q6_2, q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b5_ : search 6 0 [(bin false (bin true q6_0 q6_3) q6_2), (bin true q6_0 q6_3), q6_2, q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b6_ : search 6 0 [(bin true (bin true q6_0 q6_3) q6_2), q6_2, q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b7_ : search 6 0 [(bin true (bin true q6_0 q6_3) q6_2), (bin true q6_0 q6_3), q6_2, q6_0, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b8_ : search 6 0 [(bin false (bin true q6_0 q6_3) q6_4), q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b9_ : search 6 0 [(bin false (bin true q6_0 q6_3) q6_4), (bin true q6_0 q6_3), q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b10_ : search 6 0 [(bin false (bin true q6_0 q6_3) q6_4), q6_4, q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b11_ : search 6 0 [(bin false (bin true q6_0 q6_3) q6_4), (bin true q6_0 q6_3), q6_4, q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b12_ : search 6 0 [(bin true (bin true q6_0 q6_3) q6_4), q6_4, q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b13_ : search 6 0 [(bin true (bin true q6_0 q6_3) q6_4), (bin true q6_0 q6_3), q6_4, q6_0, q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b14_ : search 6 0 [(bin false q6_0 q6_3), q6_0, (bin true q6_0 q6_3), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b15_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_3), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b16_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_3), q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b17_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_3), q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b18_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_3), q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b19_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_3), q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b20_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_3), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b21_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_3), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b22_ : search 6 0 [(bin false q6_3 q6_1), q6_3, q6_1, (bin true q6_0 q6_3), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b23_ : search 6 0 [(bin true q6_3 q6_1), q6_1, (bin true q6_0 q6_3), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b24_ : search 6 0 [(bin true q6_3 q6_1), q6_3, q6_1, (bin true q6_0 q6_3), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b25_ : search 6 0 [(bin false q6_3 q6_2), q6_3, q6_2, (bin true q6_0 q6_3), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b26_ : search 6 0 [(bin true q6_3 q6_2), q6_2, (bin true q6_0 q6_3), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b27_ : search 6 0 [(bin true q6_3 q6_2), q6_3, q6_2, (bin true q6_0 q6_3), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b28_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_3), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b29_ : search 6 0 [(bin true q6_3 q6_4), q6_4, (bin true q6_0 q6_3), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b30_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_3), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b31_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_3), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b32_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_3), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b33_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_3), q6_0, q6_3, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b34_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_3), q6_0, q6_3, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b35_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_3), q6_0, q6_3, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_b36_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_3), q6_0, q6_3, q6_1] = false := by decide +kernel

def tbf6t0_b5_b : List (List Sig) := [[(bin false (bin true q6_0 q6_3) q6_1), q6_1, q6_0, q6_3, q6_2, q6_4], [(bin false (bin true q6_0 q6_3) q6_1), (bin true q6_0 q6_3), q6_1, q6_0, q6_3, q6_2, q6_4], [(bin true (bin true q6_0 q6_3) q6_1), q6_1, q6_0, q6_3, q6_2, q6_4], [(bin true (bin true q6_0 q6_3) q6_1), (bin true q6_0 q6_3), q6_1, q6_0, q6_3, q6_2, q6_4], [(bin false (bin true q6_0 q6_3) q6_2), q6_2, q6_0, q6_3, q6_1, q6_4], [(bin false (bin true q6_0 q6_3) q6_2), (bin true q6_0 q6_3), q6_2, q6_0, q6_3, q6_1, q6_4], [(bin true (bin true q6_0 q6_3) q6_2), q6_2, q6_0, q6_3, q6_1, q6_4], [(bin true (bin true q6_0 q6_3) q6_2), (bin true q6_0 q6_3), q6_2, q6_0, q6_3, q6_1, q6_4], [(bin false (bin true q6_0 q6_3) q6_4), q6_0, q6_3, q6_1, q6_2], [(bin false (bin true q6_0 q6_3) q6_4), (bin true q6_0 q6_3), q6_0, q6_3, q6_1, q6_2], [(bin false (bin true q6_0 q6_3) q6_4), q6_4, q6_0, q6_3, q6_1, q6_2], [(bin false (bin true q6_0 q6_3) q6_4), (bin true q6_0 q6_3), q6_4, q6_0, q6_3, q6_1, q6_2], [(bin true (bin true q6_0 q6_3) q6_4), q6_4, q6_0, q6_3, q6_1, q6_2], [(bin true (bin true q6_0 q6_3) q6_4), (bin true q6_0 q6_3), q6_4, q6_0, q6_3, q6_1, q6_2], [(bin false q6_0 q6_3), q6_0, (bin true q6_0 q6_3), q6_1, q6_2, q6_4], [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_3), q6_1, q6_2, q6_4], [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_3), q6_3, q6_2, q6_4], [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_3), q6_3, q6_2, q6_4], [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_3), q6_3, q6_1, q6_4], [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_3), q6_3, q6_1, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_3), q6_3, q6_1, q6_2], [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_3), q6_3, q6_1, q6_2], [(bin false q6_3 q6_1), q6_3, q6_1, (bin true q6_0 q6_3), q6_0, q6_2, q6_4], [(bin true q6_3 q6_1), q6_1, (bin true q6_0 q6_3), q6_0, q6_2, q6_4], [(bin true q6_3 q6_1), q6_3, q6_1, (bin true q6_0 q6_3), q6_0, q6_2, q6_4], [(bin false q6_3 q6_2), q6_3, q6_2, (bin true q6_0 q6_3), q6_0, q6_1, q6_4], [(bin true q6_3 q6_2), q6_2, (bin true q6_0 q6_3), q6_0, q6_1, q6_4], [(bin true q6_3 q6_2), q6_3, q6_2, (bin true q6_0 q6_3), q6_0, q6_1, q6_4], [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_3), q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_4, (bin true q6_0 q6_3), q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_0 q6_3), q6_0, q6_1, q6_2], [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_3), q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_3), q6_0, q6_3, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_3), q6_0, q6_3, q6_2], [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_0 q6_3), q6_0, q6_3, q6_2], [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_3), q6_0, q6_3, q6_1], [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_0 q6_3), q6_0, q6_3, q6_1]]

lemma allf6t0_b5_b : ∀ v ∈ tbf6t0_b5_b, search 6 0 v = false :=
  consAll nf6t0_b5_b0_ (consAll nf6t0_b5_b1_ (consAll nf6t0_b5_b2_ (consAll nf6t0_b5_b3_ (consAll nf6t0_b5_b4_ (consAll nf6t0_b5_b5_ (consAll nf6t0_b5_b6_ (consAll nf6t0_b5_b7_ (consAll nf6t0_b5_b8_ (consAll nf6t0_b5_b9_ (consAll nf6t0_b5_b10_ (consAll nf6t0_b5_b11_ (consAll nf6t0_b5_b12_ (consAll nf6t0_b5_b13_ (consAll nf6t0_b5_b14_ (consAll nf6t0_b5_b15_ (consAll nf6t0_b5_b16_ (consAll nf6t0_b5_b17_ (consAll nf6t0_b5_b18_ (consAll nf6t0_b5_b19_ (consAll nf6t0_b5_b20_ (consAll nf6t0_b5_b21_ (consAll nf6t0_b5_b22_ (consAll nf6t0_b5_b23_ (consAll nf6t0_b5_b24_ (consAll nf6t0_b5_b25_ (consAll nf6t0_b5_b26_ (consAll nf6t0_b5_b27_ (consAll nf6t0_b5_b28_ (consAll nf6t0_b5_b29_ (consAll nf6t0_b5_b30_ (consAll nf6t0_b5_b31_ (consAll nf6t0_b5_b32_ (consAll nf6t0_b5_b33_ (consAll nf6t0_b5_b34_ (consAll nf6t0_b5_b35_ (consAll nf6t0_b5_b36_ (nilAll)))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b5_ : search 7 0 [(bin true q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4] = false := by
  have e := search.eq_2 0 [(bin true q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4] 6
  rw [← orc_eq tbf6t0_b5_b (search 6 0) allf6t0_b5_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b0_ : search 6 0 [(bin false (bin false q6_0 q6_4) q6_1), q6_1, q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b1_ : search 6 0 [(bin false (bin false q6_0 q6_4) q6_1), (bin false q6_0 q6_4), q6_1, q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b2_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_1), q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b3_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_1), (bin false q6_0 q6_4), q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b4_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_1), q6_1, q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b5_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_1), (bin false q6_0 q6_4), q6_1, q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b6_ : search 6 0 [(bin false (bin false q6_0 q6_4) q6_2), q6_2, q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b7_ : search 6 0 [(bin false (bin false q6_0 q6_4) q6_2), (bin false q6_0 q6_4), q6_2, q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b8_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_2), q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b9_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_2), (bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b10_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_2), q6_2, q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b11_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_2), (bin false q6_0 q6_4), q6_2, q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b12_ : search 6 0 [(bin false (bin false q6_0 q6_4) q6_3), q6_3, q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b13_ : search 6 0 [(bin false (bin false q6_0 q6_4) q6_3), (bin false q6_0 q6_4), q6_3, q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b14_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_3), q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b15_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_3), (bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b16_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_3), q6_3, q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b17_ : search 6 0 [(bin true (bin false q6_0 q6_4) q6_3), (bin false q6_0 q6_4), q6_3, q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b18_ : search 6 0 [(bin true q6_0 q6_4), q6_0, (bin false q6_0 q6_4), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b19_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_4), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b20_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_4), q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b21_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_4), q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b22_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_4), q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b23_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_4), q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b24_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b25_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b26_ : search 6 0 [(bin false q6_4 q6_1), q6_4, q6_1, (bin false q6_0 q6_4), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b27_ : search 6 0 [(bin true q6_4 q6_1), q6_4, q6_1, (bin false q6_0 q6_4), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b28_ : search 6 0 [(bin false q6_4 q6_2), q6_4, q6_2, (bin false q6_0 q6_4), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b29_ : search 6 0 [(bin true q6_4 q6_2), q6_4, q6_2, (bin false q6_0 q6_4), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b30_ : search 6 0 [(bin false q6_4 q6_3), q6_3, (bin false q6_0 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b31_ : search 6 0 [(bin false q6_4 q6_3), q6_4, q6_3, (bin false q6_0 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b32_ : search 6 0 [(bin true q6_4 q6_3), q6_4, q6_3, (bin false q6_0 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b33_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_4), q6_0, q6_4, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b34_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_4), q6_0, q6_4, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b35_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_4), q6_0, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b36_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_4), q6_0, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b37_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_4), q6_0, q6_4, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_b38_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_4), q6_0, q6_4, q6_1] = false := by decide +kernel

def tbf6t0_b6_b : List (List Sig) := [[(bin false (bin false q6_0 q6_4) q6_1), q6_1, q6_0, q6_4, q6_2, q6_3], [(bin false (bin false q6_0 q6_4) q6_1), (bin false q6_0 q6_4), q6_1, q6_0, q6_4, q6_2, q6_3], [(bin true (bin false q6_0 q6_4) q6_1), q6_0, q6_4, q6_2, q6_3], [(bin true (bin false q6_0 q6_4) q6_1), (bin false q6_0 q6_4), q6_0, q6_4, q6_2, q6_3], [(bin true (bin false q6_0 q6_4) q6_1), q6_1, q6_0, q6_4, q6_2, q6_3], [(bin true (bin false q6_0 q6_4) q6_1), (bin false q6_0 q6_4), q6_1, q6_0, q6_4, q6_2, q6_3], [(bin false (bin false q6_0 q6_4) q6_2), q6_2, q6_0, q6_4, q6_1, q6_3], [(bin false (bin false q6_0 q6_4) q6_2), (bin false q6_0 q6_4), q6_2, q6_0, q6_4, q6_1, q6_3], [(bin true (bin false q6_0 q6_4) q6_2), q6_0, q6_4, q6_1, q6_3], [(bin true (bin false q6_0 q6_4) q6_2), (bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_3], [(bin true (bin false q6_0 q6_4) q6_2), q6_2, q6_0, q6_4, q6_1, q6_3], [(bin true (bin false q6_0 q6_4) q6_2), (bin false q6_0 q6_4), q6_2, q6_0, q6_4, q6_1, q6_3], [(bin false (bin false q6_0 q6_4) q6_3), q6_3, q6_0, q6_4, q6_1, q6_2], [(bin false (bin false q6_0 q6_4) q6_3), (bin false q6_0 q6_4), q6_3, q6_0, q6_4, q6_1, q6_2], [(bin true (bin false q6_0 q6_4) q6_3), q6_0, q6_4, q6_1, q6_2], [(bin true (bin false q6_0 q6_4) q6_3), (bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_2], [(bin true (bin false q6_0 q6_4) q6_3), q6_3, q6_0, q6_4, q6_1, q6_2], [(bin true (bin false q6_0 q6_4) q6_3), (bin false q6_0 q6_4), q6_3, q6_0, q6_4, q6_1, q6_2], [(bin true q6_0 q6_4), q6_0, (bin false q6_0 q6_4), q6_1, q6_2, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_0 q6_4), q6_1, q6_2, q6_3], [(bin false q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_4), q6_4, q6_2, q6_3], [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_0 q6_4), q6_4, q6_2, q6_3], [(bin false q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_4), q6_4, q6_1, q6_3], [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_0 q6_4), q6_4, q6_1, q6_3], [(bin false q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_4), q6_4, q6_1, q6_2], [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_0 q6_4), q6_4, q6_1, q6_2], [(bin false q6_4 q6_1), q6_4, q6_1, (bin false q6_0 q6_4), q6_0, q6_2, q6_3], [(bin true q6_4 q6_1), q6_4, q6_1, (bin false q6_0 q6_4), q6_0, q6_2, q6_3], [(bin false q6_4 q6_2), q6_4, q6_2, (bin false q6_0 q6_4), q6_0, q6_1, q6_3], [(bin true q6_4 q6_2), q6_4, q6_2, (bin false q6_0 q6_4), q6_0, q6_1, q6_3], [(bin false q6_4 q6_3), q6_3, (bin false q6_0 q6_4), q6_0, q6_1, q6_2], [(bin false q6_4 q6_3), q6_4, q6_3, (bin false q6_0 q6_4), q6_0, q6_1, q6_2], [(bin true q6_4 q6_3), q6_4, q6_3, (bin false q6_0 q6_4), q6_0, q6_1, q6_2], [(bin false q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_4), q6_0, q6_4, q6_3], [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_0 q6_4), q6_0, q6_4, q6_3], [(bin false q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_4), q6_0, q6_4, q6_2], [(bin true q6_1 q6_3), q6_1, q6_3, (bin false q6_0 q6_4), q6_0, q6_4, q6_2], [(bin false q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_4), q6_0, q6_4, q6_1], [(bin true q6_2 q6_3), q6_2, q6_3, (bin false q6_0 q6_4), q6_0, q6_4, q6_1]]

lemma allf6t0_b6_b : ∀ v ∈ tbf6t0_b6_b, search 6 0 v = false :=
  consAll nf6t0_b6_b0_ (consAll nf6t0_b6_b1_ (consAll nf6t0_b6_b2_ (consAll nf6t0_b6_b3_ (consAll nf6t0_b6_b4_ (consAll nf6t0_b6_b5_ (consAll nf6t0_b6_b6_ (consAll nf6t0_b6_b7_ (consAll nf6t0_b6_b8_ (consAll nf6t0_b6_b9_ (consAll nf6t0_b6_b10_ (consAll nf6t0_b6_b11_ (consAll nf6t0_b6_b12_ (consAll nf6t0_b6_b13_ (consAll nf6t0_b6_b14_ (consAll nf6t0_b6_b15_ (consAll nf6t0_b6_b16_ (consAll nf6t0_b6_b17_ (consAll nf6t0_b6_b18_ (consAll nf6t0_b6_b19_ (consAll nf6t0_b6_b20_ (consAll nf6t0_b6_b21_ (consAll nf6t0_b6_b22_ (consAll nf6t0_b6_b23_ (consAll nf6t0_b6_b24_ (consAll nf6t0_b6_b25_ (consAll nf6t0_b6_b26_ (consAll nf6t0_b6_b27_ (consAll nf6t0_b6_b28_ (consAll nf6t0_b6_b29_ (consAll nf6t0_b6_b30_ (consAll nf6t0_b6_b31_ (consAll nf6t0_b6_b32_ (consAll nf6t0_b6_b33_ (consAll nf6t0_b6_b34_ (consAll nf6t0_b6_b35_ (consAll nf6t0_b6_b36_ (consAll nf6t0_b6_b37_ (consAll nf6t0_b6_b38_ (nilAll)))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b6_ : search 7 0 [(bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3] = false := by
  have e := search.eq_2 0 [(bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3] 6
  rw [← orc_eq tbf6t0_b6_b (search 6 0) allf6t0_b6_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b0_ : search 6 0 [(bin false (bin true q6_0 q6_4) q6_1), q6_1, q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b1_ : search 6 0 [(bin false (bin true q6_0 q6_4) q6_1), (bin true q6_0 q6_4), q6_1, q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b2_ : search 6 0 [(bin true (bin true q6_0 q6_4) q6_1), q6_1, q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b3_ : search 6 0 [(bin true (bin true q6_0 q6_4) q6_1), (bin true q6_0 q6_4), q6_1, q6_0, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b4_ : search 6 0 [(bin false (bin true q6_0 q6_4) q6_2), q6_2, q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b5_ : search 6 0 [(bin false (bin true q6_0 q6_4) q6_2), (bin true q6_0 q6_4), q6_2, q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b6_ : search 6 0 [(bin true (bin true q6_0 q6_4) q6_2), q6_2, q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b7_ : search 6 0 [(bin true (bin true q6_0 q6_4) q6_2), (bin true q6_0 q6_4), q6_2, q6_0, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b8_ : search 6 0 [(bin false (bin true q6_0 q6_4) q6_3), q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b9_ : search 6 0 [(bin false (bin true q6_0 q6_4) q6_3), (bin true q6_0 q6_4), q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b10_ : search 6 0 [(bin false (bin true q6_0 q6_4) q6_3), q6_3, q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b11_ : search 6 0 [(bin false (bin true q6_0 q6_4) q6_3), (bin true q6_0 q6_4), q6_3, q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b12_ : search 6 0 [(bin true (bin true q6_0 q6_4) q6_3), q6_3, q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b13_ : search 6 0 [(bin true (bin true q6_0 q6_4) q6_3), (bin true q6_0 q6_4), q6_3, q6_0, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b14_ : search 6 0 [(bin false q6_0 q6_4), q6_0, (bin true q6_0 q6_4), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b15_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_4), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b16_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_4), q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b17_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_4), q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b18_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_4), q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b19_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_4), q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b20_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b21_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b22_ : search 6 0 [(bin false q6_4 q6_1), q6_4, q6_1, (bin true q6_0 q6_4), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b23_ : search 6 0 [(bin true q6_4 q6_1), q6_1, (bin true q6_0 q6_4), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b24_ : search 6 0 [(bin true q6_4 q6_1), q6_4, q6_1, (bin true q6_0 q6_4), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b25_ : search 6 0 [(bin false q6_4 q6_2), q6_4, q6_2, (bin true q6_0 q6_4), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b26_ : search 6 0 [(bin true q6_4 q6_2), q6_2, (bin true q6_0 q6_4), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b27_ : search 6 0 [(bin true q6_4 q6_2), q6_4, q6_2, (bin true q6_0 q6_4), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b28_ : search 6 0 [(bin false q6_4 q6_3), q6_4, q6_3, (bin true q6_0 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b29_ : search 6 0 [(bin true q6_4 q6_3), q6_3, (bin true q6_0 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b30_ : search 6 0 [(bin true q6_4 q6_3), q6_4, q6_3, (bin true q6_0 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b31_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_4), q6_0, q6_4, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b32_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_4), q6_0, q6_4, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b33_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_4), q6_0, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b34_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_4), q6_0, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b35_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_4), q6_0, q6_4, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_b36_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_4), q6_0, q6_4, q6_1] = false := by decide +kernel

def tbf6t0_b7_b : List (List Sig) := [[(bin false (bin true q6_0 q6_4) q6_1), q6_1, q6_0, q6_4, q6_2, q6_3], [(bin false (bin true q6_0 q6_4) q6_1), (bin true q6_0 q6_4), q6_1, q6_0, q6_4, q6_2, q6_3], [(bin true (bin true q6_0 q6_4) q6_1), q6_1, q6_0, q6_4, q6_2, q6_3], [(bin true (bin true q6_0 q6_4) q6_1), (bin true q6_0 q6_4), q6_1, q6_0, q6_4, q6_2, q6_3], [(bin false (bin true q6_0 q6_4) q6_2), q6_2, q6_0, q6_4, q6_1, q6_3], [(bin false (bin true q6_0 q6_4) q6_2), (bin true q6_0 q6_4), q6_2, q6_0, q6_4, q6_1, q6_3], [(bin true (bin true q6_0 q6_4) q6_2), q6_2, q6_0, q6_4, q6_1, q6_3], [(bin true (bin true q6_0 q6_4) q6_2), (bin true q6_0 q6_4), q6_2, q6_0, q6_4, q6_1, q6_3], [(bin false (bin true q6_0 q6_4) q6_3), q6_0, q6_4, q6_1, q6_2], [(bin false (bin true q6_0 q6_4) q6_3), (bin true q6_0 q6_4), q6_0, q6_4, q6_1, q6_2], [(bin false (bin true q6_0 q6_4) q6_3), q6_3, q6_0, q6_4, q6_1, q6_2], [(bin false (bin true q6_0 q6_4) q6_3), (bin true q6_0 q6_4), q6_3, q6_0, q6_4, q6_1, q6_2], [(bin true (bin true q6_0 q6_4) q6_3), q6_3, q6_0, q6_4, q6_1, q6_2], [(bin true (bin true q6_0 q6_4) q6_3), (bin true q6_0 q6_4), q6_3, q6_0, q6_4, q6_1, q6_2], [(bin false q6_0 q6_4), q6_0, (bin true q6_0 q6_4), q6_1, q6_2, q6_3], [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_0 q6_4), q6_1, q6_2, q6_3], [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_4), q6_4, q6_2, q6_3], [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_0 q6_4), q6_4, q6_2, q6_3], [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_4), q6_4, q6_1, q6_3], [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_0 q6_4), q6_4, q6_1, q6_3], [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_4), q6_4, q6_1, q6_2], [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_0 q6_4), q6_4, q6_1, q6_2], [(bin false q6_4 q6_1), q6_4, q6_1, (bin true q6_0 q6_4), q6_0, q6_2, q6_3], [(bin true q6_4 q6_1), q6_1, (bin true q6_0 q6_4), q6_0, q6_2, q6_3], [(bin true q6_4 q6_1), q6_4, q6_1, (bin true q6_0 q6_4), q6_0, q6_2, q6_3], [(bin false q6_4 q6_2), q6_4, q6_2, (bin true q6_0 q6_4), q6_0, q6_1, q6_3], [(bin true q6_4 q6_2), q6_2, (bin true q6_0 q6_4), q6_0, q6_1, q6_3], [(bin true q6_4 q6_2), q6_4, q6_2, (bin true q6_0 q6_4), q6_0, q6_1, q6_3], [(bin false q6_4 q6_3), q6_4, q6_3, (bin true q6_0 q6_4), q6_0, q6_1, q6_2], [(bin true q6_4 q6_3), q6_3, (bin true q6_0 q6_4), q6_0, q6_1, q6_2], [(bin true q6_4 q6_3), q6_4, q6_3, (bin true q6_0 q6_4), q6_0, q6_1, q6_2], [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_4), q6_0, q6_4, q6_3], [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_0 q6_4), q6_0, q6_4, q6_3], [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_4), q6_0, q6_4, q6_2], [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_0 q6_4), q6_0, q6_4, q6_2], [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_4), q6_0, q6_4, q6_1], [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_0 q6_4), q6_0, q6_4, q6_1]]

lemma allf6t0_b7_b : ∀ v ∈ tbf6t0_b7_b, search 6 0 v = false :=
  consAll nf6t0_b7_b0_ (consAll nf6t0_b7_b1_ (consAll nf6t0_b7_b2_ (consAll nf6t0_b7_b3_ (consAll nf6t0_b7_b4_ (consAll nf6t0_b7_b5_ (consAll nf6t0_b7_b6_ (consAll nf6t0_b7_b7_ (consAll nf6t0_b7_b8_ (consAll nf6t0_b7_b9_ (consAll nf6t0_b7_b10_ (consAll nf6t0_b7_b11_ (consAll nf6t0_b7_b12_ (consAll nf6t0_b7_b13_ (consAll nf6t0_b7_b14_ (consAll nf6t0_b7_b15_ (consAll nf6t0_b7_b16_ (consAll nf6t0_b7_b17_ (consAll nf6t0_b7_b18_ (consAll nf6t0_b7_b19_ (consAll nf6t0_b7_b20_ (consAll nf6t0_b7_b21_ (consAll nf6t0_b7_b22_ (consAll nf6t0_b7_b23_ (consAll nf6t0_b7_b24_ (consAll nf6t0_b7_b25_ (consAll nf6t0_b7_b26_ (consAll nf6t0_b7_b27_ (consAll nf6t0_b7_b28_ (consAll nf6t0_b7_b29_ (consAll nf6t0_b7_b30_ (consAll nf6t0_b7_b31_ (consAll nf6t0_b7_b32_ (consAll nf6t0_b7_b33_ (consAll nf6t0_b7_b34_ (consAll nf6t0_b7_b35_ (consAll nf6t0_b7_b36_ (nilAll)))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b7_ : search 7 0 [(bin true q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3] = false := by
  have e := search.eq_2 0 [(bin true q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3] 6
  rw [← orc_eq tbf6t0_b7_b (search 6 0) allf6t0_b7_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b0_ : search 6 0 [(bin false (bin false q6_1 q6_2) q6_0), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b1_ : search 6 0 [(bin false (bin false q6_1 q6_2) q6_0), (bin false q6_1 q6_2), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b2_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_0), q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b3_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_0), (bin false q6_1 q6_2), q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b4_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_0), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b5_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_0), (bin false q6_1 q6_2), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b6_ : search 6 0 [(bin false (bin false q6_1 q6_2) q6_3), q6_3, q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b7_ : search 6 0 [(bin false (bin false q6_1 q6_2) q6_3), (bin false q6_1 q6_2), q6_3, q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b8_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_3), q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b9_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_3), (bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b10_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_3), q6_3, q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b11_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_3), (bin false q6_1 q6_2), q6_3, q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b12_ : search 6 0 [(bin false (bin false q6_1 q6_2) q6_4), q6_4, q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b13_ : search 6 0 [(bin false (bin false q6_1 q6_2) q6_4), (bin false q6_1 q6_2), q6_4, q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b14_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_4), q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b15_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_4), (bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b16_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_4), q6_4, q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b17_ : search 6 0 [(bin true (bin false q6_1 q6_2) q6_4), (bin false q6_1 q6_2), q6_4, q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b18_ : search 6 0 [(bin true q6_1 q6_2), (bin false q6_1 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b19_ : search 6 0 [(bin true q6_1 q6_2), q6_1, (bin false q6_1 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b20_ : search 6 0 [(bin true q6_1 q6_2), q6_2, (bin false q6_1 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b21_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_1 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b22_ : search 6 0 [(bin false q6_1 q6_0), q6_1, q6_0, (bin false q6_1 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b23_ : search 6 0 [(bin true q6_1 q6_0), q6_1, q6_0, (bin false q6_1 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b24_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin false q6_1 q6_2), q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b25_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin false q6_1 q6_2), q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b26_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin false q6_1 q6_2), q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b27_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin false q6_1 q6_2), q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b28_ : search 6 0 [(bin false q6_2 q6_0), q6_2, q6_0, (bin false q6_1 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b29_ : search 6 0 [(bin true q6_2 q6_0), q6_2, q6_0, (bin false q6_1 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b30_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin false q6_1 q6_2), q6_1, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b31_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin false q6_1 q6_2), q6_1, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b32_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin false q6_1 q6_2), q6_1, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b33_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin false q6_1 q6_2), q6_1, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b34_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin false q6_1 q6_2), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b35_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_1 q6_2), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b36_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin false q6_1 q6_2), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b37_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_1 q6_2), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b38_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin false q6_1 q6_2), q6_1, q6_2, q6_0] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_b39_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_1 q6_2), q6_1, q6_2, q6_0] = false := by decide +kernel

def tbf6t0_b8_b : List (List Sig) := [[(bin false (bin false q6_1 q6_2) q6_0), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin false (bin false q6_1 q6_2) q6_0), (bin false q6_1 q6_2), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin true (bin false q6_1 q6_2) q6_0), q6_1, q6_2, q6_3, q6_4], [(bin true (bin false q6_1 q6_2) q6_0), (bin false q6_1 q6_2), q6_1, q6_2, q6_3, q6_4], [(bin true (bin false q6_1 q6_2) q6_0), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin true (bin false q6_1 q6_2) q6_0), (bin false q6_1 q6_2), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin false (bin false q6_1 q6_2) q6_3), q6_3, q6_1, q6_2, q6_0, q6_4], [(bin false (bin false q6_1 q6_2) q6_3), (bin false q6_1 q6_2), q6_3, q6_1, q6_2, q6_0, q6_4], [(bin true (bin false q6_1 q6_2) q6_3), q6_1, q6_2, q6_0, q6_4], [(bin true (bin false q6_1 q6_2) q6_3), (bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_4], [(bin true (bin false q6_1 q6_2) q6_3), q6_3, q6_1, q6_2, q6_0, q6_4], [(bin true (bin false q6_1 q6_2) q6_3), (bin false q6_1 q6_2), q6_3, q6_1, q6_2, q6_0, q6_4], [(bin false (bin false q6_1 q6_2) q6_4), q6_4, q6_1, q6_2, q6_0, q6_3], [(bin false (bin false q6_1 q6_2) q6_4), (bin false q6_1 q6_2), q6_4, q6_1, q6_2, q6_0, q6_3], [(bin true (bin false q6_1 q6_2) q6_4), q6_1, q6_2, q6_0, q6_3], [(bin true (bin false q6_1 q6_2) q6_4), (bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_3], [(bin true (bin false q6_1 q6_2) q6_4), q6_4, q6_1, q6_2, q6_0, q6_3], [(bin true (bin false q6_1 q6_2) q6_4), (bin false q6_1 q6_2), q6_4, q6_1, q6_2, q6_0, q6_3], [(bin true q6_1 q6_2), (bin false q6_1 q6_2), q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_1, (bin false q6_1 q6_2), q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_2, (bin false q6_1 q6_2), q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_1 q6_2), q6_0, q6_3, q6_4], [(bin false q6_1 q6_0), q6_1, q6_0, (bin false q6_1 q6_2), q6_2, q6_3, q6_4], [(bin true q6_1 q6_0), q6_1, q6_0, (bin false q6_1 q6_2), q6_2, q6_3, q6_4], [(bin false q6_1 q6_3), q6_1, q6_3, (bin false q6_1 q6_2), q6_2, q6_0, q6_4], [(bin true q6_1 q6_3), q6_1, q6_3, (bin false q6_1 q6_2), q6_2, q6_0, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin false q6_1 q6_2), q6_2, q6_0, q6_3], [(bin true q6_1 q6_4), q6_1, q6_4, (bin false q6_1 q6_2), q6_2, q6_0, q6_3], [(bin false q6_2 q6_0), q6_2, q6_0, (bin false q6_1 q6_2), q6_1, q6_3, q6_4], [(bin true q6_2 q6_0), q6_2, q6_0, (bin false q6_1 q6_2), q6_1, q6_3, q6_4], [(bin false q6_2 q6_3), q6_2, q6_3, (bin false q6_1 q6_2), q6_1, q6_0, q6_4], [(bin true q6_2 q6_3), q6_2, q6_3, (bin false q6_1 q6_2), q6_1, q6_0, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, (bin false q6_1 q6_2), q6_1, q6_0, q6_3], [(bin true q6_2 q6_4), q6_2, q6_4, (bin false q6_1 q6_2), q6_1, q6_0, q6_3], [(bin false q6_0 q6_3), q6_0, q6_3, (bin false q6_1 q6_2), q6_1, q6_2, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, (bin false q6_1 q6_2), q6_1, q6_2, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin false q6_1 q6_2), q6_1, q6_2, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, (bin false q6_1 q6_2), q6_1, q6_2, q6_3], [(bin false q6_3 q6_4), q6_3, q6_4, (bin false q6_1 q6_2), q6_1, q6_2, q6_0], [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_1 q6_2), q6_1, q6_2, q6_0]]

lemma allf6t0_b8_b : ∀ v ∈ tbf6t0_b8_b, search 6 0 v = false :=
  consAll nf6t0_b8_b0_ (consAll nf6t0_b8_b1_ (consAll nf6t0_b8_b2_ (consAll nf6t0_b8_b3_ (consAll nf6t0_b8_b4_ (consAll nf6t0_b8_b5_ (consAll nf6t0_b8_b6_ (consAll nf6t0_b8_b7_ (consAll nf6t0_b8_b8_ (consAll nf6t0_b8_b9_ (consAll nf6t0_b8_b10_ (consAll nf6t0_b8_b11_ (consAll nf6t0_b8_b12_ (consAll nf6t0_b8_b13_ (consAll nf6t0_b8_b14_ (consAll nf6t0_b8_b15_ (consAll nf6t0_b8_b16_ (consAll nf6t0_b8_b17_ (consAll nf6t0_b8_b18_ (consAll nf6t0_b8_b19_ (consAll nf6t0_b8_b20_ (consAll nf6t0_b8_b21_ (consAll nf6t0_b8_b22_ (consAll nf6t0_b8_b23_ (consAll nf6t0_b8_b24_ (consAll nf6t0_b8_b25_ (consAll nf6t0_b8_b26_ (consAll nf6t0_b8_b27_ (consAll nf6t0_b8_b28_ (consAll nf6t0_b8_b29_ (consAll nf6t0_b8_b30_ (consAll nf6t0_b8_b31_ (consAll nf6t0_b8_b32_ (consAll nf6t0_b8_b33_ (consAll nf6t0_b8_b34_ (consAll nf6t0_b8_b35_ (consAll nf6t0_b8_b36_ (consAll nf6t0_b8_b37_ (consAll nf6t0_b8_b38_ (consAll nf6t0_b8_b39_ (nilAll))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b8_ : search 7 0 [(bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4] = false := by
  have e := search.eq_2 0 [(bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4] 6
  rw [← orc_eq tbf6t0_b8_b (search 6 0) allf6t0_b8_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b0_ : search 6 0 [(bin false (bin true q6_1 q6_2) q6_0), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b1_ : search 6 0 [(bin false (bin true q6_1 q6_2) q6_0), (bin true q6_1 q6_2), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b2_ : search 6 0 [(bin true (bin true q6_1 q6_2) q6_0), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b3_ : search 6 0 [(bin true (bin true q6_1 q6_2) q6_0), (bin true q6_1 q6_2), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b4_ : search 6 0 [(bin false (bin true q6_1 q6_2) q6_3), q6_3, q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b5_ : search 6 0 [(bin false (bin true q6_1 q6_2) q6_3), (bin true q6_1 q6_2), q6_3, q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b6_ : search 6 0 [(bin true (bin true q6_1 q6_2) q6_3), q6_3, q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b7_ : search 6 0 [(bin true (bin true q6_1 q6_2) q6_3), (bin true q6_1 q6_2), q6_3, q6_1, q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b8_ : search 6 0 [(bin false (bin true q6_1 q6_2) q6_4), q6_4, q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b9_ : search 6 0 [(bin false (bin true q6_1 q6_2) q6_4), (bin true q6_1 q6_2), q6_4, q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b10_ : search 6 0 [(bin true (bin true q6_1 q6_2) q6_4), q6_4, q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b11_ : search 6 0 [(bin true (bin true q6_1 q6_2) q6_4), (bin true q6_1 q6_2), q6_4, q6_1, q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b12_ : search 6 0 [(bin false q6_1 q6_2), (bin true q6_1 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b13_ : search 6 0 [(bin false q6_1 q6_2), q6_1, (bin true q6_1 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b14_ : search 6 0 [(bin false q6_1 q6_2), q6_2, (bin true q6_1 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b15_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_2), q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b16_ : search 6 0 [(bin false q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b17_ : search 6 0 [(bin true q6_1 q6_0), q6_0, (bin true q6_1 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b18_ : search 6 0 [(bin true q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_2), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b19_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_2), q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b20_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_2), q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b21_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_2), q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b22_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_2), q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b23_ : search 6 0 [(bin false q6_2 q6_0), q6_2, q6_0, (bin true q6_1 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b24_ : search 6 0 [(bin true q6_2 q6_0), q6_0, (bin true q6_1 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b25_ : search 6 0 [(bin true q6_2 q6_0), q6_2, q6_0, (bin true q6_1 q6_2), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b26_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_1 q6_2), q6_1, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b27_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_1 q6_2), q6_1, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b28_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_1 q6_2), q6_1, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b29_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_1 q6_2), q6_1, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b30_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_1 q6_2), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b31_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_1 q6_2), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b32_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_1 q6_2), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b33_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_1 q6_2), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b34_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_1 q6_2), q6_1, q6_2, q6_0] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_b35_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_1 q6_2), q6_1, q6_2, q6_0] = false := by decide +kernel

def tbf6t0_b9_b : List (List Sig) := [[(bin false (bin true q6_1 q6_2) q6_0), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin false (bin true q6_1 q6_2) q6_0), (bin true q6_1 q6_2), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin true (bin true q6_1 q6_2) q6_0), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin true (bin true q6_1 q6_2) q6_0), (bin true q6_1 q6_2), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin false (bin true q6_1 q6_2) q6_3), q6_3, q6_1, q6_2, q6_0, q6_4], [(bin false (bin true q6_1 q6_2) q6_3), (bin true q6_1 q6_2), q6_3, q6_1, q6_2, q6_0, q6_4], [(bin true (bin true q6_1 q6_2) q6_3), q6_3, q6_1, q6_2, q6_0, q6_4], [(bin true (bin true q6_1 q6_2) q6_3), (bin true q6_1 q6_2), q6_3, q6_1, q6_2, q6_0, q6_4], [(bin false (bin true q6_1 q6_2) q6_4), q6_4, q6_1, q6_2, q6_0, q6_3], [(bin false (bin true q6_1 q6_2) q6_4), (bin true q6_1 q6_2), q6_4, q6_1, q6_2, q6_0, q6_3], [(bin true (bin true q6_1 q6_2) q6_4), q6_4, q6_1, q6_2, q6_0, q6_3], [(bin true (bin true q6_1 q6_2) q6_4), (bin true q6_1 q6_2), q6_4, q6_1, q6_2, q6_0, q6_3], [(bin false q6_1 q6_2), (bin true q6_1 q6_2), q6_0, q6_3, q6_4], [(bin false q6_1 q6_2), q6_1, (bin true q6_1 q6_2), q6_0, q6_3, q6_4], [(bin false q6_1 q6_2), q6_2, (bin true q6_1 q6_2), q6_0, q6_3, q6_4], [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_2), q6_0, q6_3, q6_4], [(bin false q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_2), q6_2, q6_3, q6_4], [(bin true q6_1 q6_0), q6_0, (bin true q6_1 q6_2), q6_2, q6_3, q6_4], [(bin true q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_2), q6_2, q6_3, q6_4], [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_2), q6_2, q6_0, q6_4], [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_2), q6_2, q6_0, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_2), q6_2, q6_0, q6_3], [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_2), q6_2, q6_0, q6_3], [(bin false q6_2 q6_0), q6_2, q6_0, (bin true q6_1 q6_2), q6_1, q6_3, q6_4], [(bin true q6_2 q6_0), q6_0, (bin true q6_1 q6_2), q6_1, q6_3, q6_4], [(bin true q6_2 q6_0), q6_2, q6_0, (bin true q6_1 q6_2), q6_1, q6_3, q6_4], [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_1 q6_2), q6_1, q6_0, q6_4], [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_1 q6_2), q6_1, q6_0, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_1 q6_2), q6_1, q6_0, q6_3], [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_1 q6_2), q6_1, q6_0, q6_3], [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_1 q6_2), q6_1, q6_2, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_1 q6_2), q6_1, q6_2, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_1 q6_2), q6_1, q6_2, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_1 q6_2), q6_1, q6_2, q6_3], [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_1 q6_2), q6_1, q6_2, q6_0], [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_1 q6_2), q6_1, q6_2, q6_0]]

lemma allf6t0_b9_b : ∀ v ∈ tbf6t0_b9_b, search 6 0 v = false :=
  consAll nf6t0_b9_b0_ (consAll nf6t0_b9_b1_ (consAll nf6t0_b9_b2_ (consAll nf6t0_b9_b3_ (consAll nf6t0_b9_b4_ (consAll nf6t0_b9_b5_ (consAll nf6t0_b9_b6_ (consAll nf6t0_b9_b7_ (consAll nf6t0_b9_b8_ (consAll nf6t0_b9_b9_ (consAll nf6t0_b9_b10_ (consAll nf6t0_b9_b11_ (consAll nf6t0_b9_b12_ (consAll nf6t0_b9_b13_ (consAll nf6t0_b9_b14_ (consAll nf6t0_b9_b15_ (consAll nf6t0_b9_b16_ (consAll nf6t0_b9_b17_ (consAll nf6t0_b9_b18_ (consAll nf6t0_b9_b19_ (consAll nf6t0_b9_b20_ (consAll nf6t0_b9_b21_ (consAll nf6t0_b9_b22_ (consAll nf6t0_b9_b23_ (consAll nf6t0_b9_b24_ (consAll nf6t0_b9_b25_ (consAll nf6t0_b9_b26_ (consAll nf6t0_b9_b27_ (consAll nf6t0_b9_b28_ (consAll nf6t0_b9_b29_ (consAll nf6t0_b9_b30_ (consAll nf6t0_b9_b31_ (consAll nf6t0_b9_b32_ (consAll nf6t0_b9_b33_ (consAll nf6t0_b9_b34_ (consAll nf6t0_b9_b35_ (nilAll))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b9_ : search 7 0 [(bin true q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4] = false := by
  have e := search.eq_2 0 [(bin true q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4] 6
  rw [← orc_eq tbf6t0_b9_b (search 6 0) allf6t0_b9_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b10_ : search 7 0 [(bin false q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b0_ : search 6 0 [(bin false (bin true q6_1 q6_3) q6_0), q6_0, q6_1, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b1_ : search 6 0 [(bin false (bin true q6_1 q6_3) q6_0), (bin true q6_1 q6_3), q6_0, q6_1, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b2_ : search 6 0 [(bin true (bin true q6_1 q6_3) q6_0), q6_0, q6_1, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b3_ : search 6 0 [(bin true (bin true q6_1 q6_3) q6_0), (bin true q6_1 q6_3), q6_0, q6_1, q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b4_ : search 6 0 [(bin false (bin true q6_1 q6_3) q6_2), q6_2, q6_1, q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b5_ : search 6 0 [(bin false (bin true q6_1 q6_3) q6_2), (bin true q6_1 q6_3), q6_2, q6_1, q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b6_ : search 6 0 [(bin true (bin true q6_1 q6_3) q6_2), q6_2, q6_1, q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b7_ : search 6 0 [(bin true (bin true q6_1 q6_3) q6_2), (bin true q6_1 q6_3), q6_2, q6_1, q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b8_ : search 6 0 [(bin false (bin true q6_1 q6_3) q6_4), q6_4, q6_1, q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b9_ : search 6 0 [(bin false (bin true q6_1 q6_3) q6_4), (bin true q6_1 q6_3), q6_4, q6_1, q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b10_ : search 6 0 [(bin true (bin true q6_1 q6_3) q6_4), q6_4, q6_1, q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b11_ : search 6 0 [(bin true (bin true q6_1 q6_3) q6_4), (bin true q6_1 q6_3), q6_4, q6_1, q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b12_ : search 6 0 [(bin false q6_1 q6_3), q6_1, (bin true q6_1 q6_3), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b13_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_3), q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b14_ : search 6 0 [(bin false q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_3), q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b15_ : search 6 0 [(bin true q6_1 q6_0), q6_0, (bin true q6_1 q6_3), q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b16_ : search 6 0 [(bin true q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_3), q6_3, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b17_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_3), q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b18_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_3), q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b19_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_3), q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b20_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_3), q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b21_ : search 6 0 [(bin false q6_3 q6_0), q6_3, q6_0, (bin true q6_1 q6_3), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b22_ : search 6 0 [(bin true q6_3 q6_0), q6_0, (bin true q6_1 q6_3), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b23_ : search 6 0 [(bin true q6_3 q6_0), q6_3, q6_0, (bin true q6_1 q6_3), q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b24_ : search 6 0 [(bin false q6_3 q6_2), q6_3, q6_2, (bin true q6_1 q6_3), q6_1, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b25_ : search 6 0 [(bin true q6_3 q6_2), q6_2, (bin true q6_1 q6_3), q6_1, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b26_ : search 6 0 [(bin true q6_3 q6_2), q6_3, q6_2, (bin true q6_1 q6_3), q6_1, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b27_ : search 6 0 [(bin false q6_3 q6_4), q6_4, (bin true q6_1 q6_3), q6_1, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b28_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_1 q6_3), q6_1, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b29_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_1 q6_3), q6_1, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b30_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_1 q6_3), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b31_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_1 q6_3), q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b32_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_1 q6_3), q6_1, q6_3, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b33_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_1 q6_3), q6_1, q6_3, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b34_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_1 q6_3), q6_1, q6_3, q6_0] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_b35_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_1 q6_3), q6_1, q6_3, q6_0] = false := by decide +kernel

def tbf6t0_b11_b : List (List Sig) := [[(bin false (bin true q6_1 q6_3) q6_0), q6_0, q6_1, q6_3, q6_2, q6_4], [(bin false (bin true q6_1 q6_3) q6_0), (bin true q6_1 q6_3), q6_0, q6_1, q6_3, q6_2, q6_4], [(bin true (bin true q6_1 q6_3) q6_0), q6_0, q6_1, q6_3, q6_2, q6_4], [(bin true (bin true q6_1 q6_3) q6_0), (bin true q6_1 q6_3), q6_0, q6_1, q6_3, q6_2, q6_4], [(bin false (bin true q6_1 q6_3) q6_2), q6_2, q6_1, q6_3, q6_0, q6_4], [(bin false (bin true q6_1 q6_3) q6_2), (bin true q6_1 q6_3), q6_2, q6_1, q6_3, q6_0, q6_4], [(bin true (bin true q6_1 q6_3) q6_2), q6_2, q6_1, q6_3, q6_0, q6_4], [(bin true (bin true q6_1 q6_3) q6_2), (bin true q6_1 q6_3), q6_2, q6_1, q6_3, q6_0, q6_4], [(bin false (bin true q6_1 q6_3) q6_4), q6_4, q6_1, q6_3, q6_0, q6_2], [(bin false (bin true q6_1 q6_3) q6_4), (bin true q6_1 q6_3), q6_4, q6_1, q6_3, q6_0, q6_2], [(bin true (bin true q6_1 q6_3) q6_4), q6_4, q6_1, q6_3, q6_0, q6_2], [(bin true (bin true q6_1 q6_3) q6_4), (bin true q6_1 q6_3), q6_4, q6_1, q6_3, q6_0, q6_2], [(bin false q6_1 q6_3), q6_1, (bin true q6_1 q6_3), q6_0, q6_2, q6_4], [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_3), q6_0, q6_2, q6_4], [(bin false q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_3), q6_3, q6_2, q6_4], [(bin true q6_1 q6_0), q6_0, (bin true q6_1 q6_3), q6_3, q6_2, q6_4], [(bin true q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_3), q6_3, q6_2, q6_4], [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_3), q6_3, q6_0, q6_4], [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_3), q6_3, q6_0, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_3), q6_3, q6_0, q6_2], [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_3), q6_3, q6_0, q6_2], [(bin false q6_3 q6_0), q6_3, q6_0, (bin true q6_1 q6_3), q6_1, q6_2, q6_4], [(bin true q6_3 q6_0), q6_0, (bin true q6_1 q6_3), q6_1, q6_2, q6_4], [(bin true q6_3 q6_0), q6_3, q6_0, (bin true q6_1 q6_3), q6_1, q6_2, q6_4], [(bin false q6_3 q6_2), q6_3, q6_2, (bin true q6_1 q6_3), q6_1, q6_0, q6_4], [(bin true q6_3 q6_2), q6_2, (bin true q6_1 q6_3), q6_1, q6_0, q6_4], [(bin true q6_3 q6_2), q6_3, q6_2, (bin true q6_1 q6_3), q6_1, q6_0, q6_4], [(bin false q6_3 q6_4), q6_4, (bin true q6_1 q6_3), q6_1, q6_0, q6_2], [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_1 q6_3), q6_1, q6_0, q6_2], [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_1 q6_3), q6_1, q6_0, q6_2], [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_1 q6_3), q6_1, q6_3, q6_4], [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_1 q6_3), q6_1, q6_3, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_1 q6_3), q6_1, q6_3, q6_2], [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_1 q6_3), q6_1, q6_3, q6_2], [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_1 q6_3), q6_1, q6_3, q6_0], [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_1 q6_3), q6_1, q6_3, q6_0]]

lemma allf6t0_b11_b : ∀ v ∈ tbf6t0_b11_b, search 6 0 v = false :=
  consAll nf6t0_b11_b0_ (consAll nf6t0_b11_b1_ (consAll nf6t0_b11_b2_ (consAll nf6t0_b11_b3_ (consAll nf6t0_b11_b4_ (consAll nf6t0_b11_b5_ (consAll nf6t0_b11_b6_ (consAll nf6t0_b11_b7_ (consAll nf6t0_b11_b8_ (consAll nf6t0_b11_b9_ (consAll nf6t0_b11_b10_ (consAll nf6t0_b11_b11_ (consAll nf6t0_b11_b12_ (consAll nf6t0_b11_b13_ (consAll nf6t0_b11_b14_ (consAll nf6t0_b11_b15_ (consAll nf6t0_b11_b16_ (consAll nf6t0_b11_b17_ (consAll nf6t0_b11_b18_ (consAll nf6t0_b11_b19_ (consAll nf6t0_b11_b20_ (consAll nf6t0_b11_b21_ (consAll nf6t0_b11_b22_ (consAll nf6t0_b11_b23_ (consAll nf6t0_b11_b24_ (consAll nf6t0_b11_b25_ (consAll nf6t0_b11_b26_ (consAll nf6t0_b11_b27_ (consAll nf6t0_b11_b28_ (consAll nf6t0_b11_b29_ (consAll nf6t0_b11_b30_ (consAll nf6t0_b11_b31_ (consAll nf6t0_b11_b32_ (consAll nf6t0_b11_b33_ (consAll nf6t0_b11_b34_ (consAll nf6t0_b11_b35_ (nilAll))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b11_ : search 7 0 [(bin true q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4] = false := by
  have e := search.eq_2 0 [(bin true q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4] 6
  rw [← orc_eq tbf6t0_b11_b (search 6 0) allf6t0_b11_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b12_ : search 7 0 [(bin false q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b0_ : search 6 0 [(bin false (bin true q6_1 q6_4) q6_0), q6_0, q6_1, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b1_ : search 6 0 [(bin false (bin true q6_1 q6_4) q6_0), (bin true q6_1 q6_4), q6_0, q6_1, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b2_ : search 6 0 [(bin true (bin true q6_1 q6_4) q6_0), q6_0, q6_1, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b3_ : search 6 0 [(bin true (bin true q6_1 q6_4) q6_0), (bin true q6_1 q6_4), q6_0, q6_1, q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b4_ : search 6 0 [(bin false (bin true q6_1 q6_4) q6_2), q6_2, q6_1, q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b5_ : search 6 0 [(bin false (bin true q6_1 q6_4) q6_2), (bin true q6_1 q6_4), q6_2, q6_1, q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b6_ : search 6 0 [(bin true (bin true q6_1 q6_4) q6_2), q6_2, q6_1, q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b7_ : search 6 0 [(bin true (bin true q6_1 q6_4) q6_2), (bin true q6_1 q6_4), q6_2, q6_1, q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b8_ : search 6 0 [(bin false (bin true q6_1 q6_4) q6_3), q6_3, q6_1, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b9_ : search 6 0 [(bin false (bin true q6_1 q6_4) q6_3), (bin true q6_1 q6_4), q6_3, q6_1, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b10_ : search 6 0 [(bin true (bin true q6_1 q6_4) q6_3), q6_3, q6_1, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b11_ : search 6 0 [(bin true (bin true q6_1 q6_4) q6_3), (bin true q6_1 q6_4), q6_3, q6_1, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b12_ : search 6 0 [(bin false q6_1 q6_4), q6_1, (bin true q6_1 q6_4), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b13_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_4), q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b14_ : search 6 0 [(bin false q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_4), q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b15_ : search 6 0 [(bin true q6_1 q6_0), q6_0, (bin true q6_1 q6_4), q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b16_ : search 6 0 [(bin true q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_4), q6_4, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b17_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_4), q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b18_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_4), q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b19_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_4), q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b20_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_4), q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b21_ : search 6 0 [(bin false q6_4 q6_0), q6_4, q6_0, (bin true q6_1 q6_4), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b22_ : search 6 0 [(bin true q6_4 q6_0), q6_0, (bin true q6_1 q6_4), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b23_ : search 6 0 [(bin true q6_4 q6_0), q6_4, q6_0, (bin true q6_1 q6_4), q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b24_ : search 6 0 [(bin false q6_4 q6_2), q6_4, q6_2, (bin true q6_1 q6_4), q6_1, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b25_ : search 6 0 [(bin true q6_4 q6_2), q6_2, (bin true q6_1 q6_4), q6_1, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b26_ : search 6 0 [(bin true q6_4 q6_2), q6_4, q6_2, (bin true q6_1 q6_4), q6_1, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b27_ : search 6 0 [(bin false q6_4 q6_3), q6_3, (bin true q6_1 q6_4), q6_1, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b28_ : search 6 0 [(bin false q6_4 q6_3), q6_4, q6_3, (bin true q6_1 q6_4), q6_1, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b29_ : search 6 0 [(bin true q6_4 q6_3), q6_4, q6_3, (bin true q6_1 q6_4), q6_1, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b30_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_1 q6_4), q6_1, q6_4, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b31_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_1 q6_4), q6_1, q6_4, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b32_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_1 q6_4), q6_1, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b33_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_1 q6_4), q6_1, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b34_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_1 q6_4), q6_1, q6_4, q6_0] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_b35_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_1 q6_4), q6_1, q6_4, q6_0] = false := by decide +kernel

def tbf6t0_b13_b : List (List Sig) := [[(bin false (bin true q6_1 q6_4) q6_0), q6_0, q6_1, q6_4, q6_2, q6_3], [(bin false (bin true q6_1 q6_4) q6_0), (bin true q6_1 q6_4), q6_0, q6_1, q6_4, q6_2, q6_3], [(bin true (bin true q6_1 q6_4) q6_0), q6_0, q6_1, q6_4, q6_2, q6_3], [(bin true (bin true q6_1 q6_4) q6_0), (bin true q6_1 q6_4), q6_0, q6_1, q6_4, q6_2, q6_3], [(bin false (bin true q6_1 q6_4) q6_2), q6_2, q6_1, q6_4, q6_0, q6_3], [(bin false (bin true q6_1 q6_4) q6_2), (bin true q6_1 q6_4), q6_2, q6_1, q6_4, q6_0, q6_3], [(bin true (bin true q6_1 q6_4) q6_2), q6_2, q6_1, q6_4, q6_0, q6_3], [(bin true (bin true q6_1 q6_4) q6_2), (bin true q6_1 q6_4), q6_2, q6_1, q6_4, q6_0, q6_3], [(bin false (bin true q6_1 q6_4) q6_3), q6_3, q6_1, q6_4, q6_0, q6_2], [(bin false (bin true q6_1 q6_4) q6_3), (bin true q6_1 q6_4), q6_3, q6_1, q6_4, q6_0, q6_2], [(bin true (bin true q6_1 q6_4) q6_3), q6_3, q6_1, q6_4, q6_0, q6_2], [(bin true (bin true q6_1 q6_4) q6_3), (bin true q6_1 q6_4), q6_3, q6_1, q6_4, q6_0, q6_2], [(bin false q6_1 q6_4), q6_1, (bin true q6_1 q6_4), q6_0, q6_2, q6_3], [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_1 q6_4), q6_0, q6_2, q6_3], [(bin false q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_4), q6_4, q6_2, q6_3], [(bin true q6_1 q6_0), q6_0, (bin true q6_1 q6_4), q6_4, q6_2, q6_3], [(bin true q6_1 q6_0), q6_1, q6_0, (bin true q6_1 q6_4), q6_4, q6_2, q6_3], [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_4), q6_4, q6_0, q6_3], [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_1 q6_4), q6_4, q6_0, q6_3], [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_4), q6_4, q6_0, q6_2], [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_1 q6_4), q6_4, q6_0, q6_2], [(bin false q6_4 q6_0), q6_4, q6_0, (bin true q6_1 q6_4), q6_1, q6_2, q6_3], [(bin true q6_4 q6_0), q6_0, (bin true q6_1 q6_4), q6_1, q6_2, q6_3], [(bin true q6_4 q6_0), q6_4, q6_0, (bin true q6_1 q6_4), q6_1, q6_2, q6_3], [(bin false q6_4 q6_2), q6_4, q6_2, (bin true q6_1 q6_4), q6_1, q6_0, q6_3], [(bin true q6_4 q6_2), q6_2, (bin true q6_1 q6_4), q6_1, q6_0, q6_3], [(bin true q6_4 q6_2), q6_4, q6_2, (bin true q6_1 q6_4), q6_1, q6_0, q6_3], [(bin false q6_4 q6_3), q6_3, (bin true q6_1 q6_4), q6_1, q6_0, q6_2], [(bin false q6_4 q6_3), q6_4, q6_3, (bin true q6_1 q6_4), q6_1, q6_0, q6_2], [(bin true q6_4 q6_3), q6_4, q6_3, (bin true q6_1 q6_4), q6_1, q6_0, q6_2], [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_1 q6_4), q6_1, q6_4, q6_3], [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_1 q6_4), q6_1, q6_4, q6_3], [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_1 q6_4), q6_1, q6_4, q6_2], [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_1 q6_4), q6_1, q6_4, q6_2], [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_1 q6_4), q6_1, q6_4, q6_0], [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_1 q6_4), q6_1, q6_4, q6_0]]

lemma allf6t0_b13_b : ∀ v ∈ tbf6t0_b13_b, search 6 0 v = false :=
  consAll nf6t0_b13_b0_ (consAll nf6t0_b13_b1_ (consAll nf6t0_b13_b2_ (consAll nf6t0_b13_b3_ (consAll nf6t0_b13_b4_ (consAll nf6t0_b13_b5_ (consAll nf6t0_b13_b6_ (consAll nf6t0_b13_b7_ (consAll nf6t0_b13_b8_ (consAll nf6t0_b13_b9_ (consAll nf6t0_b13_b10_ (consAll nf6t0_b13_b11_ (consAll nf6t0_b13_b12_ (consAll nf6t0_b13_b13_ (consAll nf6t0_b13_b14_ (consAll nf6t0_b13_b15_ (consAll nf6t0_b13_b16_ (consAll nf6t0_b13_b17_ (consAll nf6t0_b13_b18_ (consAll nf6t0_b13_b19_ (consAll nf6t0_b13_b20_ (consAll nf6t0_b13_b21_ (consAll nf6t0_b13_b22_ (consAll nf6t0_b13_b23_ (consAll nf6t0_b13_b24_ (consAll nf6t0_b13_b25_ (consAll nf6t0_b13_b26_ (consAll nf6t0_b13_b27_ (consAll nf6t0_b13_b28_ (consAll nf6t0_b13_b29_ (consAll nf6t0_b13_b30_ (consAll nf6t0_b13_b31_ (consAll nf6t0_b13_b32_ (consAll nf6t0_b13_b33_ (consAll nf6t0_b13_b34_ (consAll nf6t0_b13_b35_ (nilAll))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b13_ : search 7 0 [(bin true q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3] = false := by
  have e := search.eq_2 0 [(bin true q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3] 6
  rw [← orc_eq tbf6t0_b13_b (search 6 0) allf6t0_b13_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b14_ : search 7 0 [(bin false q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b0_ : search 6 0 [(bin false (bin true q6_2 q6_3) q6_0), q6_0, q6_2, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b1_ : search 6 0 [(bin false (bin true q6_2 q6_3) q6_0), (bin true q6_2 q6_3), q6_0, q6_2, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b2_ : search 6 0 [(bin true (bin true q6_2 q6_3) q6_0), q6_0, q6_2, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b3_ : search 6 0 [(bin true (bin true q6_2 q6_3) q6_0), (bin true q6_2 q6_3), q6_0, q6_2, q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b4_ : search 6 0 [(bin false (bin true q6_2 q6_3) q6_1), q6_1, q6_2, q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b5_ : search 6 0 [(bin false (bin true q6_2 q6_3) q6_1), (bin true q6_2 q6_3), q6_1, q6_2, q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b6_ : search 6 0 [(bin true (bin true q6_2 q6_3) q6_1), q6_1, q6_2, q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b7_ : search 6 0 [(bin true (bin true q6_2 q6_3) q6_1), (bin true q6_2 q6_3), q6_1, q6_2, q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b8_ : search 6 0 [(bin false (bin true q6_2 q6_3) q6_4), q6_4, q6_2, q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b9_ : search 6 0 [(bin false (bin true q6_2 q6_3) q6_4), (bin true q6_2 q6_3), q6_4, q6_2, q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b10_ : search 6 0 [(bin true (bin true q6_2 q6_3) q6_4), q6_4, q6_2, q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b11_ : search 6 0 [(bin true (bin true q6_2 q6_3) q6_4), (bin true q6_2 q6_3), q6_4, q6_2, q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b12_ : search 6 0 [(bin false q6_2 q6_3), q6_2, (bin true q6_2 q6_3), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b13_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_2 q6_3), q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b14_ : search 6 0 [(bin false q6_2 q6_0), q6_2, q6_0, (bin true q6_2 q6_3), q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b15_ : search 6 0 [(bin true q6_2 q6_0), q6_0, (bin true q6_2 q6_3), q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b16_ : search 6 0 [(bin true q6_2 q6_0), q6_2, q6_0, (bin true q6_2 q6_3), q6_3, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b17_ : search 6 0 [(bin false q6_2 q6_1), q6_2, q6_1, (bin true q6_2 q6_3), q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b18_ : search 6 0 [(bin true q6_2 q6_1), q6_2, q6_1, (bin true q6_2 q6_3), q6_3, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b19_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_2 q6_3), q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b20_ : search 6 0 [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_2 q6_3), q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b21_ : search 6 0 [(bin false q6_3 q6_0), q6_3, q6_0, (bin true q6_2 q6_3), q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b22_ : search 6 0 [(bin true q6_3 q6_0), q6_0, (bin true q6_2 q6_3), q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b23_ : search 6 0 [(bin true q6_3 q6_0), q6_3, q6_0, (bin true q6_2 q6_3), q6_2, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b24_ : search 6 0 [(bin false q6_3 q6_1), q6_3, q6_1, (bin true q6_2 q6_3), q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b25_ : search 6 0 [(bin true q6_3 q6_1), q6_1, (bin true q6_2 q6_3), q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b26_ : search 6 0 [(bin true q6_3 q6_1), q6_3, q6_1, (bin true q6_2 q6_3), q6_2, q6_0, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b27_ : search 6 0 [(bin false q6_3 q6_4), q6_4, (bin true q6_2 q6_3), q6_2, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b28_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_2 q6_3), q6_2, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b29_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_2 q6_3), q6_2, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b30_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_2 q6_3), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b31_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_2 q6_3), q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b32_ : search 6 0 [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_2 q6_3), q6_2, q6_3, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b33_ : search 6 0 [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_2 q6_3), q6_2, q6_3, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b34_ : search 6 0 [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_2 q6_3), q6_2, q6_3, q6_0] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_b35_ : search 6 0 [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_2 q6_3), q6_2, q6_3, q6_0] = false := by decide +kernel

def tbf6t0_b15_b : List (List Sig) := [[(bin false (bin true q6_2 q6_3) q6_0), q6_0, q6_2, q6_3, q6_1, q6_4], [(bin false (bin true q6_2 q6_3) q6_0), (bin true q6_2 q6_3), q6_0, q6_2, q6_3, q6_1, q6_4], [(bin true (bin true q6_2 q6_3) q6_0), q6_0, q6_2, q6_3, q6_1, q6_4], [(bin true (bin true q6_2 q6_3) q6_0), (bin true q6_2 q6_3), q6_0, q6_2, q6_3, q6_1, q6_4], [(bin false (bin true q6_2 q6_3) q6_1), q6_1, q6_2, q6_3, q6_0, q6_4], [(bin false (bin true q6_2 q6_3) q6_1), (bin true q6_2 q6_3), q6_1, q6_2, q6_3, q6_0, q6_4], [(bin true (bin true q6_2 q6_3) q6_1), q6_1, q6_2, q6_3, q6_0, q6_4], [(bin true (bin true q6_2 q6_3) q6_1), (bin true q6_2 q6_3), q6_1, q6_2, q6_3, q6_0, q6_4], [(bin false (bin true q6_2 q6_3) q6_4), q6_4, q6_2, q6_3, q6_0, q6_1], [(bin false (bin true q6_2 q6_3) q6_4), (bin true q6_2 q6_3), q6_4, q6_2, q6_3, q6_0, q6_1], [(bin true (bin true q6_2 q6_3) q6_4), q6_4, q6_2, q6_3, q6_0, q6_1], [(bin true (bin true q6_2 q6_3) q6_4), (bin true q6_2 q6_3), q6_4, q6_2, q6_3, q6_0, q6_1], [(bin false q6_2 q6_3), q6_2, (bin true q6_2 q6_3), q6_0, q6_1, q6_4], [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_2 q6_3), q6_0, q6_1, q6_4], [(bin false q6_2 q6_0), q6_2, q6_0, (bin true q6_2 q6_3), q6_3, q6_1, q6_4], [(bin true q6_2 q6_0), q6_0, (bin true q6_2 q6_3), q6_3, q6_1, q6_4], [(bin true q6_2 q6_0), q6_2, q6_0, (bin true q6_2 q6_3), q6_3, q6_1, q6_4], [(bin false q6_2 q6_1), q6_2, q6_1, (bin true q6_2 q6_3), q6_3, q6_0, q6_4], [(bin true q6_2 q6_1), q6_2, q6_1, (bin true q6_2 q6_3), q6_3, q6_0, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_2 q6_3), q6_3, q6_0, q6_1], [(bin true q6_2 q6_4), q6_2, q6_4, (bin true q6_2 q6_3), q6_3, q6_0, q6_1], [(bin false q6_3 q6_0), q6_3, q6_0, (bin true q6_2 q6_3), q6_2, q6_1, q6_4], [(bin true q6_3 q6_0), q6_0, (bin true q6_2 q6_3), q6_2, q6_1, q6_4], [(bin true q6_3 q6_0), q6_3, q6_0, (bin true q6_2 q6_3), q6_2, q6_1, q6_4], [(bin false q6_3 q6_1), q6_3, q6_1, (bin true q6_2 q6_3), q6_2, q6_0, q6_4], [(bin true q6_3 q6_1), q6_1, (bin true q6_2 q6_3), q6_2, q6_0, q6_4], [(bin true q6_3 q6_1), q6_3, q6_1, (bin true q6_2 q6_3), q6_2, q6_0, q6_4], [(bin false q6_3 q6_4), q6_4, (bin true q6_2 q6_3), q6_2, q6_0, q6_1], [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_2 q6_3), q6_2, q6_0, q6_1], [(bin true q6_3 q6_4), q6_3, q6_4, (bin true q6_2 q6_3), q6_2, q6_0, q6_1], [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_2 q6_3), q6_2, q6_3, q6_4], [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_2 q6_3), q6_2, q6_3, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, (bin true q6_2 q6_3), q6_2, q6_3, q6_1], [(bin true q6_0 q6_4), q6_0, q6_4, (bin true q6_2 q6_3), q6_2, q6_3, q6_1], [(bin false q6_1 q6_4), q6_1, q6_4, (bin true q6_2 q6_3), q6_2, q6_3, q6_0], [(bin true q6_1 q6_4), q6_1, q6_4, (bin true q6_2 q6_3), q6_2, q6_3, q6_0]]

lemma allf6t0_b15_b : ∀ v ∈ tbf6t0_b15_b, search 6 0 v = false :=
  consAll nf6t0_b15_b0_ (consAll nf6t0_b15_b1_ (consAll nf6t0_b15_b2_ (consAll nf6t0_b15_b3_ (consAll nf6t0_b15_b4_ (consAll nf6t0_b15_b5_ (consAll nf6t0_b15_b6_ (consAll nf6t0_b15_b7_ (consAll nf6t0_b15_b8_ (consAll nf6t0_b15_b9_ (consAll nf6t0_b15_b10_ (consAll nf6t0_b15_b11_ (consAll nf6t0_b15_b12_ (consAll nf6t0_b15_b13_ (consAll nf6t0_b15_b14_ (consAll nf6t0_b15_b15_ (consAll nf6t0_b15_b16_ (consAll nf6t0_b15_b17_ (consAll nf6t0_b15_b18_ (consAll nf6t0_b15_b19_ (consAll nf6t0_b15_b20_ (consAll nf6t0_b15_b21_ (consAll nf6t0_b15_b22_ (consAll nf6t0_b15_b23_ (consAll nf6t0_b15_b24_ (consAll nf6t0_b15_b25_ (consAll nf6t0_b15_b26_ (consAll nf6t0_b15_b27_ (consAll nf6t0_b15_b28_ (consAll nf6t0_b15_b29_ (consAll nf6t0_b15_b30_ (consAll nf6t0_b15_b31_ (consAll nf6t0_b15_b32_ (consAll nf6t0_b15_b33_ (consAll nf6t0_b15_b34_ (consAll nf6t0_b15_b35_ (nilAll))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b15_ : search 7 0 [(bin true q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4] = false := by
  have e := search.eq_2 0 [(bin true q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4] 6
  rw [← orc_eq tbf6t0_b15_b (search 6 0) allf6t0_b15_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b16_ : search 7 0 [(bin false q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b0_ : search 6 0 [(bin false (bin true q6_2 q6_4) q6_0), q6_0, q6_2, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b1_ : search 6 0 [(bin false (bin true q6_2 q6_4) q6_0), (bin true q6_2 q6_4), q6_0, q6_2, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b2_ : search 6 0 [(bin true (bin true q6_2 q6_4) q6_0), q6_0, q6_2, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b3_ : search 6 0 [(bin true (bin true q6_2 q6_4) q6_0), (bin true q6_2 q6_4), q6_0, q6_2, q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b4_ : search 6 0 [(bin false (bin true q6_2 q6_4) q6_1), q6_1, q6_2, q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b5_ : search 6 0 [(bin false (bin true q6_2 q6_4) q6_1), (bin true q6_2 q6_4), q6_1, q6_2, q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b6_ : search 6 0 [(bin true (bin true q6_2 q6_4) q6_1), q6_1, q6_2, q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b7_ : search 6 0 [(bin true (bin true q6_2 q6_4) q6_1), (bin true q6_2 q6_4), q6_1, q6_2, q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b8_ : search 6 0 [(bin false (bin true q6_2 q6_4) q6_3), q6_3, q6_2, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b9_ : search 6 0 [(bin false (bin true q6_2 q6_4) q6_3), (bin true q6_2 q6_4), q6_3, q6_2, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b10_ : search 6 0 [(bin true (bin true q6_2 q6_4) q6_3), q6_3, q6_2, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b11_ : search 6 0 [(bin true (bin true q6_2 q6_4) q6_3), (bin true q6_2 q6_4), q6_3, q6_2, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b12_ : search 6 0 [(bin false q6_2 q6_4), q6_2, (bin true q6_2 q6_4), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b13_ : search 6 0 [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_2 q6_4), q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b14_ : search 6 0 [(bin false q6_2 q6_0), q6_2, q6_0, (bin true q6_2 q6_4), q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b15_ : search 6 0 [(bin true q6_2 q6_0), q6_0, (bin true q6_2 q6_4), q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b16_ : search 6 0 [(bin true q6_2 q6_0), q6_2, q6_0, (bin true q6_2 q6_4), q6_4, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b17_ : search 6 0 [(bin false q6_2 q6_1), q6_2, q6_1, (bin true q6_2 q6_4), q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b18_ : search 6 0 [(bin true q6_2 q6_1), q6_2, q6_1, (bin true q6_2 q6_4), q6_4, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b19_ : search 6 0 [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_2 q6_4), q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b20_ : search 6 0 [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_2 q6_4), q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b21_ : search 6 0 [(bin false q6_4 q6_0), q6_4, q6_0, (bin true q6_2 q6_4), q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b22_ : search 6 0 [(bin true q6_4 q6_0), q6_0, (bin true q6_2 q6_4), q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b23_ : search 6 0 [(bin true q6_4 q6_0), q6_4, q6_0, (bin true q6_2 q6_4), q6_2, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b24_ : search 6 0 [(bin false q6_4 q6_1), q6_4, q6_1, (bin true q6_2 q6_4), q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b25_ : search 6 0 [(bin true q6_4 q6_1), q6_1, (bin true q6_2 q6_4), q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b26_ : search 6 0 [(bin true q6_4 q6_1), q6_4, q6_1, (bin true q6_2 q6_4), q6_2, q6_0, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b27_ : search 6 0 [(bin false q6_4 q6_3), q6_3, (bin true q6_2 q6_4), q6_2, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b28_ : search 6 0 [(bin false q6_4 q6_3), q6_4, q6_3, (bin true q6_2 q6_4), q6_2, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b29_ : search 6 0 [(bin true q6_4 q6_3), q6_4, q6_3, (bin true q6_2 q6_4), q6_2, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b30_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_2 q6_4), q6_2, q6_4, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b31_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_2 q6_4), q6_2, q6_4, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b32_ : search 6 0 [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_2 q6_4), q6_2, q6_4, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b33_ : search 6 0 [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_2 q6_4), q6_2, q6_4, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b34_ : search 6 0 [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_2 q6_4), q6_2, q6_4, q6_0] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_b35_ : search 6 0 [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_2 q6_4), q6_2, q6_4, q6_0] = false := by decide +kernel

def tbf6t0_b17_b : List (List Sig) := [[(bin false (bin true q6_2 q6_4) q6_0), q6_0, q6_2, q6_4, q6_1, q6_3], [(bin false (bin true q6_2 q6_4) q6_0), (bin true q6_2 q6_4), q6_0, q6_2, q6_4, q6_1, q6_3], [(bin true (bin true q6_2 q6_4) q6_0), q6_0, q6_2, q6_4, q6_1, q6_3], [(bin true (bin true q6_2 q6_4) q6_0), (bin true q6_2 q6_4), q6_0, q6_2, q6_4, q6_1, q6_3], [(bin false (bin true q6_2 q6_4) q6_1), q6_1, q6_2, q6_4, q6_0, q6_3], [(bin false (bin true q6_2 q6_4) q6_1), (bin true q6_2 q6_4), q6_1, q6_2, q6_4, q6_0, q6_3], [(bin true (bin true q6_2 q6_4) q6_1), q6_1, q6_2, q6_4, q6_0, q6_3], [(bin true (bin true q6_2 q6_4) q6_1), (bin true q6_2 q6_4), q6_1, q6_2, q6_4, q6_0, q6_3], [(bin false (bin true q6_2 q6_4) q6_3), q6_3, q6_2, q6_4, q6_0, q6_1], [(bin false (bin true q6_2 q6_4) q6_3), (bin true q6_2 q6_4), q6_3, q6_2, q6_4, q6_0, q6_1], [(bin true (bin true q6_2 q6_4) q6_3), q6_3, q6_2, q6_4, q6_0, q6_1], [(bin true (bin true q6_2 q6_4) q6_3), (bin true q6_2 q6_4), q6_3, q6_2, q6_4, q6_0, q6_1], [(bin false q6_2 q6_4), q6_2, (bin true q6_2 q6_4), q6_0, q6_1, q6_3], [(bin false q6_2 q6_4), q6_2, q6_4, (bin true q6_2 q6_4), q6_0, q6_1, q6_3], [(bin false q6_2 q6_0), q6_2, q6_0, (bin true q6_2 q6_4), q6_4, q6_1, q6_3], [(bin true q6_2 q6_0), q6_0, (bin true q6_2 q6_4), q6_4, q6_1, q6_3], [(bin true q6_2 q6_0), q6_2, q6_0, (bin true q6_2 q6_4), q6_4, q6_1, q6_3], [(bin false q6_2 q6_1), q6_2, q6_1, (bin true q6_2 q6_4), q6_4, q6_0, q6_3], [(bin true q6_2 q6_1), q6_2, q6_1, (bin true q6_2 q6_4), q6_4, q6_0, q6_3], [(bin false q6_2 q6_3), q6_2, q6_3, (bin true q6_2 q6_4), q6_4, q6_0, q6_1], [(bin true q6_2 q6_3), q6_2, q6_3, (bin true q6_2 q6_4), q6_4, q6_0, q6_1], [(bin false q6_4 q6_0), q6_4, q6_0, (bin true q6_2 q6_4), q6_2, q6_1, q6_3], [(bin true q6_4 q6_0), q6_0, (bin true q6_2 q6_4), q6_2, q6_1, q6_3], [(bin true q6_4 q6_0), q6_4, q6_0, (bin true q6_2 q6_4), q6_2, q6_1, q6_3], [(bin false q6_4 q6_1), q6_4, q6_1, (bin true q6_2 q6_4), q6_2, q6_0, q6_3], [(bin true q6_4 q6_1), q6_1, (bin true q6_2 q6_4), q6_2, q6_0, q6_3], [(bin true q6_4 q6_1), q6_4, q6_1, (bin true q6_2 q6_4), q6_2, q6_0, q6_3], [(bin false q6_4 q6_3), q6_3, (bin true q6_2 q6_4), q6_2, q6_0, q6_1], [(bin false q6_4 q6_3), q6_4, q6_3, (bin true q6_2 q6_4), q6_2, q6_0, q6_1], [(bin true q6_4 q6_3), q6_4, q6_3, (bin true q6_2 q6_4), q6_2, q6_0, q6_1], [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_2 q6_4), q6_2, q6_4, q6_3], [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_2 q6_4), q6_2, q6_4, q6_3], [(bin false q6_0 q6_3), q6_0, q6_3, (bin true q6_2 q6_4), q6_2, q6_4, q6_1], [(bin true q6_0 q6_3), q6_0, q6_3, (bin true q6_2 q6_4), q6_2, q6_4, q6_1], [(bin false q6_1 q6_3), q6_1, q6_3, (bin true q6_2 q6_4), q6_2, q6_4, q6_0], [(bin true q6_1 q6_3), q6_1, q6_3, (bin true q6_2 q6_4), q6_2, q6_4, q6_0]]

lemma allf6t0_b17_b : ∀ v ∈ tbf6t0_b17_b, search 6 0 v = false :=
  consAll nf6t0_b17_b0_ (consAll nf6t0_b17_b1_ (consAll nf6t0_b17_b2_ (consAll nf6t0_b17_b3_ (consAll nf6t0_b17_b4_ (consAll nf6t0_b17_b5_ (consAll nf6t0_b17_b6_ (consAll nf6t0_b17_b7_ (consAll nf6t0_b17_b8_ (consAll nf6t0_b17_b9_ (consAll nf6t0_b17_b10_ (consAll nf6t0_b17_b11_ (consAll nf6t0_b17_b12_ (consAll nf6t0_b17_b13_ (consAll nf6t0_b17_b14_ (consAll nf6t0_b17_b15_ (consAll nf6t0_b17_b16_ (consAll nf6t0_b17_b17_ (consAll nf6t0_b17_b18_ (consAll nf6t0_b17_b19_ (consAll nf6t0_b17_b20_ (consAll nf6t0_b17_b21_ (consAll nf6t0_b17_b22_ (consAll nf6t0_b17_b23_ (consAll nf6t0_b17_b24_ (consAll nf6t0_b17_b25_ (consAll nf6t0_b17_b26_ (consAll nf6t0_b17_b27_ (consAll nf6t0_b17_b28_ (consAll nf6t0_b17_b29_ (consAll nf6t0_b17_b30_ (consAll nf6t0_b17_b31_ (consAll nf6t0_b17_b32_ (consAll nf6t0_b17_b33_ (consAll nf6t0_b17_b34_ (consAll nf6t0_b17_b35_ (nilAll))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b17_ : search 7 0 [(bin true q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3] = false := by
  have e := search.eq_2 0 [(bin true q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3] 6
  rw [← orc_eq tbf6t0_b17_b (search 6 0) allf6t0_b17_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b0_ : search 6 0 [(bin false (bin false q6_3 q6_4) q6_0), q6_0, q6_3, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b1_ : search 6 0 [(bin false (bin false q6_3 q6_4) q6_0), (bin false q6_3 q6_4), q6_0, q6_3, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b2_ : search 6 0 [(bin true (bin false q6_3 q6_4) q6_0), q6_0, q6_3, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b3_ : search 6 0 [(bin true (bin false q6_3 q6_4) q6_0), (bin false q6_3 q6_4), q6_0, q6_3, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b4_ : search 6 0 [(bin false (bin false q6_3 q6_4) q6_1), q6_1, q6_3, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b5_ : search 6 0 [(bin false (bin false q6_3 q6_4) q6_1), (bin false q6_3 q6_4), q6_1, q6_3, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b6_ : search 6 0 [(bin true (bin false q6_3 q6_4) q6_1), q6_1, q6_3, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b7_ : search 6 0 [(bin true (bin false q6_3 q6_4) q6_1), (bin false q6_3 q6_4), q6_1, q6_3, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b8_ : search 6 0 [(bin false (bin false q6_3 q6_4) q6_2), q6_2, q6_3, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b9_ : search 6 0 [(bin false (bin false q6_3 q6_4) q6_2), (bin false q6_3 q6_4), q6_2, q6_3, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b10_ : search 6 0 [(bin true (bin false q6_3 q6_4) q6_2), q6_2, q6_3, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b11_ : search 6 0 [(bin true (bin false q6_3 q6_4) q6_2), (bin false q6_3 q6_4), q6_2, q6_3, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b12_ : search 6 0 [(bin true q6_3 q6_4), (bin false q6_3 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b13_ : search 6 0 [(bin true q6_3 q6_4), q6_3, (bin false q6_3 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b14_ : search 6 0 [(bin true q6_3 q6_4), q6_4, (bin false q6_3 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b15_ : search 6 0 [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_3 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b16_ : search 6 0 [(bin false q6_3 q6_0), q6_0, (bin false q6_3 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b17_ : search 6 0 [(bin false q6_3 q6_0), q6_3, q6_0, (bin false q6_3 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b18_ : search 6 0 [(bin true q6_3 q6_0), q6_3, q6_0, (bin false q6_3 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b19_ : search 6 0 [(bin false q6_3 q6_1), q6_3, q6_1, (bin false q6_3 q6_4), q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b20_ : search 6 0 [(bin true q6_3 q6_1), q6_1, (bin false q6_3 q6_4), q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b21_ : search 6 0 [(bin true q6_3 q6_1), q6_3, q6_1, (bin false q6_3 q6_4), q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b22_ : search 6 0 [(bin false q6_3 q6_2), q6_3, q6_2, (bin false q6_3 q6_4), q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b23_ : search 6 0 [(bin true q6_3 q6_2), q6_2, (bin false q6_3 q6_4), q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b24_ : search 6 0 [(bin true q6_3 q6_2), q6_3, q6_2, (bin false q6_3 q6_4), q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b25_ : search 6 0 [(bin false q6_4 q6_0), q6_0, (bin false q6_3 q6_4), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b26_ : search 6 0 [(bin false q6_4 q6_0), q6_4, q6_0, (bin false q6_3 q6_4), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b27_ : search 6 0 [(bin true q6_4 q6_0), q6_4, q6_0, (bin false q6_3 q6_4), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b28_ : search 6 0 [(bin false q6_4 q6_1), q6_4, q6_1, (bin false q6_3 q6_4), q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b29_ : search 6 0 [(bin true q6_4 q6_1), q6_1, (bin false q6_3 q6_4), q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b30_ : search 6 0 [(bin true q6_4 q6_1), q6_4, q6_1, (bin false q6_3 q6_4), q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b31_ : search 6 0 [(bin false q6_4 q6_2), q6_4, q6_2, (bin false q6_3 q6_4), q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b32_ : search 6 0 [(bin true q6_4 q6_2), q6_2, (bin false q6_3 q6_4), q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b33_ : search 6 0 [(bin true q6_4 q6_2), q6_4, q6_2, (bin false q6_3 q6_4), q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b34_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin false q6_3 q6_4), q6_3, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b35_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_3 q6_4), q6_3, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b36_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin false q6_3 q6_4), q6_3, q6_4, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b37_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_3 q6_4), q6_3, q6_4, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b38_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin false q6_3 q6_4), q6_3, q6_4, q6_0] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_b39_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_3 q6_4), q6_3, q6_4, q6_0] = false := by decide +kernel

def tbf6t0_b18_b : List (List Sig) := [[(bin false (bin false q6_3 q6_4) q6_0), q6_0, q6_3, q6_4, q6_1, q6_2], [(bin false (bin false q6_3 q6_4) q6_0), (bin false q6_3 q6_4), q6_0, q6_3, q6_4, q6_1, q6_2], [(bin true (bin false q6_3 q6_4) q6_0), q6_0, q6_3, q6_4, q6_1, q6_2], [(bin true (bin false q6_3 q6_4) q6_0), (bin false q6_3 q6_4), q6_0, q6_3, q6_4, q6_1, q6_2], [(bin false (bin false q6_3 q6_4) q6_1), q6_1, q6_3, q6_4, q6_0, q6_2], [(bin false (bin false q6_3 q6_4) q6_1), (bin false q6_3 q6_4), q6_1, q6_3, q6_4, q6_0, q6_2], [(bin true (bin false q6_3 q6_4) q6_1), q6_1, q6_3, q6_4, q6_0, q6_2], [(bin true (bin false q6_3 q6_4) q6_1), (bin false q6_3 q6_4), q6_1, q6_3, q6_4, q6_0, q6_2], [(bin false (bin false q6_3 q6_4) q6_2), q6_2, q6_3, q6_4, q6_0, q6_1], [(bin false (bin false q6_3 q6_4) q6_2), (bin false q6_3 q6_4), q6_2, q6_3, q6_4, q6_0, q6_1], [(bin true (bin false q6_3 q6_4) q6_2), q6_2, q6_3, q6_4, q6_0, q6_1], [(bin true (bin false q6_3 q6_4) q6_2), (bin false q6_3 q6_4), q6_2, q6_3, q6_4, q6_0, q6_1], [(bin true q6_3 q6_4), (bin false q6_3 q6_4), q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_3, (bin false q6_3 q6_4), q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_4, (bin false q6_3 q6_4), q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_3, q6_4, (bin false q6_3 q6_4), q6_0, q6_1, q6_2], [(bin false q6_3 q6_0), q6_0, (bin false q6_3 q6_4), q6_4, q6_1, q6_2], [(bin false q6_3 q6_0), q6_3, q6_0, (bin false q6_3 q6_4), q6_4, q6_1, q6_2], [(bin true q6_3 q6_0), q6_3, q6_0, (bin false q6_3 q6_4), q6_4, q6_1, q6_2], [(bin false q6_3 q6_1), q6_3, q6_1, (bin false q6_3 q6_4), q6_4, q6_0, q6_2], [(bin true q6_3 q6_1), q6_1, (bin false q6_3 q6_4), q6_4, q6_0, q6_2], [(bin true q6_3 q6_1), q6_3, q6_1, (bin false q6_3 q6_4), q6_4, q6_0, q6_2], [(bin false q6_3 q6_2), q6_3, q6_2, (bin false q6_3 q6_4), q6_4, q6_0, q6_1], [(bin true q6_3 q6_2), q6_2, (bin false q6_3 q6_4), q6_4, q6_0, q6_1], [(bin true q6_3 q6_2), q6_3, q6_2, (bin false q6_3 q6_4), q6_4, q6_0, q6_1], [(bin false q6_4 q6_0), q6_0, (bin false q6_3 q6_4), q6_3, q6_1, q6_2], [(bin false q6_4 q6_0), q6_4, q6_0, (bin false q6_3 q6_4), q6_3, q6_1, q6_2], [(bin true q6_4 q6_0), q6_4, q6_0, (bin false q6_3 q6_4), q6_3, q6_1, q6_2], [(bin false q6_4 q6_1), q6_4, q6_1, (bin false q6_3 q6_4), q6_3, q6_0, q6_2], [(bin true q6_4 q6_1), q6_1, (bin false q6_3 q6_4), q6_3, q6_0, q6_2], [(bin true q6_4 q6_1), q6_4, q6_1, (bin false q6_3 q6_4), q6_3, q6_0, q6_2], [(bin false q6_4 q6_2), q6_4, q6_2, (bin false q6_3 q6_4), q6_3, q6_0, q6_1], [(bin true q6_4 q6_2), q6_2, (bin false q6_3 q6_4), q6_3, q6_0, q6_1], [(bin true q6_4 q6_2), q6_4, q6_2, (bin false q6_3 q6_4), q6_3, q6_0, q6_1], [(bin false q6_0 q6_1), q6_0, q6_1, (bin false q6_3 q6_4), q6_3, q6_4, q6_2], [(bin true q6_0 q6_1), q6_0, q6_1, (bin false q6_3 q6_4), q6_3, q6_4, q6_2], [(bin false q6_0 q6_2), q6_0, q6_2, (bin false q6_3 q6_4), q6_3, q6_4, q6_1], [(bin true q6_0 q6_2), q6_0, q6_2, (bin false q6_3 q6_4), q6_3, q6_4, q6_1], [(bin false q6_1 q6_2), q6_1, q6_2, (bin false q6_3 q6_4), q6_3, q6_4, q6_0], [(bin true q6_1 q6_2), q6_1, q6_2, (bin false q6_3 q6_4), q6_3, q6_4, q6_0]]

lemma allf6t0_b18_b : ∀ v ∈ tbf6t0_b18_b, search 6 0 v = false :=
  consAll nf6t0_b18_b0_ (consAll nf6t0_b18_b1_ (consAll nf6t0_b18_b2_ (consAll nf6t0_b18_b3_ (consAll nf6t0_b18_b4_ (consAll nf6t0_b18_b5_ (consAll nf6t0_b18_b6_ (consAll nf6t0_b18_b7_ (consAll nf6t0_b18_b8_ (consAll nf6t0_b18_b9_ (consAll nf6t0_b18_b10_ (consAll nf6t0_b18_b11_ (consAll nf6t0_b18_b12_ (consAll nf6t0_b18_b13_ (consAll nf6t0_b18_b14_ (consAll nf6t0_b18_b15_ (consAll nf6t0_b18_b16_ (consAll nf6t0_b18_b17_ (consAll nf6t0_b18_b18_ (consAll nf6t0_b18_b19_ (consAll nf6t0_b18_b20_ (consAll nf6t0_b18_b21_ (consAll nf6t0_b18_b22_ (consAll nf6t0_b18_b23_ (consAll nf6t0_b18_b24_ (consAll nf6t0_b18_b25_ (consAll nf6t0_b18_b26_ (consAll nf6t0_b18_b27_ (consAll nf6t0_b18_b28_ (consAll nf6t0_b18_b29_ (consAll nf6t0_b18_b30_ (consAll nf6t0_b18_b31_ (consAll nf6t0_b18_b32_ (consAll nf6t0_b18_b33_ (consAll nf6t0_b18_b34_ (consAll nf6t0_b18_b35_ (consAll nf6t0_b18_b36_ (consAll nf6t0_b18_b37_ (consAll nf6t0_b18_b38_ (consAll nf6t0_b18_b39_ (nilAll))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b18_ : search 7 0 [(bin false q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2] = false := by
  have e := search.eq_2 0 [(bin false q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2] 6
  rw [← orc_eq tbf6t0_b18_b (search 6 0) allf6t0_b18_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b0_ : search 6 0 [(bin false (bin true q6_3 q6_4) q6_0), q6_0, q6_3, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b1_ : search 6 0 [(bin false (bin true q6_3 q6_4) q6_0), (bin true q6_3 q6_4), q6_0, q6_3, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b2_ : search 6 0 [(bin true (bin true q6_3 q6_4) q6_0), q6_0, q6_3, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b3_ : search 6 0 [(bin true (bin true q6_3 q6_4) q6_0), (bin true q6_3 q6_4), q6_0, q6_3, q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b4_ : search 6 0 [(bin false (bin true q6_3 q6_4) q6_1), q6_1, q6_3, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b5_ : search 6 0 [(bin false (bin true q6_3 q6_4) q6_1), (bin true q6_3 q6_4), q6_1, q6_3, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b6_ : search 6 0 [(bin true (bin true q6_3 q6_4) q6_1), q6_1, q6_3, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b7_ : search 6 0 [(bin true (bin true q6_3 q6_4) q6_1), (bin true q6_3 q6_4), q6_1, q6_3, q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b8_ : search 6 0 [(bin false (bin true q6_3 q6_4) q6_2), q6_2, q6_3, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b9_ : search 6 0 [(bin false (bin true q6_3 q6_4) q6_2), (bin true q6_3 q6_4), q6_2, q6_3, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b10_ : search 6 0 [(bin true (bin true q6_3 q6_4) q6_2), q6_2, q6_3, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b11_ : search 6 0 [(bin true (bin true q6_3 q6_4) q6_2), (bin true q6_3 q6_4), q6_2, q6_3, q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b12_ : search 6 0 [(bin false q6_3 q6_4), (bin true q6_3 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b13_ : search 6 0 [(bin false q6_3 q6_4), q6_3, (bin true q6_3 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b14_ : search 6 0 [(bin false q6_3 q6_4), q6_4, (bin true q6_3 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b15_ : search 6 0 [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_3 q6_4), q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b16_ : search 6 0 [(bin false q6_3 q6_0), q6_3, q6_0, (bin true q6_3 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b17_ : search 6 0 [(bin true q6_3 q6_0), q6_0, (bin true q6_3 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b18_ : search 6 0 [(bin true q6_3 q6_0), q6_3, q6_0, (bin true q6_3 q6_4), q6_4, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b19_ : search 6 0 [(bin false q6_3 q6_1), q6_3, q6_1, (bin true q6_3 q6_4), q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b20_ : search 6 0 [(bin true q6_3 q6_1), q6_3, q6_1, (bin true q6_3 q6_4), q6_4, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b21_ : search 6 0 [(bin false q6_3 q6_2), q6_3, q6_2, (bin true q6_3 q6_4), q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b22_ : search 6 0 [(bin true q6_3 q6_2), q6_3, q6_2, (bin true q6_3 q6_4), q6_4, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b23_ : search 6 0 [(bin false q6_4 q6_0), q6_4, q6_0, (bin true q6_3 q6_4), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b24_ : search 6 0 [(bin true q6_4 q6_0), q6_0, (bin true q6_3 q6_4), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b25_ : search 6 0 [(bin true q6_4 q6_0), q6_4, q6_0, (bin true q6_3 q6_4), q6_3, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b26_ : search 6 0 [(bin false q6_4 q6_1), q6_4, q6_1, (bin true q6_3 q6_4), q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b27_ : search 6 0 [(bin true q6_4 q6_1), q6_4, q6_1, (bin true q6_3 q6_4), q6_3, q6_0, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b28_ : search 6 0 [(bin false q6_4 q6_2), q6_4, q6_2, (bin true q6_3 q6_4), q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b29_ : search 6 0 [(bin true q6_4 q6_2), q6_4, q6_2, (bin true q6_3 q6_4), q6_3, q6_0, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b30_ : search 6 0 [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_3 q6_4), q6_3, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b31_ : search 6 0 [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_3 q6_4), q6_3, q6_4, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b32_ : search 6 0 [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_3 q6_4), q6_3, q6_4, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b33_ : search 6 0 [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_3 q6_4), q6_3, q6_4, q6_1] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b34_ : search 6 0 [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_3 q6_4), q6_3, q6_4, q6_0] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_b35_ : search 6 0 [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_3 q6_4), q6_3, q6_4, q6_0] = false := by decide +kernel

def tbf6t0_b19_b : List (List Sig) := [[(bin false (bin true q6_3 q6_4) q6_0), q6_0, q6_3, q6_4, q6_1, q6_2], [(bin false (bin true q6_3 q6_4) q6_0), (bin true q6_3 q6_4), q6_0, q6_3, q6_4, q6_1, q6_2], [(bin true (bin true q6_3 q6_4) q6_0), q6_0, q6_3, q6_4, q6_1, q6_2], [(bin true (bin true q6_3 q6_4) q6_0), (bin true q6_3 q6_4), q6_0, q6_3, q6_4, q6_1, q6_2], [(bin false (bin true q6_3 q6_4) q6_1), q6_1, q6_3, q6_4, q6_0, q6_2], [(bin false (bin true q6_3 q6_4) q6_1), (bin true q6_3 q6_4), q6_1, q6_3, q6_4, q6_0, q6_2], [(bin true (bin true q6_3 q6_4) q6_1), q6_1, q6_3, q6_4, q6_0, q6_2], [(bin true (bin true q6_3 q6_4) q6_1), (bin true q6_3 q6_4), q6_1, q6_3, q6_4, q6_0, q6_2], [(bin false (bin true q6_3 q6_4) q6_2), q6_2, q6_3, q6_4, q6_0, q6_1], [(bin false (bin true q6_3 q6_4) q6_2), (bin true q6_3 q6_4), q6_2, q6_3, q6_4, q6_0, q6_1], [(bin true (bin true q6_3 q6_4) q6_2), q6_2, q6_3, q6_4, q6_0, q6_1], [(bin true (bin true q6_3 q6_4) q6_2), (bin true q6_3 q6_4), q6_2, q6_3, q6_4, q6_0, q6_1], [(bin false q6_3 q6_4), (bin true q6_3 q6_4), q6_0, q6_1, q6_2], [(bin false q6_3 q6_4), q6_3, (bin true q6_3 q6_4), q6_0, q6_1, q6_2], [(bin false q6_3 q6_4), q6_4, (bin true q6_3 q6_4), q6_0, q6_1, q6_2], [(bin false q6_3 q6_4), q6_3, q6_4, (bin true q6_3 q6_4), q6_0, q6_1, q6_2], [(bin false q6_3 q6_0), q6_3, q6_0, (bin true q6_3 q6_4), q6_4, q6_1, q6_2], [(bin true q6_3 q6_0), q6_0, (bin true q6_3 q6_4), q6_4, q6_1, q6_2], [(bin true q6_3 q6_0), q6_3, q6_0, (bin true q6_3 q6_4), q6_4, q6_1, q6_2], [(bin false q6_3 q6_1), q6_3, q6_1, (bin true q6_3 q6_4), q6_4, q6_0, q6_2], [(bin true q6_3 q6_1), q6_3, q6_1, (bin true q6_3 q6_4), q6_4, q6_0, q6_2], [(bin false q6_3 q6_2), q6_3, q6_2, (bin true q6_3 q6_4), q6_4, q6_0, q6_1], [(bin true q6_3 q6_2), q6_3, q6_2, (bin true q6_3 q6_4), q6_4, q6_0, q6_1], [(bin false q6_4 q6_0), q6_4, q6_0, (bin true q6_3 q6_4), q6_3, q6_1, q6_2], [(bin true q6_4 q6_0), q6_0, (bin true q6_3 q6_4), q6_3, q6_1, q6_2], [(bin true q6_4 q6_0), q6_4, q6_0, (bin true q6_3 q6_4), q6_3, q6_1, q6_2], [(bin false q6_4 q6_1), q6_4, q6_1, (bin true q6_3 q6_4), q6_3, q6_0, q6_2], [(bin true q6_4 q6_1), q6_4, q6_1, (bin true q6_3 q6_4), q6_3, q6_0, q6_2], [(bin false q6_4 q6_2), q6_4, q6_2, (bin true q6_3 q6_4), q6_3, q6_0, q6_1], [(bin true q6_4 q6_2), q6_4, q6_2, (bin true q6_3 q6_4), q6_3, q6_0, q6_1], [(bin false q6_0 q6_1), q6_0, q6_1, (bin true q6_3 q6_4), q6_3, q6_4, q6_2], [(bin true q6_0 q6_1), q6_0, q6_1, (bin true q6_3 q6_4), q6_3, q6_4, q6_2], [(bin false q6_0 q6_2), q6_0, q6_2, (bin true q6_3 q6_4), q6_3, q6_4, q6_1], [(bin true q6_0 q6_2), q6_0, q6_2, (bin true q6_3 q6_4), q6_3, q6_4, q6_1], [(bin false q6_1 q6_2), q6_1, q6_2, (bin true q6_3 q6_4), q6_3, q6_4, q6_0], [(bin true q6_1 q6_2), q6_1, q6_2, (bin true q6_3 q6_4), q6_3, q6_4, q6_0]]

lemma allf6t0_b19_b : ∀ v ∈ tbf6t0_b19_b, search 6 0 v = false :=
  consAll nf6t0_b19_b0_ (consAll nf6t0_b19_b1_ (consAll nf6t0_b19_b2_ (consAll nf6t0_b19_b3_ (consAll nf6t0_b19_b4_ (consAll nf6t0_b19_b5_ (consAll nf6t0_b19_b6_ (consAll nf6t0_b19_b7_ (consAll nf6t0_b19_b8_ (consAll nf6t0_b19_b9_ (consAll nf6t0_b19_b10_ (consAll nf6t0_b19_b11_ (consAll nf6t0_b19_b12_ (consAll nf6t0_b19_b13_ (consAll nf6t0_b19_b14_ (consAll nf6t0_b19_b15_ (consAll nf6t0_b19_b16_ (consAll nf6t0_b19_b17_ (consAll nf6t0_b19_b18_ (consAll nf6t0_b19_b19_ (consAll nf6t0_b19_b20_ (consAll nf6t0_b19_b21_ (consAll nf6t0_b19_b22_ (consAll nf6t0_b19_b23_ (consAll nf6t0_b19_b24_ (consAll nf6t0_b19_b25_ (consAll nf6t0_b19_b26_ (consAll nf6t0_b19_b27_ (consAll nf6t0_b19_b28_ (consAll nf6t0_b19_b29_ (consAll nf6t0_b19_b30_ (consAll nf6t0_b19_b31_ (consAll nf6t0_b19_b32_ (consAll nf6t0_b19_b33_ (consAll nf6t0_b19_b34_ (consAll nf6t0_b19_b35_ (nilAll))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t0_b19_ : search 7 0 [(bin true q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2] = false := by
  have e := search.eq_2 0 [(bin true q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2] 6
  rw [← orc_eq tbf6t0_b19_b (search 6 0) allf6t0_b19_b] at e
  exact e.trans (by decide +kernel)

def tbf6t0_b : List (List Sig) := [[(bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin true q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4], [(bin true q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4], [(bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3], [(bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4], [(bin false q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4], [(bin true q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3], [(bin true q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3], [(bin false q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4], [(bin true q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3], [(bin true q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3], [(bin false q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2]]

lemma allf6t0_b : ∀ v ∈ tbf6t0_b, search 7 0 v = false :=
  consAll nf6t0_b0_ (consAll nf6t0_b1_ (consAll nf6t0_b2_ (consAll nf6t0_b3_ (consAll nf6t0_b4_ (consAll nf6t0_b5_ (consAll nf6t0_b6_ (consAll nf6t0_b7_ (consAll nf6t0_b8_ (consAll nf6t0_b9_ (consAll nf6t0_b10_ (consAll nf6t0_b11_ (consAll nf6t0_b12_ (consAll nf6t0_b13_ (consAll nf6t0_b14_ (consAll nf6t0_b15_ (consAll nf6t0_b16_ (consAll nf6t0_b17_ (consAll nf6t0_b18_ (consAll nf6t0_b19_ (nilAll))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative6_0 : search 8 0 r6 = false := by
  have e := search.eq_2 0 r6 7
  rw [← orc_eq tbf6t0_b (search 7 0) allf6t0_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b0_ : search 7 1 [(bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b1_ : search 7 1 [(bin true q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b2_ : search 7 1 [(bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b3_ : search 7 1 [(bin true q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b4_ : search 7 1 [(bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b5_ : search 7 1 [(bin true q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b6_ : search 7 1 [(bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b7_ : search 7 1 [(bin true q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b8_ : search 7 1 [(bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b9_ : search 7 1 [(bin true q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b10_ : search 7 1 [(bin false q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b11_ : search 7 1 [(bin true q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b12_ : search 7 1 [(bin false q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b13_ : search 7 1 [(bin true q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b14_ : search 7 1 [(bin false q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b15_ : search 7 1 [(bin true q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b16_ : search 7 1 [(bin false q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b17_ : search 7 1 [(bin true q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b18_ : search 7 1 [(bin false q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_b19_ : search 7 1 [(bin true q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_u0_ : search 7 0 [(neg q6_0), q6_0, q6_1, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_u1_ : search 7 0 [(neg q6_1), q6_1, q6_0, q6_2, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_u2_ : search 7 0 [(neg q6_2), q6_2, q6_0, q6_1, q6_3, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_u3_ : search 7 0 [(neg q6_3), q6_3, q6_0, q6_1, q6_2, q6_4] = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma nf6t1_u4_ : search 7 0 [(neg q6_4), q6_4, q6_0, q6_1, q6_2, q6_3] = false := by decide +kernel

def tbf6t1_u : List (List Sig) := [[(neg q6_0), q6_0, q6_1, q6_2, q6_3, q6_4], [(neg q6_1), q6_1, q6_0, q6_2, q6_3, q6_4], [(neg q6_2), q6_2, q6_0, q6_1, q6_3, q6_4], [(neg q6_3), q6_3, q6_0, q6_1, q6_2, q6_4], [(neg q6_4), q6_4, q6_0, q6_1, q6_2, q6_3]]

lemma allf6t1_u : ∀ v ∈ tbf6t1_u, search 7 0 v = false :=
  consAll nf6t1_u0_ (consAll nf6t1_u1_ (consAll nf6t1_u2_ (consAll nf6t1_u3_ (consAll nf6t1_u4_ (nilAll)))))

def tbf6t1_b : List (List Sig) := [[(bin false q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin true q6_0 q6_1), q6_0, q6_1, q6_2, q6_3, q6_4], [(bin false q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4], [(bin true q6_0 q6_2), q6_0, q6_2, q6_1, q6_3, q6_4], [(bin false q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4], [(bin true q6_0 q6_3), q6_0, q6_3, q6_1, q6_2, q6_4], [(bin false q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3], [(bin true q6_0 q6_4), q6_0, q6_4, q6_1, q6_2, q6_3], [(bin false q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4], [(bin true q6_1 q6_2), q6_1, q6_2, q6_0, q6_3, q6_4], [(bin false q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4], [(bin true q6_1 q6_3), q6_1, q6_3, q6_0, q6_2, q6_4], [(bin false q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3], [(bin true q6_1 q6_4), q6_1, q6_4, q6_0, q6_2, q6_3], [(bin false q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4], [(bin true q6_2 q6_3), q6_2, q6_3, q6_0, q6_1, q6_4], [(bin false q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3], [(bin true q6_2 q6_4), q6_2, q6_4, q6_0, q6_1, q6_3], [(bin false q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2], [(bin true q6_3 q6_4), q6_3, q6_4, q6_0, q6_1, q6_2]]

lemma allf6t1_b : ∀ v ∈ tbf6t1_b, search 7 1 v = false :=
  consAll nf6t1_b0_ (consAll nf6t1_b1_ (consAll nf6t1_b2_ (consAll nf6t1_b3_ (consAll nf6t1_b4_ (consAll nf6t1_b5_ (consAll nf6t1_b6_ (consAll nf6t1_b7_ (consAll nf6t1_b8_ (consAll nf6t1_b9_ (consAll nf6t1_b10_ (consAll nf6t1_b11_ (consAll nf6t1_b12_ (consAll nf6t1_b13_ (consAll nf6t1_b14_ (consAll nf6t1_b15_ (consAll nf6t1_b16_ (consAll nf6t1_b17_ (consAll nf6t1_b18_ (consAll nf6t1_b19_ (nilAll))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative6_1 : search 8 1 r6 = false := by
  have e := search.eq_2 1 r6 7
  rw [show (1 : ℕ) - 1 = 0 from rfl] at e
  rw [← orc_eq tbf6t1_u (search 7 0) allf6t1_u, ← orc_eq tbf6t1_b (search 7 1) allf6t1_b] at e
  exact e.trans (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn6 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276808424 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276808424 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4276808424 r6 8 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative6_0
      · exact negative6_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.and,[1,2]⟩,⟨.and,[3,4]⟩,⟨.or,[0,6]⟩,⟨.or,[3,4]⟩,⟨.and,[0,8]⟩,⟨.or,[1,2]⟩,⟨.and,[7,10]⟩,⟨.or,[5,11]⟩,⟨.or,[9,12]⟩],13,by simp,?_,by decide +kernel⟩
  change 8 < gs.length at bound
  change 9 ≤ gs.length
  omega

def r7 : List Sig := [(0x1ffffffff001ffc007ff001fffff800fffffffffff001fffff800ffe003fffff,0x4088110220440881102204408811022044088110220440881102204408811022),(0xe003fffffffe000007ffffe003fffff001ffc007ffffe003ffffffffffc007ff,0x8410821042084108210420841082104208410821042084108210420841082104),(0xfffc007ffffffffff800000003fffffffe000007fffffffc00000ffffffff800,0x921242484909212424849092124248490921242484909212424849092124248),(0x7ffffffffffffffffffc00000000000007fffffffffffff00000000000,0x11c2384708e11c2384708e11c2384708e11c2384708e11c2384708e11c238470),(0x7ffffffffffffffffffffffffffffffff8000000000000000000000000,0x1e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative7_0 : search 7 0 r7 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative7_1 : search 7 1 r7 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn7 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276808936 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276808936 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4276808936 r7 7 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative7_0
      · exact negative7_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.or,[0,1]⟩,⟨.and,[2,5]⟩,⟨.or,[0,2]⟩,⟨.and,[4,7]⟩,⟨.or,[1,8]⟩,⟨.or,[0,3]⟩,⟨.and,[9,10]⟩,⟨.or,[6,11]⟩],12,by simp,?_,by decide +kernel⟩
  change 7 < gs.length at bound
  change 8 ≤ gs.length
  omega

def r8 : List Sig := [(0xe003fffff001ffc007ff001fffff800fffffffffff001fffff800fffffc007ff,0x40280500a0140280500a0140280500a0140280500a0140280500a0140280500a),(0xfffc007ffffe000007ffffe003fffff001ffc007ffffe003fffff001fffff800,0x84308610c2184308610c2184308610c2184308610c2184308610c2184308610c),(0xfffffffffffffffff800000003fffffffe000007fffffffc00000001ffffffff,0x941282504a0941282504a0941282504a0941282504a0941282504a094128250),(0x7ffffffffffffffffffc00000000000007fffffffffffffffe00000000,0x1182304608c1182304608c1182304608c1182304608c1182304608c118230460),(0x7ffffffffffffffffffffffffffffffff8000000000000000000000000,0x1e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative8_0 : search 6 0 r8 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative8_1 : search 6 1 r8 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn8 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276809440 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276809440 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4276809440 r8 6 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative8_0
      · exact negative8_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.or,[0,1]⟩,⟨.and,[2,3]⟩,⟨.or,[0,6]⟩,⟨.and,[4,7]⟩,⟨.or,[2,3]⟩,⟨.and,[5,9]⟩,⟨.or,[8,10]⟩],11,by simp,?_,by decide +kernel⟩
  change 6 < gs.length at bound
  change 7 ≤ gs.length
  omega

def r9 : List Sig := [(0xe003fffff001ffc007ff001fffff800fffffffffff001ffc007ff001ffc007ff,0x4148290520a4148290520a4148290520a4148290520a4148290520a414829052),(0xfffffffffffe000007ffffe003fffff001ffc007ffffe000007fffffffffffff,0x8410821042084108210420841082104208410821042084108210420841082104),(0xfffc007ffffffffff800000003fffffffe000007ffffffffff800001fffff800,0x8610c2184308610c2184308610c2184308610c2184308610c2184308610c218),(0x7ffffffffffffffffffc00000000000007fffffffffffffffe00000000,0x1182304608c1182304608c1182304608c1182304608c1182304608c118230460),(0x7ffffffffffffffffffffffffffffffff8000000000000000000000000,0x1e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative9_0 : search 6 0 r9 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma negative9_1 : search 6 1 r9 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma fn9 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 4276813000 x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn x) = evalT 4276813000 x := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo,Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have bound := cost 4276813000 r9 6 (by rfl) (by decide +kernel) (by decide +kernel)
    (by rfl) (by decide +kernel) (by
      intro t; fin_cases t
      · exact negative9_0
      · exact negative9_1) ⟨gs,o⟩ legal hn he
  refine ⟨[⟨.and,[0,4]⟩,⟨.and,[2,3]⟩,⟨.or,[0,2]⟩,⟨.or,[1,6]⟩,⟨.or,[3,7]⟩,⟨.and,[8,9]⟩,⟨.or,[5,10]⟩],11,by simp,?_,by decide +kernel⟩
  change 6 < gs.length at bound
  change 7 ≤ gs.length
  omega

end PEqualNP.Outside.L_meta_1443_aux

theorem PEqualNP.Outside.L_meta_1443 : ∀ T ∈ ({0xfeeafcc0, 0xeeeaeaea, 0xeeeaeee8, 0xeeeeeee0, 0xfee8eee8, 0xfeeaeaaa, 0xfeeaeae8, 0xfeeaece8, 0xfeeaeee0, 0xfeeafcc8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T h
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1443_aux.fn0
  · exact PEqualNP.Outside.L_meta_1443_aux.fn1
  · exact PEqualNP.Outside.L_meta_1443_aux.fn2
  · exact PEqualNP.Outside.L_meta_1443_aux.fn3
  · exact PEqualNP.Outside.L_meta_1443_aux.fn4
  · exact PEqualNP.Outside.L_meta_1443_aux.fn5
  · exact PEqualNP.Outside.L_meta_1443_aux.fn6
  · exact PEqualNP.Outside.L_meta_1443_aux.fn7
  · exact PEqualNP.Outside.L_meta_1443_aux.fn8
  · exact PEqualNP.Outside.L_meta_1443_aux.fn9
