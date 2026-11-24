import Mathlib
import PEqualNP.Defs
-- The live-wire checker is adapted from ljste's PR 2918 and jfsantoropereira's L-meta-1007.
-- The circuit search follows the accepted proof of L-meta-1421. Apache-2.0.
-- Each pair below compares a true row with a false row from this table.
namespace PEqualNP.Outside.L_meta_1423_aux

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

def mono (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

private lemma address {env : List Sig} {a : Sig} (ha : a ∈ env) :
    ∃ j : ℕ, env.getD j zero = a := by
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp ha
  exact ⟨j.val, (List.getD_eq_getElem env zero j.isLt).trans hj⟩

-- Rebuild a circuit when compression removes its only negation.
private lemma realizeZero {k : ℕ} {S : Finset Sig} (h : Live k 0 S) (env : List Sig)
    (available : ∀ a ∈ S, a ∈ env) :
    ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, mono g) ∧ gs.length ≤ k ∧
      (execute gs env).getD o zero = target := by
  induction k generalizing S env with
  | zero =>
    obtain ⟨_,rfl⟩ := h
    obtain ⟨o,ho⟩ := address (available target (by simp))
    exact ⟨[],o,by simp,by simp,ho⟩
  | succ k ih =>
    rcases h with ⟨t,U,a,ht,_⟩ | ⟨U,a,b,d,rfl,_,_,_,_,tail⟩
    · omega
    · obtain ⟨p,hp⟩ := address (available a (by simp))
      obtain ⟨q,hq⟩ := address (available b (by simp))
      let g : Gate := ⟨if d then .or else .and,[p,q]⟩
      have value : gv env g = bin d a b := by
        cases d
        · change bin false (env.getD p zero) (bin false (env.getD q zero) one) = bin false a b
          rw [hp,hq,(bin_laws b).1]
        · change bin true (env.getD p zero) (bin true (env.getD q zero) zero) = bin true a b
          rw [hp,hq,(bin_laws b).2.1]
      have next : ∀ v ∈ insert (bin d a b) U, v ∈ env ++ [gv env g] := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · simp [value]
        · exact List.mem_append_left _ (available _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)))
      obtain ⟨gs,o,hm,hlen,he⟩ := ih tail _ next
      refine ⟨g::gs,o,?_,by simp; omega,he⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · cases d <;> simp [mono,g]
      · exact hm u hu

def rowIndex (pick : List ℕ) (x : Fin 5 → Bool) : Fin 256 :=
  Fin.ofNat 256 (pick.getD (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) 0)

def monotoneAnswer (T k : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, mono g) ∧ gs.length ≤ k ∧
    ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT T x

private lemma tableFromZero {T k : ℕ} {raw : List Sig} {pick : List ℕ}
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (surj : ∀ x, sample raw (evalT T x) (rowIndex pick x) = x)
    (h : Live k 0 raw.toFinset) : monotoneAnswer T k := by
  obtain ⟨gs,o,hm,hs,hit⟩ := realizeZero h raw (fun _ ha => List.mem_toFinset.mp ha)
  refine ⟨gs,o,hm,hs,?_⟩
  intro x
  let s := evalT T x
  let i := rowIndex pick x
  have start : List.ofFn x = raw.map (bit s i) :=
    (congrArg List.ofFn (surj x)).symm.trans (sample_list raw raw_id s i)
  have legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
    intro g hg
    rcases (hm g hg).1 with e | e <;> simp [e]
  change (gs.foldl _ (List.ofFn x)).getD o false = s
  rw [start, ← execute_bits gs s i raw legal, b_read, hit]
  cases s
  · change (0 : B).getLsbD i.val = false
    simp
  · change (BitVec.allOnes 256).getLsbD i.val = true
    rw [BitVec.getLsbD_allOnes]
    simp

-- Once the monotone case has been reconstructed, only runs with one remaining
-- inversion require an exhaustive lower bound.
theorem mixedTable (T cap : ℕ) (raw : List Sig) (pick : List ℕ)
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (samples : ∀ b i, evalT T (sample raw b i) = b)
    (surj : ∀ x, sample raw (evalT T x) (rowIndex pick x) = x)
    (nd : raw.Nodup) (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (test : search cap 1 raw = false) (upper : monotoneAnswer T (cap+1))
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (single : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (correct : ∀ x, C.eval (List.ofFn x) = evalT T x) : monotoneAnswer T C.gates.length := by
  by_cases enough : cap+1 ≤ C.gates.length
  · obtain ⟨gs,o,hm,hs,he⟩ := upper
    exact ⟨gs,o,hm,hs.trans enough,he⟩
  obtain ⟨k,t,S,hk,hcount,live,sub⟩ := extract C.gates raw legal (circuit_target T raw raw_id samples C legal correct)
  have ht := notCount C.gates single
  obtain rfl := (necessary raw essential live sub).symm
  by_cases hz : t = 0
  · subst t
    obtain ⟨gs,o,hm,hs,he⟩ := tableFromZero raw_id surj live
    exact ⟨gs,o,hm,hs.trans hk,he⟩
  · have eq : t = 1 := by omega
    subst t
    have good := search_complete live cap (by omega) raw nd rfl
    rw [test] at good
    contradiction

def raw0 : List Sig := [(0xfffffffff00000ffffffffffffffffffffffffffffffffffffffffffffffffff, 0x210922109221092210922109221092210922109221092210922109221092),
    (0xffffffffffffff00000ffffffffff00000ffffffffff00000fffffffffffffff, 0x4a5244a5244a5244a5244a5244a5244a5244a5244a5244a5244a5244a524),
    (0xfffffffffffffff00000ffffffffff00000ffffffffff00000fffff00000, 0x8c6388c6388c6388c6388c6388c6388c6388c6388c6388c6388c6388c638),
    (0xffffffffffffffffffff000000000000000fffffffffffffff0000000000, 0xf07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0),
    (0xfffffffffffffffffffffffffffffffffff0000000000000000000000000, 0xff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800)]

def pick0 : List ℕ := [0, 1, 2, 0, 3, 4, 5, 20, 6, 7, 8, 40, 9, 60, 10, 80, 11, 12, 13, 100, 14, 120, 15, 140, 16, 17, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One01 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[0]! raw0[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One02 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[0]! raw0[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One03 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[0]! raw0[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One04 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[0]! raw0[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One12 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[1]! raw0[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One13 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[1]! raw0[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One14 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[1]! raw0[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One23 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[2]! raw0[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One24 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[2]! raw0[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0One34 :
    slowBinary 6 1 (search 6 1) raw0 (coverage true raw0) raw0[3]! raw0[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0Unary0 :
    unaryAt 6 0 (search 6 0) raw0 (coverage false raw0) raw0[0]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0Unary1 :
    unaryAt 6 0 (search 6 0) raw0 (coverage false raw0) raw0[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0Unary2 :
    unaryAt 6 0 (search 6 0) raw0 (coverage false raw0) raw0[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0Unary3 :
    unaryAt 6 0 (search 6 0) raw0 (coverage false raw0) raw0[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case0Unary4 :
    unaryAt 6 0 (search 6 0) raw0 (coverage false raw0) raw0[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

lemma ruledOut0One : search 7 1 raw0 = false := by
  have bin : binaryMoves 6 1 (search 6 1) raw0 = false := by
    change scanPairs (slowBinary 6 1 (search 6 1) raw0 (coverage true raw0)) [raw0[0]!, raw0[1]!, raw0[2]!, raw0[3]!, raw0[4]!] = false
    simp only [scanPairs, List.any_cons, List.any_nil, case0One01, case0One02, case0One03, case0One04, case0One12, case0One13, case0One14, case0One23, case0One24, case0One34, Bool.false_or]

  have un : unaryMoves 6 0 (search 6 0) raw0 = false := by
    change [raw0[0]!, raw0[1]!, raw0[2]!, raw0[3]!, raw0[4]!].any (unaryAt 6 0 (search 6 0) raw0 (coverage false raw0)) = false
    simp only [List.any_cons, List.any_nil, case0Unary0, case0Unary1, case0Unary2, case0Unary3, case0Unary4, Bool.false_or]

  change stepTest 6 1 raw0 (search 6 0) (search 6 1) = false
  unfold stepTest
  rw [bin, un]
  rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table0 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3903367304 x) :
    monotoneAnswer 3903367304 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3903367304 7 raw0 pick0 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut0One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [5, 11]⟩], 12, by simp [mono], by decide, by decide +kernel⟩

def raw1 : List Sig := [(0xfffffffff00000ffffffffffffffffffffffffffffff00000fffffffffffffff, 0x214922149221492214922149221492214922149221492214922149221492),
    (0xffffffffffffff00000ffffffffff00000ffffffffffffffffffffffffffffff, 0x4a1244a1244a1244a1244a1244a1244a1244a1244a1244a1244a1244a124),
    (0xfffffffffffffff00000ffffffffff00000ffffffffff00000fffff00000, 0x8c6388c6388c6388c6388c6388c6388c6388c6388c6388c6388c6388c638),
    (0xffffffffffffffffffff000000000000000fffffffffffffff0000000000, 0xf07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0f07c0),
    (0xfffffffffffffffffffffffffffffffffff0000000000000000000000000, 0xff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800)]

def pick1 : List ℕ := [0, 1, 2, 0, 3, 4, 5, 20, 6, 7, 8, 40, 9, 10, 60, 80, 11, 12, 13, 100, 14, 120, 15, 140, 16, 17, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut1One : search 5 1 raw1 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table1 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3903375496 x) :
    monotoneAnswer 3903375496 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3903375496 5 raw1 pick1 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut1One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [5, 9]⟩], 10, by simp [mono], by decide, by decide +kernel⟩

def raw2 : List Sig := [(0xfffffffff00000ffffffffffffffffffffffffffffff00000fffffffffffffff, 0x2112a2112a2112a2112a2112a2112a2112a2112a2112a2112a2112a2112a),
    (0xffffffffffffff00000ffffffffff00000fffffffffffffff00000ffffffffff, 0x4a24c4a24c4a24c4a24c4a24c4a24c4a24c4a24c4a24c4a24c4a24c4a24c),
    (0xfffffffffffffffffff00000ffffffffff00000fffffffffffffff00000fffff, 0x8c4708c4708c4708c4708c4708c4708c4708c4708c4708c4708c4708c470),
    (0xffffffffffffffffffff000000000000000ffffffffffffffffffff00000, 0xf0780f0780f0780f0780f0780f0780f0780f0780f0780f0780f0780f0780),
    (0xfffffffffffffffffffffffffffffffffff0000000000000000000000000, 0xff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800)]

def pick2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 20, 10, 40, 60, 80, 11, 12, 13, 100, 14, 120, 15, 140, 16, 17, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One01 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[0]! raw2[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One02 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[0]! raw2[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One03 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[0]! raw2[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One04 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[0]! raw2[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One12 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[1]! raw2[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One13 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[1]! raw2[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One14 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[1]! raw2[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One23 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[2]! raw2[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One24 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[2]! raw2[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2One34 :
    slowBinary 6 1 (search 6 1) raw2 (coverage true raw2) raw2[3]! raw2[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2Unary0 :
    unaryAt 6 0 (search 6 0) raw2 (coverage false raw2) raw2[0]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2Unary1 :
    unaryAt 6 0 (search 6 0) raw2 (coverage false raw2) raw2[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2Unary2 :
    unaryAt 6 0 (search 6 0) raw2 (coverage false raw2) raw2[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2Unary3 :
    unaryAt 6 0 (search 6 0) raw2 (coverage false raw2) raw2[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case2Unary4 :
    unaryAt 6 0 (search 6 0) raw2 (coverage false raw2) raw2[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

lemma ruledOut2One : search 7 1 raw2 = false := by
  have bin : binaryMoves 6 1 (search 6 1) raw2 = false := by
    change scanPairs (slowBinary 6 1 (search 6 1) raw2 (coverage true raw2)) [raw2[0]!, raw2[1]!, raw2[2]!, raw2[3]!, raw2[4]!] = false
    simp only [scanPairs, List.any_cons, List.any_nil, case2One01, case2One02, case2One03, case2One04, case2One12, case2One13, case2One14, case2One23, case2One24, case2One34, Bool.false_or]

  have un : unaryMoves 6 0 (search 6 0) raw2 = false := by
    change [raw2[0]!, raw2[1]!, raw2[2]!, raw2[3]!, raw2[4]!].any (unaryAt 6 0 (search 6 0) raw2 (coverage false raw2)) = false
    simp only [List.any_cons, List.any_nil, case2Unary0, case2Unary1, case2Unary2, case2Unary3, case2Unary4, Bool.false_or]

  change stepTest 6 1 raw2 (search 6 0) (search 6 1) = false
  unfold stepTest
  rw [bin, un]
  rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table2 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3903383680 x) :
    monotoneAnswer 3903383680 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3903383680 7 raw2 pick2 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut2One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [5, 11]⟩], 12, by simp [mono], by decide, by decide +kernel⟩

def raw3 : List Sig := [(0xfffffffff00000fffffffffffffff00000fffffffffffffff00000ffffffffff, 0x222aa222aa222aa222aa222aa222aa222aa222aa222aa222aa222aa222aa),
    (0xffffffffffffff00000fffffffffffffff00000fffffffffffffff00000fffff, 0x444cc444cc444cc444cc444cc444cc444cc444cc444cc444cc444cc444cc),
    (0xfffffffffffffff00000fffffffffffffff00000fffffffffffffff00000, 0x888f0888f0888f0888f0888f0888f0888f0888f0888f0888f0888f0888f0),
    (0xffffffffffffffffffffffff00000000000000000000ffffffffffffffffffff, 0xf0f00f0f00f0f00f0f00f0f00f0f00f0f00f0f00f0f00f0f00f0f00f0f00),
    (0xffffffffffffffffffffffffffffffffffffffff00000000000000000000, 0xff000ff000ff000ff000ff000ff000ff000ff000ff000ff000ff000ff000)]

def pick3 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11, 20, 40, 60, 12, 13, 14, 80, 15, 100, 120, 140, 16, 17, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut3One : search 5 1 raw3 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table3 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3907577856 x) :
    monotoneAnswer 3907577856 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3907577856 5 raw3 pick3 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut3One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [5, 9]⟩], 10, by simp [mono], by decide, by decide +kernel⟩

def raw4 : List Sig := [(0xfffffffff00000ffffffffffffffffffffffffffffffffffffffffffffffffff, 0x212a0212a0212a0212a0212a0212a0212a0212a0212a0212a0212a0212a),
    (0xffffffffffffff00000fffff00000fffff00000ffffffffff00000ffffffffff, 0x54a4c54a4c54a4c54a4c54a4c54a4c54a4c54a4c54a4c54a4c54a4c54a4c),
    (0xfffffffffffffffffff0000000000ffffffffff00000ffffffffff00000fffff, 0x98c7098c7098c7098c7098c7098c7098c7098c7098c7098c7098c7098c70),
    (0xfffffffffffffffffffffffff000000000000000fffffffffffffff00000, 0xe0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80),
    (0xffffffffffffffffffffffffffffffffffffffff00000000000000000000, 0xff000ff000ff000ff000ff000ff000ff000ff000ff000ff000ff000ff000)]

def pick4 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 20, 10, 40, 11, 60, 12, 13, 14, 80, 15, 100, 16, 120, 17, 140, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One01 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[0]! raw4[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One02 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[0]! raw4[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One03 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[0]! raw4[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One04 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[0]! raw4[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One12 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[1]! raw4[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One13 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[1]! raw4[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One14 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[1]! raw4[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One23 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[2]! raw4[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One24 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[2]! raw4[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4One34 :
    slowBinary 7 1 (search 7 1) raw4 (coverage true raw4) raw4[3]! raw4[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4Unary0 :
    unaryAt 7 0 (search 7 0) raw4 (coverage false raw4) raw4[0]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4Unary1 :
    unaryAt 7 0 (search 7 0) raw4 (coverage false raw4) raw4[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4Unary2 :
    unaryAt 7 0 (search 7 0) raw4 (coverage false raw4) raw4[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4Unary3 :
    unaryAt 7 0 (search 7 0) raw4 (coverage false raw4) raw4[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case4Unary4 :
    unaryAt 7 0 (search 7 0) raw4 (coverage false raw4) raw4[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

lemma ruledOut4One : search 8 1 raw4 = false := by
  have bin : binaryMoves 7 1 (search 7 1) raw4 = false := by
    change scanPairs (slowBinary 7 1 (search 7 1) raw4 (coverage true raw4)) [raw4[0]!, raw4[1]!, raw4[2]!, raw4[3]!, raw4[4]!] = false
    simp only [scanPairs, List.any_cons, List.any_nil, case4One01, case4One02, case4One03, case4One04, case4One12, case4One13, case4One14, case4One23, case4One24, case4One34, Bool.false_or]

  have un : unaryMoves 7 0 (search 7 0) raw4 = false := by
    change [raw4[0]!, raw4[1]!, raw4[2]!, raw4[3]!, raw4[4]!].any (unaryAt 7 0 (search 7 0) raw4 (coverage false raw4)) = false
    simp only [List.any_cons, List.any_nil, case4Unary0, case4Unary1, case4Unary2, case4Unary3, case4Unary4, Bool.false_or]

  change stepTest 7 1 raw4 (search 7 0) (search 7 1) = false
  unfold stepTest
  rw [bin, un]
  rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table4 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3936921728 x) :
    monotoneAnswer 3936921728 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3936921728 8 raw4 pick4 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut4One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [8, 12]⟩], 13, by simp [mono], by decide, by decide +kernel⟩

def raw5 : List Sig := [(0xfffffffff00000fffffffffffffffffffffffffffffffffff00000ffffffffff, 0x292a0292a0292a0292a0292a0292a0292a0292a0292a0292a0292a0292a),
    (0xffffffffffffff00000fffff00000fffff00000fffffffffffffffffffffffff, 0x5424c5424c5424c5424c5424c5424c5424c5424c5424c5424c5424c5424c),
    (0xfffffffffffffffffff0000000000ffffffffff00000ffffffffff00000fffff, 0x98c7098c7098c7098c7098c7098c7098c7098c7098c7098c7098c7098c70),
    (0xfffffffffffffffffffffffff000000000000000fffffffffffffff00000, 0xe0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80),
    (0xffffffffffffffffffffffffffffffffffffffff00000000000000000000, 0xff000ff000ff000ff000ff000ff000ff000ff000ff000ff000ff000ff000)]

def pick5 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 20, 10, 11, 40, 60, 12, 13, 14, 80, 15, 100, 16, 120, 17, 140, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One01 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[0]! raw5[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One02 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[0]! raw5[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One03 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[0]! raw5[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One04 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[0]! raw5[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One12 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[1]! raw5[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One13 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[1]! raw5[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One14 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[1]! raw5[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One23 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[2]! raw5[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One24 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[2]! raw5[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5One34 :
    slowBinary 7 1 (search 7 1) raw5 (coverage true raw5) raw5[3]! raw5[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5Unary0 :
    unaryAt 7 0 (search 7 0) raw5 (coverage false raw5) raw5[0]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5Unary1 :
    unaryAt 7 0 (search 7 0) raw5 (coverage false raw5) raw5[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5Unary2 :
    unaryAt 7 0 (search 7 0) raw5 (coverage false raw5) raw5[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5Unary3 :
    unaryAt 7 0 (search 7 0) raw5 (coverage false raw5) raw5[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case5Unary4 :
    unaryAt 7 0 (search 7 0) raw5 (coverage false raw5) raw5[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

lemma ruledOut5One : search 8 1 raw5 = false := by
  have bin : binaryMoves 7 1 (search 7 1) raw5 = false := by
    change scanPairs (slowBinary 7 1 (search 7 1) raw5 (coverage true raw5)) [raw5[0]!, raw5[1]!, raw5[2]!, raw5[3]!, raw5[4]!] = false
    simp only [scanPairs, List.any_cons, List.any_nil, case5One01, case5One02, case5One03, case5One04, case5One12, case5One13, case5One14, case5One23, case5One24, case5One34, Bool.false_or]

  have un : unaryMoves 7 0 (search 7 0) raw5 = false := by
    change [raw5[0]!, raw5[1]!, raw5[2]!, raw5[3]!, raw5[4]!].any (unaryAt 7 0 (search 7 0) raw5 (coverage false raw5)) = false
    simp only [List.any_cons, List.any_nil, case5Unary0, case5Unary1, case5Unary2, case5Unary3, case5Unary4, Bool.false_or]

  change stepTest 7 1 raw5 (search 7 0) (search 7 1) = false
  unfold stepTest
  rw [bin, un]
  rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table5 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3936929920 x) :
    monotoneAnswer 3936929920 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3936929920 8 raw5 pick5 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut5One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.and, [5, 12]⟩], 13, by simp [mono], by decide, by decide +kernel⟩

def raw6 : List Sig := [(0xfffffffff00000ffffffffffffffffffffffffffffffffffffffff00000fffff, 0x152a0152a0152a0152a0152a0152a0152a0152a0152a0152a0152a0152a),
    (0xffffffffffffff00000fffff00000fffff00000fffff00000fffffffffffffff, 0x5464c5464c5464c5464c5464c5464c5464c5464c5464c5464c5464c5464c),
    (0xfffffffffffffffffff0000000000ffffffffff0000000000fffffffffffffff, 0x998709987099870998709987099870998709987099870998709987099870),
    (0xfffffffffffffffffffffffff00000000000000000000ffffffffff00000, 0xe1f80e1f80e1f80e1f80e1f80e1f80e1f80e1f80e1f80e1f80e1f80e1f80),
    (0xfffffffffffffffffffffffffffffffffffffffffffff000000000000000, 0xfe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000fe000)]

def pick6 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 10, 11, 12, 20, 40, 13, 60, 14, 80, 15, 100, 16, 120, 17, 140, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut6One : search 4 1 raw6 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table6 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3937058944 x) :
    monotoneAnswer 3937058944 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3937058944 4 raw6 pick6 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut6One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [0, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [5, 8]⟩], 9, by simp [mono], by decide, by decide +kernel⟩

def raw7 : List Sig := [(0xfffffffff00000ffffffffffffffffffff00000fffff00000fffffffffffffff, 0x1512a1512a1512a1512a1512a1512a1512a1512a1512a1512a1512a1512a),
    (0xffffffffffffff00000fffff00000ffffffffffffffffffff00000ffffffffff, 0x4624c4624c4624c4624c4624c4624c4624c4624c4624c4624c4624c4624c),
    (0xfffffffffffffffffff0000000000fffffffffffffffffffffffff00000fffff, 0x984709847098470984709847098470984709847098470984709847098470),
    (0xfffffffffffffffffffffffff0000000000ffffffffffffffffffff00000, 0xe0780e0780e0780e0780e0780e0780e0780e0780e0780e0780e0780e0780),
    (0xfffffffffffffffffffffffffffffffffff0000000000000000000000000, 0xff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800ff800)]

def pick7 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 20, 10, 40, 60, 80, 11, 12, 13, 14, 15, 16, 100, 120, 17, 140, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One01 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[0]! raw7[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One02 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[0]! raw7[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One03 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[0]! raw7[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One04 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[0]! raw7[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One12 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[1]! raw7[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One13 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[1]! raw7[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One14 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[1]! raw7[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One23 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[2]! raw7[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One24 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[2]! raw7[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7One34 :
    slowBinary 6 1 (search 6 1) raw7 (coverage true raw7) raw7[3]! raw7[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7Unary0 :
    unaryAt 6 0 (search 6 0) raw7 (coverage false raw7) raw7[0]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7Unary1 :
    unaryAt 6 0 (search 6 0) raw7 (coverage false raw7) raw7[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7Unary2 :
    unaryAt 6 0 (search 6 0) raw7 (coverage false raw7) raw7[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7Unary3 :
    unaryAt 6 0 (search 6 0) raw7 (coverage false raw7) raw7[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case7Unary4 :
    unaryAt 6 0 (search 6 0) raw7 (coverage false raw7) raw7[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

lemma ruledOut7One : search 7 1 raw7 = false := by
  have bin : binaryMoves 6 1 (search 6 1) raw7 = false := by
    change scanPairs (slowBinary 6 1 (search 6 1) raw7 (coverage true raw7)) [raw7[0]!, raw7[1]!, raw7[2]!, raw7[3]!, raw7[4]!] = false
    simp only [scanPairs, List.any_cons, List.any_nil, case7One01, case7One02, case7One03, case7One04, case7One12, case7One13, case7One14, case7One23, case7One24, case7One34, Bool.false_or]

  have un : unaryMoves 6 0 (search 6 0) raw7 = false := by
    change [raw7[0]!, raw7[1]!, raw7[2]!, raw7[3]!, raw7[4]!].any (unaryAt 6 0 (search 6 0) raw7 (coverage false raw7)) = false
    simp only [List.any_cons, List.any_nil, case7Unary0, case7Unary1, case7Unary2, case7Unary3, case7Unary4, Bool.false_or]

  change stepTest 6 1 raw7 (search 6 0) (search 6 1) = false
  unfold stepTest
  rw [bin, un]
  rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table7 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3938510976 x) :
    monotoneAnswer 3938510976 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3938510976 7 raw7 pick7 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut7One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.and, [7, 11]⟩], 12, by simp [mono], by decide, by decide +kernel⟩

def raw8 : List Sig := [(0xfffffffff00000ffffffffffffffffffff00000ffffffffff00000ffffffffff, 0x1252a1252a1252a1252a1252a1252a1252a1252a1252a1252a1252a1252a),
    (0xffffffffffffff00000fffff00000fffffffffffffffffffffffff00000fffff, 0x4464c4464c4464c4464c4464c4464c4464c4464c4464c4464c4464c4464c),
    (0xfffffffffffffffffff0000000000ffffffffff00000ffffffffffffffffffff, 0x988709887098870988709887098870988709887098870988709887098870),
    (0xfffffffffffffffffffffffff000000000000000fffffffffffffff00000, 0xe0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80e0f80),
    (0xffffffffffffffffffffffffffffffffffffffff00000000000000000000, 0xff000ff000ff000ff000ff000ff000ff000ff000ff000ff000ff000ff000)]

def pick8 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 10, 11, 20, 40, 60, 12, 13, 14, 80, 15, 16, 100, 120, 17, 140, 18, 160, 19, 180, 200, 220]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One01 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[0]! raw8[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One02 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[0]! raw8[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One03 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[0]! raw8[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One04 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[0]! raw8[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One12 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[1]! raw8[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One13 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[1]! raw8[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One14 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[1]! raw8[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One23 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[2]! raw8[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One24 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[2]! raw8[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8One34 :
    slowBinary 6 1 (search 6 1) raw8 (coverage true raw8) raw8[3]! raw8[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8Unary0 :
    unaryAt 6 0 (search 6 0) raw8 (coverage false raw8) raw8[0]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8Unary1 :
    unaryAt 6 0 (search 6 0) raw8 (coverage false raw8) raw8[1]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8Unary2 :
    unaryAt 6 0 (search 6 0) raw8 (coverage false raw8) raw8[2]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8Unary3 :
    unaryAt 6 0 (search 6 0) raw8 (coverage false raw8) raw8[3]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private lemma case8Unary4 :
    unaryAt 6 0 (search 6 0) raw8 (coverage false raw8) raw8[4]! = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in

lemma ruledOut8One : search 7 1 raw8 = false := by
  have bin : binaryMoves 6 1 (search 6 1) raw8 = false := by
    change scanPairs (slowBinary 6 1 (search 6 1) raw8 (coverage true raw8)) [raw8[0]!, raw8[1]!, raw8[2]!, raw8[3]!, raw8[4]!] = false
    simp only [scanPairs, List.any_cons, List.any_nil, case8One01, case8One02, case8One03, case8One04, case8One12, case8One13, case8One14, case8One23, case8One24, case8One34, Bool.false_or]

  have un : unaryMoves 6 0 (search 6 0) raw8 = false := by
    change [raw8[0]!, raw8[1]!, raw8[2]!, raw8[3]!, raw8[4]!].any (unaryAt 6 0 (search 6 0) raw8 (coverage false raw8)) = false
    simp only [List.any_cons, List.any_nil, case8Unary0, case8Unary1, case8Unary2, case8Unary3, case8Unary4, Bool.false_or]

  change stepTest 6 1 raw8 (search 6 0) (search 6 1) = false
  unfold stepTest
  rw [bin, un]
  rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table8 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 3939033216 x) :
    monotoneAnswer 3939033216 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 3939033216 7 raw8 pick8 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut8One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [5, 11]⟩], 12, by simp [mono], by decide, by decide +kernel⟩

def raw9 : List Sig := [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x842010840210804210084201084021080421008420108402108042100842),
    (0xfffffff00001ffffc00007ffff00001fffffffff80000fffffffffc00007ffff, 0x55294aa52954a52a94a55294aa52954a52a94a55294aa52954a52a94a55294),
    (0x7ffffffffe0000000007ffffffffe00003fffffffff00001fffffffff80000, 0x66318cc63198c63318c66318cc63198c63318c66318cc63198c63318c66318),
    (0x7ffffffffffffffffff800000000000003fffffffffffffe00000000000000, 0x783e0f07c1e0f83c1f0783e0f07c1e0f83c1f0783e0f07c1e0f83c1f0783e0),
    (0x7ffffffffffffffffffffffffffffffffc0000000000000000000000000000, 0x7fc00ff801ff003fe007fc00ff801ff003fe007fc00ff801ff003fe007fc00)]

def pick9 : List ℕ := [0, 1, 2, 0, 3, 19, 4, 38, 5, 6, 7, 57, 8, 76, 9, 95, 10, 11, 12, 114, 13, 133, 14, 152, 15, 171, 16, 190, 17, 209, 18, 228]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma ruledOut9One : search 3 1 raw9 = false := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma table9 (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ a b : Fin gs.length, (gs.get a).op = .not → (gs.get b).op = .not → a = b)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = evalT 2863179944 x) :
    monotoneAnswer 2863179944 gs.length := by
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply mixedTable 2863179944 3 raw9 pick9 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ruledOut9One _ ⟨gs,o⟩ legal hn he
  exact ⟨[⟨.and, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [0, 7]⟩], 8, by simp [mono], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_1423_aux

open PEqualNP.Outside.L_meta_1423_aux in
theorem PEqualNP.Outside.L_meta_1423 : ∀ T ∈ ({0xe8a8a888, 0xe8a8c888, 0xe8a8e880, 0xe8e8e800, 0xeaa8a880, 0xeaa8c880, 0xeaaac080, 0xeac0e880, 0xeac8e080, 0xaaa8a8a8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gs o legal single correct
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact table0 gs o legal single correct
  · exact table1 gs o legal single correct
  · exact table2 gs o legal single correct
  · exact table3 gs o legal single correct
  · exact table4 gs o legal single correct
  · exact table5 gs o legal single correct
  · exact table6 gs o legal single correct
  · exact table7 gs o legal single correct
  · exact table8 gs o legal single correct
  · exact table9 gs o legal single correct
