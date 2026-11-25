import PEqualNP.Defs
-- Live-wire search adapted from L-meta-1431 and L-meta-1007, Apache-2.0.
namespace PEqualNP.Outside.L_meta_15135_aux

abbrev B := BitVec 128
abbrev Sig := B × B
def top : B := BitVec.allOnes 128
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
  by_cases hi : i < 128
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 128 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 128
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 128 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 128)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 128) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 128 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 128)] <;> simp [hi]
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

def bit (side : Bool) (i : Fin 128) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 128).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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


def evalT (T : ℕ) (x : Fin 6 → Bool) := Nat.testBit T (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 128) (j : Fin 6) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 6 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 6 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 6 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
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

def table : ℕ := 3901268096 * 2 ^ 32 + 3901267968

def raw : List Sig := [
  (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db),
  (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78),
  (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d),
  (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036),
  (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80),
  (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)
]

lemma rawId : List.ofFn (fun j : Fin 6 => raw.getD j.val zero) = raw := rfl

lemma rawNodup : raw.Nodup := by decide

lemma rawEssential : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rows : ∀ b i, evalT table (sample raw b i) = b := by decide +kernel

def cases0u : List (List Sig) := []
lemma cases0uFalse (v : List Sig) (h : (!cases0u.contains v) = false) :
    Impossible 7 0 v := by
  have hm : v ∈ cases0u := by simpa using h
  simp [cases0u] at hm

def cases0b0 : List Sig := [(0xe3c07ff8eff27fc03fc0007fe3c07ff8, 0xa0c0125800000040c0c0c010a0c01258), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b0False : Impossible 7 0 cases0b0 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b1 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xefddfffb06136fdfdfdfddffefddfffb), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b1False : Impossible 7 0 cases0b1 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b2 : List Sig := [(0x7fc38e3f5f5dffc0003fc38c7fc38e3f, 0x5408609000001024242408405408609), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b2False : Impossible 7 0 cases0b2 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b3 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xffefbeff4a4537efefefefbdffefbeff), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b3False : Impossible 7 0 cases0b3 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b4 : List Sig := [(0x7c03f03f909de000003fc3f07c03f03f, 0x28013012000004488888813028013012), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b4False : Impossible 7 0 cases0b4 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b5 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xfdf7f6ff92995dfbfbfbf7f5fdf7f6ff), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b5False : Impossible 7 0 cases0b5 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b6 : List Sig := [(0x8003ffc0e0e260003fc003ff8003ffc0, 0x1a4800000050a0a0a01a50001a480), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b6False : Impossible 7 0 cases0b6 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b7 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xadfbffdbe2e11f7efefefbffadfbffdb), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b7False : Impossible 7 0 cases0b7 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b8 : List Sig := [(0xffc00000ff005fc0000003ffffc00000, 0xad8000000200054a8a8a81b5ad800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b8False : Impossible 7 0 cases0b8 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b9 : List Sig := [(0xffc00000ff005fc0000003ffffc00000, 0xad8000000200054a8a8a81b5ad800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b9False : Impossible 7 0 cases0b9 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b10 : List Sig := [(0xffc3ffffffffffc03fffffffffc3ffff, 0xffc1b6dbff015fffffffffffffc1b6db), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b10False : Impossible 7 0 cases0b10 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b11 : List Sig := [(0x63fc0e384f507fffc0003c0c63fc0e38, 0x424c0a280000228545454c08424c0a28), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b11False : Impossible 7 0 cases0b11 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b12 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xf7fedf7d4c567bf7f7f7fedef7fedf7d), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b12False : Impossible 7 0 cases0b12 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b13 : List Sig := [(0x603c70388090603fc0003c70603c7038, 0x60145030001048d19191945060145030), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b13False : Impossible 7 0 cases0b13 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b14 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xfaff7b7e949a7efdfdfdff7afaff7b7e), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b14False : Impossible 7 0 cases0b14 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b15 : List Sig := [(0x803c7fc0e0e2603fffc03c7f803c7fc0, 0x18490000000a141414184a00184900), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b15False : Impossible 7 0 cases0b15 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b16 : List Sig := [(0x803c7fc0e0e2603fffc03c7f803c7fc0, 0x18490000000a141414184a00184900), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b16False : Impossible 7 0 cases0b16 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b17 : List Sig := [(0xe3fffff8eff27fffffc03fffe3fffff8, 0xe2fffff8e4f27fffffffffffe2fffff8), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b17False : Impossible 7 0 cases0b17 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b18 : List Sig := [(0xe3c00000ef005fc000003c7fe3c00000, 0xe280000004004ad595959c5ae2800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b18False : Impossible 7 0 cases0b18 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b19 : List Sig := [(0xe3c00000ef005fc000003c7fe3c00000, 0xe280000004004ad595959c5ae2800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b19False : Impossible 7 0 cases0b19 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b20 : List Sig := [(0xfffc7ff8fff27fffffc03ffffffc7ff8, 0xffdc5b78ff127fffffffffffffdc5b78), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b20False : Impossible 7 0 cases0b20 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b21 : List Sig := [(0x7c3f803f101de03fc03fff807c3f803f, 0x50260024000010a12121260050260024), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b21False : Impossible 7 0 cases0b21 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b22 : List Sig := [(0x7c3f803f101de03fc03fff807c3f803f, 0x50260024000010a12121260050260024), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b22False : Impossible 7 0 cases0b22 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b23 : List Sig := [(0x7ffffe3fdfddffffc03ffffc7ffffe3f, 0x7f7ffe3fd8dc7ffffffffffc7f7ffe3f), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b23False : Impossible 7 0 cases0b23 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b24 : List Sig := [(0x3f8e004040603fc0003f8c003f8e00, 0x2a8c004040132626262a8c002a8c00), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b24False : Impossible 7 0 cases0b24 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b25 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0x577fefade8e43fbf7f7f7fef577fefad), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b25False : Impossible 7 0 cases0b25 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b26 : List Sig := [(0x7fc000005f005fc000003f8c7fc00000, 0x57000000480013a727272e8c57000000), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b26False : Impossible 7 0 cases0b26 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b27 : List Sig := [(0x7fc000005f005fc000003f8c7fc00000, 0x57000000480013a727272e8c57000000), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b27False : Impossible 7 0 cases0b27 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b28 : List Sig := [(0xffff8e3fff5dffffc03fffffffff8e3f, 0xffee8e2dff447fffffffffffffee8e2d), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b28False : Impossible 7 0 cases0b28 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b29 : List Sig := [(0x3ff0008080603fc0003ff0003ff000, 0x33600080801c383838336000336000), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b29False : Impossible 7 0 cases0b29 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b30 : List Sig := [(0xfc3ffffff0ffe03ffffffffffc3fffff, 0x783ffdb6f0f85fffbfbfbfff783ffdb6), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b30False : Impossible 7 0 cases0b30 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b31 : List Sig := [(0x7c0000009000400000003ff07c000000, 0x7800000090005cf9b9b9b77078000000), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b31False : Impossible 7 0 cases0b31 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b32 : List Sig := [(0xfffff03fff9dffffc03ffffffffff03f, 0xffb77036ff985fffbfbfbfffffb77036), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b32False : Impossible 7 0 cases0b32 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b33 : List Sig := [(0xfffff03fff9dffffc03ffffffffff03f, 0xffb77036ff985fffbfbfbfffffb77036), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b33False : Impossible 7 0 cases0b33 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b34 : List Sig := [(0x80000000e000400000003fff80000000, 0xe0001f3e3e3e3bef00000000), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b34False : Impossible 7 0 cases0b34 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b35 : List Sig := [(0xffffffc0ffe27fffffc03fffffffffc0, 0xffbbed80ffe05fffbfbfbfffffbbed80), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b35False : Impossible 7 0 cases0b35 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b36 : List Sig := [(0xffffffc0ffe27fffffc03fffffffffc0, 0xffbbed80ffe05fffbfbfbfffffbbed80), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases0b36False : Impossible 7 0 cases0b36 :=
  exclude_search (by decide) (by decide +kernel)

def cases0b : List (List Sig) := [cases0b0, cases0b1, cases0b2, cases0b3, cases0b4, cases0b5, cases0b6, cases0b7, cases0b8, cases0b9, cases0b10, cases0b11, cases0b12, cases0b13, cases0b14, cases0b15, cases0b16, cases0b17, cases0b18, cases0b19, cases0b20, cases0b21, cases0b22, cases0b23, cases0b24, cases0b25, cases0b26, cases0b27, cases0b28, cases0b29, cases0b30, cases0b31, cases0b32, cases0b33, cases0b34, cases0b35, cases0b36]
lemma cases0bFalse (v : List Sig) (h : (!cases0b.contains v) = false) :
    Impossible 7 0 v := by
  have hm : v ∈ cases0b := by simpa using h
  simp only [cases0b, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cases0b0False
  · exact cases0b1False
  · exact cases0b2False
  · exact cases0b3False
  · exact cases0b4False
  · exact cases0b5False
  · exact cases0b6False
  · exact cases0b7False
  · exact cases0b8False
  · exact cases0b9False
  · exact cases0b10False
  · exact cases0b11False
  · exact cases0b12False
  · exact cases0b13False
  · exact cases0b14False
  · exact cases0b15False
  · exact cases0b16False
  · exact cases0b17False
  · exact cases0b18False
  · exact cases0b19False
  · exact cases0b20False
  · exact cases0b21False
  · exact cases0b22False
  · exact cases0b23False
  · exact cases0b24False
  · exact cases0b25False
  · exact cases0b26False
  · exact cases0b27False
  · exact cases0b28False
  · exact cases0b29False
  · exact cases0b30False
  · exact cases0b31False
  · exact cases0b32False
  · exact cases0b33False
  · exact cases0b34False
  · exact cases0b35False
  · exact cases0b36False

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma no0 : Impossible 8 0 raw :=
  exclude_step (u := fun v => !cases0u.contains v) (b := fun v => !cases0b.contains v)
    rawNodup cases0uFalse cases0bFalse (by decide +kernel)

def cases1u0 : List Sig := [(0x3c00000000003fc0003c00003c0000, 0x523e4924fdfefab535353e4a523e4924), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1u0False : Impossible 7 0 cases1u0 :=
  exclude_search (by decide) (by decide +kernel)

def cases1u1 : List Sig := [(0x1c038007100d8000003fc3801c038007, 0x1d23a487fbed952a2a2a23a51d23a487), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1u1False : Impossible 7 0 cases1u1 :=
  exclude_search (by decide) (by decide +kernel)

def cases1u2 : List Sig := [(0x800071c0a0a200003fc00073800071c0, 0xa89171d2b7bbcc5898989173a89171d2), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1u2False : Impossible 7 0 cases1u2 :=
  exclude_search (by decide) (by decide +kernel)

def cases1u3 : List Sig := [(0x83c00fc06f621fc03fc0000f83c00fc0, 0x87c88fc96f67a3064646488f87c88fc9), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1u3False : Impossible 7 0 cases1u3 :=
  exclude_search (by decide) (by decide +kernel)

def cases1u4 : List Sig := [(0x7fc0003f1f1d9fc0003fc0007fc0003f, 0xffc4127f1f1fe0c1c1c1c410ffc4127f), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1u4False : Impossible 7 0 cases1u4 :=
  exclude_search (by decide) (by decide +kernel)

def cases1u5 : List Sig := [(0x3fffff00ffa03fffffc000003fffff, 0x7fffff00ffa00040404000007fffff), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1u5False : Impossible 7 0 cases1u5 :=
  exclude_search (by decide) (by decide +kernel)

def cases1u : List (List Sig) := [cases1u0, cases1u1, cases1u2, cases1u3, cases1u4, cases1u5]
lemma cases1uFalse (v : List Sig) (h : (!cases1u.contains v) = false) :
    Impossible 7 0 v := by
  have hm : v ∈ cases1u := by simpa using h
  simp only [cases1u, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cases1u0False
  · exact cases1u1False
  · exact cases1u2False
  · exact cases1u3False
  · exact cases1u4False
  · exact cases1u5False

def cases1b0 : List Sig := [(0xe3c07ff8eff27fc03fc0007fe3c07ff8, 0xa0c0125800000040c0c0c010a0c01258), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b0False : Impossible 7 1 cases1b0 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b1 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xefddfffb06136fdfdfdfddffefddfffb), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b1False : Impossible 7 1 cases1b1 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b2 : List Sig := [(0x7fc38e3f5f5dffc0003fc38c7fc38e3f, 0x5408609000001024242408405408609), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b2False : Impossible 7 1 cases1b2 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b3 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xffefbeff4a4537efefefefbdffefbeff), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b3False : Impossible 7 1 cases1b3 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b4 : List Sig := [(0x7c03f03f909de000003fc3f07c03f03f, 0x28013012000004488888813028013012), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b4False : Impossible 7 1 cases1b4 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b5 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xfdf7f6ff92995dfbfbfbf7f5fdf7f6ff), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b5False : Impossible 7 1 cases1b5 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b6 : List Sig := [(0x8003ffc0e0e260003fc003ff8003ffc0, 0x1a4800000050a0a0a01a50001a480), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b6False : Impossible 7 1 cases1b6 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b7 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xadfbffdbe2e11f7efefefbffadfbffdb), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b7False : Impossible 7 1 cases1b7 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b8 : List Sig := [(0xffc00000ff005fc0000003ffffc00000, 0xad8000000200054a8a8a81b5ad800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b8False : Impossible 7 1 cases1b8 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b9 : List Sig := [(0xffc00000ff005fc0000003ffffc00000, 0xad8000000200054a8a8a81b5ad800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b9False : Impossible 7 1 cases1b9 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b10 : List Sig := [(0xffc3ffffffffffc03fffffffffc3ffff, 0xffc1b6dbff015fffffffffffffc1b6db), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b10False : Impossible 7 1 cases1b10 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b11 : List Sig := [(0x63fc0e384f507fffc0003c0c63fc0e38, 0x424c0a280000228545454c08424c0a28), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b11False : Impossible 7 1 cases1b11 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b12 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xf7fedf7d4c567bf7f7f7fedef7fedf7d), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b12False : Impossible 7 1 cases1b12 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b13 : List Sig := [(0x603c70388090603fc0003c70603c7038, 0x60145030001048d19191945060145030), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b13False : Impossible 7 1 cases1b13 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b14 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0xfaff7b7e949a7efdfdfdff7afaff7b7e), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b14False : Impossible 7 1 cases1b14 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b15 : List Sig := [(0x803c7fc0e0e2603fffc03c7f803c7fc0, 0x18490000000a141414184a00184900), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b15False : Impossible 7 1 cases1b15 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b16 : List Sig := [(0x803c7fc0e0e2603fffc03c7f803c7fc0, 0x18490000000a141414184a00184900), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b16False : Impossible 7 1 cases1b16 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b17 : List Sig := [(0xe3fffff8eff27fffffc03fffe3fffff8, 0xe2fffff8e4f27fffffffffffe2fffff8), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b17False : Impossible 7 1 cases1b17 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b18 : List Sig := [(0xe3c00000ef005fc000003c7fe3c00000, 0xe280000004004ad595959c5ae2800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b18False : Impossible 7 1 cases1b18 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b19 : List Sig := [(0xe3c00000ef005fc000003c7fe3c00000, 0xe280000004004ad595959c5ae2800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b19False : Impossible 7 1 cases1b19 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b20 : List Sig := [(0xfffc7ff8fff27fffffc03ffffffc7ff8, 0xffdc5b78ff127fffffffffffffdc5b78), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b20False : Impossible 7 1 cases1b20 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b21 : List Sig := [(0x7c3f803f101de03fc03fff807c3f803f, 0x50260024000010a12121260050260024), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b21False : Impossible 7 1 cases1b21 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b22 : List Sig := [(0x7c3f803f101de03fc03fff807c3f803f, 0x50260024000010a12121260050260024), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b22False : Impossible 7 1 cases1b22 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b23 : List Sig := [(0x7ffffe3fdfddffffc03ffffc7ffffe3f, 0x7f7ffe3fd8dc7ffffffffffc7f7ffe3f), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b23False : Impossible 7 1 cases1b23 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b24 : List Sig := [(0x3f8e004040603fc0003f8c003f8e00, 0x2a8c004040132626262a8c002a8c00), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b24False : Impossible 7 1 cases1b24 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b25 : List Sig := [(0xffffffffffffffffffffffffffffffff, 0x577fefade8e43fbf7f7f7fef577fefad), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b25False : Impossible 7 1 cases1b25 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b26 : List Sig := [(0x7fc000005f005fc000003f8c7fc00000, 0x57000000480013a727272e8c57000000), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b26False : Impossible 7 1 cases1b26 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b27 : List Sig := [(0x7fc000005f005fc000003f8c7fc00000, 0x57000000480013a727272e8c57000000), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b27False : Impossible 7 1 cases1b27 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b28 : List Sig := [(0xffff8e3fff5dffffc03fffffffff8e3f, 0xffee8e2dff447fffffffffffffee8e2d), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b28False : Impossible 7 1 cases1b28 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b29 : List Sig := [(0x3ff0008080603fc0003ff0003ff000, 0x33600080801c383838336000336000), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b29False : Impossible 7 1 cases1b29 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b30 : List Sig := [(0xfc3ffffff0ffe03ffffffffffc3fffff, 0x783ffdb6f0f85fffbfbfbfff783ffdb6), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b30False : Impossible 7 1 cases1b30 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b31 : List Sig := [(0x7c0000009000400000003ff07c000000, 0x7800000090005cf9b9b9b77078000000), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b31False : Impossible 7 1 cases1b31 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b32 : List Sig := [(0xfffff03fff9dffffc03ffffffffff03f, 0xffb77036ff985fffbfbfbfffffb77036), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b32False : Impossible 7 1 cases1b32 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b33 : List Sig := [(0xfffff03fff9dffffc03ffffffffff03f, 0xffb77036ff985fffbfbfbfffffb77036), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b33False : Impossible 7 1 cases1b33 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b34 : List Sig := [(0x80000000e000400000003fff80000000, 0xe0001f3e3e3e3bef00000000), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b34False : Impossible 7 1 cases1b34 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b35 : List Sig := [(0xffffffc0ffe27fffffc03fffffffffc0, 0xffbbed80ffe05fffbfbfbfffffbbed80), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b35False : Impossible 7 1 cases1b35 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b36 : List Sig := [(0xffffffc0ffe27fffffc03fffffffffc0, 0xffbbed80ffe05fffbfbfbfffffbbed80), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases1b36False : Impossible 7 1 cases1b36 :=
  exclude_search (by decide) (by decide +kernel)

def cases1b : List (List Sig) := [cases1b0, cases1b1, cases1b2, cases1b3, cases1b4, cases1b5, cases1b6, cases1b7, cases1b8, cases1b9, cases1b10, cases1b11, cases1b12, cases1b13, cases1b14, cases1b15, cases1b16, cases1b17, cases1b18, cases1b19, cases1b20, cases1b21, cases1b22, cases1b23, cases1b24, cases1b25, cases1b26, cases1b27, cases1b28, cases1b29, cases1b30, cases1b31, cases1b32, cases1b33, cases1b34, cases1b35, cases1b36]
lemma cases1bFalse (v : List Sig) (h : (!cases1b.contains v) = false) :
    Impossible 7 1 v := by
  have hm : v ∈ cases1b := by simpa using h
  simp only [cases1b, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cases1b0False
  · exact cases1b1False
  · exact cases1b2False
  · exact cases1b3False
  · exact cases1b4False
  · exact cases1b5False
  · exact cases1b6False
  · exact cases1b7False
  · exact cases1b8False
  · exact cases1b9False
  · exact cases1b10False
  · exact cases1b11False
  · exact cases1b12False
  · exact cases1b13False
  · exact cases1b14False
  · exact cases1b15False
  · exact cases1b16False
  · exact cases1b17False
  · exact cases1b18False
  · exact cases1b19False
  · exact cases1b20False
  · exact cases1b21False
  · exact cases1b22False
  · exact cases1b23False
  · exact cases1b24False
  · exact cases1b25False
  · exact cases1b26False
  · exact cases1b27False
  · exact cases1b28False
  · exact cases1b29False
  · exact cases1b30False
  · exact cases1b31False
  · exact cases1b32False
  · exact cases1b33False
  · exact cases1b34False
  · exact cases1b35False
  · exact cases1b36False

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma no1 : Impossible 8 1 raw :=
  exclude_step (u := fun v => !cases1u.contains v) (b := fun v => !cases1b.contains v)
    rawNodup cases1uFalse cases1bFalse (by decide +kernel)

def cases2u0 : List Sig := [(0x3c00000000003fc0003c00003c0000, 0x523e4924fdfefab535353e4a523e4924), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u0False : Impossible 7 1 cases2u0 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u1 : List Sig := [(0x3c00000000003fc0003c00003c0000, 0x523e4924fdfefab535353e4a523e4924), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u1False : Impossible 7 1 cases2u1 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u2 : List Sig := [(0x1c038007100d8000003fc3801c038007, 0x1d23a487fbed952a2a2a23a51d23a487), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u2False : Impossible 7 1 cases2u2 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u3 : List Sig := [(0x1c038007100d8000003fc3801c038007, 0x1d23a487fbed952a2a2a23a51d23a487), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u3False : Impossible 7 1 cases2u3 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u4 : List Sig := [(0x800071c0a0a200003fc00073800071c0, 0xa89171d2b7bbcc5898989173a89171d2), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u4False : Impossible 7 1 cases2u4 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u5 : List Sig := [(0x800071c0a0a200003fc00073800071c0, 0xa89171d2b7bbcc5898989173a89171d2), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u5False : Impossible 7 1 cases2u5 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u6 : List Sig := [(0x83c00fc06f621fc03fc0000f83c00fc0, 0x87c88fc96f67a3064646488f87c88fc9), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u6False : Impossible 7 1 cases2u6 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u7 : List Sig := [(0x83c00fc06f621fc03fc0000f83c00fc0, 0x87c88fc96f67a3064646488f87c88fc9), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u7False : Impossible 7 1 cases2u7 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u8 : List Sig := [(0x7fc0003f1f1d9fc0003fc0007fc0003f, 0xffc4127f1f1fe0c1c1c1c410ffc4127f), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u8False : Impossible 7 1 cases2u8 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u9 : List Sig := [(0x7fc0003f1f1d9fc0003fc0007fc0003f, 0xffc4127f1f1fe0c1c1c1c410ffc4127f), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u9False : Impossible 7 1 cases2u9 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u10 : List Sig := [(0x3fffff00ffa03fffffc000003fffff, 0x7fffff00ffa00040404000007fffff), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u10False : Impossible 7 1 cases2u10 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u11 : List Sig := [(0x3fffff00ffa03fffffc000003fffff, 0x7fffff00ffa00040404000007fffff), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2u11False : Impossible 7 1 cases2u11 :=
  exclude_search (by decide) (by decide +kernel)

def cases2u : List (List Sig) := [cases2u0, cases2u1, cases2u2, cases2u3, cases2u4, cases2u5, cases2u6, cases2u7, cases2u8, cases2u9, cases2u10, cases2u11]
lemma cases2uFalse (v : List Sig) (h : (!cases2u.contains v) = false) :
    Impossible 7 1 v := by
  have hm : v ∈ cases2u := by simpa using h
  simp only [cases2u, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cases2u0False
  · exact cases2u1False
  · exact cases2u2False
  · exact cases2u3False
  · exact cases2u4False
  · exact cases2u5False
  · exact cases2u6False
  · exact cases2u7False
  · exact cases2u8False
  · exact cases2u9False
  · exact cases2u10False
  · exact cases2u11False

def cases2b0 : List Sig := [(0xffc00000ff005fc0000003ffffc00000, 0xad8000000200054a8a8a81b5ad800000), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2b0False : Impossible 7 2 cases2b0 :=
  exclude_search (by decide) (by decide +kernel)

def cases2b1 : List Sig := [(0x803c7fc0e0e2603fffc03c7f803c7fc0, 0x18490000000a141414184a00184900), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2b1False : Impossible 7 2 cases2b1 :=
  exclude_search (by decide) (by decide +kernel)

def cases2b2 : List Sig := [(0xe3c00000ef005fc000003c7fe3c00000, 0xe280000004004ad595959c5ae2800000), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2b2False : Impossible 7 2 cases2b2 :=
  exclude_search (by decide) (by decide +kernel)

def cases2b3 : List Sig := [(0x7c3f803f101de03fc03fff807c3f803f, 0x50260024000010a12121260050260024), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2b3False : Impossible 7 2 cases2b3 :=
  exclude_search (by decide) (by decide +kernel)

def cases2b4 : List Sig := [(0x7fc000005f005fc000003f8c7fc00000, 0x57000000480013a727272e8c57000000), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2b4False : Impossible 7 2 cases2b4 :=
  exclude_search (by decide) (by decide +kernel)

def cases2b5 : List Sig := [(0xfffff03fff9dffffc03ffffffffff03f, 0xffb77036ff985fffbfbfbfffffb77036), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2b5False : Impossible 7 2 cases2b5 :=
  exclude_search (by decide) (by decide +kernel)

def cases2b6 : List Sig := [(0xffffffc0ffe27fffffc03fffffffffc0, 0xffbbed80ffe05fffbfbfbfffffbbed80), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases2b6False : Impossible 7 2 cases2b6 :=
  exclude_search (by decide) (by decide +kernel)

def cases2b : List (List Sig) := [cases2b0, cases2b1, cases2b2, cases2b3, cases2b4, cases2b5, cases2b6]
lemma cases2bFalse (v : List Sig) (h : (!cases2b.contains v) = false) :
    Impossible 7 2 v := by
  have hm : v ∈ cases2b := by simpa using h
  simp only [cases2b, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cases2b0False
  · exact cases2b1False
  · exact cases2b2False
  · exact cases2b3False
  · exact cases2b4False
  · exact cases2b5False
  · exact cases2b6False

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma no2 : Impossible 8 2 raw :=
  exclude_step (u := fun v => !cases2u.contains v) (b := fun v => !cases2b.contains v)
    rawNodup cases2uFalse cases2bFalse (by decide +kernel)

def cases3u0 : List Sig := [(0x3c00000000003fc0003c00003c0000, 0x523e4924fdfefab535353e4a523e4924), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases3u0False : Impossible 7 2 cases3u0 :=
  exclude_search (by decide) (by decide +kernel)

def cases3u1 : List Sig := [(0x1c038007100d8000003fc3801c038007, 0x1d23a487fbed952a2a2a23a51d23a487), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases3u1False : Impossible 7 2 cases3u1 :=
  exclude_search (by decide) (by decide +kernel)

def cases3u2 : List Sig := [(0x800071c0a0a200003fc00073800071c0, 0xa89171d2b7bbcc5898989173a89171d2), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases3u2False : Impossible 7 2 cases3u2 :=
  exclude_search (by decide) (by decide +kernel)

def cases3u3 : List Sig := [(0x83c00fc06f621fc03fc0000f83c00fc0, 0x87c88fc96f67a3064646488f87c88fc9), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases3u3False : Impossible 7 2 cases3u3 :=
  exclude_search (by decide) (by decide +kernel)

def cases3u4 : List Sig := [(0x7fc0003f1f1d9fc0003fc0007fc0003f, 0xffc4127f1f1fe0c1c1c1c410ffc4127f), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0xffc00000ff005fc000003fffffc00000, 0xff800000ff005fffbfbfbfffff800000)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases3u4False : Impossible 7 2 cases3u4 :=
  exclude_search (by decide) (by decide +kernel)

def cases3u5 : List Sig := [(0x3fffff00ffa03fffffc000003fffff, 0x7fffff00ffa00040404000007fffff), (0xffc3ffffffffffc03fffc3ffffc3ffff, 0xadc1b6db0201054acacac1b5adc1b6db), (0xe3fc7ff8eff27fffffc03c7fe3fc7ff8, 0xe2dc5b7804126ad5d5d5dc5ae2dc5b78), (0x7fff8e3f5f5dffffc03fff8c7fff8e3f, 0x576e8e2d484433a767676e8c576e8e2d), (0x7c3ff03f909de03fc03ffff07c3ff03f, 0x7837703690985cf9b9b9b77078377036), (0x803fffc0e0e2603fffc03fff803fffc0, 0x3bed80e0e01f3e3e3e3bef003bed80)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma cases3u5False : Impossible 7 2 cases3u5 :=
  exclude_search (by decide) (by decide +kernel)

def cases3u : List (List Sig) := [cases3u0, cases3u1, cases3u2, cases3u3, cases3u4, cases3u5]
lemma cases3uFalse (v : List Sig) (h : (!cases3u.contains v) = false) :
    Impossible 7 2 v := by
  have hm : v ∈ cases3u := by simpa using h
  simp only [cases3u, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cases3u0False
  · exact cases3u1False
  · exact cases3u2False
  · exact cases3u3False
  · exact cases3u4False
  · exact cases3u5False

def cases3b : List (List Sig) := []
lemma cases3bFalse (v : List Sig) (h : (!cases3b.contains v) = false) :
    Impossible 7 3 v := by
  have hm : v ∈ cases3b := by simpa using h
  simp [cases3b] at hm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma no3 : Impossible 8 3 raw :=
  exclude_step (u := fun v => !cases3u.contains v) (b := fun v => !cases3b.contains v)
    rawNodup cases3uFalse cases3bFalse (by decide +kernel)

lemma lower (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 (evalT table) s) : 9 ≤ s := by
  obtain ⟨C, legal, sz, computes⟩ := h
  by_contra! small
  obtain ⟨k,t,S,hk,_,live,sub⟩ := extract C.gates raw legal
    (circuit_target table raw rawId rows C legal computes)
  have heq := necessary raw rawEssential live sub
  rw [← heq] at live
  have hc := (live_size live).2
  rw [List.toFinset_card_of_nodup rawNodup] at hc
  change 6 + t ≤ k + 1 at hc
  have hk' : k ≤ 8 := by
    change C.gates.length ≤ s at sz
    omega
  have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases ht with rfl | rfl | rfl | rfl
  · exact no0 k hk' live
  · exact no1 k hk' live
  · exact no2 k hk' live
  · exact no3 k hk' live

def upperCircuit : Circuit := ⟨[
  ⟨.and, [1, 4]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [0, 7]⟩,
  ⟨.and, [1, 5]⟩,
  ⟨.or, [7, 9]⟩,
  ⟨.and, [2, 10]⟩,
  ⟨.and, [0, 11]⟩,
  ⟨.and, [6, 8]⟩,
  ⟨.or, [12, 13]⟩
], 14⟩

set_option maxHeartbeats 1500000 in
lemma upper (s : ℕ) (hs : 9 ≤ s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = evalT table x := by
  refine ⟨upperCircuit, ?_, hs, ?_⟩
  · simp [upperCircuit, PEqualNP.MetaComplexity.Monotone2]
  · decide

end PEqualNP.Outside.L_meta_15135_aux

theorem PEqualNP.Outside.L_meta_15135 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3901268096 * 2 ^ 32 + 3901267968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3901268096 * 2 ^ 32 + 3901267968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  exact PEqualNP.Outside.L_meta_15135_aux.upper s (PEqualNP.Outside.L_meta_15135_aux.lower s h)
