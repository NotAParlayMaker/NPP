import PEqualNP.Defs
-- The finite search certificate is adapted from the L-meta-1667 proof by
-- loris-olsem in PR 4332 at commit 4449a8b54b349ff4bfa2223161749cbd6b16a3a9.
-- Its namespace is changed here. The final deduction prepends two AND gates.
namespace PEqualNP.Outside.L_meta_1791

abbrev B := BitVec 689
abbrev Sig := B × B
def top : B := BitVec.allOnes 689
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



def raw0 : Sig := (0x155555555555d55aaaeaab5f5d55b56daabd56aaf5dbed55b55aabaaabd6ebf6f7dbaff7c210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f000000000000000000fff000fff000000fff,0x7e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07544544544544544544544544544544544544)
def raw1 : Sig := (0x199999999999679cccb333959e66d9b6ccd67f33597d7e66d9ef3dfccd67737b7beff5bbfe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279000000000000000fff000000000000ffffff,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038823823823823823823823823823823823823)
def raw2 : Sig := (0x1e1e1e1e1e1e79ef0f3c3de7ef871e38f0e79bc39e6e77871e73ceff0e7bbdfc5d72f9fd8421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0000000000000fff000000000000ffffff000,0x1f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0314314314314314314314314314314314314)
def raw3 : Sig := (0x1fe01fe01fe07e0ff03fc1f9f7f81fc0ff07e3fc1f8fbff81f83f0cff07c3e5f9e7cfede884208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480000000fff000000000000fff000fff000000,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000069069069069069069069069069069069069)
def raw4 : Sig := (0x1fffe0001fff800fffc001fe07ffe000fff803ffe00fc7ffe003ff0fff803f9fe07f3f1f3ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802000000000000000000000ffffff000000000,0x3ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000a92a92a92a92a92a92a92a92a92a92a92a92)
def raw5 : Sig := (0x1fffffffe000000ffffffe0007ffffff000003fffff007fffffc000fffffc01fff803fe010842084210822109042108882108917fffffc00802010fffffffffe000101004000fff000fff000000fff000000000000000,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000007fffffc00000000fffffffffe00000000001b01b01b01b01b01b01b01b01b01b01b01b)
def raw6 : Sig := (0x1ffffffffffffff00000000007fffffffffffc00000007fffffffff00000001fffffc00021084108421044213ffffff004001007ffffffffffffff0100400040102000020fff000000000000fff000000000000000000,0x3fffffe000000007ffffffffffffff00000000000000000000dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc)
def raw7 : Sig := (0x1ffffffffffffffffffffffff800000000000000000007ffffffffffffffffe0000000003ffffff0002080003ffffffffffffffa108211000041004208821085000002100000000000ffffff000000000000000000000,0x3fffffe0000000003ffffffffffffff8000000000000000000000000000000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0)
def raw8 : Sig := (0x1ffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000fffffffff000000000000000000000000000,0x3fffffffffffffffc000000000000000000000000000000000000000000000000f00f00f00f00f00f00f00f00f00f00f00f00)
def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

set_option maxRecDepth 4000 in
private lemma target_proper : proper target := by unfold proper target zero one top; decide
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
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
  by_cases hi : i < 689
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 689 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 689
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 689 ≤ i)] at h

lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 689)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 689) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 689 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 689)] <;> simp [hi]
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
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
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

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
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
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
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
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
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
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 689) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 689).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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

def sample (s : Bool) (i : Fin 689) (j : Fin 9) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
private lemma sample_ok : ∀ (s : Bool) (i : Fin 689), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
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


def firstSignal : Sig := bin false raw0 raw1

private lemma execute_prefix (gs : List Gate) (w : List Sig) (i : Nat) (hi : i < w.length) :
    (execute gs w).getD i zero = w.getD i zero := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).getD i zero = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma first_value (g : Gate) (gs : List Gate) (o : Nat)
    (hf : PEqualNP.MetaComplexity.FanInTwo ⟨g::gs,o⟩)
    (h : ∀ y : Fin 9 → Bool, ((⟨g::gs,o⟩ : Circuit).wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) :
    gv raw g = firstSignal := by
  let C : Circuit := ⟨g::gs,o⟩
  have firstRead : (execute (g::gs) raw).getD 9 zero = gv raw g := by
    change (execute gs (raw ++ [gv raw g])).getD 9 zero = _
    rw [execute_prefix gs _ _ (by simp [raw])]
    rfl
  have hb (s i) : bit s i (gv raw g) = bit s i firstSignal := by
    rw [← firstRead, ← b_read, execute_bits _ _ _ _ (fun j hj => (hf j hj).1)]
    have hp := h (sample s i)
    rw [sample_list] at hp
    rw [show bit s i firstSignal = (bit s i raw0 && bit s i raw1) by exact bit_bin s i false raw0 raw1]; exact hp
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    exact fun i hi => hb true ⟨i,hi⟩
  · apply BitVec.eq_of_getLsbD_eq
    exact fun i hi => hb false ⟨i,hi⟩

def starting : List Sig := raw ++ [firstSignal]

private lemma essential : raw.all (fun a => unionSep true (starting.erase a) != top) = true := by
  decide +kernel

private lemma required_inputs {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ starting) :
    raw.toFinset ⊆ S := by
  intro a ha
  by_contra hn
  have fail := List.all_eq_true.mp essential a (List.mem_toFinset.mp ha)
  have cov : unionSep true (starting.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

theorem suffix_bound (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hh : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) (hsize : C.size ≤ 15) :
    ∃ k t S, k ≤ 14 ∧ Live k t S ∧ (S = raw.toFinset ∨ S = starting.toFinset) := by
  obtain ⟨gs,o⟩ := C
  cases gs with
  | nil =>
    have bad := hh (fun _ => true)
    contradiction
  | cons g gs =>
    have ht := circuit_target ⟨g::gs,o⟩ hf he
    change target ∈ execute gs (raw ++ [gv raw g]) at ht
    rw [first_value g gs o hf hh] at ht
    obtain ⟨k,t,S,hk,hL,hS⟩ := extract gs starting (fun a ha => hf a (List.mem_cons_of_mem g ha)) ht
    have hraw := required_inputs hL hS
    change gs.length + 1 ≤ 15 at hsize
    refine ⟨k,t,S,by omega,hL,?_⟩
    by_cases hfresh : firstSignal ∈ S
    · right
      ext a
      simp only [starting,List.mem_toFinset,List.mem_append,List.mem_singleton]
      constructor
      · exact fun ha => by simpa [starting] using hS a ha
      · rintro (ha | rfl)
        · exact hraw (List.mem_toFinset.mpr ha)
        · exact hfresh
    · left
      refine Finset.Subset.antisymm ?_ hraw
      intro a ha
      have hm := hS a ha
      simp only [starting,List.mem_append,List.mem_singleton] at hm
      exact List.mem_toFinset.mpr (hm.resolve_right (fun heq => hfresh (heq ▸ ha)))

structure Projection where
  project : Sig → Sig
  project_neg : ∀ a, project (neg a) = neg (project a)
  project_bin : ∀ d a b, project (bin d a b) = bin d (project a) (project b)
  project_target : project target = target

open Projection

def Feasible (i : Projection) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image (project i)
lemma feasible_mono {i : Projection} {k k' : Nat} {S : Finset Sig}
    (h : Feasible i k S) (hk : k ≤ k') : Feasible i k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h
  exact ⟨m, hm.trans hk, t, T, hl, hs⟩

lemma neg_rep (w : List Sig) (a : Sig) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases (Or.inl ha : represented w a) with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

lemma feasible_pull {i : Projection} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image (project i)).toList (project i g) ∨
      witness (S.image (project i)).toList (project i g))
    (h : Feasible i q S') : Feasible i (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image (project i)).toList ++ [project i g] := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩

lemma feasible_free {i : Projection} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image (project i)).toList (project i g))
    (h : Feasible i q S') : Feasible i q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb

lemma pull_unary {i : Projection} {q : Nat} {a : Sig} {U : Finset Sig}
    (h : Feasible i q (insert (neg a) U)) :
    Feasible i (q+1) (insert a U) := by
  apply feasible_pull (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [i.project_neg]
  exact neg_rep _ _ (by simp)

lemma pull_binary {i : Projection} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i (q+1) (insert a (insert b U)) := by
  apply feasible_pull (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [i.project_bin]
  exact bin_rep _ (Or.inl (by simp)) (Or.inl (by simp))

lemma free_unary {i : Projection} {q : Nat} {a : Sig} {U : Finset Sig}
    (ha : ¬ proper (project i a))
    (h : Feasible i q (insert (neg a) U)) :
    Feasible i q (insert a U) := by
  apply feasible_free (g := neg a) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rcases operand_cases (Or.inr ha : represented [] (project i a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2 (by rw [i.project_neg,hz,neg_laws.1]))
  · exact Or.inr (fun hp => hp.1 (by rw [i.project_neg,ho,neg_laws.2]))
  · simp at hm

lemma free_binary_left {i : Projection} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : ¬ proper (project i a))
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h => by simp [h]) _ h
  rw [i.project_bin, bin_comm]
  rcases operand_cases (Or.inr ha : represented [] (project i a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp => hp.1 (bin_laws _).2.2.1)
    · rw [(bin_laws _).2.1]
      exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(bin_laws _).1]
      exact Or.inl (by simp)
    · exact Or.inr (fun hp => hp.2 (bin_laws _).2.2.2.1)
  · simp at hm

lemma free_binary_right {i : Projection} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : ¬ proper (project i b))
    (h : Feasible i q (insert (bin d a b) U)) :
    Feasible i q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h


def constants (i : Projection) (S : Finset Sig) : Nat :=
  (S.filter fun a => i.project a = zero ∨ i.project a = one).card

lemma constants_insert (i : Projection) (a : Sig) (S : Finset Sig) :
    constants i (insert a S) = constants i S +
      (if a ∉ S ∧ (i.project a = zero ∨ i.project a = one) then 1 else 0) := by
  by_cases h : a ∈ S
  · simp [Finset.insert_eq_of_mem h,h]
  · by_cases p : i.project a = zero ∨ i.project a = one
    · simp [constants,Finset.filter_insert,h,p]
    · simp [constants,Finset.filter_insert,h,p]

lemma constant_bin {i : Projection} {a b : Sig} (d : Bool)
    (ha : i.project a = zero ∨ i.project a = one)
    (hb : i.project b = zero ∨ i.project b = one) :
    i.project (bin d a b) = zero ∨ i.project (bin d a b) = one := by
  rw [i.project_bin]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha,hb] <;>
    cases d <;> decide +kernel

theorem project_live_cost {k t : Nat} {S : Finset Sig} (h : Live k t S) (i : Projection) :
    ∃ q, q + constants i S ≤ k ∧ Feasible i q S := by
  induction h with
  | stop =>
    refine ⟨0,?_,0,by omega,0,{target},Live.stop,?_⟩
    · have hz := target_proper
      simp [constants,i.project_target,hz.1,hz.2]
    · simp [i.project_target]
  | @unary k t U a _ fresh tail ih =>
    obtain ⟨q,hq,hh⟩ := ih
    rw [constants_insert] at hq ⊢
    by_cases hc : i.project a = zero ∨ i.project a = one
    · refine ⟨q,?_,free_unary (fun h => hc.elim h.1 h.2) hh⟩
      split at hq <;> split <;> omega
    · refine ⟨q+1,?_,pull_unary hh⟩
      simp only [hc,and_false,if_false,Nat.add_zero]
      split at hq <;> omega
  | @binary k t U a b d _ _ _ fresh tail ih =>
    obtain ⟨q,hq,hh⟩ := ih
    have hnew : bin d a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [constants_insert] at hq
    simp only [hnew,not_false_eq_true,true_and] at hq
    simp only [constants_insert]
    by_cases ha : i.project a = zero ∨ i.project a = one
    · refine ⟨q,?_,free_binary_left (fun h => ha.elim h.1 h.2) hh⟩
      by_cases hb : i.project b = zero ∨ i.project b = one
      · rw [if_pos (constant_bin d ha hb)] at hq
        split <;> split <;> omega
      · simp only [hb,and_false,if_false,Nat.add_zero]
        split at hq <;> split <;> omega
    · simp only [ha,and_false,if_false,Nat.add_zero]
      by_cases hb : i.project b = zero ∨ i.project b = one
      · refine ⟨q,?_,free_binary_right (fun h => hb.elim h.1 h.2) hh⟩
        split at hq <;> split <;> omega
      · refine ⟨q+1,?_,pull_binary hh⟩
        simp only [hb,and_false,if_false,Nat.add_zero]
        split at hq <;> omega

def canBuild (S : Finset Sig) (a : Sig) : Prop :=
  represented S.toList a ∨ witness S.toList a

inductive Built (base : Finset Sig) : Nat → Finset Sig → Prop
  | start : Built base 0 base
  | gate {p S z} (earlier : Built base p S) (ok : canBuild S z) :
      Built base (p+1) (insert z S)

def possible (base : Finset Sig) (budget : Nat) : Prop :=
  ∃ k t T, k ≤ budget ∧ Live k t T ∧ T ⊆ base

theorem prepend_gate {q S z} (hz : canBuild S z) (h : possible (insert z S) q) :
    possible S (q+1) := by
  obtain ⟨k,t,T,hk,hl,hT⟩ := h
  have sub : ∀ a ∈ T, a ∈ S.toList ++ [z] := by
    intro a ha
    rcases Finset.mem_insert.mp (hT ha) with rfl | hm
    · simp
    · simp [hm]
  obtain ⟨j,u,V,hj,hV,hin⟩ := pull_gate hl hz sub
  exact ⟨j,u,V,by omega,hV,fun a ha => Finset.mem_toList.mp (hin a ha)⟩

theorem prepend_built {base p S q} (built : Built base p S) (h : possible S q) :
    possible base (p+q) := by
  induction built generalizing q with
  | start => simpa using h
  | gate prev ok ih =>
    have hh := ih (prepend_gate ok h)
    convert hh using 1 <;> omega

theorem projected_contradiction {k t : Nat} {S base W : Finset Sig} {p B : Nat}
    (i : Projection) (built : Built base p W)
    (available : ∀ a ∈ S.image i.project, proper a → a ∈ W)
    (bound : ¬ possible base B)
    (short : p+k < B+1+constants i S) : ¬ Live k t S := by
  intro hl
  obtain ⟨q,hq,j,hj,u,T,hT,hs⟩ := project_live_cost hl i
  have hW : possible W q :=
    ⟨j,u,T,hj,hT,fun a ha => available a (hs ha) (live_proper hT a ha)⟩
  obtain ⟨v,vn,U,hv,hU,sub⟩ := prepend_built built hW
  exact bound ⟨v,vn,U,by omega,hU,sub⟩
namespace Theta

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def xs517 : List ℕ := [0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517, 0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827, 0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248, 0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0, 0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418, 0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800, 0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688]

theorem proper_fail517 : ∀ zs ∈ xs517.sublists, zs ≠ xs517 →
    (cov 232 zs &&& lo 232) ≠ lo 232 := by decide +kernel

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag)

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag <<< d).testBit i then w.testBit (i-d) else false) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_run {k s ws} (h : NatRun (mask k) (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact Run.map _ (fun a => (move_hom tag d hz a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (move_hom tag d hz a b).1) (fun a b => (move_hom tag d hz a b).2.1) h

def deltaA : Nat := (lo 58) ||| ((lo 58) <<< 116) ||| ((lo 58) <<< 232) ||| ((lo 58) <<< 348)
def deltaB : Nat := lo 116 ||| ((lo 116) <<< 232)

def setA (xs : List Nat) := xs.map (moveBits deltaA 58)
def setB (xs : List Nat) := xs.map (moveBits deltaB 116)

theorem runA {s ws} (h : NatRun (mask 232) (goal 232) s ws) :
    NatRun (mask 232) (goal 232) s (setA ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem runB {s ws} (h : NatRun (mask 232) (goal 232) s ws) :
    NatRun (mask 232) (goal 232) s (setB ws) :=
  move_run h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def recipeStep (ma : Nat) (lit : Nat → Nat) (op : Nat) (stack : List Nat) : List Nat :=
  if op < 8 then lit op :: stack
  else match stack with
  | [] => []
  | a :: t => if op = 8 then (a ^^^ ma) :: t else match t with
    | [] => []
    | b :: r => (if op = 9 then a &&& b else a ||| b) :: r

def recipeVal (ma : Nat) (lit : Nat → Nat) : Nat → Nat → List Nat → Nat
  | 0, _, stack => stack.headD 0
  | t+1, ops, stack =>
    if ops = 0 then stack.headD 0 else
      recipeVal ma lit t (ops >>> 4) (recipeStep ma lit (ops &&& 15) stack)


theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]


def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]


def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih


def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/8 < N s && (rot (v/2 % 4) zs).isPerm (S s (v/8)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/8 < N s && (rot (v/2 % 4) zs).isPerm (S s (v/8))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h


def t1 : Nat := 0x0

def t2 : Nat := 0x20000000100000080000000000000000000000000000000000000000000000000000000000

def t3 : Nat := 0x2000000000000200000000000000000000000000000000000000000000000000000000000000

def t4 : Nat := 0x40040000400020100100001000080000000000000000000000000000000000000000000000000000000000

def t5 : Nat := 0x4004000202000000000008400010100004001100040000000000000000000000000000000000000000000000000000000000000

def t6 : Nat := 0x480000000010000000000000040000000000000000012000000008010008000004401000000000011004000000000000200400200

def t7 : Nat := 0x482000000000001208000000400010000000001000040000000000080040200000000200100800008041000000000020104000000

def t8 : Nat := 0x8000000000004000080002000000004800000000000800000000000000000000000000000000000000000000000000000000000000

def t9 : Nat := 0x40000000000000100000000000400090000000001000240000000000204010000000000810040000000c00009000000003000024000

def t10 : Nat := 0x40000080000000100400008000000000008010000000020000000000000000000000000000000000000000000000000000000000000

def t11 : Nat := 0x110000000000010020000000000002000000080000080000000000000000000000000000000000000000000000000000000000000000

def t12 : Nat := 0x24000408c00020a100400008008401190108014001100268000000000204010400100082810040000200c0001900800020b000026800

def t13 : Nat := 0x422800000880000c441280022000031104a00000000108a000000051104200000000000200400280000000801000a0000144410800000

def t14 : Nat := 0x426800408c80020e54168002a008431194b08014001108a680000051106240104001000a2850068000200c801190a800034f410826800

def t15 : Nat := 0x410090200000001040240800420400006048201081000018120800008c410090000000231040240000000000286050200000000a181408

def t16 : Nat := 0x4522902000880010c465280062040031704a20108100109a120800059d45209000000023304424280000000829605a200014441a981408

def t17 : Nat := 0x1000002480000020000000000000010000024800000200000000000000000000000000000000000000000000000000000000000000000000

def t18 : Nat := 0x10040024860040202020012080000184000349000042011000400000031004800402000000202401208008080c1102090000064114000000

def t19 : Nat := 0x100422a48600c82020e441288022018431134b00004201108a400000071104a00402000000202401288008080c11020b0000164514800000

def t20 : Nat := 0x100424248608c02020a1016080080184011b49080142011002680000031006840506001000a2a50160800a08cc111b09800026f114026800

def t21 : Nat := 0x184100b4b00004201140240800420500406248601483020218120800808cc110b0900000671140240000003100686050200000020a581608

def t22 : Nat := 0x184400349600442031200520800001844003496004420312005208008390c5902492000064316401208008390c5902492000064316401208

def t23 : Nat := 0x7150420a00c1ac0202ce440c8002a71e021124d8c2142807088280000071104200004001000ae040028000a000801120b800034c410802800

def t24 : Nat := 0x7360860204d42c028a6f000185542f5d2019249a1706304d0280808db87914560205436f020be54083c0fca200b0db24ba3f03cc4d3a83808

def t25 : Nat := 0x10904400348600402630200d248010098c080349200042411000d21800039045800402002020306409248008080c19024920000e4116001008

def t26 : Nat := 0x10984400349000042611000d24001009084802486004024212009218008190c5102090002064314408240000310849004820000c4212401208

def t27 : Nat := 0x27140000a4880200200440808800027140000a4880200200440808800000000000000000000000000000000000000000000000000000000000

def t28 : Nat := 0x27140022248c02c82024e08128000271c4111b4b80204201540a488000071106a60506001000aea58168800a08cc111b0b800036f514826800

def t29 : Nat := 0x27140024a48c0ac02024e180c8000a71c4011b4988214201540a68800000000204010400100082810040000200c0001900800020b000026800

def t30 : Nat := 0x27140400a48e024020246081a8800271c4000b49802042015408488000031004800402000000202401208008080c1102090000064114000000

def t31 : Nat := 0x27140422a48802882004c4c1a800227140311a4a80200200548a088000051104200000000000200400280000000801000a0000144410800000

def t32 : Nat := 0x27144100b4a80200201440a48800427540006a48a030830044181a8800008c410090000000231040240000000000286050200000000a181408

def t33 : Nat := 0x27150420a48c1ac0202ce4c0c8002a71e0211a4d8c2142807488288000071104200004001000ae040028000a000801120b800034c410802800

def t34 : Nat := 0x27150422a48c1ac8202ce4c1e8002a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800

def t35 : Nat := 0x40200820080000a000808000103640040201503020100104101200080000000000000000000000000000000000000000000000000000000000

def t36 : Nat := 0x40200824080408e000a0a100503648048601593128114105101268080000000204010400100082810040000200c0001900800020b000026800

def t37 : Nat := 0x40200c22880000a80080c441383662040231507a20100104109a000800051104200000000000200400280000000801000a0000144410800000

def t38 : Nat := 0x40204920982000a00090c024183642040201707820108104101a120800008c410090000000231040240000000000286050200000000a181408

def t39 : Nat := 0x500045009a200020021044640c2272040828605820108100009812180008ac41009a000008231040640200040020a86050200000000a181418

def t40 : Nat := 0x50204c20980000a00290c4441c3672040a2950582010010410980018000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t41 : Nat := 0x50204c209a0000a002908464143670040a295030201001041092001800082c00009a000008030000640200040020a040100000000008100410

def t42 : Nat := 0x50a04c20180000a00690800d3436500c0a095078201001441012921800019045000000002020304408240000000809004820000c4012001008

def t43 : Nat := 0x871e4000b058c214281640068800427550004248e1b40302c2180c0800a08c4101b01800022b104026800000200028605060010008ea181408

def t44 : Nat := 0xc72708208848dab0088ec442d8366a74722150148db10184e0982c007f3c6d0029da4ddfde1b8e02769a77f70423a0f416ddfd718ce8b92d17

def t45 : Nat := 0xc7370860a84ddaf028aef442d8776af5f221d25dadf16384f0b82c08ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t46 : Nat := 0xd00844119a1080340211046684223000082a4010408c00020a90041000282c00019a08000a0b0000668200040020a040104001000828100410

def t47 : Nat := 0x1009080c024850040242030092141018984408349204062611020d248808390c5d024922020e4317409248808390c5d024922020e4317409248

def t48 : Nat := 0x22716030024e84200280648800800427550402a48a1308300c44c1a88008080c11020b000016451480000000071104a204020000002c2481288

def t49 : Nat := 0x2800202000040c0100802080200004004104048002190010080540c080000000000000000000000000000000000000000000000000000000000

def t50 : Nat := 0x2800202240044c8d00822a90240004804944159012991410190566c080000000204010400100082810040000200c0001900800020b000026800

def t51 : Nat := 0x2a70603118068c210080648a2880042745002680081b88100cc5c0c8000200c0001902800030b400826800000401022601040010008e8180480

def t52 : Nat := 0x2a7160200a4c8c210280648828800427550404a48a1b00300c45c0c880000000000000000000000000000000000000000000000000000000000

def t53 : Nat := 0x2a716030024e8c210280648820800427550406a48a1b08300c45c1e88008080c11020b000016451480000000071104a204020000002c2481288

def t54 : Nat := 0x2a7160311a4e8c210280648a28800427550026a4881b88300cc5c0c8000200c0001902800030b400826800000401022601040010008e8180480

def t55 : Nat := 0x2a7160311a4e8c210280648a28800427550426a48a1b88300cc5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t56 : Nat := 0x2a7160311a4e8c210280748a28800427550426a48a1b88300cc5c1e88000000801000a000014441080000000051104200000000000200400280

def t57 : Nat := 0x2a7164300b4e8c210281648a68800427550406a48a1b08300c45c1e8800008c410090000000231040240000000000286050200000000a181408

def t58 : Nat := 0x2a71e031124f8c214280748828800427550422a48e1bc8302ce4c1e8800a080c11120b800036c51480280000071104a20406001000ae2481288

def t59 : Nat := 0x2a71e4200b4d8c214281748868800427550404a48e1b40302c65c1e88008080c110209000006411400000000031004800402000000202401208

def t60 : Nat := 0x2a71e4211b4d8c214281748868800427550424a48e1bc0302ce5c0c8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t61 : Nat := 0x2a71e4211b4d8c214281748a68800427550424a48e1bc0302ce5c0c8800200c0001900800020b00002680000000002040104001000828100400

def t62 : Nat := 0x2a71e4300b4f8c214281648868800427550406a48e1b48302c65c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t63 : Nat := 0x2a71e431134f8c214281748a60800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t64 : Nat := 0x2a71e4311b4f8c214281748a68800427550026a48c1bc8302ce5c1e8000a08cc111b0b800036f51482680000071106a60506001000aea581688

def t65 : Nat := 0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t66 : Nat := 0x2a71e4335b4fccad42837e9a6c8004a75d4437b49e9bdc303de5e7e8800a08cc315b1bc00136fd3c926c0000271d06a7950e00120baea5a7e88

def t67 : Nat := 0x2a71e4711b4fec254283768a7a8804275d4426b49e1bcc303de5c5e8800a39cc591b4ba00036f716c27a08008791c7b62596001064bfe581688

def t68 : Nat := 0x2a71e4733b4f8c29c2817cce7a800627550737a4ae1bc8302dede1e8800a59dc531b0b800036f714c26a8000071186b605a6001144efad81688

def t69 : Nat := 0x2b79e4711b4f8c2142e1748afac00527d584a6a48e1bc8342de5c9e9800a19cc511b0b800236f714c2ea4000071186b605860010c4afa581688

def t70 : Nat := 0x2c0220a200840c0b00882880210364004124158302190010490560c080000000000000000000000000000000000000000000000000000000000

def t71 : Nat := 0x2e73e4b31bcf8c2b42897c8a69836427552437a78e1bc8306de5e1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t72 : Nat := 0x2f71e4711bef8c2342a174ce68c227275586a6a58e1bc8302cedc1e9800a8acc111bab8000b6f5148668200047130ea60506001000aea581698

def t73 : Nat := 0x300228ae0004540c008a2b800115541849641992121506125906648480340020a04014400d00082810051024282c00099a08090a0b000266820

def t74 : Nat := 0x3271682c024cd424028263880014101f1d4408b0181606221c46448c0dbc202bad625f636d1c4cfb981518fcafbd4569ba183f2a2b3c566eae0

def t75 : Nat := 0x327368ae024cd42c028a6f880195543f5d6419b49a1706325d46c48c8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t76 : Nat := 0x3a79ec391b4fac2142c1748afa980437d54426b48e1bc8363ce5cdec800a08cc191b4ba0003ef51682780800079147a60506003020bee5896c8

def t77 : Nat := 0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800

def t78 : Nat := 0x427554526b4ae1bc8303ce5e5e8806a75e4317b4fac31c381749a7a8800079d47a69506001023bee5a568800a08cc397b5ba00036f51e9a7c08

def t79 : Nat := 0x467750c26ac8e1be830ace5c1f8b66a75e6315b7fac314385749a688800071106a60506001000aea58168800a08cc111b0b800036f514826800

def t80 : Nat := 0x477554426be8e1be8323ce5e5eca23a71ec395b5f8c214281749a6890000f3d06a69f06001803aea5e56a800e08ecb15b1b800036f51c926c10

def t81 : Nat := 0x6a7570626a4cedbd8382eedc3e8806a75f4715b4fadb14381f4de6c8800071106a60506001000aea58168800a08cc111b0b800036f514826800

def t82 : Nat := 0x6a75f4737b4fedbdc383fede7e8806a75f4737b4fedbdc383fede7e8800a79dc7b7b5be00136fffeda7e8800a79dc7b7b5be00136fffeda7e88

def t83 : Nat := 0x82794110224a80209e50440892a0082794110224a80209e50440892a0d88791f5f224b23621e47d7c892c8d88791f5f224b23621e47d7c892c8

def t84 : Nat := 0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t85 : Nat := 0x877b45d22bea802a9e794c4edbe36f27d4b397a7aa0309f54549a9ab8000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t86 : Nat := 0x8d0a85d339a3080bdc791c46fbe36f20c0b3b707a609c9d561a9a9638002dbd45219a08002a2b30446eae0004002ba9605a60011c4c3a981418

def t87 : Nat := 0x8d7be5d22ba78c2bdef96c46fbe36f27d5b39727ae1b49f56d29a9e3800adbd4521ba18002a2b30446eae0004202ba9605a60011c4cfa981418

def t88 : Nat := 0x927b499e224ad02c9e5a4f0893b5583f9c711b36b8060fe75542ad2e0dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t89 : Nat := 0xa27261b2200684289c986c8801a14c2745311382281309d14c44e08a05b44033a26016416d100ce89805907c2c2d302b9a281f0b0b4c0ae68a0

def t90 : Nat := 0xa27b61b2224e84289ed86c8893a14c27d53113a6a81309f54c44e9aa0dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t91 : Nat := 0xad0a25f229a60c0b9cf92cc6f3e36f20c1b79787a21909d5490de9e38000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t92 : Nat := 0xae7271b228868dab9c98eccc2da36ea74733178368db19d94e4de2ca07f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t93 : Nat := 0xaf7b65f22bee8c2b9ef96ccefbe36f27d5b797a7aa1b09f54d4de9eb8000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t94 : Nat := 0xaf7be5f33bef8c2bdef97ccefbe36f27d5b7b7a7ae1bc9f56dede9eb800adbdc531bab8002b6f714c6eae0004713beb605a60011c4efad81698

def t95 : Nat := 0xb27b69be224ed42c9eda6f8893b55c3fdd751bb6ba170ff75d46edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t96 : Nat := 0xb27b69be226ed42c9eda6f8a93b55c3fdd751bb6ba170ff75d46edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t97 : Nat := 0xb67b69be22ced42e9eda6f8893b77c3fdd751fb7ba170ff75d47edae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t98 : Nat := 0xb77b6dfe2beed42e9efb6fced3f77f3fddf79fb7ba170ff75d4fedaf8dbcfbffff6bff636f9e7fffded7f8fcefbfffffbfba3f2bef7dffefef8

def t99 : Nat := 0xc27d51526a6ae1bc9f52ce5e9ea80aa79e5313b6f8c21ded1748afaa000071106a60506001000aea58168800a08cc111b0b800036f514826800

def t100 : Nat := 0xc50e15d269a2219a9d798c56dfeb6fa0c2b39707e2c119dd4309ab238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t101 : Nat := 0xc67f51d26aeae1be9f5ace5e9fab6ea7de7317b7fac31dfd5749afaa800071106a60506001000aea58168800a08cc111b0b800036f514826800

def t102 : Nat := 0xc77f55d26beaa1ba9f79cc5edfeb6fa7d6b397a7eac319fd4749abab8000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t103 : Nat := 0xc77f55d26beae1be9f7bce5edfeb6fa7def397b7fac31dfd5749afab8000fbd47a69f06003823bee5ed6e800e08efb97b5ba0003ef51e9a7c18

def t104 : Nat := 0xef7ff5f37befedbfdffbfedeffeb6fa7dff7b7b7fedbddfd7fedefeb800afbdc7b7bfbe003b6fffedefee800e79fffb7b5be0013efffeda7e98

def t105 : Nat := 0xf27f79fe6a4ef5bc9fdaefdc9fbd5ebfdf771bb6fad71fff5f4eefae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t106 : Nat := 0x10df3f4c28b858deb62a9ec646dc367a757a2d525cddb50386e3982c14ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t107 : Nat := 0x22c0220a240940c8b00882890250364c04120158b00993010480562c020350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t108 : Nat := 0x23c0228ae40945c8f008a2b90251774d849641d9b129d3612590766c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t109 : Nat := 0x27275586a6a58e1bc8302cedc1e9802f71e4711bef8c2342a174ce68c20047130ea60506001000aea58169800a8acc111bab8000b6f514866820

def t110 : Nat := 0x5c3fdd751bb6ba170ff75d46edae80b27b69be224ed42c9eda6f8893b5fcafbdf5fbbeba3f2bef7d7eefae8dbc793fff625f636f1e4fffd897d8

def t111 : Nat := 0x5f3ffffffbb6ff57cffffffeedbfd5f3ffffffbb6ff57cffffffeedbfdffefbfffffbffe3ffbefffffefff8ffefbfffffbffe3ffbefffffefff8

def t112 : Nat := 0x6427552437a78e1bc8306de5e1e8802e73e4b31bcf8c2b42897c8a698300071106a60506001000aea58168800a08cc111b0b800036f514826800

def t113 : Nat := 0x66c0632a358b40d9b018ca8d62d0366c0632a358b40d9b018ca8d62d0327786e0a0ddb4dc9de1b828376d3727786e0a0ddb4dc9de1b828376d37

def t114 : Nat := 0x66e7672a358948dbb018cecdc2d8366e7672a358948dbb018cecdc2d837f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t115 : Nat := 0x6c00c0311703220109d54101292280840a019220a2000a9c58080293230000000000000000000000000000000000000000000000000000000000

def t116 : Nat := 0x6c27d53537a7ae1bc9f56de5e9ea80ae7be5b33bef8c2bded97c8afba300071106a60506001000aea58168800a08cc111b0b800036f514826800

def t117 : Nat := 0x6c40e039370b2201a9d5c1812932b6c40e039370b2201a9d5c1812932b0000000000000000000000000000000000000000000000000000000000

def t118 : Nat := 0x6c50e07d379b2201a9d7d1c56d3eb6f60e0bbb70fa201a9d5c189a933b000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t119 : Nat := 0x6cc76738268b48dbb9d9cec542da36ee7673b150b68db31d9ce09a2d237f7c6f3a2fdb4ddfde1b8e83f6db77f786e3a0fdb6ddfdf1bce8bf6d37

def t120 : Nat := 0x6ee7673b378b68dbb9d9cecde2da36ee7673b378b68dbb9d9cecde2da37f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t121 : Nat := 0x6ee7673b378b68dbb9d9cecde2da36ee7673b378b6adbb9d9cfcde2dab7f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t122 : Nat := 0x6ee7673b378fe8dbb9d9cfcde2da36ee7673f378b68dbb9d9cecde3fa37f7c6fba3fdbeddfdf5fcf8bf6db77f7d7f3e2fdb6ddfdf1bee8ff6fb7

def t123 : Nat := 0x6ee7773b37afe8dbb9f9cecde2da36ee7773b37afe8dbb9f9cecde2da37f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t124 : Nat := 0x6ee7773f37afeedbf9f9eeede3fab6ee77f7b37bff8dbbdf9dfcde6da37f7f7f3eafdf6fdfdf1beeaff7fbf7ffceffb3ffbfddfdf7fdfcbf6db7

def t125 : Nat := 0x6ee7f73b37afe8dbb9fdcecdebfa36ee7f73b37afe8dbb9fdcecdebfa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t126 : Nat := 0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t127 : Nat := 0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46dbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t128 : Nat := 0x6f20c0b39707a20109d54109a92380850a05d229a2200a9c790c46d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t129 : Nat := 0x6f20c0b39707a20109d54109a92380850a05d229a2200a9c791c46d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t130 : Nat := 0x6f20c0b39707a20109d54109a92380c50e05d269a2201a9d790c56d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t131 : Nat := 0x6f20c0b39707a20909d54109a963808d0a05d229a2080b9c790c46f3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t132 : Nat := 0x6f20c0b39707a60149d56129a92380850a85d229a3000adc791c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t133 : Nat := 0x6f20c0b39787a20109d54109a9a380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t134 : Nat := 0x6f20c0b39787a20109d54149a92b80870a05d229ea000a9c790c4ed3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t135 : Nat := 0x6f20c0b3b707a20189d54189a92380850a05d339a2000a9c791c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t136 : Nat := 0x6f20c0b3b707a609c9d561a9a963808d0a85d339a3080bdc791c46fbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t137 : Nat := 0x6f20c0b79707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t138 : Nat := 0x6f20c0b79787a20109d5410de92380a50a05f229a2000a9c790cc6d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t139 : Nat := 0x6f20c1b79787a21909d5490de9e380ad0a25f229a60c0b9cf92cc6f3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t140 : Nat := 0x6f20c1b7b787a619c9d569ade9e380ad0aa5f339a70c0bdcf93cc6fbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t141 : Nat := 0x6f20c8f39717b2010dd55109ad2380850a05d229a2400e9c7b0e46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t142 : Nat := 0x6f20d0b39727a20109f54109a92380850b05d22bea000a9e790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t143 : Nat := 0x6f20e2bbf707e741c9dde3b9a933d5c58e97d3b9a3215afd7d9c66dbeb034002ba9605e600d1c4c3a981518242dbd45299a08092a2b30466eae0

def t144 : Nat := 0x6f27d4b397a7aa0309f54549a9ab80877b45d22bea802a9e794c4edbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t145 : Nat := 0x6f27d4b3b7a7ae0bc9f565e9a9eb808f7bc5d33beb882bde795c4efbe3004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t146 : Nat := 0x6f27d5b39727ae1b49f56d29a9e3808d7be5d22ba78c2bdef96c46fbe3004202ba9605a60011c4cfa98141800adbd4521ba18002a2b30446eae0

def t147 : Nat := 0x6f27d5b797a7aa1b09f54d4de9eb80af7b65f22bee8c2b9ef96ccefbe3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t148 : Nat := 0x6f27d5b7b7a7ae1bc9f56dede9eb80af7be5f33bef8c2bdef97ccefbe3004713beb605a60011c4efad8169800adbdc531bab8002b6f714c6eae0

def t149 : Nat := 0x6f27d6b3d727ef4349fd6739a923c185fbd5d2aba3816afe79cc66dbe3dbc202bad625f636d1c4cfb981518fcafbd4569ba183f2a2b3c566eae0

def t150 : Nat := 0x6f30c0f79717a20109d75109ad2780950a0dda29a2000a9c790c46d3f3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t151 : Nat := 0x6f60c0b3970fa20129d54109a923a2850a05d269b2000a9c790c56d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t152 : Nat := 0x6f60e0bbb70fa201a9d5c189a933b6c50e07d379b2201a9d7d1c56d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t153 : Nat := 0x6f60e0bbb70fa609e9d5e1a9a973b6cd0e87d379b3281bdd7d1c56fbeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t154 : Nat := 0x6f70e0ffb79fa201a9d7d1cded3fb6f70e0ffb79fa201a9d7d1cded3fb004dbfffb69fa20029e771eded6f8004dbfffb69fa20029e771eded6f8

def t155 : Nat := 0x6fa0c0b39707a28119d54109ab2380850a05d269a2008a9c790c56d7e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t156 : Nat := 0x6fa0c2b39707e2c119dd4309ab2380c50e15d269a2219a9d798c56dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t157 : Nat := 0x6fa0c2b3b707e6c9d9dd63a9ab6380cd0e95d379a3299bdd799c56ffeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t158 : Nat := 0x6fa7d6b397a7eac319fd4749abab80c77f55d26beaa1ba9f79cc5edfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t159 : Nat := 0x6fa7def397b7fac31dfd5749afab80c77f55d26beae1be9f7bce5edfeb00e08efb97b5ba0003ef51e9a7c18000fbd47a69f06003823bee5ed6e8

def t160 : Nat := 0x6fe0e2bbb70fe2c1b9ddc389ab33b6c50e17d379b2219a9d7d9c56dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t161 : Nat := 0x6fe7f7bbf7afeddbf9fdeefdebfb77effff7f3fbffadfbfffdfcfeffebffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t162 : Nat := 0x80000000004000200000000010000800000000040002000000000100000000000000000000000000000000000000000000000000000000000000

def t163 : Nat := 0x80c02208604845e8f008a2b012507f48849201d4112bd1610490312c0803104000004045c0d41082001010724304000094009c90618000212807

def t164 : Nat := 0x81000080c04005204000203010014901808440850122406021102140480000000000000000000000000000000000000000000000000000000000

def t165 : Nat := 0x81000080e4400528c00020b1104149098084419d012a416021102368480000000204010400100082810040000200c0001900800020b000026800

def t166 : Nat := 0x81001084c0648720402020301121c9018184408749224062211021404800031004800402000000202401208008080c1102090000064114000000

def t167 : Nat := 0x810018c0c0749520442031301401490181844087496244622312215248008080c110209000006411400000000031004800402000000202401208

def t168 : Nat := 0x81402088e0480520e000a0b010117f41848641d53122506125103340480000000000000000000000000000000000000000000000000000000000

def t169 : Nat := 0x83a71ec3d1f4fde254283778b6894943f5d442ef49e3fce323de7d5ec800a08cc111b0b800036f51482680000071106a60506001000aea581688

def t170 : Nat := 0x83c0228ae04845e0f008a2b812117f41849641dd3123d0612590774c480000000000000000000000000000000000000000000000000000000000

def t171 : Nat := 0x83c0228ae04845e8f008a2b812517f49849641dd312bd1612590776c480350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t172 : Nat := 0x85275584e6e48f3bc8302cf5d1e9c92bf1e4719f4fae6162a174ab68c800071106a60506001000aea58168800a08cc111b0b800036f514826800

def t173 : Nat := 0x8950a0dde2da2520e9c7b0f47d3f7ff38c8f79f57b2250fd7510bbd278000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t174 : Nat := 0x8b27b69be264ed62c9eda6f8993b5dc3fdd751bf6ba370ff75d46fdae8dbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t175 : Nat := 0x9018084408501224060211021404881000080c040052040002030100140000000000000000000000000000000000000000000000000000000000

def t176 : Nat := 0x9018184448701524462230321404491081880c8649724462021321001c8083904540201020202030540824080820080d024922000c4013001008

def t177 : Nat := 0x9058210c6848053ce202a8b650547f3880aa2d94151e41608431a12014ff1f7104684a45fffc10ae16583e7fff042b85960f9ffc7dc411a12917

def t178 : Nat := 0x905f3d4c68f81d3ee622bcf654dc7f3af1ea2d965dde65628673a92014ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t179 : Nat := 0x908f1f0048605dfe56282e3212c04908f1f0048605dfe56282e3212c04ffb2400049605dffd6188e1212907ffb2400049605dffd6188e1212907

def t180 : Nat := 0x909f1f4448f05dfe562a3e7656cc493af1f82c864ddfe56282e3a92c14ffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t181 : Nat := 0x90d8094408d810bc3602180656c42a3800282c44145e8500822391241424386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t182 : Nat := 0x90d8294c28d810bcb60298c656dc3e7a042a2d545c7e9501863399241c243dfd4529da09c92e3b30467eae7035042ba9645e7c0d5d4c3a99151f

def t183 : Nat := 0x90d82a48485851e4360a921216147f50841a0cc41073d421068331041cffb8ec4149fa59ffee3b10527e967ff52423ace4547ffd4908eb39151f

def t184 : Nat := 0x90d82b4c685855fcf60abab656547f7884ba2dd4157fd56186b3b1241cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t185 : Nat := 0x90df3e4868785de6f62ab6f2161c7f52f5da0dd659f3f46306d3390c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t186 : Nat := 0x90df3f4c48f859f6362a9e56569c7f72f57a2cc65cf7f42386e3b9041cffbffd4569fa59ffee3b3c567ebe7ffd242bade65f7ffd5d4cfbb9151f

def t187 : Nat := 0x90df3f4c68f85dfef62abef656dc7f7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t188 : Nat := 0x90df3f4c68f85dfef62abef656dc7f7af5fa2dd67dfff56386f3bb2c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t189 : Nat := 0x90df3f4c68f85ffef62abff656dcff7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t190 : Nat := 0x90df3f4c6cf85dfef62abef756dc7f7af5fe2ddf5dfff56387f3bb6c1cffbffd476dfb5dfffe3bbed77efe7fff24ebadff5ffffd7dfcfbbb7d1f

def t191 : Nat := 0x90ff3f4c68fcddfef62abef6d6dc7f7af5fa2dde5dfff56386f7b92c9cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t192 : Nat := 0x911808c4c8501724460231321405c911808c4c8501724460231321405c0000000000000000000000000000000000000000000000000000000000

def t193 : Nat := 0x911818c4c87015244622303214054911818c4c8749724462231321405c8083904540201020202030540824080820080d024922000c4013001008

def t194 : Nat := 0x911818c4c8749724462231321405c911818c4c8749724462231321405c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t195 : Nat := 0x911818c4c8749724462231321405c911818c4c8749724462231321525c008080c110209000006411400000000031004800402000000202401208

def t196 : Nat := 0x911898c0c8749524462631321d254911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t197 : Nat := 0x911898c0c8749724462631321c05c911898c4c8701724462630321d25c808280c1d024922020e411700904880839045c024122020a0307409248

def t198 : Nat := 0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t199 : Nat := 0x911898c4c8749724462631321d25c911898c4c8769724462631323d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t200 : Nat := 0x911898c4c8749724462631321d25c9518d8c4cc749725463631331d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t201 : Nat := 0x911898c4c8f49724462631365d25c931898c6c87497244626313a1d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t202 : Nat := 0x911898c4c8f49724462631721d2dc913898c4c8749724462631329d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t203 : Nat := 0x911898c4cc74972c462631331d65c919898c4c87497a4562631321f25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t204 : Nat := 0x911898c4eaf49724ce2631f65d2dc933898c7d974b7244626313abd25c808791c5f024922020e43174092c8808390c5d024b22021e4717c09248

def t205 : Nat := 0x911898c4ec74972cc62631b31d65c919898c4d9f497a4562631323fa5c808390c7d425962030e4b3f50964880a39cc5d1b49a2022ef31742fa48

def t206 : Nat := 0x911898c5c8f4b724462631723d2dc9538d8c4ce7497254e3631339d25c80839cc5d0b4922020e731742d248808390c7d625922020e431f589648

def t207 : Nat := 0x913f9cc4c8f49f26462635729dadc913f9cc4c8f49f26462635729dadc808390c5d024922020e4317409248808390c5d024922020e4317409248

def t208 : Nat := 0x913f9cc4eaf49f26ce2635f6ddadc933f9cc7d9f4bf264626357abdadc808791c5f024922020e43174092c8808390c5d024b22021e4717c09248

def t209 : Nat := 0x9158b8cce87c9724e626b1b21d35ff518d8e4dd779725463671333d25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t210 : Nat := 0x9158b8cceafc9724ee26b1f65d3dff738d8e7dd77b7254636713bbd25c808791c5f024922020e43174092c8808390c5d024b22021e4717c09248

def t211 : Nat := 0x91df3fcce8f85dfef62abef656dd7f7bf5fe6dd75dfff563a7f3b96c5cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t212 : Nat := 0x91dfbfcce8fcdffef62ebff65ffdff7bfdfe6dd75dfff563e7f3b9fe5cffbffdc5f9fedffffeffbf767fbeffff3d2ffdf65fffff7fcffff9bf5f

def t213 : Nat := 0x92df3f4e68f85dfef62abefe56dc7f7af5fa6dde5dfff56386f3fd2c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t214 : Nat := 0x92ff3f4f79fcfdfef62abffef6dc7f7af5fa6ffe5dfffde386fffd3e9cffbffdc579fafdffff7fff5e7ebe7fff753beff65ffffd7dcefbf93f9f

def t215 : Nat := 0x933898c7d974b7244626313abd25c911898c4eaf49724ce2631f65d2dc808390c5d024b22021e4717c09248808791c5f024922020e43174092c8

def t216 : Nat := 0x933f9ec7c874ff66462e377a9d2dc953fddc4caf49f374e363d76ddadc808390c5d024b22021e4717c09248808791c5f224922020e43d74892c8

def t217 : Nat := 0x93989ac6c874d7e4562e333a1f25c9518d9c4ccf4973d463639375de5c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t218 : Nat := 0x93bf9ec6c8f4dfe6562e377a9fadc953fddc4ccf49f3f46363d77ddedc808390c5d024922020e4317409248808390c5d024922020e4317409248

def t219 : Nat := 0x93bf9ec7d9f4ffe6562e377abfadc953fddc4eef49f3fce363df7ddedc80a39cc5d1b4ba2023ef717c2fa48808791c7f625962030e4bff5896c8

def t220 : Nat := 0x93d8bacee87cd7e4f62eb3ba1f35ff518d9e4ddf7973d463679377de5c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t221 : Nat := 0x93ff3fcee8fcddfef62abefed6dd7f7bf5fe6ddf5dfff563a7f7fd6cdcffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t222 : Nat := 0x943f5d442ef49e3fce323de7d5ec883a71ec3d1f4fde254283778b689400071106a60506001000aea58168800a08cc111b0b800036f514826800

def t223 : Nat := 0x94df7f4c6cf85ffff63abef756dcff7af5fa2dd65dfff56386f3b92c1cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t224 : Nat := 0x94ff7f4c6efcdffffe3abef7d7fcff7af5fe3ddf5ffff56387f7bb6c9cffbffd47efff5ffffe3bbef7fffeffff2cefbdff5ffffd7ffdffbb7d1f

def t225 : Nat := 0x9518d9c4ccf4973d463639375de5c93989ac6c874d7e4562e333a1f25c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t226 : Nat := 0x953f5dc4eef49f3fce323df7d5edc93bf1ec7d9f4ffe6562a377ab68dc00071106a60506001000aea58168800a08cc111b0b800036f514826800

def t227 : Nat := 0x953fddc4eef49f3fce363df7ddedc93bf9ec7d9f4ffe6562e377abfadc808791c7f625962030e4bff5896c880a39cc5d1b4ba2023ef717c2fa48

def t228 : Nat := 0x97bfdfc7fff4ffffde3e3fffffedc97bfdfc7fff4ffffde3e3fffffedc80a79dc7f7b5be2033effffdafec880a79dc7f7b5be2033effffdafec8

def t229 : Nat := 0x9858a85d2ada3224afc791c67d3ebef20c0b3d747a72149d56139b923c000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t230 : Nat := 0x9858b85d6afa3524efe7b0f67d3e7ff28d8b3df67b7254ff5613bb923c808fbd4560ba1020282330546c2e080c202bad625b22001c441b981418

def t231 : Nat := 0x98dfbf5d6afa7dfeffefbef67ffe7ffafdfb3df67ffff5ffd6f3bbbe3cffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t232 : Nat := 0x991898d5ca76b7244fe731323d27c991898d5ca76b7244fe731323d27c808390c5d024922020e4317409248808390c5d024922020e4317409248

def t233 : Nat := 0x993f9cd5ca74bf264fe735729d2fc993f9cd5ca74bf264fe735729d2fcd88791f5f224b23621e47d7c892c8d88791f5f224b23621e47d7c892c8

def t234 : Nat := 0x9958a8ddeada3724efc7b1f67d3ffff38c8f7df57b7254fd7713bbd27c000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418

def t235 : Nat := 0x9958b8ddeafeb724efe7b1f67d3ffff38d8f7df77b7254ff7713bbd27c808fbdc5f0be922028e731746d2e880c392ffd625b22021e471fd89658

def t236 : Nat := 0x9b3fbedfea74ff66cfefb7fa9d3fddd3fddf5dbf6bf374ff77d76fdafcdbc793fff625f636f1e4fffd897d8fcafbdf5fbbeba3f2bef7d7eefae8

def t237 : Nat := 0x9bffbedffbfeffe6ffefb7feffbffff3fddf7fff7bf3fcff77dfffdefc80afbdc5f1beba202bef717c6fae880c793fff625b62031e4fffd896d8

def t238 : Nat := 0x9bffbfdfeafcfdfeffefbefedfff7ffbfdff7dff7ffff5fff7f7fffefcffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t239 : Nat := 0x9d7ffdddeefebf3feff7bdf7fdfffffbfdef7dff7ffe75fff777bbfafc808fbdc7f6bf962038e7bff5ed6e880e39effd7b5ba2023ef71fdafe58

def t240 : Nat := 0xa0c00000044900a83000000112402a0c00000044900a8300000011240200104000004001c0041000001000700104000004001c00410000010007

def t241 : Nat := 0xa0c00000244904a8f00020a112402a0c0084015d910a83400110136c0200104002044105c0141082811040700304c0001d009c0061b000036807

def t242 : Nat := 0xa0c02008244900a8b000808112503e4c04020154b02a9301041013240a00104000004001c0041000001000700104000004001c00410000010007

def t243 : Nat := 0xa1c00080c44905a87000203112416b0d808440c5912ac360211031644a00104000004001c0041000001000700104000004001c00410000010007

def t244 : Nat := 0xa2e71e4315fdf8ea34281749b6c82a4e7550426ed8ebbf8302ce5d3e8a00b0ccc111f0b9c0077f51483680700175106a64507c01410aea59168f

def t245 : Nat := 0xa3c0228ae44945e8f008a2b912517f4d849641d5b12bd361259077644a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t246 : Nat := 0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t247 : Nat := 0xa3c0228ee6c945e8f808a2fd53797f6f849671ddfb2bd3612590ff6c4a0355530e244145c0d410a2851079724386c8019daa9c90f5f410a76827

def t248 : Nat := 0xa3c022cbe4d965e8f008b2f936597f4f849641fdf92bd3e125907f7e4a0350ce4b04d145c0d43392c13451724386c028fdf0bc90e1b00a3f7c2f

def t249 : Nat := 0xa3c02acaf5d955e8f408b3b936d17f4d849643ddb16bdf61279a776c4a03704e0a05d14dc0d61b828136d1724386c020ddb0dc91e1b828376c27

def t250 : Nat := 0xa3c0328ee46dc7e8f028a2b91371ff4d859641dff92bd3632590776c4a0353520e844547c0d410a2a51171f24b8ecc119fa99c90e7f114276827

def t251 : Nat := 0xa3c03acae47dd5e8f428b3b916517f4d859641dff96bd7632792777e4a03d0c2cb1461d5c0d47493c110517243b7c0489de0bc90e1b202677a2f

def t252 : Nat := 0xa3e7368ae4edcdeaf028a6f992d97f4ff5d641dff9abf36325d47f6cca0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t253 : Nat := 0xa3e73ecbf5fdfdeaf428b7f9b6d97f4ff5d643fff9ebffe327de7f7eca03f0cecb15f1fdc0d77fd3c936d17243f7d06afdf0fc91e1baea7f7eaf

def t254 : Nat := 0xa7c0638ee4c947f9f018aabd52d1ff6d84b661ddb52fd361a5b0f76c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t255 : Nat := 0xa7e0628ae64dc7e9f818a2b99371ff4d849651ddb32bd3612594776cca0350420a864547c0d41082a19151f2438ec4109da09c90e3b104276827

def t256 : Nat := 0xa7e7778ee6edcffbf838aefdd3f9ff6ff5f671dfffaff363a5f4ff6cca0357530ea64547c0d410aea59179f24b8ecc119fab9c90f7f514a76827

def t257 : Nat := 0xa7e77fcff7fdfffbfc38bffdf7f9ff6ff5f673ffffefffe3a7feff7eca03f7dfcfb7f5ffc0d77fffedb7f9f24bffdc7bfffbfc91f7fffeff7eaf

def t258 : Nat := 0xabc0a29be64b65e8f9cda2b93b737fcd8c9751fdb32bd3fd759077fe6a0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t259 : Nat := 0xabd0a2dfe6db65e8f9cfb2fd7f7f7fff8c9f79fdfb2bd3fd7590fffe7a035dff4f24db45c0fc33b2c57c7f724786eba9fdfabc90fdf41abf7c3f

def t260 : Nat := 0xabe7b69be66dedeaf9eda6f99b7b7fcffdd751fffbabf3ff75d47ffeeadbd7d3fff665f7f6f5f4fffd997dffcbffdf5fbfebbff2fff7d7effaef

def t261 : Nat := 0xabf7bedff7fffdeafdefb7fdffff7ffffddf7bfffbebffff77defffefa03fdffcf35fbfdc0ff7ff3cd7eff7247f7fbebfdfafc91fdfefaff7ebf

def t262 : Nat := 0xaff7f7dfe6ffeffbf9ffbefdfffffffffdff79ffffaff3fff5f4fffefa035fff4fa6df47c0fc33bee5fd7ff24f8eefb9fffbbc90fff51ebf7c3f

def t263 : Nat := 0xb1d898c4cc7d97ac762631331f65eb1d898c4cc7d97ac762631331f65e8093d0c5d06493e024f431741924f8093d0c5d06493e024f431741924f

def t264 : Nat := 0xb3d82aceec5957ecf60ab3bb1655ff5d849e4dddb17bd7612793776c5e0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t265 : Nat := 0xb3d8baceec7dd7ecf62eb3bb1f75ff5d8d9e4ddff97bd763679377fe5e83d3d2cfd465d7e0f4f4b3f51975fa4bbfcc5d9fe9be92eff31767fa6f

def t266 : Nat := 0xb3df3fceecf95dfef62abeff56dd7f7ff5fe6ddffdfff763a7f3ff6c5effffff4f6dfb5dfffe3bbed77eff7fffa6ebadfffffffdfdfcfbbf7d3f

def t267 : Nat := 0xb3ffbecffdfdffeef62eb7fbbffdff5ffdde4ffff9fbffe367df7ffede83f3decfd5f5ffe0f7fff3fd3ff5fa4bffdc7ffff9fe93effbff7ffeef

def t268 : Nat := 0xb7ffffceeefddffffe3ebfffdffdff7ffdfe7ddffffff763e7f7fffede83d7d3cff665d7e0f4f4bff5997dfa4bbfcc5d9febbe92fff717e7fa6f

def t269 : Nat := 0xdcffff7d7bfefffffffffff6fffefffafffbbff65ffffdffdeffb9bfbdffbffdf5fbfeffffffffff7effbeffff7d3ffff65fffff7fcffff9bfdf

def t270 : Nat := 0xe7c062aaf54b47e9f018e3b93251ff4d8696c3ddb12bdb612d98776d4b0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t271 : Nat := 0xef20c0b39747a22109d54109b92388850a05d22da2020a9c790c47d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t272 : Nat := 0xef20c0b3d747a72149d56139b923c9858a85d2ada3224afc791c67d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t273 : Nat := 0xef20c0b3f747a729c9d561b9b963c98d8a85d3bda32a4bfc791c67fbeb004002ba9605a60011c4c3a981418002dbd45219a08002a2b30446eae0

def t274 : Nat := 0xef60e0bbf74fa721e9d5e1b9b933ffc58e87d3fdb3225afd7d1c77d3eb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t275 : Nat := 0xefa0c2b3d747e7e159dd6339bb23c9c58e95d2eda323dafd799c77dfeb004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t276 : Nat := 0xefc0e2bbf74b67e9f9dde3b93b73ffcd8e97d3fdb32bdbfd7d9877ff6b0350420a044145c0d41082811051724386c0009da09c90e1b000276827

def t277 : Nat := 0xefe0e2bbf74fe7e9f9dde3b9bb73ffcd8e97d3fdb32bdbfd7d9c77ffeb035042ba9645e7c0d5d4c3a99151f243dfd4529da09c92e3b30467eae7

def t278 : Nat := 0xefe767bbf7cb6dfbf9d9eefdf2db7feff6f7f3fdb7affbfdbdfcff6deb7f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7

def t279 : Nat := 0xefe7f7bff7efeffbf9fdeffdfbfbffeffff7f3ffffaffbfffdfcffffeb035753beb645e7c0d5d4efad9179f24bdfdc539fab9c92f7f714e7eae7

def t280 : Nat := 0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t281 : Nat := 0xf4d849641ddb12bd3612590776c4aa3c0228ae44947e8f008a3b91251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t282 : Nat := 0xf4d849641ddb12bd3612590776c4aa3c0228ae44b45e8f008a2b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t283 : Nat := 0xf4d849641ddb12bd3612590776c4aa7c0628ae44947e9f018a2b91251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t284 : Nat := 0xf4d849641ddb12bd3612594776ccaa3e0228ae44dc5e8f008a2b99251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t285 : Nat := 0xf4d849641ddb16bd7612792776c4aa3c02acae45955e8f408b3b91651724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t286 : Nat := 0xf4d849641fdb12bd3e12590777e4aa3c0228be44965e8f008a2b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t287 : Nat := 0xf4d849643ddb12bdb612598776c4aa3c0228af54945e8f008a3b93251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t288 : Nat := 0xf4d859641dff92bd3632590776c4aa3c0328ae46dc5e8f028a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t289 : Nat := 0xf4d8696c3ddb12bdb612d98776d4be7c062aaf54b47e9f018e3b93251f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t290 : Nat := 0xf4df7f6c7dfb5ffff63afff776dcff7ef7faafd6ddffff638efbb92d1fffbffd4569fa5dfffe3bbe567ebe7fff242badf65ffffd7dccfbb93d1f

def t291 : Nat := 0xf4ff5d641dff9abf36325d47f6ccaa3e7368ae4edcdeaf028a6f992d9724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t292 : Nat := 0xf4ff5d643fff9ebffe327de7f7ecaa3e73ecbf5fdfdeaf428b7f9b6d97243f7d06afdf0fc91e1baea7f7eaf03f0cecb15f1fdc0d77fd3c936d17

def t293 : Nat := 0xf518d8e4dd779725463671333d25c9158b8cce87c9724e626b1b21d35f808390c5d024922020e4317409248808390c5d024922020e4317409248

def t294 : Nat := 0xf5d849e4dddb17bd7612793776c5eb3d82aceec5957ecf60ab3bb1655f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t295 : Nat := 0xf5d869ecfddb17bdf612f9b776d5ff7d86aeefd5b57edf61af3bb3655f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t296 : Nat := 0xf5d8d9e4ddff97bd763679377fe5eb3d8baceec7dd7ecf62eb3bb1f75fa4bbfcc5d9fe9be92eff31767fa6f83d3d2cfd465d7e0f4f4b3f51975f

def t297 : Nat := 0xf6d84b661ddb52fd361a5b0f76c4aa7c0638ee4c947f9f018aabd52d1f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t298 : Nat := 0xf6d86b6e3ddb52fdb61adb8f76d4be7c063aef5cb47f9f018ebbd72d1f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t299 : Nat := 0xf6ff5f661dffdaff363a5f4ff6ccaa7e7778ee4edcffbf038aefdd2d9f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t300 : Nat := 0xf6ff5f671dfffaff363a5f4ff6ccaa7e7778ee6edcffbf838aefdd3f9f24b8ecc119fab9c90f7f514a768270357530ea64547c0d410aea59179f

def t301 : Nat := 0xf7af5fa2dd65dfff56386f3b92c1c90df3f4c68f85dfef62abef656dc7fff242badf65ffffd7dccfbb93d1fffbffd4569fa5dfffe3bbe567ebe7

def t302 : Nat := 0xf7d86beefddb57fdf61afbbf76d5ff7d86beefddb57fdf61afbbf76d5f27786e0a0ddb4dc9de1b828376d3727786e0a0ddb4dc9de1b828376d37

def t303 : Nat := 0xf7d8fbeefdffd7fdf63efbbf7ff5ff7d8fbeefdffd7fdf63efbbf7ff5fa7fbfecfddffdfe9feffb3f77ff7fa7fbfecfddffdfe9feffb3f77ff7f

def t304 : Nat := 0xf7ff7feefdfddffff63affffd6ddff7ff7feefdfddffff63affffd6ddfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def t305 : Nat := 0xf7ff7feeffffdffffe3afffff7fdff7ff7feffdfffffff63afffff6ddf277f7f0eafdf4fc9de1baea7f7fbf27f8eecb1dfbfdc9df7fd3cb76d37

def t306 : Nat := 0xfbd8aafbd95b71e437cfd31a3e177fd58e1bcee4b073debd7e8b75977ffff8eef959faf9ffefff515a7e977ff5f733eee4f47fffc90aeb7d97ff

def t307 : Nat := 0xfbdfbffff9fb7dfef7effffe7edf7ffffffbeff6fdfffffffefbfdbf7ffffffffd79fafdffffffff5e7ebf7ffff73beff6fffffffdcefbfdbfff

def t308 : Nat := 0xfcd8c9751fdb32bd3fd759077fe6aabc0a29be64b65e8f9cda2b93b73724386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t309 : Nat := 0xfcd8e97d3fdb32bdbfd7d9877ff6befc0e2bbf74b67e9f9dde3b93b73f24386c0009da09c90e1b0002768270350420a044145c0d410828110517

def t310 : Nat := 0xfcd8e97d3fdb32bdbfd7d9c77ffebefe0e2bbf74fe7e9f9dde3b9bb73f243dfd4529da09c92e3b30467eae7035042ba9645e7c0d5d4c3a99151f

def t311 : Nat := 0xfd18d8f5df77b7254ff771333d27c9958b8ddea7eb724efe7b1b23d37f808390c5d024922020e4317409248808390c5d024922020e4317409248

def t312 : Nat := 0xfd58e1bcee4b073debd7e8b75977ffbd8aafbd95b71e437cfd31a3e177ff5f733eee4f47fffc90aeb7d97fffff8eef959faf9ffefff515a7e977

def t313 : Nat := 0xfddffffceefb5ffffffffef75fffffffffffbdd7fffff77ffff3bbed7fffffff7fefff5ffffebbbef7ffffffffaeefbdfffffffffffdffbffd7f

def t314 : Nat := 0xfeff7f7f7ffb7dfffffbfefff6de7ffef7fbbffeffffffff9effff2dbfffffff7f6ffb7dffff3bfedffeff7fffe6fbaffffffffdfdfcfbbf7dbf

def t315 : Nat := 0xff28d8b3df67b7254ff5613bb923c9858b85d6afa3524efe7b0f67d3e780c202bad625b22001c441b981418808fbd4560ba1020282330546c2e0

def t316 : Nat := 0xff38c8f79f57b2250fd7510bbd2788950a0dde2da2520e9c7b0f47d3f7004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t317 : Nat := 0xff38c8f7df57b7254fd7713bbd27c9958a8ddeada3724efc7b1f67d3ff004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t318 : Nat := 0xff38c9f79fd7b23d0fd7590ffde788bd0a2dfe2da65e0f9cfb2fc7f3f7004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0

def t319 : Nat := 0xff38d8f7df77b7254ff7713bbd27c9958b8ddeafeb724efe7b1f67d3ff80c392ffd625b22021e471fd89658808fbdc5f0be922028e731746d2e8

def t320 : Nat := 0xfff8c9f79fdfb2bd3fd7590fffe7aabd0a2dfe6db65e8f9cfb2fd7f7f724786eba9fdfabc90fdf41abf7c3f035dff4f24db45c0fc33b2c57c7f7

def t321 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def rowsE (i : Nat) : List Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then [] else []) else (if i < 3 then [] else [])) else (if i < 6 then (if i < 5 then [] else []) else (if i < 7 then [t52,t84,t126,t225,t246,t280] else [t52,t84,t139,t198,t246,t280]))) else (if i < 12 then (if i < 10 then (if i < 9 then [t65,t77,t84,t126,t220,t280,t302] else [t65,t77,t84,t246,t294,t317]) else (if i < 11 then [t65,t77,t84,t246,t308,t311] else [t65,t77,t84,t258,t280,t293])) else (if i < 14 then (if i < 13 then [t65,t77,t84,t276,t280,t311] else [t65,t77,t117,t198,t246,t280]) else (if i < 15 then [t65,t77,t118,t198,t276,t280] else [t65,t77,t173,t246,t280,t316])))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then [t65,t77,t234,t246,t280,t317] else [t65,t77,t235,t246,t308,t319]) else (if i < 19 then [t65,t84,t112,t198,t258,t280] else [t65,t84,t116,t198,t246,t308])) else (if i < 22 then (if i < 21 then [t65,t84,t116,t198,t276,t280] else [t65,t101,t126,t198,t246,t309]) else (if i < 23 then [t65,t102,t147,t198,t246,t280] else [t65,t126,t173,t222,t246,t280]))) else (if i < 28 then (if i < 26 then (if i < 25 then [t65,t126,t226,t234,t246,t280] else [t27,t65,t84,t126,t225,t246,t280]) else (if i < 27 then [t27,t65,t84,t139,t198,t246,t280] else [t27,t84,t126,t219,t227,t246,t280])) else (if i < 30 then (if i < 29 then [t33,t65,t84,t126,t198,t246,t280] else [t33,t65,t84,t187,t198,t246,t280]) else (if i < 31 then [t34,t65,t84,t126,t198,t246,t280] else [t35,t65,t77,t115,t198,t246,t280]))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then [t35,t65,t77,t126,t198,t246,t308] else [t45,t65,t77,t84,t198,t246,t280]) else (if i < 35 then [t52,t77,t84,t95,t126,t198,t246] else [t52,t77,t84,t110,t126,t198,t280])) else (if i < 38 then (if i < 37 then [t52,t77,t84,t120,t126,t246,t280] else [t52,t77,t84,t126,t198,t246,t280]) else (if i < 39 then [t52,t77,t84,t126,t198,t246,t299] else [t52,t77,t84,t126,t198,t252,t280]))) else (if i < 44 then (if i < 42 then (if i < 41 then [t52,t77,t84,t126,t218,t246,t280] else [t52,t77,t84,t158,t198,t246,t280]) else (if i < 43 then [t52,t77,t84,t187,t198,t246,t280] else [t52,t77,t93,t126,t198,t246,t280])) else (if i < 46 then (if i < 45 then [t52,t77,t126,t198,t246,t280,t301] else [t52,t81,t84,t126,t198,t246,t280]) else (if i < 47 then [t52,t84,t126,t148,t198,t246,t280] else [t52,t84,t126,t198,t227,t246,t280])))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then [t52,t84,t126,t198,t246,t280,t306] else [t53,t77,t84,t95,t126,t198,t246]) else (if i < 51 then [t53,t77,t84,t126,t198,t246,t280] else [t54,t77,t84,t120,t126,t246,t280])) else (if i < 54 then (if i < 53 then [t54,t77,t84,t126,t198,t246,t280] else [t55,t77,t84,t126,t198,t246,t280]) else (if i < 55 then [t56,t77,t84,t126,t198,t246,t280] else [t57,t77,t84,t126,t198,t246,t280]))) else (if i < 60 then (if i < 58 then (if i < 57 then [t58,t77,t84,t126,t198,t246,t280] else [t59,t77,t84,t126,t198,t246,t280]) else (if i < 59 then [t60,t77,t84,t126,t198,t246,t280] else [t61,t77,t84,t126,t198,t246,t280])) else (if i < 62 then (if i < 61 then [t62,t77,t84,t126,t198,t246,t280] else [t63,t77,t84,t126,t198,t246,t280]) else (if i < 63 then [t64,t77,t84,t126,t198,t246,t280] else [t65,t70,t77,t84,t126,t198,t280,t302])))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then [t65,t75,t77,t84,t126,t198,t246] else [t65,t77,t84,t88,t126,t198,t246]) else (if i < 67 then [t65,t77,t84,t90,t126,t198,t246] else [t65,t77,t84,t92,t126,t246,t280])) else (if i < 70 then (if i < 69 then [t65,t77,t84,t95,t110,t120,t126] else [t65,t77,t84,t95,t110,t126,t198]) else (if i < 71 then [t65,t77,t84,t95,t110,t187,t198] else [t65,t77,t84,t95,t120,t126,t246]))) else (if i < 76 then (if i < 74 then (if i < 73 then [t65,t77,t84,t95,t120,t187,t246] else [t65,t77,t84,t95,t126,t192,t246]) else (if i < 75 then [t65,t77,t84,t95,t126,t198,t246] else [t65,t77,t84,t95,t126,t198,t252])) else (if i < 78 then (if i < 77 then [t65,t77,t84,t95,t126,t198,t254] else [t65,t77,t84,t95,t126,t198,t264]) else (if i < 79 then [t65,t77,t84,t95,t126,t204,t246] else [t65,t77,t84,t95,t126,t207,t246])))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then [t65,t77,t84,t95,t126,t209,t246] else [t65,t77,t84,t95,t126,t216,t246]) else (if i < 83 then [t65,t77,t84,t95,t126,t225,t246] else [t65,t77,t84,t95,t136,t198,t246])) else (if i < 86 then (if i < 85 then [t65,t77,t84,t95,t139,t198,t246] else [t65,t77,t84,t95,t143,t198,t246]) else (if i < 87 then [t65,t77,t84,t95,t144,t198,t246] else [t65,t77,t84,t95,t152,t198,t246]))) else (if i < 92 then (if i < 90 then (if i < 89 then [t65,t77,t84,t95,t156,t198,t246] else [t65,t77,t84,t95,t187,t198,t246]) else (if i < 91 then [t65,t77,t84,t95,t198,t246,t272] else [t65,t77,t84,t95,t198,t246,t316])) else (if i < 94 then (if i < 93 then [t65,t77,t84,t96,t126,t198,t246] else [t65,t77,t84,t97,t126,t198,t246]) else (if i < 95 then [t65,t77,t84,t106,t198,t246,t280] else [t65,t77,t84,t108,t126,t198,t280]))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then [t65,t77,t84,t110,t120,t187,t280] else [t65,t77,t84,t110,t136,t198,t280]) else (if i < 99 then [t65,t77,t84,t110,t139,t198,t280] else [t65,t77,t84,t110,t144,t198,t280])) else (if i < 102 then (if i < 101 then [t65,t77,t84,t110,t152,t198,t280] else [t65,t77,t84,t110,t156,t198,t280]) else (if i < 103 then [t65,t77,t84,t110,t187,t198,t280] else [t65,t77,t84,t110,t198,t272,t280]))) else (if i < 108 then (if i < 106 then (if i < 105 then [t65,t77,t84,t110,t198,t280,t316] else [t65,t77,t84,t113,t126,t246,t280]) else (if i < 107 then [t65,t77,t84,t114,t126,t246,t280] else [t65,t77,t84,t119,t126,t246,t280])) else (if i < 110 then (if i < 109 then [t65,t77,t84,t120,t126,t246,t280] else [t65,t77,t84,t120,t126,t246,t289]) else (if i < 111 then [t65,t77,t84,t120,t126,t246,t291] else [t65,t77,t84,t120,t126,t246,t294])))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then [t65,t77,t84,t120,t136,t246,t280] else [t65,t77,t84,t120,t139,t246,t280]) else (if i < 115 then [t65,t77,t84,t120,t144,t246,t280] else [t65,t77,t84,t120,t152,t246,t280])) else (if i < 118 then (if i < 117 then [t65,t77,t84,t120,t156,t246,t280] else [t65,t77,t84,t120,t187,t246,t280]) else (if i < 119 then [t65,t77,t84,t120,t246,t272,t280] else [t65,t77,t84,t120,t246,t280,t316]))) else (if i < 124 then (if i < 122 then (if i < 121 then [t65,t77,t84,t121,t126,t246,t280] else [t65,t77,t84,t122,t126,t246,t280]) else (if i < 123 then [t65,t77,t84,t123,t126,t246,t280] else [t65,t77,t84,t125,t126,t246,t280])) else (if i < 126 then (if i < 125 then [t65,t77,t84,t126,t170,t198,t280] else [t65,t77,t84,t126,t171,t198,t280]) else (if i < 127 then [t65,t77,t84,t126,t174,t198,t246] else [t65,t77,t84,t126,t192,t246,t280]))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then [t65,t77,t84,t126,t192,t246,t294] else [t65,t77,t84,t126,t193,t246,t280]) else (if i < 131 then [t65,t77,t84,t126,t194,t246,t280] else [t65,t77,t84,t126,t195,t246,t280])) else (if i < 134 then (if i < 133 then [t65,t77,t84,t126,t196,t246,t280] else [t65,t77,t84,t126,t197,t246,t280]) else (if i < 135 then [t65,t77,t84,t126,t198,t245,t280] else [t65,t77,t84,t126,t198,t246,t280]))) else (if i < 140 then (if i < 138 then (if i < 137 then [t65,t77,t84,t126,t198,t246,t281] else [t65,t77,t84,t126,t198,t246,t282]) else (if i < 139 then [t65,t77,t84,t126,t198,t246,t283] else [t65,t77,t84,t126,t198,t246,t284])) else (if i < 142 then (if i < 141 then [t65,t77,t84,t126,t198,t246,t285] else [t65,t77,t84,t126,t198,t246,t286]) else (if i < 143 then [t65,t77,t84,t126,t198,t246,t287] else [t65,t77,t84,t126,t198,t246,t288])))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then [t65,t77,t84,t126,t198,t246,t289] else [t65,t77,t84,t126,t198,t246,t291]) else (if i < 147 then [t65,t77,t84,t126,t198,t246,t294] else [t65,t77,t84,t126,t198,t246,t295])) else (if i < 150 then (if i < 149 then [t65,t77,t84,t126,t198,t246,t298] else [t65,t77,t84,t126,t198,t246,t299]) else (if i < 151 then [t65,t77,t84,t126,t198,t252,t291] else [t65,t77,t84,t126,t198,t256,t302,t310]))) else (if i < 156 then (if i < 154 then (if i < 153 then [t65,t77,t84,t126,t198,t264,t296] else [t65,t77,t84,t126,t199,t246,t280]) else (if i < 155 then [t65,t77,t84,t126,t200,t246,t280] else [t65,t77,t84,t126,t201,t246,t280])) else (if i < 158 then (if i < 157 then [t65,t77,t84,t126,t202,t246,t280] else [t65,t77,t84,t126,t203,t246,t280]) else (if i < 159 then [t65,t77,t84,t126,t204,t246,t280] else [t65,t77,t84,t126,t207,t246,t280]))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then [t65,t77,t84,t126,t207,t246,t291] else [t65,t77,t84,t126,t208,t246,t280]) else (if i < 163 then [t65,t77,t84,t126,t209,t246,t280] else [t65,t77,t84,t126,t209,t246,t289])) else (if i < 166 then (if i < 165 then [t65,t77,t84,t126,t210,t246,t280] else [t65,t77,t84,t126,t216,t246,t280]) else (if i < 167 then [t65,t77,t84,t126,t218,t246,t280] else [t65,t77,t84,t126,t219,t264,t280]))) else (if i < 172 then (if i < 170 then (if i < 169 then [t65,t77,t84,t126,t220,t246,t280] else [t65,t77,t84,t126,t233,t246,t280]) else (if i < 171 then [t65,t77,t84,t127,t198,t246,t280] else [t65,t77,t84,t128,t198,t246,t280])) else (if i < 174 then (if i < 173 then [t65,t77,t84,t129,t198,t246,t280] else [t65,t77,t84,t130,t198,t246,t280]) else (if i < 175 then [t65,t77,t84,t131,t198,t246,t280] else [t65,t77,t84,t132,t198,t246,t280])))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then [t65,t77,t84,t133,t198,t246,t280] else [t65,t77,t84,t134,t198,t246,t280]) else (if i < 179 then [t65,t77,t84,t135,t198,t246,t280] else [t65,t77,t84,t136,t198,t246,t280])) else (if i < 182 then (if i < 181 then [t65,t77,t84,t137,t198,t246,t280] else [t65,t77,t84,t138,t198,t246,t280]) else (if i < 183 then [t65,t77,t84,t139,t198,t246,t280] else [t65,t77,t84,t139,t198,t254,t280]))) else (if i < 188 then (if i < 186 then (if i < 185 then [t65,t77,t84,t139,t225,t246,t280] else [t65,t77,t84,t140,t198,t246,t280]) else (if i < 187 then [t65,t77,t84,t141,t198,t246,t280] else [t65,t77,t84,t142,t198,t246,t280])) else (if i < 190 then (if i < 189 then [t65,t77,t84,t143,t198,t246,t280] else [t65,t77,t84,t144,t198,t246,t280]) else (if i < 191 then [t65,t77,t84,t144,t198,t246,t291] else [t65,t77,t84,t144,t198,t252,t280])))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then [t65,t77,t84,t144,t207,t246,t280] else [t65,t77,t84,t145,t198,t246,t280]) else (if i < 195 then [t65,t77,t84,t146,t198,t246,t280] else [t65,t77,t84,t147,t198,t246,t280])) else (if i < 198 then (if i < 197 then [t65,t77,t84,t148,t198,t246,t308] else [t65,t77,t84,t148,t198,t258,t280]) else (if i < 199 then [t65,t77,t84,t149,t198,t246,t280] else [t65,t77,t84,t150,t198,t246,t280]))) else (if i < 204 then (if i < 202 then (if i < 201 then [t65,t77,t84,t151,t198,t246,t280] else [t65,t77,t84,t152,t198,t246,t280]) else (if i < 203 then [t65,t77,t84,t152,t198,t246,t289] else [t65,t77,t84,t152,t198,t259,t280])) else (if i < 206 then (if i < 205 then [t65,t77,t84,t152,t209,t246,t280] else [t65,t77,t84,t153,t198,t246,t280]) else (if i < 207 then [t65,t77,t84,t154,t198,t258,t280] else [t65,t77,t84,t155,t198,t246,t280])))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then [t65,t77,t84,t156,t198,t246,t280] else [t65,t77,t84,t156,t198,t246,t297]) else (if i < 211 then [t65,t77,t84,t156,t217,t246,t280] else [t65,t77,t84,t157,t198,t246,t280])) else (if i < 214 then (if i < 213 then [t65,t77,t84,t158,t198,t246,t280] else [t65,t77,t84,t160,t198,t246,t280]) else (if i < 215 then [t65,t77,t84,t164,t246,t280,t316] else [t65,t77,t84,t178,t198,t246,t280]))) else (if i < 220 then (if i < 218 then (if i < 217 then [t65,t77,t84,t180,t198,t246,t280] else [t65,t77,t84,t182,t198,t246,t280]) else (if i < 219 then [t65,t77,t84,t184,t198,t246,t280] else [t65,t77,t84,t185,t198,t246,t280])) else (if i < 222 then (if i < 221 then [t65,t77,t84,t186,t198,t246,t280] else [t65,t77,t84,t187,t192,t246,t280]) else (if i < 223 then [t65,t77,t84,t187,t193,t246,t280] else [t65,t77,t84,t187,t198,t246,t280]))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then [t65,t77,t84,t187,t198,t246,t289] else [t65,t77,t84,t187,t198,t246,t291]) else (if i < 227 then [t65,t77,t84,t187,t198,t246,t294] else [t65,t77,t84,t187,t198,t246,t297])) else (if i < 230 then (if i < 229 then [t65,t77,t84,t187,t198,t246,t308] else [t65,t77,t84,t187,t198,t252,t280]) else (if i < 231 then [t65,t77,t84,t187,t198,t254,t280] else [t65,t77,t84,t187,t198,t258,t280]))) else (if i < 236 then (if i < 234 then (if i < 233 then [t65,t77,t84,t187,t198,t264,t280] else [t65,t77,t84,t187,t198,t270,t280]) else (if i < 235 then [t65,t77,t84,t187,t204,t246,t280] else [t65,t77,t84,t187,t207,t246,t280])) else (if i < 238 then (if i < 237 then [t65,t77,t84,t187,t209,t246,t280] else [t65,t77,t84,t187,t215,t246,t280]) else (if i < 239 then [t65,t77,t84,t187,t217,t246,t280] else [t65,t77,t84,t187,t225,t246,t280])))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then [t65,t77,t84,t187,t232,t246,t280] else [t65,t77,t84,t187,t246,t280,t293]) else (if i < 243 then [t65,t77,t84,t188,t198,t246,t280] else [t65,t77,t84,t189,t198,t246,t280])) else (if i < 246 then (if i < 245 then [t65,t77,t84,t190,t198,t246,t280] else [t65,t77,t84,t191,t198,t246,t280]) else (if i < 247 then [t65,t77,t84,t192,t246,t280,t317] else [t65,t77,t84,t198,t211,t246,t280]))) else (if i < 252 then (if i < 250 then (if i < 249 then [t65,t77,t84,t198,t213,t246,t280] else [t65,t77,t84,t198,t221,t246,t280]) else (if i < 251 then [t65,t77,t84,t198,t223,t246,t280] else [t65,t77,t84,t198,t246,t271,t280])) else (if i < 254 then (if i < 253 then [t65,t77,t84,t198,t246,t272,t280] else [t65,t77,t84,t198,t246,t272,t294]) else (if i < 255 then [t65,t77,t84,t198,t246,t273,t280] else [t65,t77,t84,t198,t246,t274,t280])))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then [t65,t77,t84,t198,t246,t275,t280] else [t65,t77,t84,t198,t246,t280,t315]) else (if i < 259 then [t65,t77,t84,t198,t246,t280,t316] else [t65,t77,t84,t198,t246,t280,t317])) else (if i < 262 then (if i < 261 then [t65,t77,t84,t198,t246,t280,t318] else [t65,t77,t84,t198,t246,t308,t319]) else (if i < 263 then [t65,t77,t84,t198,t258,t280,t319] else [t65,t77,t84,t198,t264,t280,t316]))) else (if i < 268 then (if i < 266 then (if i < 265 then [t65,t77,t84,t219,t246,t280,t316] else [t65,t77,t84,t235,t246,t280,t316]) else (if i < 267 then [t65,t77,t84,t246,t277,t280,t293] else [t65,t77,t84,t246,t280,t293,t320])) else (if i < 270 then (if i < 269 then [t65,t77,t84,t246,t280,t296,t316] else [t65,t77,t85,t144,t198,t246,t280]) else (if i < 271 then [t65,t77,t85,t187,t198,t246,t280] else [t65,t77,t86,t187,t198,t246,t280])))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then [t65,t77,t87,t187,t198,t246,t280] else [t65,t77,t91,t156,t198,t246,t280]) else (if i < 275 then [t65,t77,t91,t187,t198,t246,t280] else [t65,t77,t95,t187,t198,t246,t301])) else (if i < 278 then (if i < 277 then [t65,t77,t100,t187,t198,t246,t280] else [t65,t77,t118,t187,t198,t246,t280]) else (if i < 279 then [t65,t77,t118,t198,t246,t277,t280] else [t65,t77,t120,t187,t246,t280,t301]))) else (if i < 284 then (if i < 282 then (if i < 281 then [t65,t77,t173,t187,t198,t246,t280] else [t65,t77,t173,t198,t246,t272,t280]) else (if i < 283 then [t65,t77,t187,t198,t229,t246,t280] else [t65,t77,t187,t198,t230,t246,t280])) else (if i < 286 then (if i < 285 then [t65,t77,t187,t198,t246,t280,t301] else [t65,t79,t84,t152,t198,t246,t280]) else (if i < 287 then [t65,t79,t84,t187,t198,t246,t280] else [t65,t79,t126,t198,t246,t280,t301]))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then [t65,t79,t126,t198,t246,t280,t310] else [t65,t81,t84,t187,t198,t246,t280]) else (if i < 291 then [t65,t81,t91,t126,t198,t246,t280] else [t65,t81,t126,t198,t246,t280,t301])) else (if i < 294 then (if i < 293 then [t65,t84,t95,t187,t198,t246,t306] else [t65,t84,t99,t187,t198,t246,t280]) else (if i < 295 then [t65,t84,t109,t187,t198,t246,t280] else [t65,t84,t109,t198,t246,t277,t280]))) else (if i < 300 then (if i < 298 then (if i < 297 then [t65,t84,t110,t187,t198,t280,t306] else [t65,t84,t112,t187,t198,t246,t280]) else (if i < 299 then [t65,t84,t112,t198,t246,t277,t280] else [t65,t84,t112,t198,t246,t280,t320])) else (if i < 302 then (if i < 301 then [t65,t84,t120,t187,t246,t280,t306] else [t65,t84,t172,t187,t198,t246,t280]) else (if i < 303 then [t65,t84,t172,t198,t246,t272,t280] else [t65,t84,t187,t198,t222,t246,t280])))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then [t65,t84,t187,t198,t246,t280,t306] else [t65,t84,t198,t222,t246,t280,t316]) else (if i < 307 then [t65,t85,t126,t148,t198,t246,t280] else [t65,t85,t126,t198,t246,t280,t306])) else (if i < 310 then (if i < 309 then [t65,t86,t126,t198,t246,t280,t306] else [t65,t91,t126,t198,t246,t280,t306]) else (if i < 311 then [t65,t95,t126,t198,t246,t301,t306] else [t65,t120,t126,t246,t280,t301,t306]))) else (if i < 316 then (if i < 314 then (if i < 313 then [t65,t126,t172,t173,t198,t246,t280] else [t65,t126,t172,t198,t246,t280,t301]) else (if i < 315 then [t65,t126,t173,t198,t246,t280,t306] else [t65,t126,t198,t246,t280,t301,t306])) else (if i < 318 then (if i < 317 then [t65,t187,t198,t246,t280,t301,t306] else [t1,t65,t77,t84,t95,t126,t198,t246]) else (if i < 319 then [t1,t65,t77,t84,t120,t126,t246,t280] else [t1,t65,t77,t84,t126,t198,t246,t280])))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then [t1,t65,t77,t84,t187,t198,t246,t280] else [t2,t65,t77,t84,t126,t198,t246,t280]) else (if i < 323 then [t3,t65,t77,t84,t126,t198,t246,t280] else [t4,t65,t77,t84,t126,t198,t246,t280])) else (if i < 326 then (if i < 325 then [t5,t65,t77,t84,t126,t198,t246,t280] else [t6,t65,t77,t84,t126,t198,t246,t280]) else (if i < 327 then [t7,t65,t77,t84,t126,t198,t246,t280] else [t8,t65,t77,t84,t126,t198,t246,t280]))) else (if i < 332 then (if i < 330 then (if i < 329 then [t9,t65,t77,t84,t126,t198,t246,t280] else [t10,t65,t77,t84,t126,t198,t246,t280]) else (if i < 331 then [t11,t65,t77,t84,t126,t198,t246,t280] else [t12,t65,t77,t84,t95,t126,t198,t246])) else (if i < 334 then (if i < 333 then [t12,t65,t77,t84,t110,t126,t198,t280] else [t12,t65,t77,t84,t120,t126,t246,t280]) else (if i < 335 then [t12,t65,t77,t84,t126,t198,t246,t280] else [t12,t65,t77,t84,t126,t198,t256,t280])))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then [t12,t65,t77,t84,t136,t198,t246,t280] else [t12,t65,t77,t84,t187,t198,t246,t280]) else (if i < 339 then [t12,t65,t77,t126,t198,t246,t280,t301] else [t12,t65,t84,t126,t198,t246,t256,t280])) else (if i < 342 then (if i < 341 then [t12,t65,t84,t126,t198,t246,t280,t306] else [t12,t77,t84,t126,t198,t246,t280,t312]) else (if i < 343 then [t13,t65,t77,t84,t95,t126,t198,t246] else [t13,t65,t77,t84,t120,t126,t246,t280]))) else (if i < 348 then (if i < 346 then (if i < 345 then [t13,t65,t77,t84,t126,t198,t246,t280] else [t13,t65,t77,t84,t126,t204,t246,t280]) else (if i < 347 then [t13,t65,t77,t84,t187,t198,t246,t280] else [t13,t65,t77,t103,t126,t198,t246,t280])) else (if i < 350 then (if i < 349 then [t13,t65,t77,t126,t198,t246,t280,t301] else [t14,t65,t77,t84,t126,t198,t246,t280]) else (if i < 351 then [t15,t65,t77,t84,t95,t126,t198,t246] else [t15,t65,t77,t84,t110,t126,t198,t280]))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then [t15,t65,t77,t84,t120,t126,t246,t280] else [t15,t65,t77,t84,t126,t198,t246,t280]) else (if i < 355 then [t15,t65,t77,t84,t187,t198,t246,t280] else [t15,t65,t77,t94,t126,t198,t246,t280])) else (if i < 358 then (if i < 357 then [t15,t65,t77,t126,t198,t246,t280,t301] else [t16,t65,t77,t84,t126,t198,t246,t280]) else (if i < 359 then [t17,t65,t77,t84,t126,t198,t246,t280] else [t18,t65,t77,t84,t95,t126,t198,t246]))) else (if i < 364 then (if i < 362 then (if i < 361 then [t18,t65,t77,t84,t110,t126,t198,t280] else [t18,t65,t77,t84,t120,t126,t246,t280]) else (if i < 363 then [t18,t65,t77,t84,t126,t198,t246,t280] else [t18,t65,t77,t84,t126,t227,t246,t280])) else (if i < 366 then (if i < 365 then [t18,t65,t77,t84,t187,t198,t246,t280] else [t18,t65,t77,t126,t198,t246,t280,t301]) else (if i < 367 then [t18,t65,t84,t126,t198,t227,t246,t280] else [t18,t65,t84,t126,t198,t246,t280,t306])))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then [t18,t77,t84,t126,t198,t246,t280,t312] else [t19,t65,t77,t84,t126,t198,t246,t280]) else (if i < 371 then [t20,t65,t77,t84,t126,t198,t246,t280] else [t21,t65,t77,t84,t126,t198,t246,t280])) else (if i < 374 then (if i < 373 then [t22,t65,t77,t84,t126,t198,t246,t280] else [t23,t65,t77,t84,t126,t198,t246,t280]) else (if i < 375 then [t23,t65,t77,t84,t187,t198,t246,t280] else [t24,t65,t77,t84,t126,t198,t246,t280]))) else (if i < 380 then (if i < 378 then (if i < 377 then [t25,t65,t77,t84,t126,t198,t246,t280] else [t26,t65,t77,t84,t126,t198,t246,t280]) else (if i < 379 then [t27,t49,t77,t84,t126,t198,t246,t280] else [t27,t65,t77,t84,t95,t126,t198,t246])) else (if i < 382 then (if i < 381 then [t27,t65,t77,t84,t120,t126,t246,t280] else [t27,t65,t77,t84,t126,t198,t246,t280]) else (if i < 383 then [t27,t65,t77,t84,t126,t198,t246,t291] else [t27,t65,t77,t84,t126,t207,t246,t280]))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then [t27,t65,t77,t84,t144,t198,t246,t280] else [t27,t65,t77,t84,t187,t198,t246,t280]) else (if i < 387 then [t27,t65,t82,t84,t126,t198,t246,t280] else [t27,t65,t84,t126,t148,t198,t246,t280])) else (if i < 390 then (if i < 389 then [t27,t65,t84,t126,t198,t227,t246,t280] else [t27,t65,t84,t126,t198,t246,t280,t306]) else (if i < 391 then [t28,t65,t77,t84,t95,t126,t198,t246] else [t28,t65,t77,t84,t126,t198,t246,t280]))) else (if i < 396 then (if i < 394 then (if i < 393 then [t29,t65,t77,t84,t126,t198,t246,t280] else [t30,t65,t77,t84,t126,t198,t246,t280]) else (if i < 395 then [t31,t65,t77,t84,t126,t198,t246,t280] else [t32,t65,t77,t84,t126,t198,t246,t280])) else (if i < 398 then (if i < 397 then [t35,t65,t77,t84,t95,t126,t198,t246] else [t35,t65,t77,t84,t110,t126,t198,t280]) else (if i < 399 then [t35,t65,t77,t84,t120,t126,t246,t280] else [t35,t65,t77,t84,t126,t198,t246,t280])))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then [t35,t65,t77,t84,t126,t198,t246,t289] else [t35,t65,t77,t84,t126,t198,t259,t280]) else (if i < 403 then [t35,t65,t77,t84,t126,t209,t246,t280] else [t35,t65,t77,t84,t152,t198,t246,t280])) else (if i < 406 then (if i < 405 then [t35,t65,t77,t84,t187,t198,t246,t280] else [t35,t65,t77,t126,t198,t246,t259,t280]) else (if i < 407 then [t35,t65,t77,t126,t198,t246,t280,t301] else [t35,t65,t77,t126,t198,t246,t280,t310]))) else (if i < 412 then (if i < 410 then (if i < 409 then [t35,t65,t79,t84,t126,t198,t246,t280] else [t35,t65,t84,t126,t198,t246,t280,t306]) else (if i < 411 then [t35,t71,t77,t84,t126,t198,t246,t280] else [t35,t77,t84,t126,t198,t246,t280,t312])) else (if i < 414 then (if i < 413 then [t36,t65,t77,t84,t126,t198,t246,t280] else [t37,t65,t77,t84,t126,t198,t246,t280]) else (if i < 415 then [t38,t65,t77,t84,t126,t198,t246,t280] else [t39,t65,t77,t84,t126,t198,t246,t280]))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then [t40,t65,t77,t84,t126,t198,t246,t280] else [t40,t65,t77,t84,t187,t198,t246,t280]) else (if i < 419 then [t41,t65,t77,t84,t126,t198,t246,t280] else [t42,t65,t77,t84,t126,t198,t246,t280])) else (if i < 422 then (if i < 421 then [t43,t65,t77,t84,t126,t198,t246,t280] else [t43,t65,t77,t84,t187,t198,t246,t280]) else (if i < 423 then [t44,t65,t77,t84,t126,t198,t246,t280] else [t46,t65,t77,t84,t126,t198,t246,t280]))) else (if i < 428 then (if i < 426 then (if i < 425 then [t47,t65,t77,t84,t95,t126,t198,t246] else [t47,t65,t77,t84,t126,t198,t246,t280]) else (if i < 427 then [t48,t65,t77,t84,t95,t126,t198,t246] else [t48,t65,t77,t84,t126,t198,t246,t280])) else (if i < 430 then (if i < 429 then [t50,t65,t77,t84,t126,t198,t246,t280] else [t51,t65,t77,t84,t120,t126,t246,t280]) else (if i < 431 then [t51,t65,t77,t84,t126,t198,t246,t280] else [t52,t65,t77,t84,t126,t198,t246,t280])))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then [t52,t77,t84,t126,t198,t246,t256,t280] else [t52,t77,t84,t126,t198,t246,t280]) else (if i < 435 then [t65,t65,t77,t84,t95,t126,t198,t246] else [t65,t65,t77,t84,t110,t126,t198,t280])) else (if i < 438 then (if i < 437 then [t65,t65,t77,t84,t120,t126,t246,t280] else [t65,t65,t77,t84,t126,t198,t246,t280]) else (if i < 439 then [t65,t65,t77,t84,t187,t198,t246,t280] else [t65,t65,t77,t126,t198,t246,t280,t301]))) else (if i < 444 then (if i < 442 then (if i < 441 then [t65,t65,t84,t126,t198,t246,t280,t306] else [t65,t66,t77,t84,t126,t198,t246,t280]) else (if i < 443 then [t65,t67,t77,t84,t126,t198,t246,t280] else [t65,t68,t77,t84,t126,t198,t246,t280])) else (if i < 446 then (if i < 445 then [t65,t69,t77,t84,t126,t198,t246,t280] else [t65,t70,t77,t84,t126,t198,t246,t280]) else (if i < 447 then [t65,t71,t77,t84,t126,t198,t246,t280] else [t65,t72,t77,t84,t126,t198,t246,t280])))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then [t65,t73,t77,t84,t95,t126,t198,t246] else [t65,t73,t77,t84,t126,t198,t246,t280]) else (if i < 451 then [t65,t74,t77,t84,t126,t198,t246,t280] else [t65,t76,t77,t84,t126,t198,t246,t280])) else (if i < 454 then (if i < 453 then [t65,t77,t78,t84,t126,t198,t246,t280] else [t65,t77,t79,t84,t126,t198,t246,t280]) else (if i < 455 then [t65,t77,t80,t84,t126,t198,t246,t280] else [t65,t77,t81,t84,t126,t198,t246,t280]))) else (if i < 460 then (if i < 458 then (if i < 457 then [t65,t77,t82,t84,t95,t126,t198,t246] else [t65,t77,t82,t84,t120,t126,t246,t280]) else (if i < 459 then [t65,t77,t82,t84,t126,t198,t246,t280] else [t65,t77,t82,t84,t187,t198,t246,t280])) else (if i < 462 then (if i < 461 then [t65,t77,t83,t84,t126,t198,t246,t280] else [t65,t77,t84,t85,t126,t198,t246,t280]) else (if i < 463 then [t65,t77,t84,t89,t126,t198,t246,t280] else [t65,t77,t84,t94,t95,t126,t198,t246])))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then [t65,t77,t84,t94,t110,t126,t198,t280] else [t65,t77,t84,t94,t120,t126,t246,t280]) else (if i < 467 then [t65,t77,t84,t94,t126,t198,t246,t280] else [t65,t77,t84,t94,t126,t198,t246,t280,t302])) else (if i < 470 then (if i < 469 then [t65,t77,t84,t94,t187,t198,t246,t280] else [t65,t77,t84,t95,t95,t126,t198,t246]) else (if i < 471 then [t65,t77,t84,t95,t98,t126,t198,t246] else [t65,t77,t84,t95,t103,t126,t198,t246]))) else (if i < 476 then (if i < 474 then (if i < 473 then [t65,t77,t84,t95,t105,t126,t198,t246] else [t65,t77,t84,t95,t110,t126,t198]) else (if i < 475 then [t65,t77,t84,t95,t110,t126,t198,t246] else [t65,t77,t84,t95,t120,t126,t198,t246])) else (if i < 478 then (if i < 477 then [t65,t77,t84,t95,t120,t126,t246] else [t65,t77,t84,t95,t120,t126,t246,t280]) else (if i < 479 then [t65,t77,t84,t95,t126,t164,t198,t246] else [t65,t77,t84,t95,t126,t175,t198,t246]))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then [t65,t77,t84,t95,t126,t187,t198,t246] else [t65,t77,t84,t95,t126,t198,t198,t246]) else (if i < 483 then [t65,t77,t84,t95,t126,t198,t219,t246] else [t65,t77,t84,t95,t126,t198,t227,t246])) else (if i < 486 then (if i < 485 then [t65,t77,t84,t95,t126,t198,t236,t246] else [t65,t77,t84,t95,t126,t198,t240,t246]) else (if i < 487 then [t65,t77,t84,t95,t126,t198,t246] else [t65,t77,t84,t95,t126,t198,t246,t246]))) else (if i < 492 then (if i < 490 then (if i < 489 then [t65,t77,t84,t95,t126,t198,t246,t253] else [t65,t77,t84,t95,t126,t198,t246,t256]) else (if i < 491 then [t65,t77,t84,t95,t126,t198,t246,t260] else [t65,t77,t84,t95,t126,t198,t246,t265])) else (if i < 494 then (if i < 493 then [t65,t77,t84,t95,t126,t198,t246,t280] else [t65,t77,t84,t95,t126,t198,t246,t292]) else (if i < 495 then [t65,t77,t84,t95,t126,t198,t246,t296] else [t65,t77,t84,t95,t126,t198,t246,t300])))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then [t65,t77,t84,t95,t126,t198,t246,t301] else [t65,t77,t84,t95,t126,t198,t246,t302]) else (if i < 499 then [t65,t77,t84,t95,t126,t198,t246,t321] else [t65,t77,t84,t95,t187,t198,t246])) else (if i < 502 then (if i < 501 then [t65,t77,t84,t95,t187,t198,t246,t280] else [t65,t77,t84,t98,t126,t198,t246,t280]) else (if i < 503 then [t65,t77,t84,t103,t120,t126,t246,t280] else [t65,t77,t84,t103,t126,t198,t246,t280]))) else (if i < 508 then (if i < 506 then (if i < 505 then [t65,t77,t84,t103,t126,t198,t246,t280,t302] else [t65,t77,t84,t103,t187,t198,t246,t280]) else (if i < 507 then [t65,t77,t84,t104,t126,t198,t246,t280] else [t65,t77,t84,t105,t126,t198,t246,t280])) else (if i < 510 then (if i < 509 then [t65,t77,t84,t107,t120,t126,t246,t280] else [t65,t77,t84,t107,t126,t198,t246,t280]) else (if i < 511 then [t65,t77,t84,t110,t187,t198,t246,t280] else [t65,t77,t84,t110,t187,t198,t280]))))))))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then [t65,t77,t84,t111,t126,t198,t246,t280] else [t65,t77,t84,t120,t120,t126,t246,t280]) else (if i < 515 then [t65,t77,t84,t120,t124,t126,t246,t280] else [t65,t77,t84,t120,t126,t164,t246,t280])) else (if i < 518 then (if i < 517 then [t65,t77,t84,t120,t126,t187,t246,t280] else [t65,t77,t84,t120,t126,t198,t246,t280]) else (if i < 519 then [t65,t77,t84,t120,t126,t219,t246,t280] else [t65,t77,t84,t120,t126,t240,t246,t280]))) else (if i < 524 then (if i < 522 then (if i < 521 then [t65,t77,t84,t120,t126,t246,t246,t280] else [t65,t77,t84,t120,t126,t246,t253,t280]) else (if i < 523 then [t65,t77,t84,t120,t126,t246,t256,t280] else [t65,t77,t84,t120,t126,t246,t265,t280])) else (if i < 526 then (if i < 525 then [t65,t77,t84,t120,t126,t246,t278,t280] else [t65,t77,t84,t120,t126,t246,t280]) else (if i < 527 then [t65,t77,t84,t120,t126,t246,t280,t302] else [t65,t77,t84,t120,t126,t246,t280,t321])))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then [t65,t77,t84,t120,t187,t198,t246,t280] else [t65,t77,t84,t120,t187,t246,t280]) else (if i < 531 then [t65,t77,t84,t124,t126,t198,t246,t280] else [t65,t77,t84,t126,t161,t198,t246,t280])) else (if i < 534 then (if i < 533 then [t65,t77,t84,t126,t162,t198,t246,t280] else [t65,t77,t84,t126,t163,t198,t246,t280]) else (if i < 535 then [t65,t77,t84,t126,t164,t175,t246,t280] else [t65,t77,t84,t126,t164,t198,t246,t280]))) else (if i < 540 then (if i < 538 then (if i < 537 then [t65,t77,t84,t126,t164,t198,t246,t294] else [t65,t77,t84,t126,t164,t198,t265,t280]) else (if i < 539 then [t65,t77,t84,t126,t164,t227,t246,t280] else [t65,t77,t84,t126,t164,t246,t265,t280])) else (if i < 542 then (if i < 541 then [t65,t77,t84,t126,t165,t198,t246,t280] else [t65,t77,t84,t126,t166,t198,t246,t280]) else (if i < 543 then [t65,t77,t84,t126,t167,t198,t246,t280] else [t65,t77,t84,t126,t168,t198,t246,t280]))))) else (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then [t65,t77,t84,t126,t169,t198,t246,t280] else [t65,t77,t84,t126,t172,t198,t246,t280]) else (if i < 547 then [t65,t77,t84,t126,t176,t198,t246,t280] else [t65,t77,t84,t126,t177,t198,t246,t280])) else (if i < 550 then (if i < 549 then [t65,t77,t84,t126,t179,t198,t246,t280] else [t65,t77,t84,t126,t181,t198,t246,t280]) else (if i < 551 then [t65,t77,t84,t126,t183,t198,t246,t280] else [t65,t77,t84,t126,t187,t198,t246,t280]))) else (if i < 556 then (if i < 554 then (if i < 553 then [t65,t77,t84,t126,t192,t198,t246,t280] else [t65,t77,t84,t126,t192,t246,t280]) else (if i < 555 then [t65,t77,t84,t126,t192,t246,t280,t302] else [t65,t77,t84,t126,t198,t198,t246,t280])) else (if i < 558 then (if i < 557 then [t65,t77,t84,t126,t198,t204,t246,t280] else [t65,t77,t84,t126,t198,t205,t246,t280]) else (if i < 559 then [t65,t77,t84,t126,t198,t206,t246,t280] else [t65,t77,t84,t126,t198,t207,t246,t280])))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then [t65,t77,t84,t126,t198,t209,t246,t280] else [t65,t77,t84,t126,t198,t212,t246,t280]) else (if i < 563 then [t65,t77,t84,t126,t198,t214,t246,t280] else [t65,t77,t84,t126,t198,t219,t246,t280])) else (if i < 566 then (if i < 565 then [t65,t77,t84,t126,t198,t224,t246,t280] else [t65,t77,t84,t126,t198,t228,t246,t280]) else (if i < 567 then [t65,t77,t84,t126,t198,t231,t246,t280] else [t65,t77,t84,t126,t198,t236,t246,t280]))) else (if i < 572 then (if i < 570 then (if i < 569 then [t65,t77,t84,t126,t198,t237,t246,t280] else [t65,t77,t84,t126,t198,t238,t246,t280]) else (if i < 571 then [t65,t77,t84,t126,t198,t239,t246,t280] else [t65,t77,t84,t126,t198,t240,t246,t280])) else (if i < 574 then (if i < 573 then [t65,t77,t84,t126,t198,t240,t246,t302] else [t65,t77,t84,t126,t198,t241,t246,t280]) else (if i < 575 then [t65,t77,t84,t126,t198,t242,t246,t280] else [t65,t77,t84,t126,t198,t243,t246,t280])))))) else (if i < 608 then (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then [t65,t77,t84,t126,t198,t244,t246,t280] else [t65,t77,t84,t126,t198,t246,t246,t280]) else (if i < 579 then [t65,t77,t84,t126,t198,t246,t247,t280] else [t65,t77,t84,t126,t198,t246,t248,t280])) else (if i < 582 then (if i < 581 then [t65,t77,t84,t126,t198,t246,t249,t280] else [t65,t77,t84,t126,t198,t246,t250,t280]) else (if i < 583 then [t65,t77,t84,t126,t198,t246,t251,t280] else [t65,t77,t84,t126,t198,t246,t252,t280]))) else (if i < 588 then (if i < 586 then (if i < 585 then [t65,t77,t84,t126,t198,t246,t253,t280] else [t65,t77,t84,t126,t198,t246,t254,t280]) else (if i < 587 then [t65,t77,t84,t126,t198,t246,t255,t280] else [t65,t77,t84,t126,t198,t246,t256,t280])) else (if i < 590 then (if i < 589 then [t65,t77,t84,t126,t198,t246,t256,t280,t310] else [t65,t77,t84,t126,t198,t246,t257,t280]) else (if i < 591 then [t65,t77,t84,t126,t198,t246,t260,t280] else [t65,t77,t84,t126,t198,t246,t261,t280])))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then [t65,t77,t84,t126,t198,t246,t262,t280] else [t65,t77,t84,t126,t198,t246,t263,t280]) else (if i < 595 then [t65,t77,t84,t126,t198,t246,t264,t280] else [t65,t77,t84,t126,t198,t246,t265,t280])) else (if i < 598 then (if i < 597 then [t65,t77,t84,t126,t198,t246,t266,t280] else [t65,t77,t84,t126,t198,t246,t267,t280]) else (if i < 599 then [t65,t77,t84,t126,t198,t246,t268,t280] else [t65,t77,t84,t126,t198,t246,t269,t280]))) else (if i < 604 then (if i < 602 then (if i < 601 then [t65,t77,t84,t126,t198,t246,t278,t280] else [t65,t77,t84,t126,t198,t246,t279,t280]) else (if i < 603 then [t65,t77,t84,t126,t198,t246,t280] else [t65,t77,t84,t126,t198,t246,t280,t290])) else (if i < 606 then (if i < 605 then [t65,t77,t84,t126,t198,t246,t280,t302] else [t65,t77,t84,t126,t198,t246,t280,t303]) else (if i < 607 then [t65,t77,t84,t126,t198,t246,t280,t304] else [t65,t77,t84,t126,t198,t246,t280,t305]))))) else (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then [t65,t77,t84,t126,t198,t246,t280,t307] else [t65,t77,t84,t126,t198,t246,t280,t313]) else (if i < 611 then [t65,t77,t84,t126,t198,t246,t280,t314] else [t65,t77,t84,t126,t198,t246,t280,t321])) else (if i < 614 then (if i < 613 then [t65,t77,t84,t126,t198,t246,t289] else [t65,t77,t84,t126,t198,t246,t291]) else (if i < 615 then [t65,t77,t84,t126,t198,t246,t292,t300] else [t65,t77,t84,t126,t198,t246,t294]))) else (if i < 620 then (if i < 618 then (if i < 617 then [t65,t77,t84,t126,t198,t246,t296,t302] else [t65,t77,t84,t126,t198,t246,t300,t302]) else (if i < 619 then [t65,t77,t84,t126,t204,t246,t280] else [t65,t77,t84,t126,t207,t246,t280])) else (if i < 622 then (if i < 621 then [t65,t77,t84,t126,t209,t246,t280] else [t65,t77,t84,t126,t219,t227,t246,t280]) else (if i < 623 then [t65,t77,t84,t126,t219,t246,t265,t280] else [t65,t77,t84,t126,t219,t246,t280,t319])))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then [t65,t77,t84,t136,t198,t246,t280] else [t65,t77,t84,t139,t198,t246,t280]) else (if i < 627 then [t65,t77,t84,t144,t198,t246,t280] else [t65,t77,t84,t148,t159,t198,t246,t280])) else (if i < 630 then (if i < 629 then [t65,t77,t84,t148,t187,t198,t246,t280] else [t65,t77,t84,t148,t198,t246,t277,t280]) else (if i < 631 then [t65,t77,t84,t148,t198,t246,t280,t320] else [t65,t77,t84,t152,t198,t246,t280]))) else (if i < 636 then (if i < 634 then (if i < 633 then [t65,t77,t84,t154,t187,t198,t246,t280] else [t65,t77,t84,t154,t198,t246,t277,t280]) else (if i < 635 then [t65,t77,t84,t156,t198,t246,t280] else [t65,t77,t84,t159,t187,t198,t246,t280])) else (if i < 638 then (if i < 637 then [t65,t77,t84,t159,t198,t246,t277,t280] else [t65,t77,t84,t163,t187,t198,t246,t280]) else (if i < 639 then [t65,t77,t84,t164,t187,t198,t246,t280] else [t65,t77,t84,t164,t198,t246,t272,t280]))))))) else (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then [t65,t77,t84,t175,t187,t198,t246,t280] else [t65,t77,t84,t175,t198,t246,t280,t316]) else (if i < 643 then [t65,t77,t84,t176,t187,t198,t246,t280] else [t65,t77,t84,t181,t187,t198,t246,t280])) else (if i < 646 then (if i < 645 then [t65,t77,t84,t187,t187,t198,t246,t280] else [t65,t77,t84,t187,t198,t198,t246,t280]) else (if i < 647 then [t65,t77,t84,t187,t198,t212,t246,t280] else [t65,t77,t84,t187,t198,t214,t246,t280]))) else (if i < 652 then (if i < 650 then (if i < 649 then [t65,t77,t84,t187,t198,t219,t246,t280] else [t65,t77,t84,t187,t198,t224,t246,t280]) else (if i < 651 then [t65,t77,t84,t187,t198,t227,t246,t280] else [t65,t77,t84,t187,t198,t231,t246,t280])) else (if i < 654 then (if i < 653 then [t65,t77,t84,t187,t198,t235,t246,t280] else [t65,t77,t84,t187,t198,t240,t246,t280]) else (if i < 655 then [t65,t77,t84,t187,t198,t246,t246,t280] else [t65,t77,t84,t187,t198,t246,t253,t280])))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then [t65,t77,t84,t187,t198,t246,t256,t280] else [t65,t77,t84,t187,t198,t246,t259,t280]) else (if i < 659 then [t65,t77,t84,t187,t198,t246,t265,t280] else [t65,t77,t84,t187,t198,t246,t266,t280])) else (if i < 662 then (if i < 661 then [t65,t77,t84,t187,t198,t246,t277,t280] else [t65,t77,t84,t187,t198,t246,t280]) else (if i < 663 then [t65,t77,t84,t187,t198,t246,t280,t280] else [t65,t77,t84,t187,t198,t246,t280,t290]))) else (if i < 668 then (if i < 666 then (if i < 665 then [t65,t77,t84,t187,t198,t246,t280,t292] else [t65,t77,t84,t187,t198,t246,t280,t296]) else (if i < 667 then [t65,t77,t84,t187,t198,t246,t280,t300] else [t65,t77,t84,t187,t198,t246,t280,t301])) else (if i < 670 then (if i < 669 then [t65,t77,t84,t187,t198,t246,t280,t302] else [t65,t77,t84,t187,t198,t246,t280,t306]) else (if i < 671 then [t65,t77,t84,t187,t198,t246,t280,t310] else [t65,t77,t84,t187,t198,t246,t280,t312]))))) else (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then [t65,t77,t84,t187,t198,t246,t280,t319] else [t65,t77,t84,t187,t198,t246,t280,t320]) else (if i < 675 then [t65,t77,t84,t187,t198,t246,t280,t321] else [t65,t77,t84,t198,t246,t272,t280])) else (if i < 678 then (if i < 677 then [t65,t77,t84,t198,t246,t277,t280,t319] else [t65,t77,t84,t198,t246,t280,t316]) else (if i < 679 then [t65,t77,t84,t198,t246,t280,t319,t320] else [t65,t77,t187,t198,t246,t280,t301]))) else (if i < 684 then (if i < 682 then (if i < 681 then [t65,t84,t187,t198,t246,t280,t306] else [t65,t126,t198,t246,t280,t301,t306]) else (if i < 683 then [t12,t65,t77,t84,t126,t198,t246,t280] else [t13,t65,t77,t84,t126,t198,t246,t280])) else (if i < 686 then (if i < 685 then [t15,t65,t77,t84,t126,t198,t246,t280] else [t18,t65,t77,t84,t126,t198,t246,t280]) else (if i < 687 then [t27,t65,t77,t84,t126,t198,t246,t280] else [t35,t65,t77,t84,t126,t198,t246,t280])))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then [t65,t65,t77,t84,t126,t198,t246,t280] else [t65,t77,t82,t84,t126,t198,t246,t280]) else (if i < 691 then [t65,t77,t84,t94,t126,t198,t246,t280] else [t65,t77,t84,t95,t126,t198,t246])) else (if i < 694 then (if i < 693 then [t65,t77,t84,t95,t126,t198,t246,t280] else [t65,t77,t84,t103,t126,t198,t246,t280]) else (if i < 695 then [t65,t77,t84,t120,t126,t198,t246,t280] else [t65,t77,t84,t120,t126,t246,t280]))) else (if i < 700 then (if i < 698 then (if i < 697 then [t65,t77,t84,t126,t164,t198,t246,t280] else [t65,t77,t84,t126,t187,t198,t246,t280]) else (if i < 699 then [t65,t77,t84,t126,t198,t198,t246,t280] else [t65,t77,t84,t126,t198,t219,t246,t280])) else (if i < 702 then (if i < 701 then [t65,t77,t84,t126,t198,t240,t246,t280] else [t65,t77,t84,t126,t198,t246,t246,t280]) else (if i < 703 then [t65,t77,t84,t126,t198,t246,t253,t280] else [t65,t77,t84,t126,t198,t246,t256,t280])))))) else (if i < 736 then (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then [t65,t77,t84,t126,t198,t246,t265,t280] else [t65,t77,t84,t126,t198,t246,t280]) else (if i < 707 then [t65,t77,t84,t126,t198,t246,t280,t302] else [t65,t77,t84,t187,t198,t246,t280])) else (if i < 710 then (if i < 709 then [t65,t77,t84,t126,t198,t246,t280] else []) else [])) else []) else []) else []))) else []))

def sixE (i : Nat) : Nat :=
  let w : Nat := (if i < 128 then (if i < 64 then (if i < 32 then 0x334dd35dbb6fdce370dd369c26b5c733cc1371b871dc5334dd35dcc6c1ce374c7379ae735cc374df2c99a6e1cc374df379ae735cc324cf369c26b5c9304dd35db66c1ce370c935d2e6d99331cc934db96d9c8164e127dae6fdbd31cdd361b25a1ce37cdd2c9b86b9cc34ccd35db06d9ce334d335db66c1ce334dd35dc46c1ce33cc1371b86e5c537cdd2c9b8669cc334e535db66c1ce31cc936dc6711c833cdd35db66c1ce334dd369b86a5ce334dd35dbb6c1ce31cdd35db66c1ce304dd369b86a5ce334dd35db66fdce31cdd379cd6b9cc37cdd379cd6b9cc374cd35db06d9ce33459371c6735cb334dd35db66c1ce else 0x31cdd369b86a5ce324dd369b86a5ce32459371c6735cb33459371c6739cb33459371bd735cb31cdc379cd6b9cc37cdc379cd6b9cc334dc35db66c1ce37cdc2c9b8669cc334dc369b86a5ce374c735db06d9ce374cf35db06d9ce384d831d68669bd374cd35db0711ce374cd35db06edce33cc934dc66d9c8324dd35db66c1ce33cc9371b86e5c531cdd379ce6b9cc31cc936dbd711c837cdd379ce6b9cc3845927dbf6b9bd34cd835d2e6d972334dd35db672dce37cdd379cd721cc334d3371c6735cb334dd35dc46fdce2d4dd35db66fdce334d335db66fdce334e535db63d1ce2d4c1371b86e5c5374cd35dbf6d9ce) else (if i < 96 then 0x334e535dc46c1ce334dd37dbb6c1ce334e5369b86a5ce31cc934dc66d9c831cc934dbd6d9c831cc9375c66edc8294c9375c96edc831cc9375b96edc8364dd379cd6b9cc304d335db66c1ce334dd35da76c1ce374cd361a96e1ce334d8371c6735cb33cdd35db66a5ce164cd371cd719cb334dd361b86a5ce374cd35da96d9ce33cdd379cd669cc37cdd379b86b9cc33cde36dc6711c83845931dbf6b9bd3845933db0669bd37cdd379b8669cc334dd35db66a5ce304e5361b86a5ce334e5361c46fdce304d8371c6735cb364e5379b8669cc304e535dc46fdce334dd35db6689ce364dd2c9b8669cc334dd35db63d1ce else 0x374c7369a9711ce31ca5371c6735cb33cc7371b86e5c5374c7369a96e1ce334dd35db64f9ce334dd35db26c1ce34cd835d2e6d9b8324d831d68669bd370c92d5c26c193374cf35db06edce324dd35dbb6c1ce334d3369b86a5ce374d835d2e6edb833cdd35dbb6c1ce31ce535dc46fdce384d833dbf6b9bd364e52c9b8669cc304e535dc472dce304db35dc46fdce304e535dcc6fdce31ce5379cd6b9cc364e5379cd6b9cc304dc369b86a5ce304e5369b86a5ce364e5379ca669cc394c135dbf711ce334e535dc46fdce304dd35dc46fdce374c135dbf6d9ce304e535db66fdce33cdd35dc46fdce33ce535dc46c1ce)) else (if i < 192 then (if i < 160 then 0x3845933dbf6e5bd334dc35db66fdce374cf35db0719ce374c735db0719ce394cf35db0711ce374d92c99a6e1cc364dd379b8669cc31cdd379cd721cc334d8371c6739cb334dc369b872dce294dd325b8669cc37cdd379ca669cc374cd35dbf6edce334dc361b25a1ce324c736dcc719c8374d835d2e6ed72370c937dbc6ed93374cf35db0711ce294c7371cd719cb33cdd369b86a5ce370c933dc26b19331cd3369b86a5ce31ce5369b86a5ce31cdd369b872dce31cd3371c6735cb31cdd369726a5ce31cdd361b85a1ce374cd369a96e1ce334dd369b85a1ce374cd37db06edce374c1369a96e1ce394cd35db06d9ce else 0x360e5379cd6b9cc360c1371cd6f5cb360c1371c9719cb360c1371cd719cb364e5379c76b9cc394c1361a96e1ce374d9371b8725c5364dd325b8669cc394c9369bf711ce374cd369bf6e1ce368cd371cd719cb374cd361b0711ce334dd361bb6fdce334d3371c66b9cb334dd369726a5ce370c92d5c26b193334dd369b872dce33cc1371b8725c537cc1371b86e5c5374cd35d3e6d9ce37cdd325b8669cc34ccd35d3e6d9ce31cdd325cd669cc31cdd379ca669cc370cd35d2e6d9ce364dd325b86b9cc370dd369c26a5c7324cf31da2669c937cdd379ca6b9cc374cd35dbc6d9ce304dd361c45a1ce37cdd325b86b9cc) else (if i < 224 then 0x324c7375bb6e5c831ca5371c6721cb324dc35db66c1ce370dd369766f5c7360dd325cd6b9cc334dd35db64b9ce294dd379cd6b9cc370dd369766b5c7294c936dc6711c8334dd35db66f1ce374c136168711ce31cdd379cd6f5cc364dd379cd6f5cc374cd35da96e1ce34cd835d2e6d9c6374c735db0711ce374c737db06edce374d935d2e6d9b836ccf35db0711ce31cdb35dc46fdce374d937dbc6edb834cd835d2e6b9bd36ccf35db06b9ce33cdd35dae6c1c9324dd369726a5ce374c1361a96e1ce364d3379b8669cc394cf361a9711ce394c1369bf6e1ce33ce5379cd669cc364e5379b86b9cc384da33dbf6b9bd else 0x374cd361bf711ce374cd361bf6edce370c935d2e6d9ce370c937dbc6edce374d937dbc6edce374c135d2e6d9ce374c137dbc6edce370c937dc26ed9337cd9371b86e5c5370dd369bc6f5c7364dd325b8669ce374d835d2e6e5b836ccf35db06f5ce394cd361bf711ce370cd35dbc6d9ce304dd35db64b9ce370c137dbc6edce370c135d2e6d9ce294dd325b8669ce31cdc325b8669ce370c937dbc6b193294dc36dc6711c8294dc36dc672dc8374c1371b8725c5370c935d2e6ed93370c937dbc6c19337cd8371b86e5c5370dd369bc669c733459371c6729cb324df369c26b5c7364dd379cd721cc)))
  (w >>> (60*(i % 32))) &&& 0xfffffffffffffff

def segE (i : Nat) : Nat :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x101 else 0x101) else (if i < 3 then 0x101 else 0x101)) else (if i < 6 then (if i < 5 then 0x101 else 0x101) else (if i < 7 then 0x78c000078c1e3078c1e3078c1e3078c1e3078c1e3070501000003030c07 else 0x78c000078c1e3078c1e3078c1e3078c1e3078c1e3070501000003030c07))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x63c1e5079c000000000000504 else 0x1fc07f01fc07f01fc07f05000000000705) else (if i < 11 then 0x7a400007641d907641d907641d907641cf0005000000040a06 else 0x7a400007641d907641d907641d907641cf0005000000040a06)) else (if i < 14 then (if i < 13 then 0x5c400004ac12b04ac12b04ac12b04ac1cf0005000000040a06 else 0x5c4171000017105c417105c417105c417105c4171020700090105010c07) else (if i < 15 then 0x171000000004ac12b073c12b04ac12b04ac12b050504000000000b07 else 0x1fc07f01fc07f01fc07f05000000000705)))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x1fc07f01fc07f01fc07f05000000000705 else 0x1ef0000043073c04307b404307ac043010c043060000000403020b07) else (if i < 19 then 0x7d41f100001f307cc1f107cc1f307cc1f3040403000000000b07 else 0x7d41f100001f307cc1f107cc1f307cc1f3040403000000000b07)) else (if i < 22 then (if i < 21 then 0x7dc1f700001f907e41f707e41f907e41f9040403000000000b07 else 0x4302bc0af02bc0af02bc0af05c40af0000000400040a06) else (if i < 23 then 0x10400007f404107ec041078c04101040410009060301000a06 else 0x3fc0ff03fc0ff03fc0ff05000000000705))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x3e40f903e40f903e40f905000000000705 else 0x1001408d000400100041690004001059c001000400100040010004001000402a0607050008000205050303140b) else (if i < 27 then 0x1001408d000400100041690004001059c00100040010004001000400100040620607050008000205050303140b else 0xa902a40a9028c05a05bc16b02a40a902a413f01780a902a40a905b40a902a40a902a40a902a40a9120015030c090005040402000400041a0f)) else (if i < 30 then (if i < 29 then 0x100040010004001000400101050000000805 else 0x1000101) else (if i < 31 then 0x100040010004001000400101050000000805 else 0x17105c417105c417105c417105cc17100e017105c417105c400605c417105c417105c400e05c417105c41711209001600010e05070308010a001a0e))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0xaf02bc17102bc0af00740af02bc0af010c0af00b00af02bc0af02bc06402bc0af02bc0af0600000e0a0d03010002000402170d else 0x13000101) else (if i < 35 then 0x87000101 else 0x87000101)) else (if i < 38 then (if i < 37 then 0x87000101 else 0x87000000000000870224175021c087021c0870234087021c087021c087021c087000105090000010300000700130c) else (if i < 39 then 0x21c08705dc07a021c175033408d021c087021c087021c087021c0460224036021c08701d8087021c087021c087150c0107100b0011100603000b0c021b0f else 0x8d0098087021c0870334087021c087021c1750224087021c08701b8087021c087021c087060a020c03000c000003000102170d))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x21c087009808d00d8179021c087033408705d40870224087021c087021c087021c087021c0870714040001010b000602000100170d else 0x87000008d01e800005ec087021c087021c087021c1750224087021c0870210087021c087021c087100e0601030007000003000102170d) else (if i < 43 then 0x87000101 else 0x21c0d505d408405f408701d808d0334087021c06e0224087021c087021c087021c087021c087021c087100e0c1100080402000100010300190e)) else (if i < 46 then (if i < 45 then 0x87000101 else 0x21c000021c087011808705d4087021c0870224087021c087021c08705e4087021c08d0900041000010e07060606140b) else (if i < 47 then 0x9906140890000181060c08902240890224089022408905fc089022408902240890224089000104090003000300000000150c else 0x17505d417505d417505d417505d418105d4000061c17505bc17505d416b062417505d41750001001300000c0f00000400150c)))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x87000101 else 0xbf000101) else (if i < 51 then 0xbf00000cb02fc0bf02fc0bf02fc0bf0003000700000906 else 0x4b000101)) else (if i < 54 then (if i < 53 then 0x12c0a9012c04b012c04b012c04b0205000000000906 else 0x1f007c01f007c01f007c01f01050000000805) else (if i < 55 then 0x32c0cb032c0cb00000cb032c0cb032c0cb0007000000000a06 else 0x18b02b40ad02b40ad02b40ad02b40ad0001010400000a06))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x1100440110044011004401101050000000805 else 0xc500000c503140c503140c503140c50003000700000906) else (if i < 59 then 0xb002c00b002c00b002c00b01050000000805 else 0xc903240c906340c9032413303240c903240c9070500020101010c07)) else (if i < 62 then (if i < 61 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 63 then 0x100040010004001000400101050000000805 else 0xe700400000000000064c195064418f000000000100000907)))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x7000101 else 0x1000101) else (if i < 67 then 0x1000101 else 0x1b000101)) else (if i < 70 then (if i < 69 then 0x101 else 0x101) else (if i < 71 then 0x101 else 0x101))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x101 else 0x7f000101) else (if i < 75 then 0x1000101 else 0x1000101)) else (if i < 78 then (if i < 77 then 0x1000101 else 0x13000101) else (if i < 79 then 0x1000101 else 0x1000101)))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x1000101 else 0xb000101) else (if i < 83 then 0x1000101 else 0x1000101)) else (if i < 86 then (if i < 85 then 0x1000101 else 0x1000101) else (if i < 87 then 0x1000101 else 0x1000101))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x1000101 else 0x101) else (if i < 91 then 0x1000101 else 0x13000101)) else (if i < 94 then (if i < 93 then 0x1000101 else 0x1000101) else (if i < 95 then 0x1000101 else 0x100040010004001000400101050000000805))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x101 else 0x1000101) else (if i < 99 then 0x1000101 else 0x1000101)) else (if i < 102 then (if i < 101 then 0x1000101 else 0x1000101) else (if i < 103 then 0x101 else 0x1000101))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x13000101 else 0xf000101) else (if i < 107 then 0x1000101 else 0xb000101)) else (if i < 110 then (if i < 109 then 0x1000101 else 0x1000101) else (if i < 111 then 0x1000101 else 0x1000101)))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x1000101 else 0x1000101) else (if i < 115 then 0x1000101 else 0x1000101)) else (if i < 118 then (if i < 117 then 0x1000101 else 0x101) else (if i < 119 then 0x1000101 else 0x13000101))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x1000101 else 0xb000101) else (if i < 123 then 0x1000101 else 0x7f000101)) else (if i < 126 then (if i < 125 then 0xf066c00f003c00f039c05f01ac00f000006b065c19d01ac199003c00f003c00f003c18f0000001100001104000d0101150c else 0x100040010004001000400101050000000805) else (if i < 127 then 0x1000101 else 0x7f01fc07f01fc0f901fc07f01fc0f901fc07f03e407f0a0a070005050107000f09))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x7f03e40f900680fb01fc0f9006000001fc07f01fc07f01fc07f01fc07f01fc07f0f11050001000300040600130b else 0x3c19f003c00f003c00f003c00f0005000000000906) else (if i < 131 then 0x100040010004001000400101050000000805 else 0x3c1a1003c00f003c00f003c00f0005030000000906)) else (if i < 134 then (if i < 133 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 135 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 139 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 142 then (if i < 141 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 143 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x100040010004001000400101050000000805 else 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09) else (if i < 147 then 0x3ec07f000400100040010004001000400100000104000200000c08 else 0x10004001000400000000fb01fc001000400100040010000000a000000000d08)) else (if i < 150 then (if i < 149 then 0x100040010004001000400101050000000805 else 0x4065027c001024c0c9031c03f000400100040010004001021c001020f000b010401020500110a) else (if i < 151 then 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09 else 0x1a3000101))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x101 else 0x100040010004001000400101050000000805) else (if i < 155 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 158 then (if i < 157 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 159 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0x6500040000004000000403f0004001024c087000400100041a50906090003000000060f09 else 0x100040010004001000400101050000000805) else (if i < 163 then 0x69c0b100040000004001000400100040010005000000000a06 else 0x2bc0b100040000004001000400100040010005000000000a06)) else (if i < 166 then (if i < 165 then 0x6a40b100040000004001000400100040010005000000000a06 else 0xb002c00b002c00b002c00b01050000000805) else (if i < 167 then 0x137000400100040870004005000400100040c50900060007040100020e09 else 0x130000013004c0a3004c01301fc013004c0130424013004c0130c00090009010301000f09))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x1a7004000000000e704dc087003c0010004001000400100040010002040005030000010f09 else 0xf003c00f003c00f003c00f01050000000805) else (if i < 171 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 174 then (if i < 173 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 175 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 179 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805)) else (if i < 182 then (if i < 181 then 0x100040010004001000400101050000000805 else 0x100040010004001000400101050000000805) else (if i < 183 then 0x1400100000010004001000400100040010001000500000a06 else 0x1400100000010004001000400100040010001000500000a06))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x1400100000010004001000400100040010001000500000a06 else 0x1400100000010004001000400100040010001000500000a06) else (if i < 187 then 0x1f007c01f007c01f007c01f01050000000805 else 0x100040010004001000400101050000000805)) else (if i < 190 then (if i < 189 then 0x100040010004001000400101050000000805 else 0x403f0004001000400100040010005000003000906) else (if i < 191 then 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09 else 0x6500040000004000000403f0004001024c0870004001000409f0906090003000000060f09)))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0x403f0004001000400100040010005000003000906 else 0x403f0004001000400100040010005000003000906) else (if i < 195 then 0x40050004001000400100040010005040000000906 else 0x400000041ab000400100041ad00fc005000400100040010004000700000a000e08)) else (if i < 198 then (if i < 197 then 0x1b7001c00702bc14706c41b10000007001c1b3001c1b506bc007001c007001c007000100100000050300020100140c else 0x1b7001c00702bc14706e41b90000007001c1b3001c1b506bc007001c007001c007000100100000050300020100140c) else (if i < 199 then 0x2f00bc02f00bc02f00bc02f01050000000805 else 0x1100440110044011004401101050000000805))) else (if i < 204 then (if i < 202 then (if i < 201 then 0x100040010004001000400101050000000805 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 203 then 0x2bc0b100040000004001000400100040010005000000000a06 else 0x101)) else (if i < 206 then (if i < 205 then 0x2bc0b100040000004001000400100040010005000000000a06 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 207 then 0x101 else 0x100040010004001000400101050000000805)))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x41370004001000400100040010005000006000906 else 0x104dc00100040010004001021c0010006000201000a06) else (if i < 211 then 0x104dc00100040010004001021c0010006000201000a06 else 0x41370004001000400100040010005000006000906)) else (if i < 214 then (if i < 213 then 0xcb04dc000000003f00000010004001000400100040010604020002000100000d09 else 0x14904dc001000400100040af00040010004191060007030104020c07) else (if i < 215 then 0x1fc07f01fc07f01fc07f01fc048022807f01fc07f01fc07f01fc07f01fc07f0004010004060601000300130b else 0x1000101))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x1000101 else 0x2f000101) else (if i < 219 then 0x1000101 else 0x1000101)) else (if i < 222 then (if i < 221 then 0x1000101 else 0x7f000101) else (if i < 223 then 0xf000101 else 0x1000101))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x1000101 else 0x1000101) else (if i < 227 then 0x1000101 else 0x1000101)) else (if i < 230 then (if i < 229 then 0x7000101 else 0x1000101) else (if i < 231 then 0x1000101 else 0x7000101))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x13000101 else 0x1bb000101) else (if i < 235 then 0x1000101 else 0x1000101)) else (if i < 238 then (if i < 237 then 0x1000101 else 0xb000101) else (if i < 239 then 0x1000101 else 0x1000101)))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0x1000101 else 0x1b000101) else (if i < 243 then 0x1000101 else 0x1000101)) else (if i < 246 then (if i < 245 then 0x1000101 else 0x1000101) else (if i < 247 then 0x1fc07f006007f01fc07f02481bd01fc07f01fc05001fc07f01fc00001fc07f01fc07f01fc07f07000509020209080503000000170d else 0x1000101))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x1000101 else 0x12b000101) else (if i < 251 then 0x1000101 else 0x100040010004001000400101050000000805)) else (if i < 254 then (if i < 253 then 0x100040010004001000400101050000000805 else 0x40fb00040010004001000407f0004001070603030300000b07) else (if i < 255 then 0x100040010004001000400101050000000805 else 0x1bf00041c10004001000400100040010005050000000a06)))))))) else (if i < 384 then (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x40c10004001000400100040010005000006000906 else 0x100040010004001000400101050000000805) else (if i < 259 then 0x4c013004c013004c013004c01301fc013070707010005000b07 else 0x42c07f004c013004c013004c013004c013004c01300000404000800000d08)) else (if i < 262 then (if i < 261 then 0x3f41c7000c003000c00307140a700f4003070c003000c003000700000b000700040f09 else 0x15b0000043056c1d1010c1cf072405806c415b056c1cd00001cb056c15b056c15b056c15b000e00090008060300000000150c) else (if i < 263 then 0x15b0000043056c1d3010c1cf072405c06e415b056c02d00001d5056c15b056c15b056c15b000e00090008060300000000150c else 0x4c013004c013004c013004c01301fc013070707010005000b07))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x1fc000004c000004c013000c013004c013004c013004c013004c01309040007000000060001100a else 0x4c01300740130074013004c013004c07f004c013004c0130a0b060402000505000f09) else (if i < 267 then 0x1d700001d7075c1d7075c1d7075c15d075c1d707641d700081d70c0a020900080605050f09 else 0x101)) else (if i < 270 then (if i < 269 then 0x101 else 0x65002c0000004000000403f0004001024c0870004001000409f0906090003000000060f09) else (if i < 271 then 0x1000101 else 0x11000101)))) else (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0xbd000101 else 0x104dc00100040010004001021c0010006000201000a06) else (if i < 275 then 0x1000101 else 0x101)) else (if i < 278 then (if i < 277 then 0x1000101 else 0x1b000101) else (if i < 279 then 0x15d0000038055c157055c12b055c171055c157055c157055c1570704020003080002000f09 else 0x101))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x5000101 else 0x40fb00040010004001000407f0004001070603030300000b07) else (if i < 283 then 0x63000101 else 0x105000101)) else (if i < 286 then (if i < 285 then 0x101 else 0x2bc0b100040000004001000400100040010005000000000a06) else (if i < 287 then 0x1000101 else 0x1000101))))) else (if i < 304 then (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x740b3000000002c40b102c403702c40b102c40b102c40b10907000005000500030e09 else 0x1000101) else (if i < 291 then 0x104dc00100040010004001021c0010006000201000a06 else 0x1000101)) else (if i < 294 then (if i < 293 then 0x101 else 0x15f000101) else (if i < 295 then 0x1000101 else 0x101))) else (if i < 300 then (if i < 298 then (if i < 297 then 0x101 else 0x1b000101) else (if i < 299 then 0x1db00001db076c1db07741db05741df00281db076c1db076c1db0a070a0004010104000f09 else 0x101)) else (if i < 302 then (if i < 301 then 0x101 else 0x5000101) else (if i < 303 then 0x100040010004001000400101050000000805 else 0x109000101)))) else (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0x101 else 0x7f0000013004c013004c013004c013004c013060301040005050b07) else (if i < 307 then 0x93024c000027400006b4041024c0930784093024c093024c0930106020006020000000f09 else 0x1000101)) else (if i < 310 then (if i < 309 then 0x11000101 else 0x1000101) else (if i < 311 then 0x101 else 0x101))) else (if i < 316 then (if i < 314 then (if i < 313 then 0x3ec0050014005001400503e40050014005020108040400050b07 else 0x5000101) else (if i < 315 then 0x5000101 else 0x101)) else (if i < 318 then (if i < 317 then 0x101 else 0x6201880000000062018800041880620188020201000100000a07) else (if i < 319 then 0xa6029800000000a6029800042980a60298020201000100000a07 else 0x4000001c3700004001000400100040010004370000437000040010004370000c370000400100040010004001000400100043700004370000400100040010004001001700100013061500251d000000001e000b0c1c2614)))))) else (if i < 352 then (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0x18c0630000000018c0630000463018c0630020201000100000a07 else 0x4000001c3780004001000400100040010004370000449200040010004370000c4de000400100040010004001000400100043700004498000400100040010004001001700100013061500251d000000001e000b0c1c2614) else (if i < 323 then 0x4000001c3800004001000400100040010004370000448a00040010004370000c4be000400100040010004001000400100044000004370000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x4000001c388000400100040010004001000437000044a200040010004370000c3700004001000400100040010004001000440800044a0000400100040010004001001700100013061500251d000000001e000b0c1c2614)) else (if i < 326 then (if i < 325 then 0x4000001c398000400100040010004001000437000043700004001000450c000c5760004001000400100040010004001000437000044b0000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x3700004001000400100040010004001001c00300040010004001000437000040010004001000400100040010dc000100040010213140e14100c051805130015040102001f11) else (if i < 327 then 0x370000400100040010004001000c001001c0010dc0001000400100040010004001000400100040010dc0001000400100040010213140e14110c0a1715050001020605001f11 else 0x4000001c39000040010004001000400100043a6000437000040010004370000c3700004001000400100040010004001000441800044c0000400100040010004001001700100013061500251d000000001e000b0c1c2614))) else (if i < 332 then (if i < 330 then (if i < 329 then 0x400100040000004001000400100040030004001000400100040010dc0001001c3700004001000400100043700004001000400100000418000f020000000a16001503021e10 else 0x4000001c37000040010004001000400100043700004370000400100045b4000c57e0004001000400100040010004001000442000044a8000400100040010004001001700100013061500251d000000001e000b0c1c2614) else (if i < 331 then 0x4000001c37000040010004001000400100043ac00044e2000400100044cc000c370000400100040010004001000400100044120004370000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x620188000400000001d00000000100000706)) else (if i < 334 then (if i < 333 then 0x106302400000000000000000504 else 0x2980a602b80000001000100000504) else (if i < 335 then 0x400100040000004001000400100040030004001000400100040010dc0001001c4d00004001000400100043700004001000400100000418000f020000000a16001503021e10 else 0x101)))) else (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 0x400100040000004001000400100040030004001000400100040011340001001c4d00004001000400100044d00004001000400100000418000f020000000a16001503021e10 else 0x63018c06d80000001000100000504) else (if i < 339 then 0x7b418d06340000001000300000504 else 0x872000101)) else (if i < 342 then (if i < 341 then 0x86a00046320000000000100000504 else 0x18d800018d8000237000100000000000605) else (if i < 343 then 0x620000000418806a00000000000000000706 else 0x2980a603020000001000100000504))) else (if i < 348 then (if i < 346 then (if i < 345 then 0x400100040010004370000400100040030004001000400100040010000001001c428000400100040010004370000400100040010000041c0017020000000f19001003121e10 else 0x400100040010004428000400100040030004001000400100040010000001001c428000400100040010004428000400100040010000041c0017020000000f19001003121e10) else (if i < 347 then 0x63018c06880000001000100000504 else 0x101)) else (if i < 350 then (if i < 349 then 0x1a9000100006340100000403 else 0x40010000001000400101f40010004001000400100040070004001000400100043700004001000400100040010c070503000000020d1003010a0b1a0e) else (if i < 351 then 0x62000100001880100000403 else 0x630001000018c0100000403))))) else (if i < 368 then (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 0xa6000100002980100000403 else 0x230dc0001000c0010004001000401100040010004001000400100040010dc000b00040010004001000400100040010000150600120500130e02051106001c0f) else (if i < 355 then 0x18c000100006300100000403 else 0x101)) else (if i < 358 then (if i < 357 then 0x46340000000303 else 0x100040010044001000c0010004001000400100040010004023002c001000400100040010dc00010004001101702130012000a0c01010d00001a0e) else (if i < 359 then 0x4000001c3b000040010004001000400100043b4000437000040010004514000c370000400100040010004001000400100043700004510000400100040010004001001700100013061500251d000000001e000b0c1c2614 else 0x18806200000000001000100000504))) else (if i < 364 then (if i < 362 then (if i < 361 then 0x18c06300000000001000100000504 else 0x2980000001000000000404) else (if i < 363 then 0x4000000400700040010004001009c0010004001000400100043700004001000400100040010004370000400100040011301000f00101000000e0b010806141c0f else 0x101)) else (if i < 366 then (if i < 365 then 0x118c06300000000000000000504 else 0x18d000100006340100000403) else (if i < 367 then 0x101 else 0x46320000000303)))) else (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 0x63600046360000000000100000504 else 0x400000040070004001000400101fc0010004001000400100044280004001000400100040010004370000400100040011301000f00101000000e0b010806141c0f) else (if i < 371 then 0x400100000010004001009c0010004001000400100040070004001000400100043700004001000400100040010c070503000000020d1003010a0b1a0e else 0x4000000401f000400100540010004023000400100040010004001002c00100040010004370000400100040011114030a000800020d01070609001a0e)) else (if i < 374 then (if i < 373 then 0x700040010004001003c00100040010004001000437000040010004001000408100040010004001007c0010b0e080a000a000309030f0604001a0e else 0x4001000400500040070004001000400100040010034083021400500040010004001000437000040010004001000400100040010200160e010911181b180f0504021700001f11) else (if i < 375 then 0x18c000100006300100000403 else 0x1006c0010004001000400100040010004001001c0010004001000400100040010024001000400102120b04040f05060105030000180d))) else (if i < 380 then (if i < 378 then (if i < 377 then 0x700040010004001003c00100040010004001000437000040010004001000400b0004001000400100440010b0e080a000a000309030f0604001a0e else 0x700040010004001005400100040010004001000437000040010004001000400b0004001000400100e40010b0e080a000a000309030f0604001a0e) else (if i < 379 then 0x21c087021c08f02240870180087022c087021c087021c087021c087021c03a02340870030087021c004021c087021c087021c087021c087021c08719151100150016171508000b020107000000122313 else 0x868188000000009501e800041b00620190020201000100000a07)) else (if i < 382 then (if i < 381 then 0xc2029800000000b302c800042ac0a602a8020201000100000a07 else 0x8700040030f0000100040010dc001f0004001000400100040010004007000400510c00930f1000100040010dc00010004001000400100040010004091000452000fc52400040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17) else (if i < 383 then 0x8700040030f0000100040010f0001f0004001000400100040010004007000400510e00930fa000100040010f000010004001000400100040010004091000452800fc53400040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17 else 0x87000400310e0001000400110c001f0004001000400100040010004007000400510c009310f0001000400110c00010004001000400100040010004091000453800fc53c00040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17))))))) else (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 0x87000400314a00010004001148001f0004001000400100040010004007000400514e009314c0001000400114800010004001000400100040010004091000452000fc7a000040010004001211e1d1c21191b1a15010d170f0c0b10200600202100022c17 else 0x1b8063000000001ea0690000466018c0640020201000100000a07) else (if i < 387 then 0x5aa000101 else 0x93024c8c8025c093026c099024c005158855a024c093024c0930254093024c099024c089024c007024c09d024c093024c093024c093024c093024c0001a1e111d00111e15001a070e0a00060803020f2313)) else (if i < 390 then (if i < 389 then 0x1002440a5029c091025c091028c001024409f024409102a476a02440911d8808f024409102440a1024400102440910244091024409102440910e1c001102000c19060b140200020a000a062212 else 0x6322188000000400023406ba19c865a0000000800000906) else (if i < 391 then 0x62000100001880100000403 else 0x4001000400100040010004001000400100340010004001001400102ac001026c00700040010dc00010004001000400100000c1a0003000100000614000000121d10))) else (if i < 396 then (if i < 394 then (if i < 393 then 0x10000001000403f000400702440010dc0540000c00100043c4000401f000400100040010014001026c00100040010004001000400100040010004001001a10161200041219140209091909000104002313 else 0x4005000400100040270244430001c001026c0010004001000400100040010004001000400100040010dc000100040010004001020d1610141a0e0b1a0d050001020608001f11) else (if i < 395 then 0x31100001000400014900010004007000400100140010004001024c00100040010004001000400100040010004370000400100040010004001001a0000000e180a001900160008111209022112 else 0x4000002c001000c0011490023024c0ad0004001000400100040110004001000400100040010004001000400100040010dc00010004001080016061a14110f090419000c00000b022011)) else (if i < 398 then (if i < 397 then 0x88024e000000006201f000041b807e8188020201000100000a07 else 0x6781de0000000000025806300010738262010000000000000a07) else (if i < 399 then 0xbe02c600000000a602d000042980b682a0020201000100000a07 else 0x1000400100040010dc00b111200af1600001000400113b8003000400116e800100040010004001000400100043b800040010004001000400700043700004001000400100090118241b1e18031713100c00211200231701070b2916)))) else (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 0x1000400100040010ee00b111400af1620001000400113d80030004001170800100040010004001000400100043b800040010004001000400700043b80004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x590000101) else (if i < 403 then 0x10004001000400111200b111200af1660001000400113f802b00040011728001000400100040010004001000445000040010004001000400700044480004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x10004001000400116000b116600af16000010004001212802b00040012080001000400100040010004001000458800040010004001000400700045800004001000400100090118241b1e18031713100c00211200231701070b2916)) else (if i < 406 then (if i < 405 then 0x1b208e2000000018c0698000463020a0638020201000100000a07 else 0x8940000794000000000404) else (if i < 407 then 0x8841f90000000400020c06c418d06840000000800000906 else 0x740b102c40b120e00b302c40b102c47ec02c488c02d40b102c408300c00b100dc01d1e300b102c40b102c40b102c40b102c40b102c40b100001112001906180011190500000d0700010b002314))) else (if i < 412 then (if i < 410 then (if i < 409 then 0x10004001000400116e80b117280af208000100040011f0802b000400116e800100040010004001000400100045c200040010004001000400700045ba0004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x1f286aa000084218c800119480001be8632030300000000010a07) else (if i < 411 then 0x10004001000400113b80b113f80af2128001000400113b80b700040011f0800100040010004001000400100044f600040010004001000400700044ee0004001000400100090118241b1e18031713100c00211200231701070b2916 else 0x1f786b6000085218d800119b80001c38636030300000000010a07)) else (if i < 414 then (if i < 413 then 0x400100040b100040010004007000c0010004001000400100045a000043700004001000400116e80010004001000400100040010100101100120f07091a0d0403031805021f11 else 0x1116000100040010dc00b100040010004003001c00100040010004001000400102bc001000400100045ba0004001000400100040010314151216140c1607080e0002040104002011) else (if i < 415 then 0x110004001000c00113b80010004001002c0b9000402300040010004001001c00100040010dc00010004001000400100040010000021a0013001400000b08001808011e10 else 0x210dc0001000c001000400100040110004001000400100040010004001135800b00040010004001004400100040010000150600120500130e02051106001c0f))))) else (if i < 432 then (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 0x37000040010084001000c001005c0110004001001c00100040010004007000400100040010004001000400100040010001000b000f010014150d030f07041c0f else 0x18c000100006300100000403) else (if i < 419 then 0x100040010004370005c003004401100440af001c01100443b8004401100040110044001004401100440110044506004400100440110100170917150c19080618010b020208002011 else 0x40110004001000c000002c001000400100040b1000400700040010004001001c00100040010dc00010004001000400100044480000021a000c001400000b08001708011e10)) else (if i < 422 then (if i < 421 then 0x400100040010004001000c0bd15300010054005000401f000400100040bb0004001000400b000400b00040010dc000100040010000151114100b031b0a170018000c07021f11 else 0x18c000100006301ee000000010000000605) else (if i < 423 then 0x1000c0010004001000400100040010004001004c0010004001000400100040010074001000400102120b04040f05060105030000180d else 0x100040390004001135000300e403900e403900e4370001c0390004039007c00100e403900e401100e44d600e401900e403901001509141208171a06150108020206001f11))) else (if i < 428 then (if i < 426 then (if i < 425 then 0x62000100001880100000403 else 0x100040010004001000401d0004001004c00f0000001000400100040010dc0001001c01300040010004001000400100040010000001c000a02010000081a000801171d10) else (if i < 427 then 0x6200010000188070000000010000000605 else 0x102fc460000400100040010004001007c00100040010004015007c0010004005004400100040070004001002c00100043700004001004c00b00200800131d071a161900151015030107082212)) else (if i < 430 then (if i < 429 then 0x100000010004001000400700040030004001000400100040c10004001160837000040010004001174000100040010004001000400101001210001411001a0d0f0709070306021f11 else 0x2980000298000000b000100000504) else (if i < 431 then 0xb002c00b00040190004003030c00b001c00b002c001002c00b000400b0004001000400b002c00b012c00b0dc000b002c00b0100150f12070c051a0b160007011806001f11 else 0x87031c0010004001021c37011a0001032c0010004001000455402b403f021c00100040600324001000400100040c500040010304001000400100043c4000c3e0001c00102445d80004001024c001007c00100140010004001000458200040191a2f2f29182a24311032232f1522000d0a092f25011600002303200006381d)))) else (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 0xcd03440cd021c0cd021c0870180087022c0cd0334087033c0cd03340cd03340cd033408703340cd034c06003340cd0334087021c060033400003340cd03340cd03340cb03340cd24041d16171202181918000a1c000014110100121a062916 else 0x8703540dd021c0e10354017035c0d9021c087021c087021c087036c090021c09801200d5021c08b0334087021c06001800cd021c087021c0870180087021c0d1021c08700d8060021c0871c18060021c0d102a0087021c08701400870160087020008b01800b0022c06802200cd01e00e303540cb01c0087037c08702e0087021c060021c0d50280087004a424b4947413d47454343413d3b38221d1b3733311900152e110d2d2b3c24260c0708342c2303045029) else (if i < 435 then 0x106201880000000403 else 0x1063018c0000000403)) else (if i < 438 then (if i < 437 then 0x10a602980000000403 else 0x401f0004001001400b005400100040010dc0001000400100040010004019000437000040010004001000400100170d0b0d150e0c0e06000800000803041d11) else (if i < 439 then 0x118c06300000000403 else 0x118d06340000000403))) else (if i < 444 then (if i < 442 then (if i < 441 then 0x118c86320000000403 else 0x10004001000400100040010004000017c01f0054001000400100040010004005002c001000400100040010dc00190004001000d0100000a021b00020a19000000161d10) else (if i < 443 then 0x40010004001000400100040050054001007c001006400100043700004001000400b000400100040010004001000400f0018000900170c17000f0015000002011d10 else 0x7c001000000100040010004001001400b000400100540010004001000400100040010004005000437000040010004019000401500160c0300040d170002110c000000091e10)) else (if i < 446 then (if i < 445 then 0xe40010000001000400100040010014051000400103940110004001000400100040010004005000437000040010004019000401500160c0300040d170002110c000000091e10 else 0xe7000447800044ee000400117800af0004001000c5e200040010f60087000400f0004130030400100040010004001000400700040010dc00010004001000400100044ec00040010004001091e0a1c20020521231d001b240d170010130f1e00000d2c17) else (if i < 447 then 0x2d40af000400100040010064001000400b0004005002c01f006401f00044ee000400100540010014001000437000040010004015000400100040010004001000400100040010004001191d0a22182306240e21002216100b002300161a1b0e052b17 else 0x3900000010004001004400100040010dc001500044d6007c00100440010064001000400100040010044001004400100040e500fc0010004001000400b0014011000400100040191c260023121d12220f1a200000221e170808000005022916)))))) else (if i < 480 then (if i < 464 then (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 0x41e006201e2000018800020004000705 else 0x11460007000400100140010004001000400100040010dc0001000c001015c001000400100040010004001001451a000400100040010004001001018190010001a00031200000d0008001103022414) else (if i < 451 then 0x10004568000400700040010004001000400100040010004001001c00100040010004001000402f00040170c13000d0b1201000103000b000b1a0e else 0x40010004001000400f0000001007c001000400100540010014001000405100040010004001000400100040010dc00190004001000604000001071c00020b1a000000121e10)) else (if i < 454 then (if i < 453 then 0x100bc0010004001002c001004400100040010004007008c0010004001000400100040010dc0001000400100040010c19031304000012000a060f0507021c0f else 0x100040b10004001000400100040010dc000100040010034001000400116e80010004001000400500040010004007000400d00140010004001001c0010004001000400100040011520251c001a24140815192507020f0001240e2100032a16) else (if i < 455 then 0x40010004011018c0110004001004400d001c01100440630044011004400103a401100040110dc00110044011004401100000d0f0015090c00150100001100021d10 else 0x100140010dc000100040010004007030458200040010004001021c00d001400100040010004001000400100040010004001000400d0004007000400101800010004001000400100040011d26160020100224000e0d1d251c180424000b0f0116002c17))) else (if i < 460 then (if i < 458 then (if i < 457 then 0x106201880000000403 else 0x10a602980000000403) else (if i < 459 then 0x40000004001006400100040010004001007c02f00540010dc00010004001000400b001400100040010dc0001000400100040010000090b00190d1500150100000b00021e10 else 0x118c06300000000403)) else (if i < 462 then (if i < 461 then 0x10004001000400100040030004001003c0011200001001c007000400100040010004001000400100040010e150012000c0b160102090006031a0e else 0x4001004400100040010004001005c0010dc000100440010004524000400100040010004001000400100040010084007005c0010004001024c021001c0010004001000400000040010925002508231a200200141e1001101a0317001500142a16) else (if i < 463 then 0x4013000400b0000001002c00b0004001002c00b000400b000400b002c00b003c00b002c00b002c00711000d000c0203000a05000404180d else 0x62000106200000100000403)))) else (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 0x63000106300000100000403 else 0xa600010a600000100000403) else (if i < 467 then 0x1006403900040010004370010400100040af000400100040e500040010004001005c00100040010004001000400700040010dc000100fc0150004001001611152113171800031306110000041611072413 else 0x10004130000c05f03ac00003ac069000003903b40ef000c07f0400000009000300000f09)) else (if i < 470 then (if i < 469 then 0x18c000118c00000100000403 else 0x106201880200000403) else (if i < 471 then 0x106201880200000403 else 0x18806200010000000403))) else (if i < 476 then (if i < 474 then (if i < 473 then 0x18806200010000010403 else 0x58018c058015805b0160058016805a8160058018805b8160080c050b040a0108000f09) else (if i < 475 then 0x1000101 else 0xb000101)) else (if i < 478 then (if i < 477 then 0x5c029805c015808f017005c017805e817005c018808f8170080c050b040a0108000f09 else 0x1000101) else (if i < 479 then 0x9f0208082818809f818800040000000328000000030302010a07 else 0x9d0210084818809d81a0004c0000000000000000000302010a07))))) else (if i < 496 then (if i < 488 then (if i < 484 then (if i < 482 then (if i < 481 then 0x1000101 else 0x18806200010000000403) else (if i < 483 then 0x18806200010000000403 else 0x18806200010000010403)) else (if i < 486 then (if i < 485 then 0x18806200010000000403 else 0x40000000188000000000404) else (if i < 487 then 0x1880dc018809b016005c01880620188080026e06201880004202080d000c070b040a031009 else 0x106201880200000403))) else (if i < 492 then (if i < 490 then (if i < 489 then 0x18800040000620000000000000504 else 0x1880620048001400000000000000000100000706) else (if i < 491 then 0xc000001880308001062000000000100000705 else 0x106201880200000403)) else (if i < 494 then (if i < 493 then 0x400100040010000001000400700040010004001000400100040010004001000c0010004001000400711000d000c0203000a05000404180d else 0x620000000000d000100000404) else (if i < 495 then 0x3c1880000000303 else 0x5406200150000010403)))) else (if i < 504 then (if i < 500 then (if i < 498 then (if i < 497 then 0x1000101 else 0x306001880200000403) else (if i < 499 then 0x6200000000188062018806200010620188010000000000000a07 else 0x80063008001681f4020008001782160200080018823a8200080c050b040a0108000f09)) else (if i < 502 then (if i < 501 then 0x1000101 else 0xc0010dc0017000401100040010004001001c02100040010004001000400100040010004001000400100040011905021000110505000303040000001b0f) else (if i < 503 then 0xa6000100002980100000403 else 0x100040010dc00010004001000400100040010004001005c00100040010dc0007000400700840010004001004402f000400100040011618151814170c001302070001010004002011))) else (if i < 508 then (if i < 506 then (if i < 505 then 0xf103cc01100bc000000c003000007f0004001000000000301000b07 else 0x18c000100006300100000403) else (if i < 507 then 0x4001000400100e4001039401700040010004001001c0010dc002f00040010004001000437000040010dc0001000400100640010004001011a00030b00110c0004101600020a0e08012112 else 0x400100040010004001000400100040010034001000400100040010004007001c001000437003d400100040030004001000201000005001a00120116000e00031d10)) else (if i < 510 then (if i < 509 then 0xa6000100002980100000403 else 0x40000000000000c0010004003000437000040010004001000400100040010004007000400100040010004001000400100040010d0718030c020c0005010a0000030600011e11) else (if i < 511 then 0x1000101 else 0x9a063009a01681f5026809a023821e026809a018c23b0268080c050b040a0108000f09))))))))) else (if i < 768 then (if i < 640 then (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then (if i < 516 then (if i < 514 then (if i < 513 then 0xc0010004001000000100040070004001000400100040010004001000400100040010004001000400111000d000c0203000a05000404180d else 0xb0a602980200000403) else (if i < 515 then 0x2980340000002c298000300000504 else 0xbd02e80ba82980bd82b000040000000000000000000302010a07)) else (if i < 518 then (if i < 517 then 0x1000101 else 0xc013000400b0000001002c0070004001002c00b000400b000400b002c00b000400b002c00b002c01311000d000c0203000a05000404180d) else (if i < 519 then 0x42980000000303 else 0x10a602980200000403))) else (if i < 524 then (if i < 522 then (if i < 521 then 0x2980a600010000000403 else 0x2980a600010000000403) else (if i < 523 then 0x142980a60058000000003000000000605 else 0x29800040000000000303)) else (if i < 526 then (if i < 525 then 0x2980a6000b0000000403 else 0x2980dc02980b9017005d02980a602980b802e60a60298002c2e2080d000c070b040a031009) else (if i < 527 then 0x298000c0000a60280000000000504 else 0xa6000000002980a602980a600010a60298010000000000000a07)))) else (if i < 536 then (if i < 532 then (if i < 530 then (if i < 529 then 0xb000101 else 0xb806300b801781fc02e00b8023822602e00b8029823c82e0080c050b040a0108000f09) else (if i < 531 then 0x40d800040130004370002c04b002c041002c001002c0010004007004c00b002c00b002c00b002c003002c00b002c0010f150014111205000700100003040000021e11 else 0x4001000400100040110004001000c12e000400100040010004001007c001000423000040e00388001000400704b000100000010004001004c001111f13001610001500140a051403080104002212)) else (if i < 534 then (if i < 533 then 0x10004001000471000043701c5800500040070004001000471200040011c50001000400100140010004003000400100040010dc00010004005000000100000010dc00011b180f1d0418001c0200120017151d1b130b1908002715 else 0x100040010004001000400101e40030004001000437000040f700040010004001001c005000400100040010004001000400000130b1100000a0100040506000201041d10) else (if i < 535 then 0x7f03e407f01fc07f01fc0f903ec5ea01fc0f901fc07f01fc0f903e407f01fc0f901fc07f0cc05ec01fc07f17b807f01fc07f17a007f01fc07f0000160f141b0f031506110e08050a0006022212 else 0x100040050004003000407f001474c00040070004005000400100043700004718000400100040011c6800100040010f20001000437000040fb00040011d38000000400100040012210170000030021201a1a1d1401100d1b0b160101172916))) else (if i < 540 then (if i < 538 then (if i < 537 then 0x100040050004003000407f0014774000401d0004005000400100043c80004720000400100040011c8800100040010f2000100043c800040fb00040011dd8000000400100040012210170000030021201a1a1d1401100d1b0b160101172916 else 0x3fc000101) else (if i < 539 then 0xc03d03f400103fc005000400100140010004001001447400040010004005000477c00040011e180010004001000400100040010d000012001a0a160c030b0400040e0004022012 else 0x1e7879c0100000303)) else (if i < 542 then (if i < 541 then 0x40010004003000400100040010004001001c00100040000dc0001000400100040051ca071a000400100040010004001000400100140c16000a0200000c0f06000407021e10 else 0x2700340010004001000401d000400100040010014001001c71a000400100040010dc0001000400100040000004001000400100040010e050f0e00140c0900000f110002040009032012) else (if i < 543 then 0xdc00011d3800100040010004001001401f000407f00540fb0004001000400100040070004001000400100040010004081000400100010f121c000e140905110f05020301041f11 else 0x40010074005000400100043d0003c001000400100040fb1ce80010004001000400100040050dc001d112074c1cc075e01fc00500040010004001000400100040070004001000400300040010026252a001a2318001c1d030000110b001a02000016080c2d18))))) else (if i < 560 then (if i < 552 then (if i < 548 then (if i < 546 then (if i < 545 then 0x1000474e0014001000401f00040150004001001400101a400101fc005000400b0004001007c3700004001001402d00040190004001000400100040010014001002c00100040010404001002112200e0f211e1523042408010000151b09000118022c17 else 0x40010004103000400100040010004001003401b000400100143700004001001c001000400100040050004001000400500040010004005000471a0004001001400100040011e20100b1827021900021b1d14120e030200180e080e2916) else (if i < 547 then 0x300040010074001003c013002c001000400100040010004105003c0010004001000437000040010004744000000100040010004001004c001101f0f0b001e001503100a05000309010a002112 else 0x4001000000100040bb00040010004001000400100040050004001000400100040010004001000408317070700070401090402000001180d)) else (if i < 550 then (if i < 549 then 0x40010000001000400700040010004001000400100040210004001000400100040010004001000401b17070700070401090402000001180d else 0x4003000c013000c0030dc001b000c017000c009004c001004401f00040010004001000c003000c003000c003001c00000020c160007020600040704000006021d10) else (if i < 551 then 0x40010000001000400100040010004001000400100040070004001000401300040010004001000400317070700070401090402000001180d else 0x40010000001000400100040010004001000400100040070004001000400300040010004001000401b17070700070401090402000001180d))) else (if i < 556 then (if i < 554 then (if i < 553 then 0xd0074750000c000004c013004c109042407f004c01101fc01301fc001004c01301fc0010dc00131d50013004c0010f200130f300131d580131d480fb004c013004c0130004001042c330004c001000407f042401f004c013004c107000c270f0000002e00082811002e192d00231c03001b001800151b01351c else 0x1ba01800cc018401fc3300c4033018800fb0cc033018886ec1ba807f03f407f0ce00fd01fc07f044407f189007f01fc33003f407f01fc07f03ec07f043407f01fc33c046410f01fc6ee189807f01fc11301fc07f01fc0fb01fc0fb03ec0fb045407f01fc07f01fc03d0cc007f01fc07f01fc07f01fc07f01fc0fd03f407f01fc11701fc07f1800000013004800330000000e4a3b490748474600453a442e43424129331f40253f3c301e21280f4d28) else (if i < 555 then 0xfd01f40fd03f433003f40fd03f411b03f40fd03f40fd03f40fd046c10f0cc00fd03f433001fc07f01fc0fb01fc0fd03ec0fd03ec0fd03f411b03f407f03f407f03f40fd1f1800181c16141018110c03000b000008001206032815 else 0x401300040010004001000400f007400100043700004001000437000040010004001000000100040010004001002c000000f0c15000a0a0400050706000001021c10)) else (if i < 558 then (if i < 557 then 0x10004001004c00f003c0010004001000400100040010004001000401d0004001004c3700004001000400b0004001000400110a00010004001007400100040000004001002c00100121610001f1d1800021c151705110b1606190207002916 else 0x400f0004013000400100040010004001000437000040010004001000401d0004000000400100040010004001002c00f0004001000d07060005091400020b0400000d001e10) else (if i < 559 then 0x8c001004c00f00040010004001004c00100040510004001000400100740010dc00010004001000400100000000004000000400100040010015151500120c070c050b020a00060900092012 else 0x10004001004c00f003c0010004001000400100040010004001000401d0004001004c3700004001000400b0004001000400110c0001000400103ec00100040000004001002c00100121610001f1d1800021c151705110b1606190207002916)))) else (if i < 568 then (if i < 564 then (if i < 562 then (if i < 561 then 0x4001002c00100040010004001003c01d0004001004c001000400f000401d004c37000040010004001112001d00740010004001000400b00040010004001000400100040010004001271e0e1f0a1b092314141900101702000d0401000b02002b17 else 0x10004001003c001000c0010004001000400100040010dc0001000401b000000100040070004001000400100040010a0308070d000705070400030002021b0f) else (if i < 563 then 0x1000000100540050004001000400100040010dc00010004001002c001006000100040010004003000400100040070004001000810070004060900010c00000a12031d10 else 0x1004c00100040010004001000400100043700474001000400f0dc00010064013001405100040010004005000402d00040000004001007c00100040011a0016130e1115150d04040900000010000a022313)) else (if i < 566 then (if i < 565 then 0x100040010004003000402f0004001001c0010004001000437000040000004001013c0010004001000400100040010e00080c0c0806100404040a0102001b0f else 0x100040030474001000402f0004370000400100040010014001000400100043700004001014437000040000000001001400100040190004001001b001c00170d0f0706090311010e0812002112) else (if i < 567 then 0x40000004105001c0010dc00bd006c0bd0004003000400100040010004001001c00100040010004023000400100040010004001071000001d000012180312180904010c001f11 else 0x400100040130004001000400f0004001000437000040010004007000403b0004000000400b00040010004001000c00f0004001000d07060005091400020b0400000d001e10))) else (if i < 572 then (if i < 570 then (if i < 569 then 0x400f00040050dc000104840010004001004c013000411d000400f00040010004001001400100040010c6000100040010dc011f0dc0001001c00100b4000012c00100040010064001000f0c06032023241c1d0021101907021a18161311002a16 else 0x122000400100040010004001001c0010004003000435a0c800010004001000400100040010460001000400100a0001006c00000040010004001000400017191c010c0814180a001114000308061104022313) else (if i < 571 then 0x1402100040010dc00010004001000437001dc0010004001048c0010004007000437000040010000001000400100bc001000400100040011d1d00001903110018130b051200040b002011 else 0x40070dc00010004001000400300043700004001000400100040010004000000400100040010004001000400100040010e0005180b0d08030a0207020001001c0f)) else (if i < 574 then (if i < 573 then 0x101 else 0x700040010004001000400300043700004001000400100040010004000000000100040010004001000400100040010e00080c0b0d07030a0206020001051b0f) else (if i < 575 then 0x40070ee00010004001000400300043700004001000400100040010004000000400100040010004001000400100040010e0005180b0d08030a0207020001001c0f else 0x1000c001000400100040010f200010004001000437000040070004001000400103ec0010004001000400100040010004001000c090600000802000e0404000201001e10)))))) else (if i < 608 then (if i < 592 then (if i < 584 then (if i < 580 then (if i < 578 then (if i < 577 then 0x400b0004001007c001000400100540050004001000400100140010dc00010004001000401900040010004001000400100040011500040e0d09010f09051200000111070a04002113 else 0x10004001001c00100040030004001000400100043700dc00010014001000000100040010004001000400100040010b000815151400090e0e05040002021b0f) else (if i < 579 then 0x7d0004001000400100040010dc000101b40050000007000400100040010004001000c0010004001000400100040010004001000c000b0000130700080d05000408021d10 else 0x440010084001017c0010004001000400b0dc00010004001000000100040010004001000400100040070004001000400114010a0a06060014020005090905031c0f)) else (if i < 582 then (if i < 581 then 0x11007c00100040010dc001f007c0010004001007c01f001c06500000070194003007c01f007c019007c01f007c01f007c01f000e001500050003000a1207000013011d10 else 0x40010494001009c001000c00500040010dc00010004001000000100040010004001000400100040010004001000400118010a080a0700120200050a0905041c0f) else (if i < 583 then 0x405f0004071000400100040030004370000400100040010000001000408100040010004001000401f00040010004001180009090b040013050107080802061c0f else 0x1c0010004001000400100040010014127001c005000c005000400100040010dc00050004005000400100143c4000c001024c00103340600004001000400100040010014005027c065000000500140050014005272421090828261c04250017021813211a120c0f0102130e003019))) else (if i < 588 then (if i < 586 then (if i < 585 then 0x5f0004001000401f0004001000400100040190dc00010dc000b00040010004001001400100040010004001000000100040010004001070c110f0a02041302080c020803070c001f11 else 0x140050004001001c00100043700004001001c0010004003000400100040010004003000400100040010004001000400100040010ef80010004001000400000040000004001000400109261a201321191e0f00151d1d0d0517191202001607002a17) else (if i < 587 then 0x24001000400100040010dc0001001c00500040010004001000400100040000004001000c00100040010004001000400100040010004001b00001405000a0e07000609021e10 else 0x1001400300040010004001001400500040010004001000406d00040050004001003400504a40050dc00cd01800010000005001400500040050014370001400500080207001513060013051c00180a03000a01002514)) else (if i < 590 then (if i < 589 then 0x4ac0b1005c00103cc00000003f000140170004005005c02f0100000801070002000e09 else 0x7c001002c001000402f00040010004001000400100043700dc03700004001000400100040010004001006400000040010004001001700020004000b000c0900000604091e10) else (if i < 591 then 0x100040010328001000c0010dc0007000400301c4001000400102fc00100440c8000000100040010004001000400100040010004001000e1c110a06001808020e080503090d021f11 else 0x400100040010004001001c0010dc000100040010dc037000040010004000017c00100040010004001000400100040390404001000c10030000000900080c05000415071e10)))) else (if i < 600 then (if i < 596 then (if i < 594 then (if i < 593 then 0x4001000400104a40ad000400100440070dc00010004001000400103c037000840010dc00010004001000400100bc001000400100140010004000001f1815140b00081002000710050d00071b2212 else 0x3c0010004001000400100040010004001000400101c400100040010004000000400100740010dc000100040010004001002c013000b15160000001b00050a04000209021e10) else (if i < 595 then 0x130074001004c013007c3700004001004c013004c003004c0750044013004c013004c013004c0010f30013004c0130cc0013004c013004c00301fc0010004013004c001004c000004c013004c01323251f0001242215032100141b121c1b180d0b0d10010705002e19 else 0x13003c0010004370000400100040010dc0001000400301c400100040010004000000400b000400100040010004001000400100040010d0b0c19090400090600140603010b0f001f11)) else (if i < 598 then (if i < 597 then 0x405f000c0010d0000f000400100043700004001000400100040010004001001c000001c00100000010004001000400100040010c0a0b170803000805000e0503010800001e11 else 0xf004c0010dc0001000400100040510dc0001000400100040010dc00010004000006400100000010004001000400100040010004001030c0d190a04000a0805110604010a0f001f11) else (if i < 599 then 0xbc001000400100040010004071000400104000030004001000437000040030dc037000040010004001002c00100040010004001000400100040c5141104120e01180c12000708070505100501032313 else 0x1000400100040010004007000400100040fc00040010000000000400100040010004001000400300040010004001160808090a060010040402010800031b0f))) else (if i < 604 then (if i < 602 then (if i < 601 then 0xb0004001004c00b000400b002c0070dc00410004001000000b0004001002c00b002c00b004c00b000c00b002c00b160b080909060007020009101001041b0f else 0x37001b400301b4071000406d01b406d001c06d01b406d01b4013000400101b400b004c001001406d0dc006d03a000001b412f03a806d04b4001008437001b406d000b2321001d1e060014181c000f1218000701002514) else (if i < 603 then 0x400100540010014001002c013003c0010dc0007002c001000418800040090004370000400100040010dc0001000401100040070a60630000400118d0007007401b0dc00010004005000400318c8017000418c00040010004007000400d000463600040010dc0001008401f000c37000040010004001006437042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x1b000401b00540010dc001b00040000004131017c003006c01b003c001006c001006c01b006c01b00bc007006c01b16190c140f000713120505100003001b0f)) else (if i < 606 then (if i < 605 then 0x1c001000c0030024013000c003017c01d004406b000c00f01a40fd017c3300dc0370000401f000c01d000c003000c0000034003000c001000c003000c0031a141d0012100003110a0d000e04020b0600032413 else 0x40070004003000400100043700dc000f003c00f003c000003c00f003c00f002c00f003c00f003c00f000402f003c00f0dc000f000a0b0c0011000e00061402000000071e10) else (if i < 607 then 0x4001000400100040010004001000400100040010d2000300040010004007000436e000410c002c36a001c1080004001000000000000010004001000400100100021000d0004000a140800061200000300022414 else 0x34354000400d003401f003400d000c3700dc002f003402f00340070dc01030034069004c00d00040110440000003400d003400d000401304cc000003402f003400d2100001b1e1716160a0e1306080a00130300100d002615))))) else (if i < 624 then (if i < 616 then (if i < 612 then (if i < 610 then (if i < 609 then 0x40010004000000400100040010004001000400100040010004007000c001000400100040010004001120e13140e0a05000009040601180d else 0x10004001000400b000436200040010000000000400300040010004001001c0010004001000400b000400100040011607071414020012120505101000021b0f) else (if i < 611 then 0x40010004000000400100040010004001000400100040010004007000c001000400100040010004001120e13140e0a05000009040601180d else 0x4001000400100040010004001000400100040010004370000c0010004001001c0010dc0370000437000040010dc000100040000dc00010dc0001000400100040010012001e000e1e23000b1b0900071400000416022614)) else (if i < 614 then (if i < 613 then 0x400100540010014001002c013003c0010ee0007002c0010004142000400900043b8000400100040010ee0001000401100040070a8063800040011a10007007401b0ee0001000400500040031948017000419e00040010004007000400d000466e00040010ee0001008401f000c3b80004001000400100643b842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x56601d013a0f0019400143c00aa03c019003c019903c000e865a0004762001c5ae0004001000400100040130f000010004676003c0010004001006c001000455a00040030004009000476e00040010004019004400100040070004017001c0550084001003400100040070f00001000401f0004001002c001000400300540050004005000400b1800000013004b00330046000e4a264907484746004539442e433b4229411f40253e3d331e30210f4e28) else (if i < 615 then 0x150f0000001a406901a406901a406901a406904dc06904d411d01a406901a40ed01a4069003406901a40690e12000e000e040b010501000300190e else 0x7400100040010034001000401f0f200010004476008400100f4001000400505200010004001069000f00040010f202b00004001000401d00046480004001000401d0ff00010f203c800040010f20003006401d005400b19f800300043c8013433819f00010004011000400b00740010074001000401300043c811d00051928001463b3b444444404040393d353716143433002f0c2e2c412928242127110d201e01081d1b1705044b27))) else (if i < 620 then (if i < 618 then (if i < 617 then 0x301ac10b01ac06b000006b01ac06b04e4000007401d01ac06b01ac06b01ac00f01ac3c801ac06b01ac06b000000040d150001000801060001190e else 0x6901a4069000c3ba01a4069047406900540fd0fc806901a406b047406904ec13703b406901a406901a406901a406901a40691c000f0d000506000206050504000605031f11) else (if i < 619 then 0x400100540010014001002c013003c00110a0007002c00100041a8000400900044280004001000400110a0001000401100040070a4868800040011a90007007401b10a0001000400500040031a8801700041ae00040010004007000400d000468e000400110a0001008401f000c42800040010004001006442842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0x400100540010014001002c013003c00110c0007002c00100041b0000400900044300004001000400110c0001000401100040070a2869000040011a5000703ec01b10c0001000400500040031ae801700041b400040010004007000400d00046be000400110c0001008401f000c43000040010004001006443042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 622 then (if i < 621 then 0x1b811201ce11201541120698112000100040151b10001001c001003400100040010004001007c794000401d11200010004007000402b00046aa0004001006c44800040011ad8001002c001000402100440130004005000400b0004001003c02b0004001001400100040011e3000711200070024001000401d00180010004019340032002e002a00390014482a470d4626451f441d4301423b41153d3a2f0c280524002119094a26 else 0x400100140010004091003c103001401f0004003047400100040550004430000400100400010004001000400102440010004001060f150f1a0011060503001008010401001f11) else (if i < 623 then 0x4001047400111280000004001000400100140010004001000413d007c0010004001000c001004c001100e00030e0301000601030300180d else 0x13d0154055002c0fb00b442a00b40fb013402d017405500b402d00b402d00b402d00b402d04fc02d00b402d00b402d0600060403020000000904000001091c0f)))) else (if i < 632 then (if i < 628 then (if i < 626 then (if i < 625 then 0x1000401500040130004005000400700040010740001000400b13404d00004009000400100444d000040010ae000100046180004007001c01d00044d01ed0001003c14121c8001002c005000400321a8017000424000040010004007000400d00048dc00040011340001008401f000c4d00004001000400100644d043413f3c403c001b3c3d3b1a3735162e30382d2b362c2a120b25230f2422190a06010e02004825 else 0x1d809204e80b004e818404e81f304e8220801f0004001000400813a0007050c0010004003000400100040070004001005c4e800040012390001002c0090004007000400700840010004001000489200040030004005005400b000400122280010044001000c00f0004001000400513a0001005c001000403d000400100040193200170039002e00120014480f3908472e4627452544204338420b413640013f1f2c00291e094a26) else (if i < 627 then 0x100540010014001000400b2330013003c0011480007002c00100041e800040090004520000400100040051480001000401100040070b2060800040011eb0007007401b1480001000400500040032188017000425000040010004007000400d00048d400040011480001008401f000c5200004001000400100645203e424038413f00373f38361a322f162e2d4027243b3126120b25230f1f1d190a06010e02004825 else 0x14007020c00100040050014069001400500140051480005001400100141450014005010400500140050014005000119050c050e09030204000d00001b0f)) else (if i < 630 then (if i < 629 then 0x18c00000000007000000000404 else 0x524007002414b02bc4d0001c007001c14d051c007001c0aa0004007001c0070524007001c007053c0230014007026c007001c00700170a000d09050b0300090000080c0307022012) else (if i < 631 then 0x10024037001c0000134009054415300240090024009027400900240090024009002400913a0009001c0090912080605051207000a0b050000190e else 0x59007c058009605800b4058017e0580007c7e4000400100540010004580001c00d00040010004001000401d00040010004007000402b00048420004001006c58000040012148001002c001000402100440130004005000400b0004001003c02b0004001001400100040011fb000716000070024001000401d0288001000401931002d443a002a00360014472a460d4526441f431d4201413740153e35380c280524002119094a26))) else (if i < 636 then (if i < 634 then (if i < 633 then 0x63000000210000000303 else 0x7001c01d008c15700740230084580008c0230554000008c005008c023008c000008c023008c023008c0230002080000040400010800040000021a0f) else (if i < 635 then 0x100040150014001002c83a004c001003c001001c5b8002c00100041f8000400900045b80004001000400116e0001000401100040070b605f000040011f7000700b401b16e00010004005000400320a8017000426000040010004007000400d0004832000400116e0001008401f000c5b80004001000400100645b843413f393b3f00373f38361a322f162e2d4127243a3126120b25230f1f1d190a06010e02004825 else 0x18c00050001000303)) else (if i < 638 then (if i < 637 then 0x55c0af01a4005001c00516e0005056400500000050014005001400501040050014149001400500140050014005080e000c120504020a04040000001a0e else 0x18c000100006300100000403) else (if i < 639 then 0x242864818c063000047f822806f00002000200000906 else 0xfb00040011c8007f0004001000400100040010004001000404f00040011c60001200071822a00010004718000400123e800100040010004001000400100040010000001000c001100a001f1e0f1e1d00121d1800091d1a0019011016002916))))))) else (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then (if i < 644 then (if i < 642 then (if i < 641 then 0x241063018c0678004c80822c06d00002000200000906 else 0x1d20013004c013004c01d004c013004c013000c770004c013004c8c0004c013004c013004c8fc004c01301fc0131d20013004c0131d20013004c804004c013004c013004c0131303001d1c1419110016151a000e0600001a050100002916) else (if i < 643 then 0x8100004630000063000000000000605 else 0x63018c00000000003000100000504)) else (if i < 646 then (if i < 645 then 0x118c06300200000403 else 0x63018c00010000000403) else (if i < 647 then 0x118c06300200000403 else 0x63018c00000004020000300000504))) else (if i < 652 then (if i < 650 then (if i < 649 then 0x118c06300200000403 else 0x118c06300200000403) else (if i < 651 then 0x400018c0630000000000504 else 0x63018c00010000000403)) else (if i < 654 then (if i < 653 then 0x63018c00010000010403 else 0x118c06300200000403) else (if i < 655 then 0x63018c00010000000403 else 0x63018c00010000000403)))) else (if i < 664 then (if i < 660 then (if i < 658 then (if i < 657 then 0x1463018c0088000000003000000000605 else 0x63000040000000630000000000504) else (if i < 659 then 0x63018c00010000010403 else 0x118a000018c0630000100000504)) else (if i < 662 then (if i < 661 then 0xba001c0000000630000000000504 else 0x6300dc0630206020009a063018c06300b8091218c063000048b8080d000c070b040a031009) else (if i < 663 then 0x318c06300200000403 else 0x6c00018c0630000000000504))) else (if i < 668 then (if i < 666 then (if i < 665 then 0x63018c000d0000010403 else 0x63018c000f0000010403) else (if i < 667 then 0x9c18c0630005400000000000000000100000706 else 0x1000101)) else (if i < 670 then (if i < 669 then 0x630000c62018c0000000000000504 else 0x1000101) else (if i < 671 then 0x1718c000018c0600000100000504 else 0x19000101))))) else (if i < 688 then (if i < 680 then (if i < 676 then (if i < 674 then (if i < 673 then 0x746300000000303 else 0x246300000000303) else (if i < 675 then 0x18c0000000063018c063018c000118c0630010000000000000a07 else 0x40010054001013c0050004001000c00b1c6000100040010004208000400f0014718002c001000404f1c6004f0004011000401d09c02e80004001203000100040131c6004f000400100040032288017000422800040010084001000400d0004902055c0011c60001000401f04c471800040010004001006471842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 678 then (if i < 677 then 0x1d000001d001404d007404f007401d008c7180574149007401d02c801d007401d056c01d03ec01d00b401d007401d007401d007401d08110002061002080503000000000b04021f11 else 0x4c013004c01300f401d004c0131d201631ff001d1e60003004c013004c0130034040004c013004c210004c013004c0030074278004c013004c013004c2f0004c0031d20013004c10b1d2090c1d2015f1d2004d1e000130584013004c01d004c748004c8b2000c01d1de00131d20013004c01300740e902ec5e8004c013004c013463917444444404040383d3836141233320f0b302c27412a262523403f081f3110011d051e001b4b27) else (if i < 679 then 0x4d1d2004d056c000000001d013404d059404d013410f013404d013401d013404d013404d007404d013404d000d020d0e040009000501000000190e else 0x20607f0206063018d081820607d0246081820607d42470818080c050b040a0108000f09))) else (if i < 684 then (if i < 682 then (if i < 681 then 0x22e089822e063018c88b822e085824608b822e087824688b8080c050b040a0108000f09 else 0x24408ee244063423c09102440632246091024408e82478910080c050b040a0108000f09) else (if i < 683 then 0x40010004001018000101b0021005444e1e0008820800010004001000400300040010004001000400b022000300040050004001001c0880004001002c08800040010004001001400102200b80064001003c83c23a00070004070006c0010024001000407800040800004001022008800040110160013000400102800070220007005c007007499802c00a80004001000402a022000100043e0022000102603c40220001000441623a00010034090000c08800040c0007c00100e000100048d26a616b0068665f6565055e3a6600596463005759462c25201e593a54555334504e4b32362e292724110c1e174a48420f4341061b19400002156f39 else 0x400101a8001000c0d80f088e8000c001000400100540131de0968000406c20a0001000400120b8007001c00100840d8000400b000400300040d800140010004001001c0010360017002c001000400103e00d80004001000400500040d803f8019003c00103800f600040c8006c001002400100040ce00040d0000401d03600d800040110158001000400103a00070360007000400d0f100d8000400103b80010004050036000100043f623a0001007c0010108001000492200040f00fc00d8315d5c006a685967676558536700535166656062605e5b54234d304e4c462a4945432840241f1d1a160a3f203e3937153836132c0f0d0406006f39)) else (if i < 686 then (if i < 685 then 0x4c012004803c223a0108000c1200440001048011804801280480138000412004a805c00c0011000400100040030004120000486c20c000104c8003001c00100840010148050000443a10e0007013013a04800011e201200f00001004c0010004001003c0010074007000400100041202470001003400500048e80480001006c001000400b00040010024007000400500040010044001000400b000400b005c00100040230004001007c00100040010004019005400100040010004001520054004e6a4a004700690045686766320000002e0000001e666564186362611260435f0c5e405d2a5c5b5a24595450063e3c3a002b38256d38 else 0x108432054000305a015800041680580168060000105a01900004168009803824a88e8000400105a0001009c0010004001000c0070004021000404805a000105c016805a017805a019805200011dc01680fa0001004c0010004001003c001007400706203fe0f100070004001000484c2100001003400500048e805a00010094001000400b000400100240070004005000400100440010004001000400b005c00100040070004001007c00100040010004019005400100040010004001530057004f0028004c006a004a00690036000000320000001e69686718666564126348620c4430252a61605f245e5d460642403e00593c556d38) else (if i < 687 then 0x80020023a023c052021025c023808703c01e4023400a820c120000307d0850251002e001420026b0001080000108002400f1000123a02000150218000490a12109a800042000004001250000107b01e808000500034001082000107c0228088001300040010800001003c00700041f8000401b0004001000400900040010004011000400100040170014001000401f00040070800001005400500840010004001000400b000c224001c0010004854080023008b0007000400b000400100a40050004001000400100040010910019000c0010004007080000140007b003b7a727936000000320076002e0075002a746f734f004b0047726c6426476c41216b67661e3c64271945144d101c62170c605e5c06075901005855547d40 else 0xba02a825e000d0a408e80a402900a2029000042b80a8003000049a6000402b00040010004001007c0010a4029000041ea23a00660004278000402b001c00b002c0010b6029027a82e00ac00090bc00010004001000440800442c000040011e6000100ac2c80004866000429800040010004280000400100049d0001c29000642d0001402000040150a400070f0800120800210004001007493800040070004290001406c000401d0a40001001c001000400100040011100001004c7e40004028003c0010004452006c001000429000040016a00487746684100660062002a0061743f7370005f005d00567226715a6e225856703b36381c536f346e526c1e5f193e13500e4e08172f4b0430110c0002793e)))) else (if i < 696 then (if i < 692 then (if i < 690 then (if i < 689 then 0x4001007c08c00540da000c01321d0001002c005000400f174829205b00010004001000400111a03b000043c000040170004007001c3c00f2000700b43c0000402100040010f4000100040010f000010f6000700043c000048e800043c01d588e8000400100142000ea0009006c3c021600010044001000c001000400b00040010f0000100341200f0000100047b000040010f000010ee04a80f0001956525200514d50524c4c00494d4646441d1505464216401203113a3d39383633312f2d2c2b070f0a2725240023211a5b2f else 0x34001007c00100040150004021000c00527885e80004001279800b001c0010004001051000711a0001000400b11a00010004001000437811a0001006400111a0001003c5ec004c001000445800043c4000c001001446811a0001006c03123a0001000445c002400711a00010004460002c3c00004001000446811a08e8000400511a0007005c37c1f0000100bc47411a000100049da0004001050001f006400127780111ce81b8000400111c0880000400108a00012210001000400108b046861696000696769006664665b00005b640000605c4f57403b3544423f3b36343057542e2b27250b2253511c1a4d4b0f4a1b09180600131102496f39) else (if i < 691 then 0xf088e812a09cc09a09c417a03c012a08e812a049012a049800044a800044a812a074c12a08e426f04a812a09ce09a8015271800117a803308d8001005c9b412807d804c04b800049b61000001000400500040010034001078000104c803300440010004001005c0010004001007c00100cc00100dc0010004350224000112e823400040150004001000400100044a80004021000400100d4033000400526f800100e400100044a8000401912c000100b4001000400b004c00100040330004001003c001000400b000401924725a7139706d00356e6a00436c00003f6b6a693168570054005300526851671e6665640c4f6362064c3e6100604b5f185d485c2c2b452212192914753c else 0x1168150156011414c049c1460072158815c15204d80da04e807c04e0032856814a054815e04d213c052015205320d60278092853816c08e816603b6185036a1368418152015e14684ca054855016c855a11604f801c00c814a84c013405600ea8616142010815203b4132027a15c054807c849009203a8166854842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 694 then (if i < 693 then 0x24c025216405f2130000315e000115e000116a007e164837217002500a1858001f05f00dc05c20054007001c00115005a015e057814404ec140036016205b8001c2841f408241608001183000100145ba000400d00044200004010222000115e00010004011000400100040170004001000401f00040070004009000400115e0578000400100040010004001000457800040210004001006c007000400500000010004001000460e0004019000c00100ec001000400b004c00100040070004001003c001000400b000400324656f003664000032630000445f0000405e00002e5d7000596d6e005a6f6e6d1e546c6b0c536a5706504f56004c4a3d18493c2b29463e2a12143b22753c else 0x17403c423a05d0007c27017a0021001c4d000044d60004005000400100040010054001001c276000400117405d817b800103c05d027f0001172000100349fa17405d00004001008400500040010bf800122780010f0800117980010004013000403d0064001005c001178000103d8001003c8e800045d0000400100041d8001c732002c0071fa000b002400100045d0000400700442f800049b4174000100bc89800049f4004400100045d00004001006c9f200049b20004001005c5d000045d000040014d6e61005f6d496c5e6b67005b695900586866005300650051004566355230642a57254f064b20331c174426161e3e12100e3c0a0c04373d002c713a) else (if i < 695 then 0x23706a80e206ac0e386aa13c0003190000b190064019000491900013001c162002c64e13d063018800081a4000b1a60770059864a180069c1a6800b002c160002c0411a7800b003400b19d000b24c0604236000b193038a002c03f002c00b002c017002c00b002c04b002c007002c63419c001005906ae001c009002c00b192038c002c013002c00b002c00b002c640004c047002c00b006c007002c041190000b000c00b002c640002c045000c00b010c00b002c00b004c00b002c007002c00b000c00b002c00b002c00b24416f003c2f0000382900004b71000047700000346f6d0062006c00616d6c6b1e5f6a690c5d5a6806592f67005844651854522229535119124d4114753c else 0x118808019b011c19a04a418e028c199828a1a006280e0050007e04f8034867c198068019005ca14106581a0066a17e00860e186781a808e818f03be1a9038218a85fc1a0028818e862c020865c1a8866e11804fc0a380d0198862017206640ee86a619401181a003bc18b80841a2068007e84a00e103b818f868042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725))) else (if i < 700 then (if i < 698 then (if i < 697 then 0x6b8000401d1b60001000404d008400100040110004001000400500f400b000400d00140011c88a1014200032cc00201b4051400040010004950002c71a2d106301b400381b406b41ba06d02cc86ea1b4001d1b407180004a0a000400300640011b4000122b001d287801d007c015007400100040011b4000123a000123a07201b40a0800046e000040220004a1c0004a2400040010004b4600046d000040010004770000403a00040131bc001d1b200010004001000c0010004a12000401d003c6d00004a260004001000482000046d00004001740040713b54724d70006e006c006a0068004600670041006400621804003761605d365c5a025754245332501e4e192e0c4b2928134910460620433d002f7a3e else 0x908b20276013c26e00fc00609302ca0003005475000040010c6000114607c81ca059c1d4000107007a018e075000047b806483c60ce000128e00010014750013c00d0004750002c6c02c6074022e004f1d40b0200048f002e82cc2ae07a80004af40004011000400100840170004001000401f0004001001401b000400100409f0000404d0004001013c001000475000040010004001000c00100040012c58001006c04f00047500004019000c0010004001000400b004c0010004001000404f003c0010074001000400124726e0036700000326f00004e6e00004a6d00002e296b00656a690064636a681e605e5f0c5b595a065654500053464c183c434529443d2212193b14753c) else (if i < 699 then 0x400500040010004001148001f000c0011ed0001000401300047b000046d40004003000477000040011dc052422d077000048e81dc08e8000401d002ca4400040151dc001d05b00011dc00211b400010004001290864000040011dc08b0000401d0004a46290000d000477005a000f00040011dc001d0134001000416a000401100047701ed803d007401d000416e002c00100047701ec80050064001004e4d55004b2f5400554852000054475346444240143e394b2c3837280f25351f0a1c273605331929000e012018045b2f else 0x100040010004005015400d00043c00084053002c7b000048e81ec00012d38001001400114a000114d0001003c019000400b007c7b000040011f6000129b000129e82601dc0001000400300048e8004cb3e000402d00047b01bf08cc0144005000434e19207ea0004001000418c1bb0001000404d0004a5800b40011ec0001000423c2c787c000b4011000401500040011ec000300647b026400011ec07121ec0001000400123001a2000400f000402d26000011ec00131ec000105d00011ec098806c8001000402d6f6f6864626e616b6b006c6868006651382d5e1e00401900001303015d4819435b1440583a0f0b56393505322e0054534f4e09294d492b1d27231f743b)) else (if i < 702 then (if i < 701 then 0x1fe07fc1ae00031fc00011fc00011fc00011fc00571fc00011fc00011fc00011fc00621fc07f0150081e019881a1510618194006020700642a00a842a08818007c0012a1800100540010004057000c001002c01d00147f01fc08a000040010004001000c0010004001004400100048242080001016400100048e823a0001004c00100040010004001003c001015c0010004001006c00100040010004001016c0570004001000400b000400100040570004001003400500040210004019430000003f0000003c0000003a666500326652002e3527211e55686718516665125064630c4f62612a4b605f244a5e5d06495c5b00455a596d38 else 0x401f000400500047f00004001000485a0004088000401523e0820000c001000429200045500004820000482023a0001000457c208000b001482000040012080001000400723a00010004001004c8700004858000400f000c820006400700246d000048200004658000401122c001d20800072a20007007408a000400d002cacc000487200040012080a8a0a40001000401b2b3882000140210014001564d5300544b47005329544e504351454427424d46222d3d3c003b3a1e1d383317163530100f202e0a011925050c0b5b2f) else (if i < 703 then 0x1000400123a0001002c001017400d220001f0f008582010007007c015216091400140010004820216005f00048e800040010004001000c0012160001000400700040192160001000400100040012160001002c0010004001002c8580014001000485800048580004858273885800040072d380010004009226802100040012a400110c2000125300012b7000100042a2000c85800640070004558004c708003c8c000041d60004584006c102018489000046600004aa200042580b080010004b266b626c0069605f68675a686600005a655c005125571c5453504e164f4d48104947420e43413b083e302b25183a381f02361e062c34190026327039 else 0x89821c08e821c03900e603a02200560000c87010b88700c008700b589e201a49c2019c005203800520808e821c000516508702ce8870001470023206680014a982bb00b00014005001400700340050c5004123800902ae88702c380630014005008c878001400500140650014005001491021c000521c09fa001406b00140050f1094c00140090014005001c005001487000140050014005004c00500140052590005006c06d00140070014019003400500140050014005001400500140050014041000c005001c0050014005246400003c7100003828706f496e6100456d6c6b346a00005f0000005e6c6b6a1e695a680c592f58065255660050145b184f51422943323112414b22763c)))))) else (if i < 736 then (if i < 720 then (if i < 712 then (if i < 708 then (if i < 706 then (if i < 705 then 0x1000400101cc001002c0010074814003c00101cc00d232001f0cc801300548c0240000500040011b808b0000400100040010004003002c0010004001000400100048b0000400b000400101c400122c0005000400122c00730004001000400100048b022c000120806f023a0001262895c000400100048b022c0001006400123a0073000498822c08b001d48ca00443300084aa80004ae4000c8b0004c7700004570000448c003c8b001bc1aa000458c000467000748c200041a80004aaa0004ae66b5e6c00695c6a0067596866000059656100606256542f522d511250294f102621490a4c48460845203f1a63413e182d3d37023a36270019357039 else 0x1ec808821d016821c07b419006d422d029223a04ac0368578080054805b085e21608e81d407b015f082023a08b0022808e05a88721a00ac01d507702b102021ed829423a02901d485d21b408242b0887611a054c0a580d821683c6174085c0f08ac61fc012023a03c411a808c23e08e805b84a804903c01d588e842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725) else (if i < 707 then 0x245832e244091411e000323e08f8007491223e09640ca0962000c003007482423e000323a000316800031ff08f820808f8000c8e81da0688000c76023e001d000c00323e04b4000c00323e000325987582560af80ca89602bf001d0074003007407b000c003000c003000c00317688f81fe095c23e09001690003007407b2be8003000c04d01dc0030074003000c8f8000c01d000c003000c00300740030cb0003007404d000cafe000c003000c003000c0031760003000c00301e4003000c003000c003007400312c0003246600003c630000386f00004b6e0000476d0000343f0000616c00005e6f6e6d1e5d5c5a0c2f576c0654535100446b691841504d292b643112142a22753c else 0x29e00a02ba01782a60a681a60a182b802e22b00a600d005b808805b00610ad02a40ac01d40a581820a882b00aa828000c628a0ab01a808e82bc0a402d403202920a302b002b82c00a502820ac82d60b0811c06100bd80e82a80a381780ad80f68b622a001282b003d429c00ac2be0ac006784b807203c82c40ac042403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725)) else (if i < 710 then (if i < 709 then 0x22800002b001802a008c018007402d002a02e00440028050008004800700a602800b801e0088015009802e00b0000800600680aa01a00c801f00800330022023802c02e002801e805a01c009c03280ae00e004c00b8008028803601600a400c80ce024001002e003400e800403000b80078040005003001f80b842403e383f3d00373d38361a322f162e2d3f27243b3126120b25230f1f1d190a06010e02004725 else 0) else 0)) else 0) else 0) else 0))) else 0))

def nsE : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 19
  | 7 => 292
  | 8 => 365
  | 9 => 26
  | 10 => 1
  | _ => 0

def offE : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 25
  | 8 => 317
  | 9 => 682
  | 10 => 708
  | _ => 0

def stateE (s i : Nat) := rowsE (offE s+i)

def actionE (s i h : Nat) : Nat :=
  let t := segE (offE s+i)
  let a := t &&& 255
  let b := (t >>> 8) &&& 255
  let d := (t >>> (16+8*(h % a))) &&& 255
  (t >>> (16+8*a+14*((h/a+d) % b))) &&& 16383

def rotateE (g : Nat) (ws : List Nat) := if g = 0 then ws else if g = 1 then setA ws else if g = 2 then setB ws else setA (setB ws)

theorem rotateE_ok (g : Nat) {s ws} (h : NatRun (mask 232) (goal 232) s ws) : NatRun (mask 232) (goal 232) s (rotateE g ws) := by
  unfold rotateE

  split
  · exact h
  · split
    · exact runA h
    · split
      · exact runB h
      · exact runA (runB h)

def Z (s : Nat) := barrier 232 stateE nsE actionE sixE rotateE s

theorem h0y0 : span (Z 0) 1 0 = true := by decide +kernel

theorem z0 : span (Z 0) 1 0 = true := h0y0

theorem h1y0 : span (Z 1) 1 0 = true := by decide +kernel

theorem z1 : span (Z 1) 1 0 = true := h1y0

theorem h2y0 : span (Z 2) 1 0 = true := by decide +kernel

theorem z2 : span (Z 2) 1 0 = true := h2y0

theorem h3y0 : span (Z 3) 1 0 = true := by decide +kernel

theorem z3 : span (Z 3) 1 0 = true := h3y0

theorem h4y0 : span (Z 4) 1 0 = true := by decide +kernel

theorem z4 : span (Z 4) 1 0 = true := h4y0

theorem h5y0 : span (Z 5) 1 0 = true := by decide +kernel

theorem z5 : span (Z 5) 1 0 = true := h5y0

theorem h6y0 : span (Z 6) 10 0 = true := by decide +kernel

theorem h6y1 : span (Z 6) 9 10 = true := by decide +kernel

theorem z6 : span (Z 6) 19 0 = true := (@span_join (Z 6) 10 0 9 h6y0 h6y1)

theorem h7y0 : span (Z 7) 10 0 = true := by decide +kernel

theorem h7y1 : span (Z 7) 10 10 = true := by decide +kernel

theorem h7y2 : span (Z 7) 10 20 = true := by decide +kernel

theorem h7y3 : span (Z 7) 10 30 = true := by decide +kernel

theorem h7y4 : span (Z 7) 10 40 = true := by decide +kernel

theorem h7y5 : span (Z 7) 10 50 = true := by decide +kernel

theorem h7y6 : span (Z 7) 10 60 = true := by decide +kernel

theorem h7y7 : span (Z 7) 10 70 = true := by decide +kernel

theorem h7y8 : span (Z 7) 10 80 = true := by decide +kernel

theorem h7y9 : span (Z 7) 10 90 = true := by decide +kernel

theorem h7y10 : span (Z 7) 10 100 = true := by decide +kernel

theorem h7y11 : span (Z 7) 10 110 = true := by decide +kernel

theorem h7y12 : span (Z 7) 10 120 = true := by decide +kernel

theorem h7y13 : span (Z 7) 10 130 = true := by decide +kernel

theorem h7y14 : span (Z 7) 10 140 = true := by decide +kernel

theorem h7y15 : span (Z 7) 10 150 = true := by decide +kernel

theorem h7y16 : span (Z 7) 10 160 = true := by decide +kernel

theorem h7y17 : span (Z 7) 10 170 = true := by decide +kernel

theorem h7y18 : span (Z 7) 10 180 = true := by decide +kernel

theorem h7y19 : span (Z 7) 10 190 = true := by decide +kernel

theorem h7y20 : span (Z 7) 10 200 = true := by decide +kernel

theorem h7y21 : span (Z 7) 10 210 = true := by decide +kernel

theorem h7y22 : span (Z 7) 10 220 = true := by decide +kernel

theorem h7y23 : span (Z 7) 10 230 = true := by decide +kernel

theorem h7y24 : span (Z 7) 10 240 = true := by decide +kernel

theorem h7y25 : span (Z 7) 10 250 = true := by decide +kernel

theorem h7y26 : span (Z 7) 10 260 = true := by decide +kernel

theorem h7y27 : span (Z 7) 10 270 = true := by decide +kernel

theorem h7y28 : span (Z 7) 10 280 = true := by decide +kernel

theorem h7y29 : span (Z 7) 2 290 = true := by decide +kernel

theorem z7 : span (Z 7) 292 0 = true := (@span_join (Z 7) 160 0 132 (@span_join (Z 7) 80 0 80 (@span_join (Z 7) 40 0 40 (@span_join (Z 7) 20 0 20 (@span_join (Z 7) 10 0 10 h7y0 h7y1) (@span_join (Z 7) 10 20 10 h7y2 h7y3)) (@span_join (Z 7) 20 40 20 (@span_join (Z 7) 10 40 10 h7y4 h7y5) (@span_join (Z 7) 10 60 10 h7y6 h7y7))) (@span_join (Z 7) 40 80 40 (@span_join (Z 7) 20 80 20 (@span_join (Z 7) 10 80 10 h7y8 h7y9) (@span_join (Z 7) 10 100 10 h7y10 h7y11)) (@span_join (Z 7) 20 120 20 (@span_join (Z 7) 10 120 10 h7y12 h7y13) (@span_join (Z 7) 10 140 10 h7y14 h7y15)))) (@span_join (Z 7) 80 160 52 (@span_join (Z 7) 40 160 40 (@span_join (Z 7) 20 160 20 (@span_join (Z 7) 10 160 10 h7y16 h7y17) (@span_join (Z 7) 10 180 10 h7y18 h7y19)) (@span_join (Z 7) 20 200 20 (@span_join (Z 7) 10 200 10 h7y20 h7y21) (@span_join (Z 7) 10 220 10 h7y22 h7y23))) (@span_join (Z 7) 40 240 12 (@span_join (Z 7) 20 240 20 (@span_join (Z 7) 10 240 10 h7y24 h7y25) (@span_join (Z 7) 10 260 10 h7y26 h7y27)) (@span_join (Z 7) 10 280 2 h7y28 h7y29))))

theorem h8y0 : span (Z 8) 10 0 = true := by decide +kernel

theorem h8y1 : span (Z 8) 10 10 = true := by decide +kernel

theorem h8y2 : span (Z 8) 10 20 = true := by decide +kernel

theorem h8y3 : span (Z 8) 10 30 = true := by decide +kernel

theorem h8y4 : span (Z 8) 10 40 = true := by decide +kernel

theorem h8y5 : span (Z 8) 10 50 = true := by decide +kernel

theorem h8y6 : span (Z 8) 10 60 = true := by decide +kernel

theorem h8y7 : span (Z 8) 10 70 = true := by decide +kernel

theorem h8y8 : span (Z 8) 10 80 = true := by decide +kernel

theorem h8y9 : span (Z 8) 10 90 = true := by decide +kernel

theorem h8y10 : span (Z 8) 10 100 = true := by decide +kernel

theorem h8y11 : span (Z 8) 10 110 = true := by decide +kernel

theorem h8y12 : span (Z 8) 10 120 = true := by decide +kernel

theorem h8y13 : span (Z 8) 10 130 = true := by decide +kernel

theorem h8y14 : span (Z 8) 10 140 = true := by decide +kernel

theorem h8y15 : span (Z 8) 10 150 = true := by decide +kernel

theorem h8y16 : span (Z 8) 10 160 = true := by decide +kernel

theorem h8y17 : span (Z 8) 10 170 = true := by decide +kernel

theorem h8y18 : span (Z 8) 10 180 = true := by decide +kernel

theorem h8y19 : span (Z 8) 10 190 = true := by decide +kernel

theorem h8y20 : span (Z 8) 10 200 = true := by decide +kernel

theorem h8y21 : span (Z 8) 10 210 = true := by decide +kernel

theorem h8y22 : span (Z 8) 10 220 = true := by decide +kernel

theorem h8y23 : span (Z 8) 10 230 = true := by decide +kernel

theorem h8y24 : span (Z 8) 10 240 = true := by decide +kernel

theorem h8y25 : span (Z 8) 10 250 = true := by decide +kernel

theorem h8y26 : span (Z 8) 10 260 = true := by decide +kernel

theorem h8y27 : span (Z 8) 10 270 = true := by decide +kernel

theorem h8y28 : span (Z 8) 10 280 = true := by decide +kernel

theorem h8y29 : span (Z 8) 10 290 = true := by decide +kernel

theorem h8y30 : span (Z 8) 10 300 = true := by decide +kernel

theorem h8y31 : span (Z 8) 10 310 = true := by decide +kernel

theorem h8y32 : span (Z 8) 10 320 = true := by decide +kernel

theorem h8y33 : span (Z 8) 10 330 = true := by decide +kernel

theorem h8y34 : span (Z 8) 10 340 = true := by decide +kernel

theorem h8y35 : span (Z 8) 10 350 = true := by decide +kernel

theorem h8y36 : span (Z 8) 5 360 = true := by decide +kernel

theorem z8 : span (Z 8) 365 0 = true := (@span_join (Z 8) 320 0 45 (@span_join (Z 8) 160 0 160 (@span_join (Z 8) 80 0 80 (@span_join (Z 8) 40 0 40 (@span_join (Z 8) 20 0 20 (@span_join (Z 8) 10 0 10 h8y0 h8y1) (@span_join (Z 8) 10 20 10 h8y2 h8y3)) (@span_join (Z 8) 20 40 20 (@span_join (Z 8) 10 40 10 h8y4 h8y5) (@span_join (Z 8) 10 60 10 h8y6 h8y7))) (@span_join (Z 8) 40 80 40 (@span_join (Z 8) 20 80 20 (@span_join (Z 8) 10 80 10 h8y8 h8y9) (@span_join (Z 8) 10 100 10 h8y10 h8y11)) (@span_join (Z 8) 20 120 20 (@span_join (Z 8) 10 120 10 h8y12 h8y13) (@span_join (Z 8) 10 140 10 h8y14 h8y15)))) (@span_join (Z 8) 80 160 80 (@span_join (Z 8) 40 160 40 (@span_join (Z 8) 20 160 20 (@span_join (Z 8) 10 160 10 h8y16 h8y17) (@span_join (Z 8) 10 180 10 h8y18 h8y19)) (@span_join (Z 8) 20 200 20 (@span_join (Z 8) 10 200 10 h8y20 h8y21) (@span_join (Z 8) 10 220 10 h8y22 h8y23))) (@span_join (Z 8) 40 240 40 (@span_join (Z 8) 20 240 20 (@span_join (Z 8) 10 240 10 h8y24 h8y25) (@span_join (Z 8) 10 260 10 h8y26 h8y27)) (@span_join (Z 8) 20 280 20 (@span_join (Z 8) 10 280 10 h8y28 h8y29) (@span_join (Z 8) 10 300 10 h8y30 h8y31))))) (@span_join (Z 8) 40 320 5 (@span_join (Z 8) 20 320 20 (@span_join (Z 8) 10 320 10 h8y32 h8y33) (@span_join (Z 8) 10 340 10 h8y34 h8y35)) h8y36))

theorem h9y0 : span (Z 9) 10 0 = true := by decide +kernel

theorem h9y1 : span (Z 9) 10 10 = true := by decide +kernel

theorem h9y2 : span (Z 9) 6 20 = true := by decide +kernel

theorem z9 : span (Z 9) 26 0 = true := (@span_join (Z 9) 20 0 6 (@span_join (Z 9) 10 0 10 h9y0 h9y1) h9y2)

theorem h10y0 : span (Z 10) 1 0 = true := by decide +kernel

theorem z10 : span (Z 10) 1 0 = true := h10y0

theorem checkedE (s : Nat) (hs : s ≤ 10) : ∀ i < nsE s, Z s i = true := by
  interval_cases s

  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

  · exact fun i hi => span_ok z10 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs517) : False := by
  have h10 : NatRun (mask 232) (goal 232) 10 xs517 := extend_run h hs
  have p : xs517.Perm (stateE 10 0) := by decide +kernel
  exact barrier_all rotateE_ok checkedE 10 (by decide) 0 (by decide) (Run.perm p h10)


theorem noSub {s : Nat} {ws : List Nat} (hs : s ≤ 10) (hsub : ws.Sublist xs517)
    (h : NatRun (mask 232) (goal 232) s ws) : False := by
  by_cases eq : ws = xs517
  · subst ws
    exact noRunFull _ hs h
  · exact proper_fail517 _ (List.mem_sublists.2 hsub) eq (required h)

end Theta

def index (key : Nat) (j : Fin 689) : Fin 689 := Fin.ofNat 689 ((key >>> (10 * (j.val % 232))) &&& 1023)

def reindex (f : Fin 689 → Fin 689) (x : B) : B :=
  (BitVec.ofBoolListLE (List.ofFn fun j => x.getLsbD (f j).val)).cast List.length_ofFn

lemma reindex_bit (f : Fin 689 → Fin 689) (a : B) (j : Nat) (hj : j < 689) :
    (reindex f a).getLsbD j = a.getLsbD (f ⟨j,hj⟩).val := by
  rw [reindex, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have h : j < (List.ofFn fun x => a.getLsbD (f x).val).length := by simpa only [List.length_ofFn] using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

lemma reindex_and (f : Fin 689 → Fin 689) (a b : B) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_and, reindex_bit _ _ _ hj]

lemma reindex_or (f : Fin 689 → Fin 689) (a b : B) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, reindex_bit _ _ _ hj]

lemma reindex_not (f : Fin 689 → Fin 689) (a : B) :
    reindex f (~~~a) = ~~~reindex f a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_not, reindex_bit _ _ _ hj, hj, (f ⟨j,hj⟩).isLt, decide_true, Bool.true_and]

lemma reindex_zero (f : Fin 689 → Fin 689) : reindex f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [reindex_bit _ _ _ hj]
  simp

lemma reindex_top (f : Fin 689 → Fin 689) : reindex f top = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [top, reindex_bit _ _ _ hj, BitVec.getLsbD_allOnes, hj, (f ⟨j,hj⟩).isLt, decide_true]

def posKey0 : Nat := 0x5800c56c181211e2f0aa304e52ece306060180602a51e210c52fc601e0542a90403048211432f0ba2a86c4f0b906184480b94156031504394cb3895b32c782e8bf181244ac6c304785805458c181811e4f124394c1480bf06048120483151e1e0a938c482100c49104150601e0c84f1004906c2f0e4061842ece440d602a5043052e301634b884400e3120aa4ac6c39484580843946c12101390e358d5b400aa1b060180602a501030c5490601507838d2f21048030cc3912038c182e53c1b1062e93c619603152f56d0b578e542c5448124180bf4301858c54580783046c181012e4bf56d632e9241b0481204831501150a92a848030842fd2f1e060151462e4bb2fc18390bc1b106400bc61d602a52f58cca5ecc13280c2ecaa120e34301856c0c
def negKey0 : Nat := 0x279922599264896549523095a2f55f389394854200d5f3894240902569390000324c935694260c030149e4e40025983474bd4095f309023880538983001522e0c22f5790155f57d5f279922599264896549523b1793895f2f4b82980000d5f2f400409025e4b85080345d175e40060c030149e2e14225983474e24095f3b1022f4052f583509524e4ec3895a0155f57d5f27992549926495225896484e25e55f568b8308000155f5680060d83388b850805370dc388004080500c9e2e142549023f97960d5f485835680356902508964e5215e4bd00d5f57d5f27992549926495225896298bd5695f5e5393b1420155f5e54260d832f539000052d4b52f5424080500c9e4e400549023f95a60d5f299835e4035e502000962e0a6568e200d5f57d5f
def posKey1 : Nat := 0x318182fc6c150b3270c1290c526d241b0240902458cb318157294240f03030529060541818a2709d3047833c9a1b0d92d09a49cc655d2931566484bf5983c274a5090d05d4782903c318303106c090b333cd0314a42d0a51b0541505455cb30f1634905418018341290c0240f16533d1b34078271221b0d926d22498c658d292917828cc45e06046d24150c15d4783146031860314781511c48924310bf46cc11e0240902458d1c06157340240c03c490db1805406167488b44906c268cf1e128274cf35cc655cdb2fd80300c5600302d0d0090a56046c310303183c290780911c268a52fcc4274d01e0541505455d1c0c1633045406060294db0f0240c18b2689b2946c4889c1e12846c9c368c658cdb31169334a45a41826cc1151246046c2fc18
def negKey1 : Nat := 0x54992279926489e2d4b5554bd284c2485305a988028c248588495252f5300200a258962f58835c0a025524c008278d72c4a1494c25552548409484d7020b526555284cd024c2308c254992279926489e2d4b55e4cd484c22849957c08028c22840849525334996200a2acab3340835c0a0255226588278d72c521494c25e52528409284d7620b54c179484bd024c2308c2549922d592648b52789e5a921334c22f49955408024c22f40835cd7484996200945d17484084940902952265882d525464cd35cc25a8d72f40a2f5256209e4c16a334a1028c2308c2549922d592648b52789e57ca12f4c2335305e588024c23358835cd72853002009240902858849409029524c0082d525464bd35cc257cd73340a335250209e2655f2f521028c2308c2
def posKey2 : Nat := 0x560005543c120ad2a8bc294e12a0e00f0300c0302e8ad210c4290301b0242f0f3000482110d2a8a92f0783e0a10f16e2c0a13c958310f3384c9379553246c2a4a40c0d0344782946c5602455c3c0c0ad3e0d0384a52c0a40f04812048310ad1b0ba3804821000340f3090301b0c73e0ee340782a8df0f16e2a0df3c1582e8f3294d428d57350843b8e0120bc34478384845608438478120ef37ce055d553b8bc1e0300c0302e8ef000c4340300906c380d621048000cc37cb03803c284f81e0f42a4f85c158310d65550a578e1428242c0d00c0a44303c55c245606c294780c0ef284a4555572a4d01e04812048310ef090ba2f04800084290d61b03009111284a82903c37caa1e0f43b8aa5c9582e8d655cca5aca5328002a0bc120e04303c55400
def negKey2 : Nat := 0x2d5922419264890549523095a28555378f53350d00d553790d3c0f0568f50000324c935690d5b803004b53d4002416e2b4a13c155308f0378013796e00152298c22856a00555555552d5922419264890549523f96a37955284a62e00000d55284003c0f05a8a6434032acab5a8005b803004b52990d2416e2b4de3c1553f8f0284012856e435523d4fe3795a00555555552d592549926495224090334de5a955568a63080000555568005b96e378a643401370dc378003c00100cb52990d548f03b16a5b9553356e56803568f0434903d4cd5a8a100d55555552d5925499264952240902e0a1569555a8f53f90d005555a90d5b96e284f5000012789e2850d3c00100cb53d400548f03b15a5b9552e16e5a8035a8f000090298b8568de00d5555555
def posKey3 : Nat := 0x2e00c2e400150e23049c2f0bb395190008421084274e2180e1554841e0482717d030541813d305632703c4015b001033915b61cb83857d2eceb478b93ac7858d55210e03983c2f0782e0482e800210e2400e02ecbc391550005415054384e21e09d464541800c3817d120841e1644013c3803c305200010339520610b82757d2f0ea578ba3a8604f1191509c3983c2ec602e0602ec3c1517b481192e8b94f09c0f084210842757b030e13808412078464e91805403167480e44640056d000f18658d00418b8384e92e541300bb50448390e021155604002e8482e0782f03c2117b56d552e4ba58ce00f054150543857b1209d2705403060554e91e0841214056ce555400480c10f1864f0c1414b8274e92e969404bc5a40c3949c15119604002e40c
def negKey3 : Nat := 0x2419224d92648932d4b5554bd568b8475393793d028b84753d60d832f5390200a258962f53d4080a008904e40824d023895a60cb8555834740247502020b557d55568fe008b82e0b82419224d92648932d4b5464fe474b85695f26408028b85680860d833f95f4f40a370dc3f8084080a0089057d3d24d023891d60cb84658356802569024f4b54e519474bd008b82e0b8241922d592648b524c933791d3f8b82f55f55408008b82f408409024755f4f40245d174740860c020289057d3d2d5835e4fe408b8379022f40a2f5834f4934e4de3f95a028b82e0b8241922d592648b524c932655a2f4b83f9394653d008b83f93d409025693902002549525693d60c02028904e4082d5835e4bd408b8265023f80a3f9830209357c992f51d028b82e0b8
def posKey4 : Nat := 0x3000c2e454000a72f0bb3049c2a89d1506c1b06c464a70f12458c6c1e0182ed69030000f1262f1552ec602915b150c82855b594c0491692712f264b94bc78555631b0c54ac6030478300182fc541b0a7290c5270c1285631500000000490a71e119274000f00c315690606c1e184290a5314602f09a150c82a89a590c04656930525580bf4943c2949d000bb4ac602703c3003c27060001582689d2fcb9294bb1806c1b06c46558031243146c06078274cb0f00003186268a12745456ca418167554a4330c0490cb2e5292e09c4a418284c51b163604542fc1830078304601b15856d632e4bf554c5180000000049158061192ec000303c58ccb1e06c0612856caa58c54268bc18167294bc31cc0464cb2fd7d318c15f40c2a8bb0009d604542e40c
def negKey4 : Nat := 0x45d9225992648962d4b55e4b857cbd264a148525028bd26525020082e0a160c0a24c932e1250000a0151728583258002995f020bd5e408264052640060cb55697957cc2014bd2f4bd45d9225992648962d4b5464c2264bd57d5a47583028bd57d83020083095a4940a2789e309830000a01517569252580029899020bd4640857c0557c00494b528519264b8014bd2f4bd45d922d592648b52589648499308bd2e15a5e583014bd2e183000002655a4940524090265830200502917569252d408554c2000bd484002e00a2e00849496285213095f028bd2f4bd45d922d592648b5258964755f2e0bd308a146525014bd309250000057ca160c055495257d250200502917285832d408554b8000bd474003080a3080860c965691d2e099028bd2f4bd
def posKey5 : Nat := 0x57800554480f099294e12a8bc268ba1201806018380991e0e32a4181b00c384ca0003c1e103294a438484304a112164270a13215e38cca2f0e72e15539c6c290a9060e5398842a86c5780c56c4806099304e52f0aa270a91203c0f03c38c991b0e02e83c1e000394ca030181b0f0304bf39484294b912164268b931d5e380ca2a8e929d5b3a4782fcba0f0e1398842f078578782f0840f0c62e4ba56d552fce12101806018380c6000e3394180306c2e8eb1e03c000f42e49c2e848284c1210cc290c15955e38ceb55504560bc4100c270e5060a94304856c0c5786c2a884060c6284a95555b290e52103c0f03c38cc6030e03843c000782a4eb1b018031062849a2a4482e4a5210cc2fca559d5e380eb56cf3580aa3cc00268e10f0ba4304855400
def negKey5 : Nat := 0x3719224d9264893549523b1552995a2e0bd3890200d5a2e10200000554bd3c003240905550202003008dc2f4f024c08264a60015a3b0002e0022e0083c152284ec2995f0095a5695a3719224d9264893549523f95f2e15a298a1378f000d5a298f00000057ca1408032589657cf002003008dc2850224c08264b80015a3f8002980229808409522f4fe2e1550095a5695a37192549926495224c93388b857d5a554a13b0f00095a554f0020082e0a1408022d4b52e0f00000200cdc28502548003095f0215a388085540355400408932f4e257ca600d5a5695a37192549926495224c93378a65555a57cbd3f9020095a57d0202008298bd3c0022789e299020000200cdc2f4f054800309550215a3780857c0357c003c093284de554b800d5a5695a
def posKey6 : Nat := 0x29c002840c090de2949a2a8a8384ae030842108426cde0c0e556c841b0482696f000240c0fa29557268183b955030f037d555c8a73956f2a0eb2b4a13ac6c55d5b210e3398182a86c29c482a40c210de3b8e32a0aa37d5b0302409024394de1b09b2b8240c00038d6f120841b1643b8f838c18294b0030f0384b05b8a726d6f2a8e8578a93a0303e0ae0909a398182a03029c302a0180916b2c0ae2a4a13e09a060842108426d6b000e538c841206c2b8e70c024001652c0df2b80c554ee0617055cee3d0a7394e7284fd28ca83f44837ce32115b5d40c2a44829c6c2a8182116b5555b284a955ce306024090243956b1209b268240003056ce71b084120fb554e156c0c2c0a5061703e0a53c8a726ce72a5663bcaa598003849a090ae5d40c28400
def negKey6 : Nat := 0x2599224d92648932789e57ca1568a62b4f5388f9024a62b4f95b96e284f50200924090284f93c009008963d40824cf03795a5b8a657d6e2b4022b4f00209e5555f568ec008a6298a62599224d92648932789e2c4ec2b4a65695526408024a6568085b96e3b1553e409370dc3b0083c00900896554f924cf0378ad5b8a62c56e56802568f03e49e3d4b12b4a1008a6298a625992279926489e24c93388ad3b0a62855557c08008a6284083c0f02b5553e4022acab2b4085b80202496554f92796e5a8ec3c0a6388f0284092856e3e4933d4e23b15a024a6298a625992279926489e24c932655a284a63b0f52c4f9008a63b0f93c0f0568f50200254952568f95b802024963d4082796e5a8a13c0a6264f03b0093b16e0209355499284ad024a6298a6
def posKey7 : Nat := 0x28c0028424030b82a8a82949a2f09b090781e0782b8b8060d055c781b03c2a1660000c060d72a95b2a0302fd55090c72e55559ca334166268d6264a13586c56d571e0c4344302946c28c3c290241e0b82fcc4268a52e5570900c0300c340b81b0ae26c0c06000311660f0781b16e2fcc1310302a89c090c72f09c590a32b966294d2560a4348183049b030a8344302681828c1826830031602709b290a1304a80c0781e0782b960000d0310780f06c26cc90600c00170270b926c24554bf0c16556cbf330a3340c9284db29c9a36c3c2e4c41e1575d4242903c28c6c294301e16055557284a456cc40c00c0300c341600f0ae2a00c0001855cc91b0780f0d9554bc55c24270aa0c165304aa320a32b8c92916f318a55bc002f0a80309b5d42428400
def negKey7 : Nat := 0x2ad9224192648902789e5a8a6554a1264bd334d7024a1264d702008298bd5b80924c93298d700009004ab2f56e240002e155020a15a80826401264005b89e5696a554c2004a1284a12ad9224192648902789e2c4c2264a15555a2b56e024a15556e020083095a35c092d4b53096e00009004ab568d7240002e099020a12c408554015540035c9e2f4b1264a6004a1284a12ad92279926489e2409033499308a12995a5a96e004a12996e000002655a35c01258962656e02001024ab568d72780857cc2000a133400298092980835c902f4cd30955024a1284a12ad92279926489e240902b555298a1308bd2c4d7004a1308d700000554bd5b80154952554d702001024ab2f56e2780857ca6000a12b40030809308085b890568ad29899024a1284a1
def posKey8 : Nat := 0x2642426c000c0cd2d0ae2749a33ca100060180602a0cd060bb464601503c2b92509030060c72d1222b80c2fd1b000d73111b4a0992ed25268d528c9b3545448919180b93440c274542643c27000180cd2fcb92689d31119000300c0302eccd150a828430060242e5250f060151342fcc52e40c2d0a4000d733ca449c992a125274c94709c32418314a10c0ae3440c26818264182680c0c121290a12709b314ae03060180602a121090bb2e4600f054284d20603009135290c42840046cbf03126488bf368992ecd226ccb2cc9a32c3c310b9181194ac002703c264542740c1812146d1926c9c488b9030300c0302ed210f0a82b83009018464d2150600f0c846ccf46400290b403126314b4364992a0d22712c3009d4b02433cae0c0a14ac0026c24
def negKey8 : Nat := 0x24d92241926489025896474b146499284c22e0000149928400495252c4c24d0052acab2c40035c050049330934240d733519494994752528401284d74d0964c11d464bd004992649924d92241926489025896298bd28499465302b5340149946534495252f530000052d4b52f53435c05004934c000240d7334a1494992992546401464d700096308a6284b1004992649924d922599264896240902e0a12f4992c53047534004992c53435cd728530000012789e2853449401014934c00025925484bd35c992e0d72c4052c52500090308b82f519014992649924d922599264896240902b5192c4992f4c229800004992f40035cd7464c24d00145d174640049401014933093425925484b135c992b4d72f4052f5254d0904c0ad2c4a10149926499
def posKey : Fin 9 → Nat := ![posKey0,posKey1,posKey2,posKey3,posKey4,posKey5,posKey6,posKey7,posKey8]
def negKey : Fin 9 → Nat := ![negKey0,negKey1,negKey2,negKey3,negKey4,negKey5,negKey6,negKey7,negKey8]
def slice (i : Fin 9) (a : Sig) : Sig :=
  (reindex (index (posKey i)) a.1, reindex (index (negKey i)) a.2)

lemma slice_neg (i : Fin 9) (a : Sig) : slice i (neg a) = neg (slice i a) := by
  simp [slice, neg, reindex_not]

lemma slice_bin (i : Fin 9) (d : Bool) (a b : Sig) :
    slice i (bin d a b) = bin d (slice i a) (slice i b) := by
  cases d <;> simp [slice, bin, reindex_and, reindex_or]

lemma slice_target (i : Fin 9) : slice i target = target :=
  Prod.ext (reindex_top _) (reindex_zero _)


def face (i : Fin 9) : Projection := ⟨slice i,slice_neg i,slice_bin i,slice_target i⟩
def thetaWord (a : Sig) : Nat :=
  ((a.1.toNat &&& Theta.lo 232) <<< 232) ||| (a.2.toNat &&& Theta.lo 232)

lemma thetaWord_bit (a : Sig) (j : Nat) :
    (thetaWord a).testBit j =
      if j < 232 then a.2.getLsbD j else if j < 464 then a.1.getLsbD (j-232) else false := by
  simp only [thetaWord, Theta.lo, Nat.testBit_or, Nat.testBit_and, BitVec.testBit_toNat,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft]
  by_cases hj : j < 232
  · simp [hj, show ¬ 232 ≤ j by omega]
  · by_cases hk : j < 464
    · simp [hj, hk, show 232 ≤ j by omega, show j - 232 < 232 by omega]
    · simp [hj, hk, show 232 ≤ j by omega, show ¬ j - 232 < 232 by omega]

lemma thetaWord_target : thetaWord target = Theta.goal 232 := by decide +kernel

lemma thetaWord_neg (a : Sig) :
    thetaWord (neg a) = thetaWord a ^^^ Theta.mask 232 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, thetaWord_bit, thetaWord_bit]
  by_cases hl : j < 232
  · simp [hl, neg, Theta.mask, Theta.lo, BitVec.getLsbD_not, show j < 689 by omega,
      show j < 464 by omega]
  · by_cases hh : j < 464
    · simp [hl, hh, neg, Theta.mask, Theta.lo, BitVec.getLsbD_not, show j - 232 < 689 by omega]
    · simp [hl, hh, Theta.mask, Theta.lo]

lemma thetaWord_bin (d : Bool) (a b : Sig) :
    thetaWord (bin d a b) = if d then thetaWord a ||| thetaWord b else thetaWord a &&& thetaWord b := by
  apply Nat.eq_of_testBit_eq
  intro j
  cases d <;> simp only [bin, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_or,
    Nat.testBit_and, thetaWord_bit, BitVec.getLsbD_or, BitVec.getLsbD_and] <;>
    split_ifs <;> rfl

lemma live_run {k t S} (h : Live k t S) (v : List Sig) (hv : v.Nodup)
    (he : v.toFinset = S) :
    Theta.Run neg (bin false) (bin true) target k v := by
  induction h generalizing v with
  | stop =>
    have hp : ([target] : List Sig).Perm v :=
      List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [he])
    exact Theta.Run.perm hp Theta.Run.done
  | @unary k t U a ha hf tail ih =>
    let rest := dropped [a] v
    have ham : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hn, eq⟩ := edit_list (del := [a]) hv (by simp) (by simpa using he)
    let save := decide (a ∈ U)
    have hkeep : Theta.kept save a rest = keepOf U [a] ++ rest := by
      by_cases hm : a ∈ U <;> simp [save, Theta.kept, keepOf, hm]
    rw [← hkeep] at hn eq
    have hs : (neg a :: Theta.kept save a rest).toFinset = insert (neg a) U := by
      rw [List.toFinset_cons, eq]
    have hnd : (neg a :: Theta.kept save a rest).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem ?_), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := recover_perm [a] v hv (by simp) (by simpa using ham)
    exact Theta.Run.perm p.symm (Theta.Run.one true save (ih _ hnd hs))
  | @binary k t U a b d ha hb hab hf tail ih =>
    let rest := dropped [a,b] v
    have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨hn, eq⟩ := edit_list (del := [a,b]) hv (by simp [hab]) (by simpa using he)
    let sa := decide (a ∈ U)
    let sb := decide (b ∈ U)
    have hkeep : Theta.kept sa a (Theta.kept sb b rest) = keepOf U [a,b] ++ rest := by
      by_cases ham : a ∈ U <;> by_cases hbm : b ∈ U <;>
        simp [sa, sb, Theta.kept, keepOf, ham, hbm]
    rw [← hkeep] at hn eq
    have hs : (bin d a b :: Theta.kept sa a (Theta.kept sb b rest)).toFinset = insert (bin d a b) U := by
      rw [List.toFinset_cons, eq]
    have hnd : (bin d a b :: Theta.kept sa a (Theta.kept sb b rest)).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := recover_perm [a,b] v hv (by simp [hab]) (by simpa using And.intro ah bh)
    have done := ih _ hnd hs
    cases d
    · exact Theta.Run.perm p.symm (Theta.Run.two true sa sb done)
    · exact Theta.Run.perm p.symm (Theta.Run.two false sa sb done)

def thetaInputOrder : Fin 9 → List Sig := ![[raw2,raw8,raw3,raw1,raw6,raw7,raw5],[raw3,raw5,raw8,raw2,raw7,raw4,raw0],[raw0,raw8,raw5,raw1,raw6,raw4,raw3],[raw1,raw5,raw0,raw2,raw7,raw6,raw8],[raw2,raw5,raw7,raw1,raw0,raw3,raw8],[raw1,raw8,raw6,raw0,raw5,raw2,raw3],[raw1,raw3,raw2,raw0,raw4,raw6,raw8],[raw0,raw3,raw4,raw1,raw2,raw5,raw8],[raw0,raw2,raw1,raw4,raw3,raw5,raw7]]
def thetaInputs (i : Fin 9) := (thetaInputOrder i).map (slice i)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaInputs_word (i : Fin 9) : (thetaInputs i).map thetaWord = Theta.xs517 := by fin_cases i <;> decide +kernel
lemma thetaWords_nodup : Theta.xs517.Nodup := by decide +kernel

lemma thetaInputs_nd (i : Fin 9) : (thetaInputs i).Nodup := by
  have h := thetaWords_nodup
  rw [← thetaInputs_word i] at h
  exact List.Nodup.of_map _ h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta_image (i : Fin 9) : raw.toFinset.image (slice i) = insert zero (thetaInputs i).toFinset := by fin_cases i <;> decide +kernel
lemma root_project_impossible (i : Fin 9) : ¬ Feasible (face i) 10 raw.toFinset := by
  rintro ⟨m, hm, t, T, h, hs⟩
  change T ⊆ raw.toFinset.image (slice i) at hs
  rw [theta_image] at hs
  have ht : ∀ a ∈ T, a ∈ thetaInputs i := by
    intro a ha
    rcases Finset.mem_insert.mp (hs ha) with eq | hmem
    · exact False.elim ((live_proper h _ ha).1 eq)
    · exact List.mem_toFinset.mp hmem
  let v := (thetaInputs i).filter (fun a => decide (a ∈ T))
  have he : v.toFinset = T := by
    ext a
    simp only [v, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨ht _ ha, ha⟩⟩
  have hh := live_run h v ((thetaInputs_nd i).filter _) he
  have hr := Theta.Run.map (inv' := (· ^^^ Theta.mask 232))
    (meet' := (· &&& ·)) (join' := (· ||| ·)) thetaWord thetaWord_neg
    (fun a b => thetaWord_bin false a b) (fun a b => thetaWord_bin true a b) hh
  rw [thetaWord_target] at hr
  apply Theta.noSub hm _ hr
  have sub := List.Sublist.map thetaWord (List.filter_sublist (l := thetaInputs i) (p := fun a => decide (a ∈ T)))
  rwa [thetaInputs_word] at sub


def special : List Sig := []
inductive Restricted : Nat → Nat → Finset Sig → Prop
  | stop : Restricted 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hf : neg a ∉ insert a U) (hr : a ∉ special)
      (tail : Restricted k t (insert (neg a) U)) :
      Restricted (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin d a b ∉ insert a (insert b U))
      (hra : a ∈ special → d = true ∧ a ∉ U)
      (hrb : b ∈ special → d = true ∧ b ∉ U)
      (tail : Restricted k t (insert (bin d a b) U)) :
      Restricted (k+1) t (insert a (insert b U))

lemma Restricted.live {k t S} (h : Restricted k t S) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary ha hf _ _ ih => exact Live.unary ha hf ih
  | binary ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih

-- A frontier contains the distinct values still needed by gates that follow it.
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
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Restricted m t (insert (neg a) U))
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
  exact ⟨by simp [ha], gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Restricted m t (insert (bin d a b) U))
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
      gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l.live hle (live_proper l.live _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Restricted m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Restricted m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
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
    (h : Restricted m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Restricted l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Restricted l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h.live
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  cases h with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf hr tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf hr tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf hra hrb tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Restricted m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    cases h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl


lemma all_restricted {k t : Nat} {S : Finset Sig} (h : Live k t S) : Restricted k t S := by
  induction h with
  | stop => exact Restricted.stop
  | unary ha hf tail ih => exact Restricted.unary ha hf (by simp [special]) ih
  | binary ha hb hab hf tail ih =>
    exact Restricted.binary ha hb hab hf (by simp [special]) (by simp [special]) ih

theorem map_zero (i : Projection) : i.project zero = zero := by
  have eq : bin false target (neg target) = zero := by decide +kernel
  calc
    i.project zero = i.project (bin false target (neg target)) := congrArg _ eq.symm
    _ = zero := by rw [i.project_bin,i.project_neg,i.project_target,eq]

theorem map_one (i : Projection) : i.project one = one := by
  rw [← neg_laws.1,i.project_neg,map_zero]

def allEssential (v : List Sig) : Bool :=
  v.all fun a => unionSep true (v.erase a) != top

theorem essential_wires {k t S} {v : List Sig} (h : Live k t S)
    (sub : S ⊆ v.toFinset) (needed : allEssential v = true) : S = v.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  by_contra hn
  have fail := List.all_eq_true.mp needed a (List.mem_toFinset.mp ha)
  have cov : unionSep true (v.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,hh⟩ := live_sep h i hi
    have ba : b ≠ a := fun eq => hn (eq ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (List.mem_toFinset.mp (sub hb))
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi hh⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

def proofSearch (v : List Sig) (k : Nat) : Bool :=
  v.length > k+1 || (List.range (k+2-v.length)).all (fun t => !(search k t v))

theorem excludeGraph {v : List Sig} {k : Nat} (hn : v.Nodup) (key : allEssential v = true)
    (check : proofSearch v k = true) : ¬ possible v.toFinset k := by
  rintro ⟨m,t,S,hm,hl,sub⟩
  obtain rfl := essential_wires hl sub key
  have len := (live_size hl).2
  rw [List.toFinset_card_of_nodup hn] at len
  simp only [proofSearch,Bool.or_eq_true,decide_eq_true_eq] at check
  rcases check with impossible | cert
  · omega
  · have test := List.all_eq_true.mp cert t (List.mem_range.mpr (by omega))
    have found := search_complete (all_restricted hl) k hm v hn rfl
    simp [found] at test

def packedIndex (key : Nat) (j : Fin 689) : Fin 689 :=
  Fin.ofNat 689 ((key >>> (10*(j.val % 403))) &&& 1023)

def rowsMap (kp kn : Nat) (s : Sig) : Sig :=
  (reindex (packedIndex kp) s.1, reindex (packedIndex kn) s.2)

def rowsProjection (kp kn : Nat) : Projection where
  project := rowsMap kp kn
  project_neg := by intro a; simp [rowsMap,neg,reindex_not]
  project_bin := by intro d a b; cases d <;> simp [rowsMap,bin,reindex_or,reindex_and]
  project_target := Prod.ext (reindex_top _) (reindex_zero _)

def wideIndex (key : Nat) (j : Fin 689) : Fin 689 :=
  Fin.ofNat 689 ((key >>> (10*j.val)) &&& 1023)

def wideMap (kp kn : Nat) (s : Sig) : Sig :=
  (reindex (wideIndex kp) s.1, reindex (wideIndex kn) s.2)

def wideProjection (kp kn : Nat) : Projection where
  project := wideMap kp kn
  project_neg := by intro a; simp [wideMap,neg,reindex_not]
  project_bin := by intro d a b; cases d <;> simp [wideMap,bin,reindex_or,reindex_and]
  project_target := Prod.ext (reindex_top _) (reindex_zero _)

def transferOK (i : Projection) (src dst : List Sig) (k m : Nat) : Bool :=
  let ws := src.map i.project
  decide (k < m+1+(ws.filter (fun a => decide (a = zero ∨ a = one))).length) &&
    ws.all (fun a => a == zero || a == one || dst.contains a)

theorem transferLower {src dst : List Sig} {k m} (i : Projection) (hn : src.Nodup)
    (hs : allEssential src = true) (check : transferOK i src dst k m = true)
    (lower : ¬ possible dst.toFinset m) : ¬ possible src.toFinset k := by
  rintro ⟨q,t,S,hq,hl,sub⟩
  have es := essential_wires hl sub hs
  subst S
  obtain ⟨small,inBudget,j,hj,u,T,lt,st⟩ := project_live_cost hl i
  obtain ⟨hlim,fromSrc⟩ := Bool.and_eq_true_iff.mp check
  have count : ((src.map i.project).filter (fun a => decide (a = zero ∨ a = one))).length =
      constants i src.toFinset := by
    rw [List.filter_map,List.length_map]
    unfold constants
    rw [List.filter_toFinset, List.toFinset_card_of_nodup (hn.filter _)]
    simp [Function.comp_def]
  have lim := of_decide_eq_true hlim
  change k < m+1+((src.map i.project).filter (fun a => decide (a = zero ∨ a = one))).length at lim
  rw [count] at lim
  apply lower
  refine ⟨j,u,T,by omega,lt,?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (st ha)
  have ok := List.all_eq_true.mp fromSrc _ (List.mem_map.mpr ⟨b,List.mem_toFinset.mp hb,rfl⟩)
  have hp := live_proper lt _ ha
  simpa [hp.1,hp.2] using ok

def recovers (i j : Projection) (a : Sig) : Prop := j.project (i.project a) = a

lemma recover_inj (i j : Projection) {a b : Sig} (ha : recovers i j a)
    (hb : recovers i j b) (eq : i.project a = i.project b) : a = b :=
  ha.symm.trans ((congrArg j.project eq).trans hb)

lemma recover_neg {i j : Projection} {a : Sig} (ha : recovers i j a) :
    recovers i j (neg a) := by
  unfold recovers at *
  rw [i.project_neg,j.project_neg,ha]

lemma recover_bin {i j : Projection} {a b : Sig} (op : Bool)
    (ha : recovers i j a) (hb : recovers i j b) : recovers i j (bin op a b) := by
  unfold recovers at *
  rw [i.project_bin,j.project_bin,ha,hb]

lemma recover_proper (i j : Projection) {a : Sig} (ha : recovers i j a)
    (properA : proper a) : proper (i.project a) := by
  constructor
  · intro eq
    exact properA.1 (ha.symm.trans ((congrArg j.project eq).trans (map_zero j)))
  · intro eq
    exact properA.2 (ha.symm.trans ((congrArg j.project eq).trans (map_one j)))

theorem live_relabel {k t S} (h : Live k t S) (i j : Projection)
    (roundtrip : ∀ a ∈ S, recovers i j a) : Live k t (S.image i.project) := by
  induction h with
  | stop => simpa [i.project_target] using Live.stop
  | @unary k t U a pa fresh tail ih =>
    have ra := roundtrip a (Finset.mem_insert_self _ _)
    have rz := recover_neg ra
    have nextRun := ih (by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact rz
      · exact roundtrip _ (Finset.mem_insert_of_mem hc))
    have new : i.project (neg a) ∉ (insert a U).image i.project := by
      rintro hm
      obtain ⟨b,hb,eq⟩ := Finset.mem_image.mp hm
      exact fresh (recover_inj i j (roundtrip b hb) rz eq ▸ hb)
    simp only [Finset.image_insert,i.project_neg] at nextRun new ⊢
    exact Live.unary (recover_proper i j ra pa) new nextRun
  | @binary k t U a b op pa pb ab fresh tail ih =>
    have ra := roundtrip a (Finset.mem_insert_self _ _)
    have rb := roundtrip b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz := recover_bin op ra rb
    have nextRun := ih (by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact rz
      · exact roundtrip _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)))
    have new : i.project (bin op a b) ∉ (insert a (insert b U)).image i.project := by
      rintro hm
      obtain ⟨c,hc,eq⟩ := Finset.mem_image.mp hm
      exact fresh (recover_inj i j (roundtrip c hc) rz eq ▸ hc)
    simp only [Finset.image_insert,i.project_bin] at nextRun new ⊢
    exact Live.binary (recover_proper i j ra pa) (recover_proper i j rb pb)
      (fun eq => ab (recover_inj i j ra rb eq)) new nextRun

theorem symmetry_excludes {m q t : Nat} {s dst : Finset Sig} (i j : Projection)
    (back : ∀ a ∈ s, recovers i j a) (same : s.image i.project = dst)
    (lower : ∀ k ≤ m, ∀ u, ¬ Live k u dst) (hq : q ≤ m) : ¬ Live q t s := by
  intro h
  exact lower q hq t (same ▸ live_relabel h i j back)

def NoSuffix (k : Nat) (s : Finset Sig) : Prop := ∀ q ≤ k, ∀ t, ¬ Live q t s

theorem theta_base : ¬ possible (thetaInputs 0).toFinset 10 := by
  rintro ⟨k,t,S,hk,hl,sub⟩
  apply root_project_impossible 0
  refine ⟨k,hk,t,S,hl,?_⟩
  change S ⊆ raw.toFinset.image (slice 0)
  rw [theta_image]
  exact Finset.Subset.trans sub (Finset.subset_insert _ _)

def wires3 : List Sig := [(0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe8fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd1),(0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_3 : ¬ possible wires3.toFinset 0 := by
  apply excludeGraph
  all_goals decide +kernel

def wires7 : List Sig := [(0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb6dd9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6dbb3,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc92c8ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff92591),(0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1010300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020206),(0x5b7ae000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b6f5c,0x60e4c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c1c98)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_7 : ¬ possible wires7.toFinset 1 := by
  apply excludeGraph
  all_goals decide +kernel

def wires15 : List Sig := [(0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffd6dd79f53c6f26bccefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffadbaf3ea78de4d799d,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffa9228664861e122c8cfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff52450cc90c3c245919),(0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffe7efbffc7f4fcdbf6afffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfdf7ff8fe9f9b7ed5,0x4210409210c0099262000000000000000000000000000000000000000000000000000000000000000000000000000000000008420812421801324c4),(0x7b77dedfcbfcfb5fb500000000000000000000000000000000000000000000000000000000000000000000000000000000000f6efbdbf97f9f6bf6a,0xc0815200a0ab005050000000000000000000000000000000000000000000000000000000000000000000000000000000000018102a401415600a0a),(0x7c79d4eba1b9bafadd00000000000000000000000000000000000000000000000000000000000000000000000000000000000f8f3a9d7437375f5ba,0x7007e01455b1011ad800000000000000000000000000000000000000000000000000000000000000000000000000000000000e00fc028ab620235b0)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_15 : ¬ possible wires15.toFinset 3 := by
  apply excludeGraph
  all_goals decide +kernel

def wires45 : List Sig := [(0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffd7aff97d737e65fdaefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaf5ff2fae6fccbfb5d,0xa9006b808b404ad8a0000000000000000000000000000000000000000000000000000000000000000000000000000000000015200d701168095b14),(0x7af6bfeebdb79b76f300000000000000000000000000000000000000000000000000000000000000000000000000000000000f5ed7fdd7b6f36ede6,0x230941940184525ab200000000000000000000000000000000000000000000000000000000000000000000000000000000000461283280308a4b564),(0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffcfadff79df5bf16d9ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9f5bfef3beb7e2db3,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffcc0434485829298449fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff98086890b052530893),(0x1fffffffffffffffffffffffffffffffffffffffffffffffffffff9f3df5bb666f75fb2ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3e7beb76ccdeebf65f,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffff002e044844a4b1225fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe005c089089496244b)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_45 : ¬ possible wires45.toFinset 2 := by
  apply excludeGraph
  all_goals decide +kernel

def wires51 : List Sig := [(0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x800001000100452200000000000000000000000000000000000000000000000000000000000000000000000000000000000010000020002008a44),(0x356aad9de3cdb0ae57000000000000000000000000000000000000000000000000000000000000000000000000000000000006ad55b3bc79b615cae,0x5515526ae1aca81a5500000000000000000000000000000000000000000000000000000000000000000000000000000000000aa2aa4d5c3595034aa),(0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffd9b331ef546f2772a5fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb36663dea8de4ee54b,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffe60c8b56a968e53085fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc1916ad52d1ca610b),(0x1fffffffffffffffffffffffffffffffffffffffffffffffffffff9e3c7b499b1a5c7f4cfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3c78f6933634b8fe99,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffff803be06658279324cffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0077c0ccb04f26499)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_51 : ¬ possible wires51.toFinset 2 := by
  apply excludeGraph
  all_goals decide +kernel

def wires31 : List Sig := [(0x1ffffffffd55eb6d7ffd596aafdcfcccece7777d659abdbc7ce715daaa51dd64bd954eb2ffffffffffffffffffffffffffffffffffffffaabd6dafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0xa4149280a104911023030020382461c1404e10b070243a00185440a1940e220000000000000000000000000000000000000014829250142092220460600407048c382809c2160e048740030a88143281c44),(0x1ffffffffe66b3f7aeff6a37937f52b953dd4f7feb9a0d7fcbd68d5ade96aa3eb3c999a5ffffffffffffffffffffffffffffffffffffffccd67ef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0x1ffffffffd08a108551088086880a0e218041b1030b41020080c1b400c26823412419085ffffffffffffffffffffffffffffffffffffffa114210aa211010d10141c4300836206168204010183680184d04682483210b),(0x7873db9f79f9e47fc6f9ff2b3daab64ab3ffe6b3290cbbc535eb71b5feca35600000000000000000000000000000000000000f0e7b73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0x31060608686180010a490506b24084c008091a26b040134358210808a80352000000000000000000000000000000000000000620c0c10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7f83e3e3feabdbffd1a3b73a6b79fe25eedea26e109e2f5c5ef54adfb773a4900000000000000000000000000000000000000ff07c7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x1c03801c011024322e03248100022512920c0c48949a2a080041261915728010000000000000000000000000000000000000038070038022048645c06490200044a25241818912934541000824c322ae5002),(0x1fffffffffffc03fc7f3b7fb228fed37fc25b6d79c7addb7b52f744526b5f1fb8e32551ffffffffffffffffffffffffffffffffffffffffff807f8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0x1ffffffffe01c0003b4c48044410009387031808008b1128060218450ba1800a0e20511cffffffffffffffffffffffffffffffffffffffc03800076989008882001270e063010011622500c04308a174300141c40a239)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_31 : ¬ possible wires31.toFinset 6 := by
  apply excludeGraph
  all_goals decide +kernel

def wires47 : List Sig := [(0x1fffff5deb6effffae7d57d73ee9adce73ddffeb5b5bdbe7ddc69dbd6c2eef92bdab5abaffffffffffffffffffffffffffffffffffebbd6ddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x901491005021008808c00600401c090c0e1004e0830e0083900604a200a18a1a220000000000000000000000000000000000120292200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0x1fffff96b3f75f7f6a9bc9bfe5c558b9ed53efbfbb48d7fcbbb595bee5c951f9b3c595acfffffffffffffffffffffffffffffffffff2d67eebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0x1ffffe24a108a488921434401a51c2240106b2510e89030081175424415811531241848cffffffffffffffffffffffffffffffffffc49421149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x1e73dbbedcff7b3fe3bf9fff371eeaafc35b7ffe55b32397be2bfdbb46d5fd6a75700000000000000000000000000000000003ce7b77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0xc106041032084000828422040358900026010090d2760801123e0104200894035200000000000000000000000000000000001820c0820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x1f83e3c75f2574ffe86abb6f34b59e7fc02edbea136006c6f6a1bf6a1b7fb7b364900000000000000000000000000000000003f07c78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x10638038a0ca0b191782bd4a8380208db59941c0e2088746a2c01929b87916b3409000000000000000000000000000000000020c70071419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0x1fffffffc03f85fcf5ed9143d66a57f6136ddb6cc755d9bb45da846525bf8fee8e384d1ffffffffffffffffffffffffffffffffffffff807f0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0x1ffffe07c0007ba78a1222242951331b82c651d0096913406097246470ba08ab0e30451dffffffffffffffffffffffffffffffffffc0f8000f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_47 : ¬ possible wires47.toFinset 4 := by
  apply transferLower (dst := wires15) (rowsProjection 0xf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73dcf73f8fd3f0fb3e8f93e0f73f8fd3f0fa3e4f83f8fd3f0f73f8f93f4f83dcfe3f8fa3e4fd3e4fb3f0fb3e0fa3dcf93dcf83f4fb3e4fc3ecfe3e4f73e8fd3e0fc3ecfd3dcfc3e0fa3ecfa3f8fe3e4fd3e0fc3e8f83ecfa3f0f73ecf7 0x1054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415054150541505415053f8fd4250841d06415044110541907424fd424fd3f90941d044210541d06415083f9043f50641105425043f9073f508424fe419093f50841508425074110742106411053f906411053f8fd420fe41cfd3f906424fd4210641d05) (by decide +kernel) (by decide +kernel) _ graph_15
  decide +kernel

def wires55 : List Sig := [(0x1ffff7bdedfffffefbef7efd7dfe9fe75e7ef7fe75fff7f3b6f3bff6bf8bb9fcaf5975f5fffffffffffffffffffffffffffffffffef7bdbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x40092000140000080028000002003808080c001808183002190008110200848244400000000000000000000000000000000008012400028000010005000000400701010180030103060043200102204010904888),(0x1ffffad6bedbfdfddcd69d7eca65785cedaddefbfbe9cdfe6d6e7bbf64f66697dce78b5affffffffffffffffffffffffffffffffff5ad7db7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0x1fffe8922124222210a142013527001210234545218a05002046ca2230520412b4a18918fffffffffffffffffffffffffffffffffd12442484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0x1ce7376d2f3f3d97e14ef27fe1b8edd15f83baff896dcd8c5da947f6d6cb57e69e2f00000000000000000000000000000000039ce6eda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x1124c092c4c8ca08149a08103681cb142a22d04162e95f80115907844ae9024616270000000000000000000000000000000002249812589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0x1f07c78e6bc93277f4ab57d3d325db3bd5a05f5d231b001b176d1b799abdbebb1c930000000000000000000000000000000003e0f8f1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0x1c70071d4328d8d1b505662ba9c50407b7538183c50609e146e1a648f9c34331893000000000000000000000000000000000038e00e3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0x1ffffff807f02ff3a76d1a0eac3965fb426af1768cf3f1ddd2f4b22a86ebc95763927a3cffffffffffffffffffffffffffffffffffff00fe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0x1fffe1f8000fda9ed89021a152a4c30db05b393d116a456058a6d2222c2a8b0d73925a38fffffffffffffffffffffffffffffffffc3f0001fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_55 : ¬ possible wires55.toFinset 4 := by
  apply transferLower (dst := wires15) (rowsProjection 0xfd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd40d00404ff408fe3f0fd40d00405023f8fc40d00404fd40cfe400fc3f50340d023f9003f8ff404ff3f1023f4fe3f4fc400ff3f9013fd033f8fd409003f1013fd003f5013f1023fd0240d033f9003f101408fc3fd02404fd3fcfd 0x10d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d4350d409034050042d0c4350a4290d4310b40503405034090142d0a4010d42d0c435004090a40d0c4290d4050a4090b40d00405024310140d00435004050b4290b4010c4290d4090c4290d409034010242d034090c405034010c42d0d) (by decide +kernel) (by decide +kernel) _ graph_15
  decide +kernel

def wires63 : List Sig := [(0x6f5bfcfd78c4d6bb6d3ee0d35a75790f592a6f2570fba28dd9a6ca2b7e8c749a6d8b9a4d55ebbd55eb6566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x10c600084200014484002a80298225002080044016803000980060022000c4090610310452000a40014800000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0x9bc2454a77b5f364abcedac82a9cf5381e43d3ea5708ff157211fd6f251e194cd839273e66b2d666b3f5ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x209cc0085dd88005b988568066042c08964103c08748ba007211e801a012184c88282728452508a4a1395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0x17de0116b977fad18d397192c26ead395665892b76f184d7abbf5359d595f2b9513b4b197873ce7873d8e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x9021024a2042088060629040188419528888837481244500964130c484521101394909188483109060621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x1ce34a27ec2db787e1851573e957e4ee1b4f7c05d8d8596ea974998f3c37bd2e9c74645a7f83f07f83e1bb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1809409d2404a56543851941b8472084214124000060090a83202c0e1832ad2a9440205260181c030382900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0x1b8565eb9ee3371cd446867f6c905077085ad26eac49ddd384dffb6e0f671c462b0f0f6afffc007ffc03ded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x200324081b25000186284360610423b081ad03b880a845004dd117005c11044290f0e2880e0e01c1c006a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x1699b2e556f31e87911a512311b9ade7d7714e033276efe31d954348afc0be501ee20fd7fffff800001ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x9314e4739959829399b142210119adb9e46c0a8212749f2253c1434caf60be401ee00f900ff001fe00097dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_63 : ¬ possible wires63.toFinset 7 := by
  apply transferLower (dst := wires31) (rowsProjection 0x16f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5e9795e1775d9755d1735c9715c16f5b96d5b16b5a9695a1675997a5e5785d9755c9715c16d5ad695e97a5e17a5d9765c96d5a1795c977599755e16d5dd715d1735c1765d5745b17a5e56d5a9785b16b5ad6f5a56e5a1675a57a5c9795c5705bd745b5785c16c5dd685ad795e5665b9775d5785bd785c56e5d16c59d6d5a1745b1675d96b5d977599705d16c5d97a5b5735e96d5bd665c9755bd715a5685cd795d16c5a1695cd775c97a5a9725a9785dd6b5c17a5c96a5bd6e59d7a5bd685d9795c5755a5785c1665b9675d5685996e59d735bd6f5d16c5dd735b9675bd6a5a16b5d96a5b5685dd665cd695b16e59d665d5725a9755ad735c96a5e56c5d1725d1715e1665ad675c1735b9765c5795a5715dd765a9695b5785c1795b5685b1775d1675ad735a5675b96a5d5695b96b5c5665a9665c1735c5705d56f 0x18260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260982609826098260981601926459063d8e6358c60d8260580649916418f6398d6318c6358e63d90645926018160983639816098d60d90601836058c6498e60d8f631826359163d906458c6358e605916498c609806358e6059163d80645926058f631906358e63d806458f63192641826018e6059163d8260d816318d6018e60d836058f631906418d639836058c63d9260982635806398f6498d6018163d8c6499064180639916318c64982635806398363981605916498c609906358d60d9164582641836458f63192631906358060d836458f6499064180639816459163d92609826358063991609926418d6059060d9163d8c631826398360d8163d82641906018e605826358f6498c6358063d8c649806398363981645926318d601836058264990601836498f649916018e60591609926359060d8e63d8d60d816099060182) (by decide +kernel) (by decide +kernel) _ graph_31
  decide +kernel

def wires111 : List Sig := [(0x15de6b26c2abd69eb1de8e353aa88671dcdf82f23177076fb6fd948a77e3a63e98b93a32d5b6aaaef5a89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x181001c200205400b754083411380038809600ea8030056a00f500087a03843c18a822222a0290a80a4aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xe6db3bf69ed2f27ab5a65f1ce7ebd768fa8cd35cccbcb5a4528fa7bdc56c8d336636ce5e6db3fcb59f9cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x5221403002304080826c902040c440608080446c20010050850a00404408302410c848094200250904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xb2a3cd9dd54d06acf31708f7569d6ae3123bbef434cfcb69bb36b268f9fd165479e972978e3ccf39ede7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x1d028548404240a2932010144420d3b81102a3a80108a806ca902602a9089044059a92290c20c230830b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0x20b76ec9ff1e9484de1dc0ebf316eca6b853acf5a15b5a8ac3eb1ed173f753673c4895e7f03f0fc1f0777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x2bc52a0b7a8aa496cc0ec4ab9100c422c8158452e251511246e81e8463365327244095630c704c31c14e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0x15d2ef7b1ae67c9410afbb200287b4235657d965377ddd05ffdfedc821ec3e888e1e1f5efffc00ffe00ceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x6452029ef0008f400a326828203fc035609fc0136cdc005fd02aea001c43a8086161d5cc0f80703e0100082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x31b8afdbb3a2d4d8db10950dcd6eb6f62954dd2adabf1ccd5b3065368790b9c257c40ff7fffff00000b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0x1a4adcc2ac0a8459455501148cd0f3aad0075552a121d18af8350643ea790b1c253c407b7f0007fc00053565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_111 : ¬ possible wires111.toFinset 6 := by
  apply excludeGraph
  all_goals decide +kernel

def wires119 : List Sig := [(0xfef3bf95caaf672bd9ff5cbe36ccdae6e97ee97518aef2f9f7dfc6a26ee553ab376d4e6db6db57bdece4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x8804000124001b2800ac00c00062004a006480060031401d020070044282150844440090140090047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0x143cd5aff77f49fd4f732b37bddf735fb3ea136bae7d95d6749a27d5fb95eac74ccdbb59edb6dfad6bb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x4910500c00828084103542042030900c2404082218400401221428080a08304841a108922000922049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0x1c9a164e3d55329595764a116e9c599595292adee61e9ad96d2f9b94a9f9e25d1d386ccb71c719ce736adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0xe8348ca941c9097c5b44401cc885cd61521329e141e3298ad8dca8c2d70425c193864cb124c55924c526711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0x170bbd7399ec7d1cd0585d895bc8afb89a61dcd4f6cc6ba9b158ece392b3b61e578231be7e07e1f07c483b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x1e5c25689afa29b4d24c5f051b008f3893815dc0b57c0b28e2582e0380d33216568231ba1c70661c700d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0xae273ae71b59bd6288df26308637914dcd5bbcab1a2d9d08bf7b79b046e9bb4bc385d30fff801ff802f56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x1924906abfc00197280c63511041f310ccc31f6035a19bc0abf20e9e806c9b949c2859309f80781f802480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0x158acb67abda8d58db5a042c9db3eaddc945996d5d6b37e219b3920d75570bb84af123f57ffffe0000597acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x192a6610db1aa4547212c420d9b0f8e4ad00b9295d0e23c815e0922d3d470b384a7121e560007fe000292a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_119 : ¬ possible wires119.toFinset 5 := by
  apply transferLower (dst := wires55) (rowsProjection 0x1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745d1745f17b5e9795e1775d9755d1735c9715c16f5b96d5b16b5f17b5e9795dd755d1725c16f5b56b5bd7c5ad7c5dd7a5f1795e5775dd725b5755ed745ad7a5c96d5d9785d56d5e5785c5735f1725e9715c1705e5745bd735b16e5b56f5ad7c5dd7b5b9765c9755c1745e1715b96e5c9775e9755b5705ed705ed765bd6b5cd6e5e9755d17a5d9765bd735e1715f16c5b9725b5785c56c5d5795c1795ad785c5795f1735f16c5c96d5e9725d1795d16b5cd775b1765bd6d5c97b5e1715bd775f1775e9725c1755f1775d1785cd6c5ad6e5f1745dd6d5e57b5d96f5e9755d96b5cd6c5b5735b1755d1745e1715d96f5b9735b1745f16d5c1795c96d5b97c5ad7b5bd745c5735b16b5b96e5dd7a5c1775ed7b5c5785b1775e17a5d96b5c1785b1715cd725d56e5e5705e5765ed6f5d9785c56f5c97a5d57b5b5715e16e5b17b5bd6c5cd735e97b5c1765ad6e5ad755e5765d5715c174 0x18c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c61985611836418f6398d6318b6298962187619856118360d8461586621896298b6318d63990641856398b6298c6118d61d896398d62d8f60d906358363190621866218f60d8562d8a62183625846158b62988619896398d6218b6298660d87631846398563d866258e6158b6218f61983631896158e62d8a629886199062d8a60d846258e639856358d6298b63d8660d8761d84639856358b6198c6318462590639906158a63d84625906398b63d8663d8761d896418860d83631856358b6218f60d8c61d846358a6218863d86631876418d6218660d8361d84641896358d6198761d906158b6218863d8f60d8c63184641856218c61d846298f61d8a6218f6198360d8c6258e6358a619876258e6158b6298c6118e6198361190625906398a6198762590639856358562d8f63d846258d62d8c61d8963984619906258562d846418f61d8d615886118d63d8c61d8a6298c) (by decide +kernel) (by decide +kernel) _ graph_55
  decide +kernel

def wires189 : List Sig := [(0x1edd55e71d6c6aa2f6a729bb8e5a736c2559b2fcb910aad86f67b3909ae8558745559932d55555aaef5ccf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x1a6e804431260012802b2a005a380d200c80d035400e306a0721801c20458604550132054a0152805422244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0xf37cb0caa6afe7349d3a73369b86ddeac9abd055aec61715a489eceee0564b192332a75e66666fcb59793499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x4408080884246c4084a04122aa478422e1298210226607010488a94022124a182210a64d18094602518854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x15f9e2ce4b939b5d321537647086ee9c452ec517f7a2a597b62e6c65a6d7e8d2a2c65799787878cf39e71a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x111074364b0881090316b40100b048801ac0416f400870506270400b492481200c65519060c21830860080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0x1d9c28179edcc7f87d4c15c0dc4683c87d74ec6ba7ba1a8ea8c3d7bd4aaf3b4b33e0c8a67f807f0fc1f85676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x1c00902c124801e2290c9480e82483001c507029028e008a1150d03c030c3249332088841810c604318005910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0x197055f279fbb3b59baa48dfb3111063f6091ad55297bd9305fefc7811db9e2c4e0e1f8cffff800ffe0069e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x4401100880898c4013a00c52a818040ce01180f0096618005c8545401c11828420a1a8ce000f8003e00809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0xb2e9856e55bd5ce8dcee5e6016925b39b9f48c1694dd76eccde608ad51e826e19bd245f7ffffff00001f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x9250e0633952002a484d128010a01b101ec0050494096028a122108f40e824619942413001f0007c000582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_189 : ¬ possible wires189.toFinset 7 := by
  apply excludeGraph
  all_goals decide +kernel

def wires250 : List Sig := [(0x194d59b24b27e77d9ded6da8698cd9ddf5b4cc646859eff95b95717a63718d7245f671ed55eaabde8aef57f55af8d7fd4df7c329ab364964fcefb3bdadb50d319b3bbeb6998c8d0b3dff2b72ae2f4c6e31ae48bece3d,0x88c05c825038ac59198f618820d84191e1b4806022c140db531061b403308d22059631e5542a02aa82064d4c10c0b886889811180b904a07158b2331ec31041b08323c36900c0458281b6a620c36806611a440b2c63c),(0x1ffd7ce49e653dc6d62ebdbebc3bb4faa335bb48af317435629fafae6a7a4e38c933b775e66b33d6be153e2feadadad40d3357ffaf9c93cca7b8dac5d7b7d787769f5466b76915e62e86ac53f5f5cd4f49c7192676eeb,0x1b2ce145822f25029262f0848c53a4c0a63098582621402942951c07704a4a184912b554e188c48c30641224c0a0602c20324b659c28b045e4a0524c5e10918a749814c6130b04c428052852a380ee094943092256aa9),(0x16776ae8e87599dc26a6bf3b14aeb72ae97ff9c0fb566cd67366ad2eccf86c69f5e5c3a77873c3e73efd337fcffcd8988954e6ceed5d1d0eb33b84d4d7e76295d6e55d2fff381f6acd9ace6cd5a5d99f0d8d3ebcb874e,0x410089848d09ad800850d1312ac112849cf01829850ac96b902617888902461b4e542a306130930c3808cc91a4991d2c849a4820113091a135b0010a1a2625582250939e030530a1592d7204c2f1112048c369ca8546),(0xd2fbe0e531885683d151795eff5be7054eaf63f5ceeb1bcabdb1ac7d9eda3717a9b39ea7f83fcf831d3dbc865cf32336a7ab1a5f7c1ca6310ad07a2a2f2bdfeb7ce0a9d5ec7eb9dd637957b6358fb3db46e2f53673d4,0x802b484581881300f8406004e31929846e8ab11508ce234a4d81a47482d2131688b296278000e3f02502900058154125982350056908b03102601f080c009c6325308dd15622a119c46949b0348e905a4262d11652c4),(0x1ce79dbd3c8a663bfbcd44c6f468d9c5fb7da4e4fb158be3d7fed251a6c713a7e7e6e4d0fffc00ffc0fe5f7edd790d4ed6d79f9cf3b7a7914cc77f79a898de8d1b38bf6fb49c9f62b17c7affda4a34d8e274fcfcdc9a1,0x651a001d8c86438626500833c6049c0e1202449c901abe0424af84087441325c7a684c0801c0fc001cc1b0b32a1344104307cca34003b190c870c4ca010678c09381c2404893920357c08495f0810e88264b8f4d0981),(0x1d6ba617d73bad6cb1119b676bff6a51d4be42bbbdea19ec5b7161da3b80f3d09fd81edf7fffff000364dd8569577631eaeef3ad74c2fae775ad9622336ced7fed4a3a97c85777bd433d8b6e2c3b47701e7a13fb03dbe,0x2a14153852744453001116730cc2900b81440aa2d2314c90b2065b83380d2c09750169d001ff00001a896d17252a3a52444c854282a70a4e888a600222ce61985201702881545a4629921640cb706701a5812ea02d3a)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_250 : ¬ possible wires250.toFinset 4 := by
  apply excludeGraph
  all_goals decide +kernel

def wires127 : List Sig := [(0x11d4267cfad57e624c07aa3e696955d659a8ac98396f68651b43b610b58bb50aac1e9834d55b56daab6aaaabd77aabd6c8864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x11b006000810702200040a1a8840158850888810a12200000b422010a40b0408a814083000a8002900a8002900a8002900820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xb577d82154824d5f2793e6dc40a8c251fd15aef6f24aab86f94186d1e1c623678a13689e66d9b6ccdb3fccd65accd67b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x40229900440044540600025440080240d0100440c84002060841809121420321021160880014942000149420001494220101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x11ae58c9aa4a33b393d4e351efb59a22865397938b3b5c1b3ab16ad4c2a14d554d326b137871e38f0e3ccf0e79cf0e7b1ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0x1124504b2a1212908b102242ab91120202349283011a4c1312316244c0814d454d1221114a32120c4a32120c4a32120c1cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x1c3b86ad0caafd0ee58cc59057d46b2ce3864d5aedda15caadaaf1ba707c1ce183454b4a7f81fc0ff03f0ff07e0ff07c2772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x8128a040488a506248c91894440499c88824c78c8c001488d8a90b2302c102080454a4a10c0607010c0607010c06070022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0xd12c22a93e3d6ad98de00c6333df3ef366fca40108db9f2f07e070f01d341d407f591ccfffe000fffc00fff800fff80695cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x400402af14102889a620044333c8062227502000009fcb07034070d01d041d407a09184e303838063038380630383804d5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x1ac5e85576bf0fc9d5c0da007b669131483472de16d4edef141ddf88a804f9d8d0cbd3317ffffff000000ffffff0000010251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x845f95573ab8f0dd0c2d10445360031083462cb56d46cfad41ddf880804f9d050cbd3017c03fc007c03fc007c03fc0010251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xa1d750fbd8eba282a6ab76a82ce4f1b7005b47ed7209fb14554e3256cc5826859c6ecd67ffffffffffff00000000000427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0xa1d964ab18fb9320a0ab78a8a0c4b59d08c163ad3729d911550e3246cc1824849c6e8d67ffc00007ffc00007ffc000010cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_127 : ¬ possible wires127.toFinset 8 := by
  apply transferLower (dst := wires63) (rowsProjection 0x15f5795d5715b56959561575595555153549515414f5394d5314b52949521475194551143509415013f4f93d4f13b4e9394e1374d9354d1334f15a5715753d435695757d4f4f9574cd464d94f5413e5753f5614a509575114f4f15e5413e555364dd35545405653a551455193d5215355d4b50539535594d55f4d940511464fd474dd334fd375313b559454d15d56d495794a511424e13d559475414e4d54b4fd37565485013c5214d4f14d5553b4f1584d1535495d50547535395554456d3c5313b5595e4d14e54156579374d55c5793550d4656d4f529494f953509364e1455694d54d4b4f53353d364ed34531345093b541544d54c4dd3356d3b54534501425713c4f15c5053951159521404ed345353c4dd355614b4e1505395150d3754d4b4e9494d54d5694455d4f5615a4f933529485415852937539335794b54d405455953d3d50136569395393b4d14854d574cd3e5093f4dd424e156541404fd4a525375194b4e541521485553f561485055b55949509565794e5594d53d5c4f9454cd4f525384f1345495556139575555113d559405553b579435253e519364f95352d44569434dd4c4d1364e958515544f54a5515954548571405193a4d539511585054a5394b54d4f4d13856940529364d13b4dd424d93b559495354f4e155561564f9334dd4d4cd3d5013e4f548569545455c5214252d3c 0x1795e1775d9755d1736158460d82605805fd7e5f57c5ed7a5e5785dd765d5745cd8561183609816017f5f97d5f17b5e9795e1775d9755d1735e9756097d5f5825ed7f6157f5fd835ed855fd835d983605765f1735cd77605775e57a5f977611775f97a5d5755ed82615855e1835d9815f1815cd73601745e5845f1745e9845d57d5d5825ed7b615855d9786157960573601815e5815cd7c5f9775d17e6017a5d174609756097d5ed7f5fd835d97860d735e179605806057c5dd815f9805e977611845d57d611756097b5fd825f57860d7f5e1765e5735e5815cd805e573605775e97e611845d17a609825f57d5fd7f5e1836057c5d97760579611775e9775e9845f5755ed835e1785d979605795f17c5d1745e975615765e179605805f1795f97e5dd845d1825fd7b615855e1836157f5d979601845f9805e977609755ed7d5fd835e18560d785f1765e5735cd805d1845f1845d57d5f57b5d9805dd7c5dd745f9775e9825d57b5fd836017c5f9775d1825f5756097f6157f60d785d9815d9795cd7e5d1746117a6097d5ed8261583615765f1735dd796117a609755f5755ed8561578605795cd80601745e9825f57f5ed8560d8160573601815f1795dd7a5f5815e5806097f60d815d979611785dd7a5d57b5e17c5e5746157f605805dd8560d845f5755d9795d17d5ed7c5dd7e60984609855d17a6017c) (by decide +kernel) (by decide +kernel) _ graph_63
  decide +kernel

def wires191 : List Sig := [(0x14d84294b4571cd76acc628169e63364af1c8c2ac5d4b1b668aa364ada291589720e3128d555555555575ad55ebbd55eb5a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x4000214ac4500124a24200108c002002e2088084484610000aa2208c8290108500a110000029090005212000a424001488a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x1379fe29953e800913995f0e6b7c506b18911eed8a9bb96a31bc4d161c1e70173c2168b1e666666666659ce66b2d666b3c36d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x1368d822419aa80911895a08213d504300953760880a9c6021144d06141650152c2168b0949425229284a45250948a4a1010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x31694ccabeac1b71254ad3d929e6d9730cb0385bc75519515a51338a4e223b286689c53787878787879ef7873ce7873db8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x14008c88204114405084640202248420080083241100840421101080a023a2820884412120c0042418008483001090618c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x8677ac64f0795189b8336b31495e6c0d4b2c1e812ecfe81d7ddac2d515c0f44c5831ea27f807f807f81f07f83f07f83e276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x4423240454b040803816093845d42409632150812cc5600d28cac29504c0c0444831aa2060701c0c0e038181c07030382228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xdf98d5a85a110859dd78d1f2623b9a6e7fc4ac67e8884fbe713e0c50313a0d6236be6c8ffff80007ffe007ffc007ffc01511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x119d0c2200a012c1145285082222a9a2018d40d70800809f211140c40312a0d22360e448b83806070700c0e0e0181c1c01501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x212d70386f6ce5fa1ff83816ab0a2480b413231e0e6efc40dde4c084fed84895ed057fffffff8000007fffff800002923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x100212850380d6480c38f58102461880080241323190c267600d5640084b6d00885ac053fc00007f80000ff00001fe00140242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0xec2ef7146f667ba3766d04aa3511e389c6df910ad4ecb49a05a4a8269a6c82c2cd2d27e7fffffffffffff8000000000008891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0xc48d44106c7228033247002a451186195679948c044c149805a0a826902480c2452523a400007f80000ff00001fe000000011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_191 : ¬ possible wires191.toFinset 10 := by
  apply transferLower (dst := (thetaInputs 0)) (wideProjection 0x1395753360d314b9735cd734f54e4c97556d73571434e5604d93b4c94959d6b4e52f529654b95054d655f1305d5604cd854f1386155c5ad5b5cd4653d2f5755c4c1435152e5cd4e529464cd5d54d5b4b93b4ed3b5d54e5713d4c53b4c9365196050d73571665297b5192f59d484b95060d485b1304f560575555d145555325ed314ed3953d2f4cd324c1324cd2f4ed6152131515385ed394bd735cd734f5614d9755197350d5c4c5514c93b4d969521534c52e5954a4bd625ad4a61d305d5514e17d4fd335f54354d465cd5b58d2e515434c15c5752f5cd615955b4e1455ad464bd3b4ed3b5d56150d3d4e53b4d93256d515717350d4c5958356d2e521674bd625ed6755d304f5515156d5dd5d5b53660d394ed3158d2e4e1364c1364e12e4ed4e59d395753360d314b9735cd734f54e4c97556d73571434e5604d93b4c94959d6b4e52f529654b95054d655f1305d5604cd854f1386155c5ad5b5cd4653d2f5755c4c1435152e5cd4e529464cd5d54d5b4b93b4ed3b5d54e5713d4c53b4c9365196050d73571665297b5192f59d484b95060d485b1304f560575555d145555325ed314ed3953d2f4cd324c1324cd2f4ed6152131515385ed394bd735cd734f5614d9755197350d5c4c5514c93b4d969521534c52e5954a4bd625ad4a61d305d5514e17d4fd335f54354d465cd5b58d2e515434c15c5752f5cd615955b4e1455ad464bd3b4ed3b5d56150d3d4e53b4d93256d515717350d4c5958356d2e521674bd625ed6755d304f5515156d5dd5d5b53660d394ed3158d2e4e1364c1364e12e4ed4e59d395753360d314b9735cd734f54e4c97556d73571434e5604d93b4c94959d6b4e52f529654b95054d655f1305d5604cd854f1386155c5ad5b5cd4653d2f5755c4c1435152e5cd4e529464cd5d54d5b4b93b4ed3b5d54e5713d4c53b4c9365196050d73571665297b5192f59d484b95060d485b1304f560575555d145555325ed314ed3953d2f4cd324c1324cd2f4ed6152131515385ed394bd735cd734f5614d9755197350d5c4c5514c93b4d969521534c52e5954a4bd625ad4a61d305d5514e17d4fd335f54354d465cd5b58d2e515434c15c5752f5cd615955b4e1455ad464bd3b4ed3b5d56150d3d4e53b4d93256d515717350d4c5958356d2e521674bd625ed6755d304f5515156d5dd5d5b53660d394ed3158d2e4e136 0x1825e5895e1836158d62d8e5f1836158e5ed7b6258d5f97c61d876258e6457c641816357e6019163d785ed835e57b61590615915f9825f5795e18c6418360d836057f6017f5fd80609826198c615835e17d6217e5f1835e17e5ed7b6317d6397c6298a6317e6457c641815f58e6019163d855ed836197b5e1905e1916398263586615896418360d836057f6097f5fd826018062d85631836257d5e57e641836257e645916157d63990611846157e5ed905f1815f58e6097b5e98c6458362d916257c6257b639806358b631785f18360d836057f6097f5fd826018062178625836318d6198e641836318e645915e18d5f990649925e18e5ed905f1816357e6097b5e98964583621916317c6317b5f9805f588625855f18360d836057f6017f5fd80609825e5895e1836158d62d8e5f1836158e5ed7b6258d5f97c61d876258e6457c641816357e6019163d785ed835e57b61590615915f9825f5795e18c6418360d836057f6017f5fd80609826198c615835e17d6217e5f1835e17e5ed7b6317d6397c6298a6317e6457c641815f58e6019163d855ed836197b5e1905e1916398263586615896418360d836057f6097f5fd826018062d85631836257d5e57e641836257e645916157d63990611846157e5ed905f1815f58e6097b5e98c6458362d916257c6257b639806358b631785f18360d836057f6097f5fd826018062178625836318d6198e641836318e645915e18d5f990649925e18e5ed905f1816357e6097b5e98964583621916317c6317b5f9805f588625855f18360d836057f6017f5fd80609825e5895e1836158d62d8e5f1836158e5ed7b6258d5f97c61d876258e6457c641816357e6019163d785ed835e57b61590615915f9825f5795e18c6418360d836057f6017f5fd80609826198c615835e17d6217e5f1835e17e5ed7b6317d6397c6298a6317e6457c641815f58e6019163d855ed836197b5e1905e1916398263586615896418360d836057f6097f5fd826018062d85631836257d5e57e641836257e645916157d63990611846157e5ed905f1815f58e6097b5e98c6458362d916257c6257b639806358b631785f18360d836057f6097f5fd826018062178625836318d6198e641836318e645915e18d5f990649925e18e5ed905f1816357e6097b5e98964583621916317c6317b5f9805f588625855f18360d83) (by decide +kernel) (by decide +kernel) _ theta_base
  decide +kernel

def wires251 : List Sig := [(0x1a9a15348d9d7052d5277bdd98b67c30e7e6182a0eb536624c958d4ccb0ae4746c88e0f0d55555aaaaaafab6d5aafebc1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x1c0210048c0420120123590500126030628208000d24504244150c088302c4206088a0a0028012509050024a120a00480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xf658c5c42297f81e72cd9281f4e088bed5c66caf5e4ab5bd10b23879871d159f6168c5de66666fcccccbcdb66fcab2fc179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x361ac5042091d00a00484085e44080a155473008080a911100a23850851115816140c5c802aa40520055480a400aa938400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0x721771a58f5868e3c7ab983e6ddc558199dcb7921e7141f524c46292d367c9abae5916b787878cf0f0f2f1c78cf33cb1d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x144157024ca1860aa4a938a36695640829b9294c29233116424c06290d267c1aaac49169130c3861c261870c384c30e0159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0xb3e7c2b8f524a4d1852d4d33e29796d9fd0973374b318ad9af6407d301f01a6172b56be7f807f0ff00fcfe07f0fc3f398c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x2aca8a9025051451250865018280b4390409623109008a898a2405430190184152346162430c08604861810c090c303084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0x10f0a7b3fab6e7b7a0c926bcf4f1cf9cc873fd051a09c7a52f20be904fb03f880fe27f04ffff800ffff00fff800ffc02af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0xb0a45020b2c780804822b0f444070488787301100107110b20a09048b032880e625504b83f00000707e00000e0fc02c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x148dcb6e77eb6ede1be0f1a1955043b3202924cafb52cafea1ebec0a14edf4a18157f4a17ffffff000000ffffff0000261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x1488412f15c2e2961ad059b5a100429122a9040a7b5a426ea1e1cc0a14ace4a18143f0a13fc000f807f8001f00ff0000614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1e685aaf3b87bd2336fd954e412b96a671d54867b26ce182a4e717f285c04b38b14d2b3e7ffffffffffff00000000000aa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0x1e4302ab1b45381116b1950d0a2990e371860066227ef8c0a4c7176285404930b10d2a3a400000fff800001fff000001086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_251 : ¬ possible wires251.toFinset 7 := by
  apply transferLower (dst := wires111) (rowsProjection 0x15f5755e571585595756d595695554d5451d45519445054050d424fd3e549505454f52d4a5394c535495213d4ed3c4e9374e5384d93856d4f511405255d571465315f4dd4b5753a56d395154455d3755551571505355456d425293b55d394dd535554f5793d54d515394d5493a4f94e4e94350148565514e15e5613d4fd5d53d3c5355954956519414f9395094e4e9544d94052138525455694852538551474d95e50153529524ed5a53d5852545571585655d50549565464e53e5715d4e9575154b541585113f531544dd3c545565355655536501485113852146555394f9434e936521455113851d574dd5c50d49521495714a4ed4c53d574dd4854d384f9494fd3a4f13a4e5405093c519415154b4e9545093d5013954d5353d5b5115653140549464f93a5055b4d9445095d5513655d4453537525564ed41521385513655d4d5794e54d3a53d5d4f93c565465794e4fd3a541465413e4ed545294054d4f5693e53954529595453f5615d565445714c54536561444fd3c4e141569395215e54d4a5694f5614d5655a521475794b5295c5694b531504dd4c5514253d4a5593b4f94b4e943501384fd544dd424f53c5454d555575155c5413d519394ed4a53d5352954511534e13c50554519374e1484e9404dd48565505113c5013f5695a5714c4d93a4f9365354b5314d53d3e5594355d5c5595750949 0x18f61d8662588615846358c6398b629806057f60d825f57e5f1906458f61d8662588615846358c6398b629806057f60d825f57e5f18d60d8660d886058061d8460d8960d8763184615805f58562985645916357f63d8662d865f17c5f98162d806258063187631895f5856397d6298a6299163d916097f645816198d5f1886057c62d8460d875f9845f9886017e5f98c61d8562589639906097f63d7f605866358862d886198b619846218060d876258c5f58e5f58562990639905fd8f6418d6357f609815f1865f1885f18660d805f98c615805f58e6418e63d8662d82619836198160d8061d836258c61d8e6157d6158a63d7f5fd8d609816358b6118b6017e625806258c5f5906097f605866218b605846118361d7e5f58a629916458f6458d63588621886018960d895f5906298563d7f6457f6358b609815f17c5f98b615896418e6418e6418d63d826218361d836118360185631855f5906297f6358d6218b62d875f98e6317d6419163d82619826057c61d845f97e6018563989631916459063d916358262d83605876258061d8c6158c5f58e5f58a645915fd8d6198d5f1815f1886118861d895f989601876398a63d866198862d8161d836018c6398f6058f6198b6098161d85625805f58a5fd866057e6458d6218360185645896418e5f5826117e6398d62d836317d6418964191635876218b) (by decide +kernel) (by decide +kernel) _ graph_111
  decide +kernel

def wires255 : List Sig := [(0x155b56daab6aaaabd77aabd6b138662c64835c38420b9a70aee44c01acc5582e12305358d55555555555aaaaaaaaaaaaaaeb5aab6adb556d55557aef557ad6270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x4a120150005250900a800292120000864821408420a0a10aa44440184854824101043500150005250900a8002928480540014942402a000a4a120150005242400010c90428108414142154888803090a9048202086a0),(0x66d9b6ccdb3fccd65accd67bb4ba0c978680b01b1d0de81c18380d86e0fc140e16e3091e66666666666cf3cccccccccccb39ccdb36d99b67f99acb599acf76974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x80a40002928405200014942080820c218480b0021909481408100d82a028040c12e108080029284052000149420290000a4a10148000525080a400029284101041843090160043212902810201b054050081825c2101),(0x1871e38f0e3ccf0e79cf0e7b55269e68d925355b404c25a6094c6d0a5319327210d28523787878787878f3cf0f0f0f0f0f3def0e3c71e1c799e1cf39e1cf6aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x10000946424180004a32120c15021e2041253059004c0120090c2d024109323200408501146424180004a32120c00025190906000128c84830000946424182a043c40824a60b20098024012185a048212646400810a02),(0x1f81fc0ff03f0ff07e0ff07c44f5895d3192fc06e926a28dc22cd3e089b0c685c09788c67f807f807f80fc0ff00ff00ff03e0ff03f81fe07e1fe0fc1fe0f889eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0xc382180c0e061c10c0607000b5810d3092cc02c922a284c220d0e088904085c09708c22180c0e061c10c0607030e086030381870430181c0c382180c0e0016b021a61259805924545098441a1c11120810b812e1184),(0x1ffe000fffc00fff800fff8050da2df08dbe00343df1107b2b110b3e40609ff48620ac8cffff80007fff000ffff0000fffc00fffc001fff801fff001fff00a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x10c0c607070086063038380544a24f0892c003434d1106b01110b1e406097500620a40cc6070700860630383804303181c1c021818c0e0e010c0c6070700a89449e11258006869a220d60222163c80c12ea00c414819),(0x1ffffff000000ffffff000001cd8da270279e9f6268a400055b93b8f808a018bcfa3c7417fffffff8000000ffffffff000000ffffffe000001fffffe0000039b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xf807f8000007c03fc001c5a99a3003969f62480400045a83b8e000a018a8ba384017807f8000007c03fc000003e01fe000001f00ff000000f807f80038b533460072d3ec490080008b50771c0014031517470802),(0x1ffffffffffff000000000005fcf0281a6a8765c9c576b384c529153942b03972adc690a7ffffffffffffff00000000000000ffffffffffffe00000000000bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0x1f00fff80000f807ffc000055e61221a6a0745c9c476b380c529103942903972ad0690a7ff80000f807ffc00007c03ffe00003e01fff00001f00fff80000abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x292114168ac486c81f8133921251f4b69e70e8117d0554747ffffffffffffffffffffffffffff0000000000000000000000005242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x1fff00000000fff80000000002520048ac086001b0132921251c0309e70c8017404507400000000fff800000007ffc00000003ffe00000001fff00000000004a400915810c003602652424a380613ce19002e808a0e8)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem graph_255 : ¬ possible wires255.toFinset 11 := by
  apply transferLower (dst := wires191) (rowsProjection 0x1575595555153549515414f5394d5314b52949521475194551143509415013f4f93d4f13b4e9394e1374d9354d1334c9314c12f4b92d4b12b4a9294a127499254912348921480ec3acea3a4e839ce6394e438ce2384e037cde374dc36cda364d835cd6354d434cd2344d033cce334cc32cca324c831cc6314c430cc2304c0370ca4f4cd30ce7484c636cc8494c13554e380e4301304a92332d2a4cccf330c93112633d2e49542319324b925520c54d13a4a8e3374cd4e8cc500d7358c44cd2634d2c4894e4ecd849529338c64f138338d5505385112d3553c49d4238922330e5355394d8ce52129548e85353838cd64b55033d2c480c5508e33acdb38cda4e0dc3a54e32d32349213014b370d63352e480c5480c9518c137ce24c0e5318ea4ad4c49941388d130d2b4853a328e330531334e24a120544c8320eb4b1303412d4a8c448d414c1384e92b358cb498d333cc34e0c332ce0361243214c3452e4b4e74e4d049cc4365525153a30533498c331d4239540490d2528e13294a35ce14d1503994b378d53a4cd34cc7500c24c9253192a344e5528ce35d4236d2236148380dc304c539d20334d75052130d20304c84c13c3112233cc35092e321484e8e335940368dc314e23952138d394c8cb300c43692b3013a4a0ca335404b0cb4e0ca3553139d4c528e149cde3a530354cf4b12548d2a4e126360c9 0x1676198561183609816017f5f97d5f17b5e9795e1775d9755d16e5b56c5ad6a5a56859d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745b96d5b16b5a9695a1676198561183609816017f5f97d5f17b5e9795e1775d9755d16e5b56c5ad6a5a56859d866158460d82605805fd7e5f57c5ed7a5e5785dd765d5745e5865e1845e57d5e1775e9745ed746056e5d5855f5675ad766157c5b1765f96e5f9795f1695a5825b17d5b57a5fd775a9855d5815e17d59d7860d755fd785ad675ed6e5ad86601835a16c5ad765dd695f1806096d6056d6117f5e17b605755f57f5e1675b9755f16b5b183619685f9765a18460d865b16b5a580619806117960577609855dd6a5e96a5d16e5fd755a97e5d9755ad855b17b60d7e5b17c60d865a56d5dd7a611865b16d5d17f5dd7d5a56a5d1785a9755ad7a5b58559d6b5ed7e5b96a5b9685f1805b16860d765b17e5b9766116b5f186619695a1815e57d5e1825fd7a5a974605835ad766056e5ad755ed8060d795a17e5a5805f16d619845b56a6098560974605825f57a59d785b96b5ed685f9826157a6056c60d686016d611825dd7a615695e5785ad675ed685d97c5b5815e5785f57a60d6e5d5845a5866016a609815e18661177615685b17e5d9775e96e5d5805b17e5f1825b57d59d785fd6b60d865b9855ad836196a5d57b5f96c5a56d5fd6a6057d) (by decide +kernel) (by decide +kernel) _ graph_191
  decide +kernel

structure MaskedFace (budget : Nat) where
  proj : Projection
  mask : Sig
  reflects : ∀ a b : Sig, bin false mask a = bin false mask b → proj.project a = proj.project b
  lower : ¬ possible (raw.toFinset.image proj.project) budget

def maskEq (m a b : Sig) : Bool :=
  ((a.1 ^^^ b.1) &&& m.1) == 0 && ((a.2 ^^^ b.2) &&& m.2) == 0

lemma maskEq_sound {m a b : Sig} (h : maskEq m a b = true) :
    bin false m a = bin false m b := by
  have ha := Bool.and_eq_true_iff.mp h
  have bits {u v w : B} (eq : ((u ^^^ v) &&& w) == 0) : w &&& u = w &&& v := by
    have hh := beq_iff_eq.mp eq
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have p := congrArg (fun x : B => x.getLsbD j) hh
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_zero] at p ⊢
    cases hw : w.getLsbD j <;> cases hu : u.getLsbD j <;> cases hv : v.getLsbD j <;>
      simp_all
  exact Prod.ext (bits ha.1) (bits ha.2)

def maskConstant (m w : Sig) := maskEq m w zero || maskEq m w one

def maskCost (m : Sig) (v : List Sig) := (v.filter (maskConstant m)).length

lemma maskConstant_sound {limit a} (f : MaskedFace limit) (h : maskConstant f.mask a = true) :
    f.proj.project a = zero ∨ f.proj.project a = one := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl ((f.reflects _ _ (maskEq_sound h)).trans (map_zero _))
  · exact Or.inr ((f.reflects _ _ (maskEq_sound h)).trans (map_one _))

def packBits (x : Fin 9 → Bool) : BitVec 9 :=
  (BitVec.ofBoolListLE (List.ofFn x)).cast List.length_ofFn

lemma packBits_get (x : Fin 9 → Bool) (j : Fin 9) :
    (packBits x).getLsbD j.val = x j := by
  rw [packBits,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  have h : j.val < (List.ofFn x).length := by simpa using j.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
  exact List.getElem_ofFn h

def grantIndex (s : Bool) (r : BitVec 9) : Fin 689 :=
  Fin.ofNat 689 (((if s then 0xac2afabaadab2abaaaa9aa2a7a9aa5a92a3a8aa1a829fa7a9da729ba6a99a6297a5a95a5293a4a91a428fa3a8da328ba2a89a2287a1a85a1191a0d8ca0a81a027f9fa7d52d469f27b9ea799e1876097c9de769d6749ce729c6709be6e9b66c9ad909a98b9a66899e669966498e629866097e5e975866057b9725b96a599618f95d8a9598e9558963400620009525394a51941855fd7a93d845f97960c000000093a4d9324b92a499224791a459111690e42905119023f8fa3d8f23b8e90c8e6388dd068da358d1018ce328c6308be2e8b62c8ae2a8a5778a17289d6d89a258922388a213d0ef8821f5a1628795e565548761c86e1a8661885e168561484d76849718456c8420f83a0d830cc82cc682a0959d618215d5615381e06815758117080d6b809745cc005b8005a80080600595607fd5c559525915f0000056800000007f9fd7f1fb7e9f97e1f77d9f57d1157cdf27c5507c1ef7b9ed7b1eb529457a9e97a10579de65013b795e478de2785e05254f77dde7754e7714d5300076dda5214351d4200000765d84f93a4f5390000075dd6755d474dd2745d073dce734da7313772d33729c9721c77192d4a123715c470cc07091f47118705c06fdbe6f53649d326f1356ed314d0004c0006e92b499214a800000006e51e4691747400000006e1b76d9146d5b46cd0f6c913448006c50e434006c1af6b9096b50841c006b103408006acff3f8006a9a96a0fb69da63c8f7694fa3e400690f63d40068da23c4ed3c0ec00000398e200000378dc00000685a067cd9678d3674ce670d835c00344003340066cc8668c331c0030800664be2f4002e0002d40066197658b3654af28cac650b22c4002b4002ac0064ca72889e298000000026496000006480000000 else 0x1910018c000000000000000000000000000000001876097c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000178001720016d00000000000000000000000005a5630015e5655400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015100000000000000052d460000000000000005053c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001380013300000000000012f4a5240000000000001204711800000000000000000000000000011600000001110000000000000000010c000000010600000001010000000000000000000000000000fd00000000f80000000000000003d0ef000003ace500000384dd0000000000000000000000000000db000d6000d00000000000002b0000c600000000c1000bc000b70000000000000000000000000000b4000b0000ac0000000000000aa294a000000274980009524992) >>> (10*r.toNat)) &&& 1023)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem grantIndex_ok : ∀ (r : Fin 512) (s : Bool), edgeF (fun j => r.val.testBit j.val) = s →
    ∀ j : Fin 9, bit s (grantIndex s (BitVec.ofNat 9 r.val)) (raw.getD j.val zero) = r.val.testBit j.val := by
  decide +kernel

def chartIndex (a : Fin 9 → Sig) (s : Bool) (i : Fin 689) :=
  grantIndex s (packBits (fun j => bit s i (a j)))

def chartProj (a : Fin 9 → Sig) : Projection where
  project := fun w => (reindex (chartIndex a true) w.1, reindex (chartIndex a false) w.2)
  project_neg := by intro w; simp [neg,reindex_not]
  project_bin := by intro d u v; cases d <;> simp [bin,reindex_and,reindex_or]
  project_target := Prod.ext (reindex_top _) (reindex_zero _)

def graphValue (a : Fin 9 → Sig) : Sig :=
  [bin false (a 0) (a 1),bin false (a 1) (a 2),bin false (a 2) (a 3),
   bin false (a 3) (a 4),bin false (a 4) (a 0),bin false (a 0) (a 5),
   bin false (a 1) (a 6),bin false (a 2) (a 7),bin false (a 3) (a 8),
   bin false (a 5) (a 7),bin false (a 6) (a 8),bin false (a 8) (a 5)].foldl (bin true) zero

lemma graphValue_bit (a : Fin 9 → Sig) (s : Bool) (i : Fin 689) :
    bit s i (graphValue a) = edgeF (fun j => bit s i (a j)) := by
  simp only [graphValue,List.foldl_cons,List.foldl_nil,bit_bin,ite_true,ite_false,
    Bool.false_eq_true,bit_zero,Bool.false_or,edgeF]

lemma chartProj_raw {a : Fin 9 → Sig} (h : graphValue a = target) (j : Fin 9) :
    (chartProj a).project (raw.getD j.val zero) = a j := by
  have result (s : Bool) (i : Fin 689) :
      bit s (chartIndex a s i) (raw.getD j.val zero) = bit s i (a j) := by
    let x : Fin 9 → Bool := fun t => bit s i (a t)
    let w := packBits x
    have decoded (t : Fin 9) : w.toNat.testBit t.val = x t := packBits_get x t
    have e : edgeF (fun t : Fin 9 => w.toNat.testBit t.val) = s := by
      simp only [decoded]
      change edgeF (fun t => bit s i (a t)) = s
      rw [← graphValue_bit,h]
      cases s
      · exact BitVec.getLsbD_zero
      · change (BitVec.allOnes 689).getLsbD i.val = true
        simp only [BitVec.getLsbD_allOnes,i.isLt,decide_true]
    have found := grantIndex_ok ⟨w.toNat,w.isLt⟩ s e j
    change bit s (grantIndex s w) (raw.getD j.val zero) = x j
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq,decoded] using found
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (reindex_bit _ _ _ hi).trans (result true ⟨i,hi⟩)
  · exact (reindex_bit _ _ _ hi).trans (result false ⟨i,hi⟩)

def cube (xs : List Sig) : Sig := neg (xs.foldr (bin true) zero)

lemma cube_proj (p : Projection) {xs : List Sig} (h : ∀ x ∈ xs, p.project x = zero) :
    p.project (cube xs) = one := by
  have e : p.project (xs.foldr (bin true) zero) = zero := by
    induction xs with
    | nil => exact map_zero p
    | cons x xs ih =>
      rw [List.foldr_cons,p.project_bin,h x (by simp),ih (fun a ha => h a (by simp [ha]))]
      exact (bin_laws zero).2.1
  rw [cube,p.project_neg,e,neg_laws.1]

lemma maskReflect (p : Projection) {m : Sig} (hw : p.project m = one)
    (a b : Sig) (h : bin false m a = bin false m b) : p.project a = p.project b := by
  have e := congrArg p.project h
  rw [p.project_bin,p.project_bin,hw] at e
  have left (z : Sig) : bin false one z = z := by
    exact Prod.ext BitVec.allOnes_and BitVec.allOnes_and
  rwa [left,left] at e
structure Minor where
  v : List Sig
  limit : Nat
  excludes : ¬ possible v.toFinset limit

def chartSlot (g : Minor) (code : Nat) (j : Fin 9) : Sig :=
  g.v.getD ((code >>> (4*j.val)) &&& 15) zero

def absent (code : Nat) (j : Fin 9) := ((code >>> (4*j.val)) &&& 15) == 15

def faceMask (code : Nat) : Sig :=
  cube (((List.finRange 9).filter (absent code)).map (fun j => raw.getD j.val zero))

def matchesMinor (g : Minor) (code : Nat) : Bool :=
  graphValue (chartSlot g code) == target &&
  (List.finRange 9).all (fun j =>
    if absent code j then chartSlot g code j == zero else g.v.contains (chartSlot g code j))

def chartFace (g : Minor) (code : Nat) (ok : matchesMinor g code = true) : MaskedFace g.limit := by
  let a := chartSlot g code
  let p := chartProj a
  obtain ⟨he,legal⟩ := Bool.and_eq_true_iff.mp ok
  have corr (j : Fin 9) : p.project (raw.getD j.val zero) = a j :=
    chartProj_raw (beq_iff_eq.mp he) j
  have hw (j : Fin 9) := List.all_eq_true.mp legal j (List.mem_finRange j)
  have hz : p.project (faceMask code) = one := by
    apply cube_proj
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    rw [corr]
    have h := hw j
    simpa only [(List.mem_filter.mp hj).2,ite_true,beq_iff_eq] using h
  refine ⟨p, faceMask code, maskReflect p hz, ?_⟩
  rintro ⟨k,t,S,hk,hl,sub⟩
  apply g.excludes
  refine ⟨k,t,S,hk,hl,?_⟩
  intro z hm
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (sub hm)
  have orig : b ∈ List.ofFn (fun j : Fin 9 => raw.getD j.val zero) := by
    rw [raw_id]
    exact List.mem_toFinset.mp hb
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp orig
  have h := hw j
  by_cases cut : absent code j = true
  · have eq : a j = zero := by simpa only [cut,ite_true,beq_iff_eq] using h
    exact False.elim ((live_proper hl _ hm).1 ((corr j).trans eq))
  · rw [corr]
    exact List.mem_toFinset.mpr (by simpa [cut,a] using h)
def faceSource : Nat → Minor
  | 15 => ⟨wires15,3,graph_15⟩
  | 31 => ⟨wires31,6,graph_31⟩
  | 45 => ⟨wires45,2,graph_45⟩
  | 47 => ⟨wires47,4,graph_47⟩
  | 51 => ⟨wires51,2,graph_51⟩
  | 55 => ⟨wires55,4,graph_55⟩
  | 63 => ⟨wires63,7,graph_63⟩
  | 111 => ⟨wires111,6,graph_111⟩
  | 119 => ⟨wires119,5,graph_119⟩
  | 127 => ⟨wires127,8,graph_127⟩
  | 189 => ⟨wires189,7,graph_189⟩
  | 191 => ⟨wires191,10,graph_191⟩
  | 250 => ⟨wires250,4,graph_250⟩
  | 251 => ⟨wires251,7,graph_251⟩
  | 255 => ⟨wires255,11,graph_255⟩
  | _ => ⟨wires3,0,graph_3⟩
def faceTags : Array Nat := #[255,255,127,255,251,127,111,255,251,127,111,191,127,63,127,111,119,55,191,189,111,47,63,47,55,15,255,127,251,111,251,250,127,63,47,111,47,45,127,191,63,127,63,47,127,111,119,55,191,63,63,31,111,55,15,63,47,55,15,55,51,127,119,111,55,111,55,15,127,127,119,191,111,63,55,127,63,47,191,63,111,55,63,55,55,51,63,47,31,15,15,191,63,111,55,189,47,47,15,111,47,45,63,31,15,47,15,55,15,15,191,111,63,55,63,31,15,111,55,15,189,47,47,15,47,15,47,45,15,63,55,55,51,47,15,47,15,45,255,251,251,250,127,111,127,111,63,47,47,45,127,111,111,119,55,55,15,191,111,189,47,111,47,45,63,47,55,15,63,55,47,15,31,15,15,15,63,55,47,15,47,45,55,51,15,127,111,119,55,111,55,15,63,47,47,45,55,15,55,15,51,63,47,55,15,55,51,47,45,15,31,15,15,15,15,15]
def faceCodes : Array Nat := #[0x25376104f,0x1762405f3,0x1362504ff,0x267143f50,0x63451f2f,0x156032ff4,0x135240fff,0x73526f401,0x43605f2f1,0x26315ff40,0x25314fff0,0x2536f104f,0x1460f23f5,0x354f12ff,0x1520f6f34,0x1420f5f3f,0x1450f2ff3,0x241f3fff,0x6352ff401,0x5241ff30f,0x2031ff4f5,0x2031ff4ff,0x4530fff21,0x1420fff3f,0x1420ffff3,0x1302fffff,0x765f32104,0x253f6104f,0x456f301f2,0x243f510ff,0x624f5f301,0x523f4f1f0,0x364ff2105,0x352ff401f,0x243ff10ff,0x342fff015,0x342fff01f,0x231fff0ff,0x24f36105f,0x16f2405f3,0x42f3501ff,0x26f143f50,0x45f023ff1,0x13f240fff,0x62f15f340,0x52f14f3f0,0x52f14ff30,0x43f02fff1,0x61f2f5043,0x24f3f105f,0x41f0f32f5,0x24f3f10ff,0x25f1f3f40,0x14f0f2ff3,0x13f2f0fff,0x54f0ff321,0x31f2ff04f,0x41f0ff2f3,0x31f2ff0ff,0x43f0fff21,0x32f0ffff1,0x65ff21043,0x54ff2103f,0x54ff210f3,0x42ff301ff,0x35fff2104,0x24fff103f,0x30fff21ff,0x1f265043f,0x1f62405f3,0x1f25403ff,0x2f6143f50,0x1f2540f3f,0xf5421ff3,0xf3421fff,0x3f245f610,0x3f245ff10,0x2f314fff0,0x2f16f3405,0xf45f123f,0x1f52f04f3,0xf34f12ff,0xf14f5f23,0xf14f3f2f,0xf41f3ff2,0xf23f1fff,0x3f42ff501,0x2f13ff40f,0x3f24fff10,0x2f13fff0f,0x2f31ffff0,0x6f5f32104,0x4f3f5012f,0x2f3f015f4,0x1f2f403ff,0x1f2f45f30,0x1f2f40f3f,0x2f3f01ff4,0x2f3f01fff,0x3f2f4f510,0x3f2f4ff10,0x2f1f3fff0,0x3f4ff2105,0x3f4ff210f,0x2f3ff10ff,0x2f1ff3f04,0x2f1ff3f0f,0x2f1fff403,0x3f2fff01f,0x3f2ffff10,0x6ff512340,0x2ff35104f,0x4ff3105f2,0x1ff2403ff,0x3ff412f50,0x3ff412ff0,0x2ff301fff,0x3ff25f401,0x2ff14ff30,0x3ff20fff1,0x5ff4f1230,0x2ff3f104f,0x1ff2f04f3,0x2ff3f10ff,0x2ff1f3f40,0x2ff1f3ff0,0x3ff2ff401,0x2ff1ff30f,0x3ff2fff01,0x5fff40123,0x4fff3012f,0x4fff103f2,0x3fff201ff,0x3fff12f40,0x3fff12ff0,0x3ffff2104,0x3ffff210f,0x2ffff1f30,0xf76543210,0xf4562301f,0xf65432f10,0xf54321f0f,0xf3645f210,0xf3425ff01,0xf253f6104,0xf243f510f,0xf352ff401,0xf243ff10f,0xf342fff01,0xf231fff0f,0xf65f32104,0xf54f3210f,0xf35f4f210,0xf54ff2103,0xf42ff301f,0xf24fff103,0xf30fff21f,0xf6f543210,0xf2f34015f,0xf5f4321f0,0xf2f3401ff,0xf3f204f51,0xf3f204ff1,0xf2f130fff,0xf3f45f210,0xf2f14f3f0,0xf2f14ff30,0xf3f20fff1,0xf4f3f5012,0xf1f2f403f,0xf1f2f40f3,0xf2f3f01ff,0xf3f4ff210,0xf2f3ff10f,0xf2f1ff3f0,0xf3f2fff01,0xf5ff34012,0xf4ff2103f,0xf4ff210f3,0xf3ff012ff,0xf3ff4f210,0xf2ff3f1f0,0xf4fff3012,0xf3fff201f,0xf3ffff210,0xff6543210,0xff4523f01,0xff543f210,0xff243ff10,0xff54f3210,0xff42ff301,0xff30fff21,0xff5f23401,0xff4f3210f,0xff4f23f01,0xff3f21f0f,0xff4f2f301,0xff3f0ff21,0xff4ff2103,0xff3ff012f,0xff3fff201,0xfff543210,0xfff4123f0,0xfff412f30,0xfff310ff2,0xfff43f210,0xfff32ff10,0xfff4f3210,0xfff3f21f0,0xfff3ff012,0xffff43210,0xffff3210f,0xffff123f0,0xffff23f01,0xffff3f012,0xfffff3210]
def familyModel (j : Nat) := faceSource (faceTags[j]?.getD 3)
def familyCode (j : Nat) := faceCodes[j]?.getD 0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma familyValid : ∀ j : Fin 216, matchesMinor (familyModel j.val) (familyCode j.val) = true := by decide +kernel
def familyFace (j : Fin 216) := chartFace (familyModel j.val) (familyCode j.val) (familyValid j)

abbrev Tagged := Sig × Nat

def below (a b : Nat) : Prop := ∀ j, a.testBit j = true → b.testBit j = true

lemma below_left {a b n : Nat} (h : below (a ||| b) n) : below a n :=
  fun j hj => h j (by simp [Nat.testBit_or,hj])

lemma below_right {a b n : Nat} (h : below (a ||| b) n) : below b n :=
  fun j hj => h j (by simp [Nat.testBit_or,hj])

def tally (mask : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => tally mask n + (mask.testBit n).toNat

def used : List Tagged → Nat
  | [] => 0
  | a::t => a.2 ||| used t

lemma below_used {a : Tagged} {v : List Tagged} (h : a ∈ v) : below a.2 (used v) := by
  induction v with
  | nil => cases h
  | cons b r ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact fun j hh => by simp [used,Nat.testBit_or,hh]
    · exact fun j hh => by simp [used,Nat.testBit_or,ih h j hh]

def includes (W : Finset Sig) (a : Sig) : Prop := a ∈ W ∨ ¬ proper a

lemma includes_mono {a z} {W : Finset Sig} (h : includes W a) : includes (insert z W) a :=
  h.imp (Finset.mem_insert_of_mem) id

def Shared {m} (f : MaskedFace m) (d : Nat) (v : List Tagged) : Prop :=
  ∀ mask, ∃ c W, Built (raw.toFinset.image f.proj.project) c W ∧ c ≤ tally mask d ∧
    ∀ a ∈ v, below a.2 mask → includes W (f.proj.project a.1)

def tagRaw := raw.map fun w => (w,0)

lemma sharedRaw {m} (f : MaskedFace m) : Shared f 0 tagRaw := by
  intro mask
  refine ⟨0,_,Built.start,Nat.le_refl _,?_⟩
  intro a ha hh
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
  exact Or.inl (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hw))

def maskedSame (m a b : Sig) := bin false m a == bin false m b

def freeWire (m w : Sig) := maskedSame m w zero || maskedSame m w one || raw.any (maskedSame m w)

lemma maskSame_project {k} (f : MaskedFace k) {a b}
    (h : maskedSame f.mask a b = true) : f.proj.project a = f.proj.project b :=
  f.reflects _ _ (beq_iff_eq.mp h)

lemma freeWire_rep {k} (f : MaskedFace k) {a}
    (h : freeWire f.mask a = true) {c W}
    (hw : Built (raw.toFinset.image f.proj.project) c W) : includes W (f.proj.project a) := by
  have subs : raw.toFinset.image f.proj.project ⊆ W := by
    induction hw with
    | start => exact fun _ h => h
    | gate wh hg ih => exact Finset.Subset.trans ih (Finset.subset_insert _ _)
  simp only [freeWire,Bool.or_eq_true] at h
  rcases h with (hz | ho) | hr
  · exact Or.inr fun hp => hp.1 ((maskSame_project f hz).trans (map_zero _))
  · exact Or.inr fun hp => hp.2 ((maskSame_project f ho).trans (map_one _))
  · obtain ⟨b,hb,he⟩ := List.any_eq_true.mp hr
    rw [maskSame_project f he]
    exact Or.inl (subs (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hb)))

def opValue (op : Nat) (a b : Sig) : Sig :=
  if op = 2 then neg a else bin (op == 1) a b

def depsNext (m : Sig) (d op : Nat) (a b : Tagged) : Tagged :=
  let g := opValue op a.1 b.1
  (g, if freeWire m g then 0 else if maskedSame m g a.1 then a.2 else
    if maskedSame m g b.1 then b.2 else (if op = 2 then a.2 else a.2 ||| b.2) ||| (1 <<< d))

lemma opReady {m} (f : MaskedFace m) (op : Nat) {W : Finset Sig} {a b : Sig}
    (ha : includes W (f.proj.project a)) (hb : op ≠ 2 → includes W (f.proj.project b)) :
    canBuild W (f.proj.project (opValue op a b)) := by
  have cv {z : Sig} (h : includes W z) : represented W.toList z :=
    h.imp Finset.mem_toList.mpr id
  unfold opValue
  split
  · rw [f.proj.project_neg]
    rcases operand_cases (cv ha) with hz | ho | ⟨hm,hp⟩
    · exact Or.inl (Or.inr (fun bad => bad.2 (by rw [hz,neg_laws.1])))
    · exact Or.inl (Or.inr (fun bad => bad.1 (by rw [ho,neg_laws.2])))
    · exact neg_rep _ _ hm
  · rename_i h
    rw [f.proj.project_bin]
    exact bin_rep _ (cv ha) (cv (hb h))

theorem shared_gate {m} (f : MaskedFace m) {d v} (h : Shared f d v)
    (a b : Tagged) (ha : a ∈ v ∨ a = (zero,0)) (hb : b ∈ v ∨ b = (zero,0)) (op : Nat) :
    Shared f (d+1) (depsNext f.mask d op a b :: v) := by
  intro mask
  obtain ⟨c,W,hW,hc,haveOld⟩ := h mask
  have getOld {x : Tagged} (hx : x ∈ v ∨ x = (zero,0)) (hs : below x.2 mask) :
      includes W (f.proj.project x.1) := by
    rcases hx with h | rfl
    · exact haveOld _ h hs
    · exact Or.inr (fun hp => hp.1 (map_zero _))
  let g := opValue op a.1 b.1
  let need := if op = 2 then a.2 else a.2 ||| b.2
  by_cases fresh : below (depsNext f.mask d op a b).2 mask
  · by_cases old : includes W (f.proj.project g)
    · refine ⟨c,W,hW,by simp only [tally]; omega,?_⟩
      intro x hx hh
      rcases List.mem_cons.mp hx with rfl | hx
      · exact old
      · exact haveOld _ hx hh
    · have hu : ¬ freeWire f.mask g = true := fun ok => old (freeWire_rep f ok hW)
      have hx : ¬ maskedSame f.mask g a.1 = true := by
        intro ok
        have sub : below a.2 mask := by simpa [depsNext,g,hu,ok] using fresh
        exact old ((maskSame_project f ok).symm ▸ getOld ha sub)
      have hy : ¬ maskedSame f.mask g b.1 = true := by
        intro ok
        have sub : below b.2 mask := by simpa [depsNext,g,hu,hx,ok] using fresh
        exact old ((maskSame_project f ok).symm ▸ getOld hb sub)
      have sub : below (need ||| (1 <<< d)) mask := by simpa [depsNext,hu,hx,hy,g,need] using fresh
      have sel := below_left sub
      have high : mask.testBit d = true := sub d (by simp [Nat.testBit_or,Nat.testBit_shiftLeft])
      have needA : below a.2 mask := by by_cases h : op=2 <;> simp [need,h] at sel <;> first | exact sel | exact below_left sel
      have needB (h : op ≠ 2) : below b.2 mask := by
        simp [need,h] at sel
        exact below_right sel
      have good := opReady f op (getOld ha needA) (fun h => getOld hb (needB h))
      refine ⟨c+1,_,Built.gate hW good,by simp [tally,high]; omega,?_⟩
      intro x hx hh
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (Finset.mem_insert_self _ _)
      · exact includes_mono (haveOld _ hx hh)
  · refine ⟨c,W,hW,by simp only [tally]; omega,?_⟩
    intro x hx hh
    rcases List.mem_cons.mp hx with rfl | hx
    · exact False.elim (fresh hh)
    · exact haveOld _ hx hh

lemma shared_sub {m d v w} (f : MaskedFace m) (h : Shared f d v) (sub : ∀ a ∈ w, a ∈ v) :
    Shared f d w := by
  intro mask
  obtain ⟨c,W,built,hc,ha⟩ := h mask
  exact ⟨c,W,built,hc,fun a hmem => ha a (sub a hmem)⟩

def pricedCut (mask : Sig) (budget limit d : Nat) (v : List Tagged) :=
  let live := v.map Prod.fst
  decide (tally (used v) d + budget < limit+1+maskCost mask live)

theorem pricedCut_sound {m k d v} (f : MaskedFace m) (h : Shared f d v)
    (nd : (v.map Prod.fst).Nodup) (check : pricedCut f.mask k m d v = true) :
    NoSuffix k (v.map Prod.fst).toFinset := by
  have cnt : maskCost f.mask (v.map Prod.fst) ≤ constants f.proj (v.map Prod.fst).toFinset := by
    unfold maskCost
    rw [← List.toFinset_card_of_nodup (nd.filter _)]
    apply Finset.card_le_card
    intro a ha
    obtain ⟨ha,hm⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ha,maskConstant_sound f hm⟩
  obtain ⟨c,W,built,hc,valid⟩ := h (used v)
  have lim := of_decide_eq_true check
  change tally (used v) d + k < m+1+maskCost f.mask (v.map Prod.fst) at lim
  intro q hq t
  apply projected_contradiction f.proj built _ f.lower (by omega)
  intro a ha hp
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  exact (valid x hx (below_used hx)).resolve_right (fun hn => hn hp)

def partialRaw : List Sig := [(0x44455455455d05a22ca884a5911254d2a2d0088a582a11134108b2a2b90888694100ac440107e00807f003e01f83e00103e01e042084423e0fc3c08020042022083e3e07000000000000000000fff000fff0000000dc,0x7e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07544544544544544544544544544544544544),(0x988888889882284cc11128482225892c4523911482c5622c8af3454c42353192bae753abe0f800178000fc00200403f0f801e008410884401004117e1f805e05e7c00078000000000000000fff000000000000fff822,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038823823823823823823823823823823823823),(0x1e1f0e1e1f0f3cef0fbe1ef6f7879e1c70e39bc3ce3e1b870f31e7d78739ddac4d30d85c0621043f883ff8c0041086422084264fc027c3e032fbc0f86018be21e60847fd9000000000000fff000000000000ffffff374,0x1f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0314314314314314314314314314314314314),(0xee00ee00ef17e1f701de1f8f3b88ee07f03e1fe1ed693fc0f89d0ef793a7c7ffc77dbcf8a4288421082110448ffc0044ffde22109f90089ff08802085ffc8008b7ffc480000000fff000000000000fff000fff00086d,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000069069069069069069069069069069069069),(0xffef0110feec507ffc022eb03fff120ffe851ddb00f87fff009d6a776843f9dc2b61a0e3ff0101fffc500083f210a1ef10840a7fe4003fe441008fffe210001ff9088802000000000000000000000ffffff000000893,0x3ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000a92a92a92a92a92a92a92a92a92a92a92a92),(0xeeeeefee000010777ffdc010fff6fdf008407ddafa92fbb7ef4098f76fda36fdfc9bef15084a284250822509042108982528917fffffc00802014fffff7fffe000121004000fff000fff000000fff000000000000119,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000007fffffc00000000fffffffffe00000000001b01b01b01b01b01b01b01b01b01b01b01b),(0x1feefffeeeffbbe0882021110fbbefdfff7be822010843bbeef7f6d80040206faf74610021084308421044233ff7fff004001007ffffffffffffff0100400040102400220fff000000000000fff000000000000000682,0x3fffffe000000007ffffffffffffff00000000000000000000dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfffeeffffeefbff777dfffee844002080140600105067bb6efdd65ff6bfdc8030ca04013ffffff0002080023ffffffffffffffa108211000041044228821095000422101000000000ffffff000000000000000000460,0x3fffffe0000000003ffffffffffffff8000000000000000000000000000000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0x1fefefeeeffebef7f75fddeff7fb7efb77ffadfdeee79c40010a08000842025000090020bffffffffffeffffe08c210008210004210422110886228411042108004210208fffffffff000000000000000000000000f20,0x3fffffffffffffffc000000000000000000000000000000000000000000000000f00f00f00f00f00f00f00f00f00f00f00f00)]
def partialFace : Projection := wideProjection 0xe5abeaeab591aaeaaaa4b4a9ea6a9563a8ea2a84dfa7e9ea74e1a6e9aa6515a5e96a551ba4e92a449da3e8ea358ea2e8aa24f4a1e86a14e7a0d27a06809fd759f5109ee7a9e52949a769d6745ca729c6703ea6e9b66c35e6a4166899e6659e6498e625126097e5e4d54696e5a9654395d849551194e5294565501069364c92d8b9264891cda916443ee429056f8fe3e8f50d8ee3a62a388dce98d6344e2328c6303ca2e8b62c36e2a8a58789d818962488cee884ae87d7b3021c86e1a3be1885e1638e1484d5b8452283e0e834e082d248252144e06814d080d2047200305907f5fc7ed6b7e5f87dcb37d5f42c1f27c4cd7bdee7b5607ad007a5e863de6579e478de2389e0561de7749c451da28dd8529d6755d4479d2745d0295ce7349a72d01725c871ccf4bdc470d2b429c06fdbe358d26ed0c411706ddb63cdb46ccd94b9286bdae351033550b6a5a8619a64b0c62fda22e9a067cbb674a92919a2f0b965d962a0c52a83c6459063d8e96d5162d8a5e18061d864bd8499141605804a569a493c5ed2458d783f4db5d56f59972359705bcd03e0d05ad575a4eb59d665949b58ce53056056d5e2f0aa56e093855855ca5504841e06c54510510fc4e13f52d4a525484a54642d4450d2e505404fcea7753c400e4481383552c4d4bb33d222d11b4bd2e32d2c4acc54a52849d264712431522485202ed1e4ad1c46c9d49c60151164551444d1244510428d44350c42d0a410ca3cd064150440ce9405002e8e03f4fc3ecfa3a0f83b8b037cf43ccf239ce33bcee38ca93acea3a4e839ce1394e438ce2384e037d402104836cda364d235cd6354d4324d2738d033cc4334cc32cca324c829cc6314c42fca4304c02fcb9270bc2ecba2e4601e0600f0b42ccae26cb02a0ae65c30090aa2a4a829d2e294a428c9a4a06c0c0182749c26c9a3ac540600c1200c56c3c0909d2108421084210842108421084210841e0781e0781e0781e0781e0781e0781b06c1b06c1b06c1b06c1b06c1b06c1806018060180601806018060180601505415054150541505415054150541204812048120481204812048120480f03c0f03c0f03c0f03c0f03c0f03c0c0300c0300c0300c0300c0300c0300902409024090240902409024090240601806018060180601806018060180300c0300c0300c0300c0300c0300c5c13c394c137d2694cd72909a2c0c4 0x19202c0b02c0b02d88621886218860d8360d8360c0a0280a0280a029795e5795e40902409024090256e5b96e5b96e5a96a5a96a02008020080200857d5f57d5f57d5a5695a5695a5555555555555525495201c0701c0701c0701806018060194250942509424f53d4f53d4f5394e5394e5344d1344d1344c1304c130014050140501405495254952549521485214851d4751d47519465194651745c0401004010044350d4350d4340300c0300c0300d0240902409023f8fe3f8fe3e4f93e4f93e4f53d4f53d4f03c0f03c0f03b0ec3b0ec008020080200802388e2388e2378de378de370dc35cd735cd735c010040100401004cd334cd334000000000000000c2308c2308c22f4bd2f4bd2f4b82e0b82e0b82d4b52d4b12c4b12c4ad2b4ad2b4ab2aca6298a6298a6284a1284a12849e2789e2649926499264962589624c9324c902409002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c020040002c0a0240801c060140400c0200400
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem partialRoot : starting.toFinset.image partialFace.project = insert zero partialRaw.toFinset := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem partialCharge : constants partialFace starting.toFinset = 1 := by decide +kernel
theorem partialEssential : allEssential partialRaw = true := by decide +kernel

theorem splitRoot {k t S} (hh : Live k t S) (lim : k ≤ 14)
    (roots : S = raw.toFinset ∨ S = starting.toFinset)
    (dead : NoSuffix 14 raw.toFinset) (live : NoSuffix 13 partialRaw.toFinset) : False := by
  rcases roots with rfl | rfl
  · exact dead k lim t hh
  · obtain ⟨q,loss,j,hj,u,T,hl,sub⟩ := project_live_cost hh partialFace
    rw [partialCharge] at loss
    rw [partialRoot] at sub
    have st : T ⊆ partialRaw.toFinset := by
      intro z hz
      exact (Finset.mem_insert.mp (sub hz)).resolve_left (live_proper hl z hz).1
    exact live j (by omega) u (essential_wires hl st partialEssential ▸ hl)

def digitA (c : Nat) := c / 192
def digitB (c : Nat) := (c / 12) % 16
def digitOp (c : Nat) := (c / 4) % 3
def keepA (c : Nat) := c.testBit 1
def keepB (c : Nat) := c.testBit 0
def label (op i j : Nat) (a b : Bool) := (i*16+j)*12 + op*4+a.toNat*2+b.toNat

def selectPins {α : Type} (v : List α) (i j : Nat) (ka kb : Bool) :=
  (v.zipIdx.filter (fun q => (q.2 != i || ka) && (q.2 != j || kb))).map Prod.fst

def advancePins {α : Type} (g : α) (v : List α) (c : Nat) :=
  g :: selectPins v (digitA c) (digitB c) (keepA c) (keepB c)

def gateOf (v : List Sig) (c : Nat) :=
  opValue (digitOp c) (v.getD (digitA c) zero) (v.getD (digitB c) zero)

def after (v : List Sig) (c : Nat) := advancePins (gateOf v c) v c

lemma mem_select {α : Type} {x : α} {v : List α} {i j ka kb} :
    x ∈ selectPins v i j ka kb ↔ ∃ h : Fin v.length, v[h.val] = x ∧
      (h.val ≠ i ∨ ka = true) ∧ (h.val ≠ j ∨ kb = true) := by
  simp only [selectPins,List.mem_map,List.mem_filter,List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff,
    Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne]
  constructor
  · rintro ⟨⟨b,n⟩,⟨⟨hn,eq⟩,h1,h2⟩,rfl⟩
    exact ⟨⟨n,by omega⟩,by simpa using eq,h1,h2⟩
  · rintro ⟨⟨n,hn⟩,eq,h1,h2⟩
    exact ⟨(x,n),⟨⟨hn,eq⟩,h1,h2⟩,rfl⟩

lemma select_sub {α : Type} {x : α} {v : List α} {i j ka kb}
    (h : x ∈ selectPins v i j ka kb) : x ∈ v := by
  obtain ⟨n,rfl,_,_⟩ := mem_select.mp h
  exact List.getElem_mem _

lemma select_map {α β : Type} (f : α → β) (v : List α) (i j : Nat) (ka kb : Bool) :
    (selectPins v i j ka kb).map f = selectPins (v.map f) i j ka kb := by
  unfold selectPins
  suffices ∀ n, (((v.zipIdx n).filter (fun q => (q.2 != i || ka) && (q.2 != j || kb))).map Prod.fst).map f =
    ((((v.map f).zipIdx n).filter (fun q => (q.2 != i || ka) && (q.2 != j || kb))).map Prod.fst) from this 0
  intro n
  induction v generalizing n with
  | nil => rfl
  | cons a v ih =>
    simp only [List.map_cons,List.zipIdx_cons,List.filter_cons]
    split <;> simp only [List.map_cons,ih]

lemma label_ok {op i j : Nat} (ho : op < 3) (hj : j < 16) (a b : Bool) :
    digitA (label op i j a b) = i ∧ digitB (label op i j a b) = j ∧
    digitOp (label op i j a b) = op ∧ keepA (label op i j a b) = a ∧
    keepB (label op i j a b) = b := by
  have bits (n : Nat) : (n*4+a.toNat*2+b.toNat).testBit 1 = a ∧
      (n*4+a.toNat*2+b.toNat).testBit 0 = b := by
    cases a <;> cases b <;> simp [Nat.testBit_eq_decide_div_mod_eq] <;> omega
  have pos : label op i j a b = ((i*16+j)*3+op)*4+a.toNat*2+b.toNat := by unfold label; omega
  exact ⟨by unfold digitA label; cases a <;> cases b <;> simp <;> omega,
    by unfold digitB label; cases a <;> cases b <;> simp <;> omega,
    by unfold digitOp label; cases a <;> cases b <;> simp <;> omega,
    by simpa only [keepA,pos] using (bits ((i*16+j)*3+op)).1,
    by simpa only [keepB,pos] using (bits ((i*16+j)*3+op)).2⟩

lemma read_mem {α : Type} {v : List α} {i : Nat} (h : i < v.length) (z : α) :
    v.getD i z = v[i] := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]

lemma pins_set {v : List Sig} {U : Finset Sig} (nd : v.Nodup)
    (i j : Fin v.length)
    (he : v.toFinset = insert v[i.val] (insert v[j.val] U)) :
    (selectPins v i.val j.val (decide (v[i.val] ∈ U)) (decide (v[j.val] ∈ U))).toFinset = U := by
  ext w
  rw [List.mem_toFinset,mem_select]
  constructor
  · rintro ⟨n,rfl,ha,hb⟩
    have hin : v[n.val] ∈ v.toFinset := List.mem_toFinset.mpr (List.getElem_mem _)
    rw [he] at hin
    rcases Finset.mem_insert.mp hin with eq | hin
    · have en : n.val = i.val := (List.Nodup.getElem_inj_iff nd).mp eq
      exact eq ▸ of_decide_eq_true (ha.resolve_left (fun h => h en))
    · rcases Finset.mem_insert.mp hin with eq | hin
      · have en : n.val = j.val := (List.Nodup.getElem_inj_iff nd).mp eq
        exact eq ▸ of_decide_eq_true (hb.resolve_left (fun h => h en))
      · exact hin
  · intro h
    have hv : w ∈ v.toFinset := he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
    obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hv)
    refine ⟨⟨n,hn⟩,eq,?_,?_⟩
    · by_cases en : n=i.val
      · subst n; right; simpa [eq] using h
      · exact Or.inl en
    · by_cases en : n=j.val
      · subst n; right; simpa [eq] using h
      · exact Or.inl en

lemma pins_nd {v : List Sig} (nd : v.Nodup) (i j : Nat) (a b : Bool) :
    (selectPins v i j a b).Nodup := by
  have h := (List.filter_sublist (l := v.zipIdx)
    (p := fun (q : Sig × Nat) => (q.2 != i || a) && (q.2 != j || b))).map Prod.fst
  exact (by simpa [selectPins] using h : (selectPins v i j a b).Sublist v).nodup nd

def pass (k : Nat) (v : List Sig) : Bool :=
  decide (v.length ≤ k+1) && unionSep (decide (v.length < k+1)) v == top

lemma pass_necessary {v k q t} (nd : v.Nodup) (leq : q ≤ k) (h : Live q t v.toFinset) :
    pass k v = true := by
  have size := (live_size h).2
  rw [List.toFinset_card_of_nodup nd] at size
  simp only [pass,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  refine ⟨by omega,?_⟩
  by_cases lt : v.length < k+1
  · simp only [lt,decide_true]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨a,ha,hs⟩ := live_sep h i hi
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using
      (mem_unionSep true v i).mpr ⟨a,List.mem_toFinset.mp ha,sep_weaken t a i hi hs⟩
  · have ht : t=0 := by omega
    subst t
    simp only [lt,decide_false]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨a,ha,hs⟩ := live_sep h i hi
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using
      (mem_unionSep false v i).mpr ⟨a,List.mem_toFinset.mp ha,hs⟩

def scanActs (n : Nat) (visit : Nat → Bool) : Bool :=
  (List.range n).all fun i =>
    visit (label 2 i i false false) && visit (label 2 i i true true) &&
    (List.range i).all (fun j =>
      [0,1].all fun op => [false,true].all fun a =>
        [false,true].all fun b => visit (label op i j a b))

lemma scan_unary {n visit} (h : scanActs n visit = true) (i : Fin n) (b : Bool) :
    visit (label 2 i.val i.val b b) = true := by
  have s := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  obtain ⟨⟨a,bh⟩,_⟩ := (Bool.and_eq_true_iff.mp s).imp_left Bool.and_eq_true_iff.mp
  cases b <;> assumption

lemma scan_binary {n visit} (h : scanActs n visit = true) (i j : Fin n)
    (lt : j.val < i.val) (op : Nat) (hop : op ∈ [0,1]) (a b : Bool) :
    visit (label op i.val j.val a b) = true := by
  have s := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have x := List.all_eq_true.mp (Bool.and_eq_true_iff.mp s).2 j.val (List.mem_range.mpr lt)
  have y := List.all_eq_true.mp x op hop
  have z := List.all_eq_true.mp y a (by cases a <;> simp)
  exact List.all_eq_true.mp z b (by cases b <;> simp)

lemma label_value {v : List Sig} (i j : Fin v.length) {op : Nat} (hop : op < 3)
    (small : j.val < 16) (ka kb : Bool) :
    gateOf v (label op i.val j.val ka kb) = opValue op v[i.val] v[j.val] := by
  obtain ⟨x,y,o,_,_⟩ := label_ok (i := i.val) hop small ka kb
  unfold gateOf
  rw [x,y,o,read_mem i.isLt,read_mem j.isLt]

lemma label_after {v : List Sig} (i j : Fin v.length) {op : Nat} (hop : op < 3)
    (small : j.val < 16) (ka kb : Bool) :
    after v (label op i.val j.val ka kb) =
    opValue op v[i.val] v[j.val] :: selectPins v i.val j.val ka kb := by
  obtain ⟨x,y,o,a,b⟩ := label_ok (i := i.val) hop small ka kb
  unfold after advancePins
  rw [label_value i j hop small,x,y,a,b]

lemma available_of {v : List Sig} {g : Sig} (fresh : g ∉ v.toFinset) (hp : proper g) :
    gateAvailable v g = true := by
  simp only [gateAvailable,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,bne_iff_ne]
  exact ⟨⟨by simpa using fresh,hp.1⟩,hp.2⟩

lemma proof_after {v : List Sig} {U : Finset Sig} {q t : Nat} {g : Sig}
    (nd : v.Nodup) {i j : Nat} {ka kb : Bool}
    (set : (selectPins v i j ka kb).toFinset = U) (fresh : g ∉ v.toFinset)
    (tail : Live q t (insert g U)) :
    (g :: selectPins v i j ka kb).Nodup ∧ Live q t (g :: selectPins v i j ka kb).toFinset ∧
      gateAvailable v g = true := by
  refine ⟨List.nodup_cons.mpr ⟨fun h => fresh (List.mem_toFinset.mpr (select_sub h)),pins_nd nd _ _ _ _⟩,?_,
    available_of fresh (live_proper tail _ (Finset.mem_insert_self _ _))⟩
  rwa [List.toFinset_cons,set]

def GoodChild (q t : Nat) (v w : List Sig) (g : Sig) := w.Nodup ∧ Live q t w.toFinset ∧ gateAvailable v g = true

lemma acceptLabel {v : List Sig} (i j : Fin v.length) {op q t : Nat} (hop : op < 3)
    (small : j.val < 16) (ka kb : Bool)
    (h : GoodChild q t v (opValue op v[i.val] v[j.val] :: selectPins v i.val j.val ka kb) (opValue op v[i.val] v[j.val])) :
    GoodChild q t v (after v (label op i.val j.val ka kb)) (gateOf v (label op i.val j.val ka kb)) :=
  Eq.mpr (congrArg₂ (GoodChild q t v) (label_after i j hop small ka kb) (label_value i j hop small ka kb)) h

lemma operationBin (d : Bool) (x y : Sig) : opValue d.toNat x y = bin d x y := by
  have h : d.toNat ≠ 2 := by cases d <;> decide
  have eq : (d.toNat == 1) = d := by cases d <;> decide
  unfold opValue
  rw [if_neg h,eq]

lemma binary_action {v : List Sig} {U : Finset Sig} {q t : Nat}
    (nd : v.Nodup) (bound : v.length ≤ 16) (i j : Fin v.length) (op : Nat) (hop : op < 3)
    (ka kb : Bool) (rest : (selectPins v i.val j.val ka kb).toFinset = U)
    (rf : opValue op v[i.val] v[j.val] ∉ v.toFinset)
    (tail : Live q t (insert (opValue op v[i.val] v[j.val]) U)) :
    GoodChild q t v (after v (label op i.val j.val ka kb)) (gateOf v (label op i.val j.val ka kb)) :=
  acceptLabel i j hop (Nat.lt_of_lt_of_le j.isLt bound) ka kb (proof_after nd rest rf tail)
def nodeTest (k : Nat) (v : List Sig) (close : Nat → Bool) : Bool :=
  !(v == [target]) && scanActs v.length (fun c =>
    !(gateAvailable v (gateOf v c) && pass k (after v c)) || close c)

set_option maxHeartbeats 0 in
theorem node_sound {k v close} (nd : v.Nodup) (width : v.length ≤ 16)
    (checked : nodeTest k v close = true)
    (closed : ∀ c, (after v c).Nodup → close c = true → NoSuffix k (after v c).toFinset) :
    NoSuffix (k+1) v.toFinset := by
  intro q hq t h
  obtain ⟨stop,scan⟩ := Bool.and_eq_true_iff.mp checked
  have reach (c : Nat) (bound : ∀ f, scanActs v.length f = true → f c = true)
      {r u} (hr : r ≤ k) (ns : (after v c).Nodup) (run : Live r u (after v c).toFinset)
      (avail : gateAvailable v (gateOf v c) = true) : False := by
    have z := bound _ scan
    change (!(gateAvailable v (gateOf v c) && pass k (after v c)) || close c) = true at z
    rw [avail,pass_necessary ns hr run] at z
    exact closed c ns z r hr u run
  generalize hs : v.toFinset = s at h
  cases h with
  | stop =>
    have hp := List.perm_of_nodup_nodup_toFinset_eq nd (by simp : [target].Nodup)
      (by simpa using hs)
    have eq := List.perm_singleton.mp hp
    simp [eq] at stop
  | @unary r u U a pa fresh tail =>
    have av : a ∈ v := List.mem_toFinset.mp (hs ▸ Finset.mem_insert_self _ _)
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp av
    let n : Fin v.length := ⟨i,hi⟩
    let keep := decide (a ∈ U)
    let c := label 2 i i keep keep
    obtain ⟨ia,ib,op,ka,kb⟩ := label_ok (op := 2) (i := i) (j := i) (by decide) (by omega) keep keep
    have hg : gateOf v c = neg a := by simp only [gateOf,c,ia,ib,op,opValue,ite_true,read_mem hi,eq]
    have he : v.toFinset = insert v[n.val] (insert v[n.val] U) := by simpa [n,eq] using hs
    have hr : (after v c).toFinset = insert (neg a) U := by
      simp only [after,advancePins,List.toFinset_cons,hg,c,ia,ka,kb,ib]
      have hh := pins_set nd n n he
      simpa [n,eq,keep] using congrArg (insert (neg a)) hh
    have nn : (after v c).Nodup := by
      simp only [after,advancePins,List.nodup_cons,hg]
      exact ⟨fun h => fresh (hs ▸ List.mem_toFinset.mpr (select_sub h)),pins_nd nd _ _ _ _⟩
    have pg := live_proper tail _ (Finset.mem_insert_self _ _)
    apply reach c (fun _ scan => scan_unary scan n keep) (by omega) nn (hr.symm ▸ tail)
    simpa [gateAvailable,hg] using
      And.intro (And.intro (fun hz => fresh (hs ▸ List.mem_toFinset.mpr hz)) pg.1) pg.2
  | @binary r u U a b d pa pb ne fresh tail =>
    obtain ⟨ix,hix,ex⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp
      (hs ▸ Finset.mem_insert_self a (insert b U)))
    obtain ⟨jx,hjx,ey⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp
      (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b U)))
    have dispatch (i j : Fin v.length) (lt : j.val < i.val)
        (he : v.toFinset = insert v[i.val] (insert v[j.val] U))
        (fr : bin d v[i.val] v[j.val] ∉ v.toFinset)
        (tl : Live r t (insert (bin d v[i.val] v[j.val]) U)) : False := by
      have rr : opValue d.toNat v[i.val] v[j.val] ∉ v.toFinset := by rw [operationBin]; exact fr
      have tt : Live r t (insert (opValue d.toNat v[i.val] v[j.val]) U) := by rw [operationBin]; exact tl
      have child := binary_action nd width i j d.toNat (by cases d <;> decide) _ _ (pins_set nd i j he) rr tt
      obtain ⟨ns,run,avail⟩ := child
      exact reach _ (fun _ h => scan_binary h i j lt d.toNat (by cases d <;> simp) _ _) (by omega) ns run avail
    by_cases ge : jx < ix
    · refine dispatch ⟨ix,hix⟩ ⟨jx,hjx⟩ ge ?_ ?_ ?_
      · simpa [ex,ey] using hs
      · change bin d v[ix] v[jx] ∉ v.toFinset
        rw [ex,ey,hs]; exact fresh
      · simpa [ex,ey] using tail
    · have neq : ix ≠ jx := by rintro rfl; exact ne (ex.symm.trans ey)
      refine dispatch ⟨jx,hjx⟩ ⟨ix,hix⟩ (show ix < jx by omega) ?_ ?_ ?_
      · simpa [ex,ey,Finset.insert_comm] using hs
      · change bin d v[jx] v[ix] ∉ v.toFinset
        rw [ey,ex,bin_comm,hs]; exact fresh
      · change Live r t (insert (bin d v[jx] v[ix]) U)
        rw [ey,ex,bin_comm]; exact tail

def readTag (v : List Tagged) (j : Nat) := v.getD j (zero,0)

lemma readTag_ok (v : List Tagged) (j : Nat) : readTag v j ∈ v ∨ readTag v j = (zero,0) := by
  by_cases h : j < v.length
  · exact Or.inl ((read_mem h _).symm ▸ List.getElem_mem h : v.getD j (zero,0) ∈ v)
  · exact Or.inr (by simp [readTag,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : v.length ≤ j)])

def valuedMove (m : Sig) (d : Nat) (v : List Tagged) (code : Nat) :=
  let a := readTag v (digitA code)
  let b := readTag v (digitB code)
  advancePins (depsNext m d (digitOp code) a b) v code

lemma valued_shared {m} (f : MaskedFace m) {d v} (h : Shared f d v) (code : Nat) :
    Shared f (d+1) (valuedMove f.mask d v code) := by
  apply shared_sub f (shared_gate f h _ _ (readTag_ok _ _) (readTag_ok _ _) _)
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (select_sub hz)

lemma valued_map (m : Sig) (d : Nat) (v : List Tagged) (code : Nat) :
    (valuedMove m d v code).map Prod.fst = after (v.map Prod.fst) code := by
  simp only [valuedMove,advancePins,after,List.map_cons,select_map,gateOf,depsNext]
  have get (j : Nat) : (readTag v j).1 = (v.map Prod.fst).getD j zero := by
    simp only [readTag,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases v[j]? <;> rfl
  rw [get,get]

def runTags (m : Sig) : Nat → List Tagged → List Nat → List Tagged
  | _, v, [] => v
  | d, v, c::cs => runTags m (d+1) (valuedMove m d v c) cs

def runPins (base : List Sig) (tape : List Nat) := tape.foldl after base

lemma tags_run (m : Sig) (d : Nat) (v : List Tagged) (tape : List Nat) :
    (runTags m d v tape).map Prod.fst = runPins (v.map Prod.fst) tape := by
  induction tape generalizing d v with
  | nil => rfl
  | cons c cs ih =>
    simp only [runTags,ih,valued_map]
    rfl

lemma tags_shared {m} (f : MaskedFace m) {v d} (h : Shared f d v) (tape : List Nat) :
    Shared f (d+tape.length) (runTags f.mask d v tape) := by
  induction tape generalizing d v with
  | nil => exact h
  | cons c cs ih =>
    have H := ih (valued_shared f h c)
    simpa [runTags,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using H

def seedTags (base : List Sig) : List Tagged := base.map fun w => (w,0)

def baseLegal (m : Sig) (base : List Sig) := base.all (freeWire m)

lemma initial_shared {k} (f : MaskedFace k) {base} (h : baseLegal f.mask base = true) :
    Shared f 0 (seedTags base) := by
  intro mask
  refine ⟨0,_,Built.start,by simp [tally],?_⟩
  intro w hw _
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  exact freeWire_rep f (List.all_eq_true.mp h _ ha) Built.start

def track (m : Sig) (base : List Sig) (tape : List Nat) := runTags m 0 (seedTags base) tape

lemma track_map (m : Sig) (base : List Sig) (tape : List Nat) :
    (track m base tape).map Prod.fst = runPins base tape := by
  simpa [track,seedTags,List.map_map,Function.comp_def] using tags_run m 0 (seedTags base) tape

def rootBase (part : Bool) := if part then partialRaw else raw

def canUse (part : Bool) (j : Nat) :=
  !part || absent (familyCode j) 0 || absent (familyCode j) 1

def costMask (j : Nat) := faceMask (familyCode j)

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
lemma rootLegal : ∀ j : Fin 216, ∀ part : Bool, canUse part j.val = true →
    baseLegal (costMask j.val) (rootBase part) = true := by decide +kernel

lemma mask_family (j : Fin 216) : (familyFace j).mask = costMask j.val := by rfl

def priceMove (k d j c : Nat) (v : List Tagged) :=
  pricedCut (costMask j) k (familyModel j).limit (d+1) (valuedMove (costMask j) d v c)

theorem priceMove_sound {part : Bool} {j k tape c} (inRange : j < 216)
    (allowed : canUse part j = true)
    (nd : (after (runPins (rootBase part) tape) c).Nodup)
    (h : priceMove k tape.length j c (track (costMask j) (rootBase part) tape) = true) :
    NoSuffix k (after (runPins (rootBase part) tape) c).toFinset := by
  let f := familyFace ⟨j,inRange⟩
  have hm : f.mask = costMask j := mask_family _
  have shared := tags_shared f (initial_shared f (hm ▸ rootLegal ⟨j,inRange⟩ part allowed)) tape
  have sh : Shared f tape.length (track (costMask j) (rootBase part) tape) := by
    simpa [track,hm] using shared
  have hnext := valued_shared f sh c
  have mapped : (valuedMove f.mask tape.length (track (costMask j) (rootBase part) tape) c).map Prod.fst =
      after (runPins (rootBase part) tape) c := (valued_map _ _ _ _).trans (by rw [track_map])
  rw [← mapped]
  exact pricedCut_sound f hnext (mapped.symm ▸ nd) (by simpa only [hm,priceMove] using h)

def deadRot : Array Nat := #[0x876543210,0x267143850,0x374268501,0x364872105,0x846375012,0x247361058,0x567840123,0x176240583,0x547068321,0x146072385,0x74561238,0x64175832]
def deadInv : Array Nat := #[0,1,2,8,4,11,6,7,3,9,10,5]
def partialRot : Array Nat := #[0x876543210,0x374268501]
def partialInv : Array Nat := #[0,1]

def rotCount (part : Bool) := if part then 2 else 12

def rotCode (part : Bool) (r : Nat) := ((if part then partialRot else deadRot)[r]?).getD 0

def rotBack (part : Bool) (r : Nat) := ((if part then partialInv else deadInv)[r]?).getD 0

def permInput (code j : Nat) := (code >>> (4*j)) &&& 15

def rotatedPin (part : Bool) (r : Nat) (j : Fin 9) :=
  (rootBase part).getD (permInput (rotCode part r) j.val) zero

def rotBase (part : Bool) (r : Nat) := List.ofFn (rotatedPin part r)

set_option maxRecDepth 20000 in
lemma partialAgreement : ∀ j : Fin 9,
    bin false (neg firstSignal) (partialRaw.getD j.val zero) =
    bin false (neg firstSignal) (raw.getD j.val zero) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma rotData_ok : ∀ part : Bool, ∀ r : Fin 12, r.val < rotCount part →
    let a := rotatedPin part r.val
    graphValue a = target ∧ (part = true → bin false (a 0) (a 1) = zero) ∧
    (∀ j : Fin 9, permInput (rotCode part r.val) j.val < 9) ∧
    rotBack part r.val < rotCount part ∧
    (∀ j : Fin 9, permInput (rotCode part (rotBack part r.val)) (permInput (rotCode part r.val) j.val) = j.val) ∧
    (∀ j : Fin 9, permInput (rotCode part r.val) (permInput (rotCode part (rotBack part r.val)) j.val) = j.val) := by
  decide +kernel

lemma rot_finite {part r} (h : r < rotCount part) : r < 12 := by cases part <;> simp [rotCount] at h <;> omega

def chartRot (part : Bool) (r : Nat) := chartProj (rotatedPin part r)

set_option maxRecDepth 12000 in
lemma rot_basis (part : Bool) {r : Nat} (hr : r < rotCount part) (j : Fin 9) :
    (chartRot part r).project ((rootBase part).getD j.val zero) = rotatedPin part r j := by
  obtain ⟨he,hz,_,_,_,_⟩ := rotData_ok part ⟨r,rot_finite hr⟩ hr
  have eq := chartProj_raw he j
  cases part
  · exact eq
  · let p := chartRot true r
    have r0 : p.project raw0 = rotatedPin true r 0 := chartProj_raw he 0
    have r1 : p.project raw1 = rotatedPin true r 1 := chartProj_raw he 1
    have unit : p.project (neg firstSignal) = one := by
      rw [p.project_neg,firstSignal,p.project_bin,r0,r1,hz rfl,neg_laws.1]
    exact (maskReflect p unit _ _ (partialAgreement j)).trans eq

lemma baseOfFn (part : Bool) :
    List.ofFn (fun j : Fin 9 => (rootBase part).getD j.val zero) = rootBase part := by cases part <;> rfl

lemma rot_images {part r} (hr : r < rotCount part) :
    (rootBase part).map (chartRot part r).project = rotBase part r := by
  nth_rw 1 [← baseOfFn part]
  simp only [List.map_ofFn,Function.comp_def,rot_basis part hr,rotBase]

lemma inverse_images {part r} (hr : r < rotCount part) :
    (rotBase part r).map (chartRot part (rotBack part r)).project = rootBase part := by
  obtain ⟨_,_,bound,back,round,_⟩ := rotData_ok part ⟨r,rot_finite hr⟩ hr
  rw [rotBase,List.map_ofFn,← baseOfFn part]
  apply congrArg List.ofFn
  funext j
  change (chartRot part (rotBack part r)).project ((rootBase part).getD (permInput (rotCode part r) j.val) zero) = _
  rw [rot_basis part back ⟨_,bound j⟩]
  exact congrArg (fun n => (rootBase part).getD n zero) (round j)

lemma getD_proj (p : Projection) (v : List Sig) (j : Nat) :
    p.project (v.getD j zero) = (v.map p.project).getD j zero := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases v[j]? <;> simp [map_zero]

lemma after_proj (p : Projection) (v : List Sig) (c : Nat) :
    (after v c).map p.project = after (v.map p.project) c := by
  simp only [after,advancePins,List.map_cons,select_map,gateOf,opValue]
  split <;> simp only [p.project_neg,p.project_bin,getD_proj]

lemma tape_proj (p : Projection) (v : List Sig) (t : List Nat) :
    (runPins v t).map p.project = runPins (v.map p.project) t := by
  induction t generalizing v with
  | nil => rfl
  | cons c cs ih =>
    change (runPins (after v c) cs).map p.project = runPins (after (v.map p.project) c) cs
    rw [ih,after_proj]

lemma liftedNo {limit part r tape} (hr : r < rotCount part)
    (no : NoSuffix limit (runPins (rootBase part) tape).toFinset) :
    NoSuffix limit (runPins (rotBase part r) tape).toFinset := by
  let p := chartRot part r
  let j := chartRot part (rotBack part r)
  let v := runPins (rotBase part r) tape
  let w := runPins (rootBase part) tape
  have eq : v.map j.project = w := by rw [tape_proj,inverse_images hr]
  have inv : w.map p.project = v := by rw [tape_proj,rot_images hr]
  have transport {y z : List Sig} (j p : Projection) (eq : y.map j.project = z) (inv : z.map p.project = y)
      (hn : NoSuffix limit z.toFinset) : NoSuffix limit y.toFinset := by
    intro q hq t hh
    apply symmetry_excludes j p _ _ hn hq hh
    · intro a ha
      obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp ha)
      have both : (y.map j.project).map p.project = y := (congrArg (List.map p.project) eq).trans inv
      have val := congrArg (fun l : List Sig => l.getD i zero) both
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hi,
        Option.map_some,Option.getD_some] at val
      exact e ▸ val
    · rw [←eq]
      ext a
      simp [Finset.mem_image,List.mem_map]
  exact transport j p eq inv no

def removed (i j : Nat) (ka kb : Bool) : Nat :=
  if ka && kb then 0 else if i == j then 1 else if ka then 2 else if kb then 1 else 3

def remainderPins (a b : Sig) (mode : Nat) (v : List Sig) :=
  if mode = 0 then v else if mode = 1 then dropped [a] v else
    if mode = 2 then dropped [b] v else dropped [a,b] v

lemma selectPerm (v : List Sig) (nd : v.Nodup) (i j : Fin v.length) (ka kb : Bool) :
    (selectPins v i.val j.val ka kb).Perm (remainderPins v[i.val] v[j.val] (removed i.val j.val ka kb) v) := by
  let mode := removed i.val j.val ka kb
  have nod : (remainderPins v[i.val] v[j.val] mode v).Nodup := by
    unfold remainderPins
    split
    · exact nd
    split
    · exact nd.filter _
    split <;> exact nd.filter _
  apply List.perm_of_nodup_nodup_toFinset_eq (pins_nd nd _ _ _ _) nod
  ext w
  simp only [List.mem_toFinset,mem_select]
  have choose : (∃ h : Fin v.length, v[h.val] = w ∧ (h.val ≠ i.val ∨ ka = true) ∧
        (h.val ≠ j.val ∨ kb = true)) ↔
      w ∈ v ∧ (w ≠ v[i.val] ∨ ka = true) ∧ (w ≠ v[j.val] ∨ kb = true) := by
    constructor
    · rintro ⟨n,rfl,ha,hb⟩
      exact ⟨List.getElem_mem _,ha.imp_left (fun h e => h ((List.Nodup.getElem_inj_iff nd).mp e)),
        hb.imp_left (fun h e => h ((List.Nodup.getElem_inj_iff nd).mp e))⟩
    · rintro ⟨hm,h1,h2⟩
      obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp hm
      refine ⟨⟨n,hn⟩,eq,h1.imp_left (fun h hei => ?_),h2.imp_left (fun h hei => ?_)⟩
      · change n = i.val at hei; subst n; exact h eq.symm
      · change n = j.val at hei; subst n; exact h eq.symm
  rw [choose]
  by_cases eq : i.val = j.val
  · have ij : i = j := Fin.ext eq
    subst j
    cases ka <;> cases kb <;> simp [mode,remainderPins,removed,dropped,and_self]
  · cases ka <;> cases kb <;> simp [mode,remainderPins,removed,dropped,eq,and_assoc]

def numDrop (h : Nat) := if h = 0 then 0 else if h = 3 then 2 else 1

def restCov (c : Cov) (a b : B) (h : Nat) :=
  if h = 0 then c.1 else if h = 1 then takeOne c a else if h = 2 then takeOne c b else takeTwo c a b

lemma droppedSummary {v : List Sig} (nd : v.Nodup) (i j : Fin v.length) (ka kb d : Bool) :
    let mode := removed i.val j.val ka kb
    let rest := selectPins v i.val j.val ka kb
    v.length-numDrop mode = rest.length ∧
    restCov (coverage d v) (sep d v[i.val]) (sep d v[j.val]) mode = unionSep d rest := by
  let a := v[i.val]
  let b := v[j.val]
  let m := removed i.val j.val ka kb
  let rem := selectPins v i.val j.val ka kb
  have hp := selectPerm v nd i j ka kb
  have he : unionSep d rem = unionSep d (remainderPins a b m v) := by
    rw [← cov_union,← cov_union,cov_perm d hp]
  change v.length-numDrop m=rem.length ∧ restCov (coverage d v) (sep d a) (sep d b) m = unionSep d rem
  rw [he,show rem.length = (remainderPins a b m v).length from hp.length_eq]
  have ar := one_rest d nd (List.getElem_mem i.isLt : a ∈ v)
  have br := one_rest d nd (List.getElem_mem j.isLt : b ∈ v)
  by_cases eq : i.val = j.val
  · have ij : i = j := Fin.ext eq
    subst j
    cases ka <;> cases kb <;> simp [m,removed,numDrop,restCov,remainderPins] <;>
      first | exact ar | exact cov_union _ _
  · have ab : a ≠ b := fun h => eq ((List.Nodup.getElem_inj_iff nd).mp h)
    have both := two_rest d nd (List.getElem_mem i.isLt) (List.getElem_mem j.isLt) ab
    have E : (i.val == j.val) = false := by simp [eq]
    cases ka <;> cases kb <;> simp [m,removed,numDrop,restCov,remainderPins,E,eq] <;>
      first | exact ar | exact br | exact both | exact cov_union _ _

def quickPass (k n : Nat) (both up : Cov) (a b g : Sig) (i j : Nat) (ka kb : Bool) :=
  let m := removed i j ka kb
  let len := (n-numDrop m)+1
  if len > k+1 then false else
    let d := decide (len < k+1)
    let cov := if d then both else up
    (sep d g ||| restCov cov (sep d a) (sep d b) m) == top

lemma quickPass_ok {v : List Sig} (nd : v.Nodup) (i j : Fin v.length) (ka kb : Bool) (g : Sig) (k : Nat) :
    quickPass k v.length (coverage true v) (coverage false v) v[i.val] v[j.val] g i.val j.val ka kb =
      pass k (g :: selectPins v i.val j.val ka kb) := by
  let m := removed i.val j.val ka kb
  let n := (v.length-numDrop m)+1
  have len := (droppedSummary nd i j ka kb true).1
  have cov := (droppedSummary nd i j ka kb (decide (n<k+1))).2
  change (if n > k+1 then false else _) = _
  unfold pass
  simp only [List.length_cons,←len]
  change (if n > k+1 then false else _) = (decide (n ≤ k+1) && _)
  by_cases le : n ≤ k+1
  · simp only [Nat.not_lt_of_ge le,ite_false,le,decide_true,Bool.true_and,unionSep]
    congr 2
    have choice : (if decide (n<k+1) then coverage true v else coverage false v) = coverage (decide (n<k+1)) v := by
      cases decide (n<k+1) <;> rfl
    rw [choice]
    exact cov
  · simp [le,Nat.lt_of_not_ge le]

def quickNode (k : Nat) (v : List Sig) (close : Nat → Bool) : Bool :=
  let n := v.length
  let both := coverage true v
  let up := coverage false v
  let test := fun op i j a b ka kb =>
    let g := opValue op a b
    !(quickPass k n both up a b g i j ka kb && gateAvailable v g) || close (label op i j ka kb)
  !(v == [target]) && (List.range n).all (fun i =>
    let a := v.getD i zero
    test 2 i i a a false false && test 2 i i a a true true &&
    (List.range i).all fun j =>
      let b := v.getD j zero
      [0,1].all fun op => [false,true].all fun ka => [false,true].all fun kb => test op i j a b ka kb)

lemma quickNode_ok {k v close} (nd : v.Nodup) (width : v.length ≤ 16) (test : quickNode k v close = true) :
    nodeTest k v close = true := by
  obtain ⟨nstop,all⟩ := Bool.and_eq_true_iff.mp test
  apply Bool.and_eq_true_iff.mpr
  refine ⟨nstop,List.all_eq_true.mpr ?_⟩
  intro i hi
  obtain hi := List.mem_range.mp hi
  have x := List.all_eq_true.mp all i (List.mem_range.mpr hi)
  have gate {op j ka kb} (ho : op < 3) (hj : j < v.length) (h : (!(quickPass k v.length (coverage true v) (coverage false v)
      (v.getD i zero) (v.getD j zero) (opValue op (v.getD i zero) (v.getD j zero)) i j ka kb &&
      gateAvailable v (opValue op (v.getD i zero) (v.getD j zero))) || close (label op i j ka kb)) = true) :
      (!(gateAvailable v (gateOf v (label op i j ka kb)) && pass k (after v (label op i j ka kb))) ||
        close (label op i j ka kb)) = true := by
    have small : j < 16 := Nat.lt_of_lt_of_le hj width
    rw [read_mem hi,read_mem hj] at h
    rw [label_value ⟨i,hi⟩ ⟨j,hj⟩ ho small,label_after ⟨i,hi⟩ ⟨j,hj⟩ ho small]
    rw [quickPass_ok nd ⟨i,hi⟩ ⟨j,hj⟩] at h
    simpa only [Bool.and_comm] using h
  obtain ⟨⟨u0,u1⟩,pairs⟩ := (Bool.and_eq_true_iff.mp x).imp_left Bool.and_eq_true_iff.mp
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨gate (by decide) hi u0,gate (by decide) hi u1⟩,
    List.all_eq_true.mpr ?_⟩
  intro j hj
  have r := List.all_eq_true.mp pairs j hj
  have jv := Nat.lt_trans (List.mem_range.mp hj) hi
  apply List.all_eq_true.mpr
  intro op ho
  have small : op < 3 := by simp at ho; rcases ho with rfl | rfl <;> decide
  exact List.all_eq_true.mpr fun ka hk => List.all_eq_true.mpr fun kb hb =>
    gate small jv (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp r op ho) ka hk) kb hb)

def deadTapeChunk0 : Array Nat := #[0x0,0x9,0xd5009,0x1a10d5009,0x26d1a10d5009,0x40526d1a10d5009,0x3ec1a10d5009,0x6691a10d5009,0x62c1a10d5009,0x26d0d5009,0x3ec26d0d5009,0x59d26d0d5009,0x66959d26d0d5009,0x66926d0d5009,0x62c26d0d5009,0x64426d0d5009,0x65c26d0d5009,0x2600d5009,0x92600d5009,0x4872600d5009,0x6eb2600d5009,0x6c72600d5009,0x3e00d5009,0x4b63e00d5009,0x93e00d5009,0x6050093e00d5009,0x3ec0d5009,0x93ec0d5009,0x6f73ec0d5009,0x59d0d5009,0x63859d0d5009,0x56c0d5009]
def deadTapeChunk1 : Array Nat := #[0x956c0d5009,0x72756c0d5009,0x6c756c0d5009,0x62c0d5009,0x962c0d5009,0x1a1009,0x2601a1009,0x92601a1009,0x4872601a1009,0x7352601a1009,0x6eb2601a1009,0x6c72601a1009,0x3ec1a1009,0x93ec1a1009,0x59d3ec1a1009,0x5473ec1a1009,0x6f73ec1a1009,0x6c73ec1a1009,0x4d11a1009,0x4ac1a1009,0x94ac1a1009,0x6691a1009,0x6201a1009,0x96201a1009,0x5450096201a1009,0x62c1a1009,0x962c1a1009,0x194009,0x9194009,0x339009194009,0x31f009194009,0x339194009]
def deadTapeChunk2 : Array Nat := #[0x493339194009,0x31f194009,0x931f194009,0x6d331f194009,0x307194009,0x9307194009,0x487307194009,0x6c7307194009,0x308194009,0x487194009,0x9487194009,0x605009487194009,0x6c7487194009,0x488194009,0x4b8194009,0x6c7194009,0x96c7194009,0x5450096c7194009,0x6c8194009,0x6f8194009,0x710194009,0x26d009,0x3e026d009,0x4b63e026d009,0x93e026d009,0x3ec26d009,0x93ec26d009,0x6050093ec26d009,0x59d3ec26d009,0x5473ec26d009,0x4d126d009,0x4ac26d009]
def deadTapeChunk3 : Array Nat := #[0x58e4ac26d009,0x94ac26d009,0x254009,0x32a254009,0xd532a254009,0x932a254009,0x6eb32a254009,0x6f56eb32a254009,0x2416f56eb32a254009,0x6f732a254009,0x1816f732a254009,0x9254009,0x247009254009,0x487009254009,0x669009254009,0x607009254009,0x6c7009254009,0x6df009254009,0xc254009,0x248254009,0x4ac254009,0x5514ac254009,0x487254009,0x9487254009,0x488254009,0x669254009,0x6eb669254009,0x6d3669254009,0x607254009,0x9607254009,0x245009607254009,0x727607254009]
def deadTapeChunk4 : Array Nat := #[0x6c7607254009,0x608254009,0x6df254009,0x6ea6df254009,0x1816ea6df254009,0x96df254009,0x6ec254009,0x7916ec254009,0xc16ec254009,0x3c50c16ec254009,0x6050c16ec254009,0x6c7254009,0x96c7254009,0x5450096c7254009,0x6c8254009,0x728254009,0x260009,0x9260009,0x59d009260009,0x6eb009260009,0x188260009,0x4a0260009,0x488260009,0x59d260009,0x547260009,0x9547260009,0x548260009,0x590260009,0x6e0260009,0x7b56e0260009,0x6eb260009,0x96eb260009]
def deadTapeChunk5 : Array Nat := #[0x6c7260009,0x96c7260009,0x6c8260009,0x3d4009,0x4aa3d4009,0xd54aa3d4009,0x94aa3d4009,0x6eb4aa3d4009,0x6f56eb4aa3d4009,0x6f74aa3d4009,0x93d4009,0x2483d4009,0x3083d4009,0x6ec3d4009,0x3e0009,0x93e0009,0x59d0093e0009,0x61159d0093e0009,0x6050093e0009,0x6eb0093e0009,0x1883e0009,0x3083e0009,0x59d3e0009,0x5783e0009,0x5473e0009,0x95473e0009,0x6050095473e0009,0x5483e0009,0x6e03e0009,0x7b56e03e0009,0x6eb3e0009,0x96eb3e0009]
def deadTapeChunk6 : Array Nat := #[0x6c83e0009,0x4d1009,0x4a0009,0x5764a0009,0xd55764a0009,0x95764a0009,0x58e4a0009,0xd558e4a0009,0x958e4a0009,0x94a0009,0x3084a0009,0x4884a0009,0x4ac009,0x94ac009,0x2484ac009,0x4884ac009,0x4c4009,0x94c4009,0x2484c4009,0x3084c4009,0x620009,0x9620009,0x187009620009,0x307009620009,0xc620009,0x188620009,0x308620009,0xc8,0x90c8,0x2530090c8,0x49f2530090c8,0x4a949f2530090c8]
def deadTapeChunk7 : Array Nat := #[0x4ab2530090c8,0x32c0090c8,0x54732c0090c8,0x7b732c0090c8,0x78732c0090c8,0x4ac0090c8,0x5824ac0090c8,0x4b80090c8,0x94b80090c8,0xc10094b80090c8,0x3c50c10094b80090c8,0x7c34b80090c8,0x6690090c8,0x6380090c8,0x96380090c8,0xc10096380090c8,0x2450c10096380090c8,0x3c50c10096380090c8,0x7f36380090c8,0x7876380090c8,0x6f80090c8,0x96f80090c8,0xc10096f80090c8,0x3c50c10096f80090c8,0x2530c8,0x92530c8,0x3130092530c8,0x49f0092530c8,0x4a949f0092530c8,0x4ab0092530c8,0x3132530c8,0x93132530c8]
def deadTapeChunk8 : Array Nat := #[0x4ab3132530c8,0x4943132530c8,0x4883132530c8,0x6d43132530c8,0x6c83132530c8,0x7103132530c8,0x3142530c8,0x56b3142530c8,0x57556b3142530c8,0x55f3142530c8,0x5773142530c8,0x5473142530c8,0x79f3142530c8,0x7873142530c8,0x3082530c8,0x56b3082530c8,0x57556b3082530c8,0x5773082530c8,0x5473082530c8,0x7933082530c8,0x7873082530c8,0x49f2530c8,0x4a949f2530c8,0x18d4a949f2530c8,0xd518d4a949f2530c8,0x3144a949f2530c8,0x94a949f2530c8,0x3084a949f2530c8,0x6384a949f2530c8,0x49249f2530c8,0x6df49249f2530c8,0xc149f2530c8]
def deadTapeChunk9 : Array Nat := #[0x30849f2530c8,0x6f849f2530c8,0x4942530c8,0x79f4942530c8,0x7874942530c8,0x4ab2530c8,0x4b64ab2530c8,0x7034b64ab2530c8,0x94ab2530c8,0x3084ab2530c8,0x6e04ab2530c8,0x6d44ab2530c8,0x6f84ab2530c8,0x6c84ab2530c8,0x4882530c8,0x7934882530c8,0x7874882530c8,0x4b82530c8,0x94b82530c8,0x7c34b82530c8,0x7db4b82530c8,0x7874b82530c8,0x6d42530c8,0x96d42530c8,0x6050096d42530c8,0x6c82530c8,0x96c82530c8,0x2450096c82530c8,0x6f82530c8,0x7102530c8,0x2470c8,0x92470c8]
def deadTapeChunk10 : Array Nat := #[0x4b80092470c8,0x6f80092470c8,0x3072470c8,0x93072470c8,0x3c50093072470c8,0x4873072470c8,0x94873072470c8,0x3c50094873072470c8,0x6c74873072470c8,0x4883072470c8,0x7103072470c8,0x3082470c8,0x5533082470c8,0x5473082470c8,0x7933082470c8,0x7873082470c8,0x4b82470c8,0x94b82470c8,0xc64b82470c8,0x7934b82470c8,0x7874b82470c8,0x6c72470c8,0x96c72470c8,0x3070096c72470c8,0x5450096c72470c8,0x5460096c72470c8,0xc6c72470c8,0x24500c6c72470c8,0x60500c6c72470c8,0x3086c72470c8,0x6c82470c8,0x96c82470c8]
def deadTapeChunk11 : Array Nat := #[0x2450096c82470c8,0x6050096c82470c8,0x6f82470c8,0xc66f82470c8,0x2480c8,0x3d32480c8,0x5533d32480c8,0x5473d32480c8,0x7933d32480c8,0x7873d32480c8,0x3c72480c8,0x5533c72480c8,0x5473c72480c8,0x7933c72480c8,0x5532480c8,0x5472480c8,0x5842480c8,0x7932480c8,0x97932480c8,0x6050097932480c8,0x7872480c8,0x97872480c8,0x2450097872480c8,0x6050097872480c8,0x7c42480c8,0x7dc2480c8,0x3070c8,0x93070c8,0xc60093070c8,0x2470093070c8,0x4ab2470093070c8,0x3c50093070c8]
def deadTapeChunk12 : Array Nat := #[0x3ec3c50093070c8,0x59d3c50093070c8,0x62c3c50093070c8,0x6443c50093070c8,0x65c3c50093070c8,0x3c60093070c8,0x4870093070c8,0x4ac0093070c8,0x6690093070c8,0x6070093070c8,0x6c70093070c8,0x6ec0093070c8,0x7100093070c8,0x7280093070c8,0xc3070c8,0x48500c3070c8,0x49348500c3070c8,0x61348500c3070c8,0x6d348500c3070c8,0x55300c3070c8,0x6d300c3070c8,0x79300c3070c8,0x2483070c8,0x5532483070c8,0x5472483070c8,0x7932483070c8,0x7872483070c8,0x4ac3070c8,0x94ac3070c8,0x6c50094ac3070c8,0xc64ac3070c8,0x7b74ac3070c8]
def deadTapeChunk13 : Array Nat := #[0x7934ac3070c8,0x7874ac3070c8,0x4883070c8,0x94883070c8,0x1850094883070c8,0x4850094883070c8,0x7934883070c8,0x7874883070c8,0x6693070c8,0x6d36693070c8,0x6073070c8,0x96073070c8,0x90096073070c8,0x2450096073070c8,0x2460096073070c8,0x3d12460096073070c8,0x3c50096073070c8,0x3c60096073070c8,0x6c70096073070c8,0xc6073070c8,0x30500c6073070c8,0x48500c6073070c8,0x6c76073070c8,0x96c76073070c8,0x2450096c76073070c8,0x3c50096c76073070c8,0x6c86073070c8,0x6083070c8,0x96083070c8,0x3050096083070c8,0x4850096083070c8,0x7936083070c8]
def deadTapeChunk14 : Array Nat := #[0x7876083070c8,0x6ec3070c8,0x96ec3070c8,0xc66ec3070c8,0x6c73070c8,0x96c73070c8,0x90096c73070c8,0x2470096c73070c8,0x3c50096c73070c8,0x3c60096c73070c8,0x5513c60096c73070c8,0x6070096c73070c8,0xc6c73070c8,0x48500c6c73070c8,0x2486c73070c8,0x6086c73070c8,0x6c83070c8,0x96c83070c8,0x4850096c83070c8,0x6050096c83070c8,0x7103070c8,0x7283070c8,0x97283070c8,0xc67283070c8,0x3080c8,0x93080c8,0x4850093080c8,0x6134850093080c8,0x6d34850093080c8,0x6d30093080c8,0x7930093080c8,0x5783080c8]
def deadTapeChunk15 : Array Nat := #[0x5483080c8,0x7353080c8,0x6d33080c8,0x96d33080c8,0x7936d33080c8,0x7876d33080c8,0x6c73080c8,0x96c73080c8,0x3050096c73080c8,0x4850096c73080c8,0x7876c73080c8,0x6c83080c8,0x7933080c8,0x7b83080c8,0x7873080c8,0x97873080c8,0x4850097873080c8,0x7883080c8,0x7dc3080c8,0x7f43080c8,0x32c0c8,0x7dc32c0c8,0x4ac0c8,0x5824ac0c8,0x1925824ac0c8,0x1865824ac0c8,0x7c35824ac0c8,0x94ac0c8,0x6c50094ac0c8,0xc64ac0c8,0x3d30c64ac0c8,0x3c84ac0c8]
def deadTapeChunk16 : Array Nat := #[0x7c44ac0c8,0x4b80c8,0x94b80c8,0xc20094b80c8,0xc70094b80c8,0x3070094b80c8,0x7870094b80c8,0xc4b80c8,0x19100c4b80c8,0xc64b80c8,0x3130c64b80c8,0x90c64b80c8,0x4850090c64b80c8,0x7930c64b80c8,0xc84b80c8,0x3084b80c8,0x7b84b80c8,0xc17b84b80c8,0x1850c17b84b80c8,0xc50c17b84b80c8,0x4850c17b84b80c8,0x7884b80c8,0x6690c8,0x7046690c8,0x6070c8,0x96070c8,0x3070096070c8,0x6f80096070c8,0xc6070c8,0x3d300c6070c8,0x3086070c8,0x93086070c8]
def deadTapeChunk17 : Array Nat := #[0x3050093086070c8,0x4850093086070c8,0x7933086070c8,0x7873086070c8,0x6f86070c8,0x6080c8,0x96080c8,0x3c86080c8,0x7c46080c8,0x6380c8,0x96380c8,0xc66380c8,0x90c66380c8,0x3050090c66380c8,0x4850090c66380c8,0x7f30c66380c8,0x7930c66380c8,0xc86380c8,0x7f36380c8,0x7886380c8,0x6f80c8,0xc86f80c8,0x188,0x9188,0x187009188,0x4b8187009188,0x6df187009188,0x307009188,0x59d307009188,0x590307009188,0x313009188,0x31e313009188]
def deadTapeChunk18 : Array Nat := #[0x9313009188,0x4ab313009188,0x4b54ab313009188,0x4b7313009188,0x59d313009188,0x6d3313009188,0x320009188,0x547320009188,0xc1547320009188,0x7ab320009188,0x4b8009188,0x94b8009188,0xc34b8009188,0xc64b8009188,0x6134b8009188,0x6074b8009188,0x7934b8009188,0x59d009188,0x547009188,0x578009188,0x9578009188,0xc3578009188,0xc6578009188,0x6c7009188,0x6e0009188,0x96e0009188,0x6050096e0009188,0xc188,0x3df00c188,0x5773df00c188,0x5815773df00c188,0x5833df00c188]
def deadTapeChunk19 : Array Nat := #[0x79f3df00c188,0x3d300c188,0x5473d300c188,0x6073d300c188,0x58400c188,0xc158400c188,0x1850c158400c188,0x66900c188,0x61300c188,0x64261300c188,0x64400c188,0x79300c188,0x979300c188,0x188188,0x3df188188,0x5773df188188,0x5815773df188188,0x5533df188188,0x5833df188188,0x79f3df188188,0x7933df188188,0x3d3188188,0x5533d3188188,0x5473d3188188,0x7933d3188188,0x3c7188188,0x5473c7188188,0x7933c7188188,0x584188188,0x793188188,0x9793188188,0x787188188]
def deadTapeChunk20 : Array Nat := #[0x9787188188,0x605009787188188,0x313188,0x31e313188,0xd531e313188,0x18d0d531e313188,0x18131e313188,0x3eb18131e313188,0x4b731e313188,0x4914b731e313188,0x2424914b731e313188,0x6374914b731e313188,0x6356374914b731e313188,0x1816356374914b731e313188,0x62b4914b731e313188,0xc162b4914b731e313188,0x4924b731e313188,0x6f74b731e313188,0x6eb4b731e313188,0x4a031e313188,0x49431e313188,0x48731e313188,0x18248731e313188,0x6df48731e313188,0xc16df48731e313188,0x48831e313188,0x9313188,0x4ab009313188,0x4b54ab009313188,0x2414b54ab009313188,0x4b7009313188,0x1814b7009313188]
def deadTapeChunk21 : Array Nat := #[0x59d009313188,0x6d3009313188,0x188313188,0x577188313188,0x581577188313188,0x583188313188,0x553188313188,0x547188313188,0x79f188313188,0x793188313188,0x787188313188,0x4a0313188,0x55e4a0313188,0x3064a0313188,0x3d13064a0313188,0x1814a0313188,0x3c51814a0313188,0x6df1814a0313188,0x6c71814a0313188,0x3c64a0313188,0x7ab4a0313188,0x79f4a0313188,0x4ab313188,0x4b54ab313188,0x1944b54ab313188,0x3084b54ab313188,0x3013084b54ab313188,0x2414b54ab313188,0x4052414b54ab313188,0x2444b54ab313188,0x5452444b54ab313188,0x4d14b54ab313188]
def deadTapeChunk22 : Array Nat := #[0x4ac4b54ab313188,0x4a04b54ab313188,0x6384b54ab313188,0xc84ab313188,0x59d4ab313188,0x5604ab313188,0x5544ab313188,0x6ec4ab313188,0x7a96ec4ab313188,0x6df4ab313188,0x6e04ab313188,0x6d44ab313188,0x494313188,0x9494313188,0x6c5009494313188,0x607494313188,0x79f494313188,0x4b7313188,0x2484b7313188,0x2412484b7313188,0x1814b7313188,0x4d11814b7313188,0x1844b7313188,0x6051844b7313188,0x1884b7313188,0x59d4b7313188,0x5604b7313188,0x5544b7313188,0x6ec4b7313188,0x488313188,0x9488313188,0x485009488313188]
def deadTapeChunk23 : Array Nat := #[0x607488313188,0x793488313188,0x59d313188,0x554313188,0x65a554313188,0x9554313188,0x245009554313188,0x548313188,0x9548313188,0x485009548313188,0x590313188,0x9590313188,0x6e0313188,0x79e6e0313188,0x96e0313188,0x6050096e0313188,0x6d3313188,0x96d3313188,0xc6d3313188,0x3c500c6d3313188,0x1886d3313188,0x6d4313188,0x96d4313188,0x3c50096d4313188,0x6c8313188,0x96c8313188,0x4850096c8313188,0x320188,0x3d2320188,0x55f3d2320188,0x79f3d2320188,0xc1320188]
def deadTapeChunk24 : Array Nat := #[0x4870c1320188,0x5450c1320188,0x554320188,0x547320188,0x9547320188,0xc5009547320188,0xc2547320188,0x6050c2547320188,0xc6547320188,0x793547320188,0xc1793547320188,0x548320188,0x308188,0x9308188,0x485009308188,0x493485009308188,0x553485009308188,0x6d3485009308188,0x553009308188,0x613009308188,0x793009308188,0x553308188,0x613553308188,0x554308188,0x547308188,0x9547308188,0x485009547308188,0x613547308188,0x607547308188,0x793547308188,0x548308188,0x669308188]
def deadTapeChunk25 : Array Nat := #[0x613308188,0x65a613308188,0x9613308188,0x245009613308188,0x614308188,0x607308188,0x9607308188,0x245009607308188,0x485009607308188,0x608308188,0x65c308188,0x7ac308188,0x85d7ac308188,0x793308188,0x9793308188,0x794308188,0x788308188,0x4b8188,0x2484b8188,0x1812484b8188,0x6051812484b8188,0xc14b8188,0x59d0c14b8188,0x5450c14b8188,0x95450c14b8188,0x5470c14b8188,0xc44b8188,0x1910c44b8188,0x6111910c44b8188,0x6c50c44b8188,0xc84b8188,0x6694b8188]
def deadTapeChunk26 : Array Nat := #[0x6134b8188,0x6116134b8188,0x6126134b8188,0x96134b8188,0x2450096134b8188,0xc66134b8188,0x6144b8188,0x7ac4b8188,0x59d188,0x547188,0x576547188,0xd5576547188,0xd8576547188,0x3050d8576547188,0x554576547188,0x9576547188,0x548576547188,0x9547188,0x185009547188,0x186009547188,0x307009547188,0x546009547188,0xc547188,0x24500c547188,0x31324500c547188,0x3d300c547188,0x308547188,0x553308547188,0x9308547188,0x245009308547188,0x485009308547188,0x548188]
def deadTapeChunk27 : Array Nat := #[0x642548188,0x186642548188,0x9548188,0x245009548188,0x3c8548188,0x578188,0x9578188,0xc6578188,0x5530c6578188,0x90c6578188,0x2450090c6578188,0x4850090c6578188,0xc8578188,0x548578188,0x6e0188,0x7926e0188,0x1927926e0188,0x96e0188,0x6050096e0188,0xc66e0188,0x3d30c66e0188,0x90c66e0188,0x2450090c66e0188,0x6050090c66e0188,0xc86e0188,0x3c86e0188,0x6c7188,0x96c7188,0x90096c7188,0x90090096c7188,0xc0096c7188,0xc60096c7188]
def deadTapeChunk28 : Array Nat := #[0x1870096c7188,0x1880096c7188,0xc6c7188,0x18600c6c7188,0x31118600c6c7188,0x24700c6c7188,0x25300c6c7188,0x1886c7188,0x3d31886c7188,0x91886c7188,0x6050091886c7188,0x6c8188,0x96c8188,0x1860096c8188,0x3111860096c8188,0x2470096c8188,0x3c70096c8188,0xc6c8188,0x2486c8188,0x3c86c8188,0x248,0x9248,0x3c5009248,0x3ec3c5009248,0x93ec3c5009248,0x6050093ec3c5009248,0x5473ec3c5009248,0x4d13c5009248,0x4ac3c5009248,0x58e4ac3c5009248,0x94ac3c5009248,0x4ac009248]
def deadTapeChunk29 : Array Nat := #[0x94ac009248,0x6074ac009248,0x59d009248,0x56c009248,0x65a56c009248,0x956c009248,0x188248,0x313188248,0x547313188248,0x9188248,0x485009188248,0x493485009188248,0x613485009188248,0x6d3485009188248,0x553009188248,0x6d3009188248,0x793009188248,0x578188248,0x553188248,0x548188248,0x735188248,0x6d3188248,0x96d3188248,0x4850096d3188248,0x7936d3188248,0x7876d3188248,0x6c7188248,0x96c7188248,0x3050096c7188248,0x4850096c7188248,0x7876c7188248,0x6c8188248]
def deadTapeChunk30 : Array Nat := #[0x793188248,0x787188248,0x9787188248,0x485009787188248,0x605009787188248,0x788188248,0x7f4188248,0x4ac248,0xc84ac248,0x6694ac248,0x6134ac248,0x96134ac248,0x4850096134ac248,0xc66134ac248,0x6144ac248,0x7ac4ac248,0x59d248,0x56c248,0x65a56c248,0x19265a56c248,0x956c248,0xc656c248,0x5530c656c248,0x90c656c248,0x2450090c656c248,0x4850090c656c248,0xc856c248,0x54856c248,0x547248,0x9547248,0x247009547248,0x3c5009547248]
def deadTapeChunk31 : Array Nat := #[0x3c6009547248,0xc547248,0x48500c547248,0x31348500c547248,0x31300c547248,0x248547248,0x553248547248,0x9248547248,0x245009248547248,0x485009248547248,0x548248,0x9548248,0x485009548248,0x308548248,0x339,0x314,0x3ea314,0xd53ea314,0xd50d53ea314,0x4943ea314,0x94943ea314,0x2450094943ea314,0x79f4943ea314,0x4883ea314,0x94883ea314,0x6c50094883ea314,0x9314,0x703009314,0x9703009314,0x248314,0x9248314,0x553009248314]
def deadTapeChunk32 : Array Nat := #[0x7cf009248314,0x793009248314,0x553248314,0x9553248314,0x185009553248314,0x7cf553248314,0x548248314,0x7cf248314,0x793248314,0x9793248314,0x605009793248314,0x788248314,0x488314,0x9488314,0x185009488314,0x703185009488314,0x6d3185009488314,0x7cf009488314,0x793009488314,0x308488314,0x7cf488314,0x793488314,0x9793488314,0x605009793488314,0x788488314,0x703314,0x6c8314,0x96c8314,0x6050096c8314,0x3086c8314,0x5486c8314]
def deadTapeChunks : Array (Array Nat) := #[deadTapeChunk0,deadTapeChunk1,deadTapeChunk2,deadTapeChunk3,deadTapeChunk4,deadTapeChunk5,deadTapeChunk6,deadTapeChunk7,deadTapeChunk8,deadTapeChunk9,deadTapeChunk10,deadTapeChunk11,deadTapeChunk12,deadTapeChunk13,deadTapeChunk14,deadTapeChunk15,deadTapeChunk16,deadTapeChunk17,deadTapeChunk18,deadTapeChunk19,deadTapeChunk20,deadTapeChunk21,deadTapeChunk22,deadTapeChunk23,deadTapeChunk24,deadTapeChunk25,deadTapeChunk26,deadTapeChunk27,deadTapeChunk28,deadTapeChunk29,deadTapeChunk30,deadTapeChunk31,deadTapeChunk32]
def deadTape (n : Nat) : Nat := ((deadTapeChunks[n/32]?.getD #[])[n % 32]?).getD 0
def deadCashChunk0 : Array Nat := #[0x9e6f5c4f483128130c,0x9e6f5c48280c08,0x8b5c48280c08,0x8b48281b0c08,0x48280c,0x0,0x8,0x48280c,0x8,0x8b5c48280c08,0x48,0x5c48280c,0x0,0x280c,0x4,0x1b,0x48,0x8b48281b1301,0x4,0x45,0x8b08,0x0,0x8b48281b0c08,0x804,0x4,0x0,0x8b5c28130401,0x8,0x8b1b,0x8b5c4828130c,0x8,0x8b5c48281301]
def deadCashChunk1 : Array Nat := #[0x8,0x8b08,0x0,0x8b48281b1301,0x8,0x9e48281b0c08,0x8b48281b1301,0x2,0x0,0x2,0x8b08,0x27,0x9e5c13040201,0x8,0x8,0x8b,0x8b1b,0x0,0x9e5c4828130c,0x9e48281b1301,0x8,0x9e481b0c0802,0x8b48281b0c08,0x2,0x0,0x9e481b130201,0x8,0x8b48281b0c0806,0x8f741b0c02,0x2,0x4,0x8b48281b1301]
def deadCashChunk2 : Array Nat := #[0x45,0x482813,0x8,0x8,0x9748281301,0x1,0x48,0x28,0x602,0x8f48281b0c,0x1,0x1,0x6f,0x4806,0x80602,0x8b48281b0c08,0x1,0x1,0x2806,0x80602,0x1b0602,0x9e6f5c48280c08,0x8b5c280c0804,0x402,0x2,0x8b48281b1301,0x4,0x0,0x48,0x45,0x9e6f281b0c0804,0x9e48281b1301]
def deadCashChunk3 : Array Nat := #[0x1b04,0x4,0x8b5c48281301,0x48280c,0x2,0x4,0xa,0xa,0x0,0x1,0x0,0x8b60280c08,0x1,0x48,0x2,0x1,0x1,0x8,0x802,0x402,0x604802,0x4,0x8b5c28130401,0x1,0x1b02,0x8b5c48281301,0x8b08,0x27,0x8b5c48281301,0x1,0x1,0x8b04]
def deadCashChunk4 : Array Nat := #[0x74,0x4802,0x9e13,0x1,0x0,0x8b,0x402,0x4,0xa,0x1,0x1,0x8b60281301,0x1,0x1,0x9e02,0xba4802,0x9e48281b130a01,0xa04d1b0c04,0x4,0x8,0x402,0xa0402,0x480a,0x9e48281b1301,0x9e48281b1301,0x1,0xa04,0x1b0a04,0x280a04,0xa,0x9e4813,0x8b]
def deadCashChunk5 : Array Nat := #[0x9e481e1301,0x1,0xa04,0x8b5c281e0c0804,0x48280c,0x2,0x4,0x60,0x601e,0x1e01,0x8b5c281e0c0a,0x4802,0x802,0x1e0402,0x9e6048281b0c08,0xa5600c0402,0x4,0x0,0x600c,0x1b,0x4802,0x4808,0x9e48281b0c08,0x482d08,0x9e48281b0c08,0x1,0x1,0x4828,0x604828,0x60,0x9e5c0c,0x8b]
def deadCashChunk6 : Array Nat := #[0x6048,0x9e6f281b130c04,0x9e482a281b130c,0x9e48281301,0x4,0x8,0x9e48281b0c,0x4,0x1b,0x9e741b0c08,0x804,0x481b,0x9e6f2d281b130401,0xa56f60280c,0x804,0x9e1b,0x9e5c483e28130c,0xd3280c0a,0x5c04,0x9e08,0x9e481b0c0802,0x9e481e0c08,0x1,0x1,0x8b04,0x2804,0x804,0x8b5c48280c0803,0x9e5c48341301,0x483407,0x7,0x7]
def deadCashChunk7 : Array Nat := #[0x1,0x9048281b1a03,0x6547,0x8,0x9003,0x8f6360483401,0x4,0x998b5c340401,0x3,0x0,0x0,0x1b,0x8f5c48290c,0x8b5c4c48290c,0x3,0x0,0x0,0x0,0x8,0xbc03,0x9048291b0c08,0x3,0x0,0x0,0x8b48281b0c0807,0x48280c07,0x4,0x1,0x3,0x3,0x8b48281b1a13,0x3]
def deadCashChunk8 : Array Nat := #[0x60480c0802,0x6048,0xc04,0x8d,0x280c04,0x4,0x48341a,0x600c,0xc04,0x804,0xc04,0xc04,0x2b13,0x3404,0x48281a13,0xc,0xc,0x140e,0x5902,0xa02,0xc02,0x8b6348281d1b0c0805,0x8b636048281e0c0805,0x48280c07,0x0,0x0,0x4,0x48,0x0,0x63280c,0x0,0x48400c07]
def deadCashChunk9 : Array Nat := #[0x0,0x0,0x48341e,0x1b04,0x2704,0x8b63605c280c0803,0x481302,0x0,0x4,0x48,0x281b,0x6002,0x0,0x48,0x6348280c07,0x1e02,0x4502,0x8b5c28130704,0x2,0x60,0xa,0x2,0x48341b08,0xa18c,0x2,0x48281b0c0807,0x8d8c02,0x0,0x63482813,0x5c281a0c04,0x8b48281b0c0807,0x8b48281b0c0807]
def deadCashChunk10 : Array Nat := #[0x1f07,0x8f07,0x8b48281b1a0c08,0x8b453e1a,0x0,0x8b48280c,0x0,0x0,0x45270c,0x480c,0x9a,0x48281a13,0x4813,0x4f,0x2813,0x31,0x8b48281f1b0c0807,0x1f07,0x4f,0xb5,0x7,0x8b48281b0c08,0x48281f0c07,0x0,0x0,0x0,0xa3a12807,0x28,0x27,0x280c,0x48281b0c0807,0xa3a1]
def deadCashChunk11 : Array Nat := #[0x1,0x0,0x998b6348281301,0x31,0x9e48341b130701,0x48281a13,0x4513,0xc04,0x2713,0x3104,0x48281a0c,0x1b0c,0x4f,0x9e0c,0x63340704,0x63453401,0x7,0x9e481b0c0807,0xa104,0x0,0x9e481b0e0801,0xa3,0x1,0x0,0x7,0x7,0x8b5c48280c08,0x8b5c482816140c0803,0x903,0x8b453e1a,0x5c,0x8b5c4828160e0c08]
def deadCashChunk12 : Array Nat := #[0x48,0x1,0x0,0x0,0x0,0x9e5c1a,0x9e451a,0x604816,0x1,0x8b3e1a,0x453e1a,0x8d16,0x9716,0xba16,0x8b45281e1a140c09,0x281a0c,0x21,0x4f04,0x9128,0x1b16,0x451a,0x8b3b,0x48281a0c,0xc04,0x450c,0x9e0c,0x270c,0x8b6048281b160c08,0x6a16,0xc,0x480c,0x8d22]
def deadCashChunk13 : Array Nat := #[0x6a4827,0x4f16,0x8b5c280c04,0x251e0c,0xc,0xc,0x9e0c,0x270c,0x8b5c48280c08,0x31,0x8b5c48280c08,0x8b5c48280c08,0xf,0x0,0x0,0x0,0x0,0x0,0x0,0x584e4847160c,0xc04,0x480c,0x5c48280c,0x0,0x0,0x0,0x48281b0c,0x8b5c48280c,0x584e470c,0xc,0xc,0x4831]
def deadCashChunk14 : Array Nat := #[0x2b1b0c,0x8d8b48281b161301,0x9516,0x31,0x8b5c48280c08,0xb445281a0c,0x270c,0x0,0x0,0x0,0x0,0x0,0xa6a19428160c,0x280c,0x280c,0x281b0c04,0x9e481b0c,0xa6a1940c,0xc,0xc,0x978b5c281a0c0804,0xba8b5c4828161301,0xbe16,0x3e0f,0x9e5c48291a1301,0xc12e281a1403,0x281a,0x0,0x28,0x4516,0x8b3b,0x48160c]
def deadCashChunk15 : Array Nat := #[0xc,0xc03,0x8b5c482813,0x5208,0x4f27,0x271b13,0x8b5c48281303,0x584e,0x0,0x0,0x371b,0x1a0c,0x9e481b1301,0x160c,0x9e481b130301,0xa694,0x0,0x34,0x160e,0x160c,0x8b48281b1a0c0a0803,0xa03,0x8b636048281b0c0803,0xc648280c08,0x4807,0xc04,0x0,0x8f6360280c0403,0x63280c,0x6348280c,0x4808,0x6548]
def deadCashChunk16 : Array Nat := #[0x604803,0x8b5c281f0c080403,0x998b5c280c080704,0x0,0x27,0x1f03,0x1f03,0x1f1e08,0xc03,0x8b5c280c04,0x480c,0x1e16,0x0,0x8b0c,0xe,0x6548,0x3,0x8f03,0x2,0x0,0x0,0x99,0x8b5c48280c0803,0x80301,0x8b5c48280c08,0x8b5c48474645280c0803,0x916327,0x8f47,0x8b7c6346450803,0x4b13,0x8b5c482813,0x584e16]
def deadCashChunk17 : Array Nat := #[0x0,0x0,0x746808,0x2b22,0x9e8f5c4847130201,0x9e5c484729130c,0x8f716345290c,0xc04,0x47,0x8b5c4c48280c0803,0x8b5c592803,0x8b5c4d280c,0x4716,0x0,0x0,0x8b59,0x8b17,0x59,0xbc8b5c48281301,0xbc,0x8f8b5c48280c0803,0x34,0x9e48281b0c08,0x9e48281b0c0805,0x8b48281b1008,0x1f05,0x9e05,0x9e481b1307,0x1,0x3e05,0x48130501,0x1]
def deadCashChunk18 : Array Nat := #[0x4,0x14,0x14,0x1,0x4,0x5,0x9748281a0905,0x5,0x0,0x8b0805,0x9e5c1f1307040201,0x5,0x0,0x0,0x1f05,0xb59e05,0xb505,0x9e48281b0c08,0x9e481b0c0807,0x9e482d281b130501,0x5,0x0,0x0,0x9e481b0c0807,0xa048281b0c0807,0x5,0x0,0x9e481b0c0807,0x9e491c1a,0x5,0x5,0x501]
def deadCashChunk19 : Array Nat := #[0x805,0xa5481b1a10,0x4f1f,0x2d0e,0x50401,0x0,0x1,0x401,0x9e48371b0807,0x2707,0x2d050401,0x9e481b0c0807,0x0,0x8b48281b0c0807,0x48281a07,0x7,0x0,0x4508,0x0,0x802,0x2708,0x48281a13,0x4513,0x4f02,0x2713,0x48281a0c,0x450c,0x8b0c,0x7,0x9e481b0c0807,0x8b02,0x8b48281b0c0807]
def deadCashChunk20 : Array Nat := #[0xa3a1,0x0,0x9e48281b1413,0x8b48281b1a0c0905,0x1,0x0,0x482e0c,0x0,0x5c0c02,0x480c05,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0x1a,0x1b0c050402,0x0,0x0,0x0,0x7,0x4814,0x1,0x1,0x0,0x1,0x0]
def deadCashChunk21 : Array Nat := #[0x8,0x8,0x48281a13,0xc04,0xc04,0x600c,0x1702,0xc04,0xc09,0x1702,0x2a13,0x8b5c281d181304,0x6,0x1,0x1,0x1b1a01,0x1d10,0x0,0x0,0x1d,0x60,0x1d08,0x9e605c281413,0x9e6048281f140c05,0x4f,0x0,0x0,0x99480c07,0x0,0x0,0x0,0x14]
def deadCashChunk22 : Array Nat := #[0x2,0xc,0x28,0x4f,0x14,0x1b0802,0xc,0x28,0x0,0x5c13,0x1b08,0x1b0c,0x9e5c130402,0x611c,0x4,0x7408,0x4d1b,0x9e48281f1b140c05,0x0,0x0,0x99480c07,0x0,0x0,0x0,0x4f,0x1,0x2,0x1b17,0x28,0x9e5c130402,0x251c,0x4]
def deadCashChunk23 : Array Nat := #[0xad04,0x1b17,0x9e482813,0x9e5c482813,0x6002,0x2c27,0x4,0x9e48281b13,0x3927,0x4,0x9e5c28181304,0x4,0x8b48281b1813,0x402,0x4,0x4,0x9e481b141302,0x90,0x8d8c0805,0x0,0x2808,0x9e481b1302,0x8d8c04,0x0,0x9e481b1302,0x948c,0x4,0x8b48281b1a0c090805,0x48281a05,0x4a,0x2,0x8b492e1b0c06]
def deadCashChunk24 : Array Nat := #[0x6b2e,0x8b492e1b0c,0x6148,0x8b5c2813050401,0x5,0x0,0x0,0x0,0x4f,0x0,0x0,0x907,0x9e48281b1a0c08,0x90483e1a1408,0x481a,0x48,0x2,0x0,0x5a1b,0x271a,0x8b18,0x9e5c1302,0x5c0e,0x4813,0x8b5c281301,0x6525,0x0,0x4f28,0x9146,0x8b4f,0x480c,0x1301]
def deadCashChunk25 : Array Nat := #[0x9e48281b13,0x2202,0x3708,0xc,0x280c,0x9e5c482813,0x392f,0x0,0x0,0xc02,0x180c,0x28180c,0xe,0x9e481b1302,0x8b13,0x13,0xc,0x9e48281f1b0c0805,0x1f,0x2,0x0,0x9948280c07,0x28,0x99482c0c07,0x5,0xd737,0x0,0x4f,0x4f,0x5,0x4f,0x801]
def deadCashChunk26 : Array Nat := #[0x9e482c281f1b0c08,0x9e281f05,0x8b1f02,0x2c1f,0x0,0xa94528,0x2c02,0xa02807,0x9e48281b0c08,0x9e48281b0c08,0x9e482d281b0c08,0x27,0x2c2a2827,0x802,0x482808,0x2808,0x8b2e1f,0x9e482c2a28271b0c08,0x9e482c291b0c08,0x9e5c2c13,0x8b5c37,0x5,0x9e48372a28271b0805,0x9e483702,0xc09,0x3708,0x9e5c482813,0x7413,0x392f2818,0x2,0x28,0x9e482c281b0c08]
def deadCashChunk27 : Array Nat := #[0x9e5c482d281305,0x1302,0x9e48372a271b08,0x9e4837,0x280c,0x9e482d281b0c0805,0xad48281b05,0xa548281b0c,0xad1b02,0x2c18,0x0,0x0,0x3802,0xb58b,0xa08b48281b0c0807,0x48280c07,0x28,0xa0481b0c080502,0xa0481b0c08,0xa09948280c,0x2808,0x2807,0x28,0x27,0xa028,0xa628,0x9e481b0c0802,0x9e481b0c0802,0x9e9890480c07,0x0,0x8d8c05,0x8d]
def deadCashChunk28 : Array Nat := #[0x48281f0c07,0x2,0x9e8d8c481b0c080502,0x0,0x0,0x7,0x28,0x48281b0c08,0x2813,0xa3a107,0x0,0x9e481b0c080702,0x9e8d8c481b0c080502,0x0,0x0,0xa38c,0x90,0x8d8c05,0x28,0xc,0x9e6f5c4828140c08,0x9e6f5c48281401,0x9e6f5c482814,0x8b482814,0x0,0x0,0x45,0x9e6f2814,0x9e48281b14,0x4,0x0,0x8b6048281401]
def deadCashChunk29 : Array Nat := #[0x14,0x8658,0x9e6f60281401,0x9e482a281b1401,0x4,0x14,0x8b5c48281a140c,0x48281a0c,0x4f02,0x8b45281e1a0c09,0x281a0c,0x21,0x4f,0x91,0x1b16,0x4516,0x8b16,0x48160c,0x8b5c280c04,0xc,0x140c,0x8b5c48280c,0x5802,0xd,0x4f27,0x6802,0x8b5c4828140c,0x4e470c,0xc,0xc,0x2a1b0c,0xc04]
def deadCashChunk30 : Array Nat := #[0x8b48281b0c,0x8b48281b140c,0xa6a10c,0xc,0xc,0x280c,0x160c,0x9e6048281b140c08,0x60480c,0x48140c,0x9e604839281b0c08,0x604839,0x48,0x8b710c,0x48390c,0x60483114,0x9e6f281b140c0804,0x9e482a281b140c08,0x9e8648281b0c08,0x4017,0x9e741b140c,0x9e741b1301,0x5c33,0x3918,0x0,0x0,0x2b0c,0x864f,0x9e6f281b0c0804,0x9e6f392d28271b140c0804,0x8b5c3b,0x9e6f39281b140c0804]
def deadCashChunk31 : Array Nat := #[0x8b483b1b,0x9e6f3b2d271b140c04,0x9e6f3b0c,0xf02,0x3b04,0x9e48281b0c,0x8b3404,0x2f2c180c,0xc,0xc,0x9e6f39281b140c04,0x9e6f3b2d271b0c04,0x9e6f3b0c,0xc02,0x8b4f311b130c0402,0x8b4f281b130d0c04,0x8b48281b130f0d0c,0x483413,0x2,0x8b483413,0x2321,0x2,0x341b04,0x8b5c28170c,0x6a21,0x2,0x9e4f341b1304,0x9e4f130e,0x2,0x9e48341b1311,0x977e1a0f060402,0x1b12]
def deadCashChunk32 : Array Nat := #[0x110f,0x8b36,0x8b48341b13,0x2304,0x0,0x8b0401,0x4801,0x9e481b130e,0x9e481b130c,0xab04,0x0,0x2808,0x9e5c48342313,0x8b5c44211d1304,0x4f4413,0x2,0x28,0x2321,0x8b44,0x480c,0x9e5c130e04,0x9e5c130c04,0xac1b,0x1,0x34,0x918b4f281b130d0c04,0xab9e4f1b130e04,0xafa091604f0e,0xaf4f0c,0x2808,0x34]
def deadCashChunks : Array (Array Nat) := #[deadCashChunk0,deadCashChunk1,deadCashChunk2,deadCashChunk3,deadCashChunk4,deadCashChunk5,deadCashChunk6,deadCashChunk7,deadCashChunk8,deadCashChunk9,deadCashChunk10,deadCashChunk11,deadCashChunk12,deadCashChunk13,deadCashChunk14,deadCashChunk15,deadCashChunk16,deadCashChunk17,deadCashChunk18,deadCashChunk19,deadCashChunk20,deadCashChunk21,deadCashChunk22,deadCashChunk23,deadCashChunk24,deadCashChunk25,deadCashChunk26,deadCashChunk27,deadCashChunk28,deadCashChunk29,deadCashChunk30,deadCashChunk31,deadCashChunk32]
def deadCash (n : Nat) : Nat := ((deadCashChunks[n/32]?.getD #[])[n % 32]?).getD 0
def deadLinkChunk0 : Array Nat := #[0x166683efa65b0db66433ef86370db862b236b61f394361323626073ee459c3efc56b3ef55533ef45473ee34d03ef64c33efb4ab3ef949f3ef348700144043ef23f723683eb39443df23633d30db23c73ee13383ef731f3ef1313001726c0db725f2367253394124700151a00db5193236118700130d40db10c70011008,0x2526680c2265b03b2643090262b0d4161f0ae26130c1259c0cc256b0d025530c114d00d014c30cc14ab0c2149f002240406223eb0ae13df0a313d3055126c090125f062125302511a003b119300210d4,0x9366801f365b0113643023162b01a361f01d159c01f156b003340401a13eb01613df009126c011125f00311a0,0x716680085643008162b004440400613eb004126c,0x576680051404,0x0,0x0,0x534d00057338,0x0,0xd1668010165b00f164300e162b00b159c007340400a13eb004126c,0x0,0xc1668,0x0,0xc166800524d00057338,0x0,0x0,0x0,0xf373401416ea01516c600844d001314860121008,0x0,0x0,0x0,0x0,0xa373401736ea01336c601714b500a133801313060181008,0x0,0x191604,0x0,0xe3734014370e01c16f601536c601714a9006126c013124601b1008,0x0,0x0,0xb366801e163700b1338,0x0,0x103734021172602216c60201008]
def deadLinkChunk1 : Array Nat := #[0x0,0x0,0x0,0x1c36e901e1668022160600834d001c14b60153486008126c01512460241008,0x0,0x3516680395643039162b036161f03214d003354c303314ab009440402c13eb02653df009726c026125f00311a0,0x29173402a16ea02b16c600e44d002814860271008,0x0,0x0,0x0,0x0,0x0,0x292734030570e03016f603116c602e159c02f1546006126c028124602d1008,0x0,0x0,0x0,0x0,0x0,0xb44d002e14b700b7338,0x1044d002f14860341008,0x0,0x724d002924b702954ab007b338029132b007126c,0xa44d002a54aa02b548600a733802a132a02b13060371008,0x381544,0x0,0xf44d003014b60311486008126c02b124603a1008,0x0,0x396734054170f05316f705216c704f16c601144d004e14b704d1487049148603f1338041131e0481307044130603c1008,0x3a673401244d003d133803e131e,0x0,0x0,0xf873404076d200f24d0040149203d10d4]
def deadLinkChunk2 : Array Nat := #[0x0,0x30673404316d201444d003e10d40421008,0x0,0x0,0x31273404716c601544d004614860451008,0x0,0x0,0x0,0x0,0x2b673404c16c60401338046130604a1008,0x4b1604,0x0,0x0,0x0,0x4610c4,0x1344d004c14860407338043131e04713060501008,0x511544,0x0,0x0,0x4710c4,0x4c10c4,0x9866805f265b03f2643056762b059261f05e259c05f755f05e14d005f84c305f14ab009240405913eb05613df009726c03f125f00911a0,0xe873405726ea04026c605714b500e733804013060581008,0x0,0x0,0xa873405786f604086c605c159c05d154605714a900a126c040124605a1008,0x5b1604,0x0,0x0,0x0,0xb24d005c14b700b7338,0x60158d01024d005d14860611008]
def deadLinkChunk3 : Array Nat := #[0x0,0x0,0x2c273408f172704e270f08616eb08216de08e16c708b16c60791668081160707c160601a24d007414ab078148707614860631329026126c041125e07312470441246072100b06b1008,0x30273406916f606616ea01c24d006410d40651008,0x0,0x0,0x6716f4,0x681240,0x0,0x6716f406a1180,0x681628,0x2d273407116de07016c606e166806f160601b24d006d14860641329027126c042125e06c1246,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x75155004610c4,0x0,0x28273407526de04626c607514a9028126c04612460771008,0x0,0x0,0x2e273407a16ea07b16d206e10d4,0x0,0x0,0x2f273407f172608016c607d1008,0x7e1244,0x0,0x0]
def deadLinkChunk4 : Array Nat := #[0x0,0x0,0x8316e907a166801724d00752492066132902a126c043124607110d40851008,0x6713f40841180,0x681328,0x0,0x8317a8087179006913f4043124404710c408810c0,0x0,0x8416dc08a160408913c406a1328,0x0,0x0,0x8716e907b1668080160601324d0046248602b126c047124608c1008,0x8d1544,0x0,0x0,0x7f16d008010c4,0x392734053270f09e16ea09c16df0a216c70a016c6097159c09b158f09a1547098154602324d0095149f096148708b2486063131d01111a0094118704411860911008,0x3a273409316ea092159c02424d0065131d01211a0,0x0,0x0,0x0,0x4610c4,0x0,0x1e259c07b255209210d4,0x2224d008024860991008,0x0,0x0,0x8020c4,0x9d17b406613e804710c4,0x6713f4,0x9d16e901c44d008724920691329014126c09310d409f1008,0x0]
def deadLinkChunk5 : Array Nat := #[0x1524d0047248601511a004711860a11008,0x0,0x0,0x26673409526f70ad16eb0a426de0ab26c704926c60a414a90561338095132b0ac13070761306026526c0ab124704912460aa1008,0x2a67340a916f60a716ea057140407513d20a510d40a61008,0x0,0x0,0xa816f4,0x0,0xa816f4,0x2767340a526de0a514a90581338027526c,0x0,0x0,0xa927a80a9157404c10c4,0x36273409c26f70be16ea0bc16df0c016c704f26c60b6159c0b715770bb15470b8154608224b50a4149d0591338074131f0b5130708b230601611a00b4118704911860af1008,0x3727340b316ea0b216040b0159c08524b50a6149d05a133801811a0,0xb11610,0x0,0x3826680b1159c05b133801911a0,0x0,0x0,0x0,0x7a258105c140407b23d20b010d4,0x8020c4,0x5d133808023060b91008,0xba1604,0x0,0x0,0xbd17b40a7156804c10c4,0xa81574,0x9d26f50bd16e908324b50a914a905783380872312017326c0b310d40bf1008,0x0]
def deadLinkChunk6 : Array Nat := #[0x0,0x1d24d007924b70b614ab05e1338097132b032126c,0xc6158d0c3157501f44d008f24b70cb14870b8148605f13380ca130709813060c91008,0x21259c07f25460c410d40c51008,0x0,0x0,0x60140407f23c60c710d40c81008,0x0,0x0,0xc7158d0c4157502044d00611338,0x0,0x0,0xc3156901f24d00b714ab0cf148707c2486033126c0ce124709812460cd1008,0xc5156902024d0034126c,0x0,0x0,0xc6156905f833809b132b0d3130707c2306033526c0d212470b812460d11008,0xc815690618338034526c,0x0,0x0,0x9e26f50be26dd01a44d008624b70be14aa0ad149f0d9248704f2486056733809e132a086131f0da13070a0130601a31a00d9118704f11860d8100b0d51008,0x9f26f50bf26dd01b44d00bf14aa0d62486058733809f132a0d7130601b31a00d61186,0x0,0x0,0x0,0x0,0x0,0x90673422937271f4370f23416f720136eb1d836c717a36c6216166822916372251607218160603b44d020114b71f614ab0f8349e164348713e348609073381f4132b1d8130717a130603b526c0f81252164124713e12460dc1008,0x9167340ed37270e1370f0f416f70e736eb0ec16680ed163703c44d00e714b70e514ab0dd349e09173380e1132b03c526c0dd1252,0x93673403e44d00e014aa0de149e0657338,0xdf14a8,0x0]
def deadLinkChunk7 : Array Nat := #[0xdf14a8,0xe317b60e417860e21546,0x0,0x0,0x0,0xe637b60e237860e615810e035680e213c60e0131c,0x0,0xe337da0eb17c20e437860e615750e213060e81008,0xe910c0,0xea13c4,0x0,0x0,0x9267340927404,0xf217f20f317860ee1008,0xef10c0,0xf113c40f01244,0x0,0x0,0x0,0x0,0xeb37b50f316c60eb15820e435460e413060f51008,0xf610c0,0xf735440f713c4,0x0,0x9e673413d170f13c16f713616d313916c704144d013114b712514aa115149e122149312e1487063733810613130fe131210e13070dd10d40f91008,0x9f673404244d00fd14aa0fb149e06473380fa1312,0x0,0xfc14a8,0x0,0xfc14a8,0x87b734105170f10316d310416c704344d010014aa101149310214870fa10d40ff1008,0x0]
def deadLinkChunk8 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x10c179e10d178610a1576107156a109155e10b1546,0x1081574,0x0,0x0,0x1081574,0x0,0x0,0x0,0x11317921141786111157610f156a1121546,0x1101574,0x0,0x1101574,0x0,0x0,0x0,0x69673412116f710736df12036d310f36c711614a811d14910697338107131f10f1313120130711d32450de11a00fb10d411f10c00fb3008,0x67666811c1637108362b119361f110361311b36070677338108132b110131f119131311b13070df126c0fc11a0117118c0fc30d411a1008,0x68659c068726c11810d4,0x0,0x0,0x118118c,0x0,0x0,0x11e16de,0x0,0x6a666811713dc06a726c]
def deadLinkChunk9 : Array Nat := #[0x119157411e3310,0x11c1574,0x123179e124178610913de10b13c6,0x0,0x0,0x9d673412c16f712a16df12b16d312d16c712614b511614a8066733810a131f100131e111131312913070e011a00fd10d41281008,0x1271702,0x0,0x11a14a8,0x11b1574,0x1083574,0x1193574,0x127158011c1574,0x11b3574,0x12f1792130178611d156810113de11213c6,0x11e1568,0x0,0x13417da13317c21351786126157410b118611210c61321008,0x0,0x1271580,0x0,0x0,0x12a1576107356a123155e124154610c13de10d13c61371008,0x1381604,0x0,0x12b1576120356a12f1552130154610313de11313d211413c613a1008,0x13b1244,0x0,0x133158212c1576121156a135154610d118611410c60eb8008,0x134158110513de13513c6124118613010c60e36008,0xa06734162570f16216f715e16c715516c604444d015014b714b54871424486044733814b1307142130613f1008,0xa16734141570f14116f704544d014014b70457338]
def deadLinkChunk10 : Array Nat := #[0x0,0x0,0x47b73414a170f14976c714576c604744d0149148714514861431008,0x14413c4,0x0,0x14816c61461008,0x147560414713c4,0x0,0x0,0x0,0x14810c4,0x14e179214f178614c155214d1546,0x0,0x0,0x0,0x0,0x135a7da13587c21531792154178614010d414d10c615210c514510c41511008,0x0,0x0,0x14810c4,0x14810c4,0x4644d015314b715d54871453486046733815d1307145730615a100b1561008,0x1591545158154415754861571306,0x0,0x0,0x0,0x15c160415b1244,0x0,0x0,0x0,0x14e555214f554614e13d214f13c615f1008,0x16116041601244]
def deadLinkChunk11 : Array Nat := #[0x0,0x0,0x135858214a4552154154614110d414f10c616310c514570c40e4b008,0x0,0xa2680017917db17817c317117921741786048459c1701583122356a16e155216f1546094740416513d216a13c6,0x16817921691786123356a16615521671546,0x0,0x0,0x0,0x0,0x16d1792163b786124356a16b155216c1546,0x0,0x0,0x0,0x167379216b378616b13d216713c6,0x166379216c378616613d216c13c6,0x167118416c10c4,0x109356a166355216b354616d13d216913c61721008,0x1731604,0x0,0x10b356a167355216c354616813d2163b3c61751008,0x17716041761244,0x0,0x0,0x1691184163b0c4,0x16b318416c30c4,0x8bb7341d517271d4170f1c116eb1d016c71c416c61a816681bb16071aa160604f44d019b14ab1a214871553486049526c0fe12521961247142124618e100b17b1008,0x8cb73418d172718c170f18b16eb18a16c61881668189160605044d018714ab186148618513c517f13c404a526c0ff125217d124617c10c5,0x0,0x17e14aa,0x0,0x8db668184165b1831643182162b181159c051440418013eb04b526c]
def deadLinkChunk12 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x180149017e1310,0x1811490,0x0,0x0,0x1821490,0x1831490,0x1841490,0x195179219416d2193155218f1484,0x19216d219116121901492,0x0,0x0,0x0,0x1901490,0x1911490,0x1921490,0x199179219a178619715521981546,0x0,0x0,0x0,0x0,0x19f17b61a017921a11786100131c18710d419810c619e10c514510c419c1008,0x19d16c4,0x0,0x0,0x0]
def deadLinkChunk13 : Array Nat := #[0x14810c4,0x14810c4,0x1a617921a71786102131e1971312198130619310d41a31008,0x1a514841a41184,0x0,0x0,0x0,0x0,0x7bb7341a916d218810d4,0x0,0x80b7341ba16c71b616c61b3100b1ab1008,0x1b216c61b113c51b013c41ae12451ad12441ac1008,0x0,0x0,0x1af13d0,0x0,0x0,0x1af1310,0x0,0x1b514841b41304,0x0,0x0,0x1b71008,0x1b935441b834841b913c41b81244,0x0,0x0,0x0,0x1bf17921c0178619410d41bc1008,0x1be14841bd1304,0x0,0x0,0x0]
def deadLinkChunk14 : Array Nat := #[0x0,0x19f157615335521a1154618b10d419a10c61c310c514570c41c21008,0x0,0x0,0x1a916681cf16071b6160604c44d01a014ab1ce3487145248604c526c1ce124714572461cc100b1c51008,0x1cb16061c935451c835441c734861c913c51c813c41c712461c61008,0x0,0x0,0x0,0x1ca1550,0x0,0x0,0x1cd36041cd1484,0x0,0x0,0x0,0x1bf16d21c016c61a615521a71546104131e199131219a130619510d41d11008,0x1d316041d21484,0x0,0x0,0x105131e14a13121a1130618c10d41a710c616c60c514520c40e26008,0x18d10d41c010c61d710c51b610c41d61008,0x0,0x0,0x9668001f317f31f217db1ed17b71ec17921f117871ee17861e117341e216d21eb16c71e616c6052459c1df1577136356a17135521e01547174354604d5338106131e165131216a13061d91008,0x1de17921dd16d2137356a17235521da1484,0x1dc16d21db161213834aa1733492,0x0,0x0,0x1db1490,0x1dc1490,0x12a363410a13e8166118416c10c4]
def deadLinkChunk15 : Array Nat := #[0x0,0x0,0x1e417921e517861dd10d41e31008,0x0,0x0,0x0,0x1e537921ea17861e71008,0x1e914841e81304,0x0,0x0,0x0,0x0,0x1e536d21e516c610c356a168355216d354610c131e16d131216813061de10d41de3008,0x1681184163b0c4,0x1e416d21ea16c610d356a1693552163854610d131e1691312163b3061ef1008,0x1f036041f01484,0x0,0x0,0x16d318416380c4,0x1e511841ea10c4,0x53b8001f517db13dc7b61f237931d43792179c787162b786053459c13d356a179355316245521f2c5471d4c5460e110d416a10c616a70c514210c40e17008,0x14a119014a318414aa0c4,0x9c680020017c31f737b61df379319b37921ff37871d4a7861f71581125356809c74041df13d319b13d21ff13c71d4c3c6125131c0e510d416f10c61fd10c514240c41fb1008,0x12c87ce1fa17c219f379e105a79212613e80e611a01f811911f91185,0x0,0x0,0x11c87cc,0x19c37921fc16c4128356819c13d2128131c,0x19d36d219d13d2,0x1f837b61fe379219e37861f815811fe13d219e13c6,0x0,0x12d363412913e81fe119019e1184]
def deadLinkChunk16 : Array Nat := #[0x12cb88012c864c12c363412c13e814a41901a0118414aa0c4,0x95680013da7da13c87c221017b71ed37931c13792215178716287861f7157504e5338131131e1701313150131220f13071d4c3060e710d420e10c717430c620910c515530c4207100b2021008,0x1c237922061786132131e151131220513060e810d420410c620310c1,0x0,0x0,0x0,0x0,0x2081190,0x0,0x130a7da11487c220d17921c337861f9157520a1312152130620810d420b1008,0x0,0x20c1484,0x0,0x0,0x0,0x20a11901521184,0x121888c1fa1640105a604105c3d01533190153118414aa0c421110c0,0x214360421414842123244212118421310c4,0x0,0x0,0x0,0x20d11901c33184,0x97673421717031e136d31a836d209774041e113d31a813d20ec10d4,0x1a91184,0x98673422416f721e36c71aa36c6098733821e13071aa130621c100b2191008,0x99673421b16f721a36c6099733821a1306,0x0,0x0,0x21d379221d13d2,0x0,0x2221792223178621d10d421f1008,0x22114842201304]
def deadLinkChunk17 : Array Nat := #[0x0,0x0,0x0,0x0,0x21b10d422310c61ea80c51b610c40f38008,0x9a680022817c31e2379222737871e6378609a74041e213d222713c71e613c62261008,0x1e337921e313d2,0x0,0x1e411841ea10c4,0x9b680023217f21f337931d53792233178722487860ed10d423110c71e610c622b10c51aa10c422a1008,0x1d637920ee10d4,0x22f17f223017921d7378622c1008,0x22e148422d1304,0x0,0x0,0x0,0x0,0x0,0xf211a022f119122f3185,0x23011901d73184,0x13cb7b5217173422816d322416d222886c722486c6054459c13c8582200157713c356a1783553162355217885471628546054533813c131e17813131621312178b307162b3060f410d423510c71ee10c61ee80c51c410c40f48008,0x0,0xd46734201a70f20186f736e16df38b16c737a16c6348159c365558f365157735f1547349154606244d033114b728254aa2fb449f30c548717a448606273382fb131f282131230c130717a73060f8525d0a331a00f8119226d118713e118625b100b2371008,0xd56734202a70f20286f725816df25716c6251159c253558f2531577252154606b44d024a14b723e54aa246549f23b548606b7338246131f23e131223b13060f9525d0aa31a00f911922381186,0xd76734206a70f20686f723a16de06c44d023914b706c7338,0x0,0x0,0xd6b734205a70f23c159c23d158f07044d0,0x0,0x0,0xbf673424516d2244159c07144d024314b624114aa23f131d0fd525d0a591a00fa11862401008,0xfc5328]
def deadLinkChunk18 : Array Nat := #[0x0,0x24214b4,0x0,0x24214b4,0x0,0x0,0x24917aa1c2b786247154623f13dc0fb53280fa1184,0x24810c0,0x0,0x0,0x132a7da13287c22501792151878624e161224f1606243557424313dc2391252247124624d10c524c10c224b1008,0xf620c0,0x0,0x0,0x0,0x0,0x0,0x6e459c244557623c555206e740424413de23c13d2,0x6f44d024e14b706f7338,0x23d555224f154625610c525510c22541008,0xef70c0,0x0,0x0,0x6d44d025014b724554aa06d73382451312,0x249556a1c2654624913ea1c2b3c623a12502591008,0x25a16040e930c0,0x0,0xd86800207a7db20787c326b1792267166826a565b26a16432681612072459c264158325c55762615552072740425c13de26113d2,0x260179e25f158225d1576,0x25e1580,0x0,0x25e1580]
def deadLinkChunk19 : Array Nat := #[0x0,0x208878626316062621546,0x0,0x0,0x25f564025f14a8262118426510c0,0x266530426611841c620c4,0x0,0x0,0x26956592691641263554626313c6,0x0,0x26916dc2631184,0x2605576208a54626013de20883c626c1008,0x0,0xda6800215a7db21587c327d179227f1786073459c27c158326e557627555522795546073740426e13de27513d227913c6,0x273179e2741792272158226f15762711552,0x2701580,0x0,0x0,0x2701580,0x0,0x0,0x278179220d878627615522771546,0x0,0x0,0x0,0x27b17921c3b7862715576276555227a1546,0x0,0x0,0x272564027214a8277118427a10c4,0x273557627b555220da54627313de27b13d220d83c627e1008,0x1601244,0x274557627855521c3654627413de27813d21c3b3c62801008]
def deadLinkChunk20 : Array Nat := #[0x2811604,0x0,0xbe67341f7a70f2ec16df2f516d32f016d22f816c72e2159c2ea158f2e315532e7154708244d02d114b62b614aa2ab149f2cc14932dd1487283131d125525d0a491a026e11932a211870fe118625c10d723e10d429a1008,0x83b7341fa670f28876ea29976df29576de29476d329376c708344d028814b6293149f294149329914872951486116532823f11a0286118028410d423f7008,0x11a5328285118c,0x118525c,0x84b668287761e084440428713ea117525c28510d4,0x0,0x29116f629216ea29014912891490287124c,0x28b163628e162a28a1241,0x0,0x28c1634,0x28d1180,0x0,0x28c163428f10c0,0x28d1568,0x0,0x28b76f428b149c,0x28b76f428e149c,0x11053f4,0x11b53f4,0x29276ea29716de28914b42961181,0x28a14b4,0x28e26e828e14b429810c0,0x28f261c28f13e8,0x290158011953f4,0xb367342a116d22a0159c08544d029e14b629b14aa284131d128525d0a691a024010d4,0x29c14b4,0x29d1240,0x0,0x29c14b429f1180,0x29d13e8]
def deadLinkChunk21 : Array Nat := #[0x0,0x0,0x2a8179e2a917922aa17862a515822a315762a615522a71546,0x2a41580,0x0,0x2a41580,0x0,0x0,0x0,0x0,0x0,0x2b417aa2b5179e19f678628855742ac155d2b313c529513c42ad1305100530427111862af11802a710c62494008,0x0,0x2ae13d0,0x0,0x2b116de2b216c628754a82b013c4,0x0,0x0,0x0,0x29055802ae13d0,0x29267a8291457429273d02b1124c,0x29267a8292557429713d0,0xbd67342c716eb2ca16df2c916de2cb16d32cb56c72c4159c2c5155f2c615532c655472b714b428854a928813290a7326c26f125f2a3125310012522a35247100524625d11a324111a029b10d42c310c729b5008,0xa866682c216372b9862b289862a2a4861f2a4a61327086072bf14d02c014ab2c1149f2c154932c084870a83338270132b2a4131f2a453132b91307289130625e126f242126c2b812472bd12432bb124029c11a02b8119329c50d425e800b2428008,0x0,0x2ba1300,0x0,0x2bc140429d11a029d50d4,0x0,0x2be1544,0x0,0x2bc130c]
def deadLinkChunk22 : Array Nat := #[0x0,0x0,0x28b86f428b13d0,0x2b81580,0x2bf1580,0x2c01580,0x2c11580,0x2c817a82c21580291457429113f4,0x28b858028b357428b73f4,0x2c816e928984b429254a92921329,0x2b98580,0x2a48580,0x2d0179e1f9a7862cf16062ac156929313e91115329101125227112462cd1008,0x2ce16c4,0x0,0x0,0x0,0xa96734126a70e2dc16eb2d286df29586de2a586d327286c72d9159c2da155f2db15532da85472b714b412653290a9926c272125f2a512532d21247295124625f11a324311a02d811872d611832d4118029e10d425f800b2438008,0x2b915802d31240,0x2ba14b4,0x2d514d02bb13e829f10d4,0x2bc14b4,0x2d716042bd1580,0x2be1580,0x2b81580,0x2bf15802d5124c,0x2c01580,0x2c11580,0x29227a82c215802927310,0x2a8279e2e117921f8a7862e0160629413e912953292a612522a712462de1008,0x2df1484,0x0]
def deadLinkChunk23 : Array Nat := #[0x0,0x0,0x7a459c2d915822c4157624411a02a010d4,0x2e416592da15822c515762cf15462e51008,0x0,0x2e61244,0x0,0x2db15822c615762e015462e81008,0x2e91484,0x0,0x2e4161d2cf11862e010c62eb1008,0x0,0x2ed179d2c9279c2dc15822c715762b4156a19f654628873e827411862aa10c62ee1008,0x29074b4,0x2ef1604,0x0,0x2c926dd075a4d029584b62c914aa2b5149f2a824932f42487295731d07591a02a811932f411872a110d42f2100b2f11008,0x0,0x2f313c4,0x0,0x0,0x2ed17a92d285822ca15762d0155e1f9a54629973e912b5329273125e1031252274124626011a02f61008,0x2f713c4,0x0,0x2a585822cb15762e115521f8a54629473e912d53292a912522aa12462f91008,0x2fa1484,0x0,0x86b80021067db2ab97aa30b7793303779230277871c1b786086459c2ab557630215531c1455230b1547303154628313dc2fc13d10fe73d011553282fc71850fe118424610d427910c627970c514210c42ff10c02467008,0x2ad97b62fe179e2ac55822fd155e11d53f4,0x0,0x2ae97b411e53f4,0x88b734211670f2af96de30076c63017604301154408844d02af54aa3001486286131011f525c]
def deadLinkChunk24 : Array Nat := #[0x212a70e2b296de21366c6,0x89b668214664f2b0961e08a44d0,0x29314a82fd149c10f53f41011250276519027a10c4,0x2b537aa30917921538786295557429513dc24710d427a10c630810c514510c430610c13041008,0x30510c4,0x0,0x3071604296557429613dc,0x0,0x0,0x29737a8297457429713dc14810c430a10c0,0x29836dc29844a82981310,0x2b3564029914a8103749c12053f42fe725027b71901c34184,0xd9b80020fa7db32b17ab32f179332d17923301787209878631f166832a165b324161332016123291607325160608e459c2cc5576302556b3171553315155231e154731815462fc13e912e53290ab926c10e125e2751252279124626110d430d1008,0x314179231316122cd5576312155230e1484,0x31116d231015522ce54b630f1492,0x0,0x0,0x0,0x30f1490,0x3101490,0x3111490,0x20a879220aa786316161231656062fd55692fd13e92765252276124631210d43125008,0x0,0x0,0x31d1792152878631b161231c16061125329112125e277125227a124626210d43191008,0x31a56c431a1484,0x0,0x0,0x0,0x0,0x0,0x0]
def deadLinkChunk25 : Array Nat := #[0x321165931b1552316554631310d43221008,0x0,0x3231244,0x0,0x0,0x2cf5576316155231c154626310d43261008,0x32814843271244,0x0,0x0,0x0,0x32116dc316518431c10c4,0x32c185c2ad94b427811841c3b0c4,0x2ae94b4,0x32c17a92d0557631d155220aa5462fe13e912f5329113125e27b1252278124631410d432e1008,0x1a473c4,0x0,0x0,0xad6800131a7da13187c234717ab3328793303879227c8787150878633f166834616133401612346860734086062d155742d113dc13153290ad326c131125e27c125315012523321247303124626410d724a10d433e10c731810c631880c51c420c433a10c333510c0264800b24a8008,0x2d256402d214a831d819015211843331180,0x33416042d355742d313dc,0x0,0x336159c339154633715442d454a82d41310,0x2d555742d513dc,0x3381008,0x0,0x0,0x33d16c42d656402d614a833b1190,0x33c1610,0x0,0x2d756402d714a833c1190,0x2d856402d814a833b118c,0x2d956402d914a81a92190336118c]
def deadLinkChunk26 : Array Nat := #[0x3421611341161024f80d431c80c634510c51b620c43431008,0x0,0x0,0x3441244,0x0,0x0,0x34286d02da56402da14a831b119031c10c4,0x2b5685c2dc56402dc14a82b533101a02190153118415380c4,0x79459c33f15832e2557631f55531a8455207974042e213de31f13d31a873d226710d725110d4,0x34a558d34a157507c44d034014b735a54871aa448607c733835a13071aa7306356100b3511008,0x7f459c34e15533501547341154634c10d734b10d434f1008,0x0,0x34d1304,0x0,0x0,0x0,0x0,0x34b558d34b1575355154507d44d034314b7354548607d7338354130635311853521184,0x7e440434413eb07e726c,0x0,0x0,0x0,0x34c565934c1641359555235913d23571244,0x34d558d34d157535854923581312,0x0,0x3581250,0x34e565935b1552345154635910d435c1008,0x0,0x35e148435d1244,0x0,0x0,0x36056593601641081459c34615832e35576324555332055523645547325554608174042e313de32413d332013d236413c732513c626810d43621008]
def deadLinkChunk27 : Array Nat := #[0x2e45642321561e342860626911a03611185,0x0,0x2e5557632255522e513de32213d23631244,0x2e654aa32354922e6131e3231312,0x0,0x360161134a161008f459c2ea557632a55531d5455236d1547340854626a10d725310d436c10c732510c636710c51aa70c43661008,0x34f16102eb55761d6455225410d4,0x36815521d745463691008,0x0,0x36b148436a1244,0x0,0x0,0x36116dc,0x35016dc36811901d74184,0x36f17912f06790074459c34715832ec55762ab356a32b555319b455237955471c1654607474042ab93ea2ec13de32b13d319b73d237913c71c1b3c625810d437810c727f10c637310c515510c43711008,0x2ed56422b3363632c561e2b394b62ed14aa32c149e3701191,0x0,0x2a1679037216042ee557619c45522ee13de19c73d225910d4,0x2ef557619d45522ef13de19d73d225a10d4,0x2a7356a374555219e45462a793ea37413d219e73c63751008,0x0,0x37716043761244,0x0,0x0,0x370185c,0x2a8b85c374119019e7184,0x2f066dd07644d030384b72f054aa303349f387248715524860767338303731f2f01312387b307155b30607631a038711871551186382100b37b1008,0x2f166dd37f66c507744d030484b72f154aa304349f381248738024860777338304731f2f11312381b307380b30637f524507731a03811187380118637f10c537e100b37c1008,0x37d1008,0x0,0x0,0x0]
def deadLinkChunk28 : Array Nat := #[0x37616de30534863057306176525e1761191,0x0,0x2f267a938367852f25576386255238525462f213de386b3d2385b3c63835305386125238512463831185,0x3842790384131037d1180,0x0,0x2f367a815b1250,0x15b1250,0x37017a92f45576388555230835462f413de38813d230873c638610d43891008,0x0,0x38a1604,0x0,0x36f17a9078459c33285832f5557630b456b32f555332d55523935547209a546078740430b73eb2f513de32f13d332d13d239313c720983c613953290ac326c139125e27d1252392124727f124626b10d4391100b38c1008,0x37e17922f6557632e555239055462f613de32e13d239013c613a532938d530513a125e27e125238f124638d118526c10d4,0x38e131037d1180,0x0,0x13b532813b125c1601250,0x2f713dc1a473d0,0x0,0x0,0x0,0xae67343d127271f6670f36eb6eb3c726df28226d23a686c717a86c63d026683d1761f3ea26073dc26063d0159c3d1858f3d1156b3ea15473dc15460aea4d028284b63c714ab36e349f3a6248717a2486282731d0ae526c1f6525f28212523a6724717a72460ae91a03a6118717a11863951008,0xaf67343a327271fb670f371b6eb39f26df29a26d23a226683a3761f3a2159c3a3858f3a3156b0afa4d029a84b639f14ab371349f39613c429a731d0af526c1fb525f29a12520af91a0,0xb2666839c265b1fc6643372b62b397261f39b259c39c755f39b14d039c84c339c14ab0b2a40439713eb37233df0b2526c1fc525f0b291a0,0x2efc6f619da6c639a15462ef44a919d52463981008,0x3991604,0x0,0x0,0xb1a4d00b15338,0x39d158d39a148639e1008,0x0,0x0,0x2eec7b619ca7863a1160629b85802ee4569397149029b131c19c52463a01008]
def deadLinkChunk29 : Array Nat := #[0x39856c439814900f620c0,0x39a1490,0xb0a59c2a0858239b14900b053382a0131e,0x3a416593a1154639c14903a51008,0x39d155c,0x39e14900ef70c0,0xb568003c617f31ff67db379b7b72dd279e3c017923c517873c117863b417343b516d23bf16c73ba16c60c0a59c2f885823b115773b215523b3154737335460b453382a2131e3a713121fd53063a91008,0x2e1279e3a87792374b7862e1858237445523a81546,0x0,0x2de279e3b017923af16d22f985823ae15523aa1484,0x2df26de3ad16d23ac16122fa84c23ab1492,0x0,0x0,0x0,0x3ab1490,0x3ac1490,0x3ad1490,0x2cb864c2a313e83a8118419e50c4,0x2a6279e3a827921fe67862a6131e1fe53123a813063ae10d43ae2008,0x0,0x0,0x3b817923b917863af10d43b61008,0x3b71484,0x0,0x0,0x0,0x2e0279e3b987923be17863bb1008,0x3bd14843bc1304,0x0,0x0,0x0,0x0]
def deadLinkChunk30 : Array Nat := #[0x3b986d23b916c62a9858237435521fe65462a9131e1fe9312374b3063b010d43b08008,0x3b816d23be16c62aa85823a8255219e65462aa131e3a8731219e93063c21008,0x3c416043c31484,0x0,0x0,0x0,0x3b911843be10c4,0xbc68002ecc7b63cf17ab2ec279e3b1879319b87923b1a78719ba7863c916683ce16133ca16123ce56073ca56062b685802ec45692ec73e92b6131c0bc326c3b1125319b12523b1524719b524639f10d43c810c73c120c63c140c51c420c439f5008,0x2c3864c2c313e8,0x2c4864c2c413e81a92190,0x3a150d43be40c63cd10c51b620c43cb1008,0x3cc1484,0x0,0x0,0x2c6864c2c613e83b821903be20c4,0x2c7b8802c728682c7864c2c736342c774b42c713e81a021901a011841a050c4,0xb6a59c2e285823c915773b425531a825520b653382e2131e3b473131a873123a210d4,0x3d216590b7a59c2ea85823c625531d525523db15473ca55463a310d43da10c73ba70c63d510c51aa70c43d41008,0x3a411a03d311913d38185,0x0,0x2eb85821d625523a510d4,0x3d316593d615521d725463d71008,0x0,0x3d914843d81244,0x0,0x0,0x0,0x3d611901d72184,0xb8a4d03ca14ab3e584871aa24860b8526c3e512471aa72463e1100b3dd1008,0xb9a4d03cb14ab3de84863e013c53df13c40b9526c3de1246,0x0,0xbaa4043cc13eb0ba526c]
def deadLinkChunk31 : Array Nat := #[0x0,0x3e485523e214843e41312,0x3e384923e31312,0x0,0x3e31490,0x3e615523cd15463e410d43e71008,0x0,0x3e914843e81244,0x0,0x0,0xbba59c2e785823ce15773b525523ed85473ba25460bb53382e7131e3b573123ed13073ba73063eb1008,0x2e885823b625523ec14842e8131e3b67312,0x2e984c23b724922e9131e3b77312,0x0,0xc1b6682166643348b62b3d0361f0c144043d043eb34833df0c1c26c216525f0c131a0,0xccb734229670f4191702365b6eb41a16c73dc36c60c244d03d144ab40c148734934863f013e90d0c26c3fd124721852463fa1008,0xc3b734232670f3f776d33f376c734ab6c60c344d03f3149334a44923f714873f110d43f17008,0xc5b73434fb6d20c444d03f210d4,0x0,0x3f6179e350b79222f67863f41008,0x3f51244,0x0,0x0,0x3f6779222fa7863f81008,0x3f916c4,0x0,0xcdb73422a670f3fb1702366b6eb0c944d03d444ab3f113e90d1c26c,0xc744d00c8c33834fb3063fc1008,0x0,0xceb80023367db40717ce408179240b1787367b7860ca459c402155240615473d545463fe1008,0x40017ce40117923ff1552,0x0]
def deadLinkChunk32 : Array Nat := #[0x0,0x0,0x40517ce368b79223067863ff10d44031008,0x4041184,0x0,0x0,0x0,0x405155e3d3455240010d4,0x3d64552230654640110d44091008,0x40a1604,0x0,0x0,0xcfb80041417ce36db7b74151792418178722b67863f314b50d3c338402131241313073d5430640d1008,0x41117ce41217923f414b5403131240e1184,0x40f170241016d23f513e94041252,0x0,0x0,0x40f1250,0x4101190,0x0,0x40513de3d343d2350b3c641110d4,0x3f614b53d64312368b30641210d44161008,0x4171604,0x0,0x0,0xc644d03d244b7414149334a349240784870c6c3384071313414830734ab3063fb10d43fb8008,0xcb459c3db4577415155241e154722b65463f774b50d2c338408131241d1307367b30641b1008,0x41c160441615523f874b54091312,0x41715523f974b540a1312,0x0,0x0]
def deadLinkChunks : Array (Array Nat) := #[deadLinkChunk0,deadLinkChunk1,deadLinkChunk2,deadLinkChunk3,deadLinkChunk4,deadLinkChunk5,deadLinkChunk6,deadLinkChunk7,deadLinkChunk8,deadLinkChunk9,deadLinkChunk10,deadLinkChunk11,deadLinkChunk12,deadLinkChunk13,deadLinkChunk14,deadLinkChunk15,deadLinkChunk16,deadLinkChunk17,deadLinkChunk18,deadLinkChunk19,deadLinkChunk20,deadLinkChunk21,deadLinkChunk22,deadLinkChunk23,deadLinkChunk24,deadLinkChunk25,deadLinkChunk26,deadLinkChunk27,deadLinkChunk28,deadLinkChunk29,deadLinkChunk30,deadLinkChunk31,deadLinkChunk32]
def deadLink (n : Nat) : Nat := ((deadLinkChunks[n/32]?.getD #[])[n % 32]?).getD 0
def partialTapeChunk0 : Array Nat := #[0x0,0x1a1,0x26d1a1,0x40526d1a1,0x59d40526d1a1,0x66940526d1a1,0x40826d1a1,0x3c426d1a1,0x3c53c426d1a1,0x3d026d1a1,0x59d26d1a1,0x66959d26d1a1,0x58426d1a1,0x66926d1a1,0x66c26d1a1,0x60426d1a1,0x61026d1a1,0x30561026d1a1,0x60561026d1a1,0x64026d1a1,0x24564026d1a1,0x30564026d1a1,0x3c564026d1a1,0x54564026d1a1,0x60564026d1a1,0x64426d1a1,0x65c26d1a1,0x2701a1,0x4d12701a1,0x4b72701a1,0x6692701a1,0x6372701a1]
def partialTapeChunk1 : Array Nat := #[0x7352701a1,0x6f72701a1,0x2441a1,0x4d12441a1,0x4872441a1,0x7352441a1,0x6c72441a1,0x4051a1,0xc44051a1,0x6050c44051a1,0x3044051a1,0x2453044051a1,0x6053044051a1,0x59d4051a1,0x5784051a1,0x6344051a1,0x2456344051a1,0x4856344051a1,0x6056344051a1,0x6384051a1,0x4081a1,0xc34081a1,0x6050c34081a1,0x4b64081a1,0x7354081a1,0x70f4081a1,0x3c41a1,0x3073c41a1,0x4b63c41a1,0x7353c41a1,0x6c73c41a1,0x3e81a1]
def partialTapeChunk2 : Array Nat := #[0x7353e81a1,0x6c73e81a1,0x3ec1a1,0x93ec1a1,0xc33ec1a1,0x6693ec1a1,0x6373ec1a1,0x6073ec1a1,0x7353ec1a1,0x6f73ec1a1,0x70f3ec1a1,0x6c73ec1a1,0x59d1a1,0x66959d1a1,0x66c59d1a1,0x63459d1a1,0x24563459d1a1,0x30563459d1a1,0x48563459d1a1,0x54563459d1a1,0x60563459d1a1,0x63859d1a1,0x65059d1a1,0x56c1a1,0x956c1a1,0x73556c1a1,0x72756c1a1,0x6c756c1a1,0x5841a1,0x7355841a1,0x7275841a1,0x6c75841a1]
def partialTapeChunk3 : Array Nat := #[0x6691a1,0xc46691a1,0x3046691a1,0x4846691a1,0x66c1a1,0xc366c1a1,0x6f666c1a1,0x70e66c1a1,0x72666c1a1,0x6041a1,0x2456041a1,0x3076041a1,0x4876041a1,0x6056041a1,0x96056041a1,0x6f66041a1,0x6281a1,0x1856281a1,0x2456281a1,0x3c56281a1,0x4856281a1,0x94856281a1,0x4876281a1,0x5456281a1,0x6056281a1,0x96056281a1,0x6076281a1,0x62c1a1,0x962c1a1,0xc362c1a1,0x6401a1,0x1856401a1]
def partialTapeChunk4 : Array Nat := #[0x2456401a1,0x3056401a1,0x93056401a1,0x3076401a1,0x3c56401a1,0x5456401a1,0x6056401a1,0x6441a1,0x7266441a1,0x96441a1,0xc36441a1,0x65c1a1,0x965c1a1,0x1a4,0x3391a4,0x4b73391a4,0x7353391a4,0x6f73391a4,0x32b1a4,0x48732b1a4,0x73532b1a4,0x6c732b1a4,0x4d41a4,0xc14d41a4,0x6050c14d41a4,0x5754d41a4,0x4ab1a4,0x4b64ab1a4,0x7354ab1a4,0x6c74ab1a4,0x4b81a4,0x94b81a4]
def partialTapeChunk5 : Array Nat := #[0xc10094b81a4,0x6050c10094b81a4,0xc14b81a4,0x7c34b81a4,0x7db4b81a4,0x7874b81a4,0x7351a4,0xc27351a4,0x7381a4,0xc17381a4,0x7b57381a4,0x6eb1a4,0x6f66eb1a4,0x6f81a4,0xc16f81a4,0x70c1a4,0x18570c1a4,0x24570c1a4,0x30570c1a4,0x3c570c1a4,0x48570c1a4,0x60570c1a4,0x6c570c1a4,0x7101a4,0x97101a4,0x26d,0x24426d,0x48724426d,0x73524426d,0x6c724426d,0x6f724426d,0x3c426d]
def partialTapeChunk6 : Array Nat := #[0x3073c426d,0x3c53c426d,0x6693c53c426d,0x4b63c426d,0x7353c426d,0x6c73c426d,0x70f3c426d,0x3e826d,0x3c53e826d,0x6693c53e826d,0x5453e826d,0x7353e826d,0x6c73e826d,0x3ec26d,0x93ec26d,0x6050093ec26d,0xc33ec26d,0x6693ec26d,0xc16693ec26d,0x6373ec26d,0x64f3ec26d,0x6013ec26d,0x6696013ec26d,0x6023ec26d,0x6073ec26d,0x7353ec26d,0x6f73ec26d,0x6c73ec26d,0x59d26d,0xc459d26d,0x66959d26d,0x66c59d26d]
def partialTapeChunk7 : Array Nat := #[0x60459d26d,0x61059d26d,0x63859d26d,0x65059d26d,0x5a026d,0xc35a026d,0x7355a026d,0x7275a026d,0x54426d,0x73554426d,0x6c754426d,0x72754426d,0x56826d,0x18556826d,0x66918556826d,0x24556826d,0x66924556826d,0x65b24556826d,0x3c556826d,0x6693c556826d,0x48556826d,0x66948556826d,0x65b48556826d,0x54556826d,0x66954556826d,0x65b54556826d,0x63556826d,0x66963556826d,0x73556826d,0x6c556826d,0x96c556826d,0x6c756826d]
def partialTapeChunk8 : Array Nat := #[0x72756826d,0x56c26d,0x73556c26d,0x6c756c26d,0x58026d,0x18558026d,0x24558026d,0x30558026d,0x3c558026d,0x54558026d,0x64d58026d,0x6c558026d,0x96c558026d,0x6c758026d,0x58426d,0x72758426d,0x6c758426d,0x66926d,0xc466926d,0x66c26d,0xc366c26d,0x6f666c26d,0x70e66c26d,0x72666c26d,0x60426d,0x30760426d,0x48760426d,0x60760426d,0x6f660426d,0x62826d,0x48762826d,0x62c26d]
def partialTapeChunk9 : Array Nat := #[0x72662c26d,0x962c26d,0xc362c26d,0x64026d,0x18564026d,0x24564026d,0x30564026d,0x930564026d,0x30764026d,0x3c564026d,0x54564026d,0x60564026d,0x64426d,0x72664426d,0x964426d,0xc364426d,0x65826d,0x24565826d,0x72565826d,0x972565826d,0x65c26d,0x965c26d,0xc365c26d,0x270,0x32a270,0x48732a270,0x66932a270,0x60732a270,0x6f732a270,0x6c732a270,0x4ac270,0x5814ac270]
def partialTapeChunk10 : Array Nat := #[0x94ac270,0x6c50094ac270,0xc14ac270,0x6c70c14ac270,0x6eb0c14ac270,0x6f74ac270,0x71b4ac270,0x6c14ac270,0x6c24ac270,0x6c74ac270,0x7b74ac270,0x7874ac270,0xc17874ac270,0x4b7270,0x6694b7270,0x6074b7270,0x70f4b7270,0x6c74b7270,0x669270,0xc2669270,0x703669270,0x66c270,0xc166c270,0x70166c270,0x62c270,0x70162c270,0x78762c270,0x637270,0x64a637270,0x24564a637270,0x3c564a637270,0x48564a637270]
def partialTapeChunk11 : Array Nat := #[0x6c564a637270,0x727637270,0x6c7637270,0x64c270,0x18564c270,0x24564c270,0x30564c270,0x3c564c270,0x48564c270,0x60564c270,0x71964c270,0x78564c270,0x650270,0x7f3650270,0x787650270,0x738270,0xc1738270,0x7c1738270,0x6ec270,0x7c16ec270,0x7f26ec270,0xc16ec270,0x4870c16ec270,0x6f7270,0x70c270,0x18570c270,0x24570c270,0x30570c270,0x3c570c270,0x48570c270,0x60570c270,0x6c570c270]
def partialTapeChunk12 : Array Nat := #[0x710270,0x7f2710270,0x724270,0x245724270,0x3c5724270,0x7f1724270,0x728270,0x9728270,0xc1009728270,0xc1728270,0x25c,0xc525c,0x6400c525c,0x1856400c525c,0x2456400c525c,0xc56400c525c,0x3056400c525c,0x3c56400c525c,0x5456400c525c,0x6056400c525c,0x6440c525c,0x18525c,0x64018525c,0x18564018525c,0x24564018525c,0x30564018525c,0x3c564018525c,0x54564018525c,0x60564018525c,0x64418525c,0x3c525c,0x6403c525c]
def partialTapeChunk13 : Array Nat := #[0x3056403c525c,0x3c56403c525c,0xc56403c525c,0x5456403c525c,0x6056403c525c,0x6443c525c,0x48525c,0x948525c,0xc48525c,0x60448525c,0x18560448525c,0x24560448525c,0x30560448525c,0x3c560448525c,0x48560448525c,0x54560448525c,0x60560448525c,0x60848525c,0x48725c,0x948725c,0x70b48725c,0x48570b48725c,0x60570b48725c,0x70f48725c,0x6c748725c,0x54525c,0x64c54525c,0x3c564c54525c,0x48564c54525c,0x60564c54525c,0x65054525c,0x60525c]
def partialTapeChunk14 : Array Nat := #[0x64c60525c,0x3c564c60525c,0xc564c60525c,0x65060525c,0x6c525c,0x96c525c,0xc6c525c,0x4846c525c,0x1854846c525c,0x2454846c525c,0x3c54846c525c,0x4854846c525c,0x6054846c525c,0x6c54846c525c,0x4886c525c,0x6c725c,0x70a6c725c,0x70e6c725c,0x96c725c,0x70c25c,0xc570c25c,0x71025c,0x260,0x9260,0x669009260,0x637009260,0x650009260,0x6eb009260,0x710009260,0x728009260,0x4ac260,0x5534ac260]
def partialTapeChunk15 : Array Nat := #[0x94ac260,0x6c50094ac260,0xc54ac260,0x6eb0c54ac260,0x6c70c54ac260,0x7b74ac260,0x7934ac260,0x7874ac260,0x4b8260,0x5534b8260,0x94b8260,0x7034b8260,0x6d34b8260,0x6c74b8260,0x7b74b8260,0x7c17b74b8260,0x7c34b8260,0x7934b8260,0x7db4b8260,0x7874b8260,0x487260,0x9487260,0x605009487260,0x607009487260,0x606009487260,0x6c7009487260,0xc487260,0x6c500c487260,0x6cd00c487260,0x669487260,0xc1669487260,0x637487260]
def partialTapeChunk16 : Array Nat := #[0x6f7637487260,0x7256f7637487260,0x727637487260,0x638487260,0x602487260,0x6f7602487260,0x6d3602487260,0x607487260,0x9607487260,0x6c7607487260,0x608487260,0x6eb487260,0x6f66eb487260,0x7266eb487260,0xc36eb487260,0x6ec487260,0x6f8487260,0x6c4487260,0x6c7487260,0x96c7487260,0x6050096c7487260,0x6026c7487260,0x6c8487260,0x728487260,0x488260,0x9488260,0x6c5009488260,0x703488260,0x6d3488260,0x6c2488260,0x6c7488260,0x7b7488260]
def partialTapeChunk17 : Array Nat := #[0x793488260,0x787488260,0x669260,0x6f7669260,0x6d3669260,0x637260,0x9637260,0x488637260,0x6f7637260,0x7256f7637260,0x7276f7637260,0x6d26f7637260,0x6066f7637260,0x6d4637260,0x710637260,0x7f1710637260,0x727637260,0x6c8637260,0x638260,0x7b7638260,0x7c17b7638260,0x7f17b7638260,0x7917b7638260,0x7c3638260,0x793638260,0x7f3638260,0x787638260,0x607260,0x9607260,0x488607260,0x6f8607260,0x710607260]
def partialTapeChunk18 : Array Nat := #[0x6c7607260,0x96c7607260,0x6c8607260,0x608260,0x7b7608260,0x793608260,0x787608260,0x650260,0x7b7650260,0x7f17b7650260,0x793650260,0x7f3650260,0x6eb260,0x6f66eb260,0x7266eb260,0x7286eb260,0x96eb260,0x3026eb260,0x3053026eb260,0x6053026eb260,0x4886eb260,0x6086eb260,0x6ec260,0xc56ec260,0x6f8260,0x6c7260,0x7286c7260,0x96c7260,0x4886c7260,0x6086c7260,0x6c8260,0x710260]
def partialTapeChunk19 : Array Nat := #[0x728260,0x9728260,0xc6728260,0x3dc,0x3073dc,0x6f73073dc,0x6c73073dc,0x3c53dc,0x6383c53dc,0x6f83dc,0x3e0,0x4b63e0,0xd54b63e0,0xd84b63e0,0x6c50d84b63e0,0x3ce4b63e0,0x6193ce4b63e0,0x3d44b63e0,0x94b63e0,0xc4b63e0,0x3024b63e0,0xc44b63e0,0x6694b63e0,0x6374b63e0,0x6416374b63e0,0x2416416374b63e0,0x6136416374b63e0,0x6426374b63e0,0x7036374b63e0,0x6c76374b63e0,0x6434b63e0,0x1816434b63e0]
def partialTapeChunk20 : Array Nat := #[0x7036434b63e0,0x7257036434b63e0,0x6d17036434b63e0,0x7276434b63e0,0x6c76434b63e0,0x6444b63e0,0x60e4b63e0,0x70360e4b63e0,0x70d70360e4b63e0,0x70f60e4b63e0,0x6df60e4b63e0,0x6144b63e0,0x6074b63e0,0x7276074b63e0,0x6084b63e0,0x6f74b63e0,0x7016f74b63e0,0x7036f74b63e0,0xc16f74b63e0,0x6f84b63e0,0x7cd6f84b63e0,0x7034b63e0,0x7044b63e0,0x6d04b63e0,0x4856d04b63e0,0x6d44b63e0,0x6c44b63e0,0x2456c44b63e0,0x3056c44b63e0,0x3c56c44b63e0,0x5456c44b63e0,0x6056c44b63e0]
def partialTapeChunk21 : Array Nat := #[0x6c56c44b63e0,0x6c84b63e0,0x7284b63e0,0x4b83e0,0xd54b83e0,0x6c50d54b83e0,0x94b83e0,0x7c34b83e0,0x93e0,0x3040093e0,0x1853040093e0,0x6111853040093e0,0x6c53040093e0,0x6d13040093e0,0x3070093e0,0x6690093e0,0x6050093e0,0x3046050093e0,0x1853046050093e0,0x6346050093e0,0x1856346050093e0,0x3056346050093e0,0x4856346050093e0,0x6386050093e0,0x6070093e0,0x6366070093e0,0x6060093e0,0x62b0093e0,0x6380093e0,0x6f40093e0,0x1856f40093e0,0x3056f40093e0]
def partialTapeChunk22 : Array Nat := #[0x4856f40093e0,0x6c56f40093e0,0x6f80093e0,0xc3e0,0x3d300c3e0,0x6d13d300c3e0,0x6c500c3e0,0x6cd00c3e0,0x3043e0,0x3d13043e0,0x6cd3043e0,0x6d36cd3043e0,0x7873043e0,0x7933043e0,0x3083e0,0x93083e0,0x6c50093083e0,0x6cd0093083e0,0xc56cd0093083e0,0x6f73083e0,0x7016f73083e0,0x7033083e0,0x71b3083e0,0x6cd3083e0,0x6d36cd3083e0,0x6ce3083e0,0x6d33083e0,0x6c23083e0,0x6c73083e0,0x7933083e0,0x7873083e0,0x6693e0]
def partialTapeChunk23 : Array Nat := #[0xc16693e0,0xc36693e0,0x62b3e0,0x63662b3e0,0x54663662b3e0,0x18163662b3e0,0x6f462b3e0,0x2456f462b3e0,0x3056f462b3e0,0x4856f462b3e0,0x5456f462b3e0,0x1856f462b3e0,0x6056f462b3e0,0x6c56f462b3e0,0xc56f462b3e0,0x6f862b3e0,0x6383e0,0x96383e0,0x5466383e0,0xc16383e0,0x6c70c16383e0,0x7270c16383e0,0xc66383e0,0x7f36383e0,0x7876383e0,0x6013e0,0x6346013e0,0x1856346013e0,0x3056346013e0,0x4856346013e0,0xc56346013e0,0x6386013e0]
def partialTapeChunk24 : Array Nat := #[0x96386013e0,0x6023e0,0x7006023e0,0x2457006023e0,0x3c57006023e0,0x5457006023e0,0xc57006023e0,0x1857006023e0,0x7046023e0,0x6073e0,0x96073e0,0x3086073e0,0x6f46073e0,0x1856f46073e0,0x3056f46073e0,0x4856f46073e0,0x6c56f46073e0,0xc56f46073e0,0x6f86073e0,0x6083e0,0x6f43e0,0x1856f43e0,0x3056f43e0,0x4856f43e0,0xc56f43e0,0x90c56f43e0,0x6050090c56f43e0,0x6020c56f43e0,0xc76f43e0,0x6c56f43e0,0x3066c56f43e0,0xc16c56f43e0]
def partialTapeChunk25 : Array Nat := #[0xc66c56f43e0,0x6c76f43e0,0x6f83e0,0x96f83e0,0xc16f83e0,0xc66f83e0,0x3e8,0x2473e8,0x6eb2473e8,0x6c72473e8,0x6ec3e8,0x7916ec3e8,0x6c73e8,0x3ec,0x93ec,0x2440093ec,0x2470093ec,0x6690093ec,0x6070093ec,0x62c0093ec,0x6370093ec,0x6c70093ec,0x6ec0093ec,0x6f70093ec,0x7280093ec,0xc3ec,0x31300c3ec,0x2443ec,0x4852443ec,0x3112443ec,0x6052443ec,0x2483ec]
def partialTapeChunk26 : Array Nat := #[0x92483ec,0x6c50092483ec,0x7032483ec,0x6d32483ec,0x6c22483ec,0x6c72483ec,0x7b72483ec,0x7c17b72483ec,0x7c32483ec,0x78f2483ec,0x18578f2483ec,0x24578f2483ec,0x48578f2483ec,0x60578f2483ec,0x6c578f2483ec,0x7932483ec,0x7872483ec,0x6693ec,0x7036693ec,0x62c3ec,0x70162c3ec,0x6d370162c3ec,0x70262c3ec,0x7c362c3ec,0x78762c3ec,0x6373ec,0x96373ec,0x3086373ec,0x6f86373ec,0x7f16f86373ec,0x7916f86373ec,0x6d46373ec]
def partialTapeChunk27 : Array Nat := #[0x7276373ec,0x1817276373ec,0x64d1817276373ec,0x6c76373ec,0x6c86373ec,0x6383ec,0x7c36383ec,0x7f36383ec,0x7876383ec,0x6073ec,0x96073ec,0x2486073ec,0x6f86073ec,0x7276073ec,0x6c86073ec,0x6083ec,0x7c36083ec,0x7936083ec,0x7f36083ec,0x7876083ec,0x6ec3ec,0x7c16ec3ec,0x18d7c16ec3ec,0x7c36ec3ec,0xc16ec3ec,0x3c50c16ec3ec,0x6f73ec,0x6ce6f73ec,0x3c56ce6f73ec,0x4856ce6f73ec,0x7286f73ec,0x96f73ec]
def partialTapeChunk28 : Array Nat := #[0x3086f73ec,0x4826f73ec,0x6086f73ec,0x6f83ec,0x6c43ec,0x1856c43ec,0x2456c43ec,0x3056c43ec,0x4863056c43ec,0x3076c43ec,0x4856c43ec,0x6056c43ec,0x6c56c43ec,0x7916c43ec,0x6c83ec,0x7283ec,0x97283ec,0x3c67283ec,0xc17283ec,0xc50c17283ec,0x70d0c17283ec,0xc67283ec,0x59d,0x30459d,0x6c730459d,0x63459d,0x18563459d,0x30563459d,0x930563459d,0x30763459d,0x48563459d,0x63859d]
def partialTapeChunk29 : Array Nat := #[0x963859d,0xc363859d,0x5a0,0x6365a0,0x6c76365a0,0x6f45a0,0x1856f45a0,0x3056f45a0,0x4856f45a0,0x6c56f45a0,0x6f85a0,0x96f85a0,0xc16f85a0,0x55c,0xc555c,0x62c0c555c,0x18555c,0x62c18555c,0x65b18555c,0x965b18555c,0x30865b18555c,0x30555c,0x930555c,0x65b00930555c,0x60830555c,0x65b30555c,0x965b30555c,0xc865b30555c,0x30755c,0x6f730755c,0x6c730755c,0x72730755c]
def partialTapeChunk30 : Array Nat := #[0x3c555c,0x6383c555c,0x48555c,0x63848555c,0x65b48555c,0x965b48555c,0x3c865b48555c,0x54555c,0x63854555c,0x65b54555c,0x965b54555c,0x3c865b54555c,0x62955c,0x63862955c,0x6c555c,0x96c555c,0xc6c555c,0x3086c555c,0x6c755c,0x6f66c755c,0x96c755c,0x6f855c,0x72755c,0x972755c,0x3c872755c,0x560,0x636560,0x9636560,0x548636560,0x704636560,0x6c8636560,0x6f4560]
def partialTapeChunk31 : Array Nat := #[0x1856f4560,0x2456f4560,0x3056f4560,0x4856f4560,0x5456f4560,0x3065456f4560,0xc65456f4560,0x5476f4560,0x6056f4560,0x6c56f4560,0xc56f4560,0x6f8560,0x96f8560,0xc66f8560,0x568,0xc5568,0x6c7568,0x96c7568,0x56c,0x956c,0x24700956c,0x48700956c,0x6c400956c,0x6c700956c,0x6f800956c,0x72700956c,0x72800956c,0xc56c,0x7f300c56c,0x79300c56c,0x24856c,0x55324856c]
def partialTapeChunk32 : Array Nat := #[0x7f324856c,0x79324856c,0x48856c,0x7f348856c,0x79348856c,0x6f856c,0x7f36f856c,0x7936f856c,0x96f856c,0x6c76f856c,0xc56f856c,0x72756c,0x6ce72756c,0x6d472756c,0xc472756c,0x72856c,0x6c456c,0x2456c456c,0x7916c456c,0x6c756c,0x96c756c,0x90096c756c,0x2470096c756c,0xc6c756c,0x2486c756c,0x6c856c,0x96c856c,0x628,0xc5628,0x245628,0x9245628,0x3c8245628]
def partialTapeChunk33 : Array Nat := #[0x93c8245628,0x6050093c8245628,0x6133c8245628,0x6013c8245628,0x6023c8245628,0x548245628,0x247628,0x3c5628,0x605628,0x9605628,0xc605628,0x248605628,0x607628,0x9607628,0x62c,0x962c,0x24700962c,0x60400962c,0x60700962c,0xc62c,0x6d300c62c,0x24462c,0x31124462c,0x24862c,0x55324862c,0x6d324862c,0x60462c,0x6d160462c,0x60862c,0x960862c]
def partialTapeChunks : Array (Array Nat) := #[partialTapeChunk0,partialTapeChunk1,partialTapeChunk2,partialTapeChunk3,partialTapeChunk4,partialTapeChunk5,partialTapeChunk6,partialTapeChunk7,partialTapeChunk8,partialTapeChunk9,partialTapeChunk10,partialTapeChunk11,partialTapeChunk12,partialTapeChunk13,partialTapeChunk14,partialTapeChunk15,partialTapeChunk16,partialTapeChunk17,partialTapeChunk18,partialTapeChunk19,partialTapeChunk20,partialTapeChunk21,partialTapeChunk22,partialTapeChunk23,partialTapeChunk24,partialTapeChunk25,partialTapeChunk26,partialTapeChunk27,partialTapeChunk28,partialTapeChunk29,partialTapeChunk30,partialTapeChunk31,partialTapeChunk32,partialTapeChunk33]
def partialTape (n : Nat) : Nat := ((partialTapeChunks[n/32]?.getD #[])[n % 32]?).getD 0
def partialCashChunk0 : Array Nat := #[0x280c,0x4a280c,0x4a280c0b,0x280c,0x0,0x0,0x0,0x0,0x0,0x0,0x280c,0x0,0x4a,0x280c,0x0,0xb,0x0,0x0,0x0,0xb,0x0,0x0,0x0,0x0,0x0,0x0,0x4a,0xa05d280c0b,0x0,0x0,0x0,0x0]
def partialCashChunk1 : Array Nat := #[0x0,0x0,0x740c0b,0x0,0x1,0x0,0x1,0x5d280c06,0x0,0x0,0x0,0x0,0x0,0x280c,0x0,0x1c06,0x0,0x0,0x0,0x0,0xa068281406,0x1,0x1,0x0,0x0,0x0,0x682b,0x1,0x1,0x0,0x1,0x5d281405]
def partialCashChunk2 : Array Nat := #[0x0,0x1,0xa05d280c0b,0x1,0x1,0x0,0x1c,0x1,0x0,0xa0,0xa0,0x1,0x745d0c,0x280c,0x0,0x49,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa0741c0c,0x1,0x0,0xa0,0x1,0x7468,0x4a,0x5d,0x1]
def partialCashChunk3 : Array Nat := #[0xa04a280c,0x0,0xa0,0xa0,0xa05d0c0b06,0x1,0x0,0x0,0x0,0xa04a0c,0xa04a0c,0x1,0x1,0xa00c,0x0,0x1,0xa01406,0xa014,0xa014,0xa014,0xa014,0x0,0x1,0xa014,0xa014,0x0,0x1,0xa05d280c0b,0x1,0x1,0xa06806,0xa068]
def partialCashChunk4 : Array Nat := #[0xa068,0xa068,0x0,0x1,0xa068,0xa068,0xa068,0xa05d280c0b,0x45,0x1,0x1,0x741c0c0b,0x4a,0xa0741c140c0b,0xa0741c0c0b,0x4a,0x0,0x0,0x740c0b,0x4a,0x0,0x1,0xa0682b14,0x8c6339,0x0,0x4a,0xa0741c0c0b,0x6,0x4a,0x4a,0xa09d741c0c,0x5]
def partialCashChunk5 : Array Nat := #[0x0,0x0,0x9d74,0x981c,0x980b,0x9d05,0xa0741c140c,0x1,0xa04a1c14,0xa868,0x0,0x8c741c0c0b,0x6,0xa8a04a1c0c,0x9d74,0xa86805,0xa868,0xa868,0xa868,0xa868,0xa868,0xa868,0xa868,0x9874140c,0x5,0x28140c,0x7414,0x4a,0x0,0x1,0x1,0x682809]
def partialCashChunk6 : Array Nat := #[0x1,0x6828,0x0,0x1,0x0,0x1,0x1,0x682b09,0x682b,0x0,0x7422,0x0,0x1,0xa05d280c0b,0x1,0x1,0x1,0x0,0x0,0x45,0x45,0x7468,0x0,0x1,0x1,0x0,0x1c,0x4a,0x5d4a28140c,0x0,0x280c,0x0]
def partialCashChunk7 : Array Nat := #[0x0,0x14,0x0,0x0,0xa0746814,0x1,0x0,0x0,0x745d14,0x14,0x1,0x1,0x682b14,0x682b,0x0,0x682b,0x0,0x1,0x682b,0x0,0x682b,0x0,0x1,0x682b,0x0,0x1,0x7468,0x0,0xa014,0x682b,0x0,0x1]
def partialCashChunk8 : Array Nat := #[0x1,0x740c09,0x0,0x1,0x742214,0x7422,0x7422,0x7422,0x7422,0x7422,0x7468,0x7422,0x0,0x1,0x682809,0x5d,0x1,0xa028140c,0x0,0xa05d140c06,0x1,0x0,0x0,0x0,0xa014,0x1,0x1,0x1,0x1,0xa04a0c09,0x1,0xa05d280c0b]
def partialCashChunk9 : Array Nat := #[0x45,0x1,0x1,0xa06814,0xa068,0xa068,0xa068,0x0,0x1,0xa068,0xa068,0xa068,0xa05d280c0b,0x45,0x1,0x1,0xa0684a09,0xa0684a,0x7468,0x0,0xa05d280c0b,0x1,0x1,0xa04a281c140b,0x280c0b,0x4a,0x0,0x1,0xb,0x1,0x9894615d2814,0x6]
def partialCashChunk10 : Array Nat := #[0x9,0x0,0x8714,0x0,0x0,0x5d,0x5d,0xc878,0x610b,0x6109,0x981c,0x5d09,0x0,0xa04a281c14,0x0,0x1,0xa0,0x1,0xa04a281c14,0x1,0x0,0xa05d1406,0xb35a,0x0,0xa0741c0c0b,0x6,0xcd09,0xa05d281406,0x14,0x1,0x1,0x1]
def partialCashChunk11 : Array Nat := #[0x1,0xa0,0x1,0x9d7409,0xa05d5b,0xb35a,0xa05d5b,0xb35a,0xa05e5a,0xb25b,0x0,0xb25d5b,0x986d5d280906,0x5d,0xc209,0xa04a1c14,0x9d452b,0x0,0xa8a04a1c14,0x6,0xcd06,0xcd14,0x45,0x8c5d281406,0xa86809,0xa36d,0xa36d,0xa868,0xa36d,0xa36d,0xa36d,0xa36d]
def partialCashChunk12 : Array Nat := #[0x9d984a2809,0x5d,0x8c746d09,0x8c845a,0x1,0x0,0xcd5d28140b,0x9,0x0,0xcdc214,0x7414,0x7414,0xae63,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9d74,0x7414,0x6d2b,0x0,0x0,0x0,0x0,0x0,0x0,0x9d74,0x7414,0xa66b]
def partialCashChunk13 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x9d74,0x7414,0x7414,0xae63,0x6d2b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9d74,0x9d8c7414,0x8c6339,0x6d2b,0x0,0x0,0x9d74,0x9d74,0x7414,0x6d2b,0x0,0x0,0x0,0x9d74,0x7414]
def partialCashChunk14 : Array Nat := #[0x6d2b,0x0,0x0,0x9d74,0x7414,0x7414,0x9d4a27,0x6d2b,0x0,0x0,0x0,0x0,0x0,0x0,0x9d74,0x9d741c14,0x6d2b,0x9d74,0x9d452b,0xa06d06,0xa06b05,0x9d74,0xa04a281c140c0b,0xa8984a280c0b,0x1,0x6,0x5d0b,0x6,0x980b,0xc20b,0xa0740c0b,0x4a]
def partialCashChunk15 : Array Nat := #[0x6109,0x0,0x8c740c,0x25,0x45,0x4a1c0b,0x4a1c,0x4e,0xa045280c0b,0x45,0x2505,0x4a,0x4a,0x4a,0x9,0x0,0x1c06,0x1c,0x9,0x5,0x8c5d4a280c0b,0x8c6d61280c0b,0x0,0x0,0x0,0x0,0x61250b,0x45,0x0,0x1,0x0,0x4a0c]
def partialCashChunk16 : Array Nat := #[0x0,0x0,0x45,0x4a,0xc26828,0x6d,0x0,0x8c280c,0x0,0x0,0x4a,0x8c28,0x0,0x0,0x6d,0xcd,0x8c45,0xc2,0x45280c,0x0,0x0,0x0,0x4a,0xc2,0xa04a280c0b,0x6125,0x0,0x4a,0x4a,0x0,0x0,0xa04a0b]
def partialCashChunk17 : Array Nat := #[0x4a1c,0x45,0xa0741c0c,0x14,0x1,0x745d4e0c,0xb,0x4a,0x4a0c0b,0x4a,0x0,0x0,0x0,0x4a,0x45,0x45,0x4a1c0c0b,0x4a,0x745a,0x9,0x0,0x0,0x0,0x4a,0x4a,0xb,0x4a,0x8c745d4e0c,0xb35a,0x0,0x4a,0x4e]
def partialCashChunk18 : Array Nat := #[0x281c0c,0x0,0x0,0x745a,0x4e,0x4a,0x0,0x987468,0x14,0x0,0x5d,0x5d,0xa8a04a280c0b,0xa814,0xa074,0x14,0x6,0x0,0x0,0x0,0x984a,0xcd,0xa84a0c0b,0xa84a0c,0xa8140b,0xa84a281c0c,0x4a,0xa868,0x4a,0x0,0xa80c0b,0xc245280c0b]
def partialCashChunk19 : Array Nat := #[0xc2741c0c0b,0xc20b,0x0,0x98682b0b,0x9868280b,0x7422,0x9d74,0x98682b0b,0x9d74,0x9d74,0xa05d4a28140c,0x4a28140c0b,0x6,0x611c,0x6,0x0,0x0,0x4a,0xb,0x251c,0x0,0x4a,0x6,0x4a01,0x5d,0x0,0x0,0x0,0x0,0x0,0x684a,0x0]
def partialCashChunk20 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x4a,0x684a,0x0,0x0,0x0,0xb,0x49,0x4a01,0x5,0x4a,0x1c060201,0x0,0x0,0x0,0x5,0x0,0x1c140c,0x6,0x1c06,0x0,0x4a0b,0x1c14,0x14,0x14,0x14,0x14,0x14]
def partialCashChunk21 : Array Nat := #[0x14,0x9d,0x6,0x9868281406,0x6109,0x0,0x6d05,0x5d,0x8c615d4a280c09,0x61,0x0,0x0,0x4a,0x0,0xaa63,0x4a,0x614a280c,0x0,0x0,0x61,0x0,0x0,0x0,0x0,0x8c6b2809,0x9,0x6b28,0x6,0x614e,0x6109,0x0,0x0]
def partialCashChunk22 : Array Nat := #[0x0,0x61,0x9461,0x986b280b,0x6109,0x4e,0x6b4528,0xa06314,0x871406,0x0,0x870c06,0x0,0x9861,0x4a,0x984a280c0b,0x250b,0x45,0x0,0x0,0x4a,0x4a,0x4a,0x4a,0x986828,0x0,0x0,0x4a,0x4a,0x4a,0x4a0b,0x45,0xa0746814]
def partialCashChunk23 : Array Nat := #[0x746861,0x61,0x746861,0x615d4a,0x0,0x0,0x1c,0x1c,0x1c,0x1c,0x1c,0x25,0x1c,0x1c,0x1c,0x1c,0xa07468614e,0x614e,0x6,0x7458,0x45,0xcd,0x0,0xb,0x6145,0x7468,0xd55a,0x45,0x45,0x45,0x4e,0x7468]
def partialCashChunk24 : Array Nat := #[0x0,0x746861,0xb,0x0,0xb,0x0,0xb,0x0,0x61,0x8c74686109,0x8c6339,0x0,0x9,0x0,0x9,0x0,0x9,0x0,0x61,0x746b,0x9845280c0b,0xa04514,0xa04514,0xa04514,0xa04514,0x0,0x0,0x0,0x45,0xa0614e14,0x1c,0x4e]
def partialCashChunk25 : Array Nat := #[0x0,0x4e,0x946145280c,0x9461,0xae63,0x45,0x985d28140b,0x9868280b,0xa868,0xa868,0xa868,0xa868,0x985d28140b,0xa05d28140c06,0x9d8c6d5d28140c05,0x25,0xa06d,0x1,0xa36d28,0x4925,0x1c,0x6d2805,0xa325,0x14,0xc225,0x9d6d281c0b,0x6d05,0x9d7414,0x9d74,0x0,0x9d74,0x985d280c06]
def partialCashChunk26 : Array Nat := #[0x610b,0x0,0x4a,0x4a,0x0,0x0,0x25,0x0,0x985d,0x5d0b,0x5d,0x5d,0x5d,0x5d,0x5d,0x5d06,0x45,0xa0682806,0xa0,0xa07468,0x684a,0x0,0x25,0x1c,0x25,0x6d684a28,0x14,0x49,0x1c,0x0,0x0,0x5d]
def partialCashChunk27 : Array Nat := #[0x6d68,0x0,0x0,0x68,0x5d,0x6d5d28,0x5d,0x5d25,0x5d,0x8c6d684a28,0xa36d,0x0,0x5d,0x8c6d5d2805,0x0,0x6d5d28,0x5d,0x5d,0x25,0x0,0xcd6d280c,0xa028140c,0x0,0x1c,0xa38c6d09,0x25,0xa09d5d280c,0x0,0x0,0x0,0x5d,0xa0]
def partialCashChunk28 : Array Nat := #[0xa8,0x0,0x5d,0xa09d281c14,0xa06d1c14,0xa06d,0xa06d,0xa06d,0x14,0x250b,0xa06d,0xa06d,0xa06d,0x0,0x9d28,0xc268282506,0xc225,0x1c,0xcd9825,0x6d02,0x0,0x0,0x5d4a280c,0x745d14,0x1,0xa04514,0xa014,0xa014,0x0,0x1,0xa014,0xa049281c140c]
def partialCashChunk29 : Array Nat := #[0x1,0x1,0xa0746814,0xa0746809,0x1,0xd55a4514,0xb35a,0xb35a,0xb35a,0xb35a,0x947468,0x45,0xa868,0x682b0b,0x682b0b,0xa868,0x682b0b,0xa868,0xc2a8682b,0x45,0x0,0x682b0b,0x682b,0x5,0xa868,0xc2a8682b,0x45,0x0,0xa868280b,0xa868,0xa868,0xa868]
def partialCashChunk30 : Array Nat := #[0x682b0b,0xa868,0x682b0b,0xa868,0xc2a8682b,0x45,0x0,0x682b0b,0xa868,0xc2a8682b,0x45,0x0,0x74680b,0x0,0x682b0b,0x682b,0xa868,0xa868,0xa8682b0b,0xa868,0xa868,0xa868,0xc2a8682b,0x45,0x0,0x745d0c,0x745d4e0c,0xb,0x4a,0x6,0x4a,0xcd0c0b]
def partialCashChunk31 : Array Nat := #[0xa05a0b,0xcd0c0b,0xcd140b,0xcd140b,0xcd0c0b,0x25,0x0,0x25,0xcd0c0b,0xcd1405,0x745a0b,0x741c0c,0x9449,0x0,0x745d14,0x745d14,0x94745d14,0x9d452b,0xa05d4a28140c,0x986d4e4a28140c,0x8c786d,0xa05a,0x4e,0x5a40,0x8c4e,0x14,0x8c4e,0xa0786d4509,0x4e45,0x8c4e,0x745a,0x4a]
def partialCashChunk32 : Array Nat := #[0xb,0x4a,0x6d5d28,0x6d,0x5d,0xa09d4a281c14,0x9,0x0,0x9445,0x0,0x7468,0xa05d4a28140c,0x0,0x14,0x14,0xa0746814,0xa06d4e14,0xa06d4e,0x0,0xa05d4a28140c,0xc2a84e280c,0x0,0x0,0xc2944e,0x0,0xa05d4a280c,0xc294,0xa098140b,0xa098140b,0xa098140b,0xa014,0xa04514]
def partialCashChunk33 : Array Nat := #[0x0,0x0,0x1c,0x45,0x0,0xcd0c0b,0xa0984a0c0b,0xa098140b,0xa098140b,0xa014,0xb35a,0xcd0c0b,0xa0986d4e140b,0xb35a,0xa04a281c140c,0xa8a09d49281c140c,0x9d4627,0x94,0x9d2b,0xa89d8c4509,0x9445,0x9d7414,0x0,0xa80c,0x6,0x4a,0x9d74,0x0,0x5d4a280c,0xc24e]
def partialCashChunks : Array (Array Nat) := #[partialCashChunk0,partialCashChunk1,partialCashChunk2,partialCashChunk3,partialCashChunk4,partialCashChunk5,partialCashChunk6,partialCashChunk7,partialCashChunk8,partialCashChunk9,partialCashChunk10,partialCashChunk11,partialCashChunk12,partialCashChunk13,partialCashChunk14,partialCashChunk15,partialCashChunk16,partialCashChunk17,partialCashChunk18,partialCashChunk19,partialCashChunk20,partialCashChunk21,partialCashChunk22,partialCashChunk23,partialCashChunk24,partialCashChunk25,partialCashChunk26,partialCashChunk27,partialCashChunk28,partialCashChunk29,partialCashChunk30,partialCashChunk31,partialCashChunk32,partialCashChunk33]
def partialCash (n : Nat) : Nat := ((partialCashChunks[n/32]?.getD #[])[n % 32]?).getD 0
def partialLinkChunk0 : Array Nat := #[0x137266b0b926683f2265b3ee26571d6264318a263f42e162b41b162732d261f326261b3a2159f396159c3d925833ad257f3f2156b3ee15673d9155f3ad155b08d2407001240432d13eb32613e726a13df26313db137126f0b9126c1d6125f18a125b08d11a300111a0,0x64166b060166808b165b087164307e163f07b162b0701627069160304c159c05c1583057156b0341407027140404213eb03f13e703a13c301b126f002126c0221243,0xe166b00d166801a165b0191643013163f010160f00f160300a159c00c15830061407003140400913cf00713c3,0x51668004159c,0x0,0x0,0x0,0x813c4,0x0,0x0,0xb166800414d0,0x0,0x0,0xb166800514d0,0x0,0x0,0x1216040111304,0x0,0x0,0x181604017154401613c401513040141244,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20173402116f601e166801f163601c14d001d14b6,0x0,0x0,0x0,0x0]
def partialLinkChunk1 : Array Nat := #[0x0,0x0,0x25173402616c602314d00241486,0x0,0x0,0x0,0x0,0x1c266b003266802e265b033163702f163302a260f023260302d159c02e157701c133b0031338023130f02a130302810c3,0x291604,0x0,0x2c160402b1244,0x0,0x0,0x426680041404,0x0,0x3216040312544031148403023040301244,0x0,0x0,0x0,0x0,0x381734039170e03714b5006133803510c2,0x361604,0x0,0x0,0x0,0x0,0x3d173403e16c603c14b5009133803b1306,0x0,0x0,0x0,0x0,0x40173404116c6]
def partialLinkChunk2 : Array Nat := #[0x0,0x0,0x48173404a170e04916f604b16c604516680461636047160603714d003c148d01d133804410c20431008,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4e166b04d1668056164f055163704f163302d14d004514b701e133b00a1338,0x4259c00b1404,0x0,0x5416040531544052148405113040501244,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x59173405a172605b16c602e14d004614b6047148601f13380581008,0x0,0x0,0x0,0x0,0x5d173405e172605f16c600c13380471306,0x0,0x0,0x0]
def partialLinkChunk3 : Array Nat := #[0x4d166805d164f059163703814d300324d004814b704014b303d148f0631483020133b00d1338025130f062130306110c3,0x0,0x0,0x0,0x681725067170d06616f504e166801c24d000e133806510c2,0x0,0x0,0x0,0x0,0x6f16f506d160402a24d006c1486010133806b130606a1244,0x2b2404011126c,0x0,0x0,0x2c24d0012133806e1008,0x0,0x0,0x4f166807a16060781604077154402f14d00761486074148407313c407212440711184,0x50159c0301404,0x51159c0302404,0x52159c0311404,0x53159c0751008,0x0,0x0,0x54159c03124d0,0x3214d00791008,0x0,0x0,0x66173406f16cd055166805b160603314d004914b604b1486021133807d10c207c1008,0x0,0x0,0x861604085154408413c4013133808313060811304080124407f1184,0x14126c]
def partialLinkChunk4 : Array Nat := #[0x15126c,0x821008,0x0,0x0,0x161338,0x171338,0x181338,0x6717340881725056166805f160603914d004a14b5019133804b130608a10c20891008,0x0,0x0,0x0,0x681734088170d05e164d05a163502e24d005f148601a133805b130608c1008,0x0,0xa817370a617340b7170f0af170b0ad16f70ab16ea09614d303424d009e14b709a14aa08e1338092132a,0x90173409116f603824d008f14b6,0x0,0x0,0x0,0x94173409516c603924d00931486,0x0,0x0,0x0,0x99157409710c0,0x981604,0x0,0x0,0x9c173409d16c609914d009b14b508f133809313060351008,0x0,0x0,0x0,0xa417da0a317c20a5178609b157409313040a210c009f1008,0xa010c0]
def partialLinkChunk5 : Array Nat := #[0xa11604,0x0,0x0,0x0,0x0,0x0,0x6259c09c1576090140409413f60a710c1,0x0,0xaa17b40a910c0,0x0,0x0,0xaa17340ac16f503724d009d1486091133809513060651008,0x0,0xac17b40a315820a5154609513040ae10c0,0x0,0xb616c40b516040b414840b313c40b213040b112440b01184,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa415810a513c609d13040b81008,0xa020c0,0x113166b1111668134165b130165712c1643123163f11f162b11d162711816030e4159f0dc159c10e1583104157f101156b0ec15670e815430a6240706024040cd13eb0c713e70bf13c308e126f002126c0ba1243,0xbc17340be16f60bd16c606324d00bb1486,0x0,0x0,0x0,0x0,0xc417340c6170e0c516c60c314b50c113c400713380c01306]
def partialLinkChunk6 : Array Nat := #[0x0,0xc216680081338,0x0,0x0,0xc21490,0x0,0x0,0xcb17340cc16c60ca15440c813c4,0xc91668,0x0,0xc92668,0xc926100c91490,0x0,0xd917340da16f60db16c60d116680d4164e0d316360d816060d716010d5160009c24d00c3148d08f13380d010c20ce1008,0xcf1604,0x0,0x0,0xd210c0,0x0,0x0,0x0,0xd61668,0x0,0x0,0x0,0xd616cc,0x0,0x0,0xdf166b0de16680e3164f0e216370e1160f0e0160304d24d00d114b700a13380dd10c3,0x0,0xb259c00b1404,0x0]
def partialLinkChunk7 : Array Nat := #[0x0,0x0,0x0,0x0,0xe617340e717260e510c2,0x0,0x0,0x0,0xe917340eb17260ea16c6,0x0,0x0,0x0,0xfc173410017260ff16c60fd16c40fa16340f715440f414840f213c40ef12440ed1184,0xee1668,0x0,0xf016680f1165a,0x0,0x0,0xf31668,0x0,0xf516680f6165a,0x0,0x0,0xf816680f9165a,0x0,0x0,0xfb1668,0x0,0xfb17000f816100f515500f314900f013100ee1250,0xfe1008,0x0,0x0]
def partialLinkChunk8 : Array Nat := #[0xf916100f615500f11310,0x102173410316c60fa163005d24d00d314b60d81486,0xfb16fc,0x0,0xfc273410d16c610b16c410a164c109154410813c4107130410612441051184,0xf02668,0xee2668,0xf52668,0xf82668,0xf32668,0xfb2668,0x10c1008,0x0,0x0,0x102273410f172611016c610a16480d414b500c13380d81306,0x0,0x0,0xe6166b0de1668102264f0fc264b10216370fc16330e9160f0e9260309024d300d24d00d914b70cb14b30c4148f0bc2483090133b00d13380bc130f0c4230311210c3,0x0,0x1171725116170d11516f50df166802024d000e133811410c2,0x0,0x0,0x0,0x0,0x11c16f50e1166811b160606224d011a148600f13381191306,0x0,0x0,0x0,0x0,0x4024d011e1486,0x0,0x1151734120172511c16cd0e21668103160604824d00da14b60db148609113380be130d12210c21211008]
def partialLinkChunk9 : Array Nat := #[0x0,0x0,0x0,0x12b160412a154412913c401313381281306126130412512441241184,0x14126c,0x15126c,0x1271008,0x0,0x0,0x161338,0x171338,0x181338,0x116173412d17250e31668110160609424d00c6148d01913380db130612f10c212e1008,0x0,0x0,0x0,0x13217241311244,0x0,0x1331008,0x0,0x1171734132172012d170d12016f50e7166810f164d10016310eb160d05924d0110148601a1338103130613610c21351008,0x1331720,0x0,0x16f1737113273418617271821723180170f178170b17716f617216eb155166b152166816c164f163164b15b1636158162b0a824d306424d014d14b613e14ab138132901b126c,0x116273413c16f613d16c613a166813b160606724d01391486,0x0,0x0,0x0,0x0,0x0,0x14a17b614b1786146171a14516f614916c614816c114716c013f158013913c414210c01401008,0x0]
def partialLinkChunk10 : Array Nat := #[0x14116c40a010c0,0x0,0x14416ea14316c6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x144118c,0x14c10c0,0x0,0x1152734150170e15116c614e166814f16060aa24d013f14b501d133813913060a72008,0x0,0x0,0x0,0x0,0xdf2734154170204e259c14e158213a13f501e133815310c1,0x0,0x0,0x157170015610c0,0x0,0x0,0x15a178615917001451576149154613b13c4,0x0,0x0,0x1172734161172616216c6157166815c1649159163506824d014f148601f133813b13060e51008,0x16016c415f148415e13c415d1244,0x0,0x0,0x0]
def partialLinkChunk11 : Array Nat := #[0x0,0x0,0x0,0x16b178416a171815c17001691604168148416713c4166130416512441641184,0x15d1634,0x0,0x15e1634,0x0,0x15f1640,0x0,0x0,0x1601700,0x16d17f216e178616a1714146157514f13c41491306,0x0,0x0,0x17117c017010c0,0x0,0x0,0x17417f117317c015a16c614a157614b154613c13f413d13c417510c0,0x0,0x0,0x1761486,0x0,0x171173417316f51541668162160606624d01511486021133813d13061141008,0x17f16c417e160417d148417c13c417b130417a12441791184,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def partialLinkChunk12 : Array Nat := #[0x18117f116e16c6150158015113c414b1306,0x0,0x18517f018413c41831244,0x0,0x0,0x0,0x18517ec18117d917417b516d1719161170016e154616213c415a130618910c01871008,0x18810c0,0x0,0x0,0x178273712327341d5170f1d3170b1cf16c61c416c41bf16041b915440af24d307e24d01b214861a6148419e13c4195118418b10c4,0x17a266b1252668194164318c163f0b124070802404,0x1931604192154419113c4190130418e124418d118418f10c4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x179266b124266819d1643196163f0b0240707f2404,0x19c160419b154419a13c419913041981244197118418f20c4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x17e266b12a26681a5164319f163f0b524070852404,0x1a416041a315441a113c41a01304192224419b21841a210c4]
def partialLinkChunk13 : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x17b266b12626681b116071a916031a8100b1a71008,0x1272668,0x0,0x1b016041af15441ae14841ad13c41ac13041ab12441aa1184,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x12827341b7170e1b4170a1b816c60b224d01b31008,0x0,0x1b616041a025441b514841ad13c41ac130418e22441982184,0x0,0x0,0x0,0x0,0x17d266b12926681be164f1ba164b0b424d308424d0,0x1bd16041bc14841bb13c41b52304191224419a21841a220c4,0x0,0x0,0x0,0x0,0x17f266b12b26681c3164f1c0164b0b624d308624d0]
def partialLinkChunk14 : Array Nat := #[0x1a426041bd24841c113c41b62304193224419c21841c210c4,0x0,0x0,0x0,0xb324d308124d01ce14871c714831c6100b1c51008,0x8224d0,0x0,0x1cd16c41cc16041cb14841ca13c41ad23041c912441c81184,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x17c27341d1170d1d0170908324d01b814861d21008,0x1c126c41a126041bb24841ca13c41ad230419022441992184,0x0,0x0,0x1d017901c016d01c026c41ba161019f26041b4155019f14901ba24841d023c41b42304196125018c224418c119019621841d410c4,0x1c216041a225441a213c418f218418f10c4,0x1d117901c316d01be16101b715501a5149019d125019411901b810c4,0x180273712c2734260172725f170f1d5270b25816f725616eb24c16ea25e16c725916c62221668247164f23216372251636243160723b16060b724d308724d01e814b71de14ab21814871f414861381338092126c1d71008,0x12e27341dd17271dc170f1db16ea1d816681da164f1d916360b824d308924d0,0x0,0x0,0x0,0x0,0x0,0x0,0x1e517b61e617921e717861df15521df10c51e210c41e01008,0x0]
def partialLinkChunk15 : Array Nat := #[0x1e116c4,0x0,0x1e316ea1e416c60a01008,0x0,0x0,0x1e31190,0x1e410c4,0x1e410c4,0x1f217da1f017c21ee17b61f117921f317861eb17021ec16d21ed16c61e915521e910c51e210c41ea1008,0x0,0x0,0x0,0x0,0x0,0x1ef17c01e31190,0x0,0x1ef17c0,0x1e410c4,0x0,0x1e410c4,0x14b27370db273421717271e7270f21016f720f16eb20b16ea21616c721216c621116c31fd166820316371ff163620a16072071606204160109d24d01e914b71df14ab1391338093126c1fa100b1f51008,0x1f916c61f716061f816051f61604,0x0,0x0,0x0,0x0,0x1fc16cc1fb16c4,0x0,0xa110c4,0x1fe10c0,0xa11008,0x202172620016f6]
def partialLinkChunk16 : Array Nat := #[0x2011724,0x0,0x2011700,0x0,0x20516f620616d21fc10d4,0x0,0x0,0x20916c62081008,0xa11604,0x0,0x0,0x20d172520c16f52001636205160d20e10c2,0x0,0x2011700,0x0,0x1e410c4,0x20c17b41e410c4,0x20e1304,0x209160621516012131008,0x2141604,0x0,0x0,0x20616cc,0x20d17b4202170020910c4,0x21f17b62201792221178621b170221c16d221e16c621d16c12191008,0x21a16c4,0x0,0x0,0x0,0x0,0x0,0x0]
def partialLinkChunk17 : Array Nat := #[0x1e410c4,0x0,0xe3273422316f622416d2056259c1fd155213a14041d810d4,0x0,0x0,0x181273712d2734230172622e170f22816f622d16d323116c708824d021b14931ff149222714871d910d42261008,0x0,0x0,0x22a1726229172422b16d122c1605200149e,0x201156a,0x0,0x0,0x0,0x0,0x22f17f0,0x0,0x22f171922a17022291700202155e,0x22b17c0,0x23917f223717c223317b6238179223a17861eb158220315521ed1546,0x23517f023417c02361790,0x0,0x0,0x0,0x23417c0,0x0,0x23517c0,0x23617b4,0x16e2737110273423f170f23e16f724216c724016c605f24d01ec14b723d1487207148613b133823c1008,0x0,0x0,0x0,0x20910c4]
def partialLinkChunk18 : Array Nat := #[0x20914862411008,0x0,0x0,0x24417b62451792246178621c155221e1546,0x0,0x0,0x0,0x24b17f224817b624a179223f27861ed13c61da10d421e10c620710c4,0x24917f0,0x0,0x20910c4,0x24917c0,0x150273424f172724e17251f2270f24d16f52231668248164f23316372281636244161325516070a424d304a24d01ee14b721f149320b1492254148713c133825113011db10d42501008,0x234170223616c61ef158220c155e,0x24917192351701229170020d155e23613c6,0x22a1700,0x0,0x25316042521304,0x0,0x0,0x0,0x22c1700,0x1e5157620f15521e7154625710c4,0x1e41486,0x24d17b4237170223e16d223a16c61f0158221015521f3154625710c4,0x151273425a17271f3270f224166824a164f238163725d160724016060a524d304b24d01f114b71e614ab25c1487212148613d1338095126c25b1008,0x0,0x0,0x0,0x0,0x22d170224516d224616c622015522211546,0x22e27f11f227b61f3279222e170223f16d223f26c61f215811e725521f313c61e713061dc10d422110c622120c521210c41dc2008]
def partialLinkChunk19 : Array Nat := #[0x22e27d924f17b624e17b425a179224b171923917012301700217155223f254623a13c61dd10d424610c626210c524010c42611008,0x0,0x0,0xc7273426916f726426c6267254426713c40c713382641306,0xcc273426516f626616c6,0x0,0x0,0xca266826816370c81338,0x0,0x26527902682610268149026513d026610c4,0x13e27370cd27342f027271de270f32216f731416f32a326eb26b26ea2ce26c71f426c62c826c32df16682e2264e2f016372e2162a3131607309160630116012f9160009a24d02a314b726b14b513e133b0cd13381de132b2ce13071f413062c8130309a126c2c3100b2a81008,0x14a27370da27342a217272961703295170229316f728f16f629916d320b26d229716cf2a116c729a16c32761668285164327e1642277163628b1613286160d28e160728c160613f140427113d326f13cd09b13382711307274130126d10d726c10d427110c727510c3273100b2721008,0x0,0x26e16c4,0x0,0x2701618,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x27c170227d16c627b16412781640,0x27a16122791240,0x0,0x0,0x0,0x0,0x27a1640,0x2831726280170220d26de28416c6278164027f1180,0x2791574]
def partialLinkChunk20 : Array Nat := #[0x281172428216d027a1604,0x0,0x0,0x281170c20126e827a1484,0x2821700,0x27b1700,0x289170e287170228a16de2701498,0x288170c,0x0,0x288170c,0x0,0x0,0x28d172627d26f6,0x27a2700,0x0,0x28027252911702291270129017002801642287161927d261227d160629210c0,0x28816252821606,0x0,0x0,0x29417cc1e32184,0x0,0x29117022941701290170020c26de27c164228916192841606,0x29127c0,0x2981484,0x0,0x28a16d8,0x2a016c429f160429e154429d13c429c130429b1244,0x0,0x0,0x0,0x0,0x0]
def partialLinkChunk21 : Array Nat := #[0x0,0x0,0x28027c0200279c283170c28d16d0284148427d13c4,0x1e527da2a717c229327b620f27921e627861e913d21df13062a410d41df10c61e910c51e210c42a61008,0x2a516c4,0x0,0x0,0x29427c0,0x14027370ce27342bc27271e0270f2c216f72bd16f32a426eb26c26ea2ae26c62a926c32af16682bb264e2bc16372bb162a2b816062ba16052b0160403524d02a414b726c14b5140133b0ce13381e0132b2ae13062a91303035126c,0x2ad16d02ac16c42aa1184,0x2ab1610,0x0,0x0,0x2ab1190,0x0,0x0,0x141266b0cf26681e1264f2b716372b316332a5262b2b1260303624d02a514b7141133b0cf13381e1132b2b11303036126c,0x2b21184,0x0,0x2b626042b525442b614842b513042b422442b41184,0x0,0x0,0x0,0x0,0x2b927262b91635,0x0,0x2ad26ce2ad13ce,0x0,0x2b916d0,0x2b316d02c116c42c026042bf25442c014842bf13042be22442be1184,0x2b41610,0x2b51610]
def partialLinkChunk22 : Array Nat := #[0x2b61610,0x0,0x2b716d0,0x26d27b62c427922c716cc2c616c426d15812c413d2,0x2c516d0,0x0,0x26e26f62c526d226e15812c513d2,0x9810c4,0x29727b62cd17922cc17862ca16cc26f15802c913d0,0x0,0x2cb16d22701580,0x0,0x29827b42cb16cc,0x0,0x29927b62dd17922cd278e2de17862d6171a2d517022d316f62da16d22d916cd2d716cc2dc16c62db16c127115812c913cc2c410d42cf1008,0x2d116cc2d016c4,0x0,0x2d210c4,0x0,0x2d41700,0x0,0x2d41700,0x0,0x28a26f62d816d22d110d4,0x0,0x0,0x0,0x0,0x0,0x1e410c4,0x2d816cc,0xd1273427626f61fd26d227615810d114041fd13d22af10d42e110c22e010c0]
def partialLinkChunk23 : Array Nat := #[0xd226680d213380981008,0x0,0x14627370d427342ef16f72e616f32d626d328c26c62e3163527714b5145133b0d313382d313132bb10d4,0x28d26d227b158127815802e415452d413dd2e51180,0x0,0x27914b4,0x2ed16c42ec16042ea15442e914842e813042e712442eb11842ee10c4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x27c1580,0x2f717f22a227b621727922f817862e316f4285158127e15802f2154528c154420313d22d513d11ff13d02bc10d42dc10c62f610c520710c42f310c02f11008,0x0,0x2e41700,0x2f517262f416c62e5162827f14b4,0x0,0x0,0x0,0x28327c0202279c283164c28d1610202149c28d23c42f5118c2f52180,0x28427b4284158020910c4,0x147266b0d526682ff16372fa1633147133b0d51338,0x2fd26042fc25442fd14842fc13042fb22442fb11842fe10c4,0x0,0x0,0x0,0x0,0x3001008]
def partialLinkChunk24 : Array Nat := #[0x0,0x14827370d72734308170330216ff28626f62d926d32d726d22ca26ce286158114814070d714042d913d32d713d22ca13ce2c710d4,0x30526c43042604305154430413c430323043031244307118430610c4,0x0,0x0,0x0,0x0,0x0,0x28927c0289164c2d81184,0x14927370d8273431216f730c16f330b26c720726c6149133b0d8133830b1307207130630a1008,0x981604,0x0,0x31016c430f260430e254430f148430e130430d224430d118431110c4,0x0,0x0,0x0,0x0,0x0,0x20910c4,0x28b27b62da27922dc278628b15812da13d22dc13c6,0x2e6271a2e616f630c16d230216cd2fa16cc32116c631d16c43172604316254431714843161304315224431511842bd10d431c10c631810c4,0x2e8264e2e7162a30d1612303160d2fb160c2be10d4,0x2ea264e30e1612304160d2fc160c2ee16062bf10d4,0x2ec264e2e9163630f1612305160d2fd160c2c010d4,0x2eb264e2eb162a311160631b16013191008,0x31a1604,0x0,0x0,0x30716cc,0x31e254531e13052c110d432010c531f10c0,0x0,0x0]
def partialLinkChunk25 : Array Nat := #[0x0,0x2ed27182ed16f431016d02ee25442ee130431110c4,0x29627b62a727b529527b421027922ef271a2ef16f631216d230816cd2ff16cc2f816c62a71582296158129515801e6254621013d21e613062c210d42de10c632510c521210c432410c03231008,0x30016cc,0x0,0x0,0x11d273432a16eb32c16c603f126c3271246,0x11e273432816ea32916c6,0x0,0x0,0x32b1790328131032910c4,0x0,0x32b16e9041126c3291246,0x172273711f273438f1727256270f24c270e38316f737a16f637416eb32a26e738e16c725926c638416c3351166836516373591636353162b36f160736916060ab24d02a314ab26b14a914d13381e8132b09e126f042126c33f12471f4124633b1243339100b32e1008,0x12127343381727250270e33716f633616eb33516c633116683341636333162b332160606524d02a614ab27214a90a723381ea132b09f126f043126c330124632f1243,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x273157533a1312,0x0,0x33e1604274157433c148433d1310,0x0,0x0,0x0,0x25427da34817c234617b634f1792349178e3501786342170234316d234516c634416c1271157533d130c33a10d43401008]
def partialLinkChunk26 : Array Nat := #[0x34116c4,0x0,0x0,0x0,0x0,0x0,0x34717c0,0x0,0x34717c0,0x34e16c434d160434c148420e130434b124434a1184,0x0,0x0,0x0,0x0,0x0,0x1e410c4,0x0,0xe22734223271a352170222426d2276157514e140404513381fd131233110d4,0x0,0x24827da35717c224a279235817863561701354170027715741ec13c633310d434510c620710c4,0x249271a35516d22781580,0x27a1580,0x27b1640,0x27c1580,0x355170027d157420910c4,0x17427371202734360172624e270e35c16f735f16d336416c736316c6354163527e14b5046133834213131ff131235b130733410d435a1008,0x0,0x0,0x35d17f035e179035516c4280158020d254420013dc,0x281164c201261020114a8,0x2821580,0x0]
def partialLinkChunk27 : Array Nat := #[0x235271a229271835d1701283158120213de35513c63611180,0x362164c,0x0,0x236270e35e16f528414b5,0x0,0x36717f224f27da36617c225a2792368178635616f528515751eb13f520313121ec1306,0x0,0x22a27e4,0x0,0x15a2737103273436d172636c16f735826eb36e16c724026c628c14a914f13381ed132b047126c36b1247207124636a1008,0x0,0x0,0x0,0x35526f528d1575,0x0,0x37217f225527da37017c23711792373178628e157534313123451306,0x0,0x0,0x22c27e4,0x0,0x35c27f11ee27da37717c237727c137517c01f1279235c170235826d235816c62932576293157528f157420f2546346254520b25441ee13f61f113c620f1312346131120b131033610d435010c635020c521210c437810c03362008,0x35e16c6294258229415812901580347255134713dd376118c,0x0,0x1ef27d8291158020c2550,0x37616f4379254429214a837913c4,0x0,0x173273437e172724d270e37716f737516f537b16cd352166835716373701613382160736316060ac24d02a714b729514b538114810a3133b04913383481313380130733710d437f1008,0x37d148437c13c4,0x0,0x0,0x23427d8,0x0]
def partialLinkChunk28 : Array Nat := #[0x0,0x0,0x0,0x37727b5366170236c16d236816c629615751f013f521013121f1130625720c4,0x25127d837b17c038d179038c16c438b160429a157538a148434913123891306387130438612443851184,0x252270c29b14a934a1252,0x29c14a934b1252,0x37c16f4388148520e10c5,0x0,0x29d157420e1310,0x37d170029e14b534c1312,0x29f157534d1312,0x25327182a0157534e1312,0x0,0x38d178c35f170237116d237316c62a1157534f13123501306,0x23327da22827d837e17c235c27b523827923671701360170037216d136d16d02a2157536813c639113c536313c42171312358130633810d437310c639510c524020c439210c03901008,0x0,0x22b27d8,0x394170c361163439310c4,0x0,0x3621640,0x0,0x152266b0dc2668222264f39f16373991633351262b397260304c24d035114b72df14ab152133b0dc1338222132b397130304c126c,0xe0273439816c6,0x0,0x39e260404f259c39d254639b254439e148404f133839d130639b130439a224439a1184,0x5124d0050126c,0x5324d039c1008,0x0,0x0,0x5424d00521338,0x154273435226f5055259c352158222425461541404055133822413063a110c23a01008]
def partialLinkChunk29 : Array Nat := #[0x0,0x0,0x15527370e427343a327263aa16f73a516f33a31635155133b0e41338,0xe727343a416c615714041531008,0x0,0x3a916c43a826043a725443a814843a713043a622443a61184,0x0,0x0,0x0,0x0,0x3a416c43ac10c03ab1008,0x18810c0,0x0,0x163273710427343d617263d516f73d216c63ce16c43cc16283c715443c214843c013c40ec13383bc13063b513043b011843ae10c4,0x165266b10626683af162b0ed126c,0x0,0x164266b10526683b2165a3b1162b0ef126c,0x0,0x15d26680f113383b413073b31008,0x0,0x0,0x16b266b10b26683b9165a3b816073b61008,0x10c26683b7165a,0x0,0x0,0x16026683b710d43bb10c73ba1008,0x0,0x0,0x10d27343bf17263bd16f63be16c6,0x0,0x0,0x3bb13c5]
def partialLinkChunk30 : Array Nat := #[0x169266b10926683c116370f21338,0x0,0x166266b10726683c4165a3c316370f41338,0x0,0x15e26680f614043c613c73c51008,0x0,0x0,0x168266b10826683c9165a3c816370f71338,0x0,0x15f26680f914043cb13c73ca1008,0x0,0x0,0x16a266b10a26683cd16370fa1338,0x0,0xfd13383d113073d0100b3cf1008,0xfe1338,0x0,0x0,0x16727343d316f50ff13383be13063d41008,0x0,0x0,0x3d317903cd16f43c816103c315503c114903bd13d03b112503af11903be10c4,0x15c27343c916103c4155010014043bf13d23b913d03d813c73b212503d71008,0x3ca16103c515503ba13d03b31250,0x3cb16dc3c6161c3bb149c3b4131c,0x16c273710e2734247270f3eb16f73df16f336926c63da16353cc162405c24d035314b72e214aa3091486158133b101133823b1306,0x16d273710f273424b271b3dd170336d26d23de16c705e259c356158335415822e315763dc154715914043db1008,0x0,0x2e41640,0x0,0x0,0x3e916c43e816042e6157630c15523e715463e415443e314843e213043e112443e011843ea10c4]
def partialLinkChunk31 : Array Nat := #[0x2e714aa30d1492,0x2e814aa30d2492,0x30e14922eb1486,0x2e914b630f1492,0x3e513053e610c5,0x0,0x0,0x2ea157430e25502eb130431110c4,0x2ec157630f2552,0x2ed15763101552,0x2ee14aa3111486,0x36c27923dd17013cd16f035715822ef1576312155224a254623e13d23ed10c524010c43ec1008,0x0,0x0,0x182273713027343f016c63ef10c4,0x183266b1312668,0x18427343f11008,0x0,0x1862737134273440f172740b1726260270f40516f738f26eb41916c741316c641016c33a316683d626493da162908b24d036514b735914b62f014ab4021487369148615b1338232132b2251329057126c3fe124723b12463fb100b3f31008,0x187273713527343fa17273f91726261270f3f816f739026eb3f716c63f616c315316683d726493db162908c24d035a14b62f114ab3f514860e513382261329058126c3f41246,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3fc17f23fd1792,0x0,0x0,0x40017f24011792395278635b15823ff15522f61546,0x0]
def partialLinkChunk32 : Array Nat := #[0x0,0x0,0x40317f2404179226227863dc16f52f2157522713f53ff13122f61306,0x0,0x0,0x40617f237e27b540717923dd16f540916c6366158236c155225a254623713f523e131223813063f810d440910c640710c540a10c44081008,0x0,0x0,0x0,0x0,0x1881008,0x1612734239271b2302719406170336726f736026f540d16d340c16cd05a259c367158336015822f71577403155336d15524002547161140423913f723013f540d13c740c23c105a13384001313403230736d23063fc10d73f910d440d10c740e10c33fc200b3f92008,0x0,0x0,0x0,0x409279240913c63fa10d440910c640920c540a10c43fa2008,0x40c17f041217904111244,0x0,0x0,0x1622734409272723a270f40716f736826eb36326e93a41668409163705b24d036814b736314b62f814ab41824872402486162133823a132b05b126c41812472401246417100b4141008,0x416248641612464151008,0x0,0x0,0x0,0x0,0x40d17f239127b5412178c3d827153de16f536415824041552262254623113f5401131239523063fd10d441a1008,0x0,0x3a5166b39916683df264f3df162b42c16064281604427254407024d031414ab426248641d248442713c4070126c426124641d124441c218441c10c4,0x3a6159f39a159c3e125833e0155f072240431513df07111a0,0x3a7159f39b159c3e425834251547074240441f13c741e1008,0x39c159c0752404,0x3e5264e42216123e62606424160142316004201008]
def partialLinkChunk33 : Array Nat := #[0x4211604,0x0,0x0,0x0,0x0,0x42214923e62486,0x39d16683e7264f3e2162a3ea160607624d031614aa3181486,0x3a8159f39e159c3e825833e3156b077240431713eb073126c,0x7824d031d14ab42b2487078126c42b124742a100b4291008,0x7924d0079126c,0x0,0x31e15763201546,0x3a916683e9264d3e9162907a24d032114ab3ea248607a126c3ea124642d1008,0x0,0x17727344052727258270f38326eb37a26e93aa166b39f16683eb264f3d5264b40516373eb162b3d5162743c1607413160643a16030ad24d307b24d038314b737a14b632214ab26914a74372487259248643524831771338258132b0ad126f07b126c437124725912464351243433100b42f1008,0x1142734408272737f26e93ab166b3a016683ec264f40816373ec162b4321606431160307c24d037f14b632314ab4302486114133807c126c4301246,0x0,0x0,0x0,0x43416d2,0x0,0x38127b44361310,0x0,0x43916d23ed16c6380158243815523251546436130c,0x1e410c4,0x0,0x43b16d0,0x0,0x38227b543b16cc382158243925523ed254643913123ed130643410d443d1008,0x0]
def partialLinkChunks : Array (Array Nat) := #[partialLinkChunk0,partialLinkChunk1,partialLinkChunk2,partialLinkChunk3,partialLinkChunk4,partialLinkChunk5,partialLinkChunk6,partialLinkChunk7,partialLinkChunk8,partialLinkChunk9,partialLinkChunk10,partialLinkChunk11,partialLinkChunk12,partialLinkChunk13,partialLinkChunk14,partialLinkChunk15,partialLinkChunk16,partialLinkChunk17,partialLinkChunk18,partialLinkChunk19,partialLinkChunk20,partialLinkChunk21,partialLinkChunk22,partialLinkChunk23,partialLinkChunk24,partialLinkChunk25,partialLinkChunk26,partialLinkChunk27,partialLinkChunk28,partialLinkChunk29,partialLinkChunk30,partialLinkChunk31,partialLinkChunk32,partialLinkChunk33]
def partialLink (n : Nat) : Nat := ((partialLinkChunks[n/32]?.getD #[])[n % 32]?).getD 0

def unpackTape : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,w => if w = 0 then [] else ((w &&& 4095)-1) :: unpackTape n (w >>> 12)

def unpackFaces : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,w => if w = 0 then [] else ((w &&& 255)-1) :: unpackFaces n (w >>> 8)

def lookupLink : Nat → Nat → Nat → Nat
  | 0,_,_ => 0
  | n+1,w,c => if w = 0 then 0 else
      if (w &&& 4095) = c then (w >>> 12) &&& 65535 else lookupLink n (w >>> 28) c

def capOf (part : Bool) := if part then 13 else 14
def countOf (part : Bool) := if part then 1086 else 1055

def tapeFor (part : Bool) (idx : Nat) := unpackTape 9 ((if part then partialTape else deadTape) idx)
def facesFor (part : Bool) (idx : Nat) := unpackFaces 18 ((if part then partialCash else deadCash) idx)
def linksFor (part : Bool) (idx : Nat) := (if part then partialLink else deadLink) idx

def StateNo (part : Bool) (idx : Nat) :=
  let t := tapeFor part idx
  NoSuffix (capOf part-t.length) (runPins (rootBase part) t).toFinset

def linkOK (part : Bool) (d : Nat) (w : List Sig) (hint : Nat) : Bool :=
  let r := (hint-1) % 16
  let n := (hint-1) / 16
  let t := tapeFor part n
  hint != 0 && n < countOf part && r < rotCount part &&
    t.length == d+1 && w.isPerm (runPins (rotBase part r) t)

lemma link_sound {part d w hint} (hdepth : d < capOf part)
    (h : linkOK part d w hint = true)
    (ih : ∀ j < countOf part, (tapeFor part j).length = d+1 → StateNo part j) :
    NoSuffix (capOf part-d-1) w.toFinset := by
  simp only [linkOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  obtain ⟨⟨⟨⟨_,hcount⟩,hrot⟩,length⟩,perm⟩ := h
  have transfer := liftedNo hrot (ih _ hcount length)
  have se : w.toFinset = (runPins (rotBase part ((hint-1)%16)) (tapeFor part ((hint-1)/16))).toFinset := by
    ext a
    exact List.mem_toFinset.trans ((List.isPerm_iff.1 perm).mem_iff.trans List.mem_toFinset.symm)
  rw [se]
  have eq : capOf part-d-1 = capOf part-(tapeFor part ((hint-1)/16)).length := by omega
  rw [eq]
  exact transfer

abbrev Rate := Nat × List Tagged

def prices (part : Bool) (t cols : List Nat) : List Rate :=
  cols.map fun j => (j,track (costMask j) (rootBase part) t)

def pricesOK (part : Bool) (k d c : Nat) (rs : List Rate) :=
  rs.any (fun p => p.1 < 216 && canUse part p.1 && priceMove k d p.1 c p.2)

lemma prices_sound {part k t c cols} (nd : (after (runPins (rootBase part) t) c).Nodup)
    (h : pricesOK part k t.length c (prices part t cols) = true) :
    NoSuffix k (after (runPins (rootBase part) t) c).toFinset := by
  obtain ⟨v,hv,h⟩ := List.any_eq_true.mp h
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
  obtain ⟨⟨hj1,hj2⟩,hp⟩ := (Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
  exact priceMove_sound (of_decide_eq_true hj1) hj2 nd hp

def localOK (part : Bool) (idx : Nat) :=
  let t := tapeFor part idx
  let base := rootBase part
  let v := runPins base t
  let d := t.length
  let k := capOf part-d-1
  let rs := prices part t (facesFor part idx)
  let refs := linksFor part idx
  decide (v.Nodup ∧ v.length ≤ 16 ∧ d < capOf part) &&
    quickNode k v (fun c =>
      let j := lookupLink 40 refs c
      (j != 0 && linkOK part d (after v c) j) || pricesOK part k d c rs)

theorem local_sound {part idx} (ok : localOK part idx = true)
    (ih : ∀ j < countOf part, (tapeFor part j).length = (tapeFor part idx).length+1 → StateNo part j) :
    StateNo part idx := by
  let t := tapeFor part idx
  let v := runPins (rootBase part) t
  let k := capOf part-t.length-1
  obtain ⟨checks,run⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨nd,within,depth⟩ := of_decide_eq_true checks
  change t.length < capOf part at depth
  have no := node_sound nd within (quickNode_ok nd within run) (by
    intro c hnd h
    rcases Bool.or_eq_true_iff.mp h with hl | hc
    · exact link_sound depth (Bool.and_eq_true_iff.mp hl).2 ih
    · exact prices_sound hnd hc)
  have eq : k+1=capOf part-t.length := by dsimp [k]; omega
  change NoSuffix (capOf part-t.length) v.toFinset
  rw [←eq]
  exact no

theorem region_sound (part : Bool) (checked : ∀ i < countOf part, localOK part i = true) :
    ∀ i < countOf part, StateNo part i := by
  suffices ∀ k i, capOf part-(tapeFor part i).length = k → i < countOf part → StateNo part i from
    fun i hi => this _ i rfl hi
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i eq hi
    have test := checked i hi
    have limits := of_decide_eq_true (Bool.and_eq_true_iff.mp test).1
    have len : (tapeFor part i).length < capOf part := limits.2.2
    apply local_sound test
    intro j hj next
    exact ih _ (by omega : capOf part - (tapeFor part j).length < k) j rfl hj

def spanD := Theta.span (localOK false)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem allD : spanD 1055 0 = true := (@Theta.span_join (localOK false) 1024 0 31 (@Theta.span_join (localOK false) 512 0 512 (@Theta.span_join (localOK false) 256 0 256 (@Theta.span_join (localOK false) 128 0 128 (@Theta.span_join (localOK false) 64 0 64 (@Theta.span_join (localOK false) 32 0 32 (@Theta.span_join (localOK false) 16 0 16 (@Theta.span_join (localOK false) 8 0 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 16 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 32 16 (@Theta.span_join (localOK false) 8 32 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 48 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK false) 32 64 32 (@Theta.span_join (localOK false) 16 64 16 (@Theta.span_join (localOK false) 8 64 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 80 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 96 16 (@Theta.span_join (localOK false) 8 96 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 112 8 (by decide +kernel) (by decide +kernel))))) (@Theta.span_join (localOK false) 64 128 64 (@Theta.span_join (localOK false) 32 128 32 (@Theta.span_join (localOK false) 16 128 16 (@Theta.span_join (localOK false) 8 128 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 144 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 160 16 (@Theta.span_join (localOK false) 8 160 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 176 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK false) 32 192 32 (@Theta.span_join (localOK false) 16 192 16 (@Theta.span_join (localOK false) 8 192 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 208 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 224 16 (@Theta.span_join (localOK false) 8 224 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 240 8 (by decide +kernel) (by decide +kernel)))))) (@Theta.span_join (localOK false) 128 256 128 (@Theta.span_join (localOK false) 64 256 64 (@Theta.span_join (localOK false) 32 256 32 (@Theta.span_join (localOK false) 16 256 16 (@Theta.span_join (localOK false) 8 256 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 272 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 288 16 (@Theta.span_join (localOK false) 8 288 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 304 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK false) 32 320 32 (@Theta.span_join (localOK false) 16 320 16 (@Theta.span_join (localOK false) 8 320 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 336 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 352 16 (@Theta.span_join (localOK false) 8 352 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 368 8 (by decide +kernel) (by decide +kernel))))) (@Theta.span_join (localOK false) 64 384 64 (@Theta.span_join (localOK false) 32 384 32 (@Theta.span_join (localOK false) 16 384 16 (@Theta.span_join (localOK false) 8 384 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 400 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 416 16 (@Theta.span_join (localOK false) 8 416 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 432 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK false) 32 448 32 (@Theta.span_join (localOK false) 16 448 16 (@Theta.span_join (localOK false) 8 448 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 464 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 480 16 (@Theta.span_join (localOK false) 8 480 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 496 8 (by decide +kernel) (by decide +kernel))))))) (@Theta.span_join (localOK false) 256 512 256 (@Theta.span_join (localOK false) 128 512 128 (@Theta.span_join (localOK false) 64 512 64 (@Theta.span_join (localOK false) 32 512 32 (@Theta.span_join (localOK false) 16 512 16 (@Theta.span_join (localOK false) 8 512 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 528 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 544 16 (@Theta.span_join (localOK false) 8 544 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 560 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK false) 32 576 32 (@Theta.span_join (localOK false) 16 576 16 (@Theta.span_join (localOK false) 8 576 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 592 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 608 16 (@Theta.span_join (localOK false) 8 608 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 624 8 (by decide +kernel) (by decide +kernel))))) (@Theta.span_join (localOK false) 64 640 64 (@Theta.span_join (localOK false) 32 640 32 (@Theta.span_join (localOK false) 16 640 16 (@Theta.span_join (localOK false) 8 640 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 656 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 672 16 (@Theta.span_join (localOK false) 8 672 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 688 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK false) 32 704 32 (@Theta.span_join (localOK false) 16 704 16 (@Theta.span_join (localOK false) 8 704 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 720 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 736 16 (@Theta.span_join (localOK false) 8 736 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 752 8 (by decide +kernel) (by decide +kernel)))))) (@Theta.span_join (localOK false) 128 768 128 (@Theta.span_join (localOK false) 64 768 64 (@Theta.span_join (localOK false) 32 768 32 (@Theta.span_join (localOK false) 16 768 16 (@Theta.span_join (localOK false) 8 768 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 784 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 800 16 (@Theta.span_join (localOK false) 8 800 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 816 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK false) 32 832 32 (@Theta.span_join (localOK false) 16 832 16 (@Theta.span_join (localOK false) 8 832 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 848 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 864 16 (@Theta.span_join (localOK false) 8 864 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 880 8 (by decide +kernel) (by decide +kernel))))) (@Theta.span_join (localOK false) 64 896 64 (@Theta.span_join (localOK false) 32 896 32 (@Theta.span_join (localOK false) 16 896 16 (@Theta.span_join (localOK false) 8 896 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 912 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 928 16 (@Theta.span_join (localOK false) 8 928 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 944 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK false) 32 960 32 (@Theta.span_join (localOK false) 16 960 16 (@Theta.span_join (localOK false) 8 960 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 976 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK false) 16 992 16 (@Theta.span_join (localOK false) 8 992 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 1008 8 (by decide +kernel) (by decide +kernel)))))))) (@Theta.span_join (localOK false) 16 1024 15 (@Theta.span_join (localOK false) 8 1024 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK false) 8 1040 7 (by decide +kernel) (by decide +kernel))))

theorem rootD : NoSuffix 14 (rootBase false).toFinset := by
  have h := region_sound false (fun i hi => Theta.span_ok allD i (Nat.zero_le _) hi) 0 (by decide)
  have eq : tapeFor false 0 = [] := by decide +kernel
  simpa only [StateNo,eq,List.length_nil,Nat.sub_zero,runPins,List.foldl_nil,show capOf false = 14 from rfl] using h

def spanP := Theta.span (localOK true)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem allP : spanP 1086 0 = true := (@Theta.span_join (localOK true) 1024 0 62 (@Theta.span_join (localOK true) 512 0 512 (@Theta.span_join (localOK true) 256 0 256 (@Theta.span_join (localOK true) 128 0 128 (@Theta.span_join (localOK true) 64 0 64 (@Theta.span_join (localOK true) 32 0 32 (@Theta.span_join (localOK true) 16 0 16 (@Theta.span_join (localOK true) 8 0 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 16 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 32 16 (@Theta.span_join (localOK true) 8 32 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 48 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK true) 32 64 32 (@Theta.span_join (localOK true) 16 64 16 (@Theta.span_join (localOK true) 8 64 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 80 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 96 16 (@Theta.span_join (localOK true) 8 96 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 112 8 (by decide +kernel) (by decide +kernel))))) (@Theta.span_join (localOK true) 64 128 64 (@Theta.span_join (localOK true) 32 128 32 (@Theta.span_join (localOK true) 16 128 16 (@Theta.span_join (localOK true) 8 128 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 144 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 160 16 (@Theta.span_join (localOK true) 8 160 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 176 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK true) 32 192 32 (@Theta.span_join (localOK true) 16 192 16 (@Theta.span_join (localOK true) 8 192 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 208 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 224 16 (@Theta.span_join (localOK true) 8 224 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 240 8 (by decide +kernel) (by decide +kernel)))))) (@Theta.span_join (localOK true) 128 256 128 (@Theta.span_join (localOK true) 64 256 64 (@Theta.span_join (localOK true) 32 256 32 (@Theta.span_join (localOK true) 16 256 16 (@Theta.span_join (localOK true) 8 256 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 272 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 288 16 (@Theta.span_join (localOK true) 8 288 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 304 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK true) 32 320 32 (@Theta.span_join (localOK true) 16 320 16 (@Theta.span_join (localOK true) 8 320 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 336 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 352 16 (@Theta.span_join (localOK true) 8 352 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 368 8 (by decide +kernel) (by decide +kernel))))) (@Theta.span_join (localOK true) 64 384 64 (@Theta.span_join (localOK true) 32 384 32 (@Theta.span_join (localOK true) 16 384 16 (@Theta.span_join (localOK true) 8 384 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 400 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 416 16 (@Theta.span_join (localOK true) 8 416 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 432 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK true) 32 448 32 (@Theta.span_join (localOK true) 16 448 16 (@Theta.span_join (localOK true) 8 448 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 464 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 480 16 (@Theta.span_join (localOK true) 8 480 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 496 8 (by decide +kernel) (by decide +kernel))))))) (@Theta.span_join (localOK true) 256 512 256 (@Theta.span_join (localOK true) 128 512 128 (@Theta.span_join (localOK true) 64 512 64 (@Theta.span_join (localOK true) 32 512 32 (@Theta.span_join (localOK true) 16 512 16 (@Theta.span_join (localOK true) 8 512 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 528 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 544 16 (@Theta.span_join (localOK true) 8 544 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 560 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK true) 32 576 32 (@Theta.span_join (localOK true) 16 576 16 (@Theta.span_join (localOK true) 8 576 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 592 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 608 16 (@Theta.span_join (localOK true) 8 608 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 624 8 (by decide +kernel) (by decide +kernel))))) (@Theta.span_join (localOK true) 64 640 64 (@Theta.span_join (localOK true) 32 640 32 (@Theta.span_join (localOK true) 16 640 16 (@Theta.span_join (localOK true) 8 640 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 656 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 672 16 (@Theta.span_join (localOK true) 8 672 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 688 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK true) 32 704 32 (@Theta.span_join (localOK true) 16 704 16 (@Theta.span_join (localOK true) 8 704 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 720 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 736 16 (@Theta.span_join (localOK true) 8 736 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 752 8 (by decide +kernel) (by decide +kernel)))))) (@Theta.span_join (localOK true) 128 768 128 (@Theta.span_join (localOK true) 64 768 64 (@Theta.span_join (localOK true) 32 768 32 (@Theta.span_join (localOK true) 16 768 16 (@Theta.span_join (localOK true) 8 768 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 784 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 800 16 (@Theta.span_join (localOK true) 8 800 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 816 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK true) 32 832 32 (@Theta.span_join (localOK true) 16 832 16 (@Theta.span_join (localOK true) 8 832 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 848 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 864 16 (@Theta.span_join (localOK true) 8 864 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 880 8 (by decide +kernel) (by decide +kernel))))) (@Theta.span_join (localOK true) 64 896 64 (@Theta.span_join (localOK true) 32 896 32 (@Theta.span_join (localOK true) 16 896 16 (@Theta.span_join (localOK true) 8 896 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 912 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 928 16 (@Theta.span_join (localOK true) 8 928 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 944 8 (by decide +kernel) (by decide +kernel)))) (@Theta.span_join (localOK true) 32 960 32 (@Theta.span_join (localOK true) 16 960 16 (@Theta.span_join (localOK true) 8 960 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 976 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 992 16 (@Theta.span_join (localOK true) 8 992 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 1008 8 (by decide +kernel) (by decide +kernel)))))))) (@Theta.span_join (localOK true) 32 1024 30 (@Theta.span_join (localOK true) 16 1024 16 (@Theta.span_join (localOK true) 8 1024 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 1040 8 (by decide +kernel) (by decide +kernel))) (@Theta.span_join (localOK true) 16 1056 14 (@Theta.span_join (localOK true) 8 1056 8 (by decide +kernel) (by decide +kernel)) (@Theta.span_join (localOK true) 8 1072 6 (by decide +kernel) (by decide +kernel)))))

theorem rootP : NoSuffix 13 (rootBase true).toFinset := by
  have h := region_sound true (fun i hi => Theta.span_ok allP i (Nat.zero_le _) hi) 0 (by decide)
  have eq : tapeFor true 0 = [] := by decide +kernel
  simpa only [StateNo,eq,List.length_nil,Nat.sub_zero,runPins,List.foldl_nil,show capOf true = 13 from rfl] using h

theorem parentBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hf hfirst he
  by_contra! hs
  obtain ⟨k,t,S,hk,hl,hS⟩ := suffix_bound C hf hfirst (fun x => congrFun he x) (by omega)
  exact splitRoot hl hk hS rootD rootP

end PEqualNP.Outside.L_meta_1791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_1791 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro operands arity tail fan budget
  by_contra! computes
  let first : Gate := ⟨GateOp.and, [0, 1]⟩
  let second : Gate := ⟨GateOp.and, operands⟩
  let full : Circuit := ⟨first :: second :: tail.gates, tail.output⟩
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have firstStep (x : Fin 9 → Bool) :
      step (List.ofFn x) first = List.ofFn x ++ [x 0 && x 1] := by
    simp [step,first,GateOp.eval]
  have keep (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
      · simp [step]; omega
  have bound := PEqualNP.Outside.L_meta_1791.parentBound full (by
    intro g hg
    change g ∈ first :: second :: tail.gates at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [first]
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp [second], arity⟩
    · exact fan g hg) (by
    intro x
    change ((second :: tail.gates).foldl step (step (List.ofFn x) first)).getD 9 false = _
    rw [firstStep, keep]
    · simp
    · simp) (by
    funext x
    change (tail.gates.foldl step (step (step (List.ofFn x) first) second)).getD tail.output false = _
    rw [firstStep]
    exact Classical.not_not.mp (computes x))
  change 16 ≤ (first :: second :: tail.gates).length at bound
  change tail.gates.length ≤ 13 at budget
  simp at bound
  omega
