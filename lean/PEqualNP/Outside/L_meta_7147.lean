import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7147

abbrev V (n : Nat) := Bool × Fin n
abbrev Row (n : Nat) := Finset (V n)

-- Expressions give a common interpretation to wires before and after pinning levels to zero.
inductive E (n : Nat) where
  | var (v : V n)
  | lit (b : Bool)
  | comb (op : Bool) (l r : E n)
deriving DecidableEq

def boolGate (op l r : Bool) := if op then l || r else l && r

def ev {n : Nat} (z : Row n) : E n → Bool
  | .var v => decide (v∈z)
  | .lit b => b
  | .comb op l r => boolGate op (ev z l) (ev z r)

def clip {n : Nat} (I : Finset (Fin n)) (z : Row n) := z.filter (fun v => v.2∈I)
def value {n : Nat} (I : Finset (Fin n)) (e : E n) (z : Row n) := ev (clip I z) e
def Fixed {n : Nat} (I : Finset (Fin n)) (e : E n) := ∀ z, value I e z=value I e ∅
def Agrees {n : Nat} (S x y : Row n) := ∀ v∈S, v∈x ↔ v∈y

open scoped Classical in
noncomputable def supp {n : Nat} (I : Finset (Fin n)) : E n → Row n
  | .var v => if v.2∈I then {v} else ∅
  | .lit _ => ∅
  | .comb op l r => if Fixed I (.comb op l r) then ∅ else supp I l ∪ supp I r

lemma supp_fixed {n : Nat} {I : Finset (Fin n)} {e : E n} (h : Fixed I e) : supp I e=∅ := by
  classical
  cases e with
  | lit b => rfl
  | comb op l r => simp [supp,h]
  | var v =>
    by_cases hv : v.2∈I
    · have bad := h {v}
      simp [value,ev,clip,hv] at bad
    · simp [supp,hv]

lemma eval_supp {n : Nat} (I : Finset (Fin n)) (e : E n) {x y : Row n}
    (h : Agrees (supp I e) x y) : value I e x=value I e y := by
  classical
  induction e with
  | lit b => rfl
  | var v =>
    by_cases hv : v.2∈I
    · have same := h v (by simp [supp,hv])
      simp [value,clip,ev,hv,same]
    · simp [value,ev,clip,hv]
  | comb op l r il ir =>
    by_cases fix : Fixed I (.comb op l r)
    · exact (fix x).trans (fix y).symm
    · have hl := il (fun v hv => h v (by simp [supp,fix,hv]))
      have hr := ir (fun v hv => h v (by simp [supp,fix,hv]))
      change boolGate op (value I l x) (value I r x)=boolGate op (value I l y) (value I r y)
      rw [hl,hr]

lemma supp_active {n : Nat} {I : Finset (Fin n)} {e : E n} {v : V n} (h : v∈supp I e) : v.2∈I := by
  classical
  induction e with
  | lit b => simp [supp] at h
  | var w =>
    by_cases hw : w.2∈I <;> simp [supp,hw] at h
    subst v; exact hw
  | comb op l r il ir =>
    by_cases fix : Fixed I (.comb op l r) <;> simp [supp,fix] at h
    exact h.elim il ir

lemma value_clip {n : Nat} {I J : Finset (Fin n)} (sub : J⊆I) (e : E n) (z : Row n) :
    value J e z=value I e (clip J z) := by
  have eq : clip I (clip J z)=clip J z := by
    ext v
    simp only [clip,Finset.mem_filter]
    exact ⟨And.left,fun h => ⟨h,sub h.2⟩⟩
  simp [value,eq]

lemma fixed_sub {n : Nat} {I J : Finset (Fin n)} (sub : J⊆I) {e : E n} (h : Fixed I e) :
    Fixed J e := by
  intro z
  rw [value_clip sub e z,value_clip sub e ∅,h (clip J z),h (clip J ∅)]

lemma fixed_off_support {n : Nat} {I J : Finset (Fin n)} (sub : J⊆I) (e : E n)
    (off : ∀ v∈supp I e, v.2∉J) : Fixed J e := by
  intro z
  rw [value_clip sub e z,value_clip sub e ∅]
  apply eval_supp
  intro v hv
  simp [clip,off v hv]

-- A gate consumes its two operands. Reusing an operand requires a copy recorded in the list.
inductive Run {n : Nat} : Multiset (E n) → E n → List (E n) → Prop where
  | stop {S f} (mem : f∈S) : Run S f []
  | join {S f cs l r} (op : Bool) (next : Run (E.comb op l r ::ₘ S) f cs) : Run (l ::ₘ r ::ₘ S) f cs
  | dup {S f cs a} (next : Run (a ::ₘ a ::ₘ S) f cs) : Run (a ::ₘ S) f (a::cs)

lemma run_agree {n : Nat} {S : Multiset (E n)} {f cs} (run : Run S f cs)
    (I : Finset (Fin n)) (x y : Row n) (agree : ∀ e∈S,value I e x=value I e y) :
    value I f x=value I f y := by
  induction run with
  | stop mem => exact agree _ mem
  | @join S f cs l r op next ih =>
    apply ih
    intro e he
    rcases Multiset.mem_cons.mp he with rfl|h
    · change boolGate op (value I l x) (value I r x)=boolGate op (value I l y) (value I r y)
      rw [agree l (by simp),agree r (by simp)]
    · exact agree _ (by simp [h])
  | @dup S f cs a next ih =>
    apply ih
    intro e he
    exact agree _ (by simpa only [Multiset.mem_cons,or_self_left] using he)

def Spec {n : Nat} (I : Finset (Fin n)) (f : E n) :=
  value I f ∅=false ∧ (∀ v : V n, v.2∈I → value I f {v}=false) ∧
  ∀ a∈I, ∀ b∈I, value I f {(false,a),(true,b)}=decide (a≤b)

lemma clip_eq_of {n : Nat} (I : Finset (Fin n)) (z : Row n) (hz : ∀ v∈z,v.2∈I) : clip I z=z := by
  ext v; simp only [clip,Finset.mem_filter]; exact ⟨And.left,fun h => ⟨h,hz v h⟩⟩

lemma spec_sub {n : Nat} {I J : Finset (Fin n)} (sub : J⊆I) {f : E n} (h : Spec I f) : Spec J f := by
  refine ⟨?_,?_,?_⟩
  · rw [value_clip sub]; simpa [clip] using h.1
  · intro v hv; rw [value_clip sub]; rw [clip_eq_of _ _ (by simpa using hv)]; exact h.2.1 v (sub hv)
  · intro a ha b hb; rw [value_clip sub]; rw [clip_eq_of _ _ (by intro v hv; simp at hv; rcases hv with rfl|rfl <;> assumption)]; exact h.2.2 a (sub ha) b (sub hb)

def Pos {n : Nat} (v w : V n) := (v.1=false ∧ w.1=true ∧ v.2≤w.2) ∨
  (w.1=false ∧ v.1=true ∧ w.2≤v.2)

lemma spec_pos {n : Nat} {I : Finset (Fin n)} {f : E n} (h : Spec I f) {v w : V n}
    (vi : v.2∈I) (wi : w.2∈I) (p : Pos v w) : value I f {v,w}=true := by
  obtain ⟨b,a⟩ := v
  obtain ⟨d,c⟩ := w
  rcases p with ⟨rfl,rfl,le⟩|⟨rfl,rfl,le⟩
  · simpa [le] using h.2.2 a vi c wi
  · simpa [le,Finset.pair_comm] using h.2.2 c wi a vi

def Small {n : Nat} (S : Row n) :=
  (∀ a b : Fin n, (false,a)∈S → (false,b)∈S → a=b) ∧
  (∀ a b : Fin n, (true,a)∈S → (true,b)∈S → a=b) ∧
  ∀ a b : Fin n, (false,a)∈S → (true,b)∈S → b<a

lemma small_sub {n : Nat} {S T : Row n} (h : Small S) (sub : T⊆S) : Small T :=
  ⟨fun a b ha hb => h.1 a b (sub ha) (sub hb),fun a b ha hb => h.2.1 a b (sub ha) (sub hb),
    fun a b ha hb => h.2.2 a b (sub ha) (sub hb)⟩

lemma small_empty {n : Nat} : Small (∅ : Row n) := by simp [Small]
lemma small_single {n : Nat} (v : V n) : Small {v} := by
  rcases v with ⟨b,i⟩; cases b <;> simp [Small]

lemma outside_two {n : Nat} (I : Finset (Fin n)) (hm : 2≤I.card) {S T : Row n}
    (hs : Small S) (ht : Small T) : ∃ v : V n, v.2∈I ∧ v∉S∪T := by
  have two : ∃ a∈I, ∃ b∈I, a<b := by
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (by omega : 1<I.card)
    rcases lt_or_gt_of_ne ne with h|h
    · exact ⟨a,ha,b,hb,h⟩
    · exact ⟨b,hb,a,ha,h⟩
  obtain ⟨a,ha,b,hb,ab⟩ := two
  by_contra! none
  have x := none (false,a) ha
  have y := none (true,a) ha
  have z := none (true,b) hb
  simp only [Finset.mem_union] at x y z
  rcases x with x|x
  · have ya : (true,a)∉S := fun h => (lt_irrefl _) (hs.2.2 a a x h)
    have yb : (true,b)∉S := fun h => (not_lt_of_ge ab.le) (hs.2.2 a b x h)
    exact ab.ne (ht.2.1 a b (y.resolve_left ya) (z.resolve_left yb))
  · have ya : (true,a)∉T := fun h => (lt_irrefl _) (ht.2.2 a a x h)
    have yb : (true,b)∉T := fun h => (not_lt_of_ge ab.le) (ht.2.2 a b x h)
    exact ab.ne (hs.2.1 a b (y.resolve_right ya) (z.resolve_right yb))

-- The diagonal pairs and the ordering between levels make the positive graph connected.
lemma crossing {n : Nat} (I : Finset (Fin n)) (S : Row n) (active : ∀ v∈S,v.2∈I)
    (inside : S.Nonempty) (outside : ∃ v : V n,v.2∈I ∧ v∉S) :
    ∃ u∈S, ∃ w : V n, w.2∈I ∧ w∉S ∧ Pos u w := by
  by_contra! none
  have eq (i j : Fin n) (hi : i∈I) (hj : j∈I) (le : i≤j) :
      (false,i)∈S ↔ (true,j)∈S := by
    constructor
    · intro x; by_contra no
      exact none (false,i) x (true,j) hj no (Or.inl ⟨rfl,rfl,le⟩)
    · intro x; by_contra no
      exact none (true,j) x (false,i) hi no (Or.inr ⟨rfl,rfl,le⟩)
  have any (i j : Fin n) (hi : i∈I) (hj : j∈I) : (false,i)∈S ↔ (false,j)∈S := by
    rcases le_total i j with le|le
    · exact (eq i j hi hj le).trans (eq j j hj hj le_rfl).symm
    · exact ((eq j i hj hi le).trans (eq i i hi hi le_rfl).symm).symm
  obtain ⟨⟨b,i⟩,hs⟩ := inside
  obtain ⟨⟨c,j⟩,hj,hno⟩ := outside
  have hi := active (b,i) hs
  have xi : (false,i)∈S := by cases b with
    | false => exact hs
    | true => exact (eq i i hi hi le_rfl).mpr hs
  have xj := (any i j hi hj).mp xi
  cases c with
  | false => exact hno xj
  | true => exact hno ((eq j j hj hj le_rfl).mp xj)

def Private {n : Nat} (I : Finset (Fin n)) (f e : E n) (S : Row n) :=
  ∀ x y : Row n, (∀ v, v∉S → (v∈x ↔ v∈y)) → value I e x=value I e y → value I f x=value I f y

lemma pair_local {n : Nat} {I : Finset (Fin n)} {e : E n} {a b : V n}
    (out : b∉supp I e) : value I e {a,b}=value I e {a} := by
  apply eval_supp
  intro v hv
  have ne : v≠b := fun h => out (h ▸ hv)
  simp [ne]

lemma single_out {n : Nat} {I : Finset (Fin n)} {e : E n} {b : V n}
    (out : b∉supp I e) : value I e {b}=value I e ∅ := by
  apply eval_supp
  intro v hv
  have ne : v≠b := fun h => out (h ▸ hv)
  simp [ne]

-- A proper set of private inputs can reach the rest of the computation through one bit.
-- A crossing edge distinguishes its inside singleton from the empty input. Both are rejected
-- in isolation, so no internal edge can be accepted. Distinct same-side singletons would
-- then have to look identical to their diagonal neighbors outside the region.
theorem cut_small {n : Nat} (I : Finset (Fin n)) (f e : E n) (spec : Spec I f)
    (priv : Private I f e (supp I e)) (outside : ∃ v : V n,v.2∈I ∧ v∉supp I e) :
    Small (supp I e) := by
  classical
  let S := supp I e
  by_cases emp : S=∅
  · change Small S; rw [emp]; exact small_empty
  have active (v : V n) (h : v∈S) := supp_active h
  have flip (u w : V n) (hu : u∈S) (hw : w∉S) (hi : w.2∈I) (edge : Pos u w) :
      value I e {u}≠value I e ∅ := by
    intro eq
    have same : value I f {u,w}=value I f {w} := by
      apply priv
      · intro v hv
        have ne : v≠u := fun h => hv (h ▸ hu)
        simp [ne]
      · exact (pair_local hw).trans (eq.trans (single_out hw).symm)
    have yes := spec_pos spec (active _ hu) hi edge
    rw [yes,spec.2.1 w hi] at same
    contradiction
  obtain ⟨u,hu,w,wi,wo,ue⟩ := crossing I S active (Finset.nonempty_iff_ne_empty.mpr emp) outside
  have switch := flip u w hu wo wi ue
  have internal (z : Row n) (hz : z⊆S) : value I f z=false := by
    have cmp : value I e z=value I e ∅ ∨ value I e z=value I e {u} := by
      revert switch; cases value I e z <;> cases value I e ∅ <;> cases value I e {u} <;> decide
    rcases cmp with cmp|cmp
    · apply (priv z ∅ (fun v hv => by simp [show v∉z from fun h => hv (hz h)]) cmp).trans spec.1
    · apply (priv z {u} (fun v hv => by
        have ne : v≠u := fun h => hv (h ▸ hu)
        simp [ne,show v∉z from fun h => hv (hz h)]) cmp).trans (spec.2.1 u (active u hu))
  have barred (a b : Fin n) (x : (false,a)∈S) (y : (true,b)∈S) : b<a := by
    by_contra! le
    have no := internal {(false,a),(true,b)} (by intro v hv; simp at hv; rcases hv with rfl|rfl <;> assumption)
    have yes := spec.2.2 a (active _ x) b (active _ y)
    simp [le,no] at yes
  have vflip (v : V n) (h : v∈S) : value I e {v}≠value I e ∅ := by
    rcases v with ⟨b,i⟩
    cases b with
    | false => exact flip (false,i) (true,i) h (fun y => (lt_irrefl _) (barred i i h y)) (active (false,i) h) (Or.inl ⟨rfl,rfl,le_rfl⟩)
    | true => exact flip (true,i) (false,i) h (fun x => (lt_irrefl _) (barred i i x h)) (active (true,i) h) (Or.inr ⟨rfl,rfl,le_rfl⟩)
  have twins (a b c : V n) (ha : a∈S) (hb : b∈S) (hc : c∉S) :
      value I f {a,c}=value I f {b,c} := by
    apply priv
    · intro v hv
      have na : v≠a := fun h => hv (h ▸ ha)
      have nb : v≠b := fun h => hv (h ▸ hb)
      simp [na,nb]
    · rw [pair_local hc,pair_local hc]
      have one := vflip a ha; have two := vflip b hb
      revert one two; cases value I e {a} <;> cases value I e {b} <;> cases value I e ∅ <;> decide
  have left {a b : Fin n} (lt : a<b) (x : (false,a)∈S) (y : (false,b)∈S) : False := by
    have t := twins _ _ (true,a) x y (fun h => (lt_irrefl _) (barred a a x h))
    rw [spec.2.2 a (active _ x) a (active _ x),spec.2.2 b (active _ y) a (active _ x)] at t
    simp [not_le_of_gt lt] at t
  have right {a b : Fin n} (lt : a<b) (x : (true,a)∈S) (y : (true,b)∈S) : False := by
    have t := twins _ _ (false,b) x y (fun h => (lt_irrefl _) (barred b b h y))
    rw [Finset.pair_comm (true,a),Finset.pair_comm (true,b),
      spec.2.2 b (active _ y) a (active _ x),spec.2.2 b (active _ y) b (active _ y)] at t
    simp [not_le_of_gt lt] at t
  exact ⟨fun a b x y => le_antisymm (le_of_not_gt (fun h => left h y x)) (le_of_not_gt (fun h => left h x y)),
    fun a b x y => le_antisymm (le_of_not_gt (fun h => right h y x)) (le_of_not_gt (fun h => right h x y)),barred⟩

def Sep {n : Nat} (I : Finset (Fin n)) (A : Multiset (E n)) :=
  ∀ v : V n, (A.filter (fun e => v∈supp I e)).card≤1

lemma comb_sub {n : Nat} (I : Finset (Fin n)) (op : Bool) (l r : E n) :
    supp I (.comb op l r) ⊆ supp I l ∪ supp I r := by
  classical
  by_cases h : Fixed I (.comb op l r) <;> simp [supp,h]

lemma hit_cons {n : Nat} (I : Finset (Fin n)) (v : V n) (a : E n) (A : Multiset (E n)) :
    ((a ::ₘ A).filter (fun e => v∈supp I e)).card =
    (A.filter (fun e => v∈supp I e)).card+(if v∈supp I a then 1 else 0) := by
  by_cases h : v∈supp I a
  · rw [Multiset.filter_cons_of_pos (p:=fun e => v∈supp I e) A h,Multiset.card_cons,if_pos h]
  · rw [Multiset.filter_cons_of_neg (p:=fun e => v∈supp I e) A h,if_neg h,Nat.add_zero]

lemma sep_join {n : Nat} {I : Finset (Fin n)} {A : Multiset (E n)} {l r : E n}
    (h : Sep I (l ::ₘ r ::ₘ A)) (op : Bool) : Sep I (.comb op l r ::ₘ A) := by
  intro v
  specialize h v
  have inc := @comb_sub n I op l r
  simp only [hit_cons] at h ⊢
  by_cases p : v∈supp I l <;> by_cases q : v∈supp I r <;> by_cases c : v∈supp I (.comb op l r) <;>
    simp only [p,q,c,ite_true,ite_false] at h ⊢ <;> first | omega | exact False.elim (by simpa [p,q] using inc c)

lemma private_head {n : Nat} {I : Finset (Fin n)} {A : Multiset (E n)} {e f cs}
    (run : Run (e ::ₘ A) f cs) (sep : Sep I (e ::ₘ A)) : Private I f e (supp I e) := by
  intro x y other same
  apply run_agree run
  intro a ha
  rcases Multiset.mem_cons.mp ha with rfl|ha
  · exact same
  apply eval_supp
  intro v hv
  apply other
  intro he
  have ct := sep v
  have pos : 0<(A.filter (fun b => v∈supp I b)).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨a,Multiset.mem_filter.mpr ⟨ha,hv⟩⟩
  rw [hit_cons,if_pos he] at ct
  omega

lemma essential_supp {n : Nat} {I : Finset (Fin n)} {f : E n} (spec : Spec I f)
    (v : V n) (act : v.2∈I) : v∈supp I f := by
  by_contra h
  rcases v with ⟨b,i⟩
  cases b with
  | false =>
    have eq := pair_local (a:=(true,i)) h
    rw [Finset.pair_comm (true,i),spec.2.2 i act i act,spec.2.1 (true,i) act] at eq
    simp at eq
  | true =>
    have eq := pair_local (a:=(false,i)) h
    rw [spec.2.2 i act i act,spec.2.1 (false,i) act] at eq
    simp at eq

-- Until a nonconstant signal is copied, the live supports are disjoint. Each proper
-- support contains at most one vertex of each side, and those two must form a nonedge.
theorem small_copy {n : Nat} {I : Finset (Fin n)} (hm : 2≤I.card) {A : Multiset (E n)} {f cs}
    (run : Run A f cs) (spec : Spec I f) (sep : Sep I A) (small : ∀ e∈A, Small (supp I e)) :
    ∃ e∈cs, ¬Fixed I e ∧ Small (supp I e) := by
  classical
  induction run with
  | stop mem =>
    obtain ⟨v,hv,miss⟩ := outside_two I hm (small _ mem) (small _ mem)
    exact (miss (Finset.mem_union_left _ (essential_supp spec v hv))).elim
  | @join A f cs l r op next ih =>
    have sn := sep_join sep op
    obtain ⟨v,hv,miss⟩ := outside_two I hm (small l (by simp)) (small r (by simp))
    have sh := cut_small I f (.comb op l r) spec (private_head next sn)
      ⟨v,hv,fun h => miss (comb_sub _ _ _ _ h)⟩
    apply ih spec sn
    intro e he
    rcases Multiset.mem_cons.mp he with rfl|h
    · exact sh
    · exact small e (by simp [h])
  | @dup A f cs a next ih =>
    by_cases fixed : Fixed I a
    · have empty := supp_fixed fixed
      have sp : Sep I (a ::ₘ a ::ₘ A) := by
        intro v
        have orig := sep v
        simpa [Multiset.filter_cons,empty] using orig
      obtain ⟨e,he,hf,hs⟩ := ih spec sp (fun u hu => small u (by simpa only [Multiset.mem_cons,or_self_left] using hu))
      exact ⟨e,by simp [he],hf,hs⟩
    · exact ⟨a,by simp,fixed,small a (by simp)⟩

open scoped Classical in
noncomputable def weight {n : Nat} (I : Finset (Fin n)) (cs : List (E n)) :=
  (cs.filter (fun e => decide (¬Fixed I e))).length

lemma weight_sub {n : Nat} {I J : Finset (Fin n)} (sub : J⊆I) (cs : List (E n)) :
    weight J cs≤weight I cs := by
  classical
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    by_cases hi : Fixed I a <;> by_cases hj : Fixed J a
    · simpa [weight,hi,hj] using ih
    · exact (hj (fixed_sub sub hi)).elim
    · simp [weight,hi,hj] at ih ⊢; omega
    · simpa [weight,hi,hj] using ih

lemma weight_strict {n : Nat} {I J : Finset (Fin n)} (sub : J⊆I) {a : E n}
    (old : ¬Fixed I a) (new : Fixed J a) (cs : List (E n)) (mem : a∈cs) :
    weight J cs<weight I cs := by
  classical
  induction cs with
  | nil => simp at mem
  | cons b cs ih =>
    rcases List.mem_cons.mp mem with rfl|later
    · have le := weight_sub sub cs
      simp [weight,old,new] at le ⊢; omega
    · specialize ih later
      by_cases hi : Fixed I b <;> by_cases hj : Fixed J b
      · simpa [weight,hi,hj] using ih
      · exact (hj (fixed_sub sub hi)).elim
      · simp [weight,hi,hj] at ih ⊢; omega
      · simpa [weight,hi,hj] using ih

lemma small_card {n : Nat} {S : Row n} (h : Small S) : S.card≤2 := by
  have inj : Set.InjOn Prod.fst (↑S : Set (V n)) := by
    rintro ⟨b,i⟩ hi ⟨c,j⟩ hj eq
    change b=c at eq; subst c
    cases b with
    | false => exact Prod.ext rfl (h.1 i j hi hj)
    | true => exact Prod.ext rfl (h.2.1 i j hi hj)
  calc
    S.card = (S.image Prod.fst).card := (Finset.card_image_of_injOn inj).symm
    _ ≤ Fintype.card Bool := Finset.card_le_univ _
    _ = 2 := rfl

def Basic {n : Nat} (e : E n) := (∃ v,e=.var v) ∨ ∃ b,e=.lit b

lemma basic_small {n : Nat} (I : Finset (Fin n)) {e : E n} (h : Basic e) : Small (supp I e) := by
  classical
  rcases h with ⟨v,rfl⟩|⟨b,rfl⟩
  · by_cases hv : v.2∈I
    · simpa [supp,hv] using small_single v
    · simpa [supp,hv] using (small_empty (n:=n))
  · exact small_empty

lemma basic_sep {n : Nat} (I : Finset (Fin n)) (A : Finset (E n)) (base : ∀ e∈A,Basic e) : Sep I A.val := by
  classical
  intro v
  change (A.filter (fun e => v∈supp I e)).card≤1
  apply Finset.card_le_one.mpr
  intro e he f hf
  have raw {e : E n} (he : e∈A.filter (fun e => v∈supp I e)) : e=.var v := by
    obtain ⟨ea,ve⟩ := Finset.mem_filter.mp he
    rcases base e ea with ⟨w,rfl⟩|⟨b,rfl⟩
    · by_cases hw : w.2∈I <;> simp [supp,hw] at ve
      subst w; rfl
    · simp [supp] at ve
  exact (raw he).trans (raw hf).symm

-- Pin the levels supporting one small copy. At most two levels disappear and this
-- copy becomes constant. A copy that was already constant stays constant.
theorem copy_lower {n : Nat} (A : Finset (E n)) (base : ∀ e∈A,Basic e) {f cs}
    (run : Run A.val f cs) (I : Finset (Fin n)) (spec : Spec I f) : I.card ≤ 2*weight I cs+1 := by
  classical
  generalize hw : weight I cs=k
  induction k using Nat.strong_induction_on generalizing I with
  | ind k ih =>
    by_cases hm : 2≤I.card
    · obtain ⟨e,mem,old,small⟩ := small_copy hm run spec (basic_sep I A base)
        (fun a ha => basic_small _ (base a ha))
      let D := (supp I e).image Prod.snd
      let J := I \ D
      have sub : J⊆I := Finset.sdiff_subset
      have new : Fixed J e := fixed_off_support sub e (fun v hv => by
        have hD : v.2∈D := Finset.mem_image_of_mem _ hv
        simp [J,hD])
      have lt := weight_strict sub old new cs mem
      have reduced := ih (weight J cs) (by omega) J (spec_sub sub spec) rfl
      have cd : D.card≤2 := Finset.card_image_le.trans (small_card small)
      have bound := Finset.card_sdiff_add_card_inter I D
      have inter : (I∩D).card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
      change J.card+(I∩D).card=I.card at bound
      omega
    · omega


inductive Hist {n : Nat} (base : Finset (E n)) : Finset (E n) → Nat → Prop where
  | init : Hist base base 0
  | skip {S k} (prev : Hist base S k) : Hist base S (k+1)
  | add {S k l r} (prev : Hist base S k) (hl : l∈S) (hr : r∈S) (op : Bool) :
      Hist base (insert (.comb op l r) S) (k+1)

lemma dup_mem {n : Nat} {A : Multiset (E n)} {a f cs} (ha : a∈A) (run : Run (a ::ₘ A) f cs) :
    Run A f (a::cs) := by
  have run' : Run (a ::ₘ a ::ₘ A.erase a) f cs := by simpa only [Multiset.cons_erase ha] using run
  have result := Run.dup run'
  simpa only [Multiset.cons_erase ha] using result

lemma stock {n : Nat} (A extra : Multiset (E n)) {f cs} (sub : ∀ e∈extra,e∈A)
    (run : Run (extra+A) f cs) : ∃ ds, Run A f (ds++cs) ∧ ds.length=extra.card := by
  induction extra using Multiset.induction_on generalizing cs with
  | empty => exact ⟨[],by simpa using run,by simp⟩
  | cons a rest ih =>
    have mem : a∈rest+A := Multiset.mem_add.mpr (Or.inr (sub a (by simp)))
    have go : Run (a ::ₘ (rest+A)) f cs := by simpa using run
    obtain ⟨ds,r,len⟩ := ih (fun e he => sub e (by simp [he])) (dup_mem mem go)
    exact ⟨ds++[a],by simpa using r,by simp [len]⟩

lemma compress {n : Nat} (M : Multiset (E n)) {f cs} (run : Run M f cs) :
    ∃ ds, Run M.toFinset.val f (ds++cs) ∧ M.toFinset.card + ds.length=M.card := by
  let A := M.toFinset.val
  have le : A≤M := Multiset.dedup_le _
  have sum : M-A+A=M := tsub_add_cancel_of_le le
  have used (e : E n) (h : e∈M-A) : e∈A := by
    have : e∈M := Multiset.mem_of_le (tsub_le_self : M-A≤M) h
    simpa [A] using this
  obtain ⟨ds,go,len⟩ := stock A (M-A) used (sum ▸ run)
  refine ⟨ds,go,?_⟩
  have cc := congrArg Multiset.card sum
  rw [Multiset.card_add] at cc
  change A.card+ds.length=M.card
  omega

-- Trace the needed wires backwards. A repeated demand uses one copy. The number
-- of initial wires plus copies never exceeds the final frontier size plus the gate count.
lemma frontier {n : Nat} {A S : Finset (E n)} {k : Nat} (hist : Hist A S k)
    (T : Finset (E n)) (sub : T⊆S) {f cs} (tail : Run T.val f cs) :
    ∃ B : Finset (E n), B⊆A ∧ ∃ ds, Run B.val f (ds++cs) ∧ B.card+ds.length≤T.card+k := by
  induction hist generalizing T cs with
  | init => exact ⟨T,sub,[],by simpa using tail,by simp⟩
  | skip prev ih =>
    obtain ⟨B,bs,ds,go,lim⟩ := ih T sub tail
    exact ⟨B,bs,ds,go,by omega⟩
  | @add S k l r prev hl hr op ih =>
    let g := E.comb op l r
    by_cases inT : g∈T
    · let R := T.erase g
      have exprs : g ::ₘ R.val=T.val := Multiset.cons_erase inT
      have go : Run (g ::ₘ R.val) f cs := exprs ▸ tail
      let M := l ::ₘ r ::ₘ R.val
      have back : Run M f cs := Run.join op go
      obtain ⟨ds,dup,length⟩ := compress M back
      have inOld : M.toFinset⊆S := by
        intro e he
        have hm : e=l ∨ e=r ∨ e∈R := by simpa [M] using he
        rcases hm with rfl|rfl|h
        · exact hl
        · exact hr
        · obtain ⟨ne,ht⟩ := Finset.mem_erase.mp h
          exact (Finset.mem_insert.mp (sub ht)).resolve_left ne
      obtain ⟨B,bs,es,out,lim⟩ := ih M.toFinset inOld dup
      have mcard : M.card=R.card+2 := by change (l ::ₘ r ::ₘ R.val).card=R.val.card+2; rw [Multiset.card_cons,Multiset.card_cons]
      have rcard : R.card+1=T.card := Finset.card_erase_add_one inT
      exact ⟨B,bs,es++ds,by simpa using out,by simp only [List.length_append]; omega⟩
    · have inOld : T⊆S := by
        intro e he
        rcases Finset.mem_insert.mp (sub he) with rfl|h
        · exact (inT he).elim
        · exact h
      obtain ⟨B,bs,ds,out,lim⟩ := ih T inOld tail
      exact ⟨B,bs,ds,out,by omega⟩

lemma base_used {n : Nat} (A : Finset (E n)) (base : ∀ e∈A,Basic e) {f cs}
    (run : Run A.val f cs) (spec : Spec Finset.univ f) : 2*n≤A.card := by
  classical
  have use (u : V n) : E.var u∈A := by
    by_contra absent
    rcases u with ⟨b,i⟩
    let u : V n := (b,i)
    let v : V n := (!b,i)
    have act : i∈(Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have edge : Pos u v := by cases b <;> simp [u,v,Pos]
    have on := spec_pos spec (v:=u) (w:=v) act act edge
    have off := spec.2.1 v act
    have eq : value Finset.univ f {u,v}= value Finset.univ f {v} := by
      apply run_agree run
      intro a ha
      rcases base a ha with ⟨w,rfl⟩|⟨c,rfl⟩
      · have ne : w≠u := by intro h; apply absent; change E.var u∈A; rw [←h]; exact ha
        simp [value,ev,clip,ne]
      · rfl
    simp [on,off] at eq
  let vars := (Finset.univ : Finset (V n)).image E.var
  have sub : vars⊆A := by
    intro v hv
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
    exact use u
  have ci : Function.Injective (@E.var n) := fun a b h => E.var.inj h
  have count : vars.card=2*n := by simp [vars,Finset.card_image_of_injective _ ci,V]
  exact count ▸ Finset.card_le_card sub

theorem history_lower {n : Nat} (A S : Finset (E n)) (base : ∀ e∈A,Basic e) (s : Nat)
    (hist : Hist A S s) (f : E n) (out : f∈S) (spec : Spec Finset.univ f) : 5*n≤2*s+3 := by
  obtain ⟨B,bs,ds,run,lim⟩ := frontier hist {f} (by simpa using out)
    (Run.stop (f:=f) (by simp : f∈({f} : Finset (E n)).val))
  simp only [List.append_nil,Finset.card_singleton] at run lim
  have start := base_used B (fun e he => base e (bs he)) run spec
  have pay := copy_lower B (fun e he => base e (bs he)) run Finset.univ spec
  have length : weight Finset.univ ds≤ds.length := List.length_filter_le _ _
  simp only [Finset.card_univ,Fintype.card_fin] at pay
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def isOr : GateOp → Bool
  | .or => true
  | _ => false

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def liftOp {n : Nat} (op : GateOp) : List (E n) → E n
  | [] => .lit (isAnd op)
  | [a] => a
  | a::b::_ => .comb (isOr op) a b

def push {n : Nat} (w : List (E n)) (g : Gate) :=
  w ++ [liftOp g.op (g.inputs.map (fun i => w.getD i (.lit false)))]

lemma lifted_eval {n : Nat} (z : Row n) (g : Gate)
    (good : g.op∈({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) (w : List (E n)) :
    ev z (liftOp g.op (g.inputs.map (fun i => w.getD i (.lit false)))) =
      g.op.eval (g.inputs.map (fun i => (w.map (ev z)).getD i false)) := by
  have read (i : Nat) : (w.map (ev z)).getD i false = ev z (w.getD i (.lit false)) := List.getD_map w (.lit false) (ev z)
  obtain ⟨op,ins⟩ := g
  rcases good with ⟨hop,lim⟩
  change op=.and ∨ op=.or at hop
  change ins.length≤2 at lim
  rcases hop with rfl|rfl <;> cases ins with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil => simp [liftOp,GateOp.eval,ev] <;> cases w[a]? <;> rfl
    | cons b tail =>
      have h : tail=[] := List.length_eq_zero_iff.mp (by simpa using lim)
      subst tail
      simp [liftOp,GateOp.eval,ev,boolGate,isOr] <;> cases w[a]? <;> cases w[b]? <;> rfl

lemma eval_fold {n : Nat} (z : Row n) (gs : List Gate)
    (good : ∀ g∈gs,g.op∈({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) (w : List (E n)) :
    (gs.foldl push w).map (ev z) =
      gs.foldl (fun (ls : List Bool) g => ls ++ [g.op.eval (g.inputs.map (fun i => ls.getD i false))]) (w.map (ev z)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun u hu => good u (by simp [hu]))]
    simp only [push,List.map_append,List.map_cons,List.map_nil,lifted_eval z g (good g (by simp))]

lemma get_available {n : Nat} (w : List (E n)) (S : Finset (E n)) (has : ∀ e∈w,e∈S)
    (zero : E.lit false∈S) (i : Nat) : w.getD i (.lit false)∈S := by
  by_cases hi : i<w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact has _ (List.getElem_mem _)
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_lt hi)] using zero

lemma fold_hist {n : Nat} (gs : List Gate) (A S : Finset (E n)) (k : Nat) (hist : Hist A S k)
    (cn : ∀ b,E.lit b∈S) (w : List (E n)) (has : ∀ e∈w,e∈S) :
    ∃ T : Finset (E n), Hist A T (k+gs.length) ∧ (∀ b,E.lit b∈T) ∧ ∀ e∈gs.foldl push w,e∈T := by
  induction gs generalizing S k w with
  | nil => exact ⟨S,by simpa using hist,cn,has⟩
  | cons g gs ih =>
    let pins := g.inputs.map (fun i => w.getD i (.lit false))
    have valid (a : E n) (ha : a∈pins) : a∈S := by
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      exact get_available _ _ has (cn false) i
    obtain ⟨U,step,sub,next⟩ : ∃ U : Finset (E n), Hist A U (k+1) ∧ S⊆U ∧ liftOp g.op pins∈U := by
      cases h : pins with
      | nil => exact ⟨S,Hist.skip hist,fun _ h => h,cn _⟩
      | cons a t =>
        have ha := valid a (by simp [h])
        cases t with
        | nil => exact ⟨S,Hist.skip hist,fun _ h => h,ha⟩
        | cons b rest =>
          have hb := valid b (by simp [h])
          exact ⟨_,Hist.add hist ha hb (isOr g.op),Finset.subset_insert _ _,Finset.mem_insert_self _ _⟩
    have ready (e : E n) (he : e∈push w g) : e∈U := by
      rcases List.mem_append.mp he with old|last
      · exact sub (has e old)
      · have eq : e=liftOp g.op pins := by simpa [pins] using last
        exact eq ▸ next
    obtain ⟨T,ht,ct,wt⟩ := ih U (k+1) step (fun b => sub (cn b)) (push w g) ready
    exact ⟨T,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht,ct,wt⟩

def rawL (m : Nat) (i : Fin (m+1)) : E m :=
  if h : i.val<m then .var (false,⟨i.val,h⟩) else .lit false
def rawR (m : Nat) (i : Fin (m+1)) : E m :=
  if h : i.val=0 then .lit false else .var (true,⟨i.val-1,by omega⟩)
def rawList (m : Nat) := List.ofFn (rawL m) ++ List.ofFn (rawR m)
def bases (m : Nat) : Finset (E m) := insert (.lit true) (insert (.lit false) (Finset.univ.image E.var))

lemma inbase {m : Nat} (e : E m) : e∈bases m ↔ Basic e := by
  constructor
  · intro h
    simp only [bases,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at h
    rcases h with rfl|rfl|⟨u,rfl⟩
    · exact Or.inr ⟨true,rfl⟩
    · exact Or.inr ⟨false,rfl⟩
    · exact Or.inl ⟨u,rfl⟩
  · rintro (⟨u,rfl⟩|⟨b,rfl⟩)
    · simp [bases]
    · cases b <;> simp [bases]

lemma raw_base (m : Nat) (e : E m) (h : e∈rawList m) : e∈bases m := by
  rcases List.mem_append.mp h with l|r
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp l
    unfold rawL; split <;> simp [bases]
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp r
    unfold rawR; split <;> simp [bases]

def encoded {m : Nat} (z : Row m) := (rawList m).map (ev z)

def outExpr (m : Nat) (C : Circuit) := (C.gates.foldl push (rawList m)).getD C.output (.lit false)

lemma eval_out {m : Nat} (z : Row m) (C : Circuit) (good : Monotone2 C) :
    ev z (outExpr m C)=C.eval (encoded z) := by
  have read := @List.getD_map _ _ (C.gates.foldl push (rawList m)) (.lit false) C.output (ev z)
  change ev z ((C.gates.foldl push (rawList m)).getD C.output (.lit false))=_
  rw [←read,eval_fold z C.gates good]
  rfl

lemma mono_read {x y : List Bool} (h : List.Forall₂ (·≤·) x y) (i : Nat) : x.getD i false≤y.getD i false := by
  induction h generalizing i with
  | nil => rfl
  | cons h t ih => cases i with
    | zero => exact h
    | succ i => exact ih i

lemma mono_eval (C : Circuit) (good : Monotone2 C) {x y : List Bool} (h : List.Forall₂ (·≤·) x y) :
    C.eval x≤C.eval y := by
  apply mono_read (i:=C.output)
  change List.Forall₂ (·≤·) (C.wires x) (C.wires y)
  unfold Circuit.wires
  generalize hg : C.gates=gs
  have ops : ∀ g∈gs,g.op=.and ∨ g.op=.or := fun g mem => (good g (hg ▸ mem)).1
  clear hg good
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    refine ih ?_ (fun u hu => ops u (by simp [hu]))
    apply List.rel_append h
    apply List.Forall₂.cons _ List.Forall₂.nil
    apply Bool.le_iff_imp.mpr
    rcases ops g (by simp) with op|op
    · simp only [op,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
      intro all i hi; exact Bool.le_iff_imp.mp (mono_read h i) (all i hi)
    · simp only [op,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
      rintro ⟨i,hi,on⟩; exact ⟨i,hi,Bool.le_iff_imp.mp (mono_read h i) on⟩

lemma parallel_ofFn {m : Nat} (f g : Fin m → Bool) (h : ∀ i,f i≤g i) :
    List.Forall₂ (·≤·) (List.ofFn f) (List.ofFn g) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hi hj
  simpa using h ⟨i,by simpa using hi⟩

lemma encode_le {m : Nat} (z : Row m) (u v : Fin (m+1))
    (left : ∀ a : Fin m, (false,a)∈z → a.castSucc=u)
    (right : ∀ b : Fin m, (true,b)∈z → b.succ=v) :
    List.Forall₂ (·≤·) (encoded z) (oneEach u v) := by
  simp only [encoded,rawList,oneEach,List.map_append,List.map_ofFn]
  apply List.rel_append
  · apply parallel_ofFn
    intro i
    apply Bool.le_iff_imp.mpr
    by_cases hi : i.val<m
    · intro h
      have mem : (false,(⟨i.val,hi⟩ : Fin m))∈z := of_decide_eq_true (by simpa [Function.comp_apply,rawL,hi,ev] using h)
      exact decide_eq_true (left _ mem)
    · simp [Function.comp_apply,rawL,hi,ev]
  · apply parallel_ofFn
    intro i
    apply Bool.le_iff_imp.mpr
    by_cases hi : i.val=0
    · simp [Function.comp_apply,rawR,hi,ev]
    · let b : Fin m := ⟨i.val-1,by omega⟩
      intro h
      have mem : (true,b)∈z := of_decide_eq_true (by simpa [b,Function.comp_apply,rawR,hi,ev] using h)
      have eq : b.succ=i := Fin.ext (by dsimp [b]; omega)
      exact decide_eq_true (eq ▸ right b mem)

lemma encoded_pair {m : Nat} (a b : Fin m) :
    encoded {(false,a),(true,b)}=oneEach a.castSucc b.succ := by
  simp only [encoded,rawList,oneEach,List.map_append,List.map_ofFn]
  congr 1 <;> apply congrArg List.ofFn <;> funext i
  · by_cases hi : i.val<m
    · simp [Function.comp_apply,rawL,hi,ev,Fin.ext_iff]
    · have ne : i≠a.castSucc := by intro e; subst i; exact hi a.isLt
      simp [Function.comp_apply,rawL,hi,ev,ne]
  · by_cases hi : i.val=0
    · have ne : i≠b.succ := by intro e; subst i; simp at hi
      simp [Function.comp_apply,rawR,hi,ev,ne]
    · simp [Function.comp_apply,rawR,hi,ev,Fin.ext_iff]
      omega

-- The unused last row and first column force rejection of singleton inputs by monotonicity.
lemma actual_spec (m : Nat) (C : Circuit) (good : Monotone2 C)
    (rep : Represents (fun u v : Fin (m+1) => decide (u<v)) C) :
    Spec Finset.univ (outExpr m C) := by
  have val (z : Row m) : value Finset.univ (outExpr m C) z=C.eval (encoded z) := by
    simpa [value,clip] using eval_out z C good
  have off (z : Row m) (u v : Fin (m+1)) (order : v≤u)
      (left : ∀ a : Fin m,(false,a)∈z → a.castSucc=u)
      (right : ∀ b : Fin m,(true,b)∈z → b.succ=v) : value Finset.univ (outExpr m C) z=false := by
    rw [val]
    have le := mono_eval C good (encode_le z u v left right)
    rw [rep u v] at le
    apply Bool.eq_false_iff.mpr
    intro h
    have bad := Bool.le_iff_imp.mp le h
    simp [not_lt_of_ge order] at bad
  refine ⟨off ∅ (Fin.last m) 0 (Fin.zero_le _) (by simp) (by simp),?_,?_⟩
  · rintro ⟨d,i⟩ _
    cases d with
    | false => exact off {(false,i)} i.castSucc 0 (Fin.zero_le _) (by intro a h; simp at h; subst a; rfl) (by simp)
    | true => exact off {(true,i)} (Fin.last m) i.succ (Fin.le_last _) (by simp) (by intro b h; simp at h; subst b; rfl)
  · intro a _ b _
    rw [val,encoded_pair,rep]
    change decide (a.val<b.val+1)=decide (a.val≤b.val)
    simp [Nat.lt_succ_iff]

theorem actual_lower (m : Nat) (C : Circuit) (good : Monotone2 C)
    (rep : Represents (fun u v : Fin (m+1) => decide (u<v)) C) : 5*m≤2*C.size+3 := by
  obtain ⟨T,hist,cn,all⟩ := fold_hist C.gates (bases m) (bases m) 0 Hist.init
    (fun b => (inbase _).mpr (Or.inr ⟨b,rfl⟩)) (rawList m) (raw_base m)
  apply history_lower (bases m) T (fun e h => (inbase _).mp h) C.size
    (by simpa [Circuit.size] using hist) (outExpr m C) _ (actual_spec m C good rep)
  exact get_available _ T all (cn false) C.output

end PEqualNP.Outside.L_meta_7147

theorem PEqualNP.Outside.L_meta_7147 : ∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u < v)) s → 5 * n ≤ 2 * s + 8 := by
  intro n s bound
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨C,good,lim,rep⟩ := bound
    have lower := PEqualNP.Outside.L_meta_7147.actual_lower m C good rep
    omega
