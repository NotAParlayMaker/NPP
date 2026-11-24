import Mathlib
import PEqualNP.Defs

-- Circuit elimination and the smaller-graph certificates are adapted from L_meta_1667.

namespace PEqualNP.Outside.L_meta_1922
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
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
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

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

private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
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
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
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
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun


end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem bridge_bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

lemma bridge_live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma bridge_get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

lemma bridge_bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

lemma bridge_operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

lemma bridge_bit_zero (i) : bit i zero = false := by simp [bit,zero]

lemma bridge_bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp

lemma bridge_bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]

lemma bridge_bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

lemma bridge_b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bridge_bit_zero _).symm
  | some a => rfl

lemma bridge_run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [bridge_b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bridge_bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bridge_bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bridge_bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bridge_bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bridge_bit_neg,bridge_bit_zero]
    | cons a l => exact bridge_bit_neg _ _

lemma bridge_execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,bridge_run_bit i g w (hg g (by simp))]

def seed04 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)

theorem seed04_table : ∀ r : Row, bit r seed04 = (sample r 0 || sample r 4) := by
  decide +kernel

def BinaryWitness (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

theorem bin_mono_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ BinaryWitness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bridge_bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bridge_bin_laws b
  rcases bridge_operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bridge_bin_comm]; cases d <;> simp_all
  · rw [bridge_bin_comm]; cases d <;> simp_all
  rcases bridge_operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

theorem gate_mono_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ BinaryWitness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bridge_bin_laws _).1] using
          Or.inl (b := BinaryWitness w (w.getD i zero)) (bridge_get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bridge_bin_laws _).2.1] using
          Or.inl (b := BinaryWitness w (w.getD i zero)) (bridge_get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bridge_bin_laws _).1] using
            bin_mono_rep false (bridge_get_rep w i) (bridge_get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bridge_bin_laws _).2.1] using
            bin_mono_rep true (bridge_get_rep w i) (bridge_get_rep w j)

theorem pull_gate_mono {w : List Sig} {z : Sig} {k S} (h : Live target k 0 S)
    (hz : represented w z ∨ BinaryWitness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ Live target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := bridge_live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k 0 (insert (bin d a b) U) := by
          simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extract_mono (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k S, k ≤ gs.length ∧ Live target k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate_mono ht (gate_mono_rep w g (legal g (by simp))) hs
    exact ⟨l,T,by simp; omega,hu,hT⟩

def neighbor04 (i : Fin 9) : Nat := [4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow04 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor04 i)
def presentRow04 (i : Fin 9) : Row :=
  Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor04 i))

theorem seed04_witness : ∀ i : Fin 9,
    (bit (absentRow04 i) graph != bit (presentRow04 i) graph) &&
    ((inputs++[seed04]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow04 i) w == bit (presentRow04 i) w) = true := by
  decide +kernel

theorem all_roots04 {k t S} (h : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ inputs++[seed04]) :
    S=inputs.toFinset ∨ S=(inputs++[seed04]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed04_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow04 i) (presentRow04 i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed04 ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live04 (C : Circuit) (legal : Monotone2 C)
    (computes : ∀ y : Fin 9 → Bool,
      C.eval (List.ofFn y ++ [y 0 || y 4]) = edge y) :
    ∃ k, k ≤ C.size ∧
      (Live graph k 0 inputs.toFinset ∨ Live graph k 0 (inputs++[seed04]).toFinset) := by
  have fan : FanInTwo C := by
    intro g hg
    obtain ⟨hop,hlen⟩ := legal g hg
    refine ⟨?_,hlen⟩
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have evalAt (r : Row) (i : Nat) :
      bit r ((execute C.gates (inputs++[seed04])).getD i zero) =
      (C.wires (List.ofFn (sample r) ++ [sample r 0 || sample r 4])).getD i false := by
    rw [←bridge_b_read,bridge_execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    rw [List.map_append,List.map_singleton,←sampled,seed04_table]
    rfl
  have goalEq : (execute C.gates (inputs++[seed04])).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (evalAt r C.output).trans ((computes (sample r)).trans (edge_table r).symm)
  have out := bridge_get_rep (execute C.gates (inputs++[seed04])) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k,S,hk,run,hs⟩ := extract_mono C.gates (inputs++[seed04]) legal graph_proper targetIn
  refine ⟨k,hk,?_⟩
  rcases all_roots04 run hs with h | h
  · exact Or.inl (h ▸ run)
  · exact Or.inr (h ▸ run)

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922.Boundary

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

open PEqualNP.MetaComplexity

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def pos : Fin 12 → Nat := ![3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
def neg : Fin 12 → Nat := ![42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
def rows : List Nat := [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402]
def positives : List Nat := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
def bits (n : Nat) (i : Fin 9) : Bool := n.testBit i.val

def init (x : Fin 9 → Bool) : Fin 10 → Bool := Fin.snoc x (x 0 || x 4)
def value (C : Circuit) (x : Fin 9 → Bool) : Bool :=
  C.eval (List.ofFn x ++ [x 0 || x 4])

lemma ofFn_snoc {n : Nat} (x : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc (α := fun _ => Bool) x b) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

lemma ofFn_init (x : Fin 9 → Bool) : List.ofFn (init x) = List.ofFn x ++ [x 0 || x 4] :=
  ofFn_snoc x (x 0 || x 4)

lemma init_mono (x y : Fin 9 → Bool) (hle : ∀ i, x i = true → y i = true) :
    ∀ i, init x i = true → init y i = true := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [init, Fin.snoc_last, Bool.or_eq_true]
    rintro (h | h)
    · exact Or.inl (hle 0 h)
    · exact Or.inr (hle 4 h)
  · simpa only [init, Fin.snoc_castSucc] using hle j

lemma value_mono (C : Circuit) (hm : Monotone2 C) (x y : Fin 9 → Bool)
    (hle : ∀ i, x i = true → y i = true) : value C x = true → value C y = true := by
  have hinit := init_mono x y hle
  have hlist : ∀ i, (List.ofFn (init x)).getD i false = true →
      (List.ofFn (init y)).getD i false = true := by
    intro i h
    by_cases hi : i < 10
    · have hx : (List.ofFn (init x)).getD i false = init x ⟨i, hi⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      have hy : (List.ofFn (init y)).getD i false = init y ⟨i, hi⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      rw [hy]
      exact hinit _ (hx ▸ h)
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      exact False.elim (Bool.false_ne_true h)
  have hw := wiresFrom_mono C.gates (fun g hg => (hm g hg).1)
    (List.ofFn (init x)) (List.ofFn (init y)) (by simp) hlist C.output
  simpa only [value, Circuit.eval, Circuit.wires, ← ofFn_init, wiresFrom] using hw

set_option maxHeartbeats 4000000 in
lemma boundary_cover : ∀ x : Fin 9 → Bool,
    (target x = true → ∃ p : Fin 12, ∀ i, bits (pos p) i = true → x i = true) ∧
    (target x = false → ∃ p : Fin 12, ∀ i, x i = true → bits (neg p) i = true) := by
  decide +kernel

lemma pos_mem (p : Fin 12) : pos p ∈ rows ∧ pos p ∈ positives := by
  fin_cases p <;> decide

lemma neg_mem (p : Fin 12) : neg p ∈ rows ∧ neg p ∉ positives := by
  fin_cases p <;> decide

lemma boundary_complete (C : Circuit) (hm : Monotone2 C)
    (ht : ∀ n ∈ rows, value C (bits n) = decide (n ∈ positives)) :
    ∀ x, value C x = target x := by
  intro x
  have hb := boundary_cover x
  cases hx : target x with
  | false =>
    by_contra hne
    have hv : value C x = true := by cases hv : value C x <;> simp_all
    obtain ⟨p, hp⟩ := hb.2 hx
    have hn := ht (neg p) (neg_mem p).1
    have htrue := value_mono C hm x (bits (neg p)) hp hv
    rw [htrue] at hn
    simpa [(neg_mem p).2] using hn
  | true =>
    obtain ⟨p, hp⟩ := hb.1 hx
    apply value_mono C hm (bits (pos p)) x hp
    have hn := ht (pos p) (pos_mem p).1
    simpa [(pos_mem p).2] using hn

end PEqualNP.Outside.L_meta_1922.Boundary

namespace PEqualNP.Outside.L_meta_1922

open PEqualNP.CircuitLowerBounds

lemma mono_bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

lemma mono_live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma mono_live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
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


def MonoImpossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬ Live T k 0 S

lemma impossible_mono {T cap S} (h : Impossible T cap S) : MonoImpossible T cap S :=
  fun k hk => h k 0 hk

theorem mono_enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      MonoImpossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    MonoImpossible T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := mono_live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (mono_live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)


theorem mono_closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → MonoImpossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    MonoImpossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact impossible_mono (scalarPoolCut_sound (pValid _ hp) nd ok)


def monoEvalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := true
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

theorem mono_evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → MonoImpossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : monoEvalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    MonoImpossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := (mono_live_size h).2
  change child.toFinset.card + 0 ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold monoEvalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_sound h rfl (pair_sep pairs) true (fun _ => rfl)
  let d := true
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change covered true (pairSig r s) child = BitVec.allOnes 768 at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k 0 child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k 0 (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact mono_closeChild_sound pv lv nd' test k hk h



def monoTestPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := monoEvalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
theorem monoTestPair_at {ctx a b d} (h : monoTestPair ctx a b d = true) (ka kb : Bool) :
    monoEvalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [monoTestPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

def monoTestAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => bs.all (fun b => monoTestPair ctx a b false && monoTestPair ctx a b true) && monoTestAll ctx bs

theorem mono_all_binary {ctx ws} (h : monoTestAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : monoTestPair ctx a b d=true ∨ monoTestPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [monoTestAll,Bool.and_eq_true,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1 b bm).1 | exact (h.1 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1 a haTail).1 | exact (h.1 a haTail).2
      · exact ih h.2 haTail hbTail


theorem mono_node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → MonoImpossible T (cap-1) (List.toFinset xs))
    (checks : monoTestAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    MonoImpossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply mono_enum_step nd out
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : monoTestPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        MonoImpossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact mono_evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (monoTestPair_at test ka kb)
    rcases mono_all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (mono_bin_comm d a.1 b.1 ▸ pro)
        (mono_bin_comm d a.1 b.1 ▸ fresh) hh



def monoPairCode (rank : Nat) : Nat :=
  (0x0edecebeae9e8e7e6e5e4e3e2e1e0dcdbdad9d8d7d6d5d4d3d2d1d0cbcac9c8c7c6c5c4c3c2c1c0bab9b8b7b6b5b4b3b2b1b0a9a8a7a6a5a4a3a2a1a0989796959493929190878685848382818076757473727170656463626160545352515043424140323130212010 >>> (8*rank)) &&& 255

def monoExpandOps : Nat → Nat → Nat → Nat
  | 0,_,_ => 0
  | n+1,j,stored =>
    let width := if j<2 then 7 else 8
    let code := stored &&& ((1 <<< width)-1)
    let op := monoPairCode (code >>> 1) ||| ((code &&& 1) <<< 8)
    op ||| (monoExpandOps n (j+1) (stored >>> width) <<< 10)

def monoStoredLen (depth : Nat) := 8*(depth-1)-min 2 (depth-1)
def monoReadNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := monoStoredLen depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := if depth=0 then 0 else 320 ||| (monoExpandOps (depth-1) 0 stored <<< 10)
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def monoBuildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem monoBuildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : monoBuildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold monoBuildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def monoStateSet (g : Forest) (k i : Nat) := (monoReadNode g k i).2.2.map Prod.fst

theorem mono_rotate_excluded {T n} {ws : List Sig} (hi : MonoImpossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : MonoImpossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

def monoLinkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (monoStateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem monoLinkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, MonoImpossible (targetOf g) k (monoStateSet g k i).toFinset)
    {pair out} (h : monoLinkedSet g k pair = some out) :
    MonoImpossible (targetOf g) k out.toFinset := by
  unfold monoLinkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact mono_rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))


def monoCountBefore (data : Nat → Nat) (header start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => packedAt data (header+5*(start+n)) 5 + monoCountBefore data header start n
def monoNodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := monoReadNode g k i
  let values := ws.map Prod.fst
  let start := num*(monoStoredLen depth+raw.length+depth)
  let nr := packedAt data (start+5*i) 5
  let countsBase := start+5*num
  let before := packedAt data (countsBase+(i/32)*offw) offw +
    monoCountBefore data start (32*(i/32)) (i % 32)
  let st := countsBase+((num+31)/32)*offw+before*(cw+depth)
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => monoBuildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (monoLinkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else monoTestAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem monoNodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1,
      MonoImpossible (targetOf g) (k-1) (monoStateSet g (k-1) j).toFinset)
    (checked : monoNodeVerified g k i = true) :
    MonoImpossible (targetOf g) k (monoStateSet g k i).toFinset := by
  simp only [monoNodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ monoStateSet g k i := by simpa [monoStateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (monoStateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply mono_node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact monoBuildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (monoLinkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact monoLinkedSet_sound g _ names (prior (by omega)) h

def monoBlock (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => monoNodeVerified g k (start+n) && monoBlock g k start n

theorem monoBlock_at {g k start n} (h : monoBlock g k start n=true) (j : Nat)
    (lo : start≤j) (hi : j<start+n) : monoNodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [monoBlock,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem monoBlock_merge {g k start a b} (h : monoBlock g k start a=true)
    (h' : monoBlock g k (start+a) b=true) : monoBlock g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [monoBlock,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,monoBlock,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def monoCheckedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, monoBlock g k 0 (g.levels k).1 = true

theorem monoForest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : monoCheckedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, MonoImpossible (targetOf g) k (monoStateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply monoNodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact monoBlock_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply monoNodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact monoBlock_at (rows _ hk) i (by omega) (by omega)

def monoIndexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (monoStateSet g k i) ws

theorem monoRoot_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : monoCheckedTables g top) (le : k ≤ top)
    (idx : monoIndexedRoot g k i ws = true) : MonoImpossible (targetOf g) k ws.toFinset := by
  simp only [monoIndexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact monoForest_all g top prior low geom blocks _ le i idx.1

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

def or04maps15 : List (Nat × List Nat) := [(420,[32,130,112,98,50,81,64])]
def or04known15 := extendKnown known383 4 or04maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04valid15 : Known or04known15 :=
  extendKnown_ok valid383 low15 (by decide +kernel)

def or04maps47 : List (Nat × List Nat) := [(157,[117,101,33,32,65,48]),(283,[131,115,99,49,50,66,81]),(91,[101,66,16])]
def or04known47 := extendKnown or04known15 5 or04maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04valid47 : Known or04known47 :=
  extendKnown_ok or04valid15 low47 (by decide +kernel)

def or04maps63 : List (Nat × List Nat) := [(483,[83,80,132,115,96,32,16]),(363,[128,64,116,81,96,49,32]),(315,[131,115,65,50,98,81]),(423,[133,80,116,96,48,32,16]),(335,[131,115,100,50,33,16,80]),(287,[133,117,101,16,64,49,32])]
def or04known63 := extendKnown or04known47 8 or04maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04valid63 : Known or04known63 :=
  extendKnown_ok or04valid47 low63 (by decide +kernel)

def or04maps111 : List (Nat × List Nat) := [(123,[101,66,16]),(343,[131,115,83,67,98]),(311,[131,115,99,67,82,16]),(111,[])]
def or04known111 := extendKnown or04known63 7 or04maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04valid111 : Known or04known111 :=
  extendKnown_ok or04valid63 low111 (by decide +kernel)

def or04maps119 : List (Nat × List Nat) := [(435,[134,81,114,50,65])]
def or04known119 := extendKnown or04known111 6 or04maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04valid119 : Known or04known119 :=
  extendKnown_ok or04valid111 low119 (by decide +kernel)

def or04maps189 : List (Nat × List Nat) := [(303,[135,50,65])]
def or04known189 := extendKnown or04known119 8 or04maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04valid189 : Known or04known189 :=
  extendKnown_ok or04valid119 low189 (by decide +kernel)

def or04baselines : List (Nat × Nat × Nat) := []
def or04baselineEntries : List (Nat × Nat) := or04baselines.map (fun e => (e.1,e.2.2))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04baselineChecks : or04baselines.all (fun e => assertSize e.1 e.2.1 e.2.2) = true := by
  decide +kernel

theorem or04baselineValid : Known or04baselineEntries := by
  intro e he
  obtain ⟨entry,hm,rfl⟩ := List.mem_map.mp he
  exact size_of (List.all_eq_true.mp or04baselineChecks entry hm)

def or04allknown : List (Nat × Nat) := or04baselineEntries ++ or04known189

theorem or04allvalid : Known or04allknown := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact or04baselineValid e h
  · exact or04valid189 e h

theorem or04prior_sound (q : Nat) : Lower (vars q) (graphGoal q) (boundsBefore or04allknown q) :=
  before_sound or04allknown or04allvalid q

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

def or04columns : Array ColumnInfo := #[(7,0,504,0,7),(35,0,476,0,7),(289,0,222,0,7),(14,0,497,0,7),(268,0,243,0,7),(296,0,215,0,7),(5,2,440,64,6),(34,1,460,16,6),(257,32,94,128,6),(10,4,369,128,6),(260,8,227,16,6),(40,256,151,64,6),(9,16,486,0,8),(258,64,189,0,8),(36,128,347,0,8),(27,0,484,0,5),(19,0,492,0,8),(17,2,424,68,6),(18,1,460,32,6),(67,0,444,0,8),(3,64,188,256,6),(65,2,440,4,6),(66,1,396,48,6),(131,0,380,0,6),(3,128,344,36,6),(129,2,312,68,6),(130,1,332,48,6),(323,0,188,0,5),(29,0,482,0,5),(21,0,490,0,7),(5,16,482,8,6),(165,0,346,0,5),(71,0,440,0,5),(133,0,378,0,7),(5,128,346,32,6),(25,0,486,0,8),(57,0,454,0,5),(89,0,422,0,5),(153,0,358,0,5),(281,0,230,0,5),(49,0,462,0,8),(17,32,78,384,6),(81,0,430,0,8),(17,64,172,258,6),(65,16,422,8,6),(145,0,366,0,8),(17,128,330,36,6),(129,16,358,8,6),(273,0,238,0,7),(257,16,230,8,6),(97,0,414,0,6),(33,64,156,258,6),(65,32,30,384,6),(96,1,396,18,6),(161,0,350,0,8),(129,32,94,256,6),(160,1,332,18,6),(193,0,318,0,7),(321,0,190,0,7),(257,64,188,2,6),(417,0,94,0,5),(6,16,480,9,6),(20,2,424,65,6),(166,0,345,0,5),(70,0,441,0,8),(6,64,185,256,6),(66,4,305,136,6),(68,2,440,1,6),(134,0,377,0,8),(130,4,369,8,6),(132,2,312,65,6),(326,0,185,0,5),(10,16,484,1,6),(74,0,437,0,7),(10,64,181,256,6),(142,0,369,0,5),(330,0,181,0,5),(51,0,460,0,5),(82,0,429,0,8),(66,16,420,9,6),(98,0,413,0,7),(34,64,157,256,6),(162,0,349,0,7),(34,128,345,4,6),(354,0,157,0,5),(194,0,317,0,8),(66,128,281,36,6),(192,2,312,5,6),(322,0,189,0,8),(450,0,61,0,5),(28,0,483,0,8),(12,16,482,1,6),(20,8,227,256,6),(172,0,339,0,5),(76,0,435,0,6),(68,8,163,272,6),(72,4,305,130,6),(140,0,371,0,8),(132,8,99,272,6),(136,4,369,2,6),(148,0,363,0,8),(132,16,354,9,6),(228,0,283,0,5),(164,0,347,0,8),(420,0,91,0,5),(196,0,315,0,8),(132,64,57,258,6),(192,4,305,10,6),(324,0,187,0,7),(260,64,185,2,6),(388,0,123,0,7),(260,128,91,32,6),(40,16,454,1,6),(88,0,423,0,8),(72,16,422,1,6),(80,8,163,260,6),(152,0,359,0,8),(136,16,358,1,6),(144,8,99,260,6),(280,0,231,0,8),(264,16,230,1,6),(272,8,227,4,6),(360,0,151,0,5),(168,0,343,0,7),(40,128,339,4,6),(200,0,311,0,7),(328,0,183,0,8),(72,256,151,32,6),(320,8,163,20,6),(392,0,119,0,6),(136,256,23,96,6),(384,8,99,20,6),(176,0,335,0,8),(160,16,326,9,6),(288,16,198,9,6),(208,0,303,0,8),(336,0,175,0,8),(320,16,166,9,6),(400,0,111,0,7),(224,0,287,0,8),(192,32,30,257,6),(352,0,159,0,8),(96,256,151,8,6),(320,32,30,129,6),(416,0,95,0,8),(160,256,23,72,6),(384,32,94,1,6),(448,0,63,0,8),(192,256,23,40,6),(17,0,494,0,11),(66,0,445,0,11),(132,0,379,0,11),(24,0,487,0,11),(80,0,431,0,11),(144,0,367,0,11),(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11)]

def column04 (i : Nat) : ColumnInfo := or04columns[i]?.getD (0,0,0,0,0)

def column04Chunk (start : Nat) : Bool :=
  (List.range (min 16 (158-start))).all (fun j => colCheck 511 (column04 (start+j)) (boundsBefore or04allknown))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part0 : column04Chunk 0 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part1 : column04Chunk 16 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part2 : column04Chunk 32 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part3 : column04Chunk 48 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part4 : column04Chunk 64 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part5 : column04Chunk 80 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part6 : column04Chunk 96 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part7 : column04Chunk 112 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part8 : column04Chunk 128 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem column04part9 : column04Chunk 144 = true := by
  decide +kernel

theorem column04Checked (i : Nat) (hi : i < 158) :
    colCheck 511 (column04 i) (boundsBefore or04allknown) = true := by
  have block (q : Nat) (hq : q < 10) : column04Chunk (16*q) = true := by
    interval_cases q
    · exact column04part0
    · exact column04part1
    · exact column04part2
    · exact column04part3
    · exact column04part4
    · exact column04part5
    · exact column04part6
    · exact column04part7
    · exact column04part8
    · exact column04part9
  have hq : i / 16 < 10 := by omega
  have hpart := block (i / 16) hq
  have hm : i % 16 < min 16 (158 - 16 * (i / 16)) := by omega
  have he := List.all_eq_true.mp hpart (i % 16) (List.mem_range.mpr hm)
  have eq : 16 * (i / 16) + i % 16 = i := by omega
  simpa only [eq] using he

theorem column04_vars : vars 511 = inputs := by decide +kernel
theorem column04_graph : chartGoal 511 = graph := by decide +kernel

theorem column04Slice (i : Nat) (hi : i < 158) :
    Slice inputs graph (subcube (column04 i).1 (column04 i).2.1)
      (column04 i).2.2.2.2 := by
  have h := col_sound (m:=511) (column04 i) (boundsBefore or04allknown) or04prior_sound (column04Checked i hi)
  simpa only [column04_vars,column04_graph] using h

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

def or04data8 : Nat → Nat
  | 0 => 0x640007db41e4f464ec487bee0c772190f121efd8315c8643c487
  | _ => 0

def or04hash8 : Nat → Nat
  | 0 => 0x62a906e98008
  | _ => 0

def or04data9 : Nat → Nat
  | 0 => 0x473d46b7e5cab9e91bb43f2e54cf48dda1f9729e7a46ed0c7bdb2915e765ff4cbd1e8cbb2ff3653cf465d97fa3a6e529eb4be79d9a29235a5feacac978cad2ff56554bc65697fab29e5e32b4bfe4b47353d323ff31a3989e8b1ff1b5651ced68fd1f6db2abc644e97b6d935e322756dcab2af1913ad6e4d9578c89d7b4cb0abc644fcb55745257627e5aa2a992bb13fa95147495d89f96a8a4a9aec4fad9653d197627e78ab9e85bb13fac5e8f42dd89f9e2a67a16ec4fee11d3d0b7626fb4d034a38f13bb96549578789decb264abc3c4efc58f255e1e277f212c2af0f132fb276608c789d75b3052463c4dee9ad5e191e26fb4d5af0c8f137fa2757864789becb56d4163c4dfe1a16a0b1e27f70a39e858f13f4e4dd3c8d685fb62ae4a46242fdb15325231217fd08e9291890bcf1dfde477084e78cf23adf8427ac7a36b1d36135e3cc8e9f9b09eb1dac74fcd84f68ed23a7e6c27b87671d3f3613de30e9f8ddb09f8e91cdcf5187fd707a4676843e3ee987b772e1e9f7583bb9970f6fb2c1dcecb87abf9649a765c3fed83d193b2e1ff8e1b9496970f6fb2c1dcb4b87feb05e325a5c3dfe2a07d1d121f77a4fcab9090f1fdad1e4f4487dfc83b0e78243def2ad7219121efb955b90c890f5fcac8f464487ede88af276243feb445293b121ffd2480e9d890ffb911474ec487bde95ae476243df74ab723b121efda54b91d890f7f529dc8ec487fb69209a76243fcf4454d3b121fafa3ca69d890ffad240f4ec487ede8f27a76243fee41d3d3b121ef7a56919d890ffbc0f48cec487efa8f23276243fef03d193b121ef7a568c1d890f7ed2a460ec487fec88e5a1e243dfe4ab7e0f121efb255bf07890f7f929df83c487bfc942fc1e243dfe0a07d0f121eff2569b87890ffd911cdc3c487bfc95af01e243dfe4a9780f121eff250bc07890ffd911cd43c487bfc956521e243ffa445290f121ffd21b9487890f7f92b5c83c487bdc95ae41e243df64ab720f121eff254b907890f7e92a5c83c487bfc94ee41e243dfc4a7720f121ff72239e87890f7f929cf03c487bfc95a5e1e243dfe4ad230f121eff2559187890ffe90dc8c3c487ff4852461e243ffe03d230f121eff2558c87890ffd92a8643c487bfc952321e243ffc435190f121fff0390c87890fff80f4643c487ffc05e321e243dfe4ad180f121eff2548c07890f7e92a4603c487ef8cfe3a36143f7c67d1d1b0a1fbe33d8e8d850fff08746c8c287ff883a365a143ff3837232d0a1efba55ca04850fdf91fc7424287efe0fe4612143fdf05923090a1ffd81b9184850ffec0a48c24287ffc03a4612143e7c68d8b79081fb6b53bf8d840fdb59fd0c6c207eeacfa8636103f7967b431b081f3e34d8e8d840fcf1a0c746c207ef8cfe3a36103f6c67f1d1b081fba33e8e8d840fde19ec746c207
  | 1 => 0x43810e043400680040010020022006405c017000b012400601e680ca030000a03080c00000166030007001c019004c007018400940400262040010001c0090128010001c009603000c0170076017300cc030007c03000700640790018013001c007001f00cc030006c03300cc030006003c006001801300640060064007001c007001c82a001d02d012800c000c007001c007001c007001c007af2daa928002100000080001000008000084000842000021000000842208861004000000000401000000002108840084410042008800000000802000000000000000100401180200002008421100200840008021080010842108021000210802008000080000042108435d6e9e21f6e3daee74710fb71efc3b47374f7a8fe39a3aa98bd17f1cd1cc4f45cb957f6122f0f5df27b82
  | _ => 0

def or04hash9 : Nat → Nat
  | 0 => 0xf499dfcc31f200005d18134000b2e0001e9ff5072518ce08400022a419fecc19c000303800113d64561f0d0e00033ad9fbe7000063148466f7f0452dee3cf0c0008a5794000037779e5de62150651bb3d5f67e49fd0ac94c639b2244b458ed05c1f58d689f20d39f28fba5c001e64eb758dc0000002104d5000ac3b6970d9e878666d358601c6414c39ab88569286843b800350d547c90b1e4000426da1754d718c8f29189e0a7306a9a240112586495c58001a28d3a426202c000438a2721540000009cbc654c5aa2a0000d04000b02b171449236a43fa03858a19a1a000027ab1b28b62455a987279b6b8c216656a90b8ba9c9ea3f6078b78884c2d8400000008de00092946670bcc98b4ea115cc000000065f70e7e41740d84ff075a00b94a4aa5eb9600031d86e7b7cb18684ae1600df4a896607dd19ec8f0d5690b1eeb0b95ed3698141880028f7214d03803d70ef36000480dd11c8d3847e4a64c7886bd401967ca80d0f6008602b05a876a50eb4019f1b10a50f4f7e08809100e8001ab638b0000770626a09052368ee17f49cf0b133f2e863b22a54dd27b1f4e55c705a2e076411928325f033a48f030ba39596abf6fab16a82a120004a758d2906d9d00045956d6000c1e8000001e5a804c8aca27b5bb990002c00e3f242586f021069a4675d74dc000b28dd7dc39a6ce868002e53f070002cef26180a0005a71c4a518e8791fed33d1d2928e28cbe39ad230000001198211c571ea462800010e8000d8922015b60b000000bb18dad0f37196d226af0e47f806cd1a222710a5c559a62c6d5b4ad647200004c0009bb0800281753000818050a06280602000b1a0001000109380306080319190900456700001a0a29181103030a2208070a050235010302062c2d320d0a030601010108042a000b03010e03063d1d01
  | _ => 0

def or04data10 : Nat → Nat
  | 0 => 0x87bfda3cf0487ff9874f0487bfd21cf0487bfda54bc487f7d964bc487dfd9e4bc487ff9874bc487bfda548c487f7d9648c487bfda4c8c487fed8dc8c487dfd9e48c487fed8a48c487ff98748c487ffc8f48c487f7d96464487bfda4c64487fdda4864487bfda4464487ff58d464487ff987464487ffc9c864487ffc8f464487ffc8bc644879fda6c60487bfda5460487bfda4460487beda4460487bfd21c60487f7d964ec487ff9874ec487f7d934ec487fbd8f4ec487f7d164ec487ffd11cec487fed240ec487fbd114ec487ffd0dcec487ffd238ec487dfd1e4ec487ffd1e0ec487ffd0d4ec487ffd0a4ec487ff9074ec487ffd220ec487ffd1c8ec487f7d134ec487ffd0f4ec487fbd0f4ec487ffd0bcec487ffd08cec487ffd064ec487ffd060ec487fdd91cb4487ff9874b4487fdd8bcb4487ff58645c487ff991c3c487df99e43c487ff98d43c487ff98f43c487ff98bc3c487ff98643c487ff90ec3c487ff90b43c487ff905c3c487ff91fc3c487ff91f83c487ff91f43c487ff911c3c487ff91ec3c487ff91143c487ff90dc3c487ff91e43c487ff91e03c487ff90d43c487ff90a43c487ff91cc3c487ff91c83c487ff90f43c487ff90f03c487ff90bc3c487ff908c3c487ff90643c487ff90603c487defa41fc287d7f965f42879ffa6d1c2879ffa691c287d7f965ec2879ffa6d142879ffa6cdc287d7f965e4287ddfa49e4287bfda2de02879ffa6d0c2879ffa690c2879ffa6cd42879ffa6ca4287dfb9fc74287dfb9f474287dfb9ec74287dfb9e474287dfd9fc6c287f7d9646c287dfd9f46c287dfd9ec6c287ff98746c287ff18746c287f7d86d34287dfe9fc8c287f7e9648c287fee8dc8c287fee8a48c287ffa8748c287ffc86c8c287ff586c642879ffa6cec287f7f164b4287fdf11cb4287fdf0dcb4287dff1e4b4287ffb074b4287ffd06cb4287ffe08cb42879ffa6c5c287dfb9fc3c287dfb9f43c287dfb9e43c287ff986c3c287ffb0b43c287f7d96424287ff987424287ff903c24287ffd25024287dfd1fc24287ffd1f824287f7d16424287ffd11c24287ffd11424287ffd0dc24287ffd23824287ffd1e024287ffd10c24287ffd0d424287ffd0a424287ff907424287f7d13424287ffd0f424287ffd08c24287ffc08c24287ffd06424287d3fa5dfc207dbfa3dfc207c7fa0d64207d3f9fd64207d5f965f4207d6f965ec207df7a55e4207d77965e4207df3a35e4207df5a2de42079ffa6d0c207cffa0d0c207dbf9fd0c207ddf9f50c207def9ed0c207df79e50c207cfba0c74207dfb9fc74207dbb9fc74207ddb9f474207deb9ec74207df39e474207d7d965d4207dfd90dd4207df9875d42079fda6c6c207cfda0c6c207dfd9fc6c207dbd9fc6c207ddd9f46c207ded9ec6c207df59e46c207ff590c6c207ff18746c207
  | 1 => 0xed84e7f9646ed84e7f94c6ed84ef790c6ed84efb8746ed84ef38746ed84efd8fc6ed84bdfa4dc1e87bfda2dc1e87d7f965f51879ffa6d1d1879ffa691d187f6f964dd187fcf91cdd187bfda2de1187fbe91cf5187fee8dcf5187def9f5e9d87def9e9e5d87bfda2de1d87def9e9cdd87def9e9c9d87f6f9e935d87f3f91535d87faf9e8f5d879ffa688dd87bbfa548dd87fbe8f48dd879ffa6865d87fbe8f465d87ddfa3df5d07ddfa25f5d07d5f9f535d07d7d9d535d079ffa6cbdd07ddf9f4bdd07dfd9d4bdd079ffa6c65d07ddf9f465d07df79e465d07dfd9d465d07dfe9cc65d07defa41fd687f5f9651d687bdfa54dd687ddf9fcdd687f5f964dd687fcf8dca5687d7f9fd35687f5f91d35687f5f8dd35687dbf9fcf5687f9f91cf5687bdfa54bd687f5f964bd687bdfa4c8d687fcf8dc8d687fde8bc65687d7f965f50879ffa6d1d087ddf9f51d087d7f9fd35087d7f9f535087f6f9648d087def9f48d087fee8f48d0879ffa6c61087befa4461087bfda2c61087f7f134ed087fbf0f4ed087fef08ced0879ffa6cdcb87afba61dcb87dfb9eddcb87df99ddd4b87dfb9ddccb8797fa6934b87d7f9f534b87d7f9ed34b879ffa6cf0b87bff21cf0b87def9ec8cb87fef240ecb87dff1ececb87fbf114ecb87ffb1dcecb87f7f134ecb87fbf0f4ecb87ff7064ecb87bff254b4b87f7f164b4b87fdf11cb4b87fdf0dcb4b87ff70a4b4b87ffb1dcb4b87f7f134b4b87fdf0bcb4b87ff7064b4b87d7f9fd34b07d7d9d534b079ffa6cf4b07dfd9d4f4b07dfe9ccf4b079ffa6cf0b07bfba54dc787fdb91cdc787fdb91cd4787bfba4ca4787feb914a4787feb8dca4787fbb91cf4787bfba3cf0787bfba1cf0787bfba54bc787bfba548c787bfba4c8c787feb8dc8c787feb8a48c787ffa8f48c787bfba4c64787fdba4864787bfba4464787ff38d464787ffa8f464787ffa8bc64787bfba5460787bfba4460787beba4460787bf9a2c60787fbb8f4ec787bfba54b4787fdb91cb4787fdb8bcb4787ffb0ecb4787bfba4c5c787ff38645c787ffb0ec5c787ffb0b45c787bfda4df8487bdda4df8487bfda3df8487bfda25f8487bfca21f4487f7d9651c487bfda54dc487f7d964dc487fdd91cdc487dfd8dde4487bfda55e0487bfda45e0487bfda25e0487f7d964d4487fdd91cd4487f7d964a4487bfda4ca4487fed914a4487fed8dca4487ff99fc74487ff99f474487ff991c74487ff99ec74487ff991474487ff98dc74487ff99e474487ff98a474487ff9875cc487bfda55c8487bbda55c8487bdda4dc8487bfda45c8487beda45c8487bfda3dc8487bf5a3dc8487f7d91d34487f7d91534487f7d8dd34487d7d9e534487f7d8d534487f7d8a534487dfda68f44879fda68f4487f7d964f4487fbd91cf4487dfd9e4f4487ff9874f4487ffd21cf44
  | 2 => 0x5fb284af7e2dfb284af5e2dfb284af7a15fb284a77e6d67284e77dfd67284e73d65df284e77d65d7284cf3dddd7284c3fe6dae984e3fe3dae984e3fe2dae984c3fe05ae184e5fe05a6184c5fe05a6184e5fd65a6184e6fe059e184c6fe059e184e6fd659e184c77e0596184e77d6596184e3fdad4e184e5fda54e184e6fd9d4e184c6fdb5ee104ccfda5ee1048efe6d9e104c6fe059e104ccfdf59e104c7edb5ce104cbedadce104cdeda5ce104ceed9dce104c7f5b5c6104cbf5adc6104cdf5a5c6104cef59dc6104cf7595c6104adbe4d0b184aebe450b184afae250b184afb61d0b184e3be5dace84ebbe3dace84ebbe2dace84e3bdad64e84e5bd65a4e84e6bd659ce84e73d6594e84ebbdad0ce84edbda50ce84eebd9d0ce848ffe6d0b084adfe4d0b084aefe450b084afde2d0b084afee250b084aff61d0b084a7de6d67084e7ddfd67084cfddfde7084e7dd65e7084a7de6d4f084e7ddfd4f084e7dde54f084afde6d0f084e7de5d0f084a7de5d0f084e7de050f084e7dd650f084ef5de50f084e7dd4d0f084afde6d0b0848fde6d0b084a7de5d0b084adde4d0b084aede450b084af9e350b084afce250b084afd61d0b084ef9dfc77084e79d6477084ef9de477084ef1de477084ef9d0c77084e7d965bf084cfd9e5bf084efd90dbf084ef9875bf084c3fe6dae784e3fe3dae784c77e6d96784e77e5596784a7fe650e784e3fdad0e784e5fda50e784e6fd9d0e784e77d950e784e7dd0d86784c3fe05adf84c5fe05a5f84e5fd65a5f84c6fe059df84e6fd659df84e77e5d95f84c77e0595f84e77d6595f84ef3e3595f84ef5e2d95f84c7fe0d4df84e3fdad4df84e5fda54df84e6fd9d4df84e77d954df84cfbe0c75f84ebbdac75f84edbda475f84eebd9c75f84ef3d9475f84c7de0585f84e7dd6585f84e7dd4d85f84ef9c7585f84cbfdfdacd84cbfe6dacd84c3fe05acd84eb7e3dacd84ebde2dacd84c7fe0d64d84c5fe05a4d84cdfdfda4d84e5fd65a4d84c6fe059cd84cefdfd9cd84e6fd659cd84c77e0594d84e77d6594d84e3fdad4cd84e5fda54cd84e6fd9d4cd84eb7dad0cd84ed7da50cd84ee7d9d0cd84ebbdac74d84edbda474d84eebd9c74d84cf3e0c74d84ef3dac74d84eb3dac74d84ed3da474d84ee3d9c74d84c7de0584d84cfddfd84d84e7dd6584d84e7dd4d84d84ef5d0d84d84ef9c7584d84ef1c7584d84afde64fcd84cfde0cfcd84ebddacfcd84eddda4fcd84eedd9cfcd84ef5d94fcd84ff1c74fcd84e7fa5d0ed84a7fa5d0ed84e7f9650ed84e7f94d0ed848ffa6d0ad84a7fa5d0ad84adfa4d0ad84aefa450ad84afba350ad84affa2d0ad84afda2d0ad84afea250ad84aff21d0ad84e7b96476d84efb90c76d84e7f90d3ed84a7fa5cfed84e7f964fed84e7f94cfed84efb874fed84a7fa5c6ed84affa546
  | 3 => 0x4f464789ffa4bc64789bfb65460789bfb64460789beb64460789bf962c60789ff949460789ff96542c789ff95a82c789ff964c2c789ff951c2c789ff96442c789bf96442c789ff95142c789ff94dc2c789ff963c2c789ff95902c789ff94d42c789ff94a42c789ff94f42c789ff84f42c789ff948c2c789ff94642c789c6fe05eb585a7fe5de3585afbe35e3585a7fe65e2c85e6fe41aeb858ffe2e0a385c7fe0d5e285c7fdb5fdb85e5fdb51db85a7fe5dab285a7fe5dfb285c5fe05f3285e5fd65f3285e5fdf157285c7fe05af205cfbdaddf205e6fe41ae985a7fe65169858ffe2e0a185c7fdb5fda85c7fe0d65a85e5fdb51da85c7fe0d55a858ffe2e09485c7fdb5fd485c7fdb5f5485e6fdb515485e6fdb4dd485eebe41ace85e7bd65a4e85e7bd659ce85afbe6514e85e6fe41ae785a7fe651e785a7fe6516785a7fe64de785e5fe4996785a7fe650e785a7fe64d6785a7fe64a6785c7fe05a5f85c7fe0d5df85c7fe059df85c7fe0595f85c7fe0d4df85cfbe0c75f85c7fe0d65885c7fe0d55885c7fe0d5d285c7fe0d4d285cfbe0c752858ffe5608d8597fe69b4d85c7fe05acd8597fe6964d85c7fe0d64d85c7fe05a4d85c7fe059cd85c7fe0d54d85ef3dac74d85ef3da474d85ef3d9c74d85ff1c74fcd85ff1c74c4d85e7bdac76685e7bd9c76685e7bd9476685e6fdb4a5185f6eca535185f7ac7535185e7edad5d185e7edad4d185f6ecdd4d185b7ee5d0d185f6edb4a5185f6ed4ca5185efadac75185f7ad6475185feacdc75185feaca475185e7edad3d185f6ecdd3d185f6eca53d185b7ee5cfd185f6ed5c95185f6ed4c95185feac7495185b7ee5c6d185ff2c746d185c7fe0d4dd85cfbe0c75d85c7fe0d3dd85e5fdb51d685f5f51d2d685f5f5b51d685f5f5651d685f5f564dd685e7f56595685e7f55595685b7f65d0d685f7b56475685f5f51d3d685f5f4dd3d685e7f5953d685b7f65cfd685b7f65c6d685ff34746d685f7e5648d685fde51c8d685fce4dc8d685f7e54c8d685fee4a48d685ffa4748d685f7e53c8d685fee4948d685c7fe0d64b85c7fe0d3cb85e7bdad64785e7bd65a4785e7bd6594785f7b564b4785fdb51cb4785bdf64df8485d7f565f4485e7f5ad5c485d7f5f554485e7f5ad4c485efb5ac74485efd5ac94485f7d56494485f7d55c94485fed51494485f7d54c94485ff947494485fed4948c485efe5ac8c485f7e5648c485dfe5f48c485f7e55c8c485fee4dc8c485f7e54c8c485fee4a48c485ffa4748c485fec4948c485efd5ac2c485f7d5642c485bfd6442c485f7d5542c485f7d54c2c485ff94742c485f7c5342c485ffc4f42c485ffc48c2c485a3fe5de3584a9fe4de3584aafe45e3584abbe35e3584abfe2de3584abde2de3584abfa15e3584a77e5dfb284ad7e4dfb284ae7e45fb284af3e3
  | 4 => 0x7ddac96689f6dd1496689adfe4e09e898dfe4e09e89cbfe69ade89eafe41ade898ffe69a5e89e3fdad5de89e3fdb51de898ffe699de898ffe6995e89e3fdad4de89ebbdac75e89ebddac95e89c7fe0d4de09cfbe0c75e09cfdd95d5e09d7dd4dd5e09df9c75d5e09d7f54dc5e09dfb475c5e09c7fdb5fd789e5fd65a5789e5fda5557898ffe56091898ffa1609189c7fdb5fd189c7fdb5f5189e6fd5d9d189e6fdb4dd189e6fd9d4d189cefe08a5189e6fdb4a5189eebd9c75189f6dd5c95189f6dd4c95189fe9c7495189e7edb4f5189ebedacf51898ffe5608c89c7fdb5f4c89e5fdb5f0c89c7fdb5ecc89e77db4d4c89e7edb578c89bbee5578c89bdee4d78c89ef6d9578c89bfea1578c89afee60f4c89e7edb4f4c89ebedacf4c89e7edb4bcc89cbfdfdacc09c7fe0d64c09c6fdb5ecc09cefdadecc09d6fd65ecc09c7fe0d54c09cfddadd4c09d7dd65d4c09d7dd55d4c09d7f565c4c09d7f555c4c09dfd495c4c09bdde4da8589bfce25a8589e7dd65a4589d7dd5dec589e7dda554589d7dded4c589df9dec74589fbcdacf4589f7cd64f4589efcda4f4589f7cd5cf4589fbcd1cf4589f7cd4cf4589ff8c74f4589ffc61cf4589e5fda51e589f7ccf42e589fbccf42dd89f6f55de9d89e7f55d9dd89f3f55d15d89e7f55d95d89ebf51595d89f6f5e94dd89e7f59d4dd89f3f5154dd89faf514a5d89feb5e875d89efb59c75d89fbb51475d89f7d55c95d89fad51495d89f7d54c95d89ff947495d89bfd62dc9d89bbf65579d89bdf64d79d89bef64579d89bf763d79d89bff21579d89a7f66135d89f6f5e935d89e7f59d35d89f3f51535d89e7f59535d89f7d49535d89f3f55cf5d89faf5e8f5d89ebf59cf5d89ebf594f5d89f3f54cf5d89fbb474f5d89fbd494f5d89bbf6548dd89fbe4f48dd89ef759465d89fbe4f465d89bbf65461d89bef64461d89bfd62c61d89f7d5642dd89f7d55c2dd89fed5e82dd89fbd5142dd89f7d54c2dd89ff94742dd89f7d5342dd89fbd4f42dd89ffc4f42dd89fbc4f42dd89e5fdb51d689edbda51c789ff8cf42c789fdb51cb4789bfb64da8789bdb64da8789bfb63da8789bfb625a8789bfa621a4789fdb5a51c789bfb654dc789fdb51cdc789bfb65590789bfb64590789bfb62590789fdb51cd4789bfb64ca4789feb514a4789feb4dca4789ff951c94789fe951494789ff959094789ff94d494789bfb65578789bbb65578789bdb64d78789bfb64578789beb64578789bfb63d78789bf363d78789ff949578789bfb21578789fbb51cf4789ff9494f4789bfb63cf0789bf962cf0789bfb654bc789ff9494bc789afb6608c789bfb6548c789bfb64c8c789feb4dc8c789feb4a48c789fe94948c789ffa4f48c789bfb64c64789fdb64864789bfb64464789ff34d464789ff949464789ffa57864789ffa
  | 5 => 0x7f7b5658d697fdb51d8d697d7f5fd3d697f5f51d3d697f5f4dd3d697f774a53d697b7f65cfd697f774a535697b7f65cf5697f5f564bd697f5f554bd697fd74a4bd697f5f53cbd6979ff6688d697fe74a48d697f7756465697bf764465697f7755465697f7753c65697ff64f465697fd64bc65697b7f65c2d697c7fe0d3de96e7ed3d7de968ffe6d85e16cfddd585e168ffe6dac596c7fe0d64596cfddfd84596e7dd6584596cfee0cf4596ebedacf4596efcd84f4596f5bd651da8f9fbe691d48fb7be54de68ff5bd1cde68ff5bd1cd668fb7be4ca668ff6bd14a668ff6bcdca668ff3bd651de8ff9bd1cdde8fbebe45e1e8ff9bd1cd5e8f9fbe68a5e8fbbbe54c5e8ff9bd1cc5e8ffb9cfc95e8fd7bdfd6578fddbdfcc578fcfbdfd9518fcfbdf59518feebcdd9518ff6bca53518ffbad1cf518fefad94f518ffbacfcf518fd7bd65f4c8fddbdfdf0c8fddbdf9f0c8ff5bd65f0c8f9fbe691cc8fddbdf1ecc8fd7bdf554c8ff5bdf154c8ff73d64d4c8ffd3d1cd4c8ff73d54d4c8fddbdf1d4c8ff7ad64f4c8ffdadf0f4c8ffbad1cf4c8fff2cd4f4c8ffbacfcf4c8fbfae54bcc8ff7ad64bcc8ff7ad54bcc8ffdacc4bcc8fd6bd65ecc0f9fbe6cfcc0fdbbdfcfcc0fdebdecfcc0fdf9dd4fcc0f9fbe6d1c58ffd9d1cc458ffbad1cf458fff8cc4f458ff3bd651dd8ff3bd64f5d8ffbacf465d8ffbacf42dd8fd7bdfd6568ff5bd651d68fedbd1d9568ff5bd1d3568ff9bd1cf568fbdbe54bd68ff5bd64bd68ffdacbc6568ff7b564ed68ffdb51ced68fd7bd65f4b8fddbdf51cb8ff73d6464b8ffd3e4864b8fff2cf464b8fff2cbc64b8ff7b564ecb8ff7b564b4b8ffdb51cb4b8fc6fe05eb589c5fdb5f750987fe3e0ac89c7edb5cb489cfeda9cb489d7ed65cb489cfedf9cb489e7ed65cb489e6fe41aeb898ffe260a389bdee21a6389e5fd65a6389b7ee21a6a89e7ee21a6a89c7fe0d5e289c7fdb5fdb89e5fdb51db89adfe4dab28997fe6967289a7fe6957289aefe45cb289c7fdb5cf209e6fe41ae989b7ee21a6989a7fe6516989a7fe6165a89e5fdb51da898ffe2609489c7fdb5f5489c7fe0d5d489e6fdb515489e6fdb4dd489eebe41ace89bfae21a4e89afbe6514e89bfce21a5289e7ddad5d289f6dd5d15289e7ddad4d289f6dd154d289ef9dac75289fe9d1475289adfe4daaf89c3fdb5fef09dbf61dfef09c5fdb5f6f09cdfdadf6f09c6fdb5eef09cefdadeef09cbfdfd9ef09cdfdf59ef09c7fdb5e6f09c77db5e6f09cf7dade6f09cf7d9de6f09cbfdfd96f09cdfdf596f09cefded96f09dbddfc96f09ddddf496f09df5de496f09c7f9b5bef09cff9adbef09cff99dbef09cff995bef09dfd895bef0987fe560a68987fe3e0a689e6fe41ae689c7fe091e689a7fe651668997fe6996689c7fe6996689c7fe08d6689a7fe64a6689e
  | 6 => 0xcbac6fdb5ecc3accfda5ecc3acebded8cc3a8ffe6d84c3acefded84c3acfddd584c3ac5fe05a45bac7fe0d5c5bac7fe0d4c5bae5fda54c5bae7dd5d845bae7dd4d845bae7ed5d7c5bae7ed4d7c5baefccc57c5baa7fe5dab2ad8ffe2e094ade6fe41ae7adb5fe54de7ade5fdacde7adf4fcdca67add5fe051dfadd5fe04ddfad8ffe2e09eadcdfe091deadd5fe051deadf1fd651deade9fe091deadd5fe04ddeade3fdad3deadf1fd1d3deadd5fdfd657add5fdfd3d7adb5fe5cfd7ad8ffe56091ad8ffe2e091adcdfe091d1adcefe08a51add5fdf53d1adf4fcdd3d1adcefe08951adcfee08f51adebedacf51adf9ed1cf51ad8ffe5608cad8ffe2e08cadcfee08f4cadf5ed64bccadf5ed54bccadf5ed3cbccadc7fe05ac5add5fe051c5add5fe04dc5adebedacf45adf9ed1cf45adf1fd1cf65adb5fe54be5adf5ecbc665add5fe051ddadf1fd651ddada7fe651e7a1e5fda51e7a1c7fe05a5fa1c7fe05ad8a1e5fdad5d8a1a7fe65e26a1c7fe05a5ea1c7fe05ad7a1e6fda53d1a1b6fe5cfd1a1f6ed5cf51a1faed1cf51a1f6ed4cf51a1f6ed3cf51a1faecfcf51a1c7fe05acca1c7fdb5f4ca1e5fdb5f0ca1e7edb4bcca1c7fe05acc21cfbdaddcc21c7fe0d3cc21d6fded3cc21c7fe05ac5a1c7fe05a45a1b7f65cd5da1b7f65cc5da1f5f55cc5da1f3f55cf5da1f3f54cf5da1f3f53cf5da1b7f65cbdda1f6f55c8dda1f6f54c8dda1f6f53c8dda1f6f5348dda1faf4f48dda1fae4f48dda1b7f65c65da1fbe4f465da1b7f65c61da1bbf65461da1bfb63461da1b7f65c2dda1fbe4f42dda1a7fe5dcb397a7fe64de797c7fdb5fef17c7fe05aef17c6fdb5eef17cefdadeef17c7fe059ef17cfbdaddef17cfbd9ddef17cfbdfd8ef17cfbded8ef17cebded8ef17cefded86f1787fe560a69787fe2e0a697a7fe65fa697b7f61dfa69797fe69866978ffe2e09e97a7fe6205e978ffe699de97c7fe059de97c7fe0d3de17d7f53dc5e178ffe56091978ffe2e09197c7fdb5fd197c7fdb5f5197e6fdb4dd197e6fd9d3d197cefe0895197e6fd9d35197e7edb4f5197a7fe6164597c7fe05a4597c7fe059c597e5fda51e597f6f55de9d97e7f55d9dd97f3f55d15d97f6f5e93dd97e7f59d3dd97f3f5153dd97faf51495d97b7f65dc9d97def5e9c9d97bf763dc9d97b7f65d79d97bbf65579d97bef64579d97bfb63579d97a7f66135d97f6f5e935d97e7f59d35d97f3f51535d97faf5e8f5d97ebf59cf5d97f3f54cf5d97f3f53cf5d97f3f534f5d979ff6688dd97bbf6548dd97fbe4f48dd97fbe4f465d97fe75e865d97f7753c65d97f7753465d97ff64f465d97fb64f465d97ff64bc65d97b7f65c2dd97fbe4f42dd97e5fdb51d697fd6cbc65697f5f51d2d697b7f65df9697b7f65da9697bfb635a9697f5f5651d697f5f564dd697fc74dca569
  | 7 => 0x420904010c20008431086000441088621086219463288c7294a5194c5198863988208c21104620102218c2118820008a2108221040310822104232086010825110230000108000088411846118c6308c62088410886218c63188621884210c658ffe61f52bdc5fdb5f6e3dd5fd65f6e3dddee21f6e3dc7fe05a6e3dc7fe0596e3dcdfdf596e3dcfbda5dee3dcfbd95dee3dcdfdf586e3da7fe65c2cafb5fe4dc2cafa7fe5de35a3afbe35e35a3b7ee25e2ca38ffe2e0a3a3c7fe05af223cfbdaddf223a7fe651e7a3f4fd1cde7a3e6fdad5d2a3f8ed1cddea3b7ee5de1ea3bfae35e1ea3b7ee5d91ea3bfae3591ea3f3ed1d3dea3f6ecdd3dea3beee6895ea3f6ed5c95ea3faed1c95ea3c7fe0d5e28bc7fdb5fdb8be5fdb51db8bf5dd651d88bf5dd1d5588be7ed5d9de8bebed1d9de8bf3ed1d55e8bf9ed1cdde8bbeee45e1e8bfdcdf4c5e8bfdcd1cc5e8bf9cd1cc5e8bf7cd54c5e8bbdee4dc1e8bbfce2dc1e8bf1fd1cddecbb6fe45e1ecbb3fe54c5ecbf1fd1cc5ecbf3dcfc95ecbd5fdfcc57cbf3ed1cf51cbf3ecfcf51cb97fe6d1c5cbf5dd1cc45cbf3ed1cf45cbf7ccc4f45cba6fe655f33be6fd5d9b2bbc6fe059b23bcebd99df23bcefd99d723bc7fdb5cf23bcefd99cf23bc6fe0d9a9bbe6fda59a9bbe6fd5d9b0bbe6fd994f0bbc6fe0d9a7bbe6fda59a7bbe6fd99967bbd6fe05998bbf4fd5d998bbd3fe05158bbf1fd5d158bbf2fd5d152bbf2fd154d2bbe6fd5d9afbba7fe5d92fbbafbe3592fbbe6fd994efbbe6fd993efbbc6fe059af3bc7fdb5e6f3bcefd99e6f3bc7fe0596f3be6fd994ef3bcefd99d6f3bc6fe0d9a6bbe6fe099a6bbe6fda59a6bba7fe65e26bbb7f61de26bbe6fd99966bbe6fd99866bbf2fd14966bbb7f63dc26bbeafda599ebbf2fd5d99ebbb3fe5de1ebbbafe45e1ebbbbbe35e1ebbbbf61de1ebbb3fe5d91ebbeafd9991ebbbbbe3591ebbbbee2591ebbf2fd994debbeafd9985ebbf2fd993debbd6fe05997bbd3fe05157bb8ffe2e091bbd3fdfd5d1bbc7fe094d1bbd3fdfd4d1bbd3fdfd3d1bbf3ed5cf51bbf3ed4cf51bbf3ed3cf51bb8ffe2e08cbbd6fe0598cbbe6fdb598cbbc7fe093ccbbfaed98f4cbbf3ed3cf4cbbe7edb4bccbbd6fe05985bbe6fdb5985bbd3fe05145bbf3ed5cf45bbfaed98f45bbf3ed4cf45bbfbccc4f45bbf3ecf4665bbf3ecf42e5bba5fe5de34baacfe45e34baadbe35e34baadfe2de34baadde2de34baadee25e34baadfa15e34baa5fe5dcb4baacfe45cb4baad7e3dcb4baadbe35cb4baadfe2dcb4baadde2dcb4baadfa15cb4bae5fe3da67bae5fe25a67bac7fe0d3d7bae5fda53d7baadfe65f0cbae5fdb5f0cba8dfe69a4cbac5fe05a4cbaedbdf18ccbac7fe0d3ccbae5fda53ccbae77d953ccbaededf17ccbae7ed3d7ccbae7edb4bccbaef6d94bccbaefad8cbc
  | 8 => 0x70021030006007a06000c00ec0c001801d81800300380a58180030038041818007014801c052079002001c008004002001c052010206001d008007008503000e010a06001c02140c0038042818007006000c00e0290020040090007014801c0f205a00380a400e05a003816800e05a003803005200703c80a6019b97dcb0020018007aa0a6fa29a019b59809519228e68b38848598287f07a676f71f6e86af6886676325ff5c55845565284fc49e4373e83933472f62aa2712361fd1bc19d17213b0bd08304f000210421084318841104221044109822088000002210881084000844600401104020842208003114431086210882108211042210842288421888210c4210c21084220042200821108411842000042108001884208001084a410843194831086210842188651084108420108831082410841088211084108421180610882108423184210042108862108221040208442088221044310440080001084110842108211000010421108a300402100421088310c420904520822110431044210821084231082108021000410040208c62088410084208800088e01002210421084c210420004220042008401000260882210841104001082210442104411082108842108220842308c41088421084108442108421084210421108421084210862084421084210862290631884210c62108221004210842088431084211020080411082218862108431084218c42188632944210c2218c4218c230844208822104220884210882104210884000421108421082208822088222086208c6318820104411044200401088221040100820008410140100442108831044200020004210800008040080010884808c4100c012080100001004212042110c440086408804004620842310002088210842320821080430806000024088821084210842110421084210842108421082108443108431084310863108421084210842104000044110842084220844208820088211042310c410842110841004220880510020008420884208822088220040110461000000982208802184242108221084210442104418c821100410082208421108421084210842108421083088621102108842108441046410840208421088421084208631846310c8220842108432104410882188421084218843208431088108c821904320c421042110c6308c632086210c61104211082410884210822108308c821088318843188620884218021088621844218821084231044010842104421084210842108411042208442084401044218882208421084208c4108842084620842310c4108841108411086210841088421082310c6118c4318c0210c83008200000208801084010000008042100421042110422210210882118440004400802008c01084420844200863108
  | 9 => 0x40418004000803c00e003007801c01200c004817800e04a00d018405a02a030818401701000880d4022005a06004602140c801802c016007808002c098007009802400e009026002400a003a06000c00e00c003800c00e00300d00a403400300380a405201a003800c01606100380b800e02e009812400e04a0038058016061003812400e01a00581860b4009003801c0060090038128012007024802c05c01300580f800e0030158068012003003800c07c01601f00f80540110078040818007009804592a00800380180eac95005802481800701f007007c01c007800c00e011015801c06a0110138044016c95003804400e00500580f8016007230801c0f8007027013806c00700880f800e03e01f000c018003003803000600f003800c00e003001812a09c013042001c09404a003812800e46100d000c00c0030060024018009003802400e04a00d012800e013004802401200900d1184034009003802400e007001800c00780c003801800e007003000c027010003404000e0060018e58034010808001800e003003004000e006008001c00c04803c803000e011007801c0ec00603c81680c280c0058125018013030a03000e049406001c00eb960038020022048024017009005c0240170090029024017201900c806017000f00c80600250180290078030090048001a03001601a0038121018009014801c0ee05a008803d018003007a03000601a003804c03480c00180a403401a34d00200ec05c003801c022007008801c0b4007006004400e016406000e72c00600b001800e00603b802c01780c0058e58022396e4a804501800b00400450180084060041018010806203001280c008802c021c95004ba6802280c003801800e006014801c00c007003001800e007003003c00e0060038018032007003006400e396806001802a01a003005400e00600c801c72d00c0033e76018019009c03000e00603c9a680f2013007801c00d00c03b806400f00c003006401e00700340300ee00f003801a01807700c804e0180067cd801800e077009803c00d00c1cb01dc03200f00340300ee019009801e018f970084030032013007801c00d00c7cebe5e01800603b804c01e007003403072c07700c803c00e00680601dc02600f34d001a018f97003003000e025008800c02600c004800c00600c004802404e01a001809801201a009802401e003007802403400f00480a801800b430813805a42800420a804840c004001d05a82a012002081840c001804c0120070018128094007027001c00e013006004403400303080b409c01a008c18405b02d027006801e003009803000c003003000c034006001806800640c00180180ee019003805481900c20600300160090089030016003206103081840c0049030022009004c04472dc955cbb0300060
  | 10 => 0x1a00d006403c00e005006801401900520b402610d025010002a10d087011021c10e013806801e01a409800000001a000006800002d006e03003a003006007400600c006001821a0490868830026003004843402610d001807402605182240400140090868024012003004802400020c0000438418009004802421c10d002001c21c10d002001c21c10d002001c21c10d002001c008007087043400800708704340080070870434008007087043400800708704340080070870434008007002001c21c10d002001c21c10d002001c02e013001801c00e001004200c00200702e802000e10e004183002e013001801c00e004003801002e013001801c02e013001801c00e00100b804c006007003800402e013001801c002007002001c00e004003801021c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c21c10d002001c0160010038004016404005800400e0015060005418008201800400e0010008004008007002001c008007002001c008007002001c02e013000001c00e003000817409000700b804c008007003801000e003007801c02e013001801c01e00700380040f210d00380100080070870434008007087043400800708704340080070870434008007087043400800708704340080070870434008007807201000e001024004000e0010874040090001106000c00e07902d001c0f2004008012000e017009800000e00f003805c026004003803c00e00f003803c00e00f003803c00e00f003803c00e00100b804c00000700b804c000007003800c02e013000001c00e003003801002e013000001c00e0032070022008008000801c008004003801c008007002001c00800b402002d008001207201081c8042070021008017009800000e003003801000e40e802002001e007007801c02e013002001d418001013802000e017009801000e00f003817541800700b804c008007007801c0baa0c003805c0260040038174010007003800c00e003003800e41920c906001c0160100038004020007000843801120c005843801720c208043a418410087483002e013002001c01e00702e883000e00300381e4418010003800421c41002400040100010008004002008000803001000100b804c006007003800400e00408704340080070870434008007087043400800708704340080070870434008007002001c21c10d002001c21c10d002001c21c10d002001c00e001106000401e007000805c026000003801c006007002203a008017009801000e00f003801041805d003801c00620c03c804000e0010872
  | 11 => 0x1800e00320181e632e0610016037018003003012c04c006007801801400f03c81e481801c02e001800604c003000c0320240030020006007003800c01e006018009800c03a00380e400e02a003100c000010003005701a003000204d027013409804c012003007801981800f003050001e006007801828000f003003c0b800f02e003800c00f003050001e006007817001e05c007817001e05c206800c00140d001800281a000007801c02c00f003003c00c00f003801981a003000005c000049806002c02e013806000c01004c003000c01c01c003017000600602e002000603000e001903a4138060126018009002003c21c0480a0003c00c140003801021c00e003001c008004006043821c006086801800680300000000020010000008004000007801803a00300e800c00e01100b000c01e007007801801e006007001821c007020001821c006009802821a00f003803c00c008007003c03200e003006400e0031cb800c0b8007001843800e004087007c00e000001801c04001f0010019820035606001c0060060018000818003001103000000d006000c00e40d000003081a00c086806800600700d000c002413000801901800b00e843821ce95004965c21a006001801801ac0c01800c001b40c001503000c006001002c0aa049005802821a013c06603000780c001e03000680c008002000640c024812401b40c018107409203020e812481810d003043421a10d001002c00680d00300240120030058010088040086802d01a006002002400e597806843400c003007843400780c004806402b80c00301e401e01311408a003300c024803c21b00c8064033018006c06003f018006007843401e10d003603000d80c0000435018010007a03000c006006043421a00340600190180100a0603001e10d007801800c00f004843402610d00c803c00d29a4060064450019006043421a006c06043400680c00304350184040062040006810008002421a00c3cba040006009086801800700c8061e5c01204900c802c01202400b00b0000027003011c00c007001809800c05900300e602681000d009c034c13004200c00c03f00300fc00c41000b00b0000047003009000c00700180f000c02700300d800e025003001c006054003019800c03a00380e400e006007203800c025003104c01e006007801801e006013001882600f00d003c00c00f00d009c00c02640980180400060138068048813003204c020006013801804a0060130018048006008001800e0050030000048016003000004e01a0120018040006012806885420c015000000002d000204000000d003801c00081340984380260074080006026813007001c21c00e000a04c00e013003a041020013408001d0200244098019026000409803c00c02d00000b632e02d0868068854
  | 12 => 0x80060260034016009000850141c001003800400000104400040010100068502020006006803400e007008801c01a007409800400e00f003806401a019507003400e040007001c00c00d003200c01a007107083800c006009800c00410e003843421c005003a040c18005003e04000e10ec08001c21c810003804c21c002001801c21a004087006821d81000d2040c1800300d043b02001a408001c01e007007801c01e007007801c41c10e0040038010008a080068026003001011000ea0e004003c03400e00d001c21c0070008024002c10003843821a0030038002820007001801c006007000005c026002003801c006007001801c00600e000883800e001107204000c04b00d009400c007209801c00e0070038010000061022001e32e10e024801c01400a003801c00e00f087001c00004b00d0434002007006043421a10d007806800004b00d007421c00e003802400e00700e0058088007003c16821c5970000018002813003803401e006005009c00c01b003002c03800602a812400c01b0030028026007086806c03201f003003801000700d8018820006007801882600700d8018038006004002905401000b004c05402a00500a8012009003023408e0440048434032013004000800c0020098028038006007801800c004208005804001f0020018280c10003104000c02c20800188200060038000002006401801c003410003805c02600f000002c02e013106002803800600e000400c0040039030016001004801c008050024801801e006003801c02200f003811c00c04d003001800e00c0000020018001004807000c01c003000581c03001a802800e001808000400c001000802883a05002800d401a03020e8140111010018043401041d004843400210d0008434016008004802c01040e087203421a0090037a5400e001026802400c00e000800800200100384340a004a000805421c10d003800406c001003801c00e10e130801d85410d000843421a10e048010007e009003043800e00f003801c00e003001800001e007003800c01e003001000800e002003843401a413006a03400e00d006801c01a00700d003421a007001008800e10d011000004410d0048030013013000c04c002013003003400e10d409802021a00800420a1818802004007c032007a08002001200900d002005a00801a006a820008003800a05000841b0020012009000802400e009003c0a001200060608100040020000810004002000003c01202d01101100880070038000012006003000d02600d006801e020001006800072e00d004800000e0000048018003196086c658002008000801c001810004002000c009003001c0020070008034002019402802801e00a00b804e018003004304c01c01900504380f2c0c03cb03000610e606001000c04b026
  | 13 => 0x10e086801c008017009800c00e007000043821a00f003803c03400f00d003c00e0040078008034007002009c00e007012001c016230007801c048007005803c00e00a00616700d8061022843821a002002000800400e001043404c00700e001c07200a016803001600401680c0060002004801001606982d011001600a087043421a007002000208010d006043421a00f00300b40a040300aa8b400c019400a00141810d906043421a035802801888120e9060065006015514001945a00691400180328014000055446006911801801a006005801c82000b208104145a0064080058058000914001a44600600ca005000a0c08680d001d20e906104002d01090640024190030248064016015006a83000c05900e104c00c00700080180a
  | _ => 0

def or04hash10 : Nat → Nat
  | 0 => 0xba36ace543dbe1adedbc9290623a6cf00cb5a1f17d7d95740000c822c1d355670000148f34c21b2fdd97c5823ab20050da0542894cea49d003e982864aed3096dc930190e308753ac22372703438e4e4000033cc0000431ccbfe214484279154846dd41a00009d7af4669c81bbd901ec3ac5325a0000f920a8c25d7b2432c501ebf5014dbd5b118431c74950000064007226551011350837b0c7504f21fc1141f1d8ed52a2df00008cb20c6ea559f38b297553d30455e1990000bc1ee51d2897bc6000002abceb34d01b00007c288b363f0283800041340812080d00111400f4000117848e40937810b87f0b8684f200c82456033f0301001081c8040405188924d0280c8e0208109b601129a0083f0ba54f00e0802114081806424061502c084c1681c1c090e0c438f4088080407081712004041b8100004818e43a20000061500008080423824ac0c00340000f019c05203288040a522f8748c180e008241439b18300b251e40231010043202021f0d62816804dc000086d0e011505004617181804061b0008c10018080046138e05c14038086403108001a050011c5808000584c2b00030ae070000c98082b9190607000005005000180209d714092120485c0402191340c152c11c0047090ac0a041283436000780c1a51218506800001488801248740c1c0b80d86170900c001000010060a2d01400030282c06260301c0a0d00858be19100000ca155834062102034241c4c0500c140f0180e000783c08060802c1016108141e07030b030001083c080b00801962d0b004064d0150402100480c0210008100a042682434d10015c0016098200004000041c180f85110071988c00030b9a00607082580c02008409861140042601008007804000202e06001280419008b0011c3401c281200054c201609782c08008040c030480816000881400000a800360c0f0142001048405402001100433108401a08079440005040d4043e0008812040005c000301815222000004380c010a80a0a020002004111040210110200001000600e15008000a39020bcee770107c000d15070080017020480e0b8340c08198000c09050884405008101e010108432010981020160781404090683c2005008082a0105000080f2d004022a0001cae00000300418008080036088ccba180100cb802140905a1e0101c0e03108080409000048a020200406150102400070e80c2c07010240a0900818ca000203c0a0001044027503808481101824561c00804062b03054020b0980004010102c4c3d0b0640e0d0005404030004c0805068b40600058782005010100040108540880000100005110600c020100c1600018001020020cc60003d81c00020602c28090101806240003c2e1a1f8741414168100601000642e006680034010102c0a0000800441f060040600
  | 1 => 0x7b00001272229b919e5d044a730000211d0000a0950bf9b93600000000000064bb63f0adbeed8a2cded87680a462b491b0b9ab10a8baa37dab0092454c8b2b98bad31b0000c91ad578a1b499caddaf199cfc6800003ad6d81d85ab6124b4927819158100a00000c47c141d0000694cf2449aa90003392ab246000000003ce65c470000c25eb0750000b2fbb35f2d2fe24c3caad17f03a370c899d8d98d9d1c74146b0643bc5c23645a23c0bb6000000000b305a00ca93984eae5170000bc22000000000000e2decd262bf0805c00005a2904b9492632e1d367611fdd1f300b50804956ec5fb809251171bd03c9222199920000c0e8b110b8e5d86375a67398e08ea9d90000124f0000d9fe687941eb5b29742800002871d2f109b800004a5dd561449f7abdf8d8dccbf9c0f2120000620b8cf3e54e78a90000bd4b000095ba000019680cf2d59efd53f232913aea9ce508f5be6b757a0bb2b3a3b80000b115b92f74194cc2fd8d345300006ccd9a382c55dc90105daa5200002c1241624aa4787f18fbbaa7b58b50ab5409521975974402ad330964aab8126892f288036a7c0502b547102a00006c56e08100005c9562529b91432c2c3912017480f81724343a61333f8b316b078c179bbc1267a27500007b2c000071d93baf4518ca720000285f000074eda91993e13d410000305884214260a8ec899699f699705c50641104e604169d5f93111274dc8bc034a532553be10900000000b00e00005cd82d2449030000a2f7f57cfcc4f8605459695d92552a7d2280627f0000bc2b12a044ddb57b000000000000c1b79b941213788e81bfe27d3a9070930afc0000334771e8d9a20000338c00000000ec8de50b71edc03b0000a0d00bb0d9446397953160fb3d87a23db912437e681f210d315050f694b4336293a5993a0000bbeb99d52d609c7c648ef0dc73f1694ab2e46beef51513a42503d5a7dc668215357fd083000024d8583aea234caf4a6929baf1405b1f8d927b69c592824813d7a2a6f82488430000735d89e0b27bd1a76c1cb84bb3d0347b68968c210000f4bf782900007380dd56b99b1cdcf082ebcc02515a7998ff78b662636aa20000244c4a8e314900008a2b0000000000e60ccaad9b00000000540ec86f0000000003071b8fcd7e006b31204071a1e9f89a9cf453c6616aed6a5ba6abfa0c65f470b0eefa00e58e0000b8bb806d000034a048f2b549b570abab186bf183000000002125b2ea22dc14c0b008094071922abba0fdd13de48a9bb1c491ac24dc34f452cc92fd3c1d3f3c300b3c755e0d84d3bd5b4289e8d4ec897e706fec641d8141dfdbed00002997adb7a0134a58c16428ead80d00000000328400003c6f0000db33b99dd5666ce4000051f564d01801a8497024688208b379e689744b797136fab40000000075737cbc0
  | 2 => 0xc3c38f8403933646b11401a0ace000008f90000240d0000490af0e0c0df60f099323c2d1bf770f163d894d490c1ca8cb96683700000521b4b2eac710000bb7368754a7e6a20fa622d23bd18d4d6434a4d8c529f7069d516e2aeb2c342921ba2caae13a178c163b7785d50c4207ef59dfb52e84ddc6b3b3282fe98860c85d327ba9888f0ba8fe4cc29b0fca28b3d3c53cd90f8f565a279a000fa28522947c9ccc4173d5a0cdf428d62b93c1d99be896d157ed91c32f4f4d71151d328c1ba61e0241514a8d4a7a2170000e818c50d93ea5b269ba979c782a173e300004d170000b2d7e53dc596a3965814bba75509c8de29c118c3e23c63d40000e4f8650e0000208c00002874817a3394dc4c6020b3da34646481f05700005035c1a53be453d1e857d8ee6094183d61ffbce2a08f989500005a067c072c09c494f4c43a5659344a68a2c9230a7556590188f7000053cdd3d5aba849000000000013afa259d39b0000535200007c5c8b20d1c5f9632a770000116e501d0000e37505b4c3c89091e8cbaadc622044cf00000000c06893b30000e9f9000059599bb900005bca2ad400001bcec4ef540c0000a99a550ce193b25729d7c97a5cad7b2300000000000000005a6583e5ad9c242600001b090000000072c10cf6000000009afe5c35bbd543497b4cb291b0cd000082be0d350000000000004cd33cbefd1b232b727a9862cbd42579b2644067e91e5507289b005f00007279cd0059c6d91000003aeb93c48da20000094634fdd44f21e638a0d16d31c1f3634d1d82f310cf7888b5997b10a2617cbd68dd9b7dd9e36d9131386b86602378567052f8390d3ac18f5c2a99d458da6b15d85bd4f602eee4399aefd0d19a474d1a4a195377f586c504a94f8ce724296493c1178283b1963b77ab0f9c20592dab84c282b21a3af94a2a50446d8e1a6e604b21578d76dbc9c5a5b5b753a2e816a204000020b7da45936f5be599a6d46222b8591fda2db300bc75e4b879c5e1caba4959db64aea55aa383dad8b81a4395ec52186cdbad1bc7e873aa84000000000202a4a1bb1bacf1000058acd3c5a32a1952119569609b51a186e800ec76eda7b98bcc4ec91400007bdd495a0be3e03f7da070253449b05b9c336b70d3e89bd784a65bdc00006303456b8cd6b227e467608b7832bb1832d4d98338cdb206553e1b40f551111c9c4500006ae88a7f5089036ec536cb44f0c3617cb5882ae56565e1234535b35b000060071130d46fa04db46b158431d00241e9ceca2c055f8b8814128d8614c758bdd273c42cea549546915e210f0000b2d2c18e0ab1747a28a5f3f2d9a4f5877b87e4f3520944e77378ac6aa431c02ec21fbb6e8355e1801c11b59c79fc129d7bdf288a815c1b1c412c001690dbc534c58d0238bae752c2e35e8af4b06cbafdcc7fe4fb7af33cb02
  | 3 => 0x831d0e52cc79b0af42d4db52d2761c9cd88240799f0ebcb7077a987fac90cc00000b34800000000ba14000035130000d03cb2cc0000095468076b4ee4608240727ed8ef696c83450000d880eda400002577223170553bf300000000d9d10000989edbb40ba5f0360000883e531dd20c5d757c9e90d94830ab49c9af00000000744e11a3ed3d0000e2cd3981fc007aa100000000d33cf2fc0000e4b1aa081104cd341cb6c58a24e2d4de816150b36db2000078680aaf74359a242855cb3ec3ce0000d59bd3ae8552db1913cb0000648812ef29aeb43e6b64ac2e6389b2e0ecf76087831670e2baa0bd74f9d68b6f1474c0549b72d2a24113000063b40adddc8e2287d04cb3b19c4a12ab390b0000b34e62ad422d18b735574998610a75b60000c554ca48c93ce369614201390000000000000000e41e0000000021e479a70000d8d643dfe17bc4b7aca800008cae820f0ac17d9e200f9469f3ede878f36ca16f29bb0000bce3000000000000c52b6c8f5d588a8644d3c25f00003116a17510f858e20445b4b60000cbae498f62c8e82ce42ab56818adf0ae2ad1cb08cacdf23075b50000214cf9ac0000426690a6191739f2fb68f1c0188900009a81c0f50000785cc006ea17a8a4b0da0000b228cb9000009072322c0000000059b6545f095c79b5519cfa01b4e8ca1c48540c04d545fa0f5869cc068b47e02220de8a41b4f0b2cf5dbb01a19a7b28ccd83f0000341c8af0833e00006a5c6be0eae00000243300008d6774cb000021a6a18124caace11b8d44af3c3bcc54c354d49d0000220dd49bdd7fb563812f4a3245ad73f992b60000a55cd0acb81111526bfb0000712ecd0168e91af7ad44fd998043aa57f298406a0000a371926ee51cb5946d2bb2938a80c834423e9d10052a0949bb1240a2a5a4ecf8cb936db935aa42584c19000052081172e1081d96b8e6f841c3148bb2f357a43c1d0853e299ad00000000fc3aa8727bc84a1b142b13b64828797759b2f29404241a025978a2990000148cb00a1d43102f5c61cb9981ce0000448d62d914844498b0a7000008449a420000626bf40340ce118c2cd000006ccebbc62c25f8db19f4bcd40000d1acad68599348caa2956d2cb1b80d129341e906000040d55444e4f43bbd4d05504ecb509c2fcac7135354ff0cec1b634b8eb5a3dc8400000000bb35c53c69ef9a99859fbcb3fd80381210840b9b294251b1015dd3a9142ef4f9fd9d4890506531abc96b7bc3000040473ca9421612a5c887d48982500840d3ddcc3f396241b60bbead6274bab3682a5e25486a3bc39df529f1f4fc14809852b1ed95c1d20000544a884a49f360cbbd6ed9230000e0f9804068fd59713ada4b97c4b01269a33900006bde1a5100783aa6b2e391fd0b0090f7546300000000cbb80904d48571f6f1d700000000519ab
  | 4 => 0xa35e55871ddd22289ec31bbabf1e2143cd2d84753c2b5bf25b00c790000287c0000caaa212acc5181551a5b2d30dc8ac85300005ae3608ac119986600008d1ea39a7523d356000041d4e11bd8e80000bbbf5da6914b00000000e5939da100d7ea503a0d1296000005402d493d460000309d62d86254a94100000000e02b000038103c83d486d8238b67f1f700002585f33259bc00000c9d8c1b0000a3655bb78b02905ad53f5da9c01ee4fcf0bcd16b700dc9b903382b1ecafadae60a4d129c70b18bc0b037ca4f0c03f128ad287ab059371af623237d5d0465ad4dbb8ae2afeacaccfc41be8187f56a32768a8989898385b06670850b898db100000bd800005dba7a377b83b541a3d218affa602cc95185523b62bac382bbe200008167b2970000a22aa4c651704d2edd94a2a999ff0b0d2cffc82a7c80b58348b47304eb7b9530000000009c87a350a45800005a2f000014d96826f9800a3e549e000000000032fd36f4786907446e3cb8831a5b13000092d152a44281e8fcd3a6d0bb6ccc24aa58ebc899ad85d340a4dc00000000000015280000e133881b63591918f2a7545623acf833c3fe82a86d9fbadb513ba0dd63f6b10e4d6c938d0000ea6ad850000073724a1651c4d326e475952d00000000fd2583dec496d804314a3160cc9914ee7499e1894dae8d827132144b35a95106a413a8582cfaab370343ca59a33b51cb2c4bf85162dd080c24ac20d2dd0ad2ede074849cc562d81ec555217dd9a5325bd4f745a11d0983467acfc012e48b2126e166ecc3e97ffadf45bbe088c95b01b2eb9c7c2663511cf5b4794373a36b635a58c862241d0dfb9ae2655d5472452991f051842f084520bac0b98146cc8878d0593efafb79fd93a70446db819ab624060337482d94046550bb2d6a257b5ae000738a280e58e402c0bb5e4a7abc9f714fb54d9495f8420938928e0a437b55a476f33112a30000cbb3d52cbd2d10e1db043b71338fc37b0156a8cf33d9aa1e4bfc6bf6644799cbdd8fe04a3d16c0e7fb5cace893218c2ce4dff2fd49113b274bc521efd98e0c32a4871500cb28b07ac9e7d47edc0de902a114f2883b1ae3e78a8d7393d017ac5af8850000f47300006306e02911f944971aeecbcdf158e3ef3b57b34f8a4ea1aa9c0b4177e408ac0c282b296f530cc3ab628ae1fb5beaa9e90c0a1d4f4b6c00b8b169851489ee912270b452caa198c0a378c43a7565b9632ff4010000328f019f70eb2d645278407f2d3742e9bd9afc6d29308cdab018a51bd01441828a2e709f2db6d50f6ca5615b20421a887cd55b596b39bba165895c37bd5c4483a0e9bbe678d9f84fc50ac2e6b52f3c3e1bd274223ade0000783865b132ff43bf71bce168ea87bb7c7a0c69f19bcfc9864c4139e12943286a7062ab2228a7099eb2358c941b7ab2b5e13401e37
  | 5 => 0xcef6ad912bd531f945c93194bc10000e3d6da669ac8c09a18c0fb9eca70b22e4d6d221d7933487b1d93c0af39734591b2c6a374238840a553b298ce431e9c89b12b19272af5bd291457f129e9bf4cd100ad893598ae19796026bb821898a94d583cbaf1d218fb3af9b3a1ae98279200dd72596eb099f210f173f9df654bd335e4e00000fc86db45fc5800000b4b4b76ca03211e5aada153e922c43b73361ca01c31000070be4d5754dba203619bb24313cfed50f42524f15b38d28b4ae9013e052e0000000095800b8c647dcbc2203871a2114562c552f8423412c7f91dcc27ea9f603e1ab7a25c21025ce9fc0f6913d0b63b65c330cb03503d0000441f088c00002cb15ceb5440000008610000c0e31d71a1c8da92c9c90000f22b19f8738ee247000052eb70d4e30e61defba3abd65abaf97d000000000000f525f23600000000a5710000ca44f5225bb50000884699b13049da6b0b1700001d21a3843aea54bc84fa395165330000415f00006118ec5b0000c0190000f18a00005021a9b470480000e09e0000a3914d4e0000ba825b147da80000000009316a64134b943dd4727b5f9277000072cb000000006c02310532331b9f0000f0a100008176653858bedd38000000006b58dcbfea7619fbd10324687a2691cc9bd373873ab50000d320a28502e7210c9a9709e20000b361a32e0000f37ab891409b3d22000093f839c8b2f679a3a256f8c59b0ce366000000000000447f6ca7c9a1a3beeb013147d24b94f5a8b5247700000000e80635a019cdb42021882cfdd333c1c2781c0000e0278c6741b328f3e03359a875bc421172eccd69e2b70953a97603240000626aa915a8f6798c0c08acfea8d120020ad00000b06e4ac2e88310ff5db3f34479dd821c8358482f000000007a6f50fedca300000000bc96e056c448e590133a0000000000f200000000cacb000039cf00d6c15a3ba00d66ebc40982000055b3dc1f519d0000000052bf8d7309905a40c9050000f29a0560d318ca3f3ad500006a22b1ee987a65b81b4fb59a0ac0606022c41d77d0111a0a234ddc78849a110bd2bbbb8b157d2ab995207a3dea96439f184ca3ada5640399834c52373a9b256f33dc892e014e5b4a1d61cc150000b93bb1c66c4934f2000069c3e21e2302041bdbdbf8360d596bf4bc739b8049250000dcc6793d0000613703bb41db3073e461288123faa437797cc22974bd98a86271830fbbd0d9eda4b5d262188ff4c999de58156d5100005bf20000db7f53347c4d30f470ca544d72d6f55b24c3f5244a3ad87d13f4dd78b892b3aa7cc59430a179106303f57ced432d5a8bd4fedc3683ee486e62d0f442d2aabca132da3004c867b1e72cb47b969329220a912778c67abed24a3be12b5db80264a31c7b6b0ed2f5a0c53a28ebeff0b59a8a6961cba463a00d033
  | 6 => 0x50d85249ea78000000009ae2000000001572d80a0000f05e43ffbcdd2a9d1d0e00006053e3b0028ce9080000d4d511e512bcd4ab0d891386d0900001d1c350bfa51f51e2924d0000cd1498fa00002031e9880c82a45e83c78b53e5af73ec037dc3ca33a8c89c0131dd830000ca33000068a110e4c443e5987cabd805000069d2fc590000b5bd24a50000d85e00000000000001f3226f33f313ebc24239aa28d2c1d608f4f8210000156cc0460000945100000000ca46b0b0fa1a0000c8e184188aab000054c50000150594a4bcfb00000000540579289b43fc9cc1a0bc13345b30f3000088fe68d700002178594e7cc1e8c7d441318ba1cd1061ba1178933a4c0000e13fba83433d7059d13c000030a9000000003cb755b28030c26db10188a6dd39a82014a93ca4eac40000c50624c8356d4b4decd9d53970c06bda295e73258205e9d3d1485a91ada3999925430070b8e7c4cd0000f8b1d9c228f1db41ba2778dc2a9e9d3b4dbde09c74e91253d1650000357acc7d8b308b48d3b5da6c340fcc1a551e9bb6e0c90000ad19e8d500009045658fe527e8abda930000482500000000a2f00000000091a90000bc74858c88b9193f0000c36a594bf3c1ea1300000000484e2225d4a282f90000c0d30a310000a207fc164bff00006b9dc36d4c62417e34e59a95b1d10000d54215127cee5ad73a1830107490f1a8e36008a2224e48773079f8dfb19795443c77b1cf403aa107984870edf12dc8b02c480000a028026cf0ea602d12ce1a1f0000f1dab076e4be388b630d0a1d1d5edd7cc8aae3e0d310fa63eb95b191599483152ae132fa4c984c100000440a0342f37f00008471ac8c0000a8d43d479bf82d6fa08dfbac418d088415765521b8a31c63dad3fd481b0bf575099f1bd10000207c3af8c482fbba789fcd79fb6d9c4f889da46a3cb9902cd1ea6b6a440bb11113fc81f20000280ff8132a551c3dc4d252b0ab3f82e8401542b2cb78faff8b66000048089accb553f1dc6a301894d0862b5bfbe7739ca159c43f6317f8bf9db8a90d000032e51864ab54caece0bd23fd000000009cbb983beb61756eb25df9daddb40aa532d35239cd32ba94d8b280fca1f0c1713b6b137c701fcd2afcbac9bddd0c00000000995f0000e163f29e81b90100f0c681fec5950000ea3990ccf87e423f69483ae4caa8e4ce6a53f4e1f865c4546909219493130d70b9dc530bba5a000019b70c91bd3e6d65aad20be92d4a627cea9a81d5fa74b1e1580b00003995a22fa9c400001d0b555d33f7d569bd310000009781afa4b31a044a6700003ccf09f5aa4b053700000000ac7a0000cd07101c000003fb3c010000bd98d98a42e2245068d38be87c1894239cc81c7e73b9fce0c82e3cdbec0514c1d9550000eb05711a9174e4daf97b9322ed4c5972000000000000a
  | 7 => 0xdd0f85ae70416526fa21337600003301c9e400008b467b160000aa3c58c9dc5e0b24000003922c38b3e4e8707bec8c290000c46c6064c3792b62a005b8e3388dca5f751abc72e12175a86bfd000032d500000ab3635c0000431223ba9d557410611230ef8cf91c70b4eba07d000000000000739e516cd8b800000b7e60b261f81b74c309da4a20ece9ebd43a9a0e21fa4ac651b54b21c54aacd798ed72ac25190000c0c280098b3b7d2000000000e0aa654fec0ee38100002ca64b560000da340000bac30000d3c30d8b186d0000000099a919210000000082db2b250000f9eabb85cbaaa4362d6b483500004bbbe4ad41a4845de3901b1d94d1ba71c98424b2000065acc4e3420edd639a6d23e6da0701430000baf2ca850
  | _ => 0

def or04data11 : Nat → Nat
  | 0 => 0x2ffd06dc3eff9a6f87fff1bdf0fdfe379a1fffd06f43dffa0de87eff40bd0fffe7b7a1fffccef43fff8dde87fff2fbd0fdfe4d7a1fffce2f43fff9c1e87bff41bc0f7fe71781effd06bc3fff9ad787eff2caf0fffe675e1fffc8abc3fffa0d187bff41a30fffe7f461effcfe8c3fff9ad187eff2ca30fffe7d461effcfa8c3fff9a5187fff23a30ffbe37461fffcf28c3fff9e1187fff2fa30fdfe4d461fffc7a8c3ffe8f5187fff38a30fffe47ba1f7fccf743fff916e87fff1bdd0fbfe5fba1fffc7b743fff8bee87fff11dd0fffe83761effd06ec3fff9add87eff2cbb0fffe7d761fffcd2ec3fff91dd87fff3dbb0ffbe7a761fffcceec3fbf915d87fff1bbb0fffe79761fffcf0ec3fff995d87fff39bb0fffe72761fffcbeec3f7f935d87fff1ebb0fefe3d761fffc5eec3fff88dd87fff0cbb0fffe5d761effd06e83dff9f5d07bbf3eba0f7fe79741efeceae83dff9cdd07eff26ba0fffe2f741fffc32e83dffa0d687fff3fad0f7fe7f5a1fbfcb2b43fdf91d687fff3dad0fffe455a1fefc6eb43fff9e5687fff14ad0fffe735a1fbfc9ab43fff8f5687fbf17ad0fffe235a1fffc32b43fff8ed687bff41a10f7fe7f421fbfcb2843dff9f5087fff23a10fffe35421fbfc9a843fff8f5087fff17a10ffbe23421fffc32843fff861087ffe1da10f7fe832e1fffcf65c3dff9ecb87fff1b970ffee772e1ffecea5c3fff9ccb87eff26970fffe3d2e1fffc785c3fff8bcb87fff11970fffe3b2e1fff8765c3fff8b4b87ffe16970f7fe832c1efecea583dff9ccb07eff26960fffe3d2c1fffc78583ffb91c787ff7228f0ffee371e1ffdc6a3c3ffb8a4787ff71e8f0ffee3c1e1ffdc5e3c3ffb88c787ff70c8f0ffee181e1ffdc763c3ffb8b4787ff70b8f0fff67f121ffecfc243ffd9ac487efb2c890fff67d121ffecd2243ffd91c487ffb3d890fff667121ffec8a243ffd8dc487ffb3c890f7f679121ffecf0243ffd994487ffb1a890fff629121ffcc3a243ffd9cc487ffb39090fff65f121fbec9a243ffd8f4487ffb1e090fff62f121ffec46243ffd864487ffb0c090fff65d121ffec76243ffd0ec487ffb16890fff617121ffcc1e243ff903c487fff41850f7fe830a1fffcfe143dff9fc287fff3f050fffe6b0a1fbfcb2143fff9f4287bff3e850fffe690a1fffc8e143fff9ec287bff3d850fffe670a1fffc8a143fff8dc287fff3c850f7fe790a1fffcf0143fff994287fff21850fffe350a1fffc52143ffb874287ffb0d850fffe5f0a1fbfc9a143fff8f4287fff11850fffa230a1fffc32143fff974287fff1d850fffe2d0a1fff85a143fff85c287ff707850fff6090a1ffe812143dffa0c2079ff41840f7fe7f081edfcfe103f7f964207bbf3e840f7be7b081effcf2103df79e4207fff21840ffee1d081efecea103ffd86c207
  | 1 => 0x5ffd9e990bffb233216bff022c2dffdfc585dffb58b0bdff591616ffef62c2effd9c585effaa8b0b7ff7916177feca2c2f7fd4c585ff78e8b0bdfb4d1617ff67a2c2ffec8c585cffb5cb0b9ff699617bfe8f2c2e7fd96585effa1cb0bdff3596173fec32c2f7fcfe585eff98cb0bdff1b9616bfee72c2f7fcf6585eff8ccb0bdff0b96167ff06ec2d7fe05d85cffb6bb0bdff597617bfeaeec2f7fd4dd85ff78ebb0bdff4f7617bfe9aec2fbfcf5d85cffb6ad0bdff595a17efe8eb42f7fd4d685ff78ead0bdff4f5a17bfa96b42f7f5b5685efeacad0bf7d475a17bfaaab42fff515685fbe9bad0bbfd655a17bfaa6b42fff50d685ffe94ad0bfed1d5a17bfa9eb42fff4fd685ffe92ad0bffd1b5a17ff246b42cffe0cb85affc0970b9ff6d2e17bfeb25c2f7fd4cb85ff78e970bdff4f2e17bfe9a5c2ff7c64b85df7b58f0bdef591e177ded23c2ffbd1c785bf7bc8f0bbef651e17fde863c2ffbcd4785df7b08f0bfef3f1e17fde623c2ffbc6c785ef7a68f0bfef3d1e17fde323c2ffbc2c785ff6968f0b5ff811217bfeb2242f7fd5c485effa9890bfef1d1217fee16242f7f52c485ff687890bdfd811217bfada242fff5f8485dfeb5890bffd6a1217bfab2242dff5f4485efeab890bffd471217bfaaa242fff514485ffe9b890bffd781217ffac8242f7f54c485ffea1890bffd351217ffa52242ffb474485ffa92890bdfd4d1217ffa7a242fff48c485ffc91890bffd191217fea16242e7fe07584dffbceb09bff75d6131ff03ac26bfde7584d7fbc6b09aff75d6133fed764263fdaec84cbface9099bf59ce133ff0394267fd67284df7bbe5099df81ca137beff9426f7dfb284ceface509bcf77ca137beeb94267fdae984c7fb5d30997f69a61337ecf4c267fd96984cefb2d3093ff838613bff030c257fe06184cffb6c309bff6b86135fed70c277fd66184dbfb4c309bbf6786137becb0c277fd4e1849ffc1c2099ff6d8412f7ef70826efd9e104bfdb9c2097fd7184137de878c26fbd0b184df7b59d09aef6b3a13bdeb27426dbda4e84dd7b39d09bef653a1379eca7427fbd0ce84cfface1099ff53c2137fe878426ffd0b084df78ee1099f781c2137eeff84267dd67084dfbbce1099f753c2137ee878426fdd0b084df38ee109bf66fc2133fed73c263fdae784cbfb4cf099bf679e133fecb3c2677d96784effa1cf099f7619e137ff06fc24ffe0df84affc0bf09bff6b7e135fed6fc277fd65f84dbfb4bf09bbf677e137fecafc26f7d95f84effa9bf09fef1d7e137eec2fc24ffe0cd84affc09b097ff7f36137fed66c26bfdacd84effac9b09b7f69361377ece6c26f7d94d84effa99b09fdf433613fde3a6c27f3c74d84dfbb09b09ff73f36133fcb36c267f94ed84dff21db09bfe42b6137dc3b6c267f93ed84dff1fdb09bfe1bb61
  | 2 => 0x17bfedb142e7fdb6285dffb4c50bdff578a167ff06dc2e7fdb5b85bffbfb70bbff6b6e17bfeb2dc2fdfd1db85cffb6e50bbff6aca17bfeb3942f7fd57285cffc0e50bbff7eca173feb3942edfdf3285dffa3e50b9ff55ca177fe8b942effcdf285affc0e40b9ff6dc816ffeff902effdaf205bf7bbe40b7ff75c816bff074c2f7fdae985cffb5d30bdff69a6173fed34c2f7fd1e985effb3d30b9ff67a617bfe8b4c2f7fcde985effb2d30b9ff65a6167ff070c2cffe0a185effb6c30b9ff6d86167ff06d42f7fdb5a85cffb6b50b7ff7f6a177fed6d42f7fd65a85fbfa3b50bbff676a17bfeaad42cffe0d4859ffc1290bdff6d52173fedaa42dffdfd485dffb5a90bdff595216ffefaa42effda5485fdfa2a90bfbf375217bfea6a42ffbdace85df7b59d0bdef593a17fded2742efbda4e85ff7a39d0bfef673a177dece742ffbd14e85ff79b9d0bfef653a177deca742ffbca4e85cffb6e10bbff6ac217bfeb3842f7fd5f085effaae10bbff64c217bfea7842ffbc77085cffc0e10bbff7ec2173feb3842e7fd5f085dffa3e10b9ff55c2177fe8b842effcdf085dffbc610b9ff53c2177fe6b842effca7085df78ee10b5ff839e17bfed73c2e7fdae785effb4cf0b9ff699e17bfe8f3c2f7fd9e785cffb3cf0bdff459e17bfe6f3c2f7fd96785cffb2cf0bdff439e17bfe6b3c2f7fca6785dffc1bf0b3ff837e17bff02fc2d7fe05f85effb6bf0bbff6b7e17bfeb2fc2effda5f85effabbf0bbff677e177fecafc2f7fd4df85ff78ebf0b3ff836216ffefec42effdad885effacb10bf7f4762177fecec42f7fd55885dffb2b10bdff536217fde3ac42cffe0d285bffbfa50bbff6b4a17bfeb2942dffdf5285dffb4a50bdff574a17f7e8a942effd95285effa9a50bfef1d4a17fee7e942cffe0cd859ffc11b0bdff813616bff026c2f7fdb4d85bffbf9b0bbff6b3617bfeb26c2dffdf4d85dffb49b0b7ff7b36177fece6c2f7fd54d85effa99b0bfef1d3617f9e3a6c2ffdcfcd85ffb989b0b9ff6b9a173fecf342f7fd16685cffb2cd0bdff439a17bfe53342f7bc76685cffb0cd0bdff3f9a17bfe37342d7fe05e85cffb6bd0bbff6b7a17bfeb2f42effd9de85dffb2bd0bdff537a17fde3af42effd85e85effa7bd0beff3f7a173feda8c2dffdfd185dffb5a30bdff5946177feca8c2f7fd4d185fdf94a30bfef1d46177fec28c2f7fd3d185fdf92a30bdfb4d4617ff67a8c2f7edb5185ffdb5a30bbfb6b4617bf6b28c2ffeda5185efdaba30bffb474617f766e8c2ffed95185efda9a30bffb434617ff66a8c2feeca5185ff58ea30bffb614617bf69e8c2ffecfd185ffd98a30bfbb254617ff6368c2d7fe04c85cffb6990b7ff7f32177fed6642f7fd64c85bffbd990bbff673217bfeaa642f7fd4cc85ff78e990bbff613217bfe9e642ff7c6cc8
  | 3 => 0x89dffb4bd13dff577a27dfe8ef44effd9de89dffb2bd13dff537a27fde3af44ffdc95e89ffeb8bd133ff8378273fedaf04dffde5e09dffb2bc13dff537827fde3af04dfddd5e09bfeb8bc139ff6d5e26ffefebc4effdad789effacaf13f7f695e276fed2bc4effd9d789effaaaf13bff655e27bfea6bc4ffbc75789ffb92af133ff8246273feda8c4dffdfd189dffb5a313dff594626ffefa8c4effda5189effaba313fbf67462777ece8c4fefcdd189dffb2a313dff534627f7e528c4ffbc75189fdb92a313ffb3d46267ff04644f7fdb4c89cffb69913bff6b3227bfeb2644dffdf4c89fbfbe19137ff7b32277fece644f7fd54c89fefb29913dff533227fbe6a644ffbc74c89ffb929913ffb5e3227ff67a644ffecbcc899ffc198139ff6d3026ffefe604effdacc09effac98137ff7b3026f7ef6604effd9cc09effaa98137f7753027fee4a604dff5c4c09efbc08b13df76d1627feefe2c4ffddac589ffbb50b13df7591627feefa2c4ffdda4589dfbb48b13df7571627fee8e2c4ffddec589bfbbd8b13ff7671627beeaa2c4ffdd14589ffb9b8b13ff7791627feeca2c4ffdd90589efba98b13ff7351627fee522c4ff9c74589efba68b13ff73d1627fe67a2c4ffdc8c589ffb8c8b13ff77116273fed72c4e7fda6589effa3cb139ff659627bfe6b2c4f7fcf6589eff8ccb13df70b96273fedaec4f7fd65d89effabbb13dff537627fde3aec4f7fd35d89f7f9ebb13ff70b7627bfa96ec4f7f605d89efeb6bb13dfd597627bfaaeec4fff51dd89fdebd3b13bfd677627dfa8aec4fff4ddd89ffebc3b13bfd657627ffac8ec4f7f54dd89ffe9abb13ffd297627fda3aec4ffd495d89ffeb93b13ffd5e7627bfa9aec4fff4f5d89f7e9ebb13ffd2f7627ffa46ec4fff465d89ffe8c3b13ff50b76273fedab44f7fd65689fbfa3ad13dff535a27fde3ab44f7fd35689fbf97ad13ff70b5a273feda5c4f7fd64b89effab9713dff532e27fde3a5c4f7fd34b89fef8c9713ff70b2e27bfa965c4efbdac789df7b48f13fef471e277deca3c4ffbcd4789ff79e8f13fef2f1e27fde323c4ff9c2c789ff69d8f13fed2d1e27fda2e3c4ffb5ac789ff6b50f13fed691e27fda8e3c4ffb59c789ff6a28f13fed371e27fdaca3c4ffb590789ff69a8f13fed291e27fca4a3c4ffb57c789ff6af0f13fed3d1e27fda783c4ffb4bc789ff6918f13fed191e27fda303c4ff942c789effbf6d0bdff78da173fedbac2e7fe07585ddfbd6b0bbff78d616bff03a82e7fdb7505bffbcea0b7ff75d416bff07642f7fdaec85cffb5d90bdff78b2173fedba42f7fd67485cfface90bdff6bae173fed75c2cffe0e3859ffc1470bdff6d8e173fedb1c2effdae385effacc70b9ff6dce17bfeb39c2f7fd5f385cfface70b9ff57ce177fe8f9c2f7fda6a85cffb4d50b3ff838a
  | 4 => 0x23ffde4a647f7bd34c8fff79e991ffeb3d323ffd65e647ffbc8cc8fff7b8991f7ef7f303fbdeb2607dfbdecc0fbd7bd981fdef55303ffde8a607dfbdd4c0fff79f981ffef25303efdee2607ffbdfc58fbf7bf8b1ffef7d163efdefa2c7ffbd1c58fff7bd8b1f7ef7b163ffde8a2c7ffbcdc58fff7bc8b1ffef35163ffde522c7ff9cc458fff79e8b1ffeb3d163ffde462c7ffbc6458fff7b88b1fdef59763ffde8eec7efbd95d8fff79abb1ffef3f763ffde62ec7f7bd35d8fff79ebb1feef3d763ffde5eec7ffbc65d8fff785bb1f7ef7f5a3fbdeb2b47fdbd1d68fdf7b2ad1ffef3f5a3fbde9ab47ffbcf568ffb797ad1ffef195a3ffde16b47ffb4ed68fef7ac971f7ef7d2e3ffde8e5c7efbd94b8fff79f971ffef312e3fbde9a5c7ffbcf4b8fff797971ffef192e3ff9e325c7ffbc2cb8fff69d971ffed2d2e3f3fedbac4e7fe07589ddfbd6b13bff78d6277fee5ac4e7fdb7509bffbeea1377f7dd426ffef3a84dffdcf5098ffc15913dff6bb2273fed7644e7fdb7489dffb56913dff59d226ff6e5a44effdfb489cfface913bfb72d227bfed75c4e7fdaeb899ffc1c7133ff828e273fedb1c4effdae389effacc713f7f698e276fed31c4e7fdb7389efface713dff57ce273feb39c4e7fd5f389dffa3e713bff78ce277fee59c4f7fda6a89cffb4d5133ff838a273fedb144effda6289effabc5133ff836e273fedadc4dffdfdb89dffb5b713dff596e27efe8edc4e7fdb7289dffb56513dff59ca27bfeaf944f7fd57289cffc0e5139ff55ca277fe6f944effdcb289cffb6e4137ff7fc8277fed7904dffdef209dffb3e4137ff73c827bfed74c4e7fdae989effb4d3139ff69a627bfe8f4c4f7fd9e989cffb3d313dff45a627bfe6f4c4f7fd96989effb6b5139ff6d6a277fed6d44f7fd65a89fbfa3b513bff676a27bfeaad44cffe0d4899ffc12913dff6d52273fedaa44effdad489effaca9137ff7d52277fed2a44f7fd5d489fdfa2a913fbf375227bfea6a44ffbdace89df7b59d13fef693a277ded2744ffbd1ce89ff7b39d13bef673a27fde8a744ffbcdce89ff7b29d13fef293a27beeda944ffddad289dfbb5a513df7594a27feed2944f7dd5d289ffba3a513fb7454a27feeca944ffdd91289efba9a513ff7354a27fce3a944e7fdb6f89dffb55f13dff59be27bfeaf7c4f7fd56f89dffb25f13dff53be27fde3b7c4ffdc96f89cffb6de137ff7fbc26dfeff784effdaef09bbfbede137ff7bbc26f7ef7784effd9ef09bffbcde137df79bc277fecb784ffdc96f09bff37de131ff829a27bfed7344e7fdae689effb4cd139ff699a27bfe8f344f7fd9e689cffb3cd13dff459a27bfe6f344f7fd96689cffb2cd13dff359a27bfe53344f7dc96689dffc1bd13bff827a267ff04f44e7fdb5e89dffb5bd13eff6b7a275fed6f44f7fd65e
  | 5 => 0x197ff7b1a32fdff4f465ff7e4a8cbf7fd35197ffd9ea32fbff83165fbff022cbd7fe04597effb68b2f7ff7f165fbfeb22cbdffdf4597dffb48b2f7ff7b165f7fece2cbf7fd54597ff7b18b2fff731165fbfe9a2cbffecf4597cffb4cb2fdff47965ebfef32cbf7fcfe597eff98cb2fdff3d965fbfe172cbd7fe05d97cffb6bb2fdff59765fbfeaeecbf7fd4dd97effa7bb2fdff4d765fdfe7aecbf7f52dd97efec0bb2fdfd6d765fbfab2ecbf7f55dd97ffea3bb2ffbd7a765f7faceecbfbf515d97ffe9bbb2fdfd53765ffdac6ecbf7f53dd97ffe9fbb2fffd31765fffa4aecbfff5c9d97ffeaf3b2fdfd4d765fffa7aecbfbf4f5d97ffe97bb2fffd23765fffa32ecbff7465d97ffe85bb2f9ff6d5a5fbfeb2b4bfdfd1d697effa7ad2fdff4d5a5fefe5eb4bff7c65697efea5ad2fdfd6d5a5effafeb4bfff5f9697ffeb52d2fdfd595a5fefa8eb4bf7f555697ffea2ad2ff7d375a5ffba52b4bffb58d697efea7ad2fffd3f5a5fffa4ab4bf7f535697ffe9ead2ff7d2f5a5fffa46b4bff7465697ffe85ad2f9ff81c25b7fee784b67fe06f96dffbfdf2dbff75be5b3fe9f7cb67fdae696cffb0cd2d9ff5f9a5b7ff06f4b4ffe0de96affc0bd2d9ff6d7a5b7dec6f4b6ffd85e96effa7bd2dbff5f7a5b7f6bef4b4ffe0de16affc0bc2d9ff6d785b7dec6f0b5ffdd5e16dffb0bc2dbff83165a7ff062cb57fe04596bffbf8b2dbff6b165bbfeb22cb6fdd84596dffaf8b2dffb3d165bbdeb31c7ffbdee38fff7bcc71ffef758e3ffdee71c7ffbdc638fbf7bfb71fdef596e3fede8edc7efbcdf28fef7acb51ff6f476a3fbdeaad47ffbd15a8fef7aca91f7ef7d523ffde8ea47febd1548ffd79ba91ffef72523ffdefafc7ffbd1df8fff7bdbf1ffef377e3ffdef2fc7ffbcd5f8fff794bf1ffef737e3ffdee2fc7ffbdfd88fbf7bfb11ff6f47623ffdef6c47ffbd1588fff7bcb11ffef29623ffdee6c47ffbdc588fbf7bfa51f7ef7d4a3ffde8e947febd1528fff79aa51ffe73f4a3fbde8f347f7bd1668fef79bcd1fdef359a3fbde53347f7be05e8fef7acbd1ffef7d7a3ffde8ef47fbbd1de8fff7bdbd1ffef377a3ffdef2f47ffbde1e8fdf7b2bd1ffef357a3ffde52f47ffbdd5e8fff79fbd1feef3f7a3ffde62f47ffbc95e8fef7a6bd1ffef717a3efdef2f07efbd95e0fbf7babc1f7ef71783efdefebc7f7bd6578fef7aaaf1ffef455e3f7decabc7ffbca578fff79faf1ff6f315e3ffde4abc7dfbdfd18fef7aca31f7ef7d463ffde8e8c7febcdd18fdf7b2a31ffef35463ff5e528c7ffbcfd18fff798a31ffaf25463fbde9a8c7ffbcf518fff59ea31ffef7f323ffdefc647f7bd64c8fff7be991f7ef7d323fedef8647ffbd1cc8fff7bd991f7ef7b323fbdeaa647ffbd14c8fff79b991ffcf35323ffde52647ffbdd4c8fff79f991ffef313
  | 6 => 0x46b6efefa8d6fdfd1d1adf9f9ba35bdff5346b7f7e528d6f7fd3d1adfdf92a35bffb3d46b67ff04656d7fe04cadeffac995b7ff7b32b7bfeaa656f7fd3ccadffd9e995bf7b2f32b77ff062d6d7fe045adbffbf8b5bbff6b16b7bfeb22d6fdfd1c5adbffbd8b5bdff5516b7efe6e2d6f7fd4c5adffd9e8b5b9ff6b96b7afe8f2d6f7fcfe5adeff9ecb5bd7f2f96b7bfe332d6f7fc2e5adaffc0bb5b9ff6d76b7bfeb2ed6fdfd1ddadeffa9bb5bdff4f76b7bfe9aed6fbfcf5dadfbf97bb5bdff78b287bfee5650e7fd674a1cffb5d7433ff838e86bff031d0edfda63a1cffb5d3439ff69a687bfe8f4d0e7fdb5aa1cffb5cf439ff699e87bfe8f3d0f7fcd67a1dffc1bf43dff817e86bff02fd0effda5fa1effabbf43dff537e86bff02c50dffdfd8a1dffb5b143dff596287afeaec50fdfd1d8a1effa9b1439ff6b9a873fed3350f7fd1e6a1effbc4d43dff359a87bfe7f350f7fcc66a1dffc1bd435ff817a877fed2f50f7fd5dea1f7fa3bd43dff537a87bfe9ef50fbfcfdea1affc0af439ff6d5e86ffefebd0effdad7a1effacaf43dff535e87bfe9ebd0fdfcc57a1edfaca343bbf694687b7eae8d0fefd1d1a1edfa9a343fbf354687b7e9e8d0fefcfd1a1fdf98a343dbf4d4687f7e7a8d0feecf51a1affc099439ff6d32877fed6650f7fd64ca1bffbe9943f7f7c3287bfea6650f7fd3cca1ffd9e9943ffb2f3287f7e46650cffe0cc21affc098439ff6d3086ffefe610effdacc21effac98437bf7b3086fdeee610dffdd4c21effa79843bff831686bff022d0dffdfc5a1dffb58b43dff591686ffefa2d0effda45a1effab8b43dff531687fee622d0ffecf45a1fdf918b43dfd817687bfaaeed0f7f54dda1ffe9abb43dfd4f7687ffa62ed0f7f535da1f7e9ebb43ffd2f7687f7a46ed0fff465da1ffe8c3b43ffd0b76873fedb9cbeffdcb397effb4d52f9ff69aa5e7ff06dcbe7fdb5b97df7b3e32ffef37c65f3fedb84bf7fd57097df7b1e12f5ff839e5fbfecf3cbe7fd9e797eff9bcf2fdff6d4a5effefa94beffda5297effaba52ffef634a5f3fedb7cbf7fd56f97df7b1df2fdff4fbe5ebff0378be7fdb6f17bffbfde2fbff6bbc5effef778bdefdeef17dffb3de2f7ef77bc5f7dec778bdffdd6f17dffb0de2f5ff839a5e3ff0534bf7fdfa697effb5cd2fdff699a5f3fed334bf7fd9e697cffb3cd2fdff379a5fbdec734bf7fd86697eff98cd2fdff259a5fbfebf34beffe0de97dffc13d2f3ff827a5fbff02f4bd7fe05e97effb6bd2f9ff6d7a5f7fecef4bffbd8de97effa7bd2fdff4d7a5e7ff06f0bd7fe05e17cffb6bc2f7ff75785fbfe9ef0bdff5c5e17cffb6af2fdff595e5f7fecebcbf7fd55797ff7b1af2fdff4f5e5fefe62bcbcffe09197cffb6a32f7ff7f465fbfeb28cbdffdf5197dffb4a32ffbf67465f77ece8cbfefcdd
  | 7 => 0xdebbeffa6bd77eff827aef9ff02f5df3fdb5ebbf7fbebd77eff697aef9feaef5dfbfdedebbf7fb3bd77ebf667aefdfe6ef5dfbfde5ebbf7fbc3d77eff657aefdfec8f5df3fd4debbf7fbabd77eff617aef9fe9ef5dfbfcc5ebbf7f92bd77cff4d7aefdfee2f5dd7fe057bbcffb6af777ff7f5eefbfeb2bddfefd997bbf7fa2af77dff535eefbfe9ebddfdfcc57bb9ffc123779ff6d46eedfefe8ddf7fd5d1bbeffa9a377dff4f46efbfe9a8ddfbfcf51bbf7d9ea3773ff8232efbfeda65de7fdb4cbbfdfb31977dff4f32efbfe9a65dffecf4cbbf7d9e9977ffb2f32ef7ff062ddf7fe045bbaffc08b77dff6d16eeffefe2ddf7fd645bbbffbe8b77dff5716eff7ecc2ddfbfd145bbeffa98b77ff73116efbfe9a2ddfbfcf45bbffd9e8b77efb3d16eebfeff2ddf7fd1e5bbeff9fcb77dff3196efbfe7b2ddf3fcf65bbeff8ccb77dff0b96ef6fef3a5d6dfde34badbfbae975b7f73d2eb6fee5a5d67fe072bacffabe575bef77caeb3fed34dd65fda69bacffb2d3759ff57c2eb3fea785d67fda67bacbfb4cf759ff659eea7ff06c5d57fe058badbfb4b175d7f5762eb7fecac5d77fd4d8bacffc0df759ff57beeb7fef37dd67fd4efbadffbadf759ff4fbeeb7fe637dd67fda66bacbfb4cd759ff659aeb3fec335d77fcc66bacffafcd753ff835eeabff02bdd67fdb57badbfb4af75bff655eebbfea6bdd6fbd8d7badffb0af75dff4f5eebefe62bdd4ffe0ccbaaffc099759ff6d32ebefef865d6dfda4cbadefb29975bef6332eb7fec265d77fd3ccbadffaf9975bfb5f32ebff65e65d4ffe0cc3acffb698757bf7b30eb7dec661d6ffd84c3adffc18b753ff8316eabff022dd5ffdf45badffb48b75b7f6916ebbfeae2dd6ffd945baeffa98b75bf76116ebfee622dd6ffd7c5badfdaf8b75bbf7ad6b6bff03a96dffde752dbffbaea5bdff6bb2b73fed7656f5fd663adefface75b9ff6d8ab6efefedd6edfdadbadebfacb75bbff6acab7bfeb3956f7fd572adcffb5d35bd7f47a6b7bfe8b4d6f5fcde9ad9ffc1295bf3f3752b77fed5856f7fd670adeffaae15bdff6b9eb73fed73d6f5fd1e7adeffb3cf5bdff459eb7afe6f3d6f7fd967adeff94cf5bbff837eb7bff02fd6d7fe05faddffb5bf5bdff597eb7efe8efd6fdfcddfadeffa9bf5b7ff7f4ab77fed6956f7fd652adfbfa3a55bfbf454ab7bfea6956ffdcfd2adeffacdf5bdff55beb7bfe9f7d6f7fdfa6adcffb5cd5bd7f479ab7bfe8b356f5fcde6adeff94cd5bdff3f9ab7bfe4b356effe0deaddffc13d5b3ff827ab6bff02f56effdadeadd7fb5bd5bdff597ab7efefaf56fdfd1deadf3fa3bd5bf7f377ab7bfea6f56f7fd3deadf7f9fbd5b77f7f5eb7afeb2bd6f5fd557adfbfa2af5bd7f535eb7efe52bd6f5fd3d7adfbf9faf5bf7f255eb67ff048d6dffdfd1addffb5a35bdff59
  | 8 => 0xbca2fbfeb3945fdfdf328bdffb4e517bff67ca2fbfeab945f7ddb588bffbb5b117df759622feee8ec45ffdd9d88befbaab117ff745622ffeecac45e7fdae68bcffb3cd17dff459a2f3fedaf45effdade8beffacbd17bff677a2fbfeaaf45f7ed35e8befdc0bd17dfb6d7a2fff6d6f45f7ed65e8bffdbebd17ffb697a2fbf6aef45ffed1de8bf7da3bd17ffb7b7a2fff6cef45efed9de8befdaabd17ffb377a2fff6f2f45ffede1e8bffdb2bd17ff3317a2fff6e2f45ffedc1e8bcffb6a3177ff7f462f7fed68c5f7fd6518bffd9ea3179ff6dba2f7fed7745f7fd66e8bdffb4dd17dff57ba2f7fecf745f7fd56e8bdffb2dd17ff731ba2fff67b745f7fdee3cbeffbcc797dff758f2fbfee71e5f7fdc63cbaffbfb797d7f476f2fbfefafe5f7fd1dfcbeffbdbf97dff377f2fbfef2fe5f7fdcdfcbeffb8bf97dff7f632ebfefec65f5fd1d8cbeffbdb197dff45632fbfef2c65f7fdcd8cbeffb8b1975ff7f4b2ebfefa965f7fd1d2cbedfa2a597df73f4b2f3ff06f65f7fdf5ecbeffa3bd97cff477b2fbfef6f65f7fcddecbeffbcbd97dff787b2fbfeeaf65f7fcfdecbe7f9fbd97dff317b2fbfe4af65f7fdc5ecbaffbcbc975ff75792ebfee2f25d7fdfd7cbeffa2af97dff3f5f2fafe62be5f7fc957cbaffbfa3975ff7d472fbfe8e8e5f6fcdd1cbeff9fa397dff31472fb7e4a8e5f7fcf51cbefd9ea397dff7f172ebfefe2e5f7fdf45cbaffbe8b97dff47172fbfef62e5d7fdec5cbeffa28b97dff37172fbfef22e5f7dcc45cbeff9e8b97dfb3d172fbfe462e5f7fdc45cbedfbd6d779ff6dd2eebff075ddd7fe063bbcffb6c777cff598eef3fedb9ddf7fd5f3bbedfb6e6779bf6dccef77ed399df6fd5f33be7fb6c577eff698aef9feaf15de7fdb5bbbcffb6e577dff57caef77ecd95dfbfd172bbaffc0e4779ff6dc8ef77ecd91ddfbddf23bbffbae4777ff73c8eebff074ddf7fda69bbeffa3d377dff67a6efb7ecd4ddf3fd169bbeff9bd377dff65a6ef3fedb85df7fd5f0bbddfb36177eff45c2ef7fec985df7fd4f0bbaffc1cf77dff699eefbfe8f3ddf7fd9e7bbedfb34f77cff459eefbfe6f3ddf7fd967bbeffb24f775ff817eef9feb2fddf7fd5dfbbeffa9bf775ff8162eeffefec5df5fd5d8bbfbfa3b177fbf6662efdfe8ac5df7fd4d8bbeffaba577ebf454aefbfea695de7fdb6fbbeffabdf77bbf66beefdfe8b7ddeffd92fbbeffa9df77dff4fbeeebff0379de7fdb6f3bddfb35e777ff79bcef7fecb79df7fd4ef3bbffbade77bff61bcefbfe9f79dd7fe0e6bbeffc14d77dff699aefbfe8f35df7fd9e6bbedfb34d77cff459aefbfe6f35df7fde26bbeffb2cd77dff649aefbfec335df7fcfe6bbeff98cd77dff259aefbfebf35df7f5c26bbaffc0bd779ff6d7aef9feb2f5df7fd5debbf7fa3bd77dff537aefbfe9ef5dfbfcf
  | 9 => 0x208a3218a6298a4314a5390851910429869414a529884194a321504208851148218c85318a6294c4294c421148390851948238c65190a5390c420d43214e2188c93a0841908241904320633108418c443204210c64398e3288c428ca318c4618c6331c6430ce3188e62a08739c89198c53950a318c531ca6288c4294c438ca5294a3414c528ca341ca331d07418a5294e739ce721c4a309044208919109310892210920c8540ce7294a742083218643088319865298c429043288c4304a41984311c630908521085210a43888311c8210c8618ca72106219063310c730c6511c8608862184a41884329c8510883110632184620c83210a4214c418ca63108531866294a6290c421887418c829ca73a087220a62a0c931109294c7198c31146810cc13904138c421a04408846410e3108631886431ce32a0c6318a6194c6effb5d74bdff57ca97bfeaf7d2f7fd5eea5affbeea9b5ff79d536bfee3aa6d7fdff24daffbde49b5ff71c937bfefe966f7fdf52cdaffbea59bdff794b37bfee2966d7fdfee4daffbedc9b5ff79b937beee9b5ee7fdb73bddffb4e77bdff69aaf6fff06ddee7fdb5bbdcffb6e17bbff67c2f7bfeab85ed7fe0e7bdeffb3cf7bdff379ef6fff0695edffe092bdbffbea57bdff574af7f7ece95ed7fdfe6bdcffb6dd7bbff69baf7bfeaf75efefdeaebddffb3dd7bbff65baf77fec375ef7fd3eebdaffc0dc7b9ff6db8f7bfeb371edffdf6e3dbbfbedc7bbff69b8f6ffef371eeffd96e3dbf7bbdc7b7ff75b8f77fec371ee7fe06ebccffa7dd79dff70b2bf3fedb157f7fd167afebfacb15fd7f5562bebff02957f7fd652afedfaaa55ffbf454abf7fef1ad1f7fe0aca3effbc59479ff59d28fbfed75d1e7fdaeba39ffc1c7473ff828e8fb7eb2dd1fcfd1dba3affc0e4477ff7fc88f7fed7911f7fd67223bf7bbe4477ff75c88fbfeaf851effd930a3effb5cf479ff6b9e8fbfed33d1e7fda67a3effa3cf47dbf379e8fbfecb3d1effdad8a3effacb147bbf6b4a8fb7eb2951defdf52a3edfaba547fbf474a8ff7ec8951e7fdae6a3edf92cd475ff817a8fbfe9ef51fefc95ea3efda6bd47dfb817a8fff6faf51f7ed5dea3f7da3bd47fbb377a8fff6f2f51ffede1ea3ffdb23d47ffb757a8fbf69ef51ffecc5ea3fdd92bd47ffb717a8fbfeaf751f7fd3eea3cffb6eb179ff81d62f7fef7ac5effdc758bdffb86b17dff6bb22f3fedba45effdaf48befface9179ff59d22fbfed75c5dffe0e38bcffb6c717dff598e2f3fedb9c5effdaf38befface717bff69ce2fbfeaf9c5e7fd6738bcffabe717bff47ce2f7fef19c5f7fdaea8bcffb5d517dff69aa2f3fed3545f7fd1ea8bbffc1c5173ff838a2f3fedb145effda628beffabc5177ff836e2e7ff06dc5e7fdb5b8bbffbfb717bff6b6e2fbfeb2dc5fdfd1db8bcffb6e517bff6
  | 10 => 0x64188e41204341904110674148238ce519d2620ca7218a3414632148721ce429089510c219045298461888438c8628c8431c84394a32a482208822908210c43418631944218d48194421a4e6321032186521042310c34a48c310e641cc5294a53092351467294871186221c86494c323108290a64110521ca420cc430d462912441484310a361884224a4214a42104721887220832108740c842148710ca3518a41906430c8349c84314a620ca6194a4190641946b1996311c65414c411cc449ca420c63314c9218c448c64514a53946229483224a41986339485290a530cc8219053a0a6290a52986a118c63a4e4310c4210a42108739083290a419866294a3128c51a084198a22988420d091148430c42418a6294832114719102290482904229486190c41084341ca4294c32a8e639064390a42110619c8710d2529482190442110719463114662908429044218a42108441062314c418c88414a451cc5520a518ce3210a621484328e51186519ca521483294c5318a3390c440d0321ca6414c7290c618864210c42908520ce6214c421083194c71204720863188c319ca9310e33146a20ca529104310a719067190c5218a21892271483314641a4a81a464214c42906448cc421087310a530c84210a518c481906519484190a3294a4294a83148429464315461948518cab18c421b4881888911c8421063298a3124c7214a6408691908410844189093944931d03208c618c63209462106710ce1088212908729083214252882308c2318443314641902331482210c6318c63046510c4438c6218c84288a638d0520ce319487298843108428c842086511ce219c8418c8318ca619c65198c33108621482309031148418c8510c6310c2618c851146421c853108430c6521c84298a420ca42990741086298843112720cc45948739d0528cc618d272908449d27214e32946718c642a0c42108420c891a4a3390a2120c4198c72912428cc418ca2304c511864110e531cc621ca4310a818c4318845310a5290c4198a53188921c8348ca3510a819108290e420c6420c441a8e43108a2a466210a6298a42214329466214a33106338cc4498c3210e72146528844418a518d05218a5298651a0653946438ca31908340c6540cc3188e82188430ce32106420c8731ca3290a31986618864190e430c4419d241104420ce41906420888490c418ca5298a719ce739cc331ce729c8451c671092640c8520d0340922610e7511052a042420a331c69310a9214a450c6430dc729cc52148320ce460d26128851a1281a0c3410c4198a738d4421085190a249826204e2108e348c4210c4230d2731cc61a4c531c8c1aca251084690a41a8491908420c84118a6194a421467290c52948629089309232906519884210c322505494a6594a838c852106320cc4290a3
  | 11 => 0x203001c0441e41dc04402c0a3254042030045a68047254e6c04003c01c03ce58170e6c040024170e5809ce6c04006805802400d03001e03103000c01c17203000c01c16804ca6801e03016813806801ce5a0301dc16813801ce5a030211e6e0301dc168138068e5a03225406804c01e031e7401800de5e0301dd18404c01e0301dc13806801ce5a0322541dca6804e031e5c00e03001c16806804001ce5a030040e5a030068040e5a03001c1e406801ce58044171e741200301e41e406804c03004001c1702601200580681e401de740301d804c01c0441701e404c0301e404001c171a681e416804c04403c01f25406801c1e40441732540680301e404017001c04401ce5b255e741dc16804403c01ce5b25404001c1d81cc1e40441701e41d81cc0a404417001f255e6c03203001f25406804c1e404003017001c047255e6c1dc1680a404406803ce5b25401c122e59e6c03006804c02401c0441e5e5c04003012017325417006804c0300401e401c06805801c17002403017006804c03c04403002401f255e5c044018031e74170044173255e5c1dc06802401c03c170e5b2541dc0a404c044025a6817003f255e5c04403016801c03004404003c01c16806803001ce58044032033a68045e741e7254e58068046260e5804003001c04406403c01c018e58031a68e5803004404009c06804f25401ce5903004406804403002c0240a801f26103000c09c17325409c06805800c02d03004417004c04402401c09f2541840981700401840b4044170068024e5801c09f2540941732545f8138a1c138e5c0400441700b40a404c04402409f25503000c0910301732572541840d81380d52541dc0b40a801d0301de0b60a804401c0a409325417000c01c0421dc05801c00c18d030024041030024e58027260e58e5c04000c044041030e58168044e5c044173254e5c04103001c0441dc06801c00ce590301dc06803002401ce58044031030e58046e5c17325404003c01ce5803c1680d4e5f03003002ce5ce5801c16804303016801ce58e5c04006805802c00d03001f03016801ce58e5c04303016801ce58e5c040030e5ce5816801f03016801ce58e5c04001c012032e5ee5804103001d03016801ce58e5c042e5ee580a403016801ea29a6468f6a13a7b09c5268b97e6546925e3ee8d562c28872181832e0357e6df1179d1deb7509c9e7009b6d6b4da3566a990c61fd7e75e0570259c95e955c14d3505d3824bc125b46ed11041d4fe13d3cecd3858d6632e0c012dd8ac728b498923b885d1f047231a9c5f215404880f7835e0b88268077c121024800019062215053204238c461948720c6a390451906429068494832148431c844108439084408a5394a520c6219c66298e521863214641ac682a085310a53988942085394653988318d2530c424a
  | 12 => 0x6804c03002801c02d04006804d03843802c43416904003001c00c02c06804d03802843843416904006804d0380284384341690410380300a401c0a406804d03802843843416904003001c01103a01000403006804d03802843843416904006804d0340300084381690400a401c00006803005802803e03001c0a40a443402c02806804d03402c02843443816904002c17401c83006804d03402843443816904006804d03402843443816904006804d0344340304381690400a403001c00c0208320300a403001c02104365802365c83104006804d03402843443816904001000403000616a04c01c43665c0408a001216a6580d665c04004c83043665e04083001043443801c8a083265a65c0400100066580280d665c04006804e03802843843416a04006804e03402843443816a04009c07325401c0b408c01c18407001e08d1dc18407018c01e03001c01108c06804f25401c06805801002d0300240272601f809401d08ca1c18603001c01108c05801c01018d030025a6402726016803c01c00d03006804d03016801c04403ce5c01ce7416818409c04d03004001e18409c01d08c16809c05802d03218409401d08e184584e5802508c09c06804325401d03002406802c02403c01f2601f809c01c0a81680681fd1dc01d03002417002409c01f25418409801c1681840b40a91dc18c1701680b7254e5c0241690a103002508e1dc18016801c18d030025030026a641ff262a6402403e03001f25404003008c01d1f803e03001e08c03e03001f25404003008c01c03c01f25603118403e03001e08c03e03001f254e5805804404007006b2540a801c1e402c058042a641de1680681fd03002ce580441e409805b256a6402da68e58044a1e04303002c0d7260e581f81e4094043260e58138a1ce580400441dc0d50300172541e40910300581dce5903004404103000f2541e40700580401dc07006801ea64025032a6404103002c168040027262a651845841380a9a6aa6725405804404103004003c01ce581dc06806b030e5801c1dc040030e581dc01c069030e5801c1dc040068030024e5801c1dc04006805802400d03001c01c00e03000c06a03009c04f25416801ce5804417004402c0a801c07325418402d0300681e41de16801c04325404413806801ce5b2540440401380a806804418c184025030068184168069030173254e5c138068184068e58046a6809c07006b25401c17006802ce5801c0732541241fd03005817009ce5801f25613804e13804c12402503005a13804d03213804c170027254e59a6a13804c01c00d0301fc1e4e5b25409c07006804f25401c9400441700a409ce5806b25413a08e03001d25503001f2540a404401da6804725526002503001e03103325401c17007203000c01d18608e03001c13a08e03001ce5804
  | 13 => 0x401c05483001c00400002000401800002001800401c00400001802400400001801800006443403000404c03604001806a04c01c00043483010004e0344340300060400180b403401800006402000400005483010004e0344340300b60400180340180008d801800006404c43400400c83004001800c00004000c00001804001800c00001800002402401800006400002400c0180001000b406404001805402801c01000406400083005400c83000c83000c83200c0008300240180000300180400541dd0a006401800c83005406503803000c02805406503803001801000c05603000c83003402c026a6004483000006404d03802c00c83007417004443804c01000d03883004083043806503800c03483004203083004203083203000c83083000006404c43801000c830042030830042030830042030830439a5483003403018002865ba5406503843801018083002603002404404203000c026044658056a60437a5503802565c041038438030018027a5408443402c04001002c02c01000c00604c43402e65c04004d83002c43665e04183001043443801c06804e03843802c43416a04003008443402c00c00504c43402d65c04000616a04c01c43665c04000616a04c01c43665c04004c43800c02004d83002c00c43400403265c01c04002001c01265a16823e65c04004c03583204265c0a583001043443801c00616a04c01c43665c04183265802265c04006804e03443443816a0400a68300280228a003002c01165965c0428a001283165965c0428a001283165965c0428a001283165965c04004c03000c43802001165916823d65c04004c03402c03104165c0a503002c00800402002c01c06800083005804c43565d04103002d04004e83002c43565d04103001c00402c04e83043565d04004e83043565d04004c03683104165c0a503001c0100200100a004003043843401c43443903303001043843401e83001043443801f03001043843401f03001043843401c04c43665e04203043603043803002002d65a8a283165c0428a283165965c04019413c02c00483001e8a283165965c0428a283165965c04004002001e83165802165c04203000402004c02c00443400c83265c12008402001043a65a1688320308300100a403c83001001c02265816843804012001000401e65820265c04006804e03802843843416a04000616a04c01c43665c04006804e03402843443816a0418a001012265a65c04004c03c43665e04083001043443801d8a012265a65c04003c16801e65a65c03000401165d65804002801000401d65802965c04001000401d65802965c04001000401d65802965c04003001000565d65816801c01000401d65802965c04003c00603001c01000401d65820165c0400280100a406804d03803043802c434169040058
  | 14 => 0x84360404340300900f48a800c83009083000c020040038090021a550b50a80900208308a008c0308a008c03803006806604c03002c01c0100a80240c006806404e03801c0340240740360300000240c006604d04c0300204380b40240740360300000240760300000a80240c40b40a80004388300c006806604d04e03801c01000c83002403001000c00002407402400000c8300c005804c01c00400c11483204d04c01c0100081150310a904002404002c02400004e0410404340240c10b40440240400100000240408300000c004402402801000002402400c0000380300101145000260a843404002504043410004c02404043402408004e0404350b40266580800250a204003800000265804e04043400c02665808002604000000c0240400380341145000250404360a802404c03803411404005402410204104004c024a3411c11002665843411002403a65843404e04104002408003401c00e65803804e04104003843412811411043843465c04e04104002411003803401c08002665804e04104043604104003843412a11204003843403a659a5404e04002400c11003401da6008003802665804e041040434502041040434038144026112041a6043604104043406805804c0200104381108300240c604d04c03800903265c0248b60a004404002665c4390a804402665c0400000380248b60a043404002665d04203843843402665c03800103443800002265e65c02043a65c43800c04402665c04003800002402400c0008a10400260a065d04003804c02405802801c01000404c83011400c0000440240310a804402400c83043400c04002504043403000c02400c8308b404400c0400240310b404402400c83200c00083011483000d04203083000d04203083000c02443400404c03204006404c4340040320400180420300000b40180b404c43403204006404003a03000001804003a03000001804c43403000604006403000001801004003000c00001804003000c00001804c02400401000006402401001800003802400006402400c00001806804103802c02400404c43403004604c01c00404c43400083006665803401c06401800903043400002e65a65803400103a6580f403400001a6580f40026580f40340000180340240185000180000b403401800503006805665c0fc0180b40360408a00684380000640b443801888e65c0000180b406401804005403803400e65c05404c03400da540180fe65c03465fa544390a800da540fe65c0360b4040438034054437a544380b40444381100f40b58a006804c01803400c43a0b44388b60b44380348b40f40b58a1a5443804c029a540340180fe65e0b40420b40400360b48b405465c658438437a5404c03a0340240080300200b404402001000406400083005406403001800c0080
  | 15 => 0x8300440010400000d48a04385008301c000c83011002001c0100648300556588a000001a03843803402c0200a80680640240a011c0308a00000180a204d04c01800c00a0340904380f40b60a08a203043808001a0384380680640340200800a00240320a08a20300f40f60a08a203043965c01800006604d04c43803000c0b402203a03402c02404c0300200b40440f008043843403000c0080f4a340000190b604d04c02406400000903004c0400300084380448d80000180c604d04c0080181140d90320a00400004380da0420384390310aa0d90308300fc0da0a08a00da0410420384350320d90a88a90308320380300240200b44340440fc43800c6340300000d41400d40180c50b406402401c0080540001410320a00400004360410400d44341401000d44360a00400004360410420344340d42220a08a021e0a08a04380a00408300200d56580000b603843802c0180a8020092a540b40a803802c02083000104c01800aa540904380f40b48a04380000b6038438018090022a540f404c0f443965c00104c4380300b40388a00200380d40200c604d04d03801c01000c83006483002800c01800c01800c01800c01c83000c01800e00c00103883001c06402805483002800c06806604d04d03843402c00c8300c204d04c01000c83103822904043a0308300b406806503801c00c8310340ea0410404360308300e604104043603083001c83000c06806604d04c43802001000c8300da04104043a0308320410404348300d40b604c438021a5483002801c01000406483005565888c00001806a0380340240a806402801c08c02c11c03088c00001a04d04c03802603402801c01808c0fc0300b608c88e0300f408001806802408006402801c08e03803403208c88e0300f608c88e0300f565c88c00001a04d04c03a0340240180b402801c08c0200fc03208c88e0300f50da08c88e03083208c88c8300d40110a802806804203403002c02400417004c04409c02806806405804c02800402c0008300100000180310a804402c09c83000c02e04043803009c0f401000c83204009c4350b403009c0440f401000c8300f5a5404c04000817043804608c0420300004390aa04043803009a0380f412c8301d208c43a03083204043403009a0380f48a800c8320400300984380f48a00301104380f404043806804002400417043404608c0420300004360400300944341240f40a803000c43608c0420300004360404340320340940f48b40a800c8305fa08e0308310b60404340320340940f40a88a000c8300f40a804c04004c0320a843404e0380300240081700200b40444384340000300f409009002006806405804c01c01002000083000c00001a08e0308300000450a804409002c02c00c83208c04203000043a040090438e740420300010a
  | 16 => 0x2c04c03401400d03004203002c03402f2606580440c01e4434044658057260437a540420310300080450300c203402c1e402004400c00903006404c02003400d030042031030040434021a5503002865ba5443404103043404203000d03006404c03400c02401503004603002c01004003402401b263a54042031030040435a6804203103000903004404203443403002801ba5408c05c03402800401c05503001811006800d03043a0408a006400d03004103011006800d03003c43800c01a04043801806403000800405401c01801c00400d03000c00503002000c01800402001c04001c00c00503165c03c0a401a04001803004001805406404043403400404e03001965c11006404c43400604203001a04003403c01806404c436a560300188da04003c01803c02401803c00c01965c06403c00c01843400c03001a0408a006465a0300181dc8a006401a0300541dc0640560300186588a0064040056030019e7603003c1dc8a0064040056030018a6aa548a004c03c01a0301dc8a00640404360300181248a006403c43401a0301dc1248a003c43401a0301dc064040056030019e6e03003ea541dc04c03c01a0301dc12406403c65801a03012465aa680541c44340301dc8a006401800e030055e5c04001a03003c8a006404c03c00c01a031e5de7603001800c019e5e0306581dc5008a006403c00c43401a0301dc04c03c00ca6801a031e5e03001804000e659e5c16801803001800001800104c03002c01c012658064040025a6010104006405402c0e40d40a809402c0256580440d409002c004e745108302185100005001e02188300440001e000c8300c404c01c00c00406483005565801800006806604c4340300000a802c09c8300c406604d04d03401c0380400240fc01a04d04c03903443402c01801c0240c00fc0316588b40000180b401c00c03011c0aa03804203403002c04c4380440b40a408043843403000c0000f00f665c0001b80181ba04d04c01801c0f265d0310aa0404380b402c0c00b40400f402c0c404d03801c0400340240640800180800180c006806400802503809c4340c003401c00c0b40800310385010410380b44348a800001800c0a801c0300fe03406804003002400443404411c0000190b406402401c0080540000e90300ea0410420344350310b48b50300f404002403c4384340c405403803401c0181140e50320a804000043a0410410300e44341541000f503043421e0a804c43665c0c604d04c04003002003802406451204002265c0fc01a65c8a800001811104006402402005422809c02204d04c03903443402c0180b402401c0200c00fc0302280e40b409802165c0442290420300b44380a800c03001c0fc0b50340e90410344360320b40e50420300b44384388a05008302180e00001c00d4218
  | 17 => 0x203015412443802603017000c0180c007406806604d04c0144380260308d84380260301401240a80260301801421100280a81240240300110a80240740240110300c00a443843407403012003c08504c01c0100080300180290a804407402c02817003c00c01843803407402726001ba5412103000c02e0300280744381200280250b48b4439042030028434045042030028120028025a541210400300284350300240101dc06804c83803000c00443416804403002801800011821810c0300142180a40a504203000017004403001800800c03200c00800011010043801c00c1dc8380184341681dc83843416804408604d04c02801001c01807d03003c43802408604043a0310310a812011103002417003c00c0180741700180b84380860410404360310301208a903503002408604104043a0310301208a10304380241210a083843a0410410340300a407404043803012050003c08406405403801002801c01810103002403c43604104103050043412010103000c43443403c0245020420310300744341208b503002417104403c00c0180740241700ac4348b40a84345020410420310304341208a10300250a08a04341210a004c14611003d03002802443404c02443407443412003043803c06403c83801807d04c02800aa6a04c018039032a6a0310310a804443aa6a65c12083903002443803c0248380244380a48b443403c026a6a04104043603103043aa6a65c12083903503002417003c00c01aa6802443800c0208b40a0438a680a0838438022a6a041041034030e5c00c8a00241908a043802406804c8380300081688a00440180000e00300d402803002800c0080440180010aa03004401c00d0300d48a04340d40848384380184341688a104000043603001801d03400d0308384384340181688a103400c0004340308380308a016804504c83816811002811104c83804003002816802504165816a04104001843400c03216811104c83843404000c03043802504104043800c16801a10203007402801800c43904c01003000c83904003043843400d04002414611203002802404043504004c01811083803000d035040434031040434030e5c02416904016a04104001800c00403216811104c43801004000c031040438031040434030168438041a5403011104c040838438010030026040024011034434028168027a55040024434838e5c02504001806443403000404e04001965c06404c43403000604001a04203003c01806404c43403204001a04203003c01803c02801001965c06603000c03c01843604001803401c06400903265801a65800d03265803400d03265803400d03265804103265803400d03326003c00c01a0366580180300540400180644340301dc16002c0180640340300140540181dc06404c43400d0300
  | 18 => 0x1240c000d6581e603000c07406806604c43603000c0a802e04d04c04003801c06402803c4381e50301e412d03050043800c168e5c04409c43903002aa681840c204d04c03843402e65c12d0305000741700444396588b400c01801400c0b40a803813203203402c17007404c4380440b40a44340300c012003e04d04c02800801c0181b90300b60404390a802c1200c018503002c0b803c1e465c0c20341e40b84380cc01c06404d0300281e41250308b400c0180cc0c007406806400c0084350300cc0c00680280381250302290410300c043409104001d0300704350300188aa03400e031a6812c0a803801d65c1120320340680400040001704340450b406405401000801c0180e903165c0ea0410404360310301210b48b503017007443404443805403402803801c0e50320a803c4360410410300e44341541204341250320a804c43604d04c04000406503002803c1e50301e400d0308b400c0188a903400d0310300640540200180a807406806400c0050310340e60410404360310300701710300a42180e00d403c03000c21804403c00c0d60300d400c43403c03c01c00e0300440244396588a000c0180a006806402000c0a84381320308a000c06565c1100a104c02800a04e0304381220a08a043a0308a000c0180680640280204381260301220a08a20301220a08a043a03001800c03c0180d904c02800a04c01807d0300da04043a0310310a81860d88d90320a08a04380da0410404360310301120d90a88a90350300680001700c00204340444380306340d403c0d404c03c0190b406405403802800801c1410320410404340d41404341240d50320a003c43565d0404360308b40d50b40301400d42220a08a021e0a08a00a00400300200d565aa540b4022a540a843a032a5565d04c04000a0304381220a08a083843801912512404c0b402043a0301220a004c1220a08384380188a00d404c0a802014111004003c04c030028125040034056658a3615413002a65843414012412111004003043412604104203405404c1400a802812012403204104003403015414412403e03002843604104203405404e03400c0040311100a802812012403204104203403004e1240a812003204d04c83801c00c06503002802400d0301e503000c01800d03503000c01d03000c01800c01a00d04103400c05404c11810c04003003c02802800c12004443800c16812003c50204003e03001843800c16812003c10c00c03c43443800c43416812003c03c4341720308380a41200a443800c16812003c0a604003c17203103400043400c03004043800c16812003c13003812c00c0301256581701300180740680640140a802443813203017016812c0180c104c02807604e03043802420c43a0301701240180cc0c006806402802443812603002413
  | 19 => 0xd012ce5c061040064040004000436030040004002030434e741c60404344360308da04043603404c1dc03043504c03401801ce5e03006802401c00165a0300c401c00011565a0301100c504c0181160300c406802400165a03126005803401c11503006a04c03401c435030024036030e5c11403401b254e5d040024556030434e5c024e7401c00903125406604c0200180050310d88da030e7603043481002403481103001b2550301d01110400301c504003043604c03401c115031658024434018e5f25421822419402000001903004c004018e5c43400d03000c43401804d03443402400401803f25410204c01c43503010001d0350305104350340dc08604c02001800503051103443611051104012c110018e5d03051104043503725406404000402403c43406804001d03043725404000402403c4340b60405004341140b725443406404c0040226590308da0420344340a325604043604104050043604104050203443604103043411404103050204043404c027254026658434e5c0200a103000810204e268435030e5c02004c02402003c018437254554064023043030e5f2540d80b4e5d0400232540400200b402403c434102269035032268560435035034554434018e5f25626804c434020e5d0400222681df2540d90401d22681c50404350341000c604ce5d030024e5c0a0024e750344340240200a32540dce5f254e5c04d040434024e5c064020434030018e5c0a021821819443400001d0300a050043704001b030434e5c0a000019503503000843603001c04c018e5c43400d03081000800003104000c00043503003000c01c01881000c04c43406400725603104000c12c11004c0400180044360301681100b504000c064004042030434562040435034556041034434e5d04000d0d88da04016a04103443411001812ce5c03000e03043725603104000e030e5c00e03001800e65843503265806404000665903001843665801804103265804043665801806801e65903001903265803402443604001843401a65806443401a65843400c01a65843403000404c036040018034434069030e5c03400443604004002000405503001806804003401800e658068018e5c0340680181020344340060400180d806801806800c0180b406404065801800443401d0300d804e0344340320400180360300180050300200040180400340300040180d80b404003000401803000e65801c01803603001c0180da03000401800406402010203443604001803000401800c0a00340400540180d80a000404001805504c03401c01665806503002816103001c0140640540185000e40d40a802c1716580440900140d503050007103001821820c20003003c02820c00c83843803c43800c1dc43412003c00c21804403003c02802404412c038030
  | 20 => 0x843404c02001800508c88d03001d08e04043503083007404103001c0260a804c43400d0b402407002406404c02800800403002401c00c00401a08c04603001c00c03001e08c04043a03001e04007043a08c04043603001e0404340300710a803000c01c018005a548b40390b403007003000c01c02608c83203004c43403204001804003a03000401806404c00c0200040300040140180400300040b401804003a03000401803803000c00401806443403000c00404c01c01800406403665903001903000401c02e65a6580340050380340d001800665803401c00401a65803401c0040180360400180a005404001a67406443402c2340180640a0014054019a540a006404c02001800443401c02c04c034004015a550390a043802c23c22002c6580440c002043404423c658054437a540404384344390a023c0a0054021a54019a5406404d03802c0280201dc00403401c09c01402c040439038040434040434040018005a5507406404d03843801800667403402001c02e0a004003402c67404103843803402c01ba54041038438040435a684390380200a004103843a03443402001ba560a00400340200040b4055030019032a680fc01a04043803400488c006a6801843801c0fc0180fc0040180fc4380180a00040540400189840d80a00542480180a003402c43804443803400843800498406804c03402c0fc01c01a66c2490a0034007a544389850a80a00680fc01c0360a0040438034004054437a54438034056a6865ba540d80a00040440540180dc0a004c0380680340fc01e0a00420a00400349840a006804c00403401c01843a0a004043800401ba5443a0a0040034438e5c01ba5443a0a004003c02817000c04c00843802404000002402400c03002800800001e65a66c0f40d803000c00843802401d6582180d800800d65843883002404c03000843802504002406804c02c0300250a043443904002c06805802403000c06804d0a043443904103006804c0350a104043843503003c02802403c02800001c02504002c0250a043843504003000c4384340080f443843483043903043443843503001c00d03083000017000c02400c06804d0340300244341710a043904003000006802421805803c00e03001c03001400c21803001c00d0344340290a002443904002504000c00a03226807a04c03401c43503003406006104006165800400325403c43407801d030434e5e65b2544340dc05404c02001800603011007a04c435031034434e6f2541100790350308d843503407806903043402000325403c4344340a10400232544340dc0a10432544350304372560400360301305560404372550d88da0401de04043725565904098406104004c434018007256030e5d0a04372560309850410345620404350349840610420410344341
  | 21 => 0x4d04d03083108d0308301110c004c0400248384340ac07443843408003401c00e65883804d04083843811008043803401c83802665904083843811008003402801c02483a65804e04104050104083843811004083843803450002410004e04104002665823411c11002443404c43803402011002483005807ea68039035032a6a041040438435032a6a04d04c43503083083a0a004c0404348301088384380a6a6904c838438830022a6a04d04c8390308320a10344360a08a0838e5c0248388a04345004385008308a00010310340e007404103443483000904000043401904c0084348300188385008a04344388a050083043503083000c07104c01c83001904000c02406404c03400402483005a08c04c04043603083204043403007204d04c43400c83208c04c04043603083204043403007204d04c00c83a04d04c00c8308b408c83803208e03083104002400c140124066658018140019a540341fe658064020019a540341fe65a0a80401fc140064029a5403401a65a0a8040140108065a540341fe65801810a65ba560a80400aba54435a6a0a80400180084360a80401240640400300200180704340188a80040189840a807401c0300fe0340400304344380440dc0540380340200180040e503006404c0300200440180dc04c00405604d04c0400640208300188a800401806604da5402083001806404c02001c01888c00401806806603803403c02001c02814003208c88e03001c1c812401a08c04043603001e0404340320340950b48b40a803001c04c0400181caa6a04d04c04003002000c066a688a8004019a5604c030018a68022a6888c00401804c008004830e5c04003001011800416c10c01c04400450204104001810c00443410007800c004434e5c01d040434018004e5c83013419404003001800016c83000c00416c01e04104001c8300d804c00c06401c0208300301481400740700316581500180fc0189840c007604d04c01a0340704381400181240c006806603843803402402001c07001814003015414001e03043883000401c01801c0040189841480b443801c8301400a801c124830e5c0040190b40450a802401d0300121000fc0c007443843403001001da6103002c01c024a6006404c00402c02483001c02013401808406604d04c0200180040110320400c0435a5402001c01908c88c02801c07403503001c024040030020e5ce74044004830e74e5c02011800903010c07004503001c07001c018020e74e5c0440de04d04c0100200180040850300fd03001c0860410420384350310a88a903001c0dc0d800401908c88d03001c58508d03083007404043803013450001c10008402001103010e0a804043401c14010103001c4360a804043843401c5020410420350304340ac0040180760380ac4348b40a843
  | 22 => 0x2801c1108320404380310a802c09c04006802e0410420410408a006843911083208c0680420304360400300944341251100a8068434830e760404345fa08e0308300a88a006843911083004c0340320a80fc0180fc0600fc01803007043807604c0a802c01803407043818411207604c0400344381621120300684381240356584381421100a80684389de1100684388321100a80684381248300450a80240690410300100761000c00a404003843407403001006818411004c02c0041148310aa04043803407402c1ba10007403402c0184380c006a65c02c0b904002604104003465c65c1b818411610003443a04104043843665c8a011006843908c88c83002816908d0304380410340b843904d03443401c00c0180fe65e65c10000c01c0fd03504103443504c04001800c8a103443851104103443504c02801c0fc01903665e04104104043503412c0a407404003803403050006a0a806804203843604104103050043411006903010043404002443443a0404341284384348a01100684390a043908c88d03006908c4350308320a804c03843412c0744341640b403043806805804c0340201108304380fc06803a0a00400380684350300fc06908c03806a0a04382401008a002443904000c02411004c03400483011608c04043a0300690aa04007043811006800c83216a04104043a08c0680420304350a806883000e04104000c11006843816a08e03083043400404c03204001965c00403843604006803204001806804165c01843400604001a04006803801806803204001a04c0040b404c43401c83001803503a6590300c002e65a6584366590a006843803406665908f26803401a65811006843803401a04003401965e03401a65809c43483008104c0184341240c007406400803809c43403401c0180380b406c02c03004002c03c4344381fc1408300588380b804c43443806402006c06843802c0180a00340300a00180081240340904388a204d04e0308304380d801807d03503006806406c02c02801c01808c03403001803c03401c02803815403088e04d04e03083088e04d04e03083004504002805904c02806404c0040001fc83005a04009c4348b604d04c8308a204d04c83003402804c83083a08c04c04043603083204043403009898604c43412483015804083083a08c4360308301108a204d04c43883006806443803402401807406c02c0300c007412401803407043904e0308304381640708308da04d04c43a03083104c13083098604d04c4388300450400240640041fc1240248300585560404380744348b604d04d0308310b48b44380348a204d04d03083088d04c83002908d03083004c03483083805808401c07d0350320b404c04103443483008604104043503011204d04c4350308308a204d04c43903083088e
  | 23 => 0xc83883043903410b26443503402c67465c83843903443402c027a572660a08a000d0a802407002903410806806404c02801c00726402403483010043402c00c01b26503443404402f26443403000c02f26608c04043843603083326616903400c83903443404604104326616903400c8332648b408c83803083007000c10904002400f26483103402c16811010043503402c010026a6006400265843402c04003402e65802c01265a65804203443403001802e65801043604001a65806483a03443603001a65843403001001a034642040438434a6843a04001c04e0341de040439832676040438434a6843a0400688d804c00c00402000c03000a65883801c01402001c04c00c00811043806811006802000e8304396740400308a000402003800c00a65883012011006800802043800e6588301116580381dc06811003c01c0381dd6580288d80a000003002800965801c04d0341dd04043805804c03803002801c04d0341dd0404381590408308380404388380300988a011043803001c0fc04c0080f402403000800e65804083804051002665c0fc43803000802001c00e6580f402400c0300000fe65804002804083803000043802804c00c00811043806811006800c0244396740408d80a043800c02400965803001c11043800c00965883002412c4380300240fc0f404c03000802403167504043805803800803002401c00567504103283167504043843904103001c8a000043903001c00567504103103003c43802403c00103001c0004390300248380240b40316750400a443801c008110058030026a696750410308384380200a56750404388380250416740a4a69675041032a6903002403c0a483800103006851002504083843802402167504002400443843843400803104001c0e043400903104043843400304001c51043400903104083000c01c02400c0a406804d0344340304380241dd04006805802400803001c03c00c43a03001c06904043806804d0344340244381dd04003001c00c83801403001c0a403001c00c4390344340241dd04083800c0004380300250410344340241dd0416580a809402c044438004510830e740a404043806804203809c83165811001807406604c0300184340a802e65c1840c104c11004001c03843415401801c0540e90310380b80404344380b804c43443812411001c0400384360404380200fc0180fc0600a204c0180a802c03409043818604c0408a00344388a20321100684381240408a005403443812c5100306340681288a104043843451204043883265c01812e65c1108a806165811088c01803402c0180a802801c08c0381640301dc03404002801c03816411088c01a08c88e0300681100e40a805404001c0380340fc0180aa08c88e0300681680450a802809c02805804c02c0040
  | 24 => 0x4c10001c06c02e65801c0180380e503043443403265816006404002c01a6588b40340185028b604283002c0d165804604104043402c04c4388a08304366741400380300e043402c62c2228a04340d44388a043483004483043402c83004443405483006404c02c0196588a003401b2648a004043803402d65806c01921c06401823c05a8a003402e83165823c01e11006c02d6588a203121c4380356580d003401804043401c01665816006483001a6588b40340185028b68a204002c1cd65804604104043402c04e0400d40448326588a003401805483006404c02c01965888c03401b26488da6803402d65806c01921c2000d406401817e88c05803402e83165801ea6211006c02d65888e03121c03565888c0340181dc8300d40372640680640280001fc04c83002c0400341fc83002f26403401083326403401083004f26403483083b26443903404002c04326483083b26503483002c2090344340460410432661d01108a04390348308b40361c483015410104002ea604348a00361c483004043403265806410002e6588b403401810a8b68a204283002d65804604104002c04c0d40460426588a003401a65888c034018004e5c43483010004003801816c43411817c05a04283a00e8305a443483004443450204104001804003483001816c00c43483050204104083001817c0400348301dc04c83001806405402c03483165801816726404043802c16565806c0180d40660405a410805803683002d65a11002401c06c02d6581560305a44380340708300040d56580181516740d483003565801813326401003483326498458443a0348301241800356581080180356588748332641dc0740680641fc04c83002c08406604c43503010002c0401fc11002f26403401083b2648b403504043802f26404003401002f26403402801002f266040034011a6002c04002c10803565802d041a6265c11010802c11004043401810002c439040025659040034018e5d04c03401c01083811c43504002404d04043410802fa5565904043843665ce5c02504067401001ce5d65a04104001867402c00665c11104c83843801c010040034018024169040024e5d65a041040034019a6011104c01c01004083803402802401904083843904043411043802c04003410802565801904004f26403483883008604c10002c01843407d03326443903404002f2640c103443503002c1190344340460410432661908a043903503083326458488d03503083326508d03083017c1501300a401c04c0305a443408406403801c10103043404002e1100244348b50305a40340a88a103003488c03417c03450002402410043423411c11265802443413001c03043843410006443402c83801807e04ea6810002c018434039032a69034434046a6b264839035030830e5
  | 25 => 0x3803011402816a0380288b420816910003812e65c0301a61681100b603002843a0380281688b403801012e65c0320b408e0380300381680288b611210006904c01c0140120300261100c006884c04203801c01203002603001007002504c03001000802811402401003002c00c4340c001002401103010001503011401010003011401002c10003002401401011401203010043420800d03002f26108d03002458410001003903108e03001002c1b81a411401002f26065d08c43503108c0101c4024a340101140c326043411001503001083508e03103326065d08c0241dc01000903065c1dd08e03001002465c20803816811443ba55a6726108c02416843400d03003801c01004c02903011484043403001002608c43401004c02400c1010308a801208c43402406806405884d03801c00d03002804400c84002402400c43800c84002400d03843400c84002402400d65c04400c8400241690380288b41dd03002400c16402c0f002c1b904002c1a002d65904002e0b404002c00400003803c434e5c18416665803843504001002904001203104001002855604104043603002801402801165802801018504002a15404c040434018014010004206030e5c1841550a04340141ba03018504002856204104043603017402812c028e5d04002a1540640400140100040004360310b404000400003a0304349c6041040030e744341550400140120304349dc16215404c01401003043408406405401010103002402d040010025040010e5c02e1000340181a002ce5d040010024556041042030434e5d040010024e7401d0300100240100110321121000180140110309d10400300289c41010400300104356580240100d003001c00c008434018e5c2180e804c00800401800c434e5d03003104043401a10004c03903443402c01801c0240401a003051204104043603103051204001103012e100038018010e5d03051010204104043503211006404000402603803c43408404000402403803c4340b60410410305004341280b411403843604103001050043604104050043503211204203903043604043404c01002411002403801265843402401211210004c43401406400401203104000c02610004c04003801801000412c4360309680b504001203104000c02611006404000603a030434561040434012030556041040436030e5d04000c02412e100038018010e5c03001203011010043401401203104000e03002400c066a5401802c04043403265801815402c0548388302342341fc03326404c83820a04c43403001801015404002c2080341fc04002c04003006404c01802e65806c01806401843402c2442081401241000e443405983011802e6585018a104183983002e6580440180598b583803583002e65911004043410002e04104002c
  | 26 => 0xc88e0300288400100241800c083001084043a0300284341bc8b403002883001002408406805884c01083002c025a6006806484c034032a6402402ea648b4438840026a648b40100248a80440248404340248aaa6565c8a0044026a6488c044026a6488c01002406804c00443484083000e65c06805803002401c83001c02c00007406884043806804c03c02802443443884003c01c0104388a084083001e65c03c01006806804c01000443484083016803c02483016801c83001006400c00843403001c00800002a65e6740f409c8300e801c06d03903058608c88e03083265c16910003802c12c83003801265c12c83008401c07c8308361901811104348300b50a083083608e03083009043402c0808304348308c00c008400802403809c4341008b40240100b401c03011e03804002403c43843417c17801c0306405001541288c00b41140384341840b40a84384344388a08305000a004c84083000843409043402c4348300808a04385008308420344340908301008b402409103843483010088c02611006a03803402402808c02c01c11c03010088c02403802402808c01c0341980300b608c88e03017c1681141000e40b402803803565c10088c0260a843403009a03a65e1d0185100434830026a600ac4341c51110388304340ac0741704384341bc1250400101008310386741c488c43483203103843843483211006a04c03002c01c01004002416a1120384380101808300241681080c003801c11404c83108c0132640241c44350300100241080a80381000341140272641141f82380272640250a80a81bc1000100381b81841b003811726465c1b018411403967043726465c0250a80100084340384340081dc0250a817c1101000100a80381fc0340289d20a90a8434038234184024011a6043411c02565808002408002511110006805801c01401103002511110006805801c01503002508c010025a6508c01002401d03001002400d10008c08405803801c02a08c4388b402412c0251000c204c03802c43412d03001203884001002405801c00904c0281141b90321680b408c03001002d11008c06884d03801c02903208c4348a802417802608c4348a80248b400d0391100c00680090390304341780c00b401c01084d03103908e04103043422809103801d03002401211006801c0140120308348a800c02403801c0100a803412e0311680b48a80120308400100240680400240041704340ac0e90b406802802400801c06d0300ea08d0404360310321688b40110380ac84002402417004043843403801c0340281140e50320a84340300700e608d04043603103216916895443503216a0a88a88d80d005a65c03802503002a65c0a608c8a002665c1740248b40a402508c4380248b665e08c4348a002665c8a800c0241681111000
  | 27 => 0x1248b402a6741248b40cc1248b402812402884c07443a030438068e74076030068064024008438e7403603006884c4380760300c006843801c07603006405402400800443a03001c1320301f60300c007604c000036030438e741ea03012603006843801ce58076030074438068438e5a03007401c11410883002d1100688400301f802402c8b44348a80248a80100240ac8400241fc1840c007403803402c1140e503111110006805802c01083043401088c02402401008484c02c02802488c01002608
  | _ => 0

def or04hash11 : Nat → Nat
  | 0 => 0xdba3e058200a09368148a410a8480c0e02800e6251e820080f0580462124f01836020116004060083cca02068200a3012060005a0003434163c8745a020703c1a08558303c022e8c97806080381210241c198390f81c040e0103c1404098184200118003e0500070780d158240a0c060a02a2600c380046010cc96ae0801c040500028022c121685c0011000240f001b0104d13008004d10004040c11014080a0016446141a81c1c070ea20283e0d0dd4a06021500a510400c30320d090021609810220b0a84c000e00004041c0100000111e0080e2f44930042c1b1d000680a9481423138443249000541430009c40003039240e3a3e014ecc93f08090150282016000600c0cd80681040190480002000080c623902010080c2b81416230b8380a0b0304c0822001d00411060082e2a0691c020b07840a8002e81842000100c020a0c8040209018184c2742a2824130e1106c020b0c816691e86000030020ca003010a05401000403a370204428030109c0205018241016381305401010242e1200874480044854280d010bc461402800000109874585a0081c16011301120020b0d00009038013c150b010aa0f0109800003283c7e070989c08250080022000c84c1c1a0100006290080400180501416150881c162117034243f0393c261f0001c00011d82812001d00c2432008041c0e000242a1e2d0002008028bc0016008c0000c0701804031300414402680402000480026070182c262104a2400570082806111580c1a230c80c1604058ac0006000080204040141a0300098b62103828200100064080008004140f0001090100408c08001d08c1404008c82003038dd6a12000341a001d05402120980000060b04416410203414050180402000c02412000d03800264201400000082006172280c00000480862060281818060183c5a020314c0c29048142818038b05e000d85406800283408000504410230083006121d0300a240202c125000ad802000b800044801038300c0b05810400f05c06000002c0601258440216040000c0701838342303004cc022e86000160300c7e1c0886806200080c00050606c060403918441119844e0010885002020b00c3c0a088081a190c000000207834120e0100400530000408020000002000a0080016020006c072484030050200046011900454413a830020e1a8e02c00010300a0100824021904000422b0082880020000026100780c08111b808060f0181c001b0180802000201c20060480400040380c120d048ac00130b004420f010680e1c0a804100702008140000000480c000100449358e0540402000100005818200201810042411004d611028040808009801c0900008721517030060d1180400230684400031885826180a0080002028000a08028580401000100402008040e101a0100011
  | 1 => 0xa111d259276adc0000628f99450e2c988d1008255968482400008bbe9502d832cc75b837e7d9580ba46804ec1ce9056e9ea000093b88000000000000c9db256b5edf0e5bf3294c079000009329c433800028773142b319f012a40000161f5c4e812af27b2000031662c63e44698397e32590f378bd316e170fdca2a2e16400007bc8bd7b3a302a1a16b4a80001e13fc4c7709c357ed296f8324c999854d26658178723c9ae31ba336a8cc8a909d3e78d5ed5f73b33a9ca3804d530293d2c9ad34d48f451781ced0e6673376730117ba255c65138d6a36124b81aeae370d8a3f243784d26a2549334bd955edb965ad60678175fa6c600005867e0d8681cde3b500000000308ed1067b3b97928a604bf84f01b998c2ec70cd6cf88bb5c2b1c653d8c1d2048d7006a1563ac4a4f598464751d64400006917800016561212f10af470d0f61d1bf75e2668cbe569c1aaa451c7430880ef52a62892e6152e7fa7152dc94e0f88f229d8b7d8d7e90fc3629e0c1ec90c4af896d6a273e11b3a92db5a7f2131986b40fda4b1214a32212b01e0000924841fd66c0bc08b00002a22d0798e42b5434a1e918077582fe4331009dadcb521fa37d6064cab11c051d1c4d8408000022d773a1ad81a67bcb5cfa0876d1e2844a3863fa4064d49636ba10b797a149a9adbb322810e3f14846161b218cb05b9b4c000126a21a7b9d0b86d66016fd3c94417881a8f00ff81c79f5142a5c13df15270b21605640b7cba16095ca167f741c9fcc4c1186d0e8cfc8c00629ece79e1baa0b691580679737f74a0ce935f00d69174d1cca8a5e4858451c4b17ec85ea97048a7f9e2b8cd3f081f3000b1b18ed20c10a2f28a1494a2a40567813742b455ec000182b598623882f2ac80000090009407466d36b508b02ce3ccb9850aa9959c8804c3e8b56c604e69ab20125c339d42f018d44ce9044c1ac4d8603e86a437992cbda0f5882e58af3852297f7859b5056c90260434000181123bca98ad8ca4e0000d0c848cd74632c4fa487a622cc706740b25038b571d2021c8028163bc2bf0b8da353a10456174ccc0f163db3a1a21b02a2a47e4078353ce6d7fd263cb6a0100415058746c0a2b0002a3800048ce1204044000d0309800240010c18220385d589c2880804f20300010020700802071d5b02a322181c260d2580000060b8bc0e0b2482c2a4a0200c1a030d9341e0a0200c6205210481c02000b0006a138040c02028146e541218054050d8100e4f400a8802d108005a310100800411d8d4da1b04018300842808be0027db9565215810b4350006c5c830107402380e8002c39068280238180081a0c068580c051e0186c14268897a1b0002e28010306824160202c062c000141239000080260090d0122b03804004f00010021d002f40000bf03c16e2228001425070001c330d91
  | 2 => 0x787c5913ea18c508b4acd00000d0b3e5dd3af32128bf3a01c562907140c600004cb56abc35844c97f8d4240001934ae24940d688b0ad0f7000064a650141214959770c9fccab646842439220db249961e2c0339050fe8ff27fe39b88d790c0ec97f2901844e0fec9a082e91ffeddb60087160dba3981e6b430f42edbb1c4c69bced8638efc2b8c47ea2dc2710580b58ee2ac7af23e83aa3901d8ecda71ceb48b535e8e59b47c238d7a0498448259d1a2e64893c09be127081765ec4217494c5a8f0e59c6a9f6e8c920d66412e80d8c0a8c1bb099194494d4f10350ea2ada97342da381ed9bfe4cacf6e9e8a33c1b1679ac5773016c4d7f10b3977013f5a54cd2f31b8293824d236be9625876903aa4b520de832fdc08855b252d6481e5e80144487250901797a430911a65dbb1f5bbcbbc55f1019c2abc05f8d4229022e8c44b88f56776e5de850c991e996e2099568c894ec4979c185347091f0823204415d2c27b6f2ddb363ee63a9329ac51f5ca12b0c733daf94df8b89c15e998198aa3021963307243987ff8a0b67a7d0f999e8291ae879531292de682138889e6447a93556187c0f32ac24a30ec93b50e7136715ea2674bf1eec0e1312bc8e777824a0bd2133f4fe070f53a74990ff43fd476d528a892346333a57b885a4c9d20109988a33b500001a14f48276b95e4c2289a76594627f5a3540001889938d48cb2b006f502a2a4aa462ccbb6b0031301a2205853482680ab7800008cee34155869e0925890d377842c1014380e5362097b1b919b8000105800000000024b1f55dafa2d2866b4fc574d4345780002ef5b6786a42e00003e8f5e2c04c56f4d30e7b118351373417b991b6000080e65d07388b66842000000003ebd7c74f9023762df4ae40000f835c1c61a2f508c022372dc9fab82c1b9e8b95db02637ab8a8ab1d99708000045c78082bce76431331c293c2803e7ade695ac82b9cd078689676aa000041772c88408ce00000000164b6d57088c82495ec00e0000c2253ce57a046040a3c5ee8932e9fea36500001d6e964f171d2000000000000163bf00000c88c034db48900004c14e232600004051a8b8ae488577e000015dcd00340615434bd1bb32735987f00006c60b453b223c000000000893e21bd8b1aa084f04476626000079d8305084523f42591284a469f62603240de9b0d79f033b053646ca4364000092df356abc7880000e3cc80003af93d35e7bff08f1e25b771770000192700000909779eee056ae345a6a901c0c962a887b92f800df7461789b8032f2169000018e6e0000630624b37009574aab3a57d4a4ee05c6c95aeca99a8000088a560a9d138baf8ed557311dc5af925eef527e004e8d750db2000003e86d932092fa8b000004d576844d44cc00000c84c0e2ac79ec059e1896c154826b00003967245b0557
  | 3 => 0x9a1dc4142adff73a66b44c9e5c000006b8f937550ce47cce75e682015f61eb64000019710000351a8a8b85356ba1da817b77f328f9000000000b10a30fef13274a7d80bb3918da244c5a37339b9faf01258e2c45681103b610a2d6e0000d98724b74af66f3bd22d3e9a262e31d766eb20c945ca9ce682b723bc1ffda2741756aa9f4def000017281945d14a47e8bd96ef89888000000018248000000001d1b028b6a0684437e847e0000c8a5c5e840001218b70d8b1bc526e400004220c10c0000013ed526b543680001e81efbcef873e894b188672889869f453e0000c41dc9d8a097e00009ba904e32ef3635faa1e9056ede2060000106ac8e6000012890000078e724ad62704f8fea1fcaa193e50b0c0cc1bf404e171e4335e800030452000000004e2b801f1b884dc6dad5840001f2aa2c4bc44d24b820000795100001207816e2000075c92ef3c0000e09bd04ba8dc0b1e794080000289786757821a38db8000100824954488deed3ba41be02df16b26c23762d1229800000001e40ed33ff505c0001f782805151b0f07a9238388b08000203c2000000001dbb000000000e2bc9842323d462f9000039ded402a307f0000000010f5c548200001d378c31447c10a64e5418a18a013251a634185a12731877398ec91d8170f86090e731f9c457ce70700007983588d1f83a00002032f8cba0000843080002abdfa636000074a4ee1e2676f638f8ca5fe0ba58d2e8e9f0559c73ba1ad1bc0c60dd068396d52465383800000f0680000200c907cbb3e2c388b8a4385be000019d710261c0aa87179b3f7c06481a446efe96280001e77945434c5378e7b2e19c53400003e22e04df530dc3a0e18c9717200e2ab84f8f0149fe023271d300001241b02b96926dd1080000c0ce7afa084e7a12c000012e5a440a091800eb00007c321ee3d70920000743778e103779f8053123c000028580000093936e1e0000c8f1800028b740000ea516a336c1ea037b185144f6de0a4a0da32bf2c4932366430af95798dc9a81ca0af23273ddb9ad94000053ac71780ce97310b39ea34e814b2721656b3875081e54b0276c29b34897f06dd4c652151d4dfc8f756131178d08c7e78cb2ad489100003628ee57a79361dfe7877800000000785080001144d005a44f3929b088bb6bd280003cf56000000002ce93ea2530425bd725cf80000000072fc3df46e091335709762902e02d5440c4072663600000c57dd3ad78d15e84fb070487e8122ba4e4b52a326c3daee23fc0000c83045c1d086ec2eeb2336603aa6ced67c5199d5bf0461a28d381b380000000183154979204440000951ed08bc53308525259b712d183d260b0c0000000000012ec0f6f63860d82e508c900dec2e02215526d78259097180003656ba686fb9d2ca3a02d77457f13c910b7025885ca92883977
  | 4 => 0x460a92ab8bca0547e8b21f4412bf569461c12323f9fb0f2e1a602426323f0e49481c3031646943e9e20e8f00ce30f8858d8eaca9c2e5fc82a968e1c8676980cab8acc613cef8d6c2d9406a35a8715a7fc000058c478c44d32e3a341cebc47a776a049c8fa17e40281084c9c451751ef7a11303a6b222f742dd10d881a68d5cd80e825897bc1f11f64c5664e5c309c0fd40eddf23061f7acffe6063867a244b3853bad48a3f21845ce0f72087e6f77017481983152e52f708c69a642f6800000000619575159c666c30079fa40000b6e44ae65db1dc2fe0000aafe2c7512c155455a3f00cf5d05cc809a034555dc9c18b8620181d62232a29301b770d5adb0628a03385ab33582da6ebe50d2a25ee1828808b789400001c53b67cf4064cba3be0b000008348a33c39f370cc808aa0000560016fa7f456788f0cae56238a7e3011661885ac56019f896d6d7534cd64599112175f576e5146410a01bc339050bf44583e900003c4f933b3bc2f000000001024d3816c58542e2867e1a91600002e87ab89b688665853ccec914f320299ea46ab516ba00005a02000011221f17f74b1930b7b2fe2010c046c0000574598af80002e5f7d6a9bba5c84c38d3775d1b2954d518ccdae12683205c531cb63c5f9c3ee8daad90dfd312e3925492623a3a52cc90b45e8e2ef8a3ae4a6141005465a256aa27e345f364b9e0625b6ce09b4c564000000004e02d2661170ba88b484884053c3c638ecc1f56f09b720918ab6136947b115ded96fedae52a5da1a36a274c37120f956773053c0ee800010244fa6425cff2b70a17d000028c95f0565144a3dec8763a7aa682f423819c31641ca0a4617180003509c0000001b6100326f2c024c8ef4174049e8d1a09a5d8da06e7ed3358ca742cffa6d00e0a15b68d868b42b817e98be6b05e1af9132f9c128302784fbec7b13c52584f3cba7f65fd963e941b509fc2800ac5c48044a1b37bf3a4d41f9a6e73615d5a59d847badb4c00a217829dc2f0a737864256fc84243d244cd40c72885fa136505a6bfeb471a2ecf77e04bf26cf9949668220b1c80176a0a3bd396cbb5ecae32130d610442a2979cac95202200007d9436176a88a1809b09d2702eb2f14b9ac8985c99472e631b19ce37c24ba3579b8500000000004cbec0b30c828ee8f81f9133c1984c461f65efa9b119092d2f82c6dbeef1268000094381aff4df5ca17e0000c3c4459cac969f882cb5880002c88600005bd924d0ec7f47755c9e03484885ef10ee440bdcf1223d6366ac98ce95db038600005248800024989b1e870f398970000000000c10a1e6d46cd85c90000000000000a4ba9296800000000516272c74c77122f6a4e85c08b80650ac926f92b1030cdf9046000050ed811b7f040f4fc9c0f0000200ff45b5000004ab343d814e2b9577c4ac000180ec
  | 5 => 0x15749b540000b852812344c9567ca4460d8fd5e2731082f5421214b514d082776c6f972ed9eba2e6c163409a0a1952389312e30cf155ae626af0742423da0b370d9f30f00002c38a10fbe73953feb11134c0dc2839ad2718f4c724c6aa2122fd295ed04c60ea3e479da08a82c73d425bd0c8bcd9be27212b2b0224aea7954fe20f149cce6c3465181bf093cd30b5f309000052000a681c0b0814168ecfc0b895314831b05d141e561aa29a4117b666367088f94329d71eafcc7694a698002f8d76c3a22094e817d6abce78c3c683a01ccf84a04eabd548452cd51531543f400002a642f34ba2abfda8b8f5474eb832804b4d260c0000a3d9800000000503f70c7e1a7d018242fb02f78000000014145f9923554409e498cd191b8897e435284040000207078e416289000000000000084f528742d919802e8018fb5e305b36eefa64d202b0c039a2f1765b83df152b089fad628dabc65cce4274d78bf24261f7a5032701a92a45589ee9615847fa45b1c264718e28112784db80000113340906452502a05027f41899d1bef0a1734929aa82098adeee628dbc9b16a4696ac6307b35d0d180000e3cb11bc1206c2e6d327c000059a43810a91b0a10d00002efc6b690a3e31dac304c571b4eb952c0822e769238d964b9d4ae4176059a2a011f280000f45241993859000000000f35ba49480001e79cf07680001ce4ee4a4ec0e01f6aefe8519542ec9c0a1c90103449b8c98b757014727a2b7458e2f6aab268f836ee1b73aa46152c5875156892776a29c19829004dca0050c21098c87a1a6a7e7a8085e80000ae2e00004be5a806ea20181c09922c1bc9b142b3875c0140f460c0291a430b980001ab4032330abe25da8a231775e99a81dfa0231c0000542baced64cd8684a7364518dc80e14107d129ad81c08f9272b60aa8604327c2000081e7d0a624620000091ead9a3a26ad95e9a1094dfd9e1f060fbe0560c287ab0125ea7b62e97db8843978ae8b58de140c3de2b0415dfdc15cc382188d80bcc036a044125639c0291e2c7ac132a731500b172b4716a36449ac79a4991b78c210cedda563e185262802052ba425ec56c7b5e89f0d6e8d742c690ad1bef88bf12cb2b6fb94af49829392e38551d42828996423233b1fce6fd731dfc44fdd17d0d6d86c06b9a36107cb64b8c8126cf53b98604663ccb801cc886fb332e7aabe8000000000000a4205c0c80000a72d404a997c828080555508e09baae87dd0455a06a095be27a00005be56cc04000624b6f253800038efb33b4a91d98d54f179a109f1e48595c66ccb84cd14b2dfb10d3c1057aa4c5087310c7c48949dd499be857850241846b0fcfb0da258daa0da9e2d0419e1e06b07c861bb094803e8117148722907238f792ea011f6682e2d0007564540ef13a63a7b7590250635e94d0d3ebcd609
  | 6 => 0xf1a0000a88aecc619168867be8ebc1ee745420000430a08f698f03338b72c2009d588b5048e43bba821ae2e182118ac3000017068752028db80002e8eb74f632c654da7e7f4a7b6ca7851cd185227704000056119c371d750f03d80002e5d1b099bc4770b12294c069a0000257122a820789ebd78000050f80000bb5600003c3a621d2f184857c400015001cbbdda0c9c5b20000c007b4520e4cdc553000044e42509aa0b5d07e00000c6e2000000001953c000030099bf0b57b78aa9f08a50bbb43f10a41e1cd3159b0c686e0c1490c2f879a072fe271890ac915524e3065776e4380d0946aeb122a20409ccfe80a64581f39738359e42200001ac0fdcf0adcd17ba000074111604212d2941880001499da493ea062096208f5981aabbf8c92ce1e0f414d3ab5c35d0e0d731423cc459ed6f4853844af515995291555f6694dfc3ce83f8c5a2000009090e7a283f0b0c93df72600f805273ec80edb852ae278436f800022875e6f808f2ad1d80000000000003d0292f5737f8324a80001677200005c2e04014a8460000c3b3a4e1950d4b15542613472b0ce1e14ce87d21c52040d96cb8a4e8d3f9eb4a0000716a291c727f6d5033a23d14e50f23c55e529d991cfb092000052c580002b11e00001c1284e28504537ac99a7b4f2ac405483ec284398a5e7f0784800002c7eea524000033870000145d114a32a9de903f1129e1bb7a5a51d666834817e00001d08671a7104e619ec40180b4a0000faa97ca9e901fb29600006400290dae8ada961f80821052f2baa2d02c4ffa8c000004c44c567b6ca5b3ef1b56800000000281300000887571a3670d5c06ec3e423f80000000031968000000005032c500ab063008d9291161c970961864a9b7c20c14c92c1b0fbd49521c00005029080c00001e3d3315489d5d50c14e268546003e94c9c0001406a0000008d800000000b35ac0d622fb485e2c224198b8d184778d0876800006ea2110f79bfe8c30a77e8873718f6060448c6c02fe39c1c9daec2eb095a93f355e508c20000da0b4ca416530d0eb3932000010981280670a3f9e131040a62359b2f097746d2f4127877d47fca24b30a5eac39113d43e58411cc2a5dba96aa0a338cc6d549c4000046d60000045a28763d1c071f6502f9afdb661b7a37355dc4fca48a6c12db834fa79898a20000514c2286f021fcb4cb1c6e214c02e5f2ead54ae84d974e05b2cf1ac3e56c00008c5b00003919667ad8a2c84a982f600000b021654f0ec652422c95034d51c810032b000000000a69ad43699b9ccde8000138561b96787c5a6edf219536569a33a02ac113d34c38afe64a0c154000011860c600000038063e09c00000000dadaf9c8a2de4e38463bc8e2c5474e000092a2461c00001187b92dc95be52cdd565491f00490490f111046aa44cd67015b75054
  | 7 => 0xddf05a0a15c94a0b421fd4bcacc4689a2a9ac5fe9436c000062bc000008bbe859201c2800000001c547c88eb4b91674e7618e020a1b4827d9f3700219cd0be6a94e49bf91af909c0001e15b78cf1db4f06432633a40e5cf090958a8350000304b5a1fc000068af353c9c562000082a8dc507813a000000004115cc1100000e2b8e1fdc0000946771e74d9b5a8da731a09e9e4508000067b41affd8db400016730a83704da8ea3998b500005968f314aa86cf30b687bc243766808111687bb26bbb63059cfb1a2305754504295252075e750c4b538a05a16c0bd7e81673590487800001047840d00003c32338acdbdc947398450b030417b32056cbc7e703b9b000000cbb1513200000a01649d9b44a51a575ce0f15400008b818000382b151a15a0804224e6c4c01149591d8230368d60ea9116035c45d5d6a5a2fd8040caf7d859f3212dca080000312ae2751156a607db4ed1410d0e8e4a940000f343856ad4b9de70233048000082f995b060e4321ea901a23933c01c05861051d5f94154c46aa50d1e42842fae22800678059a03930d2c97146f109e1659dcdc8443205e38f7f93c541900000909409a9eebe672ea21cd6830165398507643d9c818a8c80000000000000a0da66ed4be3444e7007805e159ba922e5c1e213eb499ed445feb3e67f9000004bd8c72d71acc1bfedf110f42237002732e20422020243c061f026e49d79081120338c0fe590035611fe0c6eb6581101cc09f388aec9a9b26b70e8b04740000000098946c8280000f25a81cf80001c77ca364188cfd0fccc599732141500001cb564354d90d4d23a5088000000007c41c864c369f78e2c1a2ea1a800000000085c8c7bb01b5a83f04499421534a17b92dcfc3a7b478780baed6138842895a6bba078fefc03fd4e4089bdc8f5c39408246882e8b79d100a6c7cb049e1970255549f79f9483b98e33915bfac2e1d38ce9ad04600000000003ab45b718ec299f6048340facae8322d4c3ed808331ff1c0df6c8602d511f500003d10600008893954748e6bb875d17f8468c105a065c2879460992ea894d5924c7e365a383d1062b3ef45c6e45623de0aa395091ad0891b8e9e4685c450c10438b80a55517812097c1522c04f5be26c00006b4f75112228a0834caa980001ac38c20e222a346e5c794a3b772acea21c917c5277b45fc83334cf2120500000a2142e2771dd0276bc384000138b0822ebcd45e16ca4d183f22ddbf10ee00009b50acaeecf81e28f00002e2234b4c52d60ba45107d0194b2320000358fc00000000b165258124c8ab2610000157f40000c7bb2a5f9d2be886d1073d3012cd0b85c355b9c04c8228c0001c6e4eb7779e76470000004b3190a2b2e11a308a1fb80003ee1c769200001cb40e4da8069000000002ed2c000000000000229f5f32873ede8d42c
  | 8 => 0xeae2aa00006d57c403b80e50327822b8cc0e43e40000140bce39be8c7b30f95f082f77e3db30c6c4a7c2599d89188fc20507cbcc867100002d32b0987f1b1218b04cc8c23e0000691c89c036d1ac1d6b33138d2487480000d8bf951aa0587b25190d2f12a0ab97f7fb410f5843d0eba0000943a21e7e235697d06106d9d7c0001446a3a3c8a0523185e3dc7bb1644b1ac8ea45c0000621248a64e4b030ebe19ccc88067f1e02a2e0b8007497c50270011fc2948448bd407592bace1e54add9ae5c83f4d4006ebaa6d341be6c962312b94294098898a90ad6bd029b6ea546469d000045d938904000070e858c1ff0101175000025402ec5cb54ef179bd3136f86000061f1d81de65c2000071e410c7c0000659e789e7080041747469e360f533bec46846f9b948000029fa0531624b34ce906861085b8500c903c101742a217eee2cc2236a3b2926df1e0fc59e86be5b45d5b6f28c428a47b1542261319c25b6f055946f086b901e39146ae11582e0d04fa22700d8a6bdd31c39134e8ebdcc7e031d00002d7a32cd9785fdb01808cf2f1f03d9c81db4240e730b1970c3ba94b8837e00004b22d93b9e568b5e500007ca24268ed5587359f5d840001419dea24a49652f80b27b80ca5d13c0000f68800002d5fc0000b0780c39ca02925d311e0d0a5e52f80001202863d175232eb5cc17bb9230000226411159e4446e333710f00503a42612e20b4905bd4933921d7cf04431cea4ce6258278200006b436198f6663206de0aba4876ad5e65879b41fc09c6f6dd58cc0ef48a8e827674095aeedc6358f1c588500002144ce92e000090626d7558dae000000002d3970933772fabce5137a500604e30bffa8ec1e57bf898511f6813386f5e1c6516700000a118b2fc9996e4f708d99e6da219f820cfcd4b75b71b693816a6393154b393780b9c0e5586c444692dd64a46cd4cfe0009e1b8af08a3823a3a2d72a4e7c25e8e2fd45bd07070444de382d5c74c3b2689cc27bb9f308b60b634c12a81d0a2a03a097bc2c388f700e7d2fa19cb95864eb5e38cb0016156cd882871bfd0cbfd08a6582c2a2000009124caeae27b137b0ccdb8f65d23f000040fd3239644451128c42192738867e1182648f046d80000334b18a313003e185f21f018c689ede57f835d6cd138ea3b5953c21bc820a911218c60154dedee851f5e74132e4164e5a3725fd1ba1821c2c00204b1145cdc0791a1f44c00001c54b0aba0000594650365a0f6269539243d9844a8a0000000048f14516eb31d7177e1fe00000000050a3357e365b0000089d680000422a227a00036c46be89082184127a82300001987e0000195080000e08a0000646bac19a18b4000060753071000007068d80e00000914351ad800006ae816cd634a25974e811f5e0d97599fd04fecb1da746098dacebbe356a38
  | 9 => 0xb000032339618273265d0f3c48167473135000000001637739d881dea6b06e260513eb1b78000000000c028c628000000003b9ecd26c0000000010b03ce24000182e900000000008eb01a80000191672e9e0000989dc8dabadfa741f7a0781b8e24f3d04d2a42800000000261900000000263aa00000000000000001b71c0000284ceb0cc007880fbf52a38b9112688b76dc2780001c638ca0ee138681ff937e19bec195000000000d21a909900062987d00004001401b074ea43b1ed4e7c4ee40bc23ba8635c0001d64e000000001c3bf122d00001857f49bee7870000000000000276bc31a1d2700000d6e3d206a97c7667cd3ee3342c108227e8915c5b4c000013045918c70375076800000000294d0d007ac7c00dcb38ec0bd5cde0101d1a47c1a356a5018bf4139956d950a6265882b391e8c00000000108ced8596fbf76b8d01e89b62501200000000581034a1545f35a73204af6024948122e280000e9b80000b44900000261745a8125f460560fa3109df8c8800006a37572148b300000429fb4d9b423389c6e9800000c81acc6524f1485b80a0c0000188aa8096d1af7d29c0001c6e7685cb83d8e44e00002c6a71f382ef5b6fac2ac2c2e0000987c7a9250000000000000b244245a5e5eb240200001c7d2409ef2ce10b48134a62ce006300002d00000000000000025d6a0b2be203309b00000000000000c4aecfa80001f0b50000087e38ccf4712000000001edaf33c34b28945e70aa000000000000000000b52650a68911c87e20000000071b3d6022000013aaf5da2041e14400a03003dd4068000052d7ccdf06cff76335b7a80002a32d7226734119dccaaadd2b70000380940001c84831dee81624e8c00004ab074f908e472039c006b97b0e97b94db330968a6f67d236ae7074656c7e60f261733f720540f05a00003898f9f73e9bbc794ea1940058e3a0347753d34d2472f4ea21000004df9c000027cbb87669a0f4a9cc610c1d6a91580000411a00004191d851d02a7921d30bb36dcfa5bb61cdd40da0192c50ce1a8bdc428f9f867c1438fc9d7a4a92598b2b780001651ec89b5b3a92061206866659c33bd8896f2d97923c1dedf8a22d806578b204127b429453e3a3d7de2e9496503aa5921000027009a166c2926d573435df4b692518dbc1053ce42e6a7a141e6489667c5b00130c3946b272f0d2c318523622186d4db1e5cd682b79643c02a49c2f141fb105ce1a918d2c3037f14ac3f55dd6325434060f29fc52e8000184511bb198fb66bb1516dfb457a02f47d000000000486700000000099440ccf0e6568410f90a344bd50980000d3858973c00014432106ec40b1002400000000358840001b062519d2c93ea3d9b6c8a2b8000008ad28639b87fc99d44a0401f5000000001cf71733500003946aefa800000000616f22f
  | 10 => 0xbc6c5eb0d000018e7f0419e390bccbe4d3884a08329d47213025646bda1344ddc000133d0697994afa2fcd6123528da4ec1e3b6509a5b29d9644e194856edab11c9f523c4000072189970cb19e26929a9971b1b2c0478ca29cf002b9433066f3bba1fd598c7280000e9b235d24af1d61dca954fa1af29a48474f4412473c00002852f9a365b6023500000a2af800000000537b93bc5dc580000e6d051e16e27d054ca519c20ed435a62d4f15d00003992b424112b1301ad003acd96f31f42b18000000019544d9418da17e9261568da8d51c06f05473b79a2c59d10267054c100000000231ab12020c3e09fb3882d411600007c64ba50e0000000000000000000000317d87ab66dc000000002144aa11cd22ee9f418b240001423579e3806bc000127bfeaf829ce80000533b815c45b40262d619bc0a005dc52ace82a013020ce076c7400004b438000267bff05131fecc1560f7468c6000021966c9020418000064453afad45d600000537e0655b368b8db780300001775b6160fcc5f274390d14bef082380000000000000000000002605000000000000000003aa680001869e353fb2ae00003511a000062b6bc71d6c9f1186d91008faeacc0b669545e30b0ae246c76400000000061a14538491d2c56a63f3119dead4603f8000000002c0ef5ad84bbc2395015654ea824e0b10e0a4900002679e28251866ec5340001a3bb7c0a39ab80001a07900007cf49668ac0489aedfd174000132bfd16e000000001b1a700002444ca9a2c0e7e9307c20c000106ab9931512ed8838366f1ba500c9cc681c12400001c44ae223b0800000721b8c7bfb3b2d41c88d0848a57730e99b852a400000000a3777c24408760000b901a1f25027fc7acb05280a23503e8462d08014c28ee4160330000000000001c4dde0de0000169de85d1d98f54db0000110080c04d1948e17d57d2c1725ca7b60c883ee6322796bae0bec479b313ba224000172ef9bedad7340000c4392b78800000349e34e00006c3eee4d2574eea361da4fe887e51ea30780e86c532437cf169ce01c8bcb53f7b8fb0000364aa0000000000000000000000000000028dfdf45b00000000000000000ab5a79fbc2cf290a85239607ae4a1e00001bbaa5991cbfd13c9cbfe54ea465888725b8664955941c6783cb1704d687472268a103f6cc696a03c14077ab4da116cd2253fdb2fa0000000019871e1f390e82e0fa00000bdae0baccf1f821591ba80002e729e32e62942c66800000000029ed8c06847000005a66f100cea097198f37aa592165ae0588bb62000038389d639c0e2ae1abaf45305be198bd9d882b32072d321800000001b53a000039dd90d46388d2131b4b724acc0000b3a67cb3d6fe12293ab2e25cc7cdc487d8098618588494c0000d843edb3b2e89d765e29e581bfe4cbd1ed239
  | 11 => 0x1f5a94339062688a06f7cc9c4608a1c0126a05dab61fd788ec18448549ba088a94a4ab34ee1d2993e42e472533dbc449ac70ae887963805c83a4000023d04458f0e374f20f72d1aeb517ddd0f2c0c7a3b2f886e85f53151ebc02037c000087fb00006011250bac89d0113f51efcdcab79f000074db7e1280000b1f4ca0f245f01188cab180001448fd17e7ac524105e35a542d7137017362f7170f60000213a400000000ea35f9d840000000040d9a225d06fa5631543fe8b6f468e16125aade5e428568e6a6304fca0dd2ada0000c8868cff25165b7e5b143198ed63e60000f156e07c0ad5074610000000000001d0ab000035894f0f40000c25cf18f80001e106000028187a39800007a328000024b0d466fc190000043320000b86cb9ef2d0c473131c3a061556f9c00000000792ab06c143140c1854e4c00001153ec2c8000226f0c71e0000617fc03977658a17e00002a33e0000000000000c4cc22394c559d496a3ad454d82a585d342f9fa1016a888d7984cbd68a920549023cc42d801ee399b6187aa7045e4701fd0abd8906f89e328b687b402eb75711adf70385a03613bef8f8f1ba22bafd43488601caf322fb568e7b3c0574e216fb35b000000001245e0000d2d0c589110b5401ce98e000000000c6e1000000000ea6194310000093efabea000000002d8046ba4c3c1429d69afcd0a3c3d77af1d908f0d7200004aee3538e849dd87999f0000036a9852b079f9f85daee9968a27432761afabe42317000069b44e771036f924a116abc9de353d741f9d32de51a0000ba31acfc54dd2432cd99379dfc00000000d26300003671d54ab2ada560fee5bd8596f3c000003e745c60b903d645970ac5e73200006dc6c0001a7d68894c9142056f80b1d1e188798670532d9db89000012ab2231bf3a9f23178b07982308630815fc9f1277e2a39591948b6667b7d3a42da53e2700023e88465237900325b4d1fb50c1aa759575c58737da3c832b712d446cf9d25c3f2000010d0398b50e8aa2048397b5bf86987e668498830fe0e9d98068613f11875485e0000231218023b0a200009a230d01785add6fb6a9205c680000f7ef84477836cf1000000e8df50bd00001b543800829342ec3681fa903e2d73a88346135210285a6a2aed112003d82c15043b
  | _ => 0

def or04data12 : Nat → Nat
  | 0 => 0xffff5a3bffd68f7feca3fffd28efff4a3dffae8fffe3a3fbf6e8ffff2a3fffc88ffff0a3dff9e8fffd8a3fbf4a8f7fe6a3fff7a8ffedea3fffba8f7ff68b9ffda2ffff58bbffd62f7fec8bfffd22efff48bdffae2fffe38bfffce2efff38bdffaa2fffe28bfff6e2ffff28bff7622f7fe68bfff7a2ffede8bfff462fffee8bdff8f2f7fe2cbdff6f2f7fdfcbdff632f7fd2cbdff7b2f7fde4bdff5f2f7fd1cbdff172f7ff6bb9ffdaef7fecbbfffd2ef7febbbfff8eeffff3bbfbfccefbfe2bbfff6eeffff2bbfffc8ef7fe9bbfffc2ef7fe7bbfff7eefffd8bbfff4aefffefbbfffbcef7fe6bbfff7aefbfdebbfff5eefffd1bbfff32efffc5bbdff96ee7ff6babffd2eadff4badffaeeafff2badffa6eafbf1babffc2eb7fe7bafff62eaffefbadff9aebffd7bafff32ebffcc3afff16ea7ff6adfffd6b6fff5adfffd4b77fecadf7f8eb7fff3addffaab7ffe2adf7f6eb7fff2addffa6b7ffd4adfffc2b77fe7adfff7eb7ffd2adfffbeb77fe6adfff7ab7dfd7adfff46b7ffccadfff16b77fe5adfff76b67ff6a1bffd6877feca1bffd2877feba1fff8e877fe9a1fff6a877fe7a1fff7e87ffd8a1dff9a87ffdea1fff5e87efd1a1fff3287ffcc21fff1687ff5da1dffda5e7ff697fffce5efff397dffaa5fffdb97fefc65ffff097dff9e5fffd297fffbe5fffef17dff9a5fffde97fff785fffd797fff465fffc597dff965fffdd97ffd765fffd697ffd5a5e7ff696befc65afff096dff9e5affef96dff9a5bffde96fff785bffc596defb23ffbe38fdefaa3ffbe28ffef6e3efbf28ffef6a3ffbd48ffef7e3ffbd88ffef4a3f7be68ffef7a3ffbde0ffef5e3ffbd18ffef323ffbcc0ffef163ffbdd8ffef5a3ffbcb8fdffda267ff689fffd626fff589fffd4277fec89fffd226fff489dffae27ffe389fffce26fff389dffaa27ffe289fff6e27fff289bffca27fff209dffa627ffda89fff5227fbce89ff74a27ffef89fffbc277fe689fff7a27ffde09fff5e27ffd189fff3227ffcc09ff716277fe589fff7627ff5d89fff5a27ffcb89fef1e27fb4789dffda167ff685fffd616fff585fffd4177fec85fffd216fff485dffae17ffe385fffce16fff385dffaa17ffe285fff6e17fff285bffca17fff205dffa617ffe185fff6a17ffd485fef3a17fff085bffc2177fe785fff7e17ffd885fff4a17ffcd85dff9a17ffde85fff4617fed185fff3217ffc585dff9617ffdd85fff5a17ff5685fff2e17fbc785fff1217ff44859ffda12fff584affd6137fec84b7fd212eff384bffca12f7f284dffa613ffe184fff8412fbf184fef3a12fff084bf7c2137fe784fff7e13ffcd84bfeb613ffb387ffe6e1fffaf87dfe9a1fff9e87ffe781fff9787ffe461fffae87ffe761fff9d07ffe5a1fff9087ffe2e1fff8b07fee1e1ffd8487ffe0a1fff8207
  | 1 => 0xa56ced9701c8a2cb20c7360f54ab9d450026cbd96006a600883005003008d9753165b4a8770501100700d01965ecb29852a88c1ec2d45b0aa14228026034060110ee0014c6950ee18e15228018e743a01101c0008729832fa55cec2d45b0a1140110181c43010d0000354c196d2a1de16a2d8540380639d05209008800531a541400e01802401d9d03a034a01970c0a56142280260360620c0220240019d32fa540699632fa54a069832e50086996d2b0310659d73a0a40890e012040cbe950ef0aa1400c012a60cbe950b56741682801c0310614432c15c0842d8508a086c0c418040cb996022038cb9962880474c19602251087197d2b675cec2d45a0400740c4180001419602367416828418018a2196020e743bc2d45b0a11400c01200001a9832c044cb011b2ea634a81032e658060280184342d19632e0402d19632e0400180101801d06596b2e0402d19632e0402d19632e0401800c0020a42d19632e0402d19632e0411400c008832cb59702083014d96b2f0400840c4180108710d00e040cb9960188a00620cb2d65c0800c32e6580805a0b4658cb8100b40100080701802acb5970200280080c0b565acbc1021a0281480c0b565acbc100b4658cb8100ee1702d03805a0a008025034a640380c736e5dcb40c931255ce0770700d4150280380680801692ae5c0380c131a65cb80c0500400642373ae5e064980181700e40c72ee742d39bd3308e0649872e0a1cec23532e5dcb40c9301dc2e05a0700b41502802c01c07c950340d4062990b40a1cee9a020e5a064980350300600772c1dc080777370314d39772d2600d49573ba680b40c931255cb0770b40320639b72d26003c9501903003c9872ce6c08095534e580600cd34e5a4a877050041cbb968192620600c0b401dcb39702178156b359106eecc9ca7a89c6564141c60003490e75248739ca92ad25819494a1ae6a5452a5044246a3a8a843069434c9321ae42d651aca83a46a4b509521a931d254a1aa4a92b6254d4b4cc631243990b2316e4bcea23147499ad41104421042a52748d253910b43543528c76b50d7386d719a66a544525295246a429281992341d854294a321ad495ae421cd5250a3106849d0631ca921ce43210849127329073a1296956b2a94a53d49525c95152869cc93260843dc82a1665ad245954a3346a4b4694a14b591ad43528431ae7b58c29969528a7621a521c8821104394e4314893a08c3b4883990e49d2749c8439e7ff6b7dff6f3e7ff6a5fffd697fff4a5bffd2977feba5dbfaa97fff2a5fffbe97ffeea5dffd5377fdbcddffc9377fd8cddff4b377fee4ddffdaf67ff6bdfffcef77feabdfff6ef7fff0bddff9ef7ffd2bddff9af7ffeebdfffb8f67ff6bcbffc2f37fe7bcbffbaf27ff6afdffb2bf7feaaffff8abf7fe7aff7f62bfffd2af9ffda8
  | 2 => 0x7a0080600953165acdc1012d269ced96018e7406b9b820269cbd968192544b49a01a0300649a82065a0649573ae5e0810d32d0324ab9c12ae6ecb00c72f042cb40c92ae6dceb97820435cdc0c32d255ceb970512564d077b2c031ceb9b92ae5c3a09ab2c031ceb970500424d07121a6580609672f6580602801a031cec1072f65a064950190400340c72f255ceb9b82165a0649572ee74a0028019041cb90d92b030cb39d134e6e08397b2d0324ac10018018a040c72e0a1ce82892a169cbd960180a00cb9781843403196020e75cbb9b8180184d14432c041ceb97018006060067366580829bd342002b84601e03405044b2c20c2180c01a03b4d5960196583b85a4500340669a32da542e0110540a00e80d018e774d01193165b4a803018121ce80f536262cbd9605000f4d04873a0303b85a450032cb6950b84394d0110600a00629a32e0464c59621da56cea9b0900b40680345b6590700c53420c2d42a45004c0680c02203d0708a21d2634a8770b48a00980cd341702490d0220c01401d019a68cb49821ba554dd9712c0a814048007a680600d1010a00880cb2f260cb39dd2a1dc2d05745004407a0e21a03443c9821c65b4a8770b48a00669ab2da542e01106007406228023a6814c98b2da540180c090e6c07d9db2e0a006848007659cd80c3210a88700c023261cde950ee1691682902203c0659706a4364c196d2b676cb84852b659cd80c01a1c74d10d32da543ba28018026cb05c006e5c088100060302439701f6754d82801a00ecb3970120301842d45b0aa1422803a04c0680c01404407809931a5406002022019cbb9dd2a1688700cb3a11808c9872fa543b84385a8b61422802203c060092804364c196d2a1dc09a0e0196754d1970520440780921d2634ac2a0040440605a00ce5d1401072f6582d695b3a0a2cb80f020118cb00c0b48b61422821a032cb8109306580880dd34045cec98d2b6743b85a4500300810e535260cb011b3a1dc2d22d00365c0800c93065808d9d05165c0c80f00c030cb01052aa68cb00c0c618006003b2f6580700d000a542b80e01b65ecb00c32c1011401001a0274c59773a0441502801a031cee9802365ecb69507e00c0014473a0f6cb0400600a00680c01c00d0659773aa541e80e2880474c030050032cb19702251087695b3a0f41680d006832cb29501d0a91401301c0360620c1140440010e32fa5406940023a601802801965ccb14021ba541e82a05003801a0cb2ea5406c2d85004406c0c32ce774a8570224388680d81865ccb695738e76cb84045004007009d3065ecb0110600b51400e0180474c59705365b4a9442808a01ed9d7360a00720c01a00c06597b2ca551403d85a8b61501301c0360620c05204401000d2a6421500e818044cbb9bd2ae7616a2d0520440700d8188301a80032d
  | 3 => 0xd0208a0060080066410659d020a680819d0180334d1960ee0400780108802806007b2c1dc0810e0140040000c5356583bc100ee0b41400c288674080440060040d00c00e026ce810b3a5120820e21c83004a9a052022cec10004510a041000e0680080c0136583bc1001b6580600e32c1100800dd30e740890e0540a00e80d018e774c011b2c43b4a84b0620410600e288e740d5960c20c006d9b52b65c2200e73b2690601a33a65d1400d73a0434c59621da540895521c1841401a01d2682220cb2ea5406d978510388700d819268cb69573a8a08695521c65b4ab9d0880434c59602243aced970c20314a84401a8a2cb10e034830cdb9db2e0d40d00e01b0310610e21a66ccb69573a65c22010b2ca600890e0ee032cda95088036cb80e93565911a980352682d42a85004c0880d0190394c01a0ee43b4ab9d0b50a00d40e0181c486c9a01aa6087196d2a044a210eb3a1841401d01811006a95b2c65d0610e0341141842a8500680880e01b0310601321c65f4ae9828965887197d2ae74a042803403806c0c4184388699732da54168118196774a90e73a1dc22c2a8500680880c0b4a6087197d2b676cb81ab36830cb49a086042cbc2821b0310601021d268cb01101da680680c05007406158d346774c10d32da54280490800334d29533a832cb0300500748680c2aa658876950a01242020c01a8b54aa0eb2c5011420e21c0350619d535a56cb59d09210006b9b52a8a10659673765b4a85008003111d9dd34a6106295b2c50116a280186754c596d2a5011420e21c4340629a53165b4a850092032ce84272ea550659645a8a006a0c0846774ad9672fa56cb698280e5c86996d2a8388710d418a6821029b2da55cb9404508b51410d0181094c596d2ba6b4c01121a674cb69553023c2b846d3403806d9641824821a9501c036cdd96019a6b4c3970a0035ce8290220c21401d019a6814e9832c4374aa98b2e0a807007002832cda9501a15c0890e21a0360619b32ce734aa9ab2c8300400652ae774d397b2da554c0290221dc2d0230020380680c52b66ecb22353001dce85a85ae5c3882921a0300080d53065b4ab9d53403b4c596d2ae5c1481102000403b9709b676cda9803a03806a0c002032cb39752a01c1842d45b0a81481d02603806c0c41804400e950530300880800ce774ab9701d032ce84602266dcbe9573a10e16a2d01c0360620c2800a40090d32da543bc2d45b0a81480e73a0440629800216b4ad9db2e1180700c002832cd99602004086c0c41965dcb82832c044ce80d051a61ce811b37a56ceb9d01d0310639702066ccb011d306580890e337a540819b32c030cd9960180c00e80c01ea60cb19b0200f40600200003d4c596b360434c030018000cb19b02000c01086018026cb59b02083005809b2d66e08010006438868020
  | 4 => 0xeb2e030068400548a004e98b2e0ac868280200334c19db2e4374a85a0600a00800c0800394a90db2e830ce82b2d2434180280204380616932e4374a85a9321010659db2ca540708a2808a20800e01b0310610e21a674cbe952d2438cb90d339a56cb8400548a007009d3065c869970be034b4a282801001522801365d4c02b21a0a00659d5301000700d93365ecb22352a17c3b9404510420680c0e803a4c90e21aa60cbe9533a1c60800cb2ea6086e950500740800e0b4502cea9532e0264cc284510408680d8188300499733ba574c19721a6774a82b2804344006b08a1100700408020c2105a01803806e99b2e03116a2a450840060090b5a5414010018e764c597d2a1681401001c00e2d59773a030066952c20c014010019a64cbc982c243b4ad9d05a040020038b5a640600e1070a9152288208400608a0b443a4c197d2a1dd16a284200310685ad2a0c1150280200324c59721ba562d02a0500380200345565d0680c1010b61410d019261cee950ee1ad1421021c0302d03941b26086997d2a1dd1521001c030049970b5a54076992c2438cbe9501c0102004232e168064984548a10800c01265f4a85a0b465dcec98d2a1dd142100180254c997d2a1683ba2d4548a0060090b5a55ce86e0c20400700d820e6dcbc95b2ca6a0608b0e21000669a92a65a0840c73ae5c3080e21b254cb410818e71ceb9705004002804d349decb00c73a1dd3a061736a69cbd96018e75cb88b0800a008271d34434cb00cb2c0a00800d0180380249573ae5e0840c01800c0149500d0420639d72ee6c3705a01d65a4a846821031cbb9d0b41001441001803a0619672e4364a84373a0a00800e008969cbd96019a684888d1041dc2c00c0896588684652a02c4b00eb3ba6acb00c12223418028b2e1dc2208221a02ccea95b2c8a00820e21c43405e9832c035cb811b3b264468770800310600d45b6594aa0e72e8a086e9821c02d4d19dd2a658069580224374d011d30674cb695d35a60ac10d32da55cba2841c43906087d2a4374d5964500408680bd30e5ccb00d022675cda2821b266cb877080032ce80d736a56cb228419a6acb22802043405b9732c0354c0119322342d040050032ce80d447a6906298b2ca542d42d85003005a9833ba543ba9a72e8a009c0d0192644101141c1d08710d531a551400c72e1c54c69521b6591401021a02f4c19601ae5c0881072fa5486c9911a1dc1401d01967406b9752b6590622d8508a34c01121a02ccb99dd2a65c06810d30e5ecb69521d03486c0c93211808b97d2a8b415228419a5486c2d02683a06c0c418a6a4c82902243886e9585a8b6142280270340649902216886a98d2a0a00659721a83023196021a680819d0180a00ea9a01c1dc8719d0200383b99d020038008000191dd0759d0201dc1681d0180a4c819
  | 5 => 0x300700d846035cdb97930e5a4ac0c73803b4d00c01a16916a280460ac3890d0b48a011a0e0561c4868308540a00e8100192608690ed2a22c2047105b266ced9641c0304ae9a018034ce85a45a08c1587121a18116a280460ac3890d0b48b5140230561c486d9710c031ce81d73a185cb00d21d254cbc0c7380d40380c736075ce8770c2110140102c3a648719701822c1439d0e2a65cb5970c00300d007018e580e8910d618c3004508403005e9953003806d9711ca540489801c036ced970188a91421001a02f4c5970124374a86d0540a00700441965d4a80d0d64388680d818674cbe957388a10800bd3365d4c009d2a0a0118100080380680c531676cba2352a02a16a2d8508a00ea100181c43000d21aa60cee950c01081401d0200380600401b674cb80952aa651400d017a62cbb96013a54ce86f03403c0500132e025cb21001c034ce997018030cbe9533a1681e80c0040000e295b2f6742d05a0500300880033a65f4a80dd320380605a080032cda9573a832cb86e0b41010600e454a5506d9773b65f4a86e08003111d9bd32a5506298b2e0334c961530438cbe9573a8408720d21a0314ca98b2fa544b
  | _ => 0

def or04hash12 : Nat → Nat
  | 0 => 0x19f0ced1dc04b4f00000208e48f4da209643522e4000eb59c74a2c8000151f9350002d080a064ff00038e9727a6a4a93982c38c2cc100010bce85eaea0002c6a419c80389300001540d0e0002e39d03404ec06447eeacf529d83dc5e4d01c49c14d6fa18e1af8ed5c00000ab882029920b28280004d650eb2cc1cb602e38bd98dc0ce628f306e1c032bf29ca36dbe6924cb844cca3820c53b6215adc2aed5fc39cca73016fbd0387097b772684b340006c7db1473200ed6ac015ee3f548e1545c86717e34700000000916040ab1b88fc8a3c42a9e800004fdb0d0000ec2921de7b052154509f0000c9d22e6ccc6e887264cef7b6be2f0000000d4b40007403143e20c0000002cae2d4c0000cb0000c86749c00038c3000000069bc0000002f15c840000e5000002d28000b51b4510000000a33c000b800f3d00027494afc00000002534c616140000000eaac000d42c8fb0000000e8a8a2100000267188e5b4c5caac000169b02e80000001847c911a8559dc000d34f40f90e491f14816e4cbf926d6d6f29972deb36156ce6e80620b15acac249af8944b5658a50001ae3a9c16bdb94430f7181e260001ed4a282e5684a8000d0c4000da42b2e686be020000737e88df1074d9105c1d40008217884da0a72f910c06b19e4c61180c25dbad5a1e0001adc6a509020002e894882917f1f4c44742893d0ce026c0002c644ca9009a1cf83d2550edf0b88000426ae42a462b0359874fc93e3f3b435b8578c5909f0000d116920000e9c58e5252f35811175121497c7173d94c700028df4c90f54f2f8a4300026a595279576290a760bc6a401d3928051f22bc352b6fcaa81479000307200b627d788bc236bfdd030002cf934c4000b350000da1283c02a893a00020e6041b096d371c040003326ebcb683f12d75a9bb2a5a103054c00020c430be63ff0f8216b2d40f38072215c3d6c5d7c9e00aa925cec9104000d4ce914d0a5263e0aeb12ec12802cc76b023081a6bf4c0000000000093555520003ee00002e1339fe0ab22040000001b33c9400009b4dc9de149c780001a59000000061648686c88000e9e021868a4c9130d3d3b4b44000a9970140003b4f9bf7d2ef04cb28bad1c500002755b021c8bf5094a9c8b0ce752ff541d3a0a93354f021b02c00078f0e2b9a7246f8c71938a37ba4b6b0ecc603061d0209a91604089c1110430b5919730d122b080d0303060f2a1e65101e0f0400f52f233d3a2001060e044001010a01040107000a1587001b010023006707188701250410140b3708021dc60003011b083a133e1c37050100171c0500220000001a44005d070f051000061b017706000703050a000f0200000d4f3427540d15030a00940900000c091621030d0000006213090b0f0007001a05050905000600053d050a01001e135b00010127090a
  | 1 => 0xf11a2cf41732675cf04d00a680adece46730c8f6d2b1bb28f0001811224a0fa3c4f687b9076eb000020c441c41af95ccf2dc2052629d441e1486e279d09a86b20286c03bbf115077cf499502e8632ee06e25020952ef6d793dc91a300670b191fce35c85466d4d3000695400044c8720c0fe0364367127d09eb052d5848c9b2e8d7a573c8d2bd4000a8e800000036e964f184f3b22c0781b7201c227d5f4a368b364ac810741352254f9560c893897dc6d0285bdf2e77162c953d71eb7f26c90f7375ac12558ab1612264fa0decdb5ceb6f6253685b7229b5f387c416c137c4c68f505432b2b4868d28057d498a188cc7358ae4c90000089394314557ad80000002232f0cb07b781f8e20c0602258b58c23054000a55694e9bb411311951104346c76c98363b3a75aa30a307000b104b414780d2a2a3a7218d7e3111fcc3b91df49833c7830eb946b8884b2cc291ae5294358e1b1eba628222a66f18fd010003d2fa168ef0f390e2e4b6761c0000ecafa988cd65740eaab1f69f44dd1391a7a65809ab2f464b204a7bb8ec9b0188feb585cd8606dd15f0eb46902c325e5cf86640159558cbccd1b4ccbf5e558be4a628ab431b6fac5732451982be225c97d8175cb7341397124d6c302ba80e32ceac1f360d4735286a2ea7ebc7aa8eb45a90978740007b01b1a9ca514f000181ffab402e00033
  | _ => 0

def or04data13 : Nat → Nat
  | 0 => 0x2749b260972580ca682a2540d66e9865d96672952749b25c9608e9a26095a640c65c280359da6996264981c6952749b26096a649565c0c0a010a619d65e951699da559766e99a6197a54280359da609965d96a559d0a010a65972605aa549d26c9825e9a255960400c265970a00d6769aa6196a569a1dd9d0419d0399ba619726996a559da6a9865a9567597a619b65a95a619666c10268106580c2559d65c28a689865a9567428a619765a951699665c10a6a992600c254014652906215084a4882988539885bff57ffb7bff3fffa5bff37ffbdffef3ffafffe8fff8bbff2fffbbffeebffadffe87ff97ffe5bf78fffe27ff85ffe13ff07
  | _ => 0

def or04hash13 : Nat → Nat
  | 0 => 0x321bc8900008074f8f61b8dba8a3002eca2b94000c3d8928e08a4b2c4132391b31cec1ec96b76700115410c564a2b6a4001bbf50013120000000899940308e0a0000000020
  | _ => 0

def or04data14 : Nat → Nat
  | 0 => 0x134994c25413ff
  | _ => 0

def or04hash14 : Nat → Nat
  | 0 => 0x700
  | _ => 0

def or04levels : Nat → Packing
  | 8 => (3,7,8,0,0,1,0,or04data8)
  | 9 => (161,6,8,0,0,7,0,or04data9)
  | 10 => (1472,5,8,0,0,12,0,or04data10)
  | 11 => (2268,4,8,0,0,14,0,or04data11)
  | 12 => (355,3,8,0,0,12,0,or04data12)
  | 13 => (22,2,8,0,0,8,0,or04data13)
  | 14 => (1,1,8,0,0,3,0,or04data14)
  | _ => emptyPacking

def or04index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 5 6 1 7 2 1 or04hash8
  | 10 => lookupWord 81 360 8 13 8 1 or04hash9
  | 11 => lookupWord 724 3317 9 16 11 1 or04hash10
  | 12 => lookupWord 1123 5098 9 17 12 1 or04hash11
  | 13 => lookupWord 176 770 8 14 9 1 or04hash12
  | 14 => lookupWord 24 43 5 10 5 1 or04hash13
  | 15 => lookupWord 1 2 1 5 0 1 or04hash14
  | _ => fun _ => none

def or04samples : List (Bits × Bits) := [(0xfff000000fff000000000000000000fff000fff000000fff000000000000000000fff000fff000000fff000000000000000000fff000fff000000fff000000000000000000fff000fff000000fff000000000000000000fff000fff000000fff,0x544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544544),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff,0x823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823823),(0xffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000,0x314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314314),(0xfff000000000000fff000000000000fff000fff000000000000fff000000000000fff000fff000000000000fff000000000000fff000fff000000000000fff000000000000fff000fff000000000000fff000000000000fff000fff000000,0x69069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069069),(0xfff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000,0xa92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000fff000000000000000000fff000fff000000fff000000000000000000fff000fff000000fff000000000000000000fff000fff000000fff000000000000000000fff000fff000000fff000000000000000,0x1b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000000fff000000000000000000fff000000000000fff000000000000000000fff000000000000fff000000000000000000fff000000000000fff000000000000000000fff000000000000fff000000000000000000,0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000000000000ffffff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xfffffffff000000000000000000000000000fffffffff000000000000000000000000000fffffffff000000000000000000000000000fffffffff000000000000000000000000000fffffffff000000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00)]

def or04forest : Forest := ⟨511,14,fun j => or04samples[j]?.getD (0,0),.leaf or04columns.toList,#[[],[81,130,118]],or04levels,or04index⟩

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

theorem or04_column_list : or04columns.toList = (List.range 158).map column04 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04_geometry : graphValid or04forest (boundsBefore or04allknown) = true := by
  simp only [graphValid, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel
  · change or04columns.toList.all (fun c => colCheck 511 c (boundsBefore or04allknown)) = true
    rw [or04_column_list, List.all_map]
    apply List.all_eq_true.mpr
    intro i hi
    exact column04Checked i (List.mem_range.mp hi)
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem or04_root : monoIndexedRoot or04forest 14 0 (inputs ++ [seed04]) = true := by
  decide +kernel

theorem or04_target : targetOf or04forest = graph := column04_graph

theorem anchored_excluded (checked : monoCheckedTables or04forest 14) :
    MonoImpossible graph 14 (inputs ++ [seed04]).toFinset := by
  have h := monoRoot_index (g := or04forest) (top := 14)
    (prior := boundsBefore or04allknown) (k := 14) (i := 0) (ws := inputs ++ [seed04])
    or04prior_sound or04_geometry checked (by decide) or04_root
  simpa only [or04_target] using h

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

def monoCheckAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  monoEvalMove c op a b (movedDecor op a b) ka kb

def monoBatchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,_,cov) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let mask := fullMarks r
      (takePacked cov (packedColumn true a) (packedColumn true b') un ka kb |||
        packedColumn true z)
    onMarks (fun c => monoCheckAt c i j op ka kb) mask xs

theorem monoBatchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : monoBatchMove (makeBatch k n xs) xs i j op ka kb=true) :
    monoCheckAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  by_cases small : len>k
  · simp only [monoCheckAt,monoEvalMove,budget,arity]
    change (if len>k then true else _) = true
    rw [if_pos small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn true a) (packedColumn true b) (op==2) ka kb |||
        packedColumn true (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] true (op==2) ka kb op i j = BitVec.allOnes 768
    · apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · simp only [monoCheckAt,monoEvalMove,budget,arity]
      change (if len>k then true else _) = true
      rw [if_neg small]
      change (if combField xs[q] true (op==2) ka kb op i j != BitVec.allOnes 768 then true else _) = true
      rw [if_pos (bne_iff_ne.mpr hit)]

def monoBatchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := monoBatchMove b xs i j op
  f false false && f true false && f false true && f true true

def monoBatchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  js.all (fun j => monoBatchPair b xs i j 0 && monoBatchPair b xs i j 1)

def monoBatchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => monoBatchRow b xs i js && monoBatchRows b xs js

theorem monoBatchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : monoBatchRows (makeBatch k n xs) xs js=true) :
    monoTestAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [monoBatchRows,Bool.and_eq_true,monoBatchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,monoTestAll,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @monoBatchMove_at k n xs
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1 j hj
    have opCheck (d : Bool)
        (pass : monoBatchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        monoTestPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [monoBatchPair,Bool.and_eq_true] at pass
      simp only [monoTestPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,
        check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,
        check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def monoRunBatch (k n : Nat) (xs : List NodeContext) :=
  monoBatchRows (makeBatch k n xs) xs (List.range n)

theorem monoRunBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : monoRunBatch k n xs=true) : monoTestAll xs[q] xs[q].2.2.1=true := by
  have all := monoBatchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def monoContextOf (g : Forest) (k i : Nat) : NodeContext :=
  let (num,depth,cw,_,_,offw,_,data) := g.levels k
  let (ops,bank,ws) := monoReadNode g k i
  let start := num*(monoStoredLen depth+(wiresOf g).length+depth)
  let nr := packedAt data (start+5*i) 5
  let countsBase := start+5*num
  let before := packedAt data (countsBase+(i/32)*offw) offw +
    monoCountBefore data start (32*(i/32)) (i % 32)
  let st := countsBase+((num+31)/32)*offw+before*(cw+depth)
  let rules := (getPairs data cw depth nr st).filterMap
    (fun (a,b) => monoBuildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (monoLinkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)

theorem mono_from_context (g : Forest) (k i : Nat) :
    monoNodeVerified g k i = (prelim (targetOf g) (monoContextOf g k i) &&
      (if k=0 then true else monoTestAll (monoContextOf g k i) (monoContextOf g k i).2.2.1)) := rfl

def monoBatchContexts (g : Forest) (k : Nat) (indices : List Nat) : List NodeContext :=
  indices.map (monoContextOf g k)

def monoBatchHeader (g : Forest) (k ar : Nat) (indices : List Nat) :=
  (monoBatchContexts g k indices).all (fun c => c.2.1==ar && prelim (targetOf g) c)

def monoBatchCheck (g : Forest) (k ar : Nat) (indices : List Nat) :=
  monoBatchHeader g k ar indices && monoRunBatch k ar (monoBatchContexts g k indices)

theorem monoBatchCheck_at {g k ar indices} (pass : monoBatchCheck g k ar indices = true)
    {i : Nat} (hi : i ∈ indices) : monoNodeVerified g k i = true := by
  simp only [monoBatchCheck,Bool.and_eq_true] at pass
  let xs := monoBatchContexts g k indices
  have hm : monoContextOf g k i ∈ xs := List.mem_map_of_mem hi
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp pass.1 _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [mono_from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ monoRunBatch_at hq hb ha hn pass.2

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

def checkedIndexMask : List Nat → Nat
  | [] => 0
  | i::xs => 2^i ||| checkedIndexMask xs

lemma checkedIndexMask_mem (xs : List Nat) (i : Nat) :
    (checkedIndexMask xs).testBit i = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [checkedIndexMask]
  | cons a xs ih =>
    simp only [checkedIndexMask,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,
      decide_eq_true_eq,ih,List.mem_cons]
    simp only [eq_comm]

lemma monoMakeBlock {g k start n}
    (h : ∀ (i : Nat), start ≤ i → i < start+n → monoNodeVerified g k i = true) :
    monoBlock g k start n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [monoBlock,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i lo hi => h i lo (by omega))⟩

lemma checkedByMask {g k} (xs : List Nat)
    (good : ∀ i ∈ xs, monoNodeVerified g k i = true)
    (cover : checkedIndexMask xs = 2^((g.levels k).1)-1) :
    monoBlock g k 0 (g.levels k).1 = true := by
  apply monoMakeBlock
  intro i lo hi
  apply good
  apply (checkedIndexMask_mem xs i).mp
  rw [cover,Nat.testBit_two_pow_sub_one]
  simp only [Nat.zero_add] at hi
  exact decide_eq_true hi

lemma checkedListAppend {g k} {xs ys : List Nat}
    (hx : ∀ i ∈ xs, monoNodeVerified g k i = true)
    (hy : ∀ i ∈ ys, monoNodeVerified g k i = true) :
    ∀ i ∈ xs++ys, monoNodeVerified g k i = true := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hx i hi
  · exact hy i hi

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

lemma fromBatch {g k ar indices} (p : monoBatchCheck g k ar indices = true) :
    ∀ i ∈ indices, monoNodeVerified g k i = true := fun _ hi => monoBatchCheck_at p hi

def ix8_9_0 : List Nat := [0, 1, 2]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp8_9_0 : monoBatchCheck or04forest 8 9 ix8_9_0 = true := by
  decide +kernel

def ix9_9_0 : List Nat := [0, 1, 2, 4, 5, 10, 24, 42, 44, 46, 47, 58, 61, 107, 120]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp9_9_0 : monoBatchCheck or04forest 9 9 ix9_9_0 = true := by
  decide +kernel

def ix9_10_0 : List Nat := [3, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp9_10_0 : monoBatchCheck or04forest 9 10 ix9_10_0 = true := by
  decide +kernel

def ix9_10_1 : List Nat := [39, 40, 41, 43, 45, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 59, 60, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp9_10_1 : monoBatchCheck or04forest 9 10 ix9_10_1 = true := by
  decide +kernel

def ix9_10_2 : List Nat := [77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 108, 109]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp9_10_2 : monoBatchCheck or04forest 9 10 ix9_10_2 = true := by
  decide +kernel

def ix9_10_3 : List Nat := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp9_10_3 : monoBatchCheck or04forest 9 10 ix9_10_3 = true := by
  decide +kernel

def ix9_10_4 : List Nat := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp9_10_4 : monoBatchCheck or04forest 9 10 ix9_10_4 = true := by
  decide +kernel

def ix10_10_0 : List Nat := [0, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15, 17, 24, 25, 26, 28, 29, 30, 31, 33, 35, 38, 39, 48, 50, 52, 77, 101, 102, 103]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_10_0 : monoBatchCheck or04forest 10 10 ix10_10_0 = true := by
  decide +kernel

def ix10_10_1 : List Nat := [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 127, 137, 139, 142, 146, 149, 150, 152, 157, 158, 161, 183, 191]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_10_1 : monoBatchCheck or04forest 10 10 ix10_10_1 = true := by
  decide +kernel

def ix10_10_2 : List Nat := [195, 199, 201, 203, 204, 229, 232, 243, 244, 272, 295, 297, 299, 339, 340, 367, 373, 377, 380, 381, 382, 383, 385, 386, 387, 388, 389, 392, 401, 407, 408, 409]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_10_2 : monoBatchCheck or04forest 10 10 ix10_10_2 = true := by
  decide +kernel

def ix10_10_3 : List Nat := [410, 412, 423, 426, 429, 433, 439, 453, 456, 458, 459, 467, 469, 470, 472, 473, 475, 477, 479, 480, 481, 482, 483, 484, 485, 491, 496, 500, 510, 511, 512, 513]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_10_3 : monoBatchCheck or04forest 10 10 ix10_10_3 = true := by
  decide +kernel

def ix10_10_4 : List Nat := [516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 539, 541, 544, 546, 549, 550, 552, 554, 555, 556, 558, 559, 560]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_10_4 : monoBatchCheck or04forest 10 10 ix10_10_4 = true := by
  decide +kernel

def ix10_10_5 : List Nat := [561, 562, 563, 565, 566, 567, 568, 571, 578, 612, 710, 721, 724, 732, 739, 740, 752, 757, 760, 764, 766, 768, 770, 771, 775, 787, 790, 796, 825, 834, 875, 905]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_10_5 : monoBatchCheck or04forest 10 10 ix10_10_5 = true := by
  decide +kernel

def ix10_10_6 : List Nat := [927, 938, 939, 944, 953, 958, 960, 962, 1002, 1003, 1004, 1005, 1037, 1096, 1117, 1129, 1146, 1183, 1184, 1186, 1193, 1205, 1296, 1300, 1301, 1302, 1312, 1313, 1320, 1321, 1323, 1324]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_10_6 : monoBatchCheck or04forest 10 10 ix10_10_6 = true := by
  decide +kernel

def ix10_10_7 : List Nat := [1325, 1326, 1327, 1328, 1329, 1331, 1332, 1333, 1381, 1387, 1401, 1405, 1409, 1410, 1412, 1428, 1450, 1470]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_10_7 : monoBatchCheck or04forest 10 10 ix10_10_7 = true := by
  decide +kernel

def ix10_11_0 : List Nat := [1, 6, 10, 16, 18, 19, 20, 21, 22, 23, 27, 32, 34, 36, 37, 40, 41, 42, 43, 44, 45, 46, 47, 49, 51, 53, 54, 55, 56, 57, 58, 59]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_0 : monoBatchCheck or04forest 10 11 ix10_11_0 = true := by
  decide +kernel

def ix10_11_1 : List Nat := [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_1 : monoBatchCheck or04forest 10 11 ix10_11_1 = true := by
  decide +kernel

def ix10_11_2 : List Nat := [93, 94, 95, 96, 97, 98, 99, 100, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 138, 140, 141, 143, 144, 145, 147, 148, 151, 153, 154]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_2 : monoBatchCheck or04forest 10 11 ix10_11_2 = true := by
  decide +kernel

def ix10_11_3 : List Nat := [155, 156, 159, 160, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_3 : monoBatchCheck or04forest 10 11 ix10_11_3 = true := by
  decide +kernel

def ix10_11_4 : List Nat := [192, 193, 194, 196, 197, 198, 200, 202, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_4 : monoBatchCheck or04forest 10 11 ix10_11_4 = true := by
  decide +kernel

def ix10_11_5 : List Nat := [230, 231, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_5 : monoBatchCheck or04forest 10 11 ix10_11_5 = true := by
  decide +kernel

def ix10_11_6 : List Nat := [265, 266, 267, 268, 269, 270, 271, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 296, 298, 300]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_6 : monoBatchCheck or04forest 10 11 ix10_11_6 = true := by
  decide +kernel

def ix10_11_7 : List Nat := [301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_7 : monoBatchCheck or04forest 10 11 ix10_11_7 = true := by
  decide +kernel

def ix10_11_8 : List Nat := [333, 334, 335, 336, 337, 338, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_8 : monoBatchCheck or04forest 10 11 ix10_11_8 = true := by
  decide +kernel

def ix10_11_9 : List Nat := [368, 369, 370, 371, 372, 374, 375, 376, 378, 379, 384, 390, 391, 393, 394, 395, 396, 397, 398, 399, 400, 402, 403, 404, 405, 406, 411, 413, 414, 415, 416, 417]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_9 : monoBatchCheck or04forest 10 11 ix10_11_9 = true := by
  decide +kernel

def ix10_11_10 : List Nat := [418, 419, 420, 421, 422, 424, 425, 427, 428, 430, 431, 432, 434, 435, 436, 437, 438, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 454, 455]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_10 : monoBatchCheck or04forest 10 11 ix10_11_10 = true := by
  decide +kernel

def ix10_11_11 : List Nat := [457, 460, 461, 462, 463, 464, 465, 466, 468, 471, 474, 476, 478, 486, 487, 488, 489, 490, 492, 493, 494, 495, 497, 498, 499, 501, 502, 503, 504, 505, 506, 507]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_11 : monoBatchCheck or04forest 10 11 ix10_11_11 = true := by
  decide +kernel

def ix10_11_12 : List Nat := [508, 509, 514, 515, 535, 536, 537, 538, 540, 542, 543, 545, 547, 548, 551, 553, 557, 564, 569, 570, 572, 573, 574, 575, 576, 577, 579, 580, 581, 582, 583, 584]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_12 : monoBatchCheck or04forest 10 11 ix10_11_12 = true := by
  decide +kernel

def ix10_11_13 : List Nat := [585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 613, 614, 615, 616, 617]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_13 : monoBatchCheck or04forest 10 11 ix10_11_13 = true := by
  decide +kernel

def ix10_11_14 : List Nat := [618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_14 : monoBatchCheck or04forest 10 11 ix10_11_14 = true := by
  decide +kernel

def ix10_11_15 : List Nat := [650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_15 : monoBatchCheck or04forest 10 11 ix10_11_15 = true := by
  decide +kernel

def ix10_11_16 : List Nat := [682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 711, 712, 713, 714]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_16 : monoBatchCheck or04forest 10 11 ix10_11_16 = true := by
  decide +kernel

def ix10_11_17 : List Nat := [715, 716, 717, 718, 719, 720, 722, 723, 725, 726, 727, 728, 729, 730, 731, 733, 734, 735, 736, 737, 738, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_17 : monoBatchCheck or04forest 10 11 ix10_11_17 = true := by
  decide +kernel

def ix10_11_18 : List Nat := [753, 754, 755, 756, 758, 759, 761, 762, 763, 765, 767, 769, 772, 773, 774, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 788, 789, 791, 792, 793, 794]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_18 : monoBatchCheck or04forest 10 11 ix10_11_18 = true := by
  decide +kernel

def ix10_11_19 : List Nat := [795, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 826, 827, 828]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_19 : monoBatchCheck or04forest 10 11 ix10_11_19 = true := by
  decide +kernel

def ix10_11_20 : List Nat := [829, 830, 831, 832, 833, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_20 : monoBatchCheck or04forest 10 11 ix10_11_20 = true := by
  decide +kernel

def ix10_11_21 : List Nat := [862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_21 : monoBatchCheck or04forest 10 11 ix10_11_21 = true := by
  decide +kernel

def ix10_11_22 : List Nat := [895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 928]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_22 : monoBatchCheck or04forest 10 11 ix10_11_22 = true := by
  decide +kernel

def ix10_11_23 : List Nat := [929, 930, 931, 932, 933, 934, 935, 936, 937, 940, 941, 942, 943, 945, 946, 947, 948, 949, 950, 951, 952, 954, 955, 956, 957, 959, 961, 963, 964, 965, 966, 967]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_23 : monoBatchCheck or04forest 10 11 ix10_11_23 = true := by
  decide +kernel

def ix10_11_24 : List Nat := [968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_24 : monoBatchCheck or04forest 10 11 ix10_11_24 = true := by
  decide +kernel

def ix10_11_25 : List Nat := [1000, 1001, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_25 : monoBatchCheck or04forest 10 11 ix10_11_25 = true := by
  decide +kernel

def ix10_11_26 : List Nat := [1036, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_26 : monoBatchCheck or04forest 10 11 ix10_11_26 = true := by
  decide +kernel

def ix10_11_27 : List Nat := [1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1097, 1098, 1099, 1100, 1101]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_27 : monoBatchCheck or04forest 10 11 ix10_11_27 = true := by
  decide +kernel

def ix10_11_28 : List Nat := [1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1130, 1131, 1132, 1133, 1134, 1135]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_28 : monoBatchCheck or04forest 10 11 ix10_11_28 = true := by
  decide +kernel

def ix10_11_29 : List Nat := [1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_29 : monoBatchCheck or04forest 10 11 ix10_11_29 = true := by
  decide +kernel

def ix10_11_30 : List Nat := [1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1185, 1187, 1188, 1189, 1190, 1191, 1192, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_30 : monoBatchCheck or04forest 10 11 ix10_11_30 = true := by
  decide +kernel

def ix10_11_31 : List Nat := [1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_31 : monoBatchCheck or04forest 10 11 ix10_11_31 = true := by
  decide +kernel

def ix10_11_32 : List Nat := [1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_32 : monoBatchCheck or04forest 10 11 ix10_11_32 = true := by
  decide +kernel

def ix10_11_33 : List Nat := [1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1297, 1298, 1299, 1303, 1304, 1305]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_33 : monoBatchCheck or04forest 10 11 ix10_11_33 = true := by
  decide +kernel

def ix10_11_34 : List Nat := [1306, 1307, 1308, 1309, 1310, 1311, 1314, 1315, 1316, 1317, 1318, 1319, 1322, 1330, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_34 : monoBatchCheck or04forest 10 11 ix10_11_34 = true := by
  decide +kernel

def ix10_11_35 : List Nat := [1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1382, 1383, 1384]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_35 : monoBatchCheck or04forest 10 11 ix10_11_35 = true := by
  decide +kernel

def ix10_11_36 : List Nat := [1385, 1386, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1402, 1403, 1404, 1406, 1407, 1408, 1411, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_36 : monoBatchCheck or04forest 10 11 ix10_11_36 = true := by
  decide +kernel

def ix10_11_37 : List Nat := [1423, 1424, 1425, 1426, 1427, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1451, 1452, 1453, 1454, 1455, 1456]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_37 : monoBatchCheck or04forest 10 11 ix10_11_37 = true := by
  decide +kernel

def ix10_11_38 : List Nat := [1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1471]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp10_11_38 : monoBatchCheck or04forest 10 11 ix10_11_38 = true := by
  decide +kernel

def ix11_9_0 : List Nat := [52]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_9_0 : monoBatchCheck or04forest 11 9 ix11_9_0 = true := by
  decide +kernel

def ix11_10_0 : List Nat := [1, 4, 6, 7, 9, 11, 13, 53, 56, 65, 69, 74, 83, 105, 157, 159, 236, 237, 240, 241, 270, 272, 274, 275, 276, 278, 279, 282, 284, 286, 293, 295]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_10_0 : monoBatchCheck or04forest 11 10 ix11_10_0 = true := by
  decide +kernel

def ix11_10_1 : List Nat := [296, 298, 319, 321, 322, 323, 326, 327, 330, 334, 335, 336, 341, 736, 745, 958, 1087, 1159, 1449, 1767, 1783, 1788, 1966]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_10_1 : monoBatchCheck or04forest 11 10 ix11_10_1 = true := by
  decide +kernel

def ix11_11_0 : List Nat := [0, 2, 5, 8, 10, 12, 14, 15, 17, 22, 25, 27, 28, 34, 39, 43, 45, 48, 50, 54, 55, 57, 58, 59, 60, 61, 62, 63, 64, 66, 67, 68]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_0 : monoBatchCheck or04forest 11 11 ix11_11_0 = true := by
  decide +kernel

def ix11_11_1 : List Nat := [70, 71, 72, 73, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 103, 104, 106]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_1 : monoBatchCheck or04forest 11 11 ix11_11_1 = true := by
  decide +kernel

def ix11_11_2 : List Nat := [107, 109, 115, 117, 118, 120, 122, 123, 126, 129, 132, 133, 134, 135, 139, 141, 145, 148, 149, 150, 152, 155, 156, 158, 160, 161, 166, 168, 176, 178, 183, 185]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_2 : monoBatchCheck or04forest 11 11 ix11_11_2 = true := by
  decide +kernel

def ix11_11_3 : List Nat := [190, 193, 196, 198, 202, 205, 207, 209, 211, 215, 217, 218, 219, 222, 227, 228, 230, 232, 233, 234, 235, 238, 239, 243, 244, 248, 249, 250, 252, 255, 256, 257]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_3 : monoBatchCheck or04forest 11 11 ix11_11_3 = true := by
  decide +kernel

def ix11_11_4 : List Nat := [260, 262, 263, 265, 267, 268, 273, 277, 280, 281, 283, 285, 287, 290, 291, 294, 297, 299, 300, 301, 302, 303, 304, 305, 306, 307, 309, 310, 311, 313, 315, 316]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_4 : monoBatchCheck or04forest 11 11 ix11_11_4 = true := by
  decide +kernel

def ix11_11_5 : List Nat := [318, 320, 324, 325, 328, 329, 331, 332, 333, 337, 338, 339, 340, 344, 345, 347, 350, 351, 352, 356, 361, 363, 364, 365, 367, 369, 370, 371, 372, 378, 379, 383]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_5 : monoBatchCheck or04forest 11 11 ix11_11_5 = true := by
  decide +kernel

def ix11_11_6 : List Nat := [387, 390, 391, 393, 394, 395, 402, 403, 404, 405, 409, 410, 413, 414, 415, 417, 418, 419, 420, 421, 427, 435, 436, 437, 441, 445, 448, 450, 451, 454, 465, 479]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_6 : monoBatchCheck or04forest 11 11 ix11_11_6 = true := by
  decide +kernel

def ix11_11_7 : List Nat := [480, 482, 485, 487, 488, 491, 493, 495, 497, 498, 500, 502, 513, 523, 524, 527, 528, 531, 533, 534, 537, 549, 551, 552, 564, 574, 584, 586, 591, 595, 598, 600]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_7 : monoBatchCheck or04forest 11 11 ix11_11_7 = true := by
  decide +kernel

def ix11_11_8 : List Nat := [602, 603, 606, 610, 612, 613, 615, 623, 625, 629, 632, 634, 635, 645, 647, 648, 655, 657, 658, 660, 661, 662, 666, 669, 671, 673, 675, 678, 679, 682, 684, 685]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_8 : monoBatchCheck or04forest 11 11 ix11_11_8 = true := by
  decide +kernel

def ix11_11_9 : List Nat := [687, 691, 696, 697, 700, 702, 703, 706, 707, 710, 713, 715, 716, 717, 719, 721, 723, 725, 728, 729, 731, 732, 733, 737, 738, 739, 740, 741, 742, 743, 744, 746]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_9 : monoBatchCheck or04forest 11 11 ix11_11_9 = true := by
  decide +kernel

def ix11_11_10 : List Nat := [747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 765, 767, 768, 769, 777, 785, 786, 791, 793, 796, 797, 800, 802, 805, 806, 807, 809, 810]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_10 : monoBatchCheck or04forest 11 11 ix11_11_10 = true := by
  decide +kernel

def ix11_11_11 : List Nat := [811, 812, 813, 821, 822, 826, 828, 829, 833, 835, 836, 839, 845, 847, 850, 851, 854, 858, 859, 860, 862, 865, 870, 871, 887, 889, 891, 897, 905, 906, 913, 918]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_11 : monoBatchCheck or04forest 11 11 ix11_11_11 = true := by
  decide +kernel

def ix11_11_12 : List Nat := [919, 920, 925, 926, 937, 940, 941, 944, 947, 951, 954, 956, 959, 962, 965, 967, 969, 971, 980, 981, 983, 986, 988, 990, 991, 993, 998, 1001, 1003, 1013, 1015, 1016]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_12 : monoBatchCheck or04forest 11 11 ix11_11_12 = true := by
  decide +kernel

def ix11_11_13 : List Nat := [1022, 1027, 1030, 1032, 1039, 1042, 1043, 1048, 1053, 1054, 1057, 1058, 1059, 1064, 1065, 1068, 1069, 1073, 1074, 1075, 1076, 1078, 1079, 1081, 1084, 1085, 1090, 1092, 1095, 1096, 1097, 1098]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_13 : monoBatchCheck or04forest 11 11 ix11_11_13 = true := by
  decide +kernel

def ix11_11_14 : List Nat := [1099, 1101, 1105, 1108, 1110, 1111, 1112, 1115, 1117, 1119, 1120, 1121, 1122, 1126, 1128, 1132, 1134, 1138, 1140, 1146, 1149, 1151, 1153, 1156, 1158, 1160, 1161, 1162, 1165, 1166, 1168, 1174]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_14 : monoBatchCheck or04forest 11 11 ix11_11_14 = true := by
  decide +kernel

def ix11_11_15 : List Nat := [1177, 1178, 1181, 1182, 1184, 1187, 1189, 1190, 1193, 1195, 1196, 1198, 1199, 1200, 1202, 1205, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1215, 1218, 1223, 1228, 1231, 1232, 1233, 1234, 1235]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_15 : monoBatchCheck or04forest 11 11 ix11_11_15 = true := by
  decide +kernel

def ix11_11_16 : List Nat := [1236, 1237, 1238, 1240, 1242, 1243, 1250, 1251, 1263, 1264, 1266, 1267, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1281, 1284, 1288, 1289, 1293, 1294, 1295, 1296, 1297, 1301, 1302, 1303, 1304]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_16 : monoBatchCheck or04forest 11 11 ix11_11_16 = true := by
  decide +kernel

def ix11_11_17 : List Nat := [1306, 1307, 1308, 1309, 1312, 1314, 1316, 1318, 1320, 1323, 1324, 1325, 1326, 1328, 1329, 1330, 1333, 1334, 1335, 1342, 1344, 1348, 1350, 1356, 1357, 1358, 1360, 1361, 1362, 1364, 1365, 1366]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_17 : monoBatchCheck or04forest 11 11 ix11_11_17 = true := by
  decide +kernel

def ix11_11_18 : List Nat := [1367, 1368, 1375, 1376, 1381, 1383, 1396, 1405, 1411, 1412, 1419, 1420, 1423, 1424, 1425, 1430, 1432, 1434, 1441, 1443, 1445, 1450, 1453, 1454, 1456, 1460, 1461, 1463, 1465, 1472, 1474, 1475]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_18 : monoBatchCheck or04forest 11 11 ix11_11_18 = true := by
  decide +kernel

def ix11_11_19 : List Nat := [1477, 1479, 1480, 1481, 1482, 1485, 1489, 1491, 1492, 1494, 1496, 1497, 1498, 1509, 1513, 1514, 1518, 1519, 1520, 1530, 1531, 1532, 1534, 1537, 1539, 1541, 1542, 1543, 1550, 1551, 1558, 1565]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_19 : monoBatchCheck or04forest 11 11 ix11_11_19 = true := by
  decide +kernel

def ix11_11_20 : List Nat := [1566, 1569, 1573, 1577, 1582, 1583, 1584, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1602, 1603, 1606, 1609, 1610, 1620, 1622, 1628, 1629, 1635, 1637, 1641, 1644, 1646, 1648, 1649, 1650, 1655]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_20 : monoBatchCheck or04forest 11 11 ix11_11_20 = true := by
  decide +kernel

def ix11_11_21 : List Nat := [1659, 1661, 1662, 1668, 1670, 1671, 1688, 1693, 1696, 1697, 1702, 1703, 1704, 1706, 1707, 1711, 1712, 1713, 1714, 1716, 1717, 1721, 1722, 1723, 1726, 1730, 1733, 1734, 1737, 1738, 1739, 1740]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_21 : monoBatchCheck or04forest 11 11 ix11_11_21 = true := by
  decide +kernel

def ix11_11_22 : List Nat := [1742, 1746, 1747, 1748, 1750, 1751, 1752, 1756, 1759, 1760, 1761, 1762, 1763, 1765, 1766, 1768, 1770, 1772, 1774, 1775, 1778, 1779, 1780, 1781, 1782, 1784, 1785, 1786, 1787, 1789, 1790, 1791]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_22 : monoBatchCheck or04forest 11 11 ix11_11_22 = true := by
  decide +kernel

def ix11_11_23 : List Nat := [1792, 1793, 1794, 1795, 1796, 1797, 1800, 1805, 1806, 1819, 1823, 1828, 1830, 1831, 1837, 1838, 1839, 1847, 1848, 1850, 1853, 1856, 1862, 1865, 1868, 1869, 1877, 1878, 1879, 1880, 1890, 1891]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_23 : monoBatchCheck or04forest 11 11 ix11_11_23 = true := by
  decide +kernel

def ix11_11_24 : List Nat := [1896, 1903, 1904, 1905, 1910, 1912, 1914, 1920, 1922, 1925, 1926, 1930, 1931, 1935, 1939, 1941, 1944, 1945, 1949, 1952, 1953, 1954, 1955, 1957, 1959, 1960, 1961, 1963, 1964, 1965, 1967, 1969]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_24 : monoBatchCheck or04forest 11 11 ix11_11_24 = true := by
  decide +kernel

def ix11_11_25 : List Nat := [1970, 1971, 1972, 1973, 1974, 1975, 1978, 1980, 1984, 1987, 1989, 1991, 1993, 1996, 1998, 1999, 2001, 2004, 2005, 2006, 2007, 2011, 2018, 2021, 2022, 2023, 2025, 2026, 2032, 2033, 2042, 2043]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_25 : monoBatchCheck or04forest 11 11 ix11_11_25 = true := by
  decide +kernel

def ix11_11_26 : List Nat := [2058, 2063, 2066, 2071, 2072, 2075, 2077, 2080, 2082, 2083, 2084, 2089, 2091, 2092, 2095, 2097, 2098, 2100, 2107, 2112, 2113, 2117, 2118, 2121, 2123, 2127, 2128, 2133, 2135, 2138, 2141, 2146]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_26 : monoBatchCheck or04forest 11 11 ix11_11_26 = true := by
  decide +kernel

def ix11_11_27 : List Nat := [2147, 2151, 2153, 2158, 2159, 2160, 2162, 2163, 2166, 2167, 2168, 2171, 2172, 2173, 2174, 2178, 2180, 2182, 2187, 2191, 2192, 2193, 2194, 2195, 2196, 2198, 2203, 2205, 2206, 2207, 2209, 2211]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_27 : monoBatchCheck or04forest 11 11 ix11_11_27 = true := by
  decide +kernel

def ix11_11_28 : List Nat := [2212, 2215, 2219, 2222, 2223, 2231, 2232, 2240, 2243, 2244, 2248, 2249, 2250, 2251, 2252, 2255, 2258, 2259, 2260, 2261, 2262, 2263]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_11_28 : monoBatchCheck or04forest 11 11 ix11_11_28 = true := by
  decide +kernel

def ix11_12_0 : List Nat := [3, 16, 18, 19, 20, 21, 23, 24, 26, 29, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 44, 46, 47, 49, 51, 101, 102, 108, 110, 111, 112]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_0 : monoBatchCheck or04forest 11 12 ix11_12_0 = true := by
  decide +kernel

def ix11_12_1 : List Nat := [113, 114, 116, 119, 121, 124, 125, 127, 128, 130, 131, 136, 137, 138, 140, 142, 143, 144, 146, 147, 151, 153, 154, 162, 163, 164, 165, 167, 169, 170, 171, 172]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_1 : monoBatchCheck or04forest 11 12 ix11_12_1 = true := by
  decide +kernel

def ix11_12_2 : List Nat := [173, 174, 175, 177, 179, 180, 181, 182, 184, 186, 187, 188, 189, 191, 192, 194, 195, 197, 199, 200, 201, 203, 204, 206, 208, 210, 212, 213, 214, 216, 220, 221]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_2 : monoBatchCheck or04forest 11 12 ix11_12_2 = true := by
  decide +kernel

def ix11_12_3 : List Nat := [223, 224, 225, 226, 229, 231, 242, 245, 246, 247, 251, 253, 254, 258, 259, 261, 264, 266, 269, 271, 288, 289, 292, 308, 312, 314, 317, 342, 343, 346, 348, 349]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_3 : monoBatchCheck or04forest 11 12 ix11_12_3 = true := by
  decide +kernel

def ix11_12_4 : List Nat := [353, 354, 355, 357, 358, 359, 360, 362, 366, 368, 373, 374, 375, 376, 377, 380, 381, 382, 384, 385, 386, 388, 389, 392, 396, 397, 398, 399, 400, 401, 406, 407]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_4 : monoBatchCheck or04forest 11 12 ix11_12_4 = true := by
  decide +kernel

def ix11_12_5 : List Nat := [408, 411, 412, 416, 422, 423, 424, 425, 426, 428, 429, 430, 431, 432, 433, 434, 438, 439, 440, 442, 443, 444, 446, 447, 449, 452, 453, 455, 456, 457, 458, 459]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_5 : monoBatchCheck or04forest 11 12 ix11_12_5 = true := by
  decide +kernel

def ix11_12_6 : List Nat := [460, 461, 462, 463, 464, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 481, 483, 484, 486, 489, 490, 492, 494, 496, 499, 501, 503, 504, 505]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_6 : monoBatchCheck or04forest 11 12 ix11_12_6 = true := by
  decide +kernel

def ix11_12_7 : List Nat := [506, 507, 508, 509, 510, 511, 512, 514, 515, 516, 517, 518, 519, 520, 521, 522, 525, 526, 529, 530, 532, 535, 536, 538, 539, 540, 541, 542, 543, 544, 545, 546]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_7 : monoBatchCheck or04forest 11 12 ix11_12_7 = true := by
  decide +kernel

def ix11_12_8 : List Nat := [547, 548, 550, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 565, 566, 567, 568, 569, 570, 571, 572, 573, 575, 576, 577, 578, 579, 580, 581, 582, 583]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_8 : monoBatchCheck or04forest 11 12 ix11_12_8 = true := by
  decide +kernel

def ix11_12_9 : List Nat := [585, 587, 588, 589, 590, 592, 593, 594, 596, 597, 599, 601, 604, 605, 607, 608, 609, 611, 614, 616, 617, 618, 619, 620, 621, 622, 624, 626, 627, 628, 630, 631]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_9 : monoBatchCheck or04forest 11 12 ix11_12_9 = true := by
  decide +kernel

def ix11_12_10 : List Nat := [633, 636, 637, 638, 639, 640, 641, 642, 643, 644, 646, 649, 650, 651, 652, 653, 654, 656, 659, 663, 664, 665, 667, 668, 670, 672, 674, 676, 677, 680, 681, 683]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_10 : monoBatchCheck or04forest 11 12 ix11_12_10 = true := by
  decide +kernel

def ix11_12_11 : List Nat := [686, 688, 689, 690, 692, 693, 694, 695, 698, 699, 701, 704, 705, 708, 709, 711, 712, 714, 718, 720, 722, 724, 726, 727, 730, 734, 735, 761, 762, 763, 764, 766]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_11 : monoBatchCheck or04forest 11 12 ix11_12_11 = true := by
  decide +kernel

def ix11_12_12 : List Nat := [770, 771, 772, 773, 774, 775, 776, 778, 779, 780, 781, 782, 783, 784, 787, 788, 789, 790, 792, 794, 795, 798, 799, 801, 803, 804, 808, 814, 815, 816, 817, 818]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_12 : monoBatchCheck or04forest 11 12 ix11_12_12 = true := by
  decide +kernel

def ix11_12_13 : List Nat := [819, 820, 823, 824, 825, 827, 830, 831, 832, 834, 837, 838, 840, 841, 842, 843, 844, 846, 848, 849, 852, 853, 855, 856, 857, 861, 863, 864, 866, 867, 868, 869]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_13 : monoBatchCheck or04forest 11 12 ix11_12_13 = true := by
  decide +kernel

def ix11_12_14 : List Nat := [872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 888, 890, 892, 893, 894, 895, 896, 898, 899, 900, 901, 902, 903, 904, 907, 908, 909]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_14 : monoBatchCheck or04forest 11 12 ix11_12_14 = true := by
  decide +kernel

def ix11_12_15 : List Nat := [910, 911, 912, 914, 915, 916, 917, 921, 922, 923, 924, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 938, 939, 942, 943, 945, 946, 948, 949, 950, 952, 953]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_15 : monoBatchCheck or04forest 11 12 ix11_12_15 = true := by
  decide +kernel

def ix11_12_16 : List Nat := [955, 957, 960, 961, 963, 964, 966, 968, 970, 972, 973, 974, 975, 976, 977, 978, 979, 982, 984, 985, 987, 989, 992, 994, 995, 996, 997, 999, 1000, 1002, 1004, 1005]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_16 : monoBatchCheck or04forest 11 12 ix11_12_16 = true := by
  decide +kernel

def ix11_12_17 : List Nat := [1006, 1007, 1008, 1009, 1010, 1011, 1012, 1014, 1017, 1018, 1019, 1020, 1021, 1023, 1024, 1025, 1026, 1028, 1029, 1031, 1033, 1034, 1035, 1036, 1037, 1038, 1040, 1041, 1044, 1045, 1046, 1047]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_17 : monoBatchCheck or04forest 11 12 ix11_12_17 = true := by
  decide +kernel

def ix11_12_18 : List Nat := [1049, 1050, 1051, 1052, 1055, 1056, 1060, 1061, 1062, 1063, 1066, 1067, 1070, 1071, 1072, 1077, 1080, 1082, 1083, 1086, 1088, 1089, 1091, 1093, 1094, 1100, 1102, 1103, 1104, 1106, 1107, 1109]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_18 : monoBatchCheck or04forest 11 12 ix11_12_18 = true := by
  decide +kernel

def ix11_12_19 : List Nat := [1113, 1114, 1116, 1118, 1123, 1124, 1125, 1127, 1129, 1130, 1131, 1133, 1135, 1136, 1137, 1139, 1141, 1142, 1143, 1144, 1145, 1147, 1148, 1150, 1152, 1154, 1155, 1157, 1163, 1164, 1167, 1169]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_19 : monoBatchCheck or04forest 11 12 ix11_12_19 = true := by
  decide +kernel

def ix11_12_20 : List Nat := [1170, 1171, 1172, 1173, 1175, 1176, 1179, 1180, 1183, 1185, 1186, 1188, 1191, 1192, 1194, 1197, 1201, 1203, 1204, 1206, 1214, 1216, 1217, 1219, 1220, 1221, 1222, 1224, 1225, 1226, 1227, 1229]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_20 : monoBatchCheck or04forest 11 12 ix11_12_20 = true := by
  decide +kernel

def ix11_12_21 : List Nat := [1230, 1239, 1241, 1244, 1245, 1246, 1247, 1248, 1249, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1265, 1268, 1276, 1277, 1278, 1279, 1280, 1282, 1283, 1285, 1286, 1287]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_21 : monoBatchCheck or04forest 11 12 ix11_12_21 = true := by
  decide +kernel

def ix11_12_22 : List Nat := [1290, 1291, 1292, 1298, 1299, 1300, 1305, 1310, 1311, 1313, 1315, 1317, 1319, 1321, 1322, 1327, 1331, 1332, 1336, 1337, 1338, 1339, 1340, 1341, 1343, 1345, 1346, 1347, 1349, 1351, 1352, 1353]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_22 : monoBatchCheck or04forest 11 12 ix11_12_22 = true := by
  decide +kernel

def ix11_12_23 : List Nat := [1354, 1355, 1359, 1363, 1369, 1370, 1371, 1372, 1373, 1374, 1377, 1378, 1379, 1380, 1382, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1397, 1398, 1399, 1400, 1401]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_23 : monoBatchCheck or04forest 11 12 ix11_12_23 = true := by
  decide +kernel

def ix11_12_24 : List Nat := [1402, 1403, 1404, 1406, 1407, 1408, 1409, 1410, 1413, 1414, 1415, 1416, 1417, 1418, 1421, 1422, 1426, 1427, 1428, 1429, 1431, 1433, 1435, 1436, 1437, 1438, 1439, 1440, 1442, 1444, 1446, 1447]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_24 : monoBatchCheck or04forest 11 12 ix11_12_24 = true := by
  decide +kernel

def ix11_12_25 : List Nat := [1448, 1451, 1452, 1455, 1457, 1458, 1459, 1462, 1464, 1466, 1467, 1468, 1469, 1470, 1471, 1473, 1476, 1478, 1483, 1484, 1486, 1487, 1488, 1490, 1493, 1495, 1499, 1500, 1501, 1502, 1503, 1504]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_25 : monoBatchCheck or04forest 11 12 ix11_12_25 = true := by
  decide +kernel

def ix11_12_26 : List Nat := [1505, 1506, 1507, 1508, 1510, 1511, 1512, 1515, 1516, 1517, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1533, 1535, 1536, 1538, 1540, 1544, 1545, 1546, 1547, 1548, 1549, 1552, 1553]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_26 : monoBatchCheck or04forest 11 12 ix11_12_26 = true := by
  decide +kernel

def ix11_12_27 : List Nat := [1554, 1555, 1556, 1557, 1559, 1560, 1561, 1562, 1563, 1564, 1567, 1568, 1570, 1571, 1572, 1574, 1575, 1576, 1578, 1579, 1580, 1581, 1585, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_27 : monoBatchCheck or04forest 11 12 ix11_12_27 = true := by
  decide +kernel

def ix11_12_28 : List Nat := [1604, 1605, 1607, 1608, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1621, 1623, 1624, 1625, 1626, 1627, 1630, 1631, 1632, 1633, 1634, 1636, 1638, 1639, 1640, 1642, 1643, 1645, 1647]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_28 : monoBatchCheck or04forest 11 12 ix11_12_28 = true := by
  decide +kernel

def ix11_12_29 : List Nat := [1651, 1652, 1653, 1654, 1656, 1657, 1658, 1660, 1663, 1664, 1665, 1666, 1667, 1669, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1689, 1690]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_29 : monoBatchCheck or04forest 11 12 ix11_12_29 = true := by
  decide +kernel

def ix11_12_30 : List Nat := [1691, 1692, 1694, 1695, 1698, 1699, 1700, 1701, 1705, 1708, 1709, 1710, 1715, 1718, 1719, 1720, 1724, 1725, 1727, 1728, 1729, 1731, 1732, 1735, 1736, 1741, 1743, 1744, 1745, 1749, 1753, 1754]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_30 : monoBatchCheck or04forest 11 12 ix11_12_30 = true := by
  decide +kernel

def ix11_12_31 : List Nat := [1755, 1757, 1758, 1764, 1769, 1771, 1773, 1776, 1777, 1798, 1799, 1801, 1802, 1803, 1804, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1820, 1821, 1822, 1824, 1825]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_31 : monoBatchCheck or04forest 11 12 ix11_12_31 = true := by
  decide +kernel

def ix11_12_32 : List Nat := [1826, 1827, 1829, 1832, 1833, 1834, 1835, 1836, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1849, 1851, 1852, 1854, 1855, 1857, 1858, 1859, 1860, 1861, 1863, 1864, 1866, 1867, 1870, 1871, 1872]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_32 : monoBatchCheck or04forest 11 12 ix11_12_32 = true := by
  decide +kernel

def ix11_12_33 : List Nat := [1873, 1874, 1875, 1876, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1892, 1893, 1894, 1895, 1897, 1898, 1899, 1900, 1901, 1902, 1906, 1907, 1908, 1909, 1911, 1913, 1915, 1916, 1917]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_33 : monoBatchCheck or04forest 11 12 ix11_12_33 = true := by
  decide +kernel

def ix11_12_34 : List Nat := [1918, 1919, 1921, 1923, 1924, 1927, 1928, 1929, 1932, 1933, 1934, 1936, 1937, 1938, 1940, 1942, 1943, 1946, 1947, 1948, 1950, 1951, 1956, 1958, 1962, 1968, 1976, 1977, 1979, 1981, 1982, 1983]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_34 : monoBatchCheck or04forest 11 12 ix11_12_34 = true := by
  decide +kernel

def ix11_12_35 : List Nat := [1985, 1986, 1988, 1990, 1992, 1994, 1995, 1997, 2000, 2002, 2003, 2008, 2009, 2010, 2012, 2013, 2014, 2015, 2016, 2017, 2019, 2020, 2024, 2027, 2028, 2029, 2030, 2031, 2034, 2035, 2036, 2037]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_35 : monoBatchCheck or04forest 11 12 ix11_12_35 = true := by
  decide +kernel

def ix11_12_36 : List Nat := [2038, 2039, 2040, 2041, 2044, 2045, 2046, 2047, 2048, 2049, 2050, 2051, 2052, 2053, 2054, 2055, 2056, 2057, 2059, 2060, 2061, 2062, 2064, 2065, 2067, 2068, 2069, 2070, 2073, 2074, 2076, 2078]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_36 : monoBatchCheck or04forest 11 12 ix11_12_36 = true := by
  decide +kernel

def ix11_12_37 : List Nat := [2079, 2081, 2085, 2086, 2087, 2088, 2090, 2093, 2094, 2096, 2099, 2101, 2102, 2103, 2104, 2105, 2106, 2108, 2109, 2110, 2111, 2114, 2115, 2116, 2119, 2120, 2122, 2124, 2125, 2126, 2129, 2130]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_37 : monoBatchCheck or04forest 11 12 ix11_12_37 = true := by
  decide +kernel

def ix11_12_38 : List Nat := [2131, 2132, 2134, 2136, 2137, 2139, 2140, 2142, 2143, 2144, 2145, 2148, 2149, 2150, 2152, 2154, 2155, 2156, 2157, 2161, 2164, 2165, 2169, 2170, 2175, 2176, 2177, 2179, 2181, 2183, 2184, 2185]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_38 : monoBatchCheck or04forest 11 12 ix11_12_38 = true := by
  decide +kernel

def ix11_12_39 : List Nat := [2186, 2188, 2189, 2190, 2197, 2199, 2200, 2201, 2202, 2204, 2208, 2210, 2213, 2214, 2216, 2217, 2218, 2220, 2221, 2224, 2225, 2226, 2227, 2228, 2229, 2230, 2233, 2234, 2235, 2236, 2237, 2238]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_39 : monoBatchCheck or04forest 11 12 ix11_12_39 = true := by
  decide +kernel

def ix11_12_40 : List Nat := [2239, 2241, 2242, 2245, 2246, 2247, 2253, 2254, 2256, 2257, 2264, 2265, 2266, 2267]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp11_12_40 : monoBatchCheck or04forest 11 12 ix11_12_40 = true := by
  decide +kernel

def ix12_10_0 : List Nat := [2, 3, 15, 19, 23, 26, 30, 32, 33, 35, 37, 80, 82, 120, 132, 138, 141, 143, 151, 152, 174, 194, 220, 230, 234, 236, 263, 295, 315, 322, 326, 336]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_10_0 : monoBatchCheck or04forest 12 10 ix12_10_0 = true := by
  decide +kernel

def ix12_10_1 : List Nat := [347, 352, 354]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_10_1 : monoBatchCheck or04forest 12 10 ix12_10_1 = true := by
  decide +kernel

def ix12_11_0 : List Nat := [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 22, 24, 25, 29, 31, 34, 36, 38, 40, 42, 45, 48, 51, 56, 57, 59]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_11_0 : monoBatchCheck or04forest 12 11 ix12_11_0 = true := by
  decide +kernel

def ix12_11_1 : List Nat := [63, 65, 69, 70, 73, 74, 76, 78, 81, 83, 86, 88, 89, 96, 99, 100, 103, 105, 109, 110, 113, 114, 116, 118, 121, 122, 123, 124, 125, 126, 127, 128]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_11_1 : monoBatchCheck or04forest 12 11 ix12_11_1 = true := by
  decide +kernel

def ix12_11_2 : List Nat := [129, 130, 131, 133, 134, 135, 136, 137, 139, 140, 142, 147, 148, 149, 150, 153, 155, 157, 163, 167, 169, 171, 172, 175, 176, 180, 183, 186, 188, 190, 191, 192]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_11_2 : monoBatchCheck or04forest 12 11 ix12_11_2 = true := by
  decide +kernel

def ix12_11_3 : List Nat := [193, 196, 200, 202, 206, 209, 211, 213, 215, 216, 218, 225, 226, 228, 229, 231, 232, 233, 235, 237, 242, 244, 250, 252, 256, 257, 260, 262, 264, 265, 266, 267]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_11_3 : monoBatchCheck or04forest 12 11 ix12_11_3 = true := by
  decide +kernel

def ix12_11_4 : List Nat := [268, 269, 270, 271, 272, 273, 274, 275, 278, 280, 281, 285, 286, 289, 290, 292, 293, 296, 298, 300, 301, 303, 307, 309, 310, 312, 313, 317, 318, 320, 321, 323]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_11_4 : monoBatchCheck or04forest 12 11 ix12_11_4 = true := by
  decide +kernel

def ix12_11_5 : List Nat := [324, 325, 329, 331, 334, 337, 338, 339, 340, 341, 342, 343, 348, 349, 353]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_11_5 : monoBatchCheck or04forest 12 11 ix12_11_5 = true := by
  decide +kernel

def ix12_12_0 : List Nat := [20, 21, 27, 28, 39, 41, 43, 44, 46, 47, 49, 50, 52, 53, 54, 55, 58, 60, 61, 62, 64, 66, 67, 68, 71, 72, 75, 77, 79, 84, 85, 87]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_12_0 : monoBatchCheck or04forest 12 12 ix12_12_0 = true := by
  decide +kernel

def ix12_12_1 : List Nat := [90, 91, 92, 93, 94, 95, 97, 98, 101, 102, 104, 106, 107, 108, 111, 112, 115, 117, 119, 144, 145, 146, 154, 156, 158, 159, 160, 161, 162, 164, 165, 166]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_12_1 : monoBatchCheck or04forest 12 12 ix12_12_1 = true := by
  decide +kernel

def ix12_12_2 : List Nat := [168, 170, 173, 177, 178, 179, 181, 182, 184, 185, 187, 189, 195, 197, 198, 199, 201, 203, 204, 205, 207, 208, 210, 212, 214, 217, 219, 221, 222, 223, 224, 227]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_12_2 : monoBatchCheck or04forest 12 12 ix12_12_2 = true := by
  decide +kernel

def ix12_12_3 : List Nat := [238, 239, 240, 241, 243, 245, 246, 247, 248, 249, 251, 253, 254, 255, 258, 259, 261, 276, 277, 279, 282, 283, 284, 287, 288, 291, 294, 297, 299, 302, 304, 305]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_12_3 : monoBatchCheck or04forest 12 12 ix12_12_3 = true := by
  decide +kernel

def ix12_12_4 : List Nat := [306, 308, 311, 314, 316, 319, 327, 328, 330, 332, 333, 335, 344, 345, 346, 350, 351]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp12_12_4 : monoBatchCheck or04forest 12 12 ix12_12_4 = true := by
  decide +kernel

def ix13_10_0 : List Nat := [0, 4, 11, 17, 19, 21]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp13_10_0 : monoBatchCheck or04forest 13 10 ix13_10_0 = true := by
  decide +kernel

def ix13_11_0 : List Nat := [1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 20]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp13_11_0 : monoBatchCheck or04forest 13 11 ix13_11_0 = true := by
  decide +kernel

def ix14_10_0 : List Nat := [0]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma bp14_10_0 : monoBatchCheck or04forest 14 10 ix14_10_0 = true := by
  decide +kernel

def or04ids8 : List Nat := ix8_9_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04cover8 : checkedIndexMask or04ids8 = 2^3-1 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04level8 : monoBlock or04forest 8 0 3 = true :=
  checkedByMask or04ids8 (fromBatch bp8_9_0) or04cover8

def or04ids9 : List Nat := ((ix9_9_0 ++ (ix9_10_0 ++ ix9_10_1)) ++ (ix9_10_2 ++ (ix9_10_3 ++ ix9_10_4)))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04cover9 : checkedIndexMask or04ids9 = 2^161-1 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04level9 : monoBlock or04forest 9 0 161 = true :=
  checkedByMask or04ids9 (checkedListAppend (checkedListAppend (fromBatch bp9_9_0) (checkedListAppend (fromBatch bp9_10_0) (fromBatch bp9_10_1))) (checkedListAppend (fromBatch bp9_10_2) (checkedListAppend (fromBatch bp9_10_3) (fromBatch bp9_10_4)))) or04cover9

def or04ids10 : List Nat := (((((ix10_10_0 ++ ix10_10_1) ++ (ix10_10_2 ++ (ix10_10_3 ++ ix10_10_4))) ++ ((ix10_10_5 ++ (ix10_10_6 ++ ix10_10_7)) ++ (ix10_11_0 ++ (ix10_11_1 ++ ix10_11_2)))) ++ (((ix10_11_3 ++ (ix10_11_4 ++ ix10_11_5)) ++ (ix10_11_6 ++ (ix10_11_7 ++ ix10_11_8))) ++ ((ix10_11_9 ++ (ix10_11_10 ++ ix10_11_11)) ++ (ix10_11_12 ++ (ix10_11_13 ++ ix10_11_14))))) ++ ((((ix10_11_15 ++ (ix10_11_16 ++ ix10_11_17)) ++ (ix10_11_18 ++ (ix10_11_19 ++ ix10_11_20))) ++ ((ix10_11_21 ++ (ix10_11_22 ++ ix10_11_23)) ++ (ix10_11_24 ++ (ix10_11_25 ++ ix10_11_26)))) ++ (((ix10_11_27 ++ (ix10_11_28 ++ ix10_11_29)) ++ (ix10_11_30 ++ (ix10_11_31 ++ ix10_11_32))) ++ ((ix10_11_33 ++ (ix10_11_34 ++ ix10_11_35)) ++ (ix10_11_36 ++ (ix10_11_37 ++ ix10_11_38))))))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04cover10 : checkedIndexMask or04ids10 = 2^1472-1 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04level10 : monoBlock or04forest 10 0 1472 = true :=
  checkedByMask or04ids10 (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp10_10_0) (fromBatch bp10_10_1)) (checkedListAppend (fromBatch bp10_10_2) (checkedListAppend (fromBatch bp10_10_3) (fromBatch bp10_10_4)))) (checkedListAppend (checkedListAppend (fromBatch bp10_10_5) (checkedListAppend (fromBatch bp10_10_6) (fromBatch bp10_10_7))) (checkedListAppend (fromBatch bp10_11_0) (checkedListAppend (fromBatch bp10_11_1) (fromBatch bp10_11_2))))) (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp10_11_3) (checkedListAppend (fromBatch bp10_11_4) (fromBatch bp10_11_5))) (checkedListAppend (fromBatch bp10_11_6) (checkedListAppend (fromBatch bp10_11_7) (fromBatch bp10_11_8)))) (checkedListAppend (checkedListAppend (fromBatch bp10_11_9) (checkedListAppend (fromBatch bp10_11_10) (fromBatch bp10_11_11))) (checkedListAppend (fromBatch bp10_11_12) (checkedListAppend (fromBatch bp10_11_13) (fromBatch bp10_11_14)))))) (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp10_11_15) (checkedListAppend (fromBatch bp10_11_16) (fromBatch bp10_11_17))) (checkedListAppend (fromBatch bp10_11_18) (checkedListAppend (fromBatch bp10_11_19) (fromBatch bp10_11_20)))) (checkedListAppend (checkedListAppend (fromBatch bp10_11_21) (checkedListAppend (fromBatch bp10_11_22) (fromBatch bp10_11_23))) (checkedListAppend (fromBatch bp10_11_24) (checkedListAppend (fromBatch bp10_11_25) (fromBatch bp10_11_26))))) (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp10_11_27) (checkedListAppend (fromBatch bp10_11_28) (fromBatch bp10_11_29))) (checkedListAppend (fromBatch bp10_11_30) (checkedListAppend (fromBatch bp10_11_31) (fromBatch bp10_11_32)))) (checkedListAppend (checkedListAppend (fromBatch bp10_11_33) (checkedListAppend (fromBatch bp10_11_34) (fromBatch bp10_11_35))) (checkedListAppend (fromBatch bp10_11_36) (checkedListAppend (fromBatch bp10_11_37) (fromBatch bp10_11_38))))))) or04cover10

def or04ids11 : List Nat := ((((((ix11_9_0 ++ ix11_10_0) ++ (ix11_10_1 ++ ix11_11_0)) ++ ((ix11_11_1 ++ ix11_11_2) ++ (ix11_11_3 ++ (ix11_11_4 ++ ix11_11_5)))) ++ (((ix11_11_6 ++ ix11_11_7) ++ (ix11_11_8 ++ ix11_11_9)) ++ ((ix11_11_10 ++ ix11_11_11) ++ (ix11_11_12 ++ (ix11_11_13 ++ ix11_11_14))))) ++ ((((ix11_11_15 ++ ix11_11_16) ++ (ix11_11_17 ++ ix11_11_18)) ++ ((ix11_11_19 ++ ix11_11_20) ++ (ix11_11_21 ++ (ix11_11_22 ++ ix11_11_23)))) ++ (((ix11_11_24 ++ ix11_11_25) ++ (ix11_11_26 ++ ix11_11_27)) ++ ((ix11_11_28 ++ ix11_12_0) ++ (ix11_12_1 ++ (ix11_12_2 ++ ix11_12_3)))))) ++ (((((ix11_12_4 ++ ix11_12_5) ++ (ix11_12_6 ++ ix11_12_7)) ++ ((ix11_12_8 ++ ix11_12_9) ++ (ix11_12_10 ++ (ix11_12_11 ++ ix11_12_12)))) ++ (((ix11_12_13 ++ ix11_12_14) ++ (ix11_12_15 ++ ix11_12_16)) ++ ((ix11_12_17 ++ ix11_12_18) ++ (ix11_12_19 ++ (ix11_12_20 ++ ix11_12_21))))) ++ ((((ix11_12_22 ++ ix11_12_23) ++ (ix11_12_24 ++ ix11_12_25)) ++ ((ix11_12_26 ++ ix11_12_27) ++ (ix11_12_28 ++ (ix11_12_29 ++ ix11_12_30)))) ++ (((ix11_12_31 ++ ix11_12_32) ++ (ix11_12_33 ++ (ix11_12_34 ++ ix11_12_35))) ++ ((ix11_12_36 ++ ix11_12_37) ++ (ix11_12_38 ++ (ix11_12_39 ++ ix11_12_40)))))))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04cover11 : checkedIndexMask or04ids11 = 2^2268-1 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04level11 : monoBlock or04forest 11 0 2268 = true :=
  checkedByMask or04ids11 (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp11_9_0) (fromBatch bp11_10_0)) (checkedListAppend (fromBatch bp11_10_1) (fromBatch bp11_11_0))) (checkedListAppend (checkedListAppend (fromBatch bp11_11_1) (fromBatch bp11_11_2)) (checkedListAppend (fromBatch bp11_11_3) (checkedListAppend (fromBatch bp11_11_4) (fromBatch bp11_11_5))))) (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp11_11_6) (fromBatch bp11_11_7)) (checkedListAppend (fromBatch bp11_11_8) (fromBatch bp11_11_9))) (checkedListAppend (checkedListAppend (fromBatch bp11_11_10) (fromBatch bp11_11_11)) (checkedListAppend (fromBatch bp11_11_12) (checkedListAppend (fromBatch bp11_11_13) (fromBatch bp11_11_14)))))) (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp11_11_15) (fromBatch bp11_11_16)) (checkedListAppend (fromBatch bp11_11_17) (fromBatch bp11_11_18))) (checkedListAppend (checkedListAppend (fromBatch bp11_11_19) (fromBatch bp11_11_20)) (checkedListAppend (fromBatch bp11_11_21) (checkedListAppend (fromBatch bp11_11_22) (fromBatch bp11_11_23))))) (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp11_11_24) (fromBatch bp11_11_25)) (checkedListAppend (fromBatch bp11_11_26) (fromBatch bp11_11_27))) (checkedListAppend (checkedListAppend (fromBatch bp11_11_28) (fromBatch bp11_12_0)) (checkedListAppend (fromBatch bp11_12_1) (checkedListAppend (fromBatch bp11_12_2) (fromBatch bp11_12_3))))))) (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp11_12_4) (fromBatch bp11_12_5)) (checkedListAppend (fromBatch bp11_12_6) (fromBatch bp11_12_7))) (checkedListAppend (checkedListAppend (fromBatch bp11_12_8) (fromBatch bp11_12_9)) (checkedListAppend (fromBatch bp11_12_10) (checkedListAppend (fromBatch bp11_12_11) (fromBatch bp11_12_12))))) (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp11_12_13) (fromBatch bp11_12_14)) (checkedListAppend (fromBatch bp11_12_15) (fromBatch bp11_12_16))) (checkedListAppend (checkedListAppend (fromBatch bp11_12_17) (fromBatch bp11_12_18)) (checkedListAppend (fromBatch bp11_12_19) (checkedListAppend (fromBatch bp11_12_20) (fromBatch bp11_12_21)))))) (checkedListAppend (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp11_12_22) (fromBatch bp11_12_23)) (checkedListAppend (fromBatch bp11_12_24) (fromBatch bp11_12_25))) (checkedListAppend (checkedListAppend (fromBatch bp11_12_26) (fromBatch bp11_12_27)) (checkedListAppend (fromBatch bp11_12_28) (checkedListAppend (fromBatch bp11_12_29) (fromBatch bp11_12_30))))) (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp11_12_31) (fromBatch bp11_12_32)) (checkedListAppend (fromBatch bp11_12_33) (checkedListAppend (fromBatch bp11_12_34) (fromBatch bp11_12_35)))) (checkedListAppend (checkedListAppend (fromBatch bp11_12_36) (fromBatch bp11_12_37)) (checkedListAppend (fromBatch bp11_12_38) (checkedListAppend (fromBatch bp11_12_39) (fromBatch bp11_12_40)))))))) or04cover11

def or04ids12 : List Nat := (((ix12_10_0 ++ (ix12_10_1 ++ ix12_11_0)) ++ (ix12_11_1 ++ (ix12_11_2 ++ ix12_11_3))) ++ ((ix12_11_4 ++ (ix12_11_5 ++ ix12_12_0)) ++ ((ix12_12_1 ++ ix12_12_2) ++ (ix12_12_3 ++ ix12_12_4))))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04cover12 : checkedIndexMask or04ids12 = 2^355-1 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04level12 : monoBlock or04forest 12 0 355 = true :=
  checkedByMask or04ids12 (checkedListAppend (checkedListAppend (checkedListAppend (fromBatch bp12_10_0) (checkedListAppend (fromBatch bp12_10_1) (fromBatch bp12_11_0))) (checkedListAppend (fromBatch bp12_11_1) (checkedListAppend (fromBatch bp12_11_2) (fromBatch bp12_11_3)))) (checkedListAppend (checkedListAppend (fromBatch bp12_11_4) (checkedListAppend (fromBatch bp12_11_5) (fromBatch bp12_12_0))) (checkedListAppend (checkedListAppend (fromBatch bp12_12_1) (fromBatch bp12_12_2)) (checkedListAppend (fromBatch bp12_12_3) (fromBatch bp12_12_4))))) or04cover12

def or04ids13 : List Nat := (ix13_10_0 ++ ix13_11_0)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04cover13 : checkedIndexMask or04ids13 = 2^22-1 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04level13 : monoBlock or04forest 13 0 22 = true :=
  checkedByMask or04ids13 (checkedListAppend (fromBatch bp13_10_0) (fromBatch bp13_11_0)) or04cover13

def or04ids14 : List Nat := ix14_10_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04cover14 : checkedIndexMask or04ids14 = 2^1-1 := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma or04level14 : monoBlock or04forest 14 0 1 = true :=
  checkedByMask or04ids14 (fromBatch bp14_10_0) or04cover14

theorem or04checked : monoCheckedTables or04forest 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact or04level8
  · exact or04level9
  · exact or04level10
  · exact or04level11
  · exact or04level12
  · exact or04level13
  · exact or04level14

end PEqualNP.Outside.L_meta_1922

namespace PEqualNP.Outside.L_meta_1922

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma completed (anchored : MonoImpossible graph 14 (inputs ++ [seed04]).toFinset) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size := by
  intro C hm hrows
  by_contra hsmall
  have hs : C.size ≤ 14 := by omega
  have htests : ∀ n ∈ Boundary.rows, Boundary.value C (Boundary.bits n) = decide (n ∈ Boundary.positives) := hrows
  have full := Boundary.boundary_complete C hm htests
  have computes : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y ++ [y 0 || y 4]) = edge y := full
  obtain ⟨k, hk, hrun⟩ := initial_live04 C hm computes
  rcases hrun with free | used
  · exact dead_start (before_sound known383 valid383) geomdead tablesdead k 0 (by omega) free
  · exact anchored k (by omega) used

end PEqualNP.Outside.L_meta_1922

theorem PEqualNP.Outside.L_meta_1922 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size := by
  exact PEqualNP.Outside.L_meta_1922.completed
    (PEqualNP.Outside.L_meta_1922.anchored_excluded PEqualNP.Outside.L_meta_1922.or04checked)
