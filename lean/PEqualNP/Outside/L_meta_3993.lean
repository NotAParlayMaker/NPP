import PEqualNP.Defs
-- Circuit normalization and the induced graph bounds are adapted from L-meta-1667.
namespace PEqualNP.Outside.L_meta_3993
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
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

lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
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

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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


end PEqualNP.Outside.L_meta_3993

namespace PEqualNP.Outside.L_meta_3993
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def anchor := inputs.getD 0 zero ||| inputs.getD 3 zero
def lowExample (i : Fin 9) : Row := Fin.ofNat 512 ([10, 1, 2, 5, 1, 1, 2, 4, 8].getD i.val 0)
def highExample (i : Fin 9) : Row := Fin.ofNat 512 ([11, 3, 6, 13, 17, 33, 66, 132, 264].getD i.val 0)

theorem anchor_witness : ∀ i : Fin 9,
    (bit (lowExample i) graph != bit (highExample i) graph) &&
    ((inputs++[anchor]).all fun w => w == inputs.getD i.val zero ||
      bit (lowExample i) w == bit (highExample i) w) = true := by decide +kernel

theorem anchor_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[anchor]) :
    S=inputs.toFinset ∨ S=(inputs++[anchor]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := anchor_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (lowExample i) (highExample i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : anchor ∈ S
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


theorem anchor_bit (r : Row) : bit r anchor = (sample r 0 || sample r 3) := by
  simp [anchor,bit,sample,BitVec.getLsbD_or]

theorem codes_v (x : Fin 9 → Bool) :
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
      (fun n => x (Fin.ofNat 9 (n / 10)) && x (Fin.ofNat 9 (n % 10))) = edge x := by
  simp only [edge,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  rfl

end PEqualNP.Outside.L_meta_3993

namespace PEqualNP.Outside.L_meta_3993
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def finiteW (w : List Sig) (z : Sig) (limit : Nat) : Prop :=
  (1 ≤ limit ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma binFew {w a b} (d : Bool) (limit : Nat) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ finiteW w (bin d a b) limit := by
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

lemma gateFew (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ finiteW w (gv w g) (g.op.eval [false]).toNat := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ finiteW w (neg a) 1 := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨by decide,a,hm,hp,rfl⟩)
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
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := finiteW w (w.getD i zero) (GateOp.and.eval [false]).toNat) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := finiteW w (w.getD i zero) (GateOp.or.eval [false]).toNat) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using binFew false (GateOp.and.eval [false]).toNat (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using binFew true (GateOp.or.eval [false]).toNat (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)


lemma pullFew {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    {limit : Nat} (hz : represented w z ∨ finiteW w z limit) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t+limit ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨room,a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
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
        exact ⟨_,_,_,Nat.le_refl _,by omega,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
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
        exact ⟨_,_,_,Nat.le_refl _,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extractFew (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => g.op.eval [false]) ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hnot,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hc,hu,hT⟩ := pullFew ht (gateFew w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hu,hT⟩
    cases he : g.op.eval [false] <;> simp [List.countP_cons,he] at hc ⊢ <;> omega


def FewImpossible (T : Sig) (cap fuel : Nat) (S : Finset Sig) := ∀ k t, k ≤ cap → t ≤ fuel → ¬Live T k t S

theorem few_suffix (noneLeft : FewImpossible graph 14 1 (inputs++[anchor]).toFinset)
    (C : Circuit) (fan : FanInTwo C) (small : C.size = 14) (nc : C.gates.countP (fun g => g.op.eval [false]) ≤ 1) :
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ edge x := by
  classical
  by_contra! correct
  have value : (execute C.gates (inputs++[anchor])).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r ((execute C.gates (inputs++[anchor])).getD C.output zero) = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1),
      List.map_append,List.map_singleton,anchor_bit,←sampled,edge_table]
    exact correct (sample r)
  have present := get_rep (execute C.gates (inputs++[anchor])) C.output
  rw [value] at present
  obtain ⟨k,t,S,hk,nt,run,sub⟩ := extractFew C.gates _ fan graph_proper
    (present.resolve_right (fun e => e graph_proper))
  have budget : k ≤ 14 := by change C.gates.length = 14 at small; omega
  rcases anchor_roots run sub with eq|eq
  · exact dead_start (before_sound known383 valid383) geomdead tablesdead k t budget (eq ▸ run)
  · exact noneLeft k t budget (by omega) (eq ▸ run)

theorem enumFew {T : Sig} {cap fuel : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : 0 < fuel → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      FewImpossible T (cap-1) (fuel-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      FewImpossible T (cap-1) fuel (childTwo ws a b d ka kb).toFinset) :
    FewImpossible T cap fuel ws.toFinset := by
  classical
  intro k t hk nt h
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
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) (by omega) (eq.symm ▸ tail)
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
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (by omega) (eq.symm ▸ tail)

end PEqualNP.Outside.L_meta_3993

namespace PEqualNP.Outside.L_meta_3993

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

theorem runWidth {R} {g : Wire R} {k ws} (h : Run g k ws) : ws.length ≤ k+1 := by
  induction h with
  | stop => simp
  | perm p _ ih => rwa [←p.length_eq]
  | one keep _ ih => cases keep <;> simp [kept] at ih ⊢ <;> omega
  | two op ka kb _ ih => cases ka <;> cases kb <;> simp [kept] at ih ⊢ <;> omega

theorem runWeight {R} {goal : Wire R} {k ws} (run : Run goal k ws)
    (tight : ws.length = k+1) (v : Wire R → Nat)
    (sub : ∀ op a b, v (combine op a b) ≤ v a + v b) : v goal ≤ (ws.map v).sum := by
  induction run with
  | stop => simp
  | perm p h ih => rw [←(p.map v).sum_eq]; exact ih (p.length_eq.trans tight)
  | one keep h ih => have size := runWidth h; cases keep <;> simp [kept] at size tight <;> omega
  | @two n a b rest op ka kb h ih =>
    have size := runWidth h
    cases ka <;> cases kb <;> simp [kept] at size tight <;> try omega
    have hh := ih (by simp [kept]; omega)
    simp [kept] at hh ⊢
    have hsub := sub op a b
    omega

abbrev widthKW : Nat := 40
abbrev bandKW : Nat := 0xffffffffff
abbrev LevKW := Nat × Nat × Nat

def laneKW (o x : Nat) := (x >>> o) &&& bandKW
def levelsKW (x : Decor) : LevKW :=
  let p := x.2.1.toNat
  let q := x.2.2.toNat
  let a := laneKW 0 p
  let b := laneKW widthKW p
  let c := laneKW (2*widthKW) p
  let d := laneKW 0 q ^^^ bandKW
  let e := laneKW widthKW q ^^^ bandKW
  let f := laneKW (2*widthKW) q ^^^ bandKW
  ((d &&& (b ||| c)) ||| (a &&& (e ||| f)),
   (d &&& b &&& c) ||| (a &&& e &&& f),
   a &&& d &&& b &&& c &&& e &&& f)

def pointWeights (r s : Fin 768 → Row) (i : Fin widthKW) (w : Wire Row) :=
  let i0 : Fin 768 := ⟨i.val,by have hiw := i.isLt; simp only [widthKW] at *; omega⟩
  let i1 : Fin 768 := ⟨widthKW+i.val,by have hiw := i.isLt; simp only [widthKW] at *; omega⟩
  let i2 : Fin 768 := ⟨2*widthKW+i.val,by have hiw := i.isLt; simp only [widthKW] at *; omega⟩
  value6 (w (r i0)) (w (r i1)) (w (r i2)) (w (s i0)) (w (s i1)) (w (s i2))

theorem band_bit (i : Fin widthKW) : bandKW.testBit i.val = true := by
  change (2^widthKW-1).testBit i.val = true
  simp [i.isLt]

theorem laneKW_bit (o x : Nat) (i : Fin widthKW) :
    (laneKW o x).testBit i.val = x.testBit (o+i.val) := by
  simp only [laneKW,Nat.testBit_and,Nat.testBit_shiftRight,band_bit,Bool.and_true,Nat.add_comm]

theorem gatesKW : ∀ a b c d e f : Bool,
    ((!d && (b || c)) || (a && (!e || !f))) = decide (1 ≤ value6 a b c d e f) ∧
    ((!d && b && c) || (a && !e && !f)) = decide (2 ≤ value6 a b c d e f) ∧
    (a && !d && b && c && !e && !f) = decide (3 ≤ value6 a b c d e f) := by decide +kernel

theorem levelsKW_bits {r s} {x : Decor} (good : faithful r s x) (i : Fin widthKW) :
    (levelsKW x).1.testBit i.val = decide (1 ≤ pointWeights r s i (observe x.1)) ∧
    (levelsKW x).2.1.testBit i.val = decide (2 ≤ pointWeights r s i (observe x.1)) ∧
    (levelsKW x).2.2.testBit i.val = decide (3 ≤ pointWeights r s i (observe x.1)) := by
  have hp (j : Fin 768) : x.2.1.toNat.testBit j.val = observe x.1 (r j) := by
    change x.2.1.getLsbD j.val = _
    rw [good]; apply ofRows_bit
  have hn (j : Fin 768) : x.2.2.toNat.testBit j.val = observe x.1 (s j) := by
    change x.2.2.getLsbD j.val = _
    rw [good]; apply ofRows_bit
  have h0 : i.val < 768 := by have hiw := i.isLt; simp only [widthKW] at *; omega
  have h1 : widthKW+i.val < 768 := by have hiw := i.isLt; simp only [widthKW] at *; omega
  have h2 : 2*widthKW+i.val < 768 := by have hiw := i.isLt; simp only [widthKW] at *; omega
  simp only [levelsKW,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,laneKW_bit,band_bit,
    Bool.xor_true,Nat.zero_add,pointWeights]
  rw [hp ⟨_,h0⟩,hp ⟨_,h1⟩,hp ⟨_,h2⟩,hn ⟨_,h0⟩,hn ⟨_,h1⟩,hn ⟨_,h2⟩]
  exact gatesKW _ _ _ _ _ _

def mergeKW (l r : LevKW) : LevKW :=
  (l.1 ||| r.1, l.2.1 ||| r.2.1 ||| (l.1 &&& r.1),
   l.2.2 ||| r.2.2 ||| (l.1 &&& r.2.1) ||| (l.2.1 &&& r.1))
def totalKW : List Decor → LevKW
  | [] => (0,0,0)
  | x::ws => mergeKW (levelsKW x) (totalKW ws)
theorem totalKW_bits {r s} (ws : List Decor) (good : ∀ x ∈ ws, faithful r s x) (i : Fin widthKW) :
    let v := (ws.map (fun x => pointWeights r s i (observe x.1))).sum
    (totalKW ws).1.testBit i.val = decide (1 ≤ v) ∧
    (totalKW ws).2.1.testBit i.val = decide (2 ≤ v) ∧
    (totalKW ws).2.2.testBit i.val = decide (3 ≤ v) := by
  induction ws with
  | nil => simp [totalKW]
  | cons x ws ih =>
    obtain ⟨i1,i2,i3⟩ := ih (fun u hu => good u (List.mem_cons_of_mem _ hu))
    obtain ⟨j1,j2,j3⟩ := levelsKW_bits (good _ List.mem_cons_self) i
    simp only [totalKW,mergeKW,Nat.testBit_or,Nat.testBit_and,j1,j2,j3,i1,i2,i3,
      List.map_cons,List.sum_cons]
    refine ⟨Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_, Bool.eq_iff_iff.mpr ?_⟩ <;>
      simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] <;> omega

def passesKW (ws : List Decor) := ((totalKW ws).2.2 &&& bandKW) == bandKW
theorem scoreNeeded {r s T ws k t} (pairs : properPairs T r s) (faith : ∀ a ∈ ws, faithful r s a)
    (hn : (ws.map Prod.fst).Nodup) (tight : ws.length = k+1)
    (run : Live T k t (ws.map Prod.fst).toFinset) : passesKW ws = true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < widthKW
  · let j : Fin widthKW := ⟨i,hi⟩
    have rr := list_run run _ hn rfl
    have sub (op : Bool) (a b : Wire Row) :
        pointWeights r s j (combine op a b) ≤ pointWeights r s j a + pointWeights r s j b := by
      cases op
      · exact value6_and _ _ _ _ _ _ _ _ _ _ _ _
      · exact value6_or _ _ _ _ _ _ _ _ _ _ _ _
    have sum := runWeight rr (by simpa using tight) (pointWeights r s j) sub
    have val : pointWeights r s j (observe T) = 3 := by
      simp only [pointWeights,observe, (pairs _).1,(pairs _).2]
      decide
    rw [val] at sum
    simp only [List.map_map,Function.comp_def] at sum
    have got := (totalKW_bits ws faith j).2.2
    simp only [decide_eq_true sum] at got
    change (_ && _) = _
    rw [show (totalKW ws).2.2.testBit i = true from got]
    simp
  · have hb : bandKW.testBit i = false := by
      change (2^widthKW-1).testBit i = false
      simp [hi]
    simp [hb]

end PEqualNP.Outside.L_meta_3993

namespace PEqualNP.Outside.L_meta_3993

def pairsP : Nat → Bits
  | 0 => 0x24302355591029c0b82b247c5e22d00de1d08315220fd64225701ac399d4b13a784d69220884b1b4e09427caa7743e80c210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f00886959e51000c10004a1080a08e1
  | 1 => 0x89ea8083c908404e81704784635c1b6ebc4033d8ae90c6400482b0e1c6d8316a60481c6717bb881dc31c1974481f0c66dbe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279c63551b1c50000188820e005491924
  | 2 => 0x98211e228a7ed280c4d7af124088727b2183370085e7033acb622648ea057e053a85e92bac5190c6aaca6fb1b78c90c228421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0341692241a408120510e5c13123514
  | 3 => 0xb8ddcb40c423d9e36001a4c01c40dea008b47c6a0aa2caaebcbc598300324390440a900cc6a34e926b8534c92080b1994484208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc4802948840208846b0226d1bc028e2c38
  | 4 => 0x2684577cb0f01f6a0b488ae42003c92f606c070d1d0a9bca16a9fb25e7eb008595473abc6879ed08009b5238d44d215f47ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff908880219000400009c1c8420000008800100
  | 5 => 0x5530b94a2c5ab4142ca611bf31f174c79659092d7c7c16036b5086801706b8b9ea702388ad4702721878809a4421da3d410842084210822109042108882108917fffffc00802010fffffffffe00010100406d93cea222b181ca8e101c12042c3
  | 6 => 0x120574a65464269234bae982ce2ec6852f7e82d86111310a31582c3b64d5274d899a47f099c030260d66468902c45718b61084108421044213ffffff004001007ffffffffffffff0100400040102000020e2a1a8c8286185e948280234518000
  | 7 => 0x73b88589b3482405b700983616a4249db94238318485d9bd703906628a00e6621df552045158351c5c71bb465710ae07c3ffffff0002080003ffffffffffffffa108211000041004208821085000002100d9620206d5dd723217d70010710002
  | 8 => 0x2fee70202095147193dc2e3ceeb708758004d68681c9208413c4a03e065d580e5da4e9100e1e626054021040412b42903bfffffffffffffffe084210008210004210422110882228411042108004210000000643151222e647d71a02e004c208
  | _ => 0
def pairsN : Nat → Bits
  | 0 => 0x2010221508100810184b04244a22400d01c082002006534021300802114465025805600008442110c004069aac04280040007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07900002141c090a8a08f90082e3511c
  | 1 => 0x897a0082810a004c0840408c004c186c240032160c8080c00480d0218608802a40080026563908804214181440130024d3e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038226a0ccaa3e0454511040e7014a2c1
  | 2 => 0xe200ad45a80009427014000000302810500a060020acb42245c40057c042810c9c9a8408020804ae420b08c004208000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0498580110c1c923264122084a0400a
  | 3 => 0x9051c1c0d52380403001c0000c4006000826584002008020202c4881001001a0000a140044834a922b85004b020091280400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc00094020a2cf12100cc0ae80069080ae1
  | 4 => 0x6584141000503e220a200ba42001c93f2041070d05021ac81180372456e90005804528b928281008001812145405205343ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff80000006bfdf5c302d6f531f5069d14042000
  | 5 => 0x9000954a02061410082301a1111150c30621400d3c3c0203094094005402b80d8a10008805430062000c84920401803c400000000000000000000000000000007fffffc00000000fffffffffe0000000004d058828c114d130420226191ca820
  | 6 => 0x10007465546524121422b9020c2142830a7e80486101112ba959041060942745099207c8814010268c40068992c47118200000000000000003fffffe000000007ffffffffffffff0000000000000000000dd15f3245017b0b8caeae181a84828
  | 7 => 0x67b80081f1082025b70098160aa4241cf942b0700281f9f430b102228a00026015ee12044238351d68210b4403522e0193fffffe0000000003ffffffffffffff8000000000000000000000000000000000b27a77c632e32cc599ed59620217d5
  | 8 => 0xfa400102090002181dc061ce282083c80800282808020801282202e026140025404e0100a14200050021800683a02809bfffffffffffffffc00000000000000000000000000000000000000000000000022e804d30ec80e0335150006431512
  | _ => 0
def automWords : Array (List Nat) := #[[],[81,130,118],[48,33,133,118],[48,129,82]]

def cubeInfos : Array ColumnInfo := #[(128,0,383,0,13),(64,0,447,0,13),(16,0,495,0,13),(256,0,255,0,12),(32,0,479,0,12),(8,0,503,0,12),(4,0,507,0,12),(2,0,509,0,12),(1,0,510,0,12),(320,0,191,0,11),(192,0,319,0,11),(160,0,351,0,11),(144,0,367,0,11),(132,0,379,0,11),(80,0,431,0,11),(66,0,445,0,11),(24,0,487,0,11),(17,0,494,0,11),(384,0,127,0,9),(288,0,223,0,9),(264,0,247,0,9),(136,0,375,0,9),(130,0,381,0,9),(129,0,382,0,9),(96,0,415,0,9),(65,0,446,0,9),(33,0,478,0,9),(18,0,493,0,9),(12,0,499,0,9),(6,0,505,0,9),(3,0,508,0,9),(448,0,63,0,8),(416,0,95,0,8),(352,0,159,0,8),(336,0,175,0,8),(328,0,183,0,8),(280,0,231,0,8),(194,0,317,0,8),(161,0,350,0,8),(145,0,366,0,8),(140,0,371,0,8),(134,0,377,0,8),(82,0,429,0,8),(70,0,441,0,8),(67,0,444,0,8),(49,0,462,0,8),(19,0,492,0,8),(322,0,189,0,8),(164,0,347,0,8),(25,0,486,0,8),(260,0,251,0,8),(257,0,254,0,8),(40,0,471,0,8),(10,0,501,0,8),(5,0,506,0,8),(480,0,31,0,7),(198,0,313,0,7),(177,0,334,0,7),(156,0,355,0,7),(324,0,187,0,7),(321,0,190,0,7),(296,0,215,0,7),(289,0,222,0,7),(273,0,238,0,7),(268,0,243,0,7),(193,0,318,0,7),(162,0,349,0,7),(146,0,365,0,7),(133,0,378,0,7),(98,0,413,0,7),(74,0,437,0,7),(56,0,455,0,7),(35,0,476,0,7),(21,0,490,0,7),(14,0,497,0,7),(7,0,504,0,7),(0,128,347,36,10),(0,64,189,258,10),(256,64,189,2,9),(32,128,347,4,9),(0,16,486,9,10),(8,16,486,1,9),(4,128,347,32,9),(36,128,347,0,8),(2,64,189,256,9),(258,64,189,0,8),(1,16,486,8,9),(9,16,486,0,8)]

def columnCount : Nat := 88
def disp14 (i : Nat) := (0x1 >>> (1*i)) &&& 0x1
def link14 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def programRaw14 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def program14 (i : Nat) := (programRaw14 i <<< 10) ||| 304
def getProgram14 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def live14 (i : Nat) := (0x7ff >>> (11*i)) &&& 0x7ff
def rules14 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def span14 (i : Nat) := (0xb >>> (4*i)) &&& 0xf
def pieces14 (i : Nat) := (0xa9876543210 >>> (4*i)) &&& 0xf
def atom14 (i : Nat) := (0x304021006808107110508 >>> (8*i)) &&& 0xff
def disp13 (i : Nat) := (0x520080000705028389747b001208090504014a560400008754180781500a034b004807 >>> (8*i)) &&& 0xff
def link13 (i : Nat) := (0x6258421270181308598a3081cb9020ba00314b214ab1829a69b810b0aa63c2389b4849a0b95b28220a796040508878bbc0986861d0c82391a84183d15a11ca4380a9ab9971c9 >>> (8*i)) &&& 0xff
def programRaw13 (i : Nat) := (0x12558951441214817658081144215916150491a2169525911251350e99 >>> (10*i)) &&& 0x3ff
def program13 (i : Nat) := (programRaw13 i <<< 10) ||| 304
def getProgram13 (i : Nat) := (0x5ab49ca307b9a462cca49507018a418820 >>> (5*i)) &&& 0x1f
def live13 (i : Nat) := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffebffbffbfffdffeffefbfe >>> (12*i)) &&& 0xfff
def rules13 (i : Nat) := (0x6b38bdab49ca307b9ac5a928398a418820 >>> (5*i)) &&& 0x1f
def span13 (i : Nat) := (0x27f497463b18645f907641baf67b986c5bb156c4fb128b44acfcb3a28d88329ca53233072d16b044b0d9c287071800e >>> (14*i)) &&& 0x3fff
def pieces13 (i : Nat) := (0x1c6e6365b6c0e05242c949a79944139a35d957ac386052465359104e7263650e050b65f4da4854413a584b7dc6e768066a4c30923c596181471a343a644d949104e96171a02410b2437814993c535d9668605244e86d644139a84074b6560df0674cf1618142df35d44149c3a58147cd99344149a39c6a22d94cd0d24413a586050d91344149939a8dd2d958d4133ce6a274b64d4d644138d86051d2df4414ce71a2d94cd4123ce2c93434013ce2d31434803a18147cb78175139b59a0c06527052c971b59a1590d20403071942c40585d345638c1c42c954309004f38c1c650b1014d244e2c90d004f38508b4d244e2c94033ce34c2ca2481c61440c2040 >>> (6*i)) &&& 0x3f
def atom13 (i : Nat) := (0xa630158783a8a1622e068d0720a09028341d1283402110c5526a04a11047a1e221008c20ae03c000302010200810061881e0a05 >>> (9*i)) &&& 0x1ff
def disp12 (i : Nat) := (0x147980010060008cb01c0020000007870000090006730000577a000000100f5d30025990067aa4f158d00407100f0000000081908ee00000400000601469d0037f65c380859e00800000000000000100051a6860048db0010000000008f759565200d85c67401700100000201401a0047857ee0090050000210030360030000000056130067e78837780030004ec00082952500078801900200c87d00000602d00251d7bb00004f00b7480060020320020050010180007a200186000300000600100000300b4c701100662500002602900a7765a70024c40000024f300500000900200600300000074d00000587701678104d0000000010010020927808060007ea00000400000d0078c800000700e00065c0275c400e0057f30180030000210000000060000050075b80000280010000020120160000000018530038130005cc00300000275800e00976c00b66800000700000b66e0095967eb79402b0000040050000000070004e300075500000a7907860000008d600269a0036a200100601e0160040028d100a00305101301200000400500203900082d0000015e301200000300f0020000010040000008d00020025e76890007a666901c01700900000000000500f00000071c00200000301200000c8d57a300080b0200004ea5c800200003269f65d01c73d0000057c90007d10007d500000a0047b57910168ea00100400000000072f7be00b66b00001d01e00067e5cb00a5520287650226a800000700000000000000076e0005f20025e902000052100900e4ce77479b03100100700000f00000000000000000300001200c00001900000564e0120005128ac00000101c0007d000066007800300700500651700a00000083500000000059188d6b400000500200400000500202278f0047730000058ad0010008f90000268960038c700000055465b72300b00600301800082600100b8d900101100a0575bf00000700a6870005d70030035a60020000045190157960020050010000027d600085f00f00006200600000100e58600102e01b0030000115ea84900200300100100200200066f0000000000320000000010000004a500400074e0040006a411e0000000148f200003c01e00000086378e0030010030000710005ca00000000265e00001000700174a00800c00500c00800000800600100000d0067890006015fb0068757f0000 >>> (12*i)) &&& 0xfff
def link12Bits : Nat → Nat
  | 0 => 0xa240d701b838686c2f884c410a02a032172d20e44f08fa79049a9a60f383254a686b31a20e91b40970cd81a8a6002006a233cb58d9d505012cb7c2266bba4502881c04e3a73d2560e9435a4492700d0024a65103ad6b4162305874c4461e87cc2e40800b2089910c14141a24e88f20de31787844501122f806dc43009e0d5194804c59e09e88b8040a2a12b81802f01c841107bc02ad9d09e06702d620f290872942e0d80f831491a61c912bb9419c291704983980a21474ad93b82cc82709d872008409c07b23281508eb09704f52288ff09b2208a5e14248bb7f0220597096074c244161313863c43659204617c9322e4d2c5190424a4af6e820913f4a4d0fd035c2149c4460803408e0222ef01f10f40eb6c809084305f32e0a464ac424b0cf81413f640a6d4824034ac102df8041aaa0c24fc837c26a1f8004076849ec134ae80cc0d218011892a507e804326b12dc8497106293ed22e631103a7000f649f076103caa861120223c411241106e24984609471263905c7e01a033a1d41e00f9488b144b2043d62735eca4858a09812ec23e03470835a035865445708908fec5209b88d1a8004760a98e0afa07242b83488a89af0d4066945253221f03e98e00ea2f8b269c16c4901ea3341c45a011da51406410b6b19734c1e255063074884607d328276c46a06340206fc9164bf06a932594e4d664394a80e40a6040214c03c46a02122c0b9cd4a30f81000d01dc0d804a52c0a540ab81789d00cf10b95d82184d202a026839c0a40098534b1824571f03800ee4cc10f05d483a09960ca62c092430223061c08ac3a2ab16f007263d01a88f034e61761c030d0f84dd10c86b414ed8f4b5019c24e81000e06183cc1ee07985a0ad452311f95202f615a052117dc761244fca5304788422ac87f947cc7b0d626388d612042d9089ae82450e1846cbdc4f841706cd3461d2041a4e81f045623892ad2ce1a46d887299100e8300094d9669ea102134d0000f807d84301ecc3125108d038c048124a148c52dcf04e88742480b5021b51923cc4171ca51cbe40d62e317541562090898194876132671039006224f080806432c123209093023a9694d21809a76d912db02f40d259507181ccb6810e12230c917acc461788a43c8dab440850cc465dd24723443d20604a6367dc4096d09390ed1f48440a4192814e17c20a82643d815748e240c00623209689104862490cdb5f0472105495b2bcb28c0e07221998fe90201d00a407c4b611d04a1b02e237090575146d3203b32b4c105b311307c4c601342120160850096046a2c18be48a514a301a9690742e973448c62b04604b5abed610ec38cc1b69fb4ffa5443fc25148e332111c184129802db26e144bb26f91960317012375c6ac7f127018d92815c48808152960b912803f10d4c840f9b88000e0ef4708
  | 1 => 0x2c006018ca749656a3b450ac4406119b3c096a43c11b27ac22c0ac060037c8aa254637875c34816011791302120cc32a1435b048e9116152514c595485054ca1a04966838189881c64f10664056d672a618b14700fa06381348be0be50016acb62d8d1168879b424ef6ec808ca30daf2eb354948016e07280948da85c058256c16251e03603b046c1d85109920c6e002080217d2b011a015960419e9fd0d1b8013689cb07fb5249b062749fb1c50888794450625c2211509423008da139013b3f097401f0fe12e13301200d694888a65f5028082100a07808288183a80b666e9675b54e1626a86a90948796c7989dc040ad40c0099c0820e03e08953a88a12c984ac9cec20256876008cda70e3b18914a13c41b862d92c8572ecb20c8aecf264c97e49680bd20587dc0b289941127e08e0cb70db918839806301a00412ee1c964d892dbfa64e60295bc1944a32cda70822216750f92b5b44cfc0b2854489689f6ebb19c9660ce00b812096407a23f111ca2e8da6aa91c0bda05e0ff81d14125f6108024198892b43303dc1d88fe42210f0b6a4426a6264cb881372a019584a203d2dc80248021964f1b42c2269d12c4042044401550695241be9c54a8260c0601630f402803fc60169da5d50ba0fd52035e40eaa0b11e10fc1b20ce69f046c26658a42e25e829c1034e6a6a81bec142e01804284c9212492999b856c06213312bc9060e286e039c9b86dd82c424e21a09eb2a01ce1dd48597b50962480e414892081540a085c00e68c50750885b6e8b228005d41cc4f22af111942a2522f007bdbc4426510831888e9324ef815d4582414bf061944a12f61b01d4afe1890cc1459b5801b0da83c82842566d586f41da10f10983781da597302285505a88900992bd4505d0305a5984709e50ee83f42e624709611cc40a0980e3805028c1fb0eb2350c8a4f503da4a93ae48865e0958876cfe038880c91298d6a803b995659410b04601cac166d905dc94898510a32e02d21152cb37b49c6a0c0ad15112321f409891ed9e80462ae08a992207708e86e49785e30e0884931044c2a788500b45f452335089de09507926089ca8c04c61308394039032a18511e1c125134689fc5ba0db34c5ba2026016869440e0dc69e919034c8cb2af869126a6230e802a984211c0c9180c1bc9cc6479918438d5e0c706fd008d07104040da4a
  | _ => 0
def link12 (i : Nat) := packedAt link12Bits (13*i) 13
def programRaw12Bits : Nat → Nat
  | 0 => 0x5215d5604556368960061705c560545606192054d2006980585204c52061d10615105d5105c91020523629105c510681255d0815e9622857868d62549715c56261d615d1615d9515c951589516094154941605415c5415d9215d5215452161d6062960695605c960495704856061520595202052054520145235e9105e9255a925691256852528525548811488169162685625d5615c96154961205722858268151608512085161d415d541145425c941205426089154891148915952155121681212142155021164215e9205692014520689695e52560525609516895161c915d491208915c8910658506985614216292068520685696a562691515292161521a2173a2170a21235d6885d288a2110a215055288166885ca8854a8814a8850a8824a8854688146885068824688086885c688486885d949525625255160991565215a525695625252144d23525255a8255c5785e9615a95161d9159591589915499154591569216452154d1358d135e5105e569468525e5624a9755e541649915a921568215a520649105a9235d1695a5494a8515a5915d9916119155191605915c5915c57062520565205a9206452062510565104a9504a910625915e5915659150991505915a5215e960465635e560609435e5205cd13485535691044d835d8496a525125626a551619915d5915d191591914657064573645436111356513609135c51354513485131e92559d715e5615a55146128428825a541125215e15858943461806492061d1362913625135e5135491368913605135c1134a1835cd231252552481525615c572125516456058d7359543551135e9135a913509135a51054d105a9104e9105e481461685e12852591629915e491468985a892680215a5434954354543485436158059513069532a5135891350513680811256168d512815152451680515e9916899162491564916489146892524215d5705d9435d113591130a95328913681136451028579069955c99120592468955cd70649435d9135d513209135811312481069981459228592564212094308553061534c51012451124215c94320543585431454308543619130a553065535251324913029135c913a6562a6521a6525a6551aa981aa978aa982aa985526885da99a6451a64215e6885668864a8864688aa983a648112688aa973a65605a699a6591a6520aa980a6510a6561a2113a2120a215306a99a2143a2140a65134a995569916692166881668515a9926682168c12495535a9495e8812a5515e81262812615535e969291692a5415a9915299148153669105a449125911299150943569135d17968c182a5624e8515282164913281135288152198124915291350d2048113644911251351553245132a525269215a513aa998aa979aa949126995aa9946a9926a8852a99
  | 1 => 0x54962595155cd605d920049535d5205cd206092054920619105d9105951058d1058910605105d12561d625915149515595415894158912449635496061d2058d2058920605205c52028520485200855060d105cd1060910549104c91054510485105d92559125629625d16268162619415d94154541591215491250
  | _ => 0
def programRaw12 (i : Nat) := packedAt programRaw12Bits (20*i) 20
def program12 (i : Nat) := (programRaw12 i <<< 10) ||| 304
def getProgram12 (i : Nat) := (0xe572791c7e371789c3e170781bfdf6f779bbdd6e771b7db6d769b3d96c761afd76b759abd56a54ba8d3e9b4ba4d1e8b43a0cfe7b3b9ccde6b3398cbe5b2b94c9e4b2293c863f1d8dc662f1589c461e2986c2e130782c0e02ff7ebec42377cbddeaf378bbbce1776babfee973b938ae370b7dbadb6cb5daad3686dba60b67b35963164b1a8ac5618bd82075faf576b95b62d6ab358abd5aab54a9d49cf0c79546a14fa75361509a652e9549703415b487751e8cec83299d6fc3389e8b1da250d631c632c11b42a0a2daaf6871b8f2e87bb9a350d3b9b201409fcfa7ae39e45a773a35a0dc2d178379faef9caf5db383d9ea6ed89b4d4570f6a2791224369e233346b0d511331a0283209994c6612f970f4772d964ae55299449e4d259248e452190100ac47299489b1f1e13ca83e27144984b28128931e03160aa5703c76391b8d46631178b456291389446210f87436190b8542611078341609038140600ff7f3f5f8fb7d3e5f0f77b3d5e8f3793c5e0ef773b5d8eb753a464e873b99cae4718d060e270b81bede0e2a1badc6db69b2d819b5dac3618b55a8d369345a0cf67335981665b2992c863b198ac461b086ac11a3017ebe5eaf176ba5cae16eb6112d568b313ac962b057ab8481f56ab156aa54aa038a707a994aa45188144a1500793e9e4ea71369a4ca612e964aa5126110424922901323d1c8d4622d1489120d5108743215088341205007f3f1f4f87b3d1e446783b9d8ea74399c8e270379b8da6c359a8d268338accc653218cc4613017cbc5d2e16cb4592c15cac552a14ca451281009e4e26930964a249200c4723114884321104803f038f80e3d1e0ec74391c0dc6c351a0cc6431180bc5c2d160ac54291409c4c251208c44211007c3c1d0e06c34190c05c2c150a04c24110803c1c0d0602c14090401c0c05020000602008000000 >>> (9*i)) &&& 0x1ff
def live12 (i : Nat) := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff6fff7ffbffdffefff7ff7ffdffffbf7ff7fff7fdffefffbffdffefff7ffbffbffeffffdffefdffeffefffbffbffefff7ff7ffbffefff7ff7ffdffeffefffbffdffefff7ffbffdfffbff7ffbffbffefff7ffbffbffdffefffbffdffefff7ffbffdffeffefff7ffdffeffffdfbffbffdffffdffefbffffbffbfbffbffff7f7ff7ffbffefff7ffbffdffefff7fffefff7ffbffdffefff7ffbffdfefff7fefff7ffdffbffeffeffffdfbfff7fffdfdffdffffbffdffefff7ffbffdffefff7ffbfbfffefbffff7f7ffbfff7fff7effffdfdffffbffdffefff7ffbffdffefff7effffdf7ffbffff7f7ffdffeffff7f7ffbffdffdffefff7ffff7ffbffdffefeffffbffdffefff7ffbffdffeffefdffffbffefffeeffefffbffdffefff7ffbffdffeffefffbfff7fffbffdffefff7ffbffdfbffdffefff7ffbffdffdfffdfffefff7ffbffdffeffefefff7ffbffdffffbffdffefff7effffbffdfff7ffbffdffefff7ffbffdffefff7ffbfffbfefdff6ffb7fdbfebff5ffaffd7fedff5ffb7fdbfedff6ffb7fdbfedff5ffaffdbfefef5ffb7fdbfedff6ffbff9bfebff6ffb7fdfeeffe7fbb7fdfeeffe7fba7ff3ff9ffcffe7ff3ff9ffdfbff5f3ffb7fcffedff5fffd7cfff7bf3ff9ffcffffdb3ffdefef7f7bffcfbf7ebfefdf3ffbf7df7f7dffedbefe7ff7bf7efff6ffb77f7fcffd7ffae7ff3ffdf7cffa7fd3fedef4ffa7fd3fe9ff5f7b7bd3de >>> (13*i)) &&& 0x1fff
def rules12 (i : Nat) := (0x8f23b8ea398e2378da358d2338ca318c22f8ba2d8b22b8aa298a22789a258922388a218821f87a1d8721b86a198621785a158521384a118420f83a0d8320b82a098220781a058120380a01801ff7f9fd7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea7a5e879de6795e478de2785e077dde775dc76dda765d8759d675dd6755d4751d474dd2745d073dce735cc72dca725c871dc6715c470dc2705c06fdbe6f5bc6edba6e5b86ddb66d5b46cdb26c5b06bdae6b5ac6adaa6a5a869da6695a468da1685a2685a16819f6799d6719b66999661976599565193649916299063d8e6358c62d8a6258861d866158460d82605805fd7e5f57c5ed7a5d9795d9765e1775d9755d1735ad725ad715c16f5b96d5b16b5a9695a1675956559566595645916458d625856057d5e5755c56d5a5655855d535595555153549515414f5394d5314b529495214751945511435094250942509415013f4fd3e4f53c4ed3a4e5384dd364d5344cd324c5304bd2e4b52c4ad2a4a52849d264952448d224852047d1e4751c46d1a4651845d164551444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe3f4fc3ecfa3e4f83dcf63d4f43ccf23c4f03bcee3b4ec3acea3a4e839ce6394e438ce2384e037cde374dc36cda364d835cd6354d434cd2344d033cce334cc32cca324c831cc6314c430cc2304c02fcbe2f4bc2ecba2e4b82dcb62d4b42ccb22c4b02bcae2b4ac2acaa2a4a829ca6294a428ca2284a027c9e2749c26c9a2649825c962549424c922449023c8e2348c22c8a2248821c862148420c82204801fc7e1f47c1ec7a1e4781dc761d4741cc721c4701bc6e1b46c1ac6a1a46819c661946418463188611805f1785d1705b16859160571585515053148511404f1384d1304b12849120471184511043108411003f0f83d0f03b0e8390e0370d8350d0330c8310c02f0b82d0b02b0a8290a0270982509023088210801f0781d0701b06819060170581505013048110381003c0e0340c02c0a0240801c060140400c0200400 >>> (10*i)) &&& 0x3ff
def span12Bits : Nat → Nat
  | 0 => 0x1f3a47cc91f2a47c891f1a47c491f0a47c091efa47bc91eea47b891eda47b491eca47b091eba47ac91eaa47a891e9a47a491e8a47a091e7a479c91e6a479891e5a479491e4a479091e3a478c91e2a478891e1a478491e0a47810ddfe377e0ddf2377b0dde637780ddda37750ddce37720ddc2376f0ddb6376c0ddaa37690dd9e37660dd9237630dd8637600dd7a375d0dd6e375a0dd6237570dd5637540dd4a37510dd3e374e0dd32374b0dd2637480dd1a37450dd0e37420dd02373f89cfa273d89cf2273b89cea273989ce2273789cda273589cd2273389ccc173285cca072ea1caa8726a1c8c771f9dc7077189dc5477119dc3a670b99c22670599c0a66ff99bf266f999bda66f399bc266ed99bac56e895b9856e395b8456de95b7056da11b6046d611b5046d211b4046ce11b3236cb0db2636c889aff26b6c9ab726a4c9a6f269345a2b1682459e71671c19a70661c19670651c19270641c18e70631c18a70621c18670611c18270601c17e8f5f2bd7acf5e3bd770f5d4bd734f5c5bd6f8f5b6bd6bcf5a839684e59a3964ce58c39614e57e395dce570395a4e5623956ce55439534e546394fce538394c4e52ab5490d51db545cd510b5428d503b53f4d4f6b53c0d4e9b538cd4dcb5358d4cfb5324d4c2b52f0d4b5b52bcd4a93128cc49d3125cc4913122cc485311fcc479311ccc46d3119cc4613116cc4553113cc4493110cc43d310dcc431310aeb4262d082b41b2d056b4102d02ab4052cffeb3fa2cfd2b3ef2cfa6b3e42cf7ab3d92cf4eb3ce2cf22b3c32cef6b3b82cecab3ad2ce9eb3a2a8e76a398a8e4ea38ea8e26a384a8dfea37aa8dd6a370a8daea366a8d86a35ca8d5ea352a8d36a348a8d0ea33ea8ce89335a4cc4932ca4ca09323a4c7c931aa4c589311a4c349308a4c1092ffa4bec92f6a4bc892eda4ba492e4a4b8092dba4b5c92d320b3c82cb20b1c82c320afc82bb20adc82b320abc82ab20a9c82a320a7c829b20a5c829320a3c828b20a1c8283209fc827b209dc82739c9c0726c9c9a472659c988725e9c96c72579c95072509c934724a1891c624418904623e188ec6238188d46232188be522d148aa522814896522314882521e1486e52191485a52141484842101081b31fdc87d511ecc479301dcc075301ccc071301bcc06d4f1adbc698f19ebc65cf18fbc620f180bc5e6e172b85aee164b8576e15734542d14a3450ed13d344dcc131ac4b0b126ac486a11ca84609113a443c910aa440910fabc3cee0edb039ec0e1b036ec0d5b033ec0ca2c312b0bf2c2e6b0b42c2bab0a9a8292a09fa826aa095a8242a08ba821c9082a41f89079a41d49071201b480692019480612017480592015670521c13a704b1c11e70441c104603e180ec6038940d85033940a7402334076b0182c04ab00e2402880069c0105002100004
  | 1 => 0x24ac99272248c891f2246c89172244c890f2242c89072240c88ff223ec88f7223cc88ef9e3b078e89e39478e19e37878da9e35c78d39e34078cc9e32478c59e30878be9e2ec78b79e2d078b09e2b478a99e29878a29e27c789b9e26268959a24a688f9a23268899a21a68839a202687d9a1ea68779a1d268719a1ba686b9a1a268659a18a685f9a17268599a15a68539a142684d9a12a68479a1126842160fe583d160ea5838160d65833160c2582e160ae58291609a582416086581f16072581a1605e58151604a581016036580b1602258061600e580115ffa57fc15fe657f715fd257f215fbe57ed15faa57e891f9a47e491f8a47e091f7a47dc91f6a47d891f5a47d491f4a47d09
  | _ => 0
def span12 (i : Nat) := packedAt span12Bits (18*i) 18
def pieces12Bits : Nat → Nat
  | 0 => 0x12c0d085e1c1b1a31181767236b012f0e64390d6e5e1c1b1a31186723106b01590e643963085e732b56415b306a693f3d5701353c07367156415b701b693f3d5c0a01353c303673715641703c6a693f3d7701350730367371415b703f6a69073d5501353c303666296b65636e1b1a1901681618171c4e7371565b706a693f4c68046c353c3007316d017675530f4d1f60744e61621631675066326b643963170801190e5e31673866326b656439170801180d5e296b6564636e6a1a195f1618171c4e66296b64636e1b1a3f5f1618171c4e66296b65646e1b1a195f163c171c4e66296b6564631b1a195f1618301c4e737271565b701e6a693f683c3027360250283807693f31681b223c30203166296b656439631708011c065e032902371b1a1901681618171c4e587156701e6f07693f683c3020361c1b1a19181767661f6563016e5e545345330b1c1b6919180117161c1b1a191854534d453301305e1c1b1a191767666b650d016e5e6d4e534d45313707066c5e330b1c1b1a191867666b656301085e0302286a693f31681c3c3027316766016564396332085e030228534d453137330b27114e62534d4501333054396116534d45015e3c540b4e60534d3f01330b543957592c0c4d453133015f534d4501330b54395f534d45015e33540b54534d453301301635060a0f2450150526340302081904332500060a2446150526030d450432172500060a240e150526043818321725000a0e150526030d0409253000061505260d04402a3f2530000e05260438180812254d1000060e1505263e2a25043c300049425856413e2a255d3c300035314f0e2f013403023325000e1211030d1e04100c4c000a5c5641265b09250430005a0a24083632590e170100585641263e2a25043c3000575641263e2a25043c300011353155010e5403022500052604122325532110004a0349140410321213000a035202311e51174c000e0526030d0412252a00060e03150d3217131400504f3635340302192833060a0e032a020d14304e451103334d1e0c4c001c19031832171314004b4a034932171314003403023101334847004642360345321725000223401404211300444203092527300029430125351a2d004241402a3f2530003e2a313d043c30001008343332172500033b32013a171339030902073130000302311404130003143213171600033101321713003803021437011836283534333217033201171300030231011300032a0201300024022f01002e2d012c00032b252a0029261c042500010a030f24021f0e1528050d0827260204251b0024231522210a200302060f1f0e0d01081e1d03021c1b1a191801170416060e0d03020815140413000e1211030d100c010003060f0e0d0c010b030a090108070605030201000302010403020100
  | 1 => 0x13073f3d6803022818170400855c55714140535b700400545345014d0b4c391e4e5f0106732b71565b306e4c4e676b651c1a19146e173e3c4d4531012b33533062394e534d453137542b33623900534d45375433303101174e544d45375333303101174e54534d310145333062394e54534d4531376233393a00534531350157332a394e304f6054534d863f010b1339544d45223353011339361788017371563c6370271e161c5871567020391d5d4e3e3d6829534628343204001c1b03020114191817136665631708291514131c67661524651463320813580a877156416e04003e1c0302011416181917133f3d681103283c2a04001c1b1a191801133704007c1967666518634c042a541b7d184d204e72391d545301330b4d4c1e4e5f54534d3331300162134e544d45313753336239005453453137332a393b005431030245283362390054534d45303101623d1354534d458601623013396665632a7c082b4d4c4e651c1b1a793f18014c4e5873567c353c5b2a4c4e076a3f2a013c5b30145e54534533010c5f040065646317080a29311c09577356415b2a0400855c7156417004003e44024a4901133704001c1b1a1931180130374d453137540302283354453353324e0116176a3f303c0907010400073f3e4d300104003c5856793e2a133c3039545345330b311e4e5f54534d1e0145330b4c54534d420133450b4c54534d451e01330b4c3f017371845b704c4e54533101332a62394e79600c35313f80000b544503023331016213453711032833312a4e03832a012c333013395453453110012a394e5453455133312a1330294a49013237040073565b79091330392903143213370400030228395919170003020104191713396763503215141319585b83402a133930543137530246283445313711034d283354313703024528335445313703022833534533324e011617545333324e011617545345324e01161707693f303e3c010067653832151413185871225b70404c4e76330b4c391e4e5f823331300162134e811033312a62134e603435313f80003362343130357f00335453452a333013396766656379142a3057510c2331210b5703512c0c310b54450302313337316d0a7e6074347d60740b11315407303c40023f011901335b70144e54534d45310b1e3176332a62394e3146333062394e3411313a4e33547c7b331339362a03172914131c59512c0c310b6d74460c31455759510c310b676438323118341142334c5460340c314e330b11317a4e54792a4c4e3630315a395978503214131938321413184c1e4e5f340b11424c540c4c1e4e5f460c424c45340c424c33312a62114e0c3901350b310117134e3439013533393b1e3a31624e341c1b19311767216624012d1a1f6564390d6e5e1c1b1a1931672166106b656439
  | 2 => 0x6a1a694519375f3133180b1758714107693d012c403f6e0400363c671c2d1a1f64315f164f216e174e3e07693d580a012f714140307004003e67106b651c516a1a19631831081e4c54534d45371c1b1a195f3c31300400076a3f3d587324012d5641612a0400073d28583e2a71012f65413004003c672166651c1b2419160d4c6e174d4e6766106b651c1b1a19163c90084c4e076a3f5873244d6b56613070361e166d828a530f6945603361310b62135453451c1b69195f6833180b31175841073d012c402a3f6330040036545345371c1b195f3318312a0400316d0a7675530f60745e33612a39534d454b7d127e6033613031133754534d6d237d7e4a0e336131301353453137067d60745e33612a3930544531376d2a7e60745e3361533919580a87016a7156335b224c4e0b21666b65071b1a19160d4c6e174e6721666b1c1b1a3f160d4c6e174e076a3f58732456356130704c4e4d6721666b651c1b1a19160d304c4e66106b6563071b1a191618084c4e6766106b631c1b1a3f1618084c4e076a69584f737160356330704c4e58737156076a693f8f35634c4e17073d6840032a02283f3c300400534d4537071b1a195f33183031544d45371c1a195f331853303154534d371c1b1a3f5f3318303154534d456d217e60490d3031135453456d7d603331612a1314306665641b2c19315f168e0d2b4e6721106564030228048d181700073f3d683e032a02283004003c073f58568c8b353c5b30704c4e1c1b1967666518631e2a1a4e16671c536a65194c1663186e171a534d45420154330b4c391e4e5f676b1c1a3e160d6e174f4c534e076a69587371653c5b62361e16076a3f5873563c5b2a3b361e16544d451c333001625320391d4e034f6054534d3f3101330b4e39076a6958737178353c5b624c4e1b1a196d2b1830016e274e1d391176534d461e340c4c5f0400672366030264280419186e003f3d68030902283c30070400192903011a14183213370400672310030264280463191700076a3d6803021928333004003f3d681103284d18300c0400312411067d60745e33612a39316d0a7e460e745e336130396d828a530f7e6033613130136d7d81894d1f6033613031131c1a19676b651618634c1b0b1c1a19676b651863301e1b4e54534d4531334c010b1e4e5f534d452b33303101623d134e54534d37452833303101174e534d4531012b54333062394e54453703022833313001174e5445315301872a333008394e545331352a5901333008394e5453453135012c2a3a4e3930022858712f41407004003e4558750a8756415b2a0400670a536564316332081a4e1b590e64315f1663182b4e732b7156413c61306e0400563f6c3570303e09133c3966651b51196318311e2b4c073d68030245283c17040003021c1b1a1901141817
  | 3 => 0x5e7b1a24415e7b1a3e9541161a222f41161b41167b2d1a4116613154014116613641613f654e415e79624e375f531a53232f41534d2f4153372f641b374d01532f41392f413c6e3753311c5341076d41656d0753242d4137242d643753013c242d412a40989b413e959b41532a9b419a410767374d014e77413c6e78415e39415e3f60416760073d9401743d409874743f3d653d3e957474073d67536a3001535f013c5f530130015e304e5301304e31454e3f1041692d643d4a0153412c3937013c30418f2c3967410761643c3d613931183f534c161a1b1e014e4c162a1a413e9961415e4d6153415e61411661454c162a4e4c30014e4135363053371a371a2a3d765f3753014d1b41373d1c3d01373753323d3237415e39415e4e534139373d195f112a5f762a94070b943f0b073001375f2a3f30015f015e5f012a5f3154943c0b3c300101304e46304e544e0734304e374d01013039373d0155416e413c61373118373d181e2a4e4c011b4c163e415e61145e3c4c3c01418f61145e30941b5337311301395f015f464d373753372a5f455f343701372c41371b7d41206a0154391b7d4107226701364161075d67013c39984107406a6d4e976407966d014e414e015435303960413f01543539411667010779366041078367013664074a6d014e391c01073f4e9541073e6d4e5341076d3c4e6407496d014e5e1c01073c4e4139076d304e41656d073f4e6407946d014e391c0107304e41636d073c4e414e365e6c071b4d01395e313901075e416a075c0a413c7707393139013c5e41076a6d4e4116015436018c4e1641305707012a395e39013f5e413f0755371c014e416d074e31222001395e39015e31276d150a7675530f4d1f601e5e33610b624c391c1b196721661524012d65141a0d176e134e1c1b1a6723106b1559011416186319170813534d45313777217d127e60745e54330d303903672166106b641c1b1a2c3f315f1618174e67231c1b242f4d6964315f1619186e174e076a3d584f7324011a7e65416130700400672166106b651c1b1a1915012c141817131c1b1a1958737156615d30016e1d4e3a391c1b1a67236b15012f1419180d176e13073d584073019124413f304d7004003c0793195c0a872b715641335b306e0400073f3d580a0192536656413c5b2a0400076a3d5873245a0160413c5b2a3604004d4531370a5c127e60745e3353613039545331376d237d24910e745e33612a3954534531376d217d242d60745e0d2a3954534d31376d237e2f745e45330d3039545331376d237d2a7e0e743361300439076a693d584f7371016541616236040067216665641c1b19315f168d2a0d4e3054534d1c1b1a3f653318300162391d4e54534558735633185b2a624d391d3b4e67106b65631c0a536a1a191618084c4e541c53
  | 4 => 0x531a693f2d2f413c0d4d69105a0e41304e8c20536641361a5e219d418c3e1661366041163c3163354e219841403e166136413e203c6153365e01415e4e0716363c532f414e3f16363c10a041092a16624e109d418c2a16624e100141792a16624e412a79695e35624e102d41792a16624e4d57414e07163630966a3d97232f646a69219c1243413da1a21001644e532f0e413c304e3d946910015274943d102d527430102d412c4d0d30411a72692d354e537b0141161a362101413e16613641725e35614d362d413c160d4d364d014116613036212e413e16613641866131363c0b412c164e30363c6041163c31634e6741275e35624e6641205e35624e6541795e35624e01415e7916624e5301417916624e41635d5e35624e01414e3f163630412c164e3c36308c6a239d2f411b3da1a2016409a3242d415e3d9697210164242d415e2a39093d10a052743d8c109d52745f3f01517439a210643da12d532f413f2c305137682c3c3040984116361a7201411a4e3924415e7b2a1a41160731671b7b924116301a7b0141161a36a041091661364e654161365e4116603f3579416c314e070b9f412a166136414e616e365e01417916624e98414016624e95413e16624e41613107674e4d415e79624e8741537936301b3d9e0137532f415e399764073d6d5343242d410a5c41076e242d415e396a232e2f412192102d412a9c129b413d96979b648c239d414e4d105a41393d9e01374e3e2395414e102d41304e943d01745e533d9401744d0757515f68875174534d075f01303f5f013039219d418c2e219841402e102d414d2c413f2c3c397b9c41161a09415e7b1a8c41
  | _ => 0
def pieces12 (i : Nat) := packedAt pieces12Bits (8*i) 8
def atom12 (i : Nat) := (0xed0e2390943d314281f83e0d1110b4308c4342e330250621e12cab2748a1040c03840058365303e0698c638340d6018002c0643d078480c98a02a02c0023c07070a10780c33404802048240d004110241a0781a04a090507012c184510b030bf0404d836002a06e8b14e08606110882d0e8d00458b610240e056c088b2108d144861184a4228d608080158d61a8f15c870c0290ac1d1548fa278205310c444d13c17148150061004283a0281a1286a1e05141104444e62454000040198f61c4c2240720c0300b05e03810c708 >>> (10*i)) &&& 0x3ff
def disp11Bits : Nat → Nat
  | 0 => 0x5b88001800200040035efe41d8daddc200013810010000000400b9594004000565000217df001400260ec014000c01c7558007000144968bc0030000004000400a0044000001a25a576001a00400000000007001400000080084d0c00c7f5c00182c0000000000200018055be400000000020001bf09171c62002800a4df80008cc0002000000400200030005a3c000000000099ff000000000000000004005000000000300000004001000000075300026855f2d51125ab00000040020007874d42c8f9164a0038003000155d7cac0000070005004a5860001bab8c9000b00614ad001c11e89d00440018016000980984b4068000805600014310041f1c00040050000000002c000000194301340020031f316ebc00b002c0000085ad601b8003000802a0028000003400000300100034000000228d000000981b58da0005eb60045f6e0005d52000001300500076fa1721000217c0040000000c0000000038000c00292e4001005a0b5904c000688a0ab5da800200320490001f0100000090004000000259a0006237000246400558147f5a0505a4a6490000001851800c0001d74018c00400600088c796460036397889c00095b800171e40008e68011000009a0000003000259064340000001d250000001813806200000008fe60d10009deb0035c6f909800290a1d5179ec002000c0188e9000a000c00151ac0040000000001a4d4887c0014d0401400080000000001003c0037a7400b00080000018018001c00f007e38000bd603000800100000018e11390000400b000c000001c0000030000716400097d15ff000000700000856ef80000000004003c01700053ad00a400500080000004010000000000040007b0dcc9001c000018e33e00022670030024000a568000e56f0005382000156c003400d00000000012357000000500040009648002000c0000005cf40025b6b4e598870018000693c00000000010008000739c00100b5d580114000002dd9503a934980c80126cd00010004000003c00500000006d30000001400000440bb00080034d8c00e7bd575f0000000708800152bc04c00840000001c020021dd20078000721c017767205100040e3005c00000000006f00011000c0090038001000000265ad8fe00200030010000000662e000259b01e40040009a2476900040009bac0008002001400100240000014000000191391ba3818ea800000200000001c800000021669c00000100000000003000803c0000000003400200000080000002000000500000086c5188c000c000000202e000c01f000400579f0000000234e5f84006000c00100013d800040000000001809000001515bc00000004cdd8110005ff4000401b89c800000000000002419000000100018300004002829658c0000000001c00757ec00000016247474013
  | 1 => 0x1002800a000c0000000000000000000040056f9c0008944004000001b01080006e88000002800387140010004000000002568c000c00380158379d7292580008be9fdb82d000900580326efdd31002953589ac000001800000100024e8400f854800000000030000022007800091aa4e300080000008004000c00298464790109543000c00400000000018008000c002000400700780000004000001400086a000063753570001eba0001bba6c3c00000013d600000006f1000000fa391006004500040080000000000583f00080460004003000195c00780045d980004db8010000d9d10000001659800000640030038004000000079940040001d1300980010000006008c00d006c0197f400417fadd496ec8000002401e762400100180090048000000c003000800200023af000000000040020004001000800468980380028000757c00a8f14000002800800140006425e784eee3f85cf13be5bd9db400315230000002000001d0004000000000500057a8000800500600000004001000000000000000000001002800300080070050000002647b8b5583764780000015dee8d500007338000004c013000c0018f8c000647e03773cc0440000007000000000000000000000002001f006c01400058ee00023890050000817c00e00000000014003000005400e9c710000004818991100060bb83a0000003004400025830004003000c0000004000564000781e400000018e997dc00680740008065a4000400000008002642000277fc0068f095ad85723d4000993d63d400b5d70000000400000318db68ec000000400700165b10031960002c0000008004005c000003400289b2581000153d00b40024dfc00b001003d0000000004c000000000000059c60001bc60001d8b00100444d1800000000000184003001000600056ca000000300000080080003008c0074cc15300314000000000071a0019001000600c000102c80035f8001b0004000002c0000040000001c002001d3de8a0a652932e47800193a2811e065000c006000000800000050010016001c0067a14000000801400480047bf000300400030000029000c00c0029f77004000a003c016745ddbf0010002001c0000000007011800071c8001000801375c400260600030008001002000068596fb0000007002800d0014001000000c005c0006798001000d9ce001400462a000a000000c81ec0010015c1f01ad97f00000008299efa8120001002801e000000d00000008250000000000f00c000074dc001576c01400000190074001000170d002e5ff0008000004000000840020000000000400692e8002004803c000400000200010001d8c7a1c05a80bc00979864720020000015dbb4001401500380000040000000000000040000001989000400151b000055040000000001002
  | 2 => 0x1000e00024c0003c003005d4860014001592000d8040002000000c0001d260000003001800d001d962004c02d8a914c0000400882b8000002e3a57cd00000004004004c0008d2000174c97a3011a1300020009000000060480017a4000001b19be00014690004000612c0040001d3400100000004054000c0020001810000000c000800168c8000000000000000200005b840040024003c004000000a005c00400056f20005808000000800000004e5c00a7cbc0000001c01001000d00380034dc15fa63cc0008fb000000c000f007df10003e57d63f000665b4005000001601761630034004007c000000191d0000007003c0168a9c000005c0008128000002000286a800000100090008000001800e00000066d680000044000000800600240618ec800b00000008fa1be5907800200000000029840756401f000000100cdc60004c000000212b0004002000193f8efc057008000000080035c9c0028d8400089ec0110000000000007f0031bb8000000300240017700001000e4210008013003c00000000020000041000237a000001275180000024000010c000001001b0000000007c0024da537c6d9d52f003000000018430001672000192b8c9c0000000000001c000000000171f800400a801f0001fed000400100000000010003000001d00ac000808c0000080000000001397ec01a71b5d5b00080015b65bd26d8000000117468d240007c48000012220c002000382ea3a6001c003502c0b40018005000c000755e01800464c64f880008dfc0740009ce40000000872da4a6d8800000040100001d1266440055238002726c0030000015000000070ea632005000000000000060000001c000653c00000000000009c934f0400065780008814000000c0376535de3000c00200000007fbd3ee00258ed000c00000040000004000001de59005952a0020000000400400020568ce975d003dd210009772004c000000000754b00000001db84f313b0680000500059828d1801271040030001db6769c007911000000c8002000000c79fc00000000010020000662c00d000185c000c0000000009000639600000067cb000000000007ba4000000400053cc0010000026689c0190008023000142800321f800040006ea00008cac011963400074b4007000000400000020005de10000000000000a7710096000400f693400500dc000006000000180410001b2d5bd00008d1400a000000000040005baa26f002400074ed63700013b97569bc57c5d6d300e0000000000100040000005ddd80780054cd80038c8802e003c004000c002000001100000004f3606600340000000000000001e0021a4500059567ab40108d09ec100000007725c860004019008d43f000000d54700599261e8c00000050000000000802382cc0000204001001e1a4000001
  | 3 => 0xb003000000023344f4000a71b0002001401c0001d700024008581c000001800d0004000000400000117da0000001000227076bc0035afdcfe0004003959c0054cf400a00000040014000000400e751000400080000000000000143700100027704002000400087e641b002c000000000a0059844754000100040006135dfb001000600016b464640128cf000c000002c888401f001da2c008226000000008ecc00000600000228004574400b010000a000800300100170004009003c032000000f00000090010000000400500240006d3404f000402c00a80007a440c1000c015001402700040006d8dc25002c0000150004016164473e400100180007c6c031000637d000188d000800a00200730048000000001e000000d645947e60f5b4550a40000045922000c00001ec00084d8000002545400280020001a11003c00100040000028000000401157f8066599c04f0004002000141b61e1db58174021000000488e4011001400d9608002768c00d0035d15000801500c0004000c012000231d0058000657c0037db1ff000000175f91c4d901400d0000018000000b014c0028ccc01e000000000000160000011000000e007e5780090000623d5e200f800195cc000571974a0040002000000c75a4001001800b007d3b60018006000000f9328007004c001719567796e000e00040030001c1500fdd6101b80017500000000000c00000008a59bca757400000000000004006000d60a001800100000056365d486868000001400a00000030000001000a35c0008001000001200019466a000260012103000800000640050000000003800253f400500000000001ca752540000000007000a47c79a65ac68940000011dfa0000013006c00f000400089959e4000a4926b7000293a4000006800700060a3000d6800001bf202c9393742c005000c0020000001002265501200170071b8d7884000001c001002400100f95cd000182654325fc002c02002e00030000000000000a0059b870048001000400f000000c0025ffe8de000201600000004007002000e0018000000c034000000000015e000000086d6c0009658008000a1120044000000800a88ac00001100008780015001c00900454fb74c1d43000000000080028f88005000d84202140055b8001000000005b9400900180010004000000000300fc00500040170012046002400a8dc40010000000000000c5b84000001de796480001006e40800764af7248001000800465c400200400040001585000001100000024f64000000400000280000000000000256b51c256d000203300000000000000000800c0011401001000100299d2000000500000094d2c00100015c70015c7f000002e6da9fb50024008001800090e800000100000030000000c0066e9dbb1000400a000001e6e9800000
  | 4 => 0x1e62001000500164180011718851002b64d800b001c00600018fd4ec800000000020005ccc869a4120000013005800000040017c2228a00016c090940000000000000800e0002323000400267cc000552c00000b400064f80060001f98000001b750800000100028c3c00a8a2c00074f53d7001156700a40030014002000c00a0010004836e3690028001001000e000c005813c0004d6c0060020008000153100000050002249000000800000030050000000c00a000000e80f00000000000000803c000401600540
  | _ => 0
def disp11 (i : Nat) := packedAt disp11Bits (14*i) 14
def link11Bits : Nat → Nat
  | 0 => 0x9e42be2617626202e1b0b36ad45669b3819f085401f802e010f97ff08960f38907a115621ec5f008d84c42038e65cbf1a59201b8c6c840f93e40ff416e4a4b3041067405243fc04bb25528a9446e39f22cf20f7dcef91bb0186005905500666b6e25b0086990e0672455d401894225c4191442b92c8694c2285a14095623105f350c1a64150b6283ca430a080a9ad1803e8232a135855d81ad85b41108000daa288e801a64c68919b8e313bc0f6c2548a36476216d5510b7d114ac839403707bd082a161d1bf30f2116acde02ab849512a893302a3818b27d019d53fb0049258cd2a8b4500770fca621089892937460c0a4198a10f413e4be8b9189a52b4a1408483141030e6936842333e446621fdc4b518fd1238a184b5e06c101648cedcff09fd412422d4cbe815f04bac1618ec026b6d22971d32a305f2dc2a13db590a502b06092846c8a4c0d5c08793e093de2b7a0cc832d953b6168109d4c187ed31d222e0a80008413bcc5883f6287422f09e28b79a6dd61480c8d19808800e9c1528a6c242406b225059ec046a007c1c4815925d43090db1dce0321d066e2934233134c065e14f1123939967a80f4c4e203d00ecc512849ab878737e5b49306901c1036189d28d80772a72a84dc7b0901463853b4d20b1d0479c273d18704190f6e48d8bbe31bd0fe6132431427ea082a68e043c29182b505c5d51b361b0d7a444837b0019019e0995929923e27b296952b0036b2bc41270b5581846b02873929997e04790dc099cc00530222181033eb4440a9a1d614f6101a50dc01980bd0961482e1f9c00711f20528cf9c40d17980dc8557002e99f864b207c43cd05fc2a82d6901529631497e4d2813b887f10f2dcac0a409573182ca3da5d36ec10c0c05544232142ac81b8936e39280d5e9a182ce084d129e1461cfda1952a4a47480b5886b279a06540990354142218b02c732380aa665f013031a166184fc83c0b26842f4966c088365a656a592883000d60f64972434c159a5274d0dc1df0291715000043daa71924300da9c0d995352100f542cca90c12185f1988b093f48b805a43d729cb6da662c04a884210b06a6b407517bf27780274b640a5546a2132dd17019102fc874d2c2994a469224b41a586172be885281ce907411c4df703ed94f309aa1ef9ce4a8ea0f925a4cd1884c50c726551a11912c2a449f11b1d135c2cdedbb44a7918110cc163c9dcb1a621a40b51d0a06820c4618600f9b6a247141bac1bb21916f9e43904a2a79e096a63dc43e19476400c024516994e4cc01ebd011812a245e5efd33d219a6e900ebc4bb11f16fbae7d9b923205653c82dc28d1212693c91e19c9896908f05ef0138857a24529065bdcb3ce4a16ceb850817b60464602036887b30dd4079837290b3084a27e03d897302b4424e952c16bc52745ab12750
  | 1 => 0x4d7487225241bda84c0c86243d30585990fda024541384d242dad888d2a25e564ecd8143f92602032e1ba947bb0a7533c4744c66b0f103fad0084f608e040b8e2053b985da012c0c45cb3a73f0cb842f988e231264e61051cbd875f2fbed87c30b175a2bf40dbc2e2ba0d2cb405b003403e906925e10126137905281b5dc9a898f2e8214c0a0bb36b6eeea0880a737e74ffaa3f0287841f0aa25e4917286cf42bc239012b138404e0cd944b207d00b220185b1205ee0aa8cf58c24007a0e181dac128832113aca0d5a1a80570e8c1af84012a48257c11e42a5b29b4b1c1674bec841b142e1f4802590e307ce9ac4c0f85f8329600752d499d40e2802800308442621c1474330836706f4597caa9841106cc29313ba091b0f50015cbca103f11201fa0113034f669e4d8451a06e5547ce84c3fe188602b21d8c07f398023f2e290d1da9620b168a700d03513079801ad11c217f0f7e16d94b093bd0c40e5e4215007932e22401a361304493a4c91a8088bb4490578cb2b09aa0d8a9314cd907f10ffe50f5af80640111ecb18454222b6a14476c3e3b71c10ba989440989fa13ae1a1cc0b06f21264196025d1305045860e449daa2a06ee04f517787892afa07182cf87de067847654faa81100da939c0840032294e8d80487b7590eaa116884824de2d606770a1212ef322e1a503783a020ffa17504cbb0f02db01c348401431141a195020ab0160eb80dd040394bd27d4d068c589821067040fd3bf33642ba22009865033f27f2261440803e506b42405a03073700061d64b3a8041302055b032b161113a45c08116b94264fa100c92908fe221417f11f910527200039d2b7026b12309f2146e068328ac086439f010607f8294d00581c403800985bef88852170a0a400a928231ca1c6906d09406ffed4d8a87028b0b1626f41c12367724499b482d09141122203814803f42b5e17203c096e04cf646311a905e76cc601c802e012752e65728c369a3f1032011913481540b820ec89e3254104b8dcf1ce50682413840ed34f201344621a701a7853b469c0a653060692285c0d203c997e3300c20d81a930174690637949813e20e629aec1ae03eb08521af441582990fc2c1c005c82672caee3d02a912ab33f6e7f0caf89274f7254704699023667ed6e41b6191c10104a1401e283504aa551182605bd69a29549bc020094deedc3c181817f446427d41a303484d7008a0044049d43da252006d8951695291480a3946e6278422d958a771431493402aeb445720218188c189d545d4d6393c903e7674087780f7b25a044a9dd819c82b0045e974ccfb8854487c0ba4396094523001040193091d4fee8a552fd879732d0d5214c927e2603416fc3da9a154a2418c031408a62baa64f02e808016ce493004e426a4287a402024d932820fe41440a381720234
  | 2 => 0x21a0006ab85c29de1c2c2c228b03026a1a8b0008670e440569027259e09a0561813d9995328e28454f407c228385cb8a5bb3292e2096844b80525462a69349d9285e287498d817498620cc4dec12492454027496f832e0701004a80b5c300260146c61689e5907b03480644ca813d114926685cc8018c114426d452021a562b291c4430134e25bc27a0c2907260f7221059a115ad000a51c0396854b264e8d14b1a00c701d8471c8d8066749da04d819d214d03540cdc9f3343f0738d101b50966900d4993885d20f64e60a54825c139e6eca820cae792a808341920408996c28f81384acab98d2332187d2e8966b2a6e212c151198b059e8fdc517345c2030d608cc82040267c64ec0f438882f54219d09e850f24ca66b91fd941e08b218e1b2686b952f09ad522d9849318ae5a540f02e7278ccd4ca2994510060048d097312202b010ed24206510c6ad04814e80932b120cfd18801841170848197f07ec229611bc48db8e52d36a14c09780ab045a111848f109b040c11cd51803990e12964da9d23251238e3400c7949223b2e6081781664140e98682bc2236131ece0c32414eb100e2114173073d30469dd424e00886a921a9c2f907d80fea9c402b98a4b0d741fb1a9306802b042574419025b0cce17ac872a83153cea1441fa00bc085acab84b385894e3c209041e00850c7e27ec1cd19be073421148b8006b627c264d4aea2f90c76134c0d5b2bd28a01b80330137b1006596dc23137e0fea14f00a883c507e622701e1806f05f265614f6a744018a961031a24224bac0f18b8aa0bb309e65b444c088905f85c1814017d6101a437c12f83242a7c08bc32f80ea63849da442d93f321e2a820b178667738a02043db2390223c8ef893aa3ce6fe05780a1b07f8465218e0a458472253e510c06481b841a4994ccf4984b288420c028a03e322b60bad49702370ffa54f441e190910805fe44bb89955314461dc43a3c743dcd42c0810224507401b44bc01172c5a206851a81902c521dfd04189d907ec610db7f040c27b69a6897503da4a2c1c7c0dc05c9275a263d3dc1975026802dda5c38ec31de21c02dea68427f607b53c1b01d313205b8352847809fa01bcba902eb1350e3b017807f2018c1ef8058843408661720c2c302e54420bdc1fe98f82aaccc3029d375f0c52d54123a85fe1456a47ca4f15c013382128287a6e1722462502e286c832dc681094f03dc6eda10b048e87c331f61be051638db149ccb384bca8ba524c0de0b2025bb0122c4fda4596a20e840ce8c6389bc4c2809e1c45071f2fae4fa11f0867f48c416001aa39a94b7049d8461ba3441140ab44ad336a13341f1502a07766a8c15ac21309bb0c2e01ccca492af305a013c2f8205904141ad8cd0085d2fa81e742f9293e4dfe97189f602a552b84424028a089035e9091307
  | 3 => 0x998aa0266073c14b0a180bc8e2510d3a8140524223827203dd1112c4c034ca7846df2e3d44d2842c258a1d1891380282a9411c1bb03843230a41e050d169509ee023cb8e9065144cca0540799ae01c40dddb31092f1424e6b4c59996f343418f01c783a8146692d1062949f01d0a80920c952e1256c7f81603740128608c5c4623404666441c42b00924cf818a8b4b01c14dbc18a0b5516cc22bc5154b3c10070008277037401be515886b9a4d06e4044402941b183ca4d5247d192f35940c062804172112e2d181bcdaca13f5148845014fc140f212a241d39c021d476650788dfa06c4722063d2c6070e06ee843c23b09ab0d0208c98f607250f4c5f21c4588833396197805682700914026893f02f16bca1a244e29a0220620dcc26397d3212621d433c27625284032d0d4840707b65f54c3c07366b0a19f48fb831c0d1a5a3d2118a462ce4284d16f807f5364449107c289611244b954cba2642ad40e0443638cc745c463420c3878206a66959c287830682207d05c921a03d2d27cb588362119e0d9023a16c848c823383e7047e0d106344afea38c6fea42bd2a7840e28600b7dc40899130e62024b4d81f408d20da02d5a3e614b020f9d07a2712ece273411508c90eead23899b20790a1689614e61719040e169133627a108020328874087a72d42908824a3a107b8002585998704c4e1e78a4bb40027dc0361cd1150d06aad9c046015196b9e26f5307846d06a61c4d3e48642099641c9b4203d910500d7c4d196362a2c4b80bde936526804d9ca82a01d623285294c9b54128e40cf13753a1207c285ec04a06862af85b4052391e30fba4460c2a83c345b05de44f901de31bcdccc0f8118e491e20702ffa38b05580f3c23ca95001f216ac1f88a0a13e815713e622b95100518cb61930e6f268c903eb865210c617e44f287ef004ae1edb158a3b143a4f8132d24e8080021cdae098766a865ee14a890b50f789059caa815d70dc669849885cc03609b0c07086da602250102c7136a3340469547518721474195c34785e66f8a61b44a2248266dc2500beda1430424265811a08b263cee441143b8930eeed74843b166345e48dd840787fc6e12c230249965525b6050429406ee33245e9026307f72fec867d25e23ef450c51fc24c9336332cdd3880900482588a0d0d0196c872d021c4a4185a7119e657802f805a25a860794c496004858e65108b896e04fe060da36301b0402a8cc2f9a64b33a20be82e308be0aa810803cd852731461174ccf047a0c54138c4cfa19012a815404f2031a0aa2014913e93ed30ee602829008e7115e56a443608162592e1589cf81ac090a0a3cb4117c50a841010bc407bc6102dd141ed089162461251b4e193c402811cd88f011473c218cc48d01d26b24627840b98b3051c17589a123c900e21f544db0747690
  | 4 => 0xf81be80bc85400ca28bdd86ea7bd613c478ccb01217512ac1219e404f2461a170c866329a51b29050a780a2308ee8af04fd25f314780bd4484984711a443b815d36ff13862725b5d16cc0cec2330388a3eb2f2263f81f898420de01bd43d7036669ca1365a3699576c10103c2f2987c7180ce81c3725ac139ed02082d88bc2b021aa094685ff023a5f593af38ec4d644aa0c0914d71394dd3c29185fa53429e3dc1a04fe26149f3181387ba4e84c0541dc37ff447ad315bdf218d5170241426f037d0098811c153a9bf6b20935821d86dd53e6230823d95d90c42682881398c40e96230c02e10dc0b400194b1ca2b8717822ec1a9b7e443aa20bc245a37a0b8cd78d3ad817103be02c992208b1498687550a1334b23bac77480f08ff2d9a0df508e06cc6cdc26e51e1081920da5afd8b98801501c80fc9a8a4ce115c933cb71a8ae01fadc1049ea01e272e1fa1455a6c25134099c2a906b7263e06842b90103060e8fb8c02011f69f007504e3114406a0cac8406b7c2099a1b9450d94470ec826e0a42236d489c0a25302153a09620fd4aaf87f404062065453833b53aa22a431904c400d4260c97f83b82cf619e512e899804581da045e844e253006202e106e851fe25adc2f93201296a604b3f08ab0316c825299b4a201f6993c203b2c21152a8f43edb58a09d897bd43286fd026a27744cc36b90b8ee7fd1d316b704481a20122115009be00f993d83fe05461a4017715792ef60acc22513ab0f3459cc22284870de8cc5c1a036956c1408f084382a208ee0edcae384e144329a8d8c304482da602ed96eb5310ad0113cade16bb4886626537789ee0da4457421f29c16f8e2265a5f817c518cd7a4bed08b407c609f00640987090a8360a5b94a142500fa196a20760d681a85b5984d107cc9e8836f389e5118678103603120d62e94435920d904d000f52b1801109662788285297a69645080a6c003c14120379cda09e621ee2841226098005109ce808b16a6316099a0344a3dd463a4c5423c97d56a36db2c26c86a521e816d1051004507f425d0c4633522d66a51007800f60040067129205572a20040001a12bc625686944c702b1114cd80d068801a6fcc13d54b299fd2d62861c3f488992df8045025281cb13bac9f1c3d97cb0fc2039842b319b11fa4f4846d03196604cc0db6c11ca0ec868491f68408075829092fda449738ada5c051b0f505f61028b8507ca02baa29d8a0013f0d8c1984c00052969302031858b83804820f2d9858593209c60188808849005809bc2d70a4c67960a80c4f985903920aa428c82a703eadb051a2040b6f6e066d84c34e929b8268c2b935480f2a1eed317093804d84a7c153012d4088de0d07e3517010ea0910e089a47058191009d013805402295072238e226e06f00db875e4bb828151820302036820b84a
  | 5 => 0xfc83f6003465ac97b07202a0e1e043c8b6500728a758335ba2c53489cc8139060905f81f71376132811b0871422e818a32041a3c866a1520938a601ce6338203c0c7c98fb316b29cedcec14487bd514a21bc0b5099f7034dd7412094682a0c10b450b0a0c069cdc9c248029b114a672d04880384828088d5002966093c26fd23ea9ce6f8044ac993878b0e120310529b81549448a3c115a621693a164c3fca21b03121c2052610552a68c2f885308e76e145dfc3c685cd13a649d444535f8035c1f45021831830020499061172812084b65a3f222a4afc1f392ba85ec079e56a0243a7d304da0f309e5aa0f0d3ad14c4d89438410a9ca848c09634bc82204a7009950a2097b0b94805e2722cd0c0d8866f05c6087039330460fb4428422f85340db24f283d9a6980b20cb1946f04bb60b2da6850a229751b6908508a801700f0528d0b622c00aee16744fe8446545a22fc309885e063625940c4a17e04a8266c0e1046b2124ded138b026e33de0e05197925c0e3c673c420802233c02721bbe99cc119a21a487627b013ec92bc2ff23e22334276c50ab3c006d8124842705aa09dc23e9c2d081833621c8db5192d8092619304e711f01452477108980da482645ec87386fa2deae58c8df8a0923d4e3b41f528e432de2865ce405f94e400c41c6c354b48889ebc00828f311ca8a5410331dc11d05fd1219081425421670bf114ff4946d329a4c82530586ce341e416e943c888fc40e399153965438c71041d6c30628db89159f31389a1433a09ea304480743dd08cd53281d1cd2824264bbe072002506f8630a13983c8a8f1127e1b6926d8126016c280c478029d4c3c0d88b5996c70f985fb8038923a49860fa0877a4fb07442909bf286530254267cb74899653b01a6411804ad0edc1d852fb84fa03fe22c1a5b143a300406a03f606b8507e252825804f90158135938d007c00f69a54b8987310dd047a8496902d033a947814d021e0c4207f19682a0503d207bc2c621ee03f001f83c4877d0440979c29834a7059ca5354e804271462e6c029d81eb0c866750c85a2bb055a83b48a7000c07ca57780e7026a12b46874361071653ec452c8a606c92b46152c186b31e043e1c140d68a2204bc05d44c3001f47741e303ae94db486e4d1c43d114529dcc67041183602ce21250a4324a833c6a66080300e9476c0cb84fba1190822e6c0cf1813c118a19940b284f644c6a915b5f3a1c6cb2405585127150346e02c1b4b65225541d243aba57800e2dcb833589ed06a84884cd5a42f03ca0c20465a07623c82768339b9630ba6217036e1416045a98643e7823340c4176102b080a318243e84e6243b6a7e28bc211a760110e0469b678283269a2768c74aa39704c13d042818df261ee3984b9168b08d62325b4388e0050816c80be87045464271c347020d53
  | 6 => 0xc0c0b5c3f3270f51742239b399a2549c6d424b7b186f4a6c99984d783f00ede24584ed91d60d9412244ba09e907ae250438b8a336cba24152aa23690e18e90c46b09110ed8c1dd8e61a191386a0602b4829113fe274c2dba0ba29408b613d8b93e11aaa16540213b544625e002992005147c9d65375988800c81e488df0105066a90b9cc207b8038614cc2e6a74a0a2ea1101f838ac13f28ecc027a2aa4da25ce0c1f052f118c1e709159a514c2007e1b28933e6f761110b3a221b424e0c0117685610344a14509ca64711c21c69af184e24ac41b54028016e321a284cbac12ee0e265d4415b148e0f4003ad1ac03f03188e63027fb00f0ffc08b9b3c96f2677003f823aa21a4a02e57d077b0913074d7a8272b3ab289026cc4f7270d06561e581a8163132d2cbc89f005b80e9e55fc91186af1374228906b2a1b6af6a64841918d30fb4866084296c066ae115cca0a874050406ac38882200f3a4864d1f92e00da058dca3e868e2ea62741bbe220268f4d3053068a4b2db80d083ab00ca734e1af89b801d561e6142184c99d211469150b74b68a306a87b1cb399be24bedfbd1c0052b0374df5147ca28a7210d8a548510fd0994611d9d483394a545454313052a0236d4a53e402bb649017f423f91d62f3ec7ddbb132d908b013cd16a081d0bd0d04c172b3552112a50c94604fe015c19752cd08cc4046547c13a34d40dbe00f43b825bc03b206580e819c610661d4027087a6096805053b301eb683021a0163979010a68e480e800e01172013486803835384a95849e85dd0d8e65a1149810413cc19fc93603b00ef81b009ef209a4242120186335270f5843191ee91d3099023419808208042a1480a5e121409725e41bd6a55b0ef0226d24517f00c7c102c3d90075011a0b849a3a69471e640ec2070535332c4b28a4faa4203140dfc34f0213139c0c20a6238cd210c834c30a28460ea6a42835b0700056e09f8b43268c4c8248448270a1b12980abc2508336102a589126388d1546c286491d0a1e058e1570a9d166a639a2588d0b295e4014289144607cd03241070019b90e4396a59dc9392206c74232c0f389060108ce78303874669d223d89b58619312e0cf1ad305ba0b0e0da48ab02102eae14841210981117a44604ef84994520d25541329e72776209db6c28274572095449a3a0b640ed399288819245aacdb10e8820e041645703a1b2a62a702674483830f52fe6609cd629463288d420a5180c106da06e449523265482111c89687cb4a5a0c35121895531986904d05a02f046a1cf039c8a1c2ff654c9bb1a1d333e217b401207eb0a224091be309a211e466998312205033ca2593f912040c0c9b58266a45f257e092884001100a181148926b8d442ba5f919e4a34510400b4024409b9047205bc0dd09760e681cbc39a316752e40f89c
  | 7 => 0x2c0276329628ed90ba170705ce24e495813560b1a107404787d9687816202db028e218ad4b03708340074e102430d3060702a1748af881906fb60a990b397a30c02294cc8185391032c508446a89852fe24c0373137103c2683823d838a2f5619653f4aa550dcc9629396b2e80b1ee41013288430b6a0e582ec00c744c403398a692e32f2825ac32585db4f580ccc3bf05e9129a4fc5c4e88bf4ab0ddd49e423224ab0877430e07474f2e272430a855906a007e44cc899712a4a8a093d030f12b6647c35f830c6c2acdd896e29c270d205d02f587156f68277902db9d76664a281c91892a29aacc7449605d9467a00d841215177108a810074851a0eca0650369027407380a9c86e98a72f445e6424da5bf30a4dfec3cc100011622679c94855e0aba217c45a86b5111a06bc41b897a02c6911549316a904de55682cc93860fc010283b6b9220e34599998385360f6440dc15d02da0ab2d5e5b1103ab44760d5430e82c40c4a9a15b6839210186d71cbb8349870e8c0e8acd12216bc20f68ac096242f860b2c17e816c6ff05a11c92b78703085da13a387b50e9a27a834905550658172cb3c01f305b4475c99f800e09181e05299a39404764b0582c08a02d261780490037c0b9c1ab93c707850a6442c8525116d143ca80481285cc4d5c65c0c0bb99f0a9c22e5263176208921dc40f6b4be25ac638dce81840123c2564473217965e8553004eb72f43ec1e08ba5ba0a4a98550da1a242b2e4ac1ac9158770036608000b4287d715e1c0d0533081478e05b0b7b85f40d3a1a0dd1121ab43c4e7190049924022492b83c735d707e4c70c96620db23b6822cce416a006ba67718b381b505c0a8001d7a44d00d211ed2b280eb097a126c3fe074c120e4e8c19d8846417a40ac82f08ed610c59243f9a5094b2025341caa92707e8ce2016c346704dc231dbb412250910a3e04da2934055c5d0c30a96460e36171033f890f0e58c53c029161613b25d4102b19a40eca5598ab307ab6ddc26c5a1e207d05062878d1607f14ebc1eb42bf83f6710a13ad34baa1c0242d2950960892077e0ae4866275f444c6434c3ba4562736125caa2298143a8588036289c5484a9b10139134863b4d0884db1233104a84ec9d9a31622844c5816925e6035a9bc4334331105f0c20800689b76180004c299035b3430c59005f82a463be59f8a3a02382ef40cb434b249152321d9102d2612121cd611839176a059a88893cf88c74c24a2c837e943545a20dd42f788c80f1e07fd8ec9146144e0f582b389bb48700329501b91128aa0cf01f7864532a4deed94c2915225e5cf8bb6aa5702d26320a0590a321fe1510505876740f2c8301b9077202da694842999bc0ab0119cabf2235424e4174050a3b122ec293da7e07b11154a448202818f13260baccf719eb0b4ca93cafa80a80
  | 8 => 0xccd09da33d6272244c37c89dc4d1a09188f2b736116e20ec24889a825a60d7889812fd62804070bfd1a26069854bcbd38780335c485828489c42fc297b91d901676e601a7481407b7657ec6b112bb5582e300e1c12c13b4135821f8371071721f452691ae88af60dadcf436d88b6049c413410e21cd50d28b454d9280502bc857d11819360f52125c0e31574621820a804c85960332424033e122102761441b3125aa4c6e223581522f32d80112dbb015f613bc6605c45969430b095d006b96924468de0810b218212fc250d8b1246533e01cd40e7945e0252cffc16085a34bb61fb8d1003220514170c037212b0a2ac19c2bba54352561515d1b818e0df859e84b128eb0cc88720a98083129c8d3498a21a0566260e3009536ef681a4cd014b150300dea6842b11a1427201779942155424ac2494499825012e684649ce800209a68e3dc8d218b120ac4f4cfc259f6af60adcb1a87a505f8de8580e24f60eba96c032f169f315a08e8919954a435461bc91d34c10152258028b924f088a68b087ca9036aa057bcaa3b4960a8614102b8b5b1103a4bd88a4916d402ee2dcb6e92386f8c5b5009623f840469c1528ca8a605900bb4c8226e74492093992722e6343e05a58b08895202cc058a558020494802383769708304a1dd8cd21269682453a18970193074822f89d6a46e244cc5801b4368044cc8f7c2a4a7860546a3b824a094e0cd41e704061883064a82c04a210d41280091442a931368820af8d0239d823ea15492060857097806e52cc18d20a1a94d41c706d9131010c4c86a89b141c59dd8af33c110aea6fc3181042122a16cc256257a4b2e0094baa05700684cd10be9233845688c5018308dd036c0d7c8b4a4c208ae00e531e86773322e38592b84a010c81c8422008d80bea9c70b2019a344c450c926588a4045c049440485dd49ba22081678073066a118440c2a066c6221e42b8824e0e288b098fd906030bac92d2f40a1a48e611e915a08c27194d208191819741aa500c38db96110e061088aaa6f4025285309af01530c2855bc0bb80f929148ac4923804402628e941e202a4023a14603e203e16cb6090008eb0212c646935a9c255612e61a049fbb23d10d6cbc409c15d7312a0a2927886e608f0818c04b866f2376618431a141127f0059846b83e92f980ba0bad0851675410a95113767634c15b43be1309046290cd9c488df140c19f417606a46dce1db8c2c080033344cd1246883d08d81798bb321290c36df798b4091a2168d70085f96d72df610450e2b87707d40e54209b10b05f026e1c58b33810a4a20d19bb026048a66bd0fd0017213022d133e32422a76561501318d10d50ded19fe89370518c71c117b5984da29f7443b05824c8e48c9348809e6e6493b00f405790a885ab9b2cb758082e679c
  | _ => 0
def link11 (i : Nat) := packedAt link11Bits (15*i) 15
def programRaw11Bits : Nat → Nat
  | 0 => 0xe885e520aed1854e8864520aed8144ebb5e180aed8554e8848513aed8044e9948153a2153482bb5cd80a21434828844d20a652044d20aa983a652860daba655156eaa6605baa9984aeaa6602baa99806eaa6610baa9986ae994849baa985a21524828850920a21124828828d206ac51649ab149916258a048496682156d9a0844b668211259a145b9628125658a04949628121252054db12a5821253a1451b2a5455ac52644495a89246c9a615495e8121258a0498968c12565a30494968c12125a3048b9569135257a204495e8815e54a2044b6685146ca95214b149911251a26049468951251a249ba124214657a215195a8581257a04919528852e99244d2b6695056d9a4419b4a9106e849204496688146ca95954b28d8256ca34a1b12a54256d9a485ab0855356c2154db0085536c08244c4b66881125a30611b2a5782e969544ba609914ec516499b2151352c8a44db00a9536d42854d4b14913561534817b5a4491e9a9495b12a5254a8496556a125925a8496455a125912c56a6498a129915e84a6456a129915684a6444a689916cd1a25449669216cd5a0857b2054362c2150d7b085435ec8550d5b0854366c2150d8b085535ac8544d7b2151352c8544d7b229132c97a44d6b149136ac5244db0061535aca244d4b289136c0a244ca2495535e58554d4554d2056d434814250d201ed2a654b44a9954ec816498b0959812d9a485b0209436c08150db0085432e52454c29125535a44944d59125132e98244d9b2091356c1854d9b1491362ca244d7b2891356ca244c4b649132c59244d89495536092554d89515535e54554d59245136489144d87615536258554db261553611434815a5011356d134814b44d2046153601a944d236a4a0544b04e8512d15a645b30619556c2954d91065535684944c49649131ed2554c49495535c92554cb9545132298554c49615532ad2054c9144d804954054d5850153604a044d21281134aca054c494811352153600914811368ca0545a1285926482954d48661536489244db5261536e95144d2b2555362c9554d2b281132ad2044ca968d516841a660b056913568a044da1069950691a54da14955346eaa5e6995e812a658a04a9968c12aed9a096bb6688246eaa6551baa998a657a2051baa992aed9a216bb66983aed9a614ba566882e992a20ba64688aed8a648a4aa9982e979a211b26a2246c9a9551b26a88aed791256952a9952e994954ba6562aa8496614ba6591aed8a6457baa92552e995450baa99552e994854ba656052e994417652a992c54aa659baa98252eaa6454ba65205281aa654ba65612ae995454ba64514eeaa6614ba642142eaa54c9ba215352e992053baa9822ae884813baa98052e9944cb9528212e54a20552481536158054cb9509435154054d4baa97952eaa661ba12699
  | 1 => 0x3aa969602bb62520aa8a96015aa6513aed8244ebb66153aa995601a4a21536868854e8851553a214144ebb68d80aed89442bb5e510aed8948ebb66150aed1a60e994a950aed7a60ebb62923a219a542bb569835e6aa60d59aa98364aaa60d91aa983aed9860ebb5e9695aeaa5e51baa969aa9645e6bb5e5495daaa5257b5a6995d849a657646a9946c8aa651b16a9946c2aa64a6aa9815aeaa606bb5e581aa979606bb6a581aa949606bb5e481126992069966881a65a0206bb68578aa9495e2bb52562696995891ba657846e995c6bb5e561aed4958449a65614aa995d57aa656146e995a16ba657246e995d51ba6572aed7a60aaa5a528aa9a960aaa52582aed49546aa125825aa995451ba658246e99546aa68182aed4914449a64514ae991469966851a650a20abb4e851a652a1469968051aed795056baa995aa9496616aa659156a99646bb5e998692aa661a2aa9985eeaa6456baa9915daaa66174aa998592aa66172aa99858aaa66142aa9985c6aa66161aa998506aa662bb60991aa975662aa59598aed8164aaa49598aa945662aa69598aa978662aa4a198aa948662bb62491aed79246bb62492aed98256bb62891aed7a262bb62895aed494851ba658546e99486995a921aed2a5629956921a659a485a9aa9855a6aa61549aa985646aa616bb66158126990855ba6421a65a00857b566882d159a2159126882e552a20ba54a884ec52a21b014a8812592a217b64a882e571a20ba5c68856d91a21416468866d21a209b486882e921a217526a885c89aa215226a881489aa217126a880849aa217aa6560aed8250154a2140506885029956913a656a44d69aa980602aa6016baa980aed7354e9958d13aed7344ebb5a980692aa6012baa91346eaa54d2baa953a2049482aa125805a69944ebb5e153aeda854e9964913a219244d79a21532ae8854e8849553aa9186029949553aed82482aa52180aa9586029961553a214044eaa50d80a214054e8828113aed8054e995a923a656a4429956910a219a4428866923a652a442aa44d83a657348eaa54d83a651348d3baa9795ac2aa659baa98126eaa606aa125811ea99495aba65252ae994959baa978aa8495e049a656259e995c571a65782ae9958a995c572a65185a09baa98202eaa60abb6a582126995469946128a65784a0a2aa998286aa6618baa9985eeaa6616baa998aa915662aa05598aa825662aa29598aed8944849a65212ae9948449aa98566eaa616995e158aed89048b45e6885d179a217b5268856d49a21791268852d92a204b64a8850992a20496468852d91a204b646885449aa205126a884849aa2171a6570a65755c2bb5e143aed8150ebb5e140aed8550e9946180a6585602aa48180aed8744ebb61513aed78482bb62920a214a48089aa98068aaa6017baa9135aeaa44
  | 2 => 0x4d92481134958054d5344d205912044d54481130658054d5b4811306d8054dab481135052044cba625102e979440ba56510615534417954d1054d52440ba649102e52a540b05a92306d9a60c1b669506c99a440b16692354d2a44178609234618248d5b64510649314419b485102c11360da1285792c579124ba5a5251e8a94947a125252a449494b95a8252e5a5588a9125626ad495451b28d8261c496441a12598125626444968991124a1648ba61d912e9656441a529980694a65587129910684a6601a1299512982644ba5899112962644ba54991528a16484a2859261d91245756449122d9124482644915c991244b2644912d159484ba5652164419615691252156449484b95692152d9a48449269215680a44db3545206192554d76495535912554cb9495532052554d71495535852554ca1495535052554d21495532c15144d86515535d94554d62515535c54554d61515532854554d21515535d49144c82245135c89144d76615536d18554d64615532e58554cb2615536098554d72615535898554cb1615535c58554d61615532858554d41615534858554c21615536152054d76481535912054d62481532052054d71481535852054da1481532852054d51481534852054d8750d20619434817650d20615434817550d20595434816250d205c5434816150d20485434818728113614a044d7528113594a044d62281135c4a044d76481136152044c21601535d52044d654811306d536016244d205452044cb95a9232e541a22aa29179aa9695e6bb6282546eaa5891baa9785aeaa6091baa98242eaa60aaa46598aed79646aa5e598aed7964aaa5a598aa929662aa65598a659a084b9552882e542a2049246884ec21a21b008688aed89582bb5e560aed8250ebb5e553a204944c49a2153aed0a60d6baa92546eaa5490baa981aa9a9606bb52525126994956ba652546e994611ba6525aed492057ba64814ae99206995a825aed7a2069946852a65a30616baa97842eaa5c51baa96542eaa5e2aa5a57846e995951ba6562aed8a586bb5e96842eaa546aa28d82a653a146bb628154aa996556aa6592aed87646bb5e192aed6a661a7aa99869aaa661a1aa998aed78656bb6a195aed81646aa46198aed78662bb60992aed8a24abb5e9855aeaa6151baa98542eaa616aa65585aed490869956821aed8a049545668816449a216b14a8852c52a219b14a8856d92a204924a882e551a20ba5468866c51a213b146885ed91a218b086885ec21a216b0868856c21a214b0868866c21a22bb5a973aa9595ceaa5a573aa9895cebb62573aa9915cebb66170aed9858ebb5e543aed9850d42a2143aed98502bb5e513aed8944e995a9205e6aa60192aa980646aa6016baa95346eaa4811baa980aed98602aa661802ae8844ebb62913aed7a602885291
  | 3 => 0x915d44a645651299112851649ab20991129726444a205925eda26456b6899112da26441a69598069a86558a285925e8a16484a5c5912c15164576521985d548660a1515955c94866162521985c548661ba144925ac522457b6449156d912445b6449160991245526449114991245b2644916451a261785e8915c97a2456b468922e565484ba5a521611894498b0a5581256a485a1069854ec5a484b9529215ad9a4841a6698506d9a6159a269216149a485655e15852578560495e158125914844b645212e9914859b681212d159085ba464855645908559124214497a215145e8854516a160195e8850656a161b9568210651a21449568216d58a049b4628125518a048b9568210652a161215288552d9a08578609735ed6950db35454066c8250db1209435ed6250d87509436194250d765094362d9250d7b649431ed2550d6b0954366c8150d42595434ad7550d7b585434917550d42585436e95150d9b145434ac5150d6b6454356d9150d84485435ed2150d6b4854366d2150cba625202e969480ba565206a41a54cb95a9206841a6018a029135e80a44ca1461805d5524818b64920549514818a645202e991481a12852066d21480a1485205e15854ca054d132817344d8b5d9132ad2154d2b2151362d7544d8b595135ed6544cba595132e95444cb04a9536882a54d2b229132c16a54d76569135915a44db4569132c95a44da1069534ac5a44d6b169134ac1a54db0069530694a54d87529136194a44d76529134854a54d75529135954a44cb1625135ec8944d1b225136c42954cb15e5132d16944d755a5135d16944d545a5130697954d2b065535d84944c21125535d44944d65125135698244db54a1535688244c492091346c2854dab2091362d7244d5a5c9135297244d695c9131257244d8b589135ed6244d5a589135296244c49589135ed5244c7b549131241854d2b06153688a244d87649136199244d76649134859854c21661535d59244d656491306d9854d5a649130699854d8b2491356c9244db1249130a92554d874955322d2554d84495536d12554c89495535e52554d49495535892554d81495534696554d4a5c5130691554d65515536094554c82515535c94554ca2515536054554c81515530854554d87245136149144c21255535e89144d5a245131689144d82245135489144c52245136889144d5a485135292144ca2485136492144db6615536118554d74615536e58554d69615535098554d92615532498554d81615536458554c91615536252054d6b481536052054d41481532452054db1481535a57044d925c1134956054d85581530494054d8a50d200694054c1a50d80605434808150d20545434805150d206854348186281135d8a044c85281135e8a044d82281135c8a044d5228113544a044d5a4811362d204
  | 4 => 0x44d79065534ac5944d6b1651346c5944d87125136184944d21125535a84944c1a125535e44944d7a2a513568a944d592a51361d8244d8a609135298244c49609135288244db1209135e97244d76589135956244d6a589134a17854d8b549135ad5244d75549132e95244d5a549135295244d69549131255244d28461535a11854da4061535e41854d5a509132e94244d69509135eda244d6b689135a5a244c4968913228a244d6a28913548a244c19661532a59244d74649135919244d546491362d9244c2b661535ed9244d6b6491352d9244c2a661535a99244d82649135899244d52649135099244da2649136c59244d5a249135a49244d6b249134692554d4a605136098144d8a495535ed2554d6b495535d12554d69495536e52554d42495536c52554cb1495536452554c914955361d7144c495c5135c97144d925c5135695144d52545136495144d65455535694144d155155361d4554d8a515532294554d7a515536289144c8a245132889144c49485135ed2144d15615535158554db7615536298554d49615532898554db1615536158044d74481535252054dab481532c52054d8b5c1135d57044d7a5c1134957054d855c1535e9434816a50d20569434815250d20628a044d89281135e4a044d6928113564a044d92281135a52044d7b481134618054d49481135ad134816b4811354913481b1481134852044cb1625102c5794418b565102c5594418954d106e913540ba54d106ac82441ab149106cc52440b1649101ed2a540b0569234c52a541135a95044d7a541b9569106458a48d216695062d9a4417b669106099a440516692356d3a441894a9105652a4413b4a91069d2860db94a1836852860db34555062d914417b6451056d314417a4c5104a9314402b54d236091360d8554d2354d80441a144d2354d20440b45e9695e8a45a4a4685696c969125b15a4491e96a494b95a9251e9a4494ba5e5252d1a94947a525256ad4949579125255a449495a912525684a149579124816e57a2054b668816c99a204494685266d1a1493b468525d1a30601868c52684a15e0a15c5782e97958967525715c5495e167125715c4495e179125626a449589765c5625d1795852a125755e8495857912561525715c8495c57252c815c93b205726cc185d54946168125185a0b46a5515a449545a9125512e5a35444968d512c1a3545a128582525184a049461282c5254555246128285184a1724951545552609755e128525784a0495e128589784a1525e1285a8a05454b668516c99a144b16688252d3a144494a85166d2a1456b149414ad7a654b45a5916184964576125915d4496456512591628496457a1259106849654496099112451648495c99112481648b45e99162d6a644b45a9910692a661b4569912c58a6497a069956184a64576129
  | 5 => 0x58266ca16093b2858268ca2545a6461282d9184a0a9495155e5184a1a3495155d9784a0a9595155a5784a1b15e1285c5784a1a35951568da0545a228151494a045565281152e582145ba208515259a14582668511459a209494e8516093a144824e8515252a14528628152e9795053b205426cc18514b45a99212989644b16259112979644b15e591129696444a565912c5596456a52591569496458912591564496444954991125926444a649912c592644496059112571644495459161d76645875d5912e954644b6629912d18a6457b4a9956d12a655b14a9952c52a6557b229910697a6617b5a9915ed5a6456b569916c95a645a2069955ac5a64587529916194a64576529915d54a64587609916e9516498a54592529826458a14592528516492b0559862d726454a5c9915d9626454a589914a178655ba54991129526452846195528816491b0959862da26455b68991568a164981285925aca26441a46198129816458260591529716455a54591069156554a54591129516455a5059169d48661a65219869548660a15099268948661525219820545655a1521982854866161521985454866051521985ed5924587124915d449244492089166c82245b31449212572244491489166c522453b148916e881249b32049262d922457b6489162d9124528628916c96a2556b468954618a249914689556d1a24928628952e985484ba595216e919615ab1652156d4948419125855256a4847b569214652a561b9569212c15a4859b169210659a61549669215299a48521669855d978561a25e1585c578561915e158669514859a5052156d914854b645212c592448b96142162d5908584624126e8590855b5242116449084125e8854ad1a21558628120492a16184628122c52a16021528850659a21549668214859a214216688506d9a2152168c580a5a31601968c58561785cd7b565605ed925817a5c5606056858d5b6456066d21581b46094362d6250d675e1434a17850d82509435894250d6b649434918150d28605435a18150d42495435088150d1b095434ac8150d275c54359d7150d245c5436c96550d785c5435e17550d255d5435ad5150d25455435951550d42145434ad9550d6b655435e18550d42485435958550d84085434ac8550d8b565206e55a44d705e9536a41a6013b1692056c3a481a6461802818144d6b6492056d924818a6052066c814813b205206ac814817a5c52066c514813b145206ac514815b6452069d85601b96158061d7344d8558d532e98744d875d9135e18544dab2151361d7544d86595135d96544d85595132e98444cb6629132e52a54db10a95361d7a44c2a5a9532e56a54d8b5a9130a91a54d6b569136c95a44db0569130854a54cba625134ac8944cb45e5132e97944d5a5a5135296944cba565132c559
  | 6 => 0x35c19b061704ec185c1b32057361d915cda66457356d925811b655635c1915cd195c9735a5755c1915a163645755c17b455704ad955c142545435a59150d8b4854356d2150cba61d202e9854817b215205ac85481ab2152066c854818b5a5205a55a44d695e9204657a54d715e9805c17a44cb15a9205ac5a480b6461806e51860179461804d5524817b2052062c256018b0558062d914816b645205e9914818b285205eca14816b2852056ca14813b285205e58560169615805658560153615806455854db16158064585600b154d135896344db65cd136d57344d7a58d534696354d695cd135657344d725cd135c17344d1b215135ed6a44d8b569135ed5a44c2a529532d18944d8b5a5135ed6944d7a5a51362d5944d7b565135ad5944cb4565135694944d69525136284944c2a125535e84944d8912513628a944d892a5135e4a944d7b2a5132e96244d1b1491362da244d5b68913569a244d4a689132a5a244d5a289135a4a244c49289130a59854d846491356d9244d8a649135299244c49605136498144d7a4955362d2554da4495536892554d8b5c5134956554d7b545135295144d92505134954554d6a515536894554da15155362d2144d25615535958554cba615535e98554da4615536898554da1615536c18554d18601135a52054d7b481536955348142481532e97044d205815362d6044d7b581135696044d9258113625434817950d205a5434815950d2064543480a150d2062da044d7b68113569a044d9268113495a054d856815354da3481594811352d2044c9b481136452044d7b5651066c824419b1491062c2560d8b649105ed924415b649106e52a541195e9836456a48d2b5e9505ed6a441195a9835e56a441195e9506457a48d6b5691061d9a44021669505d59a44172669102059a48d2b4e9505ad0a48d794a91056d1a48d6b469235ad2a4415b4a9105e52860d694a1835652860d91455506452860d8a4c51056931441254d55045535541a744d836991360da544d835651360d9244d836851360d13601106d57348d2858d836857348d53581106291348d7a44d2356d1348d2854d832c91348d9244d236451348d1348110291795a4a4689695ed69524b9691251e969494b45a525591694947b6a5256a4a9494ba605252a5814947a685252e5a14947a681252d179205795e8811256a095525e8810616a09552528810614a0956b668255259a2057b668810619a094b1668525251a14918628255e5a30614968c18549a3061b268c182e9875886b6857859da15e13b285782e5a4589a92a56269449589175e9682d1695c92a525755e9495857b52561699715c8b954961595185a179461682c16a544b9691516a4a95454b2a5515a9495456a125512a449544a9609515e971608b9689512a5a2545a9285825eca84554b28
  | 7 => 0x4560645635cd79649436499150d8b0495362c21601b3215202e9654816b565204656a6011b5a9535ed6a481195e980645186015a6451346198600ba605202e9714816a64520461956019a285206a5856016954d136495344d8544d536196344d7958d135656344d255cd536497344d2558d5362d7a44d2a5e9535e96a44d2a469535a91a54d6a569136294a44d7a529135a94a44d5a5291362d7944d895a5135e56944d89565135e55944d8b2a5135e9a244d4a289135e59244d49649135e99244c8a495532ad2554ca9495536492554db04955362d5144c49545134951554d5b485135a98554ca96155352d2054c9b481536452054d715c1135956044d6a581134817054d635cd20609434816344d205812044d2b215105ac854417b215106ac215418b0498366c854413b2151062d794413b145235ac5244119569235a52a541914a9505a55a441526691044d3a541694a9106492a4417a64510569914412a645104a19860d35615504955348da044d835e96360d5a5cd236257348d1958d836457348d7b44d236251348d7944d235651348d2554d834aca55a5795a4495e9a94956b525251e8a1495a92852566ca14953b285255d1792057b524812e552205ba148815256a095b45e8816c97a204b15a8525d19a20552668815a51a1492b568185e5a02057b68c1856da3061785d96266ca15e1a5525624ad6a5d52a5a5755a5715c9ab1496166c815c9b9461685e969545a46a5515d8a95456a68d51691a3544ba609512a572545a3689516cca2545a9461286a5784a0a2281516c93a1455b4688266c515093b1454266c81508b45e5914a9496556a525925e4496456912591629916498b5d9915ed6564586595915d965644ba611915ad2a6552b2299146c2a655615e9955d16a645145e9955d95a64564569914ac5a6452b069955e94a6456a529915694a645655299142c826452b145926c0516497a58592569726458b589915ed626456558991569626457b549911ed526456b549915d55264568461955e8816495a2059242c186551b149916c0816497a5059262941648ba50991529a26455b2899162ca26452a49595469256554a6059161d716451a595955c9716452a45595629416457a505915e148661655219862d792444960891125522455b648915e51a26159468986491a261195a8954657a261915a8926251a25569468956491a25589468925a51a249594689256d2a244b9551215ed6a485195a9585e56a485195e9855a55a48549569211255a48519669855a99a48576669215d59a48564669215519a4859a5491266962449a95e1585a57856191595852e5514855b649125e99148548661584652a16119468855255a085b3628125519a0858968021565a00842168c58611a30495468c125891958d8b5e5606c52958d71465705a57
  | 8 => 0x7a605251258149582281516095150d435491844d5246049609516cd5160983545824a178455205a9534816354d82545135a92054eaa46585aa949616aa1258556ca944d7a5a5915a9196555a5a99262952645184a19862d5a4855b68c124ec1254cba54d206cc1854cba545202e931481b558d136c8a944d69649135c17348d6a6a5256a5a1495b05e8812a5825058b5e5914a9696555a645925697a6497a5a9914a91a6556a469955a95a6456a54991569a16496a685925a9a26456a549925ad5a4855a645216e8850857b06170595915817258d735e17358d9258d735c17358d195a9535e56a4817a645136cc8244d2544d535e96344d8958d136496344d855cd535816344d69565130a8a954ca9289136259244d59649135a92554d79481536cc1260d3b205236451a60db25a9504656a541695e9106253a441794e9105653a441924e91044d155418a6451061d7348d695cd235a91348d5a44d235a51348d8554d836811348d6b6a525691a9495745e8815e59a204ab549712e9715897b205725ed6a5456a6a5512e962544a9589516a5a2545b9461282c93a145872a5415d4a9504a9145422a572504a9549412a481509b55a9925e9696498b5a5915ed696452a5e595569696457a4659566c516499b205925a9916497a645925d92a655744a9955912a6558b5e9915857a661745a9924517a6618a52991569616495a5c592529526455a50592569a26458b5c591569626497b5459154951645784a1984614866128521985ed5a48519469855a59a4855a669215959a485ba545216299148578661584a198560b9550216c18a049596682162da3049715a5706ac525817a645605ed91581636
  | _ => 0
def programRaw11 (i : Nat) := packedAt programRaw11Bits (30*i) 30
def program11 (i : Nat) := (programRaw11 i <<< 10) ||| 304
def getProgram11Bits : Nat → Nat
  | 0 => 0x3a24e24d24c24b24a24924824724624524424324224124023f23e23d23c23b23a23923823723623523423323223122023022f11617a22322e22d22c22b22a22922822722621c21b22522422322222122021f21e21d21c21b21a21921821721621521421321221121020f20e20d20c20b20a20920820720620500220403d2032022010272001ff01a01a1fe1fd1fc1fb1fa1f91f81f71f61f50251f41f300d0351f20391f11f01ef1ee1490241ed1ec1eb1ea1e91e80141e71e61e51e41e30141e21e114600c1e01df1de1dd1dc1db1da1d91d81d71d60120121d51d40381d31d21d11d01cf0211ca02d0111ce13c0340010370361cd0231cc1cb0211ca02d1c91c813e1c71c60340011c51c41c31c21c11c01bf1be1bd1bc1bb1ba1b91b81b71b61b51b41b31b21b11b01af1ae1ad1ac1ab01d1aa1a91a81a71a61a50311a41a31a21a11a019f19e01003c03b03319d02b03019c19b19a19919819719619502f19419319202e19119018f18e18d18c18b18a18918818718618518418318218118017f17e00f17d17c17b17a11617917800f17717617517417317217117016f16e16d16c16b10d16a16916810b16716610916516416316216116116015f15e15d15c15b15a15915815715615515315415315214f15115014f14e14d14c14b14a14902414814701814614514414301301301f1421410110fa02d14013f01e0110370360fa13e13d13c00113b13a13913813713613501d13503113413313213113012f03012e12d12c12b12a12912812712612512412312212112011f11e11d11c11b11a11911811700b11611511411311211111010f10e10d10c10b10a1091081071061051041031021011000210ff0fe0110fd0fc0360fb0fa0f90f80f802b02f02e0f70f60f50f40f30f20f10f00ef0ee0ed0ec0eb0ea0e90e80e70e60e50e40e30e20e10e00df0de0dd0dc0db0da0d90d80d70d60d50d40d30d20d10d00cf0ce0cd0cc0cb0ca0c90c80c70c60c50c40c30c20c10c00bf0050be0bd0bc0bb0ba0b90b80b70b60b50b40060060b30b20b10b00af0ae0ad0ac0ab0aa0a90a80a70a60a50a40a30a20a10a009f09e09d09c09b09a09909809709609509409309209109008f08e08d08c00508b08a08908808708608508408308208108007f07e07d07c07b07a07907807707607507407307207107006f06e05906d06c06b06a06906806706606506406306206106005f05e05d05c05b05a05905805705605505405304505205105004f04e04d04c04b04a04904804704604504404304204104003f03e03d03c03b03a03903803703603503403303203103002f02e02d02c02b02a02902802702602502402302202102001f01e01d01c01b01a01901801701601501401301201101000f00e00d00c00100b00a009008007006005004003002001000
  | 1 => 0x748648548448348248148047f47e47d47c47b47a47947847747647547447347247147046f46e46d46c46b46a4694684674664654644634624610670670d846045f45e45d45c45b45a30308b0ab0ab45944a0650a80a74580af0ae4574564554544534520ad45145044f0f344e2fc44d0e50f20880a644c0ab44b44a0654494484474464454444434420aa0a90a844144043f43e0f243d43c43b43a43943843743643543443343243143042f42e42d42c42b42a42942842742642542442342242142041f41e41d41c41b41a4190874184172eb41641541441341241141040f40e40d40c40b40a4094084070d14060d04050e24044034024014003ff0ec3fe0eb3fd0ea3fc0ef0ee0ef3fb3fa3f93f83f73f63f53f43f33f23f13f03ef3ee3ed3ec3eb3ea3e93e83e73e63e53e43e33e23e13e03df09d3de3dd3dc3db3ba3da3bf3d93d83d73d63d53d43d33d23d13d03cf3ce3cd3cc3cb3ca3c93c83c73c63c53c43c33c23c13c00980b63bf0dc0423be3bd3bc3bb3ba3b93b83b73b63b53b43b33b23b13b03af3ae3ad3ac3ab3aa3a93a83a73a63a53a43a33a23a13a006108107f39f39e39d39c39b39a39939839739639539439339239139038f38e38d09538c38b07b38a38938838738638538438338238138037f37e37d37c37b37a37937837737637537437337237137036f36e36d36c36b36a36936836736636536436336236136035f35e35d35c35b35a35935835708f35635535435335235135034f34e34d34c34b34a34934834734634534434334234134033f33e33d33c33b33a33904133833733633533433333233133032f32e32d32c32b32a04532932832732632532432332232132031f0cb31e31d31c31b31a3193183173163153140b231331231131030f30e0c830d30c30b04f30a0ed0430400ad0ac3093080ac30730630504e3043030430403023013002ff0a72fe0ba2fd2fc2fb2fa0a62f92f804e2f72f62f52f42f32f22f12f02ef2ee2ed2ec0a40a42eb0872ea0f00dc2e92e82e72e62e52e40752e32e22e12e02df2de2dd2dc2db2da2d92d82d72d62d52d42d32d22d12d02cf2ce2cd2cc2cb2ca2c92c82c72c62c52c42c32c22c10592c02bf2be2bd2bc2bb2ba2b92b82b72b62b52b42b32b22b12b02af2ae2ad2ac2ab2aa2a92a82a72a62a52a406b2a32a22a12a029f00b22529e29d1f902529c29b29a29929829702c2962952942932922912901b324f28f28e28d28c28b28a28928828717716d22f23028628521c28403228302701a02028228128027f27e27d02527c27b27a27900d27800d27727527627503927427327227127026f26e26d02426c26b26a01400c26901f01f2680120381d226726626102326526426326226126025f02c25e25d25c25b25a25925825701d25603125525425325225101001025024f0330
  | 2 => 0x6f46f36f26f16f06ef6ee6ed6ec6eb6ea6e96e86e76e66e56e46e36e26e14d00456e06df6de6dd6dc6db6da6d96d86d76d66d56d46d36d26d16d06cf6ce6cd6cc6cb6ca6c96c86c76c66c56c46c36c26c16c06bf6be6bd6bc6bb6ba6b96b86b76b66b56b46b36b26b16b06af6ae6ad6ac6ab6aa6a96a86a76a66a56a46a36a26a16a069f69e69d69c69b69a69969869769669569469369269169068f68e68d68c68b68a68968868768668568468330d68268168067f67e67d67c67b67a6796786776766756746736726716700e866f66e66d04404466c66b66a66966866766666566466366266166065f65e65d65c65b65a65965865704f65665565465365265165064f64e64d64c64b64a64964864730408a6466286260aa0a964564464364264164063f63e63d63c63b0b92fa63a08906463963863763663563463363263163062f62e62d62c62b62a62962862762662562462362262162061f61e61d61c61b61a61961861761661561461361261161060f60e60d60c60b60a6096086076066056046036026016005ff5fe5fd5fc5fb5fa5f95f85f75f65f55f45f35f25f15f05ef5ee5ed5ec5eb5ea5e95e85e75e65e55e45e35e20a55e15e05df5de5dd5dc2f05db5da5d95d85d72ec5d65d55d45d35d20c35d15d00c35cf5ce4190c35cd5cc5cb5ca5c95c85c75c65c55c45c35c25c15c05bf5be5bd5bc5bb5ba0f10a35b95b85b75b65b55b45b35b20e05b10df5b00de5af5ae5ad5ac5ab5aa5a95a85a75a65a55a45a35a25a15a059f59e59d59c59b59a59959859759659559459359259159058f58e58d58c58b58a58909e5553aa5883ae58704258658558458358258158057f57e57d57c57b57a54157957857757607757557457357257157056f56e56d56c56b56a5695685675665655645635625615600dc55f55e55d55c55b55a55955855755655555455355255155054f54e54d54c54b08054a54954854754654554454354254154053f53e53d53c53b53a53953853753653553453353253109653052f52e52d52c52b52a52952852709307909151e3820cd52606052507752452352252152051f51e51d51c51b0cd51a51951851751651551451351251151050f50e50d50c50b50a5095085075065055045035025015004ff4fe4fd4fc4fb4fa4f94f84f74f64f54f44f34f24f14f04ef4ee0704ed4ec06e4eb4ea0064e94e84e74e64e54e44e34e24e14e04df4de4dd4dc4db4da4d94d84d74d60554d54d432a4d30054d24d14d04cf4ce4cd4cc4cb4ca4c94c84c74c64c54c44c34c24c14c04bf4be4bd4bc4bb4ba4b94b84b74b64b54b44b30ca4b24b14b04af4ae4ad4ac4ab4aa4a94a84a74a64a54a44a34a24a14a00b249f49e49d49c49b49a3120b10b14994984974964954944934924910db0be49048f48e48d48c48b48a48948848
  | 3 => 0x92c92b92a92992892792692592492392292192091f14a91e91d91c11d21c11891b91a91991891791691591491391291191090f90e90d90c90b90a9099089079069059049039029019008ff8fe8fd8fc8fb8fa8f98f88f78f68f58f48f38f28f18f08ef8ee8ed8ec8eb8ea8e98e88e78e68e58e48e38e28e18e08df8de8dd8dc8db8da8d98d88d78d68d58d48d38d28d18d08cf8ce8cd8cc8cb8ca8c98c88c78c68c58c48c38c28c16608c08bf8be8bd8bc8bb8ba8b98b88b78b68b58b48b38b28b18b08af8ae8ad8ac8ab8aa8a98a88a78a68a58a48a30e58a28a18a089f89e89d89c89b89a89989889789689589489389289189088f88e88d88c88b88a88988888788688588488388288188087f87e87d87c50587b87a87987887787687587487387287187086f86e86d86c86b86a86986886756086686586486386286186085f85e85d85c85b85a07f85985871385785685585485385285103e85084f84e84d84c84b06f84a84984884784684584484384284100584083f4d583e83d83c83b83a83983883783683583483383283183082f82e82d82c82b82a82982882782682582482382282182081f81e81d81c81b81a81981881781681581481381281181080f80e80d80c80b80a8098088078068058048038028018007ff7fe7fd7fc0bb7fb7fa7f97f87f77f67f57f47f37f27f17f07ef7ee7ed7ec7eb7ea7e97e87e77e60ba7e57e47e37e27e17e07df7de7dd7dc7db7da6267d97d87d77d67d57d47d37d27d17d07cf7ce7cd7cc7cb7ca7c97c87c77c67c57c47c37c27c17c07bf7be7bd7bc7bb7ba7b97b87b77b67b57b47b37b27b17b07af7ae7ad7ac7ab7aa7a97a87a77a67a57a47a37a27a17a079f79e79d79c79b79a79979879779679579479379279179078f78e78d78c78b78a78978878778678578478378278178077f77e77d77c77b77a77977877777677577477377277177076f76e76d76c76b76a76976876776676576476376276176075f75e75d75c75b75875a75975875775675575475375275175074f74e74d74c74b74a74974874774674574474374274174073f73e73d73c73b73a7397387377360b80c009773573473373273173072f55872e72d72c72b72a72972872772672572472372272172007e0bf71f71e07c09471d71c71b71a71971871771652151f07871571471371271171070f70e70d70c07670b70a7097080497077067057047037027017006ff6fe6fd6fc6fb6fa6f90596f86f76f66f5006
  | _ => 0
def getProgram11 (i : Nat) := packedAt getProgram11Bits (12*i) 12
def live11Bits : Nat → Nat
  | 0 => 0xabfecffabfecffbbdeaffbbdeef7b6fecffb3fecffa7fecffabfe9ffafdecffabfeaffabfeaffbbdebf7b3fecffabfeaffabfeef7abfe9ffabfedfbb3fecffb3feaffb7decffabfeaffb7fcaffbbdebf7bbdeaffb3fecffb3fedfbb3fecffabfe9ffa7fe9ffafee9ffa7fe9ffb7de9ffa7fecffb7decffb3feaffabfeaffb3fecffb9feaffabfeaffbbdecffb3fecffb3fecffb3fecffb3fecffabfecffb3feaffb3fecffb3fecffb3fecffabfeaffabfeaffa7fe9ffa7feaffafdeaffabfecffa7fecffb3fecffb3fecffb3fecffabfeef7abfeef7b6fed7fb3fecffa7fe9ffabfeef7bbdeaffa7febfbaffcef7a7feaffabfe9ffa7feaffbbfaaffabfe9ffb3fecffb3fecffb3fecffb3febff3fdcff733fecffb3fe7ff27fe9ffafeeefbafeebff2ffcdff2feebfbafeebfbbfdcff73beebfbafeeefbbbeeefbafeefebbdfcffabfaebff3dfcfebbdfcfebbfecffb3fecffb3fecbfbbfeccffb3fecffb3fecffb3fedfbbbeedfbbbeedfbabfeaffa7fecffb7de9ffbafeaffb3fe9ffb7deef7bafeebfb3feef7bafee7fa7fecffb7fcaffbbde9ffb3feef7b9fee7fb7eedff33fecffb3feaffbbeeaffabfeeff33fecffb3fecffb3fecffb3fecffabfeef7a7feef7b3feaffb7de9ffb9feaffbbdeebfb3feaffabfeef7abfeef7bbf6ef7abfeef7b3fecffb3feebfbafebfbafeebff2feee7fb9fedff2feebfbaffcbff37fcdff3dfcdff2feebfbbbfcbfbbbfcbfbaffcbfbbfeabfbbfecffb2ffcffb3fecffb37fce7fabfecffb3fecffb3fecffb3fecffb3fecffabfeaffb3fecffb3fecffbff4ffd3ff4ffb23ff8fff1ffcf7e3ffcf7f3dfc7ff1ffc7fffcd8fff7cf8ffeb7fcf7e3ffcbff5dfcfbf3efcfbf7cfcfbf2ffdb7f3dfcf7e3ffaf7f3dfcf7f3df9f7f2ffcdff6dfcf7f3ef8ffe3ff8ffe7dfcf7e3ffbf3efaf8ffe3ff9fbefafbfb6fedf7b73dfdf3e3ff8ffe3ffafbebefbf3efedbebefcffe9ffadfeb6bdfcbfe3ffcf7f3dfcf7f3dfafef3dfcf7f3dfcf7f3df9fbf3dfdebeeefb7beeefbbbefafafbedefbdbeeefbf3eeefbf9ef6f9fbefedbdbefcfbfb7fa7eebffadbfb7fcdf6bf2ffcf7ebefa7ff3dfbfb6fedbfb6befef3fbcfef3e7efafbefafafbedefbbbefafef3fbebeebffa7eebfbafefafbebf6bfbafbebe7efff377edbfb6fedf7b73efcff77edcf7ebefbebfbebdf3fbcffabff8ffe9ebeff6bff8fdfb7fe9feb7fadffa7fe9bfb67efff37dedffa77edcfefbe7e7bfbe7bebe7efbebefafbfb77edcfbf3fbdfb77edcfef7ebdebe3fecbfb1fecfba3fe8ffa3fe8ffb2fe8ffa3fe8ffa3fe8ffa3fe8ffa3fecf7a3fe8ffa3fe8ffabdecf7abdeaf7b3deaf7a3fe9bfabde8ffabdeaf7abdecf7b3de8ffabdeaf7b3deaf7a3feaf7abeeaf7afecafbabde9fbb3de9ff27eebf3a3df8f7ffa5f6b6bcffe363de8f7a3de
  | 1 => 0xfff3f7efbfbefefbfbefefff3efefbfbefefbfbf3ffcfff3ffcfff7fbcfff7fddfef7fddff7dfbfedebfffedf3ffcfff7fbafffff3f6fffedffb6fefbfbefefbfbefefbfbefefbfbffedff9efefbfbefefffb7befffb77efdfbf7efdfbffebbfbefefbfbefefdfbf7efdfbf7efdfbf7efdfbffebbfbefefbfbffebff3fbefefbfbefefbefefff3ffcfff3ffcfff3ffcfdfbf7effebf7efff3efefbfbefefdfbf7efefbffcfbfbefefdfbf7efff3efeffbbffcfbfbefefff9efefefbfbefefbfbefefbfbefefbfbefefbfbefbfbefefbfbffe7febffaffebffaffebffaffebffaffebf7efdfbffebfebffaffebffaffebffaffebffafffaffebfebffebffaffebffaffebffaffebdfbf7efff9fbeffebffaffebffaffebffaffebffaffebffaffebffafefbffedffb7fedffb7fedefbfbeffebffafffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7feddfbefefefbffafffb7fedffb7fedffb7fedffb7fedffb73ffcfff3fffebfbeffebf3ffcfff7fdcfff3ffcfff3ffcfff7eff7dfdf7afffbefaffffeddfeefdfef7f3ffdbffedfef7f77fdf7f3ffef7ebffffb6fefdf7f7fbdfef7dfdf7fbdfef7fbdfef7fbdfef7f7fbaffebffefefbfbcfff3ffef7fbdfef7fbdfafffbdfafffbdfafffbdfcfffbdfefefbfbefefbfbefefbfbefefbdfcfffbfbef7fbdfcfffbdfdf7ebffef7fbdfdf7f3ffdff7fedfebffaffebffaffebffaffebffaffebffaffebffedfebffaffebffaffebffaffebffebffaffebfebffaffebffaffebffaffebffaffebffaffebffaffebffaffebffafffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedffb7fedcffebfe9ffa7fedf7b3fe9ffabfe9ffa7fe9ffa7fe9ffa7fedf7b3feaffb3feaffb3fecffb3fee7fa7fecffabfeaffbbdebfbaffcaffabfebfba7fe9ffafeebfbafeeff3afeeff3b3fe9ffbbdecffaefe9ffa7fe9ffb3feaffbbdebf7abfeaffabfeaffafdeaffabfeaffa7fecffb6fe9ffb3fedfba7fe9ffa7fe9ffb3feaffabfeaffa7fe9ffabfebfba7febf7abfedfbabfe9ffa7fedfba7fe9ffbbdecffb3feaffabfeaffb3fecffbbdecffabfeaffabfecffabfeaffa7feaffa7fe9ffa7fe9ffa7fecffabfebf7abfecffb5fe9ffb7eeeefbbdebdfafdeaffabfeef7abfe9ffabfebfbabfeb7faefebdfafbebf7abfe9ffb3fecffb3feaffb3feaffabfebfbafeeff3affcaffabfeaffa7fe9ffa7fecffb3fecffb3fe9ffa7fe9ffabfecffabfecffafeebfbaffcdfbbbfcbff37fcdfbafeeefbbbfcdfbb7eefebbfeabff2bfeaffabfeaffa7fecffa7fe9ffb3fe9ffb3fecffb3fecffabfe9ffa7fedf7a7fe9ffb3feaffb3febf7abfeef7b7deef7b3feaffabfeaffb77eddf
  | 2 => 0xbf5ffcffe7ffd7fe7ff9ffe7ffcffe7ffafffbdfcffebffdbff3ffcfff7fdaffe7ffcfff3ffafff3ffcfff3ffcfffcffd7ffcffe7ff3ffcffebffafffbfbaffebffe7fe7ffafffbdfdbfe7ffd7ff7f7d7ff5ffdfbf7f7df7f3ffcfff3ffcfff3ffdfbf7efdfbf7efdfbf7eff3febffafff6fff5febffaffffcfbfbfeeff7bffcfff3efefff3fdeff7bffcfff3efefbfbfeeffbbffcfbfbfeeffbbffafbfbffaffebffcfbfbefeff7bffcffebffcfbfbefefefefbfbafffbfbcfff7fddbff3ffbfbefefd7ffff9affebffd7febffbfbe7ffdbff6ffaffefef9ffebffefef5ffe7ffeeffebefeffbbfdefbfbfeeffdbff6ffebefeffdbfbefbfbfeefdfbfbefbfbf7efdfbf7efdfbf7efdfbf7efbfbffcfdfbfbefefbf7efffafbefbfbefefbfbffcfff3ffcfff3ffcfff3ffcfdfbf7efefbfdeff7bf7efff3f7efbfbfeeffdbff6ffdbfdefbfbefeffebefeffebf7efefbffcff7bfdefdfbfbefbfbf7efbfbfbefbfbefefefbffcfdfbf7efff9efefbfbefefbfbf7efdfbfbefff3fbefffafbefefbfbefefbfbefefbfbefefbfbefefbfbefefbfbefefbfbefefbfbefdfbfbefbfbf7efdfbfdeffebffaffebffaffebffaffebffaffebffaffebfeefff3feefefbf7effebfbeffebf7effebffaffebffaffebffebffaffebff3efeffebffaffebffaffebffaffebffaffebffaff7bffedffb7fedffb6feffbbfeeffebffafffb7fedffb7fedffb7fedffb7fedffb7fedffb7befbfbefeff7bffafffb7fedffb7fedffb7fedefefbfbafffbfbefbf7efdfbe7ff9ffefefefef6ffdff77efdfbf7efcfff3ffcfff3ffcfff3ffcffe7ffcfff3ffcffe7ffd7ff9ffd7fffafaffebffbfbf7efdfbffe7f7bffafffb77efffb77dfdf7f7dfef7fbdfef7f6ffafff6ff9ffe7ffdbffaffef7faffafffbdfef7fbdfdfefbdfdbff6ffdf7f3ffcfff7dfcfff7efdfbf7efdfefefb9fffaffebffedffb7fbdfef7fe7febff7dfdf7fbdfebffedfbf7efefbfbf9fff77fbdfef7fbdfefbffcfffb77fbe7ffddffeefdf7f7effb7fedfcffe7ffddff7dfdf7dff7bfddff77dfcfff3ffcfff7efdf7f3ffbdfe7ffdbfeffbdfee7ffdf7f7dfdf7f7dfef7f7dfdf7fbdfef7fbdfef7fbdfef7fbdfef7fbdfef7e7ffef7e7ffef7ef7f9ffedffdf7fbdfefeebffef7fbdfcfff3ffcfff3ffef7fbdfef7fbdfef7fbdfef7fbdfafffbdfef7ebffaffebffef7f3ffcfff3ffcfffbdfeff79ffe7ffbbfe7ff9ffe7fe7ffbdffbfbefefbfbefefbfbefefbfbcfff6ffdbfe7ffaffe7ffe7fedffdf7f7fbbfbebff9fff7dfcfff3ffcfff3ffcfffdbfe7ffddfef7fbdfcffebffef7f3ffeeffbdfdbff6ffddff6ffdbff77fddff6ffcfff7fbdf7f5ffd7ff5ffd7ff7bfd7ff7f7d7ff7df9fff7dfcfff3fff3fefefffb6fefbfbefefff3ffcfff3efefbfbfeefbfbefefff3efefbfbffc
  | 3 => 0xefdfbfe7fafff3ff9fff3ffebfe7ffafff9ff9fff3ffcfff3ffdfbf7ef9fff3ffdfbefefe7ff9ffdff77ef9ffebffbfbebffef7f3ffcfffbdfef7e7ffcffebffafffb7fedfebffcffebffafff3ffcfff3ffafff3ffcffebffafff3ffcfff3ffcffebffaffebffcfff3ffaffebffedff3ffafffaffafffbbfe7ff3ffcffebffaffebffcfff3ffafff3ffaffebffcfff3ffcfffaffcfffaffcfff3ffcfff9ffe7febffef7fbdfafff3ffcfff3ffcfff3ffcfff3ffcfff3ffcfff3ffcffe7ffaffe7ffcfff3ffcfff3ffcfff7dfcfff3ffcfff3ffcfff3ffcfff3ffe7ff9ffeefebffafff3ffe7ff3ffcfff3ffd7ff3ffcfff3ffdfbf7efdfbfb7faffebffebffaffaffefefbfbfaffcffebffafffaffebffaffedffaffbbfebffff3fbefbfbefef9ffe7ffbbfef7f9ffebffafff3ffcfff3ffbfef6ffdbff7fbbdffd7fe7ff9fffedeeffb7fedffaffebffcffedffbbfef7fbefefefe7ff9ffe7ffdbfeefedffe7fffebfdbefefbfbf7efdfbfbefefbfeeffbbefefbfbefefff9efefbfbefefdfbffcfbfbefefdfbfbefbfbefefbfbffcfdfbfbefff3ffcfff3ffcfdfbfbefefbefefbfbefefbfbefefbfbefefbfbefefdfbf7efdfbf7efefbffcfbfbefefff3fbefefbfbefefbfbefff3fbeffebffaffebffaffebefeffebefefbfbf7efefbffaffebffaffebefeffebffaffebffaffebffaffebffafbfbfdefffb7fedffb7fedffb6fefffb6fefbfbf7efefbffedffb7fedffb7fedffb6fefbfbf7efefbffaffebffedbfbefefffb7fedffb7fedaffebffaffedffaffebffafff3ffcfff3ff9ffe7ffcfff3ffcfff3ff9fff3ffcfff3ffcfff3ff9ffe7ffcffe7ff9ffe7ff9fff9ffe7ff9ffeeff9ffdfbf7effebffafdfbf7efdfbfbefefbf7efffb6feff7bf7efffb77efdfbefeff7bffe7efbfbefffb7bdfdf7ebffafffaffef7fb7febff3ff9fff3ffdbfebffdbffbdfdbff7dfdbff77fdf7f7df9fff3ffcfff3ffcfff3ffd7ff7efdfbf7efdfbe7ffafff77fdbfefefafff3ffdf7f6ffef7f3ffcffebffdbfebfff5ff9ffdff6bffcffebffafff3ffdf7fbdfcfff7efcfff6ffafff3ffcffeeffbf7ebffbfbf7efd7ffd7feeff9fffebfcffeeff9ffb7ffcfffebf7efdff77fdfef7fbdaffe7ffcfff3ffcfff7efdfbf7efcfff5ffcffefefbfbe7ffdf7f7df9ffe7ffdf7f7dfef7fbfbef7fbfbef7fbdfefef3ffcfffbdfef7efef9fffbdfbfbefefef7fbdfefefbdfef7fbdfebffaffafffb7fef7f3ffcfff3ffcffebffcffebffafff3ffcfff3ffafff3ffcfff3ffcfff9ffcfff3ffcfff3ffcffebffafff3ffedff3ffe7ff3ffef7f9ffcffebffaffebffcfffbfbafffbfbef7f9ffcfff3ffefef3ffef7f3ffe7ff9ffe7ffbf7e7ff9ffeeff9ffe7ff9ffe7ff9ffafffbdfef7fbdfaffefefef7fbdfaffefef9ffefefaffebffefef5ff9ffe7ffdf
  | 4 => 0x3effff7fffdffbffefffbffdfffbfdfff7ff7ffffbffefffbfefeeffbbfeff7bfeeeffbfeebfbf3ffcfff3ffcfff9ff9fff7efbfbe7ffbfbe7ff9ffefefbfbfbeffbbf3ffcfff6ffcffebffcfff3ffcfff3ffcfff3ffcfff3ffcfff3ffcfff3ff9fff3ff9ffeeffedffeeffbbfbeffbbf3ffcfff3ffbfbffafdfbfbefefbffaffdbfbefdfbf7efefbfbeffebffedbfbefefcffe7ffcfff3ffcfff3ffcfff3fffebf3fffbbfbefdfbf7efefbffafdfbebffcfff6ffcffe7ff9ffeeff9fff3ff9fff3ffcfff3ffe7ff7efcfff3ffcfff3ffcfff3ff9fff3ffaffebffcfff3ffcffebffafff3ffcfff3ffcfff3ffafff3ffcfff3ffcfff3ffcfff3ffafff3ffcffebffcffebffeeff9ffe7ff9ff9fff3ffcfff3ffcffe7ffcfff9ffe7febffd7ff3ffdfbfaff9fff3ffafffb7fefbfbefefbedffb7fefef9ffebffcffe7ff9fff3ffeeff9ffcfff9ff9ffe7ffcfff9ffcfff9ffefbfbeffebff6fefbfbeffebfbeffebefefdfbf7efbfbf7efdfbf7efdfbf7efdfbf7efbfbfbefefbfbefefbefefbfbf7efdfbefefefbfbefefbffaffebffaffebffaffebefefff3ffafbfbffaffebffafffb7fedffb7eeffdbff6fffb7fedffb7defffb7fedffb6ff7bdfeeff9ffedffaffefefaffefefbdff3ffcfff3ffcfff3ffdfbf3ffcfff3ffcfff3ffe7fffaffebf7efdfbf7efefbfbefefbefefefbfbefefbffafafffbdfcffebffdbff3ffaffefefebfebffaffe7ffcfff6ffdbff77fcfff3ffcffe7ffcfff7
  | _ => 0
def live11 (i : Nat) := packedAt live11Bits (14*i) 14
def rules11Bits : Nat → Nat
  | 0 => 0x554a894d292514a093d2724d49892d252493fc92123a4648a91121a424829011fa3e47a8f11da3a4728951c23746c8d517a2f4688cd192314608bd1722b45a8b115a2a4528a113a2644a89111a224428810fa1e43a8710da1a4248450821943085d0b21042a85109a1242484908a1041e83906a0c41682904a0840e81902a0440680900a003fe7f8fe9fc3f67e8fc9f83ee7d8fa9f43e67c8f89f03de7a4f71ed3d87acf51e93d079cf31e53c878cf11e13c077cef1dd3b876ced1d93b075ceb1d53a8630e99d23a261cbd9cb3a073ce71cd39872ce51c939071ce39c638a710e19c2382700df96737c6f4cf1713785c8dd9ba3726e0db98436c6d4da1b33646c4d71b035e6b8b89ad3586acd51a935069cd31a52d6690b59a3344684b59a033e678ce97633860ccd99a332660c618c31665ccb1952f6650c9992322640c797b31c634be18c316628c498830e550c31852a2610c19822aa604c017f2fc5f4be1732f65e4bc97a2f25dcbc1772ec5d4ba1732e45c48f9702de5b8b616d2d85acb51692d059cb39662ca590ad1582c6588b09602be578ae95a2b0570ad95a2b0564ac1572ac554aa1532a4544a814f29c534a694c296528a494828e518a2944286508a094027e4f89e93c2764e89c93826e4d89a9342664c89892c2604bc9712d2584989592a2524a09392624a490919222444849011f23c4748e1112364308d00921c4648c10d218024049172124340491522c4307a8fe0120248710d0124548591222445085113082448899132244348911122043c8210420840c0490e0124340480921842c85105210424831062124188290820e4188280920840c0480920440881102012024808fb1f64007f8fe1fa3d07e0fb1f63e47d0f91f03dc7b0f51e8024798f21e23c0048ef0120fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e3b8768ec1d63a8748e81ce398728e41c6388708e01be3786e8dc1b63686c8d81ae3586a8d41a6348688d019e338668cc196328648c818e318628c4186308608c11802fc5f0bd1782ec5d0b91702dc5b0b51682cc590b11602bc570ad1582ac550a915029c530a514828c510a114027c4f09d13826c4c8991342644c89812e25c4b09512824c4909112023c4708d11822c4508911021c4308510820c410811001fc3f07d0f81ec3d0790f01dc3b8770ec1d43a0730e41c43806f0dc1b43606b0d41a4340670cc194320630c41843005f0bc1742e05b0b41642c0570ac1542a0540a61482885009e1382684c0961242504909011c2304608a110218420821001f83f07e0f81e83c0760e81c83806e0d81a8340660c81883005e0b81682c0560a81482804e098128240460881082003e0780e81c0360680c81802e0580a8140260480881001e0380680c0160280480800e0180280400600800800
  | 1 => 0xbb0b62cc558a31361ec4988b1061ec3986b0c616c2982309610c1d83305608c1181b03604b9980af6600bfd7faff5febfd7bafe5fabf17dafa5f2be17baf65eabd1772ee5e6bb8afaf25e2bc1782ef5dcbb5762eb5d4ba5702e85ceb9972ae45c6b7d712e15c0b7d6eade5bab716dada5b2b616bad65aab5169ad25a2441682d02241082128c53cac557a9e578ac56791923047167112518424881102204408800956640d66aa6518a315791721245c84ab8552a3084009012aa48a915598b2d6591622c1054884021e1047aa8c22a4554628c518a314628c21642d4628c518acc201102204415d841012acc812aa594aad5590c2204415e2bc554471542c9590b1c8b9112244456310158a431622aa20ead086009220abd4f0f153c4415e1105764414da9a58644488912222b0878ac15803c4788f1220af15e110220abc812b756eaf15bab756e3cd48910220afc7e11221a4408800957c1095ea9e21002404a8c206af086110562aec881101eca308590b22aad804908574ae486ab8518acd599101ea4407a9105663d404a8c566acc880f52203d48810d21844088110518ad1482b42044095b2b756cad15a102204ad15a902204ad95aa905684095a2b456a408812b4568a4148290566a31590f55184454ca8c518421462b1520a308428c518ac1578fb1f43ec7d8fb1f63ec7daae55a3ec7d8f553ca7c7aaac5581054b2ad1f63ec7d0f552aab1562ac558ab1562ab522aa148aab554a8d51aa354ca4548a91522a44202a952ea914baa45223e94c8fb548a914fa911f63ed522a45223ec7da915323e9450fb546a8d51aa654ca8d5190f546a9948a91550a9950aa721c4494b91001244488aa4548a987890e21c4388711121c4380480921a3d47aaa5012448868f5548a9151913544441509102204408711052e444880f55404448890d528a354fa9f53ca788729c21ca7488a9d53aa754e29b5344354ca8a514a608929752c3ed4b2951e643486a94224a508829321aa4148290522a4948a901e43d54728f51ea3d4728d518a308428b210a281f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1fa89510a1d4327850aa1141a82502a013fa7e4fa9f13da7a4f29e13ba764ea9d139a724e29c137a6e4da9b53626b4d49a5342674cc995322634c49853025f4bc9752e25b4ae9692ca574b095d2b2
  | 2 => 0x68ad14a2744a88d10a1f43a86d0ca1742a84c5ea113f283d06a0b41281d028d335a80d009ff3fa7ecfc9f73ee7d4f99f33e27bcef9ed3d6754f49e73ca78cf09df3ba76ceb9d93ae684ea9d33a273ce69cb3966d4da9c938e6bce28c318a70ce09bf37a6acdd9b936e694da9b33666c4d79ad3566acd59ab35667cd49a734a68cd099f33a66ccc99732a64cc899131e634c595131261c719611c6614c19512a2604bf9512a25f4a797b2f25dcba9732e25bcb696d2d6544b49672ca544b19612be574ad9592ae554a99512a253ca694b29251ca29432824fc9e93b2724dc919352664c49792d2564a4939252464848f91d2324648d91922e4548991121e4348590920e414819011fe3f47d8fb1f23e47b8f51e63c4778ed1d63a4738e51c63846f8dd1b63546b8d71b235c6a8d31a233c668cb196324638c51862b4608bf17a2ec5c8b716a2cc588af15a2ac548a914a29c528a314227c4e88b13622c4c89912e2544989111e2344588b11221c428831021fc3e87b0f21243b8750e61c30786f0da1ac348670c9934318610bcc6c2e85ae5216122724ec1b5c2b8570aa14c2884f099c6425848cd4dcb6f84708a10c206de611c641f83d0760e41b834eecd3c1983105cd3b6f82d0560a4138250460840f6df03a06c0c816e9604ba45bb02a04c0880f01a02c04806ed5ca2e45c700a00c01760dae003ff7feff9febfc7f6fe9e43f97f0cddfbbf67eafd19bbf37e6fc9f8bf07defb9f6bed7d8fad9bbea7d2fa1c1b83794f9df330760ec1df2be47c6f89f13bc60ec1df0be07be624aab7e7b2f79eebdc79af59ed9547b4eb9bf3d97b0e05ebbd67aaf5183bd37a4f39e8b817a0f3de73cd798e89e5bca794f1de53c978cf21e3bc678cf19debc578af11debc3784f05debc077eef9debbd778ed9ddbba772ee1dbbb176ced5da3b3764ec5d83af75ceb5d63a4756ea9d4ba872ae51b8ba75cee9983ba571ae35d23a3744db5d0b322a0db5d039f73ce75ce39b6d6e69ccb26730e5dcb395728b9dc9b92722e39c838e71ee39c6b8b716dbdc638b716e29c4b836fce21c3b8670ae05be37d6f6e11c23816f8df5bf383706df9c13816f8dedc037f6fcdf5be37b6f4de9b636c6dadb1bcb786eedd9bab746dedcdb93716dedb5b82f06deb75b6b6e5e0db5b636b6d4d91b4b646c8d35823646c8d35b43436ced99b2b646c4d8d82362616d85923606becddaf35d6b8d6dad35966ed61abb2a250d41ab3556a8d4c9d13a6a4131a8b4d698d11a8346682d3da5b05696d39a6b4d69ad31a5b29694d25a434768cd159e344686d0982304682d019fb3e67acf182b3b674c6d9bb3926ece19bb2e65ccb97fb365fecd57fb34666cc998b3065ecb996aff658cad95329650c9c999532a6c659330764ac9191b22634c858a31e640c7d8f31d638c6d8d31962ec618
  | 3 => 0x67ecfaa308103f07e0fc1f83f07e0fc1f83f07e0fc1f83f07e0fc1f83fcf99ef3d679cf19df3b675ce99cf39671ce19bf3766dcd99af35669cd199f33665cc998f31661cc197f2f65dcb996f2d659cb195f2b655ca994f29651ca193f2764dc9992f25649c9191f23645c8990f21641c818ff1f63dc798ef1d639c718df1b635c698cf19631c618bf1762dc598af15629c5189efce26c4b89311e22c438830fe1ec3b8730de1ac338630be16c2b85309e12c2384307e0ec1b83305e0ac1382303e06c0b81301e02c03802ffdfebfb7f2fddfabf37e2fbdf6beb7d2f9df2be37c2f7deebdb7b2f5deabd37a2f3de6bcb792f1de2bc3782efddebbb772edddabb3762ebdd7bad756ea5d3ba574ae8dd0b9f73ae6dccb9772ae4dc8b8f71ae2dc4b8770ae0dc0b7f6fadedbeb7b6f2dddbab736e2dbdb6b6b6d2d9db2b636c2d7daeb5b6b2d5daab536a2d3da6b4b692d1da2b43682cfd9eb3b672cdd94b29652cd599b3165ecb595b2964ec9591b2163ec758db1962ec5589b1161ec3585b0960ec0d82b03602bfd7faff5fabed7caf75eabcd78aef5dabad74ae75c928571ae15beb756dad95aeb5569ad159eb3565a25592abcdeac758ab0d60abf57aaed5cab756aacd58aaf416ab5559a154eaa553aa5546a854fa9d536a654ba95526a452aa8f51aa2d44a874b2a1509a11506a053fa7d4f69e52da5d4ba9dd3aa734e29bd36a6b4d299d32a634c297d2da5d4b69652ba554a694527a4d49692523a0d48a90d20a3f47a8ed1ca3746a8cd15a2b4568bd18a2f4568b515a2b45
  | _ => 0
def rules11 (i : Nat) := packedAt rules11Bits (11*i) 11
def span11Bits : Nat → Nat
  | 0 => 0x8e34238c08e2c238a08e24238808e1c238608e14238408e0c238208e04238008dfc237e08df4237c08dec237a08de4237808ddc237608dd4237408dcc237208dc4237008dbc236e08db4236c08dac236a08da4236808d9c236608d94236408d8c236208d84236008d7c235e08d74235c08d6c235a08d64235808d5c235608d54235408d4c235208d44235008d3c234e08d34234c08d2c234a08d24234808d1c234608d14234408d0c234208d04234008cfc233e08cf4233c08cec233a08ce4233808cdc233608cd4233408ccc233208cc4233008cbc232e08cb4232c08cac232a08ca4232808c9c232608c94232408c8c232208c84232008c7c231e08c74231c08c6c231a08c64231808c5c231608c54231408c4c231208c44231008c3c230e08c34230c08c2c230a08c24230808c1c230608c14230408c0c230208c04230008bfc22fe08bf422fc08bec22fa08be422f808bdc22f608bd422f408bcc22f208bc422f008bbc22ee08bb422ec08bac22ea08ba422e808b9c22e608b9422e408b8e12e304b8a12e204b8612e104b8212e004b7e12df04b7a12de04b7612dd04b7212dc04b6e12db04b6a12da04b6612d904b6212d804b5e12d704b5a12d604b5612d504b5212d404b4e12d304b4a12d204b4612d104b4212d004b3e12cf04b3a12ce04b3612cd04b1eb2c22caf2b2b72cac6b2ac2ca9ca2a228a74a29828a4ca28ea4a289285a4a04927ca49e09273a49bc926aa49989261a49749258a49528250a09328248a09128240a08f28238a08d28230a08b28228a08928220a08728218a08528210a083472099c81872029c7fc71fb9c7e071f49c7c471ed9c7a871e71879061e11877861db1876061d51874861cf1873061c91871861c31870061bd946ec51b8946d851b3946c451ae946b051a99469c51a494688519f94674519a9466051959464c519094638518b946245186946105181945fc517c945e85177945d45172945c0516d945ac516894598516410588416010578415c10568415810558415410548415010538414c105284148105184144105084140104f8413c104e84138104d84134104c84130104b8412c104a841281049841241048841201047a311d0c46e311a0c46231170c45631140c44a31110c43e310e0c432310b0c42631080c41a31050c40e31020c40230ff0c3f630fc0c3ec20fa083e420f8083dc20f6083d420f4083cc20f2843c810f1843c410f1003aad0e434376d0d734344c0cb30314c0bf302e6b0b42c2bab0a92c290a09f28268a09528242908c2421e9083241fa907a241d88072201b8806a20198806220178805a9c15c70539c140704c9c12470461810c6040180f4603a180de5035140cc4031100bc402d100ac40291009e30260c09230230c088202184070b017a405070111803a500c1401e9003a00007
  | 1 => 0x25a08967e259e89676259c8966e259a8966625988965e25968965625948964e25928964625908963e258e89636258c8962e258a8962625888961e25868961625848960e2582896062580895fe257e895f6257c895ee257a895e62578895de2576895d62574895ce2572895c62570895be256e895b6256c895ae256a895a625688959e25668959625648958e25628958625608957e255e89576255c8956e255a8956625588955e25568955625548954e25528954625508953e254e89536254c8952e254a8952625488951e25468951625448950e2542895062540894fe253e894f6253c894ee253a894e62538894de2536894d62534894ce2532894c62530894be252e894b6252c894ae252a894a625288949e25268949625248948e25228948625208947e251e89476251c8946e251a8946625188945e25168945625148944e25128944625108943e250e89436250c8942e250a8942625088941e25068941625048940e2502894062500893fe24fe893f624fc893ee24fa893e624f8893de24f6893d624f4893ce24f2893c624f0893be24ee893b624ec893ae24ea893a624e88939e24e68939624e48939014e38538c14e28538814e18538414e08538014df8537c14de8537814dd8537414dc8537014db8536c14da8536814d98536414d88536014d78535c14d68535814d58535414d48535014d38534c14d28534814d18534414d08534014cf8533c14ce8533814cd8533414cc8533014cb8532c14ca8532814c98532414c88532014c78531c14c68531814c58531414c48531014c38530c14c28530814c18530414be952f054b9952de44b5912ce44b1912be44ad912ae44a99129e44a59128e44a19127e449d9126e44999125e44959124e44919123e448d9122e44899121e44859120e4481911fe447d911ee4479911de4475911ce4471911be446e0d1b2346b0d1a634680d19a34650d18e34620d182345f0d176345c0d16a34590d15e34560d15234530d14634500d13a344d0d12e344a0d12234470d11634440d10a34410d0fe343e0d0f2343b0d0e634380d0da34350d0ce34320d0c2342f0d0b6342c0d0aa34290d09e34260d09234230d08634200d07a341d0d06e341a0d06234170d05634140d04a34110d03e340e0d032340b0d02634080d01a34050d00e34020d00233ff0cff633fc0cfea33f90cfde33f60cfd233f30cfc633f00cfba33ed0cfae33ea0cfa233e70cf9633e40cf8a33e10cf7e33de0cf7233db0cf6633d80cf5a33d50cf4e33d20cf4233cf0cf3633cc0cf2a33c90cf1e33c60cf1233c30cf0633c00cefa33bd0ceee33ba0cee233b70ced633b40ceca33b10cebe33ae0ceb233ab0cea633a80ce9a33a50ce8e33a20ce82339f0ce76339c0ce6c239a08e64239808e5c239608e54239408e4c239208e44239008e3c238e0
  | 2 => 0x8dfc837f08dfbc37ed8dfb037ea8dfa437e78df9837e48df8c37e18df8037de8df7437db8df6837d88df5c37d58df5037d28df4437cf8df3837cc8df2c37c98df2037c68df1437c38df0837c08defc37bd8def037ba8dee437b78ded837b48decc37b18dec037ae8deb437ab8dea837a88de9c37a58de9037a28de84379f8de78379c8de6c37998de6037968de5437938de4837908de3c378d8de30378a8de2437878de1837848de0c37818de00377e8ddf4377b8dde837788dddc37758ddd037728ddc4376f8ddb8376c8ddac37698dda037668dd9437638dd8837608dd7c375d8dd70375a8dd6437578dd5837548dd4c37518dd40374e8dd34374b8dd2837488dd1c37458dd1037428dd04373f8dcf8373c8dcec37398dce037368dcd437338dcc837308dcbc372d8dcb0372a8dca437278dc9837248dc8c37218dc80371e8dc74371b8dc6837188dc5c37158dc5037128dc44370f8dc38370c8dc2c37098dc2037068dc1437038dc0837008dbfc36fd8dbf036fa8dbe436f78dbd836f48dbcc36f18dbc036ee8dbb436eb8dba836e88db9c36e58db9036e28db8436df8db7836dc8db6c36d98db6036d68db5436d38db4836d08db3c36cd8db3036ca8db2436c78db1836c48db0c36c18db0036be8daf436bb8dae836b88dadc36b58dad036b28dac436af8dab836ac8daac36a98daa036a68da9436a38da8836a08da7c369d8da70369a8da6436978da5836948da4c36918da40368e8da34368b8da2836888da1c36858da1036828da04367f8d9f8367c8d9ec36798d9e036768d9d436738d9c836708d9bc366d8d9b0366a8d9a436678d99836648d98c36618d980365e8d974365b8d96836588d95c36558d95036528d94626508993e264e89936264c8992e264a8992626488991e26468991626448990e2642899062640898fe263e898f6263c898ee263a898e62638898de2636898d62634898ce2632898c62630898be262e898b6262c898ae262a898a626288989e26268989626248988e26228988626208987e261e89876261c8986e261a8986626188985e26168985626148984e26128984626108983e260e89836260c8982e260a8982626088981e26068981626048980e2602898062600897fe25fe897f625fc897ee25fa897e625f8897de25f6897d625f4897ce25f2897c625f0897be25ee897b625ec897ae25ea897a625e88979e25e68979625e48978e25e28978625e08977e25de8977625dc8976e25da8976625d88975e25d68975625d48974e25d28974625d08973e25ce8973625cc8972e25ca8972625c88971e25c68971625c48970e25c28970625c0896fe25be896f625bc896ee25ba896e625b8896de25b6896d625b4896ce25b2896c625b0896be25ae896b625ac896ae25aa896a625a88969e25a68969625a48968e25a289686
  | 3 => 0x29822a5f8a9707a591a9586a531a9406a4d1a9286a471a9106a411a8f86a3b1a8e06a351a8c86a2f1a8b06a299689c5a24968885a1f968745a1a968605a159684c5a10968385a0b968245a06968105a01967fc59fc967e859f7967d459f2967c059ed967ac59e89679859e39678459de9677059d99675c59d49674859cf9673459ca9672059c59670c59c0966f859bb966e459b6966d059b1966bc59ac966a859a79669459a296680599d9666c599896658599396644598f12634498b12624498712614498312604497f125f4497b125e44977125d44973125c4496f125b4496b125a4496712594496312584495f12574495b12564495712554495312544494f12534494b12524494712514494312504493f124f4493b124e44937124d44933124c4492f124b4492b124a4492712494492312484491f12474491b12464491712454491312444490f12434490b1242449071241449031240448ff123f448fb123e448f7123d448f3123c448ef123b448eb123a448e71239448e31238448df1237448db1236448d71235448d31234448cf1233448cb1232448c71231448c31230448bf122f448bb122e448b7122d448b3122c448af122b448ab122a448a71229448a312284489f12274489b12264489712254489312244488f12234488b12224488712214488312204487f121f4487b121e44877121d44873121c4486f121b4486b121a4486712194486312184485f12174485b12164485712154485312144484f12134484b12124484712114484312104483f120f4483b120e44837120d44833120c4482f8e0b8382c8e0ac38298e0a038268e09438238e08838208e07c381d8e070381a8e06438178e05838148e04c38118e040380e8e034380b8e02838088e01c38058e01038028e00437ff8dff837fc8dfec37f98dfe037f68dfd437f3
  | _ => 0
def span11 (i : Nat) := packedAt span11Bits (18*i) 18
def pieces11Bits : Nat → Nat
  | 0 => 0xcac7007850087344988f20f02054549210990c4614f2a952a85397c9c542205008692e16cae8734970b457439a4b85a2c21cd25c2d9610ea61c0cc38612f91c8c45439808e4608a1cc05f231150e602f91c8a874519870372019d4a174609030a45199c801e0a058921b30884c6344f19042631a278c2631a278c4892898468623223534211a1911a21078d11a9a10a1800664d20c00623226d063431190468312188422746020c29b4d2180062078210c00310210c734d188288913800c4134910c1e1520054520f020910e730201c22a20181cb02009810ac703c01540a1472800a1c4688484794f8f49a64470180a9c1098d3c621098d3c6131a78c46107a5022564e9588a8830260ae8730270ae8703811282446884846204010422a4d9c484624d21800624c87074403e260840f07051240f4b8552a140710c1e562183cac153007408423007484044b04d2a5f0710c420f040102a954a204ac730780c08072b24c488703890e692201cc0e044583c08914823c84582b1d4e02a35a0d1c0508a34842144988088c02184ac8b43a282c400a00112041b1ad125f0a0cc3a040989c420435901108240a1900042b0110e8602158ac833809c02042b204e082021005c4007a1808572b1c08e61079000862108104885420100283412046080359589c542203886311f1fc184d1e1f8847b0f1f43a773b1d4921b26858844b3e078f41d3b9d8ea490d9342c42259ec3c7a0e9dcec752486c9a16211e49c68169508867188f8e21b211c83c2d0d11086311f080364d210889c55169508804188f8e24d139080855169508843188f8404d11108aa780d1dcec75249d02c4225938aa2d2a10c627302014e442340b43444338c47c71269084455168688843188f86a4d211c0aa2d2a110623e37934842a2a8b4d444188f89a4234938aa2d3511086311f108d24e2a8b4d444218c47c4d34938aa2d2a11086311f108dc04330e06e31368d8d86b3511086311f1348469271383c2d2a11086040d9349c6816950884d0219c865516868884326810304e10998ca6431988c21f3017c8c5e2e8108a4a048f076041a8ac7434048f05e041a8ec743402170b65a2c960ae56048f0762f0b87056042a8b4a844218c47c4d29850a451129409e091e0ec0835158d09c2d220f89a4213824783b178106a34048f05e04158e876091e0ec5e2b020d0084c2591494492411c8c45020fc5a44218f8844103014803f1f0f4123c1d8bc74041c8e06e36020105835158d06632188c01a2c020bc5c2816880162c020ac54291409c0826098841404048944624078180a2311084401f020780c1d0281004170e06c2c00030680a19010602e160003c2a14020180a120784c0806028480e05088400001030141e04028381a08010301607000281206028200407000180a04018080200
  | 1 => 0xc1d9f1507c0230cf8041e010aa4e0206008096a138e2723c010105402300b804021e0782d02318081d1630008140235808b5022d8082c021f408c8129255041540108204020cc088b020c80841121040867600bc082f6a10c40224a1384a274a10c107c041e0106e170a08009211c4842017355a0c6680cc1e4e1683c1e6e20134be0f2215084732003caacf500c4ba316395022312a318383155904a8bb559f0cc144e0c50e43169547c311a83c680f168109c04022f580040204c084d0231c4a046a2f4de2a3a81026043a84c08430206c9a0f020ac924b388889a4b69b441234348d09c1412851a434691c43034272844aa134b4580d0601389cbd12af4aab62a9f4be140790caaa10793528cf55a4d9c93120cc48c63ab344820668944a43289f946044d1f95acc28104462e4a218a2432899528271a811162e2b810a204110a82c046595d946710944c44912139927c208907a2e4b84c486f02220025745880b4012bb2040946408048c74a31928336293928bd5388948046208836042e30d5c146116d461b37108be47200cc100f60a909a69600609c0921af556bf1a940829225a68a2be3e1e0264910190fc3f308889c9f16a008864218c47c61211393e2d2a110c843188f8c44d0f1e83a773b1d5681b2685884180f2903aa33385880020006c9c1e1687488311f06c9a16212383c060e815381620008001b0c1a1481d5199c3616200003c7a0e9dcec750d9342c423e078f41d3b9d4364d0b108f81e3d074ee760d9342c4200a445e294121524041b1017a5516950867c268100068030740a670b1ad2240271501e4d5e0145e020fae53eb82a2ecc84355988301e339b42c6b488e080af16ac888132193408243d878fa1d3b9d82c420d8780c1d0285880020006c3c7a0e9dcec750b108367b0f1e83a773a858841b3d878f41d3b9d82c420d8780c1d02858d6912006c4006029ac247324890be553c068ee763a05884ba0d0142c1820008001a3b9d838b43a058848e340740a670885880551690c9a8e3187c00b94fae16e644e0f4c4a43386c346d3590000183686cd00533808d6185199c3c6d0d9ac00a2032600a1701000b0685b068ee67219d4e8683d0696a67219d4e81e0e8142c400100036683d0691c67219d1687c4c014661c2b908be4e340b4a8442c8f8844e2a8b43a442c8f89a4e2a8b4a844219b47c0635014ae1901001481a5199c3616202cc644d590ec082403014080915800064e2a11086110f8009c551695088311f08d1214289844862042242804308d0c4892889d1808311851a8b042184021311bc4eb10784c085a0d01538110b10034160c1ad2240581109aaf020915c3818ab466302aab0626e021053e80559908479469c4c842108d11a0f108210c00449444e730418810890208454623203c10831a1882a14021c
  | 2 => 0xf5ce6b3822124494917d349b4d124c43f4c19c92872b85cae1408901309544319961c2bb2cc4476597d96cb07b2c928b4915d24651a199163845b2d924002044805f24850c4403108596a1210cce062658cc846521a1d1604248201c084b8fc920f3003d92040b3c996404e17d5e5f0708492042017d10924411c9273313c41e5a3117c806264191349a64364cc032f97c064743100aee74dbc1343f4d145902010988ae477791cae5f2c204aebd3130084d053b1116254a1c8681f2b894fc7f24a91c4e264ba1c48c3ab157a472c97cb24162b148675111d57a7525b044a353ab944a301a38180c06e8902c9465a502c0f138114e72280602cdf459d82c3b770f1b6ed763acd4d758a70ce1e750ddd28a4622576870e0ada058628459c9e3ab1d5071333a04e910b87530574ba55928b65ac81cca738e00e0373131069d441cce0c831348681f2c98d02250b21990c02707068257294042d112b253421120f010e471810a877128f02831680942604120958e0471094f0041210408251209482041209582414a100102e6f21c1e4e212781e2d2121c5a5507a781e2d26a1c885407a1c1e4e26a1c9c4307a1c7a2e11094f804123509a4925b01904e4e300f24e021c030161a095bab91a094f2b9460ec885403aac46c164095c243460952e51108d01e20110d01e7f3f0d0fe0f3f0d0c057248d0400f110d0ce043818c1e2011094102011011b2d8678c47ed30a0942804128942804129f128a9540107838020f008c01d8109c3c020506204273000809271541e4e18b401e0427094f0045d951c0253c1541071390117adf0c090f278020944aa14a0957604541e0aa045d9118e31680118e57129f00825580118c316809528c8128cd2804600d06631680940849218c5a008100884a241399c4879043319a0417354b8d00a340aec707b319a401695480442a03c5cde2390084ab3c1541e6f150e00842558b408ab270100820122f462d012abc0808378a826041289426041284d28a827010620426b00082b268c5a0040a3484a7c24820e2220d890f2c0680d092692d309804e5f86036c8270104a0412095a434603749c256e0d04ab91a2e41e3460138682567891502d38aa05aad540b4402d2a821502d460b4aa0722150109e119f93c231133822704f08c5c0711134107f2102040421290528254a3304a784a05928c73a938fc75271c8ea4e4310d5a2512810e625020800807112a128201010c10a82709d342164268f8225c9fcf0911f9246a0f11165282045891249a64b2008201136d164e458fce08b309c138042485c7e490c03c4007111080e7e21020404d1110c0e253e09148940a094f02412890dcc52722c4a24151d49c7f3a938e275271ccea4e46010102004368803c212b4847f6cb607ecf0235c98c50213008cf309f0c23330af44a7
  | 3 => 0x7c73a30c48b333c934704408c08340bab50e8b5097d96211fa61268b438fcae1623958925644114be562481068572395848400b108bec964080428b3126992645eb9d18214599534c8142699064249c07e49381ac92242485924e74da48d616490fc68c92005c086743a2132cb0797c8057239f1961c6583c70040b0e0f8164a988925f44051246224a5c80042f98892655d85008cb6419196c842a2ce01c2103cbe871f91c7e492f8fc92871f924ca0465884be1432aec862109a54425f2488524494404c925131320f8c82b968806278168be5f3c990be142d03c224064268ccad32989989a64b6934c95689070e70b0e10e58078fcb00f4383cb0072c22cca3f0b0fc2c623221d9087649890e97310850e973221cf29b4d325346264100c457202081e734898880573125c26256010868c02a90984c0211e8ea4b2a9e0ea54461d4aa254a0696a750eb18ea685b1d43c7d3a954f0c5629341e555b314aa7d62b141e4e69b044ac112b24ea553f34c4a242a094485412a51a6254a248dc75219d5226e3aa48b6940b25196910a245160448a2d16a764b7030df2db7d161864b9d905072b35522569be9167651859928b53b959050023104a2507a18eae56f9d436f940b9d9266518ec3a9e60851503c2a0f1805f771f04a383e094e0df0a0957e092a810701512894f6083db048e402f900305f6db6c927812b498e55129e1be876015016550a155ac556328cea541296590403810190df2096492493c9c092dd0219892750d8cc4a410410580416f9242c1612924661b3a85892252c0e09279641c04a5f1295c4a471290cf240338952a9e6808dd8c93c3ac80400bb05cad160a1c22190b1982c17330e02c9c0b21d82692b968ae9e3232428660da78421b0b0442c380c1994867383e11af820284385f470cd0e3f3111d38553c1516a33670c482ce2195556ab313dd9c660893862ab5e9947e281f91c3847088e11c6616b38e0610e0c4869c3817d0e871fb14be4743a1c7ac51e95c68340c19110161a0d0ce641a0844421440fc68472015008801201118470210122042589426255da5d7a5b6801048315e95c925463b497a253f9e8ea7f12b017ad360901804023bd84aa43a90d9c871f0c49ac07a961184d18924b4253a0104a256eb04ea1462095c4083a350924060b149a1c38b6c4a183c86092400db4c4ae112b007685673d156d4088448e9e308e19cab1188556ab6418956284f0853c2855844c46555b384623559d49249128944875079cca0731a24892c06fb0980ec113244a2539b009a632ba5c4a673ab3552654d2694ae865144c2214d2c87070441ac924024a4446623e0d02ef333295961c65a70ae5a3818868e61a0d0089824958b456121002c041a2253428288a134624d268c46673998686228994a28b11b284c234583d28e707a
  | 4 => 0x394a8c754324f84e5422cea0f48b9522d23a92da47533b9cd225539c042ff12a69c07551b9dc0750b39cfc667d09584a4739899aa902160ca9a313205070249885065249c042474d320be62249c0ca4938184ca64381248e3f38124503f38124ca3f381250e64249c0c83f1a32442400b15c50400b15cf8cb64b20c40f4a21850493818892230b248503f1a32480163115c7e163115d425f6598924884aa5d12144a988286b491252e4002189249531124be880a124ca0465b210a040b1c0be62219c0500465b2042474a9252e4002084266b491241e88411010a7348988b44048988fea173b215a9a0b3214a9a0b320ce66288a050653f06c060708160de1364168caef4a1855a653115c80923115ca2254a0d1287c128d18035210d04a224d0d1a4c02a9092e25691404a354d0d1488c3abe54854669d548143ab74a8cd709d4be1462935a82564b88ea545eb84ea4b4939cb8c2541e4b4d2541e550bf3cb7550dd2c1c0264348a2d2e1472be5a06953b25c28b54895a6fa4589546dc701d584757c86d902528394ea1b7cb7c44b902094c49c0a17c50652fb09503c2a0504a1b539e8ea1b0a3009a1412b7d80557a938aa310a83c9c250404d74553a955e42512b88caa02a8f8be14629d4a8bd698104a750c138bedb24889b6491089436553c300b8540215428a82a9f5803b7e9d470ad1215466a820300925567a44647024900e049040104a7d2aa2ccc49381e466dd0d9d5be252b81c4a952488d56d2188447c665205cb88760a1d82572f970ae472d95d92044a3410ec92aac1565559aac42b5558a19eab2f91c808e3110422615e9558cc52aa807c211f91d38620a070c4bd2f8a07e47328fd0e641f95176442ab199c553eb38a8ac55955fcab3231d565463b38aa145585156be14151562855af8cab555b389c557bb389cab3210d562127154383e188707c871f83c803f3119028111090422f733338ccce268e0624e109e156623eaadeece213f50e3e438f9f2f71fb158afc1e9907e345f85868660b0d0503f1a290504051994804052984801630b4c0824603217a5502094a8b23a9558e752aabceaa42a1d548310229008916a1019247702a0aacf62950ba3e3310d9c3822338ccc23aa90267551b80eac833b492ac068050eadd0c138ea310a348f825248c5383e3a86c9adb129d046755f31d505869300762d5422c5a7549089d83c69bb068693c2a1aecf54309803b1d911808816aa1247d3a8616a7533ad8ea3c16b0046ce38340cad432bd1562855b204a50728952850600d49a54569d44a8128324ce251286c485463894f8251a058ee753e1d522251a940262512381804d601509aa23eaa04a732804cea91271d522041292c30133a8104a243384cea25622304a624d32134c964a6990e145aa5c2a945b0948e74a3ed347f4d32042
  | 5 => 0xe04a381e190e25664b2d90911c385a0872c058d2d0401950ec92f8e0ca6443901fa143310d9c4d5f11d56bf3139da6e1020952824391d84a1b5f1252e5112989ba3412b112e94728912e5112885d83412b241050728904a5064a51ca2410a8d902564a68ac625eb2596c82011d0e622b858fec21294036c82fbe88ee0541e8cc756f9c0aa781292c92080e2fd16ce320fcaa9e6497070e143b40b8d04386d9266141910e402f8a0ca404397c8087311848e652021cc2473299080873315028ce2697c806443984804732a1cc240239950e623315086ce73b4ca80412890b814542f916e5041f04ad13c1704a35122ec88a80b22d28fb812a44acd34ac16e25523ddc0752c1fd84b712b2030545db80ea553f1d5f2162e30950586409442ec4d0d04a583129ce0e145aa44a5870084eaa3738e1c0750b39cfc69333e84aad1295d34c8329010e570b15910074aa5cd6071b325244010858c4572021cc4570b11d249531124b44048a48c4d15c895ba3468895d8501a28c30dc3aa45a65412a5192545db80eac92aa85c275739d4f6d16a324ea7a69b5192753b25da8c93ab50e8e5649c408df48a2cb669762a0f27202094a01b611d5481b7ca41162564a9cb8c9458954e754806df2df4b84cd2dc12b404a5864a9dd8c26037cbefa2030182ee2a9d4805f69b51caa112b4d92e550895a255810948ee054125cac9638958e5445858cc756e9c0cc1673a2c2c773abe44a954b9e4f05548b14aab648b159c0821a20fa5545b38cc1c45b399c0827221a2d360b2470e16821c7e8d4f3247f014f324ccd343b4070e143b41a0b143b253c3f323953c3f10b95a08043b25a0a243b24aacf16b14aaa0168fa00542e8f8ca641f988aac64ab14aaa01f32d2a550e0f88e87108fdee5463338aaa116b38cc310a13576547eaadee310e0f8806443988ca553c2adee38223393eb655b20c41455be57cf755989ce47628fd8af91f988aa041289146133aa44804770b50bed254124a8bb22315a60412890b60454220b8c24aaa12add2596180c804134f82525924801b4bb50f6255f124aea15437ca8254a0edaecf5432580dd0b0ec88a80b22d48f7701d5a0286a03da0d43103ca2251a8d0f8251a891d825111404a9728395d8c02a13434b53ab25a25412890aa254a324ce553c1d428750db749c7548984b4d25432150bf6f95c4ac928
  | _ => 0
def pieces11 (i : Nat) := packedAt pieces11Bits (9*i) 9
def atom11 (i : Nat) := (0x834c54001120e100a1811b4010318e4002292881004e0a52784408c43306903118e2ec682640ee244321742ac1c4090120f050832038061048b9155140950a48210041041a820148081183c80e8104390805603e0150409c40041102a0b0180e83903010f01e00c0202c04c5106e0854581f0401540c83bc0540e80d02a0f62416480902a340b00c317a09c682d29b81c9128f108d32020050230160424d820088c481e41160cc6a05b040d50808b0941242598f02e0540682f606c0082812602c118130606c0700d50807c10188587622a2541c8b909600c0984c20618c3b8370023807280502a128828650f4442604de07c0702606e0e00c0338a60ae1d8438f702e11c300100801c19382304008a8e80d03a1ec7d81b0961b02e0808411428048d080fc0068fd0c0f423980068533810081a0050c1833c232364781b90d2241248305d21c29830027e081d4110ae13f45852d1ba27418510ade03c0831221c1488f08 >>> (11*i)) &&& 0x7ff
def disp10Bits : Nat → Nat
  | 0 => 0x40053297b98000000cba94980027cc004865004c00000200b8005d1a011ada3e3401abf00590000000001000494800562c03d0058008000000433c058eba000480400106c002aed0000002002800625001a6110000008000717b93e1f800200f0008070002005313800c000a15810400120a004802000002100100b4002f776de800c02a003000003c002022615800000310900c80000000000060088000000000000400b125797d130022000013801c00a0aea308000003375006811c00200000ab81ac6800c00f000800000000000040000000022f829ce00100343b80360050203f2c00200f0024d84001242008d93005a0066f4801c000000000000001803700000040000080000010014c5e005456000802001000000000000000064002000008b4cc012bc200046b00020005f9ae8400e0000293780000007006000578201200000000000006ad002ac7e0090000002a100226ef8004004003761371000000100000000313b000600097900100184846a032b7000001649a000000001df12001a338050000010008000003a002619007c00a00570bc7fa712f7d00000140200066b34efc172d83027800000002500080297d20080030004004f2c0000048012006000000623ef3f00050a00040030088029a0afa19b880080570b8003003dc4001e002aef5efc000000001c00000692580040000000000005b020150028024002000009800c0200000068066be20000000092280000003459c01600000050b802200001845d000000600000280e000b00000000340008b0d44000114c9b4001a1e2ed2000000400000000b0018008006000000407a0050098001f440010010000000c46005d3418a0022001800c01200000d0000000027001801000f42a0008034006038002803000200401580022ff433001bb940070b18ad805000a00b00000240040000005398000000a6c000c002000008d578002032000000003a01070b000005402101280000020005ea000000600074880100000020010008000de300100862a0e6900c00040000020070005caa00000b80000020070058009e18000000003402001200000040840000020010028000066003000e0000050049c5600000400080040006a5800000c00500001ac0000008a54d7000000070380240280000000000000013000472403000300000068260040000000010003000443c00200b0004f5c004002000800000105e00f800000c0087172eae1c6006011592000a0029d600240040340000052688001023505a48200400e80e40000050008001ca600000000080000000008008076000ae83ea00000000000088000e5b78500000051dc99e00000070618a7cc1e0f003d6ce0054008000001b9de83c00000043fdac6d2100b800001000c00041a4000f290010004012000009804c004005
  | 1 => 0x10008001ca8005005c8e400e008004b2280580000000004010bfb9ad801000a0000008004000013000000000eb4a0020086ada0030050005b1e0000068062394000844578c018deb00000000000160008015ad000000b533002a000000001800c01801780862b20120004a4410e007005811400a00b003000400000000280759aa000000000400000084a0001f68000011d7f000e00400045b4000002002aeaa176001000000000000d0003310009637007001402c05b01acec4012000000003000000500000100020087a480780040080004d5c0040087998005e8200000d8000001093006800171800a00000040000000070001b86078661000c00600901280f800200d957c3dc0014090004ec800d4e200101dc0080000000024000f300000000000df0002000001e001005000001c01f004c5f40000147bc4924004ebb00244540340170000000004000004592c0000028aa800403c00087dafe801b0c884c53ae660000a53419c00200000000040d4003006003400000b7da8001aa20010010002ade005a620024021367000c51000122700100c40014dd0053b8a3cc005004af36296018002caa803129a0018000032008001b795c5a000005b6b00015e700d491803600899d0000006000002000003e01a004cdb000c00000200cc000f03001004c000000a1080266e4fd1003800800201c0003cf23460006fe801c00000e00800028f600603a000000915c699005802801200332f60cc0030030038000000000000c02c00400500a000000300e8014026e218cb80100000020004384000005001009c0015fd000000002602600080440000020000038000f2e7a2d81400400700048d40000007d980080000090072fc40020008af003402e00b0028004000dbc007000c00a05f02881000220000000001b8a0020003ab4012d02005ae5c0015e10000000004bc600051500080040010010006025000801800000f02858f9f5b56600000b800000075900a8034c1688a000283ee4600080065c0e4c7148012ba60040000020000001000000000e001000002c0020045a700000080010020015894f4e6e680040000009ad4d740320218133ad000f1c6012800007a00a08951640000010043600002006001001a9a2001a57520800e0018af801000201f00200880100009cb53a0010ced7c9801c00800100b000000712100080000000110003329c720000043814000000000ae8a17c00200053b4002e1b002458802c00086a000000000100300080440007050038004000000800000c000a182fc8002003684000400000261b41faadc00000630c641600b5dd0001c02003009bcd4000007a8780023d801f0040000000f96000800c0000000000004000000000007a291157023010000801301b0004004008903800400400687a800000cb57000000
  | 2 => 0x2202000000004c0030dd0008001e6400000b807c0000000264e18002005791000001e0000004cec0020057d20008000004b1e8014004000003c71400cf36002000e2c8004a4f003dd4600000d800576600a00081622140000088004000000004d3a4002016000d60c01e037000b5f8002cc000e3a60006c395d2801000000000032e002600300037e001c000000367a3c200700080180db579000002c0040010000000020010002001000200377b80e8000b85000af140000005e70001b8400000100022e2000009448286c009003800aa0c0000038001748094002001c00200600080129e0000000001800a0038598000006003002800c00400076d80169ee001005004294e00f7968204027147000000236a00
  | _ => 0
def disp10 (i : Nat) := packedAt disp10Bits (13*i) 13
def link10Bits : Nat → Nat
  | 0 => 0x840092a25a14fee81b9300c899e22eb87861e61328b07347a23d0afe9c28c2617fb6101e68522a7e13362121c9673686d2080066e29b1bfc0890a808b61cd821c8378ce0ba8e6cda8f01f903481978cd4d9f34fce128ce22668bc8315b91401eb132e83883eab70b54d0a1058dd790c81e0057863b023c47f044653b08a29ec897a4c114364bf08d4dbe03eaf363b845e105700920448e7189880dc875016f30ac115106667b8502a01064e16b0b9ae4b148e32f928e31538a8169848815885e06770c1c1d837625528ce054e09fc238377a12a167004882ea23c88b0ae8a64cd669416004048a41c32c82cb805012a93d41103c2a0e7b35af03837e1f18c2422b8a6a9518b78ea08692cba987601683a41d208c0161853410304f61318c961c507925098c1ed8a8c8c94c87c426b2b16910a64414bb096d1c3cc4b05387027e850416305da54400fcd430548b04888a97d23e60f69b482a0a7ce1849306a581a1a2ed29242a718a8a8212d45e3a5c4514a91000db180266250453905a40e78b209c48544ef1aa9e2bc0b6a6b3b3c86ac897e2aa06284d5a74c6350b8671a2b3022706b6235a7d6a2e8462d16229484d10544eb9c2e2d102fa21f08e8da199ea26a08a22fc0c74824ab5cf22b2ae48b0582cad8c5a50c0af6648011081a2cf043109f6a76090a1420baa09b8abcb17aca21191c9097f9a0ec47864200681c014082ae13b87c0541ab6c53a34768b5abb42310724578067a2488aaa1c8961215d9aec64d89786ff12ac24894f233504e61740b5812914b2321852466933124cd04ae25d197c34282baec4260c3138bd422e02b41648aca2e13932f2507e288a9a3a02e85b8125068cd32109030c830a1b0999cb121bd208a0b8808c87f20911694457394e1a309aa2ba86d48f58b6413134cc2d3849862ba70001612b2542b88e0f100481218478e2931fe94c359c21e81e413ba46417705440f93bbe08485641e70360d13293ea0f81acaa611aa05f05cc28438fc1c3a726514849c2052ab0af9031210f1c0a5861a6619207a2a29058ee2828a01cd03de10bac0819284d2534002629c85c40a98a96a070b38b1d90bc909a42c20f011810cbaa42e380785d0a298620a69808636461fd98800a6bcd6cfb803e15b1918001200c2ee9610555b4e01f32c04b20207c11730d41860af6a5b38cac5305840fb1bc63318aae2a5266a201b0302a7081820280d24878016ed30018ca6368821494724c2b0c60bc21641afb8c4d7998b20989be011408680c406c40f894526bc8b3c6d70cf2236315e6be81ba56f08969b182148c3a7f01e98bc0eff22902fb074a0ff21ce90a00ec0a421ce61b952c0df118a21b03bce5bb40a4e38526b20a68007baca688ab0d80338b4064a17bcb2f16ae46a2cbe1412a2665008168ec00e064b98926a689f40ae2
  | 1 => 0x320ef3fab6a34114dc05095601738a341262a40258960ab0e08dc05b049810803e006706d2a66028c1d9942069b000a3179a5e1273bda6e3b686e2e92e0e5e01529280bb469990029040476d939c006d4867c2d28a62182928292d362a7010bfa02e064eb00890672fa0aa1060b3a5622a5228a98b46d4b778a9186f406884da6e815789680518c200822006955ee7c0a00a571b94a2085cad4ab1fa4c9044272b935c17391762fb824e2298904541bbf612d9a9421d17e440b0c640af2132153a0e0a8e07a445b803c11ba0728a71a142b786666a18c0eabd1c562b00a20229a2861b7005e16bbc0e6b41cf4314066c7211a1268409b828206d0176146668096920ad99fa489a9e617db5e4aa621dc233010e11c2d14a1a80e61809d0e1ce8848112b4da11d2c28ec817b4017b2c08518a92a3faad015b98021719952329b3d001886fc6b399f24d926c455b06281c8041670e9938f0d88fe29e362e5d6204c2202040337906a1d6859a04e88c6ec7879e9db030814b226625509d407dba3471292560aca0be050009c2cd29cc1cc078ca4812dea700c24cb5b33a98c9ca8829067ed33157a31702bc1ca8b766f4097a10e01fe2e1b6b2154acdcc6f232c0219b5285639b626d0a908820824743169cb11a9c824eb12e8fe951ef3b89a071ea6a0a4f0cb625081d21bd89de6e589961fe84aa0e221042dc0a3e9a78440a119cc026503aeecd016ee68055cc1ea9861e4183833c098428eab3c20986fe04807b80db8c6a4d28a36298093aad220ca1fd2c1ea7818eac088b400002c4215e0aa22c88a74904822a2a920e801b8432b238a54108891c47c177c1028c6e1b5b5be30186bc2ff396211e0a9661f869c150b8f80a0959c494006425db468a43bc20a2789740a7a590e5c817e173116a845042a25b057615488aa66e8ab422724925e2280eac80a8ae64a6841bc8c184e2383a23d310620808ee014b68219d8672213095a1d80456e9291ae0fc88502e700081b68664197063845e961e5bb865207e0678ce2994a25208d600915a2599125e73701a0198049a1b818d025182ca021b45ca368632071aa048bd862c5688ac4893962618f0aec243050e188089286d044a259025a09c2c4424b852a4d12310804a5dc71b05f811784421ae192a5e785ea20c076617a04489820660ecfa6220b193782dba6a2f46025e24001b62e087dc324b5b87021446a7e019e62cad14d4bab941ed85ca16e843c96c8668452288c15f85a82292ca42f4332e04f811c0b2376425198ce2b58a585e2878203020cc16602be171303a59ab8e48bbaa02139b60e4912b7af3482e4d0494fae40862c30f997051c05b66eb29b217e83b0936181430f0c341889568ede846e18c163e01583cc31b1332d6412b2196158030c01ec30b01b062285262d18c9a2c1052ce888c06
  | 2 => 0x21e4a5184e8285e22a87a02da2b601bd2bd0724042e227999e22190920fa07e008e3908a3d848c6443bf26e5a258324838c2b094d4072043425f24de27a09c22e7815a2bd02e8916002a2c7b53010d8c6ca7588e219005960f684a6472a4404b11c0aa44874e33a05fcb230156049216c6ca090ac618c6832a1546f1bb73e2260c02710039a72191e233982dc1d6914e319a328483a01ee198b5a8b687508b53c3c6caa2f25598c4c9a18af0956014a130160e11c131a9df82c0558b7fc4f613661b2032a232270229a152416619a218c00125be9ca826306fe587189417f05d41230616253029246fb744205832825bab18155801c6741498f1481b223cb0f01df28ea01127781418a441a0b324952aa2ae8c9234081877644023c25dd07f4574376a621b7703383b225d91ab6a1b375c445a0f8a9c110eaf59cac1ca96be041a76a34792801663c722682b74c4c312e300095a44984441c70810049013cd4022ec2b3054e3222c525f49046240b1de626207edb60a9011d1790a1908b42df800eb4483ca001091632e959cef686a40e52ac432007409f6244e14f0910735831418996f85e72c782b80cd29da0732631811257d06245649518164b738af5b67e06e042666b06ae9e4b10c11fac64a1e93909ca27281fa07041d18a6cc11b3024b18aee1ce91080a68b2a71a186c621268ac7a988825019082b2a90c683a7261bb1594676809a10e8c7609f043eac5849668cb658198946024c2660546a39c2d430fe2bf846c0e5a22e0fd0ae40bfacec266159413ab2baa0723f49f50154035831c5c880d02cc85f642c09322b60370e1e009c81d009e259b27890da358e39b328e078912df9b38a2221be200999644ac0ba42148634ab08baa4f004c2996356ccbb8ad86f102765c59aa6063acba92905122ee820218d8862326012c1c68b923278ae26b9989cdceb67a43d8cd2e34a5c212e16a24608bac14ca6f25158b524f38a5e7478b548b4a444f2e09680b8b566d532d10ea12c6233783b8c8f8280d9e049c9e8278c14d303091987561c6069628c051ada69c7e637815c11129125baa3ba08eba24241b876a631a8817915b019196d645e8a7c9508a9210f83ea1c9b8323060b0e40e0d208a438d0cf4156a222934868a281041980e00c787be692873829894c81748bb8925a514c1706f09170b5e0cfbc220da911619221ea22f8656306b04a260146684e084e2d628b2f1809165cc1d16b3d9a1801739fc8be04606e0182aa1111e48de8a1c95c845070d997e66402be9cc8b2a258b85c2c400106f3855c30320a833a8aca41505509341ad2a8301302a7971cc6f05ae09eb21631608cec668b16dc32ce4207a46a2e735e22af856ade215681b5030c9fd0a6e1a805c809c87606b487060ec9c3a1f20b3a203834e52fa8bc2c59c281e50cc42bf
  | 3 => 0xe94e20d6810c605989a14336742438414a36b2f29cba93413284680d807cc0b08a282ab93d20d88348a2409ae72e215a5b08ba0ced03682e7a0062e98c9cc080cbc348031ea4f11be1db82640aa03264918d161d0039a20684fa2c22960c66044c02382686d0839206b081228521a62b207c20ea90a60b62c8a49f82042f5328819426c02c00ca2e469af2805053614890ea0a3a5ee1b7a35e2301bc4704a614076a0023210a004760b1c12ea95e17783fa2d581c423085aa68325b600730940dd365a5709b1218a3d08d078156caa82d209b2cb009095540c6801e33f997005e08e40243c22db98084ac5031c32da95e45609ca1fb06661e483302ff8cf0930063468f17f6120061c0aa2c2013b3708118211a2e31b8a3292b9a266b874188b2821ab0830912130099509264e6000edb69ab82360c6291d991e6c198c2e2894226ccac820cf3a1e2242d001cd81e00cc9108a8891da326199692c01e8625808c1ff82c4c3e93b4645b03ad47806c1cd1a8c1092b980ae1c009d08b06ebe97fc08d18ae6df07f2928834609a8cc88e031c0de928e807401cc26712005d73936c6e87ee246170c23fbb72dfa8b721f981d40d603640983aba32f288621505188148a2e16a881aab522a2d749560d1f261e0880b6c071125c5a401f4e03012aec0352a87087d206d18e633d855020b145a1a6a0ae2d98a7646c2c38d3e340005c8a160778324c1380c25e5974c0bb983414687e22be08ca1f607d0cee26e82c31b620f2031633b944ed45079802ca8ac1a4354c2fe09ec113925c0548aac284a06a6be112ca018320036870a85199fe60712d2ce20c0c3243b30db382c02ef0ba65b90b7419404c64b60446f042206a491bca2b195902971c1e73da4bc2478512c28862e06cb846078a2ccaf787242822a32079b2c2a9380dc336b71e19a0a5c1bd104cf03315034190121a7a58c59c96f2d3e0c8c54f8b2620816ea594956e25733c66fea110265332610f035ecb106844829ab00ea81ccde5219631110888bc8b500642204840861a2aa9b1ea8113be120801695c986ec2808a665984320d48c16c95068a07989fc689818419b03500052b3edae88002ad2c326393a1083f11188e718b666487fe6a585de62bb03680d04289fda26215f06001aa85baec1103215203ac1ef0410a9ea010d3d0342ac93c880d32028d51273c1ee2ada0df98402012a2c6bfb0441b5175c2930a5830e1c7cc5c0cba03b85c625a866205d0b781c1a6cc1e5bb60a9097c0337b7be25408fccd0391adc936ae32517ac0ffb28c8d00b08162b574232116820a2ba80dd91660ce201c168131cc208ba2210891a12401284e8a38609087a8147249441d906010bb818e248b9030285d648984a62800520d65295ad3f82d425109faa4e01621dd85dee4188006f58160acea7b0281a7a
  | 4 => 0xadaa3733e42dc27ae32804541ac02ec4bd0d0e4dbb28a2abb386ca10680ccf24a808888582269a8a989086a8541234cc309fe19298e02231234997aa3e026a510d428caa23337bea8b087849cbc1e1248034c3903b8658006c510093c820a63a1f6887ea67ac805201990ad3b120a90818826089ce130b34cd678aee9741a0625c90f410333c4f45136ae9d05e60f702eaca6051c2cd9472a26336c27e2cfc218075e16a14ea269b496c38805c50f90fea25285a2fa82a4c6e36bcd25261a93715e266a92522eb3a565a5239e6cd8d1cc5a982e08c0d026ed83a6acb20162828ac292eb046487096ac108cce1a5b00e19b9abc1070374209248419301941d886048cc2be8148041429496d6022b6ca00008dca053ace31c252e4262b6e102076ae9419b023c34c48648384083027499d939eab7209088aa85625700288f718d2049a22855c19bc04fa3aea9ca65a16d03f6d3ca55af1c96c6446a71610e2c1a2e1a2a0ece045e8e73044cd8b9c414c224a3130b7ed0ab4ac4ac26e20b9a5f228f03f817b0bea482b42c8f6049ee2d85f008f24ea8b9124c2f98ccc12fbab61f786b4b3404f02f709560c81ba88ce9c6629c00b62d635e40510ac61851b42dc40bc233f88b855dbaa884d87daddb918c305049e0dd8840d45b7aa196b05e440a9a26a805d62f309580c6b0225fe07581dc84622e0093e1703b6814e82702c6850eca993f0150029edee80f2508aa5a19eb296e6381d60f5b9a631d10bc237b43a50639e404285da21c3cfa16999be2ba1b2c0d5078e02d09d20e98896c8fb2401359cb41d4a53e9f58bf42f712d0af604904279a546c2823c0d696f01979ba6d3d2528f1c0c60528365ce6284fc13c26164c600685959914e02023a2bebbd4669183a48d8cf820d898010385964eb8ad42bf9978b04033218182265ba8964c868b386920cb21eba50022aa4042f1302e0db93b818ea5f46c081a41cb81f2e4d94d20850c8a30581481159cca9a383a823e8638037855a1aa0bb69da11e82ee0836dc52334d0aa45ec842b3044a972c247058e0ce020a3468ac86f4a5820a81226d2321fa33089a41008888b4184062e3399e55035c0109060461b82ce1d5198e46db39601f245e5de95161721878da3b41a03e00746f005d2da98b8603da5ac9c4b670ede939c9620b0e24b0654ebf049e8ff83b61f285b2727b4e81760c3e13387385931bb241c1b8401608440d30bb00ce126e48b3a640c107b09129b9ca8b326c3441a406e923fce9fa07a51
  | _ => 0
def link10 (i : Nat) := packedAt link10Bits (14*i) 14
def programRaw10Bits : Nat → Nat
  | 0 => 0x11baa99856d3baa9954ed0baa99856c5baa9985ed4baa9985ad4baa99846d4baa99216d4baa9985d94baa9985c94baa9985894baa9985c54baa9985854baa99852d0baa99552d1baa99552c2baa9984ac2baa9985b02baa9985702baa99852d1baa99852c1baa99846c1baa99852d0baa9982b2bb609916f2aa45598532aa45598532aa055986f2aa05598532aa5d598532aa59598aa96b09598aec4a6a195532aa28592532aa5e198532aa4a1986b2bb624916b2bb5e4916b2bb564916b2bb64891aec4962891aec495e898aec4962892126bb62895532bb625126b2bb6251272c49a6521124aba65213294ba652152caba6521532995a921aec49669855329966921532bb66921532bb66985472bb66985b318b2691232d69aa98532d91aa9851259baa985532bb64912b31895e812b31895a821b31495e812126995e812472995e885472995a858b3189628125329956821272bb62812b31b962812b318956821b31496281212699628126f29962812472994a858aec4966885532bb66885472bb668855329968021b318968c12b318968021b314968c121269968c124b29968c584729968c582d0ba5e688470ba5a622470ba5e6883297b566882d0ba56688470ba566883297b526883295b52688329791268832959126883254b14a883299b14a88124ba64a883297b64a883295b64a883294b64a8812cba64a88470ba66222470ba64a883299b14688124ba646883297b646883295b646883294b6468812cba64688470ba65622470ba64a553299b486883254b086883299b086885b05226a884f05226a887005226a8872c8126a554f05126a8872c5126a886302126a885f02126a885b02126a885702126a884f02126a887002126a8872c2126a885711b26a884b11b26a885e94ba6560a20b950540a20b95154032542a21435329956913532995a9135b0aba2120432bb62913432bb5e913572bb46953432bb56913aecb9629202f2885292072c19aa9136850baa9536955baa913572bb4a553572bb5a553572bb5e553432bb56513572bb465532b28812520572bb66153532bb64913aecba6615332d79a21532f2884955327288495535f2bb4955353299495532b2885492053299615532f28848513532994815354a8854d202b28854d202b28850d20a214250d202b28844d205329948113a211244d20532995a923532995a91053299569102f288669102f28866923472bb66923532bb66983472bb66950472bb669832f28866950532994a91012552481531f15248153700a24955370c5a5618012585601533254b0a9535f08a615532ad52481534b09554d205492b281535615b28d805709854d8068d4b2815168d8b281156d55244d202e9856015332982495536b2bb5e449532995e8816f2aa12598532995e81253299628125329968c12
  | 1 => 0xbaa9986a18baa9926a18baa99152d3baa9955305baa9985302baa9985301baa998b31ab055985f2bb549912b2bb605926f2aa49598532aa49598532aa061956f2aa06195aa94b09598b31ab09598632bb69598532aa685925b2bb60591532aa46198632aa60591632aa609924f0aba65125f2bb4a958672bb4a9582f2995692153299569212d2bb66985632bb669586b09baa9216309baa958532995e158632bb65585532bb624126b2bb6241272849a642172c49a64216329962812b3189528125329966821b318b668122d2bb66885532bb66821470ba5a655470ba62655670ba54a88670ba5c688670ba546884f0ba54688670ba486885712b26a884f2bb5e9605c54ba6570532995d5705f2bb49543432bb54543632bb4a580632bb5e580632bb465804f2bb5e980532995a9205329946180632bb6558053299615805329958d135f0ab955135b2bb62913632bb5a9535694ba65135a54ba65136b2bb609135f2bb5491353299649135b2bb60513432aa495534b2aa49553432bb54513632aa61553b311860113a655248153aed1860113aa94850d80a2141501135528850153b318560153aa95854d80a658560153632bb46583632bb5e583632bb4a583632bb655835f2bb569234f2bb62910532994a9504f2bb5e910b318b66923b319b62950532994a183532995cd235329944d2342d3baa979b317b5a4495b2bb5e449472bb5a449472bb5e4495d9ba126995f16952a99470b852a995b0b252a99470b552a99470b252a995291b22a995296b0aa995291b16a995291b0aa992989baa9813256baa9815ac9baa981532bb6a581aec6a6a581b31b82a5525f2aa525255f2aa12525672aa12581124aba65251e9aba65252ad4ba65251e94ba65252b14ba6525532995a825b31495e881126995e881472995a852aec4966825532bb66825472bb6682553299468525329968081b318b2a571672aa1257872c49a6562124aba65622ad4ba65622b14ba6562532bb5e56172c49a65614a94ba65755e94ba656126d3baa9822713baa9823013baa9824ec0baa9822f2aa5a528532bb6a582b31b82a515672aa1258272c49a6551124aba6551430aba6582470aba65822ad4ba65515a94ba65512b14ba655172c49a6451aec4966882532bb66882472bb668825329942882126994e851532994a8515329968051b318b2a541b318b2a542b31b82a5455f2bb4a995b318a12591b317a12598b316a12598b318a125925b2aa125955b2aa12598472aa12592472aa12595472aa125985694ba65915b2bb62991532bb62991472bb56992432bb62991632bb5a995532bb62992432bb56991472bb62992b318a12991b317a12998b316a12998b318a12992315a7aa9981297baa9911296baa9911291baa9920694baa9980694baa99562d3baa9982911baa99529
  | 2 => 0x1535d55250d202851850d8050525501535694150113455455015359545501535d945501535c9455015358945501535c5455015358545501532854550153485455015356952501135f08150d206b08150d20515785015351568501535495150d205702850153684a150d20630a150d205f0a150d205b0a150d20570a150d20515585015361d58501530692150d2050558501535f085281135b08528113728852811372485281137088528113704852811372c21281534ad1a2815356952281133198128113619812811356981281136098128113729512811358921281136152b281534555b28d204955b28d205615b28d205692b281135711b28d204a18b281534618b281534615b28d803298b481133296b48113440ab601532e918601532e925601536c925601535e585601532e95344d205495344d20561206015356160601532ad60481135f085481136b085481136301254d80530854811367085481136441960153630196015306d1b54d802e95b44d206295b44d203295b44d206301b54d803297b44d203298b44d206c41b601535f08b44d206b05b481136302b54d805305b481135694b481135f0ab44d205acab48113570ab4811356d5244d203191854d802ad1854d806d11854d801251854d806891854d805491854d802851854d805d55244d206c51854d80729514811354951481135494854d8054891481134709854d805958560153691856015354585601535d9856015332985601535e985601537118560153591856015332585601532a5856015330585601535895854d805858560153685856015328585601535058560153485856015308585601532f1314a9502f1135a9506c41b669836c41b669506c4b1669232f113601106155360110305a944d235495348110670aba6525532bb5e4814f2bb5e9824f2aa6a582aa94b28d82532994e8514694baa998632aa461954f2bb609924f2bb4a958b312b669584f0ba5c6884f2bb629204f2bb62923b318b6691052d3baa9796309baa9186b2bb5a525532bb5e5812f2aa5e5815f2aa5a5255f2aa6a52572c49a65254f0aba65526b2bb5e48172849a648172c49a6481b317952881532996688112ebb66825532bb668815329968c185f2bb69562672bb685784f0aba65624f0aba656532da5a656259d4ba65716954ba65625c54ba65785f2bb4a975532995c5725329946168672bb5e9826309baa9284f2aa12582670aba65514f0aba65514f0aba6582432aa68d515329946128532995e128aa95b28d28532996685112ebb66882532bb668514a94ba65955a94ba65925a94ba65914f2bb62991632bb469982dabb629914f2bb46998aecb462991632bb5e9984f2bb5e9984f2bb5e991632bb5a998632bb4a9984f2bb62992aecb4629925e94baa9985a94baa9984a94baa99852d3
  | 3 => 0x535e55b061531255b061533059b14913691b006153125b0061537088a289136154a2a153569522891370d5b285202e84964913124b1649136c82b661536c41b6615352cba6491312cba6491356cb16491312cb1649134b0b56615356992249133299224913305922491370d5b2452032982605133258b4955370c5b461803256b495531edb449553325b44955332d894955361189495536248949553708894955332d794955332d69495531ecb9495531ec49495535e449495532e4494955361d824955322d82495531ed8249553125824955370d155492063172495531257249553630a24955360981495535f081495536b081495536f08149553530814955367081495534b0814955370081495535c971495531eda149553125a149553609a1495535c9a149553605a149553301a149553325b1495532f191495536449149553325ba54513301ba54513708b9545136ad25455536e8b054513630b0455535f08a515535b08a515537088a515537142a505132316a5155367082515535b0a2515535f08151553670815155363021515535f021515535b021515536b0215155367021515534b085245135b085245135f085245136b0852451367085245136f0212555370085245135f08a245133097a245134ad192555362d1925553670822451372c282555370082245135b05224513670522451372c18255537005224513630a2245135f0a2245135b0a224513570a224513700a22451357192245132b12b255536252b255536092b255533298b255537098b255536098b25553325156155361d76615537008a615532297a61553325b4615532f1896155361189615532f179615532f1696155361c496155322849615532e449615535e4496155361db261553325b261553700b26155332982615536258261553228a2615535b0a261553700a2615532f1926155364892615536309261553325b16155361d7161553229a1615532f19161553125916155364491615536f0216155363021615535f021615535b021615536b021615535302161553670216155370021615532e918601133296b54d203056b481535b0ab481535acab4815358952481535d95248153591524815332552481536309554d2054881481535f08148153530814815367081481536f01854d205701854d205497148153549614815332da148153549a148153548a148153570a854d205495148153549414815364491481535709854d206c4b148153630b1481535f0b1481535b0b1481536b0b148153570b148153530b148153549214815361d5854d2006d2148153515214815324585601134855854d203298b5c1132e97a5c1132b12058153549205815363012501535f08550d205b08550d206b012501536708550d200691a501533056a50d206841a50d805b05a50d201f1255
  | 4 => 0x2e8b45a5251e8b46a5251e9ab5252572c7a1252532969125251e9a9125251e8a9125251e8b9685255713b28525728b9548816e4b95a825124b95a8256e4495e881530b15a85232d79528812e418528255b052528815ac49668255ec4b6688112db2668816c4b1668527001868c521ecb96956232979125623254b20572325a468d512a44968d516f0a9545822e5a3689516953b295282c4b7495152c5b9495152b1695e128495a9281154f0a22815168d252811568d2b2815169d5b28d286995b28d286815b28d28728b96085112db2668516c4b166882329871259132965125911f12a125956841a125983056a125924b17a125956841a12595125ab145922e849589912e849549911256b14991125ab14991125a1285926e849545911edb44a9955ecb44a9951ecb44a9956c4b14a995311a106998311a1069953056a52992329871299132965129913198a129916841a129983056a129926316a129916841a129954b0ba455982e84a60991129ab20991131ab145923298b5c9912e84a589913296b549912e84a5499132928461955296b149911296b149913294b14991129ab14991131ab149915ec4a689915ac4a68991129a128592131a12859232982605916e84a54591684a1509924f0815159570c5252198125ba14492125ba204923097b6449170c51648925b052644914f05264491728186549570c81648926c8495a8956cd25568911256b46892728b9595212d0ba5652170d5b06585329691252132959125212f1194a95832d69569211ecb9569215ac49669216c41b669855ac4b669217091b269856e849645216e84b64521728b96142112dba46485565ba16421271125e885131195e885644195e885131195a858644195a858471495e885471495a858464495e885464495a8583255862812325b562812530b562812311b9568216e4b9568213115962812644194a8586f1496281257149628126e44962812564496281262db3568216d1b3568212e5b356821301b3568215f0855282163012528582f11952885484b952885084b9528856c4196688556c49668213115b668216c41b6688556c4b668212712168c586482968c586441968c58618b9509433254220543509b02054332542595433254258543325844854370d5b049402c0b85a95332d8a6452048d9a2891332d8544d53329875cd137158b085537018b08553301ab085533059b21513329875e91322cb05a953068b946953068b0469534b0b0569135692b169132b1920a553071982251370d1b1652017191065530691a125534b0891251370429125533055912513530ba609135f0ba60913470ba4a15370cba545202e98a609132e9b54a1533059b20913125b50a153685b50a153569b0209133298b5c9133298b589132e96a589133298b549132e95a5491332928461
  | 5 => 0x9b3545206e1b3455801259b209131319b209135699b209133299b20913529b020913125b02091372c49149135296b149131256b14913125ab149135a54b149131259b149131319b1491370cba5052072c49289133298b289135a98b289135698b289135298b289135a58b289131258b289132a58b289135498b289137152b2a1530a96b2a1535a97b289135697b289135297b289135a57b289131257b289132a57b289134697b2a1535296b289131256b289132a56b289132295b289135a95b289135295b289135a55b289131255b289132a55b289135a94b289135694b289135a54b28913569b028913529b0289135a5b028913125b028913461b02a15357029661535ac496491356c49649136f0856491363021661535b085649135f085649136b085649135702166153530856491370021661535702b661535ac4b6491356c4b649136302a661535f08a649137002a6615332d5a6491362cba649135ecba6491332982649132e94866153508b1649135695b249135e5b526153685b52615370c5a549205f08a495537108a495537088a4955370c5a461807248b4955362c7b4955332989495531ed894955331189495536f08949553624494955362582495536257249553228a2495535a8a249553690a249553624a2495532a4a249553124a249553289a14955332da149553325a149553309a1495531edb1495531259149553570b360920530b36092070c5a5218032d89515537008251553700a251553700815155370021515537008a245132892b255532298b255535f0a861553700a861553329876155361d7a6155361d8961553329896155331189615532297961553624496155331db261553329b261553125b2615536f18261553530a261553325426155312492615536f092615535f0ab6011362552481532e9a554d2071152481535e5524815352552481535ad5248153305524815354942481535649144d8054981481535489148153549b1481531255854d207095854d203097a5c113549205c15357012501536c9255015349545501535e945501532854850d806854550153085455015351518501535141850153570185015351528501535201550d80515a85015370958501536c9585015363121281135f0ab481135b0ab4811369552481136dd85601536e585601535616354d802ac4944d201255b44d2056cab481136c54854d8062c9148113551856015354985601537058560153719856015372585601535a585601536c95854d802c58560153645856015324585601531edb94a95063021669505b085669105f085669106f021669503056b669236f051669235b052669106f052669104f08166923630256698370c186695032d8244d835e1825cd2332da944d2332d2854d836a52554d836092554d836c4b15e4491e8b95a925
  | 6 => 0x3289512d9b9461284f0a55498260515549822f1625e1285d5525e1285f0a828115670a2281516994b28d826a54b28d826814b28d824955b28d2861d5b28d286a55b28d285895b28d287095b28d286855b28d286055b28d286f05166882700824e851630a960941720a94a14572ca91454272ca9205425f16a125915b15a125912e849609911253b1459272c49205921253b205921258b09598125b3061956e849495951edb14a9952d1b14a9952d0b15a9923056a5e9925acb4569912d1b2569916c4b1629925f16a129915f15a129915b15a12991571ab209911293b145921edba5499172c4a149915e94b205921293b205922915b061956858b09598291b306195689b30619562c4a6899156c4a68991631a1285926e84a605916e8b054591570b34a198305a6509925b052521984f05152198125b31449272c49148911256b148915e0495e891125725e8915ac49468956cd92468957255b468921255b46892670ba61521670ba59521720b94915812dba465856b0591252163029125581edb9569216e4b0569217299b1692156c49669211f15b669213115b6692156c4b669215d9655e158728b4464857285912421565ba12421065ba124856f0125e8855b0125e885521895e812705295e885521895a821064495e885064495a8585b058628125f058628123115956821631496281262449628120644946885630b14a8585b0b5628125f0b562812570b14a858670b5628126d1b9628126f1596281261189568212e44956821064494a858725b062812625b356821125b35682170919528855f085668216f02166885630126685853085668214b11b668856118b668125308568c127258b68c127255b68c123118968c126118968c123115968c125515968c126314968c125714968c126244968c120a44968c585644968c120644968c586d1b35454032524605435097b205433254254543325421454332584085435218b085437118b085434916b215435097b215437295b085436115b08543611b0085435f0ba44d80668b15a9206697b229136a4a14618032935549205f0ba409136695b289136696b289136697b289136698b289135f0a8561534f0a56158032d2544d533296258d1361d855cd537258b085533119b2151370cba551207158b0a9535302a5a95361cb25e9130a8b85a9533097a5a9135f08a569135302a469537002a469530b17a569130b17b469535acb9569132e5b2569135f0b846953530b256913700b2569135f08a529137002a529533097a5291363021529535b085529135f085529135702152953670215295370021529533097a5a51363021125535b085125135f085125136b02112553570211255367085125136f0851251370021125535f08a125133097a125135f08a2a5133097a2a5132f15a609132f14a609132e
  | 7 => 0x5454b28d820b17a6011354c7a461522b1b35458268d82281515711b28d824555b28d287055b28d285f1805cd134816058d535ed7a601135a96b481535acab54d205a920581535c449a6578581705cd6361553601505ac7a6a525724ab54971724ba5c5622854b28d8232d824e8512a53b145426f0a9549417156a125921ed6b4a9955acb44a9956317a129916315b66921728b9550217002168c583252468c585c9255cd5372d524815352d524815326d5248153508a150d205495368d205492054d231e99b285251e93b285254f0b15a85270cb25e88170cba5597170cab5497170cba58971724ba589515d9625e1285e14b28d286854b28d826054b28d822851b28d822855b28d28670824e851630b24e8515f0b24e8515f0b84e815530b24e851700b24e8516f0a954542630a9605422a56b149413056b4a995568b15a9920716a629920716b4a9986293b145924a97b061954a94b061954b1ab06195125286289112518628927255b4a8911255b4a8911252862895728b955121325145e885325145a858325545682171589628124f0b56281270cb856821325b45682132554628126302168c585b08568c125f08568c126f02168c585702168c586708568c123251468c586315968c12325b4609436119b08543570a3549204f0a5549204b0b9611133292b225136f08a125137002a125535b1591251370c5a2a520714ba4a1532e849609135308a289134616b2a1530a94b2a1532a5b3285205308a6491356cba649133298b249135b08a495537142a605132316a49553625b2615535e449481535f152481535b152481535d152481535a552481535ed52481536ad524815332d5248153705524815332d514815312591481535499148153548b1481536c9255c1535a9455015368945501533295150d2032d51481137295854d805a985601536a58560153525856015363012669834f0216695070c12669834f051669235719b4a910630b244d231e8b9691253297912525724ba605256f0a9495816e47a68125728b45e4815e5ba124815e4495e881630b15a8525f0b15a852670b15a8522f1525e8815f0185a8252e552528815b0526688153052668816f018668255b05268c185305268c186f01868c526705268c18724ba61d62708ba5a5513296912551724ba6095170cba54582720a94a11570cba589516a57b2a1156a54b285823254b285825eda32a11552da3289516c1a
  | _ => 0
def programRaw10 (i : Nat) := packedAt programRaw10Bits (40*i) 40
def program10 (i : Nat) := (programRaw10 i <<< 10) ||| 304
def getProgram10Bits : Nat → Nat
  | 0 => 0xbb574ae55c2b756cad55a2b2566ac958ab055eab956aac556aa954aa854ea9952aa4546a8950aa053ea794ea9c536a694ca9852ea594aa94526a480780e522a4147a8e51aa3145a8a512a2143a8650aa1141a82502a013fa7e4fa9f13da7a4f29e13ba764ea9d139a724e29c137a6e4da9b135a6a4d29a133a664ca99131a624c29812fa5e4ba9712da5a4b29612ba564aa95129a524a294127a4e49a93125a4a49292123a4648a91121a424829011fa3e47a8f11da3a4728e11b80d46c8d51a2334648c51822f41c8b916a2c4568a914a2844e89912a2444688910a2043e8790ea1a43886d0d21943085d0b21542884d0921142083d0720d41882d05a0a41282103a0640a02102203404805001ff0167f8fe8123e27f0fd9fa3f27e0fb9f63ea7d0f99f23e27c0f79ee3da7b0f59ea3d27a0f39e63ca790f19e23c2780ef9de3ba770ed9da3b2000ec1d73ac754ea00500a74ce91d13a073ce71cd39872ce51c9008720e39c638a710e19c2382700df9be37a6f0dd9ba3726e0db9b636a6d0d99b23626c0d79ae35a6b0cc99600600cd59aa3526a0d39a534c3ac6f9a534868cd11a1340678cf8db33c674ce19b334664cc19732c654ca193324644c818f31c634c618b314624c418730c614c2183304604c017f2fc5f44c17c2f65e8bc9782ee5d8ba8022e8004b99722e25c0b796e2da5b0b596a2d25a0b39662ca590b19622b0584b015f2ac578ae95c2b6568ac9582ae558aa9542a6548a895029e538a694c296528a494828e518a2944286508a094027e4f89e93c2764e89c93826e4d89a934266014991312604bc9712d2584ac9512925049c9312524848c9112124047c8f11d23846c8d11923045c8b0040084548a1132244448810f21c4348610b2144248410720c41482103204404800ff1fc3f47e0fb1f43e47c0f71ec3d47a0f31e43c4780ef1dc3b4760eb1b8328750e91d039c730e51c800c718e21c2380700df1bc3746e0db1b43646c0d71ac3546a0d31a4344680cf19c334660cb194324640c718c314620c3184304600bf17c2f45e0bb1742e45c0b716c2d45a0b31642c4580af15c2b4560ab1542a4540a714c294520a31442845009f13c2744e09b1342644c09712c2544a0931242444808f11c2344608b0040084508911021c4308510820c410010022044007f0fc1f43e07b0f41e43c0000001dc3b0750e81cc390710e01bc3706d0d81ac350690d019c330650c818c310610c017c2f05d0b816c2d0590b015c2b0550a814c290510a013c2704d09812c2504909011c2304508810c210400821001f83e07a0f01d83a0720e01b83606a0d01a0330640c41802f05c0b41602b0540a41402704c094120230440841001f03c0740e01b0340640c01702c0540a0130240440800f01e0380680c0160280480800e0180280400600800800
  | 1 => 0x7d8eb1b632c5d8ab13622c3d86b0b612c1d82b03602bfd7eafb5f2bdd7aaf35e2bbd76aeb5d2b9d72ae35c2b7d6eadb5b2b5d6aad35a2b3d66acb592b1d62ac3582afd5eabb572add5aab3562abd56aab552a9d52aa3542a7d4ea9b532a5d4aa93522a3d46a8b512a1d42a835029fd3ea7b4f29dd3aa734e29bd36a6b4d299d32a634c297d2ea5b4b295d2aa534a293d26a4b49291d22a434828fd1ea3b4728dd1aa334628bd16a2b45289d12a2344287d0ea1b43285d0aa1342283d06a0b41281d02a02d06804ff9fd3f67e4fb9f53e67c4f79ed3d67a4f39e53c6784ef9dd3b6764eb9d53a6744e79cd396724e39c5386704df9bd3766e4db9b53666c4d79ad3566a4d39a5346684cf682cfda14ce99b33265cca99332263cc698b31261cc29833025fcbe97b2f259cbb9752e65c4b796d2d65a4b39652c6584af95d2b6564ab9552a6544a794d296524a39452865049f93d2764e49b9352224cc9892f25a4ac9492724a48c9091f23a46c8c91722a44c8890f21a42c8490720a40c808ff1fa3ec7c8f71ea3cc788ef1da3ac7400d1ce394718e11be3746d8d805235c6a8d31a233c668cb19231c628c31822fc5e8bb1722dc5a8b3160084578ad1562a4538a51462844f89d1362644b8951262444702c03e2344588910e214418810fe1f43d8790ee1d4398710de1b4358690ce194318610be1742d8590ae1542985109e1342500f09211c228430820fc1e83b0720dc1a00e7f60cc1882f05a0ac1482704a08c1081f03a06c0c81702a04c0880f01a02c0480700a00c007feff9febfc7f6fe9fcbf87eefd9fabf47e6fc9f8bf07defb9f6bec7d6fa9f4be87cef99f2be47c6f89f0be07bef79eebdc014f6ded3d9012f61ebbd67aaf51e9bd27a2f41e83cf79cf35e63cb794f25e43c778cf15e23c3784f05e03bf77cef5de3bb776ee9dcbb876eed9dabb4766ec9d8bb075eeb9d6bac756ea9d4ba874ee99d2ba4746e89d0ba073ee79ceb9c736e69ccb9872ee59cab94726e49c8b9071ee39c6b8c716e29c4b8870ee19c2b84706e09c0b806fedf9beb7c6f6de9bcb786eedd9bab746e6dc9b8b706dedb9b6b6c6d6da9b4b686ced99b2b646c6d89b0b606bed79aeb5c6b6d69acb586aed59aab546a6d49a8b5069ed39a6b4c696d29a4b4868ed19a2b44686d09a0b4067ecf99eb3c676ce99cb3866ecd99ab34666cc998b3065ecb996b2c656ca994b2864ec9992b24646c8990b2063ec798eb1c636c698cb1862ec598b315628c4d89311620c3d8730d00cc300330b614c258430760cc1582303604c05802ff5fcbf57e2fb5f4be57c2f75ecbd57a2f35e4bc5782ef5dcbb5762eb5d4ba5742e75ccb95722e35c4b85702df5bcb756e2db5b4b656c2d75acb556a2d35a4b45682cf59cb35662cb594b25642c758cb15622c3584b05602bf57caf55e2
  | 2 => 0x649c9191f23645c8990f21641c818ff1f63dc798ecde63ac738e31be36c6b8d319e32c638c317e2ec5b8b315e2ac538a313e26c4b89311e22c438830fe1ec3b8730de1ac338630be16c2b85309e12c2384307e0ec1b83305e0ac1382303e06c0b81301e02c03802ffdfebfb7f2fddfabf37e2fbdf6beb7d2f9df2be37c2f7deebdb7b2f5deabd37a2f3de6bcb792f1de2bc32eef05dfbbd776ee5dbbb5766ec5d702a03eeb5d5ba974ee95d1ba173ee75cdb9972ee55c9b9171ee35c5b8970ee15c1837702dfdbeb7b6f2dddbab736e2dbdb6b6b6d2d9db2b636c2d7daeb5b6b2d5daab536a2d3da6b4b692d1da2b43682cfd9eb3b672cdd9ab33662cbd96b2b652c9d92b23642c
  | _ => 0
def getProgram10 (i : Nat) := packedAt getProgram10Bits (11*i) 11
def live10Bits : Nat → Nat
  | 0 => 0x7af6fdcdebdbf6b7ed6fdadfb5bf6b7ed6fdadfb5bf6b7ed6fdadfb5bf6b7ed6fdadfb5b1fbe3f7e3fbc7f78fee7f6fdade7d7fe961ff4bde8fdd4fbb3e757cec7bd47fa5f747ee87fd5f3a3f747ee8fdd0ffb3e747dea7bd27fa1ff4bde87fd4bfa97f4bde8fdd0ffa9ef4bdeadbd4f7a9ef63dea7bd5f3a37f43fe8fdd1fba1ff6adec7bdab7a37f5adeb3bd0ffa4ff57ce87fd1fba3f757ecb3bd677b3d753dec7bd4f7b3e767ce8fbd2f7b1ef63dec7bd2fba4ff4beec6fd4bfa9ef53eec7bd27fa5f74bee93fd2fba4ff53dea7dd8f7b1ef63dec7bdaf3b0ff61fed79d4f7a9ef53de87fd2bfa1ff43fea7bd4f7a1ff63de87fd27fa9ef4b7ea7bd47fa8ff47ee8dfd0ffa1ff53dec7bd47fa9ef43fe93fd677a4ff4bde87fd4f7a5ef56dea3fd577a9ef53de87fd8f7a9ef43fe87fd0ffa1ff43fe8fdd0ffa1ff47eed5bd6b7a7774fec8dfd27fa4ff49fe8bfd1fba9ef59de93fd677ade74eee9edd37bb3e76bce8fdd3bbade74f6ebf597e9a7f65daefbd1fe93ef47dccff91fe33ed67dacfb5927fa4ff49fe93fd1bfa3f753de8fdd0ffa1ff59deb79d6f3b3f64bde97bd8f7a5ef4bdec7bd4f7a9ef53dea7bd4f7b1ef63dec7bd8f7b1bf637ec6fd2f7b1bf43fea5fd5b7a9ef63dec5fd8f7b56f63dea7bd4bfb96f52fee5bd4dfb1ef63de87fd4f7a9ef43fea7bd2f7b1ef63dec7bd2f7a5ef63dec7bd8fbb1f767eccfd90ffa5ef43fea7bd2f7b1ef43fe87fd8f7b1ef63de97bd8f7b1ef43fea7bdcf3a9ef53de87fd0ffa1ff46fe8bfd9fb29ef53dea7bd4f7a9ef53dea7bd8f7a9ef53dec7bd2dfb1bf63de87fd0ffa4ff63de87fd0ffa9ef53dea7bd4f7a9df63dec7bd8f7b1ef63ded3dd8f7b1ef6baed7d98efb1ef63dec7bd8f7b1ef63dec7bd8f7b1ef63dec7bd8f7b1fb537ea77d8f7b1ef63fac7bd0ffa1ff53dea7bd0ffa9ef53dec6fd8f7a9ef53dea7bd0ffa1ff43fe87fd8f7b1ef63dec7bd2f7a1ff4bdec7bd8f7b1ef53dec7bd4f7a5ef63de87fd0ffa1ff43fec7bd2f7a97f537ea5fdcb7a97f537ea5fdcb7a8ff53dea3fd47fa9df51fee3bd47fa9fb51fee3bd8f7b1ef43fea7bd4fba9fe53eee79d4fba9f753eee79d8f7a1ff43fe87fd8f7a1ff43fe87fd4f7a9ef4bde87fd8f7a1ff43fe87fd8f7a1ff43fe87fd8f7a1ff43fe87fd8f7a1ff43fe87fd2f7a1ff537ea7dd4ff21ff53ee87fd47fa97f537ea77d4fba9fe43fe87fd0ffb1ef6bdcd7b96f3a9ef53decef93fb27f64fec9f5d5fb31fe47fc9fd59fb33d74fae9f5d3eba7f64faeafb93ebadd75bcec7dd2fba7d75baebd5d7e3abfa5f8e9fd57f33fd257ecafd9ff12bf65fccffc14f7a9ef53de87fd0ffa1ff63de87fd0ffa1ff53deff0bfa96fd2ddadfb1b2f3ee57e7a7ef4b7e977d2edadbb5b9f372f6efa5db5b5e9e1ef52de87bd4b7a8ef53ce
  | 1 => 0xf87ff4fee1ffd37f87ff4fbe8ffd3ef9bdff39f1f7cdefe75ff69f5ede2ffc7bfcb7f17fcedfa7bfcb7f96fe2ff9f5f0fff1bff35fe5bf5d7f1efe3dfaebf8f7f1efe3dfc7f75fb717fd3df97bf4fbf9e7c3ffc7df9ebf75debbba3ffcef6bf6f7addf9b9fb73d7e7afdbdb9ebe1ffe3dfc7f74f7e9eff2dfe7b76f6f9edd3dfe7b78f7f1efe3dfd6bf8f7f9ede3dfc5ff8f7f96fe3fbe7b7cf6e9fdd3dfa7bfcd7f9eddbdbe7b74f7f9edc3ffc7bf8f7f1efc3ffc7bf0fff1efd1ffc6ffad7e5efe3dfc7bf8f7f1eff3dbe7b747ff1eff3f3b75f67bf1efe3dfb7e76f9edbddbeba77f6f9f1efe7afc7bf0fff1efcfafa7bf4f7e1ffc3ffc5ff8f7f1fde3df87ff8f7f1efc3ffc7bf8efe97ff2dfe5f7cd7f9bdd2ffa6ffcb7f9afd1ffa3ff577f9cfe3bfe3bfcfce8ffd1ffe3bfc77f3d7e7afcf5fdeb6b6fd5dfc7bf8f7f1efe3fbc7bf8f7f1fde3dfa7dfcf9f9f5ebcfb79fbf36de7dbcfb79fbeb72fec3ffe7cf3ebeb77edafdbdb9fb75f5d6efdbdbcfafbf4d7edcf5fcf9fcf5cfedf757df2ede7dbcff7975f3f377c7efcfdb97bf3d7ebebdf1f9ebf3f6c7ef8fdf9dbe3f7e7afabdfaebf7c7ebebcfdbbf36bf3f5afef4fbeb79e7fbcbd7cfafaf1f7f3cfd7d7ef2edd7f3e7e7cfef8e7f6d5efb75f77b6dd7eeafb75f3ebf5d7f9aff35f7e9e7d7cfafdd5ffa3fdc7fb8faf5ff69fbd3fda7fd4ffe1ffd2dfa7ff0f7e9fed3deafaf5f3ebefc7dbafbf4f7eb7f53f6afef1fde9fbd3f7abef5b6ebe7d7fbabc7df9fb65f7e7afcfdb77b6f57df2fbf4f7eaeed7dbafbe5f7abedd7ddafbd5f7cbebd7dbafbfc77daef75d7ebb7d73ebeff4deebbfc7aebf5d7dbeb9f5f7fa6fb5dbeb9f5f7fa6ef5deebbed77eaeff4dbeb9f5faebf7d3cfaf9f5fb6bedd7fcafbb5fd6bedd7ebaff35f3ebe7d7fd8ffb1fee3fdc7dbafdb5faebefd6d7aff35fd6bef97dfad9f5fee9eed7dbaff95fd6be7d7fb8ff7573ebeed7deafbe5f5ebefc7dbafbf5b97bebf6dfe9bedb9fb7fd2ffa5ff4bfe97fd2dfadbf5bfe96f76dfcdb7db3fb6fd6ffa5ff4b3fb7fd2ffa5bf5bfe97fd2fbe9bf5bbfa6ef6deedbedb5fb6fd6dfcdff4bf6b7ff0ffa5fbd3fe963f7e6efafdbfe96ef6deedbedb5fb6df6f7e9bfd3dfa6fb6feadff4bf7a7fc6f7cdff1bfe37fc6ff8dff1bfe37fc6ff8dff1bdeb6f76d7edff1bfe37fd2dfadefd377b6f76df6dbf5bfe37ed6ffe1ff1b7bb6fb6d7edb7db7f96ff4cfedcfdbdeb7fb4fde9efd3f7a6bf6ffe1df5bbeb77d6efaddf5b9fb67f6ededdbdbb7b63f7c7ef8fdf9fb72f7e7afdf4fe6bf3f6ffa5fb5bf6b73f6deedafdb77b6fe6dbedf7d377b77f4d7edcfdb9fb73f6ddedafdb5fb77f4deedafdb77b6fe6e7edbddb9fb6bf6efadfadbb7b7af6ededfb9bd7b7ed6fde9ff4bfe976f6d7edff4bf6b7ff0ddedbbdbf6b
  | 2 => 0xbeb77c7ef8fdf1fbe1fffc77db9f9f3f6e7e7ebcf5f4fbeaf7d6efaddf5f3ebf6c3ffa3ff8dfe9fde3fba7f74fef1f7e2ffc7bf0fff8eff1df87ff8f7f8efc3ffa5ff4dfe9dfd1ffabdf5ebe9dfd1ffabdf5dbeb77c7efaf5f4fbe9f7d3efb79faf3efd3dfa797df1fbe7e7dfcdb79f5fb73d7e7cfaf9f1fbf6b7e7cfcfdb6f3f1f7c7efbe5f7eaeed7ebaffd4fbe9fde6ffa5ff4bfe97fd2ffa5ff4bfe97fd2cfedf79bfe97fd2efa7ff1bfe36bf6cfedfb5bf6b7ed6fdadfb5b47fe9f7d3efa7df0ffeef3e2ffa7bf0ffe1ffe2ffa7bf8f7f96fd57facff4dfe37fd67fc7bf4dfe9efc3ffaedf5f3e3f7d3ef87ff0ffe9efc3ff8fdf47fe3f7e2ffc7bf2f7f377e7cfcfdba5fefd3fdb39beff2deb7ed3fdcf9f9f3f3e7efa7db5f9ebf7d3efa7cf5fb6be1ffd7eda3ff47fe1ffc3ffa7bf4f7f1efebcf97bfaf3f4efebcfc7bf8bff1efebdba7f78f7f1efe3fba7bf4f7e9efc3ffd79f8bfe5efe3dfd79fae7f0ffebcfc7df8f7f1efd3fbc7bf8ff6dd7dbf3b2ff67bf5e7cbdfd6bfcb7f96fe3dfc7df0fff1efc3ff87ff27ff1efd3dfb3bf8bff1fec3ffc7bf8bff1efe3dff87f4f7e9efe3dfc7bf1bfeb3ff0ffa5ffc5ff96ff35faaff53ff9cfd1ffe3bfcf6eafbd57fa9ff5ede8ffe1ffa3ffc6ff9cff3d7a3ffcebfbc7d3dfa5ff0ffe8ffd3df87ff87febe7d3efa7dfcf3f8f7f3cfe75f4fbe9f7f3cfe79fcf3f9e7efcdb79fbb3ede7dbcfb79fb73f6e7ef4fdd9f9ebf7c7efcd8dff8fef17ff1fbaf6f1bfe37fe3bfc6ff8bff0ffdcbfbb5f3ebebb7fcafd3dfaf3e7f6cfafaf9fbb9f2f7d7e7addf5f3ebf6d7e7afcf8fbf1f7d6efaf9f5fb6b77d7edafcf57bebb7d6efaf5f4fbebf6dbe7bb9f7d3ef67d7cfbf1f6f3e7e7dfcdbd9f7f1eb77d7e79ddf3fb73e7c7ef8fdf9fb76f6ebcfd79f8fbf1f7e7eddf9b3f3f3b7ef4fcf9faf3f5e7ebcf9fdb3f3e7d7e5efcbdf97bf2f7e9efdb9f97bf6f3efa7cedf9bbf377e6efd5dfbb3f377e6efcedfbd3f3b7e7afcf5f9ebf5d7ef8fcf5f9f3f3e7ebcfcfdb9fb75f6efcddbdb1fbedd7ebcfd79f2fbecf7db6fb5df4fbedd7dbcfb7db6ebf5e7ebcfb3df6bbedf6cbefc7df8fbe9f7f1eff7c79ebf5d7e7afbf5b7abefc7dfa7bbdb6ebf757f3aff55fee3e7d7fb8fbf4fee9fdd3f7a7ef4fde9fdd3f7a7ff0f7e9fbd3e7afe75fde9f757fb8fbf5b7f36ef6ebafbf5b7eb6fd6dfadbfd3be9f6d7dcefbbdb76beed7fcaff35fcebfdc7f9aff71fbabf3d7ef8f9f5f7e3edd7fb8f9f5f3bbfdd3e7edff1bbeb7fd2ffa5ff4bfe97fd2ffa5f7d3fe97fd2ffa5ff1b7eb6f73ffa5bf5bbeb7fc6ff8dfb9bfe37fc6ff8dff1b7eb7fc6fdcdff1b7eb77d6dfe99ddf3dbfbd3edafdb5fe6bfed6efcddf9b9fb76f6efe9fb5bf6b6ef6fdadfb5bf6b7ed6fdadfb5bf6b7ed6fdadc5ff47fe9bfd2f
  | 3 => 0x6fcfbfcffabebf7f7ed9fdfbebf7d7deeffedbbbbffb6efedfedbeb7b76f7e6dfb5b8bfe1ffc3ffcf9f1fbf1f7c3ffa7bf8bff1efd3df87ff0ffebf6d3effd4ffe97fd2ffa5ff8bfe97fd2e2ffcddf5d
  | _ => 0
def live10 (i : Nat) := packedAt live10Bits (15*i) 15
def rules10Bits : Nat → Nat
  | 0 => 0x98452112c94492411c8c4222910844321104803f1f8542a3e170f47a3c0a8502e17150505214138ec2c270a854283a1a8e42c111209c2a38138542a17088486e290a09c60301b0d86a211a0542a15170544e150a0542a150a8542a270a8506632188c02a15180bc5e2f0a0985c151685028140a0545226160542a150b09c28120a0544e270a8482a140a05c2e2a158a828290a0504e281409c4e271009c2a15110944c260b0542a150b0543c1e0a894481f0f88c44211007c3c1d0e0702e1c0d85c30180d06832180b8542a150a8582a120a85028130904400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000803c1c0d0602c14090401c0c050200c0602008000000000000000
  | 1 => 0x530f80000000000000000000000000000001188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fae170b85f8fb7d3e5f0f77bbd9e8f47a3d5e8e823bcde4c278bc1deee76931d8eb263a9d2e86fb7dc8e773395c8e471b89c4e170379bede6eb71b6da6cb35b0d76b355a8d369335a2d067b3984cd65b3196ca64b218ec66331588c36130580b85faf97abc5dae972b85bad96ab459ac962b1581315eae1b09c2aad1caa138160b0a82c1618144de273c9e44050139f47027100ac40911505cea75412b156160b0582c2a29aa8a6392b154ce3933aa44e16158ac4e274b2a0b4a74e2994ea64c194602c4ea54606752a94e6275228d442950a849aa128279409f4f248769d28944d48643271368c4d09cb8271393532383d94d22274c0cc66560b0e52e961b8582c2a150a86e370b058222b498dc2c160b058542a150a86e37151f8ea952889ca2951389cf42a150445411150ac56934a24c6e22162491e884424924924908924920b24522910b0582c9148a4522160b0582c1648210e4694787cf08f47a3ca88f010606018010091e5447a391c8e47235181d432190c384322d0c2245229148a0fa249c8844088448514860523843a1844862e2050a843920106781b8dc6e813b1d83e783c0dc6e37409d8ec371b9d8ec781b8dd02763b0dc6e8141209028011880da7f3f9f4e21d0e86cee1d389f8422138874e27d2a954c0653e088f6223d1c426133c934f06f381bcd26d389dcee781b8dcee763b0dcea0201008ea7408844b6722d96cb65b399c8e4713895cdc57381bcde6e369b0d86b3484cc06a3487cd03009950ac550b99ccc651c984c863099883e2d2d968ac1a2d868b6612d96cb65b0d180b4600f87c045f2b860bc5d2e158b65a2a958b2582b804aa552b150aa5429944a251139484e51139409a50270589e4e2685800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _ => 0
def rules10 (i : Nat) := packedAt rules10Bits (9*i) 9
def span10 (i : Nat) := (0x38a5e0937c3dd8f703da8f643d78f583d48f4c3d18f403ce8f343cb8f283c88f1c3c58f103c28f043bf8efa2bd8af22bb8aea2b98ae22b78ada2b58ad22b38aca2b18ac22af8aba2ad8ab22ab8aaa2a98aa22a78a9a2a58a922a38a8a2a18a8229f8a7a29d8a7229b8a6a2998a622978a5a2958a522938a4a2918a4228f8a3a28d8a3228b8a2a2898a222878a1a2858a122838a0a2818a0227f89fa27d89f227b89ea27989e227789da27589d227389ca27189c226f89ba26d89b416c85b016b85ac16a85a816985a416885a0167859c166859816585941648590163858c16285881618584160858015f857c15e857815d857415c857015b856c15a856815985641588560157855c156855815585541548550153854c15285481518544150854014f853c14e853814d853414c853014b852c14a852814985241488520147851c146851814585141448510143850c14285081418504140850013f84fc13e84f813d84f413c84ee23a88e623888de23688d623488ce23288c623088c012f84bc12e84b812d84b412c84b012b84ac12a84a812984a412884a0127849c126849812584941248490123848c12284881218484120848011f847c11e847811d847411c847011b846c11a846811984641188456613144440f103440b8c283088c1c3058c103028c06201040210004000 >>> (14*i)) &&& 0x3fff
def pieces10 (i : Nat) := (0xbe61bdbc1d568b0d5dbb9bba1c2a2e2a2e45479878781d5e7881571c2a2397397ab05bb284152c8ea7941c2b2a2c2a7c121d59782d59b9611d156b6d6b090f17016b537785118cb86213609cb71db61db51db42a45b31d15474647984798492d4800651d652581b22cb18c582c8148b081af2c8aad8a58ae5496ad2a232e2dac1dab1d2d72aa1d1d6c231d121d722d2d2ea976842a017d016c9d6667181857677aa8a749a6035278078e26786ba5a4a320785e07200765606a0a96a25ca1a015136e9f0f030a6d150f166d154e9e0e5b5c5a5c0a56461e151e783b495111834f464f0f030f4e462e4c4c2e4c481d9d9c9b9a99059897969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a0b797877767574737271706f13456e6d6c126b6a69680e67666564630c6261605f5e5d465c5b5a0859585756550954535251504f150f4e474d4c4b4a49481c2a4023473a2d28462c452f2923441b2d191d1c1d23311b434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a29282726252423222120061f1e0d04031d1c1b071a1918030009170f14130a161514130601040d12111000030f00030e0d0c060a0b010a09080603070302060403050403020100 >>> (8*i)) &&& 0xff
def atom10 (i : Nat) := (0x1790060150350708d90580690730730608a016981012600880b05304303403a10510384014310606122a0468458624fa84035902502a06032686283884883386984a02584983580381581d82483886987a8148021e286022505486602702604d08c0801e408287e060d0a08e0888781a01c308607311487251284c06605404711b08383057c0480402d484015805a05005204186b82908105b812050840238081d0405108021183508e10c02003c10051004b0278100704ca80180e81d02e80c8368168320870828068002a00c00e03ab8038204dd80d8100630201b001002e02c84c81e04608687008e07c87c0702f111f02000050c80c8651161028b78018d030c0318403f78298601334cd1104404904bc05034910033031911036047 >>> (12*i)) &&& 0xfff
def disp9 (i : Nat) := (0xc1406021ae000000000e001ee9c022000569f800004250480311802005b20080000000a3c00004369e9e90cab40e004d4402008000000dc1a8c0400200400b5daba1000bd800cf1d500c010001c004210000abe1d100321008040240003eac0273200800030070080f0228b0080300c00002c500001d3e7605800014077280b09c010007400f106eec4aaa9b000090201a0ec000031f0000076f11002b6000030440a130150000200000004181432506800c24020340009e8a01c2b0042f002b105c0006400010007d000c5c00d19e300000000056e400000020100101f4a0001b00aa9019b5000000040000c0102c1a00000018002240a0081797803be712c880b718029e408002bd >>> (10*i)) &&& 0x3ff
def link9 (i : Nat) := (0x1783d38334c11cb1205f374a59026919073b1706ba2506202f98487b85e81407481eb7407726a06002021ca3986e215076b2c122b4ba4381ea33a0323632ea2da5eb0c204020809808077902a6806c02b80185505f843307823a3cb2107e80680587293bb3e03604900881f27133187da7116e80704186622384a00f048a1e01c81fa7806d86b08297e05683a86d05ab34072b7206416d12920104104f85603230003036117786586488610e03b38437cb7c01387f100880976942b1892991b88206882985782c82601c05201e286a1b00d364b63804a0504923283881792485486d937845824a7f83a97a85f06f80205e01fb4b23482b07f05107e34e97080f80482887907d01283135b35c04f07917a04da52850035a3c86407c80913526b85402407d85db3c04b821a20a79811076302162b4305382eb3303c24998506106501b10192733eb80324b0018530b17715703b84bb1c37503934934c866a70a0f92f84984e02e032075274242037b09a5bb8725185fb6706a915983a7c32781b91805881488082aa6782808584a85c885a2790a84682714d04c048323b67975b5302d16987221686213804db6690e860844029b83b2181084c934b5227603a33f86c835331b1983e84e14d17b025a0cb3724502687581f122a2907304133d06301f84287006722db1a83830380d806011839b5805d36190285982e832b27010047081877a7396f04f90a036b3702c006a0da27b3d83505a03001608303337bb3017184482e930923260b8704fa4e81aa5082e137a3388103908682e27825584002033686e04606603a07db2580b85e32d825b4098003ab4f13f05024a92a02a17282421d022047878b3581f02f014a1d82491583b01c21306901a02414a1 >>> (12*i)) &&& 0xfff
def programRaw9Bits : Nat → Nat
  | 0 => 0xa9f40a26852554db8c134292aa7d0309a149553c1302d0a4aa9cb4c06852554cf664b6292aa6bc1259149553dd298582a289ead8c2c11554fa0512564aaa77d2298b25553e9114c592aa9f4c5a56c98601b4c3af4c2aa77d2284961553ee11424b0aa9f4c5a12558602a6652a2ac300ca6258261553c6992a130aa99258c2498554fa0c6124c2aa7d3169a256180558f892aa6903656c5492054cf8e22a4902a6d971152481536e2f2a9240a9b71695492054cf864aa4902a67c1255248153bc892a9240a9b24495492054db4b5a4aa9a40d15ad5248153b6956a9240a9dacab5492054db2e0aa4902a72c4649554d20a92f840a40a9d494c2052054ea4ce102902a7526f01854d20e92b80c2a69032d526852054db8a9322902a7526449148153a931858a40a9d497c2c52054ea4b6162902a7526b0b148153e92b858a40a9d494c2c52054efa45ab0a9a40ac54920581530ead4a1286905b4a25154054f1a10a8aa02a77d0854550153b6842a2a80a9eb4215154054f3a10a8aa02a7455f01850153a134250a86905098c285434828abe150a02a7455b0a850153a12b850a86905f48a5614054fb66323051b012b4692528153c6aa495940a99f5524aca054ea4ad25650227c55491b28d20c124ac5940a9f455856ca36030a652f6c02a6da6c92560153be974c2b00a9ae95254d13481b8c52b689a41d85701b60153ea956a9226906f4a5549134831a5124ac02a6ba6d55244d203e36aa922690125b55491348314daaa489a40da6d55244d208c36492b00a9f29525452044f6aae12489a41b26309560153be974ac2a6c02f56a561536017abd2b0a9b00d9711856015366ad2c2b00a9b24496158054db2e0b0ac02a6ad6c58560153be962c2b00a9d34b16158054d7ad12b0a9b00cd6458560153c8922c2b00a9f34216158054efa092b0a9b01ad0495854d80a6842c2b00a9e74216158054d78a9240a9a46db6092554d83d6d98bdad224b6d7c5a54aa679b5d8f4d4a4b4daec6a6a5816daf95535292f7049a657a2079b5d892cd04bcdaec4966882bed9895092caef6cc628496471b662d424b2bbdb317a12598ded98b5092cc6f6cc6284964a7b6631424b24dc4a94ba65956e2d4a5d32c93715a52e996456ca6576c53236c532bb62991bed765a254cacf6bb2d18a64adb6631425323bdb318a12991c6d98b5094caef6cc5e84a6477b662d425323bdb315a129919ed98c5094c93456a52eaa64a96b6057553314b5702baa998a6d54b584acc736bb129a26479b5d892cd30adb5329966921a6d98c4af409536cc6256a087b824d32bd0254db318962812a6d98dcb1409536cc6255a087b824d32c5025cdaec4966885a6d98c4b4609536cc565a304bb824d32d18254daecba64913bed98a9240a9d36995492054ea456510a9a414da658560153
  | 1 => 0xc1346a5940a8d71a046ca360a50d1b165022bc268d8b28115b5182b5a40a9da96b5492054ed655a4aa9a401d5a95358d20be942a5946c16f4c85a84954fb85d092c1226d95308a28913a6854b5950a9f50ca6092554fb82494492aa789700a24955354b8652aa49074c5a5a558601b2a6144c2aa6ab72d52481533e382a9240a9925526452054fb63d35224a4bdb1e8a9125256ca9858ad429770b90614a09572b60a4a5103a3430a249515e8142a5946c1495a352ca0456da52ab651a51d32a18b28115a934695940a8df4a156ca34a33a50ab651a51d02855b28d28a9346c59408af15a34aca0545b2a616ac50257d214b952821c68245ca942c734212e54a215b2a6042d18b0d96d1b3545406ca84bd902a1f6cc96102150db2a431610a86d97118b08543e2386ad824a0365245ac8550db2a12f642a86d96115b085436cb08d8042a1f15c062c2154db2a6054b52a74d228b25e913902b4958b489d74ca4ac8944db49611224a26d9530ba60913be2985d30489db1c52e92854e98e0174c1227c870cba45580a6974d9aa290534ca62ca244eb4a931651227c270d5b28520d2aa4bd94489d348a56ca244fa4452b65122758529b329580d2aa4d814489ae5c12292554faae1836a92407b325b44955356b8444a4aa9f4dc506552483b83d89292aa6db5e449495533d97224a4aa9d4cca45552483866522aa92416d3298249553ed994c124aa9c4cca45552483a66522aa9241433291554920650f6c124aa9b29896092554d9424b0492aa6da6317249553b69145124aa9f508a2892554fa24514492aa68d5a8a2495536d3185124aa9e258c2892554f48e014492aa649700a2495536d304c0a4a
  | _ => 0
def programRaw9 (i : Nat) := packedAt programRaw9Bits (49*i) 49
def program9 (i : Nat) := (programRaw9 i <<< 10) ||| 304
def getProgram9 (i : Nat) := (0x42e15098441e0d058240e04d080c01feb57f3f5f8fb7d3e5f0f77b3d5e8f3793c5e0ef773b5d8eb753a5d0e773395c8e371385c0df6f375b8db6d365b0d76b355a8d369345a0cf6733598cb6532590c76331588c36130580bf5f2f578bb5d2e570b75b2d568b3592c560af572b558ab552a550a75329548a351285409f4f275389b4d26530974b255289349245208f47235188b45225108743215088341205007f3f1f4f87b3d1e4f0773b1d4e873391c4e06f371b4d86b351a4d06733194c86331184c05f2f174b85b2d164b0572b154a853291449850279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200 >>> (9*i)) &&& 0x1ff
def live9 (i : Nat) := (0xe7cdc7ede5ede5eddf69ff25efa5bf69a6cf8dcfa3cf87cf93cfa74f9fa5d7879f87dba5d7a5b9ad9b8fe7a5dea5fb85a2dfa2df935f83dfc35fd7a5a7cde78da72fa5ede7a5a6afa3afa7ade5ade7a591dfa2dfa1df83df93cfabcdaacf8bcfa9cfa9cfcf8dab4faacfab8fabcdcdad93cfa7c7e7a587af93cf93cfc6cfc72fc7cdc5eda7cda5cfe5a7cfa5e6a7a78fa7a7e5ade7a5cbab9fa5caaf97a79fa59e8fab8fea8fd7a5d7a5d727c7a7d7a5d7a5d7a5d6a7d3a7d78797a7b727b787b7a3b5a797a7d9a7d7a5df85b5a7b7a597a7b7a5f5a3b7a5caafcb8fc7cdc5edafa5acafada7adadb4afbc8f9d8fbd8dd5add1af99afd98f9dadb5adeea5bba5dea5bba59fa59fa5dea5fe85fb85fb85b7a5bfa1bf25e7a5bba5dba5dea5df85dba5cfa59fa5cfa59fa5fba1dda5dea5df25d7a59fa5df85bcadd7a5bfc1bf0dbd8dbe8dbf0db78dbb8dde8df7c1ddc5de8ddf0ddf85bcadad6de7a5afa5eea5e7a5cfa5eda5adadc5afa7a7acafe7a587ed9dadafa5afa5bda5b7a5e7a5eea5ef85e7a5e7a5eda5d7a5cfa5cdadbcadadadadadb9ad9dadf98db9adb5adbcadbd8dadad9dadf9a99dadbcadb5adbd8db9adcfa5ada783de83de82fea35e82fe92de83de83de92de83de91de83de83de83de93ce83de83de83dec35ec35ea2dea3ce935e83de91de83de83de83de93cea3dac35ec39ea35e83de83de83de92de935e92de91de91de939e91de83de93ce93ce93cea3cebea4bf84d7a4bd8c >>> (16*i)) &&& 0xffff
def rules9 (i : Nat) := (0xdcbb49a9876543210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 >>> (4*i)) &&& 0xf
def span9 (i : Nat) := (0x30361a0c8602e160a850261208840200 >>> (9*i)) &&& 0x1ff
def pieces9 (i : Nat) := (0xcba9876543210 >>> (4*i)) &&& 0xf
def atom9 (i : Nat) := (0x1b0268880c780c047388b010e21803e02de02a11186 >>> (13*i)) &&& 0x1fff
def disp8 (i : Nat) := (0x770000012414c082 >>> (6*i)) &&& 0x3f
def link8 (i : Nat) := (0x84318623070885980683b83484010507128092078 >>> (8*i)) &&& 0xff
def programRaw8 (i : Nat) := (0x11cb5182b5a40a9da8d15ad5248153b6ba86530492aa6e95348a2c97a44ef86ca985d30489ba54c70cba54520b59b2a6054542a7eb3654c228a244dd2a6994c594489fb07b2e44949553e9ba86522aa9241ed328496092554cf86cb88a9240a9fb47c1255248153762f224aa4902a67c324495492054ddac536aa922690685186c92560153 >>> (59*i)) &&& 0x7ffffffffffffff
def program8 (i : Nat) := (programRaw8 i <<< 10) ||| 304
def getProgram8 (i : Nat) := (0x2307b9ac5a928398a418820 >>> (5*i)) &&& 0x1f
def live8 (i : Nat) := (0x2bad3bf21cb83c8f1f059f43cdc1a7c0f3e439f4a8fcbc2c5e1f354b3e85adc2f6a164f4be5a1 >>> (17*i)) &&& 0x1ffff
def rules8 (i : Nat) := (0x8000 >>> (1*i)) &&& 0x1
def span8 (i : Nat) := (0x2 >>> (1*i)) &&& 0x1
def pieces8 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def atom8 (i : Nat) := (0x47 >>> (7*i)) &&& 0x7f
def disp7 (i : Nat) := (0x39 >>> (3*i)) &&& 0x7
def link7 (i : Nat) := (0x611848 >>> (6*i)) &&& 0x3f
def programRaw7 (i : Nat) := (0x1fd0b97a3157b6011347ad468ad6a9240a9ff0e95342a2e16a54ffa3e19224aa4902a6df685186c92560153 >>> (69*i)) &&& 0x1fffffffffffffffff
def program7 (i : Nat) := (programRaw7 i <<< 10) ||| 304
def getProgram7 (i : Nat) := (0x4688 >>> (3*i)) &&& 0x7
def live7 (i : Nat) := (0x21ea5af48601cfa6a16a5a1 >>> (18*i)) &&& 0x3ffff
def rules7 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def span7 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pieces7 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def atom7 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def disp6 (i : Nat) := (0xb >>> (2*i)) &&& 0x3
def link6 (i : Nat) := (0x2 >>> (1*i)) &&& 0x1
def programRaw6 (i : Nat) := (0x60e10f4ca1a14cb4a24404a3 >>> (95*i)) &&& 0x7fffffffffffffffffffffff
def program6 (i : Nat) := (programRaw6 i <<< 12) ||| 1120
def getProgram6 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def live6 (i : Nat) := (0x43d21 >>> (19*i)) &&& 0x7ffff
def rules6 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def span6 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def pieces6 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1
def atom6 (i : Nat) := (0x0 >>> (1*i)) &&& 0x1

def nodes : Nat → Nat
  | 14 => 1
  | 13 => 27
  | 12 => 600
  | 11 => 2649
  | 10 => 1681
  | 9 => 271
  | 8 => 18
  | 7 => 5
  | 6 => 1
  | _ => 0
def nAlias : Nat → Nat
  | 14 => 1
  | 13 => 70
  | 12 => 1158
  | 11 => 4910
  | 10 => 2860
  | 9 => 425
  | 8 => 22
  | 7 => 5
  | 6 => 2
  | _ => 1
def nHash : Nat → Nat
  | 14 => 1
  | 13 => 35
  | 12 => 579
  | 11 => 2455
  | 10 => 1430
  | 9 => 213
  | 8 => 11
  | 7 => 3
  | 6 => 2
  | _ => 1
def salt : Nat → Nat
  | 14 => 1
  | 13 => 53
  | 12 => 158
  | 11 => 1103
  | 10 => 486
  | 9 => 2
  | 8 => 21
  | 7 => 2
  | 6 => 2
  | _ => 0
def dispAt : Nat → Nat → Nat
  | 14 => disp14
  | 13 => disp13
  | 12 => disp12
  | 11 => disp11
  | 10 => disp10
  | 9 => disp9
  | 8 => disp8
  | 7 => disp7
  | 6 => disp6
  | _ => fun _ => 0
def linkAt : Nat → Nat → Nat
  | 14 => link14
  | 13 => link13
  | 12 => link12
  | 11 => link11
  | 10 => link10
  | 9 => link9
  | 8 => link8
  | 7 => link7
  | 6 => link6
  | _ => fun _ => 0
def programAt : Nat → Nat → Nat
  | 14 => program14
  | 13 => program13
  | 12 => program12
  | 11 => program11
  | 10 => program10
  | 9 => program9
  | 8 => program8
  | 7 => program7
  | 6 => program6
  | _ => fun _ => 0
def getProgramAt : Nat → Nat → Nat
  | 14 => getProgram14
  | 13 => getProgram13
  | 12 => getProgram12
  | 11 => getProgram11
  | 10 => getProgram10
  | 9 => getProgram9
  | 8 => getProgram8
  | 7 => getProgram7
  | 6 => getProgram6
  | _ => fun _ => 0
def liveAt : Nat → Nat → Nat
  | 14 => live14
  | 13 => live13
  | 12 => live12
  | 11 => live11
  | 10 => live10
  | 9 => live9
  | 8 => live8
  | 7 => live7
  | 6 => live6
  | _ => fun _ => 0
def rulesAt : Nat → Nat → Nat
  | 14 => rules14
  | 13 => rules13
  | 12 => rules12
  | 11 => rules11
  | 10 => rules10
  | 9 => rules9
  | 8 => rules8
  | 7 => rules7
  | 6 => rules6
  | _ => fun _ => 0
def spanAt : Nat → Nat → Nat
  | 14 => span14
  | 13 => span13
  | 12 => span12
  | 11 => span11
  | 10 => span10
  | 9 => span9
  | 8 => span8
  | 7 => span7
  | 6 => span6
  | _ => fun _ => 0
def piecesAt : Nat → Nat → Nat
  | 14 => pieces14
  | 13 => pieces13
  | 12 => pieces12
  | 11 => pieces11
  | 10 => pieces10
  | 9 => pieces9
  | 8 => pieces8
  | 7 => pieces7
  | 6 => pieces6
  | _ => fun _ => 0
def atomAt : Nat → Nat → Nat
  | 14 => atom14
  | 13 => atom13
  | 12 => atom12
  | 11 => atom11
  | 10 => atom10
  | 9 => atom9
  | 8 => atom8
  | 7 => atom7
  | 6 => atom6
  | _ => fun _ => 0
def atomWidth : Nat := 7
end PEqualNP.Outside.L_meta_3993

namespace PEqualNP.Outside.L_meta_3993

abbrev CheckContext := Nat × Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → Nat → List (List Sig))
def nextNeg (op fuel : Nat) := if op = 2 then fuel-1 else fuel

def certClose (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun p => scalarPoolCut p k rest op) || (links (keySet ws)).any (sameWords ws)

theorem certClose_sound {raw T pools links k fuel rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → FewImpossible T k fuel xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup) (ok : certClose pools links k rest op = true) :
    FewImpossible T k fuel (choiceVal op :: rest).toFinset := by
  simp only [certClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨p,hp,hh⟩ | ⟨xs,hx,hh⟩
  · exact fun n t bound _ => scalarPoolCut_sound (pValid _ hp) nd hh n t bound
  · rw [sameWords_sound hh]; exact lValid _ _ hx

def checkMove (ctx : CheckContext) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,fuel,n,ws,cov,pools,links) := ctx
  let un := op==2
  let nf := nextNeg op fuel
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if un && fuel==0 then true else
  if len>cap then true else
    let direct := (nf==0) || (len==cap)
    let cc := restCov (getCov cov direct) (column direct a.2) (column direct b.2) un ka kb
    if (cc ||| column direct z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := opKeep un ka kb a b ws
      (len==cap && !passesKW (z::rest)) ||
        certClose pools (links nf) (cap-1) (rest.map Prod.fst) (movedChoice op a b)

theorem checkMove_sound {raw T r s ws pools links cap fuel a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap) (permitted : op=2 → 0<fuel)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ f tag xs, xs ∈ links f tag → FewImpossible T (cap-1) f (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : checkMove (cap,fuel,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    FewImpossible T (cap-1) (nextNeg op fuel) (moveFront ws op a b ka kb).toFinset := by
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
  intro k t hk nt h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold checkMove at test
  have hg : ((op==2) && (fuel==0)) = false := by
    by_cases he : op=2
    · have p := permitted he; simp [he,show fuel≠0 by omega]
    · simp [he]
  simp only [hg,Bool.false_eq_true,if_false] at test
  rw [leq,if_neg (by omega)] at test
  let d := (nextNeg op fuel == 0) || (child.length == cap)
  have sep := cover_sound h (ws:=child) rfl (pair_sep pairs) d (by
    intro hx
    simp only [d,Bool.or_eq_true,beq_iff_eq] at hx
    rcases hx with h0|hv <;> omega)
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have noScore : ((child.length==cap) && !passesKW (z::rest)) = false := by
    by_cases he : child.length = cap
    · have hh : (z::rest).length=k+1 := by
        have eh : (z::rest).length = child.length := by simp [child]
        omega
      have gg : ∀ v ∈ z::rest, faithful r s v := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl|hv
        · exact moved_faithful (faith _ ha) (faith _ hb) op
        · exact faith _ (sub.subset hv)
      have tt := scoreNeeded (ws:=z::rest) pairs gg ndc hh h
      simp [tt]
    · simp [he]
  change ((child.length==cap && !passesKW (z::rest)) ||
    certClose pools (links (nextNeg op fuel)) (cap-1) (rest.map Prod.fst) (movedChoice op a b)) = true at test
  rw [noScore,Bool.false_or] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact certClose_sound pv (lv _) nd' test k t hk nt h

def testPairF (ctx : CheckContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := checkMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRowF (ctx : CheckContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  checkMove ctx 2 a a z false false && checkMove ctx 2 a a z true true &&
    bs.all (fun b => testPairF ctx a b false && testPairF ctx a b true)
def testAllF (ctx : CheckContext) : List Decor → Bool
  | [] => true
  | a::bs => testRowF ctx a bs && testAllF ctx bs

theorem all_unaryF {ctx ws} (h : testAllF ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    checkMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllF,Bool.and_eq_true,testRowF] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binaryF {ctx ws} (h : testAllF ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPairF ctx a b d=true ∨ testPairF ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllF,Bool.and_eq_true,testRowF,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPairF_at {ctx a b d} (h : testPairF ctx a b d = true) (ka kb : Bool) :
    checkMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPairF,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem nodeFew {raw T r s ws pools links cap fuel}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ f tag xs, xs ∈ links f tag → FewImpossible T (cap-1) f (List.toFinset xs))
    (checks : testAllF (cap,fuel,ws.length,ws,preCov ws,pools,links) ws = true) :
    FewImpossible T cap fuel (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk _ h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enumFew nd out
  · intro can v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact checkMove_sound (op:=2) pairs faith nd ha ha (by simp) hc' (fun _ => can) pv lv pro fresh (all_unaryF checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairF (cap,fuel,ws.length,ws,preCov ws,pools,links) a b d = true) :
        FewImpossible T (cap-1) fuel (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have p : (if d then 1 else 0 : Nat) ≠ 2 := by cases d <;> decide
      have h := checkMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc'
        (fun he => False.elim (p he)) pv lv (eq ▸ pr) (eq ▸ fr) (testPairF_at test ka kb)
      simpa only [nextNeg,if_neg p] using h
    rcases all_binaryF checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh



end PEqualNP.Outside.L_meta_3993

namespace PEqualNP.Outside.L_meta_3993

def decoratedInputs := rawDecor 511 pairsP pairsN
def countOps (k : Nat) := 15-k
def sizeOperand (k : Nat) := if 7 ≤ k then 4 else 5
def sliceNat (x i n : Nat) := (x >>> i) &&& ((1 <<< n)-1)

def evalBank (pw : Nat) : Nat → Nat → List Decor → List Decor
  | 0, _, xs => xs
  | d+1, ops, xs =>
    let a := xs.getD (sliceNat ops 0 pw) defaultDecor
    let b := xs.getD (sliceNat ops pw pw) defaultDecor
    let z := codeDecor (sliceNat ops (2*pw) 2) a b
    evalBank pw d (ops >>> (2*pw+2)) (xs++[z])

def neededOps (pw : Nat) (xs : List Decor) : Nat → Nat → Nat → List Choice
  | 0, _, _ => []
  | d+1, ops, pay =>
    let more := neededOps pw xs d (ops >>> (2*pw+2)) (pay >>> 1)
    if pay &&& 1 = 0 then more else
      (sliceNat ops (2*pw) 2,(xs.getD (sliceNat ops 0 pw) defaultDecor).1,
        (xs.getD (sliceNat ops pw pw) defaultDecor).1) :: more

def recipe (k i : Nat) := programAt k (getProgramAt k i)
def storeBank (k i : Nat) := evalBank (sizeOperand k) (countOps k) (recipe k i) decoratedInputs
def stateDecor (k i : Nat) := selectLive ((liveAt k i) >>> 1) (storeBank k i)
def stateWords (k i : Nat) := (stateDecor k i).map Prod.fst
def numNeg (k i : Nat) := liveAt k i &&& 1

def statePools (k i : Nat) (bank : List Decor) : List BoundPool :=
  let ruleList := rulesAt k i
  let entry := spanAt k ruleList
  (List.range (entry &&& 31)).filterMap fun j =>
    let atom := atomAt k (piecesAt k ((entry >>> 5)+j))
    let col := sliceNat atom 0 atomWidth
    let pay := atom >>> atomWidth
    cubeInfos[col]?.bind (fun ci =>
      materialize (vars 511) (neededOps (sizeOperand k) bank (countOps k) (recipe k i) pay)
        (subcube ci.1 ci.2.1) ci.2.2.2.2)

def stateAlias (k f tag : Nat) : Nat :=
  let h := (2*tag+f) % 4294967291
  let n := nAlias k
  let dx := dispAt k ((h * salt k % 4294967291) % nHash k)
  linkAt k (if dx ≥ n then dx-n else (h+dx) % n)

def routes (k f tag : Nat) : List (List Sig) :=
  let entry := stateAlias k f tag
  let i := entry / 8
  if i < nodes k ∧ f = numNeg k i then
    ((automWords[entry % 8]?).map (fun p =>
      (stateWords k i).map (movedWord (p.map swapRows).reverse))).toList
  else []

def verifyNode (k i : Nat) : Bool :=
  let b := storeBank k i
  let ws := selectLive ((liveAt k i) >>> 1) b
  let raw := ws.map Prod.fst
  decide raw.Nodup && !(raw.contains graph) &&
    testAllF (k,numNeg k i,ws.length,ws,preCov ws,statePools k i b,routes (k-1)) ws

theorem target_chart : chartGoal 511 = graph := by decide +kernel
theorem samplePairs : properPairs graph (asRow pairsP) (asRow pairsN) := by
  rw [←target_chart]
  exact chart_pairs (by decide +kernel) (by decide +kernel)

theorem chosenCubeChecks : cubeInfos.toList.all (fun c => colCheck 511 c (boundsBefore known383)) = true := by
  apply listPieces_all (d:=4)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

theorem chosenAutomorphisms : automWords.toList.all (fun p => autoOK graph (p.map swapRows)) = true := by
  decide +kernel

theorem bankFaith (pw n ops : Nat) (xs : List Decor) {r s}
    (h : ∀ v ∈ xs, faithful r s v) : ∀ v ∈ evalBank pw n ops xs, faithful r s v := by
  induction n generalizing ops xs with
  | zero => exact h
  | succ n ih =>
    apply ih
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact h a ha
    · rw [List.mem_singleton.mp ha]
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get h _)
      · exact faithful_bin _ (faithful_get h _) (faithful_get h _)

theorem stateFaith (k i : Nat) : ∀ v ∈ stateDecor k i, faithful (asRow pairsP) (asRow pairsN) v := by
  intro v hv
  exact bankFaith _ _ _ _ (raw_faithful 511 pairsP pairsN) _ ((selectLive_sub _ _).subset hv)

theorem poolsSound (k i : Nat) (b : List Decor) :
    ∀ p ∈ statePools k i b, ValidPool (vars 511) graph p := by
  intro p hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  obtain ⟨ci,hc,hm⟩ := Option.bind_eq_some_iff.mp hj
  have c := List.all_eq_true.mp chosenCubeChecks ci (by simpa using Array.mem_of_getElem? hc)
  have ss := col_sound (m:=511) _ (boundsBefore known383) (before_sound known383 valid383) c
  rw [target_chart] at ss
  exact materialize_sound ss hm

theorem rotateFew {T n f} {ws : List Sig} (hi : FewImpossible T n f ws.toFinset)
    (p : List Move) (ok : autoOK T p=true) : FewImpossible T n f (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  intro k t hk ht h
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
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
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run

theorem routesSound {k}
    (ih : ∀ i < nodes k, FewImpossible graph k (numNeg k i) (stateWords k i).toFinset) :
    ∀ f tag xs, xs ∈ routes k f tag → FewImpossible graph k f xs.toFinset := by
  intro f tag xs h
  simp only [routes] at h
  split at h
  next sel =>
    cases eq : automWords[stateAlias k f tag % 8]? with
    | none => simp [eq] at h
    | some p =>
      simp only [eq,Option.map_some,Option.toList_some,List.mem_singleton] at h
      rw [h]
      have hh := rotateFew (ih _ sel.1) (p.map swapRows)
        (List.all_eq_true.mp chosenAutomorphisms _ (by simpa using Array.mem_of_getElem? eq))
      exact fun n t hn ht => hh n t hn (ht.trans sel.2.le)
  next => simp at h

theorem checkedForest (checked : ∀ k ≤ 14, ∀ i < nodes k, verifyNode k i = true) (k : Nat) (hk : k ≤ 14) :
    ∀ i < nodes k, FewImpossible graph k (numNeg k i) (stateWords k i).toFinset := by
  induction k with
  | zero => intro i hi; exact (Nat.not_lt_zero _ hi).elim
  | succ k ih =>
    intro i hi
    have h := checked _ hk i hi
    simp only [verifyNode,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_true_eq,decide_eq_false_iff_not] at h
    apply nodeFew samplePairs (stateFaith _ _) h.1.1 h.1.2 (poolsSound _ _ _)
    · exact routesSound (ih (by omega))
    · exact h.2

theorem completeCertificate (checked : ∀ k ≤ 14, ∀ i < nodes k, verifyNode k i = true) :
    FewImpossible graph 14 1 (inputs++[anchor]).toFinset := by
  have h := checkedForest checked 14 (by decide) 0 (by decide)
  have raw : stateWords 14 0 = inputs++[anchor] := by decide +kernel
  have fuel : numNeg 14 0 = 1 := by decide +kernel
  rwa [raw,fuel] at h

end PEqualNP.Outside.L_meta_3993

namespace PEqualNP.Outside.L_meta_3993

def atWire (c : CheckContext) (i : Nat) := c.2.2.2.1.getD i defaultDecor
def atMove (c : CheckContext) (i j op : Nat) (ka kb : Bool) :=
  let a := atWire c i
  let b := atWire c j
  checkMove c op a b (movedDecor op a b) ka kb
def cutField (c : CheckContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := atWire c i
  let b := atWire c j
  restCov (getCov c.2.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def batchData (k n : Nat) (xs : List CheckContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (atWire c i).2) xs),
   packedCov (fun c => c.2.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.2.1.2) xs)

theorem batchColumn (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (batchData k n xs) i = packedSig (fun c => (atWire c i).2) xs := by
  simp [laneWire,batchData,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def residual (c : CheckContext) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (k,fuel,n,ws,_,pools,links) := c
  let a := atWire c i
  let b := atWire c j
  let z := movedDecor op a b
  let un := op==2
  let size := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  let rest := opKeep un ka kb a b ws
  if !properB z.1 || ws.any (fun w => w.1==z.1) then true else
    (size==k && !passesKW (z::rest)) ||
    certClose pools (links (nextNeg op fuel)) (k-1) (rest.map Prod.fst) (movedChoice op a b)

theorem residual_ok (c : CheckContext) (i j op : Nat) (ka kb : Bool)
    (h : residual c i j op ka kb=true) : atMove c i j op ka kb=true := by
  rcases c with ⟨k,f,n,ws,co,pools,links⟩
  let c : CheckContext := (k,f,n,ws,co,pools,links)
  let a := atWire c i
  let b := atWire c j
  let z := movedDecor op a b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  let di := (nextNeg op f==0) || (len==k)
  let rest := restCov (getCov co di) (column di a.2) (column di b.2) un ka kb
  change (if un && (f==0) then true else if len>k then true else
    if (rest ||| column di z.2) != BitVec.allOnes 768 then true else residual c i j op ka kb) = true
  simp only [show residual c i j op ka kb=true from h,ite_self]


def quickTry (c : CheckContext) (i j op : Nat) (ka kb : Bool) :=
  (c.2.2.2.2.2.1.map (summarizePool c.2.2.2.1)).any
    (fun r => fastCost r (c.1-1) (atWire c i) (atWire c j) op ka kb)

theorem quickTry_ok {c i j op ka kb} (hi : i<c.2.2.2.1.length) (hj : j<c.2.2.2.1.length)
    (h : quickTry c i j op ka kb=true) : residual c i j op ka kb=true := by
  have mem (x) (h : x<c.2.2.2.1.length) : atWire c x ∈ c.2.2.2.1 := by
    simp [atWire,List.getD_eq_getElem?_getD,h]
  obtain ⟨_,hs,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hs
  have cut := fastCost_good (mem i hi) (mem j hj) ok
  have hpool : c.2.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (atWire c i) (atWire c j) c.2.2.2.1).map Prod.fst)
      (movedChoice op (atWire c i) (atWire c j)))=true := List.any_eq_true.mpr ⟨p,hp,cut⟩
  rcases c with ⟨k,f,n,w,cv,ps,lk⟩
  simp only [residual,certClose,hpool,Bool.true_or,Bool.or_true,ite_self]

def runFallback (c : CheckContext) (i j op : Nat) (ka kb : Bool) :=
  quickTry c i j op ka kb || residual c i j op ka kb

theorem runFallback_ok {c i j op ka kb} (hi : i<c.2.2.2.1.length) (hj : j<c.2.2.2.1.length)
    (h : runFallback c i j op ka kb=true) : atMove c i j op ka kb=true := by
  simp only [runFallback,Bool.or_eq_true] at h
  exact residual_ok _ _ _ _ _ _ (h.elim (quickTry_ok hi hj) id)

def windowWord (o : Nat) (a : Bits) : Bits := BitVec.ofNat 768 (laneKW o a.toNat)
def smallMask : Bits := BitVec.ofNat 768 bandKW

theorem mask_value : smallMask.toNat = bandKW := by decide +kernel

set_option maxRecDepth 4096 in
theorem window_value (o : Nat) (a : Bits) : (windowWord o a).toNat = laneKW o a.toNat := by
  apply Nat.mod_eq_of_lt
  exact (show (a.toNat >>> o) &&& bandKW ≤ bandKW from Nat.and_le_right).trans_lt (by decide : bandKW < 2^768)

theorem combinedBit {α} (f : α → Bits) (xs : List α) (lane j : Nat) (hj : j<769) :
    (combineLanes f xs).testBit (769*lane+j) =
    ((xs[lane]?.map f).getD 0).toNat.testBit j := by
  induction xs generalizing lane with
  | nil => simp [combineLanes]
  | cons x xs ih =>
    simp only [combineLanes,lanePlace,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
    cases lane with
    | zero => simp [hj]
    | succ lane =>
      have hh : ¬ 769*(lane+1)+j < 769 := by omega
      have eq : 769*(lane+1)+j-769=769*lane+j := by omega
      simp only [hh,ite_false,eq,List.getElem?_cons_succ]
      exact ih lane

theorem window_combine {α} (f : α → Bits) (xs : List α) (o : Nat) (ho : o+widthKW ≤ 768) :
    (combineLanes f xs >>> o) &&& (units xs.length*bandKW) =
      combineLanes (fun c => windowWord o (f c)) xs := by
  rw [←mask_value,broadcast]
  apply Nat.eq_of_testBit_eq
  intro j
  let q := j/769
  let i := j % 769
  have hi : i<769 := Nat.mod_lt _ (by decide)
  have ej : j=769*q+i := (Nat.div_add_mod j 769).symm
  rw [ej,Nat.testBit_and,combinedBit _ _ _ _ hi,combinedBit _ _ _ _ hi]
  by_cases hq : q<xs.length
  · simp only [List.getElem?_eq_getElem hq,Option.map_some,Option.getD_some,mask_value,window_value,
      laneKW,Nat.testBit_and,Nat.testBit_shiftRight]
    by_cases little : i < widthKW
    · have lt : o+i<769 := by omega
      rw [show o+(769*q+i)=769*q+(o+i) by omega,combinedBit _ _ _ _ lt]
      simp [hq]
    · have z : bandKW.testBit i=false := by
        change (2^widthKW-1).testBit i=false
        simp [little]
      simp [z]
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hq)]

def ctxFor (k i : Nat) : CheckContext :=
  let b := storeBank k i
  let ws := selectLive ((liveAt k i) >>> 1) b
  (k,numNeg k i,ws.length,ws,preCov ws,statePools k i b,routes (k-1))

def preF (c : CheckContext) :=
  let ws := c.2.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains graph)

def contextList (k o n : Nat) := (List.range n).map (fun j => ctxFor k (o+j))
def batchHeader (k o n ar f : Nat) :=
  (contextList k o n).all (fun x => x.2.2.1==ar && x.2.1==f && preF x)


def sumAt (xs : List CheckContext) (n j : Nat) : LevKW :=
  let f := fun c : CheckContext =>
    let ws := c.2.2.2.1
    totalKW (if j=n then ws else ws.erase (atWire c j))
  (combineLanes (fun c => BitVec.ofNat 768 (f c).1) xs,
   combineLanes (fun c => BitVec.ofNat 768 (f c).2.1) xs,
   combineLanes (fun c => BitVec.ofNat 768 (f c).2.2) xs)
def sumsFor (xs : List CheckContext) (n : Nat) := (List.range (n+1)).map (sumAt xs n)

def weightMask (mask hi unit : Nat) (z : PackedSig) (rest : LevKW) :=
  let a := z.1 &&& mask
  let bb := (z.1 >>> widthKW) &&& mask
  let c := (z.1 >>> (2*widthKW)) &&& mask
  let dd := (z.2 &&& mask) ^^^ mask
  let e := ((z.2 >>> widthKW) &&& mask) ^^^ mask
  let f := ((z.2 >>> (2*widthKW)) &&& mask) ^^^ mask
  let u := (dd &&& (bb ||| c)) ||| (a &&& (e ||| f))
  let v := (dd &&& bb &&& c) ||| (a &&& e &&& f)
  let t := a &&& dd &&& bb &&& c &&& e &&& f
  fullMarks unit (hi ||| t ||| rest.2.2 ||| (u &&& rest.2.1) ||| (v &&& rest.1))

def weightGroup (fuel : Nat) (b : Batch) (weights : List LevKW) (xs : List CheckContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if un && fuel==0 then true else if len>k then true else
    let d := (nextNeg op fuel==0) || (len==k)
    let a := laneWire b i
    let bb := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a bb
    let cov := if d then v else u
    let sep := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d bb) un ka kb ||| packedColumn d z)
    if sep=0 then true else
      let mk := if len==k && (un || ka || kb) then
        let index := if !ka then i else if !un && !kb then j else n
        sep &&& weightMask (r*bandKW) (r*((BitVec.allOnes 768).toNat - bandKW)) r z (weights.getD index (0,0,0))
      else sep
      onMarks (fun c => runFallback c i j op ka kb) mk xs

def groupPair (fuel : Nat) (b : Batch) (w : List LevKW) (xs : List CheckContext) (i j op : Nat) :=
  let f := weightGroup fuel b w xs i j op
  f false false && f true false && f false true && f true true

def groupRow (fuel : Nat) (b : Batch) (w : List LevKW) (xs : List CheckContext) (i : Nat) (js : List Nat) :=
  weightGroup fuel b w xs i i 2 false false && weightGroup fuel b w xs i i 2 true true &&
    js.all (fun j => groupPair fuel b w xs i j 0 && groupPair fuel b w xs i j 1)

def groupRows (fuel : Nat) (b : Batch) (w : List LevKW) (xs : List CheckContext) : List Nat → Bool
  | [] => true
  | i :: js => groupRow fuel b w xs i js && groupRows fuel b w xs js

def groupRun (k n f : Nat) (xs : List CheckContext) :=
  groupRows f (batchData k n xs) (sumsFor xs n) xs (List.range n)

def upperKW : Bits := ~~~smallMask

theorem upper_value : upperKW.toNat = (BitVec.allOnes 768).toNat - bandKW := by decide +kernel

theorem merge_full (x : Nat) (pass : (x &&& bandKW) == bandKW) :
    upperKW ||| (BitVec.ofNat 768 x) = BitVec.allOnes 768 := by
  have eq : (BitVec.ofNat 768 x &&& smallMask) = smallMask := by
    simpa only [smallMask,BitVec.ofNat_and] using congrArg (BitVec.ofNat 768) (beq_iff_eq.mp pass)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' := congrArg (fun a : Bits => a.getLsbD i) eq
  simp only [BitVec.getLsbD_and] at hi'
  simp only [upperKW,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_allOnes,hi,decide_true,Bool.true_and]
  cases hm : smallMask.getLsbD i <;> simp_all

theorem weightLane {α} (xs : List α) (z : α → Decor) (rs : α → List Decor)
    (q : Nat) (hq : q<xs.length) (ok : passesKW (z xs[q] :: rs xs[q]) = true) :
    (weightMask (units xs.length * bandKW)
      (units xs.length * ((BitVec.allOnes 768).toNat - bandKW)) (units xs.length)
      (packedSig (fun c => (z c).2) xs)
      (combineLanes (fun c => BitVec.ofNat 768 (totalKW (rs c)).1) xs,
       combineLanes (fun c => BitVec.ofNat 768 (totalKW (rs c)).2.1) xs,
       combineLanes (fun c => BitVec.ofNat 768 (totalKW (rs c)).2.2) xs)).testBit (769*q) = true := by
  unfold weightMask packedSig
  have wind (f : α → Bits) (o : Nat) (h : o+widthKW ≤ 768) := window_combine f xs o h
  have wd (f : α → Bits) : combineLanes f xs &&& (units xs.length*bandKW) =
      combineLanes (fun c => windowWord 0 (f c)) xs := by simpa using wind f 0 (by decide)
  simp only [wind _ widthKW (by decide),wind _ (2*widthKW) (by decide),wd]
  rw [←upper_value]
  simp only [←mask_value,broadcast,lanes_xor,lanes_and,lanes_or,mark_at _ _ _ hq,beq_iff_eq]
  have good := merge_full _ ok
  simp only [totalKW,mergeKW,levelsKW,BitVec.ofNat_and,BitVec.ofNat_or,BitVec.ofNat_xor] at good
  simpa only [windowWord,smallMask,BitVec.or_assoc] using good

theorem sumsAt_eq (xs : List CheckContext) (n e : Nat) (h : e≤n) :
    (sumsFor xs n).getD e (0,0,0) = sumAt xs n e := by
  simp [sumsFor,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,Nat.lt_succ_of_le h]

def retainedIndex (un ka kb : Bool) (i j n : Nat) :=
  if !ka then i else if !un && !kb then j else n

theorem retainedIndex_le (i j n : Nat) (hi : i<n) (hj : j<n) (un ka kb : Bool) :
    retainedIndex un ka kb i j n ≤ n := by
  cases un <;> cases ka <;> cases kb <;> simp_all [retainedIndex] <;> omega

theorem retainedIndex_spec (c : CheckContext) (i j n : Nat) (hi : i<n) (hj : j<n)
    (un ka kb : Bool) (useIt : (un || ka || kb)=true) :
    (if retainedIndex un ka kb i j n = n then c.2.2.2.1
     else c.2.2.2.1.erase (atWire c (retainedIndex un ka kb i j n))) =
       opKeep un ka kb (atWire c i) (atWire c j) c.2.2.2.1 := by
  have ni := Nat.ne_of_lt hi
  have nj := Nat.ne_of_lt hj
  cases un <;> cases ka <;> cases kb <;> simp_all [retainedIndex,opKeep,delOne,delTwo]

theorem weightHit (xs : List CheckContext) (z : CheckContext → Decor) (n i j : Nat)
    (hi : i<n) (hj : j<n) (un ka kb : Bool) (useIt : (un || ka || kb)=true)
    (q : Nat) (hq : q<xs.length)
    (pass : passesKW (z xs[q] :: opKeep un ka kb (atWire xs[q] i) (atWire xs[q] j) xs[q].2.2.2.1)=true) :
    (weightMask (units xs.length*bandKW) (units xs.length*((BitVec.allOnes 768).toNat-bandKW))
      (units xs.length) (packedSig (fun c => (z c).2) xs)
      ((sumsFor xs n).getD (retainedIndex un ka kb i j n) (0,0,0))).testBit (769*q) = true := by
  rw [sumsAt_eq _ _ _ (retainedIndex_le _ _ _ hi hj _ _ _)]
  unfold sumAt
  apply weightLane
  rwa [retainedIndex_spec _ i j n hi hj un ka kb useIt]

theorem failedWeight (c : CheckContext) (i j op : Nat) (ka kb : Bool)
    (len : 1+(c.2.2.1-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))=c.1)
    (miss : passesKW (movedDecor op (atWire c i) (atWire c j) ::
      opKeep (op==2) ka kb (atWire c i) (atWire c j) c.2.2.2.1) = false) : atMove c i j op ka kb=true := by
  apply residual_ok
  rcases c with ⟨k,f,n,w,u,p,l⟩
  simp only [residual,len,miss,beq_self_eq_true,Bool.not_false,Bool.and_true,Bool.true_or,ite_self]

theorem weightGroup_at (k n fuel) (xs : List CheckContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.2.1=n) (ff : xs[q].2.1=fuel) (actual : xs[q].2.2.2.1.length=n)
    (pass : weightGroup fuel (batchData k n xs) (sumsFor xs n) xs i j op ka kb=true) :
    atMove xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := (nextNeg op fuel==0) || (len==k)
  by_cases skip : ((op==2) && (fuel==0)) = true
  · simp only [atMove,checkMove,ff,skip,if_true]
  have ns := Bool.eq_false_iff.mpr skip
  by_cases small : len>k
  · simp only [atMove,checkMove,budget,arity,ff,ns,Bool.false_eq_true,if_false]
    exact if_pos small
  let a := laneWire (batchData k n xs) i
  let bb := laneWire (batchData k n xs) j
  let cov := if d then packedCov (fun c : CheckContext => c.2.2.2.2.1.2) xs
             else packedCov (fun c : CheckContext => c.2.2.2.2.1.1) xs
  let z := packedOp ((units xs.length)*(BitVec.allOnes 768).toNat) op a bb
  let sep := fullMarks (units xs.length) (takePacked cov (packedColumn d a) (packedColumn d bb) (op==2) ka kb ||| packedColumn d z)
  have chosen : cov = packedCov (fun c => getCov c.2.2.2.2.1 d) xs := by
    dsimp only [cov]; cases d <;> rfl
  have ca : a = _ := batchColumn k n xs hi
  have cb : bb = _ := batchColumn k n xs hj
  by_cases hit : cutField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
  · have bitOn : sep.testBit (769*q)=true := by
      dsimp only [sep,z]
      rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or,mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    have nz : sep ≠ 0 := by intro h; simp [h] at bitOn
    simp only [weightGroup,batchData,ns,Bool.false_eq_true,if_false] at pass
    change (if len>k then true else if sep=0 then true else onMarks _
      (if (len==k) && ((op==2) || ka || kb) then sep &&&
        weightMask (units xs.length*bandKW) (units xs.length*((BitVec.allOnes 768).toNat-bandKW)) (units xs.length) z
        ((sumsFor xs n).getD (retainedIndex (op==2) ka kb i j n) (0,0,0)) else sep) xs) = true at pass
    rw [if_neg small,if_neg nz] at pass
    by_cases tight : ((len==k) && ((op==2) || ka || kb))=true
    · rw [if_pos tight] at pass
      obtain ⟨eqLen,useIt⟩ : len=k ∧ ((op==2) || ka || kb)=true := by
        simpa only [Bool.and_eq_true,beq_iff_eq] using tight
      by_cases weightOk : passesKW (movedDecor op (atWire xs[q] i) (atWire xs[q] j) ::
          opKeep (op==2) ka kb (atWire xs[q] i) (atWire xs[q] j) xs[q].2.2.2.1)=true
      · apply runFallback_ok (by simpa [actual] using hi) (by simpa [actual] using hj)
        apply marked_ok _ _ _ q hq _ pass
        rw [Nat.testBit_and,bitOn,Bool.true_and]
        dsimp only [z]
        rw [ca,cb,packed_op]
        exact weightHit xs (fun c => movedDecor op (atWire c i) (atWire c j)) n i j hi hj _ _ _ useIt q hq weightOk
      · apply failedWeight
        · rw [arity,budget]; exact eqLen
        · exact Bool.eq_false_iff.mpr weightOk
    · rw [if_neg tight] at pass
      exact runFallback_ok (by simpa [actual] using hi) (by simpa [actual] using hj)
        (marked_ok _ _ _ q hq bitOn pass)
  · have miss := bne_iff_ne.mpr hit
    simp only [atMove,checkMove,ff,budget,arity,ns,Bool.false_eq_true,if_false]
    change (if len>k then true else if (cutField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768) then true else _) = true
    rw [if_neg small,if_pos miss]

theorem groupRows_at (k n fuel) (xs : List CheckContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.2.1=n) (ff : xs[q].2.1=fuel) (actual : xs[q].2.2.2.1.length=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : groupRows fuel (batchData k n xs) (sumsFor xs n) xs js=true) :
    testAllF xs[q] (js.map (atWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [groupRows,Bool.and_eq_true,groupRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAllF,testRowF,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @weightGroup_at k n fuel xs
    refine ⟨⟨⟨check hi hi hq budget arity ff actual allRows.1.1.1,check hi hi hq budget arity ff actual allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : groupPair fuel (batchData k n xs) (sumsFor xs n) xs i j (if d then 1 else 0)=true) :
        testPairF xs[q] (atWire xs[q] i) (atWire xs[q] j) d=true := by
      simp only [groupPair,Bool.and_eq_true] at pass
      simp only [testPairF,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity ff actual pass.1.1.1,check hi hj' hq budget arity ff actual pass.1.1.2⟩,
        check hi hj' hq budget arity ff actual pass.1.2⟩,check hi hj' hq budget arity ff actual pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

theorem groupRun_at {k n fuel} {xs : List CheckContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.2.1=n) (ff : xs[q].2.1=fuel) (hn : xs[q].2.2.2.1.length=n)
    (pass : groupRun k n fuel xs=true) : testAllF xs[q] xs[q].2.2.2.1=true := by
  have all := groupRows_at k n fuel xs hq hb ha ff hn (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (atWire xs[q]) = xs[q].2.2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [atWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all


theorem groupVerify {k o n ar f} (hd : batchHeader k o n ar f = true)
    (hp : groupRun k ar f (contextList k o n)=true) :
    ∀ i, o ≤ i → i < o+n → verifyNode k i=true := by
  intro i lo hi
  let xs := contextList k o n
  have hm : ctxFor k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i-o,List.mem_range.mpr (by omega),by simp [Nat.add_sub_of_le lo]⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  obtain ⟨⟨ha,ff⟩,pre⟩ := (by simpa only [Bool.and_eq_true,beq_iff_eq] using List.all_eq_true.mp hd _ hm :
    ((ctxFor k i).2.2.1=ar ∧ (ctxFor k i).2.1=f) ∧ preF (ctxFor k i)=true)
  have hb : xs[q].1=k := by rw [e]; rfl
  have arity : xs[q].2.2.1=ar := e ▸ ha
  have fu : xs[q].2.1=f := e ▸ ff
  have len : xs[q].2.2.2.1.length=ar := by rw [e]; exact ha
  have ok := groupRun_at (xs:=xs) hq hb arity fu len hp
  change (preF (ctxFor k i) && testAllF (ctxFor k i) (ctxFor k i).2.2.2.1) = true
  rw [←e,ok]
  simpa [e] using pre

end PEqualNP.Outside.L_meta_3993

namespace PEqualNP.Outside.L_meta_3993

def rangeCheck (k : Nat) : Nat → Nat → Bool
  | 0,_ => true
  | n+1,o => verifyNode k o && rangeCheck k n (o+1)

theorem range_at {k n o i} (ok : rangeCheck k n o = true) (lo : o ≤ i) (hi : i < o+n) : verifyNode k i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [rangeCheck,Bool.and_eq_true] at ok
    by_cases h : i=o
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega) (by omega)
theorem joinRange {k a b o} (l : rangeCheck k a o = true) (r : rangeCheck k b (o+a) = true) :
    rangeCheck k (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using r
  | succ a ih =>
    simp only [rangeCheck,Bool.and_eq_true] at l
    rw [Nat.succ_add,rangeCheck,Bool.and_eq_true]
    exact ⟨l.1,ih l.2 (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using r)⟩

theorem makeGroup {k o n ar f : Nat}
    (h : (batchHeader k o n ar f && groupRun k ar f (contextList k o n))=true) :
    rangeCheck k n o=true := by
  simp only [Bool.and_eq_true] at h
  have all := groupVerify h.1 h.2
  clear h
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
    simp only [rangeCheck,Bool.and_eq_true]
    exact ⟨all _ (by omega) (by omega),ih (fun i lo hi => all i (by omega) (by omega))⟩

set_option maxRecDepth 16000 in
theorem p14q0 : rangeCheck 14 1 0 = true := @makeGroup 14 0 1 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished14 : rangeCheck 14 1 0 = true :=
  p14q0
set_option maxRecDepth 16000 in
theorem p13q0 : rangeCheck 13 1 0 = true := @makeGroup 13 0 1 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p13q1 : rangeCheck 13 6 1 = true := @makeGroup 13 1 6 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p13q7 : rangeCheck 13 2 7 = true := @makeGroup 13 7 2 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p13q9 : rangeCheck 13 18 9 = true := @makeGroup 13 9 18 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished13 : rangeCheck 13 27 0 = true :=
  (@joinRange 13 7 20 0 (@joinRange 13 1 6 0 p13q0 p13q1) (@joinRange 13 2 18 7 p13q7 p13q9))
set_option maxRecDepth 16000 in
theorem p12q0 : rangeCheck 12 1 0 = true := @makeGroup 12 0 1 9 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q1 : rangeCheck 12 10 1 = true := @makeGroup 12 1 10 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q11 : rangeCheck 12 32 11 = true := @makeGroup 12 11 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q43 : rangeCheck 12 15 43 = true := @makeGroup 12 43 15 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q58 : rangeCheck 12 32 58 = true := @makeGroup 12 58 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q90 : rangeCheck 12 6 90 = true := @makeGroup 12 90 6 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q96 : rangeCheck 12 32 96 = true := @makeGroup 12 96 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q128 : rangeCheck 12 32 128 = true := @makeGroup 12 128 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q160 : rangeCheck 12 32 160 = true := @makeGroup 12 160 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q192 : rangeCheck 12 32 192 = true := @makeGroup 12 192 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q224 : rangeCheck 12 32 224 = true := @makeGroup 12 224 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q256 : rangeCheck 12 32 256 = true := @makeGroup 12 256 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q288 : rangeCheck 12 31 288 = true := @makeGroup 12 288 31 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q319 : rangeCheck 12 32 319 = true := @makeGroup 12 319 32 12 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q351 : rangeCheck 12 13 351 = true := @makeGroup 12 351 13 12 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q364 : rangeCheck 12 32 364 = true := @makeGroup 12 364 32 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q396 : rangeCheck 12 32 396 = true := @makeGroup 12 396 32 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q428 : rangeCheck 12 32 428 = true := @makeGroup 12 428 32 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q460 : rangeCheck 12 32 460 = true := @makeGroup 12 460 32 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q492 : rangeCheck 12 32 492 = true := @makeGroup 12 492 32 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q524 : rangeCheck 12 32 524 = true := @makeGroup 12 524 32 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q556 : rangeCheck 12 32 556 = true := @makeGroup 12 556 32 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p12q588 : rangeCheck 12 12 588 = true := @makeGroup 12 588 12 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished12 : rangeCheck 12 600 0 = true :=
  (@joinRange 12 396 204 0 (@joinRange 12 160 236 0 (@joinRange 12 58 102 0 (@joinRange 12 11 47 0 (@joinRange 12 1 10 0 p12q0 p12q1) (@joinRange 12 32 15 11 p12q11 p12q43)) (@joinRange 12 38 64 58 (@joinRange 12 32 6 58 p12q58 p12q90) (@joinRange 12 32 32 96 p12q96 p12q128))) (@joinRange 12 128 108 160 (@joinRange 12 64 64 160 (@joinRange 12 32 32 160 p12q160 p12q192) (@joinRange 12 32 32 224 p12q224 p12q256)) (@joinRange 12 63 45 288 (@joinRange 12 31 32 288 p12q288 p12q319) (@joinRange 12 13 32 351 p12q351 p12q364)))) (@joinRange 12 128 76 396 (@joinRange 12 64 64 396 (@joinRange 12 32 32 396 p12q396 p12q428) (@joinRange 12 32 32 460 p12q460 p12q492)) (@joinRange 12 64 12 524 (@joinRange 12 32 32 524 p12q524 p12q556) p12q588)))
set_option maxRecDepth 16000 in
theorem p11q0 : rangeCheck 11 3 0 = true := @makeGroup 11 0 3 9 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q3 : rangeCheck 11 6 3 = true := @makeGroup 11 3 6 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q9 : rangeCheck 11 32 9 = true := @makeGroup 11 9 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q41 : rangeCheck 11 22 41 = true := @makeGroup 11 41 22 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q63 : rangeCheck 11 32 63 = true := @makeGroup 11 63 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q95 : rangeCheck 11 32 95 = true := @makeGroup 11 95 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q127 : rangeCheck 11 32 127 = true := @makeGroup 11 127 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q159 : rangeCheck 11 32 159 = true := @makeGroup 11 159 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q191 : rangeCheck 11 32 191 = true := @makeGroup 11 191 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q223 : rangeCheck 11 28 223 = true := @makeGroup 11 223 28 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q251 : rangeCheck 11 32 251 = true := @makeGroup 11 251 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q283 : rangeCheck 11 32 283 = true := @makeGroup 11 283 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q315 : rangeCheck 11 32 315 = true := @makeGroup 11 315 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q347 : rangeCheck 11 32 347 = true := @makeGroup 11 347 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q379 : rangeCheck 11 32 379 = true := @makeGroup 11 379 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q411 : rangeCheck 11 32 411 = true := @makeGroup 11 411 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q443 : rangeCheck 11 32 443 = true := @makeGroup 11 443 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q475 : rangeCheck 11 32 475 = true := @makeGroup 11 475 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q507 : rangeCheck 11 32 507 = true := @makeGroup 11 507 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q539 : rangeCheck 11 32 539 = true := @makeGroup 11 539 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q571 : rangeCheck 11 32 571 = true := @makeGroup 11 571 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q603 : rangeCheck 11 32 603 = true := @makeGroup 11 603 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q635 : rangeCheck 11 32 635 = true := @makeGroup 11 635 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q667 : rangeCheck 11 32 667 = true := @makeGroup 11 667 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q699 : rangeCheck 11 32 699 = true := @makeGroup 11 699 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q731 : rangeCheck 11 32 731 = true := @makeGroup 11 731 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q763 : rangeCheck 11 32 763 = true := @makeGroup 11 763 32 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q795 : rangeCheck 11 6 795 = true := @makeGroup 11 795 6 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q801 : rangeCheck 11 32 801 = true := @makeGroup 11 801 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q833 : rangeCheck 11 32 833 = true := @makeGroup 11 833 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q865 : rangeCheck 11 32 865 = true := @makeGroup 11 865 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q897 : rangeCheck 11 32 897 = true := @makeGroup 11 897 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q929 : rangeCheck 11 32 929 = true := @makeGroup 11 929 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q961 : rangeCheck 11 32 961 = true := @makeGroup 11 961 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q993 : rangeCheck 11 32 993 = true := @makeGroup 11 993 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1025 : rangeCheck 11 32 1025 = true := @makeGroup 11 1025 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1057 : rangeCheck 11 32 1057 = true := @makeGroup 11 1057 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1089 : rangeCheck 11 32 1089 = true := @makeGroup 11 1089 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1121 : rangeCheck 11 32 1121 = true := @makeGroup 11 1121 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1153 : rangeCheck 11 32 1153 = true := @makeGroup 11 1153 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1185 : rangeCheck 11 32 1185 = true := @makeGroup 11 1185 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1217 : rangeCheck 11 32 1217 = true := @makeGroup 11 1217 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1249 : rangeCheck 11 32 1249 = true := @makeGroup 11 1249 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1281 : rangeCheck 11 32 1281 = true := @makeGroup 11 1281 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1313 : rangeCheck 11 32 1313 = true := @makeGroup 11 1313 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1345 : rangeCheck 11 32 1345 = true := @makeGroup 11 1345 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1377 : rangeCheck 11 32 1377 = true := @makeGroup 11 1377 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1409 : rangeCheck 11 32 1409 = true := @makeGroup 11 1409 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1441 : rangeCheck 11 32 1441 = true := @makeGroup 11 1441 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1473 : rangeCheck 11 32 1473 = true := @makeGroup 11 1473 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1505 : rangeCheck 11 32 1505 = true := @makeGroup 11 1505 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1537 : rangeCheck 11 32 1537 = true := @makeGroup 11 1537 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1569 : rangeCheck 11 32 1569 = true := @makeGroup 11 1569 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1601 : rangeCheck 11 32 1601 = true := @makeGroup 11 1601 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1633 : rangeCheck 11 32 1633 = true := @makeGroup 11 1633 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1665 : rangeCheck 11 32 1665 = true := @makeGroup 11 1665 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1697 : rangeCheck 11 32 1697 = true := @makeGroup 11 1697 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1729 : rangeCheck 11 32 1729 = true := @makeGroup 11 1729 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1761 : rangeCheck 11 32 1761 = true := @makeGroup 11 1761 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1793 : rangeCheck 11 32 1793 = true := @makeGroup 11 1793 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1825 : rangeCheck 11 32 1825 = true := @makeGroup 11 1825 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1857 : rangeCheck 11 32 1857 = true := @makeGroup 11 1857 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1889 : rangeCheck 11 32 1889 = true := @makeGroup 11 1889 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1921 : rangeCheck 11 32 1921 = true := @makeGroup 11 1921 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1953 : rangeCheck 11 32 1953 = true := @makeGroup 11 1953 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q1985 : rangeCheck 11 32 1985 = true := @makeGroup 11 1985 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2017 : rangeCheck 11 32 2017 = true := @makeGroup 11 2017 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2049 : rangeCheck 11 32 2049 = true := @makeGroup 11 2049 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2081 : rangeCheck 11 32 2081 = true := @makeGroup 11 2081 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2113 : rangeCheck 11 32 2113 = true := @makeGroup 11 2113 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2145 : rangeCheck 11 32 2145 = true := @makeGroup 11 2145 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2177 : rangeCheck 11 32 2177 = true := @makeGroup 11 2177 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2209 : rangeCheck 11 32 2209 = true := @makeGroup 11 2209 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2241 : rangeCheck 11 32 2241 = true := @makeGroup 11 2241 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2273 : rangeCheck 11 32 2273 = true := @makeGroup 11 2273 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2305 : rangeCheck 11 32 2305 = true := @makeGroup 11 2305 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2337 : rangeCheck 11 32 2337 = true := @makeGroup 11 2337 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2369 : rangeCheck 11 32 2369 = true := @makeGroup 11 2369 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2401 : rangeCheck 11 32 2401 = true := @makeGroup 11 2401 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2433 : rangeCheck 11 32 2433 = true := @makeGroup 11 2433 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2465 : rangeCheck 11 32 2465 = true := @makeGroup 11 2465 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2497 : rangeCheck 11 32 2497 = true := @makeGroup 11 2497 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2529 : rangeCheck 11 32 2529 = true := @makeGroup 11 2529 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2561 : rangeCheck 11 32 2561 = true := @makeGroup 11 2561 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2593 : rangeCheck 11 32 2593 = true := @makeGroup 11 2593 32 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2625 : rangeCheck 11 3 2625 = true := @makeGroup 11 2625 3 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2628 : rangeCheck 11 7 2628 = true := @makeGroup 11 2628 7 12 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p11q2635 : rangeCheck 11 14 2635 = true := @makeGroup 11 2635 14 12 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished11 : rangeCheck 11 2649 0 = true :=
  (@joinRange 11 1953 696 0 (@joinRange 11 929 1024 0 (@joinRange 11 443 486 0 (@joinRange 11 191 252 0 (@joinRange 11 63 128 0 (@joinRange 11 9 54 0 (@joinRange 11 3 6 0 p11q0 p11q3) (@joinRange 11 32 22 9 p11q9 p11q41)) (@joinRange 11 64 64 63 (@joinRange 11 32 32 63 p11q63 p11q95) (@joinRange 11 32 32 127 p11q127 p11q159))) (@joinRange 11 124 128 191 (@joinRange 11 60 64 191 (@joinRange 11 32 28 191 p11q191 p11q223) (@joinRange 11 32 32 251 p11q251 p11q283)) (@joinRange 11 64 64 315 (@joinRange 11 32 32 315 p11q315 p11q347) (@joinRange 11 32 32 379 p11q379 p11q411)))) (@joinRange 11 256 230 443 (@joinRange 11 128 128 443 (@joinRange 11 64 64 443 (@joinRange 11 32 32 443 p11q443 p11q475) (@joinRange 11 32 32 507 p11q507 p11q539)) (@joinRange 11 64 64 571 (@joinRange 11 32 32 571 p11q571 p11q603) (@joinRange 11 32 32 635 p11q635 p11q667))) (@joinRange 11 102 128 699 (@joinRange 11 64 38 699 (@joinRange 11 32 32 699 p11q699 p11q731) (@joinRange 11 32 6 763 p11q763 p11q795)) (@joinRange 11 64 64 801 (@joinRange 11 32 32 801 p11q801 p11q833) (@joinRange 11 32 32 865 p11q865 p11q897))))) (@joinRange 11 512 512 929 (@joinRange 11 256 256 929 (@joinRange 11 128 128 929 (@joinRange 11 64 64 929 (@joinRange 11 32 32 929 p11q929 p11q961) (@joinRange 11 32 32 993 p11q993 p11q1025)) (@joinRange 11 64 64 1057 (@joinRange 11 32 32 1057 p11q1057 p11q1089) (@joinRange 11 32 32 1121 p11q1121 p11q1153))) (@joinRange 11 128 128 1185 (@joinRange 11 64 64 1185 (@joinRange 11 32 32 1185 p11q1185 p11q1217) (@joinRange 11 32 32 1249 p11q1249 p11q1281)) (@joinRange 11 64 64 1313 (@joinRange 11 32 32 1313 p11q1313 p11q1345) (@joinRange 11 32 32 1377 p11q1377 p11q1409)))) (@joinRange 11 256 256 1441 (@joinRange 11 128 128 1441 (@joinRange 11 64 64 1441 (@joinRange 11 32 32 1441 p11q1441 p11q1473) (@joinRange 11 32 32 1505 p11q1505 p11q1537)) (@joinRange 11 64 64 1569 (@joinRange 11 32 32 1569 p11q1569 p11q1601) (@joinRange 11 32 32 1633 p11q1633 p11q1665))) (@joinRange 11 128 128 1697 (@joinRange 11 64 64 1697 (@joinRange 11 32 32 1697 p11q1697 p11q1729) (@joinRange 11 32 32 1761 p11q1761 p11q1793)) (@joinRange 11 64 64 1825 (@joinRange 11 32 32 1825 p11q1825 p11q1857) (@joinRange 11 32 32 1889 p11q1889 p11q1921)))))) (@joinRange 11 512 184 1953 (@joinRange 11 256 256 1953 (@joinRange 11 128 128 1953 (@joinRange 11 64 64 1953 (@joinRange 11 32 32 1953 p11q1953 p11q1985) (@joinRange 11 32 32 2017 p11q2017 p11q2049)) (@joinRange 11 64 64 2081 (@joinRange 11 32 32 2081 p11q2081 p11q2113) (@joinRange 11 32 32 2145 p11q2145 p11q2177))) (@joinRange 11 128 128 2209 (@joinRange 11 64 64 2209 (@joinRange 11 32 32 2209 p11q2209 p11q2241) (@joinRange 11 32 32 2273 p11q2273 p11q2305)) (@joinRange 11 64 64 2337 (@joinRange 11 32 32 2337 p11q2337 p11q2369) (@joinRange 11 32 32 2401 p11q2401 p11q2433)))) (@joinRange 11 128 56 2465 (@joinRange 11 64 64 2465 (@joinRange 11 32 32 2465 p11q2465 p11q2497) (@joinRange 11 32 32 2529 p11q2529 p11q2561)) (@joinRange 11 35 21 2593 (@joinRange 11 32 3 2593 p11q2593 p11q2625) (@joinRange 11 7 14 2628 p11q2628 p11q2635)))))
set_option maxRecDepth 16000 in
theorem p10q0 : rangeCheck 10 6 0 = true := @makeGroup 10 0 6 9 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q6 : rangeCheck 10 18 6 = true := @makeGroup 10 6 18 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q24 : rangeCheck 10 32 24 = true := @makeGroup 10 24 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q56 : rangeCheck 10 32 56 = true := @makeGroup 10 56 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q88 : rangeCheck 10 32 88 = true := @makeGroup 10 88 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q120 : rangeCheck 10 32 120 = true := @makeGroup 10 120 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q152 : rangeCheck 10 32 152 = true := @makeGroup 10 152 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q184 : rangeCheck 10 32 184 = true := @makeGroup 10 184 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q216 : rangeCheck 10 32 216 = true := @makeGroup 10 216 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q248 : rangeCheck 10 32 248 = true := @makeGroup 10 248 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q280 : rangeCheck 10 32 280 = true := @makeGroup 10 280 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q312 : rangeCheck 10 32 312 = true := @makeGroup 10 312 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q344 : rangeCheck 10 32 344 = true := @makeGroup 10 344 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q376 : rangeCheck 10 32 376 = true := @makeGroup 10 376 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q408 : rangeCheck 10 32 408 = true := @makeGroup 10 408 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q440 : rangeCheck 10 32 440 = true := @makeGroup 10 440 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q472 : rangeCheck 10 32 472 = true := @makeGroup 10 472 32 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q504 : rangeCheck 10 14 504 = true := @makeGroup 10 504 14 10 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q518 : rangeCheck 10 32 518 = true := @makeGroup 10 518 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q550 : rangeCheck 10 32 550 = true := @makeGroup 10 550 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q582 : rangeCheck 10 32 582 = true := @makeGroup 10 582 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q614 : rangeCheck 10 32 614 = true := @makeGroup 10 614 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q646 : rangeCheck 10 32 646 = true := @makeGroup 10 646 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q678 : rangeCheck 10 32 678 = true := @makeGroup 10 678 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q710 : rangeCheck 10 32 710 = true := @makeGroup 10 710 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q742 : rangeCheck 10 32 742 = true := @makeGroup 10 742 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q774 : rangeCheck 10 32 774 = true := @makeGroup 10 774 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q806 : rangeCheck 10 32 806 = true := @makeGroup 10 806 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q838 : rangeCheck 10 32 838 = true := @makeGroup 10 838 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q870 : rangeCheck 10 32 870 = true := @makeGroup 10 870 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q902 : rangeCheck 10 32 902 = true := @makeGroup 10 902 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q934 : rangeCheck 10 32 934 = true := @makeGroup 10 934 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q966 : rangeCheck 10 32 966 = true := @makeGroup 10 966 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q998 : rangeCheck 10 32 998 = true := @makeGroup 10 998 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1030 : rangeCheck 10 32 1030 = true := @makeGroup 10 1030 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1062 : rangeCheck 10 32 1062 = true := @makeGroup 10 1062 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1094 : rangeCheck 10 32 1094 = true := @makeGroup 10 1094 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1126 : rangeCheck 10 32 1126 = true := @makeGroup 10 1126 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1158 : rangeCheck 10 32 1158 = true := @makeGroup 10 1158 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1190 : rangeCheck 10 32 1190 = true := @makeGroup 10 1190 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1222 : rangeCheck 10 32 1222 = true := @makeGroup 10 1222 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1254 : rangeCheck 10 32 1254 = true := @makeGroup 10 1254 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1286 : rangeCheck 10 32 1286 = true := @makeGroup 10 1286 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1318 : rangeCheck 10 32 1318 = true := @makeGroup 10 1318 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1350 : rangeCheck 10 32 1350 = true := @makeGroup 10 1350 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1382 : rangeCheck 10 32 1382 = true := @makeGroup 10 1382 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1414 : rangeCheck 10 32 1414 = true := @makeGroup 10 1414 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1446 : rangeCheck 10 32 1446 = true := @makeGroup 10 1446 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1478 : rangeCheck 10 32 1478 = true := @makeGroup 10 1478 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1510 : rangeCheck 10 32 1510 = true := @makeGroup 10 1510 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1542 : rangeCheck 10 32 1542 = true := @makeGroup 10 1542 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1574 : rangeCheck 10 32 1574 = true := @makeGroup 10 1574 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1606 : rangeCheck 10 32 1606 = true := @makeGroup 10 1606 32 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1638 : rangeCheck 10 27 1638 = true := @makeGroup 10 1638 27 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1665 : rangeCheck 10 2 1665 = true := @makeGroup 10 1665 2 11 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p10q1667 : rangeCheck 10 14 1667 = true := @makeGroup 10 1667 14 11 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished10 : rangeCheck 10 1681 0 = true :=
  (@joinRange 10 966 715 0 (@joinRange 10 472 494 0 (@joinRange 10 216 256 0 (@joinRange 10 88 128 0 (@joinRange 10 24 64 0 (@joinRange 10 6 18 0 p10q0 p10q6) (@joinRange 10 32 32 24 p10q24 p10q56)) (@joinRange 10 64 64 88 (@joinRange 10 32 32 88 p10q88 p10q120) (@joinRange 10 32 32 152 p10q152 p10q184))) (@joinRange 10 128 128 216 (@joinRange 10 64 64 216 (@joinRange 10 32 32 216 p10q216 p10q248) (@joinRange 10 32 32 280 p10q280 p10q312)) (@joinRange 10 64 64 344 (@joinRange 10 32 32 344 p10q344 p10q376) (@joinRange 10 32 32 408 p10q408 p10q440)))) (@joinRange 10 238 256 472 (@joinRange 10 110 128 472 (@joinRange 10 46 64 472 (@joinRange 10 32 14 472 p10q472 p10q504) (@joinRange 10 32 32 518 p10q518 p10q550)) (@joinRange 10 64 64 582 (@joinRange 10 32 32 582 p10q582 p10q614) (@joinRange 10 32 32 646 p10q646 p10q678))) (@joinRange 10 128 128 710 (@joinRange 10 64 64 710 (@joinRange 10 32 32 710 p10q710 p10q742) (@joinRange 10 32 32 774 p10q774 p10q806)) (@joinRange 10 64 64 838 (@joinRange 10 32 32 838 p10q838 p10q870) (@joinRange 10 32 32 902 p10q902 p10q934))))) (@joinRange 10 512 203 966 (@joinRange 10 256 256 966 (@joinRange 10 128 128 966 (@joinRange 10 64 64 966 (@joinRange 10 32 32 966 p10q966 p10q998) (@joinRange 10 32 32 1030 p10q1030 p10q1062)) (@joinRange 10 64 64 1094 (@joinRange 10 32 32 1094 p10q1094 p10q1126) (@joinRange 10 32 32 1158 p10q1158 p10q1190))) (@joinRange 10 128 128 1222 (@joinRange 10 64 64 1222 (@joinRange 10 32 32 1222 p10q1222 p10q1254) (@joinRange 10 32 32 1286 p10q1286 p10q1318)) (@joinRange 10 64 64 1350 (@joinRange 10 32 32 1350 p10q1350 p10q1382) (@joinRange 10 32 32 1414 p10q1414 p10q1446)))) (@joinRange 10 128 75 1478 (@joinRange 10 64 64 1478 (@joinRange 10 32 32 1478 p10q1478 p10q1510) (@joinRange 10 32 32 1542 p10q1542 p10q1574)) (@joinRange 10 59 16 1606 (@joinRange 10 32 27 1606 p10q1606 p10q1638) (@joinRange 10 2 14 1665 p10q1665 p10q1667)))))
set_option maxRecDepth 16000 in
theorem p9q0 : rangeCheck 9 32 0 = true := @makeGroup 9 0 32 9 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q32 : rangeCheck 9 20 32 = true := @makeGroup 9 32 20 9 0 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q52 : rangeCheck 9 32 52 = true := @makeGroup 9 52 32 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q84 : rangeCheck 9 32 84 = true := @makeGroup 9 84 32 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q116 : rangeCheck 9 32 116 = true := @makeGroup 9 116 32 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q148 : rangeCheck 9 32 148 = true := @makeGroup 9 148 32 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q180 : rangeCheck 9 32 180 = true := @makeGroup 9 180 32 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q212 : rangeCheck 9 32 212 = true := @makeGroup 9 212 32 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q244 : rangeCheck 9 19 244 = true := @makeGroup 9 244 19 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p9q263 : rangeCheck 9 8 263 = true := @makeGroup 9 263 8 10 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished9 : rangeCheck 9 271 0 = true :=
  (@joinRange 9 244 27 0 (@joinRange 9 116 128 0 (@joinRange 9 52 64 0 (@joinRange 9 32 20 0 p9q0 p9q32) (@joinRange 9 32 32 52 p9q52 p9q84)) (@joinRange 9 64 64 116 (@joinRange 9 32 32 116 p9q116 p9q148) (@joinRange 9 32 32 180 p9q180 p9q212))) (@joinRange 9 19 8 244 p9q244 p9q263))
set_option maxRecDepth 16000 in
theorem p8q0 : rangeCheck 8 16 0 = true := @makeGroup 8 0 16 8 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p8q16 : rangeCheck 8 2 16 = true := @makeGroup 8 16 2 9 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished8 : rangeCheck 8 18 0 = true :=
  (@joinRange 8 16 2 0 p8q0 p8q16)
set_option maxRecDepth 16000 in
theorem p7q0 : rangeCheck 7 3 0 = true := @makeGroup 7 0 3 7 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem p7q3 : rangeCheck 7 2 3 = true := @makeGroup 7 3 2 8 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished7 : rangeCheck 7 5 0 = true :=
  (@joinRange 7 3 2 0 p7q0 p7q3)
set_option maxRecDepth 16000 in
theorem p6q0 : rangeCheck 6 1 0 = true := @makeGroup 6 0 1 7 1 (by decide +kernel)
set_option maxRecDepth 16000 in
theorem finished6 : rangeCheck 6 1 0 = true :=
  p6q0
theorem all3993 : ∀ k ≤ 14, ∀ i < nodes k, verifyNode k i = true := by
  intro k hk i hi
  interval_cases k
  · exact (Nat.not_lt_zero i hi).elim
  · exact (Nat.not_lt_zero i hi).elim
  · exact (Nat.not_lt_zero i hi).elim
  · exact (Nat.not_lt_zero i hi).elim
  · exact (Nat.not_lt_zero i hi).elim
  · exact (Nat.not_lt_zero i hi).elim
  · exact range_at finished6 (Nat.zero_le i) hi
  · exact range_at finished7 (Nat.zero_le i) hi
  · exact range_at finished8 (Nat.zero_le i) hi
  · exact range_at finished9 (Nat.zero_le i) hi
  · exact range_at finished10 (Nat.zero_le i) hi
  · exact range_at finished11 (Nat.zero_le i) hi
  · exact range_at finished12 (Nat.zero_le i) hi
  · exact range_at finished13 (Nat.zero_le i) hi
  · exact range_at finished14 (Nat.zero_le i) hi

end PEqualNP.Outside.L_meta_3993

theorem PEqualNP.Outside.L_meta_3993 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List ℕ := x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates;   PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x2.gates ≤ (1 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x7 ∈ x2.gates, ∀ x9 ∈ x7.inputs, x9 ≤ (10 : ℕ) + x2.size) → (∀ x8 < (10 : ℕ) + x2.size, x8 ∈ x3) → (9 : ℕ) + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x9.op.eval [Bool.false] && !x9.op.eval [Bool.true]) x2.gates).length + ∑ x9 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x9 x3 - (1 : ℕ)) ≤ x2.size → List.count (9 : ℕ) x3 = (1 : ℕ) → x2.output ≠ (9 : ℕ) → (∀ x12 ∈ x2.gates, (9 : ℕ) ∈ x12.inputs → ¬∃ (x15 : Fin (9 : ℕ)), ∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : ℕ → Bool), (∀ (x18 : Fin (9 : ℕ)), x17 ↑x18 = x16 x18) → x12.op.eval (List.map (fun (x19 : ℕ) => if x19 = (9 : ℕ) then x16 (0 : Fin (9 : ℕ)) || x16 (3 : Fin (9 : ℕ)) else x17 x19) x12.inputs) = x12.op.eval (List.map (fun (x19 : ℕ) => if x19 = (9 : ℕ) then x16 x15 else x17 x19) x12.inputs)) → (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x14 ++ [x14 x13]) ≠ x1 x14) → ∃ (x14 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x14 ++ [x14 (0 : Fin (9 : ℕ)) || x14 (3 : Fin (9 : ℕ))]) ≠ x1 x14 := by
  dsimp only
  intro C fan sz count
  intros
  obtain ⟨x,hx⟩ := PEqualNP.Outside.L_meta_3993.few_suffix (PEqualNP.Outside.L_meta_3993.completeCertificate PEqualNP.Outside.L_meta_3993.all3993) C fan sz count
  exact ⟨x,by rw [PEqualNP.Outside.L_meta_3993.codes_v]; exact hx⟩
