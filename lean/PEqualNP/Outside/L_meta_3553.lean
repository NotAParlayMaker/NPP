import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3553

-- The circuit normalization, projections, and induced-subgraph certificates are from
-- L_meta_1667. The marked certificate starts with the extra disjunction present.
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

abbrev LiveState := Nat × Nat × Finset Sig

def LiveStep (s v : LiveState) : Prop :=
  (∃ k t U a, s = (k,t,insert (neg a) U) ∧ v = (k+1,t+1,insert a U) ∧
    proper a ∧ neg a ∉ insert a U) ∨
  ∃ k t U a b d, s = (k,t,insert (bin d a b) U) ∧ v = (k+1,t,insert a (insert b U)) ∧
    proper a ∧ proper b ∧ a ≠ b ∧ bin d a b ∉ insert a (insert b U)

def Live (target : Sig) (k t : Nat) (S : Finset Sig) : Prop :=
  proper target ∧ Relation.ReflTransGen LiveStep (0,0,{target}) (k,t,S)

theorem Live.stop (hp : proper target) : Live target 0 0 {target} := ⟨hp,.refl⟩

theorem Live.unary {k t U a} (ha : proper a) (hf : neg a ∉ insert a U)
    (h : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U) :=
  ⟨h.1,h.2.tail (Or.inl ⟨k,t,U,a,rfl,rfl,ha,hf⟩)⟩

theorem Live.binary {k t U a b d} (ha : proper a) (hb : proper b) (ne : a ≠ b)
    (hf : bin d a b ∉ insert a (insert b U)) (h : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  ⟨h.1,h.2.tail (Or.inr ⟨k,t,U,a,b,d,rfl,rfl,ha,hb,ne,hf⟩)⟩

theorem Live.induct {T : Sig} {motive : ∀ k t S, Live T k t S → Prop}
    (stop : ∀ hp, motive 0 0 {T} (Live.stop hp))
    (unary : ∀ {k t U a} (ha : proper a) (hf : neg a ∉ insert a U) (r : Live T k t (insert (neg a) U)), motive k t (insert (neg a) U) r → motive (k+1) (t+1) (insert a U) (Live.unary ha hf r))
    (binary : ∀ {k t U a b d} (ha : proper a) (hb : proper b) (ne : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (r : Live T k t (insert (bin d a b) U)), motive k t (insert (bin d a b) U) r → motive (k+1) t (insert a (insert b U)) (Live.binary ha hb ne hf r))
    {k t S} (h : Live T k t S) : motive k t S h := by
  obtain ⟨hp,trace⟩ := h
  have go (v : LiveState) (path : Relation.ReflTransGen LiveStep (0,0,{T}) v) :
      motive v.1 v.2.1 v.2.2 ⟨hp,path⟩ := by
    induction path with
    | refl => exact stop hp
    | tail p step ih =>
      rcases step with ⟨k,t,U,a,rfl,rfl,ha,hf⟩ | ⟨k,t,U,a,b,d,rfl,rfl,ha,hb,ne,hf⟩
      · exact unary ha hf ⟨hp,p⟩ ih
      · exact binary ha hb ne hf ⟨hp,p⟩ ih
  exact go _ trace

theorem Live.invert {T : Sig} {motive : ∀ k t S, Live T k t S → Prop}
    (stop : ∀ hp, motive 0 0 {T} (Live.stop hp))
    (unary : ∀ {k t U a} (ha : proper a) (hf : neg a ∉ insert a U) (r : Live T k t (insert (neg a) U)), motive (k+1) (t+1) (insert a U) (Live.unary ha hf r))
    (binary : ∀ {k t U a b d} (ha : proper a) (hb : proper b) (ne : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (r : Live T k t (insert (bin d a b) U)), motive (k+1) t (insert a (insert b U)) (Live.binary ha hb ne hf r))
    {k t S} (h : Live T k t S) : motive k t S h :=
  Live.induct stop (fun ha hf path _ => unary ha hf path)
    (fun ha hb ne hf path _ => binary ha hb ne hf path) h

theorem Live.atZero {T t S} (h : Live T 0 t S) : S = {T} := by
  have gen (k t S) (r : Live T k t S) : k = 0 → S = {T} := by
    induction r using Live.induct <;> simp
  exact gen _ _ _ h rfl

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.induct with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.induct with
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

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

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

def ReachStep {R : Type} (s v : Nat × List (Wire R)) : Prop :=
  (∃ p bank a, s = (p,bank) ∧ v = (p+1,inv a :: bank) ∧ Available bank a) ∨
  ∃ p bank a b op, s = (p,bank) ∧ v = (p+1,combine op a b :: bank) ∧
    Available bank a ∧ Available bank b

def Reach {R} (roots : List (Wire R)) (p : Nat) (bank : List (Wire R)) : Prop :=
  Relation.ReflTransGen ReachStep (0,roots) (p,bank)

theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := .refl

theorem Reach.one {R} {roots : List (Wire R)} {p bank a} (r : Reach roots p bank)
    (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) :=
  r.tail (Or.inl ⟨p,bank,a,rfl,rfl,ha⟩)

theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (r : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) : Reach roots (p+1) (combine op a b :: bank) :=
  r.tail (Or.inr ⟨p,bank,a,b,op,rfl,rfl,ha,hb⟩)

theorem Reach.induct {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p bank a} (r : Reach roots p bank) (ha : Available bank a), motive p bank r →
      motive (p+1) (inv a :: bank) (Reach.one r ha))
    (two : ∀ {p bank a b} (op : Bool) (r : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank r → motive (p+1) (combine op a b :: bank) (Reach.two op r ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  have go (v : Nat × List (Wire R)) (r : Relation.ReflTransGen ReachStep (0,roots) v) : motive v.1 v.2 r := by
    induction r with
    | refl => exact start
    | tail p step ih =>
      rcases step with ⟨_,_,_,rfl,rfl,ha⟩ | ⟨_,_,_,_,op,rfl,rfl,ha,hb⟩
      · exact one p ha ih
      · exact two op p ha hb ih
  exact go _ h

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def RunStep {R : Type} (s v : Nat × List (Wire R)) : Prop :=
  (∃ n xs zs, s = (n,xs) ∧ v = (n,zs) ∧ xs.Perm zs) ∨
  (∃ n a rest b, s = (n,inv a :: kept b a rest) ∧ v = (n+1,a::rest)) ∨
  ∃ n a b rest op ka kb, s = (n,combine op a b :: kept ka a (kept kb b rest)) ∧ v = (n+1,a::b::rest)

def Run {R} (goal : Wire R) (s : Nat) (ws : List (Wire R)) : Prop :=
  Relation.ReflTransGen RunStep (0,[goal]) (s,ws)

theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := .refl

theorem Run.perm {R} {goal : Wire R} {n xs zs} (he : xs.Perm zs) (h : Run goal n xs) : Run goal n zs :=
  h.tail (Or.inl ⟨n,xs,zs,rfl,rfl,he⟩)

theorem Run.one {R} {goal : Wire R} {n a rest} (save : Bool) (h : Run goal n (inv a :: kept save a rest)) :
    Run goal (n+1) (a::rest) := h.tail (Or.inr (Or.inl ⟨n,a,rest,save,rfl,rfl⟩))

theorem Run.two {R} {goal : Wire R} {n a b rest} (op ka kb : Bool)
    (h : Run goal n (combine op a b :: kept ka a (kept kb b rest))) :
    Run goal (n+1) (a::b::rest) := h.tail (Or.inr (Or.inr ⟨n,a,b,rest,op,ka,kb,rfl,rfl⟩))

theorem Run.induct {R} {goal : Wire R} {motive : ∀ n ws, Run goal n ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {n xs zs} (h : xs.Perm zs) (r : Run goal n xs), motive n xs r → motive n zs (Run.perm h r))
    (one : ∀ {n a rest} (b : Bool) (r : Run goal n (inv a :: kept b a rest)),
      motive n _ r → motive (n+1) _ (Run.one b r))
    (two : ∀ {n a b rest} (op ka kb : Bool) (r : Run goal n (combine op a b :: kept ka a (kept kb b rest))),
      motive n _ r → motive (n+1) _ (Run.two op ka kb r))
    {n ws} (h : Run goal n ws) : motive n ws h := by
  have go (v : Nat × List (Wire R)) (r : Relation.ReflTransGen RunStep (0,[goal]) v) : motive v.1 v.2 r := by
    induction r with
    | refl => exact stop
    | tail p step ih =>
      rcases step with ⟨_,_,_,rfl,rfl,he⟩ | ⟨_,_,_,b,rfl,rfl⟩ | ⟨_,_,_,_,op,ka,kb,rfl,rfl⟩
      · exact perm he p ih
      · exact one b p ih
      · exact two op ka kb p ih
  exact go _ h

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
  induction h using Run.induct generalizing p bank with
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
  induction h using Run.induct with
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
  induction h using Live.induct generalizing v with
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
  induction h using Reach.induct generalizing k t S with
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
  induction h using Live.induct with
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

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
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
  induction h using Live.induct with
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
  induction h using Live.induct with
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
  induction h using Live.invert with
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


abbrev BoundPool := Sig × Nat × Nat × List Sig
abbrev BoundPool.domain (c : BoundPool) := c.1
abbrev BoundPool.bound (c : BoundPool) := c.2.1
abbrev BoundPool.paid (c : BoundPool) := c.2.2.1
abbrev BoundPool.wires (c : BoundPool) := c.2.2.2

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
    rw [Live.atZero h] at he
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


def IndexTree (α : Type) := Σ xs : List α, {f : Nat → Option α // ∀ i x, f i = some x → x ∈ xs}

def IndexTree.leaf {α} (xs : List α) : IndexTree α :=
  ⟨xs,(fun i => xs[i]?),fun _ _ h => List.mem_of_getElem? h⟩
def IndexTree.fork {α} (pivot : Nat) (l r : IndexTree α) : IndexTree α :=
  ⟨l.1 ++ r.1,(fun i => if i < pivot then l.2.val i else r.2.val (i-pivot)),by
    intro i x hit
    dsimp only at hit
    split at hit
    · exact List.mem_append_left _ (l.2.property _ _ hit)
    · exact List.mem_append_right _ (r.2.property _ _ hit)⟩
def IndexTree.values {α} (t : IndexTree α) : List α := t.1
def IndexTree.read {α} (t : IndexTree α) := t.2.val
theorem IndexTree.read_mem {α} (t : IndexTree α) {i x} (e : t.read i = some x) : x ∈ t.values :=
  t.2.property _ _ e

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × IndexTree ColumnInfo ×
  Array (List Nat) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))

abbrev Forest.mask (g : Forest) := g.1
abbrev Forest.cap (g : Forest) := g.2.1
abbrev Forest.samples (g : Forest) := g.2.2.1
abbrev Forest.cols (g : Forest) := g.2.2.2.1
abbrev Forest.autos (g : Forest) := g.2.2.2.2.1
abbrev Forest.levels (g : Forest) := g.2.2.2.2.2.1
abbrev Forest.index (g : Forest) := g.2.2.2.2.2.2

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
    rw [Live.atZero h] at he
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

def markedCols : IndexTree ColumnInfo := (.fork 100 (.fork 50 (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13)]) (.leaf [(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12)])) (.fork 3 (.leaf [(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12)]) (.leaf [(17,0,494,0,11),(24,0,487,0,11),(66,0,445,0,11)]))) (.fork 6 (.fork 3 (.leaf [(80,0,431,0,11),(132,0,379,0,11),(144,0,367,0,11)]) (.leaf [(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11)])) (.fork 3 (.leaf [(0,16,486,9,10),(0,64,189,258,10),(0,128,347,36,10)]) (.leaf [(1,16,486,8,9),(2,64,189,256,9),(3,0,508,0,9),(4,128,347,32,9)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(6,0,505,0,9),(8,16,486,1,9),(12,0,499,0,9)]) (.leaf [(18,0,493,0,9),(32,128,347,4,9),(33,0,478,0,9)])) (.fork 3 (.leaf [(65,0,446,0,9),(96,0,415,0,9),(129,0,382,0,9)]) (.leaf [(130,0,381,0,9),(136,0,375,0,9),(256,64,189,2,9)]))) (.fork 6 (.fork 3 (.leaf [(264,0,247,0,9),(288,0,223,0,9),(384,0,127,0,9)]) (.leaf [(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8)])) (.fork 3 (.leaf [(0,8,227,276,8),(0,32,94,385,8),(0,256,151,104,8)]) (.leaf [(5,0,506,0,8),(9,0,486,0,8),(9,16,486,0,8),(10,0,501,0,8)]))))) (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(19,0,492,0,8),(25,0,486,0,8),(36,0,347,0,8)]) (.leaf [(36,128,347,0,8),(40,0,471,0,8),(48,0,462,0,8)])) (.fork 3 (.leaf [(49,0,462,0,8),(67,0,444,0,8),(68,0,441,0,8)]) (.leaf [(70,0,441,0,8),(72,0,183,0,8),(81,0,430,0,8)]))) (.fork 6 (.fork 3 (.leaf [(82,0,429,0,8),(134,0,377,0,8),(140,0,371,0,8)]) (.leaf [(145,0,366,0,8),(152,0,359,0,8),(161,0,350,0,8)])) (.fork 3 (.leaf [(164,0,347,0,8),(194,0,317,0,8),(257,0,254,0,8)]) (.leaf [(258,0,189,0,8),(258,64,189,0,8),(260,0,251,0,8),(272,0,231,0,8)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(280,0,231,0,8),(322,0,189,0,8),(328,0,183,0,8)]) (.leaf [(336,0,175,0,8),(352,0,159,0,8),(416,0,95,0,8)])) (.fork 3 (.leaf [(448,0,63,0,8),(1,2,440,68,7),(1,32,94,384,7)]) (.leaf [(1,64,188,258,7),(1,128,346,36,7),(2,1,460,48,7)]))) (.fork 6 (.fork 3 (.leaf [(2,4,369,136,7),(2,16,484,9,7),(2,128,345,36,7)]) (.leaf [(4,2,440,65,7),(4,8,227,272,7),(4,16,482,9,7)])) (.fork 3 (.leaf [(4,64,185,258,7),(7,0,504,0,7),(8,4,369,130,7)]) (.leaf [(8,64,181,258,7),(8,128,339,36,7),(8,256,151,96,7),(14,0,497,0,7)])))))) (.fork 50 (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(16,1,460,34,7),(16,2,424,69,7),(16,4,353,138,7)]) (.leaf [(16,8,227,260,7),(16,32,78,385,7),(16,64,173,258,7)])) (.fork 3 (.leaf [(16,128,331,36,7),(16,256,135,104,7),(20,0,490,0,7)]) (.leaf [(21,0,490,0,7),(28,0,355,0,7),(32,1,460,18,7)]))) (.fork 6 (.fork 3 (.leaf [(32,16,454,9,7),(32,256,151,72,7),(34,0,476,0,7)]) (.leaf [(35,0,476,0,7),(56,0,455,0,7),(64,1,396,50,7)])) (.fork 3 (.leaf [(64,2,440,5,7),(64,4,305,138,7),(64,8,163,276,7)]) (.leaf [(64,16,422,9,7),(64,32,30,385,7),(64,256,151,40,7),(74,0,437,0,7)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(83,0,428,0,7),(88,0,167,0,7),(98,0,413,0,7)]) (.leaf [(128,1,332,50,7),(128,2,312,69,7),(128,4,369,10,7)])) (.fork 3 (.leaf [(128,8,99,276,7),(128,16,358,9,7),(128,32,94,257,7)]) (.leaf [(128,64,61,258,7),(128,256,23,104,7),(133,0,378,0,7)]))) (.fork 6 (.fork 3 (.leaf [(146,0,365,0,7),(148,0,355,0,7),(156,0,355,0,7)]) (.leaf [(162,0,349,0,7),(176,0,334,0,7),(177,0,334,0,7)])) (.fork 3 (.leaf [(193,0,318,0,7),(196,0,313,0,7),(198,0,313,0,7)]) (.leaf [(224,0,31,0,7),(256,8,227,20,7),(256,16,230,9,7),(256,32,94,129,7)]))))) (.fork 25 (.fork 12 (.fork 6 (.fork 3 (.leaf [(268,0,243,0,7),(273,0,238,0,7),(289,0,222,0,7)]) (.leaf [(296,0,215,0,7),(321,0,190,0,7),(324,0,187,0,7)])) (.fork 3 (.leaf [(344,0,167,0,7),(480,0,31,0,7),(5,2,440,64,6)]) (.leaf [(10,4,369,128,6),(24,4,353,130,6),(34,1,460,16,6)]))) (.fork 6 (.fork 3 (.leaf [(48,1,460,2,6),(66,1,396,48,6),(96,1,396,18,6)]) (.leaf [(3,128,344,36,6),(132,2,312,65,6),(132,8,99,272,6)])) (.fork 3 (.leaf [(160,1,332,18,6),(260,8,227,16,6),(257,32,94,128,6)]) (.leaf [(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6),(21,2,424,64,5)])))) (.fork 12 (.fork 6 (.fork 3 (.leaf [(27,0,484,0,5),(11,16,484,0,5),(29,0,482,0,5)]) (.leaf [(26,4,353,128,5),(50,1,460,0,5),(69,2,440,0,5)])) (.fork 3 (.leaf [(74,4,305,128,5),(98,1,396,16,5),(133,2,312,64,5)]) (.leaf [(138,4,369,0,5),(152,4,353,2,5),(162,1,332,16,5)]))) (.fork 6 (.fork 3 (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5)]) (.leaf [(276,8,227,0,5),(273,32,78,128,5),(56,256,135,64,5)])) (.fork 3 (.leaf [(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5)]) (.leaf [(168,256,23,64,5),(224,256,23,8,5),(15,0,480,0,4),(39,0,344,0,4)])))))))
def markData14 (i : Nat) : Nat := 0x46040a05824186ffd64
def markLevel14 : Packing := (1,1,8,0,0,0,0,markData14)
def markData13 (i : Nat) : Nat := 0x1908a1f0541704c1886a00c408358449c82a0b1f60943d0d831802c230541704a0f0621a80140c41e112720a8247d0ee0c43560620e86e0418012088fb06241403108845070c10d1f4100248e83180621086c22180fa0491d06240c8470282e0c0c0c0621083c2218012868fb06240c847028287d281003c000300a020061a89008060b8450f8290d82e0903a0c4010030080181e0621a240609000058460a82e094360c40110080e0300806e0404890180fabc0a0a024480307d34238141505813061ae454b9ed20e123a7690c1d542713fc6a4a50f5104104007ff5c964ffea92c9ffc52593ffc44b27ff60164ffeb82c9ffd50593ffa60b27ff48164ffe882c97fd97593bfceeb25ff64964ff7112c97fd90593dfac0b27fe80164
def markLevel13 : Packing := (17,2,8,0,0,11,0,markData13)
def markData12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3ffd8748164fff69520593ffca548164fff61520593ffd7548164fff95520593ffda348164fff5cd20593ffd5348164fff60920593ffd5248164fff4c920593ffda148164fff60520593ffd7148164fff54520593ffd3148164fff48520593ffd8344164fff5cd10593ffd8244164fff5c910593ffd5244164fff14910593ffd3244164fff889105937fca564964dff65572592ffeaa54964dff6a552592ffda754964f7f29d52593dfe7754964dff64952593fed7254964bff68052593feca588964ffb5d6225937fd9588964fdf95622593fed5288964dff5d5905937fe5564164dff5c9905937fd5264164dff149905937fe2264164bffaa9805937fda960164f7f9dd805937fd9560164fdf955805937fd9260164ffb889805937fd9160164bffaa970592ffda85c164dff661705937fd955c164f7f5d570593f7e555c164dff64d70593dfd735c164dff64970593fee225c164dff64570593dfd715c164fbf61d60593efd7558164fbf95560593efd7358164fbf5c960593efd5258164fbf14960593efe2258164fbf5c560593efd3158164bffaa9505937fda954164bff6a1505937fd9854164bff69d50593dfe7754164dff65550593f7e5554164fef611505937fd9354164fbf58d505937fd9254164ffb889505937fd9154164fef50550593ff98054164ffe5c150592ffda74c164f7f9dd30593fee224c164ffe60130592ffeaa48164dff6a520592ffda848164dff66120592ffda748164dff65d20593dfe7748164bff695205937fd9548164fdf95520593fbd8448164bff68d205937fd9348164fbf58d205937fd9248164ffb54920593fee2248164dff64520593fbd4148164ffb48520593ff97048164ffe4c120592ffda744164dff65d10593dfe7744164bff68d105937fd9344164fbf58d10592ffda244164dff64910593fee2244164ffe48110593ff98780164ffe61600593ff97580164ffe95600593ff98380164ffe5ce00593ff95380164ffe60a00593ff97280164ffe54a00593ff85280164ffe4ca00593ffa2280164ffe60600593ff97180164ffe54600593ff93180164ffe486005927feaa65d649ffaa9925935fe77649649ff6a5525927fda914964bef69052593dee7788964dfb65622593f6e5588964dfb64a225927feaa64164d7f9dd9059377e5564164dfb889905927fda9601649ff6a570592efeaa58164f3f9dd605936fd9558164f9f95560593ebd8458164dbf64d60593eee2258164dbf64560593ebd4158164fbe601605927fda9541649ff6a530592efda64c1649ff6a5205927fda944164fbe581105937f99880164efea22005937f99780164f7e9de005937f99580164fde95600593fb98480164dfe64e00593ef96380164ff68ce005937f99280164ffa88a005937f99180164fee50600593ff21180164 else 0x122ae040900d07d2408c0301b0530d07f0244744841d1f568020460180d0101ae0a8131204747d5a008118060303507f0262430d8611f561138104806040600d4240f8160a0481f48c3e0660a61b0262420e8fa8006c3c180482200c150262408e8191f4e033810480604007c08180482200c150262430d8191f4e00f810300481f4bc08180480fa4e0582a06048200511c0c0241022702060120800381030090400803e868300905e040900d07d2702c141203e9103a0de041f5088303702c1582d08c09c18641081d02a0446a9210803042008018470530dc1623b06210460140a1f447248060740102708e0ac1623b061f8160b4220c0882300a07408837082480608539c09062480605c23c0b05e0c06054118050787d61a920181d00205c2382b05b0d8138311847810300fa4403847810300fa5c23c0b0507d251d0a31343d6830d00f9f393c7a7714e859c0f367e6b1ccf0988d2f4e59fcaed950b28ce4f6499a92bd248a457c85d90431f6a3c9c7368ddf1ace330c6048b0d14fe26bc47a883b0f861c2433d85c10a9211e41f5834704c2059401e7f14fd39f683e737c00f6b9eae3ce978d6efb5dd33b54761aeaedd1939ca72f0e4c5c64b88270a2dfd1bd6b7666e3edb8db3835dc6a4ed2d1a2bb40566cccc2595bb2866494c7318b7b11d616ac0dd7dcaf0f5d4eb8796d02d4e59e2b27d61babe556faacad5672a5053d0a6594a2291e5156a1653f327894e2c9b11333a6204b86956d284a48b48728f451b4a30c457489a110021a342a284d907220c94104803cfd91f3f3dda7a98f2a1e0d3b76754ce8b9cdb393e70b0dd71b4635d269d8d0c99c732926358c3c98272faa5d88b82967c2c3e5708abd951e29da526ca2f940227604dfc99692e62554498c91391f6238a457488b10f02168423881e10001f723df478a8ee41d50392c7128dd31b44359869a8d0f1990318060c8bdd17162ce455d8a4813aa269049308a810541fe43e987a20e8a1c5036106910cc018382e905a10ae014fc28704dd094211c021f83f807620d5017b82a504a608880e28189029a03ec04f006d00620003ffeaa54964fff69d52593ffda054964fff95622593ffeaa60164fff69d80593ffda560164fff29580593ffd7560164fff95580593ffda260164fff28980593ffd7260164fff54980593ffc5260164fff88980593ffda160164fff4c580593ffda85c164fff68d70593ffda25c164fff54970593ffda15c164fff4c570593ffda854164fff61d50593ffd8554164fff68d50593ffd7354164fff68950593ffd7254164fff54950593ffd3254164fff88950593ffda154164fff5c550593ffd3154164fff48550593ffd724c164fff54930593ffc524c164fff88930593ffd814c164fff5c530593ffd214c164fffaa920593ffda848164fff69d2059) else (if i<3 then 0x8a1a0ff00a48060238e40f08e0a21b82f0608e381dc18238682283a0409010e4708b491040182a83b05c2382f06135060741142283e01086920869351220c1503283d040310264e10dc188a118464750500743e810b70601f5541d82814c238289a87d380c138c084eb0d812238242009e0a61b0322408e330587a2720660a0fb12047200fb05818c3c2420e517120182409b0fc150262440c61a703ec0a0609cc14c342408e8910263eac0ae0a02703182c4811c760f0f44e60a0fb0262440c61a9800c1b05305604c3c488480fa9800c1d868b0e040c02407d461107782b0589cc18238e82102a04c029201808e38121178281f60b4230244ee0c4a05a0a07a4707d422274182009611c14c3705e0c11c7c18238482102a04c029201808e3e0c11c209d4343e88e4220c0c82284205c034342187d91c920182826a9ca1a1210648e4900c108228460121ac342187d91c92018290040c06b27048c09c187a1143708c8e0601f4c8068450dc222381807d3908c1582d0888ec1862058470530dc17830471c82e1109f82c1f60c26a840182500102819832181500105819832181412702c160c04e140d09dc2382b0586d0fb43604e0c5208e042a300a0f408121240b816c0c1643c0d60a07c84686a4881383121381704f0881f686a1106080298442708b2282460488e21b83140b904508c021f524035060881941c48c09938437061c81035c2205b0550d13982e0488ec18b41142001e0105d4343e88e4900c1480206035a0823a4e409c1880188302787da1a844181c27e1107d82c45e0c060705c82103d071398043e88b4900c1413683a9c09083286a48060841142103d070db8040182a4904344883060352078470560b81223b06220650707640e4e40921b831142287e1116e0c03e9900d08a0e2d308d0d0601f51847050910fa44298470560b26a437061f08e0ba1b83018140a61109e22d8160a26a1f5081d02b020908d41807d390281883a3e908289d161847810300fa740e8378120a0901f4c033810300901f4a13c0d611c142443e99038910900c03e950040c0771f498470530d0fa4428c1d828308128458107dc189060c360487d423830c0570608e1b055381f70608e2a0c060a706c2183b056041f7060303b0861a1f7060302b0f0610250887dc18602a0f604b0dc185610c091ab05060c3e0487dc18902ac170608e230861e1f7060302a05610c1c184090fb83186a00a87d4903428c2183b05060c083e9d8403061a1f48c2183b0d0601f4ac21878300fa406a120180c0a00c81943424030340880cc3c21c0c890436180914e0000543e86848060620e11086848060500384482a0c21e244181f08b0fc158244890dc1878008200c206406c3c1fa0ca1a921182d00400c220d70560b60f82686e0c500c41081d0320349043506230 else (if i<4 then 0x75380503ee0c11c4d4e0541ae0c11c4d4aa70208140fa4d4a1f184508a0f4168104126a0c03ea8143050601f508e0c11c702a0930608e13a58120541260c09e238cc218287dc180c047188a308204c143ee0c06023900a1840300fb83047180aa0c61b8304714163080610243ee0c11c7236c204e07d11c247060304205818c20184090712703e891c18c3560a1843050602383e988a21402cc20813050601f447243e308a10c168688e0601f5005984035061270a18910fa802b0330608b86056104d58140c0fa0c306430440c02ac1f064301166818c2183830c181f445c3040160610c12407d2914610c1d828166040c03ec304b0802cc3c1807d8606610c1c5a08b0fb830369c0aa0ce040a987a484221914e60c5015611847058b761e22c3207d21b831645036a1460e0c02409d4230244e07d21b831ac2308b0206b82815409c160c1878640fb831a2d00ab0fc181b4a1b40a8350908444589d8122703ee0c58151510328210d93983047203686f8194114e1059381f70608e5702c16a718787dc180c0f03082d0413b8301808b386d0e883206308a0827448e0c060a60f41c152110601204e07d21b027062e06308a080a8838309381f60490dc18ba0f4104e60c1160c0dc0b0524861e0c01507d3d06a1e054242480fa602a0585c5079381f4489c3687f02a2780b0a16100d68309d1161f581b43e308a10c1e8388b0601f520540b02aa0f2704887d3a0c1380c02429c8fa62290318430760ac083e8308fa9818c198787d0911f4c056060918fa4818c209aa356040c03ec7d440c02c05583c7d1226818c218787d0611f4d03183a9c0fa2463e980650d61e1201815042064060490603f21e9211850d5105c2212e82835c1443e87e0b0fb8249ae0c6a08030809035054089211850f09010c181351548305c400a00c11643c4891413a23886e0c5134c1443f0589d11c43706220650821e22e3e90dc1870188228420440741c4580f0fa9211810d4182e1d84486e0ac124d44890fc188c2204f0560b20b830471d0383b61f830883086818c18c3ca41d83a0312c2703ea0c07e9211850d5a00818c1e4e0358fb83286a10630820e22d3e90dc1878118060303f02782986c4811c960b0161ec0413826700e0a0fb120472e0460180d8280988e07f12204c7d61ab07b0218160180d0104e60a06ac342440989023a3ebe046010258283181360b120472700b0780e2704b40907e1f6244308fac3580488388be058284b87dc1704604e0c5f0240e25d068a80900c0f03283c9c41d04448c09c18808c816828aa11c120181d0040ca0d4161f08e82302706242350741e4358684806074008160650793904448c09c189a0e00e86f020480c03e9f08e0a0774370589cc18239005083e0a11782c1f5024230249ae0c582191c22286d020fa8444e8304a else 0x8304584f06a9f7061353818418c08a260c26a6418c2308b0206a0b04723026a0a93ea09c18d4190318410760f2728288b06a9f63ee0c26ad154c158208e1398304d1f0560b61f0441830d0fa1910760c50aa81382982e0b060c3e088640fb83160541260c11c268a0545440c1170fa08e0c11c812f03283305a0a1f462c3e139830472d83e0ac170441830d0c81f706240a8aa61b8304d140aa0c81941e4e41181224586e0c5097818c091a907a0c2a81843e13a4d608c090fb831e1be0602402b2718291982383047284ba0581941c27c110612720487d122c3706378130760d829868480fa712e1f183d0761b43424030138960c8440a07dc182389a9d840410fb8301813530b)))
def markLevel12 : Packing := (243,3,8,0,0,15,0,markData12)
def markData11 (i : Nat) : Nat := (if i<11 then (if i<5 then (if i<2 then (if i<1 then 0x4c600593efd3ba63002c97fe6d53180164fef4aa98c00b27fd9324c600593ff511263002c9ffc6053180164bff57690c00b277f9b948600592ffcdc243002c9dfe6612180164f7f51090c00b25ff9b748600593bfccba43002c9f7e9dd2180164bff36a90c00b277f99548600593fbd2aa43002c9fee6112180164bff36690c00b277f99348600593f7cb1a43002c9ff68cd2180164eff32490c00b27fea2248600593ff8b8a43002c9ffc4c52180164ffe30708c00b27ff17384600593ff8c1423002c9ffc5ca1180164ffe2a508c00b27ff05284600593ff899423002c9ffc88a11801648ffb6b55324b265feaa9dd925926fedbd54a92c997f6a4a7549649bf9753baa4b265fda99dd52592bf6dc94b112c95fbaed9588964afd974cac44b275ee7765622593eb73bcab112c91ff2e99588964eedcaac9444b257edb954a225932ff554eec82c99df2ea5564164cefd552ab20b2757e77955905933f65d444c82c99fbaaa2264164ebdcef11320b2776e55889905932fed4ceec02c91ff2e99560164cefb532ab00b247fcba649805933f6d4c44c02c9b3faaa7758164e9fceecaac0b26e7eaa95560593e3f3bcaab02c9d9f6565558164f97ceec22c0b27e3e5561160593a7f3bb26b02c9d9f9559358164dddd55112c0b27cee7788960593b76cac44b02c9f9b9562258164fd5b09112c0b276ed9388960593a7f3bb22b02c9d9f9559158164eddc44c8ac0b27cbe7750560593f5711282b02c97beaed8058164f9f4eec02c0b27e7a5560160593f7511300b02c997f6a67754164cefb532aaa0b267eda988950593ddcc2300a82c997f6a6774c164d9fceed3260b267eda988930593776d3444982c91ff2e99748164cbfb533ba40b247fcba655205933bed4caa902c99fb6a62248164cbfb533ba20b267eda988910593e7d3bac0882c9f9e9556044164fdd444b0220b27fb14148110593afccc4ef002c9e7ea227780164e7f510cac00b275fa7765600593bbccc4ab002c9edea225580164faf4ef2ac00b277799595600593edd3bb09002c9fce9558480164ebf4eec9c00b2777a5564e00592f7d5dac7002c9f3e9dd6380164fcf4aab1c00b27ed98358e00593eed3bc67002c9cfea219280164ebf4eec9400b2777a5564a00592f7cdb0a5002c9dfa6622280164f7d51111400b277e99788a00593ef53bc45002c9dfa6562280164fed4ab11400b27fa98488a00593bf4c9c45002c9fba58e2280164ff946711400b277e99288a005939fd44323002c9d7e9dd9180164eef4aac8c00b277ea2264600593ddd44283002c9f6e9dd4180164fe74aaa0c00b27faa2250600593f6cb1a63002c9dfc65e1180164fbe4ef08c00b277f19384600593f78b1c23002c9ff48ce1180164efe32508c00b27fe22284600593d5cc2300b02c9fac5056044164 else 0xc97fe6e17380164fbf30eb9c00b27f7a555ce00593f7cc3ac7002c9fbe6156380164fdf2eab1c00b27efa5558e00592ffd5daa7002c97fe6e15380164bff36ea9c00b27dfa7754e00593fbcc2aa7002c9fde9555380164ffb306a9c00b27fd97354e00593bfcc3b25002c9dfe6159280164eff2eac9400b277fa5564a00592ffd5db05002c9dfe6e58280164eff32ec1400b27bf98760a00593efd3bb05002c9dfe6558280164fef4aac1400b277f99360a00593dfcc1b05002c9fbe58d8280164eff324c1400b25ff9b85ca00593bfccc2e5002c9efea217280164eff32ab9400b27f7a555ca00593fdcc22e5002c9dfe64d7280164fbf2e6b9400b27ef9635ca00593fed19ae5002c97feaed5280164eff372a9400b25ff9b854a00593bfccc2a5002c9efea215280164bff36ea9400b27df8b754a00593efd3baa5002c9dfe6555280164fef2eaa9400b27f7a5554a00593fdcc22a5002c9dfe64d5280164fdf2c6a9400b27f795354a00593fed19aa5002c9dfe6495280164ffd304a9400b27fe97254a00592ffcdc0a5002c9dfe6605280164f7f51029400b27fb98414a00592ffcd98a5002c9dfe64c5280164fdf2c629400b27fda3314a00592ffcd88a5002c97feaed3280164bff37099400b25ff9b74ca00593efd3ba65002c97fe6d53280164fef4aa99400b27fd9734ca00593ff4c1265002c9ffa61e2280164ffd16b11400b27fe98588a00593ff4bac45002c9ffa9562280164ffd30711400b27fe97388a00593ff4a9c45002c9dfe6622280164f7f51111400b277f99588a00593fbd2ac45002c9fee6122280164eff32711400b27ef96388a00593fed19c45002c9ffa60a2280164ffd2a511400b27fe93288a00593bfcc3b23002c9dfe6159180164eff2eac8c00b277fa5564600593bfcc1323002c9dfe5c99180164eff2a4c8c00b277f85264600593bfd11323002c9f7e9dd8180164fef4aac0c00b27fda3360600593dfcc1303002c9ffa8898180164bff576b8c00b25ff9b85c600593bfccc2e3002c9efea217180164fbf30eb8c00b277f9955c600593fbd2aae3002c9fee6117180164eff326b8c00b27ef9635c600593fed19ae3002c9dfe6497180164fbf2e4b8c00b27fea225c600592ffd5daa3002c9dfe6e55180164bff370a8c00b277f99854600593dfd442a3002c97fe6dd5180164eff32ea8c00b27dfa7754600593bfccaaa3002c9fde9555180164ff7308a8c00b277f99354600593f7cb1aa3002c9ff68cd5180164eff324a8c00b27f795254600593ff5112a3002c9ffc6055180164ffe2e2a8c00b27fb98750600593fdcc2a83002c9fee5d54180164ff74aaa0c00b27fb98250600593fdcb9283002c9fee5494180164ff70a4a0c00b27fba2250600592ffd5da63002c97fe6e13180164f7f51098c00b25ff9b7) else (if i<3 then 0xeec8a40b267fda564520593bbf2ab22902c9dfb5499148164efdc44c8a40b26dfda75c5205927fe5d2a2902c9fdb5495148164df7d54a0a40b26fbda8505205937ded3a82902c9f6f9dd4148164df7b4aa0a40b27f3e5550520593fd6a9282902c9feb88941481649ff97498a40b26fdda34c520593f6eb1a62902c97fbaed2148164dfdd5490a40b277edb948520593bf6d4a42902c9dfb6612148164fbdcee90a40b25fedb548520593bf6caa42902c9fdb9552148164ff5b0890a40b277ed9348520593f76b1a42902c9ff95c52148164ffca6290a40b277ed9248520592ffd5dae0902c9bfeaa97048164eff352b8240b277f9985c1205937fcd2ae0902c9dfe6557048164fbf2eab8240b27f7a555c120593fdcc22e0902c9dfe64d7048164fbf2e6b8240b27ef9635c120593ff4a92e0902c9dfe6457048164fbf2e2b8240b27fb9415c120593ff490ae0902c9bfeaa93048164dff35098240b25ff9b74c120593efd3ba60902c9fde9553048164ffb2a698240b27fe9524c120593ff511260902c9ff64c53048164ffd24298240b24ffebb69d105927ff5db46882c9b7f9dda344164cffb4ec9a20b275fe7764d105927fedd306882c93ff6e97344164ddfb4eb1a20b27cfe7758d105927ff5db44882c99ff6e5a244164cffb30d1220b267fd97689105936ff3bb44882c9bef611a244164cffb26d1220b26efd63689105933fed3b24882c9d7f9dd9244164cffb4ac9220b267fda2649105927fedd304882c93ff6e97244164cffb52b9220b24ffdba549105933fed4aa4882c93ff6e85244164cffb5229220b25ff9b0149105927fedd264882c9bfb6a22244164efdb3111220b26feda788910593ef73bc44882c9bfb6962244164efdb2b11220b27f6e5588910593fd6c2444882c9bfb68e2244164efdb2711220b27eed63889105933fed4c44882c9bfb68a2244164efdb2511220b27ef97558110593f7d2aac0882c9fbe5cd6044164fdf2a6b0220b27ef97258110593f7ca92c0882c9fbe1496044164fdf264b0220b27efa2258110592ffd5da40882c9dfe6e52044164eff33090220b26ff9a748110593bfccba40882c9f7e9dd2044164eff32a90220b27f7a5548110593fdcc2240882c9bfe68d2044164eff32690220b27ef96348110593bfcc9240882c9ffa5492044164ffd44490220b27ff15148110592ffd5db0f002c9dfe61d9580164bff576c2c00b277f9b961600593dfcc3b0b002c9f7e9dd8580164eff32ac2c00b25ff9b85d600593bfccc2eb002c9efea217580164fbf30ebac00b27f798795600593fbc594ab002c9dfe6625580164f7f5112ac00b27f798595600593fdcbab09002c9fee9558480164eff30ec9c00b277f98564e00593bfcbab27002c9dfe9559380164fbf4eec1c00b27f7a5560e00592ffd5dae7002 else (if i<4 then 0x593efd3bb00a82c9fde2d58054164eff32ac02a0b27bf98560150593fbd2ab00a82c9dfe64d8054164fdf2c6c02a0b277f99260150593ff511300a82c9dfe6458054164ff7282c02a0b25ff9b85c150593bfccc2e0a82c9fee6117054164eff326b82a0b27df9735c150593f7cb1ae0a82c9dfe6497054164ffd444b82a0b277f9915c150593efcb8ae0a82c9fee50570541649ffd76d3a60b267fda95c93059377ed32e4982c99ff6a5524c164ddfb4ca9260b24ffdba149305933fed48a4982c97bf6d8524c164ddfb4c29260b25ff9b0149305937f6d3c44982c9f7b9de224c164fedcab11260b267fda98893059377ed3444982c97feaed804c164fbf4eec0260b27bf98560130593fbd2ab00982c9ffa889804c164f7f302c0260b27fd931601305927fedc554902c93ff6deaa481649ffb6b55240b24ffdb3aa9205927fed8d54902c99ffaa9a9481649ffd76d4240b267fdb96a1205933fed4b50902c99ffaa998481649ffd76d3a40b267fd9869d205933fed4b4e902c99ffaa99748164cffb50cba40b24ffdba61d205936ff554ee902c9d7f6a67748164dbfb513ba40b275fd989dd205927ff5db4a902c99ff6e5a548164cffb30d2a40b26dfcb7695205936ff3bb4a902c99ff6a5a548164cffb5252a40b25efdb6295205937bed294a902c99ffaa99548164cffb50caa40b267fda765520593aff3bb2a902c99ff69595481649ffb74c2a40b24ffdba5d5205933fed4aea902c9bdf2ea5548164defd552aa40b2777da9955205937bed44aa902c9ddf6625548164defb4f2aa40b27d7e7795520593fb6594aa902c93ff2ea5548164cffb532aa40b26f7da595520593bbecacaa902c9befaa98448164df7b4ec2240b27dbe77611205937ded2b08902c9fcf95584481649ffd76d1a40b26dfe7768d205937bf2ab46902c99ffaa99348164cffb4ec9a40b275fe7764d205933fed2b26902c9ddf95593481649ffb74b9a40b26dfda75cd20592f7f5dac6902c9bbfaa96348164ddfb4eb1a40b27cfe7758d2059377ed2ac6902c9f9f95563481649ffb74a9a40b24ffcba54d205933ff55324902c99ff6a19248164cffb4ac9240b2777e5564920593bf6c9304902c97fbaed5248164dfdd54a9240b277edb954920593bf6d4aa4902c9bfb6a15248164efdb30a9240b27decb7549205937f6d3aa4902c9f7b9dd5248164fed94aa9240b277ed9554920593fb6baaa4902c9fdb9555248164ff5b08a9240b277ed9354920593f76b1aa4902c9fdb54d5248164cffb52a9240b277ed9254920593bf6d4c44902c9bfb6a22248164efdb3111240b26feda588920593bf6cac44902c9fdb9562248164ff5b0911240b26feda388920593bf6c9c44902c9fbb58e2248164cffb52d0a40b267feaa645205933fed4322902c99ff69d9148164ebfc else 0xf6a1915c164ebfaeac8ae0b2777e5564570593bf711322b82c9b7faa9715c164ebfb26b8ae0b275fd925c570593ef7112e2b82c977f6dd315c164bdfd76c3ac0b26efeaa5d560593e7ec3aeab02c9f9f61e5558164fcf9652aac0b26efeaa95560593f5ebab08b02c9faf9558458164edfaeac9ac0b276fe5564d60592f7f5dae6b02c9bbfaa97358164f9fb0eb9ac0b27e7e555cd6059377f552e4b02c9dbf6557258164fcfcaab92c0b27ebd845c960593b7ec9ae4b02c9f3f5cd7258164bdfd76a92c0b26efeaa54960592f7edbaa4b02c9f3f2dd5258164f9fceea92c0b276fd9554960593f3ebaaa4b02c9f9f9555258164fd7b08a92c0b276fd9354960593f76b92a4b02c9bbfaa85258164bdfb70292c0b27ebd8414960592f7ed98a4b02c9dbf64c5258164bdfb62292c0b27eed8788960593f765ac44b02c9fbb5d62258164fddcab112c0b27eed738896059377f55444b02c9dbf6562258164fcfcab112c0b27ebd8488960593b7ec9c44b02c9fbb54a2258164edfaeac8ac0b276fe5564560593b7eb9322b02c9dbf5499158164edf8a4c8ac0b276fe2264560592f7f5dae2b02c9f9f9557158164f9fae4b8ac0b27eee225c560593f5eb9282b02c9faf5494158164fd78a4a0ac0b27ebe2250560592f7f5da62b02c97bf6dd3158164f9fcee98ac0b27e7e554c560593f7711262b02c9fbeaed8058164fdf36ec02c0b27ef9b560160593f7c5ab00b02c9fbe5d58058164fdf4aac02c0b27ef9b360160593f7cb9b00b02c9fbe6c98058164fdf164c02c0b27ef97260160593f7ca9300b02c9fbe1498058164fdf444c02c0b24ffebb6a1505933fedcb50a82c99ff6a5a854164cffd54cc2a0b267fd9869d505927fedd30ea82c9b7f6a27754164ebfb313baa0b267fda865550593bbecab0aa82c9bdf6a25554164eefb312aaa0b26fbeaa611505937ded3b08a82c9f6f9dd8454164fe7caac22a0b267feaa64d505933fed3b26a82c9d7f9dd9354164eefcaac9aa0b25efebb58d5059377f552c6a82c9bbf69d6354164f9fceeb1aa0b27e7e5558d505933fed4b44a82c99ffaa99254164cffb50c92a0b267fda764950593aff3bb24a82c9ddf9559254164cffb52b92a0b267fda9549505937f65d444a82c9bfbaaa2254164efdb53112a0b26feda888950593bf6cc444a82c9bfb69e2254164fbdcef112a0b277ed9588950593fb72ac44a82c9feb6122254164efdb27112a0b27eed63889505933fed4c44a82c9dfb64a2254164cffb52d0aa0b267feaa645505933fed4322a82c99ff69d9154164ebfceec8aa0b2777e5564550593bf711322a82c9befaa94154164df7b50a0aa0b26fbda750550593edf3ba82a82c9fcf9554154164ff5c44a0aa0b27edd634c550592ffd5db00a82c9bfeaa98054164eff372c02a0b277f9a96015))) else (if i<8 then (if i<6 then 0x220b277fd9388910593f7eb1c44882c9ffeaed2044164fff37090220b27ff9b748110593ffcc3a40882c9ffe6d52044164fff16a90220b27ff98548110593ffcbaa40882c9ffe9552044164fff36690220b27ff98348110593ffcb9a40882c9ffe54d2044164fff30490220b27ff95248110593ffc99240882c95ffaed955c9649ffb6f552a4b26dfdb7aa9525927fed8554a92c977f6deaa54964affd76d4aa4b267feaa6a552593afe5bb52a92c93ffaeda754964cffb52d3aa4b26dfeaa29d52593afed494ea92c977f2ea7754964dbfd553baa4b275fda99dd52592bff5db24a92c99ffaa99254964eef96ac92a4b26feeaa5c952593bf6d4ae4a92c99ff6a5a054964dbf94ed02a4b25fedb129622592ff6d814b112c9dfb2e99588964fed9752ac44b257febb656225933fe5d32b112c93ff2ea5588964efd96ac9444b277ee5564a22592ff75daa5112c9dfb6e55288964efdb2aa9444b27f6e5554a225933ff552eac82c9ddf2ca5564164cffd552ab20b267feaa5c990593bbf2aae4c82c95ffaed5264164cffb74a9320b267feaa54990592bfedbaa4c82c9d7f2dd5264164ebfceea9320b2777d7554990593bbf2aaa4c82c9dfb5c95264164cffd5429320b257fdb814990592bfed98a4c82c95ff6c45264164efd96b11320b277ed7588990593bf72ac44c82c99ffaaa2264164eefcab11320b277ed52889905927fedbd54c02c93ff6d6aa601649ffb6555300b24ffdb1aa9805933ff55352c02c99ff6a5a760164bef96ad3b00b26dfeaa9dd80593afed4ceec02c99ff6a5a560164cffb5252b00b25dfdb7295805937bed294ac02c97fb6c8a560164bfeb6252b00b267feaa65580593aff3bb2ac02c99ff6a57560164def9752ab00b26f7eaa95580593bbed4caac02c9f5f9de55601649ff9752ab00b267fda995580593bbecacaac02c99ff6a5a260164cffb5251300b26feda2289805933ff55324c02c9d7f9dd9260164eefcaac9300b267fda95c9805927fe5d2a4c02c99ff6a552601649ffb7429300b267fda914980592ffcd80a4c02c9bfb2ea2260164dfdd5511300b277eda988980593ef73bc44c02c9dfb6562260164fedcab11300b24ffcba889805933fed4c44c02c9dfb64a2260164cffd54c8b00b275fe7764580593bbf2ab22c02c9dfb88991601649ff97498b00b24ffebb6a1705937be5ab50b82c99ffaa9985c164cffb50caae0b26dfda85d570593afecc2eab82c9bdf6a2555c164eefb312aae0b267feaa64d70593afebab26b82c9ddf955935c164dbfd54b9ae0b267feaa649705933fed4324b82c9d7f5d5925c164eefcaac92e0b27d7d75549705937f755444b82c9bfb6a2225c164efdb31112e0b277ed9588970593ef6bac44b82c9fdb956225c164efdb27112e0b27ded73889705933ff55322b82c99f else (if i<7 then 0x7fedd2a2902c9bffaa95148164dffb4ea8a40b26ffda354520593bfec9aa2902c9fbf58d5148164ffdb64a8a40b277fd9254520593ff6a92a2902c9fef6a14148164ff7b4ea0a40b27fbd8750520593fded2a82902c9fef6154148164ff7aeaa0a40b27fbe5550520593fdec1282902c9fef5494148164bffd7698a40b25ffdba4c5205937fedd262902c9bffaa93148164dffb5098a40b25ffdb74c5205937fed3a62902c97ff6d53148164dffb4a98a40b27fdda34c520593ff6a9262902c9ff74c93148164ffeb0298a40b27ff9b04c520593ff755242902c9ffb6e12148164ffdb5090a40b27feda748520593ff6c3a42902c9ffb6d52148164ffdb4a90a40b27feca548520593ff6c2a42902c9ffb5d52148164ffdcaa90a40b27fedb348520593ff6d1a42902c9ffb5cd2148164ffdaa690a40b26ffeaa48520592ffedc242902c9bff6a12148164effb3090a40b25ffdb5485205937fed2a42902c9dff6552148164ff7b0890a40b25ffdb3485205937fed1a42902c9dff64d2148164fdfac690a40b27fed8248520593ff6a9242902c9ffb4c92148164ffea6290a40b27ffaaa5c120593ffcd42e0902c9ffe6957048164fff30ab8240b27ff9a35c120593ffca9ae0902c9ffe6857048164fff302b8240b27ff9515c120593ffc98ae0902c9ffeaa93048164fff35098240b27ff9a74c120593ffcc3a60902c9ffe6953048164fff14a98240b27ff9854c120593ffcbaa60902c9ffe9553048164fff30498240b27ff9524c120593ffcd0a60902c9ffe6053048164fff2e298240b27ff9514c120593ffc90a60902c9bff6e1a344164dffb6ed1a20b26ffdb568d105937fed9346882c97ffaed7344164bffb70b9a20b26ffda85cd10593efec3ae6882c9bffaeda244164dffb70d1220b26ffdb7689105937fec3b44882c9bff6d5a244164dff96ad1220b26ffdb3689105937feb9b44882c97ffaed8244164dffb74c1220b26ffda760910593dfec3b04882c9bff6958244164dffb46c1220b26ffda260910592ffedc2e4882c9bff6a17244164effb30b9220b26ffda55c910593bfecaae4882c9fef6117244164dffb46b9220b277fd935c910593efeb9ae4882c9fbf58d7244164bffd76a9220b26ffdba54910593bfedcaa4882c97ff6dd5244164fbf96ea9220b26ffda354910593bfec9aa4882c9fbf58d5244164dffb44a9220b277fd9254910593ff6c12a4882c9ffb5c95244164bffb6629220b26ffda314910593bfec98a4882c9fbf58c5244164bffd7699220b26ffdba4c910592ffedc264882c9bff6a13244164bffb6e99220b26ffda74c910592ffedaa64882c9bff6953244164ffbae699220b26ffda24c910593ff6c1264882c9bff6a22244164effb3111220b26ffda588910593bfecac44882c9fef6122244164dffb4711 else 0xa548164fbf96ed2a40b26ffda769520592ffedc14a902c9bff6a0a548164effb3052a40b25ffdb329520592ffed894a902c9dffaa99548164effb50caa40b277fda765520593bfec3b2a902c9dff6959548164bffd76c2a40b25ffdba615205937fedd30a902c9bffaa98548164effb72c2a40b277fda9615205937fed3b0a902c9eff61d8548164dffb4ac2a40b277fd9561520592ffedd2ea902c9bffaa97548164bffb70baa40b26ffda85d520593bfecc2ea902c9f7f61d7548164dffd552aa40b26ffda895520593bfecc4aa902c9fefaa98448164ff7b4ec2240b27fbda561120593fde52b08902c9fef5d58448164ff7caac2240b26ffebb68d205937fedc346902c9bff6dda348164dffb0ed1a40b26ffdb568d205937fe5ab46902c9bff615a348164dffaead1a40b26ffe5568d205937fed8b46902c97ffaeda348164dffd54d1a40b26ffda868d205937fed3b46902c9bff695a348164dff94ad1a40b277feaa64d20593bfed4326902c9dff69d9348164effb0ec9a40b277fda564d20593bfe52b26902c9dff6159348164effaeac9a40b277fe5564d20592ffedd2e6902c9bffaa97348164fbfb4eb9a40b27dfd875cd205937fed2ae6902c9fbfaa96348164fdfb50b1a40b27efda758d20593f7ec3ac6902c9fbf6956348164fdf94ab1a40b27efd8558d20593f7ebaac6902c9fbf9556348164dffb74a9a40b26ffeaa54d205937fed3aa6902c9dff6159248164effcaac9240b26ffeaa60920593bfecab04902c9ffbaed5248164ffdd54a9240b27fedb854920593ff6d42a4902c9ffb6dd5248164ffdb4ea9240b27fed8754920593ff6c2aa4902c9ffb6cd5248164ffdb46a9240b27fed7354920593ff6d8aa4902c97ffaed5248164dffd54a9240b25ffdb8549205937fed42a4902c9dff6615248164effb2aa9240b27fbd84549205937fed1aa4902c9dff64d5248164fdfac6a9240b27f7d5354920593ff6c12a4902c9bffaa93248164bffb6a99240b26ffda54c920593ff6a9264902c97ffaeda148164dffd54d0a40b26ffda868520593bfecc342902c9bff69da148164effb2ed0a40b26ffda5685205937fe52b42902c9dff655a148164ff7b08d0a40b26ffda368520593bfec9b42902c9fbf58da148164ffdaa4d0a40b277fda864520593bfec3b22902c9dff6959148164effb0ac8a40b277fd7564520593bff2ab22902c9dff6099148164effaa4c8a40b25ffdba605205937ff55302902c9eff6a18148164dffb4ec0a40b26ffda5605205937fed1b02902c9ffb5498148164bffb74b8a40b26ffeaa5c520592ffedc2e2902c9bff6a17148164effb30b8a40b27dfda75c520593efec3ae2902c9bff6957148164effb2ab8a40b27fbd845c5205937fed1ae2902c9dff64d7148164fdfac6b8a40b27fed525c520593)) else (if i<9 then 0x27efd6368950593bfed4324a82c9dff61d9254164effb0ac92a0b277fda2649505937fed42e4a82c9dff6617254164ff7b08b92a0b277fd935c950593efeb9ae4a82c9fbf58d7254164bffd76a92a0b26ffda854950593bfecc2a4a82c9fef6115254164effb26a92a0b27efd6354950593bfec92a4a82c9bff6e93254164dffd54992a0b26ffda74c9505937ff55444a82c9dff6a62254164dffb51112a0b277fd9888950593bfecac44a82c9fef6122254164effb27112a0b27efd6388950592fff5db42a82c9bff6a1a154164effb30d0aa0b27fbd84685505937fed1b42a82c9dff64da154164fdfac6d0aa0b26ffda268550593bfec9342a82c9dff6a19154164effb0ec8aa0b277fd8564550593bfed1322a82c9dff5c99154164effaa4c8aa0b277fe2264550592fff5dae2a82c9bff6a17154164effb30b8aa0b27dfd875c550593fdec22e2a82c9dff64d7154164fdfac6b8aa0b277fd925c550593efeb92e2a82c9fef6a14154164ff7b0ea0aa0b27fbd8550550593fded1282a82c9fef5c94154164ff7aa4a0aa0b27fbe2250550592fff5da62a82c97ff6e93154164dffb7498aa0b26ffeaa4c5505937fed4262a82c97ff6dd3154164dffb4e98aa0b26ffdba485505937ff55242a82c9dff6a52154164dffb4e90aa0b25ffdb348550593bfec9a42a82c9fbf58d2154164effb2490aa0b27ffabb60150593ffcdbb00a82c9ffe6cd8054164fff346c02a0b27ff97360150593ffcd9300a82c9ffe2c98054164fff344c02a0b27ff97260150593ffca9300a82c9ffe4c98054164fff444c02a0b27ff9b160150593ffcd0b00a82c9ffe5c58054164fff262c02a0b27ff92160150593ffc992e0a82c9ffe4c57054164fff242b82a0b25ffebb549305937fedd2a4982c97ff6dd524c164fbf96ea9260b27fed7254930592ffed88a4982c97ffaed714c164bffb70b8a60b27dfd875c530593efeb92e2982c97ffaed214c164dffb7490a60b25ffdb7485305937fed3a42982c9ffd5c5214c164fff576c0260b27ff9b760130593ffcdab00982c9ffe2d5804c164fff2eac0260b27ffa5560130593ffcd9300982c9ffe2c9804c164fff2e4c0260b27ff95260130593ffc29300982c9ffe889804c164fff362c0260b27ff97160130593ffc90b00982c9bff2d6aa48164dffd76d4240b26ffdb76a1205937fedab50902c9bff2d5a848164dffb62d4240b25ffebb6a1205937ff55350902c9dffaa99848164bffd76d3a40b26ffeaa69d205937fed434e902c9dff661a748164effd54cba40b277fda865d20592fff5db0e902c97ff6e98748164dffd54c3a40b277fda961d205937ff5db4a902c9bff6e1a548164dffb6ed2a40b26ffd87695205937fed9b4a902c9bff6c5a548164bffd76d2a40b26ffeaa695205937fed434a902c9dff661 else (if i<10 then 0xd400017ffaeda054964dffd54d02a4b26ffda868152593efe5bb40a92c9bff69da054964fbf94ed02a4b27f7d75681525937fed1b40a92c9ffb5c9a054964dffb42d02a4b277febb54990593bfedc2a4c82c9dff6dd5264164effb66a9320b277fdb154990593bff2ac44c82c9bff2d6aa60164dff96555300b27fbd41aa980592fff5db4ec02c9bffaa9a760164fef96ad3b00b25ffebb695805937ff5534ac02c9bff69da560164bffb6452b00b25ffdb129580593fdea094ac02c9dff69d9560164bffb74bab00b26ffeaa5d580593efed3aeac02c9bffaaa5560164bffd76d1300b26ffeaa689805937fed3b44c02c9bff695a260164dff94ad1300b277fd9568980592ffeda944c02c9bff694a260164bffb6251300b27fbd4128980593bff55324c02c9dff69d9260164effb4ac9300b277fca564980593bfebab24c02c9dff9559260164effb44c9300b25ffdba5c9805937ff552e4c02c9dff6a57260164effb2ab9300b25ffebb54980592ffedd2a4c02c9bff6e95260164dffd54a9300b277fda954980592ffedbaa4c02c9f7f2dd5260164fef94aa9300b27f7d7554980593ff6d12a4c02c9dff6495260164ffdae4a9300b25ffdba149805937ff550a4c02c97ff6c45260164dffd5511300b277fda988980593bfecac44c02c97ffaeda160164dffd54d0b00b26ffda7685805937fed2b42c02c9bff295a160164dffb46d0b00b26ffda2685805937fe51342c02c9dffaa99160164effb4ec8b00b277fda564580593bfe52b22c02c9dff5d59160164effcaac8b00b277fda264580593bfe51322c02c9dff5c99160164effaa4c8b00b277fc5264580593bff11322c02c9bff6e93160164dffd5498b00b277fda864d70593bfecc344b82c9dff64da25c164effb30a92e0b277fd9354970593bfecc342b82c9dff64da15c164effb50c8ae0b277fd5264570592fff5da62b82c9bff6e9315c164dffd5498ae0b26ffda84c570593efedba62b82c9f7f5d5315c164fdfb66c3ac0b27efdb261d60593f7edc2e6b02c9fbf6d57358164fdfb62b9ac0b27efebb54960593f7edc2a4b02c9fbf6dd5258164fdfb0ea92c0b27efdb354960593f7eb9aa4b02c9fbf6c55258164fdfcab112c0b27efdb55c560593f7ed9ae2b02c9fbf5497158164fdfb6e98ac0b27efdb54c560593f7ebaa62b02c9fbf9553158164fdfb6498ac0b27efd724c560593f7ea9262b02c9fbf1493158164fdfc4498ac0b26ffebb6a1505937fedbb50a82c9bff6c9a854164dff964d42a0b26ffdb16a150592fff5db50a82c97ffaeda354164dffb50d1aa0b277fda864d50593bfec3b26a82c97ffaed7354164fbfb0eb9aa0b27efda858d50593f7ec3ac6a82c97ffaeda254164dffb50d12a0b277fd9868950593fdec2344a82c9bff68da254164effb26d12a0b else 0x55fb2ad715614aab8550f2a6d152f4a928546b2a1b15034a7f853d329d514e04a6c85323296514a24a490521f28e9146a4a3005157289114324a1285053280313f449f684f7327a513c849e084eb72747138d49c484e1326ef136a49ae84d6326911335499704c9b262d130c498104bdf25d512e6497104b47258912b7495384a67252b128b493d849ab24c112534923048e324631227491184863241712074900047cb23cb11e148ed0474b238b11af48d28462f2303116e48ad845372281112a488e8442721e710e9486e04317216b10a2484c041fb20dd105b4827040eb2043100b47fc03f871fa90fc147db83eb31f450f9e47ca03e271f0b0f7847b703d8f1ead0f40479b03caf1e430f11477d83b9f1dbb0ecd475e83aa71d2d0e924741039d31ccf0e544728038f31c6b0e2e470f038371c070df346f18377b1b9d0dc446dd036bf1b570da746d0036571b170d8146bd035d71add0d6746ae835571a9d0d47469e834cb1a510d1e468a034331a0b0cfb4678833a719c50cdb466a03333198b0cbb46588329b193f0c98464883227190b0c7b46388319b18bf0c5546270311b187f0c3846170309b18390c1546058300317ed0bec45f282f6b17a70bcc45e102eeb17670bac45d102e6b171b0b8045bb02daf16c90b5d45a982d3b16890b3a459682c8b16370b11458202bf315f10aee457082b5b15930abf455902a93153b0a934544829fb14e90a6d45300296314a30a4a4521828ef14690a2d45130287b142f0a104503027fb13ef09f044f48277b13a909ca44e1826e3136309a744ce8264b1311097e44ba0259b12b3094f44a40250312730932449582483122d090c4482823f711e708ec44740237711b308d2446402303117308af445582283112d088f4442821eb10e7086f44340218310ad08524425821031073083244158209b103f08184408820270fff07f843f701f830fad07cc43e101edf0f5507a343cc81e470f15078343bc81dbb0ed5076043ab01d3b0e89073a439981c970e370714438801c170df706f7437801baf0dc906dd436b01b2f0d8906bd435b01aaf0d43069a4349819db0cd306504317018830c21060042f6817730b8d05b942cd016030ae7056642af815470a83053a4296814670a0104f342700134b097904af42528126b09210489423f811c708c904574225010ff086b0428420d81037080103f341f180f57079703c141db80eb30745039841c580df706e1035d41a800d0b066b0328418a80c1305d702db416580af7056102a6414e00a470503027141320096704930239411480887041d020440fb8079b03a701cc40e1006df035b01a340cc8062302f1016b40ad8052b0275012d408e80433020500ef40728036b018f00bd4059802a3013d00914043801f300df0065402a80137008100364017800930035)))) else (if i<17 then (if i<14 then (if i<12 then 0xfd957e60beef5f5d2fa457cb8be275eff2f7257b40bd835e9b2f3d57968bc7f5e1f2f05577f0bbc35dc72ed657630bad75d5d2e9e57470ba035cdb2e5d57268b90b5c712e2b570d8b82b5bfb2df056f00b73f5b7f2daf56d28b6775b272d8956be0b5bb5ac92d5a56a68b50b5a6b2d28568f0b44f5a132cff56748b357597f2cac564f8b23b58fd2c7456320b15b58872c3956190b093583b2c0455fa0afa757cb2bd855e28aec7574f2b9d55cc8ae4756f12b6555aa8ad37568d2b3c559a8acb7564d2b1355848abd755c52ad8555f8aac755372a8555378a99354af2a4d55200a89b542d2a0354f80a79753b729d154dd8a6c3534d299354c00a5a752ad2946549b0a48b52312914547f0a3b751c728e2546c0a337517528b054500a2575117288754418a1d750cb285854240a0d35067281a54098a0234fe527e253e789ee34f51279853c709e0f4eff277b53b889db34eb92746539f89ca34e31270b537d89bab4daf26c1535589a534d0f267753368998b4c9926395317898ab4c2925fe52f70978f4bb325cf52e1096df4b5b25a652cf896534b21257a52b08954f4a93253f529d894934a2f25135281893cb49dd24e4526e8936349a324be52540925f4909247452380917f48b7245752238910b485f241f520908ffb47ef23e751eb88f4b478b23be51dd08e9b4727238c51c108dc746bd234e519c08c9f463b2316518788c1345fb22f9517308b7b459722b8515888a83451b227d51350894f448722335117888874435220d50fe887a743b921c650d80868b432b218850bd8859f42b52147509e884bf4245210c507e083bb41c320ce505f082ab4117207e50358815f40892031501388073400d1ffc4ff907f9f3faf1fca4fe187eef3f4b1f924fc407df73ef31f694fae07d533e9b1f374f9207c1f3de31ee74f6e87b273d6d1eac4f5107a773d271e894f3f879eb3ce11e6c4f310795f3ca11e3d4f19878733c0d1df64ef30776f3ba31dc74edb8769b3b331d924ec58760f3ae11d6c4eb40755f3a8f1d434e9e074a33a3d1d1a4e85073f339d31ce24e6a8731f39751cad4e518724b39051c784e340718338a71c434e1c870a3382b1c054df906f7b37911bb84dd286e3b37031b774db986dbb36b71b4b4da086cdb36531b1f4d8a86c1f35ef1ae14d6586ad335491a944d408698734a31a3e4d128684733fd19ee4cea867073351199e4ccb86633330519634ca9864e7324d191c4c83063cb31c518e14c62862af312b188b4c3c06163308b182f4c128606b302718094bff85fd32fe117ec4bee05f232f7d17b74bd385e5b2f1917794bb785d6f2ea317474b9705c5f2e1b16f74b7685b732d9f16c84b5a85a932d3b168d4b41859bf2cb9164c4b1e058af2c4316174b098583b2c0315f14aed8571f2b7515ad4ad48569f2b3515904ac60 else (if i<13 then 0xa478d09467a63381198b8cb1464b631d918ab8c29460a62fe917e38be345ed62f4917878baf45cd62e4917078b6f45b062d49167b8b35459362c6116138afb457062b0115638a9745386295914778a1b4503627b113af89c944d762651130b897744ae624d912378913448262391118788a9444a621d110b3884b441e62059100387ed43e361e990f2f877d43b461d690e7f871f437f61ba90d9386b5435061a190cbf8639430f618410beb85d542e0616990b0b856b42a8614f10a5b852542886140909f384df4268613090943848d423961161087b841d41fe60f71078383a741cc60df906df834f419d60cc90647830f418060bc905bb82c3415160a3904e7825341196080103bf81c540cf6062902c7814340916045101f380e54065602d9014f8093403c601a900ab804140166006100077fef3ff05ff30ff637f9d3fbe5fd88fe837f273f865fbc8fdbb7ecf3f5d5fa68fcf37e653f285f8c0fc377dfb3eea5f700fb4b7d853eb55f540fa777d213e805f3b0f9a37cb13e4b5f208f8db7c533e1c5f090f7fb7be93de75eed0f74b7b853db55ed40f66b7b1b3d805ebc8f5af7ac93d515ea20f4c37a413d0d5e800f3cb79bf3cd25e640f2df794f3c975e450f20b78eb3c685e2d8f13778813c335e130f07b782f3c045dfd0efa777b93bcf5ddf8eed3774f3b975dc68edf376df3b655daa8ed0776633b245d8d0ec3f75ff3aef5d728eb7775a73ac95d5f8eabb753d3a975d468e9f374df3a655d2c0e91f74753a335d130e86374233a045cfa0e7a773b939d55ce70e703736739a65ccc8e62f72f739715cb08e55b728d39365c960e49f724739195c890e41371f538f05c718e357718538af5c528e26b711b38805c398e1a370b7384b5c208e0db705938225c0c0e037700737f95bf60df6f6f9737bb5bd58de776f1b377a5bb50dd7f6eab373f5b990dc876e2337075b7d0dbb36dc536db5b688db276d7936af5b540da8f6d3336925b458da036ced36665b2c8d92f6c8336345b138d8676c1f35ff5afc0d79f6baf35ca5ae00d6d76b5135985ac40d5f76ae735665aab0d5236a8335315a938d47f6a2b35085a7d8d3b769c134d95a690d31f697534b05a560d29f693b34965a478d21f68fb34735a348d16f68a334445a1b8d09b6833340959fe0cfaf67c333d759e68cf0b676b33ab59d08ce67671f338559bd8cdb766c7335959a78cd076675333059930cc6f661d3301597a0cba765b932cc59610caf7656732a9594f8ca5f651b3280593b0c9a364c3325459238c8f364653225590d8c843640731f658f78c79f63bb31d358e30c6ef636331a758cd0c63f630b317b58b88c59b62b9315258a58c503626d312c588f8c43b61f730ee586f0c34f619330b658548c27b61293084583a0c1b360b3304f581f8c0c7604f301a58038bfe75fd32 else 0x11e0ae0be09134e0c4304487b03302324301b1830605ac8685fac45043c437830802921f21a890860520230f60c2482302e0010650600c124118188228308c00fd434b41061f40d409418110a1a7a0050d044e0c258381380d02e12403e9185062868592980203282281a81243490e831040521a4904604a0042441a47d2187a3e8a8010910691f49811c0380c87e11c530d47d150021220d23e938070191430240fcc34cc01401811c0380c83b81307e8a00035448430200a78101802450604c1a8010351210c0802801961a13006009012e7a0040f448430250021223e8e0c023a12074008488fa3c0c08e12180472240c8020321220c0840101909106046008038308482300401c18424128010911f4781261b8183a004034304482300500604e06108010311210c0940080686089046008038308482300401c1841243e9580200e0c2120840109106032008488301b00404c240d8030321206c018190903600c0c8481a0d20d8472241106906c2391209400804860890410860c08e2480c5030350001aa18224118020020c2120940081e8608904a00400430448270881a81802f5080369901d0124350c1120a01960fc020bc1100604900da8a004024044304482a0381fc86a18224168010911f50c094008488fa860460087d8481b0042443e8d8021f61206169c2361a0600fa5611604a102354302b08d07604f06128360c09207411c0247e61f0605a0060461160d4302b0050060004c7061423b8304c11c02c0ac0811c8606200a118301900508d06418128228118408d60c0ac01411c0340941b060683024813005064180d8028320c060604905383600e0c8301d07c181240f806810940c360c0ac01c034084a1060530560c08e2482500303b0891fa1816802815847027830ac11c02c0846a8605c0030d088e0c250030470091fa18158028030248d7830a400c228603a00608e0160723f43035003062180e8038310c06c11c02c0e47e61a860683022487d1b0043ec180d8021f60c06c010fb0603200a0183087d2100505c180c80282e0c064014030610fa460c0302481b81303b029242181583a1f44c0ec1a490860460a24807d1a1843e8983d0c09206c00c0b0fa340cf02030048278102401803e925d912e87971d4b8465bb92dbf96c54b5265a412ceb965b4b20658992c2395fd4af1657392b6795994ab9655612a7b951d4a8165389298f94ad4a49651e128bb94434a146505127db93d349d964e6126fb936949a764ce9263f9305497564b59258f92ad4949649e124d3924949116483923db91d348d96466122e3915d48a1644b9223f910b487864341217790a74843641b120a390434814640211fdb8fcd47d963e491eef8f5d47a163c891e038eed476663ab11d0b8e6b4728638a91c078ddd46db636711aeb8d5b46a6634f91)) else (if i<15 then 0x870203007d2353048840b84d40c09001f5120cc01208203007d105808c08283e818140b98289101f5120a8900600fa360860701507d0b8288189a91a82bc3e940ec20b40de26a46a0fa5c0021220c1909113e000f0008488307800108e0c0ad06098330008207800424418321220fc001c0ad0608238282ac182415605112720a9038e83281c482ac182800a011106500c0a8c84b00089c642444d800321220fc00194e40a9038e8320c054190602c0021220c1e001091060cc1b000502b4182c00a0016005000b00280058014002c0021220c1e001091060f000848830702b4182306c00140ad0608c1c0c0411c1212c0022719091136000c84883f000702a40e2c0021220c1e003030884b00046058002815a0c11096001040e05683044245398003305c0016003001098d8330008207800424418321220dc001c0ad0608848837000702b41824006011109106e000cc170005800c002815a0c16001091060f00180858004244186044212235c00b02240ad065810f0008488307801c182815a0c13060471028c238302b4196043400601b02190911ae0058113001802c08660b8002815a0cb021b0660058110390c1f000411c1c0020c2121902e00109909128148920546424800c024484c0020c2131902e001099091084f001802054940b02a2c0020c2121e001091060f00084883078004244183815a0c16001091061811205683046058002306c00120ab060905581c482ac18241560c1306303898310c0482ac18241560c112720a9028e832814482a40a2a0ca05120030088a710548146c004188603a0c430a051a0ab0609055831c08682ac182212227c0019091136000c84883f000647d02a40e321223ec001909106e000c8488d7001c08840b800426424423e8152051d0640a8a832054541902a2304c00150640a8b00084883078004244183212222c001c0ad0608c1300044258004443815a0c103e8484888b00060fa1815a0c11091116000cc13000502b4182c0021220c1e0007000848830642449d8003815a0c16001091060c8481cf000702b418207d0c0ad06088481f444240e7800307d0c0ad060884b0001cc66098002815a0c1183e000823830014022800a0114005008a00280450004254023800a011400500b810c84a002804858841940302a321220c8301e001061240e8309220c0780042441860a4a0c83016001091060e8320c046080602a0c830160020a9240f00084883078001c0021220c190910ce000e05683058004244183212219c001c0ad060b000848830c0884244338003815a0c103e870008488306424433800307d0c0ad06081f4302b4182302c001182e00098310c0920682ac18241560c120ab0609055831c086c0a42c82a341560c130630288c1c0500330300374342141200c1200521a8908604302014e else (if i<16 then 0x600e8600ca08a0706d0b82d0628380604c05c168314082601382e0ac01813006303d4030b81b0005800320ec1008617049036086042070b82883c1a89a8553088517061c0d00b98440542e90c0dc14055c1811c4414135e0c08e20470400bc86011c1544082e0c08e181c0583240d8450c0806805cc1002a174860690360c430183a7062180ec090100900980f42e0d206c1003c170460403d15002092060e8010480b87400824818a044a0041202e1e060480180503074008248183a0041202e1a0984589822c201bc1f42e0a02407ca0f02b0fa13816e750f01a03e87d830280901f41843e85b9580204a0f8607ca1003408b0fb060660081283e1a81c1843e8d8020480b8620802826b0fa411483507f01501687d06d382981a82bc3e9280543c2720c02d0b402a0e03408b0fb06065060ad09183024090488a80412c1161f60c0a4014030243015a0b8301c0901d884504140581b78302c0c2080610fa307c60cd070450be0302483b00058002c10c0e0fa170460860707d0b8202f30783ea1810244205406a2060a70fa502e05303f43007d2483300481890c01f440bcc1ec140fa490524843007d184103e8488c1b78310c06c10c0e0fa17046000b0006c098200fc2e02cca14211121a0604028135e0c08e230409a82f018047141bc463830238811c160c90d0301b0402182f045818141b54178304d40c0bc08060116306f135e0c08e248103e81805b902441584d41f48122060205609107d1b000441b8320c0620a26bc18060408b0b00482881d04d78300c0820626bc19060408b083e818081f60c0402402826b0fa400c10583001209de0c0b03b004064180c1fb80541e81406810c2fa1210c0102f02c301211d00c09183047d300908282770609ac18181d02fa1201f48c01401019060405e11402a01a15007d87d3b0470885205c9009183c1f41783110c0c0bc89046b09e034122860760081280c189286283ea181380583e43c2f8068179120f20e24617c8900fa5508a0701a848830135330040bc0a8e80b8004600901cc2e21220c1141140e89e0fa170501211410f07ee0c848300a04e09aa3e900480350910691f42dcc02422846a0582040541388fa8b08b0201a42407d47d430380901418384e048a3e9801509004d0680491f42dce42660a11c8fa401211410f04ee0c83035002062240e80105d05474008248183c0c0d002092060e80105d0587818120060140c44825002062180e80105d0587400c00818860400507db0741229c47d0b73d002092060e80105d0547419090178329c70d03e8480b3288bb843813828598184241c19045dc341200c2120d0fae1b090370229c03287d8482909b8680ac240599445dc21c082cc0c2120c22ee0fc0053909012266000c82b0401f818059940b89101f40c0805012226a0fa402e60 else 0xe8010490787400c00240841a0b089d03f05c350020920f0d821819816c14a701f42e8e07ca100340770fb06091c703e01a09187d830280901f24743ec181580204a0786c0102403c360081281e1d0082581d8474181680541a1f42460c0b4030fa11d0604200a0111005008880280440f9a0406017c0fa49066000b000642181501c3102ccb20ec0cc0a0a0166508e0f0600a882618140c09202382fcc0e3c1811c3038090400ac8412414e140c0091828920808c26a04808606049066009071483c8401803e9241e42182c0c0818a26bc1811c404323f09d030230601804e8d8208fc10e43c0c0a23d20fc1826a060560c90f030182848783989a81815802408520406111c0fa410221408e13507d2b05c878180c03004b8304d60c0a01bc0203b81282c186640060c06444888b2d8102402201821822419000092c082c10c1120c0c811604806007dc1886070050120130be0ba2a0600981c124045e181804d001092c360550c02cce207c1811c8604a0041240c1e0607030280f60e8240320fa1866400b0f41607d0be2b004124180d8020920c06048061c1906046008248301b004124180d0580c01f60c0812e82cc1613806051076111230b403ee0c06d3b8108205a08e84e7060369d0d40b04882d02738301b4e07c13bc188600da560410f09c47d06d2806504503d0203685c1980045025c0a843c06a8470240fb8315c02c0cc08144170560c60420806f20c0b83027508c0280b04e85d018418200482dc0530278304d4c0f214215611009086066080240a403f0b22d0420080e82b02441a8184182007406805a0d49220c0d60420f4220340c807dc1826a8a0041240c1d003020a801049030740082489c311483506d02c02a01608ec0909ce0c5301700b0205f85c1584640881c2102710fc1210c11c23c15c1605411dc18660081280c1b0458130201210390605c1d8102b404d0c00542e8c026c1811c0da4905050408e81604000b02f04e8184182447443c06a0342a80589220c1011141089b03209023b06076008120881d0300d40c81f04705f980484520d40b00aa8441081900fb831560402c0c813826bc18601260c41a90d08c4240ba3f002092060e8010490307400c082a0041240c1d002092270e80104903078181e00080905a187f0603695022414a701cd0682e8c82481811c3412038128250884e818418168302703141220c0a4014030183502a0c09c0c50488303100500c060c4500f82740c38320c0cc01025018360081280c183f50440280b24e85d018418228210800682842201220c0ec01024110307e22607904283f0488303b0040944e0c0900fb8304760c0a20dc1826b06046000131009a8782683ed064181941c0f01228320c0b026116203c042048a0c8302b005004098c0484501440fb8320c0c22802602bc190))) else (if i<20 then (if i<18 then 0xa0b0a002d07e13902a91c7a08e0008808c50f83033004094108d800202941140808623106091c750750680f0162488301353d0228182809ac181580204a0847c1811c26a3a0041240c1d002092062839280104908474008248423a00503140c6060a80104908461161014a0850783004309c0b7381f681401a8380d01dc3ec182200d43e1f60c08c0102504236008128211b000408b41d82810c22c1f4920e0a012286026a40910982881f0641809a97000a2c0ca120274ac001c0c08e4481a060470b0243018826221241380c83084808e340038338283ec1842404e9e00e82804e121238b006e0ae0813909091c6c0c04f03983028b2b0005c1ec17025120270a11c16000809a1858684722414238242502681961a8608906403c0901328b4482982e06145a181014cc1492c2f01f7030cc01604201fe0807e04808e2e1ef0560662404714238282c16011c1844e0808e104705030092c082c10c1120c8060496041608608906e0808e130000fc0a8c848093025120274a80102689042486013a6e0803801343028b2a01809b0510944722402e9f000848c351202ccb4008198003413c0915006000a801033000740180026000a01d8302404722402e99803000481809e16086161a890640330604888e44805d36001868a00e0c004e121238a07d006138e1b048166680387d8308240b72c018123810584184241804e00dc360c084a0902d0f006e1e1390481685c0004f03309184828470504f024c361208c01800284887d83009122123810584184241504e121c3484a0c02ccce1e139090168400cc0030583009d8480b03e0018438118281c43ec241d80300205a0c08c0180102d0604600c008168302081c1204b85993031c15c082720902ccc138e1b0481664308c0c70f0158240b3360642405e0dc342720902cc8060e1a13816640977020307050b384809c3e0638104e41205995c3504e12025c80c9818e1b090409770224bc0c0b38483209b8680ac120599425f03092c2cdc36120cc0022812e05813142228181207dc18a60505c29c0ba2306302d8290414e05d1a8350ec1cc2720c1238cc2247e02608711c860601a09d06403e135e0c35002092060e801049078601940d40a03417492217e720808e0aa1d002092060e801048078740224a87706011c507ba0c08e83025008470a8040e0541141a8760e613902a91c7a0823f01304348e830330040940f0d8020480786c0010bea0c07c83048e2809d06418247118028004c01400260c608b0260620529c0ba3c2822581d839c182471804846280a8304349202602d60c120240874100e691c231060760081281e1b0040900f0ec35068100120239120c80c03541721e07e17e6e0041240c1d002092060e80034008248183a0041241e1d002092060f03034018128063c0c0900300a060 else (if i<19 then 0xd830288da0920640ad0614c0b0300c068fa0540fa3306c0c8304482082d02d062062241493905e4150542c0a20a8194180b444179054160b02482b00a06224019144168310310c02c0a53882f20a82c160590560040c43007d285a01e8368d831120520ac1882c390401560c1c8280ab06048924150582d0054920802ac18390401560c1c82306182a0b124150f80c07208c18890060411860c09103024823060180e4118311206c180ae122390460c030180a006d064879246869181c4940504501f7830510dc23c15c17c12068269c18703501606409ce0c135308110a09a706100300638042fc2e0a019405c0217e1705a0c0bf0b818090060a270609a96c088082d42fc8c18068d38cfbc182686e010bf0b8189a7060840a8010490308031400200cd0202c02422421583d0b8400605501a09a85c1541c2602e06c001b026080430b82504b0458112702185c1a832c100aaa73830238c424418c163e0021220c1a82840d18304419a0803046113a0604900b88e1144b11e49123005d309281a83ef0609a97000848580040e2c0021220c1b01486880164345419604201400f41a42443d0ba37002092028c04801ec362710f42ccc02801a84961a8348fa660081280d181218284a80d05401a85c03ea38040fc2fc2e096116040348340fa8488fa703dc0824d04409f04808e3e0470561e81a62404f8471d8020480d4781006817011c481203430f1e0402204f847100f5092c3404d0680490f42cd004812c89011c15a530605001306343028b300c80900b22423e85d1b80104901c740082481e3a0043d4071d84002d8780d03ea1e82e1d8020f6014682406861a370210613503ee0c09730167810a001f70604b9841c2a80a81080fb83025ce01820e281c1889012e600ca058300970ba2d82d0810686005d1782ac3782c193830274d4008248183a000b06500b02d8290386005d1d8140540903002e8bc1811c1343070604704d0f830238268603506141b09092217e66008158241807b0600c06205d1780104903074008248183a000e0604048c3f83025c960a8260681801745a00098415424230650090286005d16c3780583d1210c0170c0e0102a1350a813f8480308304300409098020482607c0280e02489007f61a8607012107144e0c0972d810240180222242181804846cc141ec0fb830238e02400a0261801745213305064e0c09d2f002092060e80104903074001c0c0d0020aa120f030202415461bc1812e5407b0604888e04041605c3d002090941e09011922c1f61f60c0ec0107d02b0070485600815098824230041f40ac01c12140480304522702c0a024029423813c1826a6014e0ae0b09d064e0c1353d03a8280b41f84e4182471c41d41a8140589220c04d4e18a231c1811c4021e0003f09d4302d002092060e8010490846 else 0xa81705b9084889a0f82b4907c13c150323e83e07009e211f01700ac0a900d02dc0aa1f4805013c418306d40c048a0c0b42f0612408451032832054120a818a0541902a0905048a0c81503e2281d0640a8c8300a0278622813c170244411406d81609e20c289120640a85c08a161142e027866080adc183114816c0c091220640a85c09109a961142e02dc4d4908a0fa21141228150b840c2c2285c04f0c1142e0502b41826a340c0295020a1203684f05083f901fc2dc28447480ff02a14281840a109e120983e8940c14b83078120da0e60ae450305387d182b0415834030248a2370205615008568943c2e854020e016838095030571a81848c0a8c1b42c0278054805013c4183e0c06740c076203684f83e05a101f103092027e0c0a17013c0da230407c40c09f114830283690640b04f101f103140827e0c0a609c180603503a0c83019826060180c0582d09206a0bc1817c060460c10506d1c8201521e8d8309205206c1842c390341560c1a1e8150488d831c0a82c858842c0da82a390341560c1c81a0ab060c0ee40d81d8308c18860202aa0b23e1c81a0a8458e40d05583062094180540da4c0c20c248048220640ac3e80b1085817805864180820550fa440c81550287d016290b00b02f0c1f4207a0550fa387d02a03e190b02f00b0d0c01f4520687a4903a0b43d02a091220a83ec0b0c1b70310c00ec807a0da2b0201560c3022306706014187924080558306c18050116390201560c135200ab060488e409830054720402ac1826a490260c118030201e836880a0a70520a538050390501560c1c8280ab060459181e0c0054720a02ac18390501560c1c82b03b060459183086a0c06c180be116390529c0281c82b0600a8c055830460720a02ac183015830419183b14e098338301d86c19c180ec360ce0c0761891858052c18104520c01f4295120a22824702b4188188906306c0c830448201403688c82f03e978300a18306c19c18050311441560c81280c1273306706381014101bc1790547c18050c18311412341580c0b8284d90960603ec24140a91f4422882481902b4181366302c0c048184da0920640ad06168302c10310c088fa0540fa311407d0a5448208a086c0ad062062241883505c2c1054822821a81902a14c520d41711d0b04162c86b00a06224104528302c10310c0a41a82e16082c4305c0c4301c86b00206218104d484b0301f48a040548fa360205347d057208a03e8528c4d031c502b41960481826a8606235417b020b04162c1930020658121816c091f40a81f4960482a1600e60ae5307c0c44819816060b0301f484d0c0902c818160168421305e4160b02109b002062180581446c84b0301f60c0a0548fa2212c0c83007d448288dc0ad06206224144501f42960c0822823682481902b4186212c0c30207)) else (if i<21 then 0xe0504906052240a2015830230605f4180c1920c0270602ac1882d060401560c416830220a8140368d0578301b425c26c0a0cc19c18050360ce0c7020282706112037a0a900a11f44425c1812e0501365108a0c02806d201728281400a904840a022043482054180500da4b0260c02824e2014044080b940c0a0060805c448212711421220c824c0c31067061838141049d049032056830450c44e0db60405007e5415e0c06d11e135028330670638101411833831c080a0822882ac1902501824e6e0c70202860c238101423e8c84b8304780a04d4a20f4196040500da561160cb0202824e2927017581014100a38304c1941805061e40ad24e06d2122306112037c0a9105484c0b805488605380da42640a121207d06d2281a82814017108900b84050110221222711d81215008833815060170c1b48488330302b4a419c18604050440ce0c50202c2036a0640ad06056940b100c2b4644c0dac08050411440c815a0c0ad28126060470e8450328300b0540ac1805815a130420ce0c028188a087a0940a85414450540848831093030c22821e81902a150521220f44e0c422126060470e8301c01bc620e81941920a0de520724e44e9050702a82d0600a8c8328304418e054183224a0c0151a87d00c060d41c832806031414a0da236051c18060502829c10143067060c45105430c49e030ae04050c19c18441506fe0c1a0ab06056c061045043d0542a2030a20ec180df018402847d170608d8140181041a8300a01b48050538260ca0c02808b2306506014045d05141be831054605ca0a05002a422429c10140440884822089c30c853805ce04050481521302e015210911304e0569084943c2202a08538a0f138a0a0de5e0c02820c188a20940a85c09194c1a0c3830622903581920a116540c8150b81231352a81a8282f8c17c20be1a008130511b8102f8884e8020c1054809f401026350fa008131a83d00409a82938314080ad03080da0e882481902b418641240c815a0c07411d305681504c0d0e01b407862114180540da401504902e415220ab0608289a918304141b4720ec1805411c490360ce0c02a3072c83a0aa1e8cc3c0a8220682ac1823a390341560c1b063812180d0540c1830682a11626a370202a47d1e0600a81509a9041e832c080a81b4b812419818082054540cb0210783502a281a58100a81720a9640e4350540b88813206c028196045430107a0cb0202a40c301a58100a81720a9640c22d0c078188601163c0990360cc0cb0202a0383883506015036930248330300a8104a819418a05060034550381508b181408c82f03e904128300a01b48c19418490321605e105bc3e90b0c8581784c180510fa122481521605e415210b02f081f420510fa47c321605e110602f8a0568300c8647c05c448321222781283e451291f4 else (if i<22 then 0x6b04216e32120b00b7121220670603384583b144850328302c20c0a819418a0e4901602290607503e0c830188a281d06418102702819818209c0e0007000c34580060a60e340cc007021847070002745800e04c143c00242160038108c1503300078001c0030d16000228a0582d0502c168230fc008168302058206600059c18160582d0461b80102d06040b0c007028163058303209c0b05805a10c160582c02d0823c12e24c050130560ce0c0281b067063810141105417026060508fa2097028098126270603a014018100a0a704448130221281e0c3227209188a10910640d60618c1a06847423894001438a00110970603681409a958458328300a0274a49c03d604050460120c08e1b0658101414e30514a7007ac080a08c016042224098110921c40940f11389a98056054260741803c91c311410d41240c815a0c3109106a0920f48695804238442441a83c14e430541a08e1c86b000b0300540b04d4820a819419604058521203401e41588e2a04b008470c8480d0079056238b812c0111c341588e01e1f062810152061047846d049032056830c22823682481902b418640ca05a0c05c208f01409032816830170840a49c83d0700b8511e05c02e1c8281c300a0610814a7107a0e016cb20b070c00418402807f07307d23065061240c8581cc40fa102887d23e190b039881f42e0447c0510fa4216073111204c0884889d0e204a078a02a13102a323e01e7020282109106c0f053100d00b21f5238840a47c87103c0b4512211420cc0c0ba288a20640a85d091148490782ea114860902c23a11c407d845110920f05d422901f4114442444483c26a170530481608e1d00840e28045012a074023a017021286d008a0268042386a0a070419402411e21220cc0c0b02f060141060f83019d0301d8823c819418161060540ca0c2480b0830288f10910640b60628118288ea04510328302c20c0a819c18a04052411e11941240c815a0c310c88f0140c450465049032056830c23c42441902d818521221941241e8382c1c03e8a82c4641cc0a8820618a12e360ce0c0c550f2025b060180c0c0a704c1823a060350790860c0c5200a84b88054938238720e02ac18301560c08e1c83b060180e41d8158306090c1818a360c248100ab0608e8e41d8309200c0920e02ac18390201560c3021352c8130608e81812408055830c084d4a26a4180618184e0c50202a40c208a106018606138330c303066058182c0c0b3030189110601840b606144500c083205b030a60902d8183304816c0c188c90601840b606178300a5030622841806102d8185114119412815a0c40c318100b6060c40e0c019025c8c18e05048835060560c82483041a211205100ac18100542f20c0704849d060060460ce0c82441a830280a85f4180c0558320920c0802ac18 else 0x10970609a83681508f1840c8568300a8510b412c19418e0405413a670202ae0c1b06506015047100a831c405941826a11c460ca0c702b0223028155060470dc0ac080a89f4860a60e054068443d034702424221e81538101a91c082ed0686e0482c8fa330543d83d034220a81404b8d0900a105425c882b2072101664212e0c12107b127064308150601404b92c081ef830190823c0f613024c0c85107a0c028097230650603d83218794c148488d425c8425c180fa89044150158240b3202340a987851108338301ec190822815415021e4e0c0c530f0a220838378550c84b8301b41ec26c190c20b41805012e460ca0c07b30d0642982b06506014128301bd055090808c82a144330721220c097220ac0a84c0c84b8308f91208c0242482a890404650302802420233810400c0a0260502a08c02a048450f0a80aa118228403805500a928301184419c1860e0f60c8511410d41240c815a0c3106d868140c8344750542a9090a26a12e424154420ce0c30207b0642a067062810151025d032832c082a84d4c12e46a150311414420c0aa270605509a0f832c08581823011c3307e0c0c50a2230658109a84c01514c0b03047460f61300c8309782405c06f815288ce0610905991032816830170812e05029054150aa424270608b83d832024144128302681908c194180f6421090541523ea0c8482062d0620aa12051168310c08fa120847d4180f70904415605a0c8482281c0aa84023059948f9c0a0541182ccb02a13016638150150460240b32907a87c0ac120551541d42205540c2a82ccc47d02a08c16642128158240462109286c1f40a844412188d5c0941e0560902a8ca0a42702a424130166623e50583e81502e824370642420603b1025d0328321202c20c0c410a1e0285384014088100a044088490840d6104842484206b082424e0140b7194e00a05b8c8f808543c1548)))))
def markLevel11 : Packing := (1545,4,8,0,0,17,0,markData11)
def markData10 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x87fdc82e9974816487fccbaa9974816487fccb6a197481648dfdc7aeda548164c5fdb92dda5481648dfccb9dda54816487fdc82e9954816487fccbaa9954816487fccb6a19548164a77ccb6a65548164e57da99de554816487fccb6a65548164a77cca6565548164a7ecca6555248164e76da995622481648dfdc72e93148164fec5634c52148164fd69755497048164fde1714857048164ff49535493048164ffc131485304816487fccb69d9244164e5eda99de2244164e76da99562244164fc7a779556044164bef1c11496044164fcea778896044164fe6a558896044164feb1725056044164feb1525056044164feb0525056044164feb2225056044164ff61525452044164dfb2bb5052044164fdb2775052044164ff32555052044164ffa1525052044164ffa2225052044164f1fa889dd9580164b778cb6625580164f579989de5580164f97a889de5580164f37a886565580164fd3a779558480164d778cb9559380164f57a779559380164dcfabb9dd6380164de7abb9556380164fc7a779556380164fcda7760d6380164fe5a5560d6380164f1fa889dd9280164d778cb9559280164f37a889559280164f57a77955928016497f8cb955928016497f8cb65d828016497f8cb6558280164fad98358d82801649df9c7aed5280164d5f9b92dd52801649df8cb9dd5280164ded9b68cc5280164b7e8cb6622280164f3ea8865e2280164f5e9989de2280164f9ea889de2280164b7e8cb6562280164f3ea886562280164f5ea776562280164f769989562280164fb6a889562280164fd6a779562280164f769959562280164fdaa776122280164ff2a556122280164b7e8cb64e2280164f5ea7764e2280164f76a5564e2280164beeacc58e2280164fcea7758e2280164fe6a5558e2280164fec98358e2280164fdca778ce2280164ff4a558ce228016497f8cb6562280164f3ea8864a2280164f76a5564a2280164f1fa889dd9180164f37a889559180164f57a779559180164f3ea888899180164f5ea778899180164f76a558899180164a7f8ca6e55180164f9ba889dd4180164fb3a889554180164fd3a779554180164fbaa888894180164fdaa778894180164ff2a558894180164dedabb58d3180164fcda7758d3180164fe5a5558d3180164fec9638893180164fed1634c52180164f5f27764e1180164fcf27758e1180164fbd2888ce1180164fdd2778ce1180164f5f27764a1180164f7e19888a1180164fbe28888a1180164f7e19788a1180164fde27788a1180164f7e19588a1180164ff625588a1180164ffa18488a1180164f7e19388a1180164fee16388a1180164ffc23388a1180164f7e19288a1180164dababb6118058164f8ba776118058164fa3a556118058164faa9848898058164fcb2775056044164fea2225056044164 else 0xffb1755052044164ffb2555052044164ffb1825052044164ffb1525052044164a5fdc5aaa7764964a5fdc7aa9a954964a5fecc6a4a754964c5fdc92ea7754964c5fcba6a67754964977dc5aed9254964a5fdc7aa9925496497edc12e9958896497edc02e99588964d5eebb9dd9588964bd6dc72ea558896497edc2aed958896487fdc12e9958896487fdc02e995889648dfdc72ea5588964d76ccb955928896497eccb95592889649dedc7aed5288964a7ecca6555288964d76db99555288964a77dc82ea5564164a77dc32ea5564164a77dc22ea5564164e57eaa9de556416495fdc7aed5264164c5fdba2dd526416495fccb9dd5264164a7edc82ea2264164a7edc52ea2264164a7edc32ea2264164e5eeaa9de2264164e76cca9562264164e76cba9562264164e76eaa9562264164f56e779562264164c77da92d5a760164c5fda96dca560164c7eda96c8a560164c7f5a96c4a56016487fdc22e9956016487fccbaa99560164c5fcba9dd9560164a77ccb6a65560164e57da99de556016487fccb6a6556016487fccbaa99260164c5fcba9dd9260164adedc72ea2260164a7eccb6a62260164e5eda99de2260164a7ecca6562260164e76da995622601648dfdc72ea226016487fccb6a62260164a7ecca64a22601648dfdc72e931601648f7dc5aeda85c16487fccb6a1955c1648f7ccb6a2555c16487fccb6a1925c164ec7eaa9de5558164fc3e779558458164d67ccb9559358164f47e7795593581649cfdc7aed52581649cfccb9dd5258164eceeaa9de2258164f4ee776562258164ee6eaa9562258164fc6e779562258164f66d959562258164fcae776122258164fe2e556122258164f4ee7764e2258164f66e5564e2258164f47e779559158164f4ee778899158164f66e558899158164fcae778894158164fe2e558894158164be78c56dd8058164dcfabb9dd8058164bcf9c72d58058164bed9c32d58058164bee9c22d58058164bef1c12d58058164de7abb9558058164fc7a779558058164fababb6118058164fab9b76118058164fab9b56118058164fab8b56118058164fab9756118058164faba556118058164fab9846c98058164fab9842c98058164fab9845c98058164fab9845498058164baf9c81498058164fab9841498058164deeabb8898058164fcea778898058164fe6a558898058164fab984889805816487fccbaa99254164a7eccb6a62254164e5eda99de2254164e76da9956225416487fccb6a62254164bf71c12d58054164f379956158054164dbbabb6118054164ebbaaa6118054164f9ba776118054164fb38b56118054164fb3a556118054164fba9848898054164a7eccb6a6224c164e5eda99de224c164ecee7769a224c164e76da9956224c164ee6da6956224c16487fccb6a6224c164fbd1814c5804c164) else (if i<3 then 0xe7f9a56457048164f5f9756457048164f7e9526457048164f5f9985c57048164fdb9845c57048164f5f9935c57048164fcf9635c57048164ef79a55457048164ff69525457048164efb9a55057048164fdb9755057048164ffa9525057048164fed9634c57048164f7e9984857048164bfe9c54857048164f7e9954857048164fde9754857048164ffa9844857048164f7e9934857048164fde9734857048164fee9634857048164ffe1314857048164bef9c62953048164bfd9c32953048164efe9a85493048164fde8c75493048164ff69755493048164ff59535493048164ebf9a86053048164aff8ca5453048164ff69525453048164efd9a84c53048164bfd9c54c53048164ffc9524c53048164ffd1814c53048164dfe9b74853048164bfe9c54853048164ffc9534853048164ffe1714853048164ffd13148530481648ffdc3aeda744164afecc26dda344164a7fecc69d9344164c7fccb69d93441648ffecc6e98344164aefecc69d63441648ffdc8aeda2441648ffdc5aeda2441648ffdc3aeda244164c7febb661a244164c7febb65da244164cfbebb611a244164c7febb64da244164cefebb58da244164a7fecc69592441648ffecc6e98244164c7fdba6617244164cfbdba6117244164c7fdba64d7244164cefdba58d72441649dfdc7aed52441648ffecc6e95244164cdfcc76e95244164c7febb6a55244164c7fda96dd5244164cdfdba2dd5244164d5fdb92dd5244164e5fda92dd5244164c7fdba64d5244164cefdba58d5244164e7eda95c952441648ffecc6e852441648ffdcb68c5244164cfddb368c5244164c7fdba64c5244164cefdba58c5244164cff9a86c05244164d7f9986c05244164dfb9846c05244164cff9a36c05244164d7f9936c05244164def9636c052441648ffecc6e932441648ffdcb6a132441648ffdcb69532441648ffccb6a222441648ffccb696224416497fccb6562244164befacc5cd6044164befacc54d6044164bef9c754d6044164fed97354d6044164fcf9735c96044164befacc5496044164bef9c75496044164fcf8c75496044164fe79755496044164fe79535496044164fee9725496044164bef9c31496044164befacc4c96044164bef9c74c96044164bef9c54c96044164fed9734c96044164e7f99869d2044164bff1c12d52044164efb9a76112044164e7f9a764d2044164eef9a758d2044164f7e9985492044164fde8c75492044164f7e9955492044164ff69755492044164ffa9845492044164efe9a35492044164f7e9935492044164fee9635492044164ff69535492044164f7f1935452044164fef1635452044164ffe1c25452044164f7f1925452044164ffe1525452044164ffb1b85052044164ffb1b75052044164ffb1875052044164ffb1b55052044164ffb1855052044164 else (if i<4 then 0xafbcca95584481648ffdc8aeda3481648ffdc5aeda3481648ffdc1aeda348164aefdc62d5a3481648ffccb955a348164aefdc6295a348164a7fdc8aa99348164a7fdc7aa99348164a7fdc5aa99348164a7fdc1aa99348164a7fecc69d9348164a7fecc6959348164c7fccb6959348164e5fcc76959348164a7fdca5d59348164a7fcca9559348164aefdc8aa96348164aefdc7aa96348164aefdc5aa96348164aefdc1aa96348164aefecc69d6348164aefecc6956348164ecfcc76956348164aefdca5d56348164aefcca95563481648ffecc6e95348164cdfcc76e953481648ffdc12e9534816497fccb9559248164bdedc7aed5248164cfeccb6a15248164ef6cc56a15248164ddedb82dd5248164ededa82dd5248164f5ed982dd5248164e7ed9869d5248164ef6da85d55248164f76d985d55248164fd6d875d55248164fdacb76115248164efada76115248164ff2d756115248164f5ecb764d5248164e7eda764d5248164f76d7564d5248164fcecb758d5248164eeeda758d5248164fe6d7558d5248164fd6cb754d5248164ef6da754d5248164ddecb76c552481649dfdc7aed52481648ffdcb6a15248164a7fecc6a19148164a7fdca61d9148164a7fecc6959148164e5fcc76959148164a7fdca6159148164a7fdca5d59148164e7eda85499148164f5ecc75499148164e7eda75499148164f76d755499148164aff5c1aa98148164e5fd9869d7148164edbda76117148164e5fda764d7148164ecfda758d71481648ffdc32e95148164c7fcba64d5148164cefcba58d5148164fd6cc75495148164ef6da75495148164f76d935495148164fe6d635495148164afbecc6a14148164afbecc69d4148164afbdca61d4148164afbecc6954148164edbcc76954148164afbdca6154148164afbdca5d54148164efada85494148164fdacc75494148164efada75494148164ff2d7554941481648ffdc82e931481648ffdc52e93148164eedeaa58d3148164eedda758d3148164eedda558d3148164cfecba5493148164df6db55493148164fecd635493148164cff4ba6053148164efd5a36053148164d7ed986d52148164ddecc76d52148164dfadb56112148164d7edb564d2148164deedb558d2148164f7e5985c52148164fde5a75c52148164fde5875c52148164f7e5955c52148164ffa5845c52148164f7e5935c52148164fee5635c52148164bfe5c74c52148164ffc5a34c52148164ffe1c04c52148164efd5a34c52148164fed5634c52148164ffc5324c52148164e7f9986957048164f5f9985d57048164efb9a56117048164fdb9756117048164e7f9a564d7048164f5f97564d7048164eef9a558d7048164fcf97558d7048164f7e9985497048164ffa9845497048164f7e9935497048164fee9635497048164ff69535497048164 else 0xdcfdb75c931581649efdcb1493158164beddc31493158164bef5c11493158164bef9c32d58058164bef9c22d58058164befacc5cd8058164fcf9b75cd8058164bef9c52c98058164bef9c32c98058164fcf9735c98058164befacc5498058164bef9c75498058164fcf8c75498058164fe78b55498058164fe79755498058164fee9725498058164bef9c314980581648ffdc2aeda8541648ffdc1aeda8541649dfdc7aeda254164a7fecc6a192541649dfdc7aed525416497fccb6a622541648ffccb6a2225416497fccb6562254164a7fecc6a19154164a7fdca61d9154164afbecc6a14154164afbdca61d4154164eedeaa58d3154164eedda758d3154164fbb9842c98054164fbb9846898054164f3f9856498054164fbb9845c98054164fbb9845498054164fbb9848898054164fbb9846858054164f3f9856458054164fbb9845c58054164fbb9855058054164fbb9844858054164d7f9b864d7054164def9b858d7054164d7f9b86457054164f5f9985c57054164fdb9845c57054164f5f9935c57054164fcf9635c57054164dfb9b85057054164fed9634c570541648ffdc1aeda74c1649dfdc7aed524c164c7febb6a5524c164c7fda96dd524c164cdfdba2dd524c164e5fda92dd524c164cefebb699524c164cefdb7699524c164ecfcb7699524c164e7eda95c9524c164eeeda65c9524c1648ffecc6e8524c164bf78c56dd804c164bdf9c72d5804c164bfd9c32d5804c164bfe9c22d5804c164bff1c12d5804c1649ff9cb149804c164aff9ca149804c164bbf9c8149804c164bfd9c3149804c1649ff8cb889804c164ffd131485804c164c7fdc9aeda8481648ffdc5aeda8481648ffdc1aeda848164af7cc56dda848164a7fdc7aa99848164a7fdc5aa99848164a7fdc1aa998481648ffdc8aeda7481648ffdc3aeda7481648ffdc1aeda748164c7febb661a748164a7fdc8aa99748164a7fdc1aa99748164a7fecc6a19748164c7fccb6a1974816497fccb6a19748164c7fdc9aeda5481648ffdc8aeda548164cdfdc7aeda5481648ffdc3aeda5481648ffdc1aeda548164adfdc7aeda548164a7fccb661a548164c7febb661a548164cdfebb2dda548164cdfdb82dda548164e5fd982dda548164cdfcb76cda548164cdfcb76c5a5481649dfdc7aeda548164a7fdc8aa99548164a7fdc1aa99548164a7fecc6a19548164c7fccb6a1954816497fccb6a195481648ffecc6e98548164cdfcc76e98548164a7fcca6e58548164a7fcca6558548164c7fdba66175481648ffdc82ea55481648ffdc32ea55481648ffdc12ea55481648ffccbaaa55481648ffccb6a25548164c7fcba6625548164afbdc7aa98448164afbdc5aa98448164afbdc1aa98448164afbecc69d8448164afbecc6958448164edbcc76958448164afbdca5d58448164))) else (if i<7 then (if i<6 then 0xd5febb2dd5264164e5feaa2dd5264164d5fdb82dd5264164e77eaa5d55264164d5fcb76cd5264164e7eeaa5c95264164d5fcb76c5526416497fccb9562264164cfbd416deaa60164cfbd416d6aa60164cfbd416caaa60164af7dc52caaa601649f7dc5aeda760164cf7eaa2d5a760164d7edc96c8a560164c7fda96c8a560164d7f5c96c4a560164dbf5c86c4a560164dfb5c46c4a560164ddbdb7504a560164df9db3504a560164dfadb2504a560164dfb5b1504a56016497fccb69d95601648ffdc22ea55601648ffdc12ea5560164cfbd412ea55601648ffccbaaa5560164af7cc569da260164adfdc7295a260164aff5c1295a26016497fccb655a260164c7fda96d4a260164a7fdc5aa9926016497fccb69d9260164b77cc569d9260164b5fdc72959260164b7edc22959260164b7f5c12959260164a7fcca9559260164a7fcca65572601649dfdc7aed52601648ffdc12e95260164cfbd412e95260164af7dc5aa95260164c7febb6a55260164c7fda96dd5260164cdfdba2dd5260164e5fda92dd5260164e77da92955260164bd7dc72955260164bf75c12955260164e77da95d55260164ef6ca56895260164e7eda95c952601648ffecc6e852601648ffdc52ea22601648ffdc12ea2260164cfbd412ea22601648ffccbaaa226016497fccb6a6226016497fccb6562260164a7fcca6562260164af7cc569da160164adfdc7295a160164afddc3295a160164afedc2295a160164aff5c1295a160164a7fdc7aa99160164a7fdc5aa99160164a7fdc2aa99160164b77cc569d9160164b5fdc72959160164b7ddc32959160164b7edc22959160164b7f5c12959160164a7fcca9559160164a7fcca5499160164a7fdca1499160164b3fdc81499160164b7f9c01499160164a7fcca88991601648ffdc22e931601648ffdc1aeda85c164f57d985d5525c164f57d7564d525c164a7fecc6a1915c164e77cc56a1915c164e5fda85d5915c164f57d75549915c164bdecc26dd315c1649efdc8aed52581649efdc7aed5258164dcfdc7aed52581649efdc3aed52581649efdc1aed5258164bcfdc7aed52581649efecc6dd5258164dcfebb2dd5258164dcfdb82dd5258164fc7d875d55258164debebb6115258164debdb76115258164fcbcb76115258164fe3d756115258164dcfcb76cd5258164d6febb64d5258164d6fdb764d5258164f4fcb764d5258164f67d7564d5258164fead845c95258164f6ed935c95258164fced735c95258164dcfcb76c552581649efccb9562258164b6fecc5499158164b6fdc75499158164f4fcc75499158164f67d755499158164f6ed725499158164fced725497158164bebecc5494158164bebdc75494158164fcbcc75494158164fead7254941581649efecc6dd3158164deecc26dd3158164beecc26dd3158164 else 0x6b6856c12d635a88b495689acf459c4b34165f2cac5934b1ed627ac305822afc95f02bc15778aea95cc2b8656e8adbd5b52b65568cac9d58aaaf655c8ab7d5602aa1551ea9f552f2a4c545aa8394f7a9d05362a6494b9a9545284a4c148f291951f4a3a1464a8b75130a1e5426a8215038a029402a7f34fc29f3d3d8279e4f189db53ada73c4e3a9bf937626cd4d5c9a3d33ea65e4c98991d31426164bee97952e9a5b44b44960d2b8a55f4a9a948528124f049a292c9249a48148c4914121f242c484e90211fb23e447be8f011d723a9472e8e491c0236e469e8cf519c233346428c7118522f845cc8b1d15aa2a3450889fd136a24e449288dd1192213440287bd0eea1d843a687390e4a1aa434a864d0c7217c42ee85950a9a14e427884dd099211341e8835505b20b1410a8199023a02840127fa8fe59fac3f1a7db8fa79f303e227bc8f699eb43d4479d8f2b9e383c3277e8eed9dbc3b3a75c4eaf9d403a427408e719cc43964724ce3a1c553886705cdfc1bd937746e6cdbe1b5d36966cb0d8d1afb35b86b5cd691acd35766a70d451a6b34b2691cd141a0933ee6760cdc99a7331065d8cb89952329a64ecc8e191731f06398c7098cf319462acc46187a30ea61c0c2f185930a86108c1818112ffe5f80bda17a22f205d90b9c17262e0e5c08b7e96eb2d985a80b3a166f2cba592cb1c96272c2a57d8af215df2b66561cac115632aa254fca9d15352a6054aca9314fa299c5288a3b144a28564ffc9f693e827924e409bf136c26b44d54994932425d64b3095d129b24aa483c8fe91b7236446808c7117c22ba452c8a31134225e447488590f921ce435486190b1213e423484410832094411480c8ffa1f9c3e887ce8f981ed83c647700e8d1ca8386c6f10d9c1a9233a46580c6a18ca318062d8bfb17842ec05d58ba6170e2e085b18b51167e2cb458d8b0915ee2b945700ace15922adc54c0a52144c27b44cd0961126a248c47b88be10d621644238828102c20443ff87d30f4e1db839a86fc0dba1a2834286800cf6193c32506450c1816e42b3053a09e8138826804be093e1234244048308fc11e423a046208ba1160229844e087810a820c0413081c102420203f207c00f381de03aa07300e4c1c0837c06ee0dc81b6836806c60d781ac8354069e0d2819c032606420c7018b831206000bb816e02d705a40b0015d82b605620ab015382a2053a0a60143027404c4094011f022c043408200fb01e403a407000dd81a90348067c0cd01950320062c0c3018102f805a80b28153029c052408e80e4015601c801c8000adfdc7aa9a054964cdfebb29da05496497fdc8aed526416497fdc7aed5264164d5fdc7aed526416497fdc3aed526416497fdc1aed5264164b5fdc7aed5264164c7febbaa9526416497fecc6dd5264164c7feaa6dd5264164) else (if i<8 then 0x101504b82cc740c782bc0813903005998138f0d80a82cc8308a063c3cc250300599a060c138240314809c786c0541664b81027102a0b325c35091413418025ca612032303106170d4241812ec0cb8120c01780b04241cc2482402782cc9413b86a0c0c240b32800004bdc1ee0cc0c81cdc35060701680ac91c0b327800200017016420026090a230004c00130006c18130004c001f00041400081800102d82c8409720b2056061e0c2800c1220c0180b76040b50599005802903082490600163005026bc09f0611c10e0405c0c228100182441803016805016a0b32003005206104900590606f0005808101602cc5a000818081f0604d4160305f10c00fa318781bc26be0c2015826a091f06100e8135f0620c09e0c4180805a00800e8069060135300003092120166300209103083ebc348f0878102f20600b082419427048786c0c0c240b333c3c5380b41814c26a23502bc1f4a60009800260008056060230004000001a01080000680030300c0c0200001c000f0003c000f0003c000f000205000400000000000005804360108000058003600090c02007000200000000004120e8043a010e8043a010e8043a010c0c030300c0c028300f00020b000400000000000e01081c001000c010308240cc0140c81841208600a0640c2090430030310608482180209103083e90c0104881841f492f1e5d44b8996bb2cfa58fcb0095a92ad654b4a7794b128e650d4a0893d3275e4dc4999930f25d64a4c92a91fd237e46048a190eb2126415480b8fd91f363d747828ec71d1239947138dcf1b22354c67d8cbd18fe31046018bc5170e2d245858a9914ea28dc4fc89bb12fa24fc48088c3113e218441e87ff0fea1edc3bc873b0dfa1a9433386290bd615e429084c908e210641ed839d06be0c841648271043207040b4812b01da02bc02b7ffeff81fe0bfa27f20fdf9fafbf407e42fc09f71bed17d7efab5f4dbe897cd4f961f233e277c2af80def8bddf7b80f6b9ece3d8a7af0f565e9d3d1b7a12f3dde72bcd37982f2bde483c7178bef169e2abc50787cf0b1e0d3bfb77b8ef29dd5bb8c76c0ed39d9e3b107616ebe5d6d3ad575a0eb2dd563a9a7510e9a5d253a2b7418e7b5ce739af7320e5c5ca939337242e43dc7eb8eb71cce31dc6138bd7156e299c4a387570e0e179c2cb83a7036dff1bf537d86f8cde9dbc437696e94dce1b8cb6fa6db6daf1b5536986d0cd9d1b2ab6366c2ed7e1aecb5ba6b36d625ab5354b6a72d4d1a8ab51069e2d349a59b49468ead159a1bb41867f2cf699e433a96714ce159b9b3616684cc8d98232e56572ca9d944325c647ac8798ffb1e06382c6bd8c8317162d8c569897310f61e0c345859309360e8c155814b00a5fd6bf657e3afa85f12bda97ac2f395e4ebc21774aeca5d56ba31736ae4e5c5eb8416f8add25b6 else (if i<9 then 0xd0088025a0116830200cd008812a100601e440120060802405611801c1820090030406f506080fc078100480fc200901bc401202b080240141004805020638702a0c7100480fc200900b05a0003f0817010066800409f0e8003a000e8003a000904b400200604500243014783040120060841801e1641c202af06080d030a41c39070c41c2000320f6011241ec022b00840699071241c20c83d8004907b000ac001a180420e11d1540c202ae060801808410048050201f01c040120140b02b87d100f8102200900f845070d41c2507080211a0c144102904b008920814825800400c0098805c0130580c0276000580c011d081c00102b074021d00941c5a010e8043a012810b4021283e8045507d0088a0fa0116804200c03d8802400c11032060281805a05030104d420a81a0c040160841282a2881878121481d80449030a40ec0028228460810228608a1352108e08ae011411420457000823006d10c11054205f0420882a110c030160c40820481580456010a4082048158005600081c021038002135090f92042a1f0400700840e00084d421350a40ac022b0086c021c8100c04009a85042135101c021010ec2302700042301036840000106140510002a1040c0208180502a10040c20020c280a200900305e0cc18080240141000180130090c825a0010048018200900304012006080240281004805020095804401201409025600100480502006004c401202708019601100480fc200658005c0c08048018114180a3c18200900a8401202209824c0c1304982e260900d0407e041880196004810e6041009003040120060820a430100480bc2006580040480c41082a2700c05841052180802c188238008603006004840120060810800c1004801820090030402800b8a060110640c0503009c080602382a0c040000e041382a0c0470209849060281806060138140c047020180a20a1c8298484905b008920a1482d800481508102e053101c021082a0c04070020c04830081c0010005c0ae2029981c46120800f020800b05091202f0280a8b400105502e05e0105f82e06114080a82000c8682a87a08c0f02e07e000f8004002003800102b82b8400802002cc601409a783060e00078001209054041f0007c00400178002004a80d0170360430101703078008022f0007c00100000038158600ba1b0901760ba198158600ba1b0901760ba1800c13a0b2182a81662b0020550483f0004002c0598bc0200c06202cc96000f8003e000834004152120c001409a825fc18402e02c85a000f8301602e81684426bc09f06140340b4039a0c026a508a0406c13505a20c002c5060303e000e00c2053e060b80010500c20e00058061a06068181a01868061c01870061c018400e065c0b0480b32038198240598c145848170301458481f0330480b3180 else 0x9080ab41835092830401201e8807a0140220c06802a1004807a2009015c430201500d060340090802401410050024260900a8402a60909824c3d14c083412a1e8a6041a0950f4401201508174105085c0200c0910e08de0c178300f60641b055c18260a8118402a3028982a0466120c8fa0b360a8d82a0b3150541662a0a82cc54150598a82a0b315c0902a0a2180480182009003040a1080480182c0ae8326043c0ae8305815d06084244152120e60e607100480de21015c0850460400b02a0461605408c2c0a811840120160802800d20a90909c0c08048018270081c04105d810802402a10048088260930304c1201a0b604158178305e0c0803e604204c0900e2009003040120060801807613804024076180480182582881440280150800a02a20a9090807bd06612060c5d06612060c5d06612060c5d0661207a0c4240802403e1004807c201f020458158236090781502360907815023609078150236090781502302cc6012016080e00461004807c2c01a09002a300f2054048300900a840120060802400c144082902080480282c3e81544507c0188a05803178330602055078001e00078001e0004605c00170003c000b0338002047068181a0606818158150305c000d00c34030d00c2b02a018a604c0c14c098062047078001e00070061c01870061381600c4702c018811c100007020f0003c000e0581682182f000405208058168205a02cc4830209e0907c0c0c0c02706e0640c06041804e0a83010000e065c08470209c0828302098802400c1004801820147830401201408059c0c12c1440a20090030420ca06080240281004807c2d008740218180606010183011c2002e04101830201e80a88160108120e6081241ec002483c07851020827431020c409c002483d8045902018080180121703020120150802404413049818260900d054000d00034000cc08330260008018079160930602c1260c058244180b0498301609306020830506002412090c24241804041641808001200608024056100a3c18200901384012027080240561004801820090030401202b08024014101e4201202b0802402810044810638402400c1031fc1820090030401202b08204028f060c18e100900a0411460ab8306c157060982a0c715056c182a0ad8304028f06080f210090158401201408022408048018114180a3c1822065830440c9060802404e100480182009003040120060802400c08a0c02400c100480582d008412a100968044012))))
def markLevel10 : Packing := (779,5,8,0,0,15,0,markData10)
def markData9 (i : Nat) : Nat := 0x2b0208000b804200001a06074030f8001e00c20f00020f0330301000b817818207818100016066e0425c083381041a00040010800000841d00841d00041d00841700841700041b00840f00840f00040000000000003c082003c00100000d032f02c0c00b320340cc0540b31e02a0598b40cc0c040000000001ea79fe578bd975bd4747c8717c3703be6d3ab687986578c627795db7458f6155f5554b504ff364b32a4831745312423063f2fa3c2ee392e2362d6332ca302be2d2b22a2a628ea127a9c266972529223e8620e811de751ca701b64f13235092140460f0320a01e0500a00437f772bb29da054964a2feebd77552a4c82c915fdd732e55889905928bfbaf5db52a9300b2695f6a5c72955260164d3bad4b8252aa4c02c96d6dd7295a254980592decba252b44a9300b2636f71d412ea226016492feeb99511322c02c907fedd32da8655705920ffdba65b50c92e0b249df756cc6a1915c164ae5eebd76c22a4b02c954fdd7aed935496059239fbae65cab112c0b24d3f75ecc54991581649e5eebd98a9282b02c91eedd2b31b74c560592f573a45ab08c02c0b25f1e355b75cd8058164dd5ce2b0859300b02c93cf9d7b315260160592f8f3ae5aaa4c02c0b25f9674cb55498058164bf38e896aa9300b02c9babacc611526016059375738ec22a4c02c0b27e2e31d845498058164fd1c5ab08a9300b02c9fa39756115260160593f55308b92a4c02c0b2517f75ebb6a5524c164a67eebd76d32a4982c907fcdb722aa65d205920ffdba65b50cba40b2517f75ebb661a54816483fe6db915532a902c907fedd32da8655205925b7baf6634ac2240b2497f75ecc6959348164967eebd98d2ac6902c925fdd7b31a5645205925b7baf6634aa0a40b27d5a661755497048164fe94bab08a92e0902c9f5697564d525c120593f8d2eab1aa4b8240b27d5a5d5526457048164fe94baaa4a0ae0902c9f5e1985c5215c120593fb4308b8a42b8240b27d7864d714857048164fe70b1ae290ae0902c9fec1634c5215c120593fa918ea9aa498240b26fd2715524c53048164f5e8d430298a60902c907fedd32da7649105928bfbaf5db52a9220b24f3e75ecc5496044164bf596eaa4a0ac0882c97eb1d75494158110593f961aea9282b0220b27fa85c9525056044164feb06baa4a8a40882c9f761935495148110593fcc2c6a92a290220b27f6835d525052044164ff90baaa4a0a40882c905fcdb71eaa6a5525920bfbb76635253aa4b25e8e355b76118058164ec5d5dceec2300b02c978b9d72d58460160592f553a45ab08c02c0b25eac744b56118058164ed1d5dcaac2300b02c9f83a779558460160593b55576c2444c02c0b27e2a9dd848898058164fd152ab0911300b02c97b31d12d58460150593f944ef11282b0220b27f88956225056044164
def markLevel9 : Packing := (85,6,8,0,0,10,0,markData9)
def markData8 (i : Nat) : Nat := 0x6e05b0305b03020f19140ae2e79ecc6115260160592f839e72d5845498058164be8c784b561152601605927cb1e7b75525056044164
def markLevel8 : Packing := (4,7,8,0,0,6,0,markData8)
def markLevels : Nat → Packing
  | 14 => markLevel14
  | 13 => markLevel13
  | 12 => markLevel12
  | 11 => markLevel11
  | 10 => markLevel10
  | 9 => markLevel9
  | 8 => markLevel8
  | _ => emptyPacking
def markHash14 (i : Nat) : Nat := 0x141de030005840000000000000301a000000582a8920000000002010000000000000000000000011cfaeb92100000007401280000c0de0500000010180001750000000c09aa100028040002240001087e0f00000000000000000002403e00a03a0124884e8d704900dc2000000482c0017480000934a960000005932895941e25c104694000e710284008001400000
def markHash13 (i : Nat) : Nat := (if i<1 then 0x32c1c51107d0138cb3cea7cc16bcbc0e9ff82a800014870000100b0000142e180bd8020804f812800000000000083352b4dc105c2ec81b58a6bdeca9fc26b26ca6e81861e215830000182849f394383c060022f403181cc000041c7417c000100af81638086452449452a0b4135895c000000021df0000000000000000281d3c39d806642bac01881780000000229994a7c8296883d01956945c1ac000381f1287d88fac058000280745d6e029800000002885c4202c30c68e08baa408d42b449682b648218c0ff48d91527803d821da07f01eb1ce842800000820d40275c2bc3635e1702aec25983ca037140106b7441b8cae228dbe84400024b90000041a9407000000002ca664399dc88000000000003aab70934805400000003087ec0a14174000088f400000003086c0000000202e80000039368d3c368c12fd56c8a5442a65d638ba4000129ed5eac0002c2dc00000003de1b8853426ac3049c8c000000031dbdc0f400000000c0900000dc180000e8f00001ca62c3200103cad1c876e9e49c1d809d82a080c56ad5438d1e580002aaa400000000000000000000000303678ac708c249e80002028a5df8000302d400000000000002c182e400004332038501d4c11fdd4d004429e10ab4000048b00001e94b9d531f741de6829000000000000242089dac000000008a1c000003151c24000189146b53000ccb6c5db20328ca7400004230ca8601a400000003883203c4000203a8021400000000000000000000c01dc08268315d1f41255df68d6c817149dc0003688400000003c1b3695b43268b381d5edd47dc2d4042000508cdc02c00000000000000009d55019ec1140000c1c19d27587d83740000ddbb2977c26c5cdfe8cc456ec0ef6b4640dec389434dc3580af8c91303b548c6288d00b7c221027a41ec80a4000000000000caa9882add6842c8802bddd848a6025c28e70d25490801e6c31cc30381bd410c6812aa588a439dc043b80146c198816529881f335ee00000000000000003c257a940000000000000000000000003a90f02d01f4e423e813c831b037803c35cedc27f4a2000036ab8000042f843bc8a9e423800000014000242f141e00000000000005e66e966696b1cd7c98d297302d90253080643adc078c2c70af4c1580001caa4dd2d09bec809e821c3b201dac35f421182244b2c0001c1821eee003a2525a838081010521720000213800000001c8c0000400014010040108023100046200503802f8405400030009551003004a6104410114200d000806100c00200870080018000004e16a000390200000701040000810ac06180a0680042000100000184422846000000008240800100022328491000000124000020a002284610840120000081a008007080232840000c2018400100200042118d20090000004000020 else 0x2aae18a322bc3cabea03149fa416ec342c0e901c881dc000040a800000002df58000083a1deddde5683a4005c00000000000380d40001c14cdd140001c1f84a0400010132834b9f1b09e61c714acb08249d19826683540001298400001d8800000002499c00000002406ac10bc29de80e0a3c00031e60000000000000000000030b1c000209a000000001ab0bc2fe428c49f7c0cc415c0000000240e56afc29a8889c4148811acb1800000000ca19c82c000000000003c2344888ca800000000129080001c96e0274a82d8120ca445e7e48dc00000000000000035cfb5c64019140e1ddc528dc9f25aa3349c602b2c27282bc435289b94b940002a86000000000000000034ad7088ec9d9c0b91cdadf1ec310c04a8244c2f700d80003dd200000490f5e1da9b5aa5d0a705032006c000000000b7400025ef969cb9f6f8a5b030b03945eb1c08b82cf6a0c8113c15549c1c07d68765cf7dc6edd87c96000036a55424040d0000148c80000000000000000290200034345c189cb4c00000001e9e80000436c00000002891ec22908bc0003dcf04050c034000100c003380002837fe8fc0001e9a60140aa51c248000000036b32409a9c755ef681f4000000035ebe40956b8b1d64c1fe42628207c0c90904818c024c4964dcc2091ae857400b1de9493bc152c33ecab800f100fa41a10b28a9c108a31ea8aa25093d0)
def markHash12 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x1c0020421010060400c14c82c60890000401042c0004ac75811c01004c13c00001c500c280bc600004104c02a00024014102b0c520e0c000200800200800103910e30a0041c3004047003000ec308024600000014c04004628404500100004210000130f0060410020031130c5083040042017002000046000800500002040002204c4008100104b3c430004034e0010021c600002100b042000c0504310a0050432800421c814100d04048000018101718c2400010c50000040403040400400010040802800802bc38a10218100224304120200800200100004b0015800413c00000410000003c20000080401400803840030012860090000000150080000400461400000c00001181c10004010020060c302b0c00430020001001010815c30100000150001420400c300150410d6910000030000800812002c30851811400080002781020400040805400800010890000000c204304024104580400004000204708700000000c1810000c004002604000000000314010028208308030000000104a20200000204000308000000f2050020000071803450418c10802031830011850420000011800c50450000843ce00020010005604004004b04300230200003f0020400000418820c30010840c10410421000001030420020020040800850c20000402c00851ce1820cd0000c420208800504001b0000011c00400012000050000420081420000022000400860030030000060022442860044050010002010c20040020000d810008600100d0040202c100308000000c0000002066c00020080c21800c11c50001440801800450c51810051c010150008000258024018004000a0020cb0390c00000420003400410800020400070c500438420201114000004000108330400110000300000128000b0c00d30420c40c01c10420000411c10c40010820403000c300000200000000c1c00010000070000431000410403800410420000400430810020410880020010001400817431800050800400470c02c00400810010000460060801400002000400040400c11c10000000001800c008000000104104300300000900000404000100500101e0002000430c40021c000004b1870001070000060430840000000410020000020801032410400412c02000c20440412801030810410000030c00000400400030030011000000000020080801400401c034019820104a3cf1822410000001400010400070000020000000000400810000000021c20410020800c10000000c20010000000400070000000400800000013c00030800400100400400000000420410002c10002c10000000430000800c21011410030050840400c00843400430400020400020050130040c20410000400020400040012850050002020c9041049101009002180001082041040001 else 0x40684a8f5001f4e06476e4b6c080000006045cf47b800000000090369802d800006944800000c007f0060800000000000000000023da040ae4415b1ca810000000001d453340e5552fb00000000000000000000000194b421cbab04240a4da00000000000000a0af60000000007bbb250a6c0000000000000000001ce3b800000000000000000025e4b385beaa23234d0ede0fc84a2c0b1a00003a9ae00000823e022618000000000302d034f680000000006ab2c00000000000000c075200002429580000f02a580f27084a00000ea1c67452988ad00000000004eae80000193a9000000000102ac000000000100b7088b8500e8000002eae4ca060000000001ee788000000000302d400003402278253b71b724d90000038088da28b2050b826b902ebd7761008d681f7e00e45ab6c445b58ac6d8427324ebc8565eafe2035e109b6ceefc40a1e900480744c56b40163f8025275d3c01e36972304b9573cc006eb6884b8250104c4a04dc4a933047037072b54f78276bbcf5409628e5b88002d802fc2309a03e0ca1a101d1a05cbe0a01093b13adec01bca5430490905042a2872ee949ea90383ce720c5c420de8be98351809caa048300dc091c282a7c743f3c0629000db094ea17a502a3800008002000000c04f639070000000caea88e83b9f00000ee7c80000011c000000000021d717029be272161403c07a80000c031e2ed54000000000f067c00002ddf45846d7030c60ea8c0be781faa0ad0e573501f9bd0c45090b6eff000002825e2235f00c4c0000000008a69c44c0f01f4911416073000000424c00000d2199601be810c9915baa0a5c444b4a1100000905ed6e49a01e1e9445a009e0000289cb1854f000010501400000000000001a16c00000603e6d020c2130e80efb0409900aca061c00007032d202162e65b9dced00f1e2204c0fc5c97b90193f726420e8fc0bb18419d0bc300507aa9b7d51a10595e54160a00304ae0000064badc2afe158fda9608053701b5f860500ba1ce388000000000000003497041481028d0000000001485300000806624131c00007014000000000000000301f65a48061528c130192256721e6470f6a37192e0e2a56000000000000004146040bcc0000483fb0000000000000000000000009490400004bd6400001ceac56aaa0859c0000000002c1b683c850000041171821f00000405844ed7c0000414060000100f21413300000205bc807700000304f49704f40aa289b680000a7c0e0000000004bd5e30589ef65c00000000000000606330231d0019a0902000031e43000003236f94f38c10aa80c800000000000000455b80000084c88485b000009018e000006b03c802b22379ce0b800c064903904b003040040243040fc0e825000050000000840450003000c63070820402423c600404c2670) else (if i<3 then 0x1e0ac0000043d77000000000000000000000001650e0003860446923ca0000388e5000000000000000c042a02af0023400002c891a5106f0b04e48fa68858000020b2600000000043a42f2117e548c89b900000075336023a5d28f01d500001556cc000000000000012eb92818f301ae1072d202f201a2639bec737ba08000245e83b5026f3a018069ab80000478cd64e8c02a280456d04389530641278000000000d439b0a80e81630000000001aafc80000000000000369ab2d13ef0868c146569e795267907e4a095eea5ff84c97a768a117dc04a5827e40387202dc0000000003a5ca0000000004d2680000000000000000000000000000369a95135e909be000030032502921088ec10bbc2069147cf73f2613ac680b7ba2512863442ab89d3405bb10568e1601083cf057a4aac3c17cbe90580000fa7952124742a48d019f77eb612dc00007817e000004059800004042a803cc44865a904d80676a44a4051edc9c882ad6024a817e99c2c800000a051745cc02bf901a5308c3609e7411ba941042b3c20b3c0000101615217840f769cb5901ef22808c54df80dcd555df0383807de40529045262b680000000000000080244d4b5ac08900000000000000000002818d1a2ce6e390c8ac00000e7269417700000413b8703e000001c8e7c80ce0000101169697c2d3a5da18c00000cafe6ba062089fae7eac10c006034212e811d8000000000707b400000000043c490000000000c08380000e082c000009d5e00000f02afb4be42a049909582a534424982e8e921d0000014f20819400000a05f80000000001559ba01520000000000833900b1d20577019af9440d023274115c0e9b1044302df20f96495d1043b208004f249086830544901612155800000000000000000000000000002a08c000024a11f837600000000000000083e7704bad4272095ca10cf50b931577ddd0980076b0722045d64176f05a69024f14c8ba9d6800007073e00000000025113a032440197ca1e351df205c7d4f1302d691003708c1845f800007852490a1f2063b2a29c510a4721d24b24c00b0033f1a3b2000000000784b2b7c05846c688822041a50a5500357011b39527d03f220b25c24f381a992590400a1010d78589eaa2e40cb148b095600121648e415429d238ff879f600000000078129e022ba0a1aea407d284f0b0a0068e8069281e0000000000000007848d0000000003c10e883648a5b7aea3280a4b85cec0541e018b02dbf007e827aa00f82c09ca940100001c02ce9c7a20203329e3e4b89018300000e7b4c6520f00458848800000000000000484d9224e5208b582710000060388743ec000000000000000000000001bb064089ae0df002a8a95ae7074800003aa908000000000000000000680baa03caa093080982806b803c2 else (if i<4 then 0x138ace7331eeb97c2e35ba816411ba084a0008e12115004e00002ea7e0000048166000024066d80e210af3803b41e0ea141500000d4c281c94000006041f00fa2c96b800009a23cb023400003153a00001e179a8099093b5002b76580fdc70fd0a25a8f20000000000000000001607f909e3584ea00000000000000000000000000000dec379186f032d4f21e08f2410c7b7923c068900b9a8008e06a0011fe82f1d1122da1d0000000000000000000084f126a57800000000080edc000065142aab614165cdec2954daa0a7c00003c0de8000000000000031e1393aee50b940000148c5d52cf37a7680ee2c29400000b07840000340f4800000a3d0c40cb49b4313b4000001478c5d6925143d258a6401b817945283d2307806bc8afcabd520000124d9781d2800002a248000024148c5280000000000000002954400000e15f4000000000000012eba000000000000000000000132402f07073820961e818800007a53720900cace73d99926bae146000004959652a86f4868000000000000000000042f500000000000000342960000080482953e583021808a9287f60c3800005910600ac18e154011511428022160000000000000000000014880000000009a9f1b407fc1b98000010b9f408f00000400ec000014e4e2008b23d01000002483f4285d001b0018c00000000000000000016123040201385b82367654be401638450a0a13e04290a07a95b3d211360bd49d37500dd025c8a081881ebf8014277d4a0fe2402ec0382008938420888d8104bd805786057fea62f94320000160a0ac15c40402e0046211f2c16fc005f778e974b8c000003c8d0000000003e87c83cabd070c000001d8a8000000000000000000000000784000000000048438000017531ec01d1026ffa748412708a044100ba7132c04a91d6cd0036b06b4800ef49d6301996056b442b60815883e400000000000000082700000140f3c0000354fb600dc00002dc9bd919f1053000a6a481b2513a72015409201dd3b00ab00000000035d01f84bf50a84601d580289d4559ab5c801d081ae7056a00001e0a2daa7b204e0c708705084c12b6905997491e112dc2add03b190a10a016228f4f85ff20418f482b4024c02d15097434537840d7bc80000016110a1c0f000003a1bda47188038a15a0d7877f56f80000514f250b188426908636bc3dc2093a0f7000006d3a0675e34458d028ed036a804f78024d42389933367257cf7ef002ae84f10000040c6ec082902d20058d21471414ead2a6375279524800006b90d0000000000000000000a08f200000000000000779f4000000000500d0105dc21087ca0a680e000001e421a495e3817527b2d20a3e823ae80fd00000ce7a800000bc1c2087e00002dcf700000000000000000005559a105fe000009d89f008fb0bf80000 else 0x63200e5e125ea9b0000001264e00ff800006042300000000000000000004237400c601d24884cf978ca0140e4a2490099427282e9fd807a405f1828a20000080ae003f707bf9951ea824a3048a4099de11b201394115500001cf29b9e44010cd80634050d6005fa81b200001204d4000030608c050a0000302688000000000c055301fe000000000000000000000000e0bef20e4981a5b049f000000000041e6d829f50169ce2fa88a800000803ffa5638c01f8000000001c473000004917420735405b00000185665086c2178bc1366055ef06408e7a11cf0802695258d20f2b41b4901b0071b440ef80000152b000000000020ac51513d306ead50478190cbbacc77858076a803bc856bd06c520f41e831a11e67a55ee0faf02a60910750447a177801ecd85889ab5b344949c4b70183b041c34984a882800002a202000031ddcd8601a073c0000109d6e007f00000ceeb7a951b03e21095aa0e9a4938584030a4cb814e76a7ea813b775c7c0ba483036851330a1800000000000000000016011c0000482e100000000004a03c50f8824df017cc00001022c406f60000188f9480fbf7a26a12e000006003570270c4b95eac9800004a51a000036afb4d5b70214e54edbe88e310afd75b0607f440736b809a02e8810ddc16180000000018179289fe7037952a584462b9c1135118603c9e0f6042f00013e4a568843062af6f01a8922d9c030d823c184439a242a140700e7c85702049a00000025a00000000000000000005158600000000000000000000000040c28c85d2819efa0a374c8e00d66847ee03f800000000000000000012f0090a94505cb4a55a000000000000004276cc00808ace93d31f0b372105f28a3515858087b642ef1d000000002a4a0000249626141ad04160000000007014fb2a09251124845000000000000002dcea800000000124678414a2013d20ba46e3b60961000005084c0000340ab00000b0a8c00c9c404d138f0e044f744ef880813a0d00000e0a1c0000183bf0000000000000000000906e2c102c281d800004020204b0f0a2500000506ae0000280540816e907c60000268a01ba1a67b300000000006852e0080b417e54446c04e1000000000041ab5555500000000000000000004205c814f00000285789261fe40d79d66904b5e0ac5ce090000008002208c5605c0c8268000000000000000000284ab000002f6286a3a00000106a400003813e800000200520aee88b47d1d8006bad5778dd2378018c0b47e0a9441a4c81eb8235d613200000384a6b0821a0b600000385fd60015af58c02fdb3b64920b7f474549caf002a2085ac42fc008ee11c5a032f251498878f93cc372675441c80aca84d66013000bc602a6854ff8056d60ff7c2be303ed90484cf5d5508fa386250016c4dafde44fbca700000d5020000))) else (if i<7 then (if i<6 then 0x7cdaebc8000000000801e504c840000000000000000003400be84f8000000f1d8dc15583360000000003022cf81aa57528e4c811e0080000000006eeeddc948000080b0e00002805e80000000010eef481230000000000b42440000000000000000003899c8000030952c4d80c185cd3f7707ff003240000683114a8a00000000000000000000000000000293b900000000000000000002a2e800000818b8000000001543210a0c154fa8067194dd80283891665037c8092cdec883bdaba56d2086c5cb6701854a6100434e01134d137d7577e0f50820c68337804eb40c66c029895876a16b413da2a25881ad6a192350b202bbcb95f704edc062aea60785a5100bc155b32984e1539a09f7951f98255084b6607f40e4b128d2d841b1a1a8d4061290f4d5605061ba50db024810553200354016a087218514c774c00001dc5e800000725ea4b2e00f6505230a2e2145b400000025b00001f512a42c83019470a22220200000000004a22da03f848c0b136e320cde49dec259985d430097ee5aa0a21cb8d9000016161a00f9d81440000000000c1778bd9ca7483b498a40fde02ac00001a4b4d825f43d182009800000000e58108d02c00000308e2604d4a0539246c881e0800000025e0000281a000000f005a00002c1a5682cd000000000000004829e0098800001ca8980000000000000349d9e842c0000000002412ab8110201058120e4135993b0d713a003ff9e10d02210000140cc000002d35a000004040fc1826838b30b8e212815d228808900001e4f24000000000d0249a027341b6500e9374c600000000000000b22f66077a48db490a1000000000101da0000042732f565700e4a805720001016ac0000000000000000000c299e136c77c0600000692f0000072a7800000086100000000000000081f6581790000160f6e4882a39fe92140002ec69c7f0363309e0d4eb0000058563eac0600893028215579000000000000003b98c00000a02bb8960ab9ff0000120a05c1711d3c5aa5de4137940f380073d093ba15bdddd4b04dc00001811dc0000790ce00000e0c735d4500000e25c60000000006bb90000001490c00005824ad05674054500e470167e058000000026968324a7b0e000008053b10ab0070f4073902fb3037f92a83a45bf80b2f52b800686e075d8046bbb5e6249980ccc08b0302e7fa4c880140eaff4d11512a1de05e24249e0455f71e6042e50963ad37560410801b7c115d81ed000006164400004d2b5f248e2f4ac00004009200000e05fcde05b51dbe75e70e4338228903abe0440e4a3bc2f6d8502001982e4c4c1c9e819aa0b08b4850686ee80036702e80242aa20f04c02a76b944d2293c8b8980000060948c847380212752e258104124995d20080def49940e3d847b0261cceb4c41860818b503984032bc06a73b else 0x51a1e33c8377d02bc0000280e000000e06f0c560c40d58000050a9dcec38000068480e279b410800000703ad000000000000003d19bc042e0000240e10000030740c0f580000191b5c095114f3400003047d705d59446a42dd1826d579512080b42b08952aa002400a12c9e4602b70000000000000000000a27fe000000000005b4106900000382dc80000b284f6068380be8013c7091c00002400f682bd000000000000000d148b077400000000055389000000000000000000000001c03bae9859b9a30a296016bcde35201eaf06038146e40f700ce3d07d4215658149c90b3078f1414e2ca804d448f0423413bb802473d84aa62e000000000282952a9efc0c0a29af913898aa8da0d540000515341098a6ef0769416839b8a1aa00000aa8c80000f07604e3a8a98cf90d20000000001c034800000000000001420af037460606e50cf28148000000000816636a5451533b0983c1419c8570823000000947c0000000000306dc2010800000000000001a144000003398e000006f64ac9e1b840f000000000002cca86020000140e400000452420008741594000000000f7a3c045940000000004259400003dc9700000d023c20c480000610b7a0a2c344cf81c2b85feb277400000000000000006b39460242d578234f7b0720435c8c638404a0b064170a89f201512901c601340c239605c5803e2cebbe0848101f8e2434a04618a3a79099d2151c4602009b6be04e07ab8003b5e366853dc08ce81117ca100840a808a8a04878ad0f50d8d0044a0ba30099b80ac40713e0e5481535800fb24bfa0d05027fe907d4ac0864954c0ea280b202745e13f3688dad011419c5ceecc0096750471a97cc036e8ac6703603775400b6f2847c8368f071d81331816d212bbe0106e45d9029380530b06b18069849ac6901e1219604e801eceb85a98a914a09450219800000000000000000000000fa5ce000009cfd9bc6fba9d60000000000000020a3400002c85a2819c4034e00c200000382ddda0a00000000001550a000018025b8a4000000000000000000004034f220f9e0a84000000000e00520000000004821e4069a0000000000000000001ce62e01848000097206000004aa150432200f600000000003bdc1094a353d5813e00000b0a2a00000c2bb613b72a7420000000e2f83470aad0000000000215ca805494eda1c9071830550519ef7e49d2533b65aa53ae029342f43bb0fd055d6018ca88f80104523d400000000000000000000000029b080000a7ab404fec000000000a23dd40199824af0162000014e21c0000000008a87c000000000193aa676bb45419c050000000000000003caff4052fd704d1438041552103900b28e4c20000010444407880000000000000050a5a000000000404f95036f8e057c086495ab00000e46d1c17a0106ef7) else (if i<8 then 0x9dd405444e0204242c602eeb3a7e47209606274a153b9fdb063a8ef92c2aa113922095800003093c2806cf0ba6e45a482def8233b725400000de4198453904b86ef0d484f0000030bb4e0aa40000784e30000014ab81d5e800000000000f1502d3e142500001a100729820000000000c562400000000000001e4638c8f40000020a406f4b0dddd390800000061570c8e080000000000000240fa881bf0000000001020700000000002e688000000000a257c000000000302cec0878000000000602fa504ce000000000684e890a8600002822f605f4c04d0000000276003cb00000000018020e02e600001250dc00000011100000000005de000000c051d8097d8a96f03e1faa8eb55f80000292fc00000000000000000002a8e40000241c400000a099ba0ac90165800006013b408c8e94e439f020947214ee42928bbb892170a0dc282b4f128c0000084d7c000050381806b680b200000081451a9e9b43d800000851e27a148090d280b80000000000000000000000000000e0804dd0700000ba03a2000400005bcf6c02b580d95a88670466777624175a82dc2845700001155dc4084800000000061542424de05d762a1e000038057d51da0000060fc0411c000004074ec15c400005bae700000005c901c2400d9000006053b49bd7547c4a38ca00c0c0db6846972a2980ac65c2861310b092c0141542dae5522f22e480d85c265000004784b0500a0846453d01a9fcee010000000000a0048e424dc8ab591cd400c36074982bab825a0000014b74000068164000002139880f10ba12e085f80eb288e5e013aa247e2e7e05d02e8c5f208832e968492a79441908cb1532700a5084ef6082400000e9225bbab073ad34cb7e9561009b073a80179402d000000f218a2483741388000010122c17b8000060274227e60000000000000052b08a00df813c1032f50b7f5445d01c79900c000000000241b38000000000000000000000000000000003dec4d1043307a6000000000705d9ea279c043c402d80000a05aba121c00007858f00781a052f6a61ebc2280960016f2818fb02d4f278b203e441b7c046e902a6ee1110122c3b9e0000000e35421165320f01ed3565382e40000080095456431ca0a00800000000000428b800007a9730e44b89f11907060599e117400005d321d02d7e0edac095f01b3625fd80c3d4131880c020c0fc16c80000083cc07432e01f4000059159505c0003e9ea38584d5c22e7a473942c91118f300f36081cc2d8903f6872046f4bd4858210a950238f4d4feaab203103083db4a2f0003381347025bc50aec2a06056737accc461f02caf1302c26c21547742ea884fd00000c134d6a8e384c6303b380aae5dde7941d324382148542ba15120d0751802894a258000000000414348298b8184000006f57c29599020dd26026 else (if i<9 then 0x2033d72a0ec02e75d4c305c00000180ae9819953a8e403776048d0a0d80000809c96ec1ec1ca00000000006046c00000000000000611d000000000000000000039c4d0000000000000000909800000000000000000000000c77db603f040ec4801552a060000080a80000050934446e1c151b040c00001e14d0006b00000000000000242cf40026702f725047026ee84a16054f841fb82e0a80b5f01d6c4f4548521917f000000000000000000000000416b25cf2e55a70276394f9fe955a819000b45e0e86c19dd014ca015b40c880000182ec52b11ced660294f1078007060000301fc9056ef233a80074824780000ea9300000288be800001ab88e08940000404d800000000012afef852600000000008225080a67a1f5808c68160ad16f57247c0fba8077903b3c0154617e1c2cee526902a7f80c9b82f60000000001404980000783d1971d98eb8509388826aba9c30047cc051f80dc2051400a27e95b80000907ea000000aec890850000000000e9e48000000000a562f6adfa84f5daac780520884e80000725fea176c00002041ff0b99740731e8893c7c603a12e80702e2512730062c606f35d4b48557d01a7348cb4b03b84f29aa26211aa2ade0034277af0eee2401dd901e8da4e60000148c8283bd00001a1120000000000000003412000000522700001540b7e861d03d27257a0e15100edfba1cd019ec03dec1a9a0489d775c00000000000000d07198f7f800000d012471fdce21000007b84e30428c17d509bb8000000001603cd5eca2d0e9774b3a50ba0062351f33a5aaa00f941973ba02670b1e107641804558f90be0811afe96a60181000018f6840000481d6a036324de000002019d4707c000000000680bed010c000000000439941a796000024252753fe0047b0081640ac000000000000000000008484fa59800000000060329000006455c0000703ae376c00000000006d5ee0000000000000000000602ee000035d0ed833c4213f01590000068171000016e49c00005049930c0000000880ed00e1626c7000e28040f3897a032a0000141ef304fad2219845c5c01c80000508b6000000000750ef90331204a1413fc8435f726dae256c80bc836670aba356e9884c2844c90bcfd4444000073d8870b6c2152ec9be7850e000006060a2959600076230b20afdaadcf038a4052fa091f81d7e035f9069d241afc1cea0573a02628087e29e38024eba3afa15fb9c883813f225ce256b0c073d002eb04758113989f955208e7b17ce4018a0189300f01cae084f800201050b038c0000000000000000001256c0000000000c025d810e5819d7819100000000001c33453e410018000000027484c200001ee83edded8000000001a14dfc06bc0407f0472eea48c9aa80000827fb256bfc02a2bb08c0b87216844209bd445ca4fb2e665 else 0x2023e30196000008a920000000000010a400001848232a620000329765801300000c037caadae05817097600000417f3006a0000000000000053813fa08324d05427f5500d004120edde5e4b80000a01e000002c06d49509d2110c47414835300955064a410c4008bc02047210340a595dbc3514770aaad52efca3aeb9900000000b5bc234000000000000001404b800000000194de01c7abd377a0bb1b44c28004e823bc7422000000000782f8a0a7feeebf09e700000c068c609dd0257902d3e0a64c0ec9c122681f2f0b34b526ec14cd93a1b0b5d657110851b803d204f4c05a482ad602547045ea17358aa050397705f20000000000399a50b16c01721cf220261506995439d81c01d4b56707b6078f8b012d0cc375f9c01f2405c350e58078d65422c2f580000205a00000000007baf7b7314016a0c132b03bcca6c84e4d682200000000000000021c12dbaeb47b1e057eb0089d51eb0000000002415f7004d00000d435c000000000aa0c40000302cb7056d472440000000002ba430a725ef54ec01880000505b254a16ead90000030142000038ab183bd9d07bf6eb8341116859f500d0d54f82ad8f95d8f008a000036860051de1a53f84a046a248000000000e10200000301dd000018ee4800001015562764000cc000070046000016efa740464527c000000000000000000000000a4f69410b4138ec047f8513c428fe0411a7620a10ebc01a18087a0b14c05b7c042100d1278d621162c1fa500b1976c3c542c9e36982e4e09e7e503a01bf60414709b4e4e9000754bd09209960000000e5f02f75a4d600b5f8881e05b39a853025666a4160372f0452451be817db05df1078e0124800000b9635720d6066fc0e680000a7217214d6421800000c09d20000000004d0d1f2304000014141a9005dab688109402857141f00000a4e32c945253cc405100000000002022800000000000000015cc00000815040000713c780349605e902f780000000000000000007908762a6464b8549d4555bd771d60000000002837d908c8940e16ab380000dab5f21218823d00000671add52e028a4b50a5c060fa139c8807b3d5bb06f500cd0020e00548e0773a0a89c2a94051200000c13dc48071020a000a560c51412ce5484f00657492188618bd5c9030080d1400000000000000e4e7f403d000000000000001013980000f058a400f3c02cc102a000002067cc18a80000806a84e08cc81a0d22a604dc4e0ac000000000720980000000006d0dc000014f59602d2000000000054d8f415cc8399b0857c12f3cad14d540408dea0bf581080b81462096e045280dabd3a350655a4163499e680c2c76284027f0aca7943a622f800000000058428425fa00000c0c400000c021dc11cd006c))))
def markHash11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x1c0e91a9c40000e0005c8ec0000000007012fc105b0a23019b2062e026f0000000001069a5e806ac0e885a574df8809024560034402280000b00100150d2a2c0000e0b2700c900003027c908580000000018161000036a00caa6c0000508f3c1bb72945024f000000000707b1c00b00001c0ecc0abfc0f2205a0c033000000000674980000000028814000000000e0731a9285aaebde930000000000000000000000000000000189b800000000000003c0d1e78e80000405dc000000b040000802900000b02c3a888e08d7024a2aa9dc24590a87ea656706b408e82a3400000000000000000000008205bc944b08080000e03435f01809c7c1aa309080000e06d681936a75928240000000009263d2871ca8dd8937c714369c990568c065e0b39c0addaad400008053c00004a9dd88fc000000000103bac043008e4000000000000000001aaf7805880000f0954c9334010549ae20990000080c089e69218a5429500000000000000dcbae094fc1bd42c1c0a89a06410015400efc2bdf7938ead4a04634214708145c12926f801b78049e4070e03bd82cca22408031daab041e16abac022587aa9428e8026640f390acd5cbcaa11dc29d60aab4301508300180d238e890fca6c4dc85a06bd0b04da9b142caaa96c1ea2b08ffa835000000000925a9411300001c20e000000000301ec0000703fd81ed00000de8200001407a000000000f0a1c0000100d830020814810c10000400810030c2000003040002206ec60400010080c10050010090001020010002020050050000c60053c800304200708238018824000b18104100108300000834201c0445000c300f0000863012800000020404c10406401061c62820813400c300b0c14da0140800c20000c41800150122810c010d0000002c330200000400010000104708008e0060c02c004404118010304200000004004000308001104d0000c009314850034701508a0880410005c018304100000014900900104308018020508210001700008b04a0153000c90000173430812000090000000400800081010000010c90000440c10410820c30000400003c10014800c234000a0010c214300300e00b00a24004108110100000900a00600214110b0000050014042021c00040031050000020010c00001810001430000000890052800401407820010005020090030830820803400000c10020010400d20440000c00c010000a0010440820000400400c50001020c10800c01000001c00431440401c01040820000cd30020100004005100000000608000004021608014100804000130f0000000c108a0020c20010400000000440000830c61001800010800020020030427400021000020020000800410c14420120000020000800000000411421810000480000c0043000000084080004 else 0xa11841d0e016341c000003c0de000039ce2d0b9981a110a780000e24180000000014a7c0084400000000249cc6075381e5aa9c2e80fb2c2800007a8e0000000b8000005267e830aa057400005aac6e9c500002dd1ea00ea02190295468268010a02363078f00a8000034083e24900000aa10e40ccd088c9e92fa3840067000025c30422b45c6b008a5c1532a357813000003807300000c107e00240866000000000000032b06000000000000000000009e0a960a0b880000304dfea6e103f8c104000036899900af42d0f090c019100000000010154c90ab098b01e8a22bb42381045e5d66a0439c13f30a90806b47697817f208c00000ea963c999000000000000000000aaa340000f03e00000e003041d6478e7c2c6c18a15d3600288427040a258072d2a8ec012408b5413b00bf880c320ab49cb2f06fe40b4e0836e8540aaba29d5d278742d842181c2cb605619e81675cd41d9e05e7414720b95492bd0a4dc267103d40000f07b80000c04c80000622ee081e625b00970d2a81854d32ac400003a25d819200000000000000000030274409e4009c00001a0e4000000000000000000415c2066bddf000002c03f000000000000036ae10000302fd000000000a2be6015e425e00000704f849210000000000000000004089c0000000000000000000000e05d30201e705f81dad2bff80c5708ad0172024d6c017ea9cee891ea77a824e508cf1e42502100000000000000d041842b7b0b4f6844a04e48025babdbdd3d325f0406697134000000000000000000000000000000000000000000000000000001818c00002c27b97785010c000000000a26a61e7f0a6296a6300000c030000b4de9ee05ecc275e00711ef8922d6809742576c1d3aaaae4a8860376421f223665e783aba84823a03e8000000002a81d008ca008be2c0f4a4d302c901b400003c2fb000000000a053a895b40440819c907ed8063b23a989773a6cd0902604440000a06ae0930202424a7e008c4c09bf06bac97690300682aa05f8004aa21a400a3c0972028b0000142735007eea3a00000000000000000000001091f000000000b263bde53a0940a9e1d001ac2d1302e040ba0000000002abf59c4940ada002eca1011c42500f46a6f0000000000000102f800002422a5abfc2828f05a98280c7a3f82a2201f528eeb0a8200894056cc0f1607c58210e265869bd8a95e5da4501fec05d302ffc8eb925d7425d301b09c2ea015c8256b26419c529a0f00000a00500000000000000d2b580000000019dcf0000048f23aa7981b80000000000000000000000141420000302f4426d2c99710b0cc037f251a80db205c502c5805e82aa8103084284206e82931907e00248d048380e59003f4974aa365aa362750cc2f1a2555c164ca3cec1e91a2900000000031d3500002c29a0) else (if i<3 then 0x4210fc18700c036a6200a7289acd0a528aa6000000000000000000325bc000000000000000003dea300001cb013024c0000000000000324438024670640000e09ac0000000000000c74600000000000000208b1c2b54ab9a817cd798182e34ab9789e2707240000000000000000000000872edc0d9b20180000e04a7dea1d05b200f000001c96e0000041f22029bc28cc09d30125176ee892680271c176602fb819e1097ec2be30b54000020904005f2270a00d5d2a0f002220b49010830c0f806ae75771d659047ec2d6e0a6c000000000000000001481c0000208f02081028a56772e021220b901c90109a000000000002a600000018130a59dd2b000018251000015d86229280000e04900000375e4000010662040e0079a88ff0000129d830232004cc03f6c822a0246801a804b402c4a0014c2fa00003eaa34241740205003802903a3880000e774fc220d267002c8401a300e250523c9716082a028d27213eaa4000bedcb56a5ecc0dca06c8ca8e80060c11bf0b09dcbd7092789c1b7a43c1c7278e3eb019011a28bb126499c2d406a00000026d69de262a740000725ac6ab07216d9d9fe0058000000000000000140c2f250b6f9dd4a713f404da0bb180497211342b8ea97301d17083ec01e00002de7e209b8c2e170296819f42a3069ae000000000ca8f802130000000007a07c0000304cc1c75601f8c0e45016ac0c6000000183002f2c123000000000e24cb491e000000000d02dd405e400e78a69000000000007fd000800002a889000000000f039ac8b65271000000000081549268ac9bc4242202ab0000301f5074d00000523f40000000000000d266b01a572a7d8149e2190885d504e2c8487a9921da12a2a6880c20159e9dc4a9594995620540035305d602090077c428527583412100002e895226e4000000002420b000025f073032c0000000000000800000000b09805d250000000008ab67c00dc0856aabfb0401aac50000001160000342ebe021f01d7678d68836eaacec13a5000ac945370c80000a0aedc21d8095ca837000009ce3021b4000097c15818f000004119125c80000f01d41d1a5a940000000000c84b001bc82a5ba60c8252324e5a88ac0180000000001c8e10000000000000000000000000004002aea320000000006201fc156576880000a0ad3de9400001c2b290250825a223d74178a28d48ab00039ec1be902a4000090c1c000000000c22fa06080000007210b06502b80000e059b1d5f2025681efd08e94993f035d49570000000000000240e0d0870000000001c2a90000000000000080e380320c24be0424011d774bd018e12a96810b226c5c99e40a0c00000000040c7709640000f70cec224a070c000000000000000000000060712404050ae549baa00c8000000002c93ac0a3cc298a7a34000060664 else (if i<4 then 0x49dd1d05280000faaec01b347605688cc081c0000801454078f02a901b600000aa3cf7560000000001c1678096000000242501229266f81fa80a18a85830659808600003e820709500000a05955e96324d0c143c7387003e6710c096152701c16e000a0ea69502e44048b2ab682aefaadb48f65006f81ca00003ea76926b72ab23756a418d3068228a770a2b01ea409ca42d710bb5c0805a7224a8787a76403cd0368880e97c1a80b100002418ad78dd8867b079282cfe0450000080770000020047c1f7ba75c42bccaaa440ebc0b372aec179d582614a117404f3a25bc2b0f0a5c0000e0b74000000000000067a542abd00003c99d9042a80b5fa70c00006031240cf7763f085cb07c36a54aaae5c12800737414c7a99b2a7a101bb00e1000000010806c300382074add1ba0515dc2f0011c000000001007c904bf5cb600001819d000034152103a00000f0a04000022588499400000000000000000060c10c1cb507e4000010b7041dd90c1a811c20173c246000018a805aa7008fed03535c313086e5e9f1202a9d0a506145dd2e20480000f029f8af88a8fe2a9d724ec0000c080e40715070502ace7a95827d000000000b790742a300001c907000002887503590912105b40000f0b9c0000d02bfeaccd04d6809660ba000000000000000032a010dc2a2b405400002e932309e800002a3bc000000001c08f1034bc26900002805b602eedd2e1068d806162444011e00001480097110c188ea2afc08d3ab57080d00000000000002c088f09e4000090bc12a5a1793041703026242928065f02fc2000c00000000368b67055c000072abc0000d25480000707880000000022a0d0000000000000240df00001aac00000380fc000004808e08fb08377052ea8f49aa7e8077007199e4b30bdf4218202f78140e040fc09200000000000001418900000000000000c29900000000000000000000000c266f069140859a09ec24dd04d85c51705be40f9d712382d900001aaf8604480000022e8c1a2a0aa241dea01e5030500000c2e900783defb308a1c9490000340a0000000000107f741db5a8f49eff607d05d64408d140ab00b50402c1a76d1d191018a80648714c88b0906c74aa2779f40000e02b3812b901671c36000000000a057d01fcb03615c4b004b2c1736aadcaac6e0269c25b02a09c052000000000000000000000000000309b0000000000000000000000000001093100000c1ac824880000000021c0700003c244108f400007a10bc1adf23880000e0bd6683a5a59c8217ba2a181a95a9d1c0740749202bf70761092c009fc810f0a62402f977367086f00001416900001c155000014007f0ae9c27e000000000207ae89cb80bb9683460a46021a20bfe4265c72c6015100002683e3aaf800000000100f73779dc24ce088702a737c0ec810 else 0x30045f06e641950000000000000000a1e70b30163a09dc000000a0addcd1049969ac405f5813c20583c8af000010013f778c41e7503d82af572634ca816ac2802df8073c013d6298901f37087a0947b26d80000000020925005122a7bf04b8c811b02d929cb921d540f4e08b80000b073b8308000000000e70dc1c18808dcaab80000128b8a034ca8ba9218d00c1a07fb0222104075d80626ac00000000000007089ac1599245c002100001c29fe053540ed4008c020800002eb076027c0900a243983093212448422203c000070bce01bc8a2a800fbfaa8801f620bbc00b3d011000006a15c0000705ad011540b0000003a7654206c069c0000304d0c2de0000202f60000128e3104ab9d5e0248001c2f0ac4c825bac23c81b07614ea5f50714000000504c96d10801c23bb009b007697c2a4186da9cb426a277438081e0b1cc0cd376354a7f379e400002098e2a39d03a80000807540019109d8806d504080146a0978c240226ab0069200a5c01d306539c4ef04c40a9e9014c40ce00000000000002c2da00000424700001404e00003018400ba9411a100ab0082809b)))
def markHash10 (i : Nat) : Nat := 0x80bb01000000001e48c000000050500001815302bf02e648000000000000000000000000000401582828485784c0d329e603c205381500000000b06ca019c27583e7a11c125004bb9c000000004a11101a21f045240e2822aaa46442a93800000000001009682f0000209d81f8000509ee063c8fe8420000c0934162831b237047981280000001d40b81ca121ca90c134000380f2026011d40180004097610380ee00c204620f52a633c020016059aa2c53e508920cb0052053a00fa036ca908210099a44ac22c8352071e06c80d5bc5603ca46380208436060000180f80000000c053c0a8000606fa0980003945b74a553ec91003be0676005801584110a28f18ea6d8080000602c0000000ba97c0640005052000000030236811ea7b244400000000289c0404070000000060e800013d2e09440b400094800005220022184000882320012094470800020c010080100000000030002d2100108001
def markHash9 (i : Nat) : Nat := 0xe980f020030140000
def markIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 21 83 3 13 5 4 markHash14
  | 13 => lookupWord 254 686 5 16 8 4 markHash13
  | 12 => lookupWord 1423 3851 6 19 11 4 markHash12
  | 11 => lookupWord 661 1785 6 18 10 4 markHash11
  | 10 => lookupWord 62 167 5 15 7 4 markHash10
  | 9 => lookupWord 3 9 0 10 2 4 markHash9
  | _ => fun _ => none
def marked : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),markedCols,deadautos,markLevels,markIndex⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem markedGeometry : graphValid marked (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark8_0 : block marked 8 0 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem markAll8 : block marked 8 0 4 = true := mark8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark9_0 : block marked 9 0 15 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark9_15 : block marked 9 15 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark9_55 : block marked 9 55 30 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem markAll9 : block marked 9 0 85 = true := (@block_merge marked 9 0 15 70 mark9_0 (@block_merge marked 9 15 40 30 mark9_15 mark9_55))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_0 : block marked 10 0 6 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_6 : block marked 10 6 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_46 : block marked 10 46 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_86 : block marked 10 86 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_126 : block marked 10 126 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_166 : block marked 10 166 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_206 : block marked 10 206 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_246 : block marked 10 246 6 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_252 : block marked 10 252 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_292 : block marked 10 292 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_332 : block marked 10 332 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_372 : block marked 10 372 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_412 : block marked 10 412 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_452 : block marked 10 452 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_492 : block marked 10 492 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_532 : block marked 10 532 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_572 : block marked 10 572 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_612 : block marked 10 612 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_652 : block marked 10 652 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_692 : block marked 10 692 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_732 : block marked 10 732 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark10_772 : block marked 10 772 7 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem markAll10 : block marked 10 0 779 = true := (@block_merge marked 10 0 372 407 (@block_merge marked 10 0 166 206 (@block_merge marked 10 0 46 120 (@block_merge marked 10 0 6 40 mark10_0 mark10_6) (@block_merge marked 10 46 40 80 mark10_46 (@block_merge marked 10 86 40 40 mark10_86 mark10_126))) (@block_merge marked 10 166 86 120 (@block_merge marked 10 166 40 46 mark10_166 (@block_merge marked 10 206 40 6 mark10_206 mark10_246)) (@block_merge marked 10 252 40 80 mark10_252 (@block_merge marked 10 292 40 40 mark10_292 mark10_332)))) (@block_merge marked 10 372 200 207 (@block_merge marked 10 372 80 120 (@block_merge marked 10 372 40 40 mark10_372 mark10_412) (@block_merge marked 10 452 40 80 mark10_452 (@block_merge marked 10 492 40 40 mark10_492 mark10_532))) (@block_merge marked 10 572 120 87 (@block_merge marked 10 572 40 80 mark10_572 (@block_merge marked 10 612 40 40 mark10_612 mark10_652)) (@block_merge marked 10 692 40 47 mark10_692 (@block_merge marked 10 732 40 7 mark10_732 mark10_772)))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_0 : block marked 11 0 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_2 : block marked 11 2 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_42 : block marked 11 42 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_82 : block marked 11 82 38 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_120 : block marked 11 120 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_160 : block marked 11 160 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_200 : block marked 11 200 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_240 : block marked 11 240 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_280 : block marked 11 280 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_320 : block marked 11 320 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_360 : block marked 11 360 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_400 : block marked 11 400 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_440 : block marked 11 440 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_480 : block marked 11 480 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_520 : block marked 11 520 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_560 : block marked 11 560 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_600 : block marked 11 600 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_640 : block marked 11 640 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_680 : block marked 11 680 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_720 : block marked 11 720 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_760 : block marked 11 760 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_800 : block marked 11 800 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_840 : block marked 11 840 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_880 : block marked 11 880 29 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_909 : block marked 11 909 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_949 : block marked 11 949 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_989 : block marked 11 989 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1029 : block marked 11 1029 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1069 : block marked 11 1069 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1109 : block marked 11 1109 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1149 : block marked 11 1149 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1189 : block marked 11 1189 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1229 : block marked 11 1229 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1269 : block marked 11 1269 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1309 : block marked 11 1309 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1349 : block marked 11 1349 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1389 : block marked 11 1389 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1429 : block marked 11 1429 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1469 : block marked 11 1469 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark11_1509 : block marked 11 1509 36 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem markAll11 : block marked 11 0 1545 = true := (@block_merge marked 11 0 760 785 (@block_merge marked 11 0 360 400 (@block_merge marked 11 0 160 200 (@block_merge marked 11 0 42 118 (@block_merge marked 11 0 2 40 mark11_0 mark11_2) (@block_merge marked 11 42 40 78 mark11_42 (@block_merge marked 11 82 38 40 mark11_82 mark11_120))) (@block_merge marked 11 160 80 120 (@block_merge marked 11 160 40 40 mark11_160 mark11_200) (@block_merge marked 11 240 40 80 mark11_240 (@block_merge marked 11 280 40 40 mark11_280 mark11_320)))) (@block_merge marked 11 360 200 200 (@block_merge marked 11 360 80 120 (@block_merge marked 11 360 40 40 mark11_360 mark11_400) (@block_merge marked 11 440 40 80 mark11_440 (@block_merge marked 11 480 40 40 mark11_480 mark11_520))) (@block_merge marked 11 560 80 120 (@block_merge marked 11 560 40 40 mark11_560 mark11_600) (@block_merge marked 11 640 40 80 mark11_640 (@block_merge marked 11 680 40 40 mark11_680 mark11_720))))) (@block_merge marked 11 760 389 396 (@block_merge marked 11 760 189 200 (@block_merge marked 11 760 80 109 (@block_merge marked 11 760 40 40 mark11_760 mark11_800) (@block_merge marked 11 840 40 69 mark11_840 (@block_merge marked 11 880 29 40 mark11_880 mark11_909))) (@block_merge marked 11 949 80 120 (@block_merge marked 11 949 40 40 mark11_949 mark11_989) (@block_merge marked 11 1029 40 80 mark11_1029 (@block_merge marked 11 1069 40 40 mark11_1069 mark11_1109)))) (@block_merge marked 11 1149 200 196 (@block_merge marked 11 1149 80 120 (@block_merge marked 11 1149 40 40 mark11_1149 mark11_1189) (@block_merge marked 11 1229 40 80 mark11_1229 (@block_merge marked 11 1269 40 40 mark11_1269 mark11_1309))) (@block_merge marked 11 1349 80 116 (@block_merge marked 11 1349 40 40 mark11_1349 mark11_1389) (@block_merge marked 11 1429 40 76 mark11_1429 (@block_merge marked 11 1469 40 36 mark11_1469 mark11_1509))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark12_0 : block marked 12 0 40 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark12_40 : block marked 12 40 7 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark12_47 : block marked 12 47 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark12_87 : block marked 12 87 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark12_127 : block marked 12 127 40 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark12_167 : block marked 12 167 2 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark12_169 : block marked 12 169 40 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark12_209 : block marked 12 209 34 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem markAll12 : block marked 12 0 243 = true := (@block_merge marked 12 0 127 116 (@block_merge marked 12 0 47 80 (@block_merge marked 12 0 40 7 mark12_0 mark12_40) (@block_merge marked 12 47 40 40 mark12_47 mark12_87)) (@block_merge marked 12 127 42 74 (@block_merge marked 12 127 40 2 mark12_127 mark12_167) (@block_merge marked 12 169 40 34 mark12_169 mark12_209)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark13_0 : block marked 13 0 7 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark13_7 : block marked 13 7 10 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem markAll13 : block marked 13 0 17 = true := (@block_merge marked 13 0 7 10 mark13_0 mark13_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem mark14_0 : block marked 14 0 1 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem markAll14 : block marked 14 0 1 = true := mark14_0
theorem markedChecks : checkedTables marked 14 := by
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
  · exact markAll8
  · exact markAll9
  · exact markAll10
  · exact markAll11
  · exact markAll12
  · exact markAll13
  · exact markAll14
def markedWire : Sig := inputs.getD 4 zero ||| inputs.getD 6 zero

def markedOff (i : Fin 9) : Row :=
  if i = 4 then 65 else if i = 6 then 18 else absentRow i

def markedOn (i : Fin 9) : Row := Fin.ofNat 512 ((markedOff i).val ||| (1 <<< i.val))
theorem or_witness : ∀ i : Fin 9,
    (bit (markedOff i) graph != bit (markedOn i) graph) &&
    ((inputs++[markedWire]).all fun w => w == inputs.getD i.val zero ||
      bit (markedOff i) w == bit (markedOn i) w) = true := by decide +kernel

theorem marked_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[markedWire]) :
    S=inputs.toFinset ∨ S=(inputs++[markedWire]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := or_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (markedOff i) (markedOn i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hmarkedWire : markedWire ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hmarkedWire)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hmarkedWire hw)) needed


theorem markedBound (gs : List Gate) (o : Nat)
    (hf : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gs o))
    (comp : ∀ x : Fin 9 → Bool, (Circuit.mk gs o).eval (List.ofFn x ++ [x 4 || x 6]) = edge x) :
    15 ≤ gs.length := by
  by_contra! small
  have getGraph : (execute gs (inputs ++ [markedWire])).getD o zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute gs (inputs ++ [markedWire])).getD o zero) = bit r graph
    rw [←b_read, execute_bits _ _ _ (fun g hg => (hf g hg).1), edge_table r]
    have initEq : (inputs ++ [markedWire]).map (bit r) = List.ofFn (sample r) ++ [sample r 4 || sample r 6] := by
      rw [List.map_append, ←sampled]
      change _ ++ [bit r (inputs.getD 4 zero ||| inputs.getD 6 zero)] = _
      simp only [bit, BitVec.getLsbD_or, sample]
      rfl
    rw [initEq]
    exact comp (sample r)
  have h := get_rep (execute gs (inputs ++ [markedWire])) o
  rw [getGraph] at h
  obtain ⟨k,t,S,hk,run,sub⟩ := extract gs _ hf graph_proper (h.resolve_right (fun n => n graph_proper))
  have low := before_sound known383 valid383
  rcases marked_roots run sub with e | e
  · exact dead_start low geomdead tablesdead k t (by omega) (e ▸ run)
  · have noRun := root_index (g:=marked) low markedGeometry markedChecks (k:=14) (by decide)
        (i:=0) (ws:=inputs++[markedWire]) (by decide +kernel)
    have tgt : targetOf marked = graph := by decide +kernel
    rw [tgt] at noRun
    exact noRun k t (by omega) (e ▸ run)

end PEqualNP.Outside.L_meta_3553

theorem PEqualNP.Outside.L_meta_3553 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →     (∀ (x4 : Fin (9 : ℕ) → Bool), { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ))]) = (fun (x5 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (9 : ℕ) (x6 / (9 : ℕ))) && x5 (Fin.ofNat (9 : ℕ) (x6 % (9 : ℕ)))) x4) →       (∃ (x5 : Fin x1.length) (x6 : Fin x1.length),           x5 < x6 ∧             (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x5;               x7.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x7.inputs) ∧               (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x6;                 x7.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x7.inputs) ∧                 (∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x8.inputs) →                       x7 = x5) ∧                   ∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x8.inputs) →                       x7 = x6) →         (15 : ℕ) ≤ x1.length := by
  intro gs o hf comp _
  apply PEqualNP.Outside.L_meta_3553.markedBound gs o hf
  intro x
  refine (comp x).trans ?_
  simp [PEqualNP.Outside.L_meta_3553.edge, List.any_cons, Bool.or_assoc, Fin.ofNat]
