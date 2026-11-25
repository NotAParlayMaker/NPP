import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5522_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- Each wire is represented by its truth values on the sixteen one-hot pairs.
-- The circuit extraction and rectangle lemmas are adapted from L_meta_3885.
abbrev Sig:=BitVec 16
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 16
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a : Sig) : Prop:=a≠zero∧a≠one
theorem bin_comm (d : Bool) (a b : Sig) : bin d a b=bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
-- Following an output back through the gates leaves a set of required wire values.
def Live (target : Sig) : Nat → Nat → Finset Sig → Prop:=fun k t S =>
  ∀ (M : (Nat → Nat → Finset Sig → Prop)),(proper target → M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a → neg a ∉ insert a U → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a → proper b → a≠b → bin d a b ∉ insert a (insert b U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) →
  M k t S
theorem Live.stop {target : Sig}  (h0 : proper target) : Live target 0 0 {target}:=fun M stop unary binary => @stop  h0
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U):=fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
theorem Live.induct {target : Sig} {M : (Nat → Nat → Finset Sig → Prop)} {k t S} (h : Live target k t S)
  (stop : proper target → M 0 0 {target})
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a → neg a ∉ insert a U → Live target k t (insert (neg a) U) → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a → proper b → a≠b → bin d a b ∉ insert a (insert b U) → Live target k t (insert (bin d a b) U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live target k t S∧M k t S)
  (fun h0 => ⟨@Live.stop target  h0,@stop  h0⟩)
  (@fun k t U a h0 h1 h2 => ⟨@Live.unary target k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
  (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@Live.binary target k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
theorem Live.recurse {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig) (proof : Live target k t S),Prop}
  (stop : ∀ (h0 : proper target),M 0 0 {target} (@Live.stop target  h0))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) h2),M (k+1) (t+1) (insert a U) (@Live.unary target k t U a h0 h1 h2))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) h4),M (k+1) t (insert a (insert b U)) (@Live.binary target k t U a b d h0 h1 h2 h3 h4))
  {k t S} (h : Live target k t S) : M k t S h:=by
  have r:=Live.induct (M:=fun k t S => ∀ hh : Live target k t S,M k t S hh) h
    (fun h0 _ => @stop  h0)
    (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
    (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
  exact r h

lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S,proper a:=by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live target k t S) : t ≤ k∧S.card+t ≤ k+1:=by
  induction h using Live.recurse with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U:=fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U:=fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs:=g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop:=v ∈ w∨¬proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma bin_laws (a : Sig) :
    bin false a one=a∧bin true a zero=a ∧
    bin false a zero=zero∧bin true a one=one ∧
    bin false a a=a∧bin true a a=a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
lemma neg_laws : neg zero=one∧neg one=zero:=by simp [neg,zero,one]
lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a=zero∨a=one∨a ∈ w∧proper a:=by
  by_cases hz : a=zero
  · exact Or.inl hz
  by_cases ho : a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def bit (i : Fin 16) (a : Sig) : Bool:=a.getLsbD i.val
lemma bit_zero (i) : bit i zero=false:=by simp [bit,zero]
lemma bit_one (i) : bit i one=true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g)=g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false):=by
  obtain ⟨o,l⟩:=g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _)=(_&&_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)&&x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _)=(_||_)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero)||x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _
lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _=_
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

def isNotT (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
lemma gate_repT (w : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2) :
    represented w (gv w g) ∨
      (if isNotT g.op then ∃ a,a∈w∧proper a∧gv w g=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧gv w g=bin d a b):=by
  have nx (a : Sig) (ha : represented w a) : represented w (neg a)∨∃ x,x∈w∧proper x∧neg a=neg x:=by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
    · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d : Bool) (a b : Sig) (ha : represented w a) (hb : represented w b) :
      represented w (bin d a b)∨∃ d' x y,x∈w∧y∈w∧proper x∧proper y∧x≠y∧bin d a b=bin d' x y:=by
    have bzero : ∀ v,bin false v zero=zero∧bin true v zero=v:=fun v => ⟨(bin_laws v).2.2.1,(bin_laws v).2.1⟩
    have bone : ∀ v,bin false v one=v∧bin true v one=one:=fun v => ⟨(bin_laws v).1,(bin_laws v).2.2.2.1⟩
    rcases operand_cases ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [bin_comm]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2]; exact Or.inl hb
    · rw [bin_comm]
      cases d
      · rw [(bone b).1]; exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases operand_cases hb with rfl | rfl | ⟨hmb,hpb⟩
      · cases d
        · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
        · rw [(bzero a).2]; exact Or.inl (Or.inl hma)
      · cases d
        · rw [(bone a).1]; exact Or.inl (Or.inl hma)
        · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
      · by_cases eq : a=b
        · subst b
          cases d
          · rw [(bin_laws a).2.2.2.2.1]; exact Or.inl (Or.inl hma)
          · rw [(bin_laws a).2.2.2.2.2]; exact Or.inl (Or.inl hma)
        · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
  obtain ⟨ho,hl⟩:=hg
  rcases ho with ho | ho | ho
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bn false _ _ (get_rep w i) (get_rep w j)
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bn true _ _ (get_rep w i) (get_rep w j)
  · rw [Set.mem_singleton_iff] at ho
    simp only [ho,isNotT,ite_true]
    cases hi : g.inputs with
    | nil =>
      have hgv : gv w g=one:=by simp only [gv,ho,hi,List.map_nil,List.headD_nil,neg_laws.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g=neg (w.getD i zero):=by simp only [gv,ho,hi,List.map_cons,List.headD_cons]
      rw [hgv]; exact nx _ (get_rep w i)
lemma pull_gateT {w : List Sig} {z : Sig} {k t S} (isN : Bool) (h : Live target k t S)
    (hz : represented w z ∨
      (if isN then ∃ a,a∈w∧proper a∧z=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧z=bin d a b))
    (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1∧t' ≤ t+isN.toNat∧Live target k' t' S'∧∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w∨a=z) with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | hwit
      · exact False.elim ((hr.resolve_left hw) hp)
      · cases isN with
        | true =>
          simp only [ite_true] at hwit
          obtain ⟨a,ha,hp',eq⟩:=hwit
          subst z
          let U:=S.erase (neg a)
          have ht : Live target k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : neg a ∉ insert a U:=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu _ u)
          exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by simp,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
        | false =>
          simp only [Bool.false_eq_true,ite_false] at hwit
          obtain ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩:=hwit
          subst z
          let U:=S.erase (bin d a b)
          have ht : Live target k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : bin d a b ∉ insert a (insert b U):=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp u with eq | u
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu _ u)
          exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,by simp,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
    intro a ha
    have hn : a≠z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
lemma extractT (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length∧t ≤ gs.countP (fun g => isNotT g.op)∧Live target k t S∧∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩:=ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩:=pull_gateT (isNotT g.op) hl (gate_repT w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hlu,hT⟩
    simp only [List.countP_cons]
    cases h : isNotT g.op <;> simp [h] at hu' ⊢ <;> omega

abbrev Row := Fin 16
theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T=true) (negRow : bit s T=false) :
    ∃ a ∈ S,bit r a=true∧bit s a=false:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩:=ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def separates (w : Sig) (p q : Row) := bit p w = true ∧ bit q w = false
-- At the tight leaf count, each chosen input labels a rectangle of positive-negative pairs.
def rectProtocol (T : Sig) (S : Finset Sig) : Prop :=
  ∃ f : Row → Row → Sig, (∀ p q, f p q ∈ S) ∧
    (∀ p q, separates T p q → separates (f p q) p q) ∧
    ∀ p q r s, f p q = f r s → f p s = f p q
def forkPick (d : Bool) (a b : Sig) (p q : Row) :=
  if (if d then bit p a else !(bit q a)) then a else b
lemma forkPick_mem (d a b p q) : forkPick d a b p q=a ∨ forkPick d a b p q=b := by
  cases d <;> cases hp : bit p a <;> cases hq : bit q a <;> simp [forkPick,hp,hq]
lemma forkPick_sep {d a b p q} (h : separates (bin d a b) p q) :
    separates (forkPick d a b p q) p q := by
  simp only [separates,bit_bin] at h
  cases d <;> cases hp : bit p a <;> cases hq : bit q a <;>
    simp_all [forkPick,separates]
lemma refine_protocol {T U a b d} (an : a ∉ U) (bn : b ∉ U)
    (h : rectProtocol T (insert (bin d a b) U)) :
    rectProtocol T (insert a (insert b U)) := by
  obtain ⟨f,mem,sep,rect⟩ := h
  let z := bin d a b
  let g := fun p q => if f p q=z then forkPick d a b p q else f p q
  have undo (p q) : (if g p q=a ∨ g p q=b then z else g p q) = f p q := by
    by_cases hz : f p q=z
    · simp only [g,hz,ite_true,if_pos (forkPick_mem d a b p q)]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      have ha : f p q ≠ a := fun e => an (e ▸ hu)
      have hb : f p q ≠ b := fun e => bn (e ▸ hu)
      simp [g,hz,ha,hb]
  refine ⟨g,?_,?_,?_⟩
  · intro p q
    by_cases hz : f p q=z
    · rcases forkPick_mem d a b p q with e|e <;> simp [g,hz,e]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      simp only [g,if_neg hz]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
  · intro p q st
    by_cases hz : f p q=z
    · have hh : separates z p q := by rw [←hz]; exact sep p q st
      simpa [g,hz] using forkPick_sep (d:=d) (a:=a) (b:=b) hh
    · simpa [g,hz] using sep p q st
  · intro p q r s e
    have eo : f p q=f r s := by rw [← undo p q,← undo r s,e]
    have ec := rect p q r s eo
    by_cases hz : f p q=z
    · have ht : f r s=z := eo.symm.trans hz
      have ep : forkPick d a b p q=forkPick d a b r s := by simpa only [g,hz,ht,ite_true] using e
      simp only [g,ec,hz,ite_true]
      cases d
      · exact ep.symm
      · rfl
    · simp [g,ec,hz]
theorem tight_protocol {T k t S} (h : Live T k t S) (tight : k+1 ≤ S.card) :
    rectProtocol T S := by
  induction h using Live.recurse with
  | stop hp => exact ⟨fun _ _ => T,fun _ _ => Finset.mem_singleton_self _,fun _ _ => id,fun _ _ _ _ _ => rfl⟩
  | @unary k t U a hp hf tail ih =>
    have sz := (live_size (Live.unary hp hf tail)).2
    omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have zu : bin d a b ∉ U := fun m => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have sz := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at sz
    have x := Finset.card_insert_le (a:=a) (s:=insert b U)
    have y := Finset.card_insert_le (a:=b) (s:=U)
    have an : a ∉ U := by
      intro am
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem am)] at tight
      omega
    have bn : b ∉ U := by
      intro bm
      rw [Finset.insert_eq_of_mem bm] at tight x
      omega
    apply refine_protocol an bn
    apply ih
    rw [Finset.card_insert_of_notMem zu]
    omega
def forcedPick (T : Sig) (S : Finset Sig) (w : Sig) (p q : Row) :=
  separates T p q ∧ ∀ v ∈ S, separates v p q → v=w
def clash (T : Sig) (S : Finset Sig) (a b : Sig) : Prop :=
  a∈S ∧ b∈S ∧ a≠b ∧ ∃ p u v q r s,
    forcedPick T S a p u ∧ forcedPick T S b p v ∧ forcedPick T S a r q ∧ forcedPick T S b s q
lemma protocol_consistent {T S a b} (h : rectProtocol T S) (c : clash T S a b) : False := by
  obtain ⟨f,mem,sep,rect⟩ := h
  obtain ⟨_,_,ne,p,u,v,q,r,s,w₁,w₂,w₃,w₄⟩ := c
  have pick {z x y} (w : forcedPick T S z x y) := w.2 _ (mem x y) (sep x y w.1)
  have A := rect p u r q ((pick w₁).trans (pick w₃).symm)
  have B := rect p v s q ((pick w₂).trans (pick w₄).symm)
  exact ne ((A.trans (pick w₁)).symm.trans (B.trans (pick w₂)))


def seeds : List Sig := [15,240,3840,61440,4369,8738,17476,34952]
def required : Finset Sig := {15,240,3840,4369,8738,17476,34952}

def leftVertex (i : Row) : Fin 4 := Fin.ofNat 4 (i.val / 4)
def rightVertex (i : Row) : Fin 4 := Fin.ofNat 4 (i.val % 4)

lemma samples : ∀ i : Row,
    seeds.map (bit i) = oneEach (leftVertex i) (rightVertex i) := by decide +kernel

lemma targetSample : ∀ i : Row, bit i (301 : Sig) =
    (301 : ℕ).testBit (4 * (leftVertex i).val + (rightVertex i).val) := by decide +kernel

def forced (w : Sig) (p q : Row) : Prop :=
  separates 301 p q ∧ ∀ v ∈ seeds, separates v p q → v = w

def pinCheck (w : Sig) (p q : Row) : Bool :=
  decide (bit p (301 : Sig) = true ∧ bit q (301 : Sig) = false) &&
    seeds.all (fun v => decide ((bit p v = true ∧ bit q v = false) → v = w))

lemma forced_of_check {w : Sig} {p q : Row} (h : pinCheck w p q = true) : forced w p q := by
  simpa only [pinCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, forced, separates] using h

-- Two pairs can only be distinguished by the first row input, and two by the first column input.
-- Their rectangles would both contain the pair of table positions 0 and 10.
lemma testedPins :
    forced 15 0 4 ∧ forced 4369 0 1 ∧ forced 15 2 10 ∧ forced 4369 8 10 :=
  ⟨forced_of_check (by decide), forced_of_check (by decide),
    forced_of_check (by decide), forced_of_check (by decide)⟩

lemma pins : ∀ w ∈ required, ∃ p q : Row, forced w p q := by
  intro w hw
  simp only [required, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 4, testedPins.1⟩
  · exact ⟨5, 1, forced_of_check (by decide)⟩
  · exact ⟨8, 4, forced_of_check (by decide)⟩
  · exact ⟨0, 1, testedPins.2.1⟩
  · exact ⟨5, 4, forced_of_check (by decide)⟩
  · exact ⟨2, 1, forced_of_check (by decide)⟩
  · exact ⟨3, 1, forced_of_check (by decide)⟩

lemma lower :
    ¬ RepSizeAtMost (fun u v : Fin 4 => (301 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  rintro ⟨C,mono,cap,rep⟩
  have legal : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop,hlen⟩ := mono g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
    exact ⟨hop.elim Or.inl (fun e => Or.inr (Or.inl e)), hlen⟩
  have negCount : C.gates.countP (fun g => isNotT g.op) = 0 := by
    apply List.countP_eq_zero.mpr
    intro g hg
    have ho := (mono g hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho
    rcases ho with ho | ho <;> simp [isNotT,ho]
  have hp : proper (301 : Sig) := by unfold proper; decide
  have he : (execute C.gates seeds).getD C.output zero = (301 : Sig) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates seeds).getD C.output zero) = bit r (301 : Sig)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),samples r]
    exact (rep (leftVertex r) (rightVertex r)).trans (targetSample r).symm
  have hget := get_rep (execute C.gates seeds) C.output
  rw [he] at hget
  obtain ⟨k,t,S,hk,hn,hl,hs⟩ := extractT C.gates seeds legal hp (hget.resolve_right (fun h => h hp))
  rw [negCount] at hn
  have ht : t = 0 := by omega
  have forceMem {w p q} (f : forced w p q) : w ∈ S := by
    obtain ⟨a,ha,hp',hn'⟩ := mono_row_difference hl ht f.1.1 f.1.2
    exact (f.2 a (hs a ha) ⟨hp',hn'⟩) ▸ ha
  have sub : required ⊆ S := by
    intro w hw
    obtain ⟨p,q,f⟩ := pins w hw
    exact forceMem f
  have seven : required.card = 7 := by decide
  have hs7 := Finset.card_le_card sub
  change C.gates.length ≤ 6 at cap
  have hproto := tight_protocol hl (by omega)
  have liftF {w p q} (f : forced w p q) : forcedPick 301 S w p q :=
    ⟨f.1, fun v hv => f.2 v (hs v hv)⟩
  obtain ⟨f1,f2,f3,f4⟩ := testedPins
  apply protocol_consistent hproto (a:=15) (b:=4369)
  exact ⟨forceMem f1, forceMem f2, by decide, 0,4,1,10,2,8,
    liftF f1,liftF f2,liftF f3,liftF f4⟩

-- The output is the union of three terms, for rows zero, one and two.
theorem upper : RepSizeAtMost (fun u v : Fin 4 => (301 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  refine ⟨⟨[⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [8, 7]⟩,
    ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5522_aux

theorem PEqualNP.Outside.L_meta_5522 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (301 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (301 : ℕ).testBit (4 * u.val + v.val)) 6 :=
  ⟨PEqualNP.Outside.L_meta_5522_aux.upper, PEqualNP.Outside.L_meta_5522_aux.lower⟩
